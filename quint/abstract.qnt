/// THE MACHINE. One request, one transition. A handler is a PARTIAL FUNCTION
/// from the store to the store: at most one outcome, and none at all when the
/// request does not apply. `Next` is then "some event applies", which is what
/// lets `refine.qnt` ask whether the executor's writes are abstract steps.
///
/// Every handler reads the store through `project` and writes it in one go, so
/// a promise and its task never disagree and no two requests can get inside
/// each other.
///
/// The Quint reading of `tla/AbstractAction.tla`.
module abstract {
  import requests.* from "./requests"

  /// The whole of the abstract state. `objects` is partial: the keys are what
  /// exists. `now` is NOT part of the store -- a server does not own the clock,
  /// so it cannot be asked to have noticed the time passing.
  type State = {
    objects: Id -> Object,
    outbox:  Set[OutEntry],    // at most one entry per MsgKey
    now:     int,
  }

  // ------------------------------------------------------------ record surgery
  //
  // The five things that happen to a task, named once, and the four that happen
  // to a promise's waiters. Every EXCEPT block in the TLA is one of these, and
  // naming them is most of why this file is shorter.

  pure def lapsed(tags: Tags): PromiseState =
    if (tags.timer) Resolved else RejectedTimedout

  /// The work is over, so the lease, the worker and the buffered wakeups go
  /// with it. A promise that has no task still has no task.
  pure def settled(t: Task): Task = { ...t,
    state: if (t.state == TaskNone) TaskNone else TaskFulfilled,
    pid: None, ttl: None, expiresAt: None, retryAt: None, resumes: Set() }

  /// Held by `pid` until `at + ttl`. The version bump IS the fence: whoever
  /// held it before is now naming a version that no longer exists.
  pure def acquiredBy(t: Task, pid: Pid, ttl: int, at: int): Task = { ...t,
    state: TaskAcquired, version: t.version + 1, ttl: Some(ttl), pid: Some(pid),
    expiresAt: Some(at + ttl), retryAt: None, resumes: Set() }

  /// Nobody holds it, and it is due at `at`. Keeps `resumes`: a wakeup that
  /// arrived while the task was running is still owed to whoever picks it up.
  pure def pendingAt(t: Task, at: int): Task = { ...t,
    state: TaskPending, pid: None, ttl: None, expiresAt: None, retryAt: Some(at) }

  /// Parked on someone else's promise: no lease, no retry, nothing due.
  pure def suspended(t: Task): Task = { ...t,
    state: TaskSuspended, pid: None, ttl: None, expiresAt: None,
    retryAt: None, resumes: Set() }

  pure def halted(t: Task): Task = { ...t,
    state: TaskHalted, pid: None, ttl: None, expiresAt: None, retryAt: None }

  pure def withTask(o: Object, t: Task): Object = { ...o, task: t }

  pure def withCallback(o: Object, w: Id): Object =
    { ...o, promise: { ...o.promise, callbacks: o.promise.callbacks.union(Set(w)) } }
  pure def withoutCallback(o: Object, w: Id): Object =
    { ...o, promise: { ...o.promise, callbacks: o.promise.callbacks.exclude(Set(w)) } }
  pure def withListener(o: Object, a: Address): Object =
    { ...o, promise: { ...o.promise, listeners: o.promise.listeners.union(Set(a)) } }
  pure def withoutListener(o: Object, a: Address): Object =
    { ...o, promise: { ...o.promise, listeners: o.promise.listeners.exclude(Set(a)) } }

  // ------------------------------------------------------------ the projection

  /// The object as the protocol sees it at instant `t`. A pending promise past
  /// its deadline is ALREADY settled -- the deadline settled it, not a request
  /// -- and a timer promise is the one whose lapsing is success.
  ///
  /// This is the whole trick of the abstract machine: no handler has to ask
  /// whether a timeout has been processed yet, because every handler reads
  /// through here and a lapsed promise is never pending.
  pure def project(obj: Object, t: int): Object =
    if (obj.promise.state == Pending and obj.promise.timeoutAt <= t)
      { promise: { ...obj.promise, state: lapsed(obj.promise.tags),
                   value: None, settledAt: Some(obj.promise.timeoutAt) },
        task: obj.task.settled() }
    else
      obj

  /// A promise born after its own deadline is born settled -- and its task,
  /// if it has one, is born with nothing left to do.
  pure def new(req: CreateReq, t: int): Object =
    val alive = req.timeoutAt > t
    { promise: { state:     if (alive) Pending else lapsed(req.tags),
                 param:     req.param,
                 value:     None,
                 tags:      req.tags,
                 timeoutAt: req.timeoutAt,
                 createdAt: if (alive) t else req.timeoutAt,
                 settledAt: if (alive) None else Some(req.timeoutAt),
                 callbacks: Set(),
                 listeners: Set() },
      task:    if (not(req.tags.targeted)) noTask
               else if (alive) { ...noTask, state: TaskPending, retryAt: Some(t) }
               else { ...noTask, state: TaskFulfilled } }

  // ------------------------------------------------------------- reading state

  pure def has(s: State, i: Id): bool = s.objects.keys().contains(i)

  /// The object at `i` as the protocol sees it: the lapsed deadline already
  /// applied, whether or not anyone has written that down. Every handler reads
  /// through here, so the difference between `live` and `objects` is exactly
  /// the work the timeout events have not got to yet.
  pure def live(s: State, i: Id): Object = project(s.objects.get(i), s.now)

  pure def write(s: State, i: Id, o: Object): State =
    { ...s, objects: s.objects.put(i, o) }

  /// A step that does not happen. A request that does not apply is not a
  /// smaller step, it is no step at all.
  pure val noStep: Set[State] = Set()

  // ---------------------------------------------------------------- promises

  pure def promiseCreate(s: State, req: CreateReq): Set[State] =
    if (not(s.has(req.id)))
      Set(s.write(req.id, new(req, s.now)))
    else noStep

  pure def promiseSettle(s: State, req: SettleReq): Set[State] =
    val old = s.live(req.id)
    if (and { s.has(req.id), old.promise.state == Pending })
      Set(s.write(req.id,
        { promise: { ...old.promise, state: req.state, value: Some(req.value),
                     settledAt: Some(s.now) },
          task:    old.task.settled() }))
    else noStep

  /// A promise waits on a promise. Only a targeted promise can be woken, and
  /// only an external promise is worth waiting on -- what settles it is not
  /// this server.
  pure def promiseRegisterCallback(s: State, req: CallbackReq): Set[State] =
    val awaited = s.live(req.awaited)
    val awaiter = s.live(req.awaiter)
    if (and {
      s.has(req.awaited),
      s.has(req.awaiter),
      awaiter.promise.tags.targeted,
      isExternal(awaited.promise),
      awaited.promise.state == Pending,
      awaiter.promise.state == Pending,
    })
      Set(s.write(req.awaited, awaited.withCallback(req.awaiter)))
    else noStep

  /// An address waits on a promise. Same door, no awaiter.
  pure def promiseRegisterListener(s: State, req: ListenerReq): Set[State] =
    val old = s.live(req.awaited)
    if (and {
      s.has(req.awaited),
      isExternal(old.promise),
      old.promise.state == Pending,
    })
      Set(s.write(req.awaited, old.withListener(req.address)))
    else noStep

  // ------------------------------------------------------------------- tasks

  /// Create and acquire in one request: either the promise is new -- and the
  /// caller holds its task the moment it exists -- or it is already there and
  /// its task was going begging.
  pure def taskCreate(s: State, req: TaskCreateReq): Set[State] =
    val born = new(req.act, s.now)
    val old  = s.live(req.act.id)
    if (not(req.act.tags.targeted))
      noStep
    else if (not(s.has(req.act.id)))
      Set(s.write(req.act.id,
        if (born.promise.state == Pending)
          born.withTask(born.task.acquiredBy(req.pid, req.ttl, s.now))
        else
          born))
    else if (and { old.promise.tags.targeted, old.task.state == TaskPending })
      Set(s.write(req.act.id, old.withTask(old.task.acquiredBy(req.pid, req.ttl, s.now))))
    else noStep

  pure def taskAcquire(s: State, req: TaskAcquireReq): Set[State] =
    val old = s.live(req.id)
    if (and {
      s.has(req.id),
      old.task.state == TaskPending,
      old.promise.state == Pending,
      old.task.version == req.version,
    })
      Set(s.write(req.id, old.withTask(old.task.acquiredBy(req.pid, req.ttl, s.now))))
    else noStep

  /// A worker still holding its lease writes SOMEWHERE ELSE. The version it
  /// names is the whole content: a worker whose lease was taken names a
  /// version that no longer exists, and its write does not happen.
  pure def taskFence(s: State, req: TaskFenceReq): Set[State] =
    val old = s.live(req.id)
    if (and {
      s.has(req.id),
      fencedId(req.act) != req.id,
      old.task.state == TaskAcquired,
      old.promise.state == Pending,
      old.task.version == req.version,
    })
      match req.act {
        | FenceCreate(r) => promiseCreate(s, r)
        | FenceSettle(r) => promiseSettle(s, r)
      }
    else noStep

  /// One request, many leases: a worker renews everything it still holds, and
  /// says nothing about what it does not.
  pure def taskHeartbeat(s: State, req: TaskBeatReq): Set[State] =
    val beat = s.objects.keys().filter(i =>
      val o = s.live(i)
      and {
        req.tasks.exists(rf => rf.id == i and rf.version == o.task.version),
        o.task.state == TaskAcquired,
        o.task.pid == Some(req.pid),
        o.promise.state == Pending,
      })
    if (beat != Set())
      Set(beat.fold(s, (acc, i) =>
        val o = s.live(i)
        acc.write(i, o.withTask({ ...o.task,
          expiresAt: o.task.ttl.mapOption(t => s.now + t) }))))
    else noStep

  /// Park a task on the promises it is waiting for, registering itself on each.
  /// If any of them has ALREADY settled there is nothing to wait for: the task
  /// keeps its lease and only its buffered wakeups are cleared, because it is
  /// about to be told.
  pure def taskSuspend(s: State, req: TaskSuspendReq): Set[State] =
    val aw  = req.actions.map(a => a.awaited)
    val old = s.live(req.id)
    if (and {
      req.actions != Set(),
      not(aw.contains(req.id)),
      aw.forall(a => a.origin == req.id.origin),
      s.has(req.id),
      aw.forall(a => s.has(a)),
      old.task.state == TaskAcquired,
      old.promise.state == Pending,
      old.task.version == req.version,
      aw.forall(a => isExternal(s.live(a).promise)),
    })
      if (aw.exists(a => s.live(a).promise.state != Pending))
        Set(s.write(req.id, old.withTask({ ...old.task, resumes: Set() })))
      else
        Set(aw.fold(s.write(req.id, old.withTask(old.task.suspended())),
                    (acc, a) => acc.write(a, s.live(a).withCallback(req.id))))
    else noStep

  /// Settle the promise and retire the task in one write. This is the only
  /// place a worker gets to say what its promise came to.
  pure def taskFulfill(s: State, req: TaskFulfillReq): Set[State] =
    val old = s.live(req.id)
    if (and {
      s.has(req.id),
      old.task.state == TaskAcquired,
      old.promise.state == Pending,
      old.task.version == req.version,
    })
      Set(s.write(req.id,
        { promise: { ...old.promise, state: req.act.state, value: Some(req.act.value),
                     settledAt: Some(s.now) },
          task:    old.task.settled() }))
    else noStep

  /// Hand it back, due now.
  pure def taskRelease(s: State, req: TaskRef): Set[State] =
    val old = s.live(req.id)
    if (and {
      s.has(req.id),
      old.task.state == TaskAcquired,
      old.promise.state == Pending,
      old.task.version == req.version,
    })
      Set(s.write(req.id, old.withTask(old.task.pendingAt(s.now))))
    else noStep

  /// Stop dispatching this task, without settling its promise. No version:
  /// halting is not the worker's move.
  pure def taskHalt(s: State, id: Id): Set[State] =
    val old = s.live(id)
    if (and {
      s.has(id),
      not(Set(TaskNone, TaskFulfilled, TaskHalted).contains(old.task.state)),
    })
      Set(s.write(id, old.withTask(old.task.halted())))
    else noStep

  pure def taskContinue(s: State, id: Id): Set[State] =
    val old = s.live(id)
    if (and {
      s.has(id),
      old.task.state == TaskHalted,
      old.promise.state == Pending,
    })
      Set(s.write(id, old.withTask(old.task.pendingAt(s.now))))
    else noStep

  // --------------------------------------------------------------- deadlines

  /// Writing down what `project` already says. The lapse is not a decision --
  /// it happened when the deadline passed -- so this is the ONE handler that
  /// reads `objects` raw: it exists to make the store agree with the protocol.
  pure def promiseTimeout(s: State, i: Id): Set[State] =
    val old = s.objects.get(i)
    if (and {
      s.has(i),
      old.promise.state == Pending,
      old.promise.timeoutAt <= s.now,
    })
      Set(s.write(i, project(old, s.now)))
    else noStep

  /// The lease ran out. The task goes back on the pile, due now -- the worker
  /// may still be alive and may still write, which is what the version is for.
  pure def leaseTimeout(s: State, i: Id): Set[State] =
    val old = s.live(i)
    if (and {
      s.has(i),
      old.task.state == TaskAcquired,
      due(old.task.expiresAt, s.now),
      old.promise.state == Pending,
    })
      Set(s.write(i, old.withTask(old.task.pendingAt(s.now))))
    else noStep

  /// Dispatch, and arm the next attempt. The message names the version, so a
  /// worker can tell whether the task it was handed is still the task it has.
  pure def retryTimeout(s: State, i: Id): Set[State] =
    val old = s.live(i)
    val msg = { address: old.promise.tags.target,
                message: Execute({ id: i, version: old.task.version }) }
    if (and {
      s.has(i),
      old.task.state == TaskPending,
      due(old.task.retryAt, s.now),
      old.promise.state == Pending,
    })
      Set({ ...s.write(i, old.withTask({ ...old.task, retryAt: Some(s.now + RetryTimeout) })),
            outbox: s.outbox.send(msg) })
    else noStep

  // ----------------------------------------------------------- settling news

  /// Tell an address, once, and forget it.
  pure def listenerDrain(s: State, req: ListenerDrainReq): Set[State] =
    val awaited = s.live(req.id)
    val msg = { address: req.address,
                message: Unblock({ id: req.id, state: awaited.promise.state }) }
    if (and {
      s.has(req.id),
      awaited.promise.listeners.contains(req.address),
      awaited.promise.state != Pending,
    })
      Set({ ...s.write(req.id, awaited.withoutListener(req.address)),
            outbox: s.outbox.send(msg) })
    else noStep

  /// Tell an awaiter, once. A suspended awaiter wakes up and is due now; a
  /// running one only has the news buffered, because it is not parked and
  /// waking it would mean nothing; and one that is gone or finished is simply
  /// struck off.
  pure def callbackDrain(s: State, req: CallbackDrainReq): Set[State] =
    val awaited = s.live(req.id)
    val awaiter = s.live(req.awaiter)
    val struck  = s.write(req.id, awaited.withoutCallback(req.awaiter))
    if (and {
      s.has(req.id),
      awaited.promise.callbacks.contains(req.awaiter),
      awaited.promise.state != Pending,
    })
      if (not(s.has(req.awaiter)))
        Set(struck)
      else if (Set(TaskNone, TaskFulfilled).contains(awaiter.task.state))
        Set(struck)
      else if (awaiter.task.state == TaskSuspended)
        Set(struck.write(req.awaiter, awaiter.withTask(
          { ...awaiter.task.pendingAt(s.now), resumes: Set(req.id) })))
      else
        Set(struck.write(req.awaiter, awaiter.withTask(
          { ...awaiter.task, resumes: awaiter.task.resumes.union(Set(req.id)) })))
    else noStep

  // --------------------------------------------------------------- the clock

  pure def tick(s: State): Set[State] =
    if (s.now < MaxTime) Set({ ...s, now: s.now + 1 }) else noStep

  // ------------------------------------------------------------- the alphabet

  /// What one event does to the store. A read is not a transition, so the two
  /// gets are no abstract step at all.
  pure def fire(s: State, e: Event): Set[State] =
    match e {
      | PromiseGet(_)                => noStep
      | TaskGet(_)                   => noStep
      | PromiseCreate(req)           => promiseCreate(s, req)
      | PromiseSettle(req)           => promiseSettle(s, req)
      | PromiseRegisterCallback(req) => promiseRegisterCallback(s, req)
      | PromiseRegisterListener(req) => promiseRegisterListener(s, req)
      | TaskCreate(req)              => taskCreate(s, req)
      | TaskAcquire(req)             => taskAcquire(s, req)
      | TaskFence(req)               => taskFence(s, req)
      | TaskHeartbeat(req)           => taskHeartbeat(s, req)
      | TaskSuspend(req)             => taskSuspend(s, req)
      | TaskFulfill(req)             => taskFulfill(s, req)
      | TaskRelease(req)             => taskRelease(s, req)
      | TaskHalt(id)                 => taskHalt(s, id)
      | TaskContinue(id)             => taskContinue(s, id)
      | Timeout(req)                 =>
          match req.kind {
            | PromiseDeadline => promiseTimeout(s, req.id)
            | LeaseDeadline   => leaseTimeout(s, req.id)
            | RetryDeadline   => retryTimeout(s, req.id)
          }
      | ListenerDrain(req)           => listenerDrain(s, req)
      | CallbackDrain(req)           => callbackDrain(s, req)
    }

  /// `[Next]_vars`, as a relation: one event applies, or nothing moves. This is
  /// what a lower machine has to satisfy at every one of its transitions to be
  /// an implementation of this one.
  pure def stepsTo(before: State, after: State): bool = or {
    before == after,
    tick(before).contains(after),
    Events.exists(e => fire(before, e).contains(after)),
  }

  // --------------------------------------------------------------- the machine

  var objects: Id -> Object
  var outbox:  Set[OutEntry]
  var now:     int

  val state: State = { objects: objects, outbox: outbox, now: now }

  action land(s: State): bool = all {
    objects' = s.objects, outbox' = s.outbox, now' = s.now,
  }

  action init = all {
    objects' = Map(),
    outbox'  = Set(),
    now'     = 0,
  }

  /// Take the one outcome, when there is one.
  action fireOne(outs: Set[State]): bool = all {
    outs != Set(),
    nondet s2 = outs.oneOf()
    land(s2),
  }

  action clock = all {
    now < MaxTime,
    now' = now + 1,
    objects' = objects,
    outbox'  = outbox,
  }

  /// `Next`. One request applies, or the clock moves.
  action step = any {
    nondet req = CreateReqs.oneOf()      fireOne(promiseCreate(state, req)),
    nondet req = SettleReqs.oneOf()      fireOne(promiseSettle(state, req)),
    nondet req = CallbackReqs.oneOf()    fireOne(promiseRegisterCallback(state, req)),
    nondet req = ListenerReqs.oneOf()    fireOne(promiseRegisterListener(state, req)),
    nondet req = TaskCreateReqs.oneOf()  fireOne(taskCreate(state, req)),
    nondet req = TaskAcquireReqs.oneOf() fireOne(taskAcquire(state, req)),
    nondet req = TaskFenceReqs.oneOf()   fireOne(taskFence(state, req)),
    nondet req = TaskBeatReqs.oneOf()    fireOne(taskHeartbeat(state, req)),
    nondet req = TaskSuspendReqs.oneOf() fireOne(taskSuspend(state, req)),
    nondet req = TaskFulfillReqs.oneOf() fireOne(taskFulfill(state, req)),
    nondet req = TaskRefs.oneOf()        fireOne(taskRelease(state, req)),
    nondet id  = Ids.oneOf()             fireOne(taskHalt(state, id)),
    nondet id  = Ids.oneOf()             fireOne(taskContinue(state, id)),
    nondet i   = Ids.oneOf()             fireOne(promiseTimeout(state, i)),
    nondet i   = Ids.oneOf()             fireOne(leaseTimeout(state, i)),
    nondet i   = Ids.oneOf()             fireOne(retryTimeout(state, i)),
    nondet req = ListenerDrainReqs.oneOf()  fireOne(listenerDrain(state, req)),
    nondet req = CallbackDrainReqs.oneOf()  fireOne(callbackDrain(state, req)),
    clock,
  }

  // ------------------------------------------------------------- what holds
  //
  // Stated over a STATE rather than over the variables, so that `refine.qnt`
  // can ask them of what the executor's store denotes -- which is what
  // `C_TypeOK == A!TypeOK` is in the TLA, and what Quint has no INSTANCE for.

  /// Every object in the store, as written.
  pure def stored(s: State): Set[Object] =
    s.objects.keys().map(i => s.objects.get(i))

  /// What Quint's types do not already say.
  pure def typeOk(s: State): bool = and {
    Time.contains(s.now),
    s.objects.keys().subseteq(Ids),
    s.outbox.forall(a => s.outbox.forall(b => msgKey(a) == msgKey(b) implies a == b)),
    s.stored().forall(o => o.task.state == TaskNone implies o.task == noTask),
  }

  pure def well_formed_promise_created_at_lte_timeout_at(s: State): bool =
    s.stored().forall(o => o.promise.createdAt <= o.promise.timeoutAt)

  pure def well_formed_promise_settled_at_iff_not_pending(s: State): bool =
    s.stored().forall(o => (o.promise.state != Pending) iff (o.promise.settledAt != None))

  pure def well_formed_promise_pending_has_no_value(s: State): bool =
    s.stored().forall(o => o.promise.state == Pending implies o.promise.value == None)

  pure def well_formed_promise_settled_at_lte_timeout_at(s: State): bool =
    s.stored().forall(o =>
      match o.promise.settledAt { | Some(at) => at <= o.promise.timeoutAt | None => true })

  pure def well_formed_task_pending_iff_has_retry_at(s: State): bool =
    s.stored().forall(o => o.task.state != TaskNone implies
      ((o.task.state == TaskPending) iff (o.task.retryAt != None)))

  pure def well_formed_task_acquired_iff_has_expires_at(s: State): bool =
    s.stored().forall(o => o.task.state != TaskNone implies
      ((o.task.state == TaskAcquired) iff (o.task.expiresAt != None)))

  pure def consistent_settled_promise_has_fulfilled_task(s: State): bool =
    s.stored().forall(o =>
      (o.promise.state != Pending and o.task.state != TaskNone)
        implies o.task.state == TaskFulfilled)

  pure def consistent_settled_task_promise_settled(s: State): bool =
    s.stored().forall(o => o.task.state == TaskFulfilled implies o.promise.state != Pending)

  pure def consistent_task_iff_targeted_promise(s: State): bool =
    s.stored().forall(o => (o.task.state != TaskNone) iff o.promise.tags.targeted)

  /// A promise and its task are ONE object, so one write moves both. No
  /// interleaving can catch them disagreeing -- which is a claim about the
  /// state shape, and the reason it is worth stating separately.
  pure def unitCoherent(s: State): bool =
    s.stored().forall(o => not(and {
      o.promise.state != Pending,
      not(Set(TaskNone, TaskFulfilled).contains(o.task.state)),
    }))

  /// An awaiter and the promise it awaits live at one origin. This is what
  /// makes an await local, and a server free to shard on the origin.
  pure def sameOrigin(s: State): bool =
    s.objects.keys().forall(i =>
      s.objects.get(i).promise.callbacks.forall(w => w.origin == i.origin))

  pure def invariants(s: State): bool = and {
    typeOk(s),
    well_formed_promise_created_at_lte_timeout_at(s),
    well_formed_promise_settled_at_iff_not_pending(s),
    well_formed_promise_pending_has_no_value(s),
    well_formed_promise_settled_at_lte_timeout_at(s),
    well_formed_task_pending_iff_has_retry_at(s),
    well_formed_task_acquired_iff_has_expires_at(s),
    consistent_settled_promise_has_fulfilled_task(s),
    consistent_settled_task_promise_settled(s),
    consistent_task_iff_targeted_promise(s),
    unitCoherent(s),
    sameOrigin(s),
  }

  val allInvariants = invariants(state)
}
