/// THE MACHINE. One request, one transition. Every handler reads the store
/// through `project` and writes it in one go, so a promise and its task never
/// disagree and no two requests can get inside each other.
///
/// The Quint reading of `tla/AbstractAction.tla`.
module abstractAction {
  import requests.* from "./requests"

  var objects: Id -> Object    // partial: the keys are what exists
  var outbox:  Set[OutEntry]   // at most one entry per MsgKey
  var now:     int             // the clock. NOT part of the store: a server
                               // does not own it, so it cannot be asked to
                               // have noticed the time passing.

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
    pid: NoPid, ttl: NoTime, expiresAt: NoTime, retryAt: NoTime, resumes: Set() }

  /// Held by `pid` until `at + ttl`. The version bump IS the fence: whoever
  /// held it before is now naming a version that no longer exists.
  pure def acquiredBy(t: Task, pid: Pid, ttl: int, at: int): Task = { ...t,
    state: TaskAcquired, version: t.version + 1, ttl: ttl, pid: pid,
    expiresAt: at + ttl, retryAt: NoTime, resumes: Set() }

  /// Nobody holds it, and it is due at `at`. Keeps `resumes`: a wakeup that
  /// arrived while the task was running is still owed to whoever picks it up.
  pure def pendingAt(t: Task, at: int): Task = { ...t,
    state: TaskPending, pid: NoPid, ttl: NoTime, expiresAt: NoTime, retryAt: at }

  /// Parked on someone else's promise: no lease, no retry, nothing due.
  pure def suspended(t: Task): Task = { ...t,
    state: TaskSuspended, pid: NoPid, ttl: NoTime, expiresAt: NoTime,
    retryAt: NoTime, resumes: Set() }

  pure def halted(t: Task): Task = { ...t,
    state: TaskHalted, pid: NoPid, ttl: NoTime, expiresAt: NoTime, retryAt: NoTime }

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
                   value: NoValue, settledAt: obj.promise.timeoutAt },
        task: obj.task.settled() }
    else
      obj

  /// A promise born after its own deadline is born settled -- and its task,
  /// if it has one, is born with nothing left to do.
  pure def new(req: CreateReq, t: int): Object =
    val alive = req.timeoutAt > t
    { promise: { state:     if (alive) Pending else lapsed(req.tags),
                 param:     req.param,
                 value:     NoValue,
                 tags:      req.tags,
                 timeoutAt: req.timeoutAt,
                 createdAt: if (alive) t else req.timeoutAt,
                 settledAt: if (alive) NoTime else req.timeoutAt,
                 callbacks: Set(),
                 listeners: Set() },
      task:    if (not(req.tags.targeted)) noTask
               else if (alive) { ...noTask, state: TaskPending, retryAt: t }
               else { ...noTask, state: TaskFulfilled } }

  /// The ids that exist.
  val ids: Set[Id] = objects.keys()

  /// The store as the protocol sees it: every lapsed deadline already applied.
  /// Handlers read `live` and write `objects`, and the difference between the
  /// two is exactly the work the timeout actions have not got to yet.
  val live: Id -> Object = ids.mapBy(i => project(objects.get(i), now))

  /// Every request handler writes objects and nothing else.
  action onlyObjects(written: Id -> Object): bool = all {
    objects' = written, outbox' = outbox, now' = now,
  }

  action objectsAndSend(written: Id -> Object, msg: OutEntry): bool = all {
    objects' = written, outbox' = outbox.send(msg), now' = now,
  }

  // ---------------------------------------------------------------- promises

  action promiseCreate(req: CreateReq): bool = all {
    not(ids.contains(req.id)),
    onlyObjects(objects.put(req.id, new(req, now))),
  }

  action promiseSettle(req: SettleReq): bool =
    val old = live.get(req.id)
    all {
      ids.contains(req.id),
      old.promise.state == Pending,
      onlyObjects(objects.put(req.id,
        { promise: { ...old.promise, state: req.state, value: req.value,
                     settledAt: now },
          task:    old.task.settled() })),
    }

  /// A promise waits on a promise. Only a targeted promise can be woken, and
  /// only an external promise is worth waiting on -- what settles it is not
  /// this server.
  action promiseRegisterCallback(req: CallbackReq): bool =
    val awaited = live.get(req.awaited)
    val awaiter = live.get(req.awaiter)
    all {
      ids.contains(req.awaited),
      ids.contains(req.awaiter),
      awaiter.promise.tags.targeted,
      isExternal(awaited.promise),
      awaited.promise.state == Pending,
      awaiter.promise.state == Pending,
      onlyObjects(objects.put(req.awaited, awaited.withCallback(req.awaiter))),
    }

  /// An address waits on a promise. Same door, no awaiter.
  action promiseRegisterListener(req: ListenerReq): bool =
    val old = live.get(req.awaited)
    all {
      ids.contains(req.awaited),
      isExternal(old.promise),
      old.promise.state == Pending,
      onlyObjects(objects.put(req.awaited, old.withListener(req.address))),
    }

  // ------------------------------------------------------------------- tasks

  /// Create and acquire in one request: either the promise is new -- and the
  /// caller holds its task the moment it exists -- or it is already there and
  /// its task was going begging.
  action taskCreate(req: TaskCreateReq): bool =
    val born = new(req.act, now)
    val old  = live.get(req.act.id)
    all {
      req.act.tags.targeted,
      any {
        all {
          not(ids.contains(req.act.id)),
          onlyObjects(objects.put(req.act.id,
            if (born.promise.state == Pending)
              born.withTask(born.task.acquiredBy(req.pid, req.ttl, now))
            else
              born)),
        },
        all {
          ids.contains(req.act.id),
          old.promise.tags.targeted,
          old.task.state == TaskPending,
          onlyObjects(objects.put(req.act.id,
            old.withTask(old.task.acquiredBy(req.pid, req.ttl, now)))),
        },
      },
    }

  action taskAcquire(req: TaskAcquireReq): bool =
    val old = live.get(req.id)
    all {
      ids.contains(req.id),
      old.task.state == TaskPending,
      old.promise.state == Pending,
      old.task.version == req.version,
      onlyObjects(objects.put(req.id,
        old.withTask(old.task.acquiredBy(req.pid, req.ttl, now)))),
    }

  /// A worker still holding its lease writes SOMEWHERE ELSE. The version it
  /// names is the whole content: a worker whose lease was taken names a
  /// version that no longer exists, and its write does not happen.
  action taskFence(ref: TaskRef): bool =
    val old = live.get(ref.id)
    all {
      ids.contains(ref.id),
      old.task.state == TaskAcquired,
      old.promise.state == Pending,
      old.task.version == ref.version,
      any {
        nondet req = CreateReqs.oneOf() all { req.id != ref.id, promiseCreate(req) },
        nondet req = SettleReqs.oneOf() all { req.id != ref.id, promiseSettle(req) },
      },
    }

  /// One request, many leases: a worker renews everything it still holds, and
  /// says nothing about what it does not.
  action taskHeartbeat(req: TaskBeatReq): bool =
    val beat = ids.filter(i =>
      val o = live.get(i)
      and {
        req.tasks.exists(rf => rf.id == i and rf.version == o.task.version),
        o.task.state == TaskAcquired,
        o.task.pid == req.pid,
        o.promise.state == Pending,
      })
    all {
      beat != Set(),
      onlyObjects(beat.fold(objects, (acc, i) =>
        val o = live.get(i)
        acc.put(i, o.withTask({ ...o.task, expiresAt: now + o.task.ttl })))),
    }

  /// Park a task on the promises it is waiting for, registering itself on each.
  /// If any of them has ALREADY settled there is nothing to wait for: the task
  /// keeps its lease and only its buffered wakeups are cleared, because it is
  /// about to be told.
  action taskSuspend(req: TaskSuspendReq): bool =
    val aw  = req.actions.map(a => a.awaited)
    val old = live.get(req.id)
    all {
      req.actions != Set(),
      not(aw.contains(req.id)),
      aw.forall(a => a.origin == req.id.origin),
      ids.contains(req.id),
      aw.forall(a => ids.contains(a)),
      old.task.state == TaskAcquired,
      old.promise.state == Pending,
      old.task.version == req.version,
      aw.forall(a => isExternal(live.get(a).promise)),
      if (aw.exists(a => live.get(a).promise.state != Pending))
        onlyObjects(objects.put(req.id,
          old.withTask({ ...old.task, resumes: Set() })))
      else
        onlyObjects(aw.fold(
          objects.put(req.id, old.withTask(old.task.suspended())),
          (acc, a) => acc.put(a, live.get(a).withCallback(req.id)))),
    }

  /// Settle the promise and retire the task in one write. This is the only
  /// place a worker gets to say what its promise came to.
  action taskFulfill(req: TaskFulfillReq): bool =
    val old = live.get(req.id)
    all {
      ids.contains(req.id),
      old.task.state == TaskAcquired,
      old.promise.state == Pending,
      old.task.version == req.version,
      onlyObjects(objects.put(req.id,
        { promise: { ...old.promise, state: req.act.state, value: req.act.value,
                     settledAt: now },
          task:    old.task.settled() })),
    }

  /// Hand it back, due now.
  action taskRelease(req: TaskRef): bool =
    val old = live.get(req.id)
    all {
      ids.contains(req.id),
      old.task.state == TaskAcquired,
      old.promise.state == Pending,
      old.task.version == req.version,
      onlyObjects(objects.put(req.id, old.withTask(old.task.pendingAt(now)))),
    }

  /// Stop dispatching this task, without settling its promise. No version:
  /// halting is not the worker's move.
  action taskHalt(id: Id): bool =
    val old = live.get(id)
    all {
      ids.contains(id),
      not(Set(TaskNone, TaskFulfilled, TaskHalted).contains(old.task.state)),
      onlyObjects(objects.put(id, old.withTask(old.task.halted()))),
    }

  action taskContinue(id: Id): bool =
    val old = live.get(id)
    all {
      ids.contains(id),
      old.task.state == TaskHalted,
      old.promise.state == Pending,
      onlyObjects(objects.put(id, old.withTask(old.task.pendingAt(now)))),
    }

  // --------------------------------------------------------------- deadlines

  /// Writing down what `project` already says. The lapse is not a decision --
  /// it happened when the deadline passed -- so this is the ONE action that
  /// reads `objects` raw: it exists to make the store agree with the protocol.
  action processPromiseTimeout: bool =
    nondet i = Ids.oneOf()
    val old = objects.get(i)
    all {
      ids.contains(i),
      old.promise.state == Pending,
      old.promise.timeoutAt <= now,
      onlyObjects(objects.put(i, project(old, now))),
    }

  /// The lease ran out. The task goes back on the pile, due now -- the worker
  /// may still be alive and may still write, which is what the version is for.
  action processLeaseTimeout: bool =
    nondet i = Ids.oneOf()
    val old = live.get(i)
    all {
      ids.contains(i),
      old.task.state == TaskAcquired,
      old.task.expiresAt != NoTime,
      old.task.expiresAt <= now,
      old.promise.state == Pending,
      onlyObjects(objects.put(i, old.withTask(old.task.pendingAt(now)))),
    }

  /// Dispatch, and arm the next attempt. The message names the version, so a
  /// worker can tell whether the task it was handed is still the task it has.
  action processRetryTimeout: bool =
    nondet i = Ids.oneOf()
    val old = live.get(i)
    val msg = { address: old.promise.tags.target,
                message: Execute({ id: i, version: old.task.version }) }
    all {
      ids.contains(i),
      old.task.state == TaskPending,
      old.task.retryAt != NoTime,
      old.task.retryAt <= now,
      old.promise.state == Pending,
      objectsAndSend(objects.put(i,
        old.withTask({ ...old.task, retryAt: now + RetryTimeout })), msg),
    }

  // ----------------------------------------------------------- settling news

  /// Tell an address, once, and forget it.
  action processListener: bool =
    nondet i = Ids.oneOf()
    nondet a = Addresses.oneOf()
    val awaited = live.get(i)
    val msg = { address: a,
                message: Unblock({ id: i, state: awaited.promise.state }) }
    all {
      ids.contains(i),
      awaited.promise.listeners.contains(a),
      awaited.promise.state != Pending,
      objectsAndSend(objects.put(i, awaited.withoutListener(a)), msg),
    }

  /// Tell an awaiter, once. A suspended awaiter wakes up and is due now; a
  /// running one only has the news buffered, because it is not parked and
  /// waking it would mean nothing; and one that is gone or finished is simply
  /// struck off.
  action processCallback: bool =
    nondet i = Ids.oneOf()
    nondet w = Ids.oneOf()
    val awaited = live.get(i)
    val awaiter = live.get(w)
    val struck  = objects.put(i, awaited.withoutCallback(w))
    all {
      ids.contains(i),
      awaited.promise.callbacks.contains(w),
      awaited.promise.state != Pending,
      onlyObjects(
        if (not(ids.contains(w)))
          struck
        else if (Set(TaskNone, TaskFulfilled).contains(awaiter.task.state))
          struck
        else if (awaiter.task.state == TaskSuspended)
          struck.put(w, awaiter.withTask(
            { ...awaiter.task.pendingAt(now), resumes: Set(i) }))
        else
          struck.put(w, awaiter.withTask(
            { ...awaiter.task, resumes: awaiter.task.resumes.union(Set(i)) }))),
    }

  // --------------------------------------------------------------- the clock

  action clock: bool = all {
    now < MaxTime,
    now' = now + 1,
    objects' = objects,
    outbox'  = outbox,
  }

  // --------------------------------------------------------------- the machine

  action init = all {
    objects' = Map(),
    outbox'  = Set(),
    now'     = 0,
  }

  action step = any {
    nondet req = CreateReqs.oneOf()      promiseCreate(req),
    nondet req = SettleReqs.oneOf()      promiseSettle(req),
    nondet req = CallbackReqs.oneOf()    promiseRegisterCallback(req),
    nondet req = ListenerReqs.oneOf()    promiseRegisterListener(req),
    nondet req = TaskCreateReqs.oneOf()  taskCreate(req),
    nondet req = TaskAcquireReqs.oneOf() taskAcquire(req),
    nondet req = TaskRefs.oneOf()        taskFence(req),
    nondet req = TaskBeatReqs.oneOf()    taskHeartbeat(req),
    nondet req = TaskSuspendReqs.oneOf() taskSuspend(req),
    nondet req = TaskFulfillReqs.oneOf() taskFulfill(req),
    nondet req = TaskRefs.oneOf()        taskRelease(req),
    nondet id  = Ids.oneOf()             taskHalt(id),
    nondet id  = Ids.oneOf()             taskContinue(id),
    processPromiseTimeout,
    processLeaseTimeout,
    processRetryTimeout,
    processListener,
    processCallback,
    clock,
  }

  // ------------------------------------------------------------- what holds

  /// Every object in the store, as written.
  val stored: Set[Object] = ids.map(i => objects.get(i))

  /// What Quint's types do not already say.
  val typeOk = and {
    Time.contains(now),
    ids.subseteq(Ids),
    outbox.forall(a => outbox.forall(b => msgKey(a) == msgKey(b) implies a == b)),
    stored.forall(o => o.task.state == TaskNone implies o.task == noTask),
  }

  val well_formed_promise_created_at_lte_timeout_at =
    stored.forall(o => o.promise.createdAt <= o.promise.timeoutAt)

  val well_formed_promise_settled_at_iff_not_pending =
    stored.forall(o => (o.promise.state != Pending) iff (o.promise.settledAt != NoTime))

  val well_formed_promise_pending_has_no_value =
    stored.forall(o => o.promise.state == Pending implies o.promise.value == NoValue)

  val well_formed_promise_settled_at_lte_timeout_at =
    stored.forall(o =>
      o.promise.settledAt != NoTime implies o.promise.settledAt <= o.promise.timeoutAt)

  val well_formed_task_pending_iff_has_retry_at =
    stored.forall(o => o.task.state != TaskNone implies
      ((o.task.state == TaskPending) iff (o.task.retryAt != NoTime)))

  val well_formed_task_acquired_iff_has_expires_at =
    stored.forall(o => o.task.state != TaskNone implies
      ((o.task.state == TaskAcquired) iff (o.task.expiresAt != NoTime)))

  val consistent_settled_promise_has_fulfilled_task =
    stored.forall(o =>
      (o.promise.state != Pending and o.task.state != TaskNone)
        implies o.task.state == TaskFulfilled)

  val consistent_settled_task_promise_settled =
    stored.forall(o => o.task.state == TaskFulfilled implies o.promise.state != Pending)

  val consistent_task_iff_targeted_promise =
    stored.forall(o => (o.task.state != TaskNone) iff o.promise.tags.targeted)

  /// A promise and its task are ONE object, so one write moves both. No
  /// interleaving can catch them disagreeing -- which is a claim about the
  /// state shape, and the reason it is worth stating separately.
  val unitCoherent =
    stored.forall(o => not(and {
      o.promise.state != Pending,
      not(Set(TaskNone, TaskFulfilled).contains(o.task.state)),
    }))

  /// An awaiter and the promise it awaits live at one origin. This is what
  /// makes an await local, and a server free to shard on the origin.
  val sameOrigin =
    ids.forall(i => objects.get(i).promise.callbacks.forall(w => w.origin == i.origin))

  val allInvariants = and {
    typeOk,
    well_formed_promise_created_at_lte_timeout_at,
    well_formed_promise_settled_at_iff_not_pending,
    well_formed_promise_pending_has_no_value,
    well_formed_promise_settled_at_lte_timeout_at,
    well_formed_task_pending_iff_has_retry_at,
    well_formed_task_acquired_iff_has_expires_at,
    consistent_settled_promise_has_fulfilled_task,
    consistent_settled_task_promise_settled,
    consistent_task_iff_targeted_promise,
    unitCoherent,
    sameOrigin,
  }
}
