/// THE EXECUTOR. The same protocol under the Verus executor's discipline: ONE
/// DOCUMENT PER ORIGIN, and a compare-and-swap on it.
///
/// `abstract` decides and writes in one step. This machine reads a
/// document, decides against it, and lands the decision later -- so the gap
/// between the two is a place another step can get into, and the etag is what
/// keeps a stale decision out.
///
/// THE HANDLERS ARE ITS OWN, ON PURPOSE. Borrowing `abstract`'s would
/// make the refinement unaskable: the two machines would agree by construction.
/// Only the VOCABULARY is shared, through `requests` -- what an object is, what
/// a request is, which events exist. Same protocol being spoken about, not the
/// same machine speaking.
///
/// The Quint reading of `tla/Concrete.tla`.
module concrete {
  import requests.* from "./requests"

  // ----------------------------------------------------------------- the model

  pure val Rids = Set("q1", "q2")     // how many steps may be in flight at once

  /// The fence, switchable, so the refinement can prove its own necessity.
  pure val Fenced = true

  /// Whether a step may drain what it finds due in the document it is already
  /// holding. Switchable for the same reason.
  pure val Sweeping = true

  // ----------------------------------------------------------------- the shape

  type Rid = str
  type Doc = Id -> Object
  type Env = { objects: Doc, now: int }

  type Effect =
      PutObject({ id: Id, obj: Object })
    | Send({ entry: OutEntry })
    | ArmTimeout({ entry: Entry })
    | DisarmTimeout({ entry: Entry })

  type Phase = Processing | Performing

  /// A step in flight: what it is doing, how far it has got, the document it
  /// decided against and the instant it decided at.
  type Step = {
    ev:      Event,
    phase:   Phase,
    pending: List[Effect],
    expect:  Doc,
    at:      int,
    org:     Origin,
  }

  var docs:     Origin -> Doc     // one document per origin
  var timeouts: Set[Entry]        // the wheel: an index, so nothing has to scan
  var outbox:   Set[OutEntry]
  var steps:    Rid -> Step       // work in flight
  var now:      int

  // ------------------------------------------------------------ record surgery

  pure def lapsed(tags: Tags): PromiseState =
    if (tags.timer) Resolved else RejectedTimedout

  pure def settled(t: Task): Task = { ...t,
    state: if (t.state == TaskNone) TaskNone else TaskFulfilled,
    pid: None, ttl: None, expiresAt: None, retryAt: None, resumes: Set() }

  pure def acquiredBy(t: Task, pid: Pid, ttl: int, at: int): Task = { ...t,
    state: TaskAcquired, version: t.version + 1, ttl: Some(ttl), pid: Some(pid),
    expiresAt: Some(at + ttl), retryAt: None, resumes: Set() }

  pure def pendingAt(t: Task, at: int): Task = { ...t,
    state: TaskPending, pid: None, ttl: None, expiresAt: None, retryAt: Some(at) }

  pure def suspended(t: Task): Task = { ...t,
    state: TaskSuspended, pid: None, ttl: None, expiresAt: None,
    retryAt: None, resumes: Set() }

  pure def halted(t: Task): Task = { ...t,
    state: TaskHalted, pid: None, ttl: None, expiresAt: None, retryAt: None }

  pure def withTask(o: Object, t: Task): Object = { ...o, task: t }

  pure def project(obj: Object, t: int): Object =
    if (obj.promise.state == Pending and obj.promise.timeoutAt <= t)
      { promise: { ...obj.promise, state: lapsed(obj.promise.tags),
                   value: None, settledAt: Some(obj.promise.timeoutAt) },
        task: obj.task.settled() }
    else
      obj

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

  // --------------------------------------------------------------- the effects

  pure val nothing: List[Effect] = []

  pure def putting(i: Id, o: Object): List[Effect] = [PutObject({ id: i, obj: o })]
  pure def saying(e: OutEntry): List[Effect] = [Send({ entry: e })]

  pure def puts(fx: List[Effect]): Set[{ id: Id, obj: Object }] =
    fx.foldl(Set(), (acc, e) => match e { | PutObject(w) => acc.union(Set(w)) | _ => acc })

  pure def says(fx: List[Effect]): Set[OutEntry] =
    fx.foldl(Set(), (acc, e) => match e { | Send(m) => acc.union(Set(m.entry)) | _ => acc })

  /// In order, last wins. The list is the order the writes were decided in.
  pure def putsInto(doc: Doc, fx: List[Effect]): Doc =
    fx.foldl(doc, (acc, e) => match e { | PutObject(w) => acc.put(w.id, w.obj) | _ => acc })

  pure def has(env: Env, i: Id): bool = env.objects.keys().contains(i)
  pure def live(env: Env, i: Id): Object = project(env.objects.get(i), env.now)

  // ------------------------------------------------------------- the handlers
  //
  // Total functions from a request and a document to the effects it justifies.
  // A request that does not apply justifies nothing, which is how this machine
  // says what `abstract` says with a guard.

  /// A read is not a write.
  pure def handlePromiseGet(i: Id, env: Env): List[Effect] = nothing

  pure def handlePromiseCreate(req: CreateReq, env: Env): List[Effect] =
    if (env.has(req.id)) nothing
    else putting(req.id, new(req, env.now))

  pure def handlePromiseSettle(req: SettleReq, env: Env): List[Effect] =
    if (not(env.has(req.id))) nothing
    else
      val old = env.live(req.id)
      if (old.promise.state != Pending) nothing
      else putting(req.id,
        { promise: { ...old.promise, state: req.state, value: Some(req.value),
                     settledAt: Some(env.now) },
          task:    old.task.settled() })

  pure def handlePromiseRegisterCallback(req: CallbackReq, env: Env): List[Effect] =
    if (not(env.has(req.awaited)) or not(env.has(req.awaiter))) nothing
    else
      val awaited = env.live(req.awaited)
      val awaiter = env.live(req.awaiter)
      if (or {
        not(awaiter.promise.tags.targeted),
        not(isExternal(awaited.promise)),
        awaited.promise.state != Pending,
        awaiter.promise.state != Pending,
      }) nothing
      else putting(req.awaited,
        { ...awaited, promise: { ...awaited.promise,
            callbacks: awaited.promise.callbacks.union(Set(req.awaiter)) } })

  pure def handlePromiseRegisterListener(req: ListenerReq, env: Env): List[Effect] =
    if (not(env.has(req.awaited))) nothing
    else
      val old = env.live(req.awaited)
      if (not(isExternal(old.promise)) or old.promise.state != Pending) nothing
      else putting(req.awaited,
        { ...old, promise: { ...old.promise,
            listeners: old.promise.listeners.union(Set(req.address)) } })

  pure def handleTaskGet(i: Id, env: Env): List[Effect] = nothing

  pure def handleTaskCreate(req: TaskCreateReq, env: Env): List[Effect] =
    if (not(req.act.tags.targeted)) nothing
    else if (not(env.has(req.act.id)))
      val born = new(req.act, env.now)
      putting(req.act.id,
        if (born.promise.state == Pending)
          born.withTask(born.task.acquiredBy(req.pid, req.ttl, env.now))
        else born)
    else
      val old = env.live(req.act.id)
      if (not(old.promise.tags.targeted) or old.task.state != TaskPending) nothing
      else putting(req.act.id,
        old.withTask(old.task.acquiredBy(req.pid, req.ttl, env.now)))

  pure def handleTaskAcquire(req: TaskAcquireReq, env: Env): List[Effect] =
    if (not(env.has(req.id))) nothing
    else
      val old = env.live(req.id)
      if (or {
        old.task.state != TaskPending,
        old.promise.state != Pending,
        old.task.version != req.version,
      }) nothing
      else putting(req.id, old.withTask(old.task.acquiredBy(req.pid, req.ttl, env.now)))

  pure def handleTaskFence(req: TaskFenceReq, env: Env): List[Effect] =
    if (not(env.has(req.id))) nothing
    else
      val old = env.live(req.id)
      if (or {
        fencedId(req.act) == req.id,
        old.task.state != TaskAcquired,
        old.promise.state != Pending,
        old.task.version != req.version,
      }) nothing
      else
        match req.act {
          | FenceCreate(r) => handlePromiseCreate(r, env)
          | FenceSettle(r) => handlePromiseSettle(r, env)
        }

  pure def handleTaskHeartbeat(req: TaskBeatReq, env: Env): List[Effect] =
    env.objects.keys()
      .filter(i =>
        val o = env.live(i)
        and {
          req.tasks.exists(rf => rf.id == i and rf.version == o.task.version),
          o.task.state == TaskAcquired,
          o.task.pid == Some(req.pid),
          o.promise.state == Pending,
        })
      .fold(nothing, (acc, i) =>
        val o = env.live(i)
        acc.concat(putting(i, o.withTask({ ...o.task,
          expiresAt: o.task.ttl.mapOption(t => env.now + t) }))))

  pure def handleTaskSuspend(req: TaskSuspendReq, env: Env): List[Effect] =
    val aw = req.actions.map(a => a.awaited)
    if (or {
      req.actions == Set(),
      aw.contains(req.id),
      aw.exists(a => a.origin != req.id.origin),
      not(env.has(req.id)),
      aw.exists(a => not(env.has(a))),
    }) nothing
    else
      val old = env.live(req.id)
      if (or {
        old.task.state != TaskAcquired,
        old.promise.state != Pending,
        old.task.version != req.version,
        aw.exists(a => not(isExternal(env.live(a).promise))),
      }) nothing
      else if (aw.exists(a => env.live(a).promise.state != Pending))
        putting(req.id, old.withTask({ ...old.task, resumes: Set() }))
      else
        aw.fold(putting(req.id, old.withTask(old.task.suspended())),
                (acc, a) =>
                  val awaited = env.live(a)
                  acc.concat(putting(a,
                    { ...awaited, promise: { ...awaited.promise,
                        callbacks: awaited.promise.callbacks.union(Set(req.id)) } })))

  pure def handleTaskFulfill(req: TaskFulfillReq, env: Env): List[Effect] =
    if (not(env.has(req.id))) nothing
    else
      val old = env.live(req.id)
      if (or {
        old.task.state != TaskAcquired,
        old.promise.state != Pending,
        old.task.version != req.version,
      }) nothing
      else putting(req.id,
        { promise: { ...old.promise, state: req.act.state, value: Some(req.act.value),
                     settledAt: Some(env.now) },
          task:    old.task.settled() })

  pure def handleTaskRelease(req: TaskRef, env: Env): List[Effect] =
    if (not(env.has(req.id))) nothing
    else
      val old = env.live(req.id)
      if (or {
        old.task.state != TaskAcquired,
        old.promise.state != Pending,
        old.task.version != req.version,
      }) nothing
      else putting(req.id, old.withTask(old.task.pendingAt(env.now)))

  pure def handleTaskHalt(i: Id, env: Env): List[Effect] =
    if (not(env.has(i))) nothing
    else
      val old = env.live(i)
      if (Set(TaskNone, TaskFulfilled, TaskHalted).contains(old.task.state)) nothing
      else putting(i, old.withTask(old.task.halted()))

  pure def handleTaskContinue(i: Id, env: Env): List[Effect] =
    if (not(env.has(i))) nothing
    else
      val old = env.live(i)
      if (old.task.state != TaskHalted or old.promise.state != Pending) nothing
      else putting(i, old.withTask(old.task.pendingAt(env.now)))

  pure def processPromiseTimeout(i: Id, env: Env): List[Effect] =
    if (not(env.has(i))) nothing
    else
      val old = env.objects.get(i)
      val fresh = project(old, env.now)
      if (fresh != old) putting(i, fresh) else nothing

  pure def processLeaseTimeout(i: Id, env: Env): List[Effect] =
    if (not(env.has(i))) nothing
    else
      val old = env.objects.get(i)
      if (or {
        old.task.state != TaskAcquired,
        not(due(old.task.expiresAt, env.now)),
        project(old, env.now).promise.state != Pending,
      }) nothing
      else putting(i, old.withTask(old.task.pendingAt(env.now)))

  pure def processRetryTimeout(i: Id, env: Env): List[Effect] =
    if (not(env.has(i))) nothing
    else
      val old = env.objects.get(i)
      if (or {
        old.task.state != TaskPending,
        not(due(old.task.retryAt, env.now)),
        project(old, env.now).promise.state != Pending,
      }) nothing
      else
        putting(i, old.withTask({ ...old.task, retryAt: Some(env.now + RetryTimeout) }))
          .concat(saying({ address: old.promise.tags.target,
                           message: Execute({ id: i, version: old.task.version }) }))

  pure def processListener(req: ListenerDrainReq, env: Env): List[Effect] =
    if (not(env.has(req.id))) nothing
    else
      val awaited = env.live(req.id)
      if (awaited.promise.state == Pending
          or not(awaited.promise.listeners.contains(req.address))) nothing
      else
        putting(req.id,
          { ...awaited, promise: { ...awaited.promise,
              listeners: awaited.promise.listeners.exclude(Set(req.address)) } })
          .concat(saying({ address: req.address,
                           message: Unblock({ id: req.id,
                                              state: awaited.promise.state }) }))

  pure def processCallback(req: CallbackDrainReq, env: Env): List[Effect] =
    if (not(env.has(req.id))) nothing
    else
      val awaited = env.live(req.id)
      val struck = putting(req.id,
        { ...awaited, promise: { ...awaited.promise,
            callbacks: awaited.promise.callbacks.exclude(Set(req.awaiter)) } })
      if (awaited.promise.state == Pending
          or not(awaited.promise.callbacks.contains(req.awaiter))) nothing
      else if (not(env.has(req.awaiter))) struck
      else
        val awaiter = env.live(req.awaiter)
        if (Set(TaskNone, TaskFulfilled).contains(awaiter.task.state)) struck
        else if (awaiter.task.state == TaskSuspended)
          struck.concat(putting(req.awaiter, awaiter.withTask(
            { ...awaiter.task.pendingAt(env.now), resumes: Set(req.id) })))
        else
          struck.concat(putting(req.awaiter, awaiter.withTask(
            { ...awaiter.task, resumes: awaiter.task.resumes.union(Set(req.id)) })))

  pure def handle(ev: Event, env: Env): List[Effect] =
    match ev {
      | PromiseGet(i)                => handlePromiseGet(i, env)
      | PromiseCreate(req)           => handlePromiseCreate(req, env)
      | PromiseSettle(req)           => handlePromiseSettle(req, env)
      | PromiseRegisterCallback(req) => handlePromiseRegisterCallback(req, env)
      | PromiseRegisterListener(req) => handlePromiseRegisterListener(req, env)
      | TaskGet(i)                   => handleTaskGet(i, env)
      | TaskCreate(req)              => handleTaskCreate(req, env)
      | TaskAcquire(req)             => handleTaskAcquire(req, env)
      | TaskFence(req)               => handleTaskFence(req, env)
      | TaskHeartbeat(req)           => handleTaskHeartbeat(req, env)
      | TaskSuspend(req)             => handleTaskSuspend(req, env)
      | TaskFulfill(req)             => handleTaskFulfill(req, env)
      | TaskRelease(req)             => handleTaskRelease(req, env)
      | TaskHalt(i)                  => handleTaskHalt(i, env)
      | TaskContinue(i)              => handleTaskContinue(i, env)
      | Timeout(req)                 =>
          match req.kind {
            | PromiseDeadline => processPromiseTimeout(req.id, env)
            | LeaseDeadline   => processLeaseTimeout(req.id, env)
            | RetryDeadline   => processRetryTimeout(req.id, env)
          }
      | ListenerDrain(req)           => processListener(req, env)
      | CallbackDrain(req)           => processCallback(req, env)
    }

  // ----------------------------------------------------------------- the sweep
  //
  // WHAT IS DUE IS WHAT THE DOCUMENT SAYS IS DUE. Every deadline is a field on
  // an object and the document is already in hand, so there is nothing to ask
  // an index about. The wheel is a TRIGGER: it says wake up and look at this
  // document. It does not decide what the work is.

  pure def drainableTimeouts(doc: Doc, t: int): Set[TimeoutReq] =
    tuples(doc.keys(), DeadlineKinds)
      .map(((i, k)) => { id: i, kind: k })
      .filter(d => due(deadline(doc.get(d.id), d.kind), t))

  /// A settled promise still carrying a name owes that name an answer.
  pure def answerable(doc: Doc, t: int): Set[Id] =
    doc.keys().filter(j =>
      doc.get(j).promise.state != Pending or doc.get(j).promise.timeoutAt <= t)

  pure def drainableListeners(doc: Doc, t: int): Set[ListenerDrainReq] =
    answerable(doc, t)
      .map(i => doc.get(i).promise.listeners.map(a => { id: i, address: a }))
      .flatten()

  pure def drainableCallbacks(doc: Doc, t: int): Set[CallbackDrainReq] =
    answerable(doc, t)
      .map(i => doc.get(i).promise.callbacks.map(w => { id: i, awaiter: w }))
      .flatten()

  type Swept = { doc: Doc, fx: List[Effect] }

  /// The document is threaded, so two drains on one promise do not overwrite
  /// each other's strike. One pass, not a fixpoint.
  pure def advance(st: Swept, out: List[Effect]): Swept =
    { doc: putsInto(st.doc, out), fx: st.fx.concat(out) }

  pure def sweep(doc: Doc, t: int, ts: Set[TimeoutReq], ls: Set[ListenerDrainReq],
                 cs: Set[CallbackDrainReq]): Swept =
    val afterT = ts.fold({ doc: doc, fx: nothing }, (st, d) =>
      st.advance(handle(Timeout(d), { objects: st.doc, now: t })))
    val afterL = ls.fold(afterT, (st, d) =>
      st.advance(processListener(d, { objects: st.doc, now: t })))
    cs.fold(afterL, (st, d) =>
      st.advance(processCallback(d, { objects: st.doc, now: t })))

  // ----------------------------------------------------------------- the wheel
  //
  // MAINTAINING THE INDEX IS THE EXECUTOR'S JOB. The protocol states what a
  // handler writes and stops there -- a deadline is a field. A machine that
  // keeps a wheel has to work out what that write did to the deadlines it
  // indexes, and the only way to know is to compare the document before against
  // the document after.

  pure def was(before: Doc, i: Id, k: DeadlineKind): Option[int] =
    if (before.keys().contains(i)) deadline(before.get(i), k) else None

  pure def armFor(before: Doc, i: Id, obj: Object, k: DeadlineKind): List[Effect] =
    match deadline(obj, k) {
      | None     => nothing
      | Some(at) => if (Some(at) != was(before, i, k))
                      [ArmTimeout({ entry: { at: at, id: i, kind: k } })]
                    else nothing
    }

  pure def disarmFor(before: Doc, i: Id, obj: Object, k: DeadlineKind): List[Effect] =
    match was(before, i, k) {
      | None     => nothing
      | Some(at) => if (Some(at) != deadline(obj, k))
                      [DisarmTimeout({ entry: { at: at, id: i, kind: k } })]
                    else nothing
    }

  /// Arm before the write and disarm after, which is Verus's `sched + put +
  /// ack`. Arming first means a crash between the arm and the write leaves an
  /// entry for an object that is not there -- noise, which the handler
  /// re-checks away. Writing first would leave an object carrying a deadline
  /// nothing will fire -- silence, which nothing recovers from.
  pure def arms(before: Doc, w: Set[{ id: Id, obj: Object }]): List[Effect] =
    w.fold(nothing, (acc, x) =>
      acc.concat(armFor(before, x.id, x.obj, PromiseDeadline))
         .concat(armFor(before, x.id, x.obj, LeaseDeadline))
         .concat(armFor(before, x.id, x.obj, RetryDeadline)))

  pure def disarms(before: Doc, w: Set[{ id: Id, obj: Object }]): List[Effect] =
    w.fold(nothing, (acc, x) =>
      acc.concat(disarmFor(before, x.id, x.obj, PromiseDeadline))
         .concat(disarmFor(before, x.id, x.obj, LeaseDeadline))
         .concat(disarmFor(before, x.id, x.obj, RetryDeadline)))

  // -------------------------------------------------------------- the executor

  /// Which document a step touches. An identifier already carries the origin it
  /// belongs to, which is what the pair-shaped identifier was for. A heartbeat
  /// names a set of tasks and no origin at all, so the executor has to pick;
  /// with one origin that is not a choice.
  pure val anyOrigin: Origin = Origins.fold("", (_, o) => o)

  pure def originOf(ev: Event): Origin =
    match ev {
      | PromiseGet(i)                => i.origin
      | PromiseCreate(req)           => req.id.origin
      | PromiseSettle(req)           => req.id.origin
      | PromiseRegisterCallback(req) => req.awaited.origin
      | PromiseRegisterListener(req) => req.awaited.origin
      | TaskGet(i)                   => i.origin
      | TaskCreate(req)              => req.act.id.origin
      | TaskAcquire(req)             => req.id.origin
      | TaskFence(req)               => req.id.origin
      | TaskHeartbeat(_)             => anyOrigin
      | TaskSuspend(req)             => req.id.origin
      | TaskFulfill(req)             => req.id.origin
      | TaskRelease(req)             => req.id.origin
      | TaskHalt(i)                  => i.origin
      | TaskContinue(i)              => i.origin
      | Timeout(req)                 => req.id.origin
      | ListenerDrain(req)           => req.id.origin
      | CallbackDrain(req)           => req.id.origin
    }

  pure def fresh(ev: Event): Step =
    { ev: ev, phase: Processing, pending: nothing, expect: Map(), at: 0,
      org: originOf(ev) }

  pure def without(m: Rid -> Step, r: Rid): Rid -> Step =
    m.keys().exclude(Set(r)).mapBy(k => m.get(k))

  val free: Set[Rid] = Rids.exclude(steps.keys())

  /// THE ASYMMETRY, and it is the point of having two machines. Upstairs an
  /// internal step is available whenever the DEADLINE VALUES ON AN OBJECT allow
  /// it. Down here it is available only when the WHEEL holds an armed entry for
  /// it. So this machine is strictly more restricted -- free for safety, and
  /// the whole risk for liveness, which is why `wheelComplete` is not a side
  /// condition somebody thought to write down.
  def fires(ev: Event): bool =
    match ev {
      | Timeout(d) => timeouts.exists(e => e.id == d.id and e.kind == d.kind and e.at <= now)
      | _          => false
    }

  action keepAll = all {
    docs' = docs, timeouts' = timeouts, outbox' = outbox, steps' = steps, now' = now,
  }

  action onlySteps(written: Rid -> Step): bool = all {
    steps' = written, docs' = docs, timeouts' = timeouts, outbox' = outbox, now' = now,
  }

  action submit(ev: Event, r: Rid): bool = onlySteps(steps.put(r, fresh(ev)))

  /// Read ONE DOCUMENT, decide against it, and remember the etag it was read
  /// under -- which here is the document itself.
  action process(r: Rid): bool = {
    val doc = docs.get(steps.get(r).org)
    nondet ts = (if (Sweeping) drainableTimeouts(doc, now).powerset() else Set(Set())).oneOf()
    nondet ls = (if (Sweeping) drainableListeners(doc, now).powerset() else Set(Set())).oneOf()
    nondet cs = (if (Sweeping) drainableCallbacks(doc, now).powerset() else Set(Set())).oneOf()
    processWith(r, ts, ls, cs)
  }

  /// The same, with the drained subset named rather than chosen -- which is how
  /// a trace gets written down.
  action processWith(r: Rid, ts: Set[TimeoutReq], ls: Set[ListenerDrainReq],
                     cs: Set[CallbackDrainReq]): bool = {
    val st  = steps.get(r)
    val doc = docs.get(st.org)
    val swept = sweep(doc, now, ts, ls, cs)
    val fx    = swept.fx.concat(handle(st.ev, { objects: swept.doc, now: now }))
    val landed = putsInto(doc, fx)
    val w = puts(fx).map(p => { id: p.id, obj: landed.get(p.id) })
    all {
      st.phase == Processing,
      onlySteps(steps.put(r, { ...st,
        phase:   Performing,
        pending: arms(doc, w).concat(fx).concat(disarms(doc, w)),
        expect:  doc,
        at:      now })),
    }
  }

  /// ONE STEP, ONE DOCUMENT WRITE. A step lands every `PutObject` it decided on
  /// in a single write, and every message those writes justify with them; only
  /// the wheel effects stay separate, which is the premise the whole model is
  /// here to test.
  ///
  /// A write whose document has moved since the read is REFUSED, and the step
  /// goes back to deciding -- which under the abstraction is nothing at all.
  /// THE FENCE COVERS THE CLOCK AS WELL AS THE DOCUMENT: a decision is only
  /// valid at the instant it was made, and a store etag says nothing about the
  /// clock.
  action perform(r: Rid): bool = {
    val st = steps.get(r)
    val o  = st.org
    val doc = docs.get(o)
    val sent = says(st.pending)
    all {
      st.phase == Performing,
      if (st.pending == nothing)
        onlySteps(steps.without(r))
      else
        match st.pending.head() {
          | PutObject(_) =>
              if (not(Fenced) or (doc == st.expect and now == st.at))
                all {
                  docs' = docs.put(o, putsInto(doc, st.pending)),
                  outbox' = outbox
                    .filter(x => not(sent.exists(m => msgKey(x) == msgKey(m))))
                    .union(sent),
                  steps' = steps.put(r, { ...st,
                    pending: st.pending.tail().select(e =>
                      match e { | PutObject(_) => false | Send(_) => false | _ => true }) }),
                  timeouts' = timeouts,
                  now' = now,
                }
              else
                onlySteps(steps.put(r, { ...st, phase: Processing, pending: nothing }))
          | ArmTimeout(a) => all {
              timeouts' = timeouts.union(Set(a.entry)),
              steps' = steps.put(r, { ...st, pending: st.pending.tail() }),
              docs' = docs, outbox' = outbox, now' = now,
            }
          | DisarmTimeout(a) => all {
              timeouts' = timeouts.exclude(Set(a.entry)),
              steps' = steps.put(r, { ...st, pending: st.pending.tail() }),
              docs' = docs, outbox' = outbox, now' = now,
            }
          | Send(m) => all {
              outbox' = outbox.send(m.entry),
              steps' = steps.put(r, { ...st, pending: st.pending.tail() }),
              docs' = docs, timeouts' = timeouts, now' = now,
            }
        },
    }
  }

  /// Work may be destroyed at any point. A crash makes a partial application
  /// PERMANENT; it does not make one possible -- interleaving already does.
  action crash(r: Rid): bool = onlySteps(steps.without(r))

  action clock = all {
    now < MaxTime,
    now' = now + 1,
    docs' = docs, timeouts' = timeouts, outbox' = outbox, steps' = steps,
  }

  action init = all {
    docs'     = Origins.mapBy(o => Map()),
    timeouts' = Set(),
    outbox'   = Set(),
    steps'    = Map(),
    now'      = 0,
  }

  action step = any {
    nondet ev = ExternalEvents.oneOf()
    nondet r  = Rids.oneOf()
    all { free.contains(r), submit(ev, r) },

    nondet ev = InternalEvents.oneOf()
    nondet r  = Rids.oneOf()
    all { free.contains(r), fires(ev), submit(ev, r) },

    nondet r = Rids.oneOf() all { steps.keys().contains(r), process(r) },
    nondet r = Rids.oneOf() all { steps.keys().contains(r), perform(r) },
    nondet r = Rids.oneOf() all { steps.keys().contains(r), crash(r) },
    clock,
  }

  // ------------------------------------------------------ the abstraction

  /// What a chunked store denotes: the flat one that forgets the chunking.
  /// The etags denote NOTHING, and that is the point of them -- a fence is
  /// machinery for keeping a promise the abstract machine states without it.
  val objects: Id -> Object =
    Origins.map(o => docs.get(o).keys()).flatten().mapBy(i => docs.get(i.origin).get(i))

  // ------------------------------------------------------------- what holds

  /// The wheel holds nothing stale. This one FAILS, and should: arming before
  /// writing admits an entry for an object that is not there yet.
  val wheelSound =
    timeouts.forall(e => and {
      objects.keys().contains(e.id),
      deadline(objects.get(e.id), e.kind) == Some(e.at),
    })

  /// Every deadline an object carries is one the wheel will fire. THIS is the
  /// one that matters: a deadline nothing holds is a timeout that never fires.
  val wheelComplete =
    tuples(objects.keys(), DeadlineKinds).forall(((i, k)) =>
      match deadline(objects.get(i), k) {
        | None     => true
        | Some(at) => timeouts.contains({ at: at, id: i, kind: k })
      })

  /// A step that has written part of what it decided and still holds the rest.
  val splitWrite =
    steps.keys().exists(r =>
      val st = steps.get(r)
      and {
        st.phase == Performing,
        docs.get(st.org) != st.expect,
        st.pending.select(e => match e { | PutObject(_) => true | _ => false }) != nothing,
      })

  val twoPuts =
    steps.keys().exists(r =>
      steps.get(r).pending.select(e =>
        match e { | PutObject(_) => true | _ => false }).length() > 1)

  val sweptAndHandled =
    steps.keys().exists(r =>
      val st = steps.get(r)
      st.phase == Performing and
        puts(st.pending).map(p => p.id).size() > 1)

  // ------------------------------------------------------------ not vacuity
  //
  // Random search rarely walks this far: a dispatched message is ten aligned
  // steps from an empty store, and every submit picks one event out of two
  // hundred. So the path is written down instead -- arm, fire, decide, land --
  // which is the same evidence and a better record.

  pure val targeted: Tags =
    { targeted: true, timer: false, external: false, target: "addr1", delay: 0 }

  pure val idB: Id = { origin: "o1", rest: "b" }
  pure val createB: CreateReq = { id: idB, timeoutAt: 1, param: "val", tags: targeted }

  run dispatchesExecuteTest =
    init
      .then(submit(PromiseCreate(createB), "q1"))
      .then(processWith("q1", Set(), Set(), Set()))
      .expect(steps.get("q1").pending.length() == 3)   // arm promise, arm retry, put
      .then(perform("q1"))
      .then(perform("q1"))
      .expect(timeouts.size() == 2)
      .then(perform("q1"))                             // the write lands
      .expect(objects.keys().contains(idB))
      .expect(wheelComplete)
      .then(perform("q1"))                             // the step retires
      .expect(steps.keys().size() == 0)
      // the retry is armed and due, so the wheel may fire it
      .then(submit(Timeout({ id: idB, kind: RetryDeadline }), "q1"))
      .expect(fires(Timeout({ id: idB, kind: RetryDeadline })))
      .then(processWith("q1", Set(), Set(), Set()))
      .then(perform("q1"))                             // re-arm at now + RetryTimeout
      .then(perform("q1"))                             // write and say, together
      .expect(outbox.size() == 1)
      .expect(objects.get(idB).task.retryAt == Some(RetryTimeout))
}
