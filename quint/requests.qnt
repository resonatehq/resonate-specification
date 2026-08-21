/// THE VOCABULARY. What an object is, what a request is, and what a message
/// is. Nothing here decides anything: no handler, no transition, no state.
///
/// The Quint reading of `tla/Requests.tla`, narrowed to what the abstract
/// machine actually speaks: the alphabet is not a value here, because
/// `abstract` quantifies over requests directly.
module requests {

  // ---------------------------------------------------------------- the atoms

  type Origin  = str
  type Rest    = str
  type Address = str
  type Pid     = str
  type Value   = str

  /// An identifier is two halves: the origin is what a server may shard on.
  type Id = { origin: Origin, rest: Rest }

  type Tags = {
    targeted: bool,     // has a task: someone is meant to run this
    timer:    bool,     // its deadline is the point, so lapsing RESOLVES it
    external: bool,     // someone outside settles it
    target:   Address,
    delay:    int,
  }

  /// ABSENCE IS A VALUE, and it has one name. `tla/Requests.tla` needs four --
  /// `NoTime`, `NoPid`, `NoAddr`, `NoValue` -- because TLA+ has no sum type to
  /// put absence in, and one sentinel answering four different questions is
  /// worse than four sentinels answering one each. Quint has the sum type, so
  /// the question is answered once, by the type.
  ///
  /// An absent TASK is still not one of these. A task in state `TaskNone` is the
  /// honest reading: whether a promise is targeted is part of the unit's state,
  /// not a hole in it.
  type Option[a] = Some(a) | None

  /// A deadline that has come. `None` is never due, which is a fact of the type
  /// rather than a guard anybody has to remember to write.
  pure def due(d: Option[int], t: int): bool =
    match d { | Some(at) => at <= t | None => false }

  pure def mapOption(o: Option[a], f: (a) => b): Option[b] =
    match o { | Some(x) => Some(f(x)) | None => None }

  // --------------------------------------------------------------- the object

  type PromiseState =
    Pending | Resolved | Rejected | RejectedCanceled | RejectedTimedout

  type TaskState =
    TaskNone | TaskPending | TaskAcquired | TaskSuspended | TaskHalted | TaskFulfilled

  type Promise = {
    state:     PromiseState,
    param:     Value,
    value:     Option[Value],   // a timed-out promise settles with none
    tags:      Tags,
    timeoutAt: int,             // deadline -- armed as "promise"
    createdAt: int,
    settledAt: Option[int],
    callbacks: Set[Id],         // awaiters to resume when this settles
    listeners: Set[Address],    // addresses to notify when this settles
  }

  type Task = {
    state:     TaskState,
    version:   int,             // the fencing token
    ttl:       Option[int],     // the WORKER's number: the lease it asked for
    pid:       Option[Pid],
    expiresAt: Option[int],     // deadline -- armed as "lease"
    retryAt:   Option[int],     // deadline -- armed as "retry"
    resumes:   Set[Id],         // triggers buffered while not suspended
  }

  /// A promise and its task are ONE object. That is the whole of the state
  /// shape, and most of what makes the machine short.
  type Object = { promise: Promise, task: Task }

  pure val noTask: Task = {
    state: TaskNone, version: 0, ttl: None, pid: None,
    expiresAt: None, retryAt: None, resumes: Set(),
  }

  /// Only an external promise may be awaited: something outside this server
  /// decides when it settles.
  pure def isExternal(p: Promise): bool =
    p.tags.external or p.tags.targeted or p.tags.timer

  // ------------------------------------------------------------- the deadlines

  /// Three deadlines, all of them FIELDS on the object. An executor that keeps
  /// an index keeps it of these; the protocol just reads them.
  type DeadlineKind = PromiseDeadline | LeaseDeadline | RetryDeadline

  type Entry = { at: int, id: Id, kind: DeadlineKind }

  pure val DeadlineKinds = Set(PromiseDeadline, LeaseDeadline, RetryDeadline)

  pure def deadline(o: Object, k: DeadlineKind): Option[int] =
    match k {
      | PromiseDeadline => if (o.promise.state == Pending) Some(o.promise.timeoutAt) else None
      | LeaseDeadline   => o.task.expiresAt
      | RetryDeadline   => o.task.retryAt
    }

  // -------------------------------------------------------------- the outbox

  type Message =
    Execute({ id: Id, version: int }) | Unblock({ id: Id, state: PromiseState })

  type OutEntry = { address: Address, message: Message }
  type MsgKey   = { kind: str, id: Id, address: Option[Address] }

  /// The outbox holds at most one entry per key: a second Execute for a task
  /// replaces the first, an Unblock is per (promise, address).
  pure def msgKey(e: OutEntry): MsgKey =
    match e.message {
      | Execute(m) => { kind: "execute", id: m.id, address: None }
      | Unblock(m) => { kind: "unblock", id: m.id, address: Some(e.address) }
    }

  pure def send(box: Set[OutEntry], msg: OutEntry): Set[OutEntry] =
    box.filter(o => msgKey(o) != msgKey(msg)).union(Set(msg))

  // ------------------------------------------------------------- the requests

  type CreateReq   = { id: Id, timeoutAt: int, param: Value, tags: Tags }
  type SettleReq   = { id: Id, state: PromiseState, value: Value }
  type CallbackReq = { awaited: Id, awaiter: Id }
  type ListenerReq = { awaited: Id, address: Address }
  type TaskRef     = { id: Id, version: int }

  // `action` is a Quint keyword, so the field the TLA calls `action` is `act`.
  type TimeoutReq       = { id: Id, kind: DeadlineKind }
  type ListenerDrainReq = { id: Id, address: Address }
  type CallbackDrainReq = { id: Id, awaiter: Id }

  /// A fenced write is a create or a settle, carried by the task that fences it.
  type FenceAct = FenceCreate(CreateReq) | FenceSettle(SettleReq)

  pure def fencedId(a: FenceAct): Id =
    match a { | FenceCreate(r) => r.id | FenceSettle(r) => r.id }

  type TaskFenceReq   = { id: Id, version: int, act: FenceAct }
  type TaskCreateReq  = { pid: Pid, ttl: int, act: CreateReq }
  type TaskAcquireReq = { id: Id, version: int, pid: Pid, ttl: int }
  type TaskBeatReq    = { pid: Pid, tasks: Set[TaskRef] }
  type TaskSuspendReq = { id: Id, version: int, actions: Set[CallbackReq] }
  type TaskFulfillReq = { id: Id, version: int, act: SettleReq }

  // ----------------------------------------------------------------- the model
  //
  // `tla/AbstractAction.cfg`, inlined: small enough to check and large enough
  // to interleave. One origin with two rests gives two objects that share an
  // origin; a second origin is what tests the other half of `sameOrigin`.

  pure val Origins   = Set("o1")
  pure val Rests     = Set("a", "b")
  pure val Addresses = Set("addr1")
  pure val Pids      = Set("pid1")
  pure val Values    = Set("val")
  pure val Ttls      = Set(1)

  pure val RetryTimeout = 2
  pure val MaxTime      = 1
  pure val MaxVersion   = 1

  pure val Time     = 0.to(MaxTime)
  pure val Versions = 0.to(MaxVersion)

  pure val Ids: Set[Id] =
    tuples(Origins, Rests).map(((o, r)) => { origin: o, rest: r })

  /// Four shapes of promise: plain, external, targeted, timer.
  pure val TagsSet: Set[Tags] =
    Addresses.map(a => Set(
      { targeted: false, timer: false, external: false, target: a, delay: 0 },
      { targeted: false, timer: false, external: true,  target: a, delay: 0 },
      { targeted: true,  timer: false, external: false, target: a, delay: 0 },
      { targeted: false, timer: true,  external: false, target: a, delay: 0 },
    )).flatten()

  pure val SettleStates = Set(Resolved, Rejected, RejectedCanceled)

  pure val CreateReqs: Set[CreateReq] =
    tuples(Ids, Time, Values, TagsSet)
      .map(((id, timeoutAt, param, tags)) =>
        { id: id, timeoutAt: timeoutAt, param: param, tags: tags })

  pure val SettleReqs: Set[SettleReq] =
    tuples(Ids, SettleStates, Values)
      .map(((id, state, value)) => { id: id, state: state, value: value })

  /// An awaiter is a promise, not a client -- and both ends live at one origin,
  /// which is the door the Lean is missing and the reason a server may shard.
  pure val CallbackReqs: Set[CallbackReq] =
    tuples(Ids, Ids)
      .filter(((awaited, awaiter)) =>
        awaited != awaiter and awaited.origin == awaiter.origin)
      .map(((awaited, awaiter)) => { awaited: awaited, awaiter: awaiter })

  pure val ListenerReqs: Set[ListenerReq] =
    tuples(Ids, Addresses)
      .map(((awaited, address)) => { awaited: awaited, address: address })

  pure val TaskRefs: Set[TaskRef] =
    tuples(Ids, Versions).map(((id, version)) => { id: id, version: version })

  pure val TaskCreateReqs: Set[TaskCreateReq] =
    tuples(Pids, Ttls, CreateReqs)
      .map(((pid, ttl, act)) => { pid: pid, ttl: ttl, act: act })

  pure val TaskAcquireReqs: Set[TaskAcquireReq] =
    tuples(Ids, Versions, Pids, Ttls)
      .map(((id, version, pid, ttl)) =>
        { id: id, version: version, pid: pid, ttl: ttl })

  pure val TaskBeatReqs: Set[TaskBeatReq] =
    tuples(Pids, TaskRefs.powerset())
      .map(((pid, tasks)) => { pid: pid, tasks: tasks })

  pure val TaskSuspendReqs: Set[TaskSuspendReq] =
    tuples(Ids, Versions, CallbackReqs.powerset())
      .map(((id, version, actions)) =>
        { id: id, version: version, actions: actions })

  pure val TaskFulfillReqs: Set[TaskFulfillReq] =
    tuples(Ids, Versions, SettleReqs)
      .map(((id, version, act)) => { id: id, version: version, act: act })

  // ---------------------------------------------------------------- the alphabet
  //
  // The events both machines speak. `abstract` and `concrete` are two
  // independent machines, and the refinement asks whether their behaviour lines
  // up -- so they had better be answering the same questions.

  type Event =
      PromiseGet(Id)
    | PromiseCreate(CreateReq)
    | PromiseSettle(SettleReq)
    | PromiseRegisterCallback(CallbackReq)
    | PromiseRegisterListener(ListenerReq)
    | TaskGet(Id)
    | TaskCreate(TaskCreateReq)
    | TaskAcquire(TaskAcquireReq)
    | TaskFence(TaskFenceReq)
    | TaskHeartbeat(TaskBeatReq)
    | TaskSuspend(TaskSuspendReq)
    | TaskFulfill(TaskFulfillReq)
    | TaskRelease(TaskRef)
    | TaskHalt(Id)
    | TaskContinue(Id)
    | Timeout(TimeoutReq)
    | ListenerDrain(ListenerDrainReq)
    | CallbackDrain(CallbackDrainReq)

  pure val FenceActs: Set[FenceAct] =
    CreateReqs.map(r => FenceCreate(r)).union(SettleReqs.map(r => FenceSettle(r)))

  pure val TaskFenceReqs: Set[TaskFenceReq] =
    tuples(Ids, Versions, FenceActs)
      .map(((id, version, act)) => { id: id, version: version, act: act })

  pure val TimeoutReqs: Set[TimeoutReq] =
    tuples(Ids, DeadlineKinds).map(((id, kind)) => { id: id, kind: kind })

  pure val CallbackDrainReqs: Set[CallbackDrainReq] =
    CallbackReqs.map(r => { id: r.awaited, awaiter: r.awaiter })

  pure val ListenerDrainReqs: Set[ListenerDrainReq] =
    ListenerReqs.map(r => { id: r.awaited, address: r.address })

  /// What a client may ask for.
  pure val ExternalEvents: Set[Event] =
    Ids.map(i => PromiseGet(i))
      .union(CreateReqs.map(r => PromiseCreate(r)))
      .union(SettleReqs.map(r => PromiseSettle(r)))
      .union(CallbackReqs.map(r => PromiseRegisterCallback(r)))
      .union(ListenerReqs.map(r => PromiseRegisterListener(r)))
      .union(Ids.map(i => TaskGet(i)))
      .union(TaskCreateReqs.map(r => TaskCreate(r)))
      .union(TaskAcquireReqs.map(r => TaskAcquire(r)))
      .union(TaskFenceReqs.map(r => TaskFence(r)))
      .union(TaskBeatReqs.map(r => TaskHeartbeat(r)))
      .union(TaskSuspendReqs.map(r => TaskSuspend(r)))
      .union(TaskFulfillReqs.map(r => TaskFulfill(r)))
      .union(TaskRefs.map(r => TaskRelease(r)))
      .union(Ids.map(i => TaskHalt(i)))
      .union(Ids.map(i => TaskContinue(i)))

  /// What the server owes itself: a deadline that has come due, and a settled
  /// promise that still carries a name it has not answered.
  pure val InternalEvents: Set[Event] =
    TimeoutReqs.map(r => Timeout(r))
      .union(ListenerDrainReqs.map(r => ListenerDrain(r)))
      .union(CallbackDrainReqs.map(r => CallbackDrain(r)))

  pure val Events: Set[Event] = ExternalEvents.union(InternalEvents)
}
