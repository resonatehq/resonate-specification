/// THE VOCABULARY. What an object is, what a request is, and what a message
/// is. Nothing here decides anything: no handler, no transition, no state.
///
/// The Quint reading of `tla/Requests.tla`, narrowed to what the abstract
/// machine actually speaks: the alphabet is not a value here, because
/// `abstractAction` quantifies over requests directly.
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

  /// There is no `None`. One value standing for absence answers four different
  /// questions at once, so each gets its own: an absent instant is `NoTime`, an
  /// absent worker is `NoPid`, an absent address is `NoAddr`, an absent value is
  /// `NoValue` -- and an absent task is a task in state `TaskNone`, which is the
  /// honest reading: whether a promise is targeted is part of the unit's state,
  /// not a hole in it.
  pure val NoTime  = -1
  pure val NoPid   = "nopid"
  pure val NoAddr  = "noaddr"
  pure val NoValue = "noval"

  // --------------------------------------------------------------- the object

  type PromiseState =
    Pending | Resolved | Rejected | RejectedCanceled | RejectedTimedout

  type TaskState =
    TaskNone | TaskPending | TaskAcquired | TaskSuspended | TaskHalted | TaskFulfilled

  type Promise = {
    state:     PromiseState,
    param:     Value,
    value:     Value,
    tags:      Tags,
    timeoutAt: int,             // deadline -- armed as "promise"
    createdAt: int,
    settledAt: int,             // NoTime while pending
    callbacks: Set[Id],         // awaiters to resume when this settles
    listeners: Set[Address],    // addresses to notify when this settles
  }

  type Task = {
    state:     TaskState,
    version:   int,             // the fencing token
    ttl:       int,             // the WORKER's number: the lease it asked for
    pid:       Pid,
    expiresAt: int,             // deadline -- armed as "lease"
    retryAt:   int,             // deadline -- armed as "retry"
    resumes:   Set[Id],         // triggers buffered while not suspended
  }

  /// A promise and its task are ONE object. That is the whole of the state
  /// shape, and most of what makes the machine short.
  type Object = { promise: Promise, task: Task }

  pure val noTask: Task = {
    state: TaskNone, version: 0, ttl: NoTime, pid: NoPid,
    expiresAt: NoTime, retryAt: NoTime, resumes: Set(),
  }

  /// Only an external promise may be awaited: something outside this server
  /// decides when it settles.
  pure def isExternal(p: Promise): bool =
    p.tags.external or p.tags.targeted or p.tags.timer

  // -------------------------------------------------------------- the outbox

  type Message =
    Execute({ id: Id, version: int }) | Unblock({ id: Id, state: PromiseState })

  type OutEntry = { address: Address, message: Message }
  type MsgKey   = { kind: str, id: Id, address: Address }

  /// The outbox holds at most one entry per key: a second Execute for a task
  /// replaces the first, an Unblock is per (promise, address).
  pure def msgKey(e: OutEntry): MsgKey =
    match e.message {
      | Execute(m) => { kind: "execute", id: m.id, address: NoAddr }
      | Unblock(m) => { kind: "unblock", id: m.id, address: e.address }
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
}
