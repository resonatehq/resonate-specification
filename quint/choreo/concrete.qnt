/// THE CONCRETE MACHINE: a server that holds the store, and workers that hold
/// nothing. The same program, fragmented.
///
/// A worker acquires ONE FRAGMENT of an execution, runs it to the next await,
/// hands the continuation back to the server and forgets it. Later the server
/// re-forms that continuation with the awaited value and dispatches it again --
/// possibly to a DIFFERENT WORKER. So an execution is not a process here; it is
/// a sequence of fragments stitched together by the store.
///
/// LOOK AT `Message` AGAIN. Two of these carry a `Cont`. That is the entire
/// difference from `abstract.qnt`: here a continuation is a VALUE ON THE WIRE,
/// so it can outlive the machine that made it -- which is what makes the
/// execution durable, and what makes it fragmented. The two facts are one fact.
module concrete {
  import basicSpells.* from "./spells/basicSpells"
  import workflow.* from "./workflow"
  import choreo(processes = NODES) as choreo from "./choreo"

  type Node = str

  pure val SERVER: Node = "server"
  pure val WORKERS: Set[Node] = Set("w1", "w2")
  pure val NODES = WORKERS.union(Set(SERVER))

  /// Two of the three carry a continuation.
  type Message =
    | Execute({ id: Id, cont: Cont })                 // server -> worker: run this
    | Suspends({ id: Id, cont: Cont, awaited: Id })   // worker -> server: hold this
    | Resolves({ id: Id, value: int })                // worker -> server: done

  /// What the store knows about a task. `Blocked` is THE FRAGMENTED
  /// CONTINUATION: an execution that no machine is running and no machine has
  /// forgotten, because it is written down here.
  type Task = Idle | Ready(Cont) | Running | Blocked(Cont)

  type Entry = {
    settled:  Option[int],   // the promise
    task:     Task,
    awaiters: Set[Id],       // continuations to re-form when this settles
  }

  type Role = Server | Worker

  type StateFields = {
    role:    Role,
    store:   Id -> Entry,    // the server's; empty for a worker
    running: Option[Cont],   // the worker's; held ONLY while a fragment runs
  }

  /// A ledger of which machine ran which fragment. Evidence, not protocol.
  type CustomEffects = Ran({ cont: Cont, by: Node })
  type Extensions = { ledger: Set[{ cont: Cont, by: Node }] }
  type Event = ()

  type LocalState   = choreo::LocalState[Node, StateFields]
  type LocalContext = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition   = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[Node, StateFields, Message, Event, Extensions]

  // -------------------------------------------------------------- the server

  pure def isRunning(ctx: LocalContext, i: Id): bool =
    ctx.state.store.keys().contains(i) and ctx.state.store.get(i).task == Running

  /// Every fragment that is ready, paired with every worker that could take it.
  /// The pairing is the nondeterminism, and it is the whole experiment: nothing
  /// says the second fragment of an execution goes where the first one did.
  pure def listen_dispatch(ctx: LocalContext): Set[{ id: Id, cont: Cont, to: Node }] =
    if (ctx.state.role != Server) Set() else
    ctx.state.store.keys()
      .filterMap(i => match ctx.state.store.get(i).task {
        | Ready(c) => Some({ id: i, cont: c })
        | _        => None
      })
      .map(job => WORKERS.map(w => { id: job.id, cont: job.cont, to: w }))
      .flatten()

  pure def dispatches(ctx: LocalContext, d: { id: Id, cont: Cont, to: Node }): Transition = {
    post_state: { ...ctx.state,
      store: ctx.state.store.set(d.id, { ...ctx.state.store.get(d.id), task: Running }) },
    effects: Set(choreo::Send({ to: d.to, message: Execute({ id: d.id, cont: d.cont }) })),
  }

  pure def listen_suspends(ctx: LocalContext): Set[{ id: Id, cont: Cont, awaited: Id }] =
    if (ctx.state.role != Server) Set() else
    ctx.messages.filterMap(m => match m {
      | Suspends(r) => if (isRunning(ctx, r.id)) Some(r) else None
      | _           => None
    })

  /// Take the continuation off the wire and write it down, call what it is
  /// waiting for, and record who to tell.
  pure def suspends(ctx: LocalContext, m: { id: Id, cont: Cont, awaited: Id }): Transition = {
    val parked = ctx.state.store.set(m.id,
      { ...ctx.state.store.get(m.id), task: Blocked(m.cont) })
    val child = if (parked.keys().contains(m.awaited)) parked.get(m.awaited)
                else { settled: None, task: Ready({ id: m.awaited, pc: Start }), awaiters: Set() }
    {
      post_state: { ...ctx.state,
        store: parked.put(m.awaited, { ...child, awaiters: child.awaiters.union(Set(m.id)) }) },
      effects: Set(),
    }
  }

  pure def listen_resolves(ctx: LocalContext): Set[{ id: Id, value: int }] =
    if (ctx.state.role != Server) Set() else
    ctx.messages.filterMap(m => match m {
      | Resolves(r) => if (isRunning(ctx, r.id)) Some(r) else None
      | _           => None
    })

  /// Settling a promise RE-FORMS every continuation that was waiting on it: the
  /// stored fragment plus the value it was missing, ready to be dispatched. This
  /// is the join, and it happens in the store because that is where the
  /// continuation was.
  pure def wake(store: Id -> Entry, awaiters: Set[Id], v: int): Id -> Entry =
    awaiters.fold(store, (acc, a) =>
      match acc.get(a).task {
        | Blocked(c) => acc.set(a, { ...acc.get(a), task: Ready({ ...c, pc: Resumed(v) }) })
        | _          => acc
      })

  pure def resolves(ctx: LocalContext, r: { id: Id, value: int }): Transition = {
    val e = ctx.state.store.get(r.id)
    val settled = ctx.state.store.set(r.id, { ...e, settled: Some(r.value), task: Idle })
    {
      post_state: { ...ctx.state, store: wake(settled, e.awaiters, r.value) },
      effects: Set(),
    }
  }

  // -------------------------------------------------------------- the worker

  /// A worker takes a fragment only when it is holding none. It cannot check
  /// whether the fragment is still wanted -- it has no store to ask -- which is
  /// why a real one carries a lease and a fencing version. See `../concrete.qnt`.
  pure def listen_execute(ctx: LocalContext): Set[Cont] =
    if (ctx.state.role != Worker or ctx.state.running != None) Set() else
    ctx.messages.filterMap(m => match m {
      | Execute(r) => Some(r.cont)
      | _          => None
    })

  pure def acquires(ctx: LocalContext, c: Cont): Transition = {
    post_state: { ...ctx.state, running: Some(c) },
    effects: Set(),
  }

  /// Run the fragment, hand back what remains, and FORGET IT. `running` goes
  /// back to `None` in the same step that sends the continuation away.
  pure def executes(ctx: LocalContext): Set[Transition] =
    match ctx.state.running {
      | None    => Set()
      | Some(c) =>
        val done = { ...ctx.state, running: None }
        val note = choreo::CustomEffect(Ran({ cont: c, by: ctx.state.process_id }))
        match proceed(c) {
          | Await(child) => Set({
              post_state: done,
              effects: Set(note, choreo::Send({ to: SERVER,
                message: Suspends({ id: c.id, cont: c, awaited: child }) })),
            })
          | Return(v) => Set({
              post_state: done,
              effects: Set(note, choreo::Send({ to: SERVER,
                message: Resolves({ id: c.id, value: v }) })),
            })
        }
    }

  pure def main_listener(ctx: LocalContext): Set[Transition] = Set(
    choreo::cue(ctx, listen_dispatch, dispatches),
    choreo::cue(ctx, listen_suspends, suspends),
    choreo::cue(ctx, listen_resolves, resolves),
    choreo::cue(ctx, listen_execute, acquires),
    executes(ctx),
  ).flatten()

  // --------------------------------------------------------------- the system

  pure def apply_custom_effect(env: GlobalContext, e: CustomEffects): GlobalContext =
    match e {
      | Ran(r) => { ...env, extensions: { ledger: env.extensions.ledger.union(Set(r)) } }
    }

  pure def initialize(n: Node): LocalState =
    if (n == SERVER) {
      process_id: n, role: Server, running: None,
      store: Map(ROOT -> { settled: None, task: Ready({ id: ROOT, pc: Start }), awaiters: Set() }),
    } else {
      process_id: n, role: Worker, running: None, store: Map(),
    }

  action init = choreo::init({
    system:     NODES.mapBy(n => initialize(n)),
    messages:   NODES.mapBy(n => Set()),
    events:     NODES.mapBy(n => Set()),
    extensions: { ledger: Set() },
  })

  action step = choreo::step(main_listener, apply_custom_effect)

  val s = choreo::s

  action step_with(v: Node, listener: LocalContext => Set[Transition]): bool =
    choreo::step_with(v, listener, apply_custom_effect)
  def with_cue(process, listen_fn, params) = choreo::with_cue(process, listen_fn, params)
  action perform(cue_ctx, upon_fn) = choreo::perform(cue_ctx, upon_fn, apply_custom_effect)

  // ------------------------------------------------------------- what holds

  val store: Id -> Entry = s.system.get(SERVER).store

  val answered =
    store.keys().contains(ROOT) and store.get(ROOT).settled == Some(ANSWER)

  /// Whatever the root settles to, it settles to the answer. This is what
  /// agreeing with `abstract.qnt` amounts to at this altitude.
  val noWrongAnswer =
    match store.get(ROOT).settled {
      | Some(v) => v == ANSWER
      | None    => true
    }

  /// THE HAZARD, and why a real worker carries a lease. A worker can take a
  /// fragment it has ALREADY RUN back out of its own inbox: the message soup
  /// does not forget, and a worker has no store to ask. So one fragment may run
  /// twice, and nothing here stops it.
  val sameFragmentTwice =
    WORKERS.exists(w =>
      match s.system.get(w).running {
        | None    => false
        | Some(c) => match store.get(c.id).task {
            | Blocked(_) => true      // the store has already parked this one
            | Idle       => true      // ... or already settled it
            | _          => false
          }
      })

  /// AND WHAT IT COSTS. A continuation parked on a promise that has already
  /// settled: the settle that would have re-formed it has been and gone, so
  /// nothing will ever wake it. This is a stale fragment's `Suspends` landing
  /// on a task that had already moved on -- a lost update, reachable because
  /// the server here fences on nothing but the task's own state. The fencing
  /// version in `../concrete.qnt` is the answer to exactly this.
  val stranded =
    store.keys().exists(awaited =>
      val e = store.get(awaited)
      e.settled != None and e.awaiters.exists(a =>
        match store.get(a).task { | Blocked(_) => true | _ => false }))

  // ---------------------------------------------------------- what it shows

  /// THE FRAGMENTED CONTINUATION. One machine ran the root up to its await, a
  /// DIFFERENT machine ran what came after, and it is the same execution.
  /// `abstract.qnt` cannot reach this state or describe it: there is no second
  /// machine for an execution to move to, and no way to send it there.
  val fragmentsSplit =
    s.extensions.ledger.exists(a => s.extensions.ledger.exists(b => and {
      a.cont.id == ROOT,
      b.cont.id == ROOT,
      a.cont.pc == Start,
      b.cont.pc != Start,
      a.by != b.by,
    }))

  /// The moment between fragments: the root's execution exists, no machine is
  /// holding it, and it is not lost. That state is what a store is FOR.
  val inTheStoreAndNowhereElse = and {
    WORKERS.forall(w => s.system.get(w).running == None),
    match store.get(ROOT).task { | Blocked(_) => true | _ => false },
  }

  // ------------------------------------------------------------- the trace

  pure val rootStart: Cont = { id: ROOT, pc: Start }
  pure val rootResumed: Cont = { id: ROOT, pc: Resumed(41) }
  pure val childStart: Cont = { id: CHILD, pc: Start }

  /// One execution, two machines. w1 runs the root up to its await; w2 runs the
  /// child, and then runs what was left of the root.
  run fragmentedTest =
    init
      .then(SERVER.with_cue(listen_dispatch, { id: ROOT, cont: rootStart, to: "w1" })
                  .perform(dispatches))
      .then("w1".with_cue(listen_execute, rootStart).perform(acquires))
      .then(step_with("w1", executes))                      // awaits, and forgets
      .then(SERVER.with_cue(listen_suspends,
              { id: ROOT, cont: rootStart, awaited: CHILD }).perform(suspends))
      .expect(inTheStoreAndNowhereElse)                     // nobody is holding it
      .then(SERVER.with_cue(listen_dispatch, { id: CHILD, cont: childStart, to: "w2" })
                  .perform(dispatches))
      .then("w2".with_cue(listen_execute, childStart).perform(acquires))
      .then(step_with("w2", executes))                      // the child returns 41
      .then(SERVER.with_cue(listen_resolves, { id: CHILD, value: 41 }).perform(resolves))
      .then(SERVER.with_cue(listen_dispatch, { id: ROOT, cont: rootResumed, to: "w2" })
                  .perform(dispatches))                     // re-formed, and dispatched
      .then("w2".with_cue(listen_execute, rootResumed).perform(acquires))
      .then(step_with("w2", executes))                      // the rest of the root, elsewhere
      .then(SERVER.with_cue(listen_resolves, { id: ROOT, value: ANSWER }).perform(resolves))
      .expect(answered)
      .expect(fragmentsSplit)
}
