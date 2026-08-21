/// THE IMPLEMENTATION. A server that keeps the store, and workers that keep
/// nothing between one piece of work and the next.
///
/// Nothing here is imported from `abstract.qnt`. The two files share no type,
/// no handler and no identifier: one says what may happen, the other is one way
/// of making it happen, and the only thing they have in common is the protocol
/// they are both talking about. Borrowing anything would make the comparison
/// unaskable.
///
/// This is where CONTINUATIONS live, and they live here because they have to.
/// The specification has no such thing: it never asks where a program has got
/// to. This machine asks constantly, because it hands a piece of an execution
/// to a worker, takes back what remains, and later hands that to A DIFFERENT
/// WORKER. A continuation is the machinery for keeping a promise the
/// specification states without it.
module concrete {
  import basicSpells.* from "./spells/basicSpells"
  import choreo(processes = NODES) as choreo from "./choreo"

  type Id = str
  type Value = str

  pure val IDS: Set[Id] = Set("i1", "i2")
  pure val VALUES: Set[Value] = Set("v", "w")

  type Node = str
  pure val CLIENT: Node = "client"
  pure val SERVER: Node = "server"
  pure val WORKERS: Set[Node] = Set("w1", "w2")
  pure val NODES = WORKERS.union(Set(CLIENT, SERVER))

  /// Something an execution has learned by awaiting.
  type Seen = { from: Id, value: Value }

  /// A CONTINUATION: an execution, and everything it already knows. It is what
  /// a worker needs to carry on something another worker began.
  type Cont = { id: Id, seen: Set[Seen] }

  /// Two of these carry a continuation, which is the whole difference from the
  /// specification's alphabet: here what remains of an execution is a VALUE ON
  /// THE WIRE, so it can outlive the machine that made it.
  type Message =
    | Invokes(Id)                                  // client -> server
    | Execute({ cont: Cont })                      // server -> worker
    | Suspends({ cont: Cont, awaited: Id })        // worker -> server
    | Resolves({ id: Id, value: Value })           // worker -> server

  /// `Blocked` is the fragmented continuation: an execution that no machine is
  /// running and no machine has forgotten, because it is written down here.
  type Task = Idle | Ready(Cont) | Running | Blocked(Cont)

  type Entry = { settled: Option[Value], callbacks: Set[Id], task: Task }

  type Role = Client | Server | Worker

  type StateFields = {
    role:    Role,
    store:   Id -> Entry,     // the server's
    running: Option[Cont],    // the worker's, and ONLY while a piece runs
  }

  /// What ran where. Evidence, not protocol.
  type Decision = Awaited(Id) | Returned(Value)
  type CustomEffects = Ran({ cont: Cont, by: Node, decided: Decision })
  type Extensions = { ledger: Set[{ cont: Cont, by: Node, decided: Decision }] }
  type Event = ()

  type LocalState    = choreo::LocalState[Node, StateFields]
  type LocalContext  = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition    = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[Node, StateFields, Message, Event, Extensions]

  // ---------------------------------------------------------------- the world

  pure def invokes(ctx: LocalContext): Set[Transition] =
    if (ctx.state.role != Client) Set() else
    IDS.map(i => {
      post_state: ctx.state,
      effects: Set(choreo::Send({ to: SERVER, message: Invokes(i) })),
    })

  // --------------------------------------------------------------- the server

  pure def known(ctx: LocalContext, i: Id): bool = ctx.state.store.keys().contains(i)
  pure def isRunning(ctx: LocalContext, i: Id): bool =
    known(ctx, i) and ctx.state.store.get(i).task == Running

  pure def listen_invokes(ctx: LocalContext): Set[Id] =
    if (ctx.state.role != Server) Set() else
    ctx.messages.filterMap(m => match m {
      | Invokes(i) => if (not(known(ctx, i))) Some(i) else None
      | _          => None
    })

  /// A new execution: a pending promise, and a first piece of work that knows
  /// nothing yet.
  pure def accepts(ctx: LocalContext, i: Id): Transition = {
    post_state: { ...ctx.state,
      store: ctx.state.store.put(i,
        { settled: None, callbacks: Set(), task: Ready({ id: i, seen: Set() }) }) },
    effects: Set(),
  }

  /// Every piece of work that is ready, paired with every worker that could take
  /// it. The pairing is the nondeterminism, and it is the whole experiment:
  /// nothing says the second piece of an execution goes where the first went.
  pure def listen_dispatch(ctx: LocalContext): Set[{ cont: Cont, to: Node }] =
    if (ctx.state.role != Server) Set() else
    ctx.state.store.keys()
      .filterMap(i => match ctx.state.store.get(i).task { | Ready(c) => Some(c) | _ => None })
      .map(c => WORKERS.map(w => { cont: c, to: w }))
      .flatten()

  pure def dispatches(ctx: LocalContext, d: { cont: Cont, to: Node }): Transition = {
    post_state: { ...ctx.state,
      store: ctx.state.store.set(d.cont.id,
        { ...ctx.state.store.get(d.cont.id), task: Running }) },
    effects: Set(choreo::Send({ to: d.to, message: Execute({ cont: d.cont }) })),
  }

  pure def listen_suspends(ctx: LocalContext): Set[{ cont: Cont, awaited: Id }] =
    if (ctx.state.role != Server) Set() else
    ctx.messages.filterMap(m => match m {
      | Suspends(r) => if (isRunning(ctx, r.cont.id)) Some(r) else None
      | _           => None
    })

  /// Take the continuation off the wire and write it down; start what it is
  /// waiting for if nobody has; and record who to answer.
  pure def suspends(ctx: LocalContext, m: { cont: Cont, awaited: Id }): Transition = {
    val parked = ctx.state.store.set(m.cont.id,
      { ...ctx.state.store.get(m.cont.id), task: Blocked(m.cont) })
    val awaited = if (parked.keys().contains(m.awaited)) parked.get(m.awaited)
                  else { settled: None, callbacks: Set(),
                         task: Ready({ id: m.awaited, seen: Set() }) }
    {
      post_state: { ...ctx.state,
        store: parked.put(m.awaited,
          { ...awaited, callbacks: awaited.callbacks.union(Set(m.cont.id)) }) },
      effects: Set(),
    }
  }

  pure def listen_resolves(ctx: LocalContext): Set[{ id: Id, value: Value }] =
    if (ctx.state.role != Server) Set() else
    ctx.messages.filterMap(m => match m {
      | Resolves(r) => if (isRunning(ctx, r.id)) Some(r) else None
      | _           => None
    })

  pure def resolves(ctx: LocalContext, r: { id: Id, value: Value }): Transition = {
    post_state: { ...ctx.state,
      store: ctx.state.store.set(r.id,
        { ...ctx.state.store.get(r.id), settled: Some(r.value), task: Idle }) },
    effects: Set(),
  }

  // ----------------------------------------------------------- the background

  /// THE JOIN. A settled promise still carrying a name RE-FORMS that execution's
  /// continuation -- the piece that was written down, plus the value it was
  /// missing -- and makes it ready to be handed out again. Upstairs this is a
  /// name being struck and a turn being owed. Here it is a continuation being
  /// rebuilt, because here there is one.
  pure def drains(ctx: LocalContext): Set[Transition] =
    if (ctx.state.role != Server) Set() else
    ctx.state.store.keys()
      .filter(i => ctx.state.store.get(i).settled != None)
      .map(i => ctx.state.store.get(i).callbacks.map(w => { awaited: i, awaiter: w }))
      .flatten()
      .map(c => {
        val awaited = ctx.state.store.get(c.awaited)
        val struck = ctx.state.store.set(c.awaited,
          { ...awaited, callbacks: awaited.callbacks.exclude(Set(c.awaiter)) })
        val awaiter = struck.get(c.awaiter)
        {
          post_state: { ...ctx.state, store:
            match awaiter.task {
              | Blocked(cont) => struck.set(c.awaiter, { ...awaiter, task: Ready({ ...cont,
                  seen: cont.seen.union(Set({ from: c.awaited, value: awaited.settled.unwrap() })) }) })
              | _ => struck
            } },
          effects: Set(),
        }
      })

  // -------------------------------------------------------------- the worker

  /// A worker takes a piece of work only when it is holding none. It cannot ask
  /// whether the piece is still wanted -- it has no store -- which is why a real
  /// one carries a lease and a fencing version. See `../concrete.qnt`.
  pure def listen_execute(ctx: LocalContext): Set[Cont] =
    if (ctx.state.role != Worker or ctx.state.running != None) Set() else
    ctx.messages.filterMap(m => match m { | Execute(r) => Some(r.cont) | _ => None })

  pure def acquires(ctx: LocalContext, c: Cont): Transition = {
    post_state: { ...ctx.state, running: Some(c) },
    effects: Set(),
  }

  /// Run the piece. What the program does is not this machine's business, so
  /// every possibility is offered: it may await anything, or return anything.
  /// Either way the worker hands back what remains and FORGETS IT -- `running`
  /// goes to `None` in the same step that sends the continuation away.
  pure def executes(ctx: LocalContext): Set[Transition] =
    match ctx.state.running {
      | None    => Set()
      | Some(c) =>
        val idle = { ...ctx.state, running: None }
        val awaits = IDS.exclude(Set(c.id)).map(other => {
          post_state: idle,
          effects: Set(
            choreo::CustomEffect(Ran({ cont: c, by: ctx.state.process_id, decided: Awaited(other) })),
            choreo::Send({ to: SERVER, message: Suspends({ cont: c, awaited: other }) })),
        })
        val returns = VALUES.map(v => {
          post_state: idle,
          effects: Set(
            choreo::CustomEffect(Ran({ cont: c, by: ctx.state.process_id, decided: Returned(v) })),
            choreo::Send({ to: SERVER, message: Resolves({ id: c.id, value: v }) })),
        })
        awaits.union(returns)
    }

  pure def main_listener(ctx: LocalContext): Set[Transition] = Set(
    invokes(ctx),
    choreo::cue(ctx, listen_invokes, accepts),
    choreo::cue(ctx, listen_dispatch, dispatches),
    choreo::cue(ctx, listen_suspends, suspends),
    choreo::cue(ctx, listen_resolves, resolves),
    drains(ctx),
    choreo::cue(ctx, listen_execute, acquires),
    executes(ctx),
  ).flatten()

  // --------------------------------------------------------------- the system

  pure def apply_custom_effect(env: GlobalContext, e: CustomEffects): GlobalContext =
    match e {
      | Ran(r) => { ...env, extensions: { ledger: env.extensions.ledger.union(Set(r)) } }
    }

  pure def initialize(n: Node): LocalState = {
    process_id: n,
    role: if (n == SERVER) Server else if (n == CLIENT) Client else Worker,
    store: Map(),
    running: None,
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

  // ------------------------------------------------------------- what holds

  val store: Id -> Entry = s.system.get(SERVER).store

  /// Every continuation anywhere in the machine: parked in the store, waiting to
  /// be handed out, or in a worker's hands.
  val continuations: Set[Cont] =
    store.keys().filterMap(i => match store.get(i).task {
      | Ready(c)   => Some(c)
      | Blocked(c) => Some(c)
      | _          => None
    }).union(WORKERS.filterMap(w => s.system.get(w).running))

  /// THE SPECIFICATION'S ONE LAW, asked of an implementation that has continued
  /// executions on machines that never began them: everything a continuation
  /// claims to know, it learned from a promise that really did settle to that.
  val observationsAreTruthful =
    continuations.forall(c => c.seen.forall(o => and {
      store.keys().contains(o.from),
      store.get(o.from).settled == Some(o.value),
    }))

  // ---------------------------------------------------------- what it shows

  val ledger = s.extensions.ledger

  /// THE FRAGMENTED CONTINUATION. One machine ran a piece of an execution, a
  /// DIFFERENT machine ran a later piece of the same one. Upstairs this cannot
  /// be said: there are no pieces, and no machines for them to be on.
  val fragmentsSplit =
    ledger.exists(a => ledger.exists(b => and {
      a.cont.id == b.cont.id,
      a.cont.seen == Set(),
      b.cont.seen != Set(),
      a.by != b.by,
    }))

  /// The moment between pieces: an execution that no machine is holding and no
  /// machine has lost. That state is what a store is FOR.
  val inTheStoreAndNowhereElse = and {
    WORKERS.forall(w => s.system.get(w).running == None),
    store.keys().exists(i => match store.get(i).task { | Blocked(_) => true | _ => false }),
  }

  /// THE HAZARD. A worker can take a piece it has ALREADY RUN back out of its
  /// own inbox: the soup does not forget and the worker has no store to ask.
  val sameFragmentTwice =
    WORKERS.exists(w => match s.system.get(w).running {
      | None    => false
      | Some(c) => match store.get(c.id).task {
          | Blocked(_) => true
          | Idle       => true
          | _          => false
        }
    })

  /// AND ITS SHARPEST FORM. The same piece, run twice, deciding DIFFERENTLY --
  /// which is not a modelling artefact but the reason a promise is a RECORD:
  /// what an execution did has to be remembered, because doing it again is not
  /// guaranteed to do the same thing.
  val rerunDecidedDifferently =
    ledger.exists(a => ledger.exists(b => a.cont == b.cont and a.decided != b.decided))

  /// A continuation parked on a promise that has already settled: the drain that
  /// would have re-formed it has been and gone, so nothing will wake it.
  val stranded =
    store.keys().exists(i => and {
      store.get(i).settled != None,
      store.get(i).callbacks.exists(w =>
        match store.get(w).task { | Blocked(_) => true | _ => false }),
    })
}
