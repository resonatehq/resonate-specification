/// THE SPECIFICATION. A server that handles a request when one arrives, and
/// does its own background work when that is enabled. That is all of it.
///
/// There are no executions here, no workers, no continuations and no fragments.
/// A promise is a record that settles once; a callback is a name to answer when
/// it does; and work becoming runnable is something the server does to itself.
/// What a program is, where it has got to, and what remains of it are not
/// questions at this level -- which is exactly why an implementation is free to
/// chop an execution into pieces, and why `concrete.qnt` may have continuations
/// that this file has never heard of.
///
/// The client here is the WORLD: it may send any request at any time, in any
/// order. That is what makes this a specification rather than a program.
module abstract {
  import basicSpells.* from "./spells/basicSpells"
  import choreo(processes = NODES) as choreo from "./choreo"

  type Id = str
  type Value = str

  pure val IDS: Set[Id] = Set("i1", "i2")
  pure val VALUES: Set[Value] = Set("v", "w")

  type Node = str
  pure val CLIENT: Node = "client"
  pure val SERVER: Node = "server"
  pure val NODES = Set(CLIENT, SERVER)

  /// Every request the protocol has.
  type Message =
    | Create(Id)
    | Resolve({ id: Id, value: Value })
    | Callback({ awaited: Id, awaiter: Id })

  type Promise = { settled: Option[Value], callbacks: Set[Id] }

  type Role = Client | Server

  type StateFields = {
    role:     Role,
    promises: Id -> Promise,   // the server's store
    runnable: Set[Id],         // what the server owes someone a turn for
  }

  type CustomEffects = ()
  type Event = ()
  type Extensions = ()

  type LocalState    = choreo::LocalState[Node, StateFields]
  type LocalContext  = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition    = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[Node, StateFields, Message, Event, Extensions]

  // ---------------------------------------------------------------- the world

  /// Any request, at any time. The client is not a participant with a protocol
  /// of its own -- it is the set of things that may happen to the server.
  pure def sends(ctx: LocalContext): Set[Transition] =
    if (ctx.state.role != Client) Set() else
    val creates   = IDS.map(i => Create(i))
    val resolves  = tuples(IDS, VALUES).map(((i, v)) => Resolve({ id: i, value: v }))
    val callbacks = tuples(IDS, IDS).filter(((a, w)) => a != w)
                      .map(((a, w)) => Callback({ awaited: a, awaiter: w }))
    creates.union(resolves).union(callbacks).map(req => {
      post_state: ctx.state,
      effects: Set(choreo::Send({ to: SERVER, message: req })),
    })

  // --------------------------------------------------------------- the server

  pure def known(ctx: LocalContext, i: Id): bool = ctx.state.promises.keys().contains(i)
  pure def pending(ctx: LocalContext, i: Id): bool =
    known(ctx, i) and ctx.state.promises.get(i).settled == None

  /// A promise is created once. Asking again is not an error and not a change.
  pure def listen_create(ctx: LocalContext): Set[Id] =
    if (ctx.state.role != Server) Set() else
    ctx.messages.filterMap(m => match m {
      | Create(i) => if (not(known(ctx, i))) Some(i) else None
      | _         => None
    })

  pure def creates(ctx: LocalContext, i: Id): Transition = {
    post_state: { ...ctx.state,
      promises: ctx.state.promises.put(i, { settled: None, callbacks: Set() }),
      runnable: ctx.state.runnable.union(Set(i)) },
    effects: Set(),
  }

  /// A pending promise settles, once, to whatever it was told.
  pure def listen_resolve(ctx: LocalContext): Set[{ id: Id, value: Value }] =
    if (ctx.state.role != Server) Set() else
    ctx.messages.filterMap(m => match m {
      | Resolve(r) => if (pending(ctx, r.id)) Some(r) else None
      | _          => None
    })

  pure def resolves(ctx: LocalContext, r: { id: Id, value: Value }): Transition = {
    post_state: { ...ctx.state,
      promises: ctx.state.promises.set(r.id,
        { ...ctx.state.promises.get(r.id), settled: Some(r.value) }),
      runnable: ctx.state.runnable.exclude(Set(r.id)) },
    effects: Set(),
  }

  /// A name to answer when a pending promise settles.
  pure def listen_callback(ctx: LocalContext): Set[{ awaited: Id, awaiter: Id }] =
    if (ctx.state.role != Server) Set() else
    ctx.messages.filterMap(m => match m {
      | Callback(c) =>
          if (and { pending(ctx, c.awaited), pending(ctx, c.awaiter),
                    not(ctx.state.promises.get(c.awaited).callbacks.contains(c.awaiter)) })
            Some(c) else None
      | _ => None
    })

  pure def registers(ctx: LocalContext, c: { awaited: Id, awaiter: Id }): Transition = {
    post_state: { ...ctx.state,
      promises: ctx.state.promises.set(c.awaited,
        { ...ctx.state.promises.get(c.awaited),
          callbacks: ctx.state.promises.get(c.awaited).callbacks.union(Set(c.awaiter)) }),
      runnable: ctx.state.runnable.exclude(Set(c.awaiter)) },
    effects: Set(),
  }

  // ----------------------------------------------------------- the background
  //
  // No request, no message: the server owes this to itself, and does it when
  // its own state says it is due.

  /// A settled promise still carrying a name answers it: the name is struck, and
  /// whoever it belongs to has a turn coming -- unless they have settled in the
  /// meantime, in which case there is nobody left to give a turn to.
  pure def drains(ctx: LocalContext): Set[Transition] =
    if (ctx.state.role != Server) Set() else
    ctx.state.promises.keys()
      .filter(i => ctx.state.promises.get(i).settled != None)
      .map(i => ctx.state.promises.get(i).callbacks.map(w => { awaited: i, awaiter: w }))
      .flatten()
      .map(c => {
        post_state: { ...ctx.state,
          promises: ctx.state.promises.set(c.awaited,
            { ...ctx.state.promises.get(c.awaited),
              callbacks: ctx.state.promises.get(c.awaited).callbacks.exclude(Set(c.awaiter)) }),
          runnable: if (pending(ctx, c.awaiter)) ctx.state.runnable.union(Set(c.awaiter))
                    else ctx.state.runnable },
        effects: Set(),
      })

  pure def main_listener(ctx: LocalContext): Set[Transition] = Set(
    sends(ctx),
    choreo::cue(ctx, listen_create, creates),
    choreo::cue(ctx, listen_resolve, resolves),
    choreo::cue(ctx, listen_callback, registers),
    drains(ctx),
  ).flatten()

  // --------------------------------------------------------------- the system

  pure def apply_custom_effect(env: GlobalContext, e: CustomEffects): GlobalContext = env

  pure def initialize(n: Node): LocalState = {
    process_id: n,
    role: if (n == SERVER) Server else Client,
    promises: Map(),
    runnable: Set(),
  }

  action init = choreo::init({
    system:     NODES.mapBy(n => initialize(n)),
    messages:   NODES.mapBy(n => Set()),
    events:     NODES.mapBy(n => Set()),
    extensions: (),
  })

  action step = choreo::step(main_listener, apply_custom_effect)

  val s = choreo::s

  action step_with(v: Node, listener: LocalContext => Set[Transition]): bool =
    choreo::step_with(v, listener, apply_custom_effect)

  // ------------------------------------------------------------- what holds

  val store: Id -> Promise = s.system.get(SERVER).promises
  val runnable: Set[Id] = s.system.get(SERVER).runnable

  /// A settled promise carries no name it has not answered -- eventually. What
  /// holds at every state is the weaker thing: a name is only ever registered
  /// on a promise that was pending when it was registered.
  val callbacksOnlyOnKnownPromises =
    store.keys().forall(i => store.get(i).callbacks.forall(w => store.keys().contains(w)))

  /// Nothing is runnable that does not exist, and nothing settled is runnable.
  val runnableIsLive = runnable.forall(i => and {
    store.keys().contains(i),
    store.get(i).settled == None,
  })

  // -------------------------------------------------------- what may happen

  val someoneSettled = store.keys().exists(i => store.get(i).settled != None)
  val someoneWaited  = store.keys().exists(i => store.get(i).callbacks != Set())
  val someoneDrained = store.keys().exists(i => and {
    store.get(i).settled != None,
    runnable != Set(),
  })
}
