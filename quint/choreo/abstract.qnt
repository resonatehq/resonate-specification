/// THE ABSTRACT MACHINE: one process per invocation, and a continuation that
/// never leaves the process it was born in.
///
/// An invocation that awaits PARKS -- it keeps its continuation and blocks. This
/// is what an ordinary async runtime gives you: the coroutine sits in memory
/// with its stack, and the await is a pause in one place.
///
/// LOOK AT `Message`. There is no constructor that carries a `Cont`. In this
/// machine a continuation is not sendable, so it cannot go anywhere, so one
/// execution is one process from beginning to end. That is the abstraction --
/// and `concrete.qnt` is what it costs to give it up.
module abstract {
  import basicSpells.* from "./spells/basicSpells"
  import workflow.* from "./workflow"
  import choreo(processes = IDS) as choreo from "./choreo"

  type Node = Id

  /// Two messages, neither of which carries a continuation.
  type Message =
    | Invoke(Id)
    | Completed({ id: Id, value: int })

  /// Where an invocation is. `Parked` HOLDS ITS CONTINUATION while it waits.
  type Phase =
    | Unborn
    | Holding(Cont)
    | Parked({ cont: Cont, awaited: Id })
    | Returned(int)

  type StateFields = { phase: Phase }
  type CustomEffects = ()
  type Event = ()
  type Extensions = ()

  type LocalState   = choreo::LocalState[Node, StateFields]
  type LocalContext = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition   = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[Node, StateFields, Message, Event, Extensions]

  // ---------------------------------------------------------------- the moves

  /// An invocation begins when someone calls it.
  pure def listen_invoke(ctx: LocalContext): Set[Id] =
    if (ctx.state.phase != Unborn) Set() else
    ctx.messages.filterMap(m => match m {
      | Invoke(id) => if (id == ctx.state.process_id) Some(id) else None
      | _          => None
    })

  pure def begins(ctx: LocalContext, id: Id): Transition = {
    post_state: { ...ctx.state, phase: Holding({ id: id, pc: Start }) },
    effects: Set(),
  }

  /// Run one instruction. Awaiting parks the invocation WITH its continuation;
  /// returning ends it and tells whoever is listening.
  pure def executes(ctx: LocalContext): Set[Transition] =
    match ctx.state.phase {
      | Holding(c) =>
          match proceed(c) {
            | Await(child) => Set({
                post_state: { ...ctx.state, phase: Parked({ cont: c, awaited: child }) },
                effects: Set(choreo::Broadcast(Invoke(child))),
              })
            | Return(v) => Set({
                post_state: { ...ctx.state, phase: Returned(v) },
                effects: Set(choreo::Broadcast(Completed({ id: c.id, value: v }))),
              })
          }
      | _ => Set()
    }

  /// The awaited invocation answered. Resuming is picking the continuation back
  /// up off the stack it was on, so the cue hands the act everything it needs.
  pure def listen_completion(ctx: LocalContext): Set[{ cont: Cont, value: int }] =
    match ctx.state.phase {
      | Parked(p) =>
          ctx.messages.filterMap(m => match m {
            | Completed(r) => if (r.id == p.awaited) Some({ cont: p.cont, value: r.value }) else None
            | _            => None
          })
      | _ => Set()
    }

  pure def resumes(ctx: LocalContext, r: { cont: Cont, value: int }): Transition = {
    post_state: { ...ctx.state, phase: Holding({ ...r.cont, pc: Resumed(r.value) }) },
    effects: Set(),
  }

  pure def main_listener(ctx: LocalContext): Set[Transition] = Set(
    choreo::cue(ctx, listen_invoke, begins),
    executes(ctx),
    choreo::cue(ctx, listen_completion, resumes),
  ).flatten()

  // --------------------------------------------------------------- the system

  pure def apply_custom_effect(env: GlobalContext, e: CustomEffects): GlobalContext = env

  /// The root is the top-level call: it is holding its continuation from the
  /// first instant. Everything else waits to be invoked.
  pure def initialize(n: Node): LocalState = {
    process_id: n,
    phase: if (n == ROOT) Holding({ id: n, pc: Start }) else Unborn,
  }

  action init = choreo::init({
    system:     IDS.mapBy(n => initialize(n)),
    messages:   IDS.mapBy(n => Set()),
    events:     IDS.mapBy(n => Set()),
    extensions: (),
  })

  action step = choreo::step(main_listener, apply_custom_effect)

  val s = choreo::s

  action step_with(v: Node, listener: LocalContext => Set[Transition]): bool =
    choreo::step_with(v, listener, apply_custom_effect)
  def with_cue(process, listen_fn, params) = choreo::with_cue(process, listen_fn, params)
  action perform(cue_ctx, upon_fn) = choreo::perform(cue_ctx, upon_fn, apply_custom_effect)

  // ------------------------------------------------------------- what holds

  /// The answer.
  val answered = s.system.get(ROOT).phase == Returned(ANSWER)

  /// A parked invocation is still holding its OWN continuation. Nothing is ever
  /// mid-await with nothing to come back to -- which here is true by
  /// construction, because there is no way to put a continuation anywhere else.
  val continuationStaysHome = IDS.forall(i =>
    match s.system.get(i).phase {
      | Parked(p)  => p.cont.id == i
      | Holding(c) => c.id == i
      | _          => true
    })

  /// Whatever the root returns, it returns the answer.
  val noWrongAnswer =
    match s.system.get(ROOT).phase {
      | Returned(v) => v == ANSWER
      | _           => true
    }

  // ------------------------------------------------------------- the trace

  run executionTest =
    init
      .then(step_with(ROOT, executes))                                 // f awaits g
      .then(CHILD.with_cue(listen_invoke, CHILD).perform(begins))      // g is called
      .then(step_with(CHILD, executes))                                // g returns 41
      .then(ROOT.with_cue(listen_completion,
                          { cont: { id: ROOT, pc: Start }, value: 41 }).perform(resumes))
      .then(step_with(ROOT, executes))                                 // f returns 42
      .expect(answered)
}
