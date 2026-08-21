/// THE REFINEMENT. Does the executor refine the protocol?
///
/// The statement we mean is `Spec => AbstractAction!Safety`: every behaviour of
/// the chunked, fenced machine is, once you read a document as the objects it
/// holds, a behaviour of the abstract machine.
///
/// TLA+ says that with `INSTANCE AbstractAction WITH objects <- Objects`, which
/// re-reads the abstract machine's `Next` over the executor's variables. Quint
/// has no such instance and no primed reads, so the abstract machine hands over
/// its transition RELATION -- `stepsTo` -- and this module carries the previous
/// abstract state in a spectator variable and asks the relation of every pair.
///
/// The Quint reading of `tla/RefineAction.tla`.
module refine {
  import requests.* from "./requests"
  import abstractAction as A from "./abstractAction"
  import concrete as C from "./concrete"

  /// What the executor's store denotes. The etags, the wheel and the steps in
  /// flight denote NOTHING: three of this machine's five variables map nowhere,
  /// which is why submitting, deciding, arming, disarming and a refused
  /// compare-and-swap are all stutters upstairs.
  val abs: A::State = { objects: C::objects, outbox: C::outbox, now: C::now }

  /// The abstract state before the executor's last transition.
  var prev: A::State

  action init = all {
    C::init,
    prev' = { objects: Map(), outbox: Set(), now: 0 },
  }

  action step = all {
    C::step,
    prev' = abs,
  }

  /// `A!Safety`. Every transition of the executor is a step of the protocol, or
  /// nothing at all.
  val refinesAction = A::stepsTo(prev, abs)

  /// `C_TypeOK` and the rest: the abstract machine's invariants, asked of what
  /// the executor's store denotes. Not implied by the refinement -- refinement
  /// bounds what this machine MAY do and says nothing about what it guarantees.
  val c_invariants = A::invariants(abs)

  // ------------------------------------------------------- the counterexample
  //
  // Random search will not find this: it is nine steps deep and every one of
  // them picks one event out of two hundred. TLC found it by exhausting the
  // graph; here it is written down instead, which is the same evidence and a
  // better record.
  //
  //   A step sweeps what its document says is due AND handles its own request,
  //   and lands both in ONE write. Upstairs those are two steps -- a timeout
  //   and a create -- and `[][Next]_vars` has no room for two.

  pure val plain: Tags =
    { targeted: false, timer: false, external: false, target: "addr1", delay: 0 }

  pure val idA: Id = { origin: "o1", rest: "a" }
  pure val idB: Id = { origin: "o1", rest: "b" }

  /// Born pending, with a deadline at 1.
  pure val createB: CreateReq = { id: idB, timeoutAt: 1, param: "val", tags: plain }
  /// Born ALREADY settled once the clock has reached 1.
  pure val createA: CreateReq = { id: idA, timeoutAt: 0, param: "val", tags: plain }

  pure val bIsDue: Set[TimeoutReq] = Set({ id: idB, kind: PromiseDeadline })

  action take(a: bool): bool = all { a, prev' = abs }

  /// b is created and its deadline armed, the clock reaches it, and then a
  /// step serving a create for `a` finds b due in the document it is already
  /// holding. Everything up to the write is a stutter upstairs. The write is
  /// not: it settles b and creates a together, and no single abstract step
  /// does that.
  run sweepAndHandleIsTwoStepsTest =
    init
      .then(take(C::submit(PromiseCreate(createB), "q2")))
      .then(take(C::processWith("q2", Set(), Set(), Set())))
      .then(take(C::perform("q2")))                      // arm
      .then(take(C::perform("q2")))                      // write
      .then(take(C::perform("q2")))                      // retire the step
      .then(take(C::clock))                              // now = 1, so b is due
      .then(take(C::submit(PromiseCreate(createA), "q1")))
      .then(take(C::processWith("q1", bIsDue, Set(), Set())))
      .expect(refinesAction)                             // deciding is nothing
      .expect(C::sweptAndHandled)                        // two objects in hand
      .then(take(C::perform("q1")))
      .expect(not(refinesAction))                        // and both land at once

  /// THE SAME TRACE WITH AN EMPTY SWEEP, which is the control. The step still
  /// writes, the clock has still moved, b is still lapsed -- and the refinement
  /// holds, because `project` settles b upstairs without anyone writing it.
  /// So it is the sweep that breaks this, and not the split write, the fence,
  /// or the clock.
  run emptySweepIsOneStepTest =
    init
      .then(take(C::submit(PromiseCreate(createB), "q2")))
      .then(take(C::processWith("q2", Set(), Set(), Set())))
      .then(take(C::perform("q2")))
      .then(take(C::perform("q2")))
      .then(take(C::perform("q2")))
      .then(take(C::clock))
      .then(take(C::submit(PromiseCreate(createA), "q1")))
      .then(take(C::processWith("q1", Set(), Set(), Set())))
      .expect(refinesAction)
      .then(take(C::perform("q1")))
      .expect(refinesAction)
}
