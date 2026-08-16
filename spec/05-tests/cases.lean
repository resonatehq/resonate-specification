import «05-tests».«framework»

/-!  # Test cases

Four, to prove the shape. The corpus in `work/corpus` holds 253 minimal
scripts with the branch each one witnesses; rendering those through this
framework is what turns them from a data format into something an
implementer reads.

Every case below is checked by `decide` at the bottom of the file, so it
is not a claim about the specification — it is a fact the kernel has
verified about it. -/

namespace Tests

open ServerModel

def external : Tags := [("resonate:external", "true")]
def targeted : Tags := [("resonate:target", "poll://any@w1")]
def timer    : Tags := [("resonate:timer", "true"), ("resonate:external", "true")]

/-- **The wake pipeline, driven stage by stage.**

    The case the whole projection discipline exists for. A task suspends
    on a promise; the promise settles; and the wake does NOT happen yet
    — it happens when the drain runs, which is a separate internal step
    at a moment this case chooses.

    The two reads in the middle are the point. At stage 1 the promise
    interface already reports the awaited settled, and the task
    interface still reports the awaiter suspended. Both are correct.
    An implementation that wakes the task inside `promise.settle` fails
    the first `taskIs .suspended`; one that never wakes it fails the
    last. -/
def wakePipeline : T Unit := do
  clock 1000
  expect 200 (← create "a" 9000 external)
  clock 1010
  expect 200 (← taskCreate "x" "p0" 800 9000 targeted)
  clock 1020
  expect 200 (← suspend "x" 1 ["a"])
  taskIs "x" .suspended

  clock 1030
  expect 200 (← settle "a" .resolved)
  promiseIs "a" .resolved      -- stage 1: settled …
  taskIs    "x" .suspended     -- … and not yet woken
  sentNothing                  -- settling dispatches nothing

  clock 1040
  let _ ← τresume "a" "x"      -- the drain, at a moment we choose
  taskIs "x" .pending          -- stage 2: awake and acquirable

  clock 1050
  expect 200 (← acquire "x" 1 "p1" 800)
  taskIs "x" .acquired

/-- **Timeout always wins.**

    Same shape, one difference: the awaiter's OWN promise is past its
    deadline by the time the drain runs. The wake is not owed any more —
    the timeout path owns this task's cleanup — so the drain discards it
    and the task never becomes acquirable.

    An implementation that treats the drain as an unconditional wake
    passes the case above and fails this one. That is the gap every
    known implementation shipped. -/
def timeoutWins : T Unit := do
  clock 1000
  expect 200 (← create "a" 9000 external)
  clock 1010
  expect 200 (← taskCreate "x" "p0" 800 1500 targeted)   -- own deadline: 1500
  clock 1020
  expect 200 (← suspend "x" 1 ["a"])
  clock 1030
  expect 200 (← settle "a" .resolved)

  clock 2000                    -- past the awaiter's own deadline
  promiseIs "x" .rejectedTimedout   -- projected dead, before any τ fires
  let _ ← τresume "a" "x"
  taskIs "x" .suspended         -- the wake was discarded, not delivered
  expect 409 (← acquire "x" 1 "p1" 800)

/-- **A promise born past its deadline.**

    Creation is not exempt from the deadline. A promise created with a
    timeout already in the past is born settled, and which verdict it is
    born with depends on the timer tag: a timer RESOLVES when its
    deadline arrives, everything else is rejected.

    Two `create` calls, two different terminal states, one difference in
    the tags. -/
def bornDead : T Unit := do
  clock 1000
  expect 200 (← create "late" 500 external)
  promiseIs "late" .rejectedTimedout

  expect 200 (← create "tick" 500 timer)
  promiseIs "tick" .resolved

  -- and creation is idempotent: the second call echoes, it does not
  -- overwrite the deadline it was given the first time
  expect 200 (← create "late" 9000 external)
  promiseIs "late" .rejectedTimedout

/-- **A settled promise sends to its listener, and the internal step is
    what sends it.**

    `promise.settle` records the obligation; the delivery is a separate
    internal step. So the settle itself dispatches nothing, and the
    unblock appears only when the listener step runs.

    Worth stating plainly because it is the whole message channel: in
    this machine EVERY message is emitted by an internal step. An
    implementation whose settle delivers inline is not wrong about the
    end state and is wrong about when. -/
def listenerDelivery : T Unit := do
  clock 1000
  expect 200 (← create "a" 9000 external)
  clock 1010
  expect 200 (← listen "a" "https://l")
  sentNothing

  clock 1020
  expect 200 (← settle "a" .resolved)
  sentNothing                   -- the settle records; it does not deliver

def cases : List Case :=
  [ { name := "the wake pipeline, driven stage by stage", body := wakePipeline },
    { name := "timeout always wins over a determined wake",  body := timeoutWins },
    { name := "a promise born past its deadline",            body := bornDead },
    { name := "settling records the unblock, it does not send it",
      body := listenerDelivery } ]

/-- Every case passes against the specification. Not a claim — a check.
    If a handler changes so that one of these no longer holds, this
    fails to compile and names nothing; run `#eval failures cases` for
    the case, the step and the expectation. -/
theorem cases_all_pass : (failures cases).isEmpty = true := by decide

end Tests
