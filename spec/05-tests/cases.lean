import «05-tests».«framework»

/-!  # Test cases

Every case is a sequence of ordinary requests, and every assertion is on
what a request answered. Nothing reads the server's state, because an
implementer porting these has a client and a server and nothing else.

Each case runs against the specification, and `cases_all_pass` at the
bottom is checked by `decide`. -/

namespace Tests

open ServerModel

def external : Tags := [("resonate:external", "true")]
def targeted : Tags := [("resonate:target", "poll://any@w1")]
def timer    : Tags := [("resonate:timer", "true"), ("resonate:external", "true")]

/-- **The wake pipeline, one request at a time.**

    A task suspends on a promise, the promise settles, and the task is
    NOT awake yet. It wakes when the drain runs, which is a separate
    internal step at a moment this case picks.

    The two reads in the middle are the point, and both are answers to
    ordinary `get` calls. `promise.get` already says resolved;
    `task.get` still says suspended. Both are correct, and an
    implementation that wakes the task inside `promise.settle` gives a
    different answer to the second one. -/
def wakePipeline : T Unit := do
  clock 1000
  expect 200 (← create "a" 9000 external)
  clock 1010
  expect 200 (← taskCreate "x" "p0" 800 9000 targeted)
  clock 1020
  expect 200 (← suspend "x" 1 ["a"])

  clock 1030
  let r ← taskGet "x"
  expect 200 r
  expectTask .suspended r

  clock 1040
  expect 200 (← settle "a" .resolved)
  sentNothing                        -- settling dispatches nothing

  clock 1050
  let r ← get "a"
  expect 200 r
  expectPromise .resolved r          -- the awaited is settled …

  let r ← taskGet "x"
  expect 200 r
  expectTask .suspended r            -- … and the awaiter is not awake yet

  clock 1060
  let _ ← τresume "a" "x"            -- the drain, at a moment we choose

  let r ← taskGet "x"
  expect 200 r
  expectTask .pending r              -- now it is awake

  clock 1070
  let r ← acquire "x" 1 "p1" 800
  expect 200 r
  expectTask .acquired r
  expectVersion 2 r                  -- acquisition bumps the fence by one

/-- **Timeout always wins over a determined wake.**

    The same script with one number changed: the awaiter's own promise
    times out at 1500, and the drain runs at 2000. The wake is no longer
    owed — the timeout path owns this task's cleanup — so the drain
    discards it.

    Everything asserted here is an answer to a normal request. An
    implementation that treats the drain as an unconditional wake passes
    the case above and answers 200 to the last `acquire` here. -/
def timeoutWins : T Unit := do
  clock 1000
  expect 200 (← create "a" 9000 external)
  clock 1010
  expect 200 (← taskCreate "x" "p0" 800 1500 targeted)    -- own deadline 1500
  clock 1020
  expect 200 (← suspend "x" 1 ["a"])
  clock 1030
  expect 200 (← settle "a" .resolved)

  clock 2000                                              -- past 1500
  let r ← get "x"
  expect 200 r
  expectPromise .rejectedTimedout r     -- projected dead before any τ fires

  let r ← taskGet "x"
  expect 200 r
  expectTask .fulfilled r               -- and the task reads fulfilled with it

  let _ ← τresume "a" "x"               -- the drain finds nothing owed
  expect 409 (← acquire "x" 1 "p1" 800)

/-- **A promise born past its deadline.**

    Creation is not exempt from the deadline: a promise created with a
    timeout already in the past comes back settled from the create call
    itself. Which verdict depends on one tag — a timer resolves when its
    deadline arrives, everything else is rejected.

    Then creation is idempotent, and the echo is the ORIGINAL: creating
    the same id again with a later deadline answers with the promise
    that already exists, not a new one. -/
def bornDead : T Unit := do
  clock 1000
  let r ← create "late" 500 external
  expect 200 r
  expectPromise .rejectedTimedout r

  let r ← create "tick" 500 timer
  expect 200 r
  expectPromise .resolved r

  let r ← create "late" 9000 external
  expect 200 r
  expectPromise .rejectedTimedout r

/-- **Settlement refusals.**

    Three ways to be refused, and their order matters. A malformed
    settlement is 400 even when the promise does not exist — validation
    outranks existence — and `rejected_timedout` is malformed because
    that verdict is the server's to write, never a client's. -/
def settleRefusals : T Unit := do
  clock 1000
  expect 200 (← create "a" 9000 external)

  expect 400 (← settle "a" .pending)             -- not a settlement
  expect 400 (← settle "a" .rejectedTimedout)    -- server-owned verdict
  expect 400 (← settle "ghost" .pending)         -- 400 outranks 404
  expect 404 (← settle "ghost" .resolved)        -- well formed, absent

  expect 200 (← settle "a" .resolved)
  let r ← settle "a" .rejected                   -- already settled: no change
  expect 200 r
  expectPromise .resolved r

/-- **The fence rises by exactly one, and only on acquisition.**

    A worker that lost its claim can tell, because the version it holds
    no longer matches. Every version-bearing call answers 409 to a stale
    one. -/
def fencing : T Unit := do
  clock 1000
  expect 200 (← create "x" 9000 targeted)

  clock 1010
  let r ← acquire "x" 0 "p0" 800
  expect 200 r
  expectVersion 1 r

  clock 1020
  expect 409 (← acquire "x" 0 "p1" 800)          -- stale: already taken
  expect 409 (← fulfill "x" 0 .resolved)         -- stale fence
  expect 409 (← release "x" 0)

  clock 1030
  expect 200 (← release "x" 1)                   -- the holder can release
  let r ← taskGet "x"
  expect 200 r
  expectTask .pending r
  expectVersion 1 r                              -- release does NOT bump

  clock 1040
  let r ← acquire "x" 1 "p1" 800                 -- the next claim does
  expect 200 r
  expectVersion 2 r

/-- **Suspending on something already settled is 300, not 200.**

    The task is not parked, because parking it would park it forever:
    nothing more is going to happen to a promise that has already
    settled. The client is told to look again rather than sleep. -/
def suspendOnSettled : T Unit := do
  clock 1000
  expect 200 (← create "a" 9000 external)
  clock 1010
  expect 200 (← settle "a" .resolved)
  clock 1020
  expect 200 (← taskCreate "x" "p0" 800 9000 targeted)

  clock 1030
  expect 300 (← suspend "x" 1 ["a"])

  let r ← taskGet "x"
  expect 200 r
  expectTask .acquired r                         -- still held, not parked

def cases : List Case :=
  [ { name := "the wake pipeline, one request at a time", body := wakePipeline },
    { name := "timeout always wins over a determined wake", body := timeoutWins },
    { name := "a promise born past its deadline",           body := bornDead },
    { name := "settlement refusals, and their order",       body := settleRefusals },
    { name := "the fence rises by exactly one",             body := fencing },
    { name := "suspending on a settled promise is 300",     body := suspendOnSettled } ]

/-- Every case passes against the specification. Not a claim — a check.
    `#eval failures cases` names the case, the step and the expectation
    for any that do not. -/
theorem cases_all_pass : (failures cases).isEmpty = true := by decide

end Tests
