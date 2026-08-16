import «05-tests».«framework»

/-!  # Test cases

Every case is a sequence of ordinary requests, each carrying the instant
it happens at, and every assertion is on what a request answered.
Nothing reads the server's state.

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
    internal step at an instant this case picks.

    The two reads in the middle are the point, and both are answers to
    ordinary `get` calls at the same instant. `promise.get` says
    resolved; `task.get` says suspended. Both are correct, and an
    implementation that wakes the task inside `promise.settle` gives a
    different answer to the second. -/
def wakePipeline : T Unit := do
  expect 200 (← create     1000 "a" 9000 external)
  expect 200 (← taskCreate 1010 "x" "p0" 800 9000 targeted)
  expect 200 (← suspend    1020 "x" 1 ["a"])

  let r ← taskGet 1030 "x"
  expect 200 r
  expectTask .suspended r

  expect 200 (← settle 1040 "a" .resolved)
  sentNothing                            -- settling dispatches nothing

  let r ← promiseGet 1050 "a"
  expect 200 r
  expectPromise .resolved r              -- the awaited is settled …

  let r ← taskGet 1050 "x"
  expect 200 r
  expectTask .suspended r                -- … and the awaiter is not awake

  let _ ← τresume 1060 "a" "x"           -- the drain, at an instant we pick

  let r ← taskGet 1060 "x"
  expect 200 r
  expectTask .pending r                  -- now it is awake

  let r ← acquire 1070 "x" 1 "p1" 800
  expect 200 r
  expectTask .acquired r
  expectVersion 2 r                      -- acquisition bumps the fence by one

/-- **Timeout always wins over a determined wake.**

    The same script with one number changed: the awaiter's own promise
    times out at 1500, and the drain runs at 2000. The wake is no longer
    owed — the timeout path owns this task's cleanup — so the drain
    discards it.

    An implementation that treats the drain as an unconditional wake
    passes the case above and answers 200 to the last `acquire`. -/
def timeoutWins : T Unit := do
  expect 200 (← create     1000 "a" 9000 external)
  expect 200 (← taskCreate 1010 "x" "p0" 800 1500 targeted)   -- deadline 1500
  expect 200 (← suspend    1020 "x" 1 ["a"])
  expect 200 (← settle     1030 "a" .resolved)

  let r ← promiseGet 2000 "x"            -- asked past the deadline
  expect 200 r
  expectPromise .rejectedTimedout r      -- projected dead, before any τ fires

  let r ← taskGet 2000 "x"
  expect 200 r
  expectTask .fulfilled r                -- the task reads fulfilled with it

  let _ ← τresume 2000 "a" "x"           -- the drain finds nothing owed
  expect 409 (← acquire 2010 "x" 1 "p1" 800)

/-- **A promise born past its deadline.**

    The deadline is judged against the instant of the request. A promise
    created at 1000 with a deadline of 500 is born settled, and which
    verdict depends on one tag: a timer resolves when its deadline
    arrives, everything else is rejected.

    Then creation is idempotent, and the echo is the ORIGINAL — creating
    the same id again with a later deadline answers with the promise
    that already exists. -/
def bornDead : T Unit := do
  let r ← create 1000 "late" 500 external
  expect 200 r
  expectPromise .rejectedTimedout r

  let r ← create 1000 "tick" 500 timer
  expect 200 r
  expectPromise .resolved r

  let r ← create 1010 "late" 9000 external
  expect 200 r
  expectPromise .rejectedTimedout r

/-- **The deadline is exclusive.**

    A promise with a deadline of 2000 is alive when asked at 1999 and
    dead when asked at 2000. The machine reads `timeoutAt > now` for
    live, so AT the deadline is already past it — the boundary where an
    implementation using `>=` disagrees, and the only place the
    difference shows. -/
def deadlineBoundary : T Unit := do
  expect 200 (← create 1000 "a" 2000 external)

  let r ← promiseGet 1999 "a"
  expect 200 r
  expectPromise .pending r

  let r ← promiseGet 2000 "a"
  expect 200 r
  expectPromise .rejectedTimedout r

/-- **Settlement refusals, and their order.**

    A malformed settlement is 400 even when the promise does not exist —
    validation outranks existence — and `rejected_timedout` is malformed
    because that verdict is the server's to write, never a client's. -/
def settleRefusals : T Unit := do
  expect 200 (← create 1000 "a" 9000 external)

  expect 400 (← settle 1010 "a" .pending)              -- not a settlement
  expect 400 (← settle 1010 "a" .rejectedTimedout)     -- server-owned verdict
  expect 400 (← settle 1010 "ghost" .pending)          -- 400 outranks 404
  expect 404 (← settle 1010 "ghost" .resolved)         -- well formed, absent

  expect 200 (← settle 1020 "a" .resolved)
  let r ← settle 1030 "a" .rejected                    -- settled: no change
  expect 200 r
  expectPromise .resolved r

/-- **The fence rises by exactly one, and only on acquisition.**

    A worker that lost its claim can tell, because the version it holds
    no longer matches. Every version-bearing call answers 409 to a stale
    one, and `release` does not bump. -/
def fencing : T Unit := do
  expect 200 (← create 1000 "x" 9000 targeted)

  let r ← acquire 1010 "x" 0 "p0" 800
  expect 200 r
  expectVersion 1 r

  expect 409 (← acquire 1020 "x" 0 "p1" 800)     -- stale: already taken
  expect 409 (← fulfill 1020 "x" 0 .resolved)    -- stale fence
  expect 409 (← release 1020 "x" 0)

  expect 200 (← release 1030 "x" 1)              -- the holder can release
  let r ← taskGet 1030 "x"
  expect 200 r
  expectTask .pending r
  expectVersion 1 r                              -- release does NOT bump

  let r ← acquire 1040 "x" 1 "p1" 800            -- the next claim does
  expect 200 r
  expectVersion 2 r

/-- **Suspending on something already settled is 300, not 200.**

    Parking the task would park it forever: nothing more is going to
    happen to a promise that has already settled. The client is told to
    look again rather than sleep, and keeps its claim. -/
def suspendOnSettled : T Unit := do
  expect 200 (← create     1000 "a" 9000 external)
  expect 200 (← settle     1010 "a" .resolved)
  expect 200 (← taskCreate 1020 "x" "p0" 800 9000 targeted)

  expect 300 (← suspend 1030 "x" 1 ["a"])

  let r ← taskGet 1040 "x"
  expect 200 r
  expectTask .acquired r                         -- still held, not parked

def cases : List Case :=
  [ { name := "the wake pipeline, one request at a time", body := wakePipeline },
    { name := "timeout always wins over a determined wake", body := timeoutWins },
    { name := "a promise born past its deadline",           body := bornDead },
    { name := "the deadline is exclusive",                  body := deadlineBoundary },
    { name := "settlement refusals, and their order",       body := settleRefusals },
    { name := "the fence rises by exactly one",             body := fencing },
    { name := "suspending on a settled promise is 300",     body := suspendOnSettled } ]

/-- Every case passes against the specification. Not a claim — a check.
    `#eval failures cases` names the case, the step and the expectation
    for any that do not. -/
theorem cases_all_pass : (failures cases).isEmpty = true := by decide

end Tests
