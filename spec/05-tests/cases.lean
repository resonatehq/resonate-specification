import «05-tests».«framework»

/-!  # Test cases

Real requests, real responses. Each case builds the request record the
protocol defines, calls the handler, and checks the fields that came
back. -/

namespace Tests

open ServerModel
open ConcreteModel
open ConcreteModel.P

def external : Tags := [("resonate:external", "true")]
def targeted : Tags := [("resonate:target", "poll://any@w1")]
def timer    : Tags := [("resonate:timer", "true"), ("resonate:external", "true")]

/-- **A promise born past its deadline.**

    The deadline is judged against the instant of the request. Created
    at 1000 with a deadline of 500, the promise comes back already
    settled — and which verdict depends on one tag: a timer resolves,
    everything else is rejected. -/
def bornDead : T Unit := do
  let r ← call (promiseCreate { id := "late", timeoutAt := 500, param := {},
                                tags := external }) 1000
  check (r.status == 200) "create late: status"
  check (r.promise.map (·.state) == some .rejectedTimedout) "late: rejected_timedout"

  let r ← call (promiseCreate { id := "tick", timeoutAt := 500, param := {},
                                tags := timer }) 1000
  check (r.status == 200) "create tick: status"
  check (r.promise.map (·.state) == some .resolved) "tick: resolved"

  -- creation is idempotent, and the echo is the promise that exists
  let r ← call (promiseCreate { id := "late", timeoutAt := 9000, param := {},
                                tags := external }) 1010
  check (r.status == 200) "recreate late: status"
  check (r.promise.map (·.timeoutAt) == some 500) "late: keeps its first deadline"

/-- **The deadline is exclusive.**

    Alive at 1999, dead at 2000. The machine reads `timeoutAt > now` for
    live, so AT the deadline is already past it — where an
    implementation using `>=` disagrees. -/
def deadlineBoundary : T Unit := do
  let r ← call (promiseCreate { id := "a", timeoutAt := 2000, param := {},
                                tags := external }) 1000
  check (r.status == 200) "create a: status"

  let r ← call (promiseGet { id := "a" }) 1999
  check (r.promise.map (·.state) == some .pending) "at 1999: still pending"

  let r ← call (promiseGet { id := "a" }) 2000
  check (r.promise.map (·.state) == some .rejectedTimedout) "at 2000: timed out"

/-- **Settlement refusals, and their order.**

    A malformed settlement is 400 even when the promise does not exist:
    validation outranks existence. `rejected_timedout` is malformed
    because that verdict is the server's to write, never a client's. -/
def settleRefusals : T Unit := do
  let r ← call (promiseCreate { id := "a", timeoutAt := 9000, param := {},
                                tags := external }) 1000
  check (r.status == 200) "create a: status"

  let r ← call (promiseSettle { id := "a", state := .pending, value := {} }) 1010
  check (r.status == 400) "settle to pending: 400"

  let r ← call (promiseSettle { id := "a", state := .rejectedTimedout, value := {} }) 1010
  check (r.status == 400) "settle to rejected_timedout: 400"

  let r ← call (promiseSettle { id := "ghost", state := .pending, value := {} }) 1010
  check (r.status == 400) "malformed at a missing promise: 400, not 404"

  let r ← call (promiseSettle { id := "ghost", state := .resolved, value := {} }) 1010
  check (r.status == 404) "well formed at a missing promise: 404"

  let r ← call (promiseSettle { id := "a", state := .resolved, value := {} }) 1020
  check (r.status == 200) "settle a: status"
  check (r.promise.map (·.state) == some .resolved) "a: resolved"

  let r ← call (promiseSettle { id := "a", state := .rejected, value := {} }) 1030
  check (r.status == 200) "re-settle: status"
  check (r.promise.map (·.state) == some .resolved) "re-settle does not overwrite"

/-- **The fence rises by exactly one, and only on acquisition.**

    A worker that lost its claim can tell: the version it holds no
    longer matches, and every version-bearing call answers 409. -/
def fencing : T Unit := do
  let r ← call (promiseCreate { id := "x", timeoutAt := 9000, param := {},
                                tags := targeted }) 1000
  check (r.status == 200) "create x: status"

  let r ← call (taskAcquire { id := "x", version := 0, pid := "p0", ttl := 800 }) 1010
  check (r.status == 200) "acquire: status"
  check (r.task.map (·.version) == some 1) "acquire bumps to 1"

  let r ← call (taskAcquire { id := "x", version := 0, pid := "p1", ttl := 800 }) 1020
  check (r.status == 409) "stale acquire: 409"

  let r ← call (taskFulfill { id := "x", version := 0,
                              action := { id := "x", state := .resolved, value := {} } }) 1020
  check (r.status == 409) "stale fulfill: 409"

  let r ← call (taskRelease { id := "x", version := 1 }) 1030
  check (r.status == 200) "release by the holder: status"

  let r ← call (taskGet { id := "x" }) 1030
  check (r.task.map (·.state) == some .pending) "released: pending"
  check (r.task.map (·.version) == some 1) "release does not bump"

  let r ← call (taskAcquire { id := "x", version := 1, pid := "p1", ttl := 800 }) 1040
  check (r.status == 200) "re-acquire: status"
  check (r.task.map (·.version) == some 2) "the next claim bumps to 2"

/-- **The wake pipeline, one request at a time.**

    A task suspends on a promise, the promise settles, and the task is
    not awake yet. It wakes when the drain runs — a separate internal
    step, at an instant this case picks.

    The two reads at 1050 are the point. `promise.get` says resolved;
    `task.get` says suspended. Both are correct. -/
def wakePipeline : T Unit := do
  let r ← call (promiseCreate { id := "a", timeoutAt := 9000, param := {},
                                tags := external }) 1000
  check (r.status == 200) "create a: status"

  let r ← call (taskCreate { pid := "p0", ttl := 800,
                             action := { id := "x", timeoutAt := 9000, param := {},
                                         tags := targeted } }) 1010
  check (r.status == 200) "task.create x: status"

  let r ← call (taskSuspend { id := "x", version := 1,
                              actions := [{ awaited := "a", awaiter := "x" }] }) 1020
  check (r.status == 200) "suspend: status"

  let r ← call (promiseSettle { id := "a", state := .resolved, value := {} }) 1040
  check (r.status == 200) "settle a: status"

  let r ← call (promiseGet { id := "a" }) 1050
  check (r.promise.map (·.state) == some .resolved) "the awaited is settled"

  let r ← call (taskGet { id := "x" }) 1050
  check (r.task.map (·.state) == some .suspended) "and the awaiter is not awake"

  let o ← call (processResume { awaited := "a", awaiter := "x" }) 1060
  check (o.outcome == .resumed) "the drain wakes it"

  let r ← call (taskGet { id := "x" }) 1060
  check (r.task.map (·.state) == some .pending) "now it is awake"

  let r ← call (taskAcquire { id := "x", version := 1, pid := "p1", ttl := 800 }) 1070
  check (r.status == 200) "and acquirable"

/-- **Timeout always wins over a determined wake.**

    The same script with one number changed: the awaiter's own promise
    times out at 1500 and the drain runs at 2000. The wake is no longer
    owed, so the drain discards it and reports `expired`. -/
def timeoutWins : T Unit := do
  let r ← call (promiseCreate { id := "a", timeoutAt := 9000, param := {},
                                tags := external }) 1000
  check (r.status == 200) "create a: status"

  let r ← call (taskCreate { pid := "p0", ttl := 800,
                             action := { id := "x", timeoutAt := 1500, param := {},
                                         tags := targeted } }) 1010
  check (r.status == 200) "task.create x: status"

  let r ← call (taskSuspend { id := "x", version := 1,
                              actions := [{ awaited := "a", awaiter := "x" }] }) 1020
  check (r.status == 200) "suspend: status"

  let r ← call (promiseSettle { id := "a", state := .resolved, value := {} }) 1030
  check (r.status == 200) "settle a: status"

  let r ← call (promiseGet { id := "x" }) 2000
  check (r.promise.map (·.state) == some .rejectedTimedout) "the awaiter is dead"

  let o ← call (processResume { awaited := "a", awaiter := "x" }) 2000
  check (o.outcome == .expired) "the drain discards the wake"

  let r ← call (taskAcquire { id := "x", version := 1, pid := "p1", ttl := 800 }) 2010
  check (r.status == 409) "never acquirable"

/-- **Suspending on something already settled is 300.**

    Parking the task would park it forever. The client is told to look
    again rather than sleep, and keeps its claim. -/
def suspendOnSettled : T Unit := do
  let r ← call (promiseCreate { id := "a", timeoutAt := 9000, param := {},
                                tags := external }) 1000
  check (r.status == 200) "create a: status"

  let r ← call (promiseSettle { id := "a", state := .resolved, value := {} }) 1010
  check (r.status == 200) "settle a: status"

  let r ← call (taskCreate { pid := "p0", ttl := 800,
                             action := { id := "x", timeoutAt := 9000, param := {},
                                         tags := targeted } }) 1020
  check (r.status == 200) "task.create x: status"

  let r ← call (taskSuspend { id := "x", version := 1,
                              actions := [{ awaited := "a", awaiter := "x" }] }) 1030
  check (r.status == 300) "suspend on a settled awaited: 300"

  let r ← call (taskGet { id := "x" }) 1040
  check (r.task.map (·.state) == some .acquired) "still held, not parked"

def cases : List Case :=
  [ { name := "a promise born past its deadline",            body := bornDead },
    { name := "the deadline is exclusive",                   body := deadlineBoundary },
    { name := "settlement refusals, and their order",        body := settleRefusals },
    { name := "the fence rises by exactly one",              body := fencing },
    { name := "the wake pipeline, one request at a time",    body := wakePipeline },
    { name := "timeout always wins over a determined wake",  body := timeoutWins },
    { name := "suspending on a settled promise is 300",      body := suspendOnSettled } ]

/-- Every case passes against the specification. `#eval failures cases`
    names the case, the step and the check for any that do not. -/
theorem cases_all_pass : (failures cases).isEmpty = true := by decide

end Tests
