import «01-objects».«state»
import «02-actions».«P-01-promise.get»
import «02-actions».«P-02-promise.create»
import «02-actions».«P-03-promise.settle»
import «02-actions».«P-04-promise.register_callback»
import «02-actions».«P-05-promise.register_listener»
import «02-actions».«T-01-task.get»
import «02-actions».«T-02-task.create»
import «02-actions».«T-03-task.acquire»
import «02-actions».«T-04-task.fence»
import «02-actions».«T-05-task.heartbeat»
import «02-actions».«T-06-task.suspend»
import «02-actions».«T-07-task.fulfill»
import «02-actions».«T-08-task.release»
import «02-actions».«T-09-task.halt»
import «02-actions».«T-10-task.continue»
import «02-actions».«S-01-schedule.get»
import «02-actions».«S-02-schedule.create»
import «02-actions».«S-03-schedule.delete»
import «02-actions».«02-timeouts»
import «02-actions».«03-resume»
import «02-actions».«04-guarantee»

open ServerModel

/-! ## The read/write discipline: reads observe the pre-state

Can we say that no handler issues a read after a write — that no
`setPromise` is ever followed by a `getPromise`? Yes, but the honest
statement is per LOCATION, not per trace position:

> **Over any single transition — request handler or τ-step — no effect
> reads a location an earlier effect of the same transition wrote.**

Equivalently: every read is served by the PRE-state. A handler is a pure
decision over a snapshot, applied as a batch of writes; no data flows
through the store within a transition. This is what licenses an
implementation to run each handler as one consistent read set followed by
one write-back — a one-shot transaction with no read-your-writes
dependency. The literal claim holds as a corollary: no `setPromise` is
followed by a `getPromise` of anything already written — same for tasks
and schedules.

The STRICT form — a read phase, then a write phase, no read after ANY
write (`readsThenWrites` below) — is deliberately not the invariant, and
`promiseSettle` is the standing counterexample: it writes its promise,
then reads its task to learn whether a fulfillment rides along. The read
is of a different location keyed by the same id; it observes the
pre-state, and hoisting it would change nothing — which is precisely the
content of the per-location statement. The strict form fails in exactly
three shapes, all benign under the discipline:

  * settlement writes the promise before reading the co-keyed task
    (`promiseSettle`, `onPromiseTimeout`);
  * the task τ-steps write task state before reading the co-keyed promise
    for the dispatch target (`onTaskRetryTimeout`, `onTaskLeaseTimeout`);
  * per-item loops alternate read and write over DISTINCT keys
    (`taskSuspend` over its awaited list, `taskHeartbeat` over its refs).

The third shape shows validation is load-bearing: `taskSuspend`'s `400`
on a duplicate awaited list is exactly what keeps its loop's read set
disjoint from its write set. Drop that guard and the second visit to a
duplicated awaited would read the callback the first visit wrote.

### Scope, and the boundary that proves it

The discipline is a property of TRANSITIONS: the request handlers and the
τ-steps (`onResume`, the timeout family). `drain` is not a transition but
a SCHEDULE — a composition of τ-steps — and it genuinely reads its own
writes ACROSS steps: two deferred resumes for the same awaiter, and the
second `onResume` reads the task the first one woke; that read-back is
how the second trigger buffers instead of double-waking. Checked below:
each `onResume` step is clean, their composition is not. That failure is
the boundary of the theorem, and the reason `drain` is a schedule rather
than a handler.

Two reads bypass the trace, by design: `config` is not a location (no
effect writes it — reading it is reading a constant), and `drain`'s
snapshot of `deferred` is the schedule's input, not a transition's read.
One obligation is CONDITIONAL: the schedule fire (`onScheduleTimeout`)
creates one promise per missed occurrence, so its discipline rests on
`expand` giving distinct ids to distinct occurrence timestamps — `expand`
is opaque, so this is an obligation on implementations of `expand`, not a
checkable fact here.
-/

def Eff.isRead : Eff → Bool
  | .read _  => true
  | .write _ => false

def Eff.isWrite : Eff → Bool
  | .read _  => false
  | .write _ => true

/-- The strict two-phase form: a read phase then a write phase — after
    the first write, no read of ANYTHING. True of most handlers; false of
    the settlement and task-timeout families and the per-item loops. Kept
    as a foil: where it fails, the per-location form says why the failure
    is benign. -/
def readsThenWrites (tr : List Eff) : Bool :=
  (tr.dropWhile Eff.isRead).all Eff.isWrite

/-- THE DISCIPLINE: no effect reads a location an earlier effect of the
    same transition wrote — every read is served by the pre-state. -/
def readsPreState (tr : List Eff) : Bool :=
  go [] tr
where
  go : List Loc → List Eff → Bool
    | _, [] => true
    | written, .read l  :: rest => !written.contains l && go written rest
    | written, .write l :: rest => go (l :: written) rest

/-- Run an action from a clean trace; return the effect trace it emits. -/
def traceOf {α} (act : M α) (s : ServerState) : List Eff :=
  (Id.run (act.run { s with trace := [] })).2.trace

/-! ### Fixture

One state, `now := 500`. External promises `a` (with a registered
callback and listener) and `b`; targeted promises `t`/`t2` with acquired
tasks, `q` with a pending task, `h` with a halted task, `u` with a
suspended task; one schedule `s`. -/

def pA : PromiseObject :=
  { id := "a", state := .pending, param := {},
    tags := [("resonate:external", "true")],
    timeoutAt := 1000, createdAt := 0,
    callbacks := ["t"], listeners := ["https://obs"] }

def pB : PromiseObject :=
  { id := "b", state := .pending, param := {},
    tags := [("resonate:external", "true")],
    timeoutAt := 1000, createdAt := 0 }

def pT : PromiseObject :=
  { id := "t", state := .pending, param := {},
    tags := [("resonate:target", "w")], timeoutAt := 2000, createdAt := 0 }

def pT2 : PromiseObject := { pT with id := "t2" }
def pQ  : PromiseObject := { pT with id := "q" }
def pH  : PromiseObject := { pT with id := "h" }
def pU  : PromiseObject := { pT with id := "u" }

def tAcq  : TaskObject :=
  { id := "t", state := .acquired, version := 2, ttl := some 100, pid := some "p1" }
def tAcq2 : TaskObject := { tAcq with id := "t2" }
def tPend : TaskObject := { id := "q", state := .pending, version := 3 }
def tHalt : TaskObject := { id := "h", state := .halted, version := 1 }
def tSus  : TaskObject := { id := "u", state := .suspended, version := 1 }

def sch : Schedule :=
  { id := "s", cron := "* * * * *", promiseId := "p.{{ts}}",
    promiseTimeout := 100, promiseParam := {}, promiseTags := [],
    nextRunAt := 600, createdAt := 0 }

def sFix : ServerState :=
  { promises := [pA, pB, pT, pT2, pQ, pH, pU],
    tasks := [tAcq, tAcq2, tPend, tHalt, tSus],
    schedules := [sch] }

/-! ### The strict form holds where reads have no co-keyed writes

Creation, acquisition, fulfillment, release, halt, continue, resume, the
registrations, the reads, and the schedule handlers: read phase, then
write phase. -/

example : readsThenWrites (traceOf (promiseGet { id := "a" } 500) sFix) := by decide
example : readsThenWrites (traceOf (taskGet { id := "t" } 500) sFix) := by decide
example : readsThenWrites (traceOf (scheduleGet { id := "s" } 500) sFix) := by decide

example : readsThenWrites (traceOf (promiseCreate
    { id := "n", timeoutAt := 1000, param := {},
      tags := [("resonate:target", "w")] } 500) sFix) := by decide
example : readsThenWrites (traceOf (promiseRegisterCallback
    { awaited := "a", awaiter := "t" } 500) sFix) := by decide
-- (`promiseRegisterListener` shares this read-then-write shape; no decide
-- example because its address validation -- `String.startsWith` -- does
-- not kernel-reduce.)

example : readsThenWrites (traceOf (taskCreate
    { pid := "p1", ttl := 100,
      action := { id := "n2", timeoutAt := 1000, param := {},
                  tags := [("resonate:target", "w")] } } 500) sFix) := by decide
example : readsThenWrites (traceOf (taskCreate
    { pid := "p1", ttl := 100,
      action := { id := "q", timeoutAt := 2000, param := {},
                  tags := [("resonate:target", "w")] } } 500) sFix) := by decide
example : readsThenWrites (traceOf (taskAcquire
    { id := "q", version := 3, pid := "p1", ttl := 100 } 500) sFix) := by decide
example : readsThenWrites (traceOf (taskFulfill
    { id := "t", version := 2,
      action := { id := "t", state := .resolved, value := {} } } 500) sFix) := by decide
example : readsThenWrites (traceOf (taskRelease
    { id := "t", version := 2 } 500) sFix) := by decide
example : readsThenWrites (traceOf (taskHalt { id := "t" } 500) sFix) := by decide
example : readsThenWrites (traceOf (taskContinue { id := "h" } 500) sFix) := by decide
example : readsThenWrites (traceOf (taskFence
    { id := "t", version := 2,
      action := .create { id := "n3", timeoutAt := 1000, param := {}, tags := [] } }
    500) sFix) := by decide

example : readsThenWrites (traceOf (onResume
    { awaited := "a", awaiter := "u" } 500) sFix) := by decide
example : readsThenWrites (traceOf (scheduleCreate
    { id := "s", cron := "* * * * *", promiseId := "p.{{ts}}",
      promiseTimeout := 100, promiseParam := {}, promiseTags := [] } 500) sFix) := by
  decide
example : readsThenWrites (traceOf (scheduleDelete { id := "s" } 500) sFix) := by
  decide

/-! ### Where the strict form fails — and the discipline holds

`promiseSettle` on `a`, the trace in full: the task read lands after the
promise writes. The naive theorem is false; the per-location theorem is
the reason it does not matter. -/

example : traceOf (promiseSettle { id := "a", state := .resolved, value := {} } 500) sFix
    = [.read  (.promise "a"),
       .write (.promise "a"),
       .write (.promiseTimeout "a"),
       .read  (.task "a"),
       .write (.message "a:notify:https://obs"),
       .write (.deferred "a" "t")] := by decide

example : readsThenWrites (traceOf (promiseSettle
    { id := "a", state := .resolved, value := {} } 500) sFix) = false := by decide
example : readsPreState (traceOf (promiseSettle
    { id := "a", state := .resolved, value := {} } 500) sFix) := by decide

-- Settling a promise with a co-keyed task: promise `t` is written, then
-- task `t` is read — same id, different location. Pre-state read.
example : readsPreState (traceOf (promiseSettle
    { id := "t", state := .resolved, value := {} } 500) sFix) := by decide

-- The timeout family: write task state, then read the co-keyed promise
-- for the dispatch target.
example : readsThenWrites (traceOf (Timeouts.onPromiseTimeout "a" 1500) sFix)
    = false := by decide
example : readsPreState (traceOf (Timeouts.onPromiseTimeout "a" 1500) sFix) := by
  decide
example : readsThenWrites (traceOf (Timeouts.onTaskRetryTimeout "q" 500) sFix)
    = false := by decide
example : readsPreState (traceOf (Timeouts.onTaskRetryTimeout "q" 500) sFix) := by
  decide
example : readsThenWrites (traceOf (Timeouts.onTaskLeaseTimeout "t" 500) sFix)
    = false := by decide
example : readsPreState (traceOf (Timeouts.onTaskLeaseTimeout "t" 500) sFix) := by
  decide

-- The per-item loops: distinct keys, so the alternation reads only the
-- pre-state — `taskSuspend` by grace of its duplicate-awaited 400.
example : readsThenWrites (traceOf (taskSuspend
    { id := "t", version := 2,
      actions := [{ awaited := "a", awaiter := "t" },
                  { awaited := "b", awaiter := "t" }] } 500) sFix) = false := by decide
example : readsPreState (traceOf (taskSuspend
    { id := "t", version := 2,
      actions := [{ awaited := "a", awaiter := "t" },
                  { awaited := "b", awaiter := "t" }] } 500) sFix) := by decide

example : readsThenWrites (traceOf (taskHeartbeat
    { pid := "p1", tasks := [{ id := "t", version := 2 },
                             { id := "t2", version := 2 }] } 500) sFix)
    = false := by decide
example : readsPreState (traceOf (taskHeartbeat
    { pid := "p1", tasks := [{ id := "t", version := 2 },
                             { id := "t2", version := 2 }] } 500) sFix) := by decide

-- A fenced settle inherits settlement's shape; the fence's own reads all
-- precede it.
example : readsPreState (traceOf (taskFence
    { id := "t", version := 2,
      action := .settle { id := "a", state := .resolved, value := {} } } 500) sFix) := by
  decide

/-! ### The boundary: `drain` reads its own writes, across steps

Two deferred resumes for the same awaiter. The first `onResume` wakes the
task; the second reads the task the first wrote — that read-back is the
buffering behavior. Each step is a clean transition; the composition is
not, which is why `drain` is a schedule and the theorem quantifies over
transitions. -/

def sTwo : ServerState :=
  { sFix with deferred := [{ awaited := "a", awaiter := "u" },
                           { awaited := "b", awaiter := "u" }] }

def sTwoMid : ServerState :=
  runM (do undefer { awaited := "a", awaiter := "u" }
           let _ ← onResume { awaited := "a", awaiter := "u" } 500) sTwo

example : readsPreState (traceOf (onResume
    { awaited := "a", awaiter := "u" } 500) sTwo) := by decide
example : readsPreState (traceOf (onResume
    { awaited := "b", awaiter := "u" } 500) sTwoMid) := by decide
example : readsPreState (traceOf (drain 500) sTwo) = false := by decide

-- The read-back is load-bearing: the second resume buffered into the
-- task the first one woke.
example :
    ((runM (drain 500) sTwo).tasks.find? (·.id == "u")).map
      (fun t => t.state == .pending && t.resumes == ["a", "b"]) = some true := by
  decide
