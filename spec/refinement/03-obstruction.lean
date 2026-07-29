import «refinement».«01-abstraction»
import «02-actions».«02-timeouts»
import «02-actions».«T-01-task.get»
import «02-actions».«T-02-task.create»
import «02-actions».«T-09-task.halt»
import «abstract».«03-tasks»
import «abstract».«05-rules»

/-!  # Refinement — why base ⊑ coalesced does NOT hold, exactly

The correspondence of `02-correspondence.lean` fails to extend to a full
refinement, and the failure is precise and fundamental — not an artifact
of how either spec is written.

## D1 — observation without commitment (`taskGet` then `taskHalt`)

The base machine can OBSERVE a logical fact without COMMITTING it:
`taskGet` on a task whose own promise is past its deadline serves the
projected `.fulfilled` view and writes nothing. The stored task is still
`.suspended`, and `taskHalt` — which reads the task alone, deliberately,
because halt is an operation on the material coordination layer — then
happily halts it: `200`.

A no-projection machine cannot produce this pair. To serve `.fulfilled`
at the `taskGet` it must either project (excluded by construction) or
materialize — and once materialized, the task IS `.fulfilled` and the
halt answers `409`. The information "observed but not committed" has no
carrier in the coalesced state space; it is erased at the touch.

    base:       taskGet → fulfilled   ; taskHalt → 200   (halted)
    coalesced:  taskGet → fulfilled   ; taskHalt → 409

So base ⋢ coalesced on the nose. The witness needs all three of:
a projected read, a later material-state-branching handler, and a lazy
timeout schedule between them — and `taskHalt` is the ONLY base handler
that branches on material task state without consulting the promise, so
this is the only such observation point.

What would restore refinement, pick one:

  1. Base-side: make `taskHalt` consult the task's promise (project, and
     refuse once the own promise is logically settled). Halting a
     logically dead task is ephemeral anyway — the base timeout τ will
     overwrite `.halted` with `.fulfilled` — so the `200` carries no
     durable meaning.
  2. Observation-side: weaken the refinement's observable to identify
     `200`/`409` on halt-of-a-dead-task (both post-states abstract to
     the same coalesced state — it is ONLY the status that differs).
  3. Nothing coalesced-side. The coalesced machine cannot be repaired
     without re-introducing a projected (served-but-unstored) view,
     which is the feature this spec exists to remove.

## D2 — the abstraction surfacing base defects (`taskCreate`, exists-path)

On an existing targeted promise, base `taskCreate` reads the promise and
task RAW: it serves an unprojected promise record — contradicting the
base spec's own documented invariant that every promise-bearing response
projects — and re-acquires (arms a fresh lease on) a task whose promise
is past its deadline. The coalesced machine, forced by construction to
materialize on touch, answers with the settled promise and fulfilled
task. This divergence is not fundamental — it marks a defect in the base
spec, found by trying to refine it.  -/

namespace Refinement

open ServerModel (TaskGetReq TaskHaltReq TaskCreateReq)

/-! ### D1, executed -/

def bH : ServerModel.PromiseObject :=
  { id := "h", state := .pending, param := {},
    tags := [("resonate:target", "wh")], timeoutAt := 300, createdAt := 0 }

def bTH : ServerModel.TaskObject :=
  { id := "h", state := .suspended, version := 1 }

/-- Deadline passed (now = 500), timeout τ not yet fired. -/
def d1Base : ServerModel.ServerState :=
  { promises := [bH], tasks := [bTH],
    promiseTimeouts := [{ id := "h", timeout := 300 }] }

def d1BGet  := runB (taskGet { id := "h" } 500) d1Base
def d1BHalt := runB (taskHalt { id := "h" } 500) d1BGet.2

def d1CGet  := runC (AbstractModel.taskGet { id := "h" } 500) (alpha d1Base)
def d1CHalt := runC (AbstractModel.taskHalt { id := "h" } 500) d1CGet.2

-- Both machines answer the read identically: `.fulfilled`, at the deadline.
example : d1BGet.1 == d1CGet.1 := by decide
example : d1BGet.1.task.map (·.state) = some .fulfilled := by decide

-- But the base machine did not commit the observation …
example : (d1BGet.2.tasks.find? (·.id == "h")).map (·.state)
    = some .suspended := by decide
-- … while the coalesced machine had to.
example : (d1CGet.2.tasks.find? (·.id == "h")).map (·.state)
    = some .fulfilled := by decide

-- The halt detects the difference: THE REFINEMENT COUNTEREXAMPLE.
example : d1BHalt.1.status = 200 := by decide
example : d1CHalt.1.status = 409 := by decide

-- Resolution 2's premise, verified: the divergence is RESPONSE-ONLY and
-- ephemeral. The base machine's `.halted` lasts exactly until its own
-- timeout τ overwrites it with `.fulfilled` — after which the states
-- coincide again on the nose:
example : stateEq
    (alpha (runB (Timeouts.onPromiseTimeout "h" 500) d1BHalt.2).2)
    d1CHalt.2 := by decide

/-! ### D2, executed -/

def bE : ServerModel.PromiseObject :=
  { id := "e", state := .pending, param := {},
    tags := [("resonate:target", "we")], timeoutAt := 300, createdAt := 0 }

def bTE : ServerModel.TaskObject := { id := "e", state := .pending, version := 0 }

def d2Base : ServerModel.ServerState := { promises := [bE], tasks := [bTE] }

def d2Req : TaskCreateReq :=
  { pid := "w2", ttl := 100,
    action := { id := "e", timeoutAt := 9999, param := {},
                tags := [("resonate:target", "we")] } }

def d2B := runB (taskCreate d2Req 500) d2Base
def d2C := runC (AbstractModel.taskCreate d2Req 500) (alpha d2Base)

-- The base machine serves the promise RAW — `.pending` past its own
-- deadline, violating its documented projection totality — and arms a
-- lease on the dead task.
example : d2B.1.promise.map (·.state) = some .pending := by decide
example : d2B.1.task.map (·.state) = some .acquired := by decide

-- The coalesced machine cannot: the touch settles and fulfills first.
example : d2C.1.promise.map (·.state) = some .rejectedTimedout := by decide
example : d2C.1.task.map (·.state) = some .fulfilled := by decide

/-! ### D3 — unguarded τ handlers: the base machine trusts its scheduler

A timer entry means "not before" in BOTH machines — but only the
coalesced machine enforces it. The base machine's τ handlers never
check their own due times; the "fire when due, not before" discipline
is an unstated contract on the environment. Fired off-schedule,
`onPromiseTimeout` SETTLES A LIVE PROMISE — stamping a `settledAt` that
lies in the future — where the coalesced R1, guarded by the deadline
itself, refuses.

So around timers the refinement gap runs in the OPPOSITE direction from
what "abstraction" suggests: the base transition relation is the more
permissive one, admitting scheduler misbehavior the coalesced machine
makes unrepresentable. Like D2 this is not fundamental: base ⊑
coalesced holds over environments that fire τ only when due (the
intended reading of an armed timer), or unconditionally after adding
defensive due-time guards to the base handlers.  -/

-- Deadline 300, fired at 100.
def d3B := runB (Timeouts.onPromiseTimeout "h" 100) d1Base
def d3C := runC (AbstractModel.Rules.promiseTimeout "h" 100) (alpha d1Base)

-- The base machine settles a promise with 200 time units to live —
-- and postdates the settlement to a future instant.
example : (d3B.2.promises.find? (·.id == "h")).map (fun p => (p.state, p.settledAt))
    = some (.rejectedTimedout, some 300) := by decide

-- The coalesced machine's guard is the deadline itself: no-op.
example : (d3C.2.promises.find? (·.id == "h")).map (·.state)
    = some .pending := by decide

end Refinement
