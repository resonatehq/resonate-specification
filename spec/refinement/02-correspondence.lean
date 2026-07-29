import «refinement».«01-abstraction»
import «02-actions».«P-01-promise.get»
import «02-actions».«P-03-promise.settle»
import «02-actions».«02-timeouts»
import «02-actions».«03-resume»
import «abstract».«05-rules»

/-!  # Refinement — step correspondence, executed

Each scenario runs a base transition and its coalesced counterpart — the
same handler plus the catch-up rules that discharge what the base
machine did inline — and checks, by execution:

  * the RESPONSES are equal (the observable), and
  * the post-states satisfy the simulation relation, which in each
    scenario reduces to an executable `stateEq` between the coalesced
    post-state and `alpha` of the base post-state, advanced by
    explicitly named fact rules where the coalesced machine ran ahead.

The full correspondence table (every base handler and τ-step, its
coalesced sequence, and the proof burden) is in `refinement/README.md`.

  S1  settle pipeline    base `step ∘ promiseSettle` (settle + inline
                         unblocks + deferred resumes + drain)
                         =  settle ; notify ; resume ; dispatch
  S2  timeout pipeline   base `step ∘ onPromiseTimeout`
                         =  R1 ; R2 ; notify ; resume ; dispatch
  S3  read materializes  base `promiseGet` projects and writes nothing;
                         coalesced `promiseGet` writes fact P — the
                         coalesced machine is AHEAD by exactly R1
  S4  lease expiry       base `onTaskLeaseTimeout` (flip + re-arm + emit)
                         =  leaseExpiry ; dispatch
  S6  timeout wins       base `drain` discards an expired awaiter's
                         resume; coalesced `resume` drops it via touch —
                         AHEAD by exactly R1 ; R2 on the awaiter
  S7  delayed dispatch   base delayed create + retry-τ at the delay
                         =  create ; dispatch (guarded by the delay tag)
-/

namespace Refinement

open ServerModel (PromiseSettleReq PromiseGetReq PromiseCreateReq)

/-! ### Fixtures

`a` — external promise, pending, deadline 1000, one awaiter callback
(`t1`) and one listener. `t1` — targeted promise (worker `w1`, deadline
2000) whose task is suspended awaiting `a`.  -/

def bA : ServerModel.PromiseObject :=
  { id := "a", state := .pending, param := {},
    tags := [("resonate:external", "true")],
    timeoutAt := 1000, createdAt := 0,
    callbacks := ["t1"], listeners := ["http://l"] }

def bT1P : ServerModel.PromiseObject :=
  { id := "t1", state := .pending, param := {},
    tags := [("resonate:target", "w1")],
    timeoutAt := 2000, createdAt := 0 }

def bT1 : ServerModel.TaskObject :=
  { id := "t1", state := .suspended, version := 1 }

/-! ### S1 — the settle pipeline -/

def s1Base : ServerModel.ServerState :=
  { promises := [bA, bT1P], tasks := [bT1],
    promiseTimeouts := [{ id := "a", timeout := 1000 }] }

def s1SettleReq : PromiseSettleReq := { id := "a", state := .resolved, value := {} }

def s1B := runB (step (promiseSettle s1SettleReq 500) 500) s1Base

def s1C := runC (do
    let res ← AbstractModel.promiseSettle s1SettleReq 500
    AbstractModel.Rules.notify "a" 1 500      -- batch: the one listener
    AbstractModel.Rules.resume "a" 1 500      -- batch: the one awaiter
    AbstractModel.Rules.dispatch "t1" 500     -- the woken task's execute
    return res)
  (alpha s1Base)

example : s1B.1 == s1C.1 := by decide
example : stateEq (alpha s1B.2) s1C.2 := by decide

/-! ### S2 — the timeout pipeline (awaited promise is itself targeted,
    so fact T fires on its task too) -/

def bA2 : ServerModel.PromiseObject :=
  { bA with tags := [("resonate:external", "true"), ("resonate:target", "wa")],
            timeoutAt := 300 }

def bTA : ServerModel.TaskObject :=
  { id := "a", state := .acquired, version := 2, ttl := some 100, pid := some "w" }

def s2Base : ServerModel.ServerState :=
  { promises := [bA2, bT1P], tasks := [bTA, bT1],
    promiseTimeouts := [{ id := "a", timeout := 300 }],
    taskTimeouts := [{ id := "a", kind := 1, timeout := 250 }] }

def s2B := runB (step (Timeouts.onPromiseTimeout "a" 500) 500) s2Base

def s2C := runC (do
    AbstractModel.Rules.promiseTimeout "a" 500
    AbstractModel.Rules.taskFulfillment "a" 500
    AbstractModel.Rules.notify "a" 9 500      -- batch: all
    AbstractModel.Rules.resume "a" 9 500      -- batch: all
    AbstractModel.Rules.dispatch "t1" 500)
  (alpha s2Base)

example : stateEq (alpha s2B.2) s2C.2 := by decide

/-! ### S3 — a read materializes: the coalesced machine runs AHEAD of the
    base machine by exactly one fact rule -/

def bB : ServerModel.PromiseObject :=
  { id := "b", state := .pending, param := {}, tags := [],
    timeoutAt := 300, createdAt := 0 }

def s3Base : ServerModel.ServerState := { promises := [bB] }

def s3B := runB (promiseGet { id := "b" } 500) s3Base
def s3C := runC (AbstractModel.promiseGet { id := "b" } 500) (alpha s3Base)

-- Same observation: the base serves the projection, the coalesced
-- machine serves the materialized record — byte-identical, stamped at
-- the deadline.
example : s3B.1 == s3C.1 := by decide
-- The base post-state is UNCHANGED (projection writes nothing) …
example : stateEq (alpha s3B.2) (alpha s3Base) := by decide
-- … and the coalesced post-state is alpha of it advanced by R1 alone.
example : stateEq s3C.2
    (runC (AbstractModel.Rules.promiseTimeout "b" 500) (alpha s3B.2)).2 := by
  decide
-- Without the R1 advance the states genuinely differ — the lag is real,
-- not an artifact of a too-coarse `stateEq`.
example : stateEq s3C.2 (alpha s3B.2) = false := by decide

/-! ### S4 — lease expiry -/

def bC : ServerModel.PromiseObject :=
  { id := "c", state := .pending, param := {},
    tags := [("resonate:target", "wc")], timeoutAt := 2000, createdAt := 0 }

def bTC : ServerModel.TaskObject :=
  { id := "c", state := .acquired, version := 3, ttl := some 100, pid := some "w" }

def s4Base : ServerModel.ServerState :=
  { promises := [bC], tasks := [bTC],
    promiseTimeouts := [{ id := "c", timeout := 2000 }],
    taskTimeouts := [{ id := "c", kind := 1, timeout := 400 }] }

def s4B := runB (Timeouts.onTaskLeaseTimeout "c" 500) s4Base

def s4C := runC (do
    AbstractModel.Rules.leaseExpiry "c" 500
    AbstractModel.Rules.dispatch "c" 500)
  (alpha s4Base)

example : stateEq (alpha s4B.2) s4C.2 := by decide

/-! ### S6 — timeout always wins: base `drain` discards the resume of an
    awaiter past its own deadline and leaves cleanup to the timeout path;
    the coalesced `resume` reaches the same end through the touch, which
    fulfills the awaiter on the spot — AHEAD by R1 ; R2 -/

def bASettled : ServerModel.PromiseObject :=
  { id := "a", state := .resolved, param := {},
    tags := [("resonate:external", "true")],
    timeoutAt := 1000, createdAt := 0, settledAt := some 100 }

def bT1PExp : ServerModel.PromiseObject := { bT1P with timeoutAt := 300 }

def s6Base : ServerModel.ServerState :=
  { promises := [bASettled, bT1PExp], tasks := [bT1],
    deferred := [{ awaited := "a", awaiter := "t1" }],
    promiseTimeouts := [{ id := "t1", timeout := 300 }] }

def s6B := runB (drain 500) s6Base
def s6C := runC (AbstractModel.Rules.resume "a" 1 500) (alpha s6Base)

example : stateEq s6C.2
    (runC (do
        AbstractModel.Rules.promiseTimeout "t1" 500
        AbstractModel.Rules.taskFulfillment "t1" 500)
      (alpha s6B.2)).2 := by
  decide

/-! ### S7 — delayed create, then dispatch at the delay -/

def s7Req : PromiseCreateReq :=
  { id := "d", timeoutAt := 2000, param := {},
    tags := [("resonate:target", "wd"), ("resonate:delay", "800")] }

def s7B := runB (promiseCreate s7Req 100) ServerModel.ServerState.init
def s7C := runC (AbstractModel.promiseCreate s7Req 100) AbstractModel.ServerState.init

-- Creation corresponds with NO lag: neither machine emits before the
-- delay. (`native_decide`: the delay tag's `String.toNat!` does not
-- reduce in the kernel.)
example : s7B.1 == s7C.1 := by native_decide
example : stateEq (alpha s7B.2) s7C.2 := by native_decide

-- Before the delay, R6 refuses (guard: the delay tag) …
example : stateEq (runC (AbstractModel.Rules.dispatch "d" 100) s7C.2).2 s7C.2 := by
  native_decide

-- … at the delay, base retry-τ and R6 emit the same execute.
def s7B' := runB (Timeouts.onTaskRetryTimeout "d" 800) s7B.2
def s7C' := runC (AbstractModel.Rules.dispatch "d" 800) s7C.2

example : stateEq (alpha s7B'.2) s7C'.2 := by native_decide

end Refinement
