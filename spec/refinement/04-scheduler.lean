import «refinement».«02-correspondence»

/-!  # Refinement — higher fidelity: the scheduler reification

`alpha` deliberately DROPS the concrete machine's auxiliary state
(timeout sets, deferred queue, config), and the simulation relation of
`01-abstraction.lean` absorbs the resulting slack existentially. This
file tightens the mapping. Nothing actually needs to be dropped, because
the auxiliary state is not protocol state at all — it is the reification
of a SCHEDULER for the abstract machine's rules:

    concrete  =  abstract  +  scheduler

`sigma` extracts the scheduler: every armed timer and every deferred
entry is a COMMITMENT to fire a specific abstract rule, most with a due
instant. Under the pair `(alpha, sigma)` the concrete spec maps onto the
abstract spec with full fidelity:

  * every concrete τ-step is the DISCHARGE of a due commitment — its
    state effect a fixed abstract rule sequence (that half is
    `02-correspondence.lean`), its commitment effect a fixed
    re-commitment policy (this file):

      concrete τ            discharges          re-commits
      ────────────────────  ──────────────────  ─────────────────────────
      onPromiseTimeout id   promiseTimeout id   one resume per callback
      onResume (a,t), wake  resume a t          dispatch t (now+retry)
      onTaskRetryTimeout    dispatch id         dispatch id (now+retry)
      onTaskLeaseTimeout    leaseExpiry id      dispatch id (now+retry)
      onScheduleTimeout     scheduleFire id     scheduleFire id next

  * every commitment class is DERIVABLE from `alpha`'s image: promise
    timeouts from external ∧ pending, lease expiries from acquired ∧
    `expiresAt`, dispatches from pending ∧ `retryAt`, resumes from the
    callbacks `alpha` retains on settled promises (schedule fires
    mirror `nextRunAt` likewise).

So `sigma` adds nothing to `alpha`: the mapping is LOSSLESS, and the
concrete machine's auxiliary state is redundant given the abstract
state. What remains concrete-only is not state but policy — the
`now + retryTimeout` re-commitment constant, recovered by instantiating
R6's `next` parameter. This collapses the "behind" half of the
simulation relation — the pending drains are no longer existential,
they are read off the state — while the "ahead" half (facts forced by
touches, and with it obstruction D1) remains.

One granularity note: the concrete drain walks its deferred queue in
LIFO order while the abstract `resume` rule drains a callback prefix.
Discharges of distinct commitments touch distinct awaiter tasks and
commute, so the checks below use single-entry drains and set equality;
the general statement would let the batch rules take a chosen sublist
rather than a count.  -/

namespace Refinement

open ServerModel (PromiseSettleReq)

/-- A scheduler commitment: an abstract rule firing the concrete
    machine has promised to perform. -/
inductive Pending
  | promiseTimeout (id : String) (due : Nat)
  | leaseExpiry    (id : String) (due : Nat)
  | dispatch       (id : String) (due : Nat)
  | scheduleFire   (id : String) (due : Nat)
  | resume         (awaited awaiter : String)
  deriving Repr, BEq

def Pending.isPromiseTimeout : Pending → Bool
  | .promiseTimeout .. => true | _ => false

def Pending.isLeaseExpiry : Pending → Bool
  | .leaseExpiry .. => true | _ => false

def Pending.isResume : Pending → Bool
  | .resume .. => true | _ => false

/-- THE SCHEDULER EXTRACTION: the concrete machine's entire auxiliary
    state, read as commitments. `alpha` and `sigma` together lose
    nothing but `config`. -/
def sigma (s : ServerModel.ServerState) : List Pending :=
  s.promiseTimeouts.map (fun e => .promiseTimeout e.id e.timeout)
    ++ s.taskTimeouts.map (fun e =>
        if e.kind == 1 then .leaseExpiry e.id e.timeout
        else .dispatch e.id e.timeout)
    ++ s.scheduleTimeouts.map (fun e => .scheduleFire e.id e.timeout)
    ++ s.deferred.map (fun d => .resume d.awaited d.awaiter)

/-! ### Commitment bookkeeping across the pipelines

The fixtures are those of `02-correspondence.lean`; here the concrete
steps run WITHOUT the eager `step` wrapper, so the mid-pipeline
commitments are visible.  -/

-- Settle discharges nothing but COMMITS one resume per callback
-- (and disarms the settled promise's own timeout).
def w1 := runB (promiseSettle s1SettleReq 500) s1Base

example : eqSet (sigma s1Base)
    [.promiseTimeout "a" 1000, .promiseTimeout "t1" 2000] := by decide
example : eqSet (sigma w1.2)
    [.promiseTimeout "t1" 2000, .resume "a" "t1"] := by decide

-- The drain discharges the resume commitment; the wake re-commits a
-- dispatch at now + retryTimeout (the re-commitment policy, constant
-- from `config`).
def w2 := runB (drain 500) w1.2

example : eqSet (sigma w2.2)
    [.promiseTimeout "t1" 2000, .dispatch "t1" 5500] := by decide

-- State effect of that discharge = the abstract rules, on the nose.
example : stateEq (alpha w2.2)
    (runC (do
        AbstractModel.Rules.resume "a" 1 500
        AbstractModel.Rules.dispatch "t1" 5500 500)
      (alpha w1.2)).2 := by decide

-- A promise-timeout discharge swaps itself for the resume commitments
-- (and the dead task's lease commitment evaporates with fact T).
def w3 := runB (Timeouts.onPromiseTimeout "a" 500) s2Base

example : eqSet (sigma s2Base)
    [.promiseTimeout "a" 300, .promiseTimeout "t1" 2000,
     .leaseExpiry "a" 250] := by decide
example : eqSet (sigma w3.2)
    [.promiseTimeout "t1" 2000, .resume "a" "t1"] := by decide

-- A lease-expiry discharge re-commits a dispatch.
example : eqSet (sigma s4B.2)
    [.promiseTimeout "c" 2000, .dispatch "c" 5500] := by decide

-- A dispatch discharge re-commits itself, retryTimeout later.
example : eqSet (sigma s7B.2)
    [.promiseTimeout "d" 2000, .dispatch "d" 800] := by native_decide
example : eqSet (sigma s7B'.2)
    [.promiseTimeout "d" 2000, .dispatch "d" 5800] := by native_decide

/-! ### Derivability: which commitments does `alpha` already know?

Three of the four timed classes (and the resumes) are functions of the
abstract image — the concrete machine stores them separately only
because its rules cannot guard on object state the way the abstract
rules do.  -/

def derivedPromiseTimeouts (t : AbstractModel.ServerState) : List Pending :=
  (t.promises.filter (fun p => p.external && p.state == .pending)).map
    (fun p => .promiseTimeout p.id p.timeoutAt)

def derivedLeaseExpiries (t : AbstractModel.ServerState) : List Pending :=
  t.tasks.filterMap fun tk =>
    match tk.expiresAt with
    | some due => if tk.state == .acquired then some (.leaseExpiry tk.id due) else none
    | none => none

def derivedResumes (t : AbstractModel.ServerState) : List Pending :=
  (t.promises.filter (fun p => p.state != .pending)).flatMap
    (fun p => p.callbacks.map (fun c => .resume p.id c))

example : eqSet (derivedPromiseTimeouts (alpha s1Base))
    ((sigma s1Base).filter (·.isPromiseTimeout)) := by decide
example : eqSet (derivedPromiseTimeouts (alpha w1.2))
    ((sigma w1.2).filter (·.isPromiseTimeout)) := by decide
example : eqSet (derivedLeaseExpiries (alpha s2Base))
    ((sigma s2Base).filter (·.isLeaseExpiry)) := by decide
example : eqSet (derivedResumes (alpha w1.2))
    ((sigma w1.2).filter (·.isResume)) := by decide
example : eqSet (derivedResumes (alpha w3.2))
    ((sigma w3.2).filter (·.isResume)) := by decide

/-! ### … and with `retryAt` on the task, the dispatch dues too

The abstract task now carries its dispatch due time, so the last
commitment class is also a function of the abstract image — `sigma` is
DERIVABLE FROM `alpha` in full, and the mapping is lossless: the
concrete machine's auxiliary state is redundant given the abstract
state. (What remains concrete-only is not state but POLICY — the
`now + retryTimeout` re-arm, recovered by instantiating R6's `next`
parameter, as every dispatch above does.)  -/

def Pending.isDispatch : Pending → Bool
  | .dispatch .. => true | _ => false

def derivedDispatches (t : AbstractModel.ServerState) : List Pending :=
  t.tasks.filterMap fun tk =>
    match tk.retryAt with
    | some due => if tk.state == .pending then some (.dispatch tk.id due) else none
    | none => none

example : eqSet (derivedDispatches (alpha w2.2))
    ((sigma w2.2).filter (·.isDispatch)) := by decide
example : eqSet (derivedDispatches (alpha s7B.2))
    ((sigma s7B.2).filter (·.isDispatch)) := by native_decide
example : eqSet (derivedDispatches (alpha s7B'.2))
    ((sigma s7B'.2).filter (·.isDispatch)) := by native_decide

-- Pacing is now visible to `alpha`: firing the retry τ again (on
-- schedule, at its due instant) moves `retryAt`, and the abstract
-- images DIFFER (before `retryAt`, this pair was the alpha-equal,
-- sigma-different witness) — matched, as everywhere, by R6 with the
-- base policy instantiated.
--
-- One asymmetry surfaces here: the base τ handler is UNGUARDED — its
-- due instant lives only in the timer it discharges, so an adversarial
-- environment may fire it early — while R6 is self-guarded by
-- `retryAt`. An off-schedule base firing is observationally a
-- keyed-upsert stutter (same entry, same version) plus a moved due
-- time, and its alpha-image is reached by the next on-schedule R6;
-- putting the due time into the state is exactly what makes the
-- abstract machine refuse to fire a commitment before it exists.
def w4 := runB (Timeouts.onTaskRetryTimeout "d" 5800) s7B'.2

example : stateEq (alpha s7B'.2) (alpha w4.2) = false := by native_decide
example : eqSet (sigma w4.2)
    [.promiseTimeout "d" 2000, .dispatch "d" 10800] := by native_decide
example : stateEq (alpha w4.2)
    (runC (AbstractModel.Rules.dispatch "d" 10800 5800) (alpha s7B'.2)).2 := by
  native_decide

end Refinement
