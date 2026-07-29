import «01-objects».«state»
import «abstract».«01-state»

/-!  # Refinement — the abstraction function

Direction: the BASE machine (`01-objects`/`02-actions`, rich in auxiliary
state) is the concrete spec; the COALESCED machine (`abstract/`) is the
abstract one. The claim under investigation: every base behavior is a
coalesced behavior — base ⊑ coalesced — under the state abstraction `alpha`
below, with each base step mapping to a finite sequence of coalesced steps
(the handler plus catch-up rules).

`alpha` is purely structural and TIME-INDEPENDENT — deliberately. It does
not project: a stored-pending promise past its deadline maps to a
stored-pending promise. All timing lag lives in the SIMULATION RELATION,
not the abstraction function:

    R(s, t)  ⇔  t is reachable from alpha(s) by fact rules alone
                (R1/R2 on any targets — the coalesced machine ran AHEAD
                on facts, forced by touches), and alpha(s) is reachable
                from t by drain rules alone (R3/R4/R6 — the coalesced
                machine lags BEHIND on messages and wakes, which the
                base machine performs inline).

What `alpha` folds away:

* `deferred` — a base deferred resume `(awaited, awaiter)` is the
  coalesced machine's retained callback: folded back onto the awaited
  promise's `callbacks`. (Stage 1 of the base wake pipeline becomes
  indistinguishable from stage 0 — the coalesced machine has one stage,
  "still on the promise".)
* `promiseTimeouts`, `scheduleTimeouts` — pure mirrors of `timeoutAt` /
  `nextRunAt`; dropped.
* `taskTimeouts` kind 1 (lease) — becomes the task's `expiresAt`.
* `taskTimeouts` kind 0 (retry/delay) — dropped: the dispatch rule R6 is
  always enabled for a dispatchable task, so retry instants need no
  representation. (This is sound for simulation because a base retry
  firing is state-equal to an R6 firing — the outbox upsert is keyed.)
* `config` — the retry cadence has no meaning without retry timers.

Because base handlers append callbacks in order while `alpha` folds the
LIFO deferred list back in, list ORDER in `callbacks`/`listeners` (and
across the object lists) is not preserved — and is not observable: no
response exposes it, and batch drains commute. State comparison is
therefore up-to-order: `stateEq` below.  -/

namespace Refinement

deriving instance BEq for ServerModel.Value
deriving instance BEq for ServerModel.PromiseRecord
deriving instance BEq for ServerModel.TaskRecord
deriving instance BEq for ServerModel.Message
deriving instance BEq for ServerModel.OutboxEntry
deriving instance BEq for ServerModel.Schedule
deriving instance BEq for ServerModel.PromiseGetRes
deriving instance BEq for ServerModel.PromiseCreateRes
deriving instance BEq for ServerModel.PromiseSettleRes
deriving instance BEq for ServerModel.TaskGetRes
deriving instance BEq for ServerModel.TaskCreateRes
deriving instance BEq for ServerModel.TaskHaltRes
deriving instance BEq for AbstractModel.TaskObject

/-- Equality of lists as finite multisets-up-to-membership (the object
    lists are keyed, so membership equality is what matters). -/
def eqSet [BEq α] (a b : List α) : Bool :=
  a.all b.contains && b.all a.contains

def eqSetBy (eq : α → α → Bool) (a b : List α) : Bool :=
  a.all (fun x => b.any (eq x)) && b.all (fun x => a.any (eq x))

/-- Promise equality with `callbacks`/`listeners` as sets. -/
def promiseEq (a b : AbstractModel.PromiseObject) : Bool :=
  a.id == b.id && a.state == b.state && a.param == b.param
    && a.value == b.value && a.tags == b.tags
    && a.timeoutAt == b.timeoutAt && a.createdAt == b.createdAt
    && a.settledAt == b.settledAt
    && eqSet a.callbacks b.callbacks && eqSet a.listeners b.listeners

/-- Coalesced-state equality up to list order. -/
def stateEq (a b : AbstractModel.ServerState) : Bool :=
  eqSetBy promiseEq a.promises b.promises
    && eqSet a.tasks b.tasks
    && eqSet a.schedules b.schedules
    && eqSet a.outbox b.outbox

def absPromise (p : ServerModel.PromiseObject) : AbstractModel.PromiseObject :=
  { id := p.id, state := p.state, param := p.param, value := p.value,
    tags := p.tags, timeoutAt := p.timeoutAt, createdAt := p.createdAt,
    settledAt := p.settledAt, callbacks := p.callbacks,
    listeners := p.listeners }

def absTask (timeouts : List ServerModel.TaskTimeout)
    (t : ServerModel.TaskObject) : AbstractModel.TaskObject :=
  { id := t.id, state := t.state, version := t.version, ttl := t.ttl,
    pid := t.pid, resumes := t.resumes,
    expiresAt :=
      (timeouts.find? (fun e => e.id == t.id && e.kind == 1)).map (·.timeout) }

/-- Fold one deferred resume back onto its awaited promise. -/
def addDeferred (ps : List AbstractModel.PromiseObject)
    (d : ServerModel.ResumeReq) : List AbstractModel.PromiseObject :=
  ps.map fun p => if p.id == d.awaited then p.addCallback d.awaiter else p

/-- THE ABSTRACTION. -/
def alpha (s : ServerModel.ServerState) : AbstractModel.ServerState :=
  { promises := s.deferred.foldl addDeferred (s.promises.map absPromise)
    tasks := s.tasks.map (absTask s.taskTimeouts)
    schedules := s.schedules
    outbox := s.outbox }

/-- Run a base action: (response, post-state). -/
def runB {α} (act : ServerModel.M α) (s : ServerModel.ServerState) :
    α × ServerModel.ServerState :=
  Id.run (act.run s)

/-- Run a coalesced action: (response, post-state). -/
def runC {α} (act : AbstractModel.M α) (s : AbstractModel.ServerState) :
    α × AbstractModel.ServerState :=
  Id.run (act.run s)

end Refinement
