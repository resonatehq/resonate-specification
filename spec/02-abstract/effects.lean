import «02-abstract».«state»

namespace AbstractModel
namespace E

open ServerModel (Tags Value PromiseState TaskState PromiseRecord TaskRecord
                  Schedule Message OutboxEntry PromiseCreateReq)

inductive Effect
  | setPromise  (p : PromiseObject)
  | setTask     (t : TaskObject)
  | setSchedule (s : Schedule)
  | delSchedule (id : String)
  | setMessage  (address : String) (msg : Message)
  deriving Repr

def Effect.apply (s : ServerState) : Effect → ServerState
  | .setPromise p  => { s with promises  := p :: s.promises.filter (·.id != p.id) }
  | .setTask t     => { s with tasks     := t :: s.tasks.filter (·.id != t.id) }
  | .setSchedule c => { s with schedules := c :: s.schedules.filter (·.id != c.id) }
  | .delSchedule i => { s with schedules := s.schedules.filter (·.id != i) }
  | .setMessage a m =>
      let entry := OutboxEntry.mk a m
      { s with outbox := entry :: s.outbox.filter (fun e => e.key != entry.key) }

def applyAll (s : ServerState) : List Effect → ServerState
  | []      => s
  | e :: es => applyAll (e.apply s) es

/-! ## Branches

A second output channel, beside the effects. A `Branch` records WHICH
WAY a handler went at a decision point — not what it did to the state,
which is what an `Effect` is for.

The two are separate channels rather than one, and the separation is
the point:

  * The effect list is the CONTRACT. "Handlers touch state only through
    effects; together they are what a concrete implementation must
    realize." A branch is not something an implementation realizes, and
    putting one in that list would make the contract say it is.
  * Every claim about the effect list stays literally true. Settlement's
    write set is `{p.id}` — still, with no `filter (· != note)` threaded
    through the statement of it.
  * Inertness is STRUCTURAL. `applyAll` consumes `List Effect` and
    cannot see a branch, so no theorem is needed to say branches do not
    move the state. `run` returns exactly what it returned before.

The channel exists to be read by tooling, not by the machine: no
handler branches on a branch, and `run` discards them. What it buys is
that a coverage question — which decision did this handler make, and
did anything ever make the other one — is answered BY the machine
rather than reconstructed from its inputs and outputs by something that
can get the reconstruction wrong.

Recorded as a structure of three strings rather than an inductive per
handler: the catalogue below is then plain data, so the set of branches
that exist can be diffed against the set a corpus reached, and the
difference reported by name. An inductive would be finer and would need
a new constructor per decision point; three strings can be enumerated. -/
structure Branch where
  /-- The handler, by its catalogue number: `P-02`, `T-06`, `τ-resume`. -/
  handler : String
  /-- The decision point within it. -/
  point   : String
  /-- Which way it went. -/
  taken   : String
  deriving Repr, DecidableEq

structure Env where
  state : ServerState
  mat   : Bool

def H (α : Type) : Type := Env → α × List Effect × List Branch

instance : Monad H where
  pure a   := fun _ => (a, [], [])
  bind x f := fun e =>
    let (a, w₁, b₁) := x e
    let (b, w₂, b₂) := f a e
    (b, w₁ ++ w₂, b₁ ++ b₂)

def ask : H Env := fun e => (e, [], [])

def emit (f : Effect) : H Unit := fun _ => ((), [f], [])

/-- Record a branch. Inert: it emits no effect, so `run` is unchanged. -/
def note (handler point taken : String) : H Unit :=
  fun _ => ((), [], [{ handler, point, taken }])

def run (mat : Bool) (act : H α) (s : ServerState) : α × ServerState :=
  let (a, w, _) := act { state := s, mat := mat }
  (a, applyAll s w)

/-- `run`, keeping the branch log. The coverage tooling's entry point;
    nothing in the specification calls it. -/
def runBranches (mat : Bool) (act : H α) (s : ServerState) :
    α × ServerState × List Branch :=
  let (a, w, b) := act { state := s, mat := mat }
  (a, applyAll s w, b)

def getPromise (id : String) : H (Option PromiseObject) :=
  return (← ask).state.promises.find? (·.id == id)

def getTask (id : String) : H (Option TaskObject) :=
  return (← ask).state.tasks.find? (·.id == id)

def getSchedule (id : String) : H (Option Schedule) :=
  return (← ask).state.schedules.find? (·.id == id)

def setPromise (p : PromiseObject) : H Unit := emit (.setPromise p)
def setTask (t : TaskObject) : H Unit := emit (.setTask t)
def setSchedule (c : Schedule) : H Unit := emit (.setSchedule c)
def delSchedule (id : String) : H Unit := emit (.delSchedule id)
def setMessage (a : String) (m : Message) : H Unit := emit (.setMessage a m)

def setSettled (p : PromiseObject) : H Unit := do
  setPromise p
  if p.state != .pending then
    match ← getTask p.id with
    | some t => if t.state != .fulfilled then setTask t.fulfill
    | none => pure ()

/-- The birth shapes. All four leave through one exit in `promiseCreate`,
    so nothing downstream of the response can tell them apart; the notes
    are the only place the distinction is stated. -/
def createPromise (req : PromiseCreateReq) (now : Nat) : H PromiseObject := do
  if req.timeoutAt > now then
    let p : PromiseObject :=
      { id := req.id, state := .pending, param := req.param, tags := req.tags,
        timeoutAt := req.timeoutAt, createdAt := now }
    setPromise p
    if p.tags.has "resonate:target" then
      match p.tags.get? "resonate:delay" with
      | some d =>
          note "P-02" "birth" "born-live-targeted-delayed"
          setTask { id := p.id, state := .pending, version := 0,
                    retryAt := some (max (ServerModel.parseNat d) now) }
      | none =>
          note "P-02" "birth" "born-live-targeted"
          setTask { id := p.id, state := .pending, version := 0, retryAt := some now }
    else
      note "P-02" "birth" "born-live-untargeted"
    return p
  else
    let state :=
      if req.tags.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout
    let p : PromiseObject :=
      { id := req.id, state := state, param := req.param, tags := req.tags,
        timeoutAt := req.timeoutAt, createdAt := req.timeoutAt,
        settledAt := some req.timeoutAt }
    setPromise p
    if req.tags.isTimer then
      note "P-02" "birth" "born-dead-timer-resolved"
    else
      note "P-02" "birth" "born-dead-rejected-timedout"
    if p.tags.has "resonate:target" then
      note "P-02" "birth" "born-dead-targeted-task-fulfilled"
      setTask { id := p.id, state := .fulfilled, version := 0 }
    return p

def readPromise (id : String) (now : Nat) : H (Option PromiseObject) := do
  match ← getPromise id with
  | none => return none
  | some p =>
      let p' := p.project now
      if (← ask).mat && p'.state != p.state then
        setSettled p'
      return some p'

def createIfAbsent (req : PromiseCreateReq) (now : Nat) : H Unit := do
  match ← readPromise req.id now with
  | some _ => pure ()
  | none   => let _ ← createPromise req now

def readTask (id : String) (now : Nat) :
    H (Option (TaskObject × Option PromiseObject)) := do
  match ← getTask id with
  | none => return none
  | some t =>
  match ← readPromise t.id now with
  | none => return some (t, none)
  | some p =>
      let u := t.view p
      if (← ask).mat && u.state != t.state then
        setTask u
      return some (u, some p)

def withMat (mat : Bool) (act : H α) : H α := fun e => act { e with mat := mat }

def touchPromise (id : String) (now : Nat) : H (Option PromiseObject) :=
  withMat true (readPromise id now)

def touchTask (id : String) (now : Nat) :
    H (Option (TaskObject × Option PromiseObject)) :=
  withMat true (readTask id now)

def viewPromise (id : String) (now : Nat) : H (Option PromiseObject) :=
  withMat false (readPromise id now)


open ServerModel (PromiseState
                  PromiseGetReq PromiseGetRes
                  PromiseCreateReq PromiseCreateRes
                  PromiseSettleReq PromiseSettleRes
                  PromiseRegisterCallbackReq PromiseRegisterCallbackRes
                  PromiseRegisterListenerReq PromiseRegisterListenerRes
                  PromiseSearchReq PromiseSearchRes)

def promiseGet (req : PromiseGetReq) (now : Nat) : H PromiseGetRes := do
  match ← readPromise req.id now with
  | none =>
      note "P-01" "branch" "absent"
      return { status := 404 }
  | some p =>
      note "P-01" "branch" "found"
      return { status := 200, promise := some p.toRecord }

def promiseCreate (req : PromiseCreateReq) (now : Nat) : H PromiseCreateRes := do
  if req.tags.timerTargeted then
    note "P-02" "branch" "timer-targeted"
    return { status := 400, promise := none }
  match ← readPromise req.id now with
  | some p =>
      note "P-02" "branch" "idempotent-echo"
      return { status := 200, promise := some p.toRecord }
  | none =>
      note "P-02" "branch" "created"
      let p ← createPromise req now
      return { status := 200, promise := some p.toRecord }

def promiseSettle (req : PromiseSettleReq) (now : Nat) : H PromiseSettleRes := do
  if !req.state.settable then
    note "P-03" "branch" "unsettable"
    return { status := 400 }
  match ← readPromise req.id now with
  | none =>
      note "P-03" "branch" "absent"
      return { status := 404 }
  | some p =>
      if p.state == .pending then
        note "P-03" "branch" "settled"
        let p := { p with state := req.state, value := req.value, settledAt := some now }
        setSettled p
        return { status := 200, promise := some p.toRecord }
      else
        note "P-03" "branch" "already-settled"
        return { status := 200, promise := some p.toRecord }

def promiseRegisterCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    H PromiseRegisterCallbackRes := do
  if req.awaited == req.awaiter then
    note "P-04" "branch" "self"
    return { status := 400 }
  match ← readPromise req.awaited now with
  | none =>
      note "P-04" "branch" "awaited-absent"
      return { status := 404 }
  | some pAwaited =>
  match ← readPromise req.awaiter now with
  | none =>
      note "P-04" "branch" "awaiter-absent"
      return { status := 422 }
  | some pAwaiter =>
      if !(pAwaiter.tags.has "resonate:target") then
        note "P-04" "branch" "awaiter-untargeted"
        return { status := 422 }
      if !pAwaited.external then
        note "P-04" "branch" "awaited-internal"
        return { status := 422 }
      if pAwaited.state == .pending then
        if pAwaiter.state == .pending then
          -- One of the two doors an awaits-edge can come through. The
          -- other is `task.suspend`, and the difference survives into the
          -- drain: this one leaves the awaiter RUNNING, so the drain
          -- buffers rather than wakes. Nothing in the state at drain time
          -- records which door was used.
          note "P-04" "callback" "registered"
          setPromise (pAwaited.addCallback req.awaiter)
        else
          note "P-04" "callback" "awaiter-not-live"
        return { status := 200, promise := some pAwaited.toRecord }
      else
        note "P-04" "callback" "awaited-settled"
        return { status := 200, promise := some pAwaited.toRecord }

def promiseRegisterListener (req : PromiseRegisterListenerReq) (now : Nat) :
    H PromiseRegisterListenerRes := do
  if !ServerModel.addressValid req.address then
    note "P-05" "branch" "bad-address"
    return { status := 400 }
  match ← readPromise req.awaited now with
  | none =>
      note "P-05" "branch" "awaited-absent"
      return { status := 404 }
  | some pAwaited =>
      if !pAwaited.external then
        note "P-05" "branch" "awaited-internal"
        return { status := 422 }
      if pAwaited.state == .pending then
        note "P-05" "branch" "registered"
        setPromise (pAwaited.addListener req.address)
        return { status := 200, promise := some pAwaited.toRecord }
      else
        note "P-05" "branch" "awaited-settled"
        return { status := 200, promise := some pAwaited.toRecord }

def promiseSearch (_req : PromiseSearchReq) (_now : Nat) : H PromiseSearchRes := do
  return { status := 501 }

open ServerModel (TaskGetReq TaskGetRes
                  TaskCreateReq TaskCreateRes
                  TaskAcquireReq TaskAcquireRes
                  TaskFenceAction TaskFenceReq TaskFenceRes
                  TaskHeartbeatReq TaskHeartbeatRes
                  TaskSuspendReq TaskSuspendRes
                  TaskFulfillReq TaskFulfillRes
                  TaskReleaseReq TaskReleaseRes
                  TaskHaltReq TaskHaltRes
                  TaskContinueReq TaskContinueRes
                  TaskSearchReq TaskSearchRes)

def taskGet (req : TaskGetReq) (now : Nat) : H TaskGetRes := do
  match ← readTask req.id now with
  | none =>
      note "T-01" "branch" "task-absent"
      return { status := 404 }
  | some (_, none) =>
      note "T-01" "branch" "promise-absent"
      return { status := 404 }
  | some (t, some _) =>
      note "T-01" "branch" "found"
      return { status := 200, task := some t.toRecord }

def taskCreate (req : TaskCreateReq) (now : Nat) : H TaskCreateRes := do
  let a := req.action
  if !(a.tags.has "resonate:target") ∨ a.tags.timerTargeted then
    note "T-02" "branch" "malformed-action"
    return { status := 400 }
  match ← readPromise a.id now with
  | none =>
      if a.timeoutAt > now then
        let p : PromiseObject :=
          { id := a.id, state := .pending, param := a.param, tags := a.tags,
            timeoutAt := a.timeoutAt, createdAt := now }
        setPromise p
        let t : TaskObject :=
          { id := p.id, state := .acquired, version := 1,
            ttl := some req.ttl, pid := some req.pid,
            expiresAt := some (now + req.ttl) }
        setTask t
        note "T-02" "branch" "born-live-acquired"
        return { status := 200, task := some t.toRecord, promise := some p.toRecord }
      else
        let st := ServerModel.PromiseState.rejectedTimedout
        let p : PromiseObject :=
          { id := a.id, state := st, param := a.param, tags := a.tags,
            timeoutAt := a.timeoutAt, createdAt := a.timeoutAt,
            settledAt := some a.timeoutAt }
        setPromise p
        let t : TaskObject := { id := p.id, state := .fulfilled, version := 0 }
        setTask t
        note "T-02" "branch" "born-dead-fulfilled"
        return { status := 200, task := some t.toRecord, promise := some p.toRecord }
  | some p =>
      if !(p.tags.has "resonate:target") then
        note "T-02" "branch" "promise-untargeted"
        return { status := 422 }
      match ← readTask p.id now with
      | none | some (_, none) =>
          note "T-02" "branch" "task-absent"
          return { status := 409 }
      | some (t, some p) =>

          if t.state == .fulfilled then
            note "T-02" "branch" "already-fulfilled"
            return { status := 200, task := some t.toRecord, promise := some p.toRecord }
          else if t.state == .pending then
            let t := { t with state := .acquired, version := t.version + 1,
                              ttl := some req.ttl, pid := some req.pid,
                              expiresAt := some (now + req.ttl),
                              retryAt := none, resumes := [] }
            setTask t
            note "T-02" "branch" "reacquired"
            return { status := 200, task := some t.toRecord, promise := some p.toRecord }
          else
            note "T-02" "branch" "task-not-pending"
            return { status := 409 }

def taskAcquire (req : TaskAcquireReq) (now : Nat) : H TaskAcquireRes := do
  match ← readTask req.id now with
  | none =>
      note "T-03" "branch" "task-absent"
      return { status := 404 }
  | some (_, none) =>
      note "T-03" "branch" "promise-absent"
      return { status := 409 }
  | some (t, some p) =>
      if t.state != .pending then
        note "T-03" "branch" "task-wrong-state"
        return { status := 409 }
      if p.state != .pending then
        note "T-03" "branch" "promise-not-live"
        return { status := 409 }
      if t.version != req.version then
        note "T-03" "branch" "version-mismatch"
        return { status := 409 }
      let t := { t with state := .acquired, version := t.version + 1,
                        ttl := some req.ttl, pid := some req.pid,
                        expiresAt := some (now + req.ttl),
                        retryAt := none, resumes := [] }
      setTask t
      note "T-03" "branch" "acquired"
      return { status := 200, task := some t.toRecord, promise := some p.toRecord }

def taskFence (req : TaskFenceReq) (now : Nat) : H TaskFenceRes := do
  if req.action.targetId == req.id then
    note "T-04" "branch" "self-target"
    return { status := 400 }
  match ← readTask req.id now with
  | none =>
      note "T-04" "branch" "task-absent"
      return { status := 404 }
  | some (_, none) =>
      note "T-04" "branch" "promise-absent"
      return { status := 409 }
  | some (t, some p) =>
      if t.state != .acquired then
        note "T-04" "branch" "task-wrong-state"
        return { status := 409 }
      if p.state != .pending then
        note "T-04" "branch" "promise-not-live"
        return { status := 409 }
      if t.version != req.version then
        note "T-04" "branch" "version-mismatch"
        return { status := 409 }
      match req.action with
      | .create r =>
          note "T-04" "branch" "fenced-create"
          let res ← promiseCreate r now
          return { status := 200, action := some (.create res) }
      | .settle r =>
          note "T-04" "branch" "fenced-settle"
          let res ← promiseSettle r now
          return { status := 200, action := some (.settle res) }

def heartbeatOne (pid : String) (ref : ServerModel.TaskRef) (now : Nat) : H Unit := do
  match ← readTask ref.id now with
  | some (t, some p) =>
      if t.state == .acquired ∧ t.version == ref.version
          ∧ t.pid == some pid ∧ p.state == .pending then
        note "T-05" "branch" "lease-extended"
        setTask { t with expiresAt := some (now + t.ttl.getD 0) }
      else
        note "T-05" "branch" "refused"
  | _ =>
      note "T-05" "branch" "task-absent"


def heartbeatAll (pid : String) (now : Nat) : List ServerModel.TaskRef → H Unit
  | [] => pure ()
  | ref :: refs => do
      heartbeatOne pid ref now
      heartbeatAll pid now refs

def taskHeartbeat (req : TaskHeartbeatReq) (now : Nat) : H TaskHeartbeatRes := do
  heartbeatAll req.pid now req.tasks
  return { status := 200 }

def checkAwaited (now : Nat) : List PromiseRegisterCallbackReq → H (Option Bool)
  | [] => return some false
  | action :: rest => do
      match ← readPromise action.awaited now with
      | none => return none
      | some pa =>
          if !pa.external then
            return none
          else
            match ← checkAwaited now rest with
            | none => return none
            | some settled => return some (settled || pa.state != .pending)

def registerAwaited (awaiter : String) (now : Nat) :
    List PromiseRegisterCallbackReq → H Unit
  | [] => pure ()
  | action :: rest => do
      match ← readPromise action.awaited now with
      | some pa =>
          -- The other door. This one PARKS the task, so the drain finds
          -- it `.suspended` and wakes it.
          note "T-06" "callback" "registered"
          setPromise (pa.addCallback awaiter)
      | none => note "T-06" "callback" "awaited-absent"
      registerAwaited awaiter now rest

def taskSuspend (req : TaskSuspendReq) (now : Nat) : H TaskSuspendRes := do
  if req.actions.isEmpty then
    note "T-06" "branch" "empty-actions"
    return { status := 400 }
  if req.actions.any (·.awaited == req.id) then
    note "T-06" "branch" "self-awaited"
    return { status := 400 }
  let awaitedIds := req.actions.map (·.awaited)
  if awaitedIds.eraseDups.length != awaitedIds.length then
    note "T-06" "branch" "duplicate-awaited"
    return { status := 400 }
  match ← readTask req.id now with
  | none =>
      note "T-06" "branch" "task-absent"
      return { status := 404 }
  | some (_, none) =>
      note "T-06" "branch" "promise-absent"
      return { status := 409 }
  | some (t, some tp) =>
      if t.state != .acquired then
        note "T-06" "branch" "task-wrong-state"
        return { status := 409 }
      if tp.state != .pending then
        note "T-06" "branch" "promise-not-live"
        return { status := 409 }
      if t.version != req.version then
        note "T-06" "branch" "version-mismatch"
        return { status := 409 }
      match ← checkAwaited now req.actions with
      | none =>
          note "T-06" "branch" "awaited-unusable"
          return { status := 422 }
      | some true =>
          note "T-06" "branch" "awaited-already-settled"
          setTask { t with resumes := [] }
          return { status := 300 }
      | some false =>
          note "T-06" "branch" "suspended"

          registerAwaited req.id now req.actions
          setTask { t with state := .suspended, pid := none, ttl := none,
                           expiresAt := none, retryAt := none, resumes := [] }
          return { status := 200 }

def taskFulfill (req : TaskFulfillReq) (now : Nat) : H TaskFulfillRes := do
  if !req.action.state.settable then
    note "T-07" "branch" "unsettable"
    return { status := 400 }
  match ← readTask req.id now with
  | none =>
      note "T-07" "branch" "task-absent"
      return { status := 404 }
  | some (_, none) =>
      note "T-07" "branch" "promise-absent"
      return { status := 409 }
  | some (t, some p) =>
      if t.state != .acquired then
        note "T-07" "branch" "task-wrong-state"
        return { status := 409 }
      if p.state != .pending then
        note "T-07" "branch" "promise-not-live"
        return { status := 409 }
      if t.version != req.version then
        note "T-07" "branch" "version-mismatch"
        return { status := 409 }
      let p := { p with state := req.action.state, value := req.action.value,
                        settledAt := some now }
      setSettled p
      note "T-07" "branch" "fulfilled"
      return { status := 200, promise := some p.toRecord }

def taskRelease (req : TaskReleaseReq) (now : Nat) : H TaskReleaseRes := do
  match ← readTask req.id now with
  | none =>
      note "T-08" "branch" "task-absent"
      return { status := 404 }
  | some (_, none) =>
      note "T-08" "branch" "promise-absent"
      return { status := 409 }
  | some (t, some p) =>
      if t.state != .acquired then
        note "T-08" "branch" "task-wrong-state"
        return { status := 409 }
      if p.state != .pending then
        note "T-08" "branch" "promise-not-live"
        return { status := 409 }
      if t.version != req.version then
        note "T-08" "branch" "version-mismatch"
        return { status := 409 }
      setTask { t with state := .pending, pid := none, ttl := none,
                       expiresAt := none, retryAt := some now }
      note "T-08" "branch" "released"
      return { status := 200 }

def taskHalt (req : TaskHaltReq) (now : Nat) : H TaskHaltRes := do
  match ← readTask req.id now with
  | none =>
      note "T-09" "branch" "task-absent"
      return { status := 404 }
  | some (_, none) =>
      note "T-09" "branch" "promise-absent"
      return { status := 404 }
  | some (t, some _) =>
      if t.state == .fulfilled then
        note "T-09" "branch" "already-fulfilled"
        return { status := 409 }
      if t.state == .halted then
        note "T-09" "branch" "already-halted"
        return { status := 200 }
      setTask { t with state := .halted, pid := none, ttl := none,
                       expiresAt := none, retryAt := none }
      note "T-09" "branch" "halted"
      return { status := 200 }

def taskContinue (req : TaskContinueReq) (now : Nat) : H TaskContinueRes := do
  match ← readTask req.id now with
  | none =>
      note "T-10" "branch" "task-absent"
      return { status := 404 }
  | some (t, pOpt) =>
      if t.state != .halted then
        note "T-10" "branch" "not-halted"
        return { status := 409 }
      match pOpt with
      | none =>
          return { status := 404 }
      | some p =>
          if p.state != .pending then
            return { status := 409 }
          setTask { t with state := .pending, retryAt := some now }
          note "T-10" "branch" "continued"
      return { status := 200 }

def taskSearch (_req : TaskSearchReq) (_now : Nat) : H TaskSearchRes := do
  return { status := 501 }

open ServerModel (Schedule nextCron
                  ScheduleGetReq ScheduleGetRes
                  ScheduleCreateReq ScheduleCreateRes
                  ScheduleDeleteReq ScheduleDeleteRes
                  ScheduleSearchReq ScheduleSearchRes)

def scheduleGet (req : ScheduleGetReq) (_now : Nat) : H ScheduleGetRes := do
  match ← getSchedule req.id with
  | none =>
      return { status := 404 }
  | some s =>
      return { status := 200, schedule := some s }

def scheduleCreate (req : ScheduleCreateReq) (now : Nat) : H ScheduleCreateRes := do
  if req.promiseTags.timerTargeted then
    return { status := 400 }
  match ← getSchedule req.id with
  | some s =>
      return { status := 200, schedule := some s }
  | none =>
      let s : Schedule :=
        { id := req.id
          cron := req.cron
          promiseId := req.promiseId
          promiseTimeout := req.promiseTimeout
          promiseParam := req.promiseParam
          promiseTags := req.promiseTags
          createdAt := now
          nextRunAt := nextCron req.cron now
          lastRunAt := none }
      setSchedule s
      return { status := 200, schedule := some s }

def scheduleDelete (req : ScheduleDeleteReq) (_now : Nat) : H ScheduleDeleteRes := do
  match ← getSchedule req.id with
  | none =>
      return { status := 404 }
  | some s =>
      delSchedule s.id
      return { status := 200 }

def scheduleSearch (_req : ScheduleSearchReq) (_now : Nat) : H ScheduleSearchRes := do
  return { status := 501 }

namespace Internal

open ServerModel (nextCron occurrences expand Schedule)

/-- Each internal step notes whether it did anything. A τ fired with its
    obligation already discharged is a silent no-op, and no observational
    trace can witness the difference — the note is the only record that
    the step ran at all. -/
def processPromiseTimeout (id : String) (now : Nat) : H Unit := do
  match ← getPromise id with
  | none => note "τ-promise-timeout" "branch" "absent"
  | some p =>
      if p.state == .pending ∧ p.timeoutAt ≤ now then
        note "τ-promise-timeout" "branch" "materialized"
      else
        note "τ-promise-timeout" "branch" "not-due"

  let _ ← touchPromise id now

def processListener (id : String) (address : String) (now : Nat) : H Unit := do
  match ← touchPromise id now with
  | none => note "τ-listener" "branch" "absent"
  | some p =>
      if p.state == .pending then
        note "τ-listener" "branch" "awaited-pending"
      else if p.listeners.contains address then
        note "τ-listener" "branch" "delivered"
        setPromise { p with listeners := p.listeners.filter (· != address) }
        setMessage address (.unblock p.toRecord)
      else
        note "τ-listener" "branch" "no-such-listener"


/-- The drain's verdict, and the six outcomes `ResumeOutcome` names.

    `expired` and `fulfilled` both arrive here as a `.fulfilled` task —
    `touchTask` materializes the awaiter's own deadline first, so an
    awaiter that timed out reads exactly like one a client settled. The
    promise is in hand, so the machine can say which; anything
    reconstructing this verdict from the task alone cannot, and will
    report whichever branch it happens to test for first. -/
def resumeOne (awaited awaiter : String) (now : Nat) : H Unit := do
  match ← touchTask awaiter now with
  | none => note "τ-resume" "outcome" "absent"
  | some (_, none) => note "τ-resume" "outcome" "absent"
  | some (t, some p) =>
      match t.state with
      | .suspended =>
          note "τ-resume" "outcome" "resumed"
          setTask { t with state := .pending, resumes := [awaited],
                           retryAt := some now }
      | .pending | .acquired | .halted =>
          if !(t.resumes.contains awaited) then
            note "τ-resume" "outcome" "buffered"
            setTask { t with resumes := t.resumes ++ [awaited] }
          else
            note "τ-resume" "outcome" "duplicate"
      | .fulfilled =>
          -- TIMEOUT ALWAYS WINS orders these: past its own deadline is
          -- `expired`, and only a settlement that beat the deadline is
          -- `fulfilled`.
          if p.timeoutAt ≤ now then
            note "τ-resume" "outcome" "expired"
          else
            note "τ-resume" "outcome" "fulfilled"

def processCallback (id : String) (awaiter : String) (now : Nat) : H Unit := do
  match ← touchPromise id now with
  | none => pure ()
  | some p =>
      if p.state == .pending then
        pure ()
      else if p.callbacks.contains awaiter then
        setPromise { p with callbacks := p.callbacks.filter (· != awaiter) }
        resumeOne p.id awaiter now

def processLeaseTimeout (id : String) (now : Nat) : H Unit := do
  match ← getTask id with
  | none => note "τ-lease" "branch" "task-absent"
  | some t =>
      match t.expiresAt with
      | none => note "τ-lease" "branch" "unarmed"
      | some deadline =>
          if t.state == .acquired ∧ deadline ≤ now then
            match ← viewPromise t.id now with
            | none => note "τ-lease" "branch" "promise-absent"
            | some p =>
                if p.state == .pending then
                  note "τ-lease" "branch" "expired"
                  setTask { t with state := .pending, pid := none, ttl := none,
                                   expiresAt := none, retryAt := some now }
                else
                  note "τ-lease" "branch" "promise-not-live"
          else
            note "τ-lease" "branch" "not-due"


def processRetryTimeout (id : String) (next : Nat) (now : Nat) : H Unit := do
  match ← getTask id with
  | none => note "τ-retry" "branch" "task-absent"
  | some t =>
      match t.retryAt with
      | none => note "τ-retry" "branch" "unarmed"
      | some due =>
          if t.state == .pending ∧ due ≤ now then
            match ← viewPromise t.id now with
            | none => note "τ-retry" "branch" "promise-absent"
            | some p =>
                if p.state == .pending then
                  note "τ-retry" "branch" "dispatched"
                  setTask { t with retryAt := some next }
                  setMessage ((p.tags.get? "resonate:target").getD "")
                    (.execute t.id t.version)
                else
                  note "τ-retry" "branch" "promise-not-live"
          else
            note "τ-retry" "branch" "not-due"


def fireOccurrence (s : Schedule) (t : Nat) : H Unit :=
  createIfAbsent
    { id := expand s.promiseId s.id t, timeoutAt := t + s.promiseTimeout,
      param := s.promiseParam, tags := s.promiseTags } t

def fireAll (s : Schedule) : List Nat → H Unit
  | [] => pure ()
  | t :: ts => do
      fireOccurrence s t
      fireAll s ts

def processSchedule (id : String) (now : Nat) : H Unit := do
  match ← getSchedule id with
  | none => pure ()
  | some s =>
      let ts := (occurrences s.cron s.nextRunAt now).filter (· ≤ now)
      fireAll s ts
      match ts.getLast? with
      | some last =>
          setSchedule { s with lastRunAt := some last,
                               nextRunAt := nextCron s.cron last }
      | none => pure ()

end Internal


/-! ## The catalogue

Every branch the machine can note, as DATA. The point of writing it out
rather than deriving it from a run: a search reports what it reached,
and a behaviour it never reached is indistinguishable from one that does
not exist. Diffing a corpus against this list is what turns "here is
what we covered" into "here is what we did not".

Kept beside the handlers deliberately. A branch added to a handler
without an entry here is invisible to the coverage report, which is the
one failure mode this file exists to prevent -- so the pair is a single
edit, and `branches_catalogued` below fails when it is not. -/
def branchCatalogue : List Branch :=
  [ { handler := "P-01", point := "branch", taken := "absent" },
    { handler := "P-01", point := "branch", taken := "found" },
    { handler := "P-02", point := "birth", taken := "born-dead-rejected-timedout" },
    { handler := "P-02", point := "birth", taken := "born-dead-targeted-task-fulfilled" },
    { handler := "P-02", point := "birth", taken := "born-dead-timer-resolved" },
    { handler := "P-02", point := "birth", taken := "born-live-targeted" },
    { handler := "P-02", point := "birth", taken := "born-live-targeted-delayed" },
    { handler := "P-02", point := "birth", taken := "born-live-untargeted" },
    { handler := "P-02", point := "branch", taken := "created" },
    { handler := "P-02", point := "branch", taken := "idempotent-echo" },
    { handler := "P-02", point := "branch", taken := "timer-targeted" },
    { handler := "P-03", point := "branch", taken := "absent" },
    { handler := "P-03", point := "branch", taken := "already-settled" },
    { handler := "P-03", point := "branch", taken := "settled" },
    { handler := "P-03", point := "branch", taken := "unsettable" },
    { handler := "P-04", point := "branch", taken := "awaited-absent" },
    { handler := "P-04", point := "branch", taken := "awaited-internal" },
    { handler := "P-04", point := "branch", taken := "awaiter-absent" },
    { handler := "P-04", point := "branch", taken := "awaiter-untargeted" },
    { handler := "P-04", point := "branch", taken := "self" },
    { handler := "P-04", point := "callback", taken := "awaited-settled" },
    { handler := "P-04", point := "callback", taken := "awaiter-not-live" },
    { handler := "P-04", point := "callback", taken := "registered" },
    { handler := "P-05", point := "branch", taken := "awaited-absent" },
    { handler := "P-05", point := "branch", taken := "awaited-internal" },
    { handler := "P-05", point := "branch", taken := "awaited-settled" },
    { handler := "P-05", point := "branch", taken := "bad-address" },
    { handler := "P-05", point := "branch", taken := "registered" },
    { handler := "T-01", point := "branch", taken := "found" },
    { handler := "T-01", point := "branch", taken := "promise-absent" },
    { handler := "T-01", point := "branch", taken := "task-absent" },
    { handler := "T-02", point := "branch", taken := "already-fulfilled" },
    { handler := "T-02", point := "branch", taken := "born-dead-fulfilled" },
    { handler := "T-02", point := "branch", taken := "born-live-acquired" },
    { handler := "T-02", point := "branch", taken := "malformed-action" },
    { handler := "T-02", point := "branch", taken := "promise-untargeted" },
    { handler := "T-02", point := "branch", taken := "reacquired" },
    { handler := "T-02", point := "branch", taken := "task-absent" },
    { handler := "T-02", point := "branch", taken := "task-not-pending" },
    { handler := "T-03", point := "branch", taken := "acquired" },
    { handler := "T-03", point := "branch", taken := "promise-absent" },
    { handler := "T-03", point := "branch", taken := "promise-not-live" },
    { handler := "T-03", point := "branch", taken := "task-absent" },
    { handler := "T-03", point := "branch", taken := "task-wrong-state" },
    { handler := "T-03", point := "branch", taken := "version-mismatch" },
    { handler := "T-04", point := "branch", taken := "fenced-create" },
    { handler := "T-04", point := "branch", taken := "fenced-settle" },
    { handler := "T-04", point := "branch", taken := "promise-absent" },
    { handler := "T-04", point := "branch", taken := "promise-not-live" },
    { handler := "T-04", point := "branch", taken := "self-target" },
    { handler := "T-04", point := "branch", taken := "task-absent" },
    { handler := "T-04", point := "branch", taken := "task-wrong-state" },
    { handler := "T-04", point := "branch", taken := "version-mismatch" },
    { handler := "T-05", point := "branch", taken := "lease-extended" },
    { handler := "T-05", point := "branch", taken := "refused" },
    { handler := "T-05", point := "branch", taken := "task-absent" },
    { handler := "T-06", point := "branch", taken := "awaited-already-settled" },
    { handler := "T-06", point := "branch", taken := "awaited-unusable" },
    { handler := "T-06", point := "branch", taken := "duplicate-awaited" },
    { handler := "T-06", point := "branch", taken := "empty-actions" },
    { handler := "T-06", point := "branch", taken := "promise-absent" },
    { handler := "T-06", point := "branch", taken := "promise-not-live" },
    { handler := "T-06", point := "branch", taken := "self-awaited" },
    { handler := "T-06", point := "branch", taken := "suspended" },
    { handler := "T-06", point := "branch", taken := "task-absent" },
    { handler := "T-06", point := "branch", taken := "task-wrong-state" },
    { handler := "T-06", point := "branch", taken := "version-mismatch" },
    { handler := "T-06", point := "callback", taken := "awaited-absent" },
    { handler := "T-06", point := "callback", taken := "registered" },
    { handler := "T-07", point := "branch", taken := "fulfilled" },
    { handler := "T-07", point := "branch", taken := "promise-absent" },
    { handler := "T-07", point := "branch", taken := "promise-not-live" },
    { handler := "T-07", point := "branch", taken := "task-absent" },
    { handler := "T-07", point := "branch", taken := "task-wrong-state" },
    { handler := "T-07", point := "branch", taken := "unsettable" },
    { handler := "T-07", point := "branch", taken := "version-mismatch" },
    { handler := "T-08", point := "branch", taken := "promise-absent" },
    { handler := "T-08", point := "branch", taken := "promise-not-live" },
    { handler := "T-08", point := "branch", taken := "released" },
    { handler := "T-08", point := "branch", taken := "task-absent" },
    { handler := "T-08", point := "branch", taken := "task-wrong-state" },
    { handler := "T-08", point := "branch", taken := "version-mismatch" },
    { handler := "T-09", point := "branch", taken := "already-fulfilled" },
    { handler := "T-09", point := "branch", taken := "already-halted" },
    { handler := "T-09", point := "branch", taken := "halted" },
    { handler := "T-09", point := "branch", taken := "promise-absent" },
    { handler := "T-09", point := "branch", taken := "task-absent" },
    { handler := "T-10", point := "branch", taken := "continued" },
    { handler := "T-10", point := "branch", taken := "not-halted" },
    { handler := "T-10", point := "branch", taken := "promise-not-live" },
    { handler := "T-10", point := "branch", taken := "task-absent" },
    { handler := "τ-lease", point := "branch", taken := "expired" },
    { handler := "τ-lease", point := "branch", taken := "not-due" },
    { handler := "τ-lease", point := "branch", taken := "promise-absent" },
    { handler := "τ-lease", point := "branch", taken := "promise-not-live" },
    { handler := "τ-lease", point := "branch", taken := "task-absent" },
    { handler := "τ-lease", point := "branch", taken := "unarmed" },
    { handler := "τ-listener", point := "branch", taken := "absent" },
    { handler := "τ-listener", point := "branch", taken := "awaited-pending" },
    { handler := "τ-listener", point := "branch", taken := "delivered" },
    { handler := "τ-listener", point := "branch", taken := "no-such-listener" },
    { handler := "τ-promise-timeout", point := "branch", taken := "absent" },
    { handler := "τ-promise-timeout", point := "branch", taken := "materialized" },
    { handler := "τ-promise-timeout", point := "branch", taken := "not-due" },
    { handler := "τ-resume", point := "outcome", taken := "absent" },
    { handler := "τ-resume", point := "outcome", taken := "buffered" },
    { handler := "τ-resume", point := "outcome", taken := "duplicate" },
    { handler := "τ-resume", point := "outcome", taken := "expired" },
    { handler := "τ-resume", point := "outcome", taken := "fulfilled" },
    { handler := "τ-resume", point := "outcome", taken := "resumed" },
    { handler := "τ-retry", point := "branch", taken := "dispatched" },
    { handler := "τ-retry", point := "branch", taken := "not-due" },
    { handler := "τ-retry", point := "branch", taken := "promise-absent" },
    { handler := "τ-retry", point := "branch", taken := "promise-not-live" },
    { handler := "τ-retry", point := "branch", taken := "task-absent" },
    { handler := "τ-retry", point := "branch", taken := "unarmed" } ]

/-- Branches a run reached that the catalogue does not list. -/
def uncatalogued (bs : List Branch) : List Branch :=
  bs.filter (fun b => !branchCatalogue.contains b) |>.eraseDups

/-- Catalogued branches a run did not reach -- the residue, by name. -/
def unreached (bs : List Branch) : List Branch :=
  branchCatalogue.filter (fun b => !bs.contains b)

end E
end AbstractModel
