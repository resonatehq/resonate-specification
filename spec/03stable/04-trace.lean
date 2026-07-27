import «02-actions».«02-timeouts»
import «02-actions».«03-resume»
import «02-actions».«P-01-promise.get»
import «02-actions».«P-02-promise.create»
import «02-actions».«P-03-promise.settle»
import «02-actions».«P-04-promise.register_callback»
import «02-actions».«P-05-promise.register_listener»
import «02-actions».«P-06-promise.search»
import «02-actions».«S-01-schedule.get»
import «02-actions».«S-02-schedule.create»
import «02-actions».«S-03-schedule.delete»
import «02-actions».«S-04-schedule.search»
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
import «02-actions».«T-11-task.search»
import «02-actions».«T-05-task.heartbeat»

open ServerModel

/-! ## The system as a trace

A trace is an infinite sequence of state-action pairs: the state the
machine is in and the request that hits it there, at some instant. A
trace is VALID iff every two subsequent pairs are connected by a step
— the successor's state is exactly what the protocol handler computes
from the predecessor's state, request, and clock — and the clock is
monotone: instants never run backwards.

The request alphabet is the full protocol alphabet:

  * the API requests (`promise.*`, `schedule.*`, `task.*`) — visible
    transitions, each dispatched to its handler;
  * the internal (τ) transitions — the timeout firings and the
    deferred-resume drain — modeled as requests the server issues to
    itself; their responses are never externalized to a client;
  * `idle` — the stutter step. A finite behavior becomes an infinite
    trace by idling forever.

The response is part of the pair: `(tr t).res` is what the system
externalizes at instant `t`. Validity pins it to the handler's output,
so on a valid trace it is redundant with (state, request, instant) —
recording it makes the observable behavior directly addressable.

τ-enabledness is folded into the step function rather than into
validity: a timeout may fire only if a DUE timeout record exists
(dispatching `onPromiseTimeout` ahead of the recorded deadline would
forge a timeout — the handler stamps AT THE DEADLINE), and a resume τ
fires only for a pair in the deferred set, mirroring `drain`'s
undefer-then-resume. A disabled τ is a no-op. Validity is therefore
connectivity plus the monotone clock, and because every handler is
total, every infinite request sequence with a monotone clock induces
exactly one valid trace from a given start state: the alphabet carries
no proof obligations — the handlers carry all the semantics.
-/

/-- The protocol alphabet: every transition the machine can take. -/
inductive Request
  | promiseGet              (req : PromiseGetReq)
  | promiseCreate           (req : PromiseCreateReq)
  | promiseSettle           (req : PromiseSettleReq)
  | promiseRegisterCallback (req : PromiseRegisterCallbackReq)
  | promiseRegisterListener (req : PromiseRegisterListenerReq)
  | promiseSearch           (req : PromiseSearchReq)
  | scheduleGet             (req : ScheduleGetReq)
  | scheduleCreate          (req : ScheduleCreateReq)
  | scheduleDelete          (req : ScheduleDeleteReq)
  | scheduleSearch          (req : ScheduleSearchReq)
  | taskGet                 (req : TaskGetReq)
  | taskCreate              (req : TaskCreateReq)
  | taskAcquire             (req : TaskAcquireReq)
  | taskFence               (req : TaskFenceReq)
  | taskHeartbeat           (req : TaskHeartbeatReq)
  | taskSuspend             (req : TaskSuspendReq)
  | taskFulfill             (req : TaskFulfillReq)
  | taskRelease             (req : TaskReleaseReq)
  | taskHalt                (req : TaskHaltReq)
  | taskContinue            (req : TaskContinueReq)
  | taskSearch              (req : TaskSearchReq)
  -- internal (τ): requests the server issues to itself
  | τPromiseTimeout         (id : String)
  | τTaskRetryTimeout       (id : String)
  | τTaskLeaseTimeout       (id : String)
  | τScheduleTimeout        (id : String)
  | τResume                 (req : ResumeReq)
  -- stutter
  | idle
  deriving Repr

/-- What a step externalizes. τ-steps and `idle` answer `.τ`: nobody is
    listening. `.resume` carries the drain's oracle-facing outcome (see
    `ResumeOutcome`); it is internal all the same. -/
inductive Response
  | promiseGet              (res : PromiseGetRes)
  | promiseCreate           (res : PromiseCreateRes)
  | promiseSettle           (res : PromiseSettleRes)
  | promiseRegisterCallback (res : PromiseRegisterCallbackRes)
  | promiseRegisterListener (res : PromiseRegisterListenerRes)
  | promiseSearch           (res : PromiseSearchRes)
  | scheduleGet             (res : ScheduleGetRes)
  | scheduleCreate          (res : ScheduleCreateRes)
  | scheduleDelete          (res : ScheduleDeleteRes)
  | scheduleSearch          (res : ScheduleSearchRes)
  | taskGet                 (res : TaskGetRes)
  | taskCreate              (res : TaskCreateRes)
  | taskAcquire             (res : TaskAcquireRes)
  | taskFence               (res : TaskFenceRes)
  | taskHeartbeat           (res : TaskHeartbeatRes)
  | taskSuspend             (res : TaskSuspendRes)
  | taskFulfill             (res : TaskFulfillRes)
  | taskRelease             (res : TaskReleaseRes)
  | taskHalt                (res : TaskHaltRes)
  | taskContinue            (res : TaskContinueRes)
  | taskSearch              (res : TaskSearchRes)
  | resume                  (res : ResumeRes)
  | τ
  deriving Repr

/-- THE step function: dispatch a request to its protocol handler.
    Total — an API handler answers every request in every state, and a
    τ whose obligation is not on the books is a no-op. -/
def handle (rq : Request) (now : Nat) : M Response :=
  match rq with
  | .promiseGet req              => Response.promiseGet <$> promiseGet req now
  | .promiseCreate req           => Response.promiseCreate <$> promiseCreate req now
  | .promiseSettle req           => Response.promiseSettle <$> promiseSettle req now
  | .promiseRegisterCallback req => Response.promiseRegisterCallback <$> promiseRegisterCallback req now
  | .promiseRegisterListener req => Response.promiseRegisterListener <$> promiseRegisterListener req now
  | .promiseSearch req           => Response.promiseSearch <$> promiseSearch req now
  | .scheduleGet req             => Response.scheduleGet <$> scheduleGet req now
  | .scheduleCreate req          => Response.scheduleCreate <$> scheduleCreate req now
  | .scheduleDelete req          => Response.scheduleDelete <$> scheduleDelete req now
  | .scheduleSearch req          => Response.scheduleSearch <$> scheduleSearch req now
  | .taskGet req                 => Response.taskGet <$> taskGet req now
  | .taskCreate req              => Response.taskCreate <$> taskCreate req now
  | .taskAcquire req             => Response.taskAcquire <$> taskAcquire req now
  | .taskFence req               => Response.taskFence <$> taskFence req now
  | .taskHeartbeat req           => Response.taskHeartbeat <$> taskHeartbeat req now
  | .taskSuspend req             => Response.taskSuspend <$> taskSuspend req now
  | .taskFulfill req             => Response.taskFulfill <$> taskFulfill req now
  | .taskRelease req             => Response.taskRelease <$> taskRelease req now
  | .taskHalt req                => Response.taskHalt <$> taskHalt req now
  | .taskContinue req            => Response.taskContinue <$> taskContinue req now
  | .taskSearch req              => Response.taskSearch <$> taskSearch req now
  | .τPromiseTimeout id => do
      if (← get).promiseTimeouts.any (fun e => e.id == id && decide (e.timeout ≤ now)) then
        Timeouts.onPromiseTimeout id now
      return .τ
  | .τTaskRetryTimeout id => do
      if (← get).taskTimeouts.any (fun e => e.id == id && e.kind == 0 && decide (e.timeout ≤ now)) then
        Timeouts.onTaskRetryTimeout id now
      return .τ
  | .τTaskLeaseTimeout id => do
      if (← get).taskTimeouts.any (fun e => e.id == id && e.kind == 1 && decide (e.timeout ≤ now)) then
        Timeouts.onTaskLeaseTimeout id now
      return .τ
  | .τScheduleTimeout id => do
      if (← get).scheduleTimeouts.any (fun e => e.id == id && decide (e.timeout ≤ now)) then
        Timeouts.onScheduleTimeout 1000000 id now
      return .τ
  | .τResume req => do
      if (← get).deferred.any (fun d => d.awaited == req.awaited && d.awaiter == req.awaiter) then
        undefer req
        Response.resume <$> onResume req now
      else
        return .τ
  | .idle => return .τ

/-- A state, the request that hits it there, the response the machine
    externalizes for it, and the instant on the wall clock. -/
structure StateAction where
  state : ServerState
  req   : Request
  res   : Response
  now   : Nat

/-- A trace is an infinite sequence of state-action pairs. -/
abbrev Trace := Nat → StateAction

/-- One protocol step as a total function: (request, instant, state) to
    (response, successor state). NOTE: `Id.run ∘ .run` is definitionally
    the identity -- `M Response` IS `ServerState → Response × ServerState`
    -- and is kept only because the in-flight obligation proofs in
    `06-stable-proof` were authored against this form. -/
def stepOf (rq : Request) (now : Nat) (s : ServerState) : Response × ServerState :=
  Id.run ((handle rq now).run s)

/-- **Validity**: two subsequent state-action pairs are connected by a
    step — the recorded response and the successor's state are exactly
    the handler's output — and the clock never runs backwards. The
    handlers take `now` as a free input, but a behavior of the system
    has one clock, and it flows forward. -/
def Valid (tr : Trace) : Prop :=
  ∀ t : Nat,
    (tr t).res = (stepOf (tr t).req (tr t).now (tr t).state).1 ∧
    (tr (t + 1)).state = (stepOf (tr t).req (tr t).now (tr t).state).2 ∧
    (tr t).now ≤ (tr (t + 1)).now

/-! ### Executable verification

A concrete valid trace, end to end: create an external promise at
instant 0, settle it at 500, idle forever after. Validity holds by
`rfl` — each recorded response and successor state is literally the
handler's output. -/

private def rq₀ : Request := .promiseCreate
  { id := "p", timeoutAt := 1000, param := {}, tags := [("resonate:external", "true")] }

private def rq₁ : Request := .promiseSettle
  { id := "p", state := .resolved, value := {} }

private def s₀ : ServerState := ServerState.init
private def s₁ : ServerState := (stepOf rq₀ 0 s₀).2
private def s₂ : ServerState := (stepOf rq₁ 500 s₁).2

private def trExample : Trace
  | 0     => { state := s₀, req := rq₀,   now := 0,   res := (stepOf rq₀ 0 s₀).1 }
  | 1     => { state := s₁, req := rq₁,   now := 500, res := (stepOf rq₁ 500 s₁).1 }
  | _ + 2 => { state := s₂, req := .idle, now := 500, res := .τ }

private theorem trExample_valid : Valid trExample := fun t =>
  match t with
  | 0     => ⟨rfl, rfl, Nat.zero_le _⟩
  | 1     => ⟨rfl, rfl, Nat.le_refl _⟩
  | _ + 2 => ⟨rfl, rfl, Nat.le_refl _⟩

-- The externalized response at instant 1: the settle answered 200 and
-- the promise settled on the wire.
example :
    (match (trExample 1).res with
     | .promiseSettle r => r.status == 200
        && (r.promise.map (·.state == .resolved)).getD false
     | _ => false) = true := by native_decide

-- A τ with no obligation on the books is a no-op: the trace may
-- stutter τ-requests without touching the state.
example : (stepOf (.τPromiseTimeout "p") 2000 s₂).2.promises.length
            = s₂.promises.length := by native_decide
