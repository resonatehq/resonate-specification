import «04-theorems».«trace»

/-!  # A test framework, and what it is for

The specification says what the protocol is. An implementer needs
something else: a list of concrete things to do and concrete things
that must then be true, short enough to read and mechanical enough to
transliterate into whatever language the implementation is in.

That is what this is. A test case here is a `do` block — a clock, a
sequence of external requests and internal steps, and assertions
between them — and it reads as pseudocode on purpose. Porting one is
transliteration, not interpretation.

What makes it more than pseudocode: every case RUNS, against the
specification itself, and `cases_all_pass` at the bottom of
`cases.lean` is checked by `decide`. So the claim handed over is not
"these tests are believed correct" but "the kernel agrees the
specification satisfies them".

## The monad

`StateT Ctx (Except Failure)`: state threads the machine and the clock,
`Except` short-circuits at the first failed assertion. The step index
rides along so a failure says WHERE — `step 4: expected 409, got 200` —
which is the difference between a test you can act on and one you have
to bisect.

Assertions read the state directly rather than digging through a
response, because that is what an implementer checks too: not "what did
the call return" alone, but "what is true of the server now".

## The two tiers, and why the framework cares

A case that drives internal steps may assert task-facing state
anywhere, because it fixes the schedule. A case that does not must
assert task state only at quiescence: the stage of the wake pipeline is
visible at the task interface BY DESIGN, so a conforming implementation
running its own internal loop can legitimately answer differently
mid-pipeline. `τ`-driving cases and observational ones are therefore
not interchangeable, and mixing them is the one way to write a test
here that a correct implementation fails. -/

namespace Tests

open ServerModel
open ConcreteModel
open Equivalence

/-- Where a case failed, and what it expected. -/
structure Failure where
  step : Nat
  what : String
  deriving Repr

/-- The machine, the clock, how many steps have run, and the messages
    the LAST step sent — `StateAction.msg`, per step rather than
    accumulated, so a case can assert that a step dispatched something
    at the moment it did. -/
structure Ctx where
  state : ConcreteModel.ServerState
  now   : Nat
  idx   : Nat
  msg   : List OutboxEntry

abbrev T := StateT Ctx (Except Failure)

def init : Ctx :=
  { state := ConcreteModel.ServerState.init, now := 0, idx := 0, msg := [] }

def fail (what : String) : T Unit := do
  let c ← get
  throw { step := c.idx, what := what }

/-- Set the clock. Time only moves where a case says it does; there is
    no hidden clock in the machine either (`now` is a handler argument),
    so a case controls it completely. -/
def clock (n : Nat) : T Unit :=
  modify fun c => { c with now := n }

/-- Advance the clock by `d`. -/
def wait (d : Nat) : T Unit :=
  modify fun c => { c with now := c.now + d }

/-- Run one step of the machine — external request or internal step,
    the alphabet does not distinguish them — and record what it sent. -/
def act (rq : Request) : T Response := do
  let c ← get
  let (res, s') := stepOf handleP rq c.now c.state
  let sent := s'.outbox.filter (fun e => !c.state.outbox.contains e)
  set { state := s', now := c.now, idx := c.idx + 1, msg := sent }
  return res

/-! ### The status of a response

One line per alphabet symbol. `resume` and `τ` carry no status: the
drain answers an outcome and an internal step answers nobody. -/
def status : Response → Nat
  | .promiseGet r              => r.status
  | .promiseCreate r           => r.status
  | .promiseSettle r           => r.status
  | .promiseRegisterCallback r => r.status
  | .promiseRegisterListener r => r.status
  | .promiseSearch r           => r.status
  | .scheduleGet r             => r.status
  | .scheduleCreate r          => r.status
  | .scheduleDelete r          => r.status
  | .scheduleSearch r          => r.status
  | .taskGet r                 => r.status
  | .taskCreate r              => r.status
  | .taskAcquire r             => r.status
  | .taskFence r               => r.status
  | .taskHeartbeat r           => r.status
  | .taskSuspend r             => r.status
  | .taskFulfill r             => r.status
  | .taskRelease r             => r.status
  | .taskHalt r                => r.status
  | .taskContinue r            => r.status
  | .taskSearch r              => r.status
  | .resume _                  => 0
  | .τ                         => 0

/-! ### Requests, named for the wire

Thin constructors so a case reads as the call an implementer would
make, not as an inductive.  -/

def create (id : String) (timeoutAt : Nat) (tags : Tags) : T Response :=
  act (.promiseCreate { id := id, timeoutAt := timeoutAt, param := {}, tags := tags })

def get (id : String) : T Response :=
  act (.promiseGet { id := id })

def settle (id : String) (st : PromiseState) : T Response :=
  act (.promiseSettle { id := id, state := st, value := {} })

def callback (awaited awaiter : String) : T Response :=
  act (.promiseRegisterCallback { awaited := awaited, awaiter := awaiter })

def listen (awaited address : String) : T Response :=
  act (.promiseRegisterListener { awaited := awaited, address := address })

def taskCreate (id pid : String) (ttl timeoutAt : Nat) (tags : Tags) : T Response :=
  act (.taskCreate { pid := pid, ttl := ttl,
                     action := { id := id, timeoutAt := timeoutAt, param := {}, tags := tags } })

def taskGet (id : String) : T Response :=
  act (.taskGet { id := id })

def acquire (id : String) (version : Nat) (pid : String) (ttl : Nat) : T Response :=
  act (.taskAcquire { id := id, version := version, pid := pid, ttl := ttl })

def suspend (id : String) (version : Nat) (awaited : List String) : T Response :=
  act (.taskSuspend { id := id, version := version,
                      actions := awaited.map (fun a => { awaited := a, awaiter := id }) })

def fulfill (id : String) (version : Nat) (st : PromiseState) : T Response :=
  act (.taskFulfill { id := id, version := version,
                      action := { id := id, state := st, value := {} } })

def release (id : String) (version : Nat) : T Response :=
  act (.taskRelease { id := id, version := version })

def halt (id : String) : T Response := act (.taskHalt { id := id })

def «continue» (id : String) : T Response := act (.taskContinue { id := id })

def heartbeat (pid : String) (refs : List (String × Nat)) : T Response :=
  act (.taskHeartbeat { pid := pid,
                        tasks := refs.map (fun r => { id := r.1, version := r.2 }) })

/-! ### Internal steps

Named `τ`, because that is what they are: the machine's own business,
fired by the environment at a moment the case chooses. Choosing the
moment is the point — an implementation that fires its timeouts a
little late is not the same machine, and only a case that drives them
can say so. -/

def τpromiseTimeout (id : String) : T Response := act (.τPromiseTimeout id)
def τtaskRetry     (id : String) : T Response := act (.τTaskRetryTimeout id)
def τtaskLease     (id : String) : T Response := act (.τTaskLeaseTimeout id)
def τresume (awaited awaiter : String) : T Response :=
  act (.τResume { awaited := awaited, awaiter := awaiter })

/-! ### Assertions -/

def expect (want : Nat) (res : Response) : T Unit :=
  if status res == want then pure () else
    fail s!"expected status {want}, got {status res}"

/-- The promise as an observer sees it: PROJECTED, so a promise past its
    deadline reads settled whether or not its timeout has fired. Every
    promise-facing response in the machine projects; a case asserting on
    the stored state instead would be asserting something no client can
    see. -/
def promiseIs (id : String) (st : PromiseState) : T Unit := do
  let c ← get
  match c.state.promises.find? (·.id == id) with
  | none => fail s!"no promise {id}"
  | some p =>
      if (p.project c.now).state == st then pure () else
        fail s!"promise {id}: expected {repr st}, got {repr (p.project c.now).state}"

/-- The task as STORED. Task state is material — claims, leases, fencing
    — and is deliberately not projected, so this reads the machine
    rather than a forecast. Assert it mid-pipeline only in a case that
    drives the internal steps. -/
def taskIs (id : String) (st : TaskState) : T Unit := do
  let c ← get
  match c.state.tasks.find? (·.id == id) with
  | none => fail s!"no task {id}"
  | some t =>
      if t.state == st then pure () else
        fail s!"task {id}: expected {repr st}, got {repr t.state}"

def absent (id : String) : T Unit := do
  let c ← get
  if (c.state.promises.find? (·.id == id)).isNone then pure () else
    fail s!"expected no promise {id}"

/-- The step just run sent exactly these messages. `[]` asserts silence,
    which is an assertion worth making: most steps send nothing, and a
    machine that dispatches where the specification does not is wrong in
    a way no response reveals. -/
def sent (ms : List OutboxEntry) : T Unit := do
  let c ← get
  let same := ms.all c.msg.contains && c.msg.all ms.contains
  if same then pure () else
    fail s!"messages: expected {repr ms}, got {repr c.msg}"

def sentNothing : T Unit := sent []

/-! ### Running -/

def run (t : T Unit) : Except Failure Unit :=
  match t.run init with
  | .ok _    => .ok ()
  | .error e => .error e

def passes (t : T Unit) : Bool :=
  match run t with
  | .ok _    => true
  | .error _ => false

/-- A case, named. The name is what a failure report prints and what an
    implementer ports as the test's own name. -/
structure Case where
  name : String
  body : T Unit

def failures (cs : List Case) : List String :=
  cs.filterMap fun c =>
    match run c.body with
    | .ok _    => none
    | .error e => some s!"{c.name}: step {e.step}: {e.what}"

end Tests
