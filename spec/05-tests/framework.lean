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

Every assertion is on what a request ANSWERED. Nothing reads the
server's state. An implementer porting these has a client and a server
and nothing else — a test that needs a handle on the promise table is a
test they cannot run — and it is the discipline the specification keeps
anyway: the projection exists so that what a client sees is well defined
independently of what is stored.

## The two tiers, and why the framework cares

A case that drives internal steps may assert what `task.get` answers
anywhere, because it fixes the schedule. A case that does not must ask
only at quiescence: the stage of the wake pipeline is
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

/-! ### Assertions

Everything a case asserts is something a CLIENT can see: the status a
request answered with, and the record it carried back. Nothing here
reads the server's state.

That is not fastidiousness, it is the whole point of the artifact. An
implementer porting these has a running server and a client; they do not
have a handle on its promise table, and a test that needs one is a test
they cannot run. It is also the discipline the specification itself
keeps — the projection exists precisely so that what a client sees is
well defined independently of what is stored — so an assertion on
stored state can pass against a machine that is observably wrong, and
fail against one that is observably right. -/

/-- The promise record a response carried back, if it carried one. -/
def promiseOf : Response → Option PromiseRecord
  | .promiseGet r              => r.promise
  | .promiseCreate r           => r.promise
  | .promiseSettle r           => r.promise
  | .promiseRegisterCallback r => r.promise
  | .promiseRegisterListener r => r.promise
  | .taskCreate r              => r.promise
  | .taskAcquire r             => r.promise
  | .taskFulfill r             => r.promise
  | _                          => none

/-- The task record a response carried back, if it carried one. -/
def taskOf : Response → Option TaskRecord
  | .taskGet r    => r.task
  | .taskCreate r => r.task
  | .taskAcquire r => r.task
  | _             => none

def expect (want : Nat) (res : Response) : T Unit :=
  if status res == want then pure () else
    fail s!"expected status {want}, got {status res}"

def expectPromise (st : PromiseState) (res : Response) : T Unit :=
  match promiseOf res with
  | none   => fail s!"expected a promise in the response, got none"
  | some p =>
      if p.state == st then pure () else
        fail s!"expected promise {repr st}, got {repr p.state}"

def expectTask (st : TaskState) (res : Response) : T Unit :=
  match taskOf res with
  | none   => fail s!"expected a task in the response, got none"
  | some t =>
      if t.state == st then pure () else
        fail s!"expected task {repr st}, got {repr t.state}"

def expectVersion (v : Nat) (res : Response) : T Unit :=
  match taskOf res with
  | none   => fail s!"expected a task in the response, got none"
  | some t =>
      if t.version == v then pure () else
        fail s!"expected task version {v}, got {t.version}"

/-- The messages the step just run sent. The second observable channel:
    not a response to the caller, but a delivery to a worker or a
    listener, which an implementer observes with a fake endpoint rather
    than by reading state. `[]` asserts silence, and silence is worth
    asserting — a machine that dispatches where the specification does
    not is wrong in a way no response reveals. -/
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
