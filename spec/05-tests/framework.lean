import «03-concrete».«external-steps-p»
import «03-concrete».«internal-steps-p»

/-!  # A test framework, and what it is for

The specification says what the protocol is. An implementer needs
something else: a list of concrete requests to send and concrete things
that must be true of the responses, short enough to read and mechanical
enough to transliterate.

That is all this is. There is no invented API here — a case builds a
real `PromiseCreateReq`, calls the real `promiseCreate`, and asserts on
the real `PromiseCreateRes` it gets back. What an implementer reads is
the request payload and the response fields, which is exactly what they
have to make true.

Every case runs against the specification, and `cases_all_pass` in
`cases.lean` is checked by `decide`. So what is handed over is not
"these tests are believed correct" but "the kernel agrees the
specification satisfies them".

## The monad

`StateT Ctx (Except Failure)`. The state carries the server between
calls, because a request lands on whatever the last one left behind.
`Except` short-circuits at the first failed check, and the step index
rides along so a failure says WHERE.

There is no clock. Every handler is `Req → (now : Nat) → H Res`: the
instant is an argument of the call, so each one carries its own. -/

namespace Tests

open ServerModel
open ConcreteModel

structure Failure where
  step : Nat
  what : String
  deriving Repr

structure Ctx where
  state : ServerState
  idx   : Nat

abbrev T := StateT Ctx (Except Failure)

def init : Ctx := { state := ServerState.init, idx := 0 }

def fail (what : String) : T Unit := do
  let c ← StateT.get
  throw { step := c.idx, what := what }

/-- Send a request. `h` is the handler applied to its request record —
    `P.promiseCreate req` — and `now` is the instant it happens at, so a
    call in a case reads as the call it is. -/
def call {α} (h : Nat → H α) (now : Nat) : T α := do
  let c ← StateT.get
  let (res, s') := Id.run ((h now).run c.state)
  set { state := s', idx := c.idx + 1 }
  return res

/-- The one assertion. Everything checked is a field of a response. -/
def check (b : Bool) (what : String) : T Unit :=
  if b then pure () else fail what

def run (t : T Unit) : Except Failure Unit :=
  match t.run init with
  | .ok _    => .ok ()
  | .error e => .error e

structure Case where
  name : String
  body : T Unit

def failures (cs : List Case) : List String :=
  cs.filterMap fun c =>
    match run c.body with
    | .ok _    => none
    | .error e => some s!"{c.name}: step {e.step}: {e.what}"

end Tests
