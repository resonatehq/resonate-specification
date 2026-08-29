import «01-protocol».«types»

namespace ServerModel

def Tags.get? (t : Tags) (k : String) : Option String :=
  (t.find? (·.fst == k)).map (·.snd)

def Tags.has (t : Tags) (k : String) : Bool :=
  (t.get? k).isSome

def Tags.isTimer (t : Tags) : Bool :=
  t.get? "resonate:timer" == some "true"

/-- The combinator tag, asked as a BOOLEAN rather than parsed. The two
    questions are different and both are needed: whether a promise
    claims to be a combinator decides its place on the axis below, and
    whether the name it claims is one we implement is a door check. A
    promise tagged `resonate:combinator: quorum` is a combinator with an
    unknown rule -- it must not fall through to `internal` and quietly
    become an ordinary promise. -/
def Tags.isCombinator (t : Tags) : Bool :=
  t.has "resonate:combinator"

/-- WHO SETTLES THIS PROMISE. Four answers, and every door in the
    machine is one of them asked at a different angle.

      internal    the process that created it, and nobody else may wait
      external    some party outside, reached by a listener
      runnable    a worker, handed the execution as a task
      combinator  the SERVER, by a rule over other promises

    `combinator` is the one with no counterparty: nothing acquires it,
    nothing settles it from outside, and its verdict is a function of
    promises it names. It is awaitable, because the point of combining
    is to be waited on. -/
inductive OType
  | internal
  | external
  | runnable
  | combinator
  deriving Repr, DecidableEq

def OType.awaitable : OType → Bool
  | .internal => false
  | _         => true

/-- The axis, read off the tags. ORDER IS THE CLAIM: `target` first, so
    that a promise carrying both a target and a combinator tag reads as
    `runnable` and the contradiction is a ROW the catalogue can name
    (`well_formed_promise_combinator_is_well_formed`) rather than a
    disagreement hidden inside this function. The same reading is why
    `timerTargeted` is a 400 and not a silent preference. -/
def Tags.otype (t : Tags) : OType :=
  if t.has "resonate:target" then
    .runnable
  else if t.isCombinator then
    .combinator
  else if t.get? "resonate:scope" == some "global"
      || t.get? "resonate:external" == some "true"
      || t.isTimer then
    .external
  else
    .internal

theorem otype_runnable_iff_targeted (t : Tags) :
    t.otype = .runnable ↔ t.has "resonate:target" = true := by
  cases ht : t.has "resonate:target" with
  | true  => simp [Tags.otype, ht]
  | false => simp [Tags.otype, ht]; split <;> (try split) <;> simp

theorem targeted_implies_awaitable (t : Tags) :
    t.has "resonate:target" = true → t.otype.awaitable = true := by
  intro h; simp [Tags.otype, h, OType.awaitable]

def Tags.timerTargeted (t : Tags) : Bool :=
  t.isTimer && t.has "resonate:target"

def PromiseState.settable : PromiseState → Bool
  | .resolved | .rejected | .rejectedCanceled => true
  | _ => false

def TaskFenceAction.targetId : TaskFenceAction → Ident
  | .create r => r.id
  | .settle r => r.id

/-! ## The wire form of an id

`Ident` is a pair; the wire carries one string. `render` and `parse`
are the seam, and they live HERE rather than in the trace checker
because the specification itself now has to write an id into a value —
a combinator's verdict names the promises that decided it — and read
one back out. The checker used to own both; owning them there made the
encoding a property of one consumer instead of a property of the
protocol.

`render` is `origin:suffix`, with exactly one colon, and a bare origin
when the suffix is empty. `parse` is its inverse, structurally
recursive over `toList` in the house style so nothing here is opaque to
the kernel. -/

def Ident.render (i : Ident) : String :=
  if i.suffix.isEmpty then i.origin else i.origin ++ ":" ++ i.suffix

private def splitColon : List Char → List Char × List Char
  | []          => ([], [])
  | ':' :: rest => ([], rest)
  | c :: cs     => let (o, r) := splitColon cs; (c :: o, r)

/-- An id with no colon is its own origin, which is what makes `parse`
    the inverse of `render` on every id `render` can produce. -/
def Ident.parse (s : String) : Ident :=
  let (o, r) := splitColon s.toList
  { origin := String.ofList o, suffix := String.ofList r }

def parseNat (s : String) : Nat :=
  go s.toList 0
where
  go : List Char → Nat → Nat
    | [], acc => acc
    | c :: cs, acc => go cs (acc * 10 + (c.toNat - '0'.toNat))

inductive Message
  | execute (taskId : Ident) (version : Nat)
  | unblock (promise : PromiseRecord)
  deriving Repr

structure OutboxEntry where
  address : String
  message : Message
  deriving Repr

inductive OutboxKey
  | execute (taskId : Ident)
  | notify  (promise : Ident) (address : String)
  deriving Repr, DecidableEq

instance : BEq OutboxKey := instBEqOfDecidableEq

def OutboxEntry.key : OutboxEntry → OutboxKey
  | { message := .execute taskId _,  .. } => .execute taskId
  | { address, message := .unblock p }    => .notify p.id address

opaque nextCron : (cron : String) → (after : Nat) → Nat

opaque occurrences : (cron : String) → (since now : Nat) → List Nat

opaque expand : (template id : Ident) → (timestamp : Nat) → Ident

end ServerModel
