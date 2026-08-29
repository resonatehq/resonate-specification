import «01-protocol».«validation»

/-!  # Combinators — a promise whose verdict is a rule over other promises

A COMBINATOR is a promise the server settles itself, by watching
promises it names. `resonate:combinator` says which rule; the param
says which promises. Nothing acquires it, nothing settles it from
outside, and it is awaitable — which is the point, since combining
exists to be waited on.

This file is the whole of the combinator surface that is not a
transition: the rule names, the encoding of an id list, the door check
every creating handler applies, and one function per rule. It is all
pure and all decidable, which is what lets the catalogue state a
combinator's verdict by CALLING the same function the machine calls
rather than by restating it.

## The shape of a rule

    Combinator.<name> : (children settled : List Ident) → Verdict

`children` is the promise's param, read as the id list it is required
to be. `settled` is the sublist of those that have settled, in param
order. `none` means keep waiting.

A rule sees the SET of settled children and nothing else. It does not
see settlement timestamps, and it must not: a promise settled by its
own deadline is stamped AT that deadline, which can be earlier than a
settlement recorded long before it — so `settledAt` does not order the
children by the order the server learned of them. Param order does, and
the client supplied it.

A rule sees no clock, no state and no store, so a verdict cannot depend
on WHEN it is asked, only on what has settled. That is what makes the
drain's schedule unobservable in the verdict: whichever background job
fires first, a rule asked twice at the same settled set answers the
same thing.

## Adding one

Four lines in four places, and the compiler finds all four: a
constructor, a `parse` arm, a function, a `verdict` arm. Nothing in
`02-abstract` mentions a rule by name.

## What the rules here mean

  `race`  the first child to settle decides, and the combinator
          RESOLVES with that child's id — it does not adopt the child's
          verdict. A race reports WHO finished; the awaiter reads that
          promise for what it finished with. Adopting would throw the
          winner's identity away, since a value has room for one answer
          and the identity is the answer only the race knows.

  `all`   settles when every child has settled, resolving with all of
          their ids. This is `allSettled`: it does not fail fast on a
          rejected child. Fail-fast is a DIFFERENT rule and belongs
          here as a different constructor, not as a flag on this one.

Neither rule ever rejects. A combinator that must not resolve is a
combinator that keeps waiting, and the deadline it was created with is
what ends the wait — `rejectedTimedout`, stamped at `timeoutAt`,
exactly as for any other promise. -/

namespace ServerModel

/-! ## The rules -/

inductive Combinator
  | race
  | all
  deriving Repr, DecidableEq

/-- The tag value, as a rule. `none` for a name this protocol does not
    implement, which every creating door refuses — see
    `combinatorWellFormed`. -/
def Combinator.parse : String → Option Combinator
  | "race" => some .race
  | "all"  => some .all
  | _      => none

def Combinator.render : Combinator → String
  | .race => "race"
  | .all  => "all"

def Tags.combinator (t : Tags) : Option Combinator :=
  (t.get? "resonate:combinator").bind Combinator.parse

theorem combinator_implies_isCombinator (t : Tags) :
    t.combinator.isSome = true → t.isCombinator = true := by
  unfold Tags.combinator Tags.isCombinator Tags.has
  cases h : t.get? "resonate:combinator" <;> simp

/-! ## An id list, on the wire

A combinator's param IS its child list, and its value IS the children
that decided it. Both are the same encoding: `Ident.render`ed ids
joined by commas, which is the encoding a trace already carries for one
id, comma-lifted.

`splitOnComma` is written out rather than taken from core so that the
kernel can reduce it: every sweep in `04-theorems` evaluates these by
`decide`.

A comma cannot appear inside an id under this encoding, and nothing
needs to say so separately: `isIdList` demands that rendering the parse
gives the original string back, so an id carrying a comma fails to
round-trip and the door refuses it. -/

private def splitOnComma : List Char → List (List Char)
  | []        => [[]]
  | ',' :: cs => [] :: splitOnComma cs
  | c :: cs   =>
      match splitOnComma cs with
      | p :: ps => (c :: p) :: ps
      | []      => [[c]]

def Ident.parseList (s : String) : List Ident :=
  if s.isEmpty then [] else (splitOnComma s.toList).map (fun cs => Ident.parse (String.ofList cs))

def Ident.renderList : List Ident → String
  | []      => ""
  | [i]     => i.render
  | i :: is => i.render ++ "," ++ Ident.renderList is

/-- The ids a value carries. Total: a value that is not an id list
    parses to whatever it parses to, and `isIdList` is the predicate
    that says whether that reading was faithful. Only ever consulted
    where the tags say the value is one. -/
def Value.ids (v : Value) : List Ident :=
  Ident.parseList (v.data.getD "")

def Value.ofIds (ids : List Ident) : Value :=
  { data := some (Ident.renderList ids) }

/-- The value round-trips through the id-list encoding: what it holds
    is exactly what rendering its parse produces. This is the
    "the param must be a list of promise ids" constraint, as a
    decidable predicate on the value the client actually sent. -/
def Value.isIdList (v : Value) : Bool :=
  Ident.renderList v.ids == v.data.getD ""

/-! ## The door

One predicate, applied by every handler that creates a promise and
stated again as a catalogue entry over the store. The door refuses the
write; the entry refuses the row. They are the same claim at two
places, and making them the same FUNCTION is what stops them drifting
apart. -/

/-- What a combinator promise must satisfy to exist.

    Read it as five refusals:

      * the rule is one we implement — an unknown name is a promise
        nothing will ever settle, so it is a 400 and not a shrug;
      * nothing executes a combinator, so it carries no target;
      * no deadline decides a combinator either, so it is not a timer —
        a timer resolves AT `timeoutAt` and a combinator rejects there,
        and a promise cannot be both;
      * the param is an id list, faithfully;
      * and the children are distinct, none of them the combinator
        itself, all in its origin — the last so that an awaits-edge
        never leaves the shard it started in, which is the same rule
        `promise.callback` and `task.suspend` enforce at their doors.

    Vacuously true of every promise that is not tagged a combinator, so
    a handler can apply it unconditionally. -/
def combinatorWellFormed (id : Ident) (param : Value) (tags : Tags) : Bool :=
  !tags.isCombinator
    || (tags.combinator.isSome
        && !tags.has "resonate:target"
        && !tags.isTimer
        && param.isIdList
        && (let cs := param.ids
            cs.eraseDups.length == cs.length
              && cs.all (fun c => c != id && c.sameOrigin id)))

/-- The children of a promise: its param read as an id list, and ONLY
    where the tag says the param is one. A promise with no combinator
    tag has no children, whatever its param happens to contain — the
    param of an ordinary promise is opaque application data and this
    machine never looks inside it. -/
def combinatorChildren (tags : Tags) (param : Value) : List Ident :=
  if tags.isCombinator then param.ids else []

theorem combinatorChildren_of_plain (tags : Tags) (param : Value) :
    tags.isCombinator = false → combinatorChildren tags param = [] := by
  intro h; simp [combinatorChildren, h]

/-! ## The rules, as functions

One per constructor in `Combine`, then the table that dispatches. Both
halves are here so that `02-abstract` never names a rule: the resume
path asks `Combinator.verdict` and the arm it lands in is this file's
business. -/

abbrev Verdict := Option (PromiseState × Value)

namespace Combine

/-- The first child to settle decides, and the combinator resolves
    naming it. `settled` is in param order, so the winner among several
    is the one the client listed first — a tie-break the client chose,
    rather than one read off timestamps the deadline path can stamp in
    the past. -/
def race (_children settled : List Ident) : Verdict :=
  match settled with
  | []     => none
  | w :: _ => some (.resolved, Value.ofIds [w])

/-- Every child, and then the combinator resolves naming all of them.
    The children are distinct and `settled` is a sublist of them, so
    counting is the same test as comparing the lists. -/
def all (children settled : List Ident) : Verdict :=
  if settled.length == children.length then
    some (.resolved, Value.ofIds children)
  else
    none

end Combine

def Combinator.verdict : Combinator → (children settled : List Ident) → Verdict
  | .race => Combine.race
  | .all  => Combine.all

/-- No rule rejects, and no rule leaves a promise pending-with-a-value.
    Proved rather than asserted, because the settlement path takes the
    verdict at its word: it stamps `settledAt` and fulfils whatever the
    state says, and a rule that answered `.pending` would write a row
    the catalogue forbids. Adding a rule that breaks this breaks the
    proof, which is the point. -/
theorem verdict_settles (c : Combinator) (children settled : List Ident)
    (st : PromiseState) (v : Value) :
    c.verdict children settled = some (st, v) → st.settable = true := by
  cases c
  · simp only [Combinator.verdict, Combine.race]
    cases settled with
    | nil       => simp
    | cons _ _  => intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨hst, _⟩ := h; subst hst; rfl
  · simp only [Combinator.verdict, Combine.all]
    split
    · intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hst, _⟩ := h; subst hst; rfl
    · simp

end ServerModel
