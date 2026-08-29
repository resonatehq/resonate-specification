# Combinators — the design record

The mechanics are in the files and their headers:
`spec/01-protocol/combinators.lean` (the rules and the encoding),
`spec/02-abstract/state.lean` (birth), `spec/02-abstract/internal.lean`
(the resume), `spec/02-abstract/external.lean` (the doors),
`spec/02-abstract/properties.lean` (the entries).

This file is for what those cannot say: the alternatives that were
considered and rejected, and the questions that are still open. It is a
record of a design in progress, not documentation of a finished one.

## The shape, in one paragraph

A combinator is a promise tagged `resonate:combinator: <rule>` whose
param is a list of promise ids. Creating one arms a callback on each
child that is still pending, with the combinator itself as the awaiter.
When a child settles, the existing callback drain delivers a resume to
the combinator, which re-reads its children and asks its rule what to
do. `race` resolves naming the first settled child; `all` resolves when
every child has settled, naming all of them. Children that had already
settled before the combinator was created are handled by taking the same
verdict at birth.

## Decisions, and what they were chosen over

### The verdict is recomputed, not accumulated

A resume is a TRIGGER — "the answer may have changed" — and the rule is
re-asked against the store. The obvious alternative is to accumulate:
count the resumes, or keep a set of children seen, on the combinator
row.

Recomputing wins on three counts. There is no new field, so nothing to
keep consistent and nothing for a crash to lose. `all` needs no counter
and `race` needs no flag — the same two arguments serve both rules. And
the verdict is a function of the settled SET, so firing the drain twice,
or out of order, or late, gives the same answer; the schedule of the
background job is invisible in the result. The cost is re-reading the
children on each resume, which a real server can cache and which this
machine does not care about.

### `race`'s winner is the first child in PARAM order, not the earliest
### `settledAt`

"First to finish" ought to mean earliest settlement, and it cannot,
because `settledAt` does not order the children by the order the server
learned of them: a promise settled by its own deadline is stamped AT
that deadline, and a read can materialise that stamp long afterwards. So
a race decided at instant 200 could be re-read later and find a child
settled "at 50". Param order is a total order the client itself supplied
and no later event can change it.

### `race` resolves; it does not adopt the winner's verdict

The combinator reports WHO finished, not WHAT they finished with — a
value has room for one answer, and the identity is the answer only the
race knows. The awaiter reads the winner's promise for its outcome.

This is a real divergence from JavaScript's `Promise.race`, which adopts.
It is the decision most worth arguing about; see the open questions.

### `all` is `allSettled`

It waits for every child and does not fail fast on a rejection.
Fail-fast is a genuinely different rule and belongs here as a different
constructor rather than as a flag on this one.

### A combinator has no task, and no client may settle it

`otype` gained a fourth value. `combinator` is awaitable, carries no
target, and `promise.settle` answers 422 on one. Without that door the
"who settles this promise" axis would be a suggestion, and
`consistent_combinator_settlement_matches_rule` would be false of this
machine rather than of an implementation.

### The children must already exist

`promise.create` answers 422 if a named child is absent or unawaitable.
The alternative — create anyway, arm nothing, never settle — trades a
loud failure for a silent one. It also buys acyclicity for free: a
combinator names promises created before it and never itself, so no
cycle of combinators can be built and nothing downstream has to detect
one.

### A settled child is not armed; the combinator decides at birth instead

This is the one place combinators forced an existing invariant to be
re-examined. Arming a callback on a settled child would be simpler —
creation would have one path and the drain would handle everything — and
it is illegal: `monotone_promise_callbacks_shrink_once_settled` says
obligations on a settled promise only drain. That entry is load-bearing
for the drain's progress argument, so the birth verdict is the right
answer and the third birth shape in
`consistent_new_promise_born_clean` is its price.

It pays a dividend: `all` over an empty child list resolves at birth,
matching `Promise.all([])`, with no special case anywhere.

### No new internal step

A combinator settles on the callback drain that already existed. The
alternative — a `combinator` internal step, enabled when a pending
combinator has a settled child — would have been cleaner in isolation
and would have grown the alphabet, `enabledInternal`, the trace format,
the TLA+ alphabet and both trace checkers. The drain already delivers a
resume to an awaiter; combinators are a second kind of awaiter.

### One entry, not four, for the door

`well_formed_promise_combinator_is_well_formed` IS
`combinatorWellFormed`, the function the doors call. The catalogue's
stated rule is that a door check and its shadow property are the same
claim at two places; making them the same *function* is the strongest
form of that, because there is no second copy to drift. The falsifiers
are named `.../unknown_rule`, `.../targeted` and so on, so a violation
still says which refusal was breached.

### One rename

`consistent_callback_awaiter_is_targeted` became
`consistent_callback_awaiter_is_resumable`, and now admits a combinator
as well as a runnable promise. The old name said WHO the awaiter is; the
claim the protocol needs is WHAT CAN BE DONE with it. An implementation
still reporting the old name is checking the old, stronger claim and
will reject every combinator.

## Open questions

1. **Should `race` adopt the winner's verdict?** Today a race whose
   winner rejected still RESOLVES, naming the loser-of-nothing. That is
   coherent — "the race finished, here is who won" — and it diverges
   from every SDK's `race`. Adopting would mean the value can no longer
   name the winner, unless the value grows structure. A third option is
   two rules: `race` (reports the winner) and `race_adopt`.

2. **Is the id-list encoding right?** The param is
   `Ident.render`ed ids joined by commas, and `Value.isIdList` demands
   the string round-trip. It is the trace's own encoding for one id,
   comma-lifted, and it keeps the machine's parsing kernel-transparent.
   But it means a combinator's param cannot carry application data, and
   an SDK that already puts JSON in `param` has nowhere to put it. The
   alternative is a dedicated tag (`resonate:combinator:children`),
   leaving `param` free.

3. **Should the rules that never fire be reachable at all?** A `race`
   over an empty list, and any combinator whose children never settle,
   sit pending until their own deadline and then reject `timedout`.
   That matches the language semantics and it is a silent hang. A door
   check refusing an empty child list would close half of it; nothing
   closes the other half, which is the point of the deadline.

4. **What should `all`'s value be?** Today it is all the child ids,
   which is the param again. The alternative is an empty value — the
   awaiter knows the ids — at the cost of losing the uniform reading
   "a combinator's value names the children that decided it".

5. **The next rules.** `any` (first to RESOLVE, ignoring rejections)
   and a fail-fast `all` are the two the skeleton was shaped for, and
   both are four lines. Neither is written, because both raise
   question 1 in a sharper form.

## Not done

- **`valid/porc`** — the Go checker is not ported. Its loader now
  refuses any trace mentioning `resonate:combinator` rather than
  checking it against a machine that does not have them. The Lean
  checker needs no change: it runs the specification itself.
- **`tlap/`** — the TLA+ machine does not have combinators.
- **Nothing is proved.** The three new catalogue entries are checked by
  the sweep and the battery, not by `entries.lean`; they are cross-row
  claims, which that tier cannot reach.
