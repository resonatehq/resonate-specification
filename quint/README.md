# The Quint machine

`abstractAction.qnt` is `tla/AbstractAction.tla`, said in Quint. Same protocol,
same alphabet, same handlers, same invariants, same model — one request, one
transition, and a clock that the server does not own.

| | |
|---|---|
| `requests.qnt` | the vocabulary: what an object is, what a request is. Decides nothing. |
| `abstractAction.qnt` | the machine: the handlers, the deadlines, the invariants |
| `trans.qnt` | the four properties that are about a PAIR of states |
| `witnesses.qnt` | the states the machine had better be able to reach |
| `check.sh` | types, then simulation, then `verify` for the exhaustive pass |

There is no fence and there is nothing to fence. Every handler reads the store,
decides, and writes it in one step, so no two requests can get inside each
other. That is the altitude: this file says what a request MEANS. `Abstract.tla`
is where the atomicity comes out and the interleaving questions start, and it
has no Quint counterpart here.

## What the translation changed, and why

**Three things Quint says better.**

*The projection is applied once, to the whole store.* The TLA writes
`LET old == Project(objects[req.id], now)` at the head of fourteen handlers.
Here that is one definition —

```quint
val live: Id -> Object = ids.mapBy(i => project(objects.get(i), now))
```

— and handlers read `live` and write `objects`. The difference between the two
is exactly the work the timeout actions have not got to yet, which is the point
`project` was making all along. One action reads `objects` raw:
`processPromiseTimeout`, whose whole job is to make the store agree with the
projection.

*The five things that happen to a task are named.* `settled`, `acquiredBy`,
`pendingAt`, `suspended`, `halted`. Every `EXCEPT` block in the TLA is one of
these, and naming them is most of why the file is shorter: `taskRelease` is now
one line of consequence under four lines of guard, and the reader can see that
`processLeaseTimeout` and `taskRelease` do the *same thing* for different
reasons.

*The states and the messages are tagged unions, checked.* `PromiseState`,
`TaskState` and `Message` are sum types, so `TaskAcquired` is a value the
typechecker knows and `"acquird"` is a parse error rather than a guard that is
quietly never true. This is what Apalache's type pass was buying the TLA, made
part of the language.

**Two things Quint costs.**

*No primed reads.* TLA's `[][P]_vars` may say `objects'` inside `P`. Quint may
only prime on the left of an assignment, so the four `T_*` properties move to
`trans.qnt`, which carries the previous state in a spectator variable and states
them over `(prev, current)`. The machine is untouched; the wrapper is fifteen
lines.

*`action` is a keyword*, so the field the TLA calls `action` is `act`.

**One thing that is not translated.** `Fairness` and `Spec`. `AbstractAction.cfg`
checks `INIT`/`NEXT` with invariants, never `SPEC`, so the weak-fairness
conjuncts in the TLA are not exercised by the file's own model — and Quint has
no `WF_vars` to write them with. Nothing checked here depends on them. Liveness
is a question for the machine that has steps, which is `Abstract`.

**One thing that is a matter of taste.** The `.cfg` is inlined at the bottom of
`requests.qnt`, exactly the constants of `AbstractAction.cfg`. Quint has
`const` and instances, but a spec with no free constants is a spec both
`quint run` and `quint verify` take as it stands, and the model is part of the
experiment anyway: one origin with two rests gives two objects that share an
origin, and a second origin is what tests the other half of `sameOrigin`.

## Running it

```
./check.sh              # types, then the invariants and step properties by simulation
./check.sh verify 6     # the same, exhaustively, to depth 6
```

`quint run` samples random behaviours: it is fast, it finds violations, and it
proves nothing. `quint verify` calls Apalache, which is exhaustive up to the
step bound and slow — the same trade `tla/check.sh` records, for the same
reason. Neither checker ships with Quint: `run` fetches its Rust evaluator and
`verify` fetches Apalache, both from GitHub, on first use. `check.sh` pins
`--backend=typescript` so that the fast pass needs nothing but `npm i -g
@informalsystems/quint`; set `QUINT_BACKEND=rust` if you have it.

## Results

Simulation, 2 000 behaviours of 12 steps each, `--backend=typescript`:

| | |
|---|---|
| `typeOk` and the 6 `well_formed_*` | hold |
| the 3 `consistent_*` | hold |
| `unitCoherent`, `sameOrigin` | hold |
| the 4 step properties in `trans.qnt` | hold |

The machine is not vacuous: leases are acquired and expire, tasks are
suspended, halted, continued and fulfilled, callbacks and listeners are
registered and drained, `Execute` and `Unblock` both reach the outbox, versions
climb, and promises settle by request and by deadline — each confirmed as a
witness over the same runs.

`preserved_settled_promise_record` and `consistent_promise_settlement_stamp`
are the two the TLA records as failing. They fail in `Abstract`, where a step's
decision and its writes are separated and a second step can land in between.
Here there is no in between, and both hold — which is the same finding read
from the other side: those two properties are exactly what atomicity was
buying.
