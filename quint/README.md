# The Quint machines

Two machines and the question between them.

| | |
|---|---|
| `requests.qnt` | the vocabulary: what an object is, what a request is, which events exist. Decides nothing. |
| `abstract.qnt` | THE PROTOCOL. One request, one transition. |
| `concrete.qnt` | THE EXECUTOR. One document per origin, and a compare-and-swap on it. |
| `refine.qnt` | does the executor refine the protocol? |
| `trans.qnt` | the four properties that are about a PAIR of states |
| `witnesses.qnt` | the states the machines had better be able to reach |
| `check.sh` | types, the written-down traces, then simulation |
| `choreo/` | a second cut of the same system, in [Choreo](https://quint-lang.org/docs/choreo): processes rather than a store, and what fragmenting a continuation costs |

`abstract.qnt` is `tla/AbstractAction.tla`, `concrete.qnt` is
`tla/Concrete.tla`, and `refine.qnt` is `tla/RefineAction.tla` — same protocol,
same alphabet, same handlers, same invariants, same model.

**The handlers are written twice on purpose.** `concrete.qnt` does not import
the protocol's; borrowing them would make the refinement unaskable, because the
two machines would then agree by construction. Only the vocabulary is shared.

## What the translation changed, and why

**A handler is a partial function.** `pure def promiseSettle(s: State, req):
Set[State]` — one outcome, or none at all when the request does not apply. That
is the Lean's shape (`spec/02-abstract` makes one request one transition) and it
buys the thing TLA+ gets from `INSTANCE`: the machine can hand over its
transition RELATION, `stepsTo(before, after)`, which is what `refine.qnt` asks of
every executor transition. `step` is still written as the TLA's `Next` — a table
of one line per request — and `trans.qnt` checks that the two agree
(`own_steps_are_steps`), so the relation the refinement uses is measurably the
same machine.

**The projection is read, never scattered.** The TLA writes `LET old ==
Project(objects[req.id], now)` at the head of fourteen handlers. Here it is
`s.live(i)`, and the difference between `live` and `objects` is exactly the work
the timeout events have not got to yet. One handler reads `objects` raw:
`promiseTimeout`, whose whole job is to make the store agree with the
projection.

**The five things that happen to a task are named** — `settled`, `acquiredBy`,
`pendingAt`, `suspended`, `halted`. Every `EXCEPT` block in the TLA is one of
them, which is why `processLeaseTimeout` and `taskRelease` are visibly the same
move for different reasons.

**The states, messages, effects and alphabet are tagged unions, checked.** A
misspelled state is a parse error rather than a guard that is quietly never
true — which is what the Apalache type pass was buying, made part of the
language.

**And so is absence.** `tla/Requests.tla` needs four sentinels — `NoTime`,
`NoPid`, `NoAddr`, `NoValue` — because TLA+ has no sum type to put absence in,
and one sentinel answering four different questions is worse than four answering
one each. Here it is `Option[a] = Some(a) | None`, once, and the guards get
shorter for it: `expiresAt != NoTime and expiresAt <= now` becomes
`due(expiresAt, now)`, where "`None` is never due" is a fact of the type rather
than a conjunct anybody has to remember. An absent TASK is still not an option
type — a task in state `TaskNone` is the honest reading, because whether a
promise is targeted is part of the unit's state and not a hole in it.

**Two things Quint costs.** There is no primed READ, so a two-state property
needs the previous state carried in a spectator variable: that is all of
`trans.qnt`'s scaffolding and all of `refine.qnt`'s. And `action` is a keyword,
so the field the TLA calls `action` is `act`.

**Not translated:** `Fairness` and `Spec`. The `.cfg` checks `INIT`/`NEXT`, so
nothing in the model exercises them, and Quint has no `WF_vars`. Liveness is a
question for a machine with steps, and this one has none.

## Running it

```
./check.sh              # types, the written-down traces, then simulation (~90s)
./check.sh verify 6     # the protocol's invariants, exhaustively, to depth 6
```

`quint run` samples random behaviours: it is fast, it finds violations, and it
proves nothing. `quint verify` calls Apalache, which is exhaustive up to the
step bound and slow. Neither checker ships with Quint — `run` fetches a Rust
evaluator and `verify` fetches Apalache, both from GitHub, on first use. Set
`QUINT_BACKEND=typescript` for a slower evaluator that needs no download.

**Some behaviours are written down rather than searched for.** A dispatched
message is ten aligned steps from an empty store and the refinement
counterexample is nine, while every submit picks one event out of two hundred —
so random search reaches them rarely or never. `quint test` runs those traces
directly, which is the same evidence and a better record.

## Results

Simulation, 20 000 behaviours of 30 steps, plus the scripted traces.

| | |
|---|---|
| the protocol's 12 invariants | hold |
| the four step properties, and `own_steps_are_steps` | hold |
| the protocol's invariants, asked of what the executor's store denotes | hold |
| `wheelComplete` | holds |
| `wheelSound` | **fails** |
| `refinesAction` | **fails** |

### The executor does not refine the protocol

A step reads one document, decides against it, and lands the decision in one
write. But before it decides it may SWEEP: fire whatever that same document
says is already due. Both go into the same write.

```
create b, deadline at 1            b pending, wheel armed at 1
clock                              now = 1, so b is due
create a, arriving at a step that also finds b due
  -> one write: b times out AND a is born settled
```

Upstairs those are two steps — a timeout and a create — and `[][Next]_vars` has
room for one. `sweepAndHandleIsTwoStepsTest` in `refine.qnt` is that trace;
`emptySweepIsOneStepTest` is the control, the same trace with the sweep empty,
and it holds. So it is the sweep, and not the split write, the fence, or the
clock.

**TLC says the same thing about the TLA.** `./check.sh RefineAction` in `tla/`
returns a counterexample of the same shape — a sweep that times out one promise
and creates another in a single write — which is what `RefineAction.tla`'s own
header predicts. The remedy it names, an abstract machine whose step takes an
explicit swept pre-state, is not in the repository. Two independent
translations, two checkers, one answer.

`wheelSound` fails for the reason the TLA gives: arming before writing admits an
entry for an object that is not there yet. That is noise a handler re-checks
away, and no fence removes it.

### What the fence does

`concrete.qnt` carries two knobs, both `pure val`s at the top of the file.
`Fenced` compares the document and the clock a decision was read under, and
refuses a write whose document has moved. `Sweeping` decides whether a step may
drain what it finds due. They are switchable so that each can be made to prove
its own necessity, which is the experiment the two machines are here for.
