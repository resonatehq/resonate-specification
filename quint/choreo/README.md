# The fragmented continuation

Two Choreo machines running the same program:

```
f() { val v = await g(); return v + 1 }
g() { return 41 }
```

| | |
|---|---|
| `workflow.qnt` | the program, and the `Cont` type. Shared, so every difference below is a difference in the RUNTIME. |
| `abstract.qnt` | one process per invocation. A continuation never leaves the process it was born in. |
| `concrete.qnt` | a server holding the store, and two workers holding nothing. One execution, many fragments. |
| `choreo.qnt`, `spells/`, `template.qnt` | the framework, vendored |

## The difference is in the message type

That is the whole thing, and it is visible without reading a single transition.

```quint
// abstract.qnt
type Message =
  | Invoke(Id)
  | Completed({ id: Id, value: int })

// concrete.qnt
type Message =
  | Execute({ id: Id, cont: Cont })                 // server -> worker
  | Suspends({ id: Id, cont: Cont, awaited: Id })   // worker -> server
  | Resolves({ id: Id, value: int })
```

Upstairs a continuation is **not sendable**. There is no constructor that
carries one, so it cannot go anywhere, so one execution is one process from
beginning to end. An `await` parks the process — `Parked({ cont, awaited })` —
and the continuation sits there on its stack until the answer arrives. That is
what an ordinary async runtime gives you.

Downstairs a continuation is **a value on the wire**. A worker takes one
fragment, runs it to the next await, hands what remains back to the server, and
sets `running: None` — it forgets. The server writes the continuation into the
store as `Blocked(cont)`, and when the awaited promise settles it *re-forms*
that continuation with the value it was missing:

```quint
| Blocked(c) => acc.set(a, { ...acc.get(a), task: Ready({ ...c, pc: Resumed(v) }) })
```

and dispatches it again — to whichever worker is free. **The same execution runs
on two machines**, and the store is what makes it one execution.

Being durable and being fragmented are the same fact: a continuation that can
outlive the machine that made it is a continuation that can be picked up
somewhere else.

## Running it

```
./check.sh
```

`choreo.qnt`, `template.qnt` and `spells/` are vendored verbatim from
[informalsystems/choreo](https://github.com/informalsystems/choreo) (Apache-2.0,
Gabriela Moreira, Josef Widder and Yassine Boukhari, Informal Systems) — the
same arrangement `tla/` has with `Variants.tla` and `Apalache.tla`, and for the
same reason: the dependency is on the definitions, not on a tool.

## What it shows

Simulation, 20 000 behaviours; plus two scripted traces that walk the whole
execution deterministically (`executionTest`, `fragmentedTest`).

| | abstract | concrete |
|---|---|---|
| `noWrongAnswer` — the root returns 42 or has not returned | holds | holds |
| `answered` — it gets there | 100% of traces | 4.6% |
| `fragmentsSplit` — one execution ran on two machines | *unsayable* | **30%** |
| `inTheStoreAndNowhereElse` — no machine holds it and it is not lost | *unsayable* | 99.7% |
| `sameFragmentTwice` — a worker re-ran a fragment | *unsayable* | **99.98%** |
| `stranded` — a continuation parked on an already-settled promise | *unsayable* | **78%** |

The first two rows are the ones that agree. The other four are the ones the
abstraction was hiding, and they cannot even be *stated* upstairs: there is no
second machine for an execution to move to, so there is nothing to ask.

### What fragmenting costs

**A fragment can run twice.** A worker takes work from a message soup that never
forgets, and it has no store to ask whether the fragment is still wanted. So it
can pick up one it has already run. Nothing here stops it.

**And a stale fragment can strand a live one.** The second run sends its
`Suspends` late, and the server accepts it because the only thing it fences on
is the task's own state. The continuation it parks is the OLD one, and by then
the awaited promise has already settled — so nothing will ever wake it. That is
`stranded`, and it is a permanent lost update, not a transient state.

Both are exactly what the lease and the fencing version in `../concrete.qnt` are
for. This pair is where the need for them becomes visible; that pair is where
they are modelled.
