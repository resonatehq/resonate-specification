# A specification, and one way of running it

| | |
|---|---|
| `abstract.qnt` | THE SPECIFICATION. A server that handles a request when one arrives, and does its background work when that is enabled. |
| `concrete.qnt` | THE IMPLEMENTATION. A server that keeps the store, and workers that keep nothing between one piece of work and the next. |
| `choreo.qnt`, `spells/`, `template.qnt` | the framework, vendored |

**They share nothing.** Not a type, not a handler, not an identifier. One says
what may happen; the other is one way of making it happen. Anything held in
common would make the comparison between them unaskable — the same reason
`tla/Concrete.tla` writes out handlers it could have imported.

And they are not two versions of one thing. A specification describes a world of
possibilities: any request may arrive, in any order, and the background work
happens whenever the server's own state says it may. An implementation is a
machine — it has workers, dispatch, an inbox, and a story about what happens
when a machine dies in the middle.

## The continuation is implementation machinery

The specification never asks where a program has got to. A promise settles once;
a callback is a name to answer when it does; work becoming runnable is something
the server does to itself. There is no continuation anywhere in the file, and
nothing is missing.

The implementation cannot avoid one. It hands a piece of an execution to a
worker, takes back what remains, and hands *that* to whichever worker is free:

```quint
type Cont = { id: Id, seen: Set[Seen] }   // an execution, and what it already knows

type Message =
  | Invokes(Id)                             // client -> server
  | Execute({ cont: Cont })                 // server -> worker
  | Suspends({ cont: Cont, awaited: Id })   // worker -> server
  | Resolves({ id: Id, value: Value })      // worker -> server
```

Two of those carry a continuation, so here what remains of an execution is **a
value on the wire** — it outlives the machine that made it. A worker sets
`running: None` in the same step that sends it away; the server writes it down
as `Blocked(cont)`; and when the awaited promise settles, the server *re-forms*
it with the value it was missing and hands it out again:

```quint
| Blocked(cont) => struck.set(c.awaiter, { ...awaiter, task: Ready({ ...cont,
    seen: cont.seen.union(Set({ from: c.awaited, value: awaited.settled.unwrap() })) }) })
```

Upstairs that same moment is a name being struck and a turn being owed. Being
durable and being fragmented are one fact, and this is where it is visible.

The implementation does not know what the program does, any more than the
specification knows which request will arrive next: a worker running a piece may
find that it awaits anything, or returns anything, and every possibility is
offered.

## Running it

```
./check.sh
```

`choreo.qnt`, `template.qnt` and `spells/` are vendored verbatim from
[informalsystems/choreo](https://github.com/informalsystems/choreo) (Apache-2.0,
Gabriela Moreira, Josef Widder and Yassine Boukhari, Informal Systems) — the
same arrangement `tla/` has with `Variants.tla` and `Apalache.tla`.

## What came out

Simulation, 20 000 behaviours each.

**The specification** holds its own laws: a name is only ever registered on a
promise that exists, and nothing settled or absent is ever runnable. Promises
settle (98% of behaviours), names get registered (8%), and the background drain
runs (74%) — so none of it is vacuous.

**The implementation** holds the specification's one substantive law:

> `observationsAreTruthful` — everything a continuation claims to know, it
> learned from a promise that really did settle to that.

which is the interesting obligation, because this machine carries on executions
on machines that never began them.

| | |
|---|---|
| `fragmentsSplit` — two machines, one execution | 11% |
| `inTheStoreAndNowhereElse` — held by nobody, lost by nobody | 48% |
| `sameFragmentTwice` — a worker re-ran a piece | **98%** |
| `rerunDecidedDifferently` — and decided *differently* | **95%** |
| `stranded` — a continuation parked on a promise that already settled | **39%** |

The last three are the price of fragmenting, and none of them can be *stated*
upstairs: there are no pieces there, and no machines for them to be on.

`rerunDecidedDifferently` is the one worth sitting with. A worker takes work from
an inbox that never forgets and has no store to ask whether the work is still
wanted, so it re-runs a piece — and since it does not know what the program does,
the second run may decide something else entirely. The law survives anyway,
because what an execution did is a RECORD in the store rather than something
recomputed. That is what a promise is for.

`stranded` is where it does bite: the stale run's `Suspends` lands on a task that
had moved on, parking the OLD continuation on a promise that has already settled,
and nothing will wake it. A lease and a fencing version are the answer, and
`../concrete.qnt` is where they are modelled.
