# Resonate Durable Objects

**Status**: design proposal with runnable prototypes
**Prototypes**: `resonate-sdk-ts` branch `claude/resonate-durable-objects-donm81`, `src/objects/` + `tests/objects/`
**Scope**: developer experience, semantics, and mechanics of a durable-object
(virtual actor) primitive on top of the Resonate protocol — including whether
the protocol needs extending, and how objects and durable functions compose
recursively.

---

## 1. Problem

Durable functions answer "how does a *computation* survive failure": a
function invocation is rooted in a durable promise, its progress is a tree of
durable promises, and recovery is replay-with-dedup against that tree.

They do not answer "how does an *entity* live forever": a user, an account, a
game session, a device — something with identity, state, and an inbox, that
processes messages one at a time, forever, and is mostly idle. Every mature
platform grows this second primitive (Temporal's entity workflows, Restate's
virtual objects, Cloudflare's Durable Objects, Orleans' grains), and every
naive encoding of it on an event-sourced substrate hits the same two walls:

* **W1 — unbounded replay.** If the entity is one long-lived computation,
  its journal grows with its lifetime, and recovery replays the lifetime.
* **W2 — unbounded live objects.** If the entity is a resident runtime
  artifact (an open task, a pinned loop, worker memory), a million mostly-idle
  entities cost a million residencies.

Any design below is judged first against W1 and W2, then against a third
requirement:

* **R3 — recursive integration.** Objects and durable functions must compose
  in all directions — function→object, object→function, object→object,
  function→function — with the same durability guarantees as any other edge
  in the computation graph.

## 2. Prior art

What the three reference systems actually do, reduced to the load-bearing
mechanics. (Specifics verified against current vendor documentation.)

### 2.1 Temporal entity workflows

A *pattern*, not a primitive: one long-lived workflow execution per entity,
signals/updates as the mailbox, queries for reads. The durable truth is the
**event history**; state is reconstructed by deterministic replay of the whole
history. That is W1 in its purest form, and Temporal makes the user manage it:
histories hard-cap at 51,200 events / 50 MB, so the workflow must periodically
**continue-as-new** — close the run, start a fresh run with the same workflow
id, and carry forward only what it explicitly passes as arguments (≤ ~2 MB).
The choreography is delicate: signals received but not yet processed are
*lost* across continue-as-new, so the documented sequence is stop-taking-work
→ drain the signal channel → wait for handlers to finish → continue-as-new
from the main thread. Reads are worker-bound (a query replays the execution on
a worker); there is no server-side state read. Lifecycle: server-side the
entity is durable regardless of workers (W2 is a storage cost, not a memory
cost), but per-entity throughput is capped by workflow-task serialization.

Takeaways: the *run-chain with carried state* is the right bounding move but
should be structural, not user choreography; the signal-drain hazard is what a
mailbox-shutdown protocol looks like when the platform doesn't own it; reads
deserve a path that touches no worker.

### 2.2 Restate virtual objects

A *primitive*: services keyed by `(service, key)`, exclusive handlers
serialized per key (a queue per key), shared handlers concurrent + read-only.
The decisive design split is the **two-layer state model**:

* entity state is **materialized K/V** (`ctx.get/set`), retained indefinitely,
  co-located with execution;
* execution durability is a **journal scoped to one handler invocation**,
  discarded once the invocation completes (its state effects having been
  committed to K/V).

Replay cost is therefore bounded by one handler execution regardless of how
many million invocations the object has processed — W1 dissolves because
nothing accumulates. Objects are fully virtual: no create/delete, any key
"exists", state persists until cleared — W2 is again purely a storage concern.
Messaging: durable RPC, durable one-way sends, delayed sends; per-sender FIFO
into the per-key queue. The documented failure mode is the cycle deadlock:
exclusive A calls B while B calls A (same keys) and both wait forever;
Restate does not detect it — you cancel by hand.

Takeaways: **journal-per-invocation + materialized snapshots** is the answer
to W1; serialization should be a *dispatch* property, not user code; cycle
deadlock is inherent to synchronous calls between single-writers — the
platform's job is to make one-way sends first-class so cycles have a safe
shape.

### 2.3 Cloudflare Durable Objects

No journal at all: a DO is a single-threaded class instance with transactional
storage (SQLite-backed), input/output gates for consistency, and **no replay
ever** — after a crash the object re-instantiates and reads current storage;
in-flight application logic is the caller's problem. Idle objects hibernate or
get evicted (W2 solved by the platform); alarms are the one built-in
at-least-once primitive; RPC between DOs opens the caller's input gate, so
cross-DO calls interleave rather than deadlock — at the price of the caller's
state changing under the await. There is no durable execution: retries,
resumption, idempotency are application code.

Takeaways: storage-authoritative state gives free lifecycle (create-on-first-
use, hibernate, `deleteAll`) and cheap reads; but without durable execution
each handler's *effects* are unprotected. The interesting synthesis is DO-like
lifecycle with Resonate-grade execution durability inside each handler.

### 2.4 Reference points

**Orleans** contributes the *virtual actor* idea itself: a grain logically
always exists; the runtime activates on demand and deactivates idle
activations. **Akka persistent actors** contribute the snapshot answer to W1:
event-source the actor but periodically checkpoint materialized state so
recovery replays only the suffix.

### 2.5 Synthesis

| | state model | W1: replay bound | W2: idle cost | reads | cycles |
|---|---|---|---|---|---|
| Temporal entity | event history | manual (continue-as-new) | storage | worker replay | async signals |
| Restate VO | K/V + per-invocation journal | structural | storage | shared handler | deadlock (undetected) |
| Cloudflare DO | authoritative storage | n/a (no replay) | ~zero (hibernate) | direct | interleave |
| **Target** | **snapshot chain + per-message journal** | **structural** | **zero residency** | **snapshot read** | **safe via sends** |

## 3. What the Resonate protocol already provides

The protocol surface (promises, tasks, schedules — `spec/01-protocol`) turns
out to contain almost every ingredient:

1. **CAS registers.** `promise.create` is idempotent first-writer-wins: an id
   can be claimed exactly once, and the loser observes the winner's record.
   `promise.settle` is likewise first-writer-wins. These are consensus-free
   atomic registers keyed by promise id.
2. **Server-ordered wakeups.** A task can `task.suspend` with callbacks on
   awaited promises; the server resumes it (re-dispatches an `execute`) when
   an awaited promise settles. Ordering machinery, no locks, no polling.
3. **Routed execution.** A promise tagged `resonate:target` causes the server
   to mint a task and dispatch it to a worker group — computation placement
   is already server-driven and affinity-free.
4. **Exclusive execution.** Tasks are single-claim leases with version
   fencing (`AtMostOneValidClaim`) — one worker drives one computation.
5. **Latent promises + external settles.** A promise can exist with no
   computation and be settled out of band — a durable, awaitable mailbox cell.
6. **Delayed dispatch and schedules.** `resonate:delay` defers a task's
   dispatch to a timestamp; schedules give cron. Alarms come for free.
7. **Timeout always wins.** Every object encoded in promises inherits the
   spec's timeout discipline — a wedged entity cannot outlive its deadlines.

What the protocol does **not** provide:

* any ordering *between* independent promises (each root is its own island);
* any materialized mutable state (promises are write-once);
* any "append to a sequence" or "read the head of a sequence" operation;
* retention/GC semantics for settled records (implementation latitude today).

The design question is exactly: encode ordering + mutable state in userland
over (1)–(7), or extend the protocol. We prototyped both, plus the Temporal
shape, plus a degenerate alternative — four runnable variants over one
developer-facing API.

## 4. Developer experience

The same definition mounts on every runtime variant. All code below is
running code from the prototype tests (`tests/objects/`).

```ts
import { defineObject } from "@resonatehq/sdk/objects";

const account = defineObject<{ balance: number }>({
  name: "Account",
  initial: (key) => ({ balance: 0 }),
  handlers: {
    // A handler is a full durable workflow: ctx.run / ctx.rpc / ctx.sleep /
    // ctx.detached are durable operations journaled to THIS message.
    deposit: async (ctx, amount: number) => {
      ctx.state.balance += amount;          // materialized state, committed
      return ctx.state.balance;             // atomically with the message
    },
    transfer: async (ctx, to: string, amount: number) => {
      ctx.state.balance -= amount;
      const theirs = await ctx.object(account, to)   // object → object call
        .call<number>("credit", amount);
      await ctx.detached("audit", ctx.key, to, amount); // object → function
      return { mine: ctx.state.balance, theirs };
    },
    credit: async (ctx, amount: number) => (ctx.state.balance += amount),
  },
});
```

Client side (outside any workflow):

```ts
const objects = new ChainObjects({ resonate, network }); // or Loop / Serial
objects.register(account);

const acc = objects.get(account, "alice");
await acc.call("deposit", 100);      // request/response, durable, serialized
await acc.send("deposit", 50);       // one-way, durable, returns message id
await acc.sendLater("deposit", [10], 60_000); // alarm: delayed self-message
const { state } = await acc.read();  // snapshot read — no handler, no queue
await acc.delete();                  // tombstone
```

Workflow side (inside any durable function — this is R3's function→object
edge):

```ts
const checkout = async (ctx: Context, sku: string) => {
  const order = objects.in(ctx).get(orders, "cart-1");
  return order.call("place", sku, 3, 100);   // caller suspends durably,
};                                           // resumes with the result
```

Semantics the API commits to, in one place:

* **Identity**: `(type, key)` — virtual, Orleans-style. No creation call; the
  object exists the moment anyone names it. `initial(key)` materializes
  lazily on first message.
* **Serialization**: at most one handler per object executes at a time, in a
  total order all parties agree on. Handlers of *different* objects are fully
  concurrent.
* **State**: `ctx.state` is a materialized snapshot, hydrated from the
  predecessor message, committed atomically with the message's settle. A
  handler that throws commits the *pre-message* state (rollback) and the
  error travels to the caller; the mailbox advances (no wedge, no infinite
  retry by default — retries are an explicit per-message policy).
* **Calls vs sends**: `call` is durable request/response (caller suspends);
  `send` is durable one-way (caller continues; delivery survives caller
  death). Self-`call` is rejected eagerly as a deadlock; self-`send` is the
  supported self-messaging idiom. Object→object `call` cycles can deadlock
  exactly as in Restate — the guard catches the self-edge, the docs prescribe
  `send` for cyclic topologies (prototyped in the matrix tests: an A⇄B volley
  via sends terminates cleanly).
* **Reads**: `read()` returns the latest committed snapshot without entering
  the mailbox — concurrent, unserialized, worker-free (variant-dependent
  freshness, see §5).
* **Deletion**: a tombstone message. Later messages fail with
  `ObjectDeletedError`; storage reclamation is retention policy (§7.3).

## 5. The alternatives, prototyped

Four variants, one API. Each was built and tested against the in-process
server model (`LocalNetwork`) — real promises, real tasks, real
suspend/resume, no mocks.

### 5.1 Variant A — the message chain (`chain.ts`) — recommended baseline

**The object is the totally-ordered chain of its message promises.** There is
no loop, no activation, no resident anything.

```
o/Account/alice/m0 ──▶ o/Account/alice/m1 ──▶ o/Account/alice/m2 ─▶ …
   value:{s₀,r₀}          value:{s₁,r₁}          pending
```

Mechanics of one `call`, at the wire level:

1. **Append (sender).** Probe the head (first missing `m{n}` — galloping
   binary search over `promise.get`, O(log) calls, cached watermark), then
   `promise.create m{n}` with param = envelope `{method, args, ik, replyTo}`
   and tag `resonate:target = <object worker group>`. Create is CAS: the
   loser observes a foreign envelope and retries at `n+1`. The winner's
   create *is* the enqueue — atomic, no two-phase hazard. A crashed sender's
   retry re-finds its own envelope by idempotency key and adopts it
   (exactly-once append; from inside a workflow the `ik` is the enqueue
   leaf's own deterministic promise id, so replays adopt).
2. **Dispatch (server).** The create minted a task; the server mails
   `execute m{n}` to the object group. Any worker claims it. No affinity.
3. **Serialize (worker, via server).** The executor of `m{n}` first durably
   awaits `m{n-1}`. If pending, it suspends — `task.suspend` with a callback
   on the predecessor — and the *server's* resume machinery wakes it when
   the predecessor settles. The serialization guarantee is exactly the
   protocol's callback ordering; there is no lock anywhere in the system.
4. **Hydrate.** The predecessor's value carries `{s: snapshot}`. Rejected or
   timed-out predecessor? Walk back to the newest resolved one (poison
   messages are skipped, deterministically, because the walk is over durable
   outcomes).
5. **Execute.** The handler runs against a draft of the snapshot. Its
   `ctx.run/rpc/sleep/detached` children journal under `m{n}.…` — the
   message's own computation tree. Crash → the task is redelivered and
   *this message* replays with dedup. **Replay bound = one message (W1).**
6. **Commit.** Reply promise settled (idempotently), then the message settles
   with `{s: newState, r, e?}` via `task.fulfill`. The settle is the atomic
   commit of state + result, and it is what releases message `n+1`.

**W2**: an idle object holds *no pending promise, no task, no worker memory* —
only settled records. "Passivation" is not an operation; it is the absence of
work. A million idle objects are a million cold rows, which is §7.3's
retention discussion, not a runtime problem.

**Reads**: latest resolved message's value, straight `promise.get` — stale by
at most the currently-executing message.

**Alarms**: a delayed self-message must not occupy a head slot early (it
would block successors), so `sendLater` creates a *detached alarm promise*
with `resonate:delay`; when it fires, its workflow appends normally.

Costs, honestly: the head probe (O(log) gets per append, contention retries
under fan-in — this is the price of no server-side append primitive); state
snapshot serialized into every message value (delta/interval-snapshot
variants exist but weren't needed to prove the model); per-message task
dispatch overhead (~1 suspend/resume cycle when the chain is busy).

Test evidence (`chain.test.ts`, `matrix.test.ts`): sequential + concurrent
serialization with exact per-message effect counts (6 messages → exactly 6
handler executions — the bounded-replay assertion), rollback-on-error,
tombstones, alarms, and the full recursion matrix including a
function→object→function→object nesting and send-based cycles.

### 5.2 Variant B — the generation loop (`loop.ts`) — the Temporal shape, for comparison

One long-running workflow per **generation**; the generation pre-creates a
bounded mailbox of N latent promises as its first N durable ops (so their ids
`g{i}.0 … g{i}.N-1` are computable by senders); senders deposit by **racing
to settle** a slot (settle-as-CAS); the loop races each slot against an idle
timer; on mailbox exhaustion it detach-spawns generation `i+1`
(continue-as-new, structural); on idle it **passivates** — closes remaining
slots, drains deposits that beat the close, and returns its state snapshot,
leaving the object fully passive until a sender re-activates it with a CAS
`promise.create` of the next generation.

It works (all tests pass: rolls, passivation, reactivation, concurrent
deposits), and it earns its keep in this document as the *measured cost* of
the entity-workflow shape:

* The passivation close-and-drain is precisely Temporal's documented
  signal-drain choreography, rediscovered from first principles — except here
  it is the runtime's code, not every user's.
* Two real defects found only by running it: (1) any durable op before the
  mailbox block shifts every slot id and orphans all deposits — positional id
  schemes are load-bearing and fragile; (2) race-loser idle timers hold the
  generation open (the engine's structured concurrency refuses to fulfill a
  pass with pending ops), so the loop must durably retire its own timers to
  roll promptly. Neither failure mode *exists* in variant A.
* Reads are stale up to a whole generation (state commits at roll/
  passivation), vs one message in A.
* Replay bound = one generation (N messages) — bounded, but a multiple of A's.

Its one structural advantage: a hot object processes N messages in one
resident pass — no per-message dispatch. That is a throughput optimization of
A, purchasable later (batch executor claiming a run of the chain), not a
reason to adopt the shape wholesale.

### 5.3 Variant C — the protocol extension (`serial.ts`) — recommended end-state

Everything userland-awkward in A is one server-side capability. Add a tag:

```
resonate:serial = <key>
```

with two rules, both trivially expressible in the abstract machine:

* **S1 — serialized dispatch.** Among tasks whose promises share a serial
  key, the server releases at most one for execution at a time, in promise
  **creation order** (the order the machine already linearizes). Others wait,
  undispatched. This is a *scheduling* restriction on the outbox — it touches
  no request handler semantics, and `timeout always wins` already guarantees
  a dead head cannot block the queue (its timeout settles it, releasing the
  next — the prototype's poison-walk handles the rejected-predecessor case).
* **S2 — chain stamp.** At create, the server stamps the promise with
  `resonate:serial-prev = <predecessor id>`, giving each invocation a durable
  pointer to the previous one — and thereby to the state snapshot in its
  value. (S2 is mechanical: the server already owns the linearization point.)

With S1+S2 the entire object machinery collapses into ordinary durable
function calls:

```ts
// function → object call: ctx.rpc plus one tag
ctx.rpc(handler, env, { tags: { "resonate:serial": "o/Account/alice" } })
// object → object one-way send: ctx.detached plus the same tag
ctx.detached(handler, env, { tags: { "resonate:serial": "o/Account/alice" } })
```

No probing, no CAS retry loops, no mailbox choreography; invocation ids are
opaque (a uuid, or the caller's deterministic child id — dedup and recovery
come from the existing engine); the executor hydrates by following
`serial-prev` and runs exactly variant A's steps 4–6. Replay bound: one
invocation. Idle cost: zero. The Restate virtual-object model, reconstructed
as **one tag on the existing task machinery**.

The prototype implements S1+S2 as a network middleware
(`SerialDispatchNetwork`) sitting exactly where the server extension would:
it stamps creates on the way in and gates `execute` delivery on the way out
(predecessor settled ⇒ release next), with a poll fallback for
timeout-settled heads. The runtime above it (`SerialObjects`) would not
change if the server took over. All six tests pass, including concurrent
invocations serializing in creation order with exact effect counts, and
one-way sends from handlers.

What C gives up without further extension: the anonymous-id scheme loses A's
free snapshot reads (nothing to probe), so `read()` degrades to a serialized
`$read` invocation. Restoring concurrent reads is the third, optional
extension below.

### 5.4 Variant D — optimistic state chain (`cas.ts`) — considered, rejected

The degenerate encoding: versioned state chain `v0, v1, …`, senders compute
`next = reducer(state, msg)` locally and commit by CAS-creating `v{n+1}`;
losers recompute. Two tests pass (including 8-way contention with exact
counts). Rejected as *the* primitive because the transition runs at the
sender: there is no home for durable side effects (they would execute before
the CAS decides whether the transition is real), every sender must ship the
code, and contention burns recompute. Retained in the tree because it is the
right tool for pure low-contention registers, and because its storage shape
is a strict subset of A's — promoting a CAS object to a chain object is an id
migration, not a rewrite.

### 5.5 Comparison

| | A chain | B loop | C serial (ext) | D cas |
|---|---|---|---|---|
| protocol change | none | none | S1+S2 | none |
| replay bound (W1) | 1 message | 1 generation | 1 invocation | none (no replay) |
| idle residency (W2) | zero | zero after passivation | zero | zero |
| serialization mechanism | awaited predecessor | resident loop | server dispatch | none (CAS) |
| sender cost | probe + CAS | probe + settle-race (+404 spin) | 1 create | read + CAS + recompute |
| read freshness | ≤ 1 message | ≤ 1 generation | serialized (or ext.) | exact |
| ordering | creation order (CAS-linearized) | deposit order per generation | creation order (server) | version order |
| durable effects in handler | yes | yes | yes | **no** |
| failure modes found in prototype | — | slot-id shift; timer-held generations | — | (by design) |
| lines of runtime mechanics | ~370 | ~430 | ~470 incl. emulated server | ~90 |

## 6. Recursive integration (R3)

Uniform across A/B/C because a handler *is* a workflow pass and an object
endpoint *is* a promise. All edges are prototyped in `matrix.test.ts` /
`chain.test.ts` / `serial.test.ts`:

| edge | mechanism | suspension semantics |
|---|---|---|
| function → function | `ctx.run` / `ctx.rpc` (existing SDK) | caller suspends on child promise |
| function → object | `objects.in(ctx).get(def, key).call/send/read` | `call`: caller suspends on reply promise; `send`: caller only awaits the durable enqueue |
| object → function | `octx.run` (local child) / `octx.rpc` (remote child) / `octx.detached` (fire-and-forget re-root) | journaled to the message; message suspends like any workflow |
| object → object | `octx.object(def, key).call/send` | `call` serializes behind the target's mailbox — the caller's message stays suspended meanwhile |
| object → self | `send` allowed (queues behind current message); `call` rejected eagerly (`SelfCallDeadlockError`) | |
| cycles A⇄B | `send` edges terminate (tested); `call` cycles deadlock as in Restate — detectable in principle by walking awaiter chains server-side (future work) | |

Two composition properties worth stating explicitly:

* **Lineage.** In A/C, a message/invocation is its own root (detached-style
  re-root): the object's chain is not part of any caller's computation tree,
  so callers complete independently of the object's future and vice versa —
  matching `detached`'s bounded-id discipline (the id of message n is
  `o/T/k/m{n}`, never a growing lineage path).
* **At-most-one execution, exactly-once effects.** The handler's own effects
  are journaled durable ops (exactly-once by dedup); the enqueue is
  exactly-once by CAS+adopt (A) or by the engine's deterministic child ids
  (C); the reply is at-least-once with first-writer-wins settle. The composed
  edge is therefore exactly-once end-to-end, modulo the documented
  adopt-window bound in A (a crashed sender racing >W concurrent appenders
  can double-append; W is configurable, and receiver-side ik dedup closes the
  gap entirely if a deployment needs it — or use C, which has no window).

## 7. Protocol & SDK deltas

### 7.1 Required for the baseline (variant A): none

That is the headline result of the prototyping: **durable objects with
bounded replay, zero idle residency, serialized execution, snapshot reads,
alarms, and full recursion run on the protocol as specified today.** Every
mechanism used — CAS create, CAS settle, callbacks, targeted dispatch,
delayed dispatch — is in `spec/01-protocol` already.

One SDK-level addition earns its keep immediately:

* **`ctx.attach(id)`** — durably await an existing promise by id. The
  prototypes encode it as `ctx.rpc` with an explicit id (create-dedups into
  attach); a first-class op removes the false create path and documents the
  intent. SDK change only, no protocol impact.

### 7.2 Proposed extension for the end-state (variant C): `resonate:serial`

S1 (serialized dispatch per key, creation order) + S2 (predecessor stamp), as
specified in §5.3. Formal-spec impact assessment:

* S1 constrains only the outbox/dispatch schedule — the class of behaviors it
  removes are interleavings, which `TheSquare` already treats as
  unobservable *per computation*; what S1 adds is a new *observable* — the
  cross-promise order — which needs its own small invariant:
  `SerialKeyMutualExclusion` (at most one task per serial key outside
  terminal states is ever dispatched) and `SerialKeyOrder` (dispatch order =
  creation order). Both are stateable in the abstract machine as properties
  of the rule schedule; `timeout always wins` composes cleanly because a
  timed-out head is terminal and releases the key.
* S2 is a deterministic function of the linearization the machine already
  performs at `promise.create`; it adds a stamped tag, no new transitions.

### 7.3 Adjacent, independently useful extensions

* **Retention.** Settled message/invocation records are the objects' only
  storage cost. A `resonate:retain` policy (keep last K per serial key /
  keep until age T) turns W1/W2's storage tail into a stated guarantee. The
  chain's correctness needs only the *latest resolved* record per object
  retained (hydration walks stop there), so K=1 suffices for liveness;
  larger K preserves audit history — exactly the Akka snapshot-vs-journal
  retention trade, made a server policy instead of user code.
* **Head query.** `promise.head(serialKey)` (or tag-search with
  `latest-resolved` semantics) restores variant A's concurrent snapshot
  reads under variant C's opaque ids, and eliminates A's probe entirely.
  Without it, A self-serves via the galloping probe; with it, `read()` is one
  round trip in all variants.
* Not proposed: server-side K/V. The snapshot-in-promise-value model already
  gives materialized state with the same durability, atomically committed
  with the invocation that produced it; a separate K/V would reintroduce the
  state/journal consistency problem Restate solves with co-location, without
  buying expressiveness.

### 7.4 Recommendation

1. **Ship variant A** as the SDK's object runtime now — zero protocol risk,
   full semantics, and its storage shape is forward-compatible with C (a
   chain *is* a serial key with deterministic ids).
2. **Specify and implement `resonate:serial` (S1+S2)** as the protocol-native
   path; migrate the runtime's sender side from probe+CAS to plain
   create-with-tag when available. The dispatch-gating middleware in the
   prototype is the reference semantics.
3. Adopt `ctx.attach` in both engines; take retention and head-query as
   independent server roadmap items.
4. Keep B and D in the tree as executable documentation of the rejected
   shapes (B additionally seeds the future batch-executor optimization for
   hot objects).

## 8. Open questions / future work

* **DST coverage.** The prototypes are tested against the deterministic
  local server model but not yet wired into `sim/` chaos schedules; the
  chain's crash-retry adopt window and the serial middleware's
  timeout-release path are the two places a DST run would earn its keep.
* **Generator-engine parity.** Prototypes target the async engine; the
  mapping is mechanical (`yield*` for awaits, LFI/RFI for run/rpc), and the
  object surface was kept engine-agnostic to allow it.
* **Hot objects.** A single serialized entity has an inherent throughput
  ceiling (all four reference systems share it). The known answers — batch
  claiming (B's pass model applied to A's chain), sharded sub-objects,
  shared read handlers — compose with this design; none require new protocol.
* **Reentrancy.** Orleans-style call-chain reentrancy (allow A→B→A when the
  inner call carries the outer's causality token) would lift the cycle
  deadlock; it needs a causality header on envelopes and a reentrant-dispatch
  rule in S1. Deliberately out of scope for v1 — `send` covers cycles.
* **Placement.** Cloudflare pins objects to a colo; Resonate objects have no
  affinity at all (any worker, every message). If locality ever matters
  (per-object caches), `resonate:target` unicast per key is the hook.
* **Formalization.** State `SerialKeyMutualExclusion` / `SerialKeyOrder` in
  the abstract machine and check them at small scope alongside the existing
  battery; model the chain encoding itself as a refinement (a chain object's
  observable behavior should be bisimilar to a serial-key object's).
