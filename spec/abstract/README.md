# The Coalesced Machine

A second, more abstract specification of the Resonate protocol. Same wire types, same request/response behavior — a different machine, defined by three removals:

1. **No timeout components.** The base machine mirrors every deadline into armed-timeout sets (`promiseTimeouts`, `taskTimeouts`, `scheduleTimeouts`). Here a deadline lives only on the object that owns it — `timeoutAt` on the promise, `expiresAt` on the task, `nextRunAt` on the schedule — and every internal transition is a guarded rule of the form *"if there is a promise past its deadline …"*, *"if there is a task past its lease …"*.

2. **No deferred set.** The base machine moves a settled promise's callbacks into a `deferred` queue and drains it, and emits its listener notifications inline. Here settlement writes the promise's state and nothing else: **awaiters and listeners stay on the promise**, and batch rules drain them — one to all at a time, at the environment's pace.

3. **No projection.** The base machine serves a logical view of a timed-out promise without persisting it. Here there is no logical view: **every time a handler touches an object, it materializes** what is forced at that instant, then reads the stored state. Stored state is the only state.

## State

[`01-state.lean`](01-state.lean) — four components, no config:

| Component | Content |
|---|---|
| promises | `callbacks` and `listeners` survive settlement, pending drain |
| tasks | carry `expiresAt` (absolute lease deadline) and `retryAt` (next dispatch due) |
| schedules | `nextRunAt` is the alarm |
| outbox | keyed upsert, as in the base machine |

## Facts and choices

The machine's dynamics rest on one distinction:

- A **fact** is a monotone consequence of the state, with no freedom in it:
  - **fact P** — a pending promise past `timeoutAt` is settled (`resolved` for timers, `rejectedTimedout` otherwise), stamped at the deadline;
  - **fact T** — the task of a settled promise is fulfilled.

  Facts are materialized *on touch*: `touchPromise` applies P to every promise a handler reads; `touchTask` applies P then T to every task read *together with its promise*. A handler that reads a task alone (`taskHalt`, deliberately) sees raw state — fact T is a joint fact and cannot be derived from the task alone.

- A **choice** is scheduling: waking awaiters, notifying listeners, expiring a lease, dispatching an execute, firing a schedule. Choices are never forced by observation — they are the internal rules, fired by the environment in any order, at any pace. An expired lease in particular is *permission to redispatch, not revocation*: the slow worker's fencing token stays valid until someone re-acquires, which is why lease expiry must not happen on touch.

A deadline can be *data for a choice* without making the choice a fact: `expiresAt` and `retryAt` guard R5 and R6 — they say when a firing becomes *legal*, not that anything has happened — and are therefore never materialized on touch.

Retention is what makes materialization-on-touch sound: flipping a promise's state on a read commits no notification atomically, because the obligations remain recorded on the object and the batch rules discharge them later.

## Handlers

[`02-promises.lean`](02-promises.lean) · [`03-tasks.lean`](03-tasks.lean) · [`04-schedules.lean`](04-schedules.lean)

Handlers write objects and return responses — they emit no messages and record no auxiliary state. Consequences of the discipline:

- `promiseCreate` of a targeted promise creates the task and stops; the dispatch rule emits the `execute`. The `resonate:delay` tag is consumed at creation — it seeds the task's `retryAt` — so the base machine's create-side delay machinery collapses to one field initialization.
- `promiseSettle` and `taskFulfill` write **the promise only**. Fact T fulfills the task on the next touch (or via R2); the batch rules notify and resume.
- Compound liveness guards collapse: the base machine's `p.state != .pending ∨ p.timeoutAt ≤ now` is post-touch just `p.state != .pending`, and TIMEOUT ALWAYS WINS is automatic — touching a task whose promise is past its deadline fulfills the task before any guard looks at it.

## Rules

[`05-rules.lean`](05-rules.lean) — the machine's entire internal life, seven guarded rules. Each is total (a no-guard firing is a no-op), so stale or spurious firings are harmless; rule parameters (target id, batch size) are the scheduler's nondeterminism, exactly as `now` is the clock's.

| Rule | Guard → effect |
|---|---|
| R1 `promiseTimeout` | a promise past its deadline → fact P |
| R2 `taskFulfillment` | a task of a settled promise → fact T |
| R3 `notify` | a settled promise with listeners → drain a batch (1..all), emitting `unblock`s |
| R4 `resume` | a settled promise with awaiters → drain a batch (1..all), waking each through the touch |
| R5 `leaseExpiry` | an acquired task past `expiresAt` → back to pending |
| R6 `dispatch` | a pending task past `retryAt` → emit its `execute`, re-arm `retryAt` at a chosen instant (the rule's parameter — the due time is state, the cadence is the scheduler's; repeated firing is at-least-once delivery, idempotent via the keyed upsert) |
| R7 `scheduleFire` | a schedule past `nextRunAt` → create the due occurrences, advance |

R1 and R2 are the facts themselves — firing one is the environment touching an object — and exist as rules so facts materialize eventually even on objects no request ever touches again.

## Refinement

Whether the base machine refines this one — and the precise, machine-checked point where it does not — is worked out in [`../refinement`](../refinement/README.md).
