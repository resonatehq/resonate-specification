# Refinement: base machine ⊑ coalesced machine?

**Direction.** The base machine (`01-objects`, `02-actions`) is the concrete spec — rich in auxiliary state (timeout sets, deferred queue, config) and eager in its cascades. The coalesced machine (`abstract/`) is the abstract spec. The claim under investigation:

> every base behavior is a coalesced behavior — each base step corresponds, under a state abstraction, to a finite sequence of coalesced steps with equal responses.

**Verdict.** It holds *almost* everywhere, with a mapping that is simple and instructive — and it fails at exactly one observation point, for a reason that is fundamental to the no-projection design, not an artifact of either spec. Both the correspondence and the counterexample are executed and machine-checked (`by decide` on the actual handlers, in the style of the base spec's `04-guarantee`).

## The abstraction ([`01-abstraction.lean`](01-abstraction.lean))

`alpha : ServerModel.ServerState → AbstractModel.ServerState` is purely structural and **time-independent** — it does not project:

| Base component | Image under `alpha` |
|---|---|
| `deferred` entry `(awaited, awaiter)` | folded back into `promises[awaited].callbacks` — stage 1 of the base wake pipeline becomes indistinguishable from stage 0; the coalesced machine has one stage, *still on the promise* |
| `taskTimeouts` kind 1 (lease) | the task's `expiresAt` |
| `taskTimeouts` kind 0 (retry/delay) | the task's `retryAt` — the due instant is state; the cadence (`now + retryTimeout` re-arm) is R6's parameter |
| `promiseTimeouts`, `scheduleTimeouts` | dropped — pure mirrors of `timeoutAt` / `nextRunAt` |
| `config` | dropped from state — the retry constant lives in the instantiation of R6's re-arm parameter |
| everything else | verbatim |

List order in `callbacks`/`listeners` is not preserved (base handlers append; `alpha` folds the LIFO deferred back in) and not observable (no response exposes it; batch drains commute), so state comparison is up to order: `stateEq`.

**The simulation relation.** All timing lag lives in the relation, not the abstraction:

```
R(s, t)  ⇔   t reachable from alpha(s) by fact rules alone (R1/R2)   -- coalesced ran AHEAD, forced by touches
           ∧ alpha(s) reachable from t by drain rules alone (R3/R4/R6) -- coalesced lags BEHIND on messages/wakes
```

The two lags are the two halves of the design: materialization-on-touch commits facts the base machine only observes (ahead), and batch drains defer propagation the base machine performs inline (behind). Time advancing between base steps is simulated by fact-rule firings — no time-indexed abstraction function is needed.

## The correspondence ([`02-correspondence.lean`](02-correspondence.lean))

Every base step maps to a coalesced sequence. The table below is the full map; rows marked ⚡ are executed as scenarios.

| Base step | Coalesced sequence | Lag |
|---|---|---|
| `promiseGet` ⚡S3 | `promiseGet` | ahead by R1 on the touched promise |
| `promiseCreate` (live) | `promiseCreate` ; R6 | execute lag (none if delayed ⚡S7) |
| `promiseCreate` (expired at birth) | `promiseCreate` | exact |
| `promiseSettle` ⚡S1 | `promiseSettle` ; R2 ; R3(all) ; R4(all) ; R6 per woken awaiter | exact after the drains |
| `promiseRegisterCallback` / `Listener` | same handler | ahead by R1 |
| `taskGet` | `taskGet` | ahead by R1 ; R2 |
| `taskCreate` (new) | `taskCreate` | exact |
| `taskCreate` (existing) | `taskCreate` | **divergence D2** (base defect) |
| `taskAcquire`, `taskFence`, `taskHeartbeat`, `taskSuspend` | same handler | ahead by R1 ; R2 per touched object |
| `taskFulfill` | `taskFulfill` ; R2 ; R3 ; R4 ; R6 … | as `promiseSettle` |
| `taskRelease`, `taskContinue` | same handler ; R6 | execute lag |
| `taskHalt` | `taskHalt` | **divergence D1** (fundamental) |
| `schedule.*` | same handler | exact (no timer arming) |
| τ `onPromiseTimeout` ⚡S2 | R1 ; R2 ; R3(all) ; R4(all) ; R6 … | exact after the drains |
| τ `onTaskRetryTimeout` ⚡S7 | R6 | exact (timer re-arm dropped) |
| τ `onTaskLeaseTimeout` ⚡S4 | R5 ; R6 | exact |
| τ `onScheduleTimeout` | R7 | exact |
| τ `onResume` (per deferred entry) ⚡S6 | R4, batch of 1 | ahead by R1 ; R2 on an expired awaiter |

A full proof would quantify each row over base states satisfying the base machine's reachability invariants — chiefly: a deferred entry's awaited promise is settled; a settled promise's stored `callbacks`/`listeners` are empty (settlement moved them), so `alpha`'s fold is the only source of retained obligations; a kind-1 timer exists exactly for acquired tasks. The scenarios execute each row's characteristic case, per this repo's executable-spec discipline.

## Higher fidelity: concrete = abstract + scheduler ([`04-scheduler.lean`](04-scheduler.lean))

`alpha` drops the base machine's auxiliary state and lets the simulation relation absorb the slack existentially. The tighter reading: that state was never protocol state — it is the reification of a **scheduler** for the abstract machine's rules. A second extraction `sigma` reads every armed timer and every deferred entry as a *commitment* to fire a specific abstract rule:

| Base auxiliary state | Commitment |
|---|---|
| `promiseTimeouts` entry | fire R1 (and the eager R2/R3/R4 cascade) at `timeoutAt` |
| `taskTimeouts` kind 1 | fire R5 at the lease deadline |
| `taskTimeouts` kind 0 | fire R6 at the retry/delay instant |
| `scheduleTimeouts` entry | fire R7 at `nextRunAt` |
| `deferred` entry | fire R4, batch of one, due immediately |

Under the pair `(alpha, sigma)` the mapping is checked at two levels:

- **Discharge bookkeeping** — every base τ-step discharges a due commitment (its state effect: the abstract rule sequences of the table above) and re-commits per a fixed policy: a wake, a retry, a lease expiry each re-commit a `dispatch` at `now + retryTimeout`; a promise timeout swaps itself for one `resume` commitment per callback. Executed for the settle, timeout, lease, and retry pipelines.
- **Derivability** — every commitment class is a *function of the abstract image*: promise timeouts from external ∧ pending, lease expiries from acquired ∧ `expiresAt`, dispatches from pending ∧ `retryAt`, resumes from the callbacks `alpha` retains on settled promises, schedule fires from `nextRunAt`. `sigma` adds nothing to `alpha`: the mapping is **lossless** — the base machine's entire auxiliary state is redundant given the abstract state. The base machine stores it separately only because its rules cannot guard on object state the way the abstract rules do.

What remains base-only is not state but **policy** — the `now + retryTimeout` re-commitment constant, recovered by instantiating R6's `next` parameter. (One asymmetry, machine-checked: the base τ handlers are unguarded — an adversarial environment may fire them off-schedule — while R6 is self-guarded by `retryAt`; an off-schedule base retry is observationally a keyed-upsert stutter plus a moved due time, matched by the next on-schedule R6.)

This collapses the "behind" half of the simulation relation (pending drains are read off the state, no longer existential); the "ahead" half — facts forced by touches, and with it D1 below — is untouched.

## D1 — why full refinement is impossible ([`03-obstruction.lean`](03-obstruction.lean))

The base machine can **observe a logical fact without committing it**: `taskGet` on a task whose own promise is past its deadline serves the projected `.fulfilled` view and writes nothing. The stored task is still `.suspended`. `taskHalt` — which reads the task alone, deliberately: halt is an operation on the material coordination layer — then halts it: `200`.

A no-projection machine cannot produce this pair of observations. To serve `.fulfilled` at the read it must materialize; once materialized, the halt answers `409`:

```
base:       taskGet → fulfilled ; taskHalt → 200 (halted)
coalesced:  taskGet → fulfilled ; taskHalt → 409
```

The information "observed but not yet committed" **has no carrier in the coalesced state space** — it is erased at the touch. This is the exact price of removing projection, and `taskHalt` is the only place the price is visible: it is the sole base handler that branches on material task state without consulting the promise. The witness requires all three of: a projected read, a later material-state-branching handler, and a lazy timeout schedule between them.

The divergence is response-only and ephemeral — the machine-checked coda shows that once the base machine's own timeout τ fires, the states coincide again on the nose (`.halted` is overwritten to `.fulfilled`; the halt's `200` carried no durable meaning).

**What would restore refinement**, pick one:

1. **Base-side (recommended):** make `taskHalt` consult the task's promise and refuse once the own promise is logically settled — a one-guard change, after which every row of the table goes through.
2. **Observation-side:** weaken the observable to identify `200`/`409` on halt-of-a-dead-task, i.e. refinement up to a response equivalence.
3. **Coalesced-side: nothing.** The coalesced machine cannot be repaired without re-introducing a served-but-unstored view — the feature this spec exists to remove.

## D2 — the abstraction as a defect detector

On an existing targeted promise, base `taskCreate` reads promise and task raw: it serves an **unprojected promise record** (contradicting the base spec's own documented invariant that every promise-bearing response projects) and **re-acquires — arms a fresh lease on — a task whose promise is past its deadline**. The coalesced machine, forced by construction to materialize on touch, answers with the settled promise and fulfilled task.

This divergence is not fundamental; it marks a defect in the base spec, found by trying to refine it. Fix the base's exists-path to project and guard, and the row becomes exact.

## Build

```
cd spec && lake build
```

All correspondence scenarios and both divergence witnesses are checked at build time (`decide` / `native_decide` — the latter only where the delay tag's `String.toNat!` blocks kernel reduction).
