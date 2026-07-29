import «abstract».«02-promises»

/-!  # The coalesced machine — internal rules

The machine's entire internal life is seven guarded rules, fired by the
environment in any order, at any pace, any number of times. Each rule
names its target (and, for the batch rules, a batch size) — the
parameters ARE the scheduler's nondeterminism, exactly as `now` is the
clock's. Every rule is total: if its guard does not hold it is a no-op,
so a stale or spurious firing is harmless.

  R1 `promiseTimeout`    if there is a promise past its deadline — fact P.
  R2 `taskFulfillment`   if there is a task whose promise is settled — fact T.
  R3 `notify`            if there is a settled promise with listeners:
                         drain a batch (1 to all), emitting `unblock`s.
  R4 `resume`            if there is a settled promise with awaiters:
                         drain a batch (1 to all), waking each.
  R5 `leaseExpiry`       if there is a task past its lease deadline.
  R6 `dispatch`          if there is a dispatchable pending task, emit
                         its `execute`.
  R7 `scheduleFire`      if there is a schedule past `nextRunAt`.

R1 and R2 are the facts themselves — firing one is the environment
touching an object, nothing more. They exist as rules so that facts
materialize eventually even on objects no request ever touches again.

R5 and R6 read RAW state, deliberately. Lease expiry is not a fact but a
scheduling choice — an expired lease is permission to redispatch, not
revocation: the slow worker's fencing token stays valid until someone
re-acquires, and expiry must not be forced by observation. Dispatch may
emit an `execute` for a task whose promise has meanwhile timed out; the
message is doomed (its acquire will 409) but the base machine emits it
too. Repeated firing of R6 is at-least-once delivery — the base
machine's retry timer without the timer.  -/

namespace AbstractModel
namespace Rules

open ServerModel (nextCron expand Schedule)

/-- R1: materialize fact P on a promise of the environment's choosing. -/
def promiseTimeout (id : String) (now : Nat) : M Unit := do
  let _ ← touchPromise id now

/-- R2: materialize fact T on a task of the environment's choosing. -/
def taskFulfillment (id : String) (now : Nat) : M Unit := do
  let _ ← touchTask id now

/-- R3: drain up to `batch` (at least 1 to fire meaningfully, up to all)
    listeners of a settled promise, emitting an `unblock` to each. -/
def notify (id : String) (batch : Nat) (now : Nat) : M Unit := do
  match ← touchPromise id now with
  | none => pure ()
  | some p =>
      if p.state == .pending then
        pure ()
      else
        let chosen := p.listeners.take batch
        setPromise { p with listeners := p.listeners.drop batch }
        for address in chosen do
          setMessage address (.unblock p.toRecord)

/-- Wake one awaiter of a settled promise. The touch materializes the
    awaiter's own deadline first, so TIMEOUT ALWAYS WINS falls out: an
    awaiter past its own deadline reads `.fulfilled` and is dropped —
    no explicit deadline guard, unlike the base machine's resume. -/
def resumeOne (awaited awaiter : String) (now : Nat) : M Unit := do
  match ← touchTask awaiter now with
  | none => pure ()
  | some (_, none) => pure ()
  | some (t, some _) =>
      match t.state with
      | .suspended =>
          setTask { t with state := .pending, resumes := [awaited] }
      | .pending | .acquired | .halted =>
          if !(t.resumes.contains awaited) then
            setTask { t with resumes := t.resumes ++ [awaited] }
      | .fulfilled =>
          pure ()

/-- R4: drain up to `batch` awaiters of a settled promise. A woken task
    is `.pending`; its `execute` is R6's job. -/
def resume (id : String) (batch : Nat) (now : Nat) : M Unit := do
  match ← touchPromise id now with
  | none => pure ()
  | some p =>
      if p.state == .pending then
        pure ()
      else
        let chosen := p.callbacks.take batch
        setPromise { p with callbacks := p.callbacks.drop batch }
        for awaiterId in chosen do
          resumeOne p.id awaiterId now

/-- R5: an acquired task past its lease deadline returns to `.pending`.
    Raw read — expiry is a choice, not a fact (see the header). -/
def leaseExpiry (id : String) (now : Nat) : M Unit := do
  match ← getTask id with
  | none => pure ()
  | some t =>
      match t.expiresAt with
      | none => pure ()
      | some deadline =>
          if t.state == .acquired ∧ deadline ≤ now then
            setTask { t with state := .pending, pid := none, ttl := none,
                             expiresAt := none }

/-- R6: emit the `execute` for a pending task whose `resonate:delay`
    (if any) has passed. Raw read; repeatable — the outbox's keyed
    upsert makes re-emission idempotent. -/
def dispatch (id : String) (now : Nat) : M Unit := do
  match ← getTask id with
  | none => pure ()
  | some t =>
      if t.state != .pending then
        return ()
      match ← getPromise t.id with
      | none => pure ()
      | some p =>
          let due :=
            match p.tags.get? "resonate:delay" with
            | some d => decide (d.toNat! ≤ now)
            | none => true
          if due then
            setMessage ((p.tags.get? "resonate:target").getD "")
              (.execute t.id t.version)

/-- Create every occurrence due at or before `now`, advancing the
    schedule past them. -/
partial def catchUp (now : Nat) (s : Schedule) : M Schedule := do
  if s.nextRunAt ≤ now then
    let cronTime := s.nextRunAt
    let promiseId := expand s.promiseId s.id cronTime
    let _ ← promiseCreate
      { id := promiseId, timeoutAt := cronTime + s.promiseTimeout,
        param := s.promiseParam, tags := s.promiseTags } cronTime
    catchUp now { s with lastRunAt := some cronTime,
                         nextRunAt := nextCron s.cron cronTime }
  else
    return s

/-- R7: fire a schedule past `nextRunAt` (with catch-up). -/
def scheduleFire (id : String) (now : Nat) : M Unit := do
  match ← getSchedule id with
  | none => pure ()
  | some s0 =>
      let s ← catchUp now s0
      setSchedule s

end Rules
end AbstractModel
