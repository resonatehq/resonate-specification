import «02-abstract».«external»

/-!  # Internal steps — what the server does on its own initiative

Six steps a background job may fire: the promise timeout, the callback
drain, the listener drain, the lease timeout, the retry dispatch, and
the schedule.

The callback drain now delivers a resume to two kinds of awaiter: a
task, which it wakes, and a combinator, which it asks to decide again.
Combinators added no step of their own — a combinator settles on the
drain that was already there, which is why the alphabet, the enabling
rule and the trace format did not have to grow.

They take the FORCED reads — `touchObject` where the step persists what
it projects, `viewObject` where it only needs to look. Neither is
parametric: internal steps materialise under both readings of the
machine, and `Env.mat` does not reach here. -/

namespace AbstractModel
namespace Internal


open ServerModel (Ident nextCron occurrences expand Schedule Combinator
                  PromiseTimeoutReq PromiseRegisterCallbackReq PromiseRegisterListenerReq
                  TaskLeaseTimeoutReq TaskRetryTimeoutReq ScheduleTimeoutReq)

def processPromiseTimeout (req : PromiseTimeoutReq) (now : Nat) : H Unit := do
  let _ ← touchObject req.id now

/-- Wake the worker. The task path of a resume, unchanged: a suspended
    task re-pends carrying the rung that woke it, a task that is already
    running records the rung and keeps running, a fulfilled one has
    nothing left to be told. -/
def resumeTask (o : Object) (t : TaskObject) (awaited : Ident) (now : Nat) : H Unit :=
  match t.state with
  | .suspended =>
      setTask o.id { t with state := .pending, resumes := [awaited],
                            retryTimeoutAt := some now }
  | .pending | .acquired | .halted =>
      if !(t.resumes.contains awaited) then
        setTask o.id { t with resumes := t.resumes ++ [awaited] }
      else
        pure ()
  | .fulfilled =>
      pure ()

/-- Re-ask the rule. The combinator path of a resume.

    The verdict is recomputed from the store rather than accumulated
    across resumes, so nothing about a combinator is remembered between
    drains: no counter, no set of children seen, no field on the row
    that a crash could lose or an implementation could get out of step.
    A resume is a TRIGGER — it says the answer may have changed — and
    `settledChildren` is what supplies the answer.

    That is also what makes the drain's schedule invisible in the
    result. `awaited` is not read: whichever child's callback fires
    first, the rule sees the same settled set and returns the same
    verdict. Fire them in any order, or fire one twice, and the promise
    settles the same way — the second time absorbing, because the guard
    below is the same `pending` test every settle door makes.

    `touchObject` inside `settledChildren`, not `readObject`: this is an
    internal step and internal steps materialise under both readings of
    the machine. -/
def resumeCombinator (o : Object) (c : ServerModel.Combinator) (now : Nat) : H Unit := do
  if o.promise.state != .pending then
    pure ()
  else
    let settled ← withMat true (settledChildren now o.promise.children)
    match c.verdict o.promise.children settled with
    | none         => pure ()
    | some (st, v) =>
        setSettled o { o.promise with state := st, value := v, settledAt := some now }

/-- One resume, delivered. Two kinds of awaiter can take one, and the
    read in front declines every other row. -/
def resumeOne (awaited awaiter : Ident) (now : Nat) : H Unit := do
  match ← touchResumeObject awaiter now with
  | none => pure ()
  | some o =>
  match o.promise.tags.combinator, o.task with
  | some c, _    => resumeCombinator o c now
  | none, some t => resumeTask o t awaited now
  | none, none   => pure ()

def processCallback (req : PromiseRegisterCallbackReq) (now : Nat) : H Unit := do
  match ← touchObject req.awaited now with
  | none => pure ()
  | some o =>
      if o.promise.state == .pending then
        pure ()
      else if o.promise.callbacks.contains req.awaiter then
        setPromise o.id { o.promise with
                          callbacks := o.promise.callbacks.filter (· != req.awaiter) }
        resumeOne o.id req.awaiter now

def processListener (req : PromiseRegisterListenerReq) (now : Nat) : H Unit := do
  match ← touchObject req.awaited now with
  | none => pure ()
  | some o =>
      if o.promise.state == .pending then
        pure ()
      else if o.promise.listeners.contains req.address then
        setPromise o.id { o.promise with
                          listeners := o.promise.listeners.filter (· != req.address) }
        setMessage req.address (.unblock (o.promise.toRecord o.id))

def processLeaseTimeout (req : TaskLeaseTimeoutReq) (now : Nat) : H Unit := do
  match ← viewTaskObject req.id now with
  | none => pure ()
  | some o =>
  match o.task with
  | none => pure ()
  | some t =>
      match t.leaseTimeoutAt with
      | none => pure ()
      | some deadline =>
          if t.state == .acquired ∧ deadline ≤ now then
            if o.promise.state == .pending then
              setTask o.id { t with state := .pending, pid := none, ttl := none,
                                    leaseTimeoutAt := none, retryTimeoutAt := some now }

/-- Redispatch a pending task whose dispatch clock is due.

    The next instant is COMPUTED, from the server's dial and the
    clock — it is not supplied by whoever fires the step. Every other
    arming site (`createPromise`, `taskRelease`, `taskContinue`,
    `resumeOne`, `processLeaseTimeout`) already computed it; this was
    the one exception, and the exception was the only place the
    environment could write a value into the store. It could write a
    past one, leaving the step enabled at the instant it fired.

    The interval is `config.retryTimeout`, read from the environment.
    It is the SERVER's dial — how long to wait before re-offering a task
    nobody has claimed — and it is present for every task, including one
    that has never been acquired, which is exactly where retry matters
    and where the task carries nothing of its own to read.

    It is deliberately not `TaskObject.ttl`. That is the WORKER's
    number, how long a holder asked to keep its lease; using it here
    would re-offer a dead worker's task on the dead worker's schedule,
    would be missing on the newborn path, and — since `TaskRecord`
    reports `ttl` — would be observable. A transcribed production trace
    refuses it: `valid/lean/real.lean` shows `ttl := none` on a task
    acquired with 60000, suspended and resumed. -/
def processRetryTimeout (req : TaskRetryTimeoutReq) (now : Nat) : H Unit := do
  match ← viewTaskObject req.id now with
  | none => pure ()
  | some o =>
  match o.task with
  | none => pure ()
  | some t =>
      match t.retryTimeoutAt with
      | none => pure ()
      | some due =>
          if t.state == .pending ∧ due ≤ now then
            if o.promise.state == .pending then
              setTask o.id { t with
                             retryTimeoutAt := some (now + (← ask).config.retryTimeout) }
              setMessage ((o.promise.tags.get? "resonate:target").getD "")
                (.execute o.id t.version)

def fireOccurrence (s : Schedule) (t : Nat) : H Unit :=
  createIfAbsent
    { id := expand s.promiseId s.id t, timeoutAt := t + s.promiseTimeout,
      param := s.promiseParam, tags := s.promiseTags } t

def fireAll (s : Schedule) : List Nat → H Unit
  | [] => pure ()
  | t :: ts => do
      fireOccurrence s t
      fireAll s ts

def processSchedule (req : ScheduleTimeoutReq) (now : Nat) : H Unit := do
  match ← getSchedule req.schedule with
  | none => pure ()
  | some s =>
      let ts := (occurrences s.cron s.nextRunAt now).filter (· ≤ now)
      fireAll s ts
      match ts.getLast? with
      | some last =>
          setSchedule { s with lastRunAt := some last,
                               nextRunAt := nextCron s.cron last }
      | none => pure ()

end Internal
end AbstractModel
