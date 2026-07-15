import «01-objects».«state»

open ServerModel

def taskSuspend (req : TaskSuspendReq) (now : Nat) : M TaskSuspendRes := do
  -- Request validation, highest precedence — everything rejectable by
  -- inspecting the request alone is 400, before existence, state, or
  -- version are consulted:
  -- suspending on nothing is not a suspension;
  if req.actions.isEmpty then
    return { status := 400 }
  -- a task awaiting its own promise is a self-deadlock by construction (the
  -- callback it registers could only be fired by its own completion);
  if req.actions.any (·.awaited == req.id) then
    return { status := 400 }
  -- and the same awaited id twice in one payload is malformed. Re-registration
  -- ACROSS requests stays idempotent via addCallback: a task woken by one
  -- awaited promise legitimately re-suspends on the others.
  let awaitedIds := req.actions.map (·.awaited)
  if awaitedIds.eraseDups.length != awaitedIds.length then
    return { status := 400 }
  match ← getTask req.id with
  | none =>
      return { status := 404 }
  | some t =>
  match ← getPromise t.id with
  | none =>
      return { status := 409 }
  | some tp =>
      if t.state != .acquired then return { status := 409 }
      if tp.state != .pending ∨ tp.timeoutAt ≤ now then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      let mut settled := false
      for action in req.actions do
        match ← getPromise action.awaited with
        | none =>
            return { status := 422 }
        | some pa =>
            if pa.state != .pending ∨ pa.timeoutAt ≤ now then
              settled := true
      if settled then
        setTask { t with resumes := [] }
        return { status := 300 }
      else
        for action in req.actions do
          match ← getPromise action.awaited with
          | some pa =>
              setPromise (pa.addCallback req.id)
          | none =>
              pure ()
        setTask { t with state := .suspended, pid := none, ttl := none, resumes := [] }
        delTaskTimeout t.id
        return { status := 200 }
