import «02-actions».«00-resume»

open ServerModel

def taskFulfill (req : TaskFulfillReq) (now : Nat) : M TaskFulfillRes := do
  match ← getTask req.id with
  | none =>
      return { status := 404 }
  | some t =>
  match ← getPromise t.id with
  | none =>
      return { status := 409 }
  | some p =>
      if t.state != .acquired then return { status := 409 }
      if p.state != .pending ∨ p.timeoutAt ≤ now then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      let listeners := p.listeners
      let callbacks := p.callbacks
      let p := { p with state := req.action.state, value := req.action.value, settledAt := some now, callbacks := [], listeners := [] }
      setPromise p
      delPromiseTimeout p.id
      setTask { t with state := .fulfilled, pid := none, ttl := none, resumes := [] }
      delTaskTimeout t.id
      -- settlement scrub: p can never be resumed again; drop its dead registrations
      modify fun s =>
        { s with promises := s.promises.map fun q =>
            if q.state == .pending then
              { q with callbacks := q.callbacks.filter (· != p.id) }
            else
              q }
      for address in listeners do
        setMessage address (.unblock p.toRecord)
      for awaiterId in callbacks do
        enqueueResume p.id awaiterId now
      return { status := 200, promise := some p.toRecord }
