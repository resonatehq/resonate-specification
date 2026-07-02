import «02-actions».«00-resume»

open ServerModel

def promiseSettle (req : PromiseSettleReq) (now : Nat) : M PromiseSettleRes := do
  match ← getPromise req.id with
  | none =>
      return { status := 404 }
  | some p =>
      if p.state == .pending then
        if p.timeoutAt > now then
          let listeners := p.listeners
          let callbacks := p.callbacks
          let p := { p with state := req.state, value := req.value, settledAt := some now, callbacks := [], listeners := [] }
          setPromise p
          delPromiseTimeout p.id
          match ← getTask p.id with
          | some t =>
              setTask { t with state := .fulfilled, pid := none, ttl := none, resumes := [] }
              delTaskTimeout t.id
          | none =>
              pure ()
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
        else
          let projected :=
            if p.isTimer then
              { p with state := .resolved, settledAt := some p.timeoutAt }
            else
              { p with state := .rejectedTimedout, settledAt := some p.timeoutAt }
          return { status := 200, promise := some projected.toRecord }
      else
        return { status := 200, promise := some p.toRecord }
