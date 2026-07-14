import «01-objects».«state»

open ServerModel

def promiseRegisterCallback (req : PromiseRegisterCallbackReq) (now : Nat) : M PromiseRegisterCallbackRes := do
  -- A promise cannot await itself: the callback it registers could only be
  -- fired by its own settlement — a deadlock by construction. A malformed
  -- request, rejected with highest precedence, before existence is consulted.
  if req.awaited == req.awaiter then
    return { status := 400 }
  match ← getPromise req.awaited with
  | none =>
      return { status := 404 }
  | some pAwaited =>
  match ← getPromise req.awaiter with
  | none =>
      return { status := 422 }
  | some pAwaiter =>
      if !(pAwaiter.tags.has "resonate:target") then return { status := 422 }
      if pAwaited.state == .pending then
        if pAwaited.timeoutAt > now then
          if pAwaiter.state == .pending ∧ pAwaiter.timeoutAt > now then
            setPromise (pAwaited.addCallback req.awaiter)
          return { status := 200, promise := some pAwaited.toRecord }
        else
          let projected :=
            if pAwaited.isTimer then
              { pAwaited with state := .resolved, settledAt := some pAwaited.timeoutAt }
            else
              { pAwaited with state := .rejectedTimedout, settledAt := some pAwaited.timeoutAt }
          return { status := 200, promise := some projected.toRecord }
      else
        return { status := 200, promise := some pAwaited.toRecord }
