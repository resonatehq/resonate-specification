import «01-objects».«state»

open ServerModel

def taskContinue (req : TaskContinueReq) (now : Nat) : M TaskContinueRes := do
  let retryTimeout := (← get).config.retryTimeout
  match ← getTask req.id with
  | none =>
      return { status := 404 }
  | some t =>
      if t.state != .halted then return { status := 409 }
      match ← getPromise t.id with
      | none =>
          return { status := 404 }
      | some p =>
          -- TIMEOUT ALWAYS WINS: continuing a task whose promise is logically
          -- expired is futile; reject 409, as release/fulfill/suspend do.
          if p.state != .pending || p.timeoutAt ≤ now then return { status := 409 }
          let t := { t with state := .pending }
          setTask t
          setTaskTimeout t.id 0 (now + retryTimeout)
          setMessage ((p.tags.get? "resonate:target").getD "") (.execute t.id t.version)
          return { status := 200 }
