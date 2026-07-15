import «01-objects».«state»

open ServerModel

/-- Discharge one deferred resume against its awaiter. A drain entry point,
    not a dependency: nothing imports this module. `now` is the drain's
    clock, so the deadline guard re-checks at discharge time.
    - TIMEOUT ALWAYS WINS: a logically timed-out awaiter is dead weight --
      the resume is discarded (`expired`); the timeout path owns its cleanup.
    - version is bumped ONLY on acquire: the execute emitted on wake is a
      wake-up hint carrying the CURRENT version, not a fresh fencing token.
    - idempotent per (awaited, awaiter): a second discharge lands in
      `duplicate` or `fulfilled`, so a refinement may drain at-least-once. -/
def onResume (req : ResumeReq) (now : Nat) : M ResumeRes := do
  let some t ← getTask req.awaiter    | return { outcome := .absent }
  let some p ← getPromise req.awaiter | return { outcome := .absent }
  if now >= p.timeoutAt then
    return { outcome := .expired }
  match t.state with
  | .suspended =>
      let retryTimeout := (← get).config.retryTimeout
      let t := { t with state := .pending, resumes := [req.awaited] }
      setTask t
      setTaskTimeout t.id 0 (now + retryTimeout)
      let target := (p.tags.get? "resonate:target").getD ""
      if target != "" then
        setMessage target (.execute t.id t.version)
      return { outcome := .resumed }
  | .pending | .acquired | .halted =>
      if t.resumes.contains req.awaited then
        return { outcome := .duplicate }
      else
        setTask { t with resumes := t.resumes ++ [req.awaited] }
        return { outcome := .buffered }
  | .fulfilled =>
      return { outcome := .fulfilled }

/-- Discharge every deferred resume. Depth stays 1 -- `onResume` never
    defers -- so one pass over a snapshot drains completely: a fold, no
    fixpoint, no termination proof. -/
def drain (now : Nat) : M Unit := do
  for d in (← get).deferred do
    undefer d
    let _ ← onResume d now

/-- Eager drain: run a handler, then discharge everything it deferred.
    Under this policy the machine's observable behaviour coincides with
    the old synchronous cascade -- the conformance oracle fixes eager;
    the spec also admits lazier drains. -/
def step {α} (act : M α) (now : Nat) : M α := do
  let res ← act
  drain now
  return res
