import «01-objects».«state»

open ServerModel

/-- The inter-object resume, with one deliberate strengthening over the
    go-actor oracle / TS SDK's LocalNetwork.Server:
    - version is bumped ONLY on acquire. A resume re-emits the CURRENT
      version: the execute is a wake-up hint, not a fresh fencing token.
    - TIMEOUT ALWAYS WINS: a logically timed-out awaiter (its own deadline
      REACHED, boundary included: `timeoutAt ≤ now`) is dead weight -- nothing
      fires, the timeout path owns it. The guard is DEADLINE-phrased (immutable
      data, never materialization state) so that an eager backend (which sweeps
      timeouts physically) and a lazy one (which projects on read) decide the
      resume identically; guarding one side only would make the execute an
      observable divergence. NOTE: the go-actor oracle and the TS SDK currently
      resume UNGUARDED -- adopting this guard makes them non-conforming until
      they add the same check (the both-expired corner).
    - the resumed task records its trigger (resumes := [awaitedId]);
      buffered resumes are deduplicated.
    - an absent/empty target sends nothing. -/
def enqueueResume (awaitedId awaiterId : String) (now : Nat) : M Unit := do
  let some t ← getTask awaiterId | pure ()
  let some p ← getPromise awaiterId | pure ()
  if p.timeoutAt ≤ now then
    pure ()
  else
    match t.state with
    | .suspended =>
        let retryTimeout := (← get).config.retryTimeout
        let t := { t with state := .pending, resumes := [awaitedId] }
        setTask t
        setTaskTimeout t.id 0 (now + retryTimeout)
        let target := (p.tags.get? "resonate:target").getD ""
        if target != "" then
          setMessage target (.execute t.id t.version)
    | .pending | .acquired | .halted =>
        if t.resumes.contains awaitedId then
          pure ()
        else
          setTask { t with resumes := t.resumes ++ [awaitedId] }
    | .fulfilled =>
        pure ()
