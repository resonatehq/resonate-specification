import «01-objects».«state»

open ServerModel

/-- - TIMEOUT ALWAYS WINS: a logically timed-out awaiter -- deadline
      REACHED (p.timeoutAt <= now), boundary included -- is dead weight;
      nothing fires, the timeout path owns it. The guard is
      DEADLINE-phrased (immutable data, never materialization state), so
      eager and lazy materializations of the same timeline decide
      identically. The awaiter promise is therefore required (its deadline
      must be read); an awaiter task without a promise is unreachable
      (TaskHasPromise).
    - version is bumped ONLY on acquire. A resume re-emits the CURRENT
      version: the execute is a wake-up hint, not a fresh fencing token.
    - the resumed task records its trigger (resumes := [awaitedId]);
      buffered resumes are deduplicated.
    - an absent/empty target sends nothing. -/
def enqueueResume (awaitedId awaiterId : String) (now : Nat) : M Unit := do
  let some p ← getPromise awaiterId | pure ()
  let some t ← getTask awaiterId | pure ()
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
