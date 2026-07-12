import «01-objects».«state»

open ServerModel

/-- Resume the awaiter's task when a promise it awaits settles.
    - version is bumped ONLY on acquire. A resume re-emits the CURRENT
      version: the execute is a wake-up hint, not a fresh fencing token.
    - TIMEOUT ALWAYS WINS (protocol decision 2026-07-02, reaffirmed
      2026-07-12): a logically timed-out awaiter is dead weight -- the
      resume is discarded entirely; the timeout path owns its cleanup.
      Futile wakes can still occur by racing the deadline, but one is
      never sent KNOWINGLY. (This supersedes the earlier oracle-aligned
      no-guard behavior; go-actor cascadeSettle and the TS SDK's
      LocalNetwork.Server must adopt the guard.)
    - the resumed task records its trigger (resumes := [awaitedId]);
      buffered resumes are deduplicated.
    - an absent awaiter promise or task discards the resume; an absent or
      empty target sends nothing (the state change still applies). -/
def enqueueResume (awaitedId awaiterId : String) (now : Nat) : M Unit := do
  let some t ← getTask awaiterId | pure ()
  let some p ← getPromise awaiterId | pure ()
  if now >= p.timeoutAt then
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
