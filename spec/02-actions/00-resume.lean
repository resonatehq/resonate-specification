import «01-objects».«state»

open ServerModel

/-- Oracle-aligned (go-actor cascadeSettle, the port of the TS SDK's
    LocalNetwork.Server):
    - version is bumped ONLY on acquire. A resume re-emits the CURRENT
      version: the execute is a wake-up hint, not a fresh fencing token.
    - no awaiter-deadline guard: the cascade touches the awaiter only
      through its TASK state (an expired awaiter's own settlement fulfills
      the task).
    - the resumed task records its trigger (resumes := [awaitedId]);
      buffered resumes are deduplicated.
    - the state change does not require the awaiter promise; only the
      message does -- and an absent/empty target sends nothing. -/
def enqueueResume (awaitedId awaiterId : String) (now : Nat) : M Unit := do
  let some t ← getTask awaiterId | pure ()
  match t.state with
  | .suspended =>
      let retryTimeout := (← get).config.retryTimeout
      let t := { t with state := .pending, resumes := [awaitedId] }
      setTask t
      setTaskTimeout t.id 0 (now + retryTimeout)
      match ← getPromise awaiterId with
      | none => pure ()
      | some p =>
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
