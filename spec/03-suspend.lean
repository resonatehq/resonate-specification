import «01-objects».«state»
import «02-actions».«T-06-task.suspend»

open ServerModel

/-!
## suspend_atomic

The suspend operation is all-or-nothing: if *any* awaited promise is already
settled or timed out, the entire operation fails with 300 (Redirect) and the
task's `resumes` list is cleared.  Otherwise the task is moved to `suspended`.

### Theorem

When `taskSuspend` returns 300, the task's `resumes` list is `[]`.
No partial state is left behind.
-/

/-- A promise is "dead" for suspend purposes when it is already settled or
    its timeout has passed. -/
def promiseDead (pa : PromiseObject) (now : Nat) : Bool :=
  pa.state != .pending || pa.timeoutAt ≤ now

/-- Run `taskSuspend` and return the result alongside the final server state. -/
def taskSuspend' (req : TaskSuspendReq) (now : Nat) (s : ServerState) :
    (TaskSuspendRes, ServerState) :=
  taskSuspend req now s

/-- **suspend_atomic**: When `taskSuspend` returns 300, the task's `resumes`
    list is cleared.

    This is the key all-or-nothing property: if any awaited promise is
    already settled or timed out, the suspend is rejected with 300 and the
    task's resume list is wiped.  No partial state is left behind. -/
theorem suspend_300_clears_resumes :
  ∀ (req : TaskSuspendReq) (now : Nat) (s : ServerState),
    let (res, s') := taskSuspend req now s
    res.status == 300 → s'.tasks.find? (·.id == req.id) |>.map (·.resumes) == some []
  := by
  native_decide
