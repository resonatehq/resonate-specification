import «01-objects».«state»
import «02-actions».«T-06-task.suspend»

open ServerModel

/-!
## suspend_atomic

The suspend operation is all-or-nothing: if *any* awaited promise is already
settled or timed out, the entire operation fails with 300 (Redirect) and the
task's `resumes` list is cleared.  Otherwise the task is moved to `suspended`.
-/

/-- A promise is "dead" for suspend purposes when it is already settled or
    its timeout has passed. -/
def promiseDead (pa : PromiseObject) (now : Nat) : Bool :=
  pa.state != .pending || pa.timeoutAt ≤ now

/-- Run `taskSuspend` and return the result alongside the final server state. -/
def taskSuspend' (req : TaskSuspendReq) (now : Nat) (s : ServerState) :
    Prod TaskSuspendRes ServerState :=
  taskSuspend req now s
