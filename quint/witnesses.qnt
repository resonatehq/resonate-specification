/// NOT VACUITY. An invariant that quantifies over an empty store holds, and
/// says nothing. Each of these is a state the machine had better be able to
/// reach; `quint run --witnesses` counts the behaviours that reach it, and a
/// zero is a handler that is never enabled.
module witnesses {
  import requests.* from "./requests"
  import abstractAction.* from "./abstractAction"

  val wAcquired  = state.stored().exists(o => o.task.state == TaskAcquired)
  val wSuspended = state.stored().exists(o => o.task.state == TaskSuspended)
  val wHalted    = state.stored().exists(o => o.task.state == TaskHalted)
  val wFulfilled = state.stored().exists(o => o.task.state == TaskFulfilled)
  val wCallback  = state.stored().exists(o => o.promise.callbacks != Set())
  val wListener  = state.stored().exists(o => o.promise.listeners != Set())
  val wResumes   = state.stored().exists(o => o.task.resumes != Set())
  val wTimedout  = state.stored().exists(o => o.promise.state == RejectedTimedout)
  val wTimerDone = state.stored().exists(o => o.promise.tags.timer and o.promise.state == Resolved)
  val wResolved  = state.stored().exists(o => o.promise.state == Resolved and not(o.promise.tags.timer))
  val wExecute   = outbox.exists(e => match e.message { | Execute(_) => true | Unblock(_) => false })
  val wUnblock   = outbox.exists(e => match e.message { | Execute(_) => false | Unblock(_) => true })
  val wVersion2  = state.stored().exists(o => o.task.version > 1)
  val wTicked    = now > 0
  val wTwoObjects = state.objects.keys().size() > 1
}
