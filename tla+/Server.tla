------------------------------ MODULE Server -------------------------------
(* TLA+ port of the Lean server specification (spec/).                      *)
(*                                                                          *)
(* Lean's `M := StateM ServerState` becomes the standard TLA+ shape: the    *)
(* ServerState fields are VARIABLES and every handler is an atomic action   *)
(* that updates each variable at most once.                                 *)
(*                                                                          *)
(* THE ORDER QUOTIENT. Lean renders the collections as lists, but no read   *)
(* ever observes their order: promises/tasks are accessed by id (find-by-   *)
(* id, replace-by-id), the timeout lists by their key, the outbox by its    *)
(* message key, and callbacks/listeners/resumes only by membership. That    *)
(* order is accidental state, so this port collapses it into the simplest   *)
(* representation in which it is not expressible:                           *)
(*   - promises, tasks           : id-keyed maps                            *)
(*   - promiseTimeouts           : map  id -> deadline                      *)
(*   - taskTimeouts              : map  <<id, kind>> -> deadline            *)
(*   - outbox                    : map  key -> entry                        *)
(*   - callbacks/listeners/      : sets                                     *)
(*     resumes                                                              *)
(* Tags REMAIN a sequence: their order is observable (TagsGet returns the   *)
(* first match under duplicate keys). The outbox key is structured          *)
(* (<<taskId>> / <<promiseId, address>>); Lean renders it as a string --    *)
(* both encodings are injective, so the quotient is unaffected.             *)
(* (The Dafny abstract twin of this spec makes the same choices:            *)
(* callbacks/listeners as sets, the outbox as a keyed map.)                 *)
(*                                                                          *)
(* Schedules are ignored in this port.                                      *)
EXTENDS Naturals, Sequences, FiniteSets

-----------------------------------------------------------------------------
(* 01-objects/types.lean                                                    *)
(*                                                                          *)
(* TLA+ is untyped, so the Lean structures are represented as records with  *)
(* the same field names. `Option a` is represented by the value itself or   *)
(* NULL. `Tags` is a sequence of <<key, value>> pairs. Requests and         *)
(* responses are records; where Lean relies on a field default, the TLA+    *)
(* record literal spells the default out.                                   *)
(*                                                                          *)
(*   Value                      == [headers, data]                          *)
(*   PromiseRecord              == [id, state, param, value, tags,          *)
(*                                  timeoutAt, createdAt, settledAt]        *)
(*   TaskRecord                 == [id, state, version, resumes, ttl, pid]  *)
(*                                                                          *)
(*   PromiseGetReq              == [id]                                     *)
(*   PromiseGetRes              == [status, promise]                        *)
(*   PromiseCreateReq           == [id, timeoutAt, param, tags]             *)
(*   PromiseCreateRes           == [status, promise]                        *)
(*   PromiseSettleReq           == [id, state, value]                       *)
(*   PromiseSettleRes           == [status, promise]                        *)
(*   PromiseRegisterCallbackReq == [awaited, awaiter]                       *)
(*   PromiseRegisterCallbackRes == [status, promise]                        *)
(*   PromiseRegisterListenerReq == [awaited, address]                       *)
(*   PromiseRegisterListenerRes == [status, promise]                        *)
(*   PromiseSearchReq           == [state, tags, limit, cursor]             *)
(*   PromiseSearchRes           == [status, promises, cursor]               *)
(*                                                                          *)
(*   TaskGetReq                 == [id]                                     *)
(*   TaskGetRes                 == [status, task]                           *)
(*   TaskCreateReq              == [pid, ttl, action]                       *)
(*   TaskCreateRes              == [status, task, promise, preload]         *)
(*   TaskAcquireReq             == [id, version, pid, ttl]                  *)
(*   TaskAcquireRes             == [status, task, promise, preload]         *)
(*   TaskFenceAction            == [type: "create", req]                    *)
(*                               | [type: "settle", req]                    *)
(*   TaskFenceInnerRes          == [type: "create", res]                    *)
(*                               | [type: "settle", res]                    *)
(*   TaskFenceReq               == [id, version, action]                    *)
(*   TaskFenceRes               == [status, action, preload]                *)
(*   TaskRef                    == [id, version]                            *)
(*   TaskHeartbeatReq           == [pid, tasks]                             *)
(*   TaskHeartbeatRes           == [status]                                 *)
(*   TaskSuspendReq             == [id, version, actions]                   *)
(*   TaskSuspendRes             == [status, preload]                        *)
(*   TaskFulfillReq             == [id, version, action]                    *)
(*   TaskFulfillRes             == [status, promise]                        *)
(*   TaskReleaseReq             == [id, version]                            *)
(*   TaskReleaseRes             == [status]                                 *)
(*   TaskHaltReq                == [id]                                     *)
(*   TaskHaltRes                == [status]                                 *)
(*   TaskContinueReq            == [id]                                     *)
(*   TaskContinueRes            == [status]                                 *)
(*   TaskSearchReq              == [state, limit, cursor]                   *)
(*   TaskSearchRes              == [status, tasks, cursor]                  *)

CONSTANT NULL  \* Lean: Option.none

PromiseState == {"pending", "resolved", "rejected",
                 "rejected_canceled", "rejected_timedout"}

TaskState == {"pending", "acquired", "suspended", "halted", "fulfilled"}

-----------------------------------------------------------------------------
(* 01-objects/state.lean                                                    *)
(*                                                                          *)
(*   PromiseObject == PromiseRecord + callbacks + listeners (sets)          *)
(*   TaskObject    == [id, state, version, ttl, pid, resumes (set)]         *)
(*   Message       == [type: "execute", taskId, version]                    *)
(*                  | [type: "unblock", promise]                            *)
(*   OutboxEntry   == [address, message]                                    *)
(*                                                                          *)
(* Lean's ServerState fields are the variables below. The get/set/del      *)
(* helpers operate on the individual collections: reads take the variable, *)
(* writes compute the collection's new value for one primed assignment.    *)

CONSTANT RetryTimeout  \* Lean: ServerConfig.retryTimeout := 5000

VARIABLES promises, tasks, promiseTimeouts, taskTimeouts, outbox

serverVars == <<promises, tasks, promiseTimeouts, taskTimeouts, outbox>>

VARIABLES now,  \* the clock; handlers read it, only TickAction advances it
          res   \* the response of the last handler call

vars == <<promises, tasks, promiseTimeouts, taskTimeouts, outbox, now, res>>

config == [retryTimeout |-> RetryTimeout]

TagsGet(t, k) ==
  LET matches == {i \in 1..Len(t) : t[i][1] = k}
  IN IF matches = {} THEN NULL
     ELSE t[CHOOSE i \in matches : \A j \in matches : i <= j][2]

TagsHas(t, k) == TagsGet(t, k) # NULL

TagsIsTimer(t) == TagsGet(t, "resonate:timer") = "true"

PromiseToRecord(p) ==
  [id        |-> p.id,
   state     |-> p.state,
   param     |-> p.param,
   value     |-> p.value,
   tags      |-> p.tags,
   timeoutAt |-> p.timeoutAt,
   createdAt |-> p.createdAt,
   settledAt |-> p.settledAt]

PromiseIsTimer(p) == TagsIsTimer(p.tags)

PromiseExternal(p) == TagsHas(p.tags, "resonate:target") \/ PromiseIsTimer(p)

PromiseAddCallback(p, awaiterId) ==
  [p EXCEPT !.callbacks = @ \cup {awaiterId}]

PromiseAddListener(p, address) ==
  [p EXCEPT !.listeners = @ \cup {address}]

TaskToRecord(t) ==
  [id      |-> t.id,
   state   |-> t.state,
   version |-> t.version,
   resumes |-> Cardinality(t.resumes),
   ttl     |-> t.ttl,
   pid     |-> t.pid]

OutboxKey(e) ==
  IF e.message.type = "execute"
  THEN <<e.message.taskId>>
  ELSE <<e.message.promise.id, e.address>>

GetPromise(ps, id) == IF id \in DOMAIN ps THEN ps[id] ELSE NULL

SetPromise(ps, p) ==
  [id \in DOMAIN ps \cup {p.id} |-> IF id = p.id THEN p ELSE ps[id]]

GetTask(ts, id) == IF id \in DOMAIN ts THEN ts[id] ELSE NULL

SetTask(ts, t) ==
  [id \in DOMAIN ts \cup {t.id} |-> IF id = t.id THEN t ELSE ts[id]]

SetPromiseTimeout(pts, id, timeout) ==
  [x \in DOMAIN pts \cup {id} |-> IF x = id THEN timeout ELSE pts[x]]

DelPromiseTimeout(pts, id) == [x \in DOMAIN pts \ {id} |-> pts[x]]

SetTaskTimeout(tts, id, kind, timeout) ==
  [k \in DOMAIN tts \cup {<<id, kind>>} |->
     IF k = <<id, kind>> THEN timeout ELSE tts[k]]

DelTaskTimeout(tts, id) == [k \in {x \in DOMAIN tts : x[1] # id} |-> tts[k]]

SetMessage(ob, address, msg) ==
  LET entry == [address |-> address, message |-> msg]
      key   == OutboxKey(entry)
  IN [k \in DOMAIN ob \cup {key} |-> IF k = key THEN entry ELSE ob[k]]

-----------------------------------------------------------------------------
(* 02-actions/00-resume.lean                                                *)
(*                                                                          *)
(* Lean's enqueueResume mutates tasks, taskTimeouts, and outbox for one     *)
(* awaiter, and the settling handlers loop it over a settled promise's      *)
(* callbacks. The awaiters are distinct tasks and distinct outbox keys, so  *)
(* the cascade is order-independent: each operator below gives              *)
(* enqueueResume's effect on one variable for the whole awaiter set at      *)
(* once. `ts` is the tasks value with the settled promise's task already    *)
(* fulfilled, so a self-callback is a no-op.                                *)

(* Oracle-aligned (go-actor cascadeSettle, the port of the TS SDK's
   LocalNetwork.Server):
   - version is bumped ONLY on acquire. A resume re-emits the CURRENT
     version: the execute is a wake-up hint, not a fresh fencing token.
   - no awaiter-deadline guard: the cascade touches the awaiter only
     through its TASK state (an expired awaiter's own settlement fulfills
     the task).
   - the resumed task records its trigger (resumes := {awaitedId});
     buffered resumes are deduplicated.
   - the state change does not require the awaiter promise; only the
     message does -- and an absent/empty target sends nothing. *)

\* suspended -> pending (resumes := {awaitedId}); pending/acquired/halted ->
\* buffer awaitedId; fulfilled or absent -> nothing
ResumeTasks(ts, awaitedId, awaiterIds) ==
  [id \in DOMAIN ts |->
     IF id \in awaiterIds THEN
       LET t0 == ts[id] IN
       IF t0.state = "suspended" THEN
         [t0 EXCEPT !.state = "pending", !.resumes = {awaitedId}]
       ELSE IF t0.state \in {"pending", "acquired", "halted"} THEN
         [t0 EXCEPT !.resumes = @ \cup {awaitedId}]
       ELSE \* fulfilled
         t0
     ELSE ts[id]]

\* a resumed (suspended) awaiter gets a pending-retry timeout
ResumeTaskTimeouts(tts, ts, awaiterIds, tnow) ==
  LET retryTimeout == config.retryTimeout
      resumed == {id \in awaiterIds \cap DOMAIN ts : ts[id].state = "suspended"}
      keys == {<<id, 0>> : id \in resumed}
  IN [k \in DOMAIN tts \cup keys |->
        IF k \in keys THEN tnow + retryTimeout ELSE tts[k]]

\* a resumed (suspended) awaiter whose promise has a non-empty target gets
\* an execute message re-emitting the CURRENT version
ResumeMessages(ob, ps, ts, awaiterIds) ==
  LET resumed == {id \in awaiterIds \cap DOMAIN ts : ts[id].state = "suspended"}
      targeted == {id \in resumed :
                     /\ id \in DOMAIN ps
                     /\ TagsGet(ps[id].tags, "resonate:target") # NULL
                     /\ TagsGet(ps[id].tags, "resonate:target") # ""}
      keys == {<<id>> : id \in targeted}
  IN [k \in DOMAIN ob \cup keys |->
        IF k \in keys
        THEN [address |-> TagsGet(ps[k[1]].tags, "resonate:target"),
              message |-> [type |-> "execute", taskId |-> k[1],
                           version |-> ts[k[1]].version]]
        ELSE ob[k]]

-----------------------------------------------------------------------------
(* 02-actions/02-timeouts.lean                                              *)
(* catchUp and onScheduleTimeout are omitted: schedules are ignored.        *)
(*                                                                          *)
(* Each timeout handler is an atomic action, fired one at a time by the     *)
(* tick handler at instant tnow.                                            *)

OnPromiseTimeout(id, tnow) ==
  LET p0 == GetPromise(promises, id) IN
  IF p0 = NULL THEN
    UNCHANGED serverVars
  ELSE IF p0.state # "pending" THEN
    UNCHANGED serverVars
  ELSE
    LET listeners == p0.listeners
        callbacks == p0.callbacks
        p == IF PromiseIsTimer(p0)
             THEN [p0 EXCEPT !.state = "resolved",
                             !.settledAt = p0.timeoutAt,
                             !.callbacks = {}, !.listeners = {}]
             ELSE [p0 EXCEPT !.state = "rejected_timedout",
                             !.settledAt = p0.timeoutAt,
                             !.callbacks = {}, !.listeners = {}]
        t == GetTask(tasks, p.id)
        \* settlement scrub: p can never be resumed again; drop its dead registrations
        scrubbed == [i \in DOMAIN promises |->
                       IF promises[i].state = "pending"
                       THEN [promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                       ELSE promises[i]]
        promises1 == SetPromise(scrubbed, p)
        tasks1 == IF t # NULL
                  THEN SetTask(tasks, [t EXCEPT !.state = "fulfilled", !.pid = NULL,
                                                !.ttl = NULL, !.resumes = {}])
                  ELSE tasks
        \* unblock every listener (one keyed entry per listener address)
        lkeys == {<<p.id, a>> : a \in listeners}
        unblocked == [k \in DOMAIN outbox \cup lkeys |->
                        IF k \in lkeys
                        THEN [address |-> k[2],
                              message |-> [type |-> "unblock",
                                           promise |-> PromiseToRecord(p)]]
                        ELSE outbox[k]]
    IN /\ promises' = promises1
       /\ promiseTimeouts' = DelPromiseTimeout(promiseTimeouts, p.id)
       /\ tasks' = ResumeTasks(tasks1, p.id, callbacks)
       /\ taskTimeouts' = ResumeTaskTimeouts(
                            IF t # NULL
                            THEN DelTaskTimeout(taskTimeouts, t.id)
                            ELSE taskTimeouts,
                            tasks1, callbacks, tnow)
       /\ outbox' = ResumeMessages(unblocked, promises1, tasks1, callbacks)

OnTaskRetryTimeout(id, tnow) ==
  LET retryTimeout == config.retryTimeout
      t == GetTask(tasks, id) IN
  IF t = NULL THEN
    UNCHANGED serverVars
  ELSE IF t.state # "pending" THEN
    UNCHANGED serverVars
  ELSE
    LET p == GetPromise(promises, t.id) IN
    /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id),
                                      t.id, 0, tnow + retryTimeout)
    /\ IF p = NULL THEN
         UNCHANGED outbox
       ELSE
         outbox' = SetMessage(outbox,
                     IF TagsGet(p.tags, "resonate:target") = NULL
                     THEN "" ELSE TagsGet(p.tags, "resonate:target"),
                     [type |-> "execute", taskId |-> t.id, version |-> t.version])
    /\ UNCHANGED <<promises, tasks, promiseTimeouts>>

OnTaskLeaseTimeout(id, tnow) ==
  LET retryTimeout == config.retryTimeout
      t0 == GetTask(tasks, id) IN
  IF t0 = NULL THEN
    UNCHANGED serverVars
  ELSE IF t0.state # "acquired" THEN
    UNCHANGED serverVars
  ELSE
    LET t == [t0 EXCEPT !.state = "pending", !.pid = NULL, !.ttl = NULL]
        p == GetPromise(promises, t.id) IN
    /\ tasks' = SetTask(tasks, t)
    /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id),
                                      t.id, 0, tnow + retryTimeout)
    /\ IF p = NULL THEN
         UNCHANGED outbox
       ELSE
         outbox' = SetMessage(outbox,
                     IF TagsGet(p.tags, "resonate:target") = NULL
                     THEN "" ELSE TagsGet(p.tags, "resonate:target"),
                     [type |-> "execute", taskId |-> t.id, version |-> t.version])
    /\ UNCHANGED <<promises, promiseTimeouts>>

-----------------------------------------------------------------------------
(* 02-actions/P-01-promise.get.lean                                         *)

PromiseGet(req) ==
  LET p == GetPromise(promises, req.id) IN
  /\ IF p = NULL THEN
       res' = [status |-> 404, promise |-> NULL]
     ELSE IF p.state = "pending" THEN
       IF p.timeoutAt <= now THEN
         LET projected ==
               IF PromiseIsTimer(p)
               THEN [p EXCEPT !.state = "resolved", !.settledAt = p.timeoutAt]
               ELSE [p EXCEPT !.state = "rejected_timedout", !.settledAt = p.timeoutAt]
         IN res' = [status |-> 200, promise |-> PromiseToRecord(projected)]
       ELSE
         res' = [status |-> 200, promise |-> PromiseToRecord(p)]
     ELSE
       res' = [status |-> 200, promise |-> PromiseToRecord(p)]
  /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* 02-actions/P-02-promise.create.lean                                      *)
(* Divergence: Lean parses the "resonate:delay" tag value with toNat!; here *)
(* the delay tag value is already a Nat.                                    *)
(* Wrap is the caller's response continuation (Lean returns the response    *)
(* to the caller; task.fence wraps it): plain calls pass LAMBDA r : r.      *)

PromiseCreate(req, Wrap(_)) ==
  LET retryTimeout == config.retryTimeout
      p0 == GetPromise(promises, req.id) IN
  IF p0 = NULL THEN
    IF req.timeoutAt > now THEN
      LET p == [id        |-> req.id,
                state     |-> "pending",
                param     |-> req.param,
                value     |-> [headers |-> <<>>, data |-> NULL],
                tags      |-> req.tags,
                timeoutAt |-> req.timeoutAt,
                createdAt |-> now,
                settledAt |-> NULL,
                callbacks |-> {},
                listeners |-> {}]
          target == TagsGet(p.tags, "resonate:target")
      IN
      /\ promises' = SetPromise(promises, p)
      /\ promiseTimeouts' = IF PromiseExternal(p)
                            THEN SetPromiseTimeout(promiseTimeouts, p.id, p.timeoutAt)
                            ELSE promiseTimeouts
      /\ res' = Wrap([status |-> 200, promise |-> PromiseToRecord(p)])
      /\ IF target = NULL THEN
           UNCHANGED <<tasks, taskTimeouts, outbox>>
         ELSE
           LET t == [id |-> p.id, state |-> "pending", version |-> 0,
                     ttl |-> NULL, pid |-> NULL, resumes |-> {}]
               delay == TagsGet(p.tags, "resonate:delay")
           IN
           /\ tasks' = SetTask(tasks, t)
           /\ IF delay = NULL THEN
                /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 0, now + retryTimeout)
                /\ outbox' = SetMessage(outbox, target,
                               [type |-> "execute", taskId |-> t.id, version |-> t.version])
              ELSE IF delay > now THEN
                /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 0, delay)
                /\ UNCHANGED outbox
              ELSE
                /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 0, now + retryTimeout)
                /\ outbox' = SetMessage(outbox, target,
                               [type |-> "execute", taskId |-> t.id, version |-> t.version])
    ELSE
      LET st == IF TagsIsTimer(req.tags)
                THEN "resolved"
                ELSE "rejected_timedout"
          p  == [id        |-> req.id,
                 state     |-> st,
                 param     |-> req.param,
                 value     |-> [headers |-> <<>>, data |-> NULL],
                 tags      |-> req.tags,
                 timeoutAt |-> req.timeoutAt,
                 createdAt |-> req.timeoutAt,
                 settledAt |-> req.timeoutAt,
                 callbacks |-> {},
                 listeners |-> {}]
      IN
      /\ promises' = SetPromise(promises, p)
      /\ res' = Wrap([status |-> 200, promise |-> PromiseToRecord(p)])
      /\ IF TagsHas(p.tags, "resonate:target") THEN
           LET t == [id |-> p.id, state |-> "fulfilled", version |-> 0,
                     ttl |-> NULL, pid |-> NULL, resumes |-> {}]
           IN tasks' = SetTask(tasks, t)
         ELSE
           UNCHANGED tasks
      /\ UNCHANGED <<promiseTimeouts, taskTimeouts, outbox>>
  ELSE
    IF p0.state = "pending" /\ p0.timeoutAt <= now THEN
      LET projected ==
            IF PromiseIsTimer(p0)
            THEN [p0 EXCEPT !.state = "resolved", !.settledAt = p0.timeoutAt]
            ELSE [p0 EXCEPT !.state = "rejected_timedout", !.settledAt = p0.timeoutAt]
      IN /\ res' = Wrap([status |-> 200, promise |-> PromiseToRecord(projected)])
         /\ UNCHANGED serverVars
    ELSE
      /\ res' = Wrap([status |-> 200, promise |-> PromiseToRecord(p0)])
      /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* 02-actions/P-03-promise.settle.lean                                      *)

PromiseSettle(req, Wrap(_)) ==
  LET p0 == GetPromise(promises, req.id) IN
  IF p0 = NULL THEN
    /\ res' = Wrap([status |-> 404, promise |-> NULL])
    /\ UNCHANGED serverVars
  ELSE IF p0.state = "pending" THEN
    IF p0.timeoutAt > now THEN
      LET listeners == p0.listeners
          callbacks == p0.callbacks
          p == [p0 EXCEPT !.state = req.state, !.value = req.value,
                          !.settledAt = now,
                          !.callbacks = {}, !.listeners = {}]
          t == GetTask(tasks, p.id)
          \* settlement scrub: p can never be resumed again; drop its dead registrations
          scrubbed == [i \in DOMAIN promises |->
                         IF promises[i].state = "pending"
                         THEN [promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                         ELSE promises[i]]
          promises1 == SetPromise(scrubbed, p)
          tasks1 == IF t # NULL
                    THEN SetTask(tasks, [t EXCEPT !.state = "fulfilled", !.pid = NULL,
                                                  !.ttl = NULL, !.resumes = {}])
                    ELSE tasks
          lkeys == {<<p.id, a>> : a \in listeners}
          unblocked == [k \in DOMAIN outbox \cup lkeys |->
                          IF k \in lkeys
                          THEN [address |-> k[2],
                                message |-> [type |-> "unblock",
                                             promise |-> PromiseToRecord(p)]]
                          ELSE outbox[k]]
      IN /\ promises' = promises1
         /\ promiseTimeouts' = DelPromiseTimeout(promiseTimeouts, p.id)
         /\ tasks' = ResumeTasks(tasks1, p.id, callbacks)
         /\ taskTimeouts' = ResumeTaskTimeouts(
                              IF t # NULL
                              THEN DelTaskTimeout(taskTimeouts, t.id)
                              ELSE taskTimeouts,
                              tasks1, callbacks, now)
         /\ outbox' = ResumeMessages(unblocked, promises1, tasks1, callbacks)
         /\ res' = Wrap([status |-> 200, promise |-> PromiseToRecord(p)])
    ELSE
      LET projected ==
            IF PromiseIsTimer(p0)
            THEN [p0 EXCEPT !.state = "resolved", !.settledAt = p0.timeoutAt]
            ELSE [p0 EXCEPT !.state = "rejected_timedout", !.settledAt = p0.timeoutAt]
      IN /\ res' = Wrap([status |-> 200, promise |-> PromiseToRecord(projected)])
         /\ UNCHANGED serverVars
  ELSE
    /\ res' = Wrap([status |-> 200, promise |-> PromiseToRecord(p0)])
    /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* 02-actions/P-04-promise.register_callback.lean                           *)

PromiseRegisterCallback(req) ==
  \* a promise cannot await itself (422)
  IF req.awaited = req.awaiter THEN
    /\ res' = [status |-> 422, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE
  LET pAwaited == GetPromise(promises, req.awaited) IN
  IF pAwaited = NULL THEN
    /\ res' = [status |-> 404, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE
  LET pAwaiter == GetPromise(promises, req.awaiter) IN
  IF pAwaiter = NULL THEN
    /\ res' = [status |-> 422, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE IF ~TagsHas(pAwaiter.tags, "resonate:target") THEN
    /\ res' = [status |-> 422, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE IF pAwaited.state = "pending" THEN
    IF pAwaited.timeoutAt > now THEN
      /\ promises' = IF pAwaiter.state = "pending" /\ pAwaiter.timeoutAt > now
                     THEN SetPromise(promises, PromiseAddCallback(pAwaited, req.awaiter))
                     ELSE promises
      /\ res' = [status |-> 200, promise |-> PromiseToRecord(pAwaited)]
      /\ UNCHANGED <<tasks, promiseTimeouts, taskTimeouts, outbox>>
    ELSE
      LET projected ==
            IF PromiseIsTimer(pAwaited)
            THEN [pAwaited EXCEPT !.state = "resolved",
                                  !.settledAt = pAwaited.timeoutAt]
            ELSE [pAwaited EXCEPT !.state = "rejected_timedout",
                                  !.settledAt = pAwaited.timeoutAt]
      IN /\ res' = [status |-> 200, promise |-> PromiseToRecord(projected)]
         /\ UNCHANGED serverVars
  ELSE
    /\ res' = [status |-> 200, promise |-> PromiseToRecord(pAwaited)]
    /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* 02-actions/P-05-promise.register_listener.lean                           *)

PromiseRegisterListener(req) ==
  LET pAwaited == GetPromise(promises, req.awaited) IN
  IF pAwaited = NULL THEN
    /\ res' = [status |-> 404, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE IF pAwaited.state = "pending" THEN
    IF pAwaited.timeoutAt > now THEN
      /\ promises' = SetPromise(promises, PromiseAddListener(pAwaited, req.address))
      /\ res' = [status |-> 200, promise |-> PromiseToRecord(pAwaited)]
      /\ UNCHANGED <<tasks, promiseTimeouts, taskTimeouts, outbox>>
    ELSE
      LET projected ==
            IF PromiseIsTimer(pAwaited)
            THEN [pAwaited EXCEPT !.state = "resolved",
                                  !.settledAt = pAwaited.timeoutAt]
            ELSE [pAwaited EXCEPT !.state = "rejected_timedout",
                                  !.settledAt = pAwaited.timeoutAt]
      IN /\ res' = [status |-> 200, promise |-> PromiseToRecord(projected)]
         /\ UNCHANGED serverVars
  ELSE
    /\ res' = [status |-> 200, promise |-> PromiseToRecord(pAwaited)]
    /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* 02-actions/P-06-promise.search.lean                                      *)

PromiseSearch(req) ==
  /\ res' = [status |-> 501, promises |-> <<>>, cursor |-> NULL]
  /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* 02-actions/T-01-task.get.lean                                            *)

TaskGet(req) ==
  LET t == GetTask(tasks, req.id) IN
  /\ IF t = NULL THEN
       res' = [status |-> 404, task |-> NULL]
     ELSE
       LET p == GetPromise(promises, t.id) IN
       IF p = NULL THEN
         res' = [status |-> 404, task |-> NULL]
       ELSE IF p.state = "pending" /\ p.timeoutAt > now THEN
         res' = [status |-> 200, task |-> TaskToRecord(t)]
       ELSE
         res' = [status |-> 200, task |->
                   TaskToRecord([t EXCEPT !.state = "fulfilled", !.pid = NULL,
                                          !.ttl = NULL, !.resumes = {}])]
  /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* 02-actions/T-02-task.create.lean                                         *)

TaskCreate(req) ==
  LET a  == req.action
      p0 == GetPromise(promises, a.id) IN
  IF p0 = NULL THEN
    \* a task exists to drive a TARGETED promise: an untargeted action is
    \* unroutable (mirrors the existing-promise branch below)
    IF ~TagsHas(a.tags, "resonate:target") THEN
      /\ res' = [status |-> 422, task |-> NULL, promise |-> NULL, preload |-> <<>>]
      /\ UNCHANGED serverVars
    ELSE IF a.timeoutAt > now THEN
      LET p == [id        |-> a.id,
                state     |-> "pending",
                param     |-> a.param,
                value     |-> [headers |-> <<>>, data |-> NULL],
                tags      |-> a.tags,
                timeoutAt |-> a.timeoutAt,
                createdAt |-> now,
                settledAt |-> NULL,
                callbacks |-> {},
                listeners |-> {}]
          t == [id |-> p.id, state |-> "acquired", version |-> 1,
                ttl |-> req.ttl, pid |-> req.pid, resumes |-> {}]
      IN
      /\ promises' = SetPromise(promises, p)
      /\ promiseTimeouts' = SetPromiseTimeout(promiseTimeouts, p.id, p.timeoutAt)
      /\ tasks' = SetTask(tasks, t)
      /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 1, now + req.ttl)
      /\ res' = [status |-> 200, task |-> TaskToRecord(t),
                 promise |-> PromiseToRecord(p), preload |-> <<>>]
      /\ UNCHANGED outbox
    ELSE
      LET st == IF TagsIsTimer(a.tags)
                THEN "resolved"
                ELSE "rejected_timedout"
          p  == [id        |-> a.id,
                 state     |-> st,
                 param     |-> a.param,
                 value     |-> [headers |-> <<>>, data |-> NULL],
                 tags      |-> a.tags,
                 timeoutAt |-> a.timeoutAt,
                 createdAt |-> a.timeoutAt,
                 settledAt |-> a.timeoutAt,
                 callbacks |-> {},
                 listeners |-> {}]
          t  == [id |-> p.id, state |-> "fulfilled", version |-> 0,
                 ttl |-> NULL, pid |-> NULL, resumes |-> {}]
      IN
      /\ promises' = SetPromise(promises, p)
      /\ tasks' = SetTask(tasks, t)
      /\ res' = [status |-> 200, task |-> TaskToRecord(t),
                 promise |-> PromiseToRecord(p), preload |-> <<>>]
      /\ UNCHANGED <<promiseTimeouts, taskTimeouts, outbox>>
  ELSE
    IF ~TagsHas(p0.tags, "resonate:target") THEN
      /\ res' = [status |-> 422, task |-> NULL, promise |-> NULL, preload |-> <<>>]
      /\ UNCHANGED serverVars
    ELSE
    LET t0 == GetTask(tasks, p0.id) IN
    IF t0 # NULL THEN
      IF t0.state = "fulfilled" THEN
        /\ res' = [status |-> 200, task |-> TaskToRecord(t0),
                   promise |-> PromiseToRecord(p0), preload |-> <<>>]
        /\ UNCHANGED serverVars
      ELSE IF t0.state = "pending" THEN
        LET t == [t0 EXCEPT !.state = "acquired", !.version = t0.version + 1,
                            !.ttl = req.ttl, !.pid = req.pid, !.resumes = {}]
        IN
        /\ tasks' = SetTask(tasks, t)
        /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id), t.id, 1, now + req.ttl)
        /\ res' = [status |-> 200, task |-> TaskToRecord(t),
                   promise |-> PromiseToRecord(p0), preload |-> <<>>]
        /\ UNCHANGED <<promises, promiseTimeouts, outbox>>
      ELSE
        /\ res' = [status |-> 409, task |-> NULL, promise |-> NULL, preload |-> <<>>]
        /\ UNCHANGED serverVars
    ELSE
      /\ res' = [status |-> 409, task |-> NULL, promise |-> NULL, preload |-> <<>>]
      /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* 02-actions/T-03-task.acquire.lean                                        *)

TaskAcquire(req) ==
  LET t0 == GetTask(tasks, req.id) IN
  IF t0 = NULL THEN
    /\ res' = [status |-> 404, task |-> NULL, promise |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE
  LET p == GetPromise(promises, t0.id) IN
  IF p = NULL THEN
    /\ res' = [status |-> 409, task |-> NULL, promise |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF t0.state # "pending" THEN
    /\ res' = [status |-> 409, task |-> NULL, promise |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF p.state # "pending" \/ p.timeoutAt <= now THEN
    /\ res' = [status |-> 409, task |-> NULL, promise |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF t0.version # req.version THEN
    /\ res' = [status |-> 409, task |-> NULL, promise |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE
    LET t == [t0 EXCEPT !.state = "acquired", !.version = t0.version + 1,
                        !.ttl = req.ttl, !.pid = req.pid, !.resumes = {}]
    IN
    /\ tasks' = SetTask(tasks, t)
    /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id), t.id, 1, now + req.ttl)
    /\ res' = [status |-> 200, task |-> TaskToRecord(t),
               promise |-> PromiseToRecord(p), preload |-> <<>>]
    /\ UNCHANGED <<promises, promiseTimeouts, outbox>>

-----------------------------------------------------------------------------
(* 02-actions/T-04-task.fence.lean                                          *)
(* Lean binds the inner handler's response and wraps it; here the wrapper   *)
(* is passed to the inner handler as its response continuation.             *)

TaskFence(req) ==
  LET t == GetTask(tasks, req.id) IN
  IF t = NULL THEN
    /\ res' = [status |-> 404, action |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE
  LET p == GetPromise(promises, t.id) IN
  IF p = NULL THEN
    /\ res' = [status |-> 409, action |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF t.state # "acquired" THEN
    /\ res' = [status |-> 409, action |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF p.state # "pending" \/ p.timeoutAt <= now THEN
    /\ res' = [status |-> 409, action |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF t.version # req.version THEN
    /\ res' = [status |-> 409, action |-> NULL, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF req.action.type = "create" THEN
    PromiseCreate(req.action.req,
      LAMBDA r : [status |-> 200, action |-> [type |-> "create", res |-> r],
                  preload |-> <<>>])
  ELSE
    PromiseSettle(req.action.req,
      LAMBDA r : [status |-> 200, action |-> [type |-> "settle", res |-> r],
                  preload |-> <<>>])

-----------------------------------------------------------------------------
(* 02-actions/T-05-task.heartbeat.lean                                      *)
(* The refs touch distinct task-timeout keys and only read tasks/promises,  *)
(* so Lean's loop is order-independent: one map rebuild for the whole ref   *)
(* list.                                                                    *)

TaskHeartbeat(req) ==
  LET refs == {req.tasks[i] : i \in DOMAIN req.tasks}
      valid == {r \in refs :
                  /\ r.id \in DOMAIN tasks
                  /\ tasks[r.id].state = "acquired"
                  /\ tasks[r.id].version = r.version
                  /\ tasks[r.id].pid = req.pid
                  /\ r.id \in DOMAIN promises
                  /\ promises[r.id].state = "pending"
                  /\ promises[r.id].timeoutAt > now}
      ids == {r.id : r \in valid}
  IN /\ taskTimeouts' =
          [k \in {x \in DOMAIN taskTimeouts : x[1] \notin ids}
                   \cup {<<id, 1>> : id \in ids} |->
             IF k[1] \in ids
             THEN now + (IF tasks[k[1]].ttl = NULL THEN 0 ELSE tasks[k[1]].ttl)
             ELSE taskTimeouts[k]]
     /\ res' = [status |-> 200]
     /\ UNCHANGED <<promises, tasks, promiseTimeouts, outbox>>

-----------------------------------------------------------------------------
(* 02-actions/T-06-task.suspend.lean                                        *)

TaskSuspend(req) ==
  LET t0 == GetTask(tasks, req.id) IN
  IF t0 = NULL THEN
    /\ res' = [status |-> 404, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE
  LET tp == GetPromise(promises, t0.id) IN
  IF tp = NULL THEN
    /\ res' = [status |-> 409, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF t0.state # "acquired" THEN
    /\ res' = [status |-> 409, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF tp.state # "pending" \/ tp.timeoutAt <= now THEN
    /\ res' = [status |-> 409, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF t0.version # req.version THEN
    /\ res' = [status |-> 409, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF \E i \in DOMAIN req.actions : req.actions[i].awaited = req.id THEN
    \* a task cannot await its own promise (422)
    /\ res' = [status |-> 422, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE IF \E i \in DOMAIN req.actions :
            GetPromise(promises, req.actions[i].awaited) = NULL THEN
    /\ res' = [status |-> 422, preload |-> <<>>]
    /\ UNCHANGED serverVars
  ELSE
    LET settled == \E i \in DOMAIN req.actions :
                     LET pa == GetPromise(promises, req.actions[i].awaited)
                     IN pa.state # "pending" \/ pa.timeoutAt <= now
    IN
    IF settled THEN
      /\ tasks' = SetTask(tasks, [t0 EXCEPT !.resumes = {}])
      /\ res' = [status |-> 300, preload |-> <<>>]
      /\ UNCHANGED <<promises, promiseTimeouts, taskTimeouts, outbox>>
    ELSE
      LET awaitedIds == {req.actions[i].awaited : i \in DOMAIN req.actions}
      IN
      /\ promises' = [id \in DOMAIN promises |->
                        IF id \in awaitedIds
                        THEN PromiseAddCallback(promises[id], req.id)
                        ELSE promises[id]]
      /\ tasks' = SetTask(tasks, [t0 EXCEPT !.state = "suspended", !.pid = NULL,
                                            !.ttl = NULL, !.resumes = {}])
      /\ taskTimeouts' = DelTaskTimeout(taskTimeouts, t0.id)
      /\ res' = [status |-> 200, preload |-> <<>>]
      /\ UNCHANGED <<promiseTimeouts, outbox>>

-----------------------------------------------------------------------------
(* 02-actions/T-07-task.fulfill.lean                                        *)

TaskFulfill(req) ==
  LET t0 == GetTask(tasks, req.id) IN
  IF t0 = NULL THEN
    /\ res' = [status |-> 404, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE
  LET p0 == GetPromise(promises, t0.id) IN
  IF p0 = NULL THEN
    /\ res' = [status |-> 409, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE IF t0.state # "acquired" THEN
    /\ res' = [status |-> 409, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE IF p0.state # "pending" \/ p0.timeoutAt <= now THEN
    /\ res' = [status |-> 409, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE IF t0.version # req.version THEN
    /\ res' = [status |-> 409, promise |-> NULL]
    /\ UNCHANGED serverVars
  ELSE
    LET listeners == p0.listeners
        callbacks == p0.callbacks
        p == [p0 EXCEPT !.state = req.action.state, !.value = req.action.value,
                        !.settledAt = now,
                        !.callbacks = {}, !.listeners = {}]
        \* settlement scrub: p can never be resumed again; drop its dead registrations
        scrubbed == [i \in DOMAIN promises |->
                       IF promises[i].state = "pending"
                       THEN [promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                       ELSE promises[i]]
        promises1 == SetPromise(scrubbed, p)
        tasks1 == SetTask(tasks, [t0 EXCEPT !.state = "fulfilled", !.pid = NULL,
                                            !.ttl = NULL, !.resumes = {}])
        lkeys == {<<p.id, a>> : a \in listeners}
        unblocked == [k \in DOMAIN outbox \cup lkeys |->
                        IF k \in lkeys
                        THEN [address |-> k[2],
                              message |-> [type |-> "unblock",
                                           promise |-> PromiseToRecord(p)]]
                        ELSE outbox[k]]
    IN /\ promises' = promises1
       /\ promiseTimeouts' = DelPromiseTimeout(promiseTimeouts, p.id)
       /\ tasks' = ResumeTasks(tasks1, p.id, callbacks)
       /\ taskTimeouts' = ResumeTaskTimeouts(DelTaskTimeout(taskTimeouts, t0.id),
                                             tasks1, callbacks, now)
       /\ outbox' = ResumeMessages(unblocked, promises1, tasks1, callbacks)
       /\ res' = [status |-> 200, promise |-> PromiseToRecord(p)]

-----------------------------------------------------------------------------
(* 02-actions/T-08-task.release.lean                                        *)

TaskRelease(req) ==
  LET retryTimeout == config.retryTimeout
      t0 == GetTask(tasks, req.id) IN
  IF t0 = NULL THEN
    /\ res' = [status |-> 404]
    /\ UNCHANGED serverVars
  ELSE
  LET p == GetPromise(promises, t0.id) IN
  IF p = NULL THEN
    /\ res' = [status |-> 409]
    /\ UNCHANGED serverVars
  ELSE IF t0.state # "acquired" THEN
    /\ res' = [status |-> 409]
    /\ UNCHANGED serverVars
  ELSE IF p.state # "pending" \/ p.timeoutAt <= now THEN
    /\ res' = [status |-> 409]
    /\ UNCHANGED serverVars
  ELSE IF t0.version # req.version THEN
    /\ res' = [status |-> 409]
    /\ UNCHANGED serverVars
  ELSE
    LET t == [t0 EXCEPT !.state = "pending", !.pid = NULL, !.ttl = NULL]
    IN
    /\ tasks' = SetTask(tasks, t)
    /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id), t.id, 0, now + retryTimeout)
    /\ outbox' = SetMessage(outbox,
                   IF TagsGet(p.tags, "resonate:target") = NULL
                   THEN "" ELSE TagsGet(p.tags, "resonate:target"),
                   [type |-> "execute", taskId |-> t.id, version |-> t.version])
    /\ res' = [status |-> 200]
    /\ UNCHANGED <<promises, promiseTimeouts>>

-----------------------------------------------------------------------------
(* 02-actions/T-09-task.halt.lean                                           *)

TaskHalt(req) ==
  LET t == GetTask(tasks, req.id) IN
  IF t = NULL THEN
    /\ res' = [status |-> 404]
    /\ UNCHANGED serverVars
  ELSE IF t.state = "fulfilled" THEN
    /\ res' = [status |-> 409]
    /\ UNCHANGED serverVars
  ELSE IF t.state = "halted" THEN
    /\ res' = [status |-> 200]
    /\ UNCHANGED serverVars
  ELSE
    /\ tasks' = SetTask(tasks, [t EXCEPT !.state = "halted", !.pid = NULL, !.ttl = NULL])
    /\ taskTimeouts' = DelTaskTimeout(taskTimeouts, t.id)
    /\ res' = [status |-> 200]
    /\ UNCHANGED <<promises, promiseTimeouts, outbox>>

-----------------------------------------------------------------------------
(* 02-actions/T-10-task.continue.lean                                       *)

TaskContinue(req) ==
  LET retryTimeout == config.retryTimeout
      t0 == GetTask(tasks, req.id) IN
  IF t0 = NULL THEN
    /\ res' = [status |-> 404]
    /\ UNCHANGED serverVars
  ELSE IF t0.state # "halted" THEN
    /\ res' = [status |-> 409]
    /\ UNCHANGED serverVars
  ELSE
  LET p == GetPromise(promises, t0.id) IN
  IF p = NULL THEN
    /\ res' = [status |-> 404]
    /\ UNCHANGED serverVars
  ELSE
    LET t == [t0 EXCEPT !.state = "pending"]
    IN
    /\ tasks' = SetTask(tasks, t)
    /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 0, now + retryTimeout)
    /\ outbox' = SetMessage(outbox,
                   IF TagsGet(p.tags, "resonate:target") = NULL
                   THEN "" ELSE TagsGet(p.tags, "resonate:target"),
                   [type |-> "execute", taskId |-> t.id, version |-> t.version])
    /\ res' = [status |-> 200]
    /\ UNCHANGED <<promises, promiseTimeouts>>

-----------------------------------------------------------------------------
(* 02-actions/T-11-task.search.lean                                         *)

TaskSearch(req) ==
  /\ res' = [status |-> 501, tasks |-> <<>>, cursor |-> NULL]
  /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* Tick — no Lean counterpart. A tick advances the clock and/or fires ONE   *)
(* eligible timeout handler (deadline <= now) as one atomic step. Because   *)
(* a tick may leave the clock unchanged, consecutive ticks at the same      *)
(* instant fire the remaining eligible entries one at a time: at a single   *)
(* instant any number of eligible actions -- from 1 to all -- can execute,  *)
(* in any order.                                                            *)

Eligible(tnow) ==
  {[type |-> "promise", id |-> id] :
     id \in {x \in DOMAIN promiseTimeouts : promiseTimeouts[x] <= tnow}}
  \cup
  {[type |-> "task", id |-> k[1], kind |-> k[2]] :
     k \in {x \in DOMAIN taskTimeouts : taskTimeouts[x] <= tnow}}

Fire(entry, tnow) ==
  IF entry.type = "promise" THEN OnPromiseTimeout(entry.id, tnow)
  ELSE IF entry.kind = 0 THEN OnTaskRetryTimeout(entry.id, tnow)
  ELSE OnTaskLeaseTimeout(entry.id, tnow)

-----------------------------------------------------------------------------
(* Model: requests are records drawn nondeterministically from the small    *)
(* sets below; time advances only via TickAction.                           *)

CONSTANTS PromiseIds,  \* promise ids == task ids
          Pids,        \* worker process ids
          Addresses,   \* "resonate:target" values / listener addresses
          DataValues,  \* payload data values
          MaxTime      \* clock horizon

-----------------------------------------------------------------------------
(* Request generators.                                                      *)

Times == 0..(MaxTime + 1)

Versions == 0..3

TTLs == {2}

Values == {[headers |-> <<>>, data |-> NULL]}
            \cup {[headers |-> <<>>, data |-> d] : d \in DataValues}

TagOptions ==
  {<<>>, <<<<"resonate:timer", "true">>>>}
    \cup {<<<<"resonate:target", a>>>> : a \in Addresses}
    \cup {<<<<"resonate:target", a>>, <<"resonate:delay", d>>>> :
            a \in Addresses, d \in {2}}

SettleStates == {"resolved", "rejected", "rejected_canceled"}

PromiseCreateReqs ==
  [id : PromiseIds, timeoutAt : Times, param : Values, tags : TagOptions]

PromiseSettleReqs == [id : PromiseIds, state : SettleStates, value : Values]

RegisterCallbackReqs == [awaited : PromiseIds, awaiter : PromiseIds]

TaskRefs == [id : PromiseIds, version : Versions]

FenceActions == {[type |-> "create", req |-> r] : r \in PromiseCreateReqs}
                  \cup {[type |-> "settle", req |-> r] : r \in PromiseSettleReqs}

HeartbeatLists == {<<>>}
                    \cup {<<r>> : r \in TaskRefs}
                    \cup {<<r1, r2>> : r1 \in TaskRefs, r2 \in TaskRefs}

SuspendLists == {<<>>}
                  \cup {<<a>> : a \in RegisterCallbackReqs}
                  \cup {<<a1, a2>> : a1 \in RegisterCallbackReqs,
                                     a2 \in RegisterCallbackReqs}

-----------------------------------------------------------------------------
(* One action per protocol handler.                                         *)

PromiseGetAction ==
  \E req \in [id : PromiseIds] :
    PromiseGet(req) /\ UNCHANGED now

PromiseCreateAction ==
  \E req \in PromiseCreateReqs :
    PromiseCreate(req, LAMBDA r : r) /\ UNCHANGED now

PromiseSettleAction ==
  \E req \in PromiseSettleReqs :
    PromiseSettle(req, LAMBDA r : r) /\ UNCHANGED now

PromiseRegisterCallbackAction ==
  \E req \in RegisterCallbackReqs :
    PromiseRegisterCallback(req) /\ UNCHANGED now

PromiseRegisterListenerAction ==
  \E req \in [awaited : PromiseIds, address : Addresses] :
    PromiseRegisterListener(req) /\ UNCHANGED now

PromiseSearchAction ==
  PromiseSearch([state |-> NULL, tags |-> <<>>, limit |-> NULL, cursor |-> NULL])
    /\ UNCHANGED now

TaskGetAction ==
  \E req \in [id : PromiseIds] :
    TaskGet(req) /\ UNCHANGED now

TaskCreateAction ==
  \E req \in [pid : Pids, ttl : TTLs, action : PromiseCreateReqs] :
    TaskCreate(req) /\ UNCHANGED now

TaskAcquireAction ==
  \E req \in [id : PromiseIds, version : Versions, pid : Pids, ttl : TTLs] :
    TaskAcquire(req) /\ UNCHANGED now

TaskFenceAction ==
  \E req \in [id : PromiseIds, version : Versions, action : FenceActions] :
    TaskFence(req) /\ UNCHANGED now

TaskHeartbeatAction ==
  \E req \in [pid : Pids, tasks : HeartbeatLists] :
    TaskHeartbeat(req) /\ UNCHANGED now

TaskSuspendAction ==
  \E req \in [id : PromiseIds, version : Versions, actions : SuspendLists] :
    TaskSuspend(req) /\ UNCHANGED now

TaskFulfillAction ==
  \E req \in [id : PromiseIds, version : Versions, action : PromiseSettleReqs] :
    TaskFulfill(req) /\ UNCHANGED now

TaskReleaseAction ==
  \E req \in [id : PromiseIds, version : Versions] :
    TaskRelease(req) /\ UNCHANGED now

TaskHaltAction ==
  \E req \in [id : PromiseIds] :
    TaskHalt(req) /\ UNCHANGED now

TaskContinueAction ==
  \E req \in [id : PromiseIds] :
    TaskContinue(req) /\ UNCHANGED now

TaskSearchAction ==
  TaskSearch([state |-> NULL, limit |-> NULL, cursor |-> NULL])
    /\ UNCHANGED now

-----------------------------------------------------------------------------
(* The tick handler: advance the clock and/or fire one eligible timeout     *)
(* handler. A tick that fires nothing must at least advance the clock.      *)

TickAction ==
  \E newNow \in now..MaxTime :
    /\ \/ /\ newNow > now
          /\ UNCHANGED serverVars
       \/ \E entry \in Eligible(newNow) :
            Fire(entry, newNow)
    /\ now' = newNow
    /\ res' = NULL

-----------------------------------------------------------------------------

Init == /\ promises = [id \in {} |-> NULL]        \* Lean: ServerState.init
        /\ tasks = [id \in {} |-> NULL]
        /\ promiseTimeouts = [id \in {} |-> NULL]
        /\ taskTimeouts = [k \in {} |-> NULL]
        /\ outbox = [k \in {} |-> NULL]
        /\ now = 0
        /\ res = NULL

Next == \/ PromiseGetAction
        \/ PromiseCreateAction
        \/ PromiseSettleAction
        \/ PromiseRegisterCallbackAction
        \/ PromiseRegisterListenerAction
        \/ PromiseSearchAction
        \/ TaskGetAction
        \/ TaskCreateAction
        \/ TaskAcquireAction
        \/ TaskFenceAction
        \/ TaskHeartbeatAction
        \/ TaskSuspendAction
        \/ TaskFulfillAction
        \/ TaskReleaseAction
        \/ TaskHaltAction
        \/ TaskContinueAction
        \/ TaskSearchAction
        \/ TickAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Bound for model checking: task versions only grow via acquire.           *)

Constraint == \A id \in DOMAIN tasks : tasks[id].version <= 3

(* State identity for TLC (cfg: VIEW View): the last response is an         *)
(* observation of a step, not state -- no handler reads `res`, so           *)
(* successors and per-transition checks are independent of it. Excluding    *)
(* it from the fingerprint collapses states that differ only in what was    *)
(* last answered.                                                           *)
View == <<promises, tasks, promiseTimeouts, taskTimeouts, outbox, now>>

-----------------------------------------------------------------------------
(* The structural invariant catalog from the Dafny abstract spec            *)
(* (resonate-kafka/abstract/Invariants.dfy), ported predicate-for-          *)
(* predicate. Unbounded Dafny quantifiers are bounded by the map domains.   *)
(* Check with ServerInv.cfg; the verdicts (which hold, which need an        *)
(* environment assumption) are recorded next to each predicate.             *)

PromiseHasTarget(p) == TagsHas(p.tags, "resonate:target")

WFState ==
  /\ \A id \in DOMAIN promises : promises[id].id = id
  /\ \A id \in DOMAIN tasks : tasks[id].id = id

\* Section 1 -- Promise-Task Coupling

PromiseWithTargetHasTask ==
  \A id \in DOMAIN promises :
    PromiseHasTarget(promises[id]) => id \in DOMAIN tasks

TaskHasPromise ==
  \A id \in DOMAIN tasks : id \in DOMAIN promises

ActivePromiseHasActiveTask ==
  \A id \in DOMAIN promises :
    (promises[id].state = "pending" /\ PromiseHasTarget(promises[id]))
      => id \in DOMAIN tasks /\ tasks[id].state # "fulfilled"

ActiveTaskHasActivePromise ==
  \A id \in DOMAIN tasks :
    tasks[id].state # "fulfilled"
      => id \in DOMAIN promises /\ promises[id].state = "pending"

SettledPromiseHasFulfilledTask ==
  \A id \in DOMAIN promises :
    (promises[id].state # "pending" /\ PromiseHasTarget(promises[id]))
      => id \in DOMAIN tasks /\ tasks[id].state = "fulfilled"

FulfilledTaskHasSettledPromise ==
  \A id \in DOMAIN tasks :
    tasks[id].state = "fulfilled"
      => id \in DOMAIN promises /\ promises[id].state # "pending"

PromiseNoTargetHasNoTask ==
  \A id \in DOMAIN promises :
    ~PromiseHasTarget(promises[id]) => id \notin DOMAIN tasks

\* Section 2 -- Promise Structure

PendingExternalPromiseHasTimeout ==
  \A id \in DOMAIN promises :
    (promises[id].state = "pending" /\ PromiseExternal(promises[id]))
      => id \in DOMAIN promiseTimeouts

NonExternalPromiseHasNoTimeout ==
  \A id \in DOMAIN promiseTimeouts :
    id \in DOMAIN promises => PromiseExternal(promises[id])

PTimeoutsSubsetPromises == DOMAIN promiseTimeouts \subseteq DOMAIN promises

SettledPromiseHasNoTimeout ==
  \A id \in DOMAIN promises :
    promises[id].state # "pending" => id \notin DOMAIN promiseTimeouts

SettledPromiseHasNoCallbacks ==
  \A id \in DOMAIN promises :
    promises[id].state # "pending" => promises[id].callbacks = {}

CallbackNotSelfReferential ==
  \A id \in DOMAIN promises : id \notin promises[id].callbacks

CallbackAwaiterHasTask ==
  \A id \in DOMAIN promises : \A aw \in promises[id].callbacks :
    aw \in DOMAIN tasks

CallbackAwaiterIsPending ==
  \A id \in DOMAIN promises : \A aw \in promises[id].callbacks :
    aw \in DOMAIN promises /\ promises[aw].state = "pending"

\* Section 5 -- Task Structure

NonAcquiredTaskNoPidOrTtl ==
  \A id \in DOMAIN tasks :
    tasks[id].state # "acquired"
      => tasks[id].pid = NULL /\ tasks[id].ttl = NULL

\* FAILS: a suspend with an empty actions list (Lean T-06 allows it) parks
\* the task without registering anything. An environment assumption.
SuspendedTaskHasCallback ==
  \A id \in DOMAIN tasks :
    tasks[id].state = "suspended"
      => \E pid \in DOMAIN promises : id \in promises[pid].callbacks

FulfilledTaskHasEmptyResumes ==
  \A id \in DOMAIN tasks :
    tasks[id].state = "fulfilled" => tasks[id].resumes = {}

\* Section 7 -- Task Timeouts

PendingTaskHasRetryTimeout ==
  \A id \in DOMAIN tasks :
    tasks[id].state = "pending" => <<id, 0>> \in DOMAIN taskTimeouts

AcquiredTaskHasLeaseTimeout ==
  \A id \in DOMAIN tasks :
    tasks[id].state = "acquired" => <<id, 1>> \in DOMAIN taskTimeouts

LeaseTimeoutHasValidPidAndTtl ==
  \A k \in DOMAIN taskTimeouts :
    k[2] = 1 => /\ k[1] \in DOMAIN tasks
                /\ tasks[k[1]].state = "acquired"
                /\ tasks[k[1]].pid # NULL
                /\ tasks[k[1]].ttl # NULL

TaskHasAtMostOneTimeout ==
  \A k \in DOMAIN taskTimeouts : <<k[1], 1 - k[2]>> \notin DOMAIN taskTimeouts

SuspendedTaskHasNoTimeout ==
  \A k \in DOMAIN taskTimeouts :
    k[1] \in DOMAIN tasks => tasks[k[1]].state # "suspended"

HaltedTaskHasNoTimeout ==
  \A k \in DOMAIN taskTimeouts :
    k[1] \in DOMAIN tasks => tasks[k[1]].state # "halted"

FulfilledTaskHasNoTimeout ==
  \A k \in DOMAIN taskTimeouts :
    k[1] \in DOMAIN tasks => tasks[k[1]].state # "fulfilled"

LeaseTimeoutOnlyForAcquiredTask ==
  \A k \in DOMAIN taskTimeouts :
    k[2] = 1 => k[1] \in DOMAIN tasks /\ tasks[k[1]].state = "acquired"

RetryTimeoutOnlyForPendingTask ==
  \A k \in DOMAIN taskTimeouts :
    k[2] = 0 => k[1] \in DOMAIN tasks /\ tasks[k[1]].state = "pending"

=============================================================================
