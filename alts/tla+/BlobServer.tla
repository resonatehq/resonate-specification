---------------------------- MODULE BlobServer -----------------------------
(* Resonate on blob storage. Sources:                                       *)
(*   - resonate-kafka/blobfun (Dafny): the sharded, blob-backed model --    *)
(*     one blob = one workflow = one S3 object; handlers are                *)
(*     Load ; Sweep ; Apply ; Store with a timer index reconciled at every  *)
(*     store; the driver wakes due workflows off the index.                 *)
(*   - libr8/impl/rs (Rust): the running implementation -- every operation  *)
(*     is load -> sweep due timeouts -> apply -> conditional PUT (CAS,      *)
(*     retry on conflict); every pending promise's deadline is armed        *)
(*     in-blob (write-through observation); a `_timer-<enc20(deadline)>-    *)
(*     <origin>` marker publishes the workflow's next deadline for the      *)
(*     driver; the outbox is in-blob and keyed.                             *)
(*                                                                          *)
(* THE ORDER QUOTIENT (matching the abstract Server spec): collections are  *)
(* id-keyed maps and sets, the outbox a key-indexed map. blobfun already    *)
(* models them this way; libr8's vectors carry only accidental order (all   *)
(* access is by id / by key), so nothing observable is lost -- and the      *)
(* accidental representation differences between the two specs (list       *)
(* recency order, outbox append-vs-prepend) are no longer expressible.      *)
(*                                                                          *)
(* THE ATOMICITY MODEL. The CAS makes each Load-Sweep-Apply-Store commit    *)
(* atomic (contention only retries; blobfun models the ideal single-op     *)
(* case, as do we). TLA+ refinement is checked step for step, so the       *)
(* commit is decomposed into micro-steps that are each one abstract step:  *)
(*   - SweepDueAction fires ONE due timeout entry of one workflow (= the    *)
(*     abstract TickAction at an unchanged clock);                          *)
(*   - a mutating handler requires its workflow to be SWEPT (no due         *)
(*     entries) -- the sweep prefix of the real commit has been factored    *)
(*     into SweepDueAction steps; the remaining Apply is one abstract       *)
(*     step.                                                                 *)
(*   - RESPONSES ARE OUT OF SCOPE (as in the abstract spec): the checked    *)
(*     property is state evolution. Reads (get / search) take no store      *)
(*     write -- pure observations, absent from Next.                        *)
(* A real commit is exactly a SweepDueAction* ; Handler sequence of these   *)
(* micro-steps; the model additionally allows other requests to interleave  *)
(* between them, a superset of behaviors that must (and does) still refine. *)
(*                                                                          *)
(* DELIBERATE DEVIATION from the sources: the task-timeout firings send     *)
(* the execute message even when the promise has no target (address ""),   *)
(* mirroring the abstract spec's unconditional getD-"" send; blobfun and    *)
(* libr8 both GUARD that send -- a real divergence from the abstract spec,  *)
(* surfaced by this refinement (the spec's release/continue send            *)
(* unconditionally, its timeout paths too; the implementations only guard   *)
(* the timeout paths).                                                      *)
(*                                                                          *)
(* ENVIRONMENT ASSUMPTIONS under which refinement is stated (both sources   *)
(* make them):                                                              *)
(*   - same-origin: all ids of one REQUEST share an origin -- callbacks,    *)
(*     suspends, heartbeats, fence inner actions stay within one blob       *)
(*     (libr8 validates `same_origin`). The request generators below        *)
(*     enforce it.                                                          *)
(*   - external-only promises: every promise carries resonate:target or     *)
(*     resonate:timer. libr8 arms EVERY pending promise's deadline and its  *)
(*     sweep persists every expiry; the abstract spec arms only external    *)
(*     promises and settles internal expiries never (projection only).     *)
(*     On external-only requests the two coincide exactly.                  *)
(*                                                                          *)
(* The refinement (the very last section) maps this module's variables to   *)
(* the abstract Server spec with INSTANCE ... WITH and states               *)
(* Refinement == Abs!Spec. Under the order quotient the abstraction        *)
(* function is simply the union of the shards -- exact for ANY number of    *)
(* origins (the recency-order obstruction of the sequence representation    *)
(* is gone).                                                                *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NULL

CONSTANTS PromiseIds,  \* promise ids == task ids
          Pids,        \* worker process ids
          Addresses,   \* "resonate:target" values / listener addresses
          DataValues,  \* payload data values
          MaxTime      \* clock horizon

CONSTANT RetryTimeout  \* libr8: RETRY_TIMEOUT

CONSTANTS Origins,     \* workflow keys: one blob per origin
          OriginMap    \* id -> origin (libr8: origin(id), the id's routing segment)

VARIABLES blobs,    \* [Origins -> workflow record]: the bucket, one blob per workflow
          markers   \* the timer index: {[deadline, origin]} -- the driver's wake structure

VARIABLE now  \* the clock; only SweepDueAction/AdvanceClockAction move it

vars == <<blobs, markers, now>>

config == [retryTimeout |-> RetryTimeout]

OriginOf(id) == OriginMap[id]

-----------------------------------------------------------------------------
(* The wire/pure layer -- shared shapes with the abstract spec (the Dafny   *)
(* twins share Types.dfy the same way).                                     *)

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

\* libr8 Workflow::send -- per-key replacement (keyed map update).
SendMsg(ob, address, msg) ==
  LET entry == [address |-> address, message |-> msg]
      key   == OutboxKey(entry)
  IN [k \in DOMAIN ob \cup {key} |-> IF k = key THEN entry ELSE ob[k]]

\* The promise a live create stores; the promise an expired create stores
\* (settled at birth); a settled promise.
PromiseCreated(req) ==
  [id        |-> req.id,
   state     |-> "pending",
   param     |-> req.param,
   value     |-> [headers |-> <<>>, data |-> NULL],
   tags      |-> req.tags,
   timeoutAt |-> req.timeoutAt,
   createdAt |-> now,
   settledAt |-> NULL,
   callbacks |-> {},
   listeners |-> {}]

PromiseCreatedExpired(req) ==
  [id        |-> req.id,
   state     |-> IF TagsIsTimer(req.tags) THEN "resolved" ELSE "rejected_timedout",
   param     |-> req.param,
   value     |-> [headers |-> <<>>, data |-> NULL],
   tags      |-> req.tags,
   timeoutAt |-> req.timeoutAt,
   createdAt |-> req.timeoutAt,
   settledAt |-> req.timeoutAt,
   callbacks |-> {},
   listeners |-> {}]

PromiseSettled(p, req) ==
  [p EXCEPT !.state = req.state, !.value = req.value, !.settledAt = now,
            !.callbacks = {}, !.listeners = {}]

-----------------------------------------------------------------------------
(* The resume cascade, per variable (libr8 enqueue_resume, sliced exactly   *)
(* like the abstract spec's 00-resume section). `ts` is the tasks value     *)
(* with the settled promise's task already fulfilled.                       *)

ResumeTasks(ps, ts, awaitedId, awaiterIds, tnow) ==
  [id \in DOMAIN ts |->
     IF /\ id \in awaiterIds
        \* TIMEOUT ALWAYS WINS: an expired awaiter is dead weight
        /\ id \in DOMAIN ps
        /\ ps[id].timeoutAt > tnow
     THEN
       LET t0 == ts[id] IN
       IF t0.state = "suspended" THEN
         [t0 EXCEPT !.state = "pending", !.resumes = {awaitedId}]
       ELSE IF t0.state \in {"pending", "acquired", "halted"} THEN
         [t0 EXCEPT !.resumes = @ \cup {awaitedId}]
       ELSE \* fulfilled
         t0
     ELSE ts[id]]

ResumeTaskTimeouts(ps, tts, ts, awaiterIds, tnow) ==
  LET retryTimeout == config.retryTimeout
      resumed == {id \in awaiterIds \cap DOMAIN ts :
                    /\ ts[id].state = "suspended"
                    /\ id \in DOMAIN ps
                    /\ ps[id].timeoutAt > tnow}
      keys == {<<id, 0>> : id \in resumed}
  IN [k \in DOMAIN tts \cup keys |->
        IF k \in keys THEN tnow + retryTimeout ELSE tts[k]]

ResumeMessages(ob, ps, ts, awaiterIds, tnow) ==
  LET resumed == {id \in awaiterIds \cap DOMAIN ts :
                    /\ ts[id].state = "suspended"
                    /\ id \in DOMAIN ps
                    /\ ps[id].timeoutAt > tnow}
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
(* The workflow blob (libr8 Workflow / blobfun Blob) and the timer index.   *)

EmptyWf == [promises        |-> [id \in {} |-> NULL],
            tasks           |-> [id \in {} |-> NULL],
            promiseTimeouts |-> [id \in {} |-> NULL],
            taskTimeouts    |-> [k \in {} |-> NULL],
            outbox          |-> [k \in {} |-> NULL]]

\* The due timeout entries of one workflow (blobfun DueKeys, authoritative
\* side): what the eager sweep still has to fire at instant tnow.
WfEligible(wf, tnow) ==
  {[type |-> "promise", id |-> id] :
     id \in {x \in DOMAIN wf.promiseTimeouts : wf.promiseTimeouts[x] <= tnow}}
  \cup
  {[type |-> "task", id |-> k[1], kind |-> k[2]] :
     k \in {x \in DOMAIN wf.taskTimeouts : wf.taskTimeouts[x] <= tnow}}

\* Swept: nothing due -- the guard under which Apply runs.
ShardSwept(wf, tnow) == WfEligible(wf, tnow) = {}

\* libr8 Workflow::next_deadline -- the earliest armed deadline, published
\* to the timer index as this workflow's marker.
NextDeadline(wf) ==
  LET ds == {wf.promiseTimeouts[id] : id \in DOMAIN wf.promiseTimeouts}
              \cup {wf.taskTimeouts[k] : k \in DOMAIN wf.taskTimeouts}
  IN IF ds = {} THEN NULL ELSE CHOOSE d \in ds : \A x \in ds : d <= x

MarkersOf(origin, wf) ==
  IF NextDeadline(wf) = NULL THEN {}
  ELSE {[deadline |-> NextDeadline(wf), origin |-> origin]}

\* Store-time reconciliation (blobfun Store diffs the before/after timer
\* projections; libr8 publishes the new marker before the CAS and deletes
\* the superseded one after -- idealized here as atomic and exact, the
\* real-world weakening being coverage: stale markers allowed, missing
\* markers not).
ReconcileMarkers(origin, wfOld, wfNew) ==
  (markers \ MarkersOf(origin, wfOld)) \cup MarkersOf(origin, wfNew)

-----------------------------------------------------------------------------
(* Timeout firings -- one due entry at a time (the decomposed sweep; also   *)
(* what a driver wake runs). Bodies mirror the abstract spec's timeout      *)
(* handlers, scoped to the entry's workflow.                                *)

OnPromiseTimeout(origin, id, tnow) ==
  LET wf == blobs[origin]
      p0 == GetPromise(wf.promises, id) IN
  IF p0 = NULL \/ p0.state # "pending" THEN
    UNCHANGED <<blobs, markers>>
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
        t == GetTask(wf.tasks, p.id)
        \* settlement scrub: p can never be resumed again
        scrubbed == [i \in DOMAIN wf.promises |->
                       IF wf.promises[i].state = "pending"
                       THEN [wf.promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                       ELSE wf.promises[i]]
        promises1 == SetPromise(scrubbed, p)
        tasks1 == IF t # NULL
                  THEN SetTask(wf.tasks, [t EXCEPT !.state = "fulfilled", !.pid = NULL,
                                                   !.ttl = NULL, !.resumes = {}])
                  ELSE wf.tasks
        lkeys == {<<p.id, a>> : a \in listeners}
        unblocked == [k \in DOMAIN wf.outbox \cup lkeys |->
                        IF k \in lkeys
                        THEN [address |-> k[2],
                              message |-> [type |-> "unblock",
                                           promise |-> PromiseToRecord(p)]]
                        ELSE wf.outbox[k]]
        wfNew == [promises        |-> promises1,
                  tasks           |-> ResumeTasks(promises1, tasks1, p.id, callbacks, tnow),
                  promiseTimeouts |-> DelPromiseTimeout(wf.promiseTimeouts, p.id),
                  taskTimeouts    |-> ResumeTaskTimeouts(
                                        promises1,
                                        IF t # NULL
                                        THEN DelTaskTimeout(wf.taskTimeouts, t.id)
                                        ELSE wf.taskTimeouts,
                                        tasks1, callbacks, tnow),
                  outbox          |-> ResumeMessages(unblocked,
                                                     promises1, tasks1, callbacks, tnow)]
    IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
       /\ markers' = ReconcileMarkers(origin, wf, wfNew)

OnTaskRetryTimeout(origin, id, tnow) ==
  LET retryTimeout == config.retryTimeout
      wf == blobs[origin]
      t == GetTask(wf.tasks, id) IN
  IF t = NULL \/ t.state # "pending" THEN
    UNCHANGED <<blobs, markers>>
  ELSE
    LET p == GetPromise(wf.promises, t.id)
        \* the abstract spec sends unconditionally (address "" when the
        \* promise has no target); blobfun/libr8 guard this send -- see the
        \* header. Mirrored on the spec for the refinement.
        wfNew == [wf EXCEPT
                    !.taskTimeouts = SetTaskTimeout(DelTaskTimeout(@, t.id),
                                                    t.id, 0, tnow + retryTimeout),
                    !.outbox = IF p = NULL THEN @
                               ELSE SendMsg(@,
                                      IF TagsGet(p.tags, "resonate:target") = NULL
                                      THEN "" ELSE TagsGet(p.tags, "resonate:target"),
                                      [type |-> "execute", taskId |-> t.id,
                                       version |-> t.version])]
    IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
       /\ markers' = ReconcileMarkers(origin, wf, wfNew)

OnTaskLeaseTimeout(origin, id, tnow) ==
  LET retryTimeout == config.retryTimeout
      wf == blobs[origin]
      t0 == GetTask(wf.tasks, id) IN
  IF t0 = NULL \/ t0.state # "acquired" THEN
    UNCHANGED <<blobs, markers>>
  ELSE
    LET t == [t0 EXCEPT !.state = "pending", !.pid = NULL, !.ttl = NULL]
        p == GetPromise(wf.promises, t.id)
        wfNew == [wf EXCEPT
                    !.tasks = SetTask(@, t),
                    !.taskTimeouts = SetTaskTimeout(DelTaskTimeout(@, t.id),
                                                    t.id, 0, tnow + retryTimeout),
                    !.outbox = IF p = NULL THEN @
                               ELSE SendMsg(@,
                                      IF TagsGet(p.tags, "resonate:target") = NULL
                                      THEN "" ELSE TagsGet(p.tags, "resonate:target"),
                                      [type |-> "execute", taskId |-> t.id,
                                       version |-> t.version])]
    IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
       /\ markers' = ReconcileMarkers(origin, wf, wfNew)

-----------------------------------------------------------------------------
(* Handlers. A mutation requires its blob swept, applies, and stores        *)
(* (commit + marker reconciliation). The pure reads (P-01 promise.get,      *)
(* P-06/T-11 search, T-01 task.get) answer by projection off the loaded     *)
(* blob without a store write: observations, not transitions.               *)

\* P-02 promise.create -- applied at an explicit origin so task.fence can
\* run it against the fence task's workflow (blobfun CreateOnWf).
PromiseCreateAt(origin, req) ==
  LET retryTimeout == config.retryTimeout
      wf == blobs[origin]
      p0 == GetPromise(wf.promises, req.id) IN
  /\ ShardSwept(wf, now)
  /\ IF p0 = NULL THEN
       IF req.timeoutAt > now THEN
         LET p == PromiseCreated(req)
             target == TagsGet(p.tags, "resonate:target")
             delay == TagsGet(p.tags, "resonate:delay")
             t == [id |-> p.id, state |-> "pending", version |-> 0,
                   ttl |-> NULL, pid |-> NULL, resumes |-> {}]
             \* write-through observation (libr8): every pending deadline is
             \* armed, not just external ones -- which coincides with the
             \* abstract spec's external-gated arming on this module's
             \* external-only requests.
             wfNew == [promises        |-> SetPromise(wf.promises, p),
                       tasks           |-> IF target = NULL THEN wf.tasks
                                           ELSE SetTask(wf.tasks, t),
                       promiseTimeouts |-> SetPromiseTimeout(wf.promiseTimeouts,
                                                             p.id, p.timeoutAt),
                       taskTimeouts    |-> IF target = NULL THEN wf.taskTimeouts
                                           ELSE IF delay = NULL
                                           THEN SetTaskTimeout(wf.taskTimeouts, t.id, 0,
                                                               now + retryTimeout)
                                           ELSE IF delay > now
                                           THEN SetTaskTimeout(wf.taskTimeouts, t.id, 0, delay)
                                           ELSE SetTaskTimeout(wf.taskTimeouts, t.id, 0,
                                                               now + retryTimeout),
                       outbox          |-> IF target = NULL THEN wf.outbox
                                           ELSE IF delay = NULL
                                           THEN SendMsg(wf.outbox, target,
                                                  [type |-> "execute", taskId |-> t.id,
                                                   version |-> t.version])
                                           ELSE IF delay > now THEN wf.outbox
                                           ELSE SendMsg(wf.outbox, target,
                                                  [type |-> "execute", taskId |-> t.id,
                                                   version |-> t.version])]
         IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
            /\ markers' = ReconcileMarkers(origin, wf, wfNew)
       ELSE
         LET p  == PromiseCreatedExpired(req)
             t  == [id |-> p.id, state |-> "fulfilled", version |-> 0,
                    ttl |-> NULL, pid |-> NULL, resumes |-> {}]
             wfNew == [wf EXCEPT
                         !.promises = SetPromise(@, p),
                         !.tasks = IF TagsHas(p.tags, "resonate:target")
                                   THEN SetTask(@, t) ELSE @]
         IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
            /\ markers' = ReconcileMarkers(origin, wf, wfNew)
     ELSE
       \* idempotent by id: no state effect
       UNCHANGED <<blobs, markers>>

\* P-03 promise.settle (blobfun SettleOnWf + TriggerSettlement; libr8
\* settle_cascade).
PromiseSettleAt(origin, req) ==
  LET wf == blobs[origin]
      p0 == GetPromise(wf.promises, req.id) IN
  /\ ShardSwept(wf, now)
  /\ IF p0 # NULL /\ p0.state = "pending" /\ p0.timeoutAt > now THEN
       LET listeners == p0.listeners
           callbacks == p0.callbacks
           p == PromiseSettled(p0, req)
           t == GetTask(wf.tasks, p.id)
           scrubbed == [i \in DOMAIN wf.promises |->
                          IF wf.promises[i].state = "pending"
                          THEN [wf.promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                          ELSE wf.promises[i]]
           promises1 == SetPromise(scrubbed, p)
           tasks1 == IF t # NULL
                     THEN SetTask(wf.tasks, [t EXCEPT !.state = "fulfilled", !.pid = NULL,
                                                      !.ttl = NULL, !.resumes = {}])
                     ELSE wf.tasks
           lkeys == {<<p.id, a>> : a \in listeners}
           unblocked == [k \in DOMAIN wf.outbox \cup lkeys |->
                           IF k \in lkeys
                           THEN [address |-> k[2],
                                 message |-> [type |-> "unblock",
                                              promise |-> PromiseToRecord(p)]]
                           ELSE wf.outbox[k]]
           wfNew == [promises        |-> promises1,
                     tasks           |-> ResumeTasks(promises1, tasks1, p.id, callbacks, now),
                     promiseTimeouts |-> DelPromiseTimeout(wf.promiseTimeouts, p.id),
                     taskTimeouts    |-> ResumeTaskTimeouts(
                                           promises1,
                                           IF t # NULL
                                           THEN DelTaskTimeout(wf.taskTimeouts, t.id)
                                           ELSE wf.taskTimeouts,
                                           tasks1, callbacks, now),
                     outbox          |-> ResumeMessages(unblocked,
                                                        promises1, tasks1, callbacks, now)]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)
     ELSE
       \* missing, already settled, or expired-pending: no state effect
       UNCHANGED <<blobs, markers>>

\* P-04 promise.register_callback -- same-origin (libr8 validates it; the
\* awaiter is looked up in the awaited promise's workflow). A promise
\* cannot await itself (422).
PromiseRegisterCallback(req) ==
  LET origin == OriginOf(req.awaited)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF /\ req.awaited # req.awaiter
        /\ req.awaited \in DOMAIN wf.promises
        /\ req.awaiter \in DOMAIN wf.promises
        /\ TagsHas(wf.promises[req.awaiter].tags, "resonate:target")
        /\ wf.promises[req.awaited].state = "pending"
        /\ wf.promises[req.awaited].timeoutAt > now
     THEN
       LET wfNew == [wf EXCEPT
                       !.promises = IF wf.promises[req.awaiter].state = "pending"
                                       /\ wf.promises[req.awaiter].timeoutAt > now
                                    THEN SetPromise(@, PromiseAddCallback(
                                             wf.promises[req.awaited], req.awaiter))
                                    ELSE @]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)
     ELSE
       UNCHANGED <<blobs, markers>>

\* P-05 promise.register_listener
PromiseRegisterListener(req) ==
  LET origin == OriginOf(req.awaited)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF /\ req.awaited \in DOMAIN wf.promises
        /\ wf.promises[req.awaited].state = "pending"
        /\ wf.promises[req.awaited].timeoutAt > now
     THEN
       LET wfNew == [wf EXCEPT
                       !.promises = SetPromise(@, PromiseAddListener(
                                        wf.promises[req.awaited], req.address))]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)
     ELSE
       UNCHANGED <<blobs, markers>>

\* T-02 task.create
TaskCreate(req) ==
  LET a  == req.action
      origin == OriginOf(a.id)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF a.id \notin DOMAIN wf.promises THEN
       \* untargeted action: unroutable (422; mirrors the abstract spec)
       IF ~TagsHas(a.tags, "resonate:target") THEN
         UNCHANGED <<blobs, markers>>
       ELSE IF a.timeoutAt > now THEN
         LET p == PromiseCreated(a)
             t == [id |-> p.id, state |-> "acquired", version |-> 1,
                   ttl |-> req.ttl, pid |-> req.pid, resumes |-> {}]
             wfNew == [promises        |-> SetPromise(wf.promises, p),
                       tasks           |-> SetTask(wf.tasks, t),
                       promiseTimeouts |-> SetPromiseTimeout(wf.promiseTimeouts,
                                                             p.id, p.timeoutAt),
                       taskTimeouts    |-> SetTaskTimeout(wf.taskTimeouts, t.id, 1,
                                                          now + req.ttl),
                       outbox          |-> wf.outbox]
         IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
            /\ markers' = ReconcileMarkers(origin, wf, wfNew)
       ELSE
         LET p  == PromiseCreatedExpired(a)
             t  == [id |-> p.id, state |-> "fulfilled", version |-> 0,
                    ttl |-> NULL, pid |-> NULL, resumes |-> {}]
             wfNew == [wf EXCEPT !.promises = SetPromise(@, p),
                                 !.tasks = SetTask(@, t)]
         IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
            /\ markers' = ReconcileMarkers(origin, wf, wfNew)
     ELSE
       IF /\ TagsHas(wf.promises[a.id].tags, "resonate:target")
          /\ a.id \in DOMAIN wf.tasks
          /\ wf.tasks[a.id].state = "pending"
       THEN
         LET t == [wf.tasks[a.id] EXCEPT !.state = "acquired", !.version = @ + 1,
                                         !.ttl = req.ttl, !.pid = req.pid,
                                         !.resumes = {}]
             wfNew == [wf EXCEPT
                         !.tasks = SetTask(@, t),
                         !.taskTimeouts = SetTaskTimeout(DelTaskTimeout(@, t.id),
                                                         t.id, 1, now + req.ttl)]
         IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
            /\ markers' = ReconcileMarkers(origin, wf, wfNew)
       ELSE
         \* fulfilled (idempotent), non-pending, missing task, or untargeted
         UNCHANGED <<blobs, markers>>

\* T-03 task.acquire
TaskAcquire(req) ==
  LET origin == OriginOf(req.id)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF /\ req.id \in DOMAIN wf.tasks
        /\ req.id \in DOMAIN wf.promises
        /\ wf.tasks[req.id].state = "pending"
        /\ wf.promises[req.id].state = "pending"
        /\ wf.promises[req.id].timeoutAt > now
        /\ wf.tasks[req.id].version = req.version
     THEN
       LET t == [wf.tasks[req.id] EXCEPT !.state = "acquired", !.version = @ + 1,
                                         !.ttl = req.ttl, !.pid = req.pid,
                                         !.resumes = {}]
           wfNew == [wf EXCEPT
                       !.tasks = SetTask(@, t),
                       !.taskTimeouts = SetTaskTimeout(DelTaskTimeout(@, t.id),
                                                       t.id, 1, now + req.ttl)]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)
     ELSE
       UNCHANGED <<blobs, markers>>

\* The fenced guard (task acquired, promise live, version match) on one
\* workflow, shared by fence, fulfill, and release.
WfFenceOk(wf, id, version) ==
  /\ id \in DOMAIN wf.tasks
  /\ id \in DOMAIN wf.promises
  /\ wf.tasks[id].state = "acquired"
  /\ wf.promises[id].state = "pending"
  /\ wf.promises[id].timeoutAt > now
  /\ wf.tasks[id].version = version

\* T-04 task.fence -- the inner action runs against the FENCE task's
\* workflow (blobfun applies CreateOnWf/SettleOnWf to the fence's shard;
\* same-origin makes that the inner id's shard too).
TaskFence(req) ==
  LET origin == OriginOf(req.id) IN
  IF ~WfFenceOk(blobs[origin], req.id, req.version) THEN
    /\ ShardSwept(blobs[origin], now)
    /\ UNCHANGED <<blobs, markers>>
  ELSE IF req.action.type = "create" THEN
    PromiseCreateAt(origin, req.action.req)
  ELSE
    PromiseSettleAt(origin, req.action.req)

\* T-05 task.heartbeat -- routed by the FIRST ref's origin; a worker
\* heartbeats per shard (same-origin). Empty list: unroutable, pure no-op.
TaskHeartbeat(req) ==
  IF req.tasks = <<>> THEN
    UNCHANGED <<blobs, markers>>
  ELSE
    LET origin == OriginOf(Head(req.tasks).id)
        wf == blobs[origin] IN
    /\ ShardSwept(wf, now)
    /\ LET refs == {req.tasks[i] : i \in DOMAIN req.tasks}
           valid == {r \in refs :
                       /\ r.id \in DOMAIN wf.tasks
                       /\ wf.tasks[r.id].state = "acquired"
                       /\ wf.tasks[r.id].version = r.version
                       /\ wf.tasks[r.id].pid = req.pid
                       /\ r.id \in DOMAIN wf.promises
                       /\ wf.promises[r.id].state = "pending"
                       /\ wf.promises[r.id].timeoutAt > now}
           ids == {r.id : r \in valid}
           wfNew == [wf EXCEPT !.taskTimeouts =
                       [k \in {x \in DOMAIN @ : x[1] \notin ids}
                                \cup {<<id, 1>> : id \in ids} |->
                          IF k[1] \in ids
                          THEN now + (IF wf.tasks[k[1]].ttl = NULL
                                      THEN 0 ELSE wf.tasks[k[1]].ttl)
                          ELSE @[k]]]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)

\* T-06 task.suspend -- awaited promises are looked up in the task's
\* workflow (same-origin). Rejected (422): an empty actions list, an
\* action awaiting the task's own promise, or a missing awaited promise.
TaskSuspend(req) ==
  LET origin == OriginOf(req.id)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF ~(/\ req.actions # <<>>
          /\ req.id \in DOMAIN wf.tasks
          /\ req.id \in DOMAIN wf.promises
          /\ wf.tasks[req.id].state = "acquired"
          /\ wf.promises[req.id].state = "pending"
          /\ wf.promises[req.id].timeoutAt > now
          /\ wf.tasks[req.id].version = req.version
          /\ \A i \in DOMAIN req.actions : req.actions[i].awaited # req.id
          /\ \A i \in DOMAIN req.actions :
               req.actions[i].awaited \in DOMAIN wf.promises)
     THEN
       UNCHANGED <<blobs, markers>>
     ELSE
       LET settled == \E i \in DOMAIN req.actions :
                        LET pa == wf.promises[req.actions[i].awaited]
                        IN pa.state # "pending" \/ pa.timeoutAt <= now
       IN
       IF settled THEN
         \* declined (300): re-check instead of parking
         LET wfNew == [wf EXCEPT !.tasks = SetTask(@, [wf.tasks[req.id]
                                                        EXCEPT !.resumes = {}])]
         IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
            /\ markers' = ReconcileMarkers(origin, wf, wfNew)
       ELSE
         LET awaitedIds == {req.actions[i].awaited : i \in DOMAIN req.actions}
             wfNew == [wf EXCEPT
                         !.promises = [id \in DOMAIN @ |->
                                         IF id \in awaitedIds
                                         THEN PromiseAddCallback(@[id], req.id)
                                         ELSE @[id]],
                         !.tasks = SetTask(@, [wf.tasks[req.id]
                                                EXCEPT !.state = "suspended",
                                                       !.pid = NULL, !.ttl = NULL,
                                                       !.resumes = {}]),
                         !.taskTimeouts = DelTaskTimeout(@, req.id)]
         IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
            /\ markers' = ReconcileMarkers(origin, wf, wfNew)

\* T-07 task.fulfill
TaskFulfill(req) ==
  LET origin == OriginOf(req.id)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF ~WfFenceOk(wf, req.id, req.version) THEN
       UNCHANGED <<blobs, markers>>
     ELSE
       LET p0 == wf.promises[req.id]
           listeners == p0.listeners
           callbacks == p0.callbacks
           p == PromiseSettled(p0, req.action)
           scrubbed == [i \in DOMAIN wf.promises |->
                          IF wf.promises[i].state = "pending"
                          THEN [wf.promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                          ELSE wf.promises[i]]
           promises1 == SetPromise(scrubbed, p)
           tasks1 == SetTask(wf.tasks, [wf.tasks[req.id]
                                         EXCEPT !.state = "fulfilled",
                                                !.pid = NULL, !.ttl = NULL,
                                                !.resumes = {}])
           lkeys == {<<p.id, a>> : a \in listeners}
           unblocked == [k \in DOMAIN wf.outbox \cup lkeys |->
                           IF k \in lkeys
                           THEN [address |-> k[2],
                                 message |-> [type |-> "unblock",
                                              promise |-> PromiseToRecord(p)]]
                           ELSE wf.outbox[k]]
           wfNew == [promises        |-> promises1,
                     tasks           |-> ResumeTasks(promises1, tasks1, p.id, callbacks, now),
                     promiseTimeouts |-> DelPromiseTimeout(wf.promiseTimeouts, p.id),
                     taskTimeouts    |-> ResumeTaskTimeouts(
                                           promises1,
                                           DelTaskTimeout(wf.taskTimeouts, req.id),
                                           tasks1, callbacks, now),
                     outbox          |-> ResumeMessages(unblocked,
                                                        promises1, tasks1, callbacks, now)]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)

\* T-08 task.release
TaskRelease(req) ==
  LET origin == OriginOf(req.id)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF ~WfFenceOk(wf, req.id, req.version) THEN
       UNCHANGED <<blobs, markers>>
     ELSE
       LET retryTimeout == config.retryTimeout
           t == [wf.tasks[req.id] EXCEPT !.state = "pending",
                                         !.pid = NULL, !.ttl = NULL]
           wfNew == [wf EXCEPT
                       !.tasks = SetTask(@, t),
                       !.taskTimeouts = SetTaskTimeout(DelTaskTimeout(@, t.id),
                                                       t.id, 0, now + retryTimeout),
                       !.outbox = SendMsg(@,
                                    IF TagsGet(wf.promises[req.id].tags,
                                               "resonate:target") = NULL
                                    THEN ""
                                    ELSE TagsGet(wf.promises[req.id].tags,
                                                 "resonate:target"),
                                    [type |-> "execute", taskId |-> t.id,
                                     version |-> t.version])]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)

\* T-09 task.halt
TaskHalt(req) ==
  LET origin == OriginOf(req.id)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF req.id \in DOMAIN wf.tasks
        /\ wf.tasks[req.id].state \notin {"fulfilled", "halted"}
     THEN
       LET wfNew == [wf EXCEPT
                       !.tasks = SetTask(@, [wf.tasks[req.id]
                                              EXCEPT !.state = "halted",
                                                     !.pid = NULL, !.ttl = NULL]),
                       !.taskTimeouts = DelTaskTimeout(@, req.id)]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)
     ELSE
       UNCHANGED <<blobs, markers>>

\* T-10 task.continue
TaskContinue(req) ==
  LET origin == OriginOf(req.id)
      wf == blobs[origin] IN
  /\ ShardSwept(wf, now)
  /\ IF /\ req.id \in DOMAIN wf.tasks
        /\ wf.tasks[req.id].state = "halted"
        /\ req.id \in DOMAIN wf.promises
     THEN
       LET retryTimeout == config.retryTimeout
           t == [wf.tasks[req.id] EXCEPT !.state = "pending"]
           wfNew == [wf EXCEPT
                       !.tasks = SetTask(@, t),
                       !.taskTimeouts = SetTaskTimeout(@, t.id, 0, now + retryTimeout),
                       !.outbox = SendMsg(@,
                                    IF TagsGet(wf.promises[req.id].tags,
                                               "resonate:target") = NULL
                                    THEN ""
                                    ELSE TagsGet(wf.promises[req.id].tags,
                                                 "resonate:target"),
                                    [type |-> "execute", taskId |-> t.id,
                                     version |-> t.version])]
       IN /\ blobs' = [blobs EXCEPT ![origin] = wfNew]
          /\ markers' = ReconcileMarkers(origin, wf, wfNew)
     ELSE
       UNCHANGED <<blobs, markers>>

-----------------------------------------------------------------------------
(* Model: requests drawn nondeterministically. External-only tags and       *)
(* same-origin requests are the environment assumptions (see the header).   *)

Times == 0..(MaxTime + 1)

Versions == 0..3

TTLs == {2}

Values == {[headers |-> <<>>, data |-> NULL]}
            \cup {[headers |-> <<>>, data |-> d] : d \in DataValues}

\* External-only: every promise carries resonate:timer or resonate:target
\* (a strict subset of the abstract spec's TagOptions).
TagOptions ==
  {<<<<"resonate:timer", "true">>>>}
    \cup {<<<<"resonate:target", a>>>> : a \in Addresses}
    \cup {<<<<"resonate:target", a>>, <<"resonate:delay", d>>>> :
            a \in Addresses, d \in {2}}

SettleStates == {"resolved", "rejected", "rejected_canceled"}

PromiseCreateReqs ==
  [id : PromiseIds, timeoutAt : Times, param : Values, tags : TagOptions]

PromiseSettleReqs == [id : PromiseIds, state : SettleStates, value : Values]

\* same-origin: the awaiter is registered in the awaited promise's workflow
\* (libr8 same_origin()).
RegisterCallbackReqs ==
  {r \in [awaited : PromiseIds, awaiter : PromiseIds] :
     OriginOf(r.awaited) = OriginOf(r.awaiter)}

TaskRefs == [id : PromiseIds, version : Versions]

\* same-origin: a fence acts within its task's workflow.
FenceActions == {[type |-> "create", req |-> r] : r \in PromiseCreateReqs}
                  \cup {[type |-> "settle", req |-> r] : r \in PromiseSettleReqs}

TaskFenceReqs ==
  {r \in [id : PromiseIds, version : Versions, action : FenceActions] :
     OriginOf(r.action.req.id) = OriginOf(r.id)}

\* same-origin: a worker heartbeats per shard.
HeartbeatLists == {<<>>}
                    \cup {<<r>> : r \in TaskRefs}
                    \cup {<<r1, r2>> : r1 \in TaskRefs, r2 \in TaskRefs}

TaskHeartbeatReqs ==
  {r \in [pid : Pids, tasks : HeartbeatLists] :
     \A i, j \in DOMAIN r.tasks :
       OriginOf(r.tasks[i].id) = OriginOf(r.tasks[j].id)}

\* same-origin: a task suspends on promises of its own workflow.
SuspendLists == {<<>>}
                  \cup {<<a>> : a \in RegisterCallbackReqs}
                  \cup {<<a1, a2>> : a1 \in RegisterCallbackReqs,
                                     a2 \in RegisterCallbackReqs}

TaskSuspendReqs ==
  {r \in [id : PromiseIds, version : Versions, actions : SuspendLists] :
     \A i \in DOMAIN r.actions :
       OriginOf(r.actions[i].awaited) = OriginOf(r.id)}

-----------------------------------------------------------------------------
(* Actions. Naming: X(req) is the handler (a parameterized action),         *)
(* XAction the closed Next disjunct -- the environment submits some         *)
(* request, the driver fires a due timeout, or the clock advances.          *)

PromiseCreateAction ==
  \E req \in PromiseCreateReqs :
    PromiseCreateAt(OriginOf(req.id), req) /\ UNCHANGED now

PromiseSettleAction ==
  \E req \in PromiseSettleReqs :
    PromiseSettleAt(OriginOf(req.id), req) /\ UNCHANGED now

PromiseRegisterCallbackAction ==
  \E req \in RegisterCallbackReqs :
    PromiseRegisterCallback(req) /\ UNCHANGED now

PromiseRegisterListenerAction ==
  \E req \in [awaited : PromiseIds, address : Addresses] :
    PromiseRegisterListener(req) /\ UNCHANGED now

TaskCreateAction ==
  \E req \in [pid : Pids, ttl : TTLs, action : PromiseCreateReqs] :
    TaskCreate(req) /\ UNCHANGED now

TaskAcquireAction ==
  \E req \in [id : PromiseIds, version : Versions, pid : Pids, ttl : TTLs] :
    TaskAcquire(req) /\ UNCHANGED now

TaskFenceAction ==
  \E req \in TaskFenceReqs :
    TaskFence(req) /\ UNCHANGED now

TaskHeartbeatAction ==
  \E req \in TaskHeartbeatReqs :
    TaskHeartbeat(req) /\ UNCHANGED now

TaskSuspendAction ==
  \E req \in TaskSuspendReqs :
    TaskSuspend(req) /\ UNCHANGED now

TaskFulfillAction ==
  \E req \in [id : PromiseIds, version : Versions, action : PromiseSettleReqs] :
    TaskFulfill(req) /\ UNCHANGED now

TaskReleaseAction ==
  \E req \in [id : PromiseIds, version : Versions] :
    TaskRelease(req) /\ UNCHANGED now

TaskHaltAction ==
  \E req \in [id : PromiseIds] : TaskHalt(req) /\ UNCHANGED now

TaskContinueAction ==
  \E req \in [id : PromiseIds] : TaskContinue(req) /\ UNCHANGED now

\* The decomposed sweep / driver wake: fire ONE due timeout entry of one
\* workflow at the current instant. The real commit runs these to
\* exhaustion before Apply (the ShardSwept guard); the real sweep fires
\* them in a fixed priority order (libr8: promise, lease, retry) -- one of
\* the schedules this action's nondeterminism allows.
SweepDueAction ==
  \E origin \in Origins :
    \E entry \in WfEligible(blobs[origin], now) :
      /\ IF entry.type = "promise" THEN OnPromiseTimeout(origin, entry.id, now)
         ELSE IF entry.kind = 0 THEN OnTaskRetryTimeout(origin, entry.id, now)
         ELSE OnTaskLeaseTimeout(origin, entry.id, now)
      /\ UNCHANGED now

AdvanceClockAction ==
  \E newNow \in (now + 1)..MaxTime :
    /\ now' = newNow
    /\ UNCHANGED <<blobs, markers>>

-----------------------------------------------------------------------------

Init == /\ blobs = [o \in Origins |-> EmptyWf]
        /\ markers = {}
        /\ now = 0

Next == \/ PromiseCreateAction
        \/ PromiseSettleAction
        \/ PromiseRegisterCallbackAction
        \/ PromiseRegisterListenerAction
        \/ TaskCreateAction
        \/ TaskAcquireAction
        \/ TaskFenceAction
        \/ TaskHeartbeatAction
        \/ TaskSuspendAction
        \/ TaskFulfillAction
        \/ TaskReleaseAction
        \/ TaskHaltAction
        \/ TaskContinueAction
        \/ SweepDueAction
        \/ AdvanceClockAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants -- the blob-specific machinery.                               *)

\* The timer index is exact: precisely each workflow's next-deadline marker
\* (blobfun TimersExact, idealized; the real weakening is coverage).
MarkersExact == markers = UNION {MarkersOf(o, blobs[o]) : o \in Origins}

\* Armed (libr8): every pending promise has its deadline armed in-blob.
Armed ==
  \A o \in Origins : \A id \in DOMAIN blobs[o].promises :
    blobs[o].promises[id].state = "pending" =>
      /\ id \in DOMAIN blobs[o].promiseTimeouts
      /\ blobs[o].promiseTimeouts[id] = blobs[o].promises[id].timeoutAt

\* Shard integrity: an object lives in the blob its id routes to (the
\* outbox clause is what routes outbox keys in the abstraction below).
ShardIntegrity ==
  \A o \in Origins :
    /\ \A id \in DOMAIN blobs[o].promises : OriginOf(id) = o
    /\ \A id \in DOMAIN blobs[o].tasks : OriginOf(id) = o
    /\ \A id \in DOMAIN blobs[o].promiseTimeouts : OriginOf(id) = o
    /\ \A k \in DOMAIN blobs[o].taskTimeouts : OriginOf(k[1]) = o
    /\ \A k \in DOMAIN blobs[o].outbox : OriginOf(k[1]) = o

Constraint == \A o \in Origins : \A id \in DOMAIN blobs[o].tasks :
                blobs[o].tasks[id].version <= 3


-----------------------------------------------------------------------------
(* THE REFINEMENT:  BlobServer  =>  Server.                                 *)
(*                                                                          *)
(* The abstraction function is the WITH mapping below: union the workflow   *)
(* shards and forget the sharding. Under the order quotient this is exact   *)
(* for ANY number of origins -- an object (or outbox key, whose first       *)
(* component is always an id) is found in the blob its id routes to         *)
(* (ShardIntegrity).                                                        *)
(*                                                                          *)
(* Every micro-step maps to one abstract step: SweepDueAction and AdvanceClockAction    *)
(* to TickAction (fire one eligible entry / pure clock advance), each       *)
(* handler to its abstract handler (the ShardSwept guard makes the          *)
(* projection branches dead, so blob's post-sweep bodies coincide with the  *)
(* abstract ones).                                                          *)

\* Union the shards: an object (or outbox key, whose first component is
\* always an id) lives in the blob its id routes to (ShardIntegrity).
AbsPromises ==
  [id \in UNION {DOMAIN blobs[o].promises : o \in Origins} |->
     blobs[OriginOf(id)].promises[id]]

AbsTasks ==
  [id \in UNION {DOMAIN blobs[o].tasks : o \in Origins} |->
     blobs[OriginOf(id)].tasks[id]]

AbsPromiseTimeouts ==
  [id \in UNION {DOMAIN blobs[o].promiseTimeouts : o \in Origins} |->
     blobs[OriginOf(id)].promiseTimeouts[id]]

AbsTaskTimeouts ==
  [k \in UNION {DOMAIN blobs[o].taskTimeouts : o \in Origins} |->
     blobs[OriginOf(k[1])].taskTimeouts[k]]

AbsOutbox ==
  [k \in UNION {DOMAIN blobs[o].outbox : o \in Origins} |->
     blobs[OriginOf(k[1])].outbox[k]]

\* The default routing: every id lives in the one workflow. TwoOriginMap
\* splits p1 from the rest (see BlobTwoOrigins.cfg).
TheOrigin == CHOOSE o \in Origins : TRUE

DefaultOriginMap == [id \in PromiseIds |-> TheOrigin]

TwoOriginMap == [id \in PromiseIds |-> IF id = "p1" THEN "wf1" ELSE "wf2"]

Abs == INSTANCE Server
         WITH promises        <- AbsPromises,
              tasks           <- AbsTasks,
              promiseTimeouts <- AbsPromiseTimeouts,
              taskTimeouts    <- AbsTaskTimeouts,
              outbox          <- AbsOutbox
         \* now and all constants map by name.

Refinement == Abs!Spec

=============================================================================
