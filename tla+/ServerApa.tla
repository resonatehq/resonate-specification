----------------------------- MODULE ServerApa -----------------------------
(* The abstract Server spec in Apalache's typed fragment, for symbolic      *)
(* (SMT) checking. Derived from Server.tla with the adaptations Apalache's  *)
(* type system and fragment force:                                          *)
(*                                                                          *)
(*   - Option types become sentinels: settledAt/ttl/delay = -1, pid = "",   *)
(*     an absent tag reads as "" (which collapses Lean's `getD ""` -- the   *)
(*     spec never distinguishes an absent target from an empty one, and no  *)
(*     generated tag value is "").                                          *)
(*   - Heterogeneous records become uniform: outbox entries flatten the     *)
(*     Message variants (mtype = "execute" | "unblock", unused fields       *)
(*     sentineled); outbox keys are <<id, address>> with address = "" for   *)
(*     execute keys; tick entries carry kind = -1 for promise timeouts;     *)
(*     fence actions flatten the create/settle payloads into one record.    *)
(*   - TagsGet's first-match CHOOSE becomes a left fold.                    *)
(*   - `res` is dropped: heterogeneous response shapes would need the       *)
(*     Variants module, and the reads/searches (pure observations) with it. *)
(*     This variant checks STATE evolution; response correspondence lives   *)
(*     in the TLC refinement (BlobServer.tla).                              *)
(*   - No CONSTRAINT: Apalache bounds exploration by --length instead      *)
(*     (task versions may grow with depth, symbolically unproblematic).     *)
(*                                                                          *)
(* Checked invariants (states the protocol maintains):                      *)
(*   InvSettledAt        pending <=> not settled                            *)
(*   InvPromiseTimeouts  armed entries: pending promise, exact deadline     *)
(*   InvTaskTimeouts     kind 0 only for pending, kind 1 only for acquired  *)
(*   InvTaskHasPromise   every task shares its id with a promise            *)
EXTENDS Integers, Sequences, Apalache

(*
  @typeAlias: tags = Seq(<<Str, Str>>);
  @typeAlias: value = { headers: Seq(<<Str, Str>>), data: Str };
  @typeAlias: promise = { id: Str, state: Str, param: $value, value: $value,
                          tags: Seq(<<Str, Str>>), timeoutAt: Int,
                          createdAt: Int, settledAt: Int,
                          callbacks: Set(Str), listeners: Set(Str) };
  @typeAlias: prec = { id: Str, state: Str, param: $value, value: $value,
                       tags: Seq(<<Str, Str>>), timeoutAt: Int,
                       createdAt: Int, settledAt: Int };
  @typeAlias: task = { id: Str, state: Str, version: Int, ttl: Int,
                       pid: Str, resumes: Set(Str) };
  @typeAlias: entry = { address: Str, mtype: Str, taskId: Str, version: Int,
                        promise: $prec };
*)
ServerApaAliases == TRUE

CONSTANTS
  \* @type: Set(Str);
  PromiseIds,
  \* @type: Set(Str);
  Pids,
  \* @type: Set(Str);
  Addresses,
  \* @type: Set(Str);
  DataValues,
  \* @type: Int;
  MaxTime,
  \* @type: Int;
  RetryTimeout

VARIABLES
  \* @type: Str -> $promise;
  promises,
  \* @type: Str -> $task;
  tasks,
  \* @type: Str -> Int;
  promiseTimeouts,
  \* @type: <<Str, Int>> -> Int;
  taskTimeouts,
  \* @type: <<Str, Str>> -> $entry;
  outbox,
  \* @type: Int;
  now

serverVars == <<promises, tasks, promiseTimeouts, taskTimeouts, outbox>>

vars == <<promises, tasks, promiseTimeouts, taskTimeouts, outbox, now>>

config == [retryTimeout |-> RetryTimeout]

\* First match wins (Lean list lookup); "" when absent. No generated tag
\* value is "", so the sentinel is unambiguous.
\* @type: (Seq(<<Str, Str>>), Str) => Str;
TagsGet(t, k) ==
  LET \* @type: (Str, <<Str, Str>>) => Str;
      Pick(acc, pr) == IF acc # "" THEN acc
                       ELSE IF pr[1] = k THEN pr[2] ELSE acc
  IN ApaFoldSeqLeft(Pick, "", t)

\* @type: ($tags, Str) => Bool;
TagsHas(t, k) == TagsGet(t, k) # ""

\* @type: $tags => Bool;
TagsIsTimer(t) == TagsGet(t, "resonate:timer") = "true"

\* Lean's ParseNat / toNat!, total over the model's delay values.
\* @type: Str => Int;
ParseNat(s) == IF s = "2" THEN 2 ELSE 0

\* @type: $promise => $prec;
PromiseToRecord(p) ==
  [id        |-> p.id,
   state     |-> p.state,
   param     |-> p.param,
   value     |-> p.value,
   tags      |-> p.tags,
   timeoutAt |-> p.timeoutAt,
   createdAt |-> p.createdAt,
   settledAt |-> p.settledAt]

\* @type: $promise => Bool;
PromiseIsTimer(p) == TagsIsTimer(p.tags)

\* @type: $promise => Bool;
PromiseExternal(p) == TagsHas(p.tags, "resonate:target") \/ PromiseIsTimer(p)

\* @type: ($promise, Str) => $promise;
PromiseAddCallback(p, awaiterId) ==
  [p EXCEPT !.callbacks = @ \union {awaiterId}]

\* @type: ($promise, Str) => $promise;
PromiseAddListener(p, address) ==
  [p EXCEPT !.listeners = @ \union {address}]

\* @type: $value;
EmptyValue == [headers |-> <<>>, data |-> ""]

\* @type: $prec;
NoPromiseRec ==
  [id |-> "", state |-> "", param |-> EmptyValue, value |-> EmptyValue,
   tags |-> <<>>, timeoutAt |-> -1, createdAt |-> -1, settledAt |-> -1]

\* Message constructors, flattened (mtype selects; unused fields sentineled).
\* @type: (Str, Int) => $entry;
ExecuteMsg(taskId, version) ==
  [address |-> "", mtype |-> "execute", taskId |-> taskId,
   version |-> version, promise |-> NoPromiseRec]

\* @type: $prec => $entry;
UnblockMsg(prec) ==
  [address |-> "", mtype |-> "unblock", taskId |-> "",
   version |-> -1, promise |-> prec]

\* The keyed outbox: one outstanding execute per task (key <<id, "">>), one
\* outstanding unblock per (promise, address).
\* @type: $entry => <<Str, Str>>;
OutboxKey(e) ==
  IF e.mtype = "execute" THEN <<e.taskId, "">> ELSE <<e.promise.id, e.address>>

\* @type: (Str -> $promise, $promise) => (Str -> $promise);
SetPromise(ps, p) ==
  [id \in DOMAIN ps \union {p.id} |-> IF id = p.id THEN p ELSE ps[id]]

\* @type: (Str -> $task, $task) => (Str -> $task);
SetTask(ts, t) ==
  [id \in DOMAIN ts \union {t.id} |-> IF id = t.id THEN t ELSE ts[id]]

\* @type: (Str -> Int, Str, Int) => (Str -> Int);
SetPromiseTimeout(pts, id, timeout) ==
  [x \in DOMAIN pts \union {id} |-> IF x = id THEN timeout ELSE pts[x]]

\* @type: (Str -> Int, Str) => (Str -> Int);
DelPromiseTimeout(pts, id) == [x \in DOMAIN pts \ {id} |-> pts[x]]

\* @type: (<<Str, Int>> -> Int, Str, Int, Int) => (<<Str, Int>> -> Int);
SetTaskTimeout(tts, id, kind, timeout) ==
  [k \in DOMAIN tts \union {<<id, kind>>} |->
     IF k = <<id, kind>> THEN timeout ELSE tts[k]]

\* @type: (<<Str, Int>> -> Int, Str) => (<<Str, Int>> -> Int);
DelTaskTimeout(tts, id) == [k \in {x \in DOMAIN tts : x[1] # id} |-> tts[k]]

\* @type: (<<Str, Str>> -> $entry, Str, $entry) => (<<Str, Str>> -> $entry);
SetMessage(ob, address, msg) ==
  LET entry == [msg EXCEPT !.address = address]
      key   == OutboxKey(entry)
  IN [k \in DOMAIN ob \union {key} |-> IF k = key THEN entry ELSE ob[k]]

-----------------------------------------------------------------------------
(* The resume cascade, per variable (00-resume). `ts` has the settled       *)
(* promise's task already fulfilled, so a self-callback is a no-op.         *)

\* @type: (Str -> $task, Str, Set(Str)) => (Str -> $task);
ResumeTasks(ts, awaitedId, awaiterIds) ==
  [id \in DOMAIN ts |->
     IF id \in awaiterIds THEN
       LET t0 == ts[id] IN
       IF t0.state = "suspended" THEN
         [t0 EXCEPT !.state = "pending", !.resumes = {awaitedId}]
       ELSE IF t0.state \in {"pending", "acquired", "halted"} THEN
         [t0 EXCEPT !.resumes = @ \union {awaitedId}]
       ELSE \* fulfilled
         t0
     ELSE ts[id]]

\* @type: (<<Str, Int>> -> Int, Str -> $task, Set(Str), Int) => (<<Str, Int>> -> Int);
ResumeTaskTimeouts(tts, ts, awaiterIds, tnow) ==
  LET retryTimeout == config.retryTimeout
      resumed == {id \in awaiterIds \intersect DOMAIN ts :
                    ts[id].state = "suspended"}
      keys == {<<id, 0>> : id \in resumed}
  IN [k \in DOMAIN tts \union keys |->
        IF k \in keys THEN tnow + retryTimeout ELSE tts[k]]

\* @type: (<<Str, Str>> -> $entry, Str -> $promise, Str -> $task, Set(Str)) => (<<Str, Str>> -> $entry);
ResumeMessages(ob, ps, ts, awaiterIds) ==
  LET resumed == {id \in awaiterIds \intersect DOMAIN ts :
                    ts[id].state = "suspended"}
      targeted == {id \in resumed :
                     id \in DOMAIN ps /\ TagsGet(ps[id].tags, "resonate:target") # ""}
      \* @type: Set(<<Str, Str>>);
      keys == {<<id, "">> : id \in targeted}
  IN [k \in DOMAIN ob \union keys |->
        IF k \in keys
        THEN [address |-> TagsGet(ps[k[1]].tags, "resonate:target"),
              mtype |-> "execute", taskId |-> k[1],
              version |-> ts[k[1]].version, promise |-> NoPromiseRec]
        ELSE ob[k]]

-----------------------------------------------------------------------------
(* Timeout handlers (02-timeouts), fired one at a time by the tick.         *)

\* @type: (Str, Int) => Bool;
OnPromiseTimeout(id, tnow) ==
  IF id \notin DOMAIN promises THEN
    UNCHANGED serverVars
  ELSE IF promises[id].state # "pending" THEN
    UNCHANGED serverVars
  ELSE
    LET p0 == promises[id]
        listeners == p0.listeners
        callbacks == p0.callbacks
        p == IF PromiseIsTimer(p0)
             THEN [p0 EXCEPT !.state = "resolved",
                             !.settledAt = p0.timeoutAt,
                             !.callbacks = {}, !.listeners = {}]
             ELSE [p0 EXCEPT !.state = "rejected_timedout",
                             !.settledAt = p0.timeoutAt,
                             !.callbacks = {}, !.listeners = {}]
        hasTask == p.id \in DOMAIN tasks
        scrubbed == [i \in DOMAIN promises |->
                       IF promises[i].state = "pending"
                       THEN [promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                       ELSE promises[i]]
        promises1 == SetPromise(scrubbed, p)
        tasks1 == IF hasTask
                  THEN SetTask(tasks, [tasks[p.id] EXCEPT !.state = "fulfilled",
                                                          !.pid = "", !.ttl = -1,
                                                          !.resumes = {}])
                  ELSE tasks
        \* @type: Set(<<Str, Str>>);
        lkeys == {<<p.id, a>> : a \in listeners}
        unblocked == [k \in DOMAIN outbox \union lkeys |->
                        IF k \in lkeys
                        THEN [address |-> k[2], mtype |-> "unblock", taskId |-> "",
                              version |-> -1, promise |-> PromiseToRecord(p)]
                        ELSE outbox[k]]
    IN /\ promises' = promises1
       /\ promiseTimeouts' = DelPromiseTimeout(promiseTimeouts, p.id)
       /\ tasks' = ResumeTasks(tasks1, p.id, callbacks)
       /\ taskTimeouts' = ResumeTaskTimeouts(
                            IF hasTask
                            THEN DelTaskTimeout(taskTimeouts, p.id)
                            ELSE taskTimeouts,
                            tasks1, callbacks, tnow)
       /\ outbox' = ResumeMessages(unblocked, promises1, tasks1, callbacks)

\* @type: (Str, Int) => Bool;
OnTaskRetryTimeout(id, tnow) ==
  IF id \notin DOMAIN tasks THEN
    UNCHANGED serverVars
  ELSE IF tasks[id].state # "pending" THEN
    UNCHANGED serverVars
  ELSE
    LET retryTimeout == config.retryTimeout
        t == tasks[id] IN
    /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id),
                                      t.id, 0, tnow + retryTimeout)
    /\ IF t.id \notin DOMAIN promises THEN
         UNCHANGED outbox
       ELSE
         outbox' = SetMessage(outbox,
                     TagsGet(promises[t.id].tags, "resonate:target"),
                     ExecuteMsg(t.id, t.version))
    /\ UNCHANGED <<promises, tasks, promiseTimeouts>>

\* @type: (Str, Int) => Bool;
OnTaskLeaseTimeout(id, tnow) ==
  IF id \notin DOMAIN tasks THEN
    UNCHANGED serverVars
  ELSE IF tasks[id].state # "acquired" THEN
    UNCHANGED serverVars
  ELSE
    LET retryTimeout == config.retryTimeout
        t == [tasks[id] EXCEPT !.state = "pending", !.pid = "", !.ttl = -1] IN
    /\ tasks' = SetTask(tasks, t)
    /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id),
                                      t.id, 0, tnow + retryTimeout)
    /\ IF t.id \notin DOMAIN promises THEN
         UNCHANGED outbox
       ELSE
         outbox' = SetMessage(outbox,
                     TagsGet(promises[t.id].tags, "resonate:target"),
                     ExecuteMsg(t.id, t.version))
    /\ UNCHANGED <<promises, promiseTimeouts>>

-----------------------------------------------------------------------------
(* Handlers (the mutating twelve; the pure reads/searches carry no state    *)
(* effect and are omitted with `res`).                                      *)

\* P-02 promise.create
\* @type: { id: Str, timeoutAt: Int, param: $value, tags: $tags } => Bool;
PromiseCreate(req) ==
  LET retryTimeout == config.retryTimeout IN
  IF req.id \notin DOMAIN promises THEN
    IF req.timeoutAt > now THEN
      LET p == [id        |-> req.id,
                state     |-> "pending",
                param     |-> req.param,
                value     |-> EmptyValue,
                tags      |-> req.tags,
                timeoutAt |-> req.timeoutAt,
                createdAt |-> now,
                settledAt |-> -1,
                callbacks |-> {},
                listeners |-> {}]
          target == TagsGet(p.tags, "resonate:target")
      IN
      /\ promises' = SetPromise(promises, p)
      /\ promiseTimeouts' = IF PromiseExternal(p)
                            THEN SetPromiseTimeout(promiseTimeouts, p.id, p.timeoutAt)
                            ELSE promiseTimeouts
      /\ IF target = "" THEN
           UNCHANGED <<tasks, taskTimeouts, outbox>>
         ELSE
           LET t == [id |-> p.id, state |-> "pending", version |-> 0,
                     ttl |-> -1, pid |-> "", resumes |-> {}]
           IN
           /\ tasks' = SetTask(tasks, t)
           /\ IF ~TagsHas(p.tags, "resonate:delay") THEN
                /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 0,
                                                  now + retryTimeout)
                /\ outbox' = SetMessage(outbox, target, ExecuteMsg(t.id, t.version))
              ELSE IF ParseNat(TagsGet(p.tags, "resonate:delay")) > now THEN
                /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 0,
                                     ParseNat(TagsGet(p.tags, "resonate:delay")))
                /\ UNCHANGED outbox
              ELSE
                /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 0,
                                                  now + retryTimeout)
                /\ outbox' = SetMessage(outbox, target, ExecuteMsg(t.id, t.version))
    ELSE
      LET st == IF TagsIsTimer(req.tags)
                THEN "resolved"
                ELSE "rejected_timedout"
          p  == [id        |-> req.id,
                 state     |-> st,
                 param     |-> req.param,
                 value     |-> EmptyValue,
                 tags      |-> req.tags,
                 timeoutAt |-> req.timeoutAt,
                 createdAt |-> req.timeoutAt,
                 settledAt |-> req.timeoutAt,
                 callbacks |-> {},
                 listeners |-> {}]
      IN
      /\ promises' = SetPromise(promises, p)
      /\ IF TagsHas(p.tags, "resonate:target") THEN
           tasks' = SetTask(tasks, [id |-> p.id, state |-> "fulfilled",
                                    version |-> 0, ttl |-> -1, pid |-> "",
                                    resumes |-> {}])
         ELSE
           UNCHANGED tasks
      /\ UNCHANGED <<promiseTimeouts, taskTimeouts, outbox>>
  ELSE
    \* idempotent by id
    UNCHANGED serverVars

\* P-03 promise.settle
\* @type: { id: Str, state: Str, value: $value } => Bool;
PromiseSettle(req) ==
  IF req.id \notin DOMAIN promises THEN
    UNCHANGED serverVars
  ELSE IF promises[req.id].state = "pending" /\ promises[req.id].timeoutAt > now THEN
    LET p0 == promises[req.id]
        listeners == p0.listeners
        callbacks == p0.callbacks
        p == [p0 EXCEPT !.state = req.state, !.value = req.value,
                        !.settledAt = now,
                        !.callbacks = {}, !.listeners = {}]
        hasTask == p.id \in DOMAIN tasks
        scrubbed == [i \in DOMAIN promises |->
                       IF promises[i].state = "pending"
                       THEN [promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                       ELSE promises[i]]
        promises1 == SetPromise(scrubbed, p)
        tasks1 == IF hasTask
                  THEN SetTask(tasks, [tasks[p.id] EXCEPT !.state = "fulfilled",
                                                          !.pid = "", !.ttl = -1,
                                                          !.resumes = {}])
                  ELSE tasks
        \* @type: Set(<<Str, Str>>);
        lkeys == {<<p.id, a>> : a \in listeners}
        unblocked == [k \in DOMAIN outbox \union lkeys |->
                        IF k \in lkeys
                        THEN [address |-> k[2], mtype |-> "unblock", taskId |-> "",
                              version |-> -1, promise |-> PromiseToRecord(p)]
                        ELSE outbox[k]]
    IN /\ promises' = promises1
       /\ promiseTimeouts' = DelPromiseTimeout(promiseTimeouts, p.id)
       /\ tasks' = ResumeTasks(tasks1, p.id, callbacks)
       /\ taskTimeouts' = ResumeTaskTimeouts(
                            IF hasTask
                            THEN DelTaskTimeout(taskTimeouts, p.id)
                            ELSE taskTimeouts,
                            tasks1, callbacks, now)
       /\ outbox' = ResumeMessages(unblocked, promises1, tasks1, callbacks)
  ELSE
    \* absent-pending (already settled or projected): no state effect
    UNCHANGED serverVars

\* P-04 promise.register_callback
\* @type: { awaited: Str, awaiter: Str } => Bool;
PromiseRegisterCallback(req) ==
  IF req.awaited \notin DOMAIN promises THEN
    UNCHANGED serverVars
  ELSE IF req.awaiter \notin DOMAIN promises THEN
    UNCHANGED serverVars
  ELSE IF ~TagsHas(promises[req.awaiter].tags, "resonate:target") THEN
    UNCHANGED serverVars
  ELSE IF promises[req.awaited].state = "pending"
          /\ promises[req.awaited].timeoutAt > now THEN
    /\ promises' = IF promises[req.awaiter].state = "pending"
                      /\ promises[req.awaiter].timeoutAt > now
                   THEN SetPromise(promises,
                          PromiseAddCallback(promises[req.awaited], req.awaiter))
                   ELSE promises
    /\ UNCHANGED <<tasks, promiseTimeouts, taskTimeouts, outbox>>
  ELSE
    UNCHANGED serverVars

\* P-05 promise.register_listener
\* @type: { awaited: Str, address: Str } => Bool;
PromiseRegisterListener(req) ==
  IF req.awaited \notin DOMAIN promises THEN
    UNCHANGED serverVars
  ELSE IF promises[req.awaited].state = "pending"
          /\ promises[req.awaited].timeoutAt > now THEN
    /\ promises' = SetPromise(promises,
                     PromiseAddListener(promises[req.awaited], req.address))
    /\ UNCHANGED <<tasks, promiseTimeouts, taskTimeouts, outbox>>
  ELSE
    UNCHANGED serverVars

\* T-02 task.create
\* @type: { pid: Str, ttl: Int, action: { id: Str, timeoutAt: Int, param: $value, tags: $tags } } => Bool;
TaskCreate(req) ==
  LET a == req.action IN
  IF a.id \notin DOMAIN promises THEN
    IF ~TagsHas(a.tags, "resonate:target") THEN
      \* untargeted action: unroutable (422; mirrors the existing branch)
      UNCHANGED serverVars
    ELSE IF a.timeoutAt > now THEN
      LET p == [id        |-> a.id,
                state     |-> "pending",
                param     |-> a.param,
                value     |-> EmptyValue,
                tags      |-> a.tags,
                timeoutAt |-> a.timeoutAt,
                createdAt |-> now,
                settledAt |-> -1,
                callbacks |-> {},
                listeners |-> {}]
          t == [id |-> p.id, state |-> "acquired", version |-> 1,
                ttl |-> req.ttl, pid |-> req.pid, resumes |-> {}]
      IN
      /\ promises' = SetPromise(promises, p)
      /\ promiseTimeouts' = SetPromiseTimeout(promiseTimeouts, p.id, p.timeoutAt)
      /\ tasks' = SetTask(tasks, t)
      /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 1, now + req.ttl)
      /\ UNCHANGED outbox
    ELSE
      LET st == IF TagsIsTimer(a.tags)
                THEN "resolved"
                ELSE "rejected_timedout"
          p  == [id        |-> a.id,
                 state     |-> st,
                 param     |-> a.param,
                 value     |-> EmptyValue,
                 tags      |-> a.tags,
                 timeoutAt |-> a.timeoutAt,
                 createdAt |-> a.timeoutAt,
                 settledAt |-> a.timeoutAt,
                 callbacks |-> {},
                 listeners |-> {}]
      IN
      /\ promises' = SetPromise(promises, p)
      /\ tasks' = SetTask(tasks, [id |-> p.id, state |-> "fulfilled",
                                  version |-> 0, ttl |-> -1, pid |-> "",
                                  resumes |-> {}])
      /\ UNCHANGED <<promiseTimeouts, taskTimeouts, outbox>>
  ELSE
    IF ~TagsHas(promises[a.id].tags, "resonate:target") THEN
      UNCHANGED serverVars
    ELSE IF a.id \in DOMAIN tasks /\ tasks[a.id].state = "pending" THEN
      LET t == [tasks[a.id] EXCEPT !.state = "acquired", !.version = @ + 1,
                                   !.ttl = req.ttl, !.pid = req.pid,
                                   !.resumes = {}]
      IN
      /\ tasks' = SetTask(tasks, t)
      /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id),
                                        t.id, 1, now + req.ttl)
      /\ UNCHANGED <<promises, promiseTimeouts, outbox>>
    ELSE
      \* fulfilled (idempotent), non-pending, or missing task: no state effect
      UNCHANGED serverVars

\* T-03 task.acquire
\* @type: { id: Str, version: Int, pid: Str, ttl: Int } => Bool;
TaskAcquire(req) ==
  IF /\ req.id \in DOMAIN tasks
     /\ req.id \in DOMAIN promises
     /\ tasks[req.id].state = "pending"
     /\ promises[req.id].state = "pending"
     /\ promises[req.id].timeoutAt > now
     /\ tasks[req.id].version = req.version
  THEN
    LET t == [tasks[req.id] EXCEPT !.state = "acquired", !.version = @ + 1,
                                   !.ttl = req.ttl, !.pid = req.pid,
                                   !.resumes = {}]
    IN
    /\ tasks' = SetTask(tasks, t)
    /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id),
                                      t.id, 1, now + req.ttl)
    /\ UNCHANGED <<promises, promiseTimeouts, outbox>>
  ELSE
    UNCHANGED serverVars

\* Fence guard, shared shape of T-04 (task acquired, promise live, version).
\* @type: (Str, Int) => Bool;
FenceOk(id, version) ==
  /\ id \in DOMAIN tasks
  /\ id \in DOMAIN promises
  /\ tasks[id].state = "acquired"
  /\ promises[id].state = "pending"
  /\ promises[id].timeoutAt > now
  /\ tasks[id].version = version

\* T-04 task.fence (action payload flattened: ftype selects create/settle)
\* @type: { id: Str, version: Int, ftype: Str, aid: Str, atimeoutAt: Int, aparam: $value, atags: $tags, astate: Str, avalue: $value } => Bool;
TaskFence(req) ==
  IF ~FenceOk(req.id, req.version) THEN
    UNCHANGED serverVars
  ELSE IF req.ftype = "create" THEN
    PromiseCreate([id |-> req.aid, timeoutAt |-> req.atimeoutAt,
                   param |-> req.aparam, tags |-> req.atags])
  ELSE
    PromiseSettle([id |-> req.aid, state |-> req.astate, value |-> req.avalue])

\* T-05 task.heartbeat
\* @type: { pid: Str, tasks: Seq({ id: Str, version: Int }) } => Bool;
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
                   \union {<<id, 1>> : id \in ids} |->
             IF k[1] \in ids
             THEN now + (IF tasks[k[1]].ttl = -1 THEN 0 ELSE tasks[k[1]].ttl)
             ELSE taskTimeouts[k]]
     /\ UNCHANGED <<promises, tasks, promiseTimeouts, outbox>>

\* T-06 task.suspend
\* @type: { id: Str, version: Int, actions: Seq({ awaited: Str, awaiter: Str }) } => Bool;
TaskSuspend(req) ==
  IF ~(/\ req.id \in DOMAIN tasks
       /\ req.id \in DOMAIN promises
       /\ tasks[req.id].state = "acquired"
       /\ promises[req.id].state = "pending"
       /\ promises[req.id].timeoutAt > now
       /\ tasks[req.id].version = req.version
       /\ \A i \in DOMAIN req.actions : req.actions[i].awaited \in DOMAIN promises)
  THEN
    UNCHANGED serverVars
  ELSE
    LET settled == \E i \in DOMAIN req.actions :
                     LET pa == promises[req.actions[i].awaited]
                     IN pa.state # "pending" \/ pa.timeoutAt <= now
    IN
    IF settled THEN
      /\ tasks' = SetTask(tasks, [tasks[req.id] EXCEPT !.resumes = {}])
      /\ UNCHANGED <<promises, promiseTimeouts, taskTimeouts, outbox>>
    ELSE
      LET awaitedIds == {req.actions[i].awaited : i \in DOMAIN req.actions}
      IN
      /\ promises' = [id \in DOMAIN promises |->
                        IF id \in awaitedIds
                        THEN PromiseAddCallback(promises[id], req.id)
                        ELSE promises[id]]
      /\ tasks' = SetTask(tasks, [tasks[req.id] EXCEPT !.state = "suspended",
                                                       !.pid = "", !.ttl = -1,
                                                       !.resumes = {}])
      /\ taskTimeouts' = DelTaskTimeout(taskTimeouts, req.id)
      /\ UNCHANGED <<promiseTimeouts, outbox>>

\* T-07 task.fulfill
\* @type: { id: Str, version: Int, action: { id: Str, state: Str, value: $value } } => Bool;
TaskFulfill(req) ==
  IF ~FenceOk(req.id, req.version) THEN
    UNCHANGED serverVars
  ELSE
    LET p0 == promises[req.id]
        listeners == p0.listeners
        callbacks == p0.callbacks
        p == [p0 EXCEPT !.state = req.action.state, !.value = req.action.value,
                        !.settledAt = now,
                        !.callbacks = {}, !.listeners = {}]
        scrubbed == [i \in DOMAIN promises |->
                       IF promises[i].state = "pending"
                       THEN [promises[i] EXCEPT !.callbacks = @ \ {p.id}]
                       ELSE promises[i]]
        promises1 == SetPromise(scrubbed, p)
        tasks1 == SetTask(tasks, [tasks[req.id] EXCEPT !.state = "fulfilled",
                                                       !.pid = "", !.ttl = -1,
                                                       !.resumes = {}])
        \* @type: Set(<<Str, Str>>);
        lkeys == {<<p.id, a>> : a \in listeners}
        unblocked == [k \in DOMAIN outbox \union lkeys |->
                        IF k \in lkeys
                        THEN [address |-> k[2], mtype |-> "unblock", taskId |-> "",
                              version |-> -1, promise |-> PromiseToRecord(p)]
                        ELSE outbox[k]]
    IN /\ promises' = promises1
       /\ promiseTimeouts' = DelPromiseTimeout(promiseTimeouts, p.id)
       /\ tasks' = ResumeTasks(tasks1, p.id, callbacks)
       /\ taskTimeouts' = ResumeTaskTimeouts(DelTaskTimeout(taskTimeouts, req.id),
                                             tasks1, callbacks, now)
       /\ outbox' = ResumeMessages(unblocked, promises1, tasks1, callbacks)

\* T-08 task.release
\* @type: { id: Str, version: Int } => Bool;
TaskRelease(req) ==
  IF ~FenceOk(req.id, req.version) THEN
    UNCHANGED serverVars
  ELSE
    LET retryTimeout == config.retryTimeout
        t == [tasks[req.id] EXCEPT !.state = "pending", !.pid = "", !.ttl = -1]
    IN
    /\ tasks' = SetTask(tasks, t)
    /\ taskTimeouts' = SetTaskTimeout(DelTaskTimeout(taskTimeouts, t.id),
                                      t.id, 0, now + retryTimeout)
    /\ outbox' = SetMessage(outbox,
                   TagsGet(promises[req.id].tags, "resonate:target"),
                   ExecuteMsg(t.id, t.version))
    /\ UNCHANGED <<promises, promiseTimeouts>>

\* T-09 task.halt
\* @type: { id: Str } => Bool;
TaskHalt(req) ==
  IF req.id \in DOMAIN tasks
     /\ tasks[req.id].state \notin {"fulfilled", "halted"} THEN
    /\ tasks' = SetTask(tasks, [tasks[req.id] EXCEPT !.state = "halted",
                                                     !.pid = "", !.ttl = -1])
    /\ taskTimeouts' = DelTaskTimeout(taskTimeouts, req.id)
    /\ UNCHANGED <<promises, promiseTimeouts, outbox>>
  ELSE
    UNCHANGED serverVars

\* T-10 task.continue
\* @type: { id: Str } => Bool;
TaskContinue(req) ==
  IF /\ req.id \in DOMAIN tasks
     /\ tasks[req.id].state = "halted"
     /\ req.id \in DOMAIN promises
  THEN
    LET retryTimeout == config.retryTimeout
        t == [tasks[req.id] EXCEPT !.state = "pending"]
    IN
    /\ tasks' = SetTask(tasks, t)
    /\ taskTimeouts' = SetTaskTimeout(taskTimeouts, t.id, 0, now + retryTimeout)
    /\ outbox' = SetMessage(outbox,
                   TagsGet(promises[req.id].tags, "resonate:target"),
                   ExecuteMsg(t.id, t.version))
    /\ UNCHANGED <<promises, promiseTimeouts>>
  ELSE
    UNCHANGED serverVars

-----------------------------------------------------------------------------
(* The tick: fire one eligible timeout entry, kind = -1 marks a promise     *)
(* deadline.                                                                *)

\* @type: Int => Set({ etype: Str, id: Str, kind: Int });
Eligible(tnow) ==
  {[etype |-> "promise", id |-> id, kind |-> -1] :
     id \in {x \in DOMAIN promiseTimeouts : promiseTimeouts[x] <= tnow}}
  \union
  {[etype |-> "task", id |-> k[1], kind |-> k[2]] :
     k \in {x \in DOMAIN taskTimeouts : taskTimeouts[x] <= tnow}}

\* @type: ({ etype: Str, id: Str, kind: Int }, Int) => Bool;
Fire(entry, tnow) ==
  IF entry.etype = "promise" THEN OnPromiseTimeout(entry.id, tnow)
  ELSE IF entry.kind = 0 THEN OnTaskRetryTimeout(entry.id, tnow)
  ELSE OnTaskLeaseTimeout(entry.id, tnow)

-----------------------------------------------------------------------------
(* Request generators.                                                      *)

Times == 0..(MaxTime + 1)

Versions == 0..3

TTLs == {2}

\* @type: Set($value);
Values == {EmptyValue}
            \union {[headers |-> <<>>, data |-> d] : d \in DataValues}

\* The full request space, untagged (internal) promises included --
\* NonExternalPromiseHasNoTimeout is only meaningful with them present.
\* @type: Set($tags);
TagOptions ==
  {<<>>, <<<<"resonate:timer", "true">>>>}
    \union {<<<<"resonate:target", a>>>> : a \in Addresses}
    \union {<<<<"resonate:target", a>>, <<"resonate:delay", "2">>>> :
              a \in Addresses}

SettleStates == {"resolved", "rejected", "rejected_canceled"}

\* @type: Set({ id: Str, timeoutAt: Int, param: $value, tags: $tags });
PromiseCreateReqs ==
  [id : PromiseIds, timeoutAt : Times, param : Values, tags : TagOptions]

\* @type: Set({ id: Str, state: Str, value: $value });
PromiseSettleReqs == [id : PromiseIds, state : SettleStates, value : Values]

\* @type: Set({ awaited: Str, awaiter: Str });
RegisterCallbackReqs == [awaited : PromiseIds, awaiter : PromiseIds]

\* @type: Set({ id: Str, version: Int });
TaskRefs == [id : PromiseIds, version : Versions]

\* fence payload, flattened
\* @type: Set({ id: Str, version: Int, ftype: Str, aid: Str, atimeoutAt: Int, aparam: $value, atags: $tags, astate: Str, avalue: $value });
TaskFenceReqs ==
  {[id |-> f.id, version |-> f.version, ftype |-> "create",
    aid |-> r.id, atimeoutAt |-> r.timeoutAt, aparam |-> r.param,
    atags |-> r.tags, astate |-> "", avalue |-> EmptyValue] :
      f \in [id : PromiseIds, version : Versions], r \in PromiseCreateReqs}
  \union
  {[id |-> f.id, version |-> f.version, ftype |-> "settle",
    aid |-> r.id, atimeoutAt |-> -1, aparam |-> EmptyValue,
    atags |-> <<>>, astate |-> r.state, avalue |-> r.value] :
      f \in [id : PromiseIds, version : Versions], r \in PromiseSettleReqs}

\* @type: Set(Seq({ id: Str, version: Int }));
HeartbeatLists == {<<>>}
                    \union {<<r>> : r \in TaskRefs}
                    \union {<<r1, r2>> : r1 \in TaskRefs, r2 \in TaskRefs}

\* @type: Set(Seq({ awaited: Str, awaiter: Str }));
SuspendLists == {<<>>}
                  \union {<<a>> : a \in RegisterCallbackReqs}
                  \union {<<a1, a2>> : a1 \in RegisterCallbackReqs,
                                       a2 \in RegisterCallbackReqs}

-----------------------------------------------------------------------------

\* Constant initializer for Apalache (--cinit=CInit).
CInit == /\ PromiseIds = {"p1", "p2"}
         /\ Pids = {"w1"}
         /\ Addresses = {"a1"}
         /\ DataValues = {"d1"}
         /\ MaxTime = 3
         /\ RetryTimeout = 2

Init == /\ promises = SetAsFun({})
        /\ tasks = SetAsFun({})
        /\ promiseTimeouts = SetAsFun({})
        /\ taskTimeouts = SetAsFun({})
        /\ outbox = SetAsFun({})
        /\ now = 0

Next ==
  \/ \E req \in PromiseCreateReqs : PromiseCreate(req) /\ UNCHANGED now
  \/ \E req \in PromiseSettleReqs : PromiseSettle(req) /\ UNCHANGED now
  \/ \E req \in RegisterCallbackReqs : PromiseRegisterCallback(req) /\ UNCHANGED now
  \/ \E req \in [awaited : PromiseIds, address : Addresses] :
       PromiseRegisterListener(req) /\ UNCHANGED now
  \/ \E req \in [pid : Pids, ttl : TTLs, action : PromiseCreateReqs] :
       TaskCreate(req) /\ UNCHANGED now
  \/ \E req \in [id : PromiseIds, version : Versions, pid : Pids, ttl : TTLs] :
       TaskAcquire(req) /\ UNCHANGED now
  \/ \E req \in TaskFenceReqs : TaskFence(req) /\ UNCHANGED now
  \/ \E req \in [pid : Pids, tasks : HeartbeatLists] :
       TaskHeartbeat(req) /\ UNCHANGED now
  \/ \E req \in [id : PromiseIds, version : Versions, actions : SuspendLists] :
       TaskSuspend(req) /\ UNCHANGED now
  \/ \E req \in [id : PromiseIds, version : Versions, action : PromiseSettleReqs] :
       TaskFulfill(req) /\ UNCHANGED now
  \/ \E req \in [id : PromiseIds, version : Versions] :
       TaskRelease(req) /\ UNCHANGED now
  \/ \E req \in [id : PromiseIds] : TaskHalt(req) /\ UNCHANGED now
  \/ \E req \in [id : PromiseIds] : TaskContinue(req) /\ UNCHANGED now
  \/ \E newNow \in now..MaxTime :
       /\ \/ /\ newNow > now
             /\ UNCHANGED serverVars
          \/ \E entry \in Eligible(newNow) : Fire(entry, newNow)
       /\ now' = newNow

-----------------------------------------------------------------------------
(* Invariants.                                                              *)

InvSettledAt ==
  \A id \in DOMAIN promises :
    (promises[id].state = "pending") <=> (promises[id].settledAt = -1)

InvPromiseTimeouts ==
  \A id \in DOMAIN promiseTimeouts :
    /\ id \in DOMAIN promises
    /\ promises[id].state = "pending"
    /\ promiseTimeouts[id] = promises[id].timeoutAt

InvTaskTimeouts ==
  \A k \in DOMAIN taskTimeouts :
    /\ k[1] \in DOMAIN tasks
    /\ (k[2] = 0) => tasks[k[1]].state = "pending"
    /\ (k[2] = 1) => tasks[k[1]].state = "acquired"

InvTaskHasPromise ==
  \A id \in DOMAIN tasks : id \in DOMAIN promises

Inv == InvSettledAt /\ InvPromiseTimeouts /\ InvTaskTimeouts /\ InvTaskHasPromise

-----------------------------------------------------------------------------
(* The structural invariant catalog from the Dafny abstract spec            *)
(* (resonate-kafka/abstract/Invariants.dfy), sentinel-typed. Four conjuncts *)
(* are FALSE without environment assumptions and are excluded (TLC          *)
(* counterexamples, see Server.tla): CallbackNotSelfReferential and         *)
(* SuspendedTaskHasCallback.                                                *)
(* StructuralInv is proven INDUCTIVE below (IndInit/IndInv) -- the          *)
(* preservation proof the Dafny file leaves as its substantial TODO,        *)
(* discharged mechanically for the fixed constants.                         *)

\* @type: $promise => Bool;
PromiseHasTarget(p) == TagsGet(p.tags, "resonate:target") # ""

PromiseWithTargetHasTask ==
  \A id \in DOMAIN promises :
    PromiseHasTarget(promises[id]) => id \in DOMAIN tasks

PromiseNoTargetHasNoTask ==
  \A id \in DOMAIN promises :
    ~PromiseHasTarget(promises[id]) => id \notin DOMAIN tasks

TaskHasPromiseC ==
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

CallbackAwaiterHasTask ==
  \A id \in DOMAIN promises : \A aw \in promises[id].callbacks :
    aw \in DOMAIN tasks

CallbackAwaiterIsPending ==
  \A id \in DOMAIN promises : \A aw \in promises[id].callbacks :
    aw \in DOMAIN promises /\ promises[aw].state = "pending"

NonAcquiredTaskNoPidOrTtl ==
  \A id \in DOMAIN tasks :
    tasks[id].state # "acquired"
      => tasks[id].pid = "" /\ tasks[id].ttl = -1

FulfilledTaskHasEmptyResumes ==
  \A id \in DOMAIN tasks :
    tasks[id].state = "fulfilled" => tasks[id].resumes = {}

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
                /\ tasks[k[1]].pid # ""
                /\ tasks[k[1]].ttl # -1

TaskHasAtMostOneTimeout ==
  \A k \in DOMAIN taskTimeouts : <<k[1], 1 - k[2]>> \notin DOMAIN taskTimeouts

LeaseTimeoutOnlyForAcquiredTask ==
  \A k \in DOMAIN taskTimeouts :
    k[2] = 1 => k[1] \in DOMAIN tasks /\ tasks[k[1]].state = "acquired"

RetryTimeoutOnlyForPendingTask ==
  \A k \in DOMAIN taskTimeouts :
    k[2] = 0 => k[1] \in DOMAIN tasks /\ tasks[k[1]].state = "pending"

\* Suspended/Halted/FulfilledTaskHasNoTimeout follow from the two "only
\* for" predicates plus TaskHasAtMostOneTimeout; WFState is in IndTypeOk.

StructuralInv ==
  /\ PromiseWithTargetHasTask
  /\ PromiseNoTargetHasNoTask
  /\ TaskHasPromiseC
  /\ ActivePromiseHasActiveTask
  /\ ActiveTaskHasActivePromise
  /\ SettledPromiseHasFulfilledTask
  /\ FulfilledTaskHasSettledPromise
  /\ PendingExternalPromiseHasTimeout
  /\ NonExternalPromiseHasNoTimeout
  /\ PTimeoutsSubsetPromises
  /\ SettledPromiseHasNoTimeout
  /\ SettledPromiseHasNoCallbacks
  /\ CallbackAwaiterHasTask
  /\ CallbackAwaiterIsPending
  /\ NonAcquiredTaskNoPidOrTtl
  /\ FulfilledTaskHasEmptyResumes
  /\ PendingTaskHasRetryTimeout
  /\ AcquiredTaskHasLeaseTimeout
  /\ LeaseTimeoutHasValidPidAndTtl
  /\ TaskHasAtMostOneTimeout
  /\ LeaseTimeoutOnlyForAcquiredTask
  /\ RetryTimeoutOnlyForPendingTask

-----------------------------------------------------------------------------
(* Induction: IndInv is closed under Next from ANY state satisfying it      *)
(* (--init=IndInit --inv=IndInv --length=1) and holds initially             *)
(* (--init=Init --inv=IndInv --length=0), hence at EVERY depth -- an        *)
(* unbounded proof, which bounded enumeration cannot give.                  *)
(* IndTypeOk is the inductive typing envelope the protocol maintains.       *)

PromiseStates == {"pending", "resolved", "rejected",
                  "rejected_canceled", "rejected_timedout"}

TaskStates == {"pending", "acquired", "suspended", "halted", "fulfilled"}

IndTypeOk ==
  /\ now >= 0
  /\ DOMAIN promises \subseteq PromiseIds
  /\ \A id \in DOMAIN promises :
       /\ promises[id].id = id
       /\ promises[id].state \in PromiseStates
       /\ promises[id].timeoutAt >= 0
       /\ promises[id].tags \in TagOptions
       /\ promises[id].callbacks \subseteq PromiseIds
       /\ promises[id].listeners \subseteq Addresses
  /\ DOMAIN tasks \subseteq PromiseIds
  /\ \A id \in DOMAIN tasks :
       /\ tasks[id].id = id
       /\ tasks[id].state \in TaskStates
  /\ DOMAIN promiseTimeouts \subseteq PromiseIds
  /\ \A k \in DOMAIN taskTimeouts : k[1] \in PromiseIds /\ k[2] \in {0, 1}

IndInv == IndTypeOk /\ Inv /\ StructuralInv

\* An arbitrary IndInv state (Gen bounds the collection sizes to the
\* constants' capacity). The outbox is write-only -- no transition reads
\* it to decide anything, and no invariant mentions it -- so fixing it
\* empty does not weaken the induction.
IndInit ==
  /\ promises = Gen(2)
  /\ tasks = Gen(2)
  /\ promiseTimeouts = Gen(2)
  /\ taskTimeouts = Gen(4)
  /\ outbox = SetAsFun({})
  /\ now = Gen(1)
  /\ IndInv

=============================================================================
