// Package model is a Go transcription of the Resonate abstract machine
// specified in Lean 4 under ../spec. It follows the Lean specification
// as closely as Go allows: the same state, the same effects (atomic
// operations on the state), and the same request handlers (transitions
// composed from effects).
//
// It is meant to READ like the Lean spec. Where Lean has a monad
//
//	Req → (now : Nat) → M Res    -- M = StateM ServerState
//
// this file has a method
//
//	func (s *ServerState) handler(req Req, now int) Res
//
// The StateM effects (getPromise, setPromise, ...) become methods on
// *ServerState. Every Lean `let p := { p with ... }` becomes a mutation
// of a local COPY followed by a setX write-back — the Lean value
// semantics are preserved because getX returns a fresh copy, so nothing
// is observed until the corresponding setX.
//
// Source mapping:
//   - spec/01-objects/types.lean  → "Objects — types"
//   - spec/01-objects/state.lean  → "Objects — state" + "Effects"
//   - spec/02-actions/*.lean      → "Handlers"
package model

import "strconv"

// ============================================================================
// Objects — types  (spec/01-objects/types.lean)
// ============================================================================

// Tags is `List (String × String)` — an association list, NOT a map;
// Tags.get returns the first matching entry.
type KV struct {
	fst string
	snd string
}

type Tags []KV

type Value struct {
	headers Tags    // := []
	data    *string // Option String := none
}

type PromiseState int

const (
	pending PromiseState = iota
	resolved
	rejected
	rejectedCanceled
	rejectedTimedout
)

type TaskState int

const (
	taskPending TaskState = iota
	taskAcquired
	taskSuspended
	taskHalted
	taskFulfilled
)

type PromiseRecord struct {
	id        string
	state     PromiseState
	param     Value
	value     Value // := {}
	tags      Tags
	timeoutAt int
	createdAt int
	settledAt *int // Option Nat := none
}

type TaskRecord struct {
	id      string
	state   TaskState
	version int
	resumes int
	ttl     *int    // Option Nat := none
	pid     *string // Option String := none
}

type Schedule struct {
	id             string
	cron           string
	promiseId      string
	promiseTimeout int
	promiseParam   Value
	promiseTags    Tags
	nextRunAt      int
	lastRunAt      *int // := none
	createdAt      int
}

type PromiseGetReq struct {
	id string
}

type PromiseGetRes struct {
	status  int
	promise *PromiseRecord // := none
}

type PromiseCreateReq struct {
	id        string
	timeoutAt int
	param     Value
	tags      Tags
}

type PromiseCreateRes struct {
	status  int
	promise *PromiseRecord
}

type PromiseSettleReq struct {
	id    string
	state PromiseState
	value Value
}

type PromiseSettleRes struct {
	status  int
	promise *PromiseRecord // := none
}

type PromiseRegisterCallbackReq struct {
	awaited string
	awaiter string
}

type PromiseRegisterCallbackRes struct {
	status  int
	promise *PromiseRecord // := none
}

type PromiseRegisterListenerReq struct {
	awaited string
	address string
}

type PromiseRegisterListenerRes struct {
	status  int
	promise *PromiseRecord // := none
}

type PromiseSearchReq struct {
	state  *PromiseState // := none
	tags   Tags          // := []
	limit  *int          // := none
	cursor *string       // := none
}

type PromiseSearchRes struct {
	status   int
	promises []PromiseRecord // := []
	cursor   *string         // := none
}

type ScheduleGetReq struct {
	id string
}

type ScheduleGetRes struct {
	status   int
	schedule *Schedule // := none
}

type ScheduleCreateReq struct {
	id             string
	cron           string
	promiseId      string
	promiseTimeout int
	promiseParam   Value
	promiseTags    Tags
}

type ScheduleCreateRes struct {
	status   int
	schedule *Schedule // := none
}

type ScheduleDeleteReq struct {
	id string
}

type ScheduleDeleteRes struct {
	status int
}

type ScheduleSearchReq struct {
	limit  *int    // := none
	cursor *string // := none
}

type ScheduleSearchRes struct {
	status    int
	schedules []Schedule // := []
	cursor    *string    // := none
}

type TaskGetReq struct {
	id string
}

type TaskGetRes struct {
	status int
	task   *TaskRecord // := none
}

type TaskCreateReq struct {
	pid    string
	ttl    int
	action PromiseCreateReq
}

type TaskCreateRes struct {
	status  int
	task    *TaskRecord     // := none
	promise *PromiseRecord  // := none
	preload []PromiseRecord // := []
}

type TaskAcquireReq struct {
	id      string
	version int
	pid     string
	ttl     int
}

type TaskAcquireRes struct {
	status  int
	task    *TaskRecord     // := none
	promise *PromiseRecord  // := none
	preload []PromiseRecord // := []
}

// TaskFenceAction is `create (req) | settle (req)`. Exactly one pointer
// is set.
type TaskFenceAction struct {
	create *PromiseCreateReq
	settle *PromiseSettleReq
}

// TaskFenceInnerRes is `create (res) | settle (res)`.
type TaskFenceInnerRes struct {
	create *PromiseCreateRes
	settle *PromiseSettleRes
}

type TaskFenceReq struct {
	id      string
	version int
	action  TaskFenceAction
}

type TaskFenceRes struct {
	status  int
	action  *TaskFenceInnerRes // := none
	preload []PromiseRecord    // := []
}

type TaskRef struct {
	id      string
	version int
}

type TaskHeartbeatReq struct {
	pid   string
	tasks []TaskRef
}

type TaskHeartbeatRes struct {
	status int
}

type TaskSuspendReq struct {
	id      string
	version int
	actions []PromiseRegisterCallbackReq
}

type TaskSuspendRes struct {
	status  int
	preload []PromiseRecord // := []
}

type TaskFulfillReq struct {
	id      string
	version int
	action  PromiseSettleReq
}

type TaskFulfillRes struct {
	status  int
	promise *PromiseRecord // := none
}

type TaskReleaseReq struct {
	id      string
	version int
}

type TaskReleaseRes struct {
	status int
}

type TaskHaltReq struct {
	id string
}

type TaskHaltRes struct {
	status int
}

type TaskContinueReq struct {
	id string
}

type TaskContinueRes struct {
	status int
}

type TaskSearchReq struct {
	state  *TaskState // := none
	limit  *int       // := none
	cursor *string    // := none
}

type TaskSearchRes struct {
	status int
	tasks  []TaskRecord // := []
	cursor *string      // := none
}

// ============================================================================
// Objects — state  (spec/01-objects/state.lean)
// ============================================================================

// Tags.get?
func (t Tags) get(k string) *string {
	for _, kv := range t {
		if kv.fst == k {
			v := kv.snd
			return &v
		}
	}
	return nil
}

// Tags.has
func (t Tags) has(k string) bool {
	return t.get(k) != nil
}

// Tags.isTimer
func (t Tags) isTimer() bool {
	v := t.get("resonate:timer")
	return v != nil && *v == "true"
}

type PromiseObject struct {
	id        string
	state     PromiseState
	param     Value
	value     Value // := {}
	tags      Tags
	timeoutAt int
	createdAt int
	settledAt *int     // Option Nat := none
	callbacks []string // := []
	listeners []string // := []
}

func (p PromiseObject) toRecord() PromiseRecord {
	return PromiseRecord{
		id: p.id, state: p.state, param: p.param, value: p.value,
		tags: p.tags, timeoutAt: p.timeoutAt, createdAt: p.createdAt,
		settledAt: p.settledAt,
	}
}

func (p PromiseObject) isTimer() bool { return p.tags.isTimer() }

func (p PromiseObject) external() bool {
	return p.tags.has("resonate:target") || p.isTimer()
}

func (p PromiseObject) addCallback(awaiterId string) PromiseObject {
	if contains(p.callbacks, awaiterId) {
		return p
	}
	p.callbacks = appended(p.callbacks, awaiterId)
	return p
}

func (p PromiseObject) addListener(address string) PromiseObject {
	if contains(p.listeners, address) {
		return p
	}
	p.listeners = appended(p.listeners, address)
	return p
}

type TaskObject struct {
	id      string
	state   TaskState
	version int
	ttl     *int     // Option Nat := none
	pid     *string  // Option String := none
	resumes []string // := []
}

func (t TaskObject) toRecord() TaskRecord {
	return TaskRecord{
		id: t.id, state: t.state, version: t.version,
		resumes: len(t.resumes), ttl: t.ttl, pid: t.pid,
	}
}

type PromiseTimeout struct {
	id      string
	timeout int
}

type TaskTimeout struct {
	id      string
	kind    int // 0 = pending retry, 1 = lease expiration
	timeout int
}

type ScheduleTimeout struct {
	id      string
	timeout int
}

// Message is `execute (taskId) (version) | unblock (promise)`.
type Message struct {
	kind    string // "execute" | "unblock"
	taskId  string
	version int
	promise PromiseRecord
}

func execute(taskId string, version int) Message {
	return Message{kind: "execute", taskId: taskId, version: version}
}

func unblock(p PromiseRecord) Message {
	return Message{kind: "unblock", promise: p}
}

type OutboxEntry struct {
	address string
	message Message
}

func (e OutboxEntry) key() string {
	switch e.message.kind {
	case "execute":
		return e.message.taskId
	default: // unblock
		return e.message.promise.id + ":notify:" + e.address
	}
}

type ServerConfig struct {
	retryTimeout int // := 5000
}

type ServerState struct {
	config           ServerConfig
	promises         []PromiseObject
	tasks            []TaskObject
	schedules        []Schedule
	promiseTimeouts  []PromiseTimeout
	taskTimeouts     []TaskTimeout
	scheduleTimeouts []ScheduleTimeout
	outbox           []OutboxEntry
}

// ServerState.init
func InitServerState() ServerState {
	return ServerState{config: ServerConfig{retryTimeout: 5000}}
}

// ---------------------------------------------------------------------------
// Effects — the atomic operations of the machine.
// ---------------------------------------------------------------------------

func (s *ServerState) getPromise(id string) *PromiseObject {
	return find(s.promises, func(p PromiseObject) bool { return p.id == id })
}

func (s *ServerState) setPromise(p PromiseObject) {
	s.promises = append([]PromiseObject{p},
		filter(s.promises, func(q PromiseObject) bool { return q.id != p.id })...)
}

func (s *ServerState) getTask(id string) *TaskObject {
	return find(s.tasks, func(t TaskObject) bool { return t.id == id })
}

func (s *ServerState) setTask(t TaskObject) {
	s.tasks = append([]TaskObject{t},
		filter(s.tasks, func(u TaskObject) bool { return u.id != t.id })...)
}

func (s *ServerState) getSchedule(id string) *Schedule {
	return find(s.schedules, func(sch Schedule) bool { return sch.id == id })
}

func (s *ServerState) setSchedule(sch Schedule) {
	s.schedules = append([]Schedule{sch},
		filter(s.schedules, func(o Schedule) bool { return o.id != sch.id })...)
}

func (s *ServerState) delSchedule(id string) {
	s.schedules = filter(s.schedules, func(sch Schedule) bool { return sch.id != id })
}

// nextCron: next cron fire time strictly after the given instant. Opaque
// in the spec (`opaque nextCron`); injected by a driver.
var nextCron = func(cron string, after int) int {
	panic("opaque: nextCron unimplemented")
}

// expand: expand a schedule's promise-id template against one occurrence.
// Opaque in the spec (`opaque expand`); injected by a driver.
var expand = func(template, id string, timestamp int) string {
	panic("opaque: expand unimplemented")
}

func (s *ServerState) setPromiseTimeout(id string, timeout int) {
	s.promiseTimeouts = append([]PromiseTimeout{{id: id, timeout: timeout}},
		filter(s.promiseTimeouts, func(t PromiseTimeout) bool { return t.id != id })...)
}

func (s *ServerState) delPromiseTimeout(id string) {
	s.promiseTimeouts = filter(s.promiseTimeouts, func(t PromiseTimeout) bool { return t.id != id })
}

func (s *ServerState) setTaskTimeout(id string, kind, timeout int) {
	s.taskTimeouts = append([]TaskTimeout{{id: id, kind: kind, timeout: timeout}},
		filter(s.taskTimeouts, func(t TaskTimeout) bool { return !(t.id == id && t.kind == kind) })...)
}

func (s *ServerState) delTaskTimeout(id string) {
	s.taskTimeouts = filter(s.taskTimeouts, func(t TaskTimeout) bool { return t.id != id })
}

func (s *ServerState) setScheduleTimeout(id string, timeout int) {
	s.scheduleTimeouts = append([]ScheduleTimeout{{id: id, timeout: timeout}},
		filter(s.scheduleTimeouts, func(t ScheduleTimeout) bool { return t.id != id })...)
}

func (s *ServerState) delScheduleTimeout(id string) {
	s.scheduleTimeouts = filter(s.scheduleTimeouts, func(t ScheduleTimeout) bool { return t.id != id })
}

func (s *ServerState) setMessage(address string, msg Message) {
	entry := OutboxEntry{address: address, message: msg}
	key := entry.key()
	s.outbox = append([]OutboxEntry{entry},
		filter(s.outbox, func(e OutboxEntry) bool { return e.key() != key })...)
}

// ============================================================================
// Handlers — internal: resume  (spec/02-actions/00-resume.lean)
// ============================================================================

// enqueueResume — the settlement chain. Oracle-aligned (go-actor
// cascadeSettle, the port of the TS SDK's LocalNetwork.Server):
//   - version is bumped ONLY on acquire. A resume re-emits the CURRENT
//     version: the execute is a wake-up hint, not a fresh fencing token.
//   - no awaiter-deadline guard: the cascade touches the awaiter only
//     through its TASK state (an expired awaiter's own settlement fulfills
//     the task).
//   - the resumed task records its trigger (resumes := [awaitedId]);
//     buffered resumes are deduplicated.
//   - the state change does not require the awaiter promise; only the
//     message does -- and an absent/empty target sends nothing.
func (s *ServerState) enqueueResume(awaitedId, awaiterId string, now int) {
	t := s.getTask(awaiterId)
	if t == nil {
		return
	}
	switch t.state {
	case taskSuspended:
		retryTimeout := s.config.retryTimeout
		t.state = taskPending
		t.resumes = []string{awaitedId}
		s.setTask(*t)
		s.setTaskTimeout(t.id, 0, now+retryTimeout)
		p := s.getPromise(awaiterId)
		if p == nil {
			return
		}
		target := getD(p.tags.get("resonate:target"), "")
		if target != "" {
			s.setMessage(target, execute(t.id, t.version))
		}
	case taskPending, taskAcquired, taskHalted:
		if contains(t.resumes, awaitedId) {
			return
		}
		t.resumes = appended(t.resumes, awaitedId)
		s.setTask(*t)
	case taskFulfilled:
		return
	}
}

// ============================================================================
// Handlers — internal: timeouts  (spec/02-actions/02-timeouts.lean)
// ============================================================================

func (s *ServerState) onPromiseTimeout(id string, now int) {
	p := s.getPromise(id)
	if p == nil {
		return
	}
	if p.state != pending {
		return
	}
	listeners := p.listeners
	callbacks := p.callbacks
	if p.isTimer() {
		p.state = resolved
	} else {
		p.state = rejectedTimedout
	}
	p.settledAt = opt(p.timeoutAt)
	p.callbacks = []string{}
	p.listeners = []string{}
	s.setPromise(*p)
	s.delPromiseTimeout(p.id)
	if t := s.getTask(p.id); t != nil {
		t.state = taskFulfilled
		t.pid = nil
		t.ttl = nil
		t.resumes = []string{}
		s.setTask(*t)
		s.delTaskTimeout(t.id)
	}
	// settlement scrub: p can never be resumed again; drop its dead registrations
	for i := range s.promises {
		if s.promises[i].state == pending {
			s.promises[i].callbacks = removed(s.promises[i].callbacks, p.id)
		}
	}
	for _, address := range listeners {
		s.setMessage(address, unblock(p.toRecord()))
	}
	for _, awaiterId := range callbacks {
		s.enqueueResume(p.id, awaiterId, now)
	}
}

func (s *ServerState) onTaskRetryTimeout(id string, now int) {
	retryTimeout := s.config.retryTimeout
	t := s.getTask(id)
	if t == nil {
		return
	}
	if t.state != taskPending {
		return
	}
	s.delTaskTimeout(t.id)
	s.setTaskTimeout(t.id, 0, now+retryTimeout)
	p := s.getPromise(t.id)
	if p == nil {
		return
	}
	s.setMessage(getD(p.tags.get("resonate:target"), ""), execute(t.id, t.version))
}

func (s *ServerState) onTaskLeaseTimeout(id string, now int) {
	retryTimeout := s.config.retryTimeout
	t := s.getTask(id)
	if t == nil {
		return
	}
	if t.state != taskAcquired {
		return
	}
	t.state = taskPending
	t.pid = nil
	t.ttl = nil
	s.setTask(*t)
	s.delTaskTimeout(t.id)
	s.setTaskTimeout(t.id, 0, now+retryTimeout)
	p := s.getPromise(t.id)
	if p == nil {
		return
	}
	s.setMessage(getD(p.tags.get("resonate:target"), ""), execute(t.id, t.version))
}

func (s *ServerState) catchUp(now int, sch Schedule) Schedule {
	if sch.nextRunAt <= now {
		cronTime := sch.nextRunAt
		promiseId := expand(sch.promiseId, sch.id, cronTime)
		_ = s.promiseCreate(PromiseCreateReq{
			id: promiseId, timeoutAt: cronTime + sch.promiseTimeout,
			param: sch.promiseParam, tags: sch.promiseTags,
		}, cronTime)
		sch.lastRunAt = opt(cronTime)
		sch.nextRunAt = nextCron(sch.cron, cronTime)
		return s.catchUp(now, sch)
	}
	return sch
}

func (s *ServerState) onScheduleTimeout(id string, now int) {
	s0 := s.getSchedule(id)
	if s0 == nil {
		return
	}
	sch := s.catchUp(now, *s0)
	s.setSchedule(sch)
	s.delScheduleTimeout(sch.id)
	s.setScheduleTimeout(sch.id, sch.nextRunAt)
}

// ============================================================================
// Handlers — promises
// ============================================================================

// P-01 promise.get
func (s *ServerState) promiseGet(req PromiseGetReq, now int) PromiseGetRes {
	p := s.getPromise(req.id)
	if p == nil {
		return PromiseGetRes{status: 404}
	}
	if p.state == pending {
		if p.timeoutAt <= now {
			projected := *p
			if p.isTimer() {
				projected.state = resolved
			} else {
				projected.state = rejectedTimedout
			}
			projected.settledAt = opt(p.timeoutAt)
			return PromiseGetRes{status: 200, promise: opt(projected.toRecord())}
		}
		return PromiseGetRes{status: 200, promise: opt(p.toRecord())}
	}
	return PromiseGetRes{status: 200, promise: opt(p.toRecord())}
}

// P-02 promise.create
func (s *ServerState) promiseCreate(req PromiseCreateReq, now int) PromiseCreateRes {
	retryTimeout := s.config.retryTimeout
	if p := s.getPromise(req.id); p == nil {
		if req.timeoutAt > now {
			p := PromiseObject{
				id:        req.id,
				state:     pending,
				param:     req.param,
				tags:      req.tags,
				timeoutAt: req.timeoutAt,
				createdAt: now,
			}
			s.setPromise(p)
			if p.external() {
				s.setPromiseTimeout(p.id, p.timeoutAt)
			}
			target := p.tags.get("resonate:target")
			if target == nil {
				return PromiseCreateRes{status: 200, promise: opt(p.toRecord())}
			}
			t := TaskObject{id: p.id, state: taskPending, version: 0}
			s.setTask(t)
			delayStr := p.tags.get("resonate:delay")
			if delayStr == nil {
				s.setTaskTimeout(t.id, 0, now+retryTimeout)
				s.setMessage(*target, execute(t.id, t.version))
				return PromiseCreateRes{status: 200, promise: opt(p.toRecord())}
			}
			delay, _ := strconv.Atoi(*delayStr)
			if delay > now {
				s.setTaskTimeout(t.id, 0, delay)
				return PromiseCreateRes{status: 200, promise: opt(p.toRecord())}
			}
			s.setTaskTimeout(t.id, 0, now+retryTimeout)
			s.setMessage(*target, execute(t.id, t.version))
			return PromiseCreateRes{status: 200, promise: opt(p.toRecord())}
		}
		state := rejectedTimedout
		if req.tags.isTimer() {
			state = resolved
		}
		p := PromiseObject{
			id:        req.id,
			state:     state,
			param:     req.param,
			tags:      req.tags,
			timeoutAt: req.timeoutAt,
			createdAt: req.timeoutAt,
			settledAt: opt(req.timeoutAt),
		}
		s.setPromise(p)
		if p.tags.has("resonate:target") {
			t := TaskObject{
				id: p.id, state: taskFulfilled, version: 0,
				ttl: nil, pid: nil, resumes: []string{},
			}
			s.setTask(t)
			return PromiseCreateRes{status: 200, promise: opt(p.toRecord())}
		}
		return PromiseCreateRes{status: 200, promise: opt(p.toRecord())}
	} else {
		if p.state == pending && p.timeoutAt <= now {
			projected := *p
			if p.isTimer() {
				projected.state = resolved
			} else {
				projected.state = rejectedTimedout
			}
			projected.settledAt = opt(p.timeoutAt)
			return PromiseCreateRes{status: 200, promise: opt(projected.toRecord())}
		}
		return PromiseCreateRes{status: 200, promise: opt(p.toRecord())}
	}
}

// P-03 promise.settle
func (s *ServerState) promiseSettle(req PromiseSettleReq, now int) PromiseSettleRes {
	p := s.getPromise(req.id)
	if p == nil {
		return PromiseSettleRes{status: 404}
	}
	if p.state == pending {
		if p.timeoutAt > now {
			listeners := p.listeners
			callbacks := p.callbacks
			p.state = req.state
			p.value = req.value
			p.settledAt = opt(now)
			p.callbacks = []string{}
			p.listeners = []string{}
			s.setPromise(*p)
			s.delPromiseTimeout(p.id)
			if t := s.getTask(p.id); t != nil {
				t.state = taskFulfilled
				t.pid = nil
				t.ttl = nil
				t.resumes = []string{}
				s.setTask(*t)
				s.delTaskTimeout(t.id)
			}
			// settlement scrub: p can never be resumed again; drop its dead registrations
			for i := range s.promises {
				if s.promises[i].state == pending {
					s.promises[i].callbacks = removed(s.promises[i].callbacks, p.id)
				}
			}
			for _, address := range listeners {
				s.setMessage(address, unblock(p.toRecord()))
			}
			for _, awaiterId := range callbacks {
				s.enqueueResume(p.id, awaiterId, now)
			}
			return PromiseSettleRes{status: 200, promise: opt(p.toRecord())}
		}
		projected := *p
		if p.isTimer() {
			projected.state = resolved
		} else {
			projected.state = rejectedTimedout
		}
		projected.settledAt = opt(p.timeoutAt)
		return PromiseSettleRes{status: 200, promise: opt(projected.toRecord())}
	}
	return PromiseSettleRes{status: 200, promise: opt(p.toRecord())}
}

// P-04 promise.register_callback
func (s *ServerState) promiseRegisterCallback(req PromiseRegisterCallbackReq, now int) PromiseRegisterCallbackRes {
	pAwaited := s.getPromise(req.awaited)
	if pAwaited == nil {
		return PromiseRegisterCallbackRes{status: 404}
	}
	pAwaiter := s.getPromise(req.awaiter)
	if pAwaiter == nil {
		return PromiseRegisterCallbackRes{status: 422}
	}
	if !pAwaiter.tags.has("resonate:target") {
		return PromiseRegisterCallbackRes{status: 422}
	}
	if pAwaited.state == pending {
		if pAwaited.timeoutAt > now {
			if pAwaiter.state == pending && pAwaiter.timeoutAt > now {
				s.setPromise(pAwaited.addCallback(req.awaiter))
			}
			return PromiseRegisterCallbackRes{status: 200, promise: opt(pAwaited.toRecord())}
		}
		projected := *pAwaited
		if pAwaited.isTimer() {
			projected.state = resolved
		} else {
			projected.state = rejectedTimedout
		}
		projected.settledAt = opt(pAwaited.timeoutAt)
		return PromiseRegisterCallbackRes{status: 200, promise: opt(projected.toRecord())}
	}
	return PromiseRegisterCallbackRes{status: 200, promise: opt(pAwaited.toRecord())}
}

// P-05 promise.register_listener
func (s *ServerState) promiseRegisterListener(req PromiseRegisterListenerReq, now int) PromiseRegisterListenerRes {
	pAwaited := s.getPromise(req.awaited)
	if pAwaited == nil {
		return PromiseRegisterListenerRes{status: 404}
	}
	if pAwaited.state == pending {
		if pAwaited.timeoutAt > now {
			s.setPromise(pAwaited.addListener(req.address))
			return PromiseRegisterListenerRes{status: 200, promise: opt(pAwaited.toRecord())}
		}
		projected := *pAwaited
		if pAwaited.isTimer() {
			projected.state = resolved
		} else {
			projected.state = rejectedTimedout
		}
		projected.settledAt = opt(pAwaited.timeoutAt)
		return PromiseRegisterListenerRes{status: 200, promise: opt(projected.toRecord())}
	}
	return PromiseRegisterListenerRes{status: 200, promise: opt(pAwaited.toRecord())}
}

// P-06 promise.search — not yet specified (501)
func (s *ServerState) promiseSearch(req PromiseSearchReq, now int) PromiseSearchRes {
	return PromiseSearchRes{status: 501}
}

// ============================================================================
// Handlers — schedules
// ============================================================================

// S-01 schedule.get
func (s *ServerState) scheduleGet(req ScheduleGetReq, now int) ScheduleGetRes {
	sch := s.getSchedule(req.id)
	if sch == nil {
		return ScheduleGetRes{status: 404}
	}
	return ScheduleGetRes{status: 200, schedule: sch}
}

// S-02 schedule.create
func (s *ServerState) scheduleCreate(req ScheduleCreateReq, now int) ScheduleCreateRes {
	if sch := s.getSchedule(req.id); sch != nil {
		return ScheduleCreateRes{status: 200, schedule: sch}
	}
	sch := Schedule{
		id:             req.id,
		cron:           req.cron,
		promiseId:      req.promiseId,
		promiseTimeout: req.promiseTimeout,
		promiseParam:   req.promiseParam,
		promiseTags:    req.promiseTags,
		createdAt:      now,
		nextRunAt:      nextCron(req.cron, now),
		lastRunAt:      nil,
	}
	s.setSchedule(sch)
	s.setScheduleTimeout(sch.id, sch.nextRunAt)
	return ScheduleCreateRes{status: 200, schedule: &sch}
}

// S-03 schedule.delete
func (s *ServerState) scheduleDelete(req ScheduleDeleteReq, now int) ScheduleDeleteRes {
	sch := s.getSchedule(req.id)
	if sch == nil {
		return ScheduleDeleteRes{status: 404}
	}
	s.delSchedule(sch.id)
	s.delScheduleTimeout(sch.id)
	return ScheduleDeleteRes{status: 200}
}

// S-04 schedule.search — not yet specified (501)
func (s *ServerState) scheduleSearch(req ScheduleSearchReq, now int) ScheduleSearchRes {
	return ScheduleSearchRes{status: 501}
}

// ============================================================================
// Handlers — tasks
// ============================================================================

// T-01 task.get
func (s *ServerState) taskGet(req TaskGetReq, now int) TaskGetRes {
	t := s.getTask(req.id)
	if t == nil {
		return TaskGetRes{status: 404}
	}
	p := s.getPromise(t.id)
	if p == nil {
		return TaskGetRes{status: 404}
	}
	if p.state == pending && p.timeoutAt > now {
		return TaskGetRes{status: 200, task: opt(t.toRecord())}
	}
	projected := *t
	projected.state = taskFulfilled
	projected.pid = nil
	projected.ttl = nil
	projected.resumes = []string{}
	return TaskGetRes{status: 200, task: opt(projected.toRecord())}
}

// T-02 task.create
func (s *ServerState) taskCreate(req TaskCreateReq, now int) TaskCreateRes {
	a := req.action
	if p := s.getPromise(a.id); p == nil {
		if a.timeoutAt > now {
			p := PromiseObject{
				id: a.id, state: pending, param: a.param, tags: a.tags,
				timeoutAt: a.timeoutAt, createdAt: now,
			}
			s.setPromise(p)
			s.setPromiseTimeout(p.id, p.timeoutAt)
			t := TaskObject{
				id: p.id, state: taskAcquired, version: 1,
				ttl: opt(req.ttl), pid: opt(req.pid), resumes: []string{},
			}
			s.setTask(t)
			s.setTaskTimeout(t.id, 1, now+req.ttl)
			return TaskCreateRes{status: 200, task: opt(t.toRecord()), promise: opt(p.toRecord())}
		}
		st := rejectedTimedout
		if a.tags.isTimer() {
			st = resolved
		}
		p := PromiseObject{
			id: a.id, state: st, param: a.param, tags: a.tags,
			timeoutAt: a.timeoutAt, createdAt: a.timeoutAt, settledAt: opt(a.timeoutAt),
		}
		s.setPromise(p)
		t := TaskObject{
			id: p.id, state: taskFulfilled, version: 0,
			ttl: nil, pid: nil, resumes: []string{},
		}
		s.setTask(t)
		return TaskCreateRes{status: 200, task: opt(t.toRecord()), promise: opt(p.toRecord())}
	} else {
		if !p.tags.has("resonate:target") {
			return TaskCreateRes{status: 422}
		}
		if t := s.getTask(p.id); t != nil {
			if t.state == taskFulfilled {
				return TaskCreateRes{status: 200, task: opt(t.toRecord()), promise: opt(p.toRecord())}
			} else if t.state == taskPending {
				t.state = taskAcquired
				t.version = t.version + 1
				t.ttl = opt(req.ttl)
				t.pid = opt(req.pid)
				t.resumes = []string{}
				s.setTask(*t)
				s.delTaskTimeout(t.id)
				s.setTaskTimeout(t.id, 1, now+req.ttl)
				return TaskCreateRes{status: 200, task: opt(t.toRecord()), promise: opt(p.toRecord())}
			} else {
				return TaskCreateRes{status: 409}
			}
		} else {
			return TaskCreateRes{status: 409}
		}
	}
}

// T-03 task.acquire
func (s *ServerState) taskAcquire(req TaskAcquireReq, now int) TaskAcquireRes {
	t := s.getTask(req.id)
	if t == nil {
		return TaskAcquireRes{status: 404}
	}
	p := s.getPromise(t.id)
	if p == nil {
		return TaskAcquireRes{status: 409}
	}
	if t.state != taskPending {
		return TaskAcquireRes{status: 409}
	}
	if p.state != pending || p.timeoutAt <= now {
		return TaskAcquireRes{status: 409}
	}
	if t.version != req.version {
		return TaskAcquireRes{status: 409}
	}
	t.state = taskAcquired
	t.version = t.version + 1
	t.ttl = opt(req.ttl)
	t.pid = opt(req.pid)
	t.resumes = []string{}
	s.setTask(*t)
	s.delTaskTimeout(t.id)
	s.setTaskTimeout(t.id, 1, now+req.ttl)
	return TaskAcquireRes{status: 200, task: opt(t.toRecord()), promise: opt(p.toRecord())}
}

// T-04 task.fence
func (s *ServerState) taskFence(req TaskFenceReq, now int) TaskFenceRes {
	t := s.getTask(req.id)
	if t == nil {
		return TaskFenceRes{status: 404}
	}
	p := s.getPromise(t.id)
	if p == nil {
		return TaskFenceRes{status: 409}
	}
	if t.state != taskAcquired {
		return TaskFenceRes{status: 409}
	}
	if p.state != pending || p.timeoutAt <= now {
		return TaskFenceRes{status: 409}
	}
	if t.version != req.version {
		return TaskFenceRes{status: 409}
	}
	switch {
	case req.action.create != nil:
		res := s.promiseCreate(*req.action.create, now)
		return TaskFenceRes{status: 200, action: &TaskFenceInnerRes{create: &res}}
	case req.action.settle != nil:
		res := s.promiseSettle(*req.action.settle, now)
		return TaskFenceRes{status: 200, action: &TaskFenceInnerRes{settle: &res}}
	default:
		panic("task.fence: empty action")
	}
}

// T-05 task.heartbeat
func (s *ServerState) taskHeartbeat(req TaskHeartbeatReq, now int) TaskHeartbeatRes {
	for _, ref := range req.tasks {
		t := s.getTask(ref.id)
		if t == nil {
			continue
		}
		if t.state == taskAcquired && t.version == ref.version && eqStr(t.pid, req.pid) {
			p := s.getPromise(t.id)
			if p != nil {
				if p.state == pending && p.timeoutAt > now {
					s.delTaskTimeout(t.id)
					s.setTaskTimeout(t.id, 1, now+getDInt(t.ttl, 0))
				}
			}
		}
	}
	return TaskHeartbeatRes{status: 200}
}

// T-06 task.suspend
func (s *ServerState) taskSuspend(req TaskSuspendReq, now int) TaskSuspendRes {
	t := s.getTask(req.id)
	if t == nil {
		return TaskSuspendRes{status: 404}
	}
	tp := s.getPromise(t.id)
	if tp == nil {
		return TaskSuspendRes{status: 409}
	}
	if t.state != taskAcquired {
		return TaskSuspendRes{status: 409}
	}
	if tp.state != pending || tp.timeoutAt <= now {
		return TaskSuspendRes{status: 409}
	}
	if t.version != req.version {
		return TaskSuspendRes{status: 409}
	}
	settled := false
	for _, action := range req.actions {
		pa := s.getPromise(action.awaited)
		if pa == nil {
			return TaskSuspendRes{status: 422}
		}
		if pa.state != pending || pa.timeoutAt <= now {
			settled = true
		}
	}
	if settled {
		t.resumes = []string{}
		s.setTask(*t)
		return TaskSuspendRes{status: 300}
	}
	for _, action := range req.actions {
		if pa := s.getPromise(action.awaited); pa != nil {
			s.setPromise(pa.addCallback(req.id))
		}
	}
	t.state = taskSuspended
	t.pid = nil
	t.ttl = nil
	t.resumes = []string{}
	s.setTask(*t)
	s.delTaskTimeout(t.id)
	return TaskSuspendRes{status: 200}
}

// T-07 task.fulfill
func (s *ServerState) taskFulfill(req TaskFulfillReq, now int) TaskFulfillRes {
	t := s.getTask(req.id)
	if t == nil {
		return TaskFulfillRes{status: 404}
	}
	p := s.getPromise(t.id)
	if p == nil {
		return TaskFulfillRes{status: 409}
	}
	if t.state != taskAcquired {
		return TaskFulfillRes{status: 409}
	}
	if p.state != pending || p.timeoutAt <= now {
		return TaskFulfillRes{status: 409}
	}
	if t.version != req.version {
		return TaskFulfillRes{status: 409}
	}
	listeners := p.listeners
	callbacks := p.callbacks
	p.state = req.action.state
	p.value = req.action.value
	p.settledAt = opt(now)
	p.callbacks = []string{}
	p.listeners = []string{}
	s.setPromise(*p)
	s.delPromiseTimeout(p.id)
	t.state = taskFulfilled
	t.pid = nil
	t.ttl = nil
	t.resumes = []string{}
	s.setTask(*t)
	s.delTaskTimeout(t.id)
	// settlement scrub: p can never be resumed again; drop its dead registrations
	for i := range s.promises {
		if s.promises[i].state == pending {
			s.promises[i].callbacks = removed(s.promises[i].callbacks, p.id)
		}
	}
	for _, address := range listeners {
		s.setMessage(address, unblock(p.toRecord()))
	}
	for _, awaiterId := range callbacks {
		s.enqueueResume(p.id, awaiterId, now)
	}
	return TaskFulfillRes{status: 200, promise: opt(p.toRecord())}
}

// T-08 task.release
func (s *ServerState) taskRelease(req TaskReleaseReq, now int) TaskReleaseRes {
	retryTimeout := s.config.retryTimeout
	t := s.getTask(req.id)
	if t == nil {
		return TaskReleaseRes{status: 404}
	}
	p := s.getPromise(t.id)
	if p == nil {
		return TaskReleaseRes{status: 409}
	}
	if t.state != taskAcquired {
		return TaskReleaseRes{status: 409}
	}
	if p.state != pending || p.timeoutAt <= now {
		return TaskReleaseRes{status: 409}
	}
	if t.version != req.version {
		return TaskReleaseRes{status: 409}
	}
	t.state = taskPending
	t.pid = nil
	t.ttl = nil
	s.setTask(*t)
	s.delTaskTimeout(t.id)
	s.setTaskTimeout(t.id, 0, now+retryTimeout)
	s.setMessage(getD(p.tags.get("resonate:target"), ""), execute(t.id, t.version))
	return TaskReleaseRes{status: 200}
}

// T-09 task.halt
func (s *ServerState) taskHalt(req TaskHaltReq, now int) TaskHaltRes {
	t := s.getTask(req.id)
	if t == nil {
		return TaskHaltRes{status: 404}
	}
	if t.state == taskFulfilled {
		return TaskHaltRes{status: 409}
	}
	if t.state == taskHalted {
		return TaskHaltRes{status: 200}
	}
	t.state = taskHalted
	t.pid = nil
	t.ttl = nil
	s.setTask(*t)
	s.delTaskTimeout(t.id)
	return TaskHaltRes{status: 200}
}

// T-10 task.continue
func (s *ServerState) taskContinue(req TaskContinueReq, now int) TaskContinueRes {
	retryTimeout := s.config.retryTimeout
	t := s.getTask(req.id)
	if t == nil {
		return TaskContinueRes{status: 404}
	}
	if t.state != taskHalted {
		return TaskContinueRes{status: 409}
	}
	p := s.getPromise(t.id)
	if p == nil {
		return TaskContinueRes{status: 404}
	}
	t.state = taskPending
	s.setTask(*t)
	s.setTaskTimeout(t.id, 0, now+retryTimeout)
	s.setMessage(getD(p.tags.get("resonate:target"), ""), execute(t.id, t.version))
	return TaskContinueRes{status: 200}
}

// T-11 task.search — not yet specified (501)
func (s *ServerState) taskSearch(req TaskSearchReq, now int) TaskSearchRes {
	return TaskSearchRes{status: 501}
}

// ============================================================================
// Prelude — the fragments of Lean's Option/List used above.
// ============================================================================

// opt is Lean's `some`.
func opt[T any](v T) *T { return &v }

// getD is `Option.getD` for strings.
func getD(p *string, d string) string {
	if p != nil {
		return *p
	}
	return d
}

// getDInt is `Option.getD` for Nats.
func getDInt(p *int, d int) int {
	if p != nil {
		return *p
	}
	return d
}

// eqStr is `t.pid == some x`.
func eqStr(p *string, x string) bool {
	return p != nil && *p == x
}

// find is `List.find?` — returns a COPY, so callers may mutate it freely
// and only a setX write-back is observed (Lean value semantics).
func find[T any](xs []T, pred func(T) bool) *T {
	for i := range xs {
		if pred(xs[i]) {
			v := xs[i]
			return &v
		}
	}
	return nil
}

// filter is `List.filter`.
func filter[T any](xs []T, keep func(T) bool) []T {
	out := []T{}
	for _, x := range xs {
		if keep(x) {
			out = append(out, x)
		}
	}
	return out
}

// contains is `List.contains` for strings.
func contains(xs []string, x string) bool {
	for _, y := range xs {
		if y == x {
			return true
		}
	}
	return false
}

// appended is `xs ++ [x]`, always allocating a fresh list.
func appended(xs []string, x string) []string {
	out := make([]string, len(xs)+1)
	copy(out, xs)
	out[len(xs)] = x
	return out
}

// removed is `xs.filter (· != x)`.
func removed(xs []string, x string) []string {
	out := []string{}
	for _, y := range xs {
		if y != x {
			out = append(out, y)
		}
	}
	return out
}
