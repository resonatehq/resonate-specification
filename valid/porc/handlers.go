package model

import (
	"encoding/json"
	"strings"
)

// Protocol handlers, ported from spec/02-abstract/{p,m}.lean.
//
// ONE copy, taking a `Discipline`, because the two Lean files are the same
// code modulo viewPromise/viewTask vs touchPromise/touchTask — checked by
// diff before writing this. Guards are transcribed in the Lean's order,
// because order is observable: validation errors (400) outrank existence
// (404), which outranks state and version (409).
//
// Each handler mutates the receiver. The caller clones first, so the
// function porcupine sees is pure.

// Response is what a handler returns. Only `Status` and the fields a
// recorded trace actually carries are modelled — the checker compares
// responses, so anything the wire format does not report cannot be
// compared and would be invented detail.
// Response carries the RECORDS a handler returns, not just a status.
//
// The Lean checker decodes full `PromiseRecord`/`TaskRecord` values and
// compares them, so a Go response that carried only a status and a state
// would be checking strictly less than its counterpart — and a
// differential test between the two would pass on differences neither
// could see. Records it is.
type Response struct {
	Status  int
	Promise *Promise
	Task    *Task
	// Inner is the nested response a `task.fence` carries. A fence that
	// succeeds around a create that 404s is 200 outside and 404 inside,
	// and both are compared.
	Inner *InnerResponse
}

func promiseRes(status int, p *Promise) Response { return Response{Status: status, Promise: p} }

// ------------------------------------------------------------------ promises

func (s *ServerState) PromiseGet(d Discipline, id string, now uint64) Response {
	p := s.readPromise(d, id, now)
	if p == nil {
		s.note("P-01", "branch", "absent")
		return Response{Status: 404}
	}
	s.note("P-01", "branch", "found")
	return Response{Status: 200, Promise: p}
}

type PromiseCreateReq struct {
	ID        string
	TimeoutAt uint64
	Tags      Tags
	Param     json.RawMessage
}

func (s *ServerState) PromiseCreate(d Discipline, req PromiseCreateReq, now uint64) Response {
	if req.Tags.TimerTargeted() {
		s.note("P-02", "branch", "timer-targeted")
		return Response{Status: 400}
	}
	if p := s.readPromise(d, req.ID, now); p != nil {
		s.note("P-02", "branch", "idempotent-echo")
		return Response{Status: 200, Promise: p}
	}
	s.note("P-02", "branch", "created")
	if req.TimeoutAt > now {
		p := &Promise{ID: req.ID, State: Pending, Tags: req.Tags,
			TimeoutAt: req.TimeoutAt, CreatedAt: now, Param: req.Param}
		s.SetPromise(p)
		if p.Tags.Has("resonate:target") {
			// The delay tag seeds `retryAt`: the first dispatch is due at
			// the delay if it is still ahead, immediately otherwise.
			due := now
			if v, ok := p.Tags.Get("resonate:delay"); ok {
				if n := parseNat(v); n > due {
					due = n
				}
			}
			if _, ok := p.Tags.Get("resonate:delay"); ok {
				s.note("P-02", "birth", "born-live-targeted-delayed")
			} else {
				s.note("P-02", "birth", "born-live-targeted")
			}
			s.SetTask(&Task{ID: p.ID, State: TaskPending, Version: 0, RetryAt: u64p(due)})
		} else {
			s.note("P-02", "birth", "born-live-untargeted")
		}
		return Response{Status: 200, Promise: p}
	}
	// Born past its deadline: fact P holds at birth, so the promise is
	// written settled and its task (if targeted) fulfilled.
	st := RejectedTimedout
	if req.Tags.IsTimer() {
		st = Resolved
	}
	p := &Promise{ID: req.ID, State: st, Tags: req.Tags, TimeoutAt: req.TimeoutAt,
		CreatedAt: req.TimeoutAt, SettledAt: u64p(req.TimeoutAt), Param: req.Param}
	s.SetPromise(p)
	if req.Tags.IsTimer() {
		s.note("P-02", "birth", "born-dead-timer-resolved")
	} else {
		s.note("P-02", "birth", "born-dead-rejected-timedout")
	}
	if p.Tags.Has("resonate:target") {
		s.note("P-02", "birth", "born-dead-targeted-task-fulfilled")
		s.SetTask(&Task{ID: p.ID, State: TaskFulfilled, Version: 0})
	}
	return Response{Status: 200, Promise: p}
}

func (s *ServerState) PromiseSettle(d Discipline, id string, st PromiseState, val json.RawMessage, now uint64) Response {
	if !st.Settable() {
		s.note("P-03", "branch", "unsettable")
		return Response{Status: 400}
	}
	p := s.readPromise(d, id, now)
	if p == nil {
		s.note("P-03", "branch", "absent")
		return Response{Status: 404}
	}
	if p.State == Pending {
		s.note("P-03", "branch", "settled")
		q := p.clone()
		q.State = st
		q.SettledAt = u64p(now)
		q.Value = val
		// The promise and its task pair, coupled. The awaiters and
		// listeners stay on the promise for the batch internal steps — that is
		// what makes the model nondeterministic.
		s.SetSettled(q)
		return Response{Status: 200, Promise: q}
	}
	s.note("P-03", "branch", "already-settled")
	return Response{Status: 200, Promise: p}
}

func (s *ServerState) PromiseRegisterCallback(d Discipline, awaited, awaiter string, now uint64) Response {
	if awaited == awaiter {
		s.note("P-04", "branch", "self")
		return Response{Status: 400}
	}
	pa := s.readPromise(d, awaited, now)
	if pa == nil {
		s.note("P-04", "branch", "awaited-absent")
		return Response{Status: 404}
	}
	pw := s.readPromise(d, awaiter, now)
	if pw == nil {
		s.note("P-04", "branch", "awaiter-absent")
		return Response{Status: 422}
	}
	if !pw.Tags.Has("resonate:target") {
		s.note("P-04", "branch", "awaiter-untargeted")
		return Response{Status: 422}
	}
	if !pa.External() {
		s.note("P-04", "branch", "awaited-internal")
		return Response{Status: 422}
	}
	if pa.State == Pending && pw.State == Pending {
		// One of two doors an awaits-edge can come through. This one leaves
		// the awaiter RUNNING, so the drain buffers rather than wakes.
		s.note("P-04", "callback", "registered")
		s.SetPromise(pa.AddCallback(awaiter))
	} else if pa.State != Pending {
		s.note("P-04", "callback", "awaited-settled")
	} else {
		s.note("P-04", "callback", "awaiter-not-live")
	}
	return Response{Status: 200, Promise: pa}
}

// ---------------------------------------------------------------------- tasks

func (s *ServerState) TaskGet(d Discipline, id string, now uint64) Response {
	t, p := s.readTask(d, id, now)
	if t == nil {
		s.note("T-01", "branch", "task-absent")
		return Response{Status: 404}
	}
	if p == nil {
		s.note("T-01", "branch", "promise-absent")
		return Response{Status: 404}
	}
	s.note("T-01", "branch", "found")
	return Response{Status: 200, Task: t}
}

func (s *ServerState) TaskAcquire(d Discipline, id string, version uint64, pid string, ttl uint64, now uint64) Response {
	t, p := s.readTask(d, id, now)
	if t == nil {
		s.note("T-03", "branch", "task-absent")
		return Response{Status: 404}
	}
	if p == nil {
		s.note("T-03", "branch", "promise-absent")
		return Response{Status: 409}
	}
	if t.State != TaskPending {
		s.note("T-03", "branch", "task-wrong-state")
		return Response{Status: 409}
	}
	if p.State != Pending {
		s.note("T-03", "branch", "promise-not-live")
		return Response{Status: 409}
	}
	if t.Version != version {
		s.note("T-03", "branch", "version-mismatch")
		return Response{Status: 409}
	}
	u := t.clone()
	u.State = TaskAcquired
	u.Version = t.Version + 1
	u.TTL, u.PID = u64p(ttl), strp(pid)
	u.ExpiresAt = u64p(now + ttl)
	u.RetryAt, u.Resumes = nil, nil
	s.note("T-03", "branch", "acquired")
	s.SetTask(u)
	// `taskAcquire` returns BOTH records in the Lean —
	// `{ status, task := some t.toRecord, promise := some p.toRecord }` —
	// and the capture carries both, so both are compared.
	return Response{Status: 200, Task: u, Promise: p}
}

// TaskSuspend parks an acquired task on awaited promises. `300` if any
// awaited promise is already settled — the client must re-check rather
// than sleep.
func (s *ServerState) TaskSuspend(d Discipline, id string, version uint64, awaited []string, now uint64) Response {
	if len(awaited) == 0 {
		s.note("T-06", "branch", "empty-actions")
		return Response{Status: 400}
	}
	seen := map[string]bool{}
	for _, a := range awaited {
		if a == id {
			s.note("T-06", "branch", "self-awaited")
			return Response{Status: 400}
		}
		if seen[a] {
			s.note("T-06", "branch", "duplicate-awaited")
			return Response{Status: 400}
		}
		seen[a] = true
	}
	t, tp := s.readTask(d, id, now)
	if t == nil {
		s.note("T-06", "branch", "task-absent")
		return Response{Status: 404}
	}
	if tp == nil {
		s.note("T-06", "branch", "promise-absent")
		return Response{Status: 409}
	}
	if t.State != TaskAcquired {
		s.note("T-06", "branch", "task-wrong-state")
		return Response{Status: 409}
	}
	if tp.State != Pending {
		s.note("T-06", "branch", "promise-not-live")
		return Response{Status: 409}
	}
	if t.Version != version {
		s.note("T-06", "branch", "version-mismatch")
		return Response{Status: 409}
	}
	// Pass 1: stop at the first undischargeable waiter.
	anySettled := false
	for _, a := range awaited {
		pa := s.readPromise(d, a, now)
		if pa == nil || !pa.External() {
			s.note("T-06", "branch", "awaited-unusable")
			return Response{Status: 422}
		}
		if pa.State != Pending {
			anySettled = true
		}
	}
	if anySettled {
		s.note("T-06", "branch", "awaited-already-settled")
		u := t.clone()
		u.Resumes = nil
		s.SetTask(u)
		return Response{Status: 300}
	}
	s.note("T-06", "branch", "suspended")
	// Pass 2: park the awaiter on every awaited promise.
	for _, a := range awaited {
		if pa := s.readPromise(d, a, now); pa != nil {
			// The other door. This one PARKS the task, so the drain finds it
			// suspended and wakes it.
			s.note("T-06", "callback", "registered")
			s.SetPromise(pa.AddCallback(id))
		}
	}
	u := t.clone()
	u.State = TaskSuspended
	u.PID, u.TTL, u.ExpiresAt, u.RetryAt = nil, nil, nil, nil
	u.Resumes = nil
	s.SetTask(u)
	return Response{Status: 200}
}

func (s *ServerState) TaskFulfill(d Discipline, id string, version uint64, st PromiseState, val json.RawMessage, now uint64) Response {
	if !st.Settable() {
		return Response{Status: 400}
	}
	t, p := s.readTask(d, id, now)
	if t == nil {
		s.note("T-07", "branch", "task-absent")
		return Response{Status: 404}
	}
	if p == nil {
		s.note("T-07", "branch", "promise-absent")
		return Response{Status: 409}
	}
	if t.State != TaskAcquired {
		s.note("T-07", "branch", "task-wrong-state")
		return Response{Status: 409}
	}
	if p.State != Pending {
		s.note("T-07", "branch", "promise-not-live")
		return Response{Status: 409}
	}
	if t.Version != version {
		s.note("T-07", "branch", "version-mismatch")
		return Response{Status: 409}
	}
	q := p.clone()
	q.State = st
	q.SettledAt = u64p(now)
	q.Value = val
	// The promise and its own task, coupled: this settle fulfils the task
	// it was issued against, in the same step.
	s.note("T-07", "branch", "fulfilled")
	s.SetSettled(q)
	return Response{Status: 200, Promise: q}
}

func (s *ServerState) TaskRelease(d Discipline, id string, version uint64, now uint64) Response {
	t, p := s.readTask(d, id, now)
	if t == nil {
		s.note("T-08", "branch", "task-absent")
		return Response{Status: 404}
	}
	if p == nil {
		s.note("T-08", "branch", "promise-absent")
		return Response{Status: 409}
	}
	if t.State != TaskAcquired {
		s.note("T-08", "branch", "task-wrong-state")
		return Response{Status: 409}
	}
	if p.State != Pending {
		s.note("T-08", "branch", "promise-not-live")
		return Response{Status: 409}
	}
	if t.Version != version {
		s.note("T-08", "branch", "version-mismatch")
		return Response{Status: 409}
	}
	u := t.clone()
	u.State = TaskPending
	u.PID, u.TTL, u.ExpiresAt = nil, nil, nil
	u.RetryAt = u64p(now)
	s.note("T-08", "branch", "released")
	s.SetTask(u)
	return Response{Status: 200}
}

// TaskRef is one (id, version) a heartbeat names.
type TaskRef struct {
	ID      string
	Version uint64
}

// TaskHeartbeat is T-05, from `taskHeartbeat` in
// spec/02-abstract/external-steps-p.lean.
//
// It extends the lease of the REFERENCED tasks only, and only when the
// version matches — `heartbeatOne` checks
// `t.version == ref.version ∧ t.pid == some pid`.
//
// An earlier version here swept every acquired task belonging to the pid
// and ignored both the request's task list and the version. That is
// invisible on the response channel, which always answers 200, but it
// writes `expiresAt` on tasks the request never named — and `expiresAt`
// is what R5 `leaseExpiry` guards on. A checker built on it would accept
// runs the specification forbids.
func (s *ServerState) TaskHeartbeat(d Discipline, pid string, refs []TaskRef, now uint64) Response {
	for _, ref := range refs {
		t, p := s.readTask(d, ref.ID, now)
		if t == nil || p == nil {
			s.note("T-05", "branch", "task-absent")
			continue
		}
		if t.State == TaskAcquired && t.Version == ref.Version &&
			t.PID != nil && *t.PID == pid && p.State == Pending {
			s.note("T-05", "branch", "lease-extended")
			u := t.clone()
			ttl := uint64(0)
			if t.TTL != nil {
				ttl = *t.TTL
			}
			u.ExpiresAt = u64p(now + ttl)
			s.SetTask(u)
		} else {
			s.note("T-05", "branch", "refused")
		}
	}
	return Response{Status: 200}
}

// The three search handlers are `501` in the specification — P-06, T-11
// and S-04 are all "not yet specified". Modelled so that a trace
// containing one is CHECKED rather than rejected by the loader: a 501 is
// a response like any other, and a server answering something else to a
// search is a divergence worth catching.
func (s *ServerState) Search() Response { return Response{Status: 501} }

func parseNat(s string) uint64 {
	var n uint64
	for _, c := range s {
		n = n*10 + uint64(c-'0')
	}
	return n
}

// PromiseRegisterListener subscribes an address for an `unblock` when the
// promise settles. External promises only — a waiter may attach only where
// an armed timeout guarantees discharge.
//
// Ported for the fuzzer: nothing in the recorded captures registers a
// listener, so R3 `notify` was unreachable and therefore untested.
func (s *ServerState) PromiseRegisterListener(d Discipline, awaited, address string, now uint64) Response {
	if !addressValid(address) {
		s.note("P-05", "branch", "bad-address")
		return Response{Status: 400}
	}
	pa := s.readPromise(d, awaited, now)
	if pa == nil {
		s.note("P-05", "branch", "awaited-absent")
		return Response{Status: 404}
	}
	if !pa.External() {
		s.note("P-05", "branch", "awaited-internal")
		return Response{Status: 422}
	}
	if pa.State == Pending {
		s.note("P-05", "branch", "registered")
		s.SetPromise(pa.AddListener(address))
	} else {
		s.note("P-05", "branch", "awaited-settled")
	}
	return Response{Status: 200, Promise: pa}
}

// addressValid is `ServerModel.addressValid`.
func addressValid(a string) bool {
	return strings.HasPrefix(a, "http://") || strings.HasPrefix(a, "https://") ||
		(strings.HasPrefix(a, "poll://") && strings.ContainsRune(a, '@'))
}

func (s *ServerState) TaskHalt(d Discipline, id string, now uint64) Response {
	t, p := s.readTask(d, id, now)
	if t == nil {
		s.note("T-09", "branch", "task-absent")
		return Response{Status: 404}
	}
	if p == nil {
		s.note("T-09", "branch", "promise-absent")
		return Response{Status: 404}
	}
	if t.State == TaskFulfilled {
		s.note("T-09", "branch", "already-fulfilled")
		return Response{Status: 409}
	}
	if t.State == TaskHalted {
		s.note("T-09", "branch", "already-halted")
		return Response{Status: 200}
	}
	s.note("T-09", "branch", "halted")
	u := t.clone()
	u.State = TaskHalted
	u.PID, u.TTL, u.ExpiresAt, u.RetryAt = nil, nil, nil, nil
	s.SetTask(u)
	return Response{Status: 200}
}

func (s *ServerState) TaskContinue(d Discipline, id string, now uint64) Response {
	t, p := s.readTask(d, id, now)
	if t == nil {
		s.note("T-10", "branch", "task-absent")
		return Response{Status: 404}
	}
	if t.State != TaskHalted {
		s.note("T-10", "branch", "not-halted")
		return Response{Status: 409}
	}
	if p == nil {
		s.note("T-10", "branch", "promise-absent")
		return Response{Status: 404}
	}
	if p.State != Pending {
		s.note("T-10", "branch", "promise-not-live")
		return Response{Status: 409}
	}
	s.note("T-10", "branch", "continued")
	u := t.clone()
	u.State = TaskPending
	u.RetryAt = u64p(now)
	s.SetTask(u)
	return Response{Status: 200}
}

// FenceAction is the create-or-settle a fence carries.
type FenceAction struct {
	Kind      string // "promise.create" | "promise.settle"
	ID        string
	TimeoutAt uint64
	Tags      Tags
	State     PromiseState
	Param     json.RawMessage
	Value     json.RawMessage
}

// TargetID is `TaskFenceAction.targetId` — the promise the action
// operates on, whichever variant it is.
func (a FenceAction) TargetID() string { return a.ID }

// InnerResponse is the nested `{kind, head, data}` a fence returns.
type InnerResponse struct {
	Kind    string
	Status  int
	Promise *Promise
}

// TaskFence is T-04, transcribed from `taskFence` in
// spec/02-abstract/external-steps-p.lean, guard
// for guard.
//
// The validation guard is FIRST — an action operating on the fencing task
// itself is 400, ahead of existence and version — which is the same
// precedence discipline `precedence_test.go` pins for every other handler.
//
// `preload` is NOT modelled. `TaskFenceRes.preload` defaults to `[]` and
// no handler in the specification ever sets it, while the server populates
// it. That is a genuine gap in the specification, not an oversight here;
// comparing it would refute every fence for a channel the spec does not
// describe.
func (s *ServerState) TaskFence(d Discipline, id string, version uint64, act FenceAction, now uint64) (Response, *InnerResponse) {
	if act.TargetID() == id {
		s.note("T-04", "branch", "self-target")
		return Response{Status: 400}, nil
	}
	t, p := s.readTask(d, id, now)
	if t == nil {
		s.note("T-04", "branch", "task-absent")
		return Response{Status: 404}, nil
	}
	if p == nil {
		s.note("T-04", "branch", "promise-absent")
		return Response{Status: 409}, nil
	}
	if t.State != TaskAcquired {
		s.note("T-04", "branch", "task-wrong-state")
		return Response{Status: 409}, nil
	}
	if p.State != Pending {
		s.note("T-04", "branch", "promise-not-live")
		return Response{Status: 409}, nil
	}
	if t.Version != version {
		s.note("T-04", "branch", "version-mismatch")
		return Response{Status: 409}, nil
	}
	switch act.Kind {
	case "promise.create":
		s.note("T-04", "branch", "fenced-create")
		r := s.PromiseCreate(d, PromiseCreateReq{act.ID, act.TimeoutAt, act.Tags, act.Param}, now)
		return Response{Status: 200}, &InnerResponse{act.Kind, r.Status, r.Promise}
	case "promise.settle":
		s.note("T-04", "branch", "fenced-settle")
		r := s.PromiseSettle(d, act.ID, act.State, act.Value, now)
		return Response{Status: 200}, &InnerResponse{act.Kind, r.Status, r.Promise}
	}
	return Response{Status: 400}, nil
}

// TaskCreate is T-02, transcribed from `taskCreate` in
// spec/02-abstract/external-steps-p.lean.
//
// Two shapes in one handler: create a promise with an immediately-acquired
// task, or re-acquire an existing pending one. The SDK issues it for every
// root workflow, so without it a recorded trace has no promise to explain
// anything against — which is exactly how the first end-to-end run refuted
// at event 0.
//
// The validation guard is first, as everywhere: an action without
// `resonate:target` is 400 before existence is consulted.
func (s *ServerState) TaskCreate(d Discipline, pid string, ttl uint64, act PromiseCreateReq, now uint64) Response {
	if !act.Tags.Has("resonate:target") || act.Tags.TimerTargeted() {
		s.note("T-02", "branch", "malformed-action")
		return Response{Status: 400}
	}
	p := s.readPromise(d, act.ID, now)
	if p == nil {
		if act.TimeoutAt > now {
			np := &Promise{ID: act.ID, State: Pending, Tags: act.Tags,
				TimeoutAt: act.TimeoutAt, CreatedAt: now, Param: act.Param}
			s.SetPromise(np)
			nt := &Task{ID: np.ID, State: TaskAcquired, Version: 1,
				TTL: u64p(ttl), PID: strp(pid), ExpiresAt: u64p(now + ttl)}
			s.note("T-02", "branch", "born-live-acquired")
			s.SetTask(nt)
			return Response{Status: 200, Task: nt, Promise: np}
		}
		// Born past its deadline: fact P holds at birth. Targeted,
		// therefore not a timer, so this is the only verdict here.
		np := &Promise{ID: act.ID, State: RejectedTimedout, Tags: act.Tags, TimeoutAt: act.TimeoutAt,
			CreatedAt: act.TimeoutAt, SettledAt: u64p(act.TimeoutAt), Param: act.Param}
		s.SetPromise(np)
		nt := &Task{ID: np.ID, State: TaskFulfilled, Version: 0}
		s.note("T-02", "branch", "born-dead-fulfilled")
		s.SetTask(nt)
		return Response{Status: 200, Task: nt, Promise: np}
	}
	if !p.Tags.Has("resonate:target") {
		s.note("T-02", "branch", "promise-untargeted")
		return Response{Status: 422}
	}
	t, tp := s.readTask(d, p.ID, now)
	if t == nil || tp == nil {
		s.note("T-02", "branch", "task-absent")
		return Response{Status: 409}
	}
	switch t.State {
	case TaskFulfilled:
		s.note("T-02", "branch", "already-fulfilled")
		return Response{Status: 200, Task: t, Promise: tp}
	case TaskPending:
		s.note("T-02", "branch", "reacquired")
		u := t.clone()
		u.State = TaskAcquired
		u.Version = t.Version + 1
		u.TTL, u.PID = u64p(ttl), strp(pid)
		u.ExpiresAt = u64p(now + ttl)
		u.RetryAt, u.Resumes = nil, nil
		s.SetTask(u)
		return Response{Status: 200, Task: u, Promise: tp}
	default:
		s.note("T-02", "branch", "task-not-pending")
		return Response{Status: 409}
	}
}
