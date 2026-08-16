package model

import (
	"encoding/json"
	"fmt"
	"sort"
	"strings"
)

// Coverage-directed trace generation.
//
// `gen.go` generates RANDOM scripts for differential fuzzing: the question
// there is whether two checkers agree, and a random corpus answers it. The
// question here is different — which distinct behaviours of the machine does
// a corpus exercise, and what is the SMALLEST set of readable traces that
// exercises all of them. That is a set-cover problem, not a sampling one.
//
// ## The coverage domain
//
// A bucket is one observable outcome class: the request kind, the status,
// and the facts about the pre-state that decided WHICH branch produced that
// status. `promise.create` returning 200 is not one behaviour — it is nine,
// and a corpus that reaches one of them has not covered the handler.
//
// The classifier below is OBSERVATIONAL: it reconstructs the branch from
// (request, pre-state, response) rather than reading a label the handler
// emitted. That is a deliberate approximation with a known limit — two spec
// exits that agree on all three are one bucket here. Instrumenting the Lean
// handlers with explicit exit labels would remove the approximation; until
// then, a bucket is a lower bound on the distinctions the spec draws, never
// an upper one.
//
// ## Why the τs are kept
//
// `Run` discards internal steps, because the CHECKERS must rediscover a
// schedule. A test corpus wants the opposite. A harness that can drive the
// server's internal loop replays the schedule literally, and then every
// response is forced: no quiescence assumption, no set-valued assertion, and
// the stages of the wake pipeline become directly assertable rather than
// collapsed. So each case is emitted twice — driven (τs included) and
// observational (τs erased, the existing wire format, still consumed
// unchanged by `lincheck` and `lake exe checktrace`).

// ---------------------------------------------------------------- facts

// promiseFact names the pre-state of a promise as the handlers see it: the
// three-valued liveness the specification turns on, not the stored state.
//
//	absent          no such promise
//	live            pending, deadline ahead
//	logically-dead  pending in the store, deadline passed — the projection
//	                reports it settled and no τ has persisted that yet
//	<state>         materially settled
func promiseFact(s *ServerState, id string, now uint64) string {
	p := s.GetPromise(id)
	if p == nil {
		return "absent"
	}
	if p.State != Pending {
		return promiseWire[p.State]
	}
	if p.TimeoutAt > now {
		return "live"
	}
	return "logically-dead"
}

func taskFact(s *ServerState, id string, now uint64) string {
	t := s.GetTask(id)
	if t == nil {
		return "absent"
	}
	f := taskWireName(t.State)
	if t.State == TaskAcquired && t.ExpiresAt != nil {
		if *t.ExpiresAt <= now {
			f += ".lease-expired"
		} else {
			f += ".lease-live"
		}
	}
	return f
}

func taskWireName(st TaskState) string {
	switch st {
	case TaskPending:
		return "pending"
	case TaskAcquired:
		return "acquired"
	case TaskSuspended:
		return "suspended"
	case TaskHalted:
		return "halted"
	default:
		return "fulfilled"
	}
}

// tagShape is the birth shape of a promise, which decides whether it carries
// a task, an armed deadline, or neither.
func tagShape(t Tags) string {
	switch {
	case t.TimerTargeted():
		return "timer-targeted"
	case t.IsTimer():
		return "timer"
	case t.Has("resonate:target") && t.Has("resonate:delay"):
		return "targeted-delayed"
	case t.Has("resonate:target"):
		return "targeted"
	case t.Has("resonate:external"):
		return "external"
	default:
		return "internal"
	}
}

func versionFact(want, got uint64) string {
	switch {
	case want == got:
		return "version-current"
	case want > got:
		return "version-future"
	default:
		return "version-stale"
	}
}

// The classifier is gone.
//
// What stood between here and the script DSL was ~200 lines reconstructing,
// from (request, pre-state, response), which branch each handler had taken.
// The handlers now say so themselves, and `bucketsOf` reads the log. Three
// bugs went with the twenty-line version of this that covered the drain
// alone; this was five times its size.

func containsStr(xs []string, x string) bool {
	for _, s := range xs {
		if s == x {
			return true
		}
	}
	return false
}

// ------------------------------------------------------- the script DSL

type scriptBuilder struct {
	steps []step
	now   uint64
}

func newScript(start uint64) *scriptBuilder { return &scriptBuilder{now: start} }

func (b *scriptBuilder) at(n uint64) *scriptBuilder { b.now = n; return b }

func (b *scriptBuilder) tick(d uint64) *scriptBuilder { b.now += d; return b }

func (b *scriptBuilder) op(o Op) *scriptBuilder {
	o.Now = b.now
	if o.Tags == nil {
		o.Tags = Tags{}
	}
	b.steps = append(b.steps, step{op: &o, now: b.now})
	return b
}

func (b *scriptBuilder) tau(name, arg, arg2 string) *scriptBuilder {
	b.steps = append(b.steps, step{internal: name, arg: arg, arg2: arg2, now: b.now})
	return b
}

// ------------------------------------------------------------ templates

const origin = "o"

func oid(s string) string { return origin + "." + s }

func tagsExternal() Tags {
	return Tags{"resonate:external": "true", "resonate:origin": origin}
}
func tagsTargeted() Tags {
	return Tags{"resonate:target": "poll://any@w1", "resonate:origin": origin}
}
func tagsTargetedDelay(d uint64) Tags {
	return Tags{"resonate:target": "poll://any@w1", "resonate:delay": fmt.Sprintf("%d", d),
		"resonate:origin": origin}
}
func tagsTimer() Tags {
	return Tags{"resonate:timer": "true", "resonate:external": "true", "resonate:origin": origin}
}
func tagsTimerTargeted() Tags {
	return Tags{"resonate:timer": "true", "resonate:target": "poll://any@w1",
		"resonate:origin": origin}
}
func tagsInternal() Tags { return Tags{"resonate:origin": origin} }

// scenario is a named skeleton. The name survives into the emitted corpus
// only as provenance; the case is named for the bucket it witnesses.
type scenario struct {
	name  string
	build func() []step
}

// pcreate, tcreate and friends keep the templates readable.
func pcreate(id string, to uint64, tags Tags) Op {
	return Op{Kind: "promise.create", ID: id, TimeoutAt: to, Tags: tags}
}
func pget(id string) Op    { return Op{Kind: "promise.get", ID: id} }
func tget(id string) Op    { return Op{Kind: "task.get", ID: id} }
func psettle(id string, st PromiseState) Op {
	return Op{Kind: "promise.settle", ID: id, State: st}
}
func pcallback(awaited, awaiter string) Op {
	return Op{Kind: "promise.register_callback", ID: awaited, Awaiter: awaiter}
}
func plisten(awaited, addr string) Op {
	return Op{Kind: "promise.register_listener", ID: awaited, PID: addr}
}
func tcreate(id, pid string, ttl, to uint64, tags Tags) Op {
	return Op{Kind: "task.create", ID: id, PID: pid, TTL: ttl,
		Action: &FenceAction{Kind: "promise.create", ID: id, TimeoutAt: to, Tags: tags}}
}
func tacquire(id string, v uint64, pid string, ttl uint64) Op {
	return Op{Kind: "task.acquire", ID: id, Version: v, PID: pid, TTL: ttl}
}
func tsuspend(id string, v uint64, awaited ...string) Op {
	return Op{Kind: "task.suspend", ID: id, Version: v, Awaited: awaited}
}
func tfulfill(id string, v uint64, st PromiseState) Op {
	return Op{Kind: "task.fulfill", ID: id, Version: v, State: st}
}
func trelease(id string, v uint64) Op {
	return Op{Kind: "task.release", ID: id, Version: v}
}
func thalt(id string) Op     { return Op{Kind: "task.halt", ID: id} }
func tcontinue(id string) Op { return Op{Kind: "task.continue", ID: id} }
func theartbeat(pid string, refs ...TaskRef) Op {
	return Op{Kind: "task.heartbeat", PID: pid, Refs: refs}
}
func tfenceCreate(id string, v uint64, target string, to uint64, tags Tags) Op {
	return Op{Kind: "task.fence", ID: id, Version: v,
		Action: &FenceAction{Kind: "promise.create", ID: target, TimeoutAt: to, Tags: tags}}
}
func tfenceSettle(id string, v uint64, target string, st PromiseState) Op {
	return Op{Kind: "task.fence", ID: id, Version: v,
		Action: &FenceAction{Kind: "promise.settle", ID: target, State: st}}
}

// scenarios is the hand-designed half of the corpus: one skeleton per region
// of the semantic state space that the machine can be driven into. The
// search below adds whatever these miss, and the coverage report names
// whatever neither reaches.
func scenarios() []scenario {
	a, x, i, m, g := oid("a"), oid("x"), oid("i"), oid("m"), oid("ghost")
	y := oid("y")

	return []scenario{
		{"promise lifecycle, external", func() []step {
			return newScript(1000).
				op(pcreate(a, 5000, tagsExternal())).
				tick(10).op(pget(a)).
				tick(10).op(psettle(a, Resolved)).
				tick(10).op(pget(a)).steps
		}},
		{"promise create is idempotent", func() []step {
			return newScript(1000).
				op(pcreate(a, 5000, tagsExternal())).
				tick(10).op(pcreate(a, 9000, tagsInternal())).steps
		}},
		{"promise born past its deadline", func() []step {
			return newScript(1000).
				op(pcreate(a, 500, tagsExternal())).
				tick(10).op(pget(a)).steps
		}},
		{"timer born past its deadline resolves", func() []step {
			return newScript(1000).
				op(pcreate(m, 500, tagsTimer())).
				tick(10).op(pget(m)).steps
		}},
		{"a timer is never targeted", func() []step {
			return newScript(1000).
				op(pcreate(m, 5000, tagsTimerTargeted())).
				tick(10).op(tcreate(y, "p0", 500, 5000, tagsTimerTargeted())).steps
		}},
		{"settlement refusals", func() []step {
			return newScript(1000).
				op(pcreate(a, 5000, tagsExternal())).
				tick(10).op(psettle(a, Pending)).
				tick(10).op(psettle(a, RejectedTimedout)).
				tick(10).op(psettle(g, Resolved)).
				tick(10).op(psettle(a, RejectedCanceled)).
				tick(10).op(psettle(a, Rejected)).steps
		}},
		{"settle a logically dead promise", func() []step {
			return newScript(1000).
				op(pcreate(a, 1500, tagsExternal())).
				at(2000).op(psettle(a, Resolved)).
				tick(10).op(pget(a)).steps
		}},
		{"listeners", func() []step {
			return newScript(1000).
				op(pcreate(a, 5000, tagsExternal())).
				tick(10).op(pcreate(i, 5000, tagsInternal())).
				tick(10).op(plisten(a, "nonsense")).
				tick(10).op(plisten(a, "poll://any@w1")).
				tick(10).op(plisten(a, "https://l")).
				tick(10).op(plisten(i, "https://l")).
				tick(10).op(plisten(g, "https://l")).
				tick(10).op(psettle(a, Resolved)).
				tick(10).op(plisten(a, "https://late")).
				tick(10).tau("R3", a, "https://l").steps
		}},
		{"callbacks", func() []step {
			return newScript(1000).
				op(pcreate(a, 5000, tagsExternal())).
				tick(10).op(pcreate(i, 5000, tagsInternal())).
				tick(10).op(tcreate(x, "p0", 500, 5000, tagsTargeted())).
				tick(10).op(pcallback(a, a)).
				tick(10).op(pcallback(g, x)).
				tick(10).op(pcallback(a, g)).
				tick(10).op(pcallback(a, i)).
				tick(10).op(pcallback(i, x)).
				tick(10).op(pcallback(a, x)).steps
		}},
		{"task create, acquire, fulfil", func() []step {
			return newScript(1000).
				op(pcreate(x, 9000, tagsTargeted())).
				tick(10).op(tget(x)).
				tick(10).op(tacquire(x, 1, "p0", 800)).
				tick(10).op(tacquire(x, 0, "p0", 800)).
				tick(10).op(tacquire(x, 0, "p1", 800)).
				tick(10).op(tget(x)).
				tick(10).op(tfulfill(x, 1, Resolved)).
				tick(10).op(tget(x)).
				tick(10).op(pget(x)).steps
		}},
		{"task.create births and re-acquires", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 500, 9000, tagsTargeted())).
				tick(10).op(tcreate(x, "p0", 500, 9000, tagsTargeted())).
				tick(10).op(tcreate(y, "p0", 500, 9000, tagsInternal())).
				tick(10).op(tcreate(oid("z"), "p0", 500, 500, tagsTargeted())).steps
		}},
		{"task.create re-acquires a released task", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 500, 9000, tagsTargeted())).
				tick(10).op(trelease(x, 1)).
				tick(10).op(tcreate(x, "p1", 500, 9000, tagsTargeted())).steps
		}},
		{"fencing", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tfenceCreate(x, 1, a, 9000, tagsExternal())).
				tick(10).op(tfenceSettle(x, 1, a, Resolved)).
				tick(10).op(tfenceSettle(x, 9, a, Resolved)).
				tick(10).op(tfenceCreate(x, 1, x, 9000, tagsExternal())).
				tick(10).op(trelease(x, 1)).
				tick(10).op(tfenceSettle(x, 1, a, Resolved)).steps
		}},
		{"heartbeat holds the lease", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 400, 9000, tagsTargeted())).
				tick(100).op(theartbeat("p0", TaskRef{ID: x, Version: 1})).
				tick(100).op(theartbeat("p1", TaskRef{ID: x, Version: 1})).
				tick(100).op(theartbeat("p0", TaskRef{ID: x, Version: 7})).
				tick(100).op(theartbeat("p0", TaskRef{ID: g, Version: 1})).
				tick(100).op(theartbeat("p0", TaskRef{ID: x, Version: 1})).
				tick(10).op(tget(x)).steps
		}},
		{"heartbeat on a dead promise", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 400, 1500, tagsTargeted())).
				at(2000).op(theartbeat("p0", TaskRef{ID: x, Version: 1})).
				tick(10).op(tget(x)).steps
		}},
		{"suspend refusals", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tsuspend(x, 1)).
				tick(10).op(tsuspend(x, 1, x)).
				tick(10).op(tsuspend(x, 1, a, a)).
				tick(10).op(tsuspend(x, 9, a)).
				tick(10).op(tsuspend(g, 1, a)).
				tick(10).op(tsuspend(x, 1, oid("i"))).steps
		}},
		{"suspend on a settled awaited is 300", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(psettle(a, Resolved)).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tsuspend(x, 1, a)).
				tick(10).op(tget(x)).steps
		}},
		{"the wake pipeline, driven stage by stage", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tsuspend(x, 1, a)).
				tick(10).op(tget(x)).                // stage 0: suspended
				tick(10).op(psettle(a, Resolved)).   // -> stage 1
				tick(10).op(tget(x)).                // still suspended: the drain has not run
				tick(10).tau("R4", a, x).            // -> stage 2
				tick(10).op(tget(x)).                // pending, resumes recorded
				tick(10).op(tacquire(x, 1, "p1", 800)).steps
		}},
		{"a callback registered by promise.register_callback, drained", func() []step {
			// The other door to the drain. `task.suspend` parks the task, so
			// the drain finds it `.suspended` and wakes it; P-04 leaves the
			// awaiter running, so the drain finds it live and merely records
			// the trigger. Same τ, different outcome — and nothing in the
			// state at drain time says which door was used, which is why the
			// corpus reached the drain 4 ways and all 4 through suspend.
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(pcallback(a, x)).
				tick(10).op(psettle(a, Resolved)).
				tick(10).tau("R4", a, x). // buffered: the awaiter is live, not suspended
				tick(10).op(tget(x)).
				tick(10).tau("R4", a, x). // duplicate: the trigger is already recorded
				tick(10).op(tget(x)).steps
		}},
		{"a woken task buffers its second awaited", func() []step {
			// Both edges registered by suspend, but the second drains onto a
			// task that the FIRST drain already woke — so it buffers rather
			// than resumes. The route is the same; the awaiter's state is
			// not.
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(pcreate(oid("b"), 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tsuspend(x, 1, a, oid("b"))).
				tick(10).op(psettle(a, Resolved)).
				tick(10).op(psettle(oid("b"), Resolved)).
				tick(10).tau("R4", a, x).        // resumed
				tick(10).tau("R4", oid("b"), x). // buffered: no longer suspended
				tick(10).op(tget(x)).steps
		}},
		{"a suspended task whose own promise is settled under it", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tsuspend(x, 1, a)).
				tick(10).op(psettle(x, Resolved)).
				tick(10).op(psettle(a, Resolved)).
				tick(10).tau("R4", a, x). // fulfilled, not expired: no deadline passed
				tick(10).op(tget(x)).steps
		}},
		{"a callback drained onto an already-settled awaiter", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(pcallback(a, x)).
				tick(10).op(psettle(a, Resolved)).
				tick(10).op(tfulfill(x, 1, Resolved)).
				tick(10).tau("R4", a, x). // fulfilled: the awaiter is done
				tick(10).op(tget(x)).steps
		}},
		{"a suspended task whose awaited was registered by P-04", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(pcreate(oid("b"), 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(pcallback(a, x)).
				tick(10).op(tsuspend(x, 1, oid("b"))).
				tick(10).op(psettle(a, Resolved)).
				tick(10).tau("R4", a, x). // resumed, but registered via P-04
				tick(10).op(tget(x)).steps
		}},
		{"a P-04 callback drained onto an awaiter past its own deadline", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 1500, tagsTargeted())).
				tick(10).op(pcallback(a, x)).
				tick(10).op(psettle(a, Resolved)).
				at(2000).tau("R4", a, x). // expired, registered via P-04
				tick(10).op(tget(x)).steps
		}},
		{"timeout always wins: the awaiter is dead at drain time", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 1500, tagsTargeted())).
				tick(10).op(tsuspend(x, 1, a)).
				tick(10).op(psettle(a, Resolved)).
				at(2000).op(tget(x)).
				tick(10).tau("R4", a, x).
				tick(10).op(tget(x)).steps
		}},
		{"timeout always wins: the awaited dies by deadline", func() []step {
			return newScript(1000).
				op(pcreate(a, 1500, tagsExternal())).
				tick(10).op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tsuspend(x, 1, a)).
				at(2000).op(pget(a)).  // projected: rejected_timedout, nothing materialised
				tick(10).op(tget(x)).  // still suspended: the task interface is material
				tick(10).tau("R1", a, "").
				tick(10).tau("R4", a, x).
				tick(10).op(tget(x)).steps
		}},
		{"lease expiry returns the task", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 300, 9000, tagsTargeted())).
				tick(100).op(tget(x)).
				at(1400).tau("R5", x, "").
				tick(10).op(tget(x)).
				tick(10).op(tacquire(x, 1, "p1", 800)).steps
		}},
		{"lease expiry is a no-op while the lease holds", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 3000, 9000, tagsTargeted())).
				tick(100).tau("R5", x, "").
				tick(10).op(tget(x)).steps
		}},
		{"retry re-dispatches a pending task", func() []step {
			return newScript(1000).
				op(pcreate(x, 9000, tagsTargeted())).
				tick(10).tau("R6", x, "").
				tick(10).op(tget(x)).
				tick(10).op(tacquire(x, 0, "p0", 800)).steps
		}},
		{"a delayed first dispatch", func() []step {
			return newScript(1000).
				op(pcreate(x, 9000, tagsTargetedDelay(3000))).
				tick(10).op(tget(x)).
				tick(10).tau("R6", x, "").
				at(3100).tau("R6", x, "").
				tick(10).op(tget(x)).steps
		}},
		{"release and halt and continue", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(trelease(x, 9)).
				tick(10).op(trelease(x, 1)).
				tick(10).op(trelease(x, 1)).
				tick(10).op(thalt(x)).
				tick(10).op(thalt(x)).
				tick(10).op(tcontinue(x)).
				tick(10).op(tcontinue(x)).
				tick(10).op(thalt(g)).steps
		}},
		{"halt and continue on a dead promise", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 800, 1500, tagsTargeted())).
				at(2000).op(thalt(x)).
				tick(10).op(tcontinue(x)).
				tick(10).op(tget(x)).steps
		}},
		{"halt a fulfilled task", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tfulfill(x, 1, Resolved)).
				tick(10).op(thalt(x)).
				tick(10).op(tcontinue(x)).steps
		}},
		{"the promise timeout τ, and firing it twice", func() []step {
			return newScript(1000).
				op(pcreate(a, 1500, tagsExternal())).
				at(2000).tau("R1", a, "").
				tick(10).tau("R1", a, "").
				tick(10).op(pget(a)).steps
		}},
		{"τ no-ops: nothing is armed", func() []step {
			return newScript(1000).
				op(pcreate(a, 9000, tagsExternal())).
				tick(10).tau("R1", a, "").
				tick(10).tau("R4", a, oid("nobody")).
				tick(10).tau("R5", oid("nobody"), "").
				tick(10).tau("R6", oid("nobody"), "").
				tick(10).tau("R3", a, "https://nobody").
				tick(10).op(pget(a)).steps
		}},
		{"two workers race for one task", func() []step {
			return newScript(1000).
				op(pcreate(x, 9000, tagsTargeted())).
				tick(10).op(tacquire(x, 0, "p0", 800)).
				tick(10).op(tacquire(x, 0, "p1", 800)).
				tick(10).op(tacquire(x, 1, "p1", 800)).
				tick(10).op(tfulfill(x, 1, Resolved)).
				tick(10).op(tfulfill(x, 1, Rejected)).steps
		}},
		{"fulfil refusals", func() []step {
			return newScript(1000).
				op(tcreate(x, "p0", 800, 9000, tagsTargeted())).
				tick(10).op(tfulfill(x, 1, Pending)).
				tick(10).op(tfulfill(x, 9, Resolved)).
				tick(10).op(tfulfill(g, 1, Resolved)).
				tick(10).op(tfulfill(x, 1, RejectedCanceled)).steps
		}},
		{"reads of what does not exist", func() []step {
			return newScript(1000).
				op(pget(g)).
				tick(10).op(tget(g)).
				tick(10).op(tacquire(g, 0, "p0", 800)).
				tick(10).op(tcontinue(g)).steps
		}},
	}
}

// -------------------------------------------------------------- the corpus

// Case is one emitted test case: a script, the bucket it was selected to
// witness, and everything a harness needs to replay it.
type Case struct {
	Name    string   `json:"name"`
	Witness string   `json:"witness"`
	Covers  []string `json:"covers"`
	From    string   `json:"from"`
	Steps   int      `json:"steps"`
	Taus    int      `json:"taus"`
	Outbox  []string `json:"expectedOutbox"`
	// Tier is "both" when the case survives τ-erasure, "driven" when it does
	// not. A case whose observational projection is EMPTY is not a defect:
	// an internal step that fires with its obligation already discharged is
	// a silent no-op, so no request/response capture can witness it. Those
	// behaviours are reachable only by a harness that can drive the loop,
	// and the size of this set is the price of not having one.
	Tier string `json:"tier"`

	script []step
}

// Declared is a coverage domain stated up front rather than discovered.
//
// Everything else in this file measures what a search REACHED, which can
// only ever report what it found. A behaviour the search never reaches is
// invisible to it — indistinguishable from one that does not exist. So the
// places where the specification names its own cases are transcribed here,
// and anything absent from the corpus is reported as residue by name.
//
// `ResumeOutcome` is the clearest such place: `01-protocol/types.lean`
// enumerates six, and says why the enum exists rather than a unit return —
// "`expired` vs `fulfilled` is the distinction TIMEOUT ALWAYS WINS
// legislates". A corpus reaching four of six has a gap worth printing.
var _unusedDeclared = []string{
	"tau.resume/resumed/via:suspend",
	"tau.resume/resumed/via:register_callback",
	"tau.resume/buffered/via:suspend",
	"tau.resume/buffered/via:register_callback",
	// `duplicate` is declared here and is BELIEVED UNREACHABLE in this
	// machine, deliberately left in the list so the report keeps saying so.
	// `ProcessCallback` removes the callback from the awaited before calling
	// `resumeOne`, so a pair cannot drain twice: the second firing returns
	// at the `contains(p.Callbacks, awaiter)` guard and is a silent no-op,
	// never reaching the `contains(t.Resumes, awaited)` branch that would
	// report `duplicate`. Two different awaited promises append two
	// different entries, so they do not reach it either.
	//
	// Either that branch is defensive-only, or it is reachable in the
	// CONCRETE machine — whose `deferred` queue is a separate component
	// rather than a projection of the callback list — and this abstract port
	// cannot witness it. Worth settling against `internal-steps-p.lean`
	// before anyone writes a test for it.
	"tau.resume/duplicate/via:register_callback",
	"tau.resume/expired/via:suspend",
	"tau.resume/expired/via:register_callback",
	"tau.resume/fulfilled/via:suspend",
	"tau.resume/fulfilled/via:register_callback",
	"tau.resume/absent/via:none",
}

// Corpus is the generated suite plus its coverage accounting.
type Corpus struct {
	Cases      []*Case
	Buckets    []string
	FromTmpl   int
	FromRand   int
	DrivenOnly int
}

// bucketsOf replays a script and returns every bucket it touches, external
// and internal. The pre-state for each step comes from `States`, so the
// classification sees exactly what the handler saw.
func bucketsOf(d Discipline, script []step) []string {
	var out []string
	s := &ServerState{}
	for _, st := range script {
		before := len(s.Branches)
		if st.op != nil {
			st.op.apply(s, d)
		} else {
			switch st.internal {
			case "R1":
				s.ProcessPromiseTimeout(st.arg, st.now)
			case "R3":
				s.ProcessListener(st.arg, st.arg2, st.now)
			case "R4":
				s.ProcessCallback(st.arg, st.arg2, st.now)
			case "R5":
				s.ProcessLeaseTimeout(st.arg, st.now)
			case "R6":
				s.ProcessRetryTimeout(st.arg, st.now, st.now)
			}
		}
		for _, b := range s.Branches[before:] {
			out = append(out, b.Handler+"/"+b.Point+"/"+b.Taken)
		}
	}
	return out
}

// minimize drops every step the witness does not need. A test case a human
// has to read is worth more than one a search happened to find, and the
// difference is usually a factor of five.
func minimize(d Discipline, script []step, want string) []step {
	changed := true
	for changed {
		changed = false
		for i := 0; i < len(script); i++ {
			trial := make([]step, 0, len(script)-1)
			trial = append(trial, script[:i]...)
			trial = append(trial, script[i+1:]...)
			if containsStr(bucketsOf(d, trial), want) {
				script = trial
				changed = true
				break
			}
		}
	}
	return script
}

// BuildCorpus runs the templates, then a random search for whatever they
// miss, then greedily selects a minimal covering subset.
//
// Greedy set cover is within a log factor of optimal and is the right
// trade here: the alternative is an exact cover nobody can read.
func BuildCorpus(d Discipline, seeds int) *Corpus {
	type cand struct {
		from    string
		script  []step
		buckets []string
	}
	var cands []cand
	seen := map[string]bool{}

	for _, sc := range scenarios() {
		s := sc.build()
		bs := bucketsOf(d, s)
		cands = append(cands, cand{"template: " + sc.name, s, bs})
		for _, b := range bs {
			seen[b] = true
		}
	}
	tmplBuckets := len(seen)

	// The random half exists to falsify the templates: anything it reaches
	// that they do not is a region the hand-written skeletons forgot.
	for i := 0; i < seeds; i++ {
		g := NewGen(int64(i), origin)
		g.Jumpy = i%2 == 0
		s := g.Script(28)
		bs := bucketsOf(d, s)
		fresh := false
		for _, b := range bs {
			if !seen[b] {
				fresh, seen[b] = true, true
			}
		}
		if fresh {
			cands = append(cands, cand{fmt.Sprintf("search: seed %d", i), s, bs})
		}
	}

	all := make([]string, 0, len(seen))
	for b := range seen {
		all = append(all, b)
	}
	sort.Strings(all)

	uncovered := map[string]bool{}
	for _, b := range all {
		uncovered[b] = true
	}
	c := &Corpus{Buckets: all}

	// One case per behaviour still uncovered, anchored on that behaviour.
	//
	// A candidate is NOT retired after it is used: minimizing against one
	// witness throws away the rest of what a long script reached, and the
	// same script minimized against a different witness is a different —
	// and equally small — case. Retiring it was the bug that lost 120 of
	// 205 behaviours: the cover ran out of candidates while the behaviours
	// it needed were sitting inside scripts already spent.
	for _, target := range all {
		if !uncovered[target] {
			continue
		}
		best := -1
		for i, cd := range cands {
			if !containsStr(cd.buckets, target) {
				continue
			}
			// Prefer a template over a random find — same coverage, better
			// provenance — and a shorter script over a longer one.
			if best < 0 {
				best = i
				continue
			}
			bt := strings.HasPrefix(cands[best].from, "template")
			ct := strings.HasPrefix(cd.from, "template")
			if ct && !bt {
				best = i
			} else if ct == bt && len(cd.script) < len(cands[best].script) {
				best = i
			}
		}
		if best < 0 {
			continue
		}
		cd := cands[best]
		script := minimize(d, cd.script, target)
		got := bucketsOf(d, script)
		for _, b := range got {
			delete(uncovered, b)
		}
		ops, _, _ := Run(d, script)
		if strings.HasPrefix(cd.from, "template") {
			c.FromTmpl++
		} else {
			c.FromRand++
		}
		tier := "both"
		if len(ops) == 0 {
			tier = "driven"
			c.DrivenOnly++
		}
		c.Cases = append(c.Cases, &Case{
			Name:    caseName(target),
			Witness: target,
			Covers:  dedupStrings(got),
			From:    cd.from,
			Steps:   len(ops),
			Taus:    len(script) - len(ops),
			Outbox:  outboxOf(d, script),
			Tier:    tier,
			script:  script,
		})
	}
	_ = tmplBuckets
	return c
}

func dedupStrings(xs []string) []string {
	seen := map[string]bool{}
	var out []string
	for _, x := range xs {
		if !seen[x] {
			seen[x] = true
			out = append(out, x)
		}
	}
	sort.Strings(out)
	return out
}

var nameSanitizer = strings.NewReplacer("/", "--", ":", "-", " ", "_", ".", "_")

func caseName(bucket string) string { return nameSanitizer.Replace(bucket) }

// outboxOf reports the outbox as a KEYED set, because that is what it is:
// `setMessage` collapses on the entry key, so multiplicity is not
// observable and a harness must never assert a count.
func outboxOf(d Discipline, script []step) []string {
	out := []string{}
	s := &ServerState{}
	for _, st := range script {
		if st.op != nil {
			st.op.apply(s, d)
			continue
		}
		switch st.internal {
		case "R1":
			s.ProcessPromiseTimeout(st.arg, st.now)
		case "R3":
			s.ProcessListener(st.arg, st.arg2, st.now)
		case "R4":
			s.ProcessCallback(st.arg, st.arg2, st.now)
		case "R5":
			s.ProcessLeaseTimeout(st.arg, st.now)
		case "R6":
			s.ProcessRetryTimeout(st.arg, st.now, st.now)
		}
	}
	for _, m := range s.Outbox {
		if m.Kind == "execute" {
			out = append(out, fmt.Sprintf("execute %s v%d -> %s", m.TaskID, m.Version, m.Address))
		} else {
			out = append(out, fmt.Sprintf("unblock %s -> %s", m.Promise, m.Address))
		}
	}
	sort.Strings(out)
	return out
}

// ------------------------------------------------------------- emission

// Observational renders the case in the recorded-trace wire format: external
// events only, exactly what `lincheck` and `lake exe checktrace` consume.
func (c *Case) Observational(d Discipline) string {
	ops, resps, _ := Run(d, c.script)
	return Emit(ops, resps)
}

// Driven renders the case with its internal steps in place. A harness that
// can fire the server's τs replays this literally, and every response is
// then forced rather than schedule-dependent.
//
// A separate file rather than extra rows in the observational one: the
// checkers consume that format unchanged, and teaching them a new row kind
// to ignore would be a change to the thing being relied upon.
func (c *Case) Driven(d Discipline) string {
	var b strings.Builder
	s := &ServerState{}
	for _, st := range c.script {
		if st.op != nil {
			res := st.op.apply(s, d)
			fmt.Fprintf(&b, `{"kind":%q,"now":%d,"req":%s,"res":{"kind":%q,"head":{"status":%d},"data":%s}}`+"\n",
				st.op.Kind, st.op.Now, emitReq(*st.op), st.op.Kind, res.Status, emitData(res))
			continue
		}
		name := map[string]string{
			"R1": "tau.promise_timeout", "R3": "tau.listener", "R4": "tau.resume",
			"R5": "tau.task_lease", "R6": "tau.task_retry",
		}[st.internal]
		before := s.Key()
		switch st.internal {
		case "R1":
			s.ProcessPromiseTimeout(st.arg, st.now)
		case "R3":
			s.ProcessListener(st.arg, st.arg2, st.now)
		case "R4":
			s.ProcessCallback(st.arg, st.arg2, st.now)
		case "R5":
			s.ProcessLeaseTimeout(st.arg, st.now)
		case "R6":
			s.ProcessRetryTimeout(st.arg, st.now, st.now)
		}
		effect := "fired"
		if before == s.Key() {
			effect = "no-op"
		}
		arg2 := ""
		if st.arg2 != "" {
			arg2 = fmt.Sprintf(`,"awaiter":%q`, st.arg2)
		}
		fmt.Fprintf(&b, `{"kind":%q,"now":%d,"target":%q%s,"effect":%q}`+"\n",
			name, st.now, st.arg, arg2, effect)
	}
	return b.String()
}

// Sidecar carries what the wire format has no room for: which behaviour the
// case witnesses, and the outbox — half of the observation function, and
// absent from a request/response capture.
func (c *Case) Sidecar() string {
	b, _ := json.MarshalIndent(c, "", "  ")
	return string(b)
}


// Catalogue mirrors `branchCatalogue` in
// `spec/02-abstract/effects.lean` — every branch the machine can note.
//
// Two copies of one list is a smell, and it is the same smell the port
// itself is: this package exists because the Lean cannot be run inside a
// search loop. `TestCatalogueMatchesLean` keeps them honest by counting;
// the real fix is generating one from the other.
var Catalogue = []Branch{
	{"P-01", "branch", "absent"},
	{"P-01", "branch", "found"},
	{"P-02", "birth", "born-dead-rejected-timedout"},
	{"P-02", "birth", "born-dead-targeted-task-fulfilled"},
	{"P-02", "birth", "born-dead-timer-resolved"},
	{"P-02", "birth", "born-live-targeted"},
	{"P-02", "birth", "born-live-targeted-delayed"},
	{"P-02", "birth", "born-live-untargeted"},
	{"P-02", "branch", "created"},
	{"P-02", "branch", "idempotent-echo"},
	{"P-02", "branch", "timer-targeted"},
	{"P-03", "branch", "absent"},
	{"P-03", "branch", "already-settled"},
	{"P-03", "branch", "settled"},
	{"P-03", "branch", "unsettable"},
	{"P-04", "branch", "awaited-absent"},
	{"P-04", "branch", "awaited-internal"},
	{"P-04", "branch", "awaiter-absent"},
	{"P-04", "branch", "awaiter-untargeted"},
	{"P-04", "branch", "self"},
	{"P-04", "callback", "awaited-settled"},
	{"P-04", "callback", "awaiter-not-live"},
	{"P-04", "callback", "registered"},
	{"P-05", "branch", "awaited-absent"},
	{"P-05", "branch", "awaited-internal"},
	{"P-05", "branch", "awaited-settled"},
	{"P-05", "branch", "bad-address"},
	{"P-05", "branch", "registered"},
	{"T-01", "branch", "found"},
	{"T-01", "branch", "promise-absent"},
	{"T-01", "branch", "task-absent"},
	{"T-02", "branch", "already-fulfilled"},
	{"T-02", "branch", "born-dead-fulfilled"},
	{"T-02", "branch", "born-live-acquired"},
	{"T-02", "branch", "malformed-action"},
	{"T-02", "branch", "promise-untargeted"},
	{"T-02", "branch", "reacquired"},
	{"T-02", "branch", "task-absent"},
	{"T-02", "branch", "task-not-pending"},
	{"T-03", "branch", "acquired"},
	{"T-03", "branch", "promise-absent"},
	{"T-03", "branch", "promise-not-live"},
	{"T-03", "branch", "task-absent"},
	{"T-03", "branch", "task-wrong-state"},
	{"T-03", "branch", "version-mismatch"},
	{"T-04", "branch", "fenced-create"},
	{"T-04", "branch", "fenced-settle"},
	{"T-04", "branch", "promise-absent"},
	{"T-04", "branch", "promise-not-live"},
	{"T-04", "branch", "self-target"},
	{"T-04", "branch", "task-absent"},
	{"T-04", "branch", "task-wrong-state"},
	{"T-04", "branch", "version-mismatch"},
	{"T-05", "branch", "lease-extended"},
	{"T-05", "branch", "refused"},
	{"T-05", "branch", "task-absent"},
	{"T-06", "branch", "awaited-already-settled"},
	{"T-06", "branch", "awaited-unusable"},
	{"T-06", "branch", "duplicate-awaited"},
	{"T-06", "branch", "empty-actions"},
	{"T-06", "branch", "promise-absent"},
	{"T-06", "branch", "promise-not-live"},
	{"T-06", "branch", "self-awaited"},
	{"T-06", "branch", "suspended"},
	{"T-06", "branch", "task-absent"},
	{"T-06", "branch", "task-wrong-state"},
	{"T-06", "branch", "version-mismatch"},
	{"T-06", "callback", "awaited-absent"},
	{"T-06", "callback", "registered"},
	{"T-07", "branch", "fulfilled"},
	{"T-07", "branch", "promise-absent"},
	{"T-07", "branch", "promise-not-live"},
	{"T-07", "branch", "task-absent"},
	{"T-07", "branch", "task-wrong-state"},
	{"T-07", "branch", "unsettable"},
	{"T-07", "branch", "version-mismatch"},
	{"T-08", "branch", "promise-absent"},
	{"T-08", "branch", "promise-not-live"},
	{"T-08", "branch", "released"},
	{"T-08", "branch", "task-absent"},
	{"T-08", "branch", "task-wrong-state"},
	{"T-08", "branch", "version-mismatch"},
	{"T-09", "branch", "already-fulfilled"},
	{"T-09", "branch", "already-halted"},
	{"T-09", "branch", "halted"},
	{"T-09", "branch", "promise-absent"},
	{"T-09", "branch", "task-absent"},
	{"T-10", "branch", "continued"},
	{"T-10", "branch", "not-halted"},
	{"T-10", "branch", "promise-not-live"},
	{"T-10", "branch", "task-absent"},
	{"\u03c4-lease", "branch", "expired"},
	{"\u03c4-lease", "branch", "not-due"},
	{"\u03c4-lease", "branch", "promise-absent"},
	{"\u03c4-lease", "branch", "promise-not-live"},
	{"\u03c4-lease", "branch", "task-absent"},
	{"\u03c4-lease", "branch", "unarmed"},
	{"\u03c4-listener", "branch", "absent"},
	{"\u03c4-listener", "branch", "awaited-pending"},
	{"\u03c4-listener", "branch", "delivered"},
	{"\u03c4-listener", "branch", "no-such-listener"},
	{"\u03c4-promise-timeout", "branch", "absent"},
	{"\u03c4-promise-timeout", "branch", "materialized"},
	{"\u03c4-promise-timeout", "branch", "not-due"},
	{"\u03c4-resume", "outcome", "absent"},
	{"\u03c4-resume", "outcome", "buffered"},
	{"\u03c4-resume", "outcome", "duplicate"},
	{"\u03c4-resume", "outcome", "expired"},
	{"\u03c4-resume", "outcome", "fulfilled"},
	{"\u03c4-resume", "outcome", "resumed"},
	{"\u03c4-retry", "branch", "dispatched"},
	{"\u03c4-retry", "branch", "not-due"},
	{"\u03c4-retry", "branch", "promise-absent"},
	{"\u03c4-retry", "branch", "promise-not-live"},
	{"\u03c4-retry", "branch", "task-absent"},
	{"\u03c4-retry", "branch", "unarmed"},
}

// Unreached names the catalogued branches no case in the corpus covers.
// The half a search cannot supply: a behaviour never reached looks exactly
// like one that does not exist.
func Unreached(covered map[string]bool) []string {
	var out []string
	for _, b := range Catalogue {
		k := b.Handler + "/" + b.Point + "/" + b.Taken
		if !covered[k] {
			out = append(out, k)
		}
	}
	sort.Strings(out)
	return out
}

// Uncatalogued names branches a run noted that the catalogue does not list
// — an instrumented handler whose branch nobody declared, and therefore one
// the coverage report would silently ignore.
func Uncatalogued(covered map[string]bool) []string {
	in := map[string]bool{}
	for _, b := range Catalogue {
		in[b.Handler+"/"+b.Point+"/"+b.Taken] = true
	}
	var out []string
	for k := range covered {
		if !in[k] {
			out = append(out, k)
		}
	}
	sort.Strings(out)
	return out
}
