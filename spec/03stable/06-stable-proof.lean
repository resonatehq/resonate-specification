import «03stable».«05-stable»
open ServerModel

def logical (s : ServerState) (id : String) (now : Nat) : Option PromiseState :=
  (s.promises.find? (·.id == id)).map (fun p => (p.project now).state)

theorem project_mono (p : PromiseObject) {now now' : Nat} (h : now ≤ now')
    (hs : (p.project now).state ≠ .pending) :
    (p.project now').state = (p.project now).state := by
  unfold PromiseObject.project at hs ⊢
  by_cases h1 : p.state == .pending ∧ p.timeoutAt ≤ now
  · have h2 : p.state == .pending ∧ p.timeoutAt ≤ now' := ⟨h1.1, Nat.le_trans h1.2 h⟩
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1] at hs
    have h2 : ¬(p.state == .pending ∧ p.timeoutAt ≤ now') := by
      intro ⟨hpend, _⟩; exact hs (by simpa using hpend)
    rw [if_neg h1, if_neg h2]

theorem logical_mono {s : ServerState} {id : String} {st : PromiseState}
    {now now' : Nat} (h : now ≤ now') (hset : Settled st)
    (hl : logical s id now = some st) :
    logical s id now' = some st := by
  unfold logical at hl ⊢
  cases hfind : s.promises.find? (·.id == id) with
  | none => rw [hfind] at hl; exact absurd hl (by simp)
  | some p =>
      rw [hfind] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      have hns : (p.project now).state ≠ .pending := by rw [hl]; exact hset
      simp only [Option.map_some, Option.some.injEq]
      rw [project_mono p h hns]
      exact hl

def StepSound : Prop :=
  ∀ (rq : Request) (now : Nat) (s : ServerState) (id : String) (st : PromiseState),
    Externalized (stepOf rq now s).1 id st →
      logical (stepOf rq now s).2 id now = some st

def StepFrozen : Prop :=
  ∀ (rq : Request) (now : Nat) (s : ServerState) (id : String) (st : PromiseState),
    Settled st →
      logical s id now = some st →
        logical (stepOf rq now s).2 id now = some st

section RunKit
variable {α β : Type}
@[simp] theorem run_bind (x : M α) (f : α → M β) (s : ServerState) :
    (x >>= f) s = (f (x s).1) (x s).2 := rfl
@[simp] theorem run_get (s : ServerState) :
    (get : M ServerState) s = (s, s) := rfl
@[simp] theorem run_pure (a : α) (s : ServerState) :
    (pure a : M α) s = (a, s) := rfl
@[simp] theorem run_map (f : α → β) (x : M α) (s : ServerState) :
    (f <$> x) s = ((f (x s).1), (x s).2) := rfl
@[simp] theorem run_stepOf (rq : Request) (now : Nat) (s : ServerState) :
    stepOf rq now s = handle rq now s := rfl
@[simp] theorem run_modify (f : ServerState → ServerState) (s : ServerState) :
    (modify f : M Unit) s = ((), f s) := rfl
@[simp] theorem run_setTask (t : TaskObject) (s : ServerState) :
    (setTask t : M Unit) s = ((), { s with tasks := t :: s.tasks.filter (·.id != t.id) }) := rfl
@[simp] theorem run_setPromise (p : PromiseObject) (s : ServerState) :
    (setPromise p : M Unit) s = ((), { s with promises := p :: s.promises.filter (·.id != p.id) }) := rfl
@[simp] theorem run_delTaskTimeout (id : String) (s : ServerState) :
    (delTaskTimeout id : M Unit) s = ((), { s with taskTimeouts := s.taskTimeouts.filter (·.id != id) }) := rfl
@[simp] theorem run_setTaskTimeout (id : String) (kind timeout : Nat) (s : ServerState) :
    (setTaskTimeout id kind timeout : M Unit) s = ((), { s with taskTimeouts := { id, kind, timeout } :: s.taskTimeouts.filter (fun t => !(t.id == id && t.kind == kind)) }) := rfl
@[simp] theorem run_delPromiseTimeout (id : String) (s : ServerState) :
    (delPromiseTimeout id : M Unit) s = ((), { s with promiseTimeouts := s.promiseTimeouts.filter (·.id != id) }) := rfl
@[simp] theorem run_setPromiseTimeout (id : String) (timeout : Nat) (s : ServerState) :
    (setPromiseTimeout id timeout : M Unit) s = ((), { s with promiseTimeouts := { id, timeout } :: s.promiseTimeouts.filter (·.id != id) }) := rfl
@[simp] theorem run_delScheduleTimeout (id : String) (s : ServerState) :
    (delScheduleTimeout id : M Unit) s = ((), { s with scheduleTimeouts := s.scheduleTimeouts.filter (·.id != id) }) := rfl
@[simp] theorem run_setScheduleTimeout (id : String) (timeout : Nat) (s : ServerState) :
    (setScheduleTimeout id timeout : M Unit) s = ((), { s with scheduleTimeouts := { id, timeout } :: s.scheduleTimeouts.filter (·.id != id) }) := rfl
@[simp] theorem run_setMessage (address : String) (msg : Message) (s : ServerState) :
    (setMessage address msg : M Unit) s = ((), { s with outbox := OutboxEntry.mk address msg :: s.outbox.filter (fun e => e.key != (OutboxEntry.mk address msg).key) }) := rfl
@[simp] theorem run_defer (d : ResumeReq) (s : ServerState) :
    (defer d : M Unit) s = ((), { s with deferred := d :: s.deferred.filter (fun e => !(e.awaited == d.awaited && e.awaiter == d.awaiter)) }) := rfl
@[simp] theorem run_undefer (d : ResumeReq) (s : ServerState) :
    (undefer d : M Unit) s = ((), { s with deferred := s.deferred.filter (fun e => !(e.awaited == d.awaited && e.awaiter == d.awaiter)) }) := rfl

@[simp] theorem run_delTaskTimeout_2 (id : String) (s : ServerState) :
    ((delTaskTimeout id : M Unit) s).2 = { s with taskTimeouts := s.taskTimeouts.filter (·.id != id) } := by
  simp [run_delTaskTimeout]
@[simp] theorem run_setTaskTimeout_2 (id : String) (kind timeout : Nat) (s : ServerState) :
    ((setTaskTimeout id kind timeout : M Unit) s).2 = { s with taskTimeouts := { id, kind, timeout } :: s.taskTimeouts.filter (fun t => !(t.id == id && t.kind == kind)) } := by
  simp [run_setTaskTimeout]
@[simp] theorem run_delPromiseTimeout_2 (id : String) (s : ServerState) :
    ((delPromiseTimeout id : M Unit) s).2 = { s with promiseTimeouts := s.promiseTimeouts.filter (·.id != id) } := by
  simp [run_delPromiseTimeout]
@[simp] theorem run_setPromiseTimeout_2 (id : String) (timeout : Nat) (s : ServerState) :
    ((setPromiseTimeout id timeout : M Unit) s).2 = { s with promiseTimeouts := { id, timeout } :: s.promiseTimeouts.filter (·.id != id) } := by
  simp [run_setPromiseTimeout]
@[simp] theorem run_delScheduleTimeout_2 (id : String) (s : ServerState) :
    ((delScheduleTimeout id : M Unit) s).2 = { s with scheduleTimeouts := s.scheduleTimeouts.filter (·.id != id) } := by
  simp [run_delScheduleTimeout]
@[simp] theorem run_setScheduleTimeout_2 (id : String) (timeout : Nat) (s : ServerState) :
    ((setScheduleTimeout id timeout : M Unit) s).2 = { s with scheduleTimeouts := { id, timeout } :: s.scheduleTimeouts.filter (·.id != id) } := by
  simp [run_setScheduleTimeout]
@[simp] theorem run_setMessage_2 (address : String) (msg : Message) (s : ServerState) :
    ((setMessage address msg : M Unit) s).2 = { s with outbox := OutboxEntry.mk address msg :: s.outbox.filter (fun e => e.key != (OutboxEntry.mk address msg).key) } := by
  simp [run_setMessage]
@[simp] theorem run_defer_2 (d : ResumeReq) (s : ServerState) :
    ((defer d : M Unit) s).2 = { s with deferred := d :: s.deferred.filter (fun e => !(e.awaited == d.awaited && e.awaiter == d.awaiter)) } := by
  simp [run_defer]
@[simp] theorem run_undefer_2 (d : ResumeReq) (s : ServerState) :
    ((undefer d : M Unit) s).2 = { s with deferred := s.deferred.filter (fun e => !(e.awaited == d.awaited && e.awaiter == d.awaiter)) } := by
  simp [run_undefer]
end RunKit

theorem project_id (p : PromiseObject) (now : Nat) : (p.project now).id = p.id := by
  unfold PromiseObject.project
  split
  · rename_i h; split <;> rfl
  · rfl

theorem find?_filter_ne {l : List PromiseObject} {id p_id : String} (h : id ≠ p_id) :
    (l.filter (·.id != p_id)).find? (·.id == id) = l.find? (·.id == id) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x.id = p_id
      · have h2 : (x.id == id) = false := by rw [hx]; exact beq_eq_false_iff_ne.mpr (Ne.symm h)
        have h3 : (p_id == id) = false := by rw [← hx]; exact h2
        simp [List.filter_cons, List.find?_cons, hx, h2, h3, ih]
      · simp [List.filter_cons, List.find?_cons, hx, ih]

theorem promiseCreate_preserves_existing (req : PromiseCreateReq) (now : Nat) (s : ServerState) (id : String)
    (hfind : s.promises.find? (·.id == req.id) ≠ none) (hne : req.id ≠ id) :
    (Id.run ((promiseCreate req now).run s)).2.promises.find? (·.id == id) =
      s.promises.find? (·.id == id) := by
  unfold promiseCreate getPromise
  cases h : s.promises.find? (·.id == req.id)
  · contradiction
  · rename_i p; simp [h]

theorem promiseCreate_find?_mono (req : PromiseCreateReq) (now : Nat) (s : ServerState)
    {id : String} {p : PromiseObject}
    (hid : s.promises.find? (·.id == id) = some p) :
    ((promiseCreate req now : M PromiseCreateRes) s).2.promises.find? (·.id == id) = some p := by
  cases h : s.promises.find? (·.id == req.id) with
  | some q =>
      simp only [promiseCreate, getPromise, run_bind, run_get, run_pure, run_map, h]; exact hid
  | none =>
      have hne : req.id ≠ id := by intro he; subst he; rw [h] at hid; simp at hid
      have hcons : ∀ (q : PromiseObject), q.id = req.id →
          (q :: s.promises.filter (·.id != req.id)).find? (·.id == id) = some p := by
        intro q hq
        have hqid : (q.id == id) = false := by rw [hq]; exact beq_eq_false_iff_ne.mpr hne
        simp only [List.find?_cons, hqid, cond_false]
        rw [find?_filter_ne (Ne.symm hne)]; exact hid
      simp only [promiseCreate, getPromise, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage, run_bind, run_get, run_pure, run_map, run_modify, h]
      repeat first | (exact hcons _ rfl) | split

theorem catchUp_find?_preserved (fuel : Nat) (now : Nat) :
    ∀ (sch : Schedule) (s : ServerState) {id : String} {p : PromiseObject},
      s.promises.find? (·.id == id) = some p →
      ((Timeouts.catchUp fuel now sch : M Schedule) s).2.promises.find? (·.id == id) = some p := by
  induction fuel with
  | zero => intro sch s id p hid; simp [Timeouts.catchUp, run_pure, hid]
  | succ n ih =>
      intro sch s id p hid
      rw [Timeouts.catchUp]
      simp only [Nat.succ_ne_zero, if_false, run_bind, run_pure, Nat.add_sub_cancel]
      by_cases hrun : sch.nextRunAt ≤ now
      · simp only [if_pos hrun, run_bind, run_pure]; exact ih _ _ (promiseCreate_find?_mono _ _ _ hid)
      · simp only [if_neg hrun, run_pure]; exact hid

theorem stable_of_sound_frozen (stepSound : StepSound) (stepFrozen : StepFrozen) :
    ∀ tr : Trace, Valid tr → Stable tr := by
  intro tr hvalid i j id st₁ st₂ hij hex₁ hset₁ hex₂
  have hvalid_i := hvalid i; rcases hvalid_i with ⟨hres_i, hstate_i, hclock_i⟩
  have hex₁_step : Externalized (stepOf (tr i).req (tr i).now (tr i).state).1 id st₁ := by rw [← hres_i]; exact hex₁
  have hlog₁_step : logical (stepOf (tr i).req (tr i).now (tr i).state).2 id (tr i).now = some st₁ :=
    stepSound (tr i).req (tr i).now (tr i).state id st₁ hex₁_step
  have hlog₁ : logical (tr (i+1)).state id (tr i).now = some st₁ := by simpa [hstate_i] using hlog₁_step
  have hlog_base : logical (tr (i+1)).state id (tr (i+1)).now = some st₁ := logical_mono hclock_i hset₁ hlog₁
  have hvalid_j := hvalid j; rcases hvalid_j with ⟨hres_j, hstate_j, hclock_j⟩
  have hex₂_step : Externalized (stepOf (tr j).req (tr j).now (tr j).state).1 id st₂ := by rw [← hres_j]; exact hex₂
  have hlog₂_step : logical (stepOf (tr j).req (tr j).now (tr j).state).2 id (tr j).now = some st₂ :=
    stepSound (tr j).req (tr j).now (tr j).state id st₂ hex₂_step
  have hlog₂ : logical (tr (j+1)).state id (tr j).now = some st₂ := by simpa [hstate_j] using hlog₂_step
  by_cases heq : i = j
  · subst heq; rw [hlog₁] at hlog₂; simpa using (Option.some.inj hlog₂).symm
  · have h_lt : i < j := Nat.lt_of_le_of_ne hij heq
    have hstep : ∀ k, i+1 ≤ k → k < j →
      logical (tr k).state id (tr k).now = some st₁ →
      logical (tr (k+1)).state id (tr (k+1)).now = some st₁ := by
      intro k hk_low hk_lt hlogk
      have hk_le_j : k ≤ j := Nat.le_of_lt hk_lt
      have hvalid_k := hvalid k; rcases hvalid_k with ⟨hres_k, hstate_k, hclock_k⟩
      have hfrozen := stepFrozen (tr k).req (tr k).now (tr k).state id st₁ hset₁ hlogk
      have hfrozen' : logical (tr (k+1)).state id (tr k).now = some st₁ := by simpa [hstate_k] using hfrozen
      exact logical_mono hclock_k hset₁ hfrozen'
    have hlog_j_at_j : logical (tr j).state id (tr j).now = some st₁ := by
      have h_exists : ∃ d, j = (i+1) + d := Nat.exists_eq_add_of_le (by omega)
      rcases h_exists with ⟨d, hd⟩; subst hd
      refine Nat.rec hlog_base (fun d ih => ?_) d
      have hvalid_k := hvalid (i+1+d); rcases hvalid_k with ⟨hres_k, hstate_k, hclock_k⟩
      have hfrozen := stepFrozen (tr (i+1+d)).req (tr (i+1+d)).now (tr (i+1+d)).state id st₁ hset₁ ih
      have hfrozen' : logical (tr (i+1+d+1)).state id (tr (i+1+d)).now = some st₁ := by simpa [hstate_k] using hfrozen
      exact logical_mono hclock_k hset₁ hfrozen'
    have hfrozen_j := stepFrozen (tr j).req (tr j).now (tr j).state id st₁ hset₁ hlog_j_at_j
    have hlog₂_rev : logical (tr (j+1)).state id (tr j).now = some st₁ := by simpa [hstate_j] using hfrozen_j
    rw [hlog₂] at hlog₂_rev; simpa using (Option.some.inj hlog₂_rev)

/-- Any `for` loop whose body preserves a state invariant preserves it. -/
theorem forIn_inv {α β : Type} (Inv : ServerState → Prop) (f : α → β → M (ForInStep β))
    (hf : ∀ a b s, Inv s → Inv ((f a b) s).2) :
    ∀ (l : List α) (b : β) (s : ServerState), Inv s → Inv ((forIn l b f : M β) s).2 := by
  intro l
  induction l with
  | nil => intro b s h; exact h
  | cons x xs ih =>
      intro b s h
      rw [List.forIn_cons]
      simp only [run_bind]
      cases hstep : ((f x b) s).1 with
      | done b' => exact hf x b s h
      | yield b' => exact ih b' _ (hf x b s h)

/-- Projection is the identity on a live pending promise. -/
theorem project_of_live (p : PromiseObject) (now : Nat) (h : now < p.timeoutAt) :
    p.project now = p := by
  unfold PromiseObject.project
  rw [if_neg]
  intro ⟨_, hle⟩
  omega

theorem onTaskRetryTimeout_promises_eq (id : String) (now : Nat) (s : ServerState) :
    (Timeouts.onTaskRetryTimeout id now s).snd.promises = s.promises := by
  unfold Timeouts.onTaskRetryTimeout getTask getPromise
  by_cases h : s.tasks.find? (·.id == id) = none
  · simp [h]
  · have h' := Option.eq_none_or_eq_some _ |>.resolve_left h
    rcases h' with ⟨t, h⟩
    simp [h]
    by_cases h_state : t.state = TaskState.pending
    · simp [h_state]
      cases s.promises.find? (·.id == t.id) <;> simp
    · simp [h_state]

theorem onTaskLeaseTimeout_promises_eq (id : String) (now : Nat) (s : ServerState) :
    (Timeouts.onTaskLeaseTimeout id now s).snd.promises = s.promises := by
  unfold Timeouts.onTaskLeaseTimeout getTask getPromise
  by_cases h : s.tasks.find? (·.id == id) = none
  · simp [h]
  · have h' := Option.eq_none_or_eq_some _ |>.resolve_left h
    rcases h' with ⟨t, h⟩
    simp [h]
    by_cases h_state : t.state = TaskState.acquired
    · simp [h_state]
      cases s.promises.find? (·.id == t.id) <;> simp
    · simp [h_state]

theorem onResume_promises_eq (req : ResumeReq) (now : Nat) (s : ServerState) :
    (onResume req now s).2.promises = s.promises := by
  unfold onResume getTask getPromise
  by_cases h_t : s.tasks.find? (·.id == req.awaiter) = none
  · simp [h_t]
  · have h_t' := Option.eq_none_or_eq_some (s.tasks.find? (·.id == req.awaiter)) |>.resolve_left h_t
    rcases h_t' with ⟨t, h_t⟩
    simp [h_t]
    by_cases h_p : s.promises.find? (·.id == req.awaiter) = none
    · simp [h_p]
    · have h_p' := Option.eq_none_or_eq_some (s.promises.find? (·.id == req.awaiter)) |>.resolve_left h_p
      rcases h_p' with ⟨p, h_p⟩
      simp [h_p]
      by_cases h_to : now ≥ p.timeoutAt
      · simp [h_to]
      · simp [h_to]
        cases t.state <;> simp [h_to] <;> split <;> simp

theorem stepOf_promiseGet (req : PromiseGetReq) (now : Nat) (s : ServerState) :
    stepOf (.promiseGet req) now s =
      (match s.promises.find? (·.id == req.id) with
       | none => (Response.promiseGet { status := 404 }, s)
       | some p => (Response.promiseGet { status := 200, promise := some ((p.project now).toRecord) }, s)) := by
  simp only [run_stepOf, handle, promiseGet, getPromise, run_bind, run_get, run_pure, run_map]
  cases s.promises.find? (·.id == req.id) <;> rfl

theorem frozen_promiseGet (req : PromiseGetReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.promiseGet req) now s).2 id now = some st := by
  rw [stepOf_promiseGet]; cases s.promises.find? (·.id == req.id) <;> exact hl

theorem sound_promiseGet (req : PromiseGetReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.promiseGet req) now s).1 id st) :
    logical (stepOf (.promiseGet req) now s).2 id now = some st := by
  rw [stepOf_promiseGet] at hx ⊢
  cases hf : s.promises.find? (·.id == req.id) with
  | none => rw [hf] at hx; simp [Externalized, Response.promises] at hx
  | some p =>
      rw [hf] at hx
      simp only [Externalized, Response.promises, Option.toList, List.mem_singleton] at hx
      obtain ⟨q, hq, hid, hst⟩ := hx; subst hq
      have hpid : p.id = id := by rw [← hid]; simp [PromiseObject.toRecord, project_id]
      have hrid : p.id = req.id := by have := List.find?_some hf; simpa using this
      have hidr : id = req.id := hpid ▸ hrid; subst hidr
      simp only [logical]; rw [hf]; simp only [Option.map_some, Option.some.injEq]; rw [← hst]; rfl

theorem frozen_idle (now : Nat) (s : ServerState) (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf .idle now s).2 id now = some st := by
  unfold stepOf; unfold handle; simpa [logical] using hl

theorem sound_idle (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf .idle now s).1 id st) :
    logical (stepOf .idle now s).2 id now = some st := by
  simp [stepOf, handle, Externalized, Response.promises] at hx

theorem frozen_promiseSearch (r : PromiseSearchReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.promiseSearch r) now s).2 id now = some st := by
  unfold stepOf; unfold handle; simpa [promiseSearch, logical] using hl

theorem sound_promiseSearch (r : PromiseSearchReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.promiseSearch r) now s).1 id st) :
    logical (stepOf (.promiseSearch r) now s).2 id now = some st := by
  simp [stepOf, handle, promiseSearch, Externalized, Response.promises] at hx

theorem frozen_scheduleSearch (r : ScheduleSearchReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.scheduleSearch r) now s).2 id now = some st := by
  unfold stepOf; unfold handle; simpa [scheduleSearch, logical] using hl

theorem sound_scheduleSearch (r : ScheduleSearchReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.scheduleSearch r) now s).1 id st) :
    logical (stepOf (.scheduleSearch r) now s).2 id now = some st := by
  simp [stepOf, handle, scheduleSearch, Externalized, Response.promises] at hx

theorem frozen_taskSearch (r : TaskSearchReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.taskSearch r) now s).2 id now = some st := by
  unfold stepOf; unfold handle; simpa [taskSearch, logical] using hl

theorem sound_taskSearch (r : TaskSearchReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskSearch r) now s).1 id st) :
    logical (stepOf (.taskSearch r) now s).2 id now = some st := by
  simp [stepOf, handle, taskSearch, Externalized, Response.promises] at hx

theorem frozen_scheduleGet (r : ScheduleGetReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.scheduleGet r) now s).2 id now = some st := by
  have hprom : (stepOf (.scheduleGet r) now s).2.promises = s.promises := by
    simp only [run_stepOf, handle, scheduleGet, getSchedule, run_bind, run_get, run_pure, run_map]
    cases s.schedules.find? (·.id == r.id) <;> rfl
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_scheduleGet (r : ScheduleGetReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.scheduleGet r) now s).1 id st) :
    logical (stepOf (.scheduleGet r) now s).2 id now = some st := by
  simp [stepOf, handle, scheduleGet, getSchedule, run_bind, run_get, run_pure, run_map, Externalized, Response.promises] at hx

theorem frozen_scheduleCreate (r : ScheduleCreateReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.scheduleCreate r) now s).2 id now = some st := by
  have hprom : (stepOf (.scheduleCreate r) now s).2.promises = s.promises := by
    simp only [run_stepOf, handle, scheduleCreate, getSchedule, setSchedule, setScheduleTimeout, run_bind, run_get, run_pure, run_map]
    cases s.schedules.find? (·.id == r.id) <;> rfl
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_scheduleCreate (r : ScheduleCreateReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.scheduleCreate r) now s).1 id st) :
    logical (stepOf (.scheduleCreate r) now s).2 id now = some st := by
  simp [stepOf, handle, scheduleCreate, getSchedule, setSchedule, setScheduleTimeout, run_bind, run_get, run_pure, run_map, Externalized, Response.promises] at hx

theorem frozen_scheduleDelete (r : ScheduleDeleteReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.scheduleDelete r) now s).2 id now = some st := by
  have hprom : (stepOf (.scheduleDelete r) now s).2.promises = s.promises := by
    simp only [run_stepOf, handle, scheduleDelete, getSchedule, delSchedule, delScheduleTimeout, run_bind, run_get, run_pure, run_map]
    cases s.schedules.find? (·.id == r.id) <;> rfl
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_scheduleDelete (r : ScheduleDeleteReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.scheduleDelete r) now s).1 id st) :
    logical (stepOf (.scheduleDelete r) now s).2 id now = some st := by
  simp [stepOf, handle, scheduleDelete, getSchedule, delSchedule, delScheduleTimeout, run_bind, run_get, run_pure, run_map, Externalized, Response.promises] at hx

theorem frozen_taskGet (r : TaskGetReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.taskGet r) now s).2 id now = some st := by
  have hprom : (stepOf (.taskGet r) now s).2.promises = s.promises := by
    unfold stepOf; unfold handle
    simp [taskGet, getTask, getPromise, run_bind, run_get, run_pure, run_map]
    cases h1 : s.tasks.find? (·.id == r.id)
    · simp
    · rename_i t
      cases h2 : s.promises.find? (·.id == t.id)
      · simp [h2]
      · rename_i p; simp [h2]; split <;> rfl
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_taskGet (r : TaskGetReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskGet r) now s).1 id st) :
    logical (stepOf (.taskGet r) now s).2 id now = some st := by
  simp [stepOf, handle, taskGet, getTask, getPromise, run_bind, run_get, run_pure, run_map, Externalized, Response.promises] at hx

theorem frozen_taskHalt (r : TaskHaltReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.taskHalt r) now s).2 id now = some st := by
  have hprom : (stepOf (.taskHalt r) now s).2.promises = s.promises := by
    simp only [run_stepOf, handle, taskHalt, getTask, setTask, delTaskTimeout, run_bind, run_get, run_pure, run_map]
    cases h : s.tasks.find? (·.id == r.id)
    · simp
    · rename_i t; simp [h]; cases t.state with | fulfilled => simp | pending => simp | acquired => simp | halted => simp | suspended => simp
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_taskHalt (r : TaskHaltReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskHalt r) now s).1 id st) :
    logical (stepOf (.taskHalt r) now s).2 id now = some st := by
  simp [stepOf, handle, taskHalt, getTask, setTask, delTaskTimeout, run_bind, run_get, run_pure, run_map, Externalized, Response.promises] at hx

theorem frozen_taskContinue (r : TaskContinueReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.taskContinue r) now s).2 id now = some st := by
  have hprom : (stepOf (.taskContinue r) now s).2.promises = s.promises := by
    simp only [run_stepOf, handle, taskContinue, getTask, getPromise, setTask, setTaskTimeout, setMessage, run_bind, run_get, run_pure, run_map]
    cases h : s.tasks.find? (·.id == r.id)
    · simp
    · rename_i t; cases h_state : t.state with
      | fulfilled => simp [h_state]
      | pending => simp [h_state]
      | acquired => simp [h_state]
      | halted =>
          cases h2 : s.promises.find? (·.id == t.id)
          · simp [h_state, h2]
          · rename_i p; simp [h_state, h2]
            by_cases h_pending : ¬ p.state = .pending ∨ p.timeoutAt ≤ now
            · simp [h_pending]
            · simp [h_pending]
      | suspended => simp [h_state]
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_taskContinue (r : TaskContinueReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskContinue r) now s).1 id st) :
    logical (stepOf (.taskContinue r) now s).2 id now = some st := by
  simp [stepOf, handle, taskContinue, getTask, getPromise, setTask, setTaskTimeout, setMessage, run_bind, run_get, run_pure, run_map, Externalized, Response.promises] at hx

theorem frozen_taskRelease (r : TaskReleaseReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.taskRelease r) now s).2 id now = some st := by
  have hprom : (stepOf (.taskRelease r) now s).2.promises = s.promises := by
    simp only [run_stepOf, handle, taskRelease, getTask, getPromise, setTask, delTaskTimeout, setTaskTimeout, setMessage, run_bind, run_get, run_pure, run_map]
    cases h : s.tasks.find? (·.id == r.id)
    · simp
    · rename_i t
      cases h2 : s.promises.find? (·.id == t.id)
      · simp [h2]
      · rename_i p; simp [h2]
        cases h_state : t.state with
        | fulfilled => simp [h_state]
        | pending => simp [h_state]
        | acquired =>
            by_cases h_pending : ¬ p.state = .pending ∨ p.timeoutAt ≤ now
            · simp [h_pending]
            · simp [h_pending]
              by_cases h_version : t.version = r.version
              · simp [h_version]
              · simp [h_version]
        | halted => simp [h_state]
        | suspended => simp [h_state]
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_taskRelease (r : TaskReleaseReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskRelease r) now s).1 id st) :
    logical (stepOf (.taskRelease r) now s).2 id now = some st := by
  simp [stepOf, handle, taskRelease, getTask, getPromise, setTask, delTaskTimeout, setTaskTimeout, setMessage, run_bind, run_get, run_pure, run_map, Externalized, Response.promises] at hx

theorem frozen_τTaskRetryTimeout (id : String) (now : Nat) (s : ServerState) (st_id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s st_id now = some st) :
    logical (stepOf (.τTaskRetryTimeout id) now s).2 st_id now = some st := by
  have hprom : (stepOf (.τTaskRetryTimeout id) now s).2.promises = s.promises := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    by_cases h_any : (s.taskTimeouts.any (fun e => e.id == id && e.kind == 0 && decide (e.timeout ≤ now)))
    · simp [h_any, run_bind, run_get, run_pure, run_map]
      simpa using onTaskRetryTimeout_promises_eq id now s
    · simp [h_any, run_bind, run_get, run_pure, run_map]
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_τTaskRetryTimeout (id : String) (now : Nat) (s : ServerState) (st_id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.τTaskRetryTimeout id) now s).1 st_id st) :
    logical (stepOf (.τTaskRetryTimeout id) now s).2 st_id now = some st := by
  have hres : Response.promises (stepOf (.τTaskRetryTimeout id) now s).1 = [] := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    by_cases h_any : (s.taskTimeouts.any (fun e => e.id == id && e.kind == 0 && decide (e.timeout ≤ now)))
    · simp [h_any, run_bind, run_get, run_pure, run_map, Response.promises]
    · simp [h_any, run_bind, run_get, run_pure, run_map, Response.promises]
  have h_contra : ¬ Externalized (stepOf (.τTaskRetryTimeout id) now s).1 st_id st := by
    rw [Externalized, hres]
    simp
  exact absurd hx h_contra

theorem frozen_τTaskLeaseTimeout (id : String) (now : Nat) (s : ServerState) (st_id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s st_id now = some st) :
    logical (stepOf (.τTaskLeaseTimeout id) now s).2 st_id now = some st := by
  have hprom : (stepOf (.τTaskLeaseTimeout id) now s).2.promises = s.promises := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    by_cases h_any : (s.taskTimeouts.any (fun e => e.id == id && e.kind == 1 && decide (e.timeout ≤ now)))
    · simp [h_any, run_bind, run_get, run_pure, run_map]
      simpa using onTaskLeaseTimeout_promises_eq id now s
    · simp [h_any, run_bind, run_get, run_pure, run_map]
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_τTaskLeaseTimeout (id : String) (now : Nat) (s : ServerState) (st_id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.τTaskLeaseTimeout id) now s).1 st_id st) :
    logical (stepOf (.τTaskLeaseTimeout id) now s).2 st_id now = some st := by
  have hres : Response.promises (stepOf (.τTaskLeaseTimeout id) now s).1 = [] := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    by_cases h_any : (s.taskTimeouts.any (fun e => e.id == id && e.kind == 1 && decide (e.timeout ≤ now)))
    · simp [h_any, run_bind, run_get, run_pure, run_map, Response.promises]
    · simp [h_any, run_bind, run_get, run_pure, run_map, Response.promises]
  have h_contra : ¬ Externalized (stepOf (.τTaskLeaseTimeout id) now s).1 st_id st := by
    rw [Externalized, hres]
    simp
  exact absurd hx h_contra

theorem frozen_τResume (req : ResumeReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.τResume req) now s).2 id now = some st := by
  have hprom : (stepOf (.τResume req) now s).2.promises = s.promises := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    by_cases h : (s.deferred.any (fun d => d.awaited == req.awaited && d.awaiter == req.awaiter))
    · simp [h, onResume_promises_eq]
    · simp [h]
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_τResume (req : ResumeReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.τResume req) now s).1 id st) :
    logical (stepOf (.τResume req) now s).2 id now = some st := by
  have hres : Response.promises (stepOf (.τResume req) now s).1 = [] := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    by_cases h : (s.deferred.any (fun d => d.awaited == req.awaited && d.awaiter == req.awaiter))
    · simp [h, Response.promises]
    · simp [h, Response.promises]
  rw [run_stepOf] at hres
  simp [Externalized, hres] at hx

theorem frozen_τScheduleTimeout (id : String) (now : Nat) (s : ServerState) (st_id : String) (st : PromiseState)
    (_hset : Settled st) (hl : logical s st_id now = some st) :
    logical (stepOf (.τScheduleTimeout id) now s).2 st_id now = some st := by
  unfold logical at hl ⊢
  cases hfind : s.promises.find? (·.id == st_id) with
  | none => rw [hfind] at hl; simp at hl
  | some p =>
      rw [hfind] at hl
      have hpost : (stepOf (.τScheduleTimeout id) now s).2.promises.find? (·.id == st_id) = some p := by
        rw [run_stepOf]
        simp only [handle, run_bind, run_get, run_pure, run_map]
        by_cases h : (s.scheduleTimeouts.any (fun e => e.id == id && decide (e.timeout ≤ now)))
        · simp only [h, if_true]
          simp only [Timeouts.onScheduleTimeout, getSchedule, run_bind, run_get, run_pure]
          cases hs : s.schedules.find? (·.id == id) with
          | none => simp [hs]; exact hfind
          | some sch =>
              simp [hs, setSchedule, delScheduleTimeout, setScheduleTimeout]
              exact catchUp_find?_preserved 1000000 now sch s hfind
        · simp [h, hfind]
      rw [hpost]; exact hl

theorem sound_τScheduleTimeout (id : String) (now : Nat) (s : ServerState) (st_id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.τScheduleTimeout id) now s).1 st_id st) :
    logical (stepOf (.τScheduleTimeout id) now s).2 st_id now = some st := by
  have hres : Response.promises (stepOf (.τScheduleTimeout id) now s).1 = [] := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    by_cases h : (s.scheduleTimeouts.any (fun e => e.id == id && decide (e.timeout ≤ now)))
    · simp [h, Response.promises]
    · simp [h, Response.promises]
  rw [run_stepOf] at hres
  simp [Externalized, hres] at hx

theorem stepOf_taskHeartbeat (r : TaskHeartbeatReq) (now : Nat) (s : ServerState) :
    (stepOf (.taskHeartbeat r) now s).1 = Response.taskHeartbeat { status := 200 } := by
  simp only [run_stepOf, handle, taskHeartbeat, run_bind, run_get, run_pure, run_map]

theorem taskHeartbeat_promises_eq (req : TaskHeartbeatReq) (now : Nat) (s : ServerState) :
    (taskHeartbeat req now s).2.promises = s.promises := by
  unfold taskHeartbeat
  simp only [run_bind, run_pure]
  exact forIn_inv (fun st => st.promises = s.promises)
    _
    (by
      intro ref b st hst
      by_cases h : st.tasks.find? (·.id == ref.id) = none
      · simpa [getTask, h] using hst
      · obtain ⟨t, h⟩ := Option.eq_none_or_eq_some (st.tasks.find? (·.id == ref.id)) |>.resolve_left h
        by_cases hc : (t.state = TaskState.acquired ∧ t.version = ref.version ∧ t.pid = some req.pid)
        · by_cases hp : st.promises.find? (·.id == t.id) = none
          · simpa [getTask, getPromise, h, hc, hp] using hst
          · obtain ⟨p, hp⟩ := Option.eq_none_or_eq_some (st.promises.find? (·.id == t.id)) |>.resolve_left hp
            by_cases hl : (p.state = PromiseState.pending ∧ now < p.timeoutAt)
            · simpa [getTask, getPromise, h, hc, hp, hl, delTaskTimeout, setTaskTimeout] using hst
            · simpa [getTask, getPromise, h, hc, hp, hl] using hst
        · simpa [getTask, h, hc] using hst)
    req.tasks () s rfl

theorem frozen_taskHeartbeat (r : TaskHeartbeatReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.taskHeartbeat r) now s).2 id now = some st := by
  have hprom : (stepOf (.taskHeartbeat r) now s).2.promises = s.promises := by
    simp [run_stepOf, handle, taskHeartbeat_promises_eq]
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_taskHeartbeat (r : TaskHeartbeatReq) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskHeartbeat r) now s).1 id st) :
    logical (stepOf (.taskHeartbeat r) now s).2 id now = some st := by
  rw [stepOf_taskHeartbeat] at hx; simp [Externalized, Response.promises] at hx

theorem taskAcquire_promises_eq (r : TaskAcquireReq) (now : Nat) (s : ServerState) :
    (taskAcquire r now s).2.promises = s.promises := by
  unfold taskAcquire getTask getPromise
  by_cases h : s.tasks.find? (·.id == r.id) = none
  · simp [h]
  · obtain ⟨t, h⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == r.id)) |>.resolve_left h
    simp [h]
    by_cases hp : s.promises.find? (·.id == t.id) = none
    · simp [hp]
    · obtain ⟨p, hp⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == t.id)) |>.resolve_left hp
      simp [hp]
      by_cases h1 : t.state = TaskState.pending
      · simp [h1]
        by_cases h2 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
        · simp [h2]
        · simp [h2]
          by_cases h3 : t.version = r.version
          · simp [h3, setTask, delTaskTimeout, setTaskTimeout]
          · simp [h3]
      · simp [h1]

theorem taskAcquire_res_eq (r : TaskAcquireReq) (now : Nat) (s : ServerState) :
    (taskAcquire r now s).1 =
      (match s.tasks.find? (·.id == r.id) with
       | none => { status := 404 }
       | some t =>
         match s.promises.find? (·.id == t.id) with
         | none => { status := 409 }
         | some p =>
           if t.state ≠ TaskState.pending then { status := 409 }
           else if p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now then { status := 409 }
           else if t.version ≠ r.version then { status := 409 }
           else { status := 200,
                  task := some ({ t with state := .acquired, version := t.version + 1, ttl := some r.ttl, pid := some r.pid, resumes := [] } : TaskObject).toRecord,
                  promise := some p.toRecord }) := by
  unfold taskAcquire getTask getPromise
  by_cases h : s.tasks.find? (·.id == r.id) = none
  · simp [h]
  · obtain ⟨t, h⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == r.id)) |>.resolve_left h
    simp [h]
    by_cases hp : s.promises.find? (·.id == t.id) = none
    · simp [hp]
    · obtain ⟨p, hp⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == t.id)) |>.resolve_left hp
      simp [hp]
      by_cases h1 : t.state = TaskState.pending
      · by_cases h2 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
        · simp [h1, h2]
        · by_cases h3 : t.version = r.version
          · simp [h1, h2, h3, setTask, delTaskTimeout, setTaskTimeout]
          · simp [h1, h2, h3]
      · simp [h1]

theorem frozen_taskAcquire (r : TaskAcquireReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.taskAcquire r) now s).2 id now = some st := by
  have hprom : (stepOf (.taskAcquire r) now s).2.promises = s.promises := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    exact taskAcquire_promises_eq r now s
  unfold logical at hl ⊢; rw [hprom]; exact hl

theorem sound_taskAcquire (r : TaskAcquireReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskAcquire r) now s).1 id st) :
    logical (stepOf (.taskAcquire r) now s).2 id now = some st := by
  rw [run_stepOf] at hx ⊢
  simp only [handle, run_map] at hx ⊢
  rw [taskAcquire_res_eq] at hx
  have hgoal : logical ((taskAcquire r now) s).2 id now = logical s id now := by
    unfold logical; rw [taskAcquire_promises_eq]
  rw [hgoal]
  cases hf : s.tasks.find? (·.id == r.id) with
  | none => simp only [hf] at hx; simp [Externalized, Response.promises] at hx
  | some t =>
      simp only [hf] at hx
      cases hfp : s.promises.find? (·.id == t.id) with
      | none => simp only [hfp] at hx; simp [Externalized, Response.promises] at hx
      | some p =>
          simp only [hfp] at hx
          by_cases h1 : t.state ≠ TaskState.pending
          · simp [h1, Externalized, Response.promises] at hx
          · by_cases h2 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
            · simp [h1, h2, Externalized, Response.promises] at hx
            · by_cases h3 : t.version ≠ r.version
              · simp [h1, h2, h3, Externalized, Response.promises] at hx
              · simp [h1, h2, h3, Externalized, Response.promises] at hx
                obtain ⟨hid, hst⟩ := hx
                have hlive : now < p.timeoutAt :=
                  Nat.not_le.mp (fun hle => h2 (Or.inr hle))
                have hpid : p.id = t.id := by
                  have := List.find?_some hfp; simpa using this
                unfold logical
                rw [← hid]
                simp only [PromiseObject.toRecord]
                rw [hpid, hfp]
                simp [project_of_live p now hlive, ← hst, PromiseObject.toRecord]

theorem addCallback_id (p : PromiseObject) (c : String) : (p.addCallback c).id = p.id := by
  unfold PromiseObject.addCallback; split <;> rfl

theorem addListener_id (p : PromiseObject) (a : String) : (p.addListener a).id = p.id := by
  unfold PromiseObject.addListener; split <;> rfl

/-- `addCallback` never changes what `project` reports: it touches only
    the `callbacks` field, and projection reads `state`, `timeoutAt`,
    and `tags` alone. -/
theorem addCallback_project_state (p : PromiseObject) (c : String) (now : Nat) :
    ((p.addCallback c).project now).state = (p.project now).state := by
  unfold PromiseObject.addCallback
  split
  · rfl
  · unfold PromiseObject.project PromiseObject.isTimer Tags.isTimer
    by_cases hC : p.state == PromiseState.pending ∧ p.timeoutAt ≤ now
    · rw [if_pos hC, if_pos hC]
      split <;> rfl
    · rw [if_neg hC, if_neg hC]

theorem addListener_project_state (p : PromiseObject) (a : String) (now : Nat) :
    ((p.addListener a).project now).state = (p.project now).state := by
  unfold PromiseObject.addListener
  split
  · rfl
  · unfold PromiseObject.project PromiseObject.isTimer Tags.isTimer
    by_cases hC : p.state == PromiseState.pending ∧ p.timeoutAt ≤ now
    · rw [if_pos hC, if_pos hC]
      split <;> rfl
    · rw [if_neg hC, if_neg hC]

/-- Writing back a promise whose projected STATE is unchanged does not
    move the logical view of any id. `q` is the rewritten object: same
    id, same projected state, arbitrary other fields. -/
theorem logical_write_same_state (s : ServerState) (pA q : PromiseObject) (id : String) (now : Nat)
    (hpa : s.promises.find? (·.id == pA.id) = some pA)
    (hqid : q.id = pA.id)
    (hqst : (q.project now).state = (pA.project now).state) :
    logical { s with promises := q :: s.promises.filter (·.id != q.id) } id now
      = logical s id now := by
  unfold logical
  by_cases hid : id = pA.id
  · subst hid
    have hhead : (q.id == pA.id) = true := by simp [hqid]
    simp [List.find?_cons, hhead, hpa, hqst]
  · have hhead : (q.id == id) = false := by
      rw [hqid]; exact beq_eq_false_iff_ne.mpr (fun he => hid he.symm)
    simp only [List.find?_cons, hhead, cond_false]
    rw [hqid]
    rw [find?_filter_ne (fun he => hid he)]

theorem stepOf_promiseRegisterCallback (r : PromiseRegisterCallbackReq) (now : Nat) (s : ServerState) :
    stepOf (.promiseRegisterCallback r) now s =
      (if r.awaited == r.awaiter then (Response.promiseRegisterCallback { status := 400 }, s)
       else match s.promises.find? (·.id == r.awaited) with
       | none => (Response.promiseRegisterCallback { status := 404 }, s)
       | some pA =>
         match s.promises.find? (·.id == r.awaiter) with
         | none => (Response.promiseRegisterCallback { status := 422 }, s)
         | some pAw =>
           if ¬(pAw.tags.has "resonate:target") then (Response.promiseRegisterCallback { status := 422 }, s)
           else if ¬pA.external then (Response.promiseRegisterCallback { status := 422 }, s)
           else if pA.state = PromiseState.pending ∧ now < pA.timeoutAt then
             (Response.promiseRegisterCallback { status := 200, promise := some pA.toRecord },
              if pAw.state = PromiseState.pending ∧ now < pAw.timeoutAt then
                { s with promises := (pA.addCallback r.awaiter) :: s.promises.filter (·.id != (pA.addCallback r.awaiter).id) }
              else s)
           else (Response.promiseRegisterCallback { status := 200, promise := some (pA.project now).toRecord }, s)) := by
  rw [run_stepOf]
  simp only [handle, run_bind, run_get, run_pure, run_map]
  unfold promiseRegisterCallback getPromise
  by_cases h0 : r.awaited == r.awaiter
  · simp [h0]
  · simp only [h0]
    by_cases h : s.promises.find? (·.id == r.awaited) = none
    · simp [h0, h]
    · obtain ⟨pA, h⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == r.awaited)) |>.resolve_left h
      simp [h0, h]
      by_cases h2 : s.promises.find? (·.id == r.awaiter) = none
      · simp [h2]
      · obtain ⟨pAw, h2⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == r.awaiter)) |>.resolve_left h2
        simp [h2]
        by_cases h3 : pAw.tags.has "resonate:target"
        · by_cases h4 : pA.external
          · by_cases h5 : (pA.state = PromiseState.pending ∧ now < pA.timeoutAt)
            · by_cases h6 : (pAw.state = PromiseState.pending ∧ now < pAw.timeoutAt)
              · simp [h3, h4, h5, h6, setPromise]
              · simp [h3, h4, h5, h6]
            · simp [h3, h4, h5]
          · simp [h3, h4]
        · simp [h3]

theorem frozen_promiseRegisterCallback (r : PromiseRegisterCallbackReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.promiseRegisterCallback r) now s).2 id now = some st := by
  rw [stepOf_promiseRegisterCallback]
  by_cases h0 : r.awaited == r.awaiter
  · simp only [h0, if_true]; exact hl
  · simp only [h0, Bool.false_eq_true, if_false]
    cases hf : s.promises.find? (·.id == r.awaited) with
    | none => exact hl
    | some pA =>
        cases hf2 : s.promises.find? (·.id == r.awaiter) with
        | none => exact hl
        | some pAw =>
            by_cases h3 : ¬(pAw.tags.has "resonate:target")
            · simp only [h3, if_true]; exact hl
            · simp only [h3, if_false]
              by_cases h4 : ¬pA.external
              · simp only [h4, if_true]; exact hl
              · simp only [h4, if_false]
                by_cases h5 : (pA.state = PromiseState.pending ∧ now < pA.timeoutAt)
                · simp only [h5, and_self, if_true]
                  by_cases h6 : (pAw.state = PromiseState.pending ∧ now < pAw.timeoutAt)
                  · simp only [h6, and_self, if_true]
                    have hpa' : s.promises.find? (·.id == pA.id) = some pA := by
                      have hpid : pA.id = r.awaited := by
                        have := List.find?_some hf; simpa using this
                      rw [hpid]; exact hf
                    rw [logical_write_same_state s pA (pA.addCallback r.awaiter) id now hpa'
                      (addCallback_id pA _) (addCallback_project_state pA _ now)]
                    exact hl
                  · simp only [h6, and_self, if_false]; exact hl
                · simp only [h5, and_self, if_false]; exact hl

theorem sound_promiseRegisterCallback (r : PromiseRegisterCallbackReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.promiseRegisterCallback r) now s).1 id st) :
    logical (stepOf (.promiseRegisterCallback r) now s).2 id now = some st := by
  rw [stepOf_promiseRegisterCallback] at hx ⊢
  by_cases h0 : r.awaited == r.awaiter
  · simp only [h0, if_true] at hx; simp [Externalized, Response.promises] at hx
  · simp only [h0, Bool.false_eq_true, if_false] at hx ⊢
    cases hf : s.promises.find? (·.id == r.awaited) with
    | none => simp only [hf] at hx; simp [Externalized, Response.promises] at hx
    | some pA =>
        simp only [hf] at hx ⊢
        cases hf2 : s.promises.find? (·.id == r.awaiter) with
        | none => simp only [hf2] at hx; simp [Externalized, Response.promises] at hx
        | some pAw =>
            simp only [hf2] at hx ⊢
            have hpa' : s.promises.find? (·.id == pA.id) = some pA := by
              have hpid : pA.id = r.awaited := by
                have := List.find?_some hf; simpa using this
              rw [hpid]; exact hf
            by_cases h3 : ¬(pAw.tags.has "resonate:target")
            · simp only [h3, if_true] at hx; simp [Externalized, Response.promises] at hx
            · simp only [h3, if_false] at hx ⊢
              by_cases h4 : ¬pA.external
              · simp only [h4, if_true] at hx; simp [Externalized, Response.promises] at hx
              · simp only [h4, if_false] at hx ⊢
                by_cases h5 : (pA.state = PromiseState.pending ∧ now < pA.timeoutAt)
                · simp only [h5, and_self, if_true] at hx ⊢
                  simp [Externalized, Response.promises] at hx
                  obtain ⟨hid, hst⟩ := hx
                  by_cases h6 : (pAw.state = PromiseState.pending ∧ now < pAw.timeoutAt)
                  · simp only [h6, and_self, if_true]
                    rw [logical_write_same_state s pA (pA.addCallback r.awaiter) id now hpa'
                      (addCallback_id pA _) (addCallback_project_state pA _ now)]
                    unfold logical
                    rw [← hid]
                    simp only [PromiseObject.toRecord]
                    rw [hpa']
                    simp [project_of_live pA now h5.2, ← hst, PromiseObject.toRecord]
                  · simp only [h6, and_self, if_false]
                    unfold logical
                    rw [← hid]
                    simp only [PromiseObject.toRecord]
                    rw [hpa']
                    simp [project_of_live pA now h5.2, ← hst, PromiseObject.toRecord]
                · simp only [h5, and_self, if_false] at hx ⊢
                  simp [Externalized, Response.promises] at hx
                  obtain ⟨hid, hst⟩ := hx
                  unfold logical
                  rw [← hid]
                  simp only [PromiseObject.toRecord, project_id]
                  rw [hpa']
                  simp [← hst, PromiseObject.toRecord]

theorem stepOf_promiseRegisterListener (r : PromiseRegisterListenerReq) (now : Nat) (s : ServerState) :
    stepOf (.promiseRegisterListener r) now s =
      (if ¬addressValid r.address then (Response.promiseRegisterListener { status := 400 }, s)
       else match s.promises.find? (·.id == r.awaited) with
       | none => (Response.promiseRegisterListener { status := 404 }, s)
       | some pA =>
         if pA.state = PromiseState.pending ∧ now < pA.timeoutAt then
           (Response.promiseRegisterListener { status := 200, promise := some pA.toRecord },
            { s with promises := (pA.addListener r.address) :: s.promises.filter (·.id != (pA.addListener r.address).id) })
         else (Response.promiseRegisterListener { status := 200, promise := some (pA.project now).toRecord }, s)) := by
  rw [run_stepOf]
  simp only [handle, run_bind, run_get, run_pure, run_map]
  unfold promiseRegisterListener getPromise
  by_cases h0 : addressValid r.address
  · simp only [h0]
    by_cases h : s.promises.find? (·.id == r.awaited) = none
    · simp [h0, h]
    · obtain ⟨pA, h⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == r.awaited)) |>.resolve_left h
      simp [h0, h]
      by_cases h5 : (pA.state = PromiseState.pending ∧ now < pA.timeoutAt)
      · simp [h5, setPromise]
      · simp [h5]
  · simp [h0]

theorem frozen_promiseRegisterListener (r : PromiseRegisterListenerReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.promiseRegisterListener r) now s).2 id now = some st := by
  rw [stepOf_promiseRegisterListener]
  by_cases h0 : ¬addressValid r.address
  · simp only [h0, if_true]; exact hl
  · simp only [h0, if_false]
    cases hf : s.promises.find? (·.id == r.awaited) with
    | none => exact hl
    | some pA =>
        by_cases h5 : (pA.state = PromiseState.pending ∧ now < pA.timeoutAt)
        · simp only [h5, and_self, if_true]
          have hpa' : s.promises.find? (·.id == pA.id) = some pA := by
            have hpid : pA.id = r.awaited := by
              have := List.find?_some hf; simpa using this
            rw [hpid]; exact hf
          rw [logical_write_same_state s pA (pA.addListener r.address) id now hpa'
            (addListener_id pA _) (addListener_project_state pA _ now)]
          exact hl
        · simp only [h5, and_self, if_false]; exact hl

theorem sound_promiseRegisterListener (r : PromiseRegisterListenerReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.promiseRegisterListener r) now s).1 id st) :
    logical (stepOf (.promiseRegisterListener r) now s).2 id now = some st := by
  rw [stepOf_promiseRegisterListener] at hx ⊢
  by_cases h0 : ¬addressValid r.address
  · simp only [h0, if_true] at hx; simp [Externalized, Response.promises] at hx
  · simp only [h0, if_false] at hx ⊢
    cases hf : s.promises.find? (·.id == r.awaited) with
    | none => simp only [hf] at hx; simp [Externalized, Response.promises] at hx
    | some pA =>
        simp only [hf] at hx ⊢
        have hpa' : s.promises.find? (·.id == pA.id) = some pA := by
          have hpid : pA.id = r.awaited := by
            have := List.find?_some hf; simpa using this
          rw [hpid]; exact hf
        by_cases h5 : (pA.state = PromiseState.pending ∧ now < pA.timeoutAt)
        · simp only [h5, and_self, if_true] at hx ⊢
          simp [Externalized, Response.promises] at hx
          obtain ⟨hid, hst⟩ := hx
          rw [logical_write_same_state s pA (pA.addListener r.address) id now hpa'
            (addListener_id pA _) (addListener_project_state pA _ now)]
          unfold logical
          rw [← hid]
          simp only [PromiseObject.toRecord]
          rw [hpa']
          simp [project_of_live pA now h5.2, ← hst, PromiseObject.toRecord]
        · simp only [h5, and_self, if_false] at hx ⊢
          simp [Externalized, Response.promises] at hx
          obtain ⟨hid, hst⟩ := hx
          unfold logical
          rw [← hid]
          simp only [PromiseObject.toRecord, project_id]
          rw [hpa']
          simp [← hst, PromiseObject.toRecord]

/-- A loop whose body leaves the state untouched leaves it untouched. -/
theorem forIn_state_id {α β : Type} (f : α → β → M (ForInStep β))
    (hf : ∀ a b s, ((f a b) s).2 = s) :
    ∀ (l : List α) (b : β) (s : ServerState), ((forIn l b f : M β) s).2 = s := by
  intro l
  induction l with
  | nil => intro b s; rfl
  | cons x xs ih =>
      intro b s
      rw [List.forIn_cons]
      simp only [run_bind]
      cases hstep : ((f x b) s).1 with
      | done b' => exact hf x b s
      | yield b' => rw [ih b' _]; exact hf x b s

/-- A loop-value invariant: preserved by every done/yield, holds at the end. -/
theorem forIn_val_inv {α β : Type} (P : β → Prop) (f : α → β → M (ForInStep β))
    (hf : ∀ a b s, P b → (match ((f a b) s).1 with
      | .done b' => P b' | .yield b' => P b')) :
    ∀ (l : List α) (b : β) (s : ServerState), P b → P ((forIn l b f : M β) s).1 := by
  intro l
  induction l with
  | nil => intro b s h; exact h
  | cons x xs ih =>
      intro b s h
      rw [List.forIn_cons]
      simp only [run_bind]
      have hb := hf x b s h
      cases hstep : ((f x b) s).1 with
      | done b' => rw [hstep] at hb; exact hb
      | yield b' => rw [hstep] at hb; exact ih b' _ hb

/-- Loop 1 of `taskSuspend`, as elaborated: read-only await validation. -/
private def suspF (r : TaskSuspendReq) (now : Nat) :
    PromiseRegisterCallbackReq → MProd (Option TaskSuspendRes) Bool →
      M (ForInStep (MProd (Option TaskSuspendRes) Bool)) := fun action racc => do
  let a ← get
  match a.promises.find? (·.id == action.awaited) with
  | none => pure (ForInStep.done ⟨some { status := 422 }, racc.snd⟩)
  | some pa =>
    if pa.external = false then pure (ForInStep.done ⟨some { status := 422 }, racc.snd⟩)
    else if ¬pa.state = PromiseState.pending ∨ pa.timeoutAt ≤ now then
      pure (ForInStep.yield ⟨none, true⟩)
    else pure (ForInStep.yield ⟨none, racc.snd⟩)

/-- Loop 2 of `taskSuspend`, as elaborated: the callback registrations. -/
private def suspF2 (r : TaskSuspendReq) :
    PromiseRegisterCallbackReq → PUnit → M (ForInStep PUnit) := fun action _ => do
  let a ← get
  match a.promises.find? (·.id == action.awaited) with
  | some pa => (fun _ => ForInStep.yield PUnit.unit) <$> setPromise (pa.addCallback r.id)
  | none => pure (ForInStep.yield PUnit.unit)

/-- The continuation after loop 1, as elaborated. -/
private def suspG (r : TaskSuspendReq) (t : TaskObject) :
    MProd (Option TaskSuspendRes) Bool → M TaskSuspendRes := fun r1 =>
  match r1.fst with
  | none =>
      if r1.snd = true then
        (fun _ => { status := 300 }) <$>
          setTask { id := t.id, state := t.state, version := t.version, ttl := t.ttl, pid := t.pid }
      else do
        forIn r.actions PUnit.unit (suspF2 r)
        setTask { id := t.id, state := TaskState.suspended, version := t.version }
        (fun _ => { status := 200 }) <$> delTaskTimeout t.id
  | some a => pure a

theorem suspF_state_id (r : TaskSuspendReq) (now : Nat) :
    ∀ a b σ, ((suspF r now a b) σ).2 = σ := by
  intro a b σ
  unfold suspF
  by_cases h : σ.promises.find? (·.id == a.awaited) = none
  · simp [h]
  · obtain ⟨pa, h⟩ := Option.eq_none_or_eq_some (σ.promises.find? (·.id == a.awaited)) |>.resolve_left h
    simp only [run_bind, run_get, run_pure, h]
    by_cases hext : pa.external = false
    · simp [hext]
    · simp only [hext, if_false]
      by_cases hsettled : (¬pa.state = PromiseState.pending ∨ pa.timeoutAt ≤ now)
      · simp [hsettled]
      · simp [hsettled]

theorem suspF2_logical (r : TaskSuspendReq) (id : String) (now : Nat) (stv : PromiseState) :
    ∀ a b σ, logical σ id now = some stv →
      logical ((suspF2 r a b) σ).2 id now = some stv := by
  intro a b σ hσ
  unfold suspF2
  by_cases h : σ.promises.find? (·.id == a.awaited) = none
  · simpa [h] using hσ
  · obtain ⟨pa, h⟩ := Option.eq_none_or_eq_some (σ.promises.find? (·.id == a.awaited)) |>.resolve_left h
    have hpa' : σ.promises.find? (·.id == pa.id) = some pa := by
      have hpid : pa.id = a.awaited := by
        have := List.find?_some h; simpa using this
      rw [hpid]; exact h
    simp only [run_bind, run_get, run_pure, h]
    have := logical_write_same_state σ pa (pa.addCallback r.id) id now hpa'
      (addCallback_id pa _) (addCallback_project_state pa _ now)
    simp only [run_map, setPromise, run_modify]
    rw [this]
    exact hσ

set_option maxHeartbeats 2000000 in
theorem stepOf_taskSuspend (r : TaskSuspendReq) (now : Nat) (s : ServerState) :
    stepOf (.taskSuspend r) now s =
      (if r.actions.isEmpty then (Response.taskSuspend { status := 400 }, s)
       else if r.actions.any (·.awaited == r.id) then (Response.taskSuspend { status := 400 }, s)
       else if (r.actions.map (·.awaited)).eraseDups.length ≠ r.actions.length then
         (Response.taskSuspend { status := 400 }, s)
       else match s.tasks.find? (·.id == r.id) with
       | none => (Response.taskSuspend { status := 404 }, s)
       | some t =>
         match s.promises.find? (·.id == t.id) with
         | none => (Response.taskSuspend { status := 409 }, s)
         | some tp =>
           if t.state ≠ TaskState.acquired then (Response.taskSuspend { status := 409 }, s)
           else if tp.state ≠ PromiseState.pending ∨ tp.timeoutAt ≤ now then (Response.taskSuspend { status := 409 }, s)
           else if t.version ≠ r.version then (Response.taskSuspend { status := 409 }, s)
           else (Response.taskSuspend ((forIn r.actions (⟨none, false⟩ : MProd (Option TaskSuspendRes) Bool) (suspF r now) >>= suspG r t) s).1,
                 ((forIn r.actions (⟨none, false⟩ : MProd (Option TaskSuspendRes) Bool) (suspF r now) >>= suspG r t) s).2)) := by
  rw [run_stepOf]
  simp only [handle, run_bind, run_get, run_pure, run_map]
  unfold taskSuspend getTask getPromise
  by_cases h_empty : r.actions.isEmpty
  · simp [h_empty]
  · by_cases h_any : r.actions.any (·.awaited == r.id)
    · simp [h_empty, h_any]
    · by_cases h_dup : (r.actions.map (·.awaited)).eraseDups.length = r.actions.length
      · by_cases h_task : s.tasks.find? (·.id == r.id) = none
        · simp [h_empty, h_any, h_dup, h_task, List.length_map]
        · obtain ⟨t, h_task⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == r.id)) |>.resolve_left h_task
          by_cases h_tp : s.promises.find? (·.id == t.id) = none
          · simp [h_empty, h_any, h_dup, h_task, h_tp, List.length_map]
          · obtain ⟨tp, h_tp⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == t.id)) |>.resolve_left h_tp
            by_cases hst1 : t.state = TaskState.acquired
            · by_cases hst2 : (tp.state ≠ PromiseState.pending ∨ tp.timeoutAt ≤ now)
              · simp [h_empty, h_any, h_dup, h_task, h_tp, hst1, hst2, List.length_map]
              · by_cases hver : t.version = r.version
                · simp [h_empty, h_any, h_dup, h_task, h_tp, hst1, hst2, hver, List.length_map,
                    suspF, suspG, suspF2]
                  try rfl
                  try (constructor <;> rfl)
                · simp [h_empty, h_any, h_dup, h_task, h_tp, hst1, hst2, hver, List.length_map]
            · simp [h_empty, h_any, h_dup, h_task, h_tp, hst1, List.length_map]
      · simp [h_empty, h_any, h_dup, List.length_map]

theorem suspF_val_P (r : TaskSuspendReq) (now : Nat) :
    ∀ a b σ, (∀ res, (b : MProd (Option TaskSuspendRes) Bool).fst = some res → res.preload = []) →
      (match ((suspF r now a b) σ).1 with
        | .done b' => ∀ res, b'.fst = some res → res.preload = []
        | .yield b' => ∀ res, b'.fst = some res → res.preload = []) := by
  intro a b σ _hP
  unfold suspF
  by_cases h : σ.promises.find? (·.id == a.awaited) = none
  · simp [h]
  · obtain ⟨pa, h⟩ := Option.eq_none_or_eq_some (σ.promises.find? (·.id == a.awaited)) |>.resolve_left h
    simp only [run_bind, run_get, run_pure, h]
    by_cases hext : pa.external = false
    · simp [hext]
    · simp only [hext, if_false]
      by_cases hsettled : (¬pa.state = PromiseState.pending ∨ pa.timeoutAt ≤ now)
      · simp [hsettled]
      · simp [hsettled]

theorem frozen_taskSuspend (r : TaskSuspendReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.taskSuspend r) now s).2 id now = some st := by
  rw [stepOf_taskSuspend]
  repeat first
    | exact hl
    | split
  simp only [run_bind]
  have hs1 : ((forIn r.actions (⟨none, false⟩ : MProd (Option TaskSuspendRes) Bool)
      (suspF r now) : M (MProd (Option TaskSuspendRes) Bool)) s).2 = s :=
    forIn_state_id _ (suspF_state_id r now) r.actions _ s
  rw [hs1]
  cases hval : ((forIn r.actions (⟨none, false⟩ : MProd (Option TaskSuspendRes) Bool)
      (suspF r now) : M (MProd (Option TaskSuspendRes) Bool)) s).1 with
  | mk v1 v2 =>
      cases v1 with
      | some a => exact hl
      | none =>
          by_cases hsnd : v2 = true
          · subst hsnd; exact hl
          · have hv2 : v2 = false := by cases v2 <;> simp_all
            subst hv2
            exact forIn_inv (fun σ => logical σ id now = some st) _
              (suspF2_logical r id now st) r.actions PUnit.unit s hl

theorem taskSuspend_res_promises (r : TaskSuspendReq) (now : Nat) (s : ServerState) :
    Response.promises (stepOf (.taskSuspend r) now s).1 = [] := by
  rw [stepOf_taskSuspend]
  repeat first
    | rfl
    | split
  simp only [run_bind]
  have hs1 : ((forIn r.actions (⟨none, false⟩ : MProd (Option TaskSuspendRes) Bool)
      (suspF r now) : M (MProd (Option TaskSuspendRes) Bool)) s).2 = s :=
    forIn_state_id _ (suspF_state_id r now) r.actions _ s
  rw [hs1]
  have hP : ∀ res, (((forIn r.actions (⟨none, false⟩ : MProd (Option TaskSuspendRes) Bool)
      (suspF r now) : M (MProd (Option TaskSuspendRes) Bool)) s).1).fst = some res → res.preload = [] :=
    forIn_val_inv (fun b => ∀ res, b.fst = some res → res.preload = [])
      (suspF r now)
      (by intro a b σ hPb
          have h := suspF_val_P r now a b σ hPb
          cases hstep : ((suspF r now a b) σ).1 with
          | done b' => rw [hstep] at h; exact h
          | yield b' => rw [hstep] at h; exact h)
      r.actions _ s
      (by intro res h; simp at h)
  cases hval : ((forIn r.actions (⟨none, false⟩ : MProd (Option TaskSuspendRes) Bool)
      (suspF r now) : M (MProd (Option TaskSuspendRes) Bool)) s).1 with
  | mk v1 v2 =>
      rw [hval] at hP
      cases v1 with
      | some a =>
          simp only [suspG, run_pure, Response.promises]
          exact hP a rfl
      | none =>
          by_cases hsnd : v2 = true
          · subst hsnd
            simp [suspG, Response.promises, setTask]
          · have hv2 : v2 = false := by cases v2 <;> simp_all
            subst hv2
            simp [suspG, Response.promises, setTask, delTaskTimeout]

theorem sound_taskSuspend (r : TaskSuspendReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskSuspend r) now s).1 id st) :
    logical (stepOf (.taskSuspend r) now s).2 id now = some st := by
  have hres := taskSuspend_res_promises r now s
  rw [run_stepOf] at hres
  simp [Externalized, hres] at hx

theorem promiseCreate_res_eq (req : PromiseCreateReq) (now : Nat) (s : ServerState) :
    (promiseCreate req now s).1 =
      (match s.promises.find? (·.id == req.id) with
       | some p => { status := 200, promise := some ((p.project now).toRecord) }
       | none =>
         if now < req.timeoutAt then
           { status := 200, promise := some ({ id := req.id, state := .pending, param := req.param, tags := req.tags, timeoutAt := req.timeoutAt, createdAt := now } : PromiseObject).toRecord }
         else
           { status := 200, promise := some ({ id := req.id, state := (if req.tags.isTimer then .resolved else .rejectedTimedout), param := req.param, tags := req.tags, timeoutAt := req.timeoutAt, createdAt := req.timeoutAt, settledAt := some req.timeoutAt } : PromiseObject).toRecord }) := by
  unfold promiseCreate getPromise
  by_cases hfind : s.promises.find? (·.id == req.id) = none
  · by_cases hto : now < req.timeoutAt
    · cases htarget : req.tags.get? "resonate:target" with
      | none =>
          simp [hfind, hto, htarget, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
          repeat first | rfl | split
      | some target =>
          cases hdelay : req.tags.get? "resonate:delay" with
          | none =>
              simp [hfind, hto, htarget, hdelay, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
              repeat first | rfl | split
          | some dstr =>
              by_cases hd : dstr.toNat! > now
              · simp [hfind, hto, htarget, hdelay, hd, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
                repeat first | rfl | split
              · simp [hfind, hto, htarget, hdelay, hd, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
                repeat first | rfl | split
    · simp [hfind, hto, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
      repeat first | rfl | split
  · obtain ⟨p, hfind⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == req.id)) |>.resolve_left hfind
    simp [hfind]

theorem promiseCreate_promises_eq (req : PromiseCreateReq) (now : Nat) (s : ServerState) :
    (promiseCreate req now s).2.promises =
      (match s.promises.find? (·.id == req.id) with
       | some _ => s.promises
       | none =>
         (if now < req.timeoutAt then
            ({ id := req.id, state := .pending, param := req.param, tags := req.tags, timeoutAt := req.timeoutAt, createdAt := now } : PromiseObject)
          else
            ({ id := req.id, state := (if req.tags.isTimer then .resolved else .rejectedTimedout), param := req.param, tags := req.tags, timeoutAt := req.timeoutAt, createdAt := req.timeoutAt, settledAt := some req.timeoutAt } : PromiseObject))
           :: s.promises.filter (·.id != req.id)) := by
  unfold promiseCreate getPromise
  by_cases hfind : s.promises.find? (·.id == req.id) = none
  · by_cases hto : now < req.timeoutAt
    · cases htarget : req.tags.get? "resonate:target" with
      | none =>
          simp [hfind, hto, htarget, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
          repeat first | rfl | split
      | some target =>
          cases hdelay : req.tags.get? "resonate:delay" with
          | none =>
              simp [hfind, hto, htarget, hdelay, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
              repeat first | rfl | split
          | some dstr =>
              by_cases hd : dstr.toNat! > now
              · simp [hfind, hto, htarget, hdelay, hd, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
                repeat first | rfl | split
              · simp [hfind, hto, htarget, hdelay, hd, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
                repeat first | rfl | split
    · simp [hfind, hto, setPromise, setPromiseTimeout, setTask, setTaskTimeout, setMessage]
      repeat first | rfl | split
  · obtain ⟨p, hfind⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == req.id)) |>.resolve_left hfind
    simp [hfind]

theorem frozen_promiseCreate (req : PromiseCreateReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.promiseCreate req) now s).2 id now = some st := by
  have hstep : (stepOf (.promiseCreate req) now s).2 = ((promiseCreate req now : M PromiseCreateRes) s).2 := rfl
  rw [hstep]
  unfold logical at hl ⊢
  cases hfind : s.promises.find? (·.id == id) with
  | none => rw [hfind] at hl; simp at hl
  | some p =>
      rw [hfind] at hl
      rw [promiseCreate_find?_mono req now s hfind]
      exact hl

theorem sound_promiseCreate (req : PromiseCreateReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.promiseCreate req) now s).1 id st) :
    logical (stepOf (.promiseCreate req) now s).2 id now = some st := by
  have hres : (stepOf (.promiseCreate req) now s).1 = Response.promiseCreate ((promiseCreate req now : M PromiseCreateRes) s).1 := rfl
  have hst2 : (stepOf (.promiseCreate req) now s).2 = ((promiseCreate req now : M PromiseCreateRes) s).2 := rfl
  rw [hres, promiseCreate_res_eq] at hx
  rw [hst2]
  have hprom := promiseCreate_promises_eq req now s
  cases hfind : s.promises.find? (·.id == req.id) with
  | some p =>
      rw [hfind] at hprom
      simp only [hfind] at hx
      simp [Externalized, Response.promises] at hx
      obtain ⟨hid, hst⟩ := hx
      have hpid : p.id = req.id := by
        have := List.find?_some hfind; simpa using this
      have hpid2 : p.id = id := by
        rw [← hid]; simp [PromiseObject.toRecord, project_id]
      unfold logical
      rw [hprom, ← hpid2, hpid, hfind]
      simp only [Option.map_some, Option.some.injEq]
      rw [← hst]
      rfl
  | none =>
      rw [hfind] at hprom
      simp only [hfind] at hx
      by_cases hto : now < req.timeoutAt
      · simp only [hto, if_true] at hx hprom
        simp [Externalized, Response.promises] at hx
        obtain ⟨hid, hst⟩ := hx
        unfold logical
        rw [hprom]
        have hhead : ((({ id := req.id, state := .pending, param := req.param, tags := req.tags, timeoutAt := req.timeoutAt, createdAt := now } : PromiseObject)).id == id) = true := by
          simp [← hid, PromiseObject.toRecord]
        simp only [List.find?_cons, hhead, cond_true, Option.map_some, Option.some.injEq]
        rw [project_of_live _ now (by simpa using hto)]
        rw [← hst]
        rfl
      · simp only [hto, if_false] at hx hprom
        simp [Externalized, Response.promises] at hx
        obtain ⟨hid, hst⟩ := hx
        unfold logical
        rw [hprom]
        have hhead : ((({ id := req.id, state := (if req.tags.isTimer then .resolved else .rejectedTimedout), param := req.param, tags := req.tags, timeoutAt := req.timeoutAt, createdAt := req.timeoutAt, settledAt := some req.timeoutAt } : PromiseObject)).id == id) = true := by
          simp [← hid, PromiseObject.toRecord]
        simp only [List.find?_cons, hhead, cond_true, Option.map_some, Option.some.injEq]
        have hsettled : (({ id := req.id, state := (if req.tags.isTimer then .resolved else .rejectedTimedout), param := req.param, tags := req.tags, timeoutAt := req.timeoutAt, createdAt := req.timeoutAt, settledAt := some req.timeoutAt } : PromiseObject).project now).state
            = (if req.tags.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout) := by
          by_cases htimer : req.tags.isTimer
          · simp [htimer, PromiseObject.project, PromiseObject.isTimer]
          · simp [htimer, PromiseObject.project, PromiseObject.isTimer]
        rw [hsettled, ← hst]
        rfl

theorem foldlM_inv {α β : Type} (Inv : ServerState → Prop) (f : β → α → M β)
    (hf : ∀ b a σ, Inv σ → Inv ((f b a) σ).2) :
    ∀ (l : List α) (b : β) (σ : ServerState), Inv σ → Inv ((List.foldlM f b l : M β) σ).2 := by
  intro l
  induction l with
  | nil => intro b σ h; exact h
  | cons x xs ih =>
      intro b σ h
      rw [List.foldlM_cons]
      simp only [run_bind]
      exact ih _ _ (hf b x σ h)

theorem foldlM_setMessage_promises (rec : PromiseRecord) (L : List String) (σ : ServerState) :
    ((List.foldlM (fun (_ : PUnit) a => setMessage a (Message.unblock rec)) PUnit.unit L : M PUnit) σ).2.promises = σ.promises :=
  foldlM_inv (fun σ' => σ'.promises = σ.promises) _
    (fun b a σ' h => by simpa [setMessage] using h) L PUnit.unit σ rfl

theorem foldlM_defer_promises (pid : String) (L : List String) (σ : ServerState) :
    ((List.foldlM (fun (_ : PUnit) a => defer { awaited := pid, awaiter := a }) PUnit.unit L : M PUnit) σ).2.promises = σ.promises :=
  foldlM_inv (fun σ' => σ'.promises = σ.promises) _
    (fun b a σ' h => by simpa [defer] using h) L PUnit.unit σ rfl

theorem promiseSettle_promises_eq (req : PromiseSettleReq) (now : Nat) (s : ServerState) :
    (promiseSettle req now s).2.promises =
      (if ¬req.state.settable then s.promises
       else match s.promises.find? (·.id == req.id) with
       | none => s.promises
       | some p =>
         if p.state = PromiseState.pending ∧ now < p.timeoutAt then
           ({ p with state := req.state, value := req.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject) :: s.promises.filter (·.id != p.id)
         else s.promises) := by
  unfold promiseSettle getPromise getTask
  by_cases hset : req.state.settable
  · by_cases hfind : s.promises.find? (·.id == req.id) = none
    · simp [hset, hfind]
    · obtain ⟨p, hfind⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == req.id)) |>.resolve_left hfind
      by_cases hlive : (p.state = PromiseState.pending ∧ now < p.timeoutAt)
      · by_cases htask : s.tasks.find? (·.id == p.id) = none
        · simp [hset, hfind, hlive, htask, setPromise, delPromiseTimeout]
          rw [foldlM_defer_promises, foldlM_setMessage_promises]
        · obtain ⟨t, htask⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == p.id)) |>.resolve_left htask
          simp [hset, hfind, hlive, htask, setPromise, delPromiseTimeout, setTask, delTaskTimeout]
          rw [foldlM_defer_promises, foldlM_setMessage_promises]
      · simp [hset, hfind, hlive]
  · simp [hset]

theorem promiseSettle_res_eq (req : PromiseSettleReq) (now : Nat) (s : ServerState) :
    (promiseSettle req now s).1 =
      (if ¬req.state.settable then { status := 400 }
       else match s.promises.find? (·.id == req.id) with
       | none => { status := 404 }
       | some p =>
         if p.state = PromiseState.pending ∧ now < p.timeoutAt then
           { status := 200, promise := some ({ p with state := req.state, value := req.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject).toRecord }
         else { status := 200, promise := some ((p.project now).toRecord) }) := by
  unfold promiseSettle getPromise getTask
  by_cases hset : req.state.settable
  · by_cases hfind : s.promises.find? (·.id == req.id) = none
    · simp [hset, hfind]
    · obtain ⟨p, hfind⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == req.id)) |>.resolve_left hfind
      by_cases hlive : (p.state = PromiseState.pending ∧ now < p.timeoutAt)
      · by_cases htask : s.tasks.find? (·.id == p.id) = none
        · simp [hset, hfind, hlive, htask, setPromise, delPromiseTimeout]
        · obtain ⟨t, htask⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == p.id)) |>.resolve_left htask
          simp [hset, hfind, hlive, htask, setPromise, delPromiseTimeout, setTask, delTaskTimeout]
      · simp [hset, hfind, hlive]
  · simp [hset]

theorem frozen_promiseSettle (req : PromiseSettleReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.promiseSettle req) now s).2 id now = some st := by
  have hstep : (stepOf (.promiseSettle req) now s).2 = ((promiseSettle req now : M PromiseSettleRes) s).2 := rfl
  rw [hstep]
  have hp := promiseSettle_promises_eq req now s
  unfold logical at hl ⊢
  rw [hp]
  by_cases hsettable : ¬req.state.settable
  · simp only [hsettable, if_true]; exact hl
  · simp only [hsettable, if_false]
    cases hfind : s.promises.find? (·.id == req.id) with
    | none => exact hl
    | some p =>
        by_cases hlive : (p.state = PromiseState.pending ∧ now < p.timeoutAt)
        · simp only [hlive, and_self, if_true]
          by_cases hid : id = p.id
          · subst hid
            have hpa : s.promises.find? (·.id == p.id) = some p := by
              have hpid : p.id = req.id := by
                have := List.find?_some hfind; simpa using this
              rw [hpid]; exact hfind
            rw [hpa] at hl
            simp only [Option.map_some, Option.some.injEq] at hl
            rw [project_of_live p now hlive.2] at hl
            rw [hlive.1] at hl
            exact absurd hl.symm hset
          · have hhead : ((({ p with state := req.state, value := req.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject)).id == id) = false := by
              simp only [PromiseObject.toRecord]
              exact beq_eq_false_iff_ne.mpr (fun he => hid (he.symm))
            simp only [List.find?_cons, hhead, cond_false]
            rw [find?_filter_ne (fun he => hid he)]
            exact hl
        · simp only [hlive, and_self, if_false]; exact hl

theorem sound_promiseSettle (req : PromiseSettleReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.promiseSettle req) now s).1 id st) :
    logical (stepOf (.promiseSettle req) now s).2 id now = some st := by
  have hres : (stepOf (.promiseSettle req) now s).1 = Response.promiseSettle ((promiseSettle req now : M PromiseSettleRes) s).1 := rfl
  have hst2 : (stepOf (.promiseSettle req) now s).2 = ((promiseSettle req now : M PromiseSettleRes) s).2 := rfl
  rw [hres, promiseSettle_res_eq] at hx
  rw [hst2]
  have hprom := promiseSettle_promises_eq req now s
  unfold logical
  rw [hprom]
  by_cases hsettable : ¬req.state.settable
  · simp only [hsettable, if_true] at hx ⊢
    simp [Externalized, Response.promises] at hx
  · simp only [hsettable, if_false] at hx ⊢
    cases hfind : s.promises.find? (·.id == req.id) with
    | none => simp only [hfind] at hx; simp [Externalized, Response.promises] at hx
    | some p =>
        simp only [hfind] at hx ⊢
        have hpa : s.promises.find? (·.id == p.id) = some p := by
          have hpid : p.id = req.id := by
            have := List.find?_some hfind; simpa using this
          rw [hpid]; exact hfind
        by_cases hlive : (p.state = PromiseState.pending ∧ now < p.timeoutAt)
        · simp only [hlive, and_self, if_true] at hx ⊢
          simp [Externalized, Response.promises] at hx
          obtain ⟨hid, hst⟩ := hx
          have hhead : ((({ p with state := req.state, value := req.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject)).id == id) = true := by
            simp only [PromiseObject.toRecord] at hid
            simp [← hid]
          simp only [List.find?_cons, hhead, cond_true, Option.map_some, Option.some.injEq]
          have hsettled : (({ p with state := req.state, value := req.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject).project now).state = req.state := by
            unfold PromiseObject.project
            rw [if_neg]
            intro ⟨hpend, _⟩
            have hreq : req.state = PromiseState.pending := by simpa using hpend
            rw [hreq] at hsettable
            simp [PromiseState.settable] at hsettable
          rw [hsettled]
          simp only [PromiseObject.toRecord] at hst
          exact hst
        · simp only [hlive, and_self, if_false] at hx ⊢
          simp [Externalized, Response.promises] at hx
          obtain ⟨hid, hst⟩ := hx
          have hpid2 : p.id = id := by
            rw [← hid]; simp [PromiseObject.toRecord, project_id]
          rw [← hpid2, hpa]
          simp only [Option.map_some, Option.some.injEq]
          rw [← hst]
          rfl

theorem stepOf_taskFence (r : TaskFenceReq) (now : Nat) (s : ServerState) :
    stepOf (.taskFence r) now s =
      (if r.action.targetId == r.id then (Response.taskFence { status := 400 }, s)
       else match s.tasks.find? (·.id == r.id) with
       | none => (Response.taskFence { status := 404 }, s)
       | some t =>
         match s.promises.find? (·.id == t.id) with
         | none => (Response.taskFence { status := 409 }, s)
         | some p =>
           if t.state ≠ TaskState.acquired then (Response.taskFence { status := 409 }, s)
           else if p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now then (Response.taskFence { status := 409 }, s)
           else if t.version ≠ r.version then (Response.taskFence { status := 409 }, s)
           else match r.action with
           | .create r2 =>
               (Response.taskFence { status := 200, action := some (.create ((promiseCreate r2 now : M PromiseCreateRes) s).1) },
                ((promiseCreate r2 now : M PromiseCreateRes) s).2)
           | .settle r2 =>
               (Response.taskFence { status := 200, action := some (.settle ((promiseSettle r2 now : M PromiseSettleRes) s).1) },
                ((promiseSettle r2 now : M PromiseSettleRes) s).2)) := by
  rw [run_stepOf]
  simp only [handle, run_bind, run_get, run_pure, run_map]
  unfold taskFence getTask getPromise
  by_cases h0 : r.action.targetId == r.id
  · simp [h0]
  · simp only [h0]
    by_cases h1 : s.tasks.find? (·.id == r.id) = none
    · simp [h0, h1]
    · obtain ⟨t, h1⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == r.id)) |>.resolve_left h1
      simp [h0, h1]
      by_cases h2 : s.promises.find? (·.id == t.id) = none
      · simp [h2]
      · obtain ⟨p, h2⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == t.id)) |>.resolve_left h2
        simp [h2]
        by_cases h3 : t.state = TaskState.acquired
        · by_cases h4 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
          · simp [h3, h4]
          · by_cases h5 : t.version = r.version
            · cases r.action with
              | create r2 => simp [h3, h4, h5]
              | settle r2 => simp [h3, h4, h5]
            · simp [h3, h4, h5]
        · simp [h3]

theorem frozen_taskFence (r : TaskFenceReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.taskFence r) now s).2 id now = some st := by
  rw [stepOf_taskFence]
  repeat first
    | exact hl
    | split
  · exact frozen_promiseCreate _ now s id st hset hl
  · exact frozen_promiseSettle _ now s id st hset hl

theorem sound_taskFence (r : TaskFenceReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskFence r) now s).1 id st) :
    logical (stepOf (.taskFence r) now s).2 id now = some st := by
  rw [stepOf_taskFence] at hx ⊢
  by_cases h0 : r.action.targetId == r.id
  · simp only [h0, if_true] at hx; simp [Externalized, Response.promises] at hx
  · simp only [h0, Bool.false_eq_true, if_false] at hx ⊢
    cases hf : s.tasks.find? (·.id == r.id) with
    | none => simp [hf, Externalized, Response.promises] at hx
    | some t =>
        simp only [hf] at hx ⊢
        cases hf2 : s.promises.find? (·.id == t.id) with
        | none => simp [hf2, Externalized, Response.promises] at hx
        | some p =>
            simp only [hf2] at hx ⊢
            by_cases h3 : t.state ≠ TaskState.acquired
            · simp [h3, Externalized, Response.promises] at hx
            · simp only [h3, if_false] at hx ⊢
              by_cases h4 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
              · simp only [h4, if_true] at hx; simp [Externalized, Response.promises] at hx
              · simp only [h4, if_false] at hx ⊢
                by_cases h5 : t.version ≠ r.version
                · simp [h5, Externalized, Response.promises] at hx
                · simp only [h5, if_false] at hx ⊢
                  cases hact : r.action with
                  | create r2 =>
                      simp only [hact] at hx
                      simp [Externalized, Response.promises] at hx
                      have hx' : Externalized (stepOf (.promiseCreate r2) now s).1 id st := by
                        have hbr : (stepOf (.promiseCreate r2) now s).1 = Response.promiseCreate ((promiseCreate r2 now : M PromiseCreateRes) s).1 := rfl
                        rw [hbr]
                        simp only [Externalized, Response.promises]
                        obtain ⟨q, hq, hid', hst'⟩ := hx
                        exact ⟨q, by simp [hq], hid', hst'⟩
                      exact sound_promiseCreate r2 now s id st hx'
                  | settle r2 =>
                      simp only [hact] at hx
                      simp [Externalized, Response.promises] at hx
                      have hx' : Externalized (stepOf (.promiseSettle r2) now s).1 id st := by
                        have hbr : (stepOf (.promiseSettle r2) now s).1 = Response.promiseSettle ((promiseSettle r2 now : M PromiseSettleRes) s).1 := rfl
                        rw [hbr]
                        simp only [Externalized, Response.promises]
                        obtain ⟨q, hq, hid', hst'⟩ := hx
                        exact ⟨q, by simp [hq], hid', hst'⟩
                      exact sound_promiseSettle r2 now s id st hx'

theorem taskFulfill_promises_eq (r : TaskFulfillReq) (now : Nat) (s : ServerState) :
    (taskFulfill r now s).2.promises =
      (if ¬r.action.state.settable then s.promises
       else match s.tasks.find? (·.id == r.id) with
       | none => s.promises
       | some t =>
         match s.promises.find? (·.id == t.id) with
         | none => s.promises
         | some p =>
           if t.state ≠ TaskState.acquired then s.promises
           else if p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now then s.promises
           else if t.version ≠ r.version then s.promises
           else ({ p with state := r.action.state, value := r.action.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject) :: s.promises.filter (·.id != p.id)) := by
  unfold taskFulfill getTask getPromise
  by_cases hset : r.action.state.settable
  · by_cases h1 : s.tasks.find? (·.id == r.id) = none
    · simp [hset, h1]
    · obtain ⟨t, h1⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == r.id)) |>.resolve_left h1
      by_cases h2 : s.promises.find? (·.id == t.id) = none
      · simp [hset, h1, h2]
      · obtain ⟨p, h2⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == t.id)) |>.resolve_left h2
        by_cases h3 : t.state = TaskState.acquired
        · by_cases h4 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
          · simp [hset, h1, h2, h3, h4]
          · by_cases h5 : t.version = r.version
            · simp [hset, h1, h2, h3, h4, h5, setPromise, delPromiseTimeout, setTask, delTaskTimeout]
              rw [foldlM_defer_promises, foldlM_setMessage_promises]
            · simp [hset, h1, h2, h3, h4, h5]
        · simp [hset, h1, h2, h3]
  · simp [hset]

theorem taskFulfill_res_eq (r : TaskFulfillReq) (now : Nat) (s : ServerState) :
    (taskFulfill r now s).1 =
      (if ¬r.action.state.settable then { status := 400 }
       else match s.tasks.find? (·.id == r.id) with
       | none => { status := 404 }
       | some t =>
         match s.promises.find? (·.id == t.id) with
         | none => { status := 409 }
         | some p =>
           if t.state ≠ TaskState.acquired then { status := 409 }
           else if p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now then { status := 409 }
           else if t.version ≠ r.version then { status := 409 }
           else { status := 200, promise := some ({ p with state := r.action.state, value := r.action.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject).toRecord }) := by
  unfold taskFulfill getTask getPromise
  by_cases hset : r.action.state.settable
  · by_cases h1 : s.tasks.find? (·.id == r.id) = none
    · simp [hset, h1]
    · obtain ⟨t, h1⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == r.id)) |>.resolve_left h1
      by_cases h2 : s.promises.find? (·.id == t.id) = none
      · simp [hset, h1, h2]
      · obtain ⟨p, h2⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == t.id)) |>.resolve_left h2
        by_cases h3 : t.state = TaskState.acquired
        · by_cases h4 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
          · simp [hset, h1, h2, h3, h4]
          · by_cases h5 : t.version = r.version
            · simp [hset, h1, h2, h3, h4, h5, setPromise, delPromiseTimeout, setTask, delTaskTimeout]
            · simp [hset, h1, h2, h3, h4, h5]
        · simp [hset, h1, h2, h3]
  · simp [hset]

theorem frozen_taskFulfill (r : TaskFulfillReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.taskFulfill r) now s).2 id now = some st := by
  have hstep : (stepOf (.taskFulfill r) now s).2 = ((taskFulfill r now : M TaskFulfillRes) s).2 := rfl
  rw [hstep]
  have hp := taskFulfill_promises_eq r now s
  unfold logical at hl ⊢
  rw [hp]
  by_cases hsettable : ¬r.action.state.settable
  · simpa [hsettable] using hl
  · simp only [hsettable, if_false]
    cases h1 : s.tasks.find? (·.id == r.id) with
    | none => exact hl
    | some t =>
        dsimp only
        cases h2 : s.promises.find? (·.id == t.id) with
        | none => exact hl
        | some p =>
            dsimp only
            by_cases h3 : t.state ≠ TaskState.acquired
            · simpa [h3] using hl
            · simp only [h3, if_false]
              by_cases h4 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
              · simpa [h4] using hl
              · simp only [h4, if_false]
                by_cases h5 : t.version ≠ r.version
                · simpa [h5] using hl
                · simp only [h5, if_false]
                  by_cases hid : id = p.id
                  · subst hid
                    have hp1 : p.state = PromiseState.pending := by
                      by_cases h' : p.state = PromiseState.pending
                      · exact h'
                      · exact absurd (Or.inl h') h4
                    have hp2 : now < p.timeoutAt := Nat.not_le.mp (fun hle => h4 (Or.inr hle))
                    have hpa : s.promises.find? (·.id == p.id) = some p := by
                      have hpid : p.id = t.id := by
                        have := List.find?_some h2; simpa using this
                      rw [hpid]; exact h2
                    rw [hpa] at hl
                    simp only [Option.map_some, Option.some.injEq] at hl
                    rw [project_of_live p now hp2, hp1] at hl
                    exact absurd hl.symm hset
                  · have hhead : ((({ p with state := r.action.state, value := r.action.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject)).id == id) = false := by
                      exact beq_eq_false_iff_ne.mpr (fun he => hid (he.symm))
                    simp only [List.find?_cons, hhead, cond_false]
                    rw [find?_filter_ne (fun he => hid he)]
                    exact hl

theorem sound_taskFulfill (r : TaskFulfillReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskFulfill r) now s).1 id st) :
    logical (stepOf (.taskFulfill r) now s).2 id now = some st := by
  have hres : (stepOf (.taskFulfill r) now s).1 = Response.taskFulfill ((taskFulfill r now : M TaskFulfillRes) s).1 := rfl
  have hst2 : (stepOf (.taskFulfill r) now s).2 = ((taskFulfill r now : M TaskFulfillRes) s).2 := rfl
  rw [hres, taskFulfill_res_eq] at hx
  rw [hst2]
  have hprom := taskFulfill_promises_eq r now s
  unfold logical
  rw [hprom]
  by_cases hsettable : ¬r.action.state.settable
  · simp only [hsettable, if_true] at hx ⊢
    simp [Externalized, Response.promises] at hx
  · simp only [hsettable, if_false] at hx ⊢
    cases h1 : s.tasks.find? (·.id == r.id) with
    | none => simp [h1, Externalized, Response.promises] at hx
    | some t =>
        simp only [h1] at hx ⊢
        cases h2 : s.promises.find? (·.id == t.id) with
        | none => simp [h2, Externalized, Response.promises] at hx
        | some p =>
            simp only [h2] at hx ⊢
            by_cases h3 : t.state ≠ TaskState.acquired
            · simp [h3, Externalized, Response.promises] at hx
            · simp only [h3, if_false] at hx ⊢
              by_cases h4 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
              · simp [h4, Externalized, Response.promises] at hx
              · simp only [h4, if_false] at hx ⊢
                by_cases h5 : t.version ≠ r.version
                · simp [h5, Externalized, Response.promises] at hx
                · simp only [h5, if_false] at hx ⊢
                  simp [Externalized, Response.promises] at hx
                  obtain ⟨hid, hst⟩ := hx
                  have hhead : ((({ p with state := r.action.state, value := r.action.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject)).id == id) = true := by
                    simp only [PromiseObject.toRecord] at hid
                    simp [← hid]
                  simp only [List.find?_cons, hhead, cond_true, Option.map_some, Option.some.injEq]
                  have hsettled : (({ p with state := r.action.state, value := r.action.value, settledAt := some now, callbacks := [], listeners := [] } : PromiseObject).project now).state = r.action.state := by
                    unfold PromiseObject.project
                    rw [if_neg]
                    intro ⟨hpend, _⟩
                    have hreq : r.action.state = PromiseState.pending := by simpa using hpend
                    rw [hreq] at hsettable
                    simp [PromiseState.settable] at hsettable
                  rw [hsettled]
                  simp only [PromiseObject.toRecord] at hst
                  exact hst

theorem onPromiseTimeout_promises_eq (pid : String) (now : Nat) (s : ServerState) :
    (Timeouts.onPromiseTimeout pid now s).2.promises =
      (match s.promises.find? (·.id == pid) with
       | none => s.promises
       | some p =>
         if p.state ≠ PromiseState.pending then s.promises
         else ({ p.project p.timeoutAt with callbacks := [], listeners := [] } : PromiseObject) :: s.promises.filter (·.id != p.id)) := by
  unfold Timeouts.onPromiseTimeout getPromise getTask
  by_cases hfind : s.promises.find? (·.id == pid) = none
  · simp [hfind]
  · obtain ⟨p, hfind⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == pid)) |>.resolve_left hfind
    by_cases hpend : p.state = PromiseState.pending
    · by_cases htask : s.tasks.find? (·.id == p.id) = none
      · simp [hfind, hpend, htask, setPromise, delPromiseTimeout, project_id]
        rw [foldlM_defer_promises, foldlM_setMessage_promises]
      · obtain ⟨t, htask⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == p.id)) |>.resolve_left htask
        simp [hfind, hpend, htask, setPromise, delPromiseTimeout, setTask, delTaskTimeout, project_id]
        rw [foldlM_defer_promises, foldlM_setMessage_promises]
    · simp [hfind, hpend]

theorem frozen_τPromiseTimeout (pid : String) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hset : Settled st) (hl : logical s id now = some st) :
    logical (stepOf (.τPromiseTimeout pid) now s).2 id now = some st := by
  rw [run_stepOf]
  simp only [handle, run_bind, run_get, run_pure, run_map]
  by_cases hen : (s.promiseTimeouts.any (fun e => e.id == pid && decide (e.timeout ≤ now)))
  · simp only [hen, if_true]
    show logical ((Timeouts.onPromiseTimeout pid now : M Unit) s).2 id now = some st
    have hp := onPromiseTimeout_promises_eq pid now s
    unfold logical at hl ⊢
    rw [hp]
    cases hfind : s.promises.find? (·.id == pid) with
    | none => exact hl
    | some p =>
        dsimp only
        by_cases hpend : p.state ≠ PromiseState.pending
        · simpa [hpend] using hl
        · simp only [hpend, if_false]
          by_cases hid : id = p.id
          · subst hid
            have hpa : s.promises.find? (·.id == p.id) = some p := by
              have hpid : p.id = pid := by
                have := List.find?_some hfind; simpa using this
              rw [hpid]; exact hfind
            rw [hpa] at hl
            simp only [Option.map_some, Option.some.injEq] at hl
            have hpend' : p.state = PromiseState.pending := by
              by_cases h' : p.state = PromiseState.pending
              · exact h'
              · exact absurd h' (by simpa using hpend)
            by_cases hlate : p.timeoutAt ≤ now
            · have hhead : ((({ p.project p.timeoutAt with callbacks := [], listeners := [] } : PromiseObject)).id == p.id) = true := by
                simp [project_id]
              simp only [List.find?_cons, hhead, cond_true, Option.map_some, Option.some.injEq]
              have hstamp : (p.project now).state = (if p.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout) := by
                unfold PromiseObject.project
                rw [if_pos ⟨by simp [hpend'], hlate⟩]
                split <;> rfl
              have hbase : (p.project p.timeoutAt).state = (if p.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout) := by
                unfold PromiseObject.project
                rw [if_pos ⟨by simp [hpend'], Nat.le_refl _⟩]
                split <;> rfl
              have hq : ∀ P' : PromiseObject,
                  P'.state = (if p.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout) →
                  ((({ P' with callbacks := [], listeners := [] } : PromiseObject)).project now).state
                    = (if p.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout) := by
                intro P' hP'
                unfold PromiseObject.project
                rw [if_neg]
                · exact hP'
                · intro ⟨hc, _⟩
                  rw [show (({ P' with callbacks := [], listeners := [] } : PromiseObject)).state = P'.state from rfl, hP'] at hc
                  revert hc
                  split <;> simp
              have hstamp' := hq (p.project p.timeoutAt) hbase
              rw [hstamp'] at *
              rw [hstamp] at hl
              exact hl
            · rw [project_of_live p now (Nat.not_le.mp hlate)] at hl
              rw [hpend'] at hl
              exact absurd hl.symm hset
          · have hhead : ((({ p.project p.timeoutAt with callbacks := [], listeners := [] } : PromiseObject)).id == id) = false := by
              simp only [project_id]
              exact beq_eq_false_iff_ne.mpr (fun he => hid (he.symm))
            simp only [List.find?_cons, hhead, cond_false]
            rw [find?_filter_ne (fun he => hid he)]
            exact hl
  · simp only [hen, Bool.false_eq_true, if_false]
    exact hl

theorem sound_τPromiseTimeout (pid : String) (now : Nat) (s : ServerState) (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.τPromiseTimeout pid) now s).1 id st) :
    logical (stepOf (.τPromiseTimeout pid) now s).2 id now = some st := by
  have hres : Response.promises (stepOf (.τPromiseTimeout pid) now s).1 = [] := by
    rw [run_stepOf]
    simp only [handle, run_bind, run_get, run_pure, run_map]
    by_cases h : (s.promiseTimeouts.any (fun e => e.id == pid && decide (e.timeout ≤ now)))
    · simp [h, Response.promises]
    · simp [h, Response.promises]
  rw [run_stepOf] at hres
  simp [Externalized, hres] at hx

theorem taskCreate_promises_eq (r : TaskCreateReq) (now : Nat) (s : ServerState) :
    (taskCreate r now s).2.promises =
      (if ¬(r.action.tags.has "resonate:target") then s.promises
       else match s.promises.find? (·.id == r.action.id) with
       | some _ => s.promises
       | none =>
         (if now < r.action.timeoutAt then
            ({ id := r.action.id, state := .pending, param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := now } : PromiseObject)
          else
            ({ id := r.action.id, state := (if r.action.tags.isTimer then .resolved else .rejectedTimedout), param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := r.action.timeoutAt, settledAt := some r.action.timeoutAt } : PromiseObject))
           :: s.promises.filter (·.id != r.action.id)) := by
  unfold taskCreate getPromise getTask
  by_cases htag : r.action.tags.has "resonate:target"
  · by_cases hfind : s.promises.find? (·.id == r.action.id) = none
    · by_cases hto : now < r.action.timeoutAt
      · simp [htag, hfind, hto, setPromise, setPromiseTimeout, setTask, setTaskTimeout]
      · simp [htag, hfind, hto, setPromise, setTask]
    · obtain ⟨p, hfind⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == r.action.id)) |>.resolve_left hfind
      by_cases hptag : p.tags.has "resonate:target"
      · by_cases htask : s.tasks.find? (·.id == p.id) = none
        · simp [htag, hfind, hptag, htask]
        · obtain ⟨t, htask⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == p.id)) |>.resolve_left htask
          by_cases hful : t.state = TaskState.fulfilled
          · simp [htag, hfind, hptag, htask, hful]
          · by_cases hpen : t.state = TaskState.pending
            · simp [htag, hfind, hptag, htask, hful, hpen, setTask, delTaskTimeout, setTaskTimeout]
            · simp [htag, hfind, hptag, htask, hful, hpen]
      · simp [htag, hfind, hptag]
  · simp [htag]

theorem taskCreate_res_eq (r : TaskCreateReq) (now : Nat) (s : ServerState) :
    (taskCreate r now s).1 =
      (if ¬(r.action.tags.has "resonate:target") then { status := 400 }
       else match s.promises.find? (·.id == r.action.id) with
       | none =>
         if now < r.action.timeoutAt then
           { status := 200,
             task := some ({ id := r.action.id, state := .acquired, version := 1, ttl := some r.ttl, pid := some r.pid, resumes := [] } : TaskObject).toRecord,
             promise := some ({ id := r.action.id, state := .pending, param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := now } : PromiseObject).toRecord }
         else
           { status := 200,
             task := some ({ id := r.action.id, state := .fulfilled, version := 0, ttl := none, pid := none, resumes := [] } : TaskObject).toRecord,
             promise := some ({ id := r.action.id, state := (if r.action.tags.isTimer then .resolved else .rejectedTimedout), param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := r.action.timeoutAt, settledAt := some r.action.timeoutAt } : PromiseObject).toRecord }
       | some p =>
         if ¬(p.tags.has "resonate:target") then { status := 422 }
         else match s.tasks.find? (·.id == p.id) with
         | none => { status := 409 }
         | some t =>
           if t.state = TaskState.fulfilled then
             { status := 200, task := some t.toRecord, promise := some ((p.project now).toRecord) }
           else if t.state = TaskState.pending then
             { status := 200,
               task := some ({ t with state := .acquired, version := t.version + 1, ttl := some r.ttl, pid := some r.pid, resumes := [] } : TaskObject).toRecord,
               promise := some ((p.project now).toRecord) }
           else { status := 409 }) := by
  unfold taskCreate getPromise getTask
  by_cases htag : r.action.tags.has "resonate:target"
  · by_cases hfind : s.promises.find? (·.id == r.action.id) = none
    · by_cases hto : now < r.action.timeoutAt
      · simp [htag, hfind, hto, setPromise, setPromiseTimeout, setTask, setTaskTimeout]
      · simp [htag, hfind, hto, setPromise, setTask]
    · obtain ⟨p, hfind⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == r.action.id)) |>.resolve_left hfind
      by_cases hptag : p.tags.has "resonate:target"
      · by_cases htask : s.tasks.find? (·.id == p.id) = none
        · simp [htag, hfind, hptag, htask]
        · obtain ⟨t, htask⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == p.id)) |>.resolve_left htask
          by_cases hful : t.state = TaskState.fulfilled
          · simp [htag, hfind, hptag, htask, hful]
          · by_cases hpen : t.state = TaskState.pending
            · simp [htag, hfind, hptag, htask, hful, hpen, setTask, delTaskTimeout, setTaskTimeout]
            · simp [htag, hfind, hptag, htask, hful, hpen]
      · simp [htag, hfind, hptag]
  · simp [htag]

theorem frozen_taskCreate (r : TaskCreateReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState) (_hset : Settled st)
    (hl : logical s id now = some st) :
    logical (stepOf (.taskCreate r) now s).2 id now = some st := by
  have hstep : (stepOf (.taskCreate r) now s).2 = ((taskCreate r now : M TaskCreateRes) s).2 := rfl
  rw [hstep]
  have hp := taskCreate_promises_eq r now s
  unfold logical at hl ⊢
  rw [hp]
  by_cases htag : ¬(r.action.tags.has "resonate:target")
  · simpa [htag] using hl
  · simp only [htag, if_false]
    cases hfind : s.promises.find? (·.id == r.action.id) with
    | some p => exact hl
    | none =>
        dsimp only
        have hne : r.action.id ≠ id := by
          intro he
          rw [← he, hfind] at hl
          simp at hl
        by_cases hto : now < r.action.timeoutAt
        · simp only [hto, if_true]
          have hhead : ((({ id := r.action.id, state := .pending, param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := now } : PromiseObject)).id == id) = false :=
            beq_eq_false_iff_ne.mpr hne
          simp only [List.find?_cons, hhead, cond_false]
          rw [find?_filter_ne (Ne.symm hne)]
          exact hl
        · simp only [hto, if_false]
          have hhead : ((({ id := r.action.id, state := (if r.action.tags.isTimer then .resolved else .rejectedTimedout), param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := r.action.timeoutAt, settledAt := some r.action.timeoutAt } : PromiseObject)).id == id) = false :=
            beq_eq_false_iff_ne.mpr hne
          simp only [List.find?_cons, hhead, cond_false]
          rw [find?_filter_ne (Ne.symm hne)]
          exact hl

theorem sound_taskCreate (r : TaskCreateReq) (now : Nat) (s : ServerState)
    (id : String) (st : PromiseState)
    (hx : Externalized (stepOf (.taskCreate r) now s).1 id st) :
    logical (stepOf (.taskCreate r) now s).2 id now = some st := by
  have hres : (stepOf (.taskCreate r) now s).1 = Response.taskCreate ((taskCreate r now : M TaskCreateRes) s).1 := rfl
  have hst2 : (stepOf (.taskCreate r) now s).2 = ((taskCreate r now : M TaskCreateRes) s).2 := rfl
  rw [hres, taskCreate_res_eq] at hx
  rw [hst2]
  have hprom := taskCreate_promises_eq r now s
  unfold logical
  rw [hprom]
  by_cases htag : ¬(r.action.tags.has "resonate:target")
  · simp only [htag, if_true] at hx ⊢
    simp [Externalized, Response.promises] at hx
  · simp only [htag, if_false] at hx ⊢
    cases hfind : s.promises.find? (·.id == r.action.id) with
    | none =>
        simp only [hfind] at hx ⊢
        by_cases hto : now < r.action.timeoutAt
        · simp only [hto, if_true] at hx ⊢
          simp [Externalized, Response.promises] at hx
          obtain ⟨hid, hst⟩ := hx
          have hhead : ((({ id := r.action.id, state := .pending, param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := now } : PromiseObject)).id == id) = true := by
            simp [← hid, PromiseObject.toRecord]
          simp only [List.find?_cons, hhead, cond_true, Option.map_some, Option.some.injEq]
          rw [project_of_live _ now (by simpa using hto)]
          rw [← hst]
          rfl
        · simp only [hto, if_false] at hx ⊢
          simp [Externalized, Response.promises] at hx
          obtain ⟨hid, hst⟩ := hx
          have hhead : ((({ id := r.action.id, state := (if r.action.tags.isTimer then .resolved else .rejectedTimedout), param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := r.action.timeoutAt, settledAt := some r.action.timeoutAt } : PromiseObject)).id == id) = true := by
            simp [← hid, PromiseObject.toRecord]
          simp only [List.find?_cons, hhead, cond_true, Option.map_some, Option.some.injEq]
          have hsettled : (({ id := r.action.id, state := (if r.action.tags.isTimer then .resolved else .rejectedTimedout), param := r.action.param, tags := r.action.tags, timeoutAt := r.action.timeoutAt, createdAt := r.action.timeoutAt, settledAt := some r.action.timeoutAt } : PromiseObject).project now).state
              = (if r.action.tags.isTimer then PromiseState.resolved else PromiseState.rejectedTimedout) := by
            by_cases htimer : r.action.tags.isTimer
            · simp [htimer, PromiseObject.project, PromiseObject.isTimer]
            · simp [htimer, PromiseObject.project, PromiseObject.isTimer]
          rw [hsettled, ← hst]
          rfl
    | some p =>
        simp only [hfind] at hx ⊢
        have hpa : s.promises.find? (·.id == p.id) = some p := by
          have hpid : p.id = r.action.id := by
            have := List.find?_some hfind; simpa using this
          rw [hpid]; exact hfind
        by_cases hptag : ¬(p.tags.has "resonate:target")
        · simp [hptag, Externalized, Response.promises] at hx
        simp only [hptag, if_false] at hx
        cases htask : s.tasks.find? (·.id == p.id) with
        | none => simp [htask, Externalized, Response.promises] at hx
        | some t =>
            simp only [htask] at hx
            by_cases hful : t.state = TaskState.fulfilled
            · simp only [hful, if_true] at hx
              simp [Externalized, Response.promises] at hx
              obtain ⟨hid, hst⟩ := hx
              have hpid2 : p.id = id := by
                rw [← hid]; simp [PromiseObject.toRecord, project_id]
              rw [← hpid2, hpa]
              simp only [Option.map_some, Option.some.injEq]
              rw [← hst]
              rfl
            · simp only [hful, if_false] at hx
              by_cases hpen : t.state = TaskState.pending
              · simp only [hpen, if_true] at hx
                simp [Externalized, Response.promises] at hx
                obtain ⟨hid, hst⟩ := hx
                have hpid2 : p.id = id := by
                  rw [← hid]; simp [PromiseObject.toRecord, project_id]
                rw [← hpid2, hpa]
                simp only [Option.map_some, Option.some.injEq]
                rw [← hst]
                rfl
              · simp [hpen, Externalized, Response.promises] at hx

theorem stepSound : StepSound := by
  intro rq now s id st hx
  cases rq with
  | promiseGet req => exact sound_promiseGet req now s id st hx
  | promiseCreate req => exact sound_promiseCreate req now s id st hx
  | promiseSettle req => exact sound_promiseSettle req now s id st hx
  | promiseRegisterCallback req => exact sound_promiseRegisterCallback req now s id st hx
  | promiseRegisterListener req => exact sound_promiseRegisterListener req now s id st hx
  | promiseSearch req => simp [stepOf, handle, promiseSearch, Externalized, Response.promises] at hx
  | scheduleGet req => simp [stepOf, handle, scheduleGet, Externalized, Response.promises] at hx
  | scheduleCreate req => simp [stepOf, handle, scheduleCreate, Externalized, Response.promises] at hx
  | scheduleDelete req => simp [stepOf, handle, scheduleDelete, Externalized, Response.promises] at hx
  | scheduleSearch req => simp [stepOf, handle, scheduleSearch, Externalized, Response.promises] at hx
  | taskGet req => simp [stepOf, handle, taskGet, Externalized, Response.promises] at hx
  | taskCreate req => exact sound_taskCreate req now s id st hx
  | taskAcquire req => exact sound_taskAcquire req now s id st hx
  | taskFence req => exact sound_taskFence req now s id st hx
  | taskHeartbeat req => exact sound_taskHeartbeat req now s id st hx
  | taskSuspend req => exact sound_taskSuspend req now s id st hx
  | taskFulfill req => exact sound_taskFulfill req now s id st hx
  | taskRelease req => simp [stepOf, handle, taskRelease, Externalized, Response.promises] at hx
  | taskHalt req => simp [stepOf, handle, taskHalt, Externalized, Response.promises] at hx
  | taskContinue req => simp [stepOf, handle, taskContinue, Externalized, Response.promises] at hx
  | taskSearch req => simp [stepOf, handle, taskSearch, Externalized, Response.promises] at hx
  | τPromiseTimeout tid => exact sound_τPromiseTimeout tid now s id st hx
  | τTaskRetryTimeout tid => exact sound_τTaskRetryTimeout tid now s id st hx
  | τTaskLeaseTimeout tid => exact sound_τTaskLeaseTimeout tid now s id st hx
  | τScheduleTimeout tid => 
      have hres : Response.promises (stepOf (.τScheduleTimeout tid) now s).1 = [] := by
        rw [run_stepOf]
        simp only [handle, run_bind, run_get, run_pure, run_map]
        split <;> simp [Response.promises]
      have h_contra : ¬ Externalized (stepOf (.τScheduleTimeout tid) now s).1 id st := by
        rw [Externalized, hres]
        simp
      exact absurd hx h_contra
  | τResume req => exact sound_τResume req now s id st hx
  | idle => simp [stepOf, handle, Externalized, Response.promises] at hx

theorem stepFrozen : StepFrozen := by
  intro rq now s id st hset hl
  cases rq with
  | promiseGet req => exact frozen_promiseGet req now s id st hset hl
  | promiseCreate req => exact frozen_promiseCreate req now s id st hset hl
  | promiseSettle req => exact frozen_promiseSettle req now s id st hset hl
  | promiseRegisterCallback req => exact frozen_promiseRegisterCallback req now s id st hset hl
  | promiseRegisterListener req => exact frozen_promiseRegisterListener req now s id st hset hl
  | promiseSearch req => unfold stepOf; unfold handle; simpa [promiseSearch, logical] using hl
  | scheduleGet req =>
      have hprom : (stepOf (.scheduleGet req) now s).2.promises = s.promises := by simp only [run_stepOf, handle, scheduleGet, getSchedule, run_bind, run_get, run_pure, run_map]; cases s.schedules.find? (·.id == req.id) <;> rfl
      unfold logical at hl ⊢; rw [hprom]; exact hl
  | scheduleCreate req =>
      have hprom : (stepOf (.scheduleCreate req) now s).2.promises = s.promises := by simp only [run_stepOf, handle, scheduleCreate, getSchedule, setSchedule, setScheduleTimeout, run_bind, run_get, run_pure, run_map]; cases s.schedules.find? (·.id == req.id) <;> rfl
      unfold logical at hl ⊢; rw [hprom]; exact hl
  | scheduleDelete req =>
      have hprom : (stepOf (.scheduleDelete req) now s).2.promises = s.promises := by simp only [run_stepOf, handle, scheduleDelete, getSchedule, delSchedule, delScheduleTimeout, run_bind, run_get, run_pure, run_map]; cases s.schedules.find? (·.id == req.id) <;> rfl
      unfold logical at hl ⊢; rw [hprom]; exact hl
  | scheduleSearch req => unfold stepOf; unfold handle; simpa [scheduleSearch, logical] using hl
  | taskGet req =>
      have hprom : (stepOf (.taskGet req) now s).2.promises = s.promises := by 
        unfold stepOf; unfold handle; simp [taskGet, getTask, getPromise, run_bind, run_get, run_pure, run_map]
        cases h1 : s.tasks.find? (·.id == req.id) <;> simp
        · rename_i t; cases h2 : s.promises.find? (·.id == t.id) <;> simp [h2] <;> try split <;> rfl
      unfold logical at hl ⊢; rw [hprom]; exact hl
  | taskCreate req => exact frozen_taskCreate req now s id st hset hl
  | taskAcquire req => exact frozen_taskAcquire req now s id st hset hl
  | taskFence req => exact frozen_taskFence req now s id st hset hl
  | taskHeartbeat req => exact frozen_taskHeartbeat req now s id st hset hl
  | taskSuspend req => exact frozen_taskSuspend req now s id st hset hl
  | taskFulfill req => exact frozen_taskFulfill req now s id st hset hl
  | taskRelease req =>
      have hrel : (taskRelease req now s).2.promises = s.promises := by
        unfold taskRelease getTask getPromise
        by_cases h1 : s.tasks.find? (·.id == req.id) = none
        · simp [h1]
        · obtain ⟨t, h1⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == req.id)) |>.resolve_left h1
          by_cases h2 : s.promises.find? (·.id == t.id) = none
          · simp [h1, h2]
          · obtain ⟨p, h2⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == t.id)) |>.resolve_left h2
            by_cases h3 : t.state = TaskState.acquired
            · by_cases h4 : (p.state ≠ PromiseState.pending ∨ p.timeoutAt ≤ now)
              · simp [h1, h2, h3, h4]
              · by_cases h5 : t.version = req.version
                · simp [h1, h2, h3, h4, h5, setTask, delTaskTimeout, setTaskTimeout, setMessage]
                · simp [h1, h2, h3, h4, h5]
            · simp [h1, h2, h3]
      have hprom : (stepOf (.taskRelease req) now s).2.promises = s.promises := hrel
      unfold logical at hl ⊢; rw [hprom]; exact hl
  | taskHalt req => exact frozen_taskHalt req now s id st hset hl
  | taskContinue req =>
      have hcont : (taskContinue req now s).2.promises = s.promises := by
        unfold taskContinue getTask getPromise
        by_cases h1 : s.tasks.find? (·.id == req.id) = none
        · simp [h1]
        · obtain ⟨t, h1⟩ := Option.eq_none_or_eq_some (s.tasks.find? (·.id == req.id)) |>.resolve_left h1
          by_cases h3 : t.state = TaskState.halted
          case neg => simp [h1, h3]
          · by_cases h2 : s.promises.find? (·.id == t.id) = none
            · simp [h1, h2, h3]
            · obtain ⟨p, h2⟩ := Option.eq_none_or_eq_some (s.promises.find? (·.id == t.id)) |>.resolve_left h2
              by_cases h4 : p.state = PromiseState.pending
              · by_cases h5 : p.timeoutAt ≤ now
                · simp [h1, h2, h3, h4, h5]
                · simp [h1, h2, h3, h4, h5, setTask, setTaskTimeout, setMessage]
              · simp [h1, h2, h3, h4]
      have hprom : (stepOf (.taskContinue req) now s).2.promises = s.promises := hcont
      unfold logical at hl ⊢; rw [hprom]; exact hl
  | taskSearch req => unfold stepOf; unfold handle; simpa [taskSearch, logical] using hl
  | τPromiseTimeout pid => exact frozen_τPromiseTimeout pid now s id st hset hl
  | τTaskRetryTimeout pid => exact frozen_τTaskRetryTimeout pid now s id st hset hl
  | τTaskLeaseTimeout pid => exact frozen_τTaskLeaseTimeout pid now s id st hset hl
  | τScheduleTimeout pid => exact frozen_τScheduleTimeout pid now s id st hset hl
  | τResume req => exact frozen_τResume req now s id st hset hl
  | idle => unfold stepOf; unfold handle; simpa [logical] using hl

theorem stable : ∀ tr : Trace, Valid tr → Stable tr :=
  stable_of_sound_frozen stepSound stepFrozen
