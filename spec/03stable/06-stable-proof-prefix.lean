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
@[simp] theorem run_setTask_2 (t : TaskObject) (s : ServerState) :
    ((setTask t : M Unit) s).2 = { s with tasks := t :: s.tasks.filter (·.id != t.id) } := by
  simp [run_setTask]
@[simp] theorem run_setPromise_2 (p : PromiseObject) (s : ServerState) :
    ((setPromise p : M Unit) s).2 = { s with promises := p :: s.promises.filter (·.id != p.id) } := by
  simp [run_setPromise]
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
  unfold PromiseObject.project; split
  · split <;> rfl
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
theorem test_prefix_ok : True := by trivial
