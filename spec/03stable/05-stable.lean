import «03stable».«04-trace»

open ServerModel

/-! ## Stability

Once the system externalizes a promise in a settled state, it never
externalizes that promise in any other state. Settlement, once on the
wire, is forever.

Stability is a property of RESPONSES, not of stored state: it does not
care when materialization happens, only that no two externalizations
ever disagree about a settled promise. This is what makes the
materialization schedule unobservable — a `promiseGet` serves the
PROJECTED record, so a pending promise past its deadline is
externalized settled (stamped AT THE DEADLINE) before any timeout τ
materializes it, and the τ later writes the byte-identical record.

The monotone clock in `Valid` is load-bearing here: projection settles
a promise as a function of `now`. If the clock could run backwards, a
`get` after the deadline followed by a `get` before it would
externalize settled-then-pending — connectivity alone does not give
stability; connectivity plus the forward clock does.
-/

/-- Every promise record a response externalizes. -/
def Response.promises : Response → List PromiseRecord
  | .promiseGet r              => r.promise.toList
  | .promiseCreate r           => r.promise.toList
  | .promiseSettle r           => r.promise.toList
  | .promiseRegisterCallback r => r.promise.toList
  | .promiseRegisterListener r => r.promise.toList
  | .promiseSearch r           => r.promises
  | .taskCreate r              => r.promise.toList ++ r.preload
  | .taskAcquire r             => r.promise.toList ++ r.preload
  | .taskFence r               =>
      (match r.action with
       | some (.create c) => c.promise.toList
       | some (.settle s) => s.promise.toList
       | none             => []) ++ r.preload
  | .taskSuspend r             => r.preload
  | .taskFulfill r             => r.promise.toList
  | _                          => []

/-- Response `rs` externalizes promise `id` in state `st`. -/
def Externalized (rs : Response) (id : String) (st : PromiseState) : Prop :=
  ∃ p ∈ rs.promises, p.id = id ∧ p.state = st

instance (rs : Response) (id : String) (st : PromiseState) :
    Decidable (Externalized rs id st) :=
  inferInstanceAs (Decidable (∃ p ∈ rs.promises, p.id = id ∧ p.state = st))

/-- A settled state: anything but `pending`. -/
def Settled (st : PromiseState) : Prop :=
  st ≠ .pending

/-- **Stability**: once promise `id` is externalized in a settled
    state, every later externalization of `id` shows the same state.

    The protocol's claim — to be discharged over the machine's
    invariants (settled stored state is frozen, projection is monotone
    in `now`, every promise-bearing response projects):

      theorem stable_of_valid : ∀ tr : Trace, Valid tr → Stable tr
-/
def Stable (tr : Trace) : Prop :=
  ∀ i j : Nat, ∀ id : String, ∀ st₁ st₂ : PromiseState,
    i ≤ j →
      Externalized (tr i).res id st₁ →
        Settled st₁ →
          Externalized (tr j).res id st₂ →
            st₂ = st₁

/-! ### Executable verification

The sharpest scenario: an external promise is created with deadline
1000, and a `get` at 1500 externalizes it settled (`rejectedTimedout`,
stamped at the deadline) BEFORE the timeout τ has fired. The τ then
materializes it, and a later `get` externalizes it again. Stability
demands all externalizations after instant 1 agree — projection first,
materialization later, byte-identical on the wire. -/

private def rq₀ : Request := .promiseCreate
  { id := "p", timeoutAt := 1000, param := {}, tags := [("resonate:external", "true")] }
private def rq₁ : Request := .promiseGet { id := "p" }
private def rq₂ : Request := .τPromiseTimeout "p"
private def rq₃ : Request := .promiseGet { id := "p" }

private def s₀ : ServerState := ServerState.init
private def s₁ : ServerState := (stepOf rq₀ 0    s₀).2
private def s₂ : ServerState := (stepOf rq₁ 1500 s₁).2
private def s₃ : ServerState := (stepOf rq₂ 1600 s₂).2
private def s₄ : ServerState := (stepOf rq₃ 1700 s₃).2

private def demoTr : Trace
  | 0     => { state := s₀, req := rq₀,   now := 0,    res := (stepOf rq₀ 0    s₀).1 }
  | 1     => { state := s₁, req := rq₁,   now := 1500, res := (stepOf rq₁ 1500 s₁).1 }
  | 2     => { state := s₂, req := rq₂,   now := 1600, res := (stepOf rq₂ 1600 s₂).1 }
  | 3     => { state := s₃, req := rq₃,   now := 1700, res := (stepOf rq₃ 1700 s₃).1 }
  | _ + 4 => { state := s₄, req := .idle, now := 1700, res := .τ }

private theorem demoTr_valid : Valid demoTr := fun t =>
  match t with
  | 0     => ⟨rfl, rfl, Nat.zero_le _⟩
  | 1     => ⟨rfl, rfl, by decide⟩
  | 2     => ⟨rfl, rfl, by decide⟩
  | 3     => ⟨rfl, rfl, Nat.le_refl _⟩
  | _ + 4 => ⟨rfl, rfl, Nat.le_refl _⟩

-- Instant 1 externalizes "p" settled before the τ fired; instant 3
-- externalizes it after. Same state on the wire.
example : Externalized (demoTr 1).res "p" .rejectedTimedout := by native_decide
example : Externalized (demoTr 3).res "p" .rejectedTimedout := by native_decide

/-- Stability, checked decidably over a window of the trace. -/
private def stableUpTo (tr : Trace) (n : Nat) : Bool :=
  (List.range n).all fun i =>
    (List.range n).all fun j =>
      !(decide (i ≤ j)) ||
        ((tr i).res.promises.all fun p =>
          p.state == .pending ||
            ((tr j).res.promises.all fun q =>
              q.id != p.id || q.state == p.state))

-- Every externalization in the window agrees (instants ≥ 4 idle: vacuous).
example : stableUpTo demoTr 6 = true := by native_decide
