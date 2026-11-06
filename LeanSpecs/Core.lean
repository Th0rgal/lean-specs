namespace LeanSpecs

inductive Result (ε σ α : Type) where
  | ok (val : α) (state : σ)
  | err (error : ε) (state : σ)
  deriving Repr, DecidableEq, BEq

namespace Result

@[inline, simp]
def isOk {ε σ α : Type} : Result ε σ α → Bool
  | .ok _ _ => true
  | .err _ _ => false

@[inline, simp]
def isErr {ε σ α : Type} : Result ε σ α → Bool
  | .ok _ _ => false
  | .err _ _ => true

@[inline, simp]
def state {ε σ α : Type} : Result ε σ α → σ
  | .ok _ s => s
  | .err _ s => s

@[inline, simp]
def val? {ε σ α : Type} : Result ε σ α → Option α
  | .ok a _ => some a
  | .err _ _ => none

@[inline, simp]
def err? {ε σ α : Type} : Result ε σ α → Option ε
  | .ok _ _ => none
  | .err e _ => some e

theorem isOk_eq_not_isErr {ε σ α : Type} (r : Result ε σ α) :
    r.isOk = !r.isErr := by
  cases r <;> rfl

theorem isErr_eq_true_iff_not_isOk {ε σ α : Type} (r : Result ε σ α) :
    r.isErr = true ↔ r.isOk = false := by
  cases r <;> simp

end Result

abbrev SpecM (σ ε α : Type) := σ → Result ε σ α

namespace SpecM

@[inline, simp]
def pure {σ ε α : Type} (a : α) : SpecM σ ε α :=
  fun s => .ok a s

@[inline, simp]
def bind {σ ε α β : Type} (m : SpecM σ ε α) (f : α → SpecM σ ε β) : SpecM σ ε β :=
  fun s =>
    match m s with
    | .ok a s' => f a s'
    | .err e s' => .err e s'

instance {σ ε : Type} : Monad (SpecM σ ε) where
  pure := pure
  bind := bind

@[simp]
theorem bind_pure {σ ε α : Type} (m : SpecM σ ε α) :
    bind m pure = m := by
  funext s
  dsimp [bind, pure]
  cases m s <;> rfl

@[simp]
theorem pure_bind {σ ε α β : Type} (a : α) (f : α → SpecM σ ε β) :
    bind (pure a) f = f a := rfl

@[simp]
theorem bind_assoc {σ ε α β γ : Type}
    (m : SpecM σ ε α) (f : α → SpecM σ ε β) (g : β → SpecM σ ε γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  funext s
  dsimp [bind]
  cases m s <;> rfl

@[inline, simp]
def get {σ ε : Type} : SpecM σ ε σ :=
  fun s => .ok s s

@[inline, simp]
def set {σ ε : Type} (s' : σ) : SpecM σ ε Unit :=
  fun _ => .ok () s'

@[inline, simp]
def modify {σ ε : Type} (f : σ → σ) : SpecM σ ε Unit :=
  fun s => .ok () (f s)

@[inline, simp]
def throw {σ ε α : Type} (e : ε) : SpecM σ ε α :=
  fun s => .err e s

@[inline, simp]
def guardOr {σ ε : Type} (cond : Bool) (e : ε) : SpecM σ ε Unit :=
  fun s => if cond then .ok () s else .err e s

@[inline, simp]
def atomicRollback {σ ε α : Type} (m : SpecM σ ε α) : SpecM σ ε α :=
  fun s =>
    match m s with
    | .ok a s' => .ok a s'
    | .err e _ => .err e s

theorem atomicRollback_err_preserves_state {σ ε α : Type}
    (m : SpecM σ ε α) (s : σ) (hErr : (atomicRollback m s).isErr = true) :
    (atomicRollback m s).state = s := by
  unfold atomicRollback at hErr ⊢
  cases h : m s <;> simp [h] at hErr ⊢

end SpecM

structure Costed (α : Type) where
  val   : α
  steps : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

structure ObsQuotient (State Obs : Type) where
  observe : State → Obs

def ObsQuotient.Equiv {State Obs : Type} (Q : ObsQuotient State Obs) (s₁ s₂ : State) : Prop :=
  Q.observe s₁ = Q.observe s₂

@[simp]
theorem ObsQuotient.equiv_refl {State Obs : Type} (Q : ObsQuotient State Obs) (s : State) :
    Q.Equiv s s := rfl

theorem ObsQuotient.equiv_symm {State Obs : Type} (Q : ObsQuotient State Obs) {s₁ s₂ : State}
    (h : Q.Equiv s₁ s₂) : Q.Equiv s₂ s₁ :=
  h.symm

theorem ObsQuotient.equiv_trans {State Obs : Type} (Q : ObsQuotient State Obs) {s₁ s₂ s₃ : State}
    (h₁₂ : Q.Equiv s₁ s₂) (h₂₃ : Q.Equiv s₂ s₃) : Q.Equiv s₁ s₃ :=
  h₁₂.trans h₂₃

structure ObsAndCostRefinement (State Obs : Type) where
  quotient      : ObsQuotient State Obs
  cost          : State → Nat
  baseline      : State
  candidate     : State
  preserves_obs : quotient.Equiv candidate baseline
  improves_cost : cost candidate ≤ cost baseline

theorem ObsAndCostRefinement.trans {State Obs : Type}
    {Q : ObsQuotient State Obs} {cost : State → Nat} {s₀ s₁ s₂ : State}
    (r₁ : ObsAndCostRefinement State Obs)
    (r₂ : ObsAndCostRefinement State Obs)
    (hq₁ : r₁.quotient = Q) (hc₁ : r₁.cost = cost)
    (hb₁ : r₁.baseline = s₀) (hca₁ : r₁.candidate = s₁)
    (hq₂ : r₂.quotient = Q) (hc₂ : r₂.cost = cost)
    (hb₂ : r₂.baseline = s₁) (hca₂ : r₂.candidate = s₂) :
    Q.Equiv s₂ s₀ ∧ cost s₂ ≤ cost s₀ := by
  have ho₁ : Q.Equiv s₁ s₀ := by
    have h := r₁.preserves_obs
    rw [hq₁, hb₁, hca₁] at h
    exact h
  have ho₂ : Q.Equiv s₂ s₁ := by
    have h := r₂.preserves_obs
    rw [hq₂, hb₂, hca₂] at h
    exact h
  have hco₁ : cost s₁ ≤ cost s₀ := by
    have h := r₁.improves_cost
    rw [hc₁, hb₁, hca₁] at h
    exact h
  have hco₂ : cost s₂ ≤ cost s₁ := by
    have h := r₂.improves_cost
    rw [hc₂, hb₂, hca₂] at h
    exact h
  exact ⟨Q.equiv_trans ho₂ ho₁, Nat.le_trans hco₂ hco₁⟩

end LeanSpecs
