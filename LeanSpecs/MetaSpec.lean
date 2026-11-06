import LeanSpecs.Core

namespace LeanSpecs

structure MetaGateSpec (Input : Type) (Safe : Input → Prop) where
  gate       : Input → Bool
  sound      : ∀ x, gate x = true → Safe x
  complete   : ∀ x, Safe x → gate x = true
  posWitness : Input
  negWitness : Input
  nonVacuous : gate posWitness = true
  tight      : gate negWitness = false

theorem MetaGateSpec.iff_safe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) :
    M.gate x = true ↔ Safe x :=
  ⟨M.sound x, M.complete x⟩

theorem MetaGateSpec.rejects_unsafe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) (hUnsafe : ¬ Safe x) :
    M.gate x = false :=
  Bool.eq_false_iff.mpr (fun hOk => hUnsafe (M.sound x hOk))

theorem MetaGateSpec.pos_ne_neg {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) :
    M.posWitness ≠ M.negWitness :=
  fun h => by simpa [h, M.tight] using M.nonVacuous

structure MetaAlgorithmSpec (Input Output : Type) where
  fast      : Input → Costed Output
  oracle    : Input → Output
  stepBound : Input → Nat
  equiv     : ∀ x, (fast x).val = oracle x
  bounded   : ∀ x, (fast x).steps ≤ stepBound x

theorem MetaAlgorithmSpec.sound_and_bounded {Input Output : Type}
    (A : MetaAlgorithmSpec Input Output) (x : Input) :
    (A.fast x).val = A.oracle x ∧ (A.fast x).steps ≤ A.stepBound x :=
  ⟨A.equiv x, A.bounded x⟩

structure JointSatisfiableSpec (Impl : Type) (Specs : List (Impl → Prop)) where
  witness   : Impl
  all_hold  : ∀ S, S ∈ Specs → S witness

theorem JointSatisfiableSpec.no_pairwise_contradiction {Impl : Type}
    {Specs : List (Impl → Prop)}
    (J : JointSatisfiableSpec Impl Specs)
    {S₁ S₂ : Impl → Prop}
    (h₁ : S₁ ∈ Specs) (h₂ : S₂ ∈ Specs) :
    ¬ (∀ impl, S₁ impl → ¬ S₂ impl) :=
  fun hContra => hContra J.witness (J.all_hold S₁ h₁) (J.all_hold S₂ h₂)

structure NonVacuousSpec (Input Output : Type)
    (Pre : Input → Prop) (Post : Input → Output → Prop) (step : Input → Output) where
  sound                 : ∀ x, Pre x → Post x (step x)
  okWitness             : Input
  pre_inhabited         : Pre okWitness
  badOutputWitness      : Output
  post_non_tautological : ¬ Post okWitness badOutputWitness

theorem NonVacuousSpec.step_ne_bad {Input Output : Type}
    {Pre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (S : NonVacuousSpec Input Output Pre Post step) :
    step S.okWitness ≠ S.badOutputWitness := by
  intro h
  have hPost := S.sound S.okWitness S.pre_inhabited
  rw [h] at hPost
  exact S.post_non_tautological hPost

structure HypothesisMinimalWitness (Input Output : Type)
    (DroppedPre KeptPre : Input → Prop)
    (Post : Input → Output → Prop)
    (step : Input → Output) where
  dropWitness   : Input
  kept_holds    : KeptPre dropWitness
  dropped_fails : ¬ DroppedPre dropWitness
  post_fails    : ¬ Post dropWitness (step dropWitness)

theorem HypothesisMinimalWitness.cannot_drop_hypothesis {Input Output : Type}
    {DroppedPre KeptPre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (W : HypothesisMinimalWitness Input Output DroppedPre KeptPre Post step) :
    ¬ (∀ x, KeptPre x → Post x (step x)) :=
  fun hTooWeak => W.post_fails (hTooWeak W.dropWitness W.kept_holds)

structure FrameInvariant (State Op Proj : Type) where
  project   : State → Proj
  step      : State → Op → State
  preserved : ∀ (s : State) (op : Op), project (step s op) = project s

theorem FrameInvariant.preserved_list {State Op Proj : Type}
    (F : FrameInvariant State Op Proj) (s : State) (ops : List Op) :
    F.project (ops.foldl F.step s) = F.project s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => simpa [List.foldl, F.preserved s op] using ih (F.step s op)

structure ExactDeltaSpec (State Op FrameProj WriteProj : Type) where
  frame           : FrameInvariant State Op FrameProj
  readWrite       : State → WriteProj
  expectedWrite   : State → Op → WriteProj
  delta_exact     : ∀ (s : State) (op : Op),
    readWrite (frame.step s op) = expectedWrite s op
  witnessState    : State
  witnessOp       : Op
  nonTrivialWrite : readWrite (frame.step witnessState witnessOp) ≠ readWrite witnessState

theorem ExactDeltaSpec.witness_step_ne_id {State Op FrameProj WriteProj : Type}
    (E : ExactDeltaSpec State Op FrameProj WriteProj) :
    E.frame.step E.witnessState E.witnessOp ≠ E.witnessState :=
  fun hEq => E.nonTrivialWrite (congrArg E.readWrite hEq)

structure OutcomePartitionSpec (σ ε α : Type) (op : SpecM σ ε α) (ErrCond : σ → Prop) where
  err_iff          : ∀ s, (op s).isErr = true ↔ ErrCond s
  ok_iff           : ∀ s, (op s).isOk = true ↔ ¬ ErrCond s
  okWitness        : σ
  errWitness       : σ
  okWitness_valid  : (op okWitness).isOk = true
  errWitness_valid : (op errWitness).isErr = true

theorem OutcomePartitionSpec.ok_ne_err {σ ε α : Type} {op : SpecM σ ε α} {ErrCond : σ → Prop}
    (P : OutcomePartitionSpec σ ε α op ErrCond) :
    P.okWitness ≠ P.errWitness := by
  intro hEq
  have hOk := (P.ok_iff P.okWitness).mp P.okWitness_valid
  rw [hEq] at hOk
  exact hOk ((P.err_iff P.errWitness).mp P.errWitness_valid)

structure AccountingBoundarySpec (State Op : Type) where
  step      : State → Op → State
  measure   : State → Nat
  inflow    : State → Op → Nat
  outflow   : State → Op → Nat
  conserved : ∀ (s : State) (op : Op),
    measure (step s op) + outflow s op = measure s + inflow s op

theorem AccountingBoundarySpec.supply_neutral_when_balanced {State Op : Type}
    (A : AccountingBoundarySpec State Op) (s : State) (op : Op)
    (hBal : A.inflow s op = A.outflow s op) :
    A.measure (A.step s op) = A.measure s := by
  have h := A.conserved s op
  omega

structure OrderIndependence (State Elem : Type) (f : State → Elem → State) where
  idempotent  : ∀ (s : State) (x : Elem), f (f s x) x = f s x
  commutative : ∀ (s : State) (x y : Elem), f (f s x) y = f (f s y) x

theorem OrderIndependence.swap_pair {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x y : Elem) :
    [x, y].foldl f s = [y, x].foldl f s :=
  O.commutative s x y

theorem OrderIndependence.dedup_pair {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x : Elem) :
    [x, x].foldl f s = [x].foldl f s :=
  O.idempotent s x

theorem OrderIndependence.foldl_comm_single {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x : Elem) (xs : List Elem) :
    xs.foldl f (f s x) = f (xs.foldl f s) x := by
  induction xs generalizing s with
  | nil => rfl
  | cons y ys ih =>
    dsimp [List.foldl]
    rw [O.commutative s x y]
    exact ih (f s y)

theorem OrderIndependence.foldl_swap_adjacent {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (pre suf : List Elem) (x y : Elem) :
    (pre ++ x :: y :: suf).foldl f s = (pre ++ y :: x :: suf).foldl f s := by
  simp only [List.foldl_append, List.foldl]
  rw [O.commutative (pre.foldl f s) x y]

structure WitnessRefuter (Input Output : Type) (Valid : Input → Output → Prop) where
  reference      : Input → Output
  mutant         : Input → Output
  ref_sound      : ∀ x, Valid x (reference x)
  killWitness    : Input
  mutant_refuted : ¬ Valid killWitness (mutant killWitness)

theorem WitnessRefuter.mutant_ne_reference {Input Output : Type}
    {Valid : Input → Output → Prop} (W : WitnessRefuter Input Output Valid) :
    W.mutant W.killWitness ≠ W.reference W.killWitness := by
  intro h
  have hValid := W.ref_sound W.killWitness
  rw [← h] at hValid
  exact W.mutant_refuted hValid

structure MutantKillBundle (Input Output : Type) (Valid : Input → Output → Prop) where
  reference     : Input → Output
  arithMutant   : WitnessRefuter Input Output Valid
  fieldMutant   : WitnessRefuter Input Output Valid
  orderMutant   : WitnessRefuter Input Output Valid
  aliasMutant   : WitnessRefuter Input Output Valid
  arith_ref_eq  : arithMutant.reference = reference := by rfl
  field_ref_eq  : fieldMutant.reference = reference := by rfl
  order_ref_eq  : orderMutant.reference = reference := by rfl
  alias_ref_eq  : aliasMutant.reference = reference := by rfl

structure ClauseIndependenceWitness (Impl : Type)
    (TargetClause OtherClauses : Impl → Prop) where
  separatingMutant : Impl
  others_satisfied : OtherClauses separatingMutant
  target_violated  : ¬ TargetClause separatingMutant

theorem ClauseIndependenceWitness.not_entailed {Impl : Type}
    {TargetClause OtherClauses : Impl → Prop}
    (W : ClauseIndependenceWitness Impl TargetClause OtherClauses) :
    ¬ (∀ impl, OtherClauses impl → TargetClause impl) :=
  fun hRedundant => W.target_violated (hRedundant W.separatingMutant W.others_satisfied)

@[inline]
def evalWithSpeculativeGate {Goal Cert : Type}
    (accel : Goal → Option Cert)
    (verifyCert : Goal → Cert → Bool)
    (fallback : Goal → Bool)
    (g : Goal) : Bool :=
  match accel g with
  | some c => if verifyCert g c then true else fallback g
  | none => fallback g

theorem speculativeGate_sound_eq {Goal Cert : Type}
    (accel : Goal → Option Cert)
    (verifyCert : Goal → Cert → Bool)
    (fallback : Goal → Bool)
    (hSound : ∀ g c, verifyCert g c = true → fallback g = true)
    (g : Goal) :
    evalWithSpeculativeGate accel verifyCert fallback g = fallback g := by
  unfold evalWithSpeculativeGate
  split
  · split
    · exact (hSound g _ ‹_›).symm
    · rfl
  · rfl

@[inline]
def evalWithVerifiedTransform {Decl Cert : Type}
    (propose : Decl → Option (Decl × Cert))
    (verifyGate : Decl → Decl → Cert → Bool)
    (d : Decl) : Decl :=
  match propose d with
  | some (cand, cert) => if verifyGate d cand cert then cand else d
  | none => d

theorem verifiedTransform_refines {Decl Cert : Type}
    (Refines : Decl → Decl → Prop)
    (hRefl : ∀ d, Refines d d)
    (propose : Decl → Option (Decl × Cert))
    (verifyGate : Decl → Decl → Cert → Bool)
    (hSound : ∀ d cand cert, verifyGate d cand cert = true → Refines d cand)
    (d : Decl) :
    Refines d (evalWithVerifiedTransform propose verifyGate d) := by
  unfold evalWithVerifiedTransform
  split
  · split
    · exact hSound d _ _ ‹_›
    · exact hRefl d
  · exact hRefl d

end LeanSpecs
