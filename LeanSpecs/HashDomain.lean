import LeanSpecs.MetaSpec

namespace LeanSpecs

def CollisionFreeOn {Key Digest : Type} (hash : Key → Digest) (footprint : List Key) : Prop :=
  ∀ x, x ∈ footprint → ∀ y, y ∈ footprint → hash x = hash y → x = y

def checkCollisionFreeOn {Key Digest : Type} [DecidableEq Key] [DecidableEq Digest]
    (hash : Key → Digest) : List Key → Bool
  | [] => true
  | x :: xs =>
    xs.all (fun y => !(hash x == hash y) || (x == y)) && checkCollisionFreeOn hash xs

theorem collisionFreeOn_nil {Key Digest : Type} (hash : Key → Digest) :
    CollisionFreeOn hash [] := by
  intro _ hx
  cases hx

theorem collisionFreeOn_singleton {Key Digest : Type} (hash : Key → Digest) (k : Key) :
    CollisionFreeOn hash [k] := by
  intro x hx y hy _
  simp at hx hy
  subst hx
  subst hy
  rfl

theorem CollisionFreeOn.lookup_unique {Key Digest : Type}
    {hash : Key → Digest} {footprint : List Key}
    (hFree : CollisionFreeOn hash footprint)
    {k₁ k₂ : Key} (h₁ : k₁ ∈ footprint) (h₂ : k₂ ∈ footprint)
    (hDigest : hash k₁ = hash k₂) :
    k₁ = k₂ :=
  hFree k₁ h₁ k₂ h₂ hDigest

theorem CollisionFreeOn.subset {Key Digest : Type}
    {hash : Key → Digest} {small large : List Key}
    (hFree : CollisionFreeOn hash large)
    (hSub : ∀ k, k ∈ small → k ∈ large) :
    CollisionFreeOn hash small :=
  fun x hx y hy hEq => hFree x (hSub x hx) y (hSub y hy) hEq

theorem checkCollisionFreeOn_iff {Key Digest : Type} [DecidableEq Key] [DecidableEq Digest]
    (hash : Key → Digest) (footprint : List Key) :
    checkCollisionFreeOn hash footprint = true ↔ CollisionFreeOn hash footprint := by
  induction footprint with
  | nil =>
    simp [checkCollisionFreeOn, collisionFreeOn_nil]
  | cons x xs ih =>
    constructor
    · intro hOk
      simp only [checkCollisionFreeOn, Bool.and_eq_true, List.all_eq_true] at hOk
      rcases hOk with ⟨hHead, hTail⟩
      have hFreeTail : CollisionFreeOn hash xs := ih.mp hTail
      intro a ha b hb hEq
      cases List.mem_cons.mp ha with
      | inl hax =>
        subst hax
        cases List.mem_cons.mp hb with
        | inl hbx =>
          subst hbx
          rfl
        | inr hbx =>
          have hPair := hHead b hbx
          simp [hEq] at hPair
          exact hPair
      | inr hax =>
        cases List.mem_cons.mp hb with
        | inl hbx =>
          subst hbx
          have hPair := hHead a hax
          have hEqSymm : hash b = hash a := hEq.symm
          simp [hEqSymm] at hPair
          exact hPair.symm
        | inr hbx =>
          exact hFreeTail a hax b hbx hEq
    · intro hFree
      have hTailFree : CollisionFreeOn hash xs :=
        hFree.subset (fun _ hk => List.mem_cons_of_mem x hk)
      simp only [checkCollisionFreeOn, Bool.and_eq_true, List.all_eq_true]
      refine ⟨?_, ih.mpr hTailFree⟩
      intro y hy
      by_cases hHash : hash x = hash y
      · have hEq : x = y :=
          hFree x (List.mem_cons_self ..) y (List.mem_cons_of_mem x hy) hHash
        simp [hEq]
      · simp [hHash]

theorem universal_fin2_footprint_forces_global_injective {Key Digest : Type}
    {hash : Key → Digest}
    (hAllPairs : ∀ x y : Key, CollisionFreeOn hash [x, y]) :
    ∀ x y : Key, hash x = hash y → x = y := by
  intro x y hEq
  exact hAllPairs x y x (by simp) y (by simp) hEq

theorem no_global_injective_fin_succ {n : Nat} (f : Fin (n + 1) → Fin n)
    (hInj : ∀ x y : Fin (n + 1), f x = f y → x = y) :
    False := by
  induction n with
  | zero =>
    exact Fin.elim0 (f ⟨0, Nat.zero_lt_one⟩)
  | succ m ih =>
    let last : Fin (m + 2) := ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
    let emb (i : Fin (m + 1)) : Fin (m + 2) := ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    have hNeLast : ∀ i : Fin (m + 1), (f (emb i)).1 ≠ (f last).1 := by
      intro i hEqVal
      have hSame : emb i = last := hInj (emb i) last (Fin.ext hEqVal)
      have hVal : i.1 = m + 1 := congrArg Fin.val hSame
      omega
    let g (i : Fin (m + 1)) : Fin m :=
      if hLt : (f (emb i)).1 < (f last).1 then
        ⟨(f (emb i)).1, Nat.lt_of_lt_of_le hLt (Nat.le_of_lt_succ (f last).2)⟩
      else
        have hGt : (f last).1 < (f (emb i)).1 := by
          have hNeVal := hNeLast i
          omega
        ⟨(f (emb i)).1 - 1, by omega⟩
    have hgInj : ∀ i j : Fin (m + 1), g i = g j → i = j := by
      intro i j hEqG
      have hValG : (g i).1 = (g j).1 := congrArg Fin.val hEqG
      have hNeI := hNeLast i
      have hNeJ := hNeLast j
      dsimp only [g] at hValG
      split at hValG <;> split at hValG <;> simp only at hValG
      · have hF : f (emb i) = f (emb j) := Fin.ext hValG
        have hEmb : emb i = emb j := hInj (emb i) (emb j) hF
        have hValIJ : (emb i).1 = (emb j).1 := congrArg Fin.val hEmb
        exact Fin.ext hValIJ
      · omega
      · omega
      · have hF : f (emb i) = f (emb j) := Fin.ext (by omega)
        have hEmb : emb i = emb j := hInj (emb i) (emb j) hF
        have hValIJ : (emb i).1 = (emb j).1 := congrArg Fin.val hEmb
        exact Fin.ext hValIJ
    exact ih g hgInj

theorem no_global_injective_fin_gt {dom cod : Nat}
    (hGt : cod < dom)
    (f : Fin dom → Fin cod)
    (hInj : ∀ x y : Fin dom, f x = f y → x = y) :
    False := by
  let emb (i : Fin (cod + 1)) : Fin dom :=
    ⟨i.1, Nat.lt_of_lt_of_le i.2 hGt⟩
  have hSubInj : ∀ x y : Fin (cod + 1), f (emb x) = f (emb y) → x = y := by
    intro x y hEq
    have hEmb : emb x = emb y := hInj (emb x) (emb y) hEq
    have hVal : (emb x).1 = (emb y).1 := congrArg Fin.val hEmb
    exact Fin.ext hVal
  exact no_global_injective_fin_succ (fun x => f (emb x)) hSubInj

theorem no_global_pair_hash_injective {n : Nat}
    (hAtLeastTwo : 2 ≤ n)
    (hash : Fin n → Fin n → Fin n)
    (hInj : ∀ a₁ b₁ a₂ b₂ : Fin n, hash a₁ b₁ = hash a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂) :
    False := by
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let unrank (k : Fin (n + 1)) : Fin n × Fin n :=
    if hLt : k.1 < n then
      (zero, ⟨k.1, hLt⟩)
    else
      (one, zero)
  have hUnrankInj : ∀ x y : Fin (n + 1), unrank x = unrank y → x = y := by
    intro x y hEq
    dsimp only [unrank] at hEq
    split at hEq <;> split at hEq
    · injection hEq with _ hSecond
      have hVal : x.1 = y.1 := congrArg (Fin.val : Fin n → Nat) hSecond
      exact Fin.ext hVal
    · injection hEq with hFirst _
      have h01 : (0 : Nat) = 1 := congrArg Fin.val hFirst
      omega
    · injection hEq with hFirst _
      have h10 : (1 : Nat) = 0 := congrArg Fin.val hFirst
      omega
    · exact Fin.ext (by omega)
  have hCompInj : ∀ x y : Fin (n + 1),
      hash (unrank x).1 (unrank x).2 = hash (unrank y).1 (unrank y).2 → x = y := by
    intro x y hHashEq
    have hPair := hInj (unrank x).1 (unrank x).2 (unrank y).1 (unrank y).2 hHashEq
    have hProdEq : unrank x = unrank y := Prod.ext hPair.1 hPair.2
    exact hUnrankInj x y hProdEq
  exact no_global_injective_fin_succ (fun x => hash (unrank x).1 (unrank x).2) hCompInj

structure RoutingGateSpec (Raw Flags : Type)
    (extractInTcb : Raw → Flags)
    (PolicySafe : Flags → Prop) where
  policyGate     : MetaGateSpec Flags PolicySafe
  rawSafeWitness : Raw
  rawBadWitness  : Raw
  raw_nonVacuous : policyGate.gate (extractInTcb rawSafeWitness) = true
  raw_tight      : policyGate.gate (extractInTcb rawBadWitness) = false

@[inline]
def RoutingGateSpec.eval {Raw Flags : Type}
    {extractInTcb : Raw → Flags} {PolicySafe : Flags → Prop}
    (R : RoutingGateSpec Raw Flags extractInTcb PolicySafe) (raw : Raw) : Bool :=
  R.policyGate.gate (extractInTcb raw)

theorem RoutingGateSpec.eval_iff_extracted_policy {Raw Flags : Type}
    {extractInTcb : Raw → Flags} {PolicySafe : Flags → Prop}
    (R : RoutingGateSpec Raw Flags extractInTcb PolicySafe) (raw : Raw) :
    R.eval raw = true ↔ PolicySafe (extractInTcb raw) :=
  R.policyGate.iff_safe (extractInTcb raw)

theorem RoutingGateSpec.rawSafe_ne_rawBad {Raw Flags : Type}
    {extractInTcb : Raw → Flags} {PolicySafe : Flags → Prop}
    (R : RoutingGateSpec Raw Flags extractInTcb PolicySafe) :
    R.rawSafeWitness ≠ R.rawBadWitness :=
  fun h => by simpa [h, R.raw_tight] using R.raw_nonVacuous

theorem RoutingGateSpec.sound_for_raw_of_faithful_extractor {Raw Flags : Type}
    {extractInTcb : Raw → Flags} {PolicySafe : Flags → Prop}
    (R : RoutingGateSpec Raw Flags extractInTcb PolicySafe)
    (TrueRawSafe : Raw → Prop)
    (hFaithful : ∀ raw, PolicySafe (extractInTcb raw) → TrueRawSafe raw)
    (raw : Raw)
    (hEval : R.eval raw = true) :
    TrueRawSafe raw :=
  hFaithful raw (R.policyGate.sound (extractInTcb raw) hEval)

theorem RoutingGateSpec.extractor_spoof_breaks_raw_safety {Raw Flags : Type}
    {extractInTcb : Raw → Flags} {PolicySafe : Flags → Prop}
    (R : RoutingGateSpec Raw Flags extractInTcb PolicySafe)
    (TrueRawSafe : Raw → Prop)
    (spoofedRaw : Raw)
    (hUnsafeRaw : ¬ TrueRawSafe spoofedRaw)
    (hExtractorBug : extractInTcb spoofedRaw = R.policyGate.posWitness) :
    R.eval spoofedRaw = true ∧ ¬ TrueRawSafe spoofedRaw := by
  refine ⟨?_, hUnsafeRaw⟩
  unfold RoutingGateSpec.eval
  rw [hExtractorBug]
  exact R.policyGate.nonVacuous

end LeanSpecs
