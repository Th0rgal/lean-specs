import LeanSpecs.Core

namespace LeanSpecs

structure Footprint (Loc : Type) where
  locs : List Loc := []
  deriving Repr, DecidableEq

def Disjoint {Loc : Type} (a b : Footprint Loc) : Prop :=
  ∀ l, l ∈ a.locs → l ∉ b.locs

theorem Disjoint.symm {Loc : Type} {a b : Footprint Loc} (h : Disjoint a b) :
    Disjoint b a :=
  fun l hb ha => h l ha hb

@[simp]
theorem disjoint_empty_left {Loc : Type} (fp : Footprint Loc) :
    Disjoint ({} : Footprint Loc) fp := by
  intro l hl
  cases hl

@[simp]
theorem disjoint_empty_right {Loc : Type} (fp : Footprint Loc) :
    Disjoint fp ({} : Footprint Loc) :=
  (disjoint_empty_left fp).symm

def Footprint.union {Loc : Type} (a b : Footprint Loc) : Footprint Loc :=
  { locs := a.locs ++ b.locs }

theorem Disjoint.union_left {Loc : Type} {a b c : Footprint Loc}
    (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (Footprint.union a b) c := by
  intro l hl
  cases List.mem_append.mp hl with
  | inl h => exact ha l h
  | inr h => exact hb l h

theorem Disjoint.union_right {Loc : Type} {a b c : Footprint Loc}
    (hb : Disjoint a b) (hc : Disjoint a c) :
    Disjoint a (Footprint.union b c) :=
  (Disjoint.union_left hb.symm hc.symm).symm

structure StateSpace (State Loc Val : Type) where
  read : State → Loc → Val

def AgreesOn {State Loc Val : Type} (S : StateSpace State Loc Val)
    (fp : Footprint Loc) (s s' : State) : Prop :=
  ∀ l, l ∈ fp.locs → S.read s' l = S.read s l

def WritesOnly {State Loc Val : Type} (S : StateSpace State Loc Val)
    (fp : Footprint Loc) (s s' : State) : Prop :=
  ∀ l, l ∉ fp.locs → S.read s' l = S.read s l

def InvDependsOnlyOn {State Loc Val : Type} (S : StateSpace State Loc Val)
    (Inv : State → Prop) (fp : Footprint Loc) : Prop :=
  ∀ s s', AgreesOn S fp s s' → (Inv s ↔ Inv s')

theorem AgreesOn.of_eq {State Loc Val : Type} (S : StateSpace State Loc Val)
    (fp : Footprint Loc) {s₁ s₂ : State} (h : s₁ = s₂) :
    AgreesOn S fp s₁ s₂ := by
  subst h
  exact fun _ _ => rfl

theorem AgreesOn.symm {State Loc Val : Type} {S : StateSpace State Loc Val}
    {fp : Footprint Loc} {s₁ s₂ : State} (h : AgreesOn S fp s₁ s₂) :
    AgreesOn S fp s₂ s₁ :=
  fun l hl => (h l hl).symm

theorem AgreesOn.trans {State Loc Val : Type} {S : StateSpace State Loc Val}
    {fp : Footprint Loc} {s₁ s₂ s₃ : State}
    (h₁₂ : AgreesOn S fp s₁ s₂) (h₂₃ : AgreesOn S fp s₂ s₃) :
    AgreesOn S fp s₁ s₃ :=
  fun l hl => (h₂₃ l hl).trans (h₁₂ l hl)

@[simp]
theorem agreesOn_empty {State Loc Val : Type} (S : StateSpace State Loc Val) (s s' : State) :
    AgreesOn S {} s s' := by
  intro _ hl
  cases hl

theorem WritesOnly.of_eq {State Loc Val : Type} (S : StateSpace State Loc Val)
    (fp : Footprint Loc) {s₁ s₂ : State} (h : s₁ = s₂) :
    WritesOnly S fp s₁ s₂ := by
  subst h
  exact fun _ _ => rfl

theorem WritesOnly.trans {State Loc Val : Type} {S : StateSpace State Loc Val}
    {fp : Footprint Loc} {s₁ s₂ s₃ : State}
    (h₁₂ : WritesOnly S fp s₁ s₂) (h₂₃ : WritesOnly S fp s₂ s₃) :
    WritesOnly S fp s₁ s₃ :=
  fun l hl => (h₂₃ l hl).trans (h₁₂ l hl)

theorem WritesOnly.mono_left {State Loc Val : Type} {S : StateSpace State Loc Val}
    {a b : Footprint Loc} {s s' : State} (h : WritesOnly S a s s') :
    WritesOnly S (Footprint.union a b) s s' :=
  fun l hnot => h l (fun hm => hnot (List.mem_append_left _ hm))

theorem WritesOnly.mono_right {State Loc Val : Type} {S : StateSpace State Loc Val}
    {a b : Footprint Loc} {s s' : State} (h : WritesOnly S b s s') :
    WritesOnly S (Footprint.union a b) s s' :=
  fun l hnot => h l (fun hm => hnot (List.mem_append_right _ hm))

theorem WritesOnly.seq_union {State Loc Val : Type} {S : StateSpace State Loc Val}
    {a b : Footprint Loc} {s₁ s₂ s₃ : State}
    (h₁₂ : WritesOnly S a s₁ s₂) (h₂₃ : WritesOnly S b s₂ s₃) :
    WritesOnly S (Footprint.union a b) s₁ s₃ :=
  (WritesOnly.mono_left h₁₂).trans (WritesOnly.mono_right h₂₃)

theorem writesOnly_agrees_on_disjoint {State Loc Val : Type}
    (S : StateSpace State Loc Val)
    (hostFp mixinFp : Footprint Loc)
    (hDisjoint : Disjoint hostFp mixinFp)
    (s s' : State)
    (hWrite : WritesOnly S hostFp s s') :
    AgreesOn S mixinFp s s' :=
  fun l hMixin => hWrite l (fun hHost => hDisjoint l hHost hMixin)

theorem writesOnly_preserves_other_inv {State Loc Val : Type}
    (S : StateSpace State Loc Val)
    (hostFp mixinFp : Footprint Loc)
    (hDisjoint : Disjoint hostFp mixinFp)
    (Inv : State → Prop)
    (hInv : InvDependsOnlyOn S Inv mixinFp)
    (s s' : State)
    (hWrite : WritesOnly S hostFp s s')
    (hInvS : Inv s) :
    Inv s' :=
  (hInv s s' (writesOnly_agrees_on_disjoint S hostFp mixinFp hDisjoint s s' hWrite)).mp hInvS

theorem writesOnly_seq_union_preserves_other_inv {State Loc Val : Type}
    (S : StateSpace State Loc Val)
    (fp₁ fp₂ mixinFp : Footprint Loc)
    (hDisjoint₁ : Disjoint fp₁ mixinFp)
    (hDisjoint₂ : Disjoint fp₂ mixinFp)
    (Inv : State → Prop)
    (hInv : InvDependsOnlyOn S Inv mixinFp)
    (s₁ s₂ s₃ : State)
    (h₁₂ : WritesOnly S fp₁ s₁ s₂)
    (h₂₃ : WritesOnly S fp₂ s₂ s₃)
    (hInvS : Inv s₁) :
    Inv s₃ :=
  writesOnly_preserves_other_inv S (Footprint.union fp₁ fp₂) mixinFp
    (Disjoint.union_left hDisjoint₁ hDisjoint₂) Inv hInv s₁ s₃
    (WritesOnly.seq_union h₁₂ h₂₃) hInvS

structure SpecBlock (State Loc Val : Type) (S : StateSpace State Loc Val) where
  footprint : Footprint Loc
  Inv       : State → Prop
  localized : InvDependsOnlyOn S Inv footprint

theorem SpecBlock.preserved_by_disjoint_write {State Loc Val : Type}
    {S : StateSpace State Loc Val}
    (B : SpecBlock State Loc Val S)
    (writerFp : Footprint Loc)
    (hDisjoint : Disjoint writerFp B.footprint)
    {s s' : State}
    (hWrite : WritesOnly S writerFp s s')
    (hInv : B.Inv s) :
    B.Inv s' :=
  writesOnly_preserves_other_inv S writerFp B.footprint hDisjoint B.Inv B.localized s s' hWrite hInv

theorem SpecBlock.compose_orthogonal_step {State Loc Val : Type}
    {S : StateSpace State Loc Val}
    (B₁ B₂ : SpecBlock State Loc Val S)
    (hDisjoint : Disjoint B₁.footprint B₂.footprint)
    {s₁ s₂ : State}
    (hWrite₁ : WritesOnly S B₁.footprint s₁ s₂)
    (hMaintains₁ : B₁.Inv s₁ → B₁.Inv s₂)
    (hBoth : B₁.Inv s₁ ∧ B₂.Inv s₁) :
    B₁.Inv s₂ ∧ B₂.Inv s₂ :=
  ⟨hMaintains₁ hBoth.1, B₂.preserved_by_disjoint_write B₁.footprint hDisjoint hWrite₁ hBoth.2⟩

theorem SpecBlock.compose_orthogonal_seq {State Loc Val : Type}
    {S : StateSpace State Loc Val}
    (B₁ B₂ : SpecBlock State Loc Val S)
    (hDisjoint : Disjoint B₁.footprint B₂.footprint)
    {s₀ s₁ s₂ : State}
    (hWrite₁ : WritesOnly S B₁.footprint s₀ s₁)
    (hMaintains₁ : B₁.Inv s₀ → B₁.Inv s₁)
    (hWrite₂ : WritesOnly S B₂.footprint s₁ s₂)
    (hMaintains₂ : B₂.Inv s₁ → B₂.Inv s₂)
    (hInit : B₁.Inv s₀ ∧ B₂.Inv s₀) :
    B₁.Inv s₂ ∧ B₂.Inv s₂ := by
  have hMid := SpecBlock.compose_orthogonal_step B₁ B₂ hDisjoint hWrite₁ hMaintains₁ hInit
  have hEnd := SpecBlock.compose_orthogonal_step B₂ B₁ hDisjoint.symm hWrite₂ hMaintains₂ ⟨hMid.2, hMid.1⟩
  exact ⟨hEnd.2, hEnd.1⟩

end LeanSpecs
