import LeanSpecs.MetaSpec

namespace LeanSpecs

structure SubspecCorollary (Impl : Type)
    (CoreSpec Subspec : Impl → Prop) where
  entails : ∀ impl, CoreSpec impl → Subspec impl

theorem SubspecCorollary.contrapositive {Impl : Type}
    {CoreSpec Subspec : Impl → Prop}
    (C : SubspecCorollary Impl CoreSpec Subspec)
    {mutant : Impl} (hViolates : ¬ Subspec mutant) :
    ¬ CoreSpec mutant :=
  fun hCore => hViolates (C.entails mutant hCore)

structure CveSubspec (Impl : Type)
    (CoreSpec ExploitReachable : Impl → Prop) where
  cveId         : String
  no_exploit    : ∀ impl, CoreSpec impl → ¬ ExploitReachable impl
  cveMutant     : Impl
  mutant_buggy  : ExploitReachable cveMutant

theorem CveSubspec.kills_cve_mutant {Impl : Type}
    {CoreSpec ExploitReachable : Impl → Prop}
    (S : CveSubspec Impl CoreSpec ExploitReachable) :
    ¬ CoreSpec S.cveMutant :=
  fun hCore => S.no_exploit S.cveMutant hCore S.mutant_buggy

theorem CveSubspec.reference_ne_cve_mutant {Impl : Type}
    {CoreSpec ExploitReachable : Impl → Prop}
    (S : CveSubspec Impl CoreSpec ExploitReachable)
    {reference : Impl} (hRef : CoreSpec reference) :
    reference ≠ S.cveMutant := by
  intro hEq
  rw [hEq] at hRef
  exact S.kills_cve_mutant hRef

structure CveBacktestSuite (Impl : Type) (CoreSpec : Impl → Prop) where
  reference      : Impl
  reference_ok   : CoreSpec reference
  verifiedCveIds : List String
  killedMutants  : List Impl
  all_killed     : ∀ m, m ∈ killedMutants → ¬ CoreSpec m

theorem CveBacktestSuite.reference_not_in_killed {Impl : Type} {CoreSpec : Impl → Prop}
    (B : CveBacktestSuite Impl CoreSpec) :
    B.reference ∉ B.killedMutants :=
  fun hMem => B.all_killed B.reference hMem B.reference_ok

structure SpecEquivalence (Impl : Type) (OldSpec NewSpec : Impl → Prop) where
  iff_equiv : ∀ impl, OldSpec impl ↔ NewSpec impl

theorem SpecEquivalence.preserves_subspec {Impl : Type}
    {OldSpec NewSpec Subspec : Impl → Prop}
    (E : SpecEquivalence Impl OldSpec NewSpec)
    (hOld : ∀ impl, OldSpec impl → Subspec impl) :
    ∀ impl, NewSpec impl → Subspec impl :=
  fun impl hNew => hOld impl ((E.iff_equiv impl).mpr hNew)

def SpecEquivalence.transportCveSubspec {Impl : Type}
    {OldSpec NewSpec ExploitReachable : Impl → Prop}
    (E : SpecEquivalence Impl OldSpec NewSpec)
    (S : CveSubspec Impl OldSpec ExploitReachable) :
    CveSubspec Impl NewSpec ExploitReachable where
  cveId := S.cveId
  no_exploit := fun impl hNew => S.no_exploit impl ((E.iff_equiv impl).mpr hNew)
  cveMutant := S.cveMutant
  mutant_buggy := S.mutant_buggy

theorem SpecEquivalence.transportCveSubspec_kills_mutant {Impl : Type}
    {OldSpec NewSpec ExploitReachable : Impl → Prop}
    (E : SpecEquivalence Impl OldSpec NewSpec)
    (S : CveSubspec Impl OldSpec ExploitReachable) :
    ¬ NewSpec S.cveMutant :=
  (E.transportCveSubspec S).kills_cve_mutant

structure ControlledSpecRelaxation (Impl : Type)
    (OldSpec NewSpec ExternalPromise : Impl → Prop) where
  preserves_promise   : ∀ impl, NewSpec impl → ExternalPromise impl
  killedMutants       : List Impl
  kills_all_prior     : ∀ m, m ∈ killedMutants → ¬ NewSpec m
  newlyAdmittedWitness : Impl
  newly_admitted_ok   : NewSpec newlyAdmittedWitness
  previously_blocked  : ¬ OldSpec newlyAdmittedWitness

theorem ControlledSpecRelaxation.strictly_separates_witness {Impl : Type}
    {OldSpec NewSpec ExternalPromise : Impl → Prop}
    (R : ControlledSpecRelaxation Impl OldSpec NewSpec ExternalPromise) :
    ExternalPromise R.newlyAdmittedWitness ∧ ¬ OldSpec R.newlyAdmittedWitness :=
  ⟨R.preserves_promise R.newlyAdmittedWitness R.newly_admitted_ok, R.previously_blocked⟩

theorem ControlledSpecRelaxation.witness_not_in_killed {Impl : Type}
    {OldSpec NewSpec ExternalPromise : Impl → Prop}
    (R : ControlledSpecRelaxation Impl OldSpec NewSpec ExternalPromise) :
    R.newlyAdmittedWitness ∉ R.killedMutants :=
  fun hMem => R.kills_all_prior R.newlyAdmittedWitness hMem R.newly_admitted_ok

end LeanSpecs
