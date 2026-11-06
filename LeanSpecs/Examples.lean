import LeanSpecs.Core
import LeanSpecs.Composition
import LeanSpecs.MetaSpec
import LeanSpecs.Subspec
import LeanSpecs.HashDomain

namespace LeanSpecs.Examples

inductive VaultSlot where
  | balances (acct : Nat)
  | totalSupply
  | paused
  deriving Repr, DecidableEq

structure VaultState where
  bal0        : Nat
  bal1        : Nat
  totalSupply : Nat
  paused      : Bool
  auditCount  : Nat
  deriving Repr, DecidableEq

def vaultSpace : StateSpace VaultState VaultSlot Nat where
  read s slot :=
    match slot with
    | .balances 0 => s.bal0
    | .balances 1 => s.bal1
    | .balances _ => 0
    | .totalSupply => s.totalSupply
    | .paused => if s.paused then 1 else 0

def accountingBlock : SpecBlock VaultState VaultSlot Nat vaultSpace where
  footprint := { locs := [.balances 0, .balances 1, .totalSupply] }
  Inv s := s.bal0 + s.bal1 = s.totalSupply
  localized s s' hAgree := by
    have h0 : s'.bal0 = s.bal0 := hAgree (.balances 0) (by simp)
    have h1 : s'.bal1 = s.bal1 := hAgree (.balances 1) (by simp)
    have ht : s'.totalSupply = s.totalSupply := hAgree .totalSupply (by simp)
    simp [h0, h1, ht]

def pauseBlock : SpecBlock VaultState VaultSlot Nat vaultSpace where
  footprint := { locs := [.paused] }
  Inv s := s.paused = false
  localized s s' hAgree := by
    have hp := hAgree .paused (by simp)
    dsimp [vaultSpace] at hp
    cases hp1 : s.paused <;> cases hp2 : s'.paused <;> simp_all

theorem accounting_disjoint_pause :
    Disjoint accountingBlock.footprint pauseBlock.footprint := by
  intro l hl hp
  simp [accountingBlock, pauseBlock] at hl hp
  rcases hl with rfl | rfl | rfl <;> cases hp

def transfer0to1 (amt : Nat) (s : VaultState) : VaultState :=
  if amt ≤ s.bal0 then
    { s with bal0 := s.bal0 - amt, bal1 := s.bal1 + amt, auditCount := s.auditCount + 1 }
  else
    s

theorem transfer0to1_writes_accounting (amt : Nat) (s : VaultState) :
    WritesOnly vaultSpace accountingBlock.footprint s (transfer0to1 amt s) := by
  intro l hNot
  unfold transfer0to1
  split
  · cases l with
    | balances acct =>
      match acct with
      | 0 => exact False.elim (hNot (by simp [accountingBlock]))
      | 1 => exact False.elim (hNot (by simp [accountingBlock]))
      | _ + 2 => rfl
    | totalSupply => exact False.elim (hNot (by simp [accountingBlock]))
    | paused => rfl
  · rfl

def vaultObs : ObsQuotient VaultState (Nat × Nat × Nat × Bool) where
  observe s := (s.bal0, s.bal1, s.totalSupply, s.paused)

theorem audit_counter_elision_refines (s : VaultState) :
    vaultObs.Equiv { s with auditCount := 0 } { s with auditCount := s.auditCount + 1 } :=
  rfl

structure DebitInput where
  balance : Nat
  debit   : Nat
  deriving Repr, DecidableEq

def debitSafe (x : DebitInput) : Prop :=
  x.debit ≤ x.balance

def debitGateSpec : MetaGateSpec DebitInput debitSafe where
  gate x := decide (x.debit ≤ x.balance)
  sound x h := by
    unfold debitSafe
    exact of_decide_eq_true h
  complete x h := by
    unfold debitSafe at h
    exact decide_eq_true h
  posWitness := ⟨100, 40⟩
  negWitness := ⟨40, 100⟩
  nonVacuous := rfl
  tight := rfl

abbrev DebitImpl := DebitInput → Option Nat

def CoreDebitSpec (impl : DebitImpl) : Prop :=
  ∀ x,
    (x.debit ≤ x.balance → impl x = some (x.balance - x.debit)) ∧
    (x.balance < x.debit → impl x = none)

def refDebitImpl : DebitImpl :=
  fun x => if x.debit ≤ x.balance then some (x.balance - x.debit) else none

theorem refDebitImpl_satisfies_core : CoreDebitSpec refDebitImpl := by
  intro x
  unfold refDebitImpl
  constructor
  · intro hLe
    simp [hLe]
  · intro hLt
    have hNot : ¬ x.debit ≤ x.balance := by omega
    simp [hNot]

def saturatingUnderflowExploit (impl : DebitImpl) : Prop :=
  ∃ x, x.balance < x.debit ∧ impl x = some 0

def saturatingMutant : DebitImpl :=
  fun x => some (x.balance - x.debit)

def cveUnderflowSubspec : CveSubspec DebitImpl CoreDebitSpec saturatingUnderflowExploit where
  cveId := "CVE-EXAMPLE-SATURATING-SUB"
  no_exploit impl hCore := by
    rintro ⟨x, hLt, hSome⟩
    have hNone := (hCore x).2 hLt
    rw [hNone] at hSome
    cases hSome
  cveMutant := saturatingMutant
  mutant_buggy := ⟨⟨10, 25⟩, by decide, rfl⟩

def debitBacktestSuite : CveBacktestSuite DebitImpl CoreDebitSpec where
  reference := refDebitImpl
  reference_ok := refDebitImpl_satisfies_core
  verifiedCveIds := [cveUnderflowSubspec.cveId]
  killedMutants := [cveUnderflowSubspec.cveMutant]
  all_killed m hm := by
    simp at hm
    subst hm
    exact cveUnderflowSubspec.kills_cve_mutant

def ExternalSolvencyPromise (impl : DebitImpl) : Prop :=
  ∀ x,
    (x.debit ≤ x.balance → ∃ r, impl x = some r ∧ r ≤ x.balance - x.debit) ∧
    (x.balance < x.debit → impl x = none)

def FeeAwareDebitSpec (impl : DebitImpl) : Prop :=
  ∀ x,
    (x.debit + 1 ≤ x.balance → impl x = some (x.balance - x.debit - 1)) ∧
    (x.debit = x.balance → impl x = some 0) ∧
    (x.balance < x.debit → impl x = none)

def RelaxedDebitSpec (impl : DebitImpl) : Prop :=
  CoreDebitSpec impl ∨ FeeAwareDebitSpec impl

def feeDebitImpl : DebitImpl :=
  fun x =>
    if x.debit + 1 ≤ x.balance then some (x.balance - x.debit - 1)
    else if x.debit = x.balance then some 0
    else none

theorem feeDebitImpl_satisfies_fee : FeeAwareDebitSpec feeDebitImpl := by
  intro x
  unfold feeDebitImpl
  refine ⟨?_, ?_, ?_⟩
  · intro hLe
    simp [hLe]
  · intro hEq
    simp [hEq]
  · intro hLt
    have hNot1 : ¬ x.debit + 1 ≤ x.balance := by omega
    have hNot2 : x.debit ≠ x.balance := by omega
    simp [hNot1, hNot2]

def debitFeeRelaxation :
    ControlledSpecRelaxation DebitImpl CoreDebitSpec RelaxedDebitSpec ExternalSolvencyPromise where
  preserves_promise impl hNew x := by
    rcases hNew with hCore | hFee
    · refine ⟨?_, (hCore x).2⟩
      intro hLe
      exact ⟨x.balance - x.debit, (hCore x).1 hLe, Nat.le_refl _⟩
    · refine ⟨?_, (hFee x).2.2⟩
      intro hLe
      by_cases hStrict : x.debit + 1 ≤ x.balance
      · exact ⟨x.balance - x.debit - 1, (hFee x).1 hStrict, by omega⟩
      · have hEq : x.debit = x.balance := by omega
        exact ⟨0, (hFee x).2.1 hEq, by omega⟩
  killedMutants := [saturatingMutant]
  kills_all_prior m hm := by
    simp at hm
    subst hm
    rintro (hCore | hFee)
    · exact cveUnderflowSubspec.kills_cve_mutant hCore
    · have hNone := (hFee ⟨10, 25⟩).2.2 (by decide)
      unfold saturatingMutant at hNone
      cases hNone
  newlyAdmittedWitness := feeDebitImpl
  newly_admitted_ok := Or.inr feeDebitImpl_satisfies_fee
  previously_blocked hCore := by
    have hExact := (hCore ⟨10, 4⟩).1 (by decide)
    unfold feeDebitImpl at hExact
    simp at hExact

def toyModHash (k : Nat) : Nat := k % 4

def toyCollisionFreeSpec : MetaGateSpec (List Nat) (CollisionFreeOn toyModHash) where
  gate keys := checkCollisionFreeOn toyModHash keys
  sound keys h := (checkCollisionFreeOn_iff toyModHash keys).mp h
  complete keys h := (checkCollisionFreeOn_iff toyModHash keys).mpr h
  posWitness := [1, 2, 3]
  negWitness := [1, 5]
  nonVacuous := rfl
  tight := rfl

def extractNonZeroFlag (raw : Nat) : Bool := raw != 0

def boolTruePolicyGate : MetaGateSpec Bool (fun b => b = true) where
  gate b := b
  sound _ h := h
  complete _ h := h
  posWitness := true
  negWitness := false
  nonVacuous := rfl
  tight := rfl

def demoRoutingGate : RoutingGateSpec Nat Bool extractNonZeroFlag (fun b => b = true) where
  policyGate := boolTruePolicyGate
  rawSafeWitness := 7
  rawBadWitness := 0
  raw_nonVacuous := rfl
  raw_tight := rfl

def extractLowByteNonZero (raw : Nat) : Bool := (raw % 256) != 0

def spoofedRoutingGate : RoutingGateSpec Nat Bool extractLowByteNonZero (fun b => b = true) where
  policyGate := boolTruePolicyGate
  rawSafeWitness := 7
  rawBadWitness := 0
  raw_nonVacuous := rfl
  raw_tight := rfl

theorem spoofedRoutingGate_admits_high_bit_payload :
    spoofedRoutingGate.eval 257 = true ∧ ¬ (257 < 256) :=
  spoofedRoutingGate.extractor_spoof_breaks_raw_safety (fun raw => raw < 256) 257
    (by decide) rfl

end LeanSpecs.Examples

def main : IO UInt32 := do
  let g := LeanSpecs.Examples.debitGateSpec
  if !(g.gate g.posWitness && !g.gate g.negWitness) then
    IO.eprintln "FAIL: debitGateSpec witness check failed"
    return 1
  let h := LeanSpecs.Examples.toyCollisionFreeSpec
  if !(h.gate h.posWitness && !h.gate h.negWitness) then
    IO.eprintln "FAIL: toyCollisionFreeSpec witness check failed"
    return 1
  for keys in [[], [1], [1, 1], [1, 2, 1], [1, 5], [5, 1], [0, 1, 4]] do
    let oracle := keys.all fun x => keys.all fun y =>
      x == y || LeanSpecs.Examples.toyModHash x != LeanSpecs.Examples.toyModHash y
    if h.gate keys != oracle then
      IO.eprintln s!"FAIL: hash checker differs from all-pairs oracle on {keys}"
      return 1
  let rg := LeanSpecs.Examples.demoRoutingGate
  if !(rg.eval rg.rawSafeWitness && !rg.eval rg.rawBadWitness) then
    IO.eprintln "FAIL: demoRoutingGate witness check failed"
    return 1
  let sg := LeanSpecs.Examples.spoofedRoutingGate
  if !(sg.eval 257 && !(257 < 256)) then
    IO.eprintln "FAIL: spoofedRoutingGate TCB demonstration failed"
    return 1
  let r0 := LeanSpecs.Examples.refDebitImpl ⟨10, 25⟩
  let m0 := LeanSpecs.Examples.saturatingMutant ⟨10, 25⟩
  if !(r0 == none && m0 == some 0) then
    IO.eprintln "FAIL: CVE mutant separation check failed"
    return 1
  IO.println ("lean-specs self-test: MetaGateSpec, HashDomain, RoutingGateSpec, " ++
    "SpecBlock orthogonality, ObsQuotient, and CveSubspec checks passed")
  return 0
