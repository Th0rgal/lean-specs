# `lean-specs` — Reusable 4-Layer Formal Specification Combinators for Lean 4

> **Status: Archived / Retired (Via Negativa).** `lean-specs` is retired in favor of writing plain, idiomatic Lean 4 specifications directly inside downstream domain repositories—following the `formal-specs` methodology and auditing theorems directly with [`turbo-lean audit-spec`](https://github.com/Th0rgal/turbo-lean)—rather than coupling projects to a shared specification-combinator wrapper library. Existing modules, proofs, and commit history remain intact for historical provenance and reference.

`Th0rgal/lean-specs` is a zero-dependency, zero-FFI Lean 4 library (`0 import Lean`, `0 sorryAx`, `0 native_decide`, compatible across Lean `v4.31.0..v4.35.0`) providing reusable specification combinators for human-auditable formal verification, composable protocol invariants, two-sided CVE regression subspecs, and machine-checked specification evolution.

Every theorem in `LeanSpecs` is audited by [`Th0rgal/turbo-lean`](https://github.com/Th0rgal/turbo-lean) (`76/76 non_vacuous_and_tight`, `0` vacuous, `0` trivial, `0` droppable hypotheses).

## 4-Layer Specification Architecture

1. **Layer 1 — Minimal Human-Auditable Core Spec (`LeanSpecs.Core`)**:
   - `Result ε σ α`, `SpecM σ ε α` (`bind_pure`, `pure_bind`, `bind_assoc`, `atomicRollback_err_preserves_state`), `Costed α`.
   - `ObsQuotient State Obs` and `ObsAndCostRefinement State Obs`: specify systems up to observable state quotients (`observe s₁ = observe s₂`) rather than internal representation layout, leaving internal caches, arenas, and non-observable counters free for optimization.
2. **Layer 2 — Composable Spec Blocks & Disjoint Footprints (`LeanSpecs.Composition`)**:
   - `Footprint Loc`, `Disjoint`, `StateSpace State Loc Val`, `AgreesOn`, `WritesOnly`, `InvDependsOnlyOn`, and `SpecBlock`.
   - Orthogonality theorems (`writesOnly_preserves_other_inv`, `SpecBlock.preserved_by_disjoint_write`, `SpecBlock.compose_orthogonal_step`, `SpecBlock.compose_orthogonal_seq`) compose independent subsystem invariants without quadratic cross-invariant proof blowup.
3. **Layer 3 — Two-Sided CVE & Regression Subspecs (`LeanSpecs.Subspec`)**:
   - Keep Layer 1 minimal and push historical bugs, exploit classes, and edge-case regressions into derived subspecs (`SubspecCorollary`, `CveSubspec`, `CveBacktestSuite`).
   - Every `CveSubspec` proves **two sides** inside the Lean kernel:
     1. **Deductive prevention**: `∀ impl, CoreSpec impl → ¬ ExploitReachable impl`
     2. **Mutant refutation**: an explicit defective `cveMutant : Impl` satisfying `ExploitReachable cveMutant`, deriving `¬ CoreSpec cveMutant` (`CveSubspec.kills_cve_mutant`).
   - Safe spec evolution combinators: `SpecEquivalence` (`S ↔ S'` with automatic `transportCveSubspec`) and 4-gate `ControlledSpecRelaxation` (`NewSpec → ExternalPromise`, survival of all prior `killedMutants`, and strict witness separation `NewSpec w ∧ ¬ OldSpec w`).
4. **Layer 4 — Meta-Specs & Speculative Gate Contracts (`LeanSpecs.MetaSpec`)**:
   - `MetaGateSpec` (sound + complete boolean decision procedure with positive and negative witnesses), `MetaAlgorithmSpec` (oracle equivalence + step bound), `JointSatisfiableSpec` (multi-clause inhabitance witness), `NonVacuousSpec`, `HypothesisMinimalWitness`, `FrameInvariant`, `ExactDeltaSpec`, `OutcomePartitionSpec`, `AccountingBoundarySpec`, `OrderIndependence`, `WitnessRefuter`, `MutantKillBundle`, `ClauseIndependenceWitness`.
   - Speculative verification & translation-validation combinators (`evalWithSpeculativeGate`, `speculativeGate_sound_eq`, `evalWithVerifiedTransform`, `verifiedTransform_refines`).
   - Finite-footprint hash domain & TCB-explicit routing gates (`LeanSpecs.HashDomain`): `CollisionFreeOn` + `checkCollisionFreeOn` (`checkCollisionFreeOn_iff`), constructive finite pigeonhole impossibility proofs explaining why global non-injective compression cannot be asserted universally (`universal_fin2_footprint_forces_global_injective`, `no_global_injective_fin_succ`, `no_global_injective_fin_gt`, `no_global_pair_hash_injective`), and `RoutingGateSpec` exposing `extractInTcb : Raw → Flags` inside the trusted computing base (`eval_iff_extracted_policy`, `sound_for_raw_of_faithful_extractor`, `extractor_spoof_breaks_raw_safety`).

## Adding `lean-specs` to a Lake Project

In `lakefile.lean`:

```lean
require «lean-specs» from git
  "https://github.com/Th0rgal/lean-specs.git" @ "main"
```

Or in `lakefile.toml`:

```toml
[[require]]
name = "lean-specs"
git = "https://github.com/Th0rgal/lean-specs.git"
rev = "main"
```

## Verification

```bash
lake build
./.lake/build/bin/lean-specs-test
turbo-lean --json ci-verify --project-dir .
turbo-lean --json audit-spec LeanSpecs/Core.lean LeanSpecs/Composition.lean LeanSpecs/MetaSpec.lean LeanSpecs/Subspec.lean LeanSpecs/HashDomain.lean LeanSpecs/Examples.lean
```

## License

Apache-2.0
