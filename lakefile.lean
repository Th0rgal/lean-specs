import Lake
open Lake DSL

package «lean-specs» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

@[default_target]
lean_lib «LeanSpecs» where
  globs := #[.andSubmodules `LeanSpecs]
  precompileModules := false

@[default_target]
lean_exe «lean-specs-test» where
  root := `LeanSpecs.Examples
  supportInterpreter := false
