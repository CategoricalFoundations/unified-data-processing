import Lake
open Lake DSL

package «categorical-data-processing» where
  -- Minimal configuration for Lean 4.3.0 compatibility

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0"

@[default_target]
lean_lib «CategoricalDataProcessing» where
  roots := #[`Nexus]
  globs := #[.submodules `CategoricalDataProcessing]

lean_lib Categories where
  roots := #[`Categories]

lean_lib Adjunctions where
  roots := #[`Adjunctions]

lean_lib KanExtensions where
  roots := #[`KanExtensions]

lean_lib DeltaUniqueness where
  roots := #[`DeltaUniqueness]

lean_lib ZRelations where
  roots := #[`ZRelations]

lean_lib CorrectionMonad where
  roots := #[`CorrectionMonad]

lean_lib Utilities where
  roots := #[`Utilities]
