import Lake
open Lake DSL

package «math» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

-- Validation target for checking submission files
@[default_target]
lean_lib Validate where
  srcDir := "."
  roots := #[`Validate]
