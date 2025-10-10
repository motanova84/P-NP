import Lake
open Lake DSL

package pnp

-- Mathlib4 dependency (compatible with Lean 4.12.0)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

lean_lib ComputationalDichotomy where
  -- add library configuration options here
  roots := #[`ComputationalDichotomy]

@[default_target]
lean_exe pnp where
  root := `Main
