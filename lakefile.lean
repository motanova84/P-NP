import Lake
open Lake DSL

package pnp

-- Dependencia de Mathlib4 (ajustada a Lean 4.10.0–4.12.0)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

lean_lib ComputationalDichotomy where
  -- add library configuration options here
  roots := #[`ComputationalDichotomy]

@[default_target]
lean_exe pnp where
  root := `Main
