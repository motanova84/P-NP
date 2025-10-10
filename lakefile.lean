import Lake
open Lake DSL

package PNP

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

lean_lib ComputationalDichotomy where
  roots := #[`ComputationalDichotomy]

@[default_target]
lean_exe pnp where
  root := `Principal
