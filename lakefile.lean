import Lake
open Lake DSL

package pnp where
  -- add package configuration options here

-- Mathlib4 dependency for graph theory and combinatorics
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib ComputationalDichotomy where
  -- add library configuration options here
  roots := #[`ComputationalDichotomy]

@[default_target]
lean_exe pnp where
  root := `Main
