import Lake
open Lake DSL

package «PvsNP» where
  -- add package configuration options here

lean_lib «PvsNP» where
  -- add library configuration options here

@[default_target]
lean_exe «pvsnp» where
  root := `Main
package PNP

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

lean_lib ComputationalDichotomy where
  roots := #[`ComputationalDichotomy]

lean_lib FormalVerification where
  roots := #[`FormalVerification]
  globs := #[.submodules `Treewidth, .submodules `Lifting, .submodules `LowerBounds]

@[default_target]
lean_exe pnp where
  root := `Director
