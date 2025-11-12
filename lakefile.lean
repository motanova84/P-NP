import Lake
open Lake DSL

package «pnp» where
  -- add package configuration options here

lean_lib «PNP» where
  -- add library configuration options here

@[default_target]
lean_exe «pnp» where
  root := `Main
package PNP

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

lean_lib ComputationalDichotomy where
  roots := #[`ComputationalDichotomy]

lean_lib FormalVerification where
  roots := #[`FormalVerification]
  globs := #[.submodules `Treewidth, .submodules `Lifting, .submodules `LowerBounds]

lean_lib Formal where
  roots := #[`Formal]

@[default_target]
lean_exe pnp where
  root := `Director
