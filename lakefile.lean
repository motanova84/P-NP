import Lake
open Lake DSL

package PNP

-- Dependencia esencial: Mathlib4
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

@[default_target]
lean_lib PNP where
  globs := #[.submodules `PNP]
