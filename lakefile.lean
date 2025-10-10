import Lake
open Lake DSL

package pnp where
  -- add package configuration options here

lean_lib ComputationalDichotomy where
  -- add library configuration options here
  roots := #[`ComputationalDichotomy]

@[default_target]
lean_exe pnp where
  root := `Main
