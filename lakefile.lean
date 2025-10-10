import Lake
open Lake DSL

package «pnp» where
  -- add package configuration options here

lean_lib «PNP» where
  -- add library configuration options here

@[default_target]
lean_exe «pnp» where
  root := `Main
