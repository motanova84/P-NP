import Lake
open Lake DSL

package «PvsNP» where
  -- add package configuration options here

lean_lib «PvsNP» where
  -- add library configuration options here

@[default_target]
lean_exe «pvsnp» where
  root := `Main
