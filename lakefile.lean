import Lake
open Lake DSL

package "lightblue-lean" where
  -- add package configuration options here

lean_lib «LightblueLean» where
  -- add library configuration options here

@[default_target]
lean_exe "lightblue-lean" where
  root := `Main
