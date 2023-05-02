import Lake
open Lake DSL

package «Catlib4» {
  -- add package configuration options here
}

lean_lib Catlib4 {
  -- add library configuration options here
}

/-@[default_target]
lean_exe «catlib4» {
  root := `Main
}-/

