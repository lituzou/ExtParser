import Lake
open Lake DSL

package extParser {
  -- add package configuration options here
}

lean_lib ExtParser {
  -- add library configuration options here
}

@[default_target]
lean_exe extParser {
  root := `Main
}
