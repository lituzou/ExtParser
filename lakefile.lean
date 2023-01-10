import Lake
open Lake DSL

package extParser {
  -- add package configuration options here
}

lean_lib ExtParser {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe extParser {
  root := `Main
}
