import Lake
open Lake DSL

package extParser {
  -- add package configuration options here
}

lean_lib ExtParser {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "28c23e3c3744968baf25c65dadf7a117ec087dce"

@[default_target]
lean_exe extParser {
  root := `Main
}
