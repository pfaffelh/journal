import Lake
open Lake DSL

package Journal {
  -- optional: project-specific configuration
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib Journal {
  -- hier landen deine sauberen Module
}

@[default_target]
lean_exe journal where
  srcDir := "./"
  root := `Main
