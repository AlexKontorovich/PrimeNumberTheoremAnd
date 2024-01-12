import Lake
open Lake DSL

package «PrimeNumberTheoremAnd» where
  -- add package configuration options here

lean_lib «PrimeNumberTheoremAnd» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"e659b1b"

meta if get_config? env = some "dev" then require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "29f7f43"

@[default_target]
lean_exe «primenumbertheoremand» where
  root := `Main
