import Lake
open Lake DSL

package «PrimeNumberTheoremAnd»

@[default_target]
lean_lib «PrimeNumberTheoremAnd»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "aa79ce0"

require EulerProducts from git
  "https://github.com/MichaelStollBayreuth/EulerProducts.git" @ "751e411"

meta if get_config? env = some "dev" then require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "780bbec"
