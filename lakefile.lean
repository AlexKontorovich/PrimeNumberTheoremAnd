import Lake
open Lake DSL

package «PrimeNumberTheoremAnd»

@[default_target]
lean_lib «PrimeNumberTheoremAnd»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "4921260"

require EulerProducts from git
  "https://github.com/MichaelStollBayreuth/EulerProducts.git" @ "1ff0d26"

meta if get_config? env = some "dev" then require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "780bbec"
