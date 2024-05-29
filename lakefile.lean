import Lake
open Lake DSL

package «PrimeNumberTheoremAnd» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «PrimeNumberTheoremAnd»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require EulerProducts from git
  "https://github.com/MichaelStollBayreuth/EulerProducts.git" @ "main"

meta if get_config? env = some "dev" then require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "main"
