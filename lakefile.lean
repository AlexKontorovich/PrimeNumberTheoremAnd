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

--
-- DO NOT REPLACE WITH '@ "master"': the pace of development of mathlib is too
-- fast for us to keep up. If you need to bump the version of mathlib, change
-- the commit to a more recent one.
--
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d5ab93e3a3afadaf265a583a92f7e7c47203b540"

require EulerProducts from git
  "https://github.com/MichaelStollBayreuth/EulerProducts.git" @ "51a29f3"

meta if get_config? env = some "dev" then require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "v4.13.0"
