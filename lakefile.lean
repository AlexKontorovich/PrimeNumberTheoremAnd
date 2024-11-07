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
  "https://github.com/leanprover-community/mathlib4.git" @ "e348a4c"

require EulerProducts from git
  "https://github.com/MichaelStollBayreuth/EulerProducts.git" @ "757d816"

meta if get_config? env = some "dev" then require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "b6ae1cf"
