import Lake
open Lake DSL

package RSBounds

require TernaryGoldbach from git
  "https://github.com/calr3/ternary-goldbach.git" @
  "ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0"

@[default_target] lean_lib RSBounds where
  globs := #[.one `RSBounds]

lean_lib RSTotientChallenge where
  srcDir := "comparator"

lean_lib RSTotientSolution where
  srcDir := "comparator"

lean_lib RSZeroCountChallenge where
  srcDir := "comparator"

lean_lib RSZeroCountSolution where
  srcDir := "comparator"

-- Exact, checked 99-module dependency closure of RHHeight100.Main100.
-- The pinned upstream sources and adaptations are recorded under vendor/rh100.
lean_lib Zeta23 where
  srcDir := "vendor/rh100"
  globs := #[.submodules `Zeta23]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

lean_lib ZetaLean where
  srcDir := "vendor/rh100"
  globs := #[.submodules `ZetaLean]

lean_lib RHHeight where
  srcDir := "vendor/rh100"
  globs := #[.submodules `RHHeight]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib RHHeight100 where
  srcDir := "vendor/rh100"
  globs := #[.submodules `RHHeight100]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib HardyFirstZero where
  srcDir := "vendor/rh100"
  globs := #[.submodules `HardyFirstZero]

lean_lib HardyTenZeros where
  srcDir := "vendor/rh100"
  globs := #[.submodules `HardyTenZeros]
