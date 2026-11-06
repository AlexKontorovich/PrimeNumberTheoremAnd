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
