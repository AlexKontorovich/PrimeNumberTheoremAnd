module

public import RHHeight.ExactArgument
public import RHHeight.LowHeight
public import RHHeight100.Skeleton100
public import RHHeight100.GammaIncrement100
public import RHHeight100.HorizontalLegs100
public import RHHeight100.TwentyNineZeros

@[expose] public section

/-!
# Hunt #137 (`rh_height_lean`), second target: RH with simplicity to height 100

`RHHeight100.rh_height_hundred : RHHeight100`: every zero `ρ` of Mathlib's `riemannZeta` with
`0 < Re ρ < 1` and `0 < Im ρ ≤ 100` has `Re ρ = 1/2` and analytic order `1`; and
`RHHeight100.zero_count_hundred : ZeroCountUpTo 100 29`, exactly 29 distinct such zeros.

The pieces, as `Prop`s in `RHHeight100/Skeleton100.lean`:

* `GammaIncrement100` by `gamma_increment100` (`RHHeight100/GammaIncrement100.lean`):
  `28.1 ≤ ∫_3^100 μ ≤ 29.7`, from the vendored `digamma_stirling`;
* `HorizontalLegs100` by `horizontalLegs100` (`RHHeight100/HorizontalLegs100.lean`): `Re ζ > 0`
  on `[1/2, 2] + 3i` and `[1/2, 2] + 100i`, both left-end arguments in `[-1/5, 0]`;
* `ExactArgument` and `LowHeight` by the height-50 proof's `exact_argument_holds` and
  `low_height`, unchanged;
* `TwentyNineZerosOnLine` by `twenty_nine_zeros_on_line_below_hundred`
  (`RHHeight100/TwentyNineZeros.lean`): hunt #133's ten zeros and nineteen more located by
  the generated files `RHHeight100/Box*.lean`.

The enclosures put the count of zeros with `3 < Im ρ ≤ 100` in `(28, 30)`, so it is `29`; the
twenty-nine distinct zeros on the line lie in that window, so they are all of its zeros, each
simple; `LowHeight` covers `0 < Im ρ ≤ 3`.

**What this does not say.** Nothing above height 100 and nothing about the Riemann
hypothesis (`docs/08`). Height 100 is above the Davenport-Heilbronn function's first off-line
zero (height 85.699, `hunts/rh_height_lean/MISSION.md`), so unlike the height-50 statement this
one is false for that function; it is still a statement about finitely many zeros.
-/

namespace RHHeight100

open RHHeight

/-- **The count on the contour**: exactly 29 zeros of `riemannZeta`, counted with multiplicity
(`Zeta23.Ncount`), with `0 < Re ρ < 1` and `3 < Im ρ ≤ 100`. -/
theorem ncount_three_hundred : Zeta23.Ncount 3 100 = 29 :=
  count_eq_twenty_nine_of gamma_increment100 horizontalLegs100 exact_argument_holds

/-- **The second target of hunt #137.** Every zero `ρ` of Mathlib's `riemannZeta` with
`0 < Re ρ < 1` and `0 < Im ρ ≤ 100` has `Re ρ = 1/2` and analytic order exactly `1`. -/
theorem rh_height_hundred : RHHeight100 :=
  rhUpToHeight100_of_pieces gamma_increment100 horizontalLegs100 exact_argument_holds
    low_height twenty_nine_zeros_on_line_below_hundred

/-- **Exactly 29 zeros** of `riemannZeta` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 100`
(distinct zeros; each is simple by `rh_height_hundred`). -/
theorem zero_count_hundred : ZeroCountUpTo 100 29 :=
  zeroCount100_of_pieces gamma_increment100 horizontalLegs100 exact_argument_holds
    low_height twenty_nine_zeros_on_line_below_hundred

end RHHeight100
