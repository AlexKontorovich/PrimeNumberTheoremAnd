module

public import RHHeight.Skeleton
public import RHHeight.LegsBottom
public import RHHeight.LegsTop1
public import RHHeight.LegsTop2
public import RHHeight.LegsArg

@[expose] public section

/-!
# The piece `horizontal_legs` of hunt #137: `Re ζ > 0` on both horizontal legs

`RHHeight.HorizontalLegs` (`RHHeight/Skeleton.lean`) asks for four facts about Mathlib's
`riemannZeta`: `Re ζ(σ + 3i) > 0` and `Re ζ(σ + 52i) > 0` for every `σ ∈ [1/2, 2]`, and
`-1/5 ≤ arg ζ(1/2 + 3i) ≤ 0`, `-1/3 ≤ arg ζ(1/2 + 52i) ≤ 0`. This file proves them, as
`horizontal_legs`, from:

* `RHHeight/LegSupport.lean`: the general analysis. On a segment `[a, b] + iy` the order-4
  main term `M_N` moves by at most `(σ - a) L` from its value at the left end
  (`norm_mainTerm_sub_le`), hunt #132's remainder `zeta_em4_error` is bounded uniformly
  (`norm_zeta_sub_mainTerm_le`), and `re_pos_of_segment` concludes `Re ζ > 0` on the whole
  segment from one table of term boxes at `a + iy` and one rational inequality;
* the generated files `RHHeight/LegsBottom.lean` (three segments at height 3, all `N = 2`),
  `RHHeight/LegsTop1.lean` and `RHHeight/LegsTop2.lean` (six segments at height 52,
  `N = 12, 12, 12, 10, 10, 10`) and `RHHeight/LegsArg.lean` (boxes for `ζ(1/2 + 3i)` at
  `N = 4` and `ζ(1/2 + 52i)` at `N = 28`), every literal and every inequality decided by the
  kernel.

The segments, their truncations and the generator are `hunts/rh_height_lean/gen_legs.py`.
-/

open Complex

namespace RHHeight

open RHHeight.Legs

private lemma cast_le_of_le {q : ℚ} {r : ℝ} {σ : ℝ} (hq : ((q : ℚ) : ℝ) = r) (h : r ≤ σ) :
    ((q : ℚ) : ℝ) ≤ σ := hq ▸ h

private lemma le_cast_of_le {q : ℚ} {r : ℝ} {σ : ℝ} (hq : ((q : ℚ) : ℝ) = r) (h : σ ≤ r) :
    σ ≤ ((q : ℚ) : ℝ) := hq ▸ h

/-- **`Re ζ > 0` on the bottom leg** `[1/2, 2] + 3i`. -/
theorem re_zeta_pos_bottom : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 3 * I)).re := by
  intro σ hσ
  obtain ⟨h1, h2⟩ := hσ
  have e : ((3 : ℚ) : ℂ) = 3 := by norm_num
  rcases le_or_gt σ (43 / 64) with ha | ha
  · have h := Legs.H3S1.seg σ (cast_le_of_le (by norm_num) h1) (le_cast_of_le (by norm_num) ha)
    rwa [e] at h
  rcases le_or_gt σ (19 / 16) with hb | hb
  · have h := Legs.H3S2.seg σ (cast_le_of_le (by norm_num) ha.le) (le_cast_of_le (by norm_num) hb)
    rwa [e] at h
  · have h := Legs.H3S3.seg σ (cast_le_of_le (by norm_num) hb.le) (le_cast_of_le (by norm_num) h2)
    rwa [e] at h

/-- **`Re ζ > 0` on the top leg** `[1/2, 2] + 52i`. -/
theorem re_zeta_pos_top : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 52 * I)).re := by
  intro σ hσ
  obtain ⟨h1, h2⟩ := hσ
  have e : ((52 : ℚ) : ℂ) = 52 := by norm_num
  rcases le_or_gt σ (39 / 64) with h₁ | h₁
  · have h := Legs.H52S1.seg σ (cast_le_of_le (by norm_num) h1) (le_cast_of_le (by norm_num) h₁)
    rwa [e] at h
  rcases le_or_gt σ (3 / 4) with h₂ | h₂
  · have h := Legs.H52S2.seg σ (cast_le_of_le (by norm_num) h₁.le)
      (le_cast_of_le (by norm_num) h₂)
    rwa [e] at h
  rcases le_or_gt σ (15 / 16) with h₃ | h₃
  · have h := Legs.H52S3.seg σ (cast_le_of_le (by norm_num) h₂.le)
      (le_cast_of_le (by norm_num) h₃)
    rwa [e] at h
  rcases le_or_gt σ (9 / 8) with h₄ | h₄
  · have h := Legs.H52S4.seg σ (cast_le_of_le (by norm_num) h₃.le)
      (le_cast_of_le (by norm_num) h₄)
    rwa [e] at h
  rcases le_or_gt σ (23 / 16) with h₅ | h₅
  · have h := Legs.H52S5.seg σ (cast_le_of_le (by norm_num) h₄.le)
      (le_cast_of_le (by norm_num) h₅)
    rwa [e] at h
  · have h := Legs.H52S6.seg σ (cast_le_of_le (by norm_num) h₅.le)
      (le_cast_of_le (by norm_num) h2)
    rwa [e] at h

/-- **The argument at the bottom left corner**: `-1/5 ≤ arg ζ(1/2 + 3i) ≤ 0`. -/
theorem arg_zeta_bottom :
    -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧ (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 := by
  have h := Legs.Arg3.arg_bounds
  have hp : ptQ (1 / 2 : ℚ) (3 : ℚ) = 1 / 2 + 3 * I := by unfold ptQ; push_cast; ring
  rw [hp] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨le_trans (le_of_eq ?_) h1, h2⟩
  norm_num

/-- **The argument at the top left corner**: `-1/3 ≤ arg ζ(1/2 + 52i) ≤ 0`. -/
theorem arg_zeta_top :
    -(1 / 3 : ℝ) ≤ (riemannZeta (1 / 2 + 52 * I)).arg ∧
      (riemannZeta (1 / 2 + 52 * I)).arg ≤ 0 := by
  have h := Legs.Arg52.arg_bounds
  have hp : ptQ (1 / 2 : ℚ) (52 : ℚ) = 1 / 2 + 52 * I := by unfold ptQ; push_cast; ring
  rw [hp] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨le_trans (le_of_eq ?_) h1, h2⟩
  norm_num

/-- **The piece `horizontal_legs`**, with the plan's signature verbatim: `Re ζ > 0` on the
horizontal legs `[1/2, 2] + 3i` and `[1/2, 2] + 52i`, and the arguments of `ζ` at their left
ends in `[-1/5, 0]` and `[-1/3, 0]`. -/
theorem horizontal_legs :
    (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 3 * I)).re) ∧
    (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 52 * I)).re) ∧
    -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧ (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 ∧
    -(1 / 3 : ℝ) ≤ (riemannZeta (1 / 2 + 52 * I)).arg ∧
      (riemannZeta (1 / 2 + 52 * I)).arg ≤ 0 :=
  ⟨re_zeta_pos_bottom, re_zeta_pos_top, arg_zeta_bottom.1, arg_zeta_bottom.2, arg_zeta_top.1,
    arg_zeta_top.2⟩

/-- The same, as the skeleton's `Prop`. -/
theorem horizontalLegs : HorizontalLegs := horizontal_legs

end RHHeight
