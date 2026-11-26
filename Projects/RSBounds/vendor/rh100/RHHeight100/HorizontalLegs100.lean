module

public import RHHeight100.Skeleton100
public import RHHeight.HorizontalLegs
public import RHHeight100.LegsTop100A
public import RHHeight100.LegsTop100B
public import RHHeight100.LegsArg100

@[expose] public section

/-!
# `Re ζ > 0` on the horizontal legs at heights 3 and 100

`RHHeight100.HorizontalLegs100` (`RHHeight100/Skeleton100.lean`) asks for `Re ζ(σ + 3i) > 0`
and `Re ζ(σ + 100i) > 0` for every `σ ∈ [1/2, 2]`, and `-1/5 ≤ arg ζ(1/2 + 3i) ≤ 0`,
`-1/5 ≤ arg ζ(1/2 + 100i) ≤ 0`. The two facts at height 3 are the height-50 proof's
(`RHHeight.re_zeta_pos_bottom`, `RHHeight.arg_zeta_bottom`), reused. The two at height 100 come
from the generated files `RHHeight100/LegsTop100A.lean` and `LegsTop100B.lean` (seven segments,
`N = 24, 20, 20, 20, 18, 16, 10`) and `RHHeight100/LegsArg100.lean` (a box for `ζ(1/2 + 100i)`
at `N = 68`), through `RHHeight.Legs.re_pos_of_segment` and `RHHeight.Legs.arg_mem_of_box`.
The generator is `hunts/rh_height_lean/gen_legs100.py`.
-/

open Complex

namespace RHHeight100

open RHHeight RHHeight.Legs

private lemma cast_le_of_le {q : ℚ} {r : ℝ} {σ : ℝ} (hq : ((q : ℚ) : ℝ) = r) (h : r ≤ σ) :
    ((q : ℚ) : ℝ) ≤ σ := hq ▸ h

private lemma le_cast_of_le {q : ℚ} {r : ℝ} {σ : ℝ} (hq : ((q : ℚ) : ℝ) = r) (h : σ ≤ r) :
    σ ≤ ((q : ℚ) : ℝ) := hq ▸ h

/-- **`Re ζ > 0` on the top leg** `[1/2, 2] + 100i`. -/
theorem re_zeta_pos_top100 :
    ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 100 * I)).re := by
  intro σ hσ
  obtain ⟨h1, h2⟩ := hσ
  have e : ((100 : ℚ) : ℂ) = 100 := by norm_num
  rcases le_or_gt σ (39 / 64) with h₁ | h₁
  · have h := Legs.H100S1.seg σ (cast_le_of_le (by norm_num) h1) (le_cast_of_le (by norm_num) h₁)
    rwa [e] at h
  rcases le_or_gt σ (47 / 64) with h₂ | h₂
  · have h := Legs.H100S2.seg σ (cast_le_of_le (by norm_num) h₁.le)
      (le_cast_of_le (by norm_num) h₂)
    rwa [e] at h
  rcases le_or_gt σ (57 / 64) with h₃ | h₃
  · have h := Legs.H100S3.seg σ (cast_le_of_le (by norm_num) h₂.le)
      (le_cast_of_le (by norm_num) h₃)
    rwa [e] at h
  rcases le_or_gt σ (71 / 64) with h₄ | h₄
  · have h := Legs.H100S4.seg σ (cast_le_of_le (by norm_num) h₃.le)
      (le_cast_of_le (by norm_num) h₄)
    rwa [e] at h
  rcases le_or_gt σ (91 / 64) with h₅ | h₅
  · have h := Legs.H100S5.seg σ (cast_le_of_le (by norm_num) h₄.le)
      (le_cast_of_le (by norm_num) h₅)
    rwa [e] at h
  rcases le_or_gt σ (63 / 32) with h₆ | h₆
  · have h := Legs.H100S6.seg σ (cast_le_of_le (by norm_num) h₅.le)
      (le_cast_of_le (by norm_num) h₆)
    rwa [e] at h
  · have h := Legs.H100S7.seg σ (cast_le_of_le (by norm_num) h₆.le)
      (le_cast_of_le (by norm_num) h2)
    rwa [e] at h

/-- **The argument at the top left corner**: `-1/5 ≤ arg ζ(1/2 + 100i) ≤ 0`. -/
theorem arg_zeta_top100 :
    -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 100 * I)).arg ∧
      (riemannZeta (1 / 2 + 100 * I)).arg ≤ 0 := by
  have h := Legs.Arg100.arg_bounds
  have hp : ptQ (1 / 2 : ℚ) (100 : ℚ) = 1 / 2 + 100 * I := by unfold ptQ; push_cast; ring
  rw [hp] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨le_trans (le_of_eq ?_) h1, h2⟩
  norm_num

/-- **The piece `HorizontalLegs100`.** -/
theorem horizontalLegs100 : HorizontalLegs100 :=
  ⟨re_zeta_pos_bottom, re_zeta_pos_top100, arg_zeta_bottom.1, arg_zeta_bottom.2,
    arg_zeta_top100.1, arg_zeta_top100.2⟩

end RHHeight100
