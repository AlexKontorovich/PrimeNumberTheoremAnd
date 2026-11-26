module

public import RHHeight.Skeleton
public import Zeta23.GammaFacts
public import Zeta23.GammaFacts.StirlingVert
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# `gamma_increment`: the Gamma side of hunt #137's count, enclosed

The piece `GammaIncrement` of `RHHeight/Skeleton.lean` (key `gamma_increment`,
`hunts/rh_height_lean/PLAN.md` section 4.1):

    92/10 ≤ ∫_3^52 μ ≤ 109/10,

where `μ = Zeta23.mu` is `zeta23`'s density
`μ(τ) = (1/2π) Re ψ(1/4 + iτ/2) - log π/(2π)`, `ψ = Γ'/Γ`. By the vendored `gamma_side` this
integral is the Gamma half of the folded argument principle, `(θ(52) - θ(3))/π` with `θ` the
Riemann-Siegel theta function. Measured (mpmath quadrature, one route; the sibling numeric
plan has the same value in Arb): `10.042613`.

The route:

1. `GammaSide.abs_mu_sub_muMain_le`: for `|t| ≥ 1`, with `w = 1/4 + it/2`, the vendored
   `Zeta23.StirlingVert.digamma_stirling` gives `‖ψ(w) - log w + 1/(2w)‖ ≤ 3/(Im w)² = 12/t²`.
   Keeping `Re log w = (1/2) log((1 + 4t²)/16)` and `Re 1/(2w) = 2/(1 + 4t²)` exactly gives
   `|μ t - m t| ≤ 6/(π t²)` with
   `m t = (1/2π) ((1/2) log((1 + 4t²)/16) - 2/(1 + 4t²) - log π)` (`GammaSide.muMain`).
2. `GammaSide.hasDerivAt_muPrim`: `m` has the elementary primitive
   `F t = (1/2π) ((t/2) log((1 + 4t²)/16) - t - (1/2) arctan(2t) - t log π)`
   (`GammaSide.muPrim`).
3. `GammaSide.abs_integral_mu_sub_le`: for `1 ≤ T₁ ≤ T₂`, integral monotonicity against
   `m ± 6/(π t²)` and the fundamental theorem of calculus (primitives `F ∓ 6/(π t)`) give
   `|∫_{T₁}^{T₂} μ - (F T₂ - F T₁)| ≤ (6/π)(1/T₁ - 1/T₂)`. `μ` is integrable because it is
   continuous (`Zeta23.mu_smooth`), which avoids `GammaFacts.Complete`.
4. `gamma_increment`: at `(3, 52)`, `2π (F 52 - F 3) = 26 log(10817/16) - (3/2) log(37/16) - 49
   - (1/2)(arctan 104 - arctan 6) - 49 log π`, and the error is `(1/2π)(49/13)`. The three
   logarithms are bounded by Mathlib's series bound `Real.abs_log_sub_add_sum_range_le`
   after splitting off powers of `2` (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`), `log π`
   by monotonicity from `Real.pi_gt_d4` and `Real.pi_lt_d4`, and the arctangent term lies
   in `[-π/4, 0]` by monotonicity alone.

Measured (mpmath, one route): `F 52 - F 3 = 10.026188` and `(6/π)(1/3 - 1/52) = 0.599892`,
so step 3 confines the integral to `[9.4263, 10.6261]`. The rational bounds of step 4, with
`arctan 104 - arctan 6` taken anywhere in `[0, π/2]`, confine it to `[9.3109, 10.6429]`
(evaluated in mpmath from those rationals). The theorem states the skeleton's `[9.2, 10.9]`,
which leaves `0.111` below and `0.257` above. On `[3, 52]` the true `|μ - m|` is at most
`0.028` of the bound `6/(π t²)` (measured on a grid of 401 points), so the width of the
step-3 interval comes from the constant `3` of `digamma_stirling`, not from the main term.

`gamma_increment` has exactly the type of the skeleton's `Prop` `GammaIncrement`, and
`gamma_increment_holds` records that match. Helpers live in the namespace
`RHHeight.GammaSide`, so they cannot collide with the other pieces' names.
-/

noncomputable section

open Complex MeasureTheory

namespace RHHeight

namespace GammaSide

/-- The Stirling main term of `μ` with `log |w|` and `Re 1/(2w)` kept exactly, `w = 1/4 + it/2`:
`m t = (1/2π) ((1/2) log((1 + 4t²)/16) - 2/(1 + 4t²) - log π)`. -/
def muMain (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ((1 / 2) * Real.log ((1 + 4 * t ^ 2) / 16) - 2 / (1 + 4 * t ^ 2) - Real.log Real.pi)

/-- A primitive of `muMain`:
`F t = (1/2π) ((t/2) log((1 + 4t²)/16) - t - (1/2) arctan(2t) - t log π)`. -/
def muPrim (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (t / 2 * Real.log ((1 + 4 * t ^ 2) / 16) - t - (1 / 2) * Real.arctan (2 * t)
      - t * Real.log Real.pi)

/-- **Pointwise Stirling bound for `μ`.** For `|t| ≥ 1`, `|μ t - m t| ≤ 6/(π t²)`: the vendored
`digamma_stirling` at `w = 1/4 + it/2`, whose real part is `1/4` and imaginary part `t/2`. -/
theorem abs_mu_sub_muMain_le {t : ℝ} (ht : 1 ≤ |t|) :
    |Zeta23.mu t - muMain t| ≤ 6 / (Real.pi * t ^ 2) := by
  unfold Zeta23.mu
  set w : ℂ := 1 / 4 + Complex.I * (t : ℂ) / 2 with hw
  have hwre : w.re = 1 / 4 := by simp [hw]
  have hwim : w.im = t / 2 := by simp [hw]
  have hpos : 0 < w.re := by rw [hwre]; norm_num
  have him : 1 / 2 ≤ |w.im| := by rw [hwim, abs_div, abs_two]; linarith
  have hS := Zeta23.StirlingVert.digamma_stirling hpos him
  rw [hwim] at hS
  have hnsq : Complex.normSq w = (1 + 4 * t ^ 2) / 16 := by
    rw [Complex.normSq_apply, hwre, hwim]; ring
  -- `Re log w = log ‖w‖ = (1/2) log ‖w‖²`
  have hlogre : (Complex.log w).re = (1 / 2) * Real.log ((1 + 4 * t ^ 2) / 16) := by
    rw [Complex.log_re, ← hnsq, Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast
    ring
  -- `Re (1/2)/w = (1/2) Re w / ‖w‖² = 2/(1 + 4t²)`
  have hinvre : ((1 / 2 : ℂ) / w).re = 2 / (1 + 4 * t ^ 2) := by
    rw [Complex.div_re, hnsq, hwre, hwim]
    have h1 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    have h2 : (1 / 2 : ℂ).im = 0 := by norm_num
    rw [h1, h2]
    have hd : (1 : ℝ) + 4 * t ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hkey : (1 / (2 * Real.pi)) * (Complex.digamma w).re - Real.log Real.pi / (2 * Real.pi)
      - muMain t
      = (1 / (2 * Real.pi)) * (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re := by
    rw [Complex.add_re, Complex.sub_re, hlogre, hinvre, muMain]
    ring
  rw [hkey, abs_mul, abs_of_pos (by positivity)]
  have ht0 : 0 < t ^ 2 := by
    have : 0 < |t| := by linarith
    rw [← sq_abs]; positivity
  have hE : |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re| ≤ 12 / t ^ 2 := by
    refine le_trans (Complex.abs_re_le_norm _) (le_trans hS (le_of_eq ?_))
    field_simp
    ring
  calc 1 / (2 * Real.pi) * |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re|
      ≤ 1 / (2 * Real.pi) * (12 / t ^ 2) := by gcongr
    _ = 6 / (Real.pi * t ^ 2) := by field_simp; ring

/-- `muPrim` is a primitive of `muMain` on the whole real line. -/
theorem hasDerivAt_muPrim (t : ℝ) : HasDerivAt muPrim (muMain t) t := by
  have hq : (1 + 4 * t ^ 2) / 16 ≠ 0 := by positivity
  have hd : (1 : ℝ) + 4 * t ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (1 + 4 * t ^ 2) / 16) (8 * t / 16) t := by
    have := (((hasDerivAt_id' t).pow 2).const_mul 4).const_add 1 |>.div_const 16
    convert this using 1
    simp
    ring
  have hlog := h1.log hq
  have hc : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := (hasDerivAt_id' t).div_const 2
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
    simpa using (hasDerivAt_id' t).const_mul 2
  have harc := h2.arctan
  have H := ((((hc.mul hlog).sub (hasDerivAt_id' t)).sub (harc.const_mul (1 / 2))).sub
    ((hasDerivAt_id' t).mul_const (Real.log Real.pi))).const_mul (1 / (2 * Real.pi))
  convert H using 1
  · funext y
    rfl
  · unfold muMain
    field_simp
    ring

theorem continuous_muMain : Continuous muMain := by
  have h1 : Continuous (fun t : ℝ => Real.log ((1 + 4 * t ^ 2) / 16)) :=
    (by fun_prop : Continuous fun t : ℝ => (1 + 4 * t ^ 2) / 16).log (fun t => by positivity)
  have h2 : Continuous (fun t : ℝ => 2 / (1 + 4 * t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun t => by positivity)
  exact continuous_const.mul (((continuous_const.mul h1).sub h2).sub continuous_const)

/-- The derivative of the error primitive `6/(π t)`. -/
theorem hasDerivAt_six_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 6 / (Real.pi * t)) (-(6 / (Real.pi * x ^ 2))) x := by
  have hπ := Real.pi_pos
  have h := (hasDerivAt_const x (6 : ℝ)).div ((hasDerivAt_id' x).const_mul Real.pi)
    (mul_ne_zero hπ.ne' hx)
  convert h using 1
  field_simp
  ring

/-- **The Gamma side between two heights, to within the Stirling error.** For `1 ≤ T₁ ≤ T₂`,
`|∫_{T₁}^{T₂} μ - (F T₂ - F T₁)| ≤ (6/π)(1/T₁ - 1/T₂)`, with `F = muPrim`. -/
theorem abs_integral_mu_sub_le {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ ≤ T₂) :
    |(∫ t in T₁..T₂, Zeta23.mu t) - (muPrim T₂ - muPrim T₁)|
      ≤ 6 / Real.pi * (1 / T₁ - 1 / T₂) := by
  have hπ := Real.pi_pos
  have hT₁ : 0 < T₁ := by linarith
  have hT₂ : 0 < T₂ := by linarith
  have hmu_int : IntervalIntegrable Zeta23.mu volume T₁ T₂ :=
    Zeta23.mu_smooth.continuous.intervalIntegrable T₁ T₂
  have hIcc : Set.uIcc T₁ T₂ = Set.Icc T₁ T₂ := Set.uIcc_of_le h12
  have hderU : ∀ x ∈ Set.uIcc T₁ T₂, HasDerivAt (fun t => muPrim t - 6 / (Real.pi * t))
      (muMain x + 6 / (Real.pi * x ^ 2)) x := by
    intro x hx
    rw [hIcc] at hx
    have hx0 : x ≠ 0 := (by linarith [hx.1] : (0 : ℝ) < x).ne'
    have h := (hasDerivAt_muPrim x).sub (hasDerivAt_six_div x hx0)
    convert h using 1
    ring
  have hderL : ∀ x ∈ Set.uIcc T₁ T₂, HasDerivAt (fun t => muPrim t + 6 / (Real.pi * t))
      (muMain x - 6 / (Real.pi * x ^ 2)) x := by
    intro x hx
    rw [hIcc] at hx
    have hx0 : x ≠ 0 := (by linarith [hx.1] : (0 : ℝ) < x).ne'
    have h := (hasDerivAt_muPrim x).add (hasDerivAt_six_div x hx0)
    convert h using 1
  have hcont6 : ContinuousOn (fun t : ℝ => 6 / (Real.pi * t ^ 2)) (Set.uIcc T₁ T₂) := by
    rw [hIcc]
    apply continuousOn_const.div (by fun_prop)
    intro x hx
    have : 0 < x := by linarith [hx.1]
    positivity
  have hintU : IntervalIntegrable (fun t => muMain t + 6 / (Real.pi * t ^ 2)) volume T₁ T₂ :=
    (continuous_muMain.continuousOn.add hcont6).intervalIntegrable
  have hintL : IntervalIntegrable (fun t => muMain t - 6 / (Real.pi * t ^ 2)) volume T₁ T₂ :=
    (continuous_muMain.continuousOn.sub hcont6).intervalIntegrable
  have hU := intervalIntegral.integral_eq_sub_of_hasDerivAt hderU hintU
  have hL := intervalIntegral.integral_eq_sub_of_hasDerivAt hderL hintL
  have hpt : ∀ x ∈ Set.Icc T₁ T₂, |Zeta23.mu x - muMain x| ≤ 6 / (Real.pi * x ^ 2) := by
    intro x hx
    exact abs_mu_sub_muMain_le (by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.1])
  have hle : ∫ t in T₁..T₂, Zeta23.mu t ≤ ∫ t in T₁..T₂, (muMain t + 6 / (Real.pi * t ^ 2)) :=
    intervalIntegral.integral_mono_on h12 hmu_int hintU fun x hx => by
      linarith [(abs_le.mp (hpt x hx)).2]
  have hge : ∫ t in T₁..T₂, (muMain t - 6 / (Real.pi * t ^ 2)) ≤ ∫ t in T₁..T₂, Zeta23.mu t :=
    intervalIntegral.integral_mono_on h12 hintL hmu_int fun x hx => by
      linarith [(abs_le.mp (hpt x hx)).1]
  have herr : 6 / (Real.pi * T₁) - 6 / (Real.pi * T₂) = 6 / Real.pi * (1 / T₁ - 1 / T₂) := by
    field_simp
  rw [abs_le]
  constructor <;> linarith

/-! ### Rational bounds for the constants at `(3, 52)` -/

/-- Mathlib's series bound for `log (1 - x)`, `|x| < 1`, in two-sided form. -/
theorem log_one_sub_bounds {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - |x| ^ (n + 1) / (1 - |x|)
        ≤ Real.log (1 - x) ∧
      Real.log (1 - x)
        ≤ -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + |x| ^ (n + 1) / (1 - |x|) := by
  have h := abs_le.mp (Real.abs_log_sub_add_sum_range_le hx n)
  constructor <;> linarith [h.1, h.2]

/-- `log(10817/16) = 9 log 2 + log(10817/8192)`, measured `6.516286`. -/
theorem log_10817_div_16_mem :
    (6516 / 1000 : ℝ) ≤ Real.log (10817 / 16) ∧ Real.log (10817 / 16) ≤ 6517 / 1000 := by
  have hsplit : Real.log (10817 / 16) = 9 * Real.log 2 + Real.log (10817 / 8192) := by
    rw [show (10817 / 16 : ℝ) = 2 ^ 9 * (10817 / 8192) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hx : |(-2625 / 8192 : ℝ)| = 2625 / 8192 := by
    rw [abs_of_neg (by norm_num)]; norm_num
  obtain ⟨hlo, hhi⟩ := log_one_sub_bounds (x := -2625 / 8192) (by rw [hx]; norm_num) 10
  rw [hx, show (1 : ℝ) - -2625 / 8192 = 10817 / 8192 by norm_num] at hlo hhi
  norm_num [Finset.sum_range_succ] at hlo hhi
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  rw [hsplit]
  constructor <;> linarith

/-- `log(37/16) = log 2 + log(37/32)`, measured `0.838329`. -/
theorem log_37_div_16_mem :
    (838 / 1000 : ℝ) ≤ Real.log (37 / 16) ∧ Real.log (37 / 16) ≤ 839 / 1000 := by
  have hsplit : Real.log (37 / 16) = Real.log 2 + Real.log (37 / 32) := by
    rw [show (37 / 16 : ℝ) = 2 * (37 / 32) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hx : |(-5 / 32 : ℝ)| = 5 / 32 := by
    rw [abs_of_neg (by norm_num)]; norm_num
  obtain ⟨hlo, hhi⟩ := log_one_sub_bounds (x := -5 / 32) (by rw [hx]; norm_num) 8
  rw [hx, show (1 : ℝ) - -5 / 32 = 37 / 32 by norm_num] at hlo hhi
  norm_num [Finset.sum_range_succ] at hlo hhi
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  rw [hsplit]
  constructor <;> linarith

theorem pi_gt_6283_div_2000 : (6283 / 2000 : ℝ) < Real.pi := by
  have := Real.pi_gt_d4; norm_num at this ⊢; linarith

theorem pi_lt_3927_div_1250 : Real.pi < 3927 / 1250 := by
  have := Real.pi_lt_d4; norm_num at this ⊢; linarith

/-- `log π`, measured `1.144730`, between `log 3.1415` and `log 3.1416`. -/
theorem log_pi_mem :
    (11446 / 10000 : ℝ) ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ 11449 / 10000 := by
  have hlo0 : Real.log (6283 / 2000) ≤ Real.log Real.pi :=
    Real.log_le_log (by norm_num) pi_gt_6283_div_2000.le
  have hhi0 : Real.log Real.pi ≤ Real.log (3927 / 1250) :=
    Real.log_le_log Real.pi_pos pi_lt_3927_div_1250.le
  have hs1 : Real.log (6283 / 2000) = 2 * Real.log 2 + Real.log (6283 / 8000) := by
    rw [show (6283 / 2000 : ℝ) = 2 ^ 2 * (6283 / 8000) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hs2 : Real.log (3927 / 1250) = 2 * Real.log 2 + Real.log (3927 / 5000) := by
    rw [show (3927 / 1250 : ℝ) = 2 ^ 2 * (3927 / 5000) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hx1 : |(1717 / 8000 : ℝ)| = 1717 / 8000 := abs_of_pos (by norm_num)
  have hx2 : |(1073 / 5000 : ℝ)| = 1073 / 5000 := abs_of_pos (by norm_num)
  obtain ⟨hlo, -⟩ := log_one_sub_bounds (x := 1717 / 8000) (by rw [hx1]; norm_num) 8
  obtain ⟨-, hhi⟩ := log_one_sub_bounds (x := 1073 / 5000) (by rw [hx2]; norm_num) 8
  rw [hx1, show (1 : ℝ) - 1717 / 8000 = 6283 / 8000 by norm_num] at hlo
  rw [hx2, show (1 : ℝ) - 1073 / 5000 = 3927 / 5000 by norm_num] at hhi
  norm_num [Finset.sum_range_succ] at hlo hhi
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  constructor <;> linarith

/-- `F` at the two heights of the contour. -/
theorem two_pi_mul_muPrim_sub :
    2 * Real.pi * (muPrim 52 - muPrim 3)
      = 26 * Real.log (10817 / 16) - 3 / 2 * Real.log (37 / 16) - 49
        - (1 / 2) * (Real.arctan 104 - Real.arctan 6) - 49 * Real.log Real.pi := by
  have hπ := Real.pi_pos
  unfold muPrim
  rw [show (1 + 4 * (52 : ℝ) ^ 2) / 16 = 10817 / 16 by norm_num,
    show (2 : ℝ) * 52 = 104 by norm_num, show (1 + 4 * (3 : ℝ) ^ 2) / 16 = 37 / 16 by norm_num,
    show (2 : ℝ) * 3 = 6 by norm_num]
  field_simp
  ring

end GammaSide

open GammaSide

/-- **`gamma_increment`.** The Gamma side of hunt #137's folded count at the heights
`T₁ = 3`, `T₂ = 52`: `92/10 ≤ ∫_3^52 μ ≤ 109/10`. This is the skeleton's `GammaIncrement`. -/
theorem gamma_increment :
    (92 / 10 : ℝ) ≤ ∫ t in (3 : ℝ)..52, Zeta23.mu t ∧
      ∫ t in (3 : ℝ)..52, Zeta23.mu t ≤ 109 / 10 := by
  have hπ := Real.pi_pos
  obtain ⟨hlo, hhi⟩ := abs_le.mp (abs_integral_mu_sub_le (T₁ := 3) (T₂ := 52)
    (by norm_num) (by norm_num))
  have hF := two_pi_mul_muPrim_sub
  have herr : 6 / Real.pi * (1 / 3 - 1 / 52) = 49 / 13 / (2 * Real.pi) := by
    field_simp
    ring
  obtain ⟨ha1, ha2⟩ := log_10817_div_16_mem
  obtain ⟨hb1, hb2⟩ := log_37_div_16_mem
  obtain ⟨hc1, hc2⟩ := log_pi_mem
  have hA : Real.arctan 104 < Real.pi / 2 := Real.arctan_lt_pi_div_two 104
  have hB : 0 < Real.arctan 6 := Real.arctan_pos.mpr (by norm_num)
  have hAB : Real.arctan 6 ≤ Real.arctan 104 := Real.arctan_strictMono.monotone (by norm_num)
  have hp1 := pi_gt_6283_div_2000
  have hp2 := pi_lt_3927_div_1250
  set G := ∫ t in (3 : ℝ)..52, Zeta23.mu t
  -- in units of `1/(2π)`, `G` lies within `49/13` of `2π (F 52 - F 3)`
  have hGlo : (2 * Real.pi * (muPrim 52 - muPrim 3) - 49 / 13) / (2 * Real.pi) ≤ G := by
    have h : (2 * Real.pi * (muPrim 52 - muPrim 3) - 49 / 13) / (2 * Real.pi)
        = (muPrim 52 - muPrim 3) - 49 / 13 / (2 * Real.pi) := by
      field_simp
    rw [h, ← herr]
    linarith
  have hGhi : G ≤ (2 * Real.pi * (muPrim 52 - muPrim 3) + 49 / 13) / (2 * Real.pi) := by
    have h : (2 * Real.pi * (muPrim 52 - muPrim 3) + 49 / 13) / (2 * Real.pi)
        = (muPrim 52 - muPrim 3) + 49 / 13 / (2 * Real.pi) := by
      field_simp
    rw [h, ← herr]
    linarith
  rw [hF] at hGlo hGhi
  constructor
  · refine le_trans ?_ hGlo
    rw [le_div_iff₀ (by positivity)]
    linarith
  · refine le_trans hGhi ?_
    rw [div_le_iff₀ (by positivity)]
    linarith

/-- `gamma_increment` proves the skeleton's `Prop` as stated. -/
theorem gamma_increment_holds : GammaIncrement := gamma_increment

end RHHeight
