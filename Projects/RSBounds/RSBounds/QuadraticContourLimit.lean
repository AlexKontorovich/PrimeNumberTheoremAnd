import RSBounds.PolynomialExplicitFormula
import RSBounds.PolynomialLeftRemainder
import TernaryGoldbach.Explicit.ZetaExplicit
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Contour limits for degree-two kernels

The logarithmic left-line estimate for `(s - 1)ζ(s)` and the polynomial
zeta datum allow inverse-square Mellin decay. These are the contour
inputs for the finite-interval signed integral in Rosser--Schoenfeld
(1962), Section 8. No RH or quantitative zero-free hypothesis is used.

The generic contour passage records its analytic premises explicitly;
the actual-zeta export below proves them from the existing unconditional
polynomial datum. The pole at zero remains visible in the formula.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.QuadraticContourLimit

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialLeftRemainder

/-- Inverse-square bounds on the vertical lines and horizontal strip. -/
structure DecayTwo (M : ℂ → ℂ) (K : ℝ) : Prop where
  nonneg : 0 ≤ K
  continuous_line : ∀ σ : ℝ, σ = -1 / 2 ∨ σ = 3 / 2 →
    Continuous (fun t : ℝ => M ((σ : ℂ) + t * I))
  line_bound : ∀ σ : ℝ, σ = -1 / 2 ∨ σ = 3 / 2 → ∀ t : ℝ,
    ‖M ((σ : ℂ) + t * I)‖ ≤ K / (1 + |t|) ^ 2
  strip_bound : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
    ‖M s‖ ≤ K / |s.im| ^ 2

/-- A logarithmic weight remains integrable against inverse-square decay. -/
theorem log_weighted_integrable_of_decay_two {g : ℝ → ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hc : Continuous g)
    (hg : ∀ t, ‖g t‖ ≤ K / (1 + |t|) ^ 2) :
    Integrable (fun t : ℝ => (1 + Real.log (max 1 |t|)) * ‖g t‖) := by
  have hi : Integrable (fun t : ℝ => (1 + |t|) ^ (- (3 / 2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num))
  have hlogcont : Continuous (fun t : ℝ => Real.log (max 1 |t|)) :=
    (continuous_const.max continuous_abs).log (fun t =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  refine (hi.const_mul (3 * K)).mono'
    ((continuous_const.add hlogcont).mul hc.norm).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have ha : 0 ≤ |t| := abs_nonneg t
  have hp : 0 < 1 + |t| := by positivity
  have hm : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hl0 : 0 ≤ Real.log (max 1 |t|) := Real.log_nonneg (le_max_left _ _)
  have hlog : Real.log (max 1 |t|) ≤ 2 * (1 + |t|) ^ (1 / 2 : ℝ) := by
    have h1 := Real.log_le_log hm (show max 1 |t| ≤ 1 + |t| by
      exact max_le (by linarith) (by linarith))
    have h2 := Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hpow : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (1 + Real.log (max 1 |t|)) * ‖g t‖
        ≤ (3 * (1 + |t|) ^ (1 / 2 : ℝ)) * (K / (1 + |t|) ^ 2) := by
      exact mul_le_mul (by linarith) (hg t) (norm_nonneg _) (by positivity)
    _ = (3 * K) * (1 + |t|) ^ (- (3 / 2 : ℝ)) := by
      calc
        _ = (3 * K) * ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ (2 : ℝ)) := by
          rw [Real.rpow_two]
          ring
        _ = _ := by rw [← Real.rpow_sub hp]; norm_num

theorem DecayTwo.log_weighted_integrable {M : ℂ → ℂ} {K : ℝ}
    (hM : DecayTwo M K) {σ : ℝ} (hσ : σ = -1 / 2 ∨ σ = 3 / 2) :
    Integrable (fun t : ℝ =>
      (1 + Real.log (max 1 |t|)) * ‖M ((σ : ℂ) + t * I)‖) :=
  log_weighted_integrable_of_decay_two hM.nonneg (hM.continuous_line σ hσ)
    (hM.line_bound σ hσ)

theorem DecayTwo.integrable_line {M : ℂ → ℂ} {K : ℝ}
    (hM : DecayTwo M K) {σ : ℝ} (hσ : σ = -1 / 2 ∨ σ = 3 / 2) :
    Integrable (fun t : ℝ => M ((σ : ℂ) + t * I)) := by
  refine (hM.log_weighted_integrable hσ).mono'
    (hM.continuous_line σ hσ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  exact le_mul_of_one_le_left (norm_nonneg _)
    (by linarith [Real.log_nonneg (le_max_left (1 : ℝ) |t|)])

/-- Right-line integrability requires only the bounded logarithmic derivative. -/
theorem integrable_contour_right {f M : ℂ → ℂ} {B : ℝ → ℝ} {D CR K : ℝ}
    (hd : LDatum f B D CR) (hM : DecayTwo M K) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + t * I)) := by
  have hcont : Continuous (fun t : ℝ =>
      contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    unfold contourIntegrand
    refine (continuous_logDeriv_lineD hd (3 / 2)
      (fun t => hd.nz_right _ (by simp; norm_num))).mul
      ((hM.continuous_line (3 / 2) (Or.inr rfl)).mul ?_)
    exact continuous_iff_continuousAt.2 fun t =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  have hCR : 0 ≤ CR := (norm_nonneg _).trans (hd.right_bound 0)
  refine (((hM.integrable_line (Or.inr rfl)).norm).const_mul
    (CR * x ^ (3 / 2 : ℝ))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [contourIntegrand, norm_mul, norm_mul, norm_cpow_x hx]
  have hre : (((3 / 2 : ℝ) : ℂ) + t * I).re = 3 / 2 := by simp
  rw [hre]
  calc
    ‖logDeriv f (((3 / 2 : ℝ) : ℂ) + t * I)‖ *
        (‖M (((3 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (3 / 2 : ℝ))
      ≤ CR * (‖M (((3 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (3 / 2 : ℝ)) := by
        gcongr
        exact hd.right_bound t
    _ = _ := by ring

/-- Actual-zeta left-line integrability follows from logarithmic growth. -/
theorem integrable_zetaF_contour_left {M : ℂ → ℂ} {K : ℝ}
    (hM : DecayTwo M K) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      contourIntegrand zetaF M x (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
  have hcont : Continuous (fun t : ℝ =>
      contourIntegrand zetaF M x (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
    unfold contourIntegrand
    refine (continuous_logDeriv_lineD ldatum_zeta2 (-1 / 2) (fun t =>
      ldatum_zeta2.nz_strip _ (by simp; norm_num) (by simp; norm_num))).mul
      ((hM.continuous_line (-1 / 2) (Or.inl rfl)).mul ?_)
    exact continuous_iff_continuousAt.2 fun t =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  refine ((hM.log_weighted_integrable (Or.inl rfl)).const_mul
    (336 * x ^ (-1 / 2 : ℝ))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [contourIntegrand, norm_mul, norm_mul, norm_cpow_x hx]
  have hre : (((-1 / 2 : ℝ) : ℂ) + t * I).re = -1 / 2 := by simp
  rw [hre]
  have hbound : ‖logDeriv zetaF (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      336 * (1 + Real.log (max 1 |t|)) := by
    have := norm_logDeriv_zetaF_left_log t
    have := Real.log_nonneg (le_max_left (1 : ℝ) |t|)
    linarith
  calc
    ‖logDeriv zetaF (((-1 / 2 : ℝ) : ℂ) + t * I)‖ *
        (‖M (((-1 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (-1 / 2 : ℝ))
      ≤ (336 * (1 + Real.log (max 1 |t|))) *
        (‖M (((-1 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (-1 / 2 : ℝ)) := by
          gcongr
    _ = _ := by ring

/-- The actual polynomial zeta datum has `HkD = O(log² k)`, so second-power
kernel decay is enough to kill the two horizontal integrals. -/
theorem tendsto_HkD_BPz2_div_sq :
    Tendsto (fun k : ℕ => HkD BPz2 (k + 1) / ((k : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
  let P : ℕ → ℝ := fun k => 10.24 + 10 * Real.log (1.25 * ((k : ℝ) + 24))
  have hkTop : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hInv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
  have hArg : Tendsto (fun k : ℕ => 1.25 * ((k : ℝ) + 24)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
      (by norm_num)
  have hLog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hArg
  have hRatio : Tendsto
      (fun k : ℕ => (1.25 * ((k : ℝ) + 24)) / ((k : ℝ) + 1)) atTop (𝓝 1.25) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1.25 : ℝ)) atTop (𝓝 1.25)).add (hInv.const_mul (28.75 : ℝ))
    convert h using 1
    · ext k
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · norm_num
  have hLogDiv : Tendsto
      (fun k : ℕ => Real.log (1.25 * ((k : ℝ) + 24)) / ((k : ℝ) + 1))
      atTop (𝓝 0) := by
    have h := hLog.mul hRatio
    convert h using 1
    · ext k
      dsimp [Function.comp_def, id]
      have ha : 1.25 * ((k : ℝ) + 24) ≠ 0 := by positivity
      field_simp
    · norm_num
  have hP : Tendsto (fun k : ℕ => P k / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (hInv.const_mul (10.24 : ℝ)).add (hLogDiv.const_mul (10 : ℝ))
    convert h using 1
    · ext k
      dsimp [P]
      ring
    · norm_num
  have hMajor : Tendsto
      (fun k : ℕ => 11.4 * (P k / ((k : ℝ) + 1)) ^ 2 +
        7.7 * (P k / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ((hP.pow 2).const_mul (11.4 : ℝ)).add
      ((hP.const_mul (7.7 : ℝ)).mul hInv)
  refine squeeze_zero (fun k => div_nonneg (HkD_BPz2_nonneg _) (by positivity))
    (fun k => ?_) hMajor
  have h := HkD_BPz2_le (k + 1)
  have hPk : 10.24 + 10 * Real.log (1.25 * (((k + 1 : ℕ) : ℝ) + 23)) = P k := by
    simp only [P, Nat.cast_add, Nat.cast_one]
    congr 3 <;> ring
  rw [hPk] at h
  calc
    HkD BPz2 (k + 1) / ((k : ℝ) + 1) ^ 2
      ≤ (11.4 * P k ^ 2 + 7.7 * P k) / ((k : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp <;> ring

/-- Generic degree-two contour passage. The vertical integrability and
horizontal decay assumptions are explicit; no zeta estimate is hidden. -/
theorem contour_limit_of_residue_formula_at_heights {f M : ℂ → ℂ} {B : ℝ → ℝ} {K : ℝ}
    (hM : DecayTwo M K) {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hHeights : GoodHeights f B T)
    (hRightInt : Integrable (fun t : ℝ =>
      contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + t * I)))
    (hLeftInt : Integrable (fun t : ℝ =>
      contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + t * I)))
    (hHeightDecay : Tendsto
      (fun k : ℕ => HkD B (k + 1) / ((k : ℝ) + 1) ^ 2) atTop (𝓝 0))
    (residueZero : ℂ)
    (hrectFormula : ∀ T : ℝ, 0 < T →
      (∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
      (∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) →
      rectInt (contourIntegrand f M x) (zT T) (wT T) =
        2 * π * I * ((∑ u ∈ zerosRectD f T, (multRectD f T u : ℂ) *
          (M u * (x : ℂ) ^ u)) + residueZero)) :
    Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
        (M u * (x : ℂ) ^ u)) atTop
        (𝓝 ((1 / (2 * π) : ℂ) *
          ((∫ y : ℝ, contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + y * I)) -
            ∫ y : ℝ, contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + y * I)) - residueZero)) := by
  have hT' := hHeights.mem
  have hgood := hHeights.bounds
  have hTpos : ∀ k, 0 < T k := fun k => by linarith [(hT' k).1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  set Rinf := ∫ y : ℝ, contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + y * I) with hRinf
  set Linf := ∫ y : ℝ, contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + y * I) with hLinf
  set Sk := fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) * (M u * (x : ℂ) ^ u)
  set Bot := fun k => ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), contourIntegrand f M x ((σ : ℂ) + ((-T k : ℝ) : ℂ) * I)
  set Top := fun k => ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), contourIntegrand f M x ((σ : ℂ) + ((T k : ℝ) : ℂ) * I)
  set Right := fun k => ∫ y in (-T k)..(T k), contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + y * I)
  set Left := fun k => ∫ y in (-T k)..(T k), contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + y * I)
  -- the rectangle identity, expanded
  have hrect : ∀ k, Bot k - Top k + I * Right k - I * Left k = 2 * π * I * (Sk k + residueZero) := by
    intro k
    have h := hrectFormula (T k) (hTpos k) (fun σ hσ => ((hgood k σ hσ).1).2)
      (fun σ hσ => ((hgood k σ hσ).1).1)
    rw [← h]
    unfold rectInt
    simp only [zT_re, zT_im, wT_re, wT_im, smul_eq_mul]
    rfl
  -- The second-power kernel estimate, without exponential decay.
  have hside : ∀ k, ∀ S : ℝ, (S = T k ∨ S = -T k) →
      ‖∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), contourIntegrand f M x ((σ : ℂ) + (S : ℂ) * I)‖ ≤
        (HkD B (k + 1) / ((k : ℝ) + 1) ^ 2) *
          (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) *
          |(3 / 2 : ℝ) - (-1 / 2)| := by
    intro k S hS
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    have hσ' : σ ∈ [[(-1 / 2 : ℝ), 3 / 2]] := Set.uIoc_subset_uIcc hσ
    have hσ2 : -1 / 2 ≤ σ ∧ σ ≤ 3 / 2 := by
      rw [Set.uIcc_of_le (by norm_num)] at hσ'; exact hσ'
    have hb : ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ ≤ HkD B (k + 1) := by
      rcases hS with rfl | rfl
      · exact ((hgood k σ hσ').2).1
      · exact ((hgood k σ hσ').2).2
    have hS' : |S| = T k := by
      rcases hS with rfl | rfl
      · exact abs_of_pos (hTpos k)
      · rw [abs_neg]; exact abs_of_pos (hTpos k)
    have hTk : (k : ℝ) + 1 ≤ T k := (hT' k).1
    have hK1 : 1 ≤ T k := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hG := hM.strip_bound ((σ : ℂ) + (S : ℂ) * I)
      (by simp; linarith) (by simp; linarith) (by simpa [hS'] using hK1)
    have him : ((σ : ℂ) + (S : ℂ) * I).im = S := by simp
    have hre : ((σ : ℂ) + (S : ℂ) * I).re = σ := by simp
    rw [him, hS'] at hG
    have hden : K / (T k) ^ 2 ≤ K / ((k : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_left hM.nonneg (by positivity)
        (pow_le_pow_left₀ (by positivity) hTk 2)
    have hxσ := rpow_le_of_mem hx hσ2.1 hσ2.2
    have hHk0 : 0 ≤ HkD B (k + 1) := le_trans (norm_nonneg _) hb
    rw [contourIntegrand, norm_mul, norm_mul, norm_cpow_x hx, hre]
    calc
      ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ *
          (‖M ((σ : ℂ) + (S : ℂ) * I)‖ * x ^ σ)
        ≤ HkD B (k + 1) * ((K / ((k : ℝ) + 1) ^ 2) *
          (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) := by
            exact mul_le_mul hb
              (mul_le_mul (hG.trans hden) hxσ (by positivity)
                (div_nonneg hM.nonneg (by positivity)))
              (by positivity) hHk0
      _ = _ := by ring
  have hdecay : Tendsto (fun k : ℕ => (HkD B (k + 1) / ((k : ℝ) + 1) ^ 2) *
      (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) *
      |(3 / 2 : ℝ) - (-1 / 2)|) atTop (𝓝 0) := by
    have h := (hHeightDecay.mul_const
      (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ)))).mul_const
      |(3 / 2 : ℝ) - (-1 / 2)|
    simpa using h
  have hBot : Tendsto Bot atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hside k (-T k) (Or.inr rfl)) hdecay
  have hTop : Tendsto Top atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hside k (T k) (Or.inl rfl)) hdecay
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun k => (hT' k).1) (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hRight : Tendsto Right atTop (𝓝 Rinf) :=
    intervalIntegral_tendsto_integral hRightInt
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hLeft : Tendsto Left atTop (𝓝 Linf) :=
    intervalIntegral_tendsto_integral hLeftInt
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hSk : ∀ k, Sk k = (Bot k - Top k + I * Right k - I * Left k) / (2 * π * I) - residueZero := by
    intro k
    have hne : (2 * π * I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    rw [hrect k]; field_simp; ring
  have hlim := ((((hBot.sub hTop).add (hRight.const_mul I)).sub (hLeft.const_mul I)).div_const
    (2 * π * I)).sub_const residueZero
  rw [show Sk = fun k => (Bot k - Top k + I * Right k - I * Left k) / (2 * π * I) - residueZero from funext hSk]
  convert hlim using 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring


/-- The actual-zeta contour passage, with all analytic premises discharged. -/
theorem zetaF_contour_limit_of_residue_formula_at_heights {M : ℂ → ℂ} {K : ℝ}
    (hM : DecayTwo M K) {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hHeights : GoodHeights zetaF BPz2 T)
    (residueZero : ℂ)
    (hrectFormula : ∀ T : ℝ, 0 < T →
      (∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], zetaF ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
      (∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], zetaF ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) →
      rectInt (contourIntegrand zetaF M x) (zT T) (wT T) =
        2 * π * I * ((∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) *
          (M u * (x : ℂ) ^ u)) + residueZero)) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        (M u * (x : ℂ) ^ u)) atTop
        (𝓝 ((1 / (2 * π) : ℂ) *
          ((∫ y : ℝ, contourIntegrand zetaF M x (((3 / 2 : ℝ) : ℂ) + y * I)) -
            ∫ y : ℝ, contourIntegrand zetaF M x (((-1 / 2 : ℝ) : ℂ) + y * I)) - residueZero)) :=
  contour_limit_of_residue_formula_at_heights hM hx hHeights
    (integrable_contour_right ldatum_zeta2 hM hx)
    (integrable_zetaF_contour_left hM hx) tendsto_HkD_BPz2_div_sq residueZero hrectFormula

/-- Degree-two pole-zero formula for actual zeta, along any supplied good heights. -/
theorem explicit_formula_pole_zero_at_heights {H : ℂ → ℂ} {K : ℝ}
    (hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ H s)
    (hM : DecayTwo (fun s => H s / s) K) {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hT : GoodHeights zetaF BPz2 T) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
      (H u / u * (x : ℂ) ^ u)) atTop
      (𝓝 ((1 / (2 * π) : ℂ) *
        ((∫ y : ℝ, contourIntegrand zetaF (fun s => H s / s) x
          (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, contourIntegrand zetaF (fun s => H s / s) x
            (((-1 / 2 : ℝ) : ℂ) + y * I)) - logDeriv zetaF 0 * H 0)) :=
  zetaF_contour_limit_of_residue_formula_at_heights hM hx hT (logDeriv zetaF 0 * H 0)
    (fun _ hT hbot htop => rect_identity_pole_zero ldatum_zeta2
      (by rw [zetaF_of_ne (by norm_num), riemannZeta_zero]; norm_num) hH hx hT hbot htop)

end TernaryGoldbach.RSBounds.QuadraticContourLimit
