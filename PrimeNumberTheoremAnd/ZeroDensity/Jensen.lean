/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
public import PrimeNumberTheoremAnd.ZeroDensity.Uniform
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.ZetaValues

/-!
# Unconditional Bohr–Landau via Jensen's formula on discs centred at `2 + iτ`

We apply Jensen's formula to the entire function `riemannZeta₁ s = (s-1) ζ(s)` on discs
centred at `2 + iτ`, average over `τ`, and control the resulting circle averages of
`log |ζ|` by the uniform mean square bound `uniformMeanSquare`.

`jensen_count` is a minor variant of Mathlib's `AnalyticOnNhd.sum_divisor_le`
(Mathlib, Apache 2.0 licence), keeping the circle average instead of a sup bound.
-/

open Complex Set Metric MeasureTheory Filter MeromorphicOn

@[expose] public noncomputable section
namespace ZeroDensity

lemma zg_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs]; field_simp [sub_ne_zero.2 hs]

lemma zg_analytic (U : Set ℂ) : AnalyticOnNhd ℂ riemannZeta₁ U :=
  fun z _ => differentiable_riemannZeta₁.analyticAt z

lemma zg_two_ne : riemannZeta₁ 2 ≠ 0 := by
  rw [zg_eq (by norm_num)]
  exact mul_ne_zero (by norm_num) (riemannZeta_ne_zero_of_one_lt_re (by norm_num))

lemma zg_order_ne_top (z : ℂ) : analyticOrderAt riemannZeta₁ z ≠ ⊤ := by
  refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (zg_analytic univ) isPreconnected_univ
    (mem_univ 2) (mem_univ z) ?_
  rw [analyticOrderAt_eq_zero.2 (Or.inr zg_two_ne)]; simp

lemma one_le_divisor_zg {U : Set ℂ} {u : ℂ} (hu : u ∈ U) (h0 : riemannZeta₁ u = 0) :
    1 ≤ divisor riemannZeta₁ U u := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (zg_order_ne_top u)
  rw [(zg_analytic U).divisor_apply hu, ← hn]
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := analyticOrderAt_eq_zero.1 hn.symm
    rcases this with h | h
    · exact h (zg_analytic univ u (mem_univ u))
    · exact h h0
  simp; omega

lemma card_le_finsum_divisor {c : ℂ} {r : ℝ} (Z : Finset ℂ)
    (hZ : ∀ u ∈ Z, u ∈ closedBall c r ∧ riemannZeta₁ u = 0) :
    (Z.card : ℝ) ≤ ∑ᶠ u, (divisor riemannZeta₁ (closedBall c r) u : ℝ) := by
  set D := divisor riemannZeta₁ (closedBall c r)
  have hfin := D.finiteSupport (isCompact_closedBall c r)
  have hsub : (Function.support fun u => (D u : ℝ)) ⊆ hfin.toFinset := by
    intro u hu; simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hu
    simpa using hu
  rw [finsum_eq_sum_of_support_subset _ hsub]
  have hZs : Z ⊆ hfin.toFinset := by
    intro u hu
    have := one_le_divisor_zg (hZ u hu).1 (hZ u hu).2
    have h' : D u ≠ 0 := (lt_of_lt_of_le one_pos this).ne'
    simpa using h'
  calc (Z.card : ℝ) = ∑ u ∈ Z, (1 : ℝ) := by simp
    _ ≤ ∑ u ∈ Z, (D u : ℝ) := Finset.sum_le_sum fun u hu => by
        exact_mod_cast one_le_divisor_zg (hZ u hu).1 (hZ u hu).2
    _ ≤ ∑ u ∈ hfin.toFinset, (D u : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hZs fun u _ _ => by
          exact_mod_cast (zg_analytic _).divisor_nonneg u

/-- Jensen's inequality keeping the circle average (variant of Mathlib's
`AnalyticOnNhd.sum_divisor_le`). -/
theorem jensen_count {c : ℂ} {r R : ℝ} {f : ℂ → ℂ} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0) :
    (∑ᶠ u, (divisor f (closedBall c |r|) u : ℝ)) * Real.log (R / r) ≤
      Real.circleAverage (fun x ↦ Real.log ‖f x‖) c R - Real.log ‖f c‖ := by
  rw [finsum_mul]
  have jensen := h₁f.circleAverage_log_norm (abs_ne_zero.mp (by linarith)) h₂f
  calc
  _ ≤ ∑ᶠ u, ((divisor f (closedBall c |R|)) u) * Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_le_finsum ?_ ?_ fun u ↦ ?_
    · exact (divisor f (closedBall c |r|)).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · exact (divisor f (closedBall c |R|)).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · by_cases h1 : u ∈ closedBall c |R|
      · by_cases h2 : u ∈ closedBall c |r|
        · simp only [(h₁f.mono (closedBall_subset_closedBall r_lt_R.le)), h2,
            AnalyticOnNhd.divisor_apply, h₁f, h1]
          by_cases! h3 : u = c
          · rw [h3, (h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]
            simp
          simp +singlePass only [← Real.log_abs]
          gcongr 2
          · simp
          · exact abs_pos.2 (div_ne_zero (abs_pos.1 (r_pos.trans r_lt_R)) (abs_pos.1 r_pos))
          · have : ‖c - u‖ ≠ 0 := by simpa [sub_eq_zero] using h3.symm
            have hcu : 0 < ‖c - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm this)
            rw [mem_closedBall, dist_eq_norm'] at h2
            rw [abs_div, abs_mul, abs_inv, abs_norm, div_eq_mul_inv]
            gcongr
        · simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
            Int.cast_zero, zero_mul]
          refine mul_nonneg (mod_cast h₁f.divisor_nonneg ..) ?_
          apply Real.log_abs _ ▸ Real.log_nonneg
          simp only [mem_closedBall, dist_eq_norm', not_le] at h1 h2
          have : ‖c - u‖ ≠ 0 := (r_pos.trans h2).ne'
          simpa [field]
      · have : u ∉ closedBall c |r| := by
          simp_all
          linarith
        simp [h1, this]
  _ = _ := by linarith

/-- `‖ζ(s) - 1‖ ≤ π²/6 - 1` for `Re s ≥ 2`. -/
lemma norm_zeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have h2 : HasSum (fun n : ℕ => (1:ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' 2).2 hasSum_zeta_two
    simpa [Finset.sum_range_succ] using this
  have hb : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ ≤ (1:ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    have hn : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega)]
    apply one_div_le_one_div_of_le (by positivity)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
      (by push_cast; linarith)
  have hsum1 : Summable (fun n : ℕ => (1:ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    have := (summable_nat_add_iff 1).2 hasSum_zeta_two.summable
    simpa using this
  have hsN : Summable (fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖) :=
    hsum1.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith), hsN.of_norm.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, one_cpow, div_one, add_sub_cancel_left]
  calc ‖∑' n : ℕ, (1:ℂ) / ((((n + 1 : ℕ) : ℂ)) + 1) ^ s‖
      ≤ ∑' n : ℕ, ‖(1:ℂ) / ((((n + 1 : ℕ) : ℂ)) + 1) ^ s‖ :=
        norm_tsum_le_tsum_norm ((summable_nat_add_iff 1).2 hsN)
    _ ≤ ∑' n : ℕ, (1:ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 :=
        ((summable_nat_add_iff 1).2 hsN).tsum_le_tsum (fun n => hb (n + 1)) h2.summable
    _ = _ := h2.tsum_eq

lemma one_third_le_norm_zeta {s : ℂ} (hs : 2 ≤ s.re) : 1 / 3 ≤ ‖riemannZeta s‖ := by
  have h := norm_zeta_sub_one_le hs
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 2 / 3 := by
    have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
  have := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_sub_rev] at h
  simp at this
  linarith

lemma log_le_sq_half' (y : ℝ) (hy : 0 ≤ y) : Real.log y ≤ y ^ 2 / 2 := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp
  · have := Real.log_le_sub_one_of_pos h; nlinarith [sq_nonneg (y - 1)]

/-- Points within distance `R` of `2 + iτ`, `τ ≥ R + 2`, have imaginary part `≥ 2`. -/
lemma im_ge_two {τ R : ℝ} (hτ : R + 2 ≤ τ) {z : ℂ} (hz : ‖z - (2 + τ * I)‖ ≤ R) : 2 ≤ z.im := by
  have := abs_im_le_norm (z - (2 + τ * I))
  simp at this
  have := (abs_le.1 (this.trans hz)).1
  linarith

lemma continuous_zeta_circle {τ R : ℝ} (hR : 0 ≤ R) (hτ : R + 2 ≤ τ) :
    Continuous fun θ : ℝ => riemannZeta (circleMap (2 + τ * I) R θ) := by
  rw [continuous_iff_continuousAt]; intro θ
  have hm : ‖circleMap (2 + τ * I) R θ - (2 + τ * I)‖ ≤ R := by
    have := circleMap_mem_sphere' (2 + τ * I) R θ
    rw [mem_sphere_iff_norm, abs_of_nonneg hR] at this; exact this.le
  have hne : circleMap (2 + τ * I) R θ ≠ 1 := by
    intro h; have := im_ge_two hτ hm; rw [h] at this; simp at this; linarith
  exact (differentiableAt_riemannZeta hne).continuousAt.comp
    (continuous_circleMap _ _).continuousAt

/-- **Jensen count on one disc.** -/
theorem disc_count {σ R r h τ : ℝ} (hσ2 : σ ≤ 2) (hd : (2 - σ) ^ 2 + h ^ 2 ≤ r ^ 2)
    (hr : 0 < r) (hrR : r < R) (hτ : R + 2 ≤ τ) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ |ρ.im - τ| ≤ h) :
    (Z.card : ℝ) * Real.log (R / r) ≤
      R + 2 + Real.circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) (2 + τ * I) R := by
  set c : ℂ := 2 + τ * I with hc
  have hR : 0 < R := hr.trans hrR
  have hc1 : 1 ≤ ‖c - 1‖ := by
    have := abs_im_le_norm (c - 1); simp only [hc, sub_im, add_im, im_ofNat, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, zero_add, one_im, sub_zero] at this
    rw [abs_of_pos (by linarith)] at this; linarith
  have hcne : c ≠ 1 := by intro h; rw [h] at hc1; norm_num at hc1
  have hζc : 1 / 3 ≤ ‖riemannZeta c‖ := one_third_le_norm_zeta (by simp [hc])
  have hzc : riemannZeta₁ c ≠ 0 := by
    rw [zg_eq hcne]; refine mul_ne_zero (sub_ne_zero.2 hcne) ?_
    intro h; rw [h] at hζc; norm_num at hζc
  -- count ≤ divisor sum
  have hcount : (Z.card : ℝ) ≤ ∑ᶠ u, (divisor riemannZeta₁ (closedBall c |r|) u : ℝ) := by
    rw [abs_of_pos hr]
    apply card_le_finsum_divisor
    intro ρ hρ
    obtain ⟨h0, hre, him, hh⟩ := hZ ρ hρ
    have hρ1 : ρ ≠ 1 := by intro e; rw [e] at him; simp at him
    have hlt : ρ.re < 1 := by
      by_contra hh'; exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hh') h0
    refine ⟨?_, by rw [zg_eq hρ1, h0, mul_zero]⟩
    rw [mem_closedBall, dist_eq_norm]
    have e : ‖ρ - c‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - τ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply, hc]; ring
    have h1 : (ρ.re - 2) ^ 2 ≤ (2 - σ) ^ 2 := by nlinarith
    have h2 : (ρ.im - τ) ^ 2 ≤ h ^ 2 := by
      have := sq_abs (ρ.im - τ); nlinarith [abs_nonneg (ρ.im - τ)]
    nlinarith [norm_nonneg (ρ - c)]
  have hL : 0 ≤ Real.log (R / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have hJ := jensen_count (c := c) (f := riemannZeta₁) (r := r) (R := R)
    (by rw [abs_of_pos hr]; exact hr) (by rw [abs_of_pos hr, abs_of_pos hR]; exact hrR)
    (zg_analytic _) hzc
  -- circle bound
  have hsph : ∀ z ∈ sphere c |R|, ‖z - c‖ ≤ R := by
    intro z hz; rw [mem_sphere_iff_norm, abs_of_pos hR] at hz; exact hz.le
  have hI1 : CircleIntegrable (fun x => Real.log ‖riemannZeta₁ x‖) c R :=
    (zg_analytic (sphere c |R|)).meromorphicOn.circleIntegrable_log_norm
  have hI2 : CircleIntegrable (fun z => ‖riemannZeta z‖ ^ 2 / 2) c R :=
    (((continuous_zeta_circle hR.le hτ).norm.pow 2).div_const 2).intervalIntegrable _ _
  have hI3 : CircleIntegrable (fun _ : ℂ => Real.log (‖c - 1‖ + R)) c R :=
    circleIntegrable_const _ _ _
  have hmono : Real.circleAverage (fun x => Real.log ‖riemannZeta₁ x‖) c R ≤
      Real.circleAverage (fun z => Real.log (‖c - 1‖ + R) + ‖riemannZeta z‖ ^ 2 / 2) c R := by
    apply Real.circleAverage_mono hI1 (hI3.add hI2)
    intro z hz
    have hzR := hsph z hz
    have h2 := im_ge_two hτ hzR
    have hz1 : z ≠ 1 := by intro e; rw [e] at h2; simp at h2; linarith
    have hz1' : 1 ≤ ‖z - 1‖ := by
      have := abs_im_le_norm (z - 1); simp only [sub_im, one_im, sub_zero] at this
      rw [abs_of_pos (by linarith)] at this; linarith
    have hzle : ‖z - 1‖ ≤ ‖c - 1‖ + R := by
      have := norm_sub_le_norm_sub_add_norm_sub z c 1
      linarith
    have hlog1 : Real.log ‖z - 1‖ ≤ Real.log (‖c - 1‖ + R) :=
      Real.log_le_log (by linarith) hzle
    have hlog2 := log_le_sq_half' ‖riemannZeta z‖ (norm_nonneg _)
    rw [zg_eq hz1, norm_mul]
    change _ ≤ Real.log (‖c - 1‖ + R) + ‖riemannZeta z‖ ^ 2 / 2
    by_cases hζ : riemannZeta z = 0
    · have := Real.log_nonneg (show (1:ℝ) ≤ ‖c - 1‖ + R by linarith)
      simp only [hζ, norm_zero, mul_zero, Real.log_zero]
      positivity
    · rw [Real.log_mul (by positivity) (norm_ne_zero_iff.2 hζ)]
      linarith
  rw [show (fun z => Real.log (‖c - 1‖ + R) + ‖riemannZeta z‖ ^ 2 / 2) =
      (fun _ => Real.log (‖c - 1‖ + R)) + (fun z => ‖riemannZeta z‖ ^ 2 / 2) from rfl,
    Real.circleAverage_add hI3 hI2, Real.circleAverage_const] at hmono
  have hlogc : Real.log ‖c - 1‖ + Real.log (1 / 3) ≤ Real.log ‖riemannZeta₁ c‖ := by
    rw [zg_eq hcne, norm_mul, Real.log_mul (by positivity) (by positivity)]
    gcongr
  have hlog3 : -2 ≤ Real.log (1 / 3) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3); linarith
  have hlogR : Real.log (‖c - 1‖ + R) - Real.log ‖c - 1‖ ≤ R := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < (‖c - 1‖ + R) / ‖c - 1‖)
    have e : (‖c - 1‖ + R) / ‖c - 1‖ - 1 = R / ‖c - 1‖ := by field_simp; ring
    have : R / ‖c - 1‖ ≤ R := div_le_self hR.le hc1
    linarith
  have := mul_le_mul_of_nonneg_right hcount hL
  linarith

lemma circleMap_eq_sl (τ R θ : ℝ) :
    circleMap (2 + τ * I) R θ = sl (2 + R * Real.cos θ) (τ + R * Real.sin θ) := by
  apply Complex.ext <;> simp [circleMap, sl, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The clamped integrand `(τ, θ) ↦ |ζ(circle point)|²/2` is jointly continuous. -/
lemma continuous_F {R : ℝ} (hR : 0 ≤ R) :
    Continuous (Function.uncurry fun τ θ : ℝ =>
      ‖riemannZeta (circleMap (2 + (max τ (R + 2) : ℝ) * I) R θ)‖ ^ 2 / 2) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap (2 + (max p.1 (R + 2) : ℝ) * I) R p.2) := by
    unfold circleMap; fun_prop
  refine (Continuous.div_const (Continuous.pow (Continuous.norm ?_) 2) 2)
  rw [continuous_iff_continuousAt]; intro p
  have hτ : R + 2 ≤ max p.1 (R + 2) := le_max_right _ _
  have hm : ‖circleMap (2 + (max p.1 (R + 2) : ℝ) * I) R p.2 - (2 + (max p.1 (R + 2) : ℝ) * I)‖
      ≤ R := by
    have := circleMap_mem_sphere' (2 + (max p.1 (R + 2) : ℝ) * I) R p.2
    rw [mem_sphere_iff_norm, abs_of_nonneg hR] at this; exact this.le
  have hne : circleMap (2 + (max p.1 (R + 2) : ℝ) * I) R p.2 ≠ 1 := by
    intro e; have := im_ge_two hτ hm; rw [e] at this; simp at this; linarith
  exact (differentiableAt_riemannZeta hne).continuousAt.comp (f := fun p : ℝ × ℝ => circleMap (2 + (max p.1 (R + 2) : ℝ) * I) R p.2) hc.continuousAt

/-- Interval integral of the indicator of `[p,q] ⊆ (a,b]`. -/
lemma integral_indicator_Icc {a b p q : ℝ} (hap : a < p) (hpq : p ≤ q) (hqb : q ≤ b) :
    (∫ τ in a..b, (Icc p q).indicator (fun _ => (1:ℝ)) τ) = q - p := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.2 (Icc_subset_Ioc_iff hpq |>.2 ⟨hap, hqb⟩)]
  simp [Real.volume_real_Icc_of_le hpq]

/-- Integrated Jensen count: zeros with imaginary part in `[R+h+3, T]`. -/
@[blueprint
  "zd-high-count"
  (title := "Zero counting via Jensen")
  (statement := /--
    Let $0<r<R$, $0<h$, $\sigma\le 2$, $(2-\sigma)^2+h^2\le r^2$, $2+R\le 4$ and $\sigma_0\le 2-R$.
    Assume $\int_\alpha^\beta|\zeta(x+it)|^2\,dt\le C\beta$ uniformly for $\sigma_0\le x\le 4$ and
    $2\le\alpha\le\beta$. If $Z$ is a finite set of zeros of $\zeta$ with $\Re\rho\ge\sigma$ and
    $R+h+3\le\Im\rho\le T$, then
    $$|Z|\cdot(2h)\log(R/r)
      \le(R+2)\bigl((T+R+2h+3)-(R+2)\bigr)+C\bigl((T+R+2h+3)+R\bigr)/2.$$
  -/)]
theorem high_count {σ σ₀ R r h C : ℝ} (hσ2 : σ ≤ 2) (hd : (2 - σ) ^ 2 + h ^ 2 ≤ r ^ 2)
    (hr : 0 < r) (hrR : r < R) (hh : 0 < h) (hR4 : 2 + R ≤ 4) (hRσ : σ₀ ≤ 2 - R) (hC : 0 ≤ C)
    (hU : ∀ x, σ₀ ≤ x → x ≤ 4 → ∀ α β, 2 ≤ α → α ≤ β →
      (∫ t in α..β, ‖riemannZeta (sl x t)‖ ^ 2) ≤ C * β)
    (T : ℝ) (hT : 0 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ R + h + 3 ≤ ρ.im ∧ ρ.im ≤ T) :
    (Z.card : ℝ) * (2 * h) * Real.log (R / r) ≤
      (R + 2) * ((T + R + 2 * h + 3) - (R + 2)) + C * ((T + R + 2 * h + 3) + R) / 2 := by
  set a := R + 2 with ha
  set b := T + R + 2 * h + 3 with hb
  set L := Real.log (R / r)
  have hR0 : 0 ≤ R := by linarith
  have hab : a ≤ b := by linarith
  set F : ℝ → ℝ → ℝ := fun τ θ =>
    ‖riemannZeta (circleMap (2 + (max τ (R + 2) : ℝ) * I) R θ)‖ ^ 2 / 2 with hF
  have hFc : Continuous (Function.uncurry F) := continuous_F hR0
  clear_value F
  set G : ℝ → ℝ := fun τ => (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, F τ θ with hG
  have hGc : Continuous G :=
    continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFc _ _)
  set cnt : ℝ → ℝ := fun τ => ∑ ρ ∈ Z, (Icc (ρ.im - h) (ρ.im + h)).indicator (fun _ => (1:ℝ)) τ
  have hind : ∀ ρ : ℂ, IntervalIntegrable
      ((Icc (ρ.im - h) (ρ.im + h)).indicator (fun _ => (1:ℝ))) volume a b := by
    intro ρ
    rw [intervalIntegrable_iff]
    exact (integrableOn_const (by simp)).indicator measurableSet_Icc
  have hcntI : IntervalIntegrable cnt volume a b := by
    have := IntervalIntegrable.sum Z (fun ρ _ => hind ρ)
    convert this using 1; funext τ; simp [cnt, Finset.sum_apply]
  -- pointwise bound
  have hpt : ∀ τ ∈ Icc a b, cnt τ * L ≤ R + 2 + G τ := by
    intro τ hτ
    have hτa : R + 2 ≤ τ := hτ.1
    have hcard : cnt τ = ((Z.filter (fun ρ => τ ∈ Icc (ρ.im - h) (ρ.im + h))).card : ℝ) := by
      simp only [cnt, Set.indicator_apply]
      rw [Finset.sum_boole]
    have hG' : G τ = Real.circleAverage (fun z => ‖riemannZeta z‖ ^ 2 / 2) (2 + τ * I) R := by
      simp only [G, hF, Real.circleAverage_def, max_eq_left hτa, smul_eq_mul]
    rw [hcard, hG']
    refine disc_count hσ2 hd hr hrR hτa _ ?_
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨h1, h2, h3, h4⟩ := hZ ρ hρ.1
    refine ⟨h1, h2, by linarith, abs_le.2 ⟨by linarith [hρ.2.2], by linarith [hρ.2.1]⟩⟩
  have hmono := intervalIntegral.integral_mono_on hab (hcntI.mul_const L)
    ((intervalIntegrable_const).add (hGc.intervalIntegrable a b)) hpt
  -- left side
  have hleft : (∫ τ in a..b, cnt τ * L) = (Z.card : ℝ) * (2 * h) * L := by
    rw [intervalIntegral.integral_mul_const]
    simp only [cnt]
    rw [intervalIntegral.integral_finsetSum (fun ρ _ => hind ρ)]
    rw [Finset.sum_congr rfl (g := fun _ => 2 * h)]
    · simp
    intro ρ hρ
    obtain ⟨-, -, h3, h4⟩ := hZ ρ hρ
    rw [integral_indicator_Icc (by linarith) (by linarith) (by linarith)]; ring
  -- right side
  have hθ : ∀ θ : ℝ, (∫ τ in a..b, F τ θ) ≤ C * (b + R) / 2 := by
    intro θ
    set x := 2 + R * Real.cos θ
    set y := R * Real.sin θ
    have hcos := Real.neg_one_le_cos θ
    have hcos' := Real.cos_le_one θ
    have hsin := Real.neg_one_le_sin θ
    have hsin' := Real.sin_le_one θ
    have hy1 : -R ≤ y := by nlinarith
    have hy2 : y ≤ R := by nlinarith
    have hx1 : σ₀ ≤ x := by nlinarith
    have hx2 : x ≤ 4 := by nlinarith
    have hcongr : (∫ τ in a..b, F τ θ) =
        ∫ τ in a..b, (fun t => ‖riemannZeta (sl x t)‖ ^ 2 / 2) (τ + y) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      rw [Set.uIcc_of_le hab] at hτ
      simp only [hF, max_eq_left (show R + 2 ≤ τ from hτ.1), circleMap_eq_sl]
      rfl
    rw [hcongr, intervalIntegral.integral_comp_add_right (fun t => ‖riemannZeta (sl x t)‖ ^ 2 / 2) y,
      intervalIntegral.integral_div]
    have := hU x hx1 hx2 (a + y) (b + y) (by linarith) (by linarith)
    have : C * (b + y) ≤ C * (b + R) := mul_le_mul_of_nonneg_left (by linarith) hC
    linarith
  have hswap : (∫ τ in a..b, ∫ θ in (0:ℝ)..2 * Real.pi, F τ θ) =
      ∫ θ in (0:ℝ)..2 * Real.pi, ∫ τ in a..b, F τ θ := by
    apply intervalIntegral_intervalIntegral_swap
    exact (hFc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hinner : (∫ θ in (0:ℝ)..2 * Real.pi, ∫ τ in a..b, F τ θ) ≤ 2 * Real.pi * (C * (b + R) / 2) := by
    have hc2 : Continuous (fun θ => ∫ τ in a..b, F τ θ) := by
      have : Continuous (Function.uncurry fun θ τ => F τ θ) := by
        have h2 := hFc.comp continuous_swap
        exact h2
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this _ _
    have := intervalIntegral.integral_mono_on (by positivity : (0:ℝ) ≤ 2 * Real.pi)
      (hc2.intervalIntegrable (μ := volume) _ _) (intervalIntegrable_const (μ := volume) (c := C * (b + R) / 2))
      (fun θ _ => hθ θ)
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  have hright : (∫ τ in a..b, (R + 2 + G τ)) ≤ (R + 2) * (b - a) + C * (b + R) / 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hGc.intervalIntegrable a b)]
    simp only [G]
    rw [intervalIntegral.integral_const_mul, hswap, intervalIntegral.integral_const, smul_eq_mul]
    have hpi : 0 < 2 * Real.pi := by positivity
    have : (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2 * Real.pi, ∫ τ in a..b, F τ θ) ≤ C * (b + R) / 2 := by
      rw [inv_mul_le_iff₀ hpi]; exact hinner
    nlinarith
  rw [hleft] at hmono
  linarith

end ZeroDensity
