/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import PrimeNumberTheoremAnd.IEANTN.KadiriContourShift
import PrimeNumberTheoremAnd.IEANTN.KadiriFunctionalEquation
import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeights
import PrimeNumberTheoremAnd.IEANTN.KadiriU6aEndpointClose
import PrimeNumberTheoremAnd.Backlund.ZeroCountCrude
import PrimeNumberTheoremAnd.ZetaConj
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The explicit-formula contour pull (sprint unit U6)

Assembly of the `T → ∞` limit for the Kadiri explicit-formula contour: the rectangle
integrals of `(-ζ'/ζ)(z) · (-Φ(-z))` between the vertical lines `Re z = -(1+a)` and
`Re z = σR > 1` converge, along a sequence of good heights, to the difference of the
two vertical integrals; combined with the residue identity
`rectangleIntegral'_negLogDeriv_riemannZeta_mul_negCoeff_eq_zeroes_sum_sub_pole_one`
this exhibits the limit of the partial zero sums.

The horizontal edges cross the critical strip. On the sub-`(1)` part the required
bound on `-ζ'/ζ` at well-chosen heights is classical but not yet in the tree; it is
banked here as `horizontalSegmentLogDerivBound` together with the sorried classical
target `exists_arbitrarily_large_horizontalSegmentLogDerivBound` (sub-unit U6a). All
other inputs are proved: the left vertical line integrability comes from the
functional-equation bound of `KadiriFunctionalEquation` with its digamma hypothesis
discharged by `Complex.exists_norm_digamma_div_two_le_log`, and the right line from
the `Re > 1` edge estimates in `Kadiri.lean`.
-/

open Complex MeasureTheory Filter Set

namespace Kadiri

/-! ## The digamma input to the functional-equation bound -/

/-- The digamma strip bound consumed by `left_logDeriv_le_log_of_functional_equation`,
discharged by the digamma series machinery of `DigammaSeries.lean`. -/
theorem digamma_strip_bound {α β : ℝ} (hα : 0 < α) :
    ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ w : ℂ, α ≤ w.re → w.re ≤ β →
      ‖digamma (w / 2)‖ ≤ Cψ * Real.log (|w.im| + 2) :=
  Complex.exists_norm_digamma_div_two_le_log hα

/-! ## Nonvanishing of `ζ` between the trivial zeros -/

/-- `ζ` does not vanish on the strip `-2 < Re z < 0`: non-real zeros lie in the closed
critical strip, and on the real segment every factor of the functional equation is
nonzero. In particular `ζ` does not vanish on the left contour line `Re z = -(1+a)`
for `0 < a < 1`. -/
lemma riemannZeta_ne_zero_of_re_mem_Ioo_neg {z : ℂ} (h2 : -2 < z.re) (h0 : z.re < 0) :
    riemannZeta z ≠ 0 := by
  intro hzero
  rcases lt_trichotomy z.im 0 with him | him | him
  · -- conjugate to positive imaginary part and use the strip localization
    have hconj0 : riemannZeta (starRingEnd ℂ z) = 0 := by
      have h := conj_riemannZeta_conj z
      rw [hzero] at h
      have h' := congrArg (starRingEnd ℂ) h
      simpa using h'
    have him' : 0 < (starRingEnd ℂ z).im := by
      rw [Complex.conj_im]
      linarith
    have hloc := Backlund.zeta_zero_re_mem_of_im_pos hconj0 him'
    rw [Complex.conj_re] at hloc
    linarith [hloc.1]
  · -- real point: peel the factors of the functional equation
    have hz_eq : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him]
    set s : ℂ := 1 - z with hs_def
    have hs_re : s.re = 1 - z.re := by
      rw [hs_def]
      simp
    have hs1 : (1 : ℝ) < s.re := by rw [hs_re]; linarith
    have hsne : ∀ n : ℕ, s ≠ -n := by
      intro n h
      have hre : s.re = -(n : ℝ) := by rw [h]; simp
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hre] at hs1
      linarith
    have hsne1 : s ≠ 1 := by
      intro h
      rw [h] at hs1
      simp at hs1
    have hFE := riemannZeta_one_sub hsne hsne1
    have h1s : (1 : ℂ) - s = z := by rw [hs_def]; ring
    rw [h1s, hzero] at hFE
    have hprod := hFE.symm
    have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
    have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    have hpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
      have hbase : (2 * (Real.pi : ℂ)) ≠ 0 := by
        intro h
        apply h2π
        rw [← h]
        push_cast
        ring
      rw [Complex.cpow_def_of_ne_zero hbase]
      exact Complex.exp_ne_zero _
    have hΓ : Gamma s ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m h
      have hre : s.re = -(m : ℝ) := by rw [h]; simp
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hre] at hs1
      linarith
    have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
    have hcos : Complex.cos (Real.pi * s / 2) ≠ 0 := by
      have hs_real : s = ((1 - z.re : ℝ) : ℂ) := by
        rw [hs_def]
        nth_rewrite 1 [hz_eq]
        push_cast
        ring
      intro hc
      have hcast : Complex.cos (((Real.pi * (1 - z.re) / 2 : ℝ)) : ℂ) = 0 := by
        rw [← hc, hs_real]
        push_cast
        ring_nf
      rw [← Complex.ofReal_cos] at hcast
      have hr : Real.cos (Real.pi * (1 - z.re) / 2) = 0 := by exact_mod_cast hcast
      rw [Real.cos_eq_zero_iff] at hr
      obtain ⟨n, hn⟩ := hr
      have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
      have hx_eq : 1 - z.re = 2 * (n : ℝ) + 1 := by
        have h1 : Real.pi * (1 - z.re) / 2 = Real.pi * (2 * (n : ℝ) + 1) / 2 := by
          rw [hn]
          ring
        have h2 : Real.pi * (1 - z.re) = Real.pi * (2 * (n : ℝ) + 1) := by
          linarith
        exact mul_left_cancel₀ hπ.ne' h2
      have hn_bounds : (0 : ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 := by
        constructor <;> nlinarith
      have hn0 : (0 : ℤ) < n := by exact_mod_cast hn_bounds.1
      have hn1 : n < (1 : ℤ) := by exact_mod_cast hn_bounds.2
      omega
    simp only [mul_eq_zero] at hprod
    rcases hprod with (((h | h) | h) | h) | h
    · exact h2ne h
    · exact hpow h
    · exact hΓ h
    · exact hcos h
    · exact hζs h
  · -- positive imaginary part: directly inside the closed critical strip
    have hloc := Backlund.zeta_zero_re_mem_of_im_pos hzero him
    linarith [hloc.1]

/-! ## Integrability on the left vertical line -/

private lemma log_le_two_mul_sqrt' {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]
    ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
  have h3 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  linarith

/-- A continuous function on `ℝ` whose norm is eventually dominated by
`C · log (|t| + 2) / t²` is integrable. -/
lemma integrable_of_norm_le_log_div_sq {F : ℝ → ℂ} {C : ℝ} (hcont : Continuous F)
    (hbound : ∀ t : ℝ, 1 ≤ |t| → ‖F t‖ ≤ C * Real.log (|t| + 2) / t ^ 2) :
    MeasureTheory.Integrable F := by
  set C' : ℝ := max C 0 with hC'_def
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hC' : ∀ t : ℝ, 1 ≤ |t| → ‖F t‖ ≤ C' * Real.log (|t| + 2) / t ^ 2 := by
    intro t ht
    refine (hbound t ht).trans ?_
    have hlog : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    have ht2 : (0 : ℝ) < t ^ 2 := by nlinarith [sq_abs t]
    gcongr
    exact le_max_left C 0
  set c : ℝ := 2 * Real.sqrt 3 * C' with hc_def
  have hc0 : 0 ≤ c := by positivity
  have htail_bound : ∀ u : ℝ, 1 ≤ u →
      C' * Real.log (u + 2) / u ^ 2 ≤ c * u ^ (-(3 : ℝ) / 2) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hlog : Real.log (u + 2) ≤ 2 * Real.sqrt (u + 2) :=
      log_le_two_mul_sqrt' (by linarith)
    have hsq : Real.sqrt (u + 2) ≤ Real.sqrt 3 * Real.sqrt u := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hkey : u ^ (-(3 : ℝ) / 2) = Real.sqrt u / u ^ 2 := by
      have h1 : (-(3 : ℝ) / 2) = (1 : ℝ) / 2 - 2 := by norm_num
      rw [h1, Real.rpow_sub hu0, Real.sqrt_eq_rpow,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hchain : C' * Real.log (u + 2) / u ^ 2 ≤ c * (Real.sqrt u / u ^ 2) := by
      have hu2 : (0 : ℝ) < u ^ 2 := by positivity
      rw [hc_def]
      rw [div_le_iff₀ hu2]
      have h1 : C' * Real.log (u + 2) ≤ C' * (2 * (Real.sqrt 3 * Real.sqrt u)) := by
        apply mul_le_mul_of_nonneg_left _ hC'0
        calc Real.log (u + 2) ≤ 2 * Real.sqrt (u + 2) := hlog
          _ ≤ 2 * (Real.sqrt 3 * Real.sqrt u) := by
              apply mul_le_mul_of_nonneg_left hsq (by norm_num)
      calc C' * Real.log (u + 2) ≤ C' * (2 * (Real.sqrt 3 * Real.sqrt u)) := h1
        _ = 2 * Real.sqrt 3 * C' * (Real.sqrt u / u ^ 2) * u ^ 2 := by
            field_simp
    rw [hkey]
    exact hchain
  have hbase_int : IntegrableOn (fun u : ℝ => u ^ (-(3 : ℝ) / 2)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := 1) (by norm_num) one_pos
  have hG_int : IntegrableOn (fun u : ℝ => c * u ^ (-(3 : ℝ) / 2)) (Set.Ioi 1) :=
    hbase_int.const_mul c
  have hsplit : (Set.univ : Set ℝ) = Set.Iio (-1) ∪ Set.Icc (-1) 1 ∪ Set.Ioi 1 := by
    ext u
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, true_iff]
    by_cases h1 : u < -1
    · exact Or.inl (Or.inl h1)
    · by_cases hu2 : u ≤ 1
      · exact Or.inl (Or.inr ⟨le_of_not_gt h1, hu2⟩)
      · exact Or.inr (by linarith)
  rw [← MeasureTheory.integrableOn_univ, hsplit]
  refine MeasureTheory.IntegrableOn.union (MeasureTheory.IntegrableOn.union ?_ ?_) ?_
  · -- negative tail: bound the reflected function on the positive tail, then reflect back
    have hFneg : IntegrableOn (fun t : ℝ => F (-t)) (Set.Ioi 1) := by
      apply MeasureTheory.Integrable.mono' hG_int
        ((hcont.comp continuous_neg).aestronglyMeasurable.restrict)
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
      have habs : |(-u)| = u := by
        rw [abs_neg, abs_of_pos (by linarith)]
      refine (hC' (-u) (by rw [habs]; exact hu1)).trans ?_
      rw [habs]
      have h2 : (-u) ^ 2 = u ^ 2 := by ring
      rw [h2]
      exact htail_bound u hu1
    have hcomp : IntegrableOn (fun x : ℝ => F (-(-x))) (Set.Iio (-1)) := by
      apply MeasureTheory.IntegrableOn.comp_neg_Iio (c := (-1 : ℝ))
        (f := fun t : ℝ => F (-t))
      rw [show (-(-1 : ℝ)) = 1 by norm_num]
      exact hFneg
    exact hcomp.congr_fun (fun x _ => by rw [neg_neg]) measurableSet_Iio
  · -- compact middle
    exact (hcont.integrableOn_Icc)
  · -- positive tail
    apply MeasureTheory.Integrable.mono' hG_int
      (hcont.aestronglyMeasurable.restrict)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    have habs : |u| = u := abs_of_pos (by linarith)
    refine (hC' u (by rw [habs]; exact hu1)).trans ?_
    rw [habs]
    exact htail_bound u hu1

/-- Continuity of the contour integrand on the left vertical line `Re z = -(1+a)`. -/
lemma continuous_left_line_integrand {Φ : ℂ → ℂ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hΦ_cont : Continuous fun t : ℝ => Φ (-(verticalLine (-(1 + a)) t))) :
    Continuous fun t : ℝ =>
      (-deriv riemannZeta (verticalLine (-(1 + a)) t) /
          riemannZeta (verticalLine (-(1 + a)) t)) *
        Φ (-(verticalLine (-(1 + a)) t)) := by
  have hline : Continuous fun t : ℝ => verticalLine (-(1 + a)) t := by
    unfold verticalLine
    exact continuous_const.add (continuous_ofReal.mul continuous_const)
  have hre : ∀ t : ℝ, (verticalLine (-(1 + a)) t).re = -(1 + a) := by
    intro t
    unfold verticalLine
    simp
  have hzcont : Continuous fun t : ℝ =>
      -deriv riemannZeta (verticalLine (-(1 + a)) t) /
        riemannZeta (verticalLine (-(1 + a)) t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne1 : verticalLine (-(1 + a)) t ≠ 1 := by
      intro h
      have h1 : (verticalLine (-(1 + a)) t).re = 1 := by rw [h]; simp
      rw [hre t] at h1
      linarith
    have hne0 : riemannZeta (verticalLine (-(1 + a)) t) ≠ 0 := by
      apply riemannZeta_ne_zero_of_re_mem_Ioo_neg
      · rw [hre t]; linarith
      · rw [hre t]; linarith
    have hcomp : ContinuousAt
        ((fun z : ℂ => -deriv riemannZeta z / riemannZeta z) ∘
          fun t : ℝ => verticalLine (-(1 + a)) t) t :=
      ContinuousAt.comp (continuousAt_neg_deriv_riemannZeta_div hne1 hne0)
        hline.continuousAt
    exact hcomp
  exact hzcont.mul hΦ_cont

/-- Integrability of the contour integrand on the left vertical line `Re z = -(1+a)`,
combining the functional-equation bound (with its digamma hypothesis discharged by the
digamma series machinery) with the generic `log/t²` integrability criterion. This is
the `hleft` input to the contour pull. -/
theorem integrable_left_line_neg_logDeriv_mul {Φ : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hΦ_cont : Continuous fun t : ℝ => Φ (-(verticalLine (-(1 + a)) t)))
    (hΦ : ∃ CΦ : ℝ, 0 ≤ CΦ ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Φ (-(verticalLine (-(1 + a)) t))‖ ≤ CΦ / t ^ 2) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (-deriv riemannZeta (verticalLine (-(1 + a)) t) /
          riemannZeta (verticalLine (-(1 + a)) t)) *
        Φ (-(verticalLine (-(1 + a)) t))) := by
  obtain ⟨C, hC0, hC⟩ := left_vertical_integrable_of_functional_equation ha hab ha1 hΦ
    (fun {α β} hα => digamma_strip_bound hα)
  exact integrable_of_norm_le_log_div_sq
    (continuous_left_line_integrand ha ha1 hΦ_cont) hC

/-! ## The good-heights bound (sub-unit U6a)

`exists_arbitrarily_large_horizontalSegmentLogDerivBound` is proved in
`KadiriU6aEndpointClose` (three-region clip over the unconditional zero-sum
remainder and local zero-count bounds) and imported here. -/

/-! ## The rectangle limit along a sequence of heights -/

/-- Sequence version of `RectangleIntegral_tendsTo_VerticalIntegral`: if the contour
integrand is integrable on the two vertical lines and its horizontal edge integrals
vanish along a sequence of heights tending to infinity, then the rectangle integrals
along that sequence converge to the difference of the two vertical integrals. -/
lemma rectangleIntegral_tendsto_verticalIntegral_of_seq {F : ℂ → ℂ} {σL σR : ℝ}
    {T : ℕ → ℝ} (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hleft : MeasureTheory.Integrable fun t : ℝ => F (σL + t * I))
    (hright : MeasureTheory.Integrable fun t : ℝ => F (σR + t * I))
    (hbot : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR, F (x + (-(T k)) * I))
      Filter.atTop (nhds 0))
    (htop : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR, F (x + (T k) * I))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k : ℕ => RectangleIntegral F ((σL : ℂ) - I * (T k)) ((σR : ℂ) + I * (T k)))
      Filter.atTop
      (nhds (VerticalIntegral F σR - VerticalIntegral F σL)) := by
  simp only [RectangleIntegral, HIntegral, VIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul,
    I_im, ofReal_im, mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im, one_mul,
    zero_add, zero_sub, add_im, Complex.ofReal_neg]
  apply Filter.Tendsto.sub
  · rw [← zero_add (VerticalIntegral _ _), ← zero_sub_zero]
    apply Filter.Tendsto.add (Filter.Tendsto.sub hbot htop)
    exact (MeasureTheory.intervalIntegral_tendsto_integral hright
      (tendsto_neg_atTop_atBot.comp hT) hT).const_smul I
  · exact (MeasureTheory.intervalIntegral_tendsto_integral hleft
      (tendsto_neg_atTop_atBot.comp hT) hT).const_smul I

/-! ## The contour pull -/


/-- U6 headline: along a sequence of good heights, the partial zero sums of `Φ(-ρ)`
over the rectangle `[σL, σR] × [-T k, T k]` converge to the normalized difference of the
two vertical integrals plus the pole contribution `Φ(-1)`. The vertical-line
integrability and horizontal-edge vanishing are named hypotheses, dischargeable from
`integrable_left_line_neg_logDeriv_mul`, the `Re > 1` edge estimates of `Kadiri.lean`,
and `horizontalSegmentLogDerivBound` (sub-unit U6a). -/
theorem tendsto_zeroes_sum_of_good_heights {Φ : ℂ → ℂ} {σL σR : ℝ} {T : ℕ → ℝ}
    (hσL2 : -2 < σL) (hσL0 : σL < 0) (hσR : 1 < σR)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (hT0 : ∀ k, 0 < T k)
    (hgood : ∀ k, horizontalSegmentZeroFree σL σR (T k))
    (hΦ_an : ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR → AnalyticAt ℂ (fun u => Φ (-u)) s)
    (hleft : MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σL : ℂ) + t * I) * (-(Φ (-((σL : ℂ) + t * I)))))
    (hright : MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σR : ℂ) + t * I) * (-(Φ (-((σR : ℂ) + t * I)))))
    (hbot : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
        -logDeriv riemannZeta ((x : ℂ) + (-(T k)) * I) *
          (-(Φ (-((x : ℂ) + (-(T k)) * I))))) Filter.atTop (nhds 0))
    (htop : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
        -logDeriv riemannZeta ((x : ℂ) + (T k) * I) *
          (-(Φ (-((x : ℂ) + (T k) * I))))) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k : ℕ => riemannZeta.zeroes_sum (Set.uIcc σL σR) (Set.uIcc (-(T k)) (T k))
        (fun ρ => Φ (-ρ)))
      Filter.atTop
      (nhds ((1 / (2 * (Real.pi : ℂ) * I)) •
        (VerticalIntegral (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) σR -
          VerticalIntegral (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) σL) +
        Φ (-1))) := by
  set F : ℂ → ℂ := fun s => -logDeriv riemannZeta s * (-(Φ (-s))) with hF_def
  have hσLR : σL ≤ σR := by linarith
  -- the residue identity at each good height
  have hres : ∀ k : ℕ,
      riemannZeta.zeroes_sum (Set.uIcc σL σR) (Set.uIcc (-(T k)) (T k)) (fun ρ => Φ (-ρ))
        = RectangleIntegral' F ((σL : ℂ) - I * (T k)) ((σR : ℂ) + I * (T k)) + Φ (-1) := by
    intro k
    have hzre : ((σL : ℂ) - I * (T k)).re = σL := by simp
    have hzim : ((σL : ℂ) - I * (T k)).im = -(T k) := by simp
    have hwre : ((σR : ℂ) + I * (T k)).re = σR := by simp
    have hwim : ((σR : ℂ) + I * (T k)).im = T k := by simp
    have h911 :=
      rectangleIntegral'_negLogDeriv_riemannZeta_mul_negCoeff_eq_zeroes_sum_sub_pole_one
        (z := (σL : ℂ) - I * (T k)) (w := (σR : ℂ) + I * (T k)) (Φ := Φ)
        (by rw [hzre, hwre]; exact hσLR)
        (by rw [hzim, hwim]; linarith [hT0 k])
        ?_ ?_ ?_
    · rw [hzre, hzim, hwre, hwim] at h911
      rw [h911]
      ring
    · -- 1 is inside the rectangle
      rw [Rectangle, Complex.mem_reProdIm, hzre, hzim, hwre, hwim]
      constructor
      · rw [Set.uIcc_of_le hσLR]
        constructor
        · simpa using hσL0.le.trans (by norm_num)
        · simpa using hσR.le
      · rw [Set.uIcc_of_le (by linarith [hT0 k] : -(T k) ≤ T k)]
        constructor
        · simpa using (by linarith [hT0 k] : -(T k) ≤ (0 : ℝ))
        · simpa using (hT0 k).le
    · -- the border avoids the zeros and the pole
      rw [Set.disjoint_right]
      rintro u hu hub
      rw [RectangleBorder, hzre, hzim, hwre, hwim] at hub
      have hcases :
          (u.re ∈ Set.uIcc σL σR ∧ u.im = -(T k)) ∨ (u.re = σL ∧ u.im ∈ Set.uIcc (-(T k)) (T k))
            ∨ (u.re ∈ Set.uIcc σL σR ∧ u.im = T k)
            ∨ (u.re = σR ∧ u.im ∈ Set.uIcc (-(T k)) (T k)) := by
        rcases hub with ((h | h) | h) | h
        · exact Or.inl ⟨h.1, by simpa using h.2⟩
        · exact Or.inr (Or.inl ⟨by simpa using h.1, h.2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h.1, by simpa using h.2⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨by simpa using h.1, h.2⟩))
      rcases hu with hu | hu
      · -- a zero of `ζ` in the rectangle
        have hζu : riemannZeta u = 0 := hu.2.2
        rcases hcases with h | h | h | h
        · exact (((hgood k).2 u h.1 h.2).1) hζu
        · exact riemannZeta_ne_zero_of_re_mem_Ioo_neg (by rw [h.1]; linarith)
            (by rw [h.1]; exact hσL0) hζu
        · exact (((hgood k).1 u h.1 h.2).1) hζu
        · exact riemannZeta_ne_zero_of_one_lt_re (by rw [h.1]; exact hσR) hζu
      · -- the pole at `1`
        have hu1 : u = 1 := hu
        rcases hcases with h | h | h | h
        · have : (0 : ℝ) = -(T k) := by rw [← h.2, hu1]; simp
          linarith [hT0 k]
        · have : (1 : ℝ) = σL := by rw [← h.1, hu1]; simp
          linarith
        · have : (0 : ℝ) = T k := by rw [← h.2, hu1]; simp
          linarith [hT0 k]
        · have : (1 : ℝ) = σR := by rw [← h.1, hu1]; simp
          linarith
    · -- analyticity of the coefficient on the rectangle
      intro s hs
      rw [Rectangle, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
        Set.uIcc_of_le hσLR] at hs
      exact hΦ_an s hs.1.1 hs.1.2
  -- the rectangle limit, normalized
  have hrect := rectangleIntegral_tendsto_verticalIntegral_of_seq (F := F)
    hT hleft hright hbot htop
  have hrect' := hrect.const_smul (1 / (2 * (Real.pi : ℂ) * I))
  have hfinal := hrect'.add_const (Φ (-1))
  exact hfinal.congr fun k => (hres k).symm

/-! ## Locating the zeros: the band `(-2, σR)` sees only critical-strip zeros (U7) -/

/-- `ζ` does not vanish on the line `Re z = 0`: the point `0` itself has
`ζ(0) = -1/2`, and for `Im z ≠ 0` the functional equation factors at `1 - z`
(which has real part `1`) are all nonzero. -/
lemma riemannZeta_ne_zero_of_re_eq_zero {z : ℂ} (h0 : z.re = 0) :
    riemannZeta z ≠ 0 := by
  by_cases hz0 : z = 0
  · rw [hz0, riemannZeta_zero]
    norm_num
  intro hzero
  set s : ℂ := 1 - z with hs_def
  have hs_re : s.re = 1 := by rw [hs_def]; simp [h0]
  have hsne : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have hre : s.re = -(n : ℝ) := by rw [h]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hs_re] at hre
    linarith
  have hsne1 : s ≠ 1 := by
    intro h
    apply hz0
    have : z = 1 - s := by rw [hs_def]; ring
    rw [this, h]
    ring
  have hFE := riemannZeta_one_sub hsne hsne1
  have h1s : (1 : ℂ) - s = z := by rw [hs_def]; ring
  rw [h1s, hzero] at hFE
  have hprod := hFE.symm
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have hpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    have hbase : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have h1 : (0 : ℝ) < 2 * Real.pi := by positivity
      intro h
      have h2 : ((2 * Real.pi : ℝ) : ℂ) = 0 := by rw [← h]; push_cast; ring
      exact h1.ne' (by exact_mod_cast h2)
    rw [Complex.cpow_def_of_ne_zero hbase]
    exact Complex.exp_ne_zero _
  have hΓ : Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have hre : s.re = -(m : ℝ) := by rw [h]; simp
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hs_re] at hre
    linarith
  have hζs : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hs_re])
  have hcos : Complex.cos (Real.pi * s / 2) ≠ 0 := by
    intro hc
    -- `s = 1 - z` with `Re z = 0`, so `π s / 2 = π/2 - π z / 2` and the cosine is
    -- `sin (π z / 2)`, which vanishes only at real multiples of `π`
    have hrw : Real.pi * s / 2 = Real.pi / 2 - Real.pi * z / 2 := by
      rw [hs_def]
      ring
    rw [hrw, Complex.cos_pi_div_two_sub] at hc
    rw [Complex.sin_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    -- compare real parts: `Re (π z / 2) = 0` while `Re (k π) = k π`
    have hre_eq : (Real.pi * z / 2).re = ((k : ℂ) * (Real.pi : ℂ)).re := by rw [hk]
    have hL : (Real.pi * z / 2).re = 0 := by
      rw [show Real.pi * z / 2 = ((Real.pi / 2 : ℝ) : ℂ) * z by push_cast; ring,
        Complex.re_ofReal_mul, h0]
      ring
    have hR : ((k : ℂ) * (Real.pi : ℂ)).re = (k : ℝ) * Real.pi := by
      rw [show ((k : ℂ) * (Real.pi : ℂ)) = (((k * Real.pi : ℝ)) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    have hk0 : (k : ℝ) * Real.pi = 0 := by rw [← hR, ← hre_eq, hL]
    have hkz : k = 0 := by
      rcases mul_eq_zero.mp hk0 with h | h
      · exact_mod_cast h
      · exact absurd h Real.pi_pos.ne'
    rw [hkz] at hk
    -- now `π z / 2 = 0`, forcing `z = 0`
    apply hz0
    have hπc : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_pos.ne'
    have h2 : Real.pi * z / 2 = 0 := by
      rw [hk]
      simp
    have h3 : (Real.pi : ℂ) * z = 0 := by
      have h4 := congrArg (fun w : ℂ => w * 2) h2
      simpa using h4
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hπc
    · exact h
  simp only [mul_eq_zero] at hprod
  rcases hprod with (((h | h) | h) | h) | h
  · exact h2ne h
  · exact hpow h
  · exact hΓ h
  · exact hcos h
  · exact hζs h

/-- `ζ` does not vanish on the real interval `(0, 1)`: by the truncated-series
representation `Zeta0EqZeta` at `N = 1`, the real part is at most `-x/(1-x) < 0`. -/
lemma riemannZeta_ne_zero_of_real_mem_Ioo {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    riemannZeta ((x : ℝ) : ℂ) ≠ 0 := by
  have hne1 : ((x : ℝ) : ℂ) ≠ 1 := by
    intro h
    have : x = 1 := by exact_mod_cast h
    linarith
  have hre : (0 : ℝ) < (((x : ℝ) : ℂ)).re := by simpa using h0
  have hzeta0 := (Zeta0EqZeta (N := 1) one_pos hre hne1).symm
  -- the head of the truncated series
  have hsum : (∑ n ∈ Finset.range 2, 1 / (n : ℂ) ^ ((x : ℝ) : ℂ)) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by
      intro h
      have : x = 0 := by exact_mod_cast h
      linarith
    norm_num [zero_cpow hx0, one_cpow]
  -- the tail integral is bounded by `1/(2x)` in norm
  set K : ℂ := ∫ u in Set.Ioi (1 : ℝ), (⌊u⌋ + 1 / 2 - u) / (u : ℂ) ^ (((x : ℝ) : ℂ) + 1)
    with hK_def
  have hmaj : MeasureTheory.IntegrableOn (fun u : ℝ => (1 / 2 : ℝ) * u ^ (-x - 1))
      (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have hptw : ∀ u ∈ Set.Ioi (1 : ℝ),
      ‖(⌊u⌋ + 1 / 2 - u : ℂ) / (u : ℂ) ^ (((x : ℝ) : ℂ) + 1)‖
        ≤ (1 / 2 : ℝ) * u ^ (-x - 1) := by
    intro u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := by linarith
    rw [norm_div]
    have hnum : ‖(⌊u⌋ + 1 / 2 - u : ℂ)‖ ≤ 1 / 2 := by
      have hcast : ((⌊u⌋ : ℂ) + 1 / 2 - u) = (((⌊u⌋ : ℝ) + 1 / 2 - u : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hfl1 := Int.sub_one_lt_floor u
      have hfl2 := Int.floor_le u
      constructor <;> linarith
    have hden : ‖(u : ℂ) ^ (((x : ℝ) : ℂ) + 1)‖ = u ^ (x + 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      norm_num
    rw [hden]
    have hpos : (0 : ℝ) < u ^ (x + 1) := Real.rpow_pos_of_pos hu0 _
    rw [div_le_iff₀ hpos]
    have hflip : (1 / 2 : ℝ) * u ^ (-x - 1) * u ^ (x + 1) = 1 / 2 := by
      rw [mul_assoc, ← Real.rpow_add hu0]
      norm_num
    rw [hflip]
    exact hnum
  have hKnorm : ‖K‖ ≤ 1 / (2 * x) := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    have hmono : (∫ u in Set.Ioi (1 : ℝ),
          ‖(⌊u⌋ + 1 / 2 - u : ℂ) / (u : ℂ) ^ (((x : ℝ) : ℂ) + 1)‖)
        ≤ ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-x - 1) := by
      apply MeasureTheory.integral_mono_of_nonneg
      · filter_upwards with u
        exact norm_nonneg _
      · exact hmaj
      · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (MeasureTheory.ae_of_all _ hptw)
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      Real.one_rpow]
    rw [show (-x - 1 + 1 : ℝ) = -x by ring]
    field_simp
    norm_num
  -- assemble: the real part of `ζ x` is at most `-x/(1-x) < 0`
  have hre_neg : (riemannZeta ((x : ℝ) : ℂ)).re < 0 := by
    have heq : riemannZeta ((x : ℝ) : ℂ) =
        (((1 / 2 - 1 / (1 - x) : ℝ)) : ℂ) + ((x : ℝ) : ℂ) * K := by
      rw [← Zeta0EqZeta (N := 1) one_pos hre hne1]
      rw [riemannZeta0]
      rw [show ((1 : ℕ) : ℂ) = 1 by norm_cast]
      rw [hsum, one_cpow, one_cpow]
      rw [show ((1 : ℕ) : ℝ) = (1 : ℝ) from Nat.cast_one]
      rw [← hK_def]
      have h1x : ((1 : ℂ) - ((x : ℝ) : ℂ)) = (((1 - x : ℝ)) : ℂ) := by push_cast; ring
      rw [h1x]
      have hcast : (-1 : ℂ) / (((1 - x : ℝ)) : ℂ) = (((-1 / (1 - x) : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hcast]
      push_cast
      ring
    rw [heq]
    rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    have hKre : K.re ≤ 1 / (2 * x) := (Complex.re_le_norm K).trans hKnorm
    have hxK : x * K.re ≤ 1 / 2 := by
      have h2 := mul_le_mul_of_nonneg_left hKre h0.le
      have h3 : x * (1 / (2 * x)) = 1 / 2 := by field_simp
      linarith
    have hfrac : (1 : ℝ) < 1 / (1 - x) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    linarith
  intro hzero
  rw [hzero] at hre_neg
  simp at hre_neg

/-- Wrapper for the strip localization covering both signs of the imaginary part:
a zero of `ζ` off the real axis has real part in `[0, 1]`. -/
lemma zeta_zero_re_mem_of_im_ne_zero {z : ℂ} (hz : riemannZeta z = 0) (him : z.im ≠ 0) :
    0 ≤ z.re ∧ z.re ≤ 1 := by
  rcases him.lt_or_gt with hlt | hgt
  · have hconj0 : riemannZeta (starRingEnd ℂ z) = 0 := by
      have h := conj_riemannZeta_conj z
      rw [hz] at h
      have h' := congrArg (starRingEnd ℂ) h
      simpa using h'
    have him' : 0 < (starRingEnd ℂ z).im := by
      rw [Complex.conj_im]
      linarith
    have hloc := Backlund.zeta_zero_re_mem_of_im_pos hconj0 him'
    rwa [Complex.conj_re] at hloc
  · exact Backlund.zeta_zero_re_mem_of_im_pos hz hgt

/-- The index-set bridge: every zero of `ζ` in the band `σL < Re < σR` (with
`-2 < σL < 0` and `σR > 1`) lies in the open critical strip, so the rectangle zero sets
of the contour and of `kadiri_thm_3_1_q1` agree for every height window. -/
lemma zeroes_rect_band_eq_critical {σL σR : ℝ} (hσL2 : -2 < σL) (hσL0 : σL < 0)
    (hσR : 1 < σR) (J : Set ℝ) :
    riemannZeta.zeroes_rect (Set.uIcc σL σR) J = riemannZeta.zeroes_rect (Set.Ioo 0 1) J := by
  have hσLR : σL ≤ σR := by linarith
  ext z
  simp only [riemannZeta.zeroes_rect, Set.mem_setOf_eq, riemannZeta.zeroes]
  constructor
  · rintro ⟨hre, him, hζ⟩
    refine ⟨?_, him, hζ⟩
    rw [Set.uIcc_of_le hσLR] at hre
    by_cases him0 : z.im = 0
    · -- a real zero in the band is impossible
      exfalso
      have hz_eq : z = ((z.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [him0]
      rcases lt_trichotomy z.re 0 with h | h | h
      · exact riemannZeta_ne_zero_of_re_mem_Ioo_neg (by linarith [hre.1]) h hζ
      · exact riemannZeta_ne_zero_of_re_eq_zero h hζ
      · rcases lt_trichotomy z.re 1 with h1 | h1 | h1
        · apply riemannZeta_ne_zero_of_real_mem_Ioo h h1
          rw [← hz_eq]
          exact hζ
        · exact riemannZeta_ne_zero_of_one_le_re (by rw [h1]) hζ
        · exact riemannZeta_ne_zero_of_one_le_re (by linarith) hζ
    · have hloc := zeta_zero_re_mem_of_im_ne_zero hζ him0
      constructor
      · rcases hloc.1.lt_or_eq with h | h
        · exact h
        · exact absurd hζ (riemannZeta_ne_zero_of_re_eq_zero h.symm)
      · rcases hloc.2.lt_or_eq with h | h
        · exact h
        · exact absurd hζ (riemannZeta_ne_zero_of_one_le_re (by rw [h]))
  · rintro ⟨hre, him, hζ⟩
    refine ⟨?_, him, hζ⟩
    rw [Set.uIcc_of_le hσLR]
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-! ## Window exhaustion of the zero sum (U7) -/

/-- A sequence of zero-free heights tending to infinity, from the good-heights
selector. -/
lemma exists_goodHeight_seq (σ₁ σ₂ : ℝ) :
    ∃ T : ℕ → ℝ, Filter.Tendsto T Filter.atTop Filter.atTop ∧ (∀ k, 0 < T k) ∧
      ∀ k, horizontalSegmentZeroFree σ₁ σ₂ (T k) := by
  choose T hT1 hT2 hT3 using fun k : ℕ =>
    exists_arbitrarily_large_horizontalSegmentZeroFree σ₁ σ₂ (k : ℝ)
  exact ⟨T, tendsto_atTop_mono hT1 tendsto_natCast_atTop_atTop, hT2, hT3⟩

/-- Window exhaustion: if the multiplicity-weighted family over all zeros in the strip
`I` is summable, the zero sums over growing height windows converge to the full zero
sum. This is the bridge from the contour limit to the `hΦ_sum` hypothesis of
`kadiri_thm_3_1_q1`. -/
lemma tendsto_zeroes_sum_window {I : Set ℝ} {g : ℂ → ℂ} {T : ℕ → ℝ}
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hsum : Summable (fun ρ : riemannZeta.zeroes_rect I (Set.univ : Set ℝ) =>
      g ρ.val * (riemannZeta.order ρ.val : ℂ))) :
    Filter.Tendsto (fun k => riemannZeta.zeroes_sum I (Set.uIcc (-(T k)) (T k)) g)
      Filter.atTop (nhds (riemannZeta.zeroes_sum I (Set.univ : Set ℝ) g)) := by
  set W : ℕ → ℂ → ℂ := fun k =>
    ({z : ℂ | z.im ∈ Set.uIcc (-(T k)) (T k)}).indicator
      (fun z => g z * (riemannZeta.order z : ℂ))
    with hW_def
  -- each window sum is the full-subtype sum of the cut-off family
  have hwin : ∀ k, riemannZeta.zeroes_sum I (Set.uIcc (-(T k)) (T k)) g
      = ∑' ρ : riemannZeta.zeroes_rect I (Set.univ : Set ℝ), W k ρ.val := by
    intro k
    calc riemannZeta.zeroes_sum I (Set.uIcc (-(T k)) (T k)) g
        = ∑' x : ℂ, (riemannZeta.zeroes_rect I (Set.uIcc (-(T k)) (T k))).indicator
            (fun z => g z * (riemannZeta.order z : ℂ)) x :=
          tsum_subtype (riemannZeta.zeroes_rect I (Set.uIcc (-(T k)) (T k)))
            (fun z => g z * (riemannZeta.order z : ℂ))
      _ = ∑' x : ℂ, (riemannZeta.zeroes_rect I (Set.univ : Set ℝ)).indicator (W k) x := by
          congr 1
          funext z
          by_cases hz : z ∈ riemannZeta.zeroes_rect I (Set.univ : Set ℝ)
          · rw [Set.indicator_of_mem hz]
            by_cases him : z.im ∈ Set.uIcc (-(T k)) (T k)
            · have hzw : z ∈ riemannZeta.zeroes_rect I (Set.uIcc (-(T k)) (T k)) :=
                ⟨hz.1, him, hz.2.2⟩
              rw [Set.indicator_of_mem hzw]
              simp only [hW_def]
              exact (Set.indicator_of_mem
                (show z ∈ {w : ℂ | w.im ∈ Set.uIcc (-(T k)) (T k)} from him)
                (fun w => g w * (riemannZeta.order w : ℂ))).symm
            · have hzw : z ∉ riemannZeta.zeroes_rect I (Set.uIcc (-(T k)) (T k)) := by
                intro hcon
                exact him hcon.2.1
              rw [Set.indicator_of_notMem hzw]
              simp only [hW_def]
              exact (Set.indicator_of_notMem
                (show z ∉ {w : ℂ | w.im ∈ Set.uIcc (-(T k)) (T k)} from him)
                (fun w => g w * (riemannZeta.order w : ℂ))).symm
          · have hzw : z ∉ riemannZeta.zeroes_rect I (Set.uIcc (-(T k)) (T k)) := by
              intro hcon
              exact hz ⟨hcon.1, Set.mem_univ _, hcon.2.2⟩
            rw [Set.indicator_of_notMem hzw, Set.indicator_of_notMem hz]
      _ = ∑' ρ : riemannZeta.zeroes_rect I (Set.univ : Set ℝ), W k ρ.val :=
          (tsum_subtype (riemannZeta.zeroes_rect I (Set.univ : Set ℝ)) (W k)).symm
  -- Tannery's theorem with the summable norm bound
  have hconv : Filter.Tendsto
      (fun k => ∑' ρ : riemannZeta.zeroes_rect I (Set.univ : Set ℝ), W k ρ.val)
      Filter.atTop
      (nhds (∑' ρ : riemannZeta.zeroes_rect I (Set.univ : Set ℝ),
        g ρ.val * (riemannZeta.order ρ.val : ℂ))) := by
    apply tendsto_tsum_of_dominated_convergence
      (bound := fun ρ : riemannZeta.zeroes_rect I (Set.univ : Set ℝ) =>
        ‖g ρ.val * (riemannZeta.order ρ.val : ℂ)‖)
      (summable_norm_iff.mpr hsum)
    · intro ρ
      have hev : ∀ᶠ k in Filter.atTop,
          W k ρ.val = g ρ.val * (riemannZeta.order ρ.val : ℂ) := by
        filter_upwards [hT.eventually_ge_atTop |(ρ.val).im|] with k hk
        have him : (ρ.val).im ∈ Set.uIcc (-(T k)) (T k) := by
          have habs := abs_le.mp hk
          have hTk0 : 0 ≤ T k := le_trans (abs_nonneg _) hk
          rw [Set.uIcc_of_le (by linarith)]
          exact ⟨habs.1, habs.2⟩
        simp only [hW_def]
        exact Set.indicator_of_mem
          (show ρ.val ∈ {w : ℂ | w.im ∈ Set.uIcc (-(T k)) (T k)} from him)
          (fun w => g w * (riemannZeta.order w : ℂ))
      exact Filter.Tendsto.congr' (hev.mono fun k hk => hk.symm) tendsto_const_nhds
    · filter_upwards with k
      intro ρ
      simp only [hW_def]
      by_cases him : (ρ.val).im ∈ Set.uIcc (-(T k)) (T k)
      · rw [Set.indicator_of_mem
          (show ρ.val ∈ {w : ℂ | w.im ∈ Set.uIcc (-(T k)) (T k)} from him)]
      · rw [Set.indicator_of_notMem
          (show ρ.val ∉ {w : ℂ | w.im ∈ Set.uIcc (-(T k)) (T k)} from him)]
        rw [norm_zero]
        exact norm_nonneg _
  exact hconv.congr fun k => (hwin k).symm

/-! ## The endpoint: the critical-strip zero sum equals the contour limit -/

/-- U7 endpoint, shaped for the `kadiri_thm_3_1_q1` close: given the edge and line
hypotheses of the contour pull along a sequence of good heights, and the summability
of the multiplicity-weighted family over all critical-strip zeros (the `hΦ_sum`
hypothesis of `kadiri_thm_3_1_q1` at `g = Φ(-·)`), the full zero sum equals the
normalized difference of the two vertical integrals plus the pole contribution. -/
theorem zeroes_sum_critical_eq_contour {Φ : ℂ → ℂ} {σL σR : ℝ} {T : ℕ → ℝ}
    (hσL2 : -2 < σL) (hσL0 : σL < 0) (hσR : 1 < σR)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (hT0 : ∀ k, 0 < T k)
    (hgood : ∀ k, horizontalSegmentZeroFree σL σR (T k))
    (hΦ_an : ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR → AnalyticAt ℂ (fun u => Φ (-u)) s)
    (hleft : MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σL : ℂ) + t * I) * (-(Φ (-((σL : ℂ) + t * I)))))
    (hright : MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σR : ℂ) + t * I) * (-(Φ (-((σR : ℂ) + t * I)))))
    (hbot : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
        -logDeriv riemannZeta ((x : ℂ) + (-(T k)) * I) *
          (-(Φ (-((x : ℂ) + (-(T k)) * I))))) Filter.atTop (nhds 0))
    (htop : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
        -logDeriv riemannZeta ((x : ℂ) + (T k) * I) *
          (-(Φ (-((x : ℂ) + (T k) * I))))) Filter.atTop (nhds 0))
    (hsum : Summable (fun ρ : riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.univ : Set ℝ) =>
      Φ (-ρ.val) * (riemannZeta.order ρ.val : ℂ))) :
    riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.univ : Set ℝ) (fun ρ => Φ (-ρ))
      = (1 / (2 * (Real.pi : ℂ) * I)) •
          (VerticalIntegral (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) σR -
            VerticalIntegral (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) σL) +
        Φ (-1) := by
  -- the contour limit of the band zero sums
  have h1 := tendsto_zeroes_sum_of_good_heights hσL2 hσL0 hσR hT hT0 hgood hΦ_an
    hleft hright hbot htop
  -- the band sums agree with the critical-strip sums for every window
  have hbr : ∀ k : ℕ,
      riemannZeta.zeroes_sum (Set.uIcc σL σR) (Set.uIcc (-(T k)) (T k)) (fun ρ => Φ (-ρ))
        = riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.uIcc (-(T k)) (T k))
            (fun ρ => Φ (-ρ)) := by
    intro k
    have hset := zeroes_rect_band_eq_critical hσL2 hσL0 hσR (Set.uIcc (-(T k)) (T k))
    exact congrArg
      (fun S : Set ℂ => ∑' ρ : S, (fun z => Φ (-z)) ρ.val * (riemannZeta.order ρ.val : ℂ))
      hset
  -- the exhaustion limit of the critical-strip window sums
  have h2 := tendsto_zeroes_sum_window (I := Set.Ioo 0 1) (g := fun z => Φ (-z)) hT hsum
  -- limit uniqueness
  exact tendsto_nhds_unique h2 ((h1.congr fun k => hbr k))

/-! ## Discharging the line and edge hypotheses -/

/-- The right vertical line input (`hright` of the contour pull), from the `Re > 1`
edge machinery of `Kadiri.lean` via the spelling bridge
`-logDeriv ζ · (-Φ(-·)) = -((-ζ'/ζ) · Φ(-·))`. -/
theorem integrable_right_line_neg_logDeriv_mul {Φ : ℂ → ℂ} {σR : ℝ} (hσR : 1 < σR)
    (hΦ_cont : Continuous fun t : ℝ => Φ (-((σR : ℂ) + t * I)))
    {C R : ℝ} (hΦ_dec : ∀ t : ℝ, R ≤ |t| → ‖Φ (-((σR : ℂ) + t * I))‖ ≤ C / t ^ 2) :
    MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σR : ℂ) + t * I) * (-(Φ (-((σR : ℂ) + t * I)))) := by
  have h := integrable_neg_deriv_zeta_div_mul_of_decay hσR
    (g := fun z => Φ (-z)) hΦ_cont hΦ_dec
  refine h.neg.congr ?_
  filter_upwards with t
  simp only [Pi.neg_apply, logDeriv_apply]
  ring

/-- Horizontal-edge vanishing (`hbot`/`htop` of the contour pull) from the good-heights
log-derivative bound (sub-unit U6a) and quadratic decay of the coefficient on the band:
the edge integrals are `O(log² T_k / T_k²)`. The sign sequence `ε` covers both edges at
once (`ε k = ± T k`). -/
theorem tendsto_horizontal_edge_zero_of_logDerivBound {Φ : ℂ → ℂ}
    {σL σR C CΦ Y₀ : ℝ} {T ε : ℕ → ℝ}
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (hT3 : ∀ k, 3 ≤ T k)
    (hε : ∀ k, |ε k| = T k)
    (hbound : ∀ k, horizontalSegmentLogDerivBound σL σR (T k) C)
    (hΦdec : ∀ x ∈ Set.uIcc σL σR, ∀ t : ℝ, Y₀ ≤ |t| →
      ‖Φ (-((x : ℂ) + t * I))‖ ≤ CΦ / t ^ 2)
    (hC : 0 ≤ C) :
    Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
      -logDeriv riemannZeta ((x : ℂ) + (ε k) * I) *
        (-(Φ (-((x : ℂ) + (ε k) * I))))) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- the scalar bound sequence tends to zero
  have hlog : Filter.Tendsto (fun u : ℝ => Real.log u ^ 2 / u ^ 2)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun u : ℝ => Real.log u ^ 2 / (1 * u + 0))
        Filter.atTop (nhds 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have h2 : Filter.Tendsto (fun u : ℝ => u⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have h3 := h1.mul h2
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp
    ring
  have hbnd : Filter.Tendsto
      (fun k : ℕ => C * CΦ * |σR - σL| * (Real.log (T k) ^ 2 / (T k) ^ 2))
      Filter.atTop (nhds 0) := by
    have := (hlog.comp hT).const_mul (C * CΦ * |σR - σL|)
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbnd
  · filter_upwards with k
    exact norm_nonneg _
  · filter_upwards [hT.eventually_ge_atTop (max Y₀ 1)] with k hk
    have hTk0 : (0 : ℝ) < T k := by linarith [hT3 k]
    have hYk : Y₀ ≤ |ε k| := by rw [hε k]; exact le_trans (le_max_left _ _) hk
    have hptw : ∀ x ∈ Set.uIoc σL σR,
        ‖-logDeriv riemannZeta ((x : ℂ) + (ε k) * I) *
          (-(Φ (-((x : ℂ) + (ε k) * I))))‖
          ≤ C * Real.log (T k) ^ 2 * (CΦ / (T k) ^ 2) := by
      intro x hx
      have hx' : x ∈ Set.uIcc σL σR := Set.uIoc_subset_uIcc hx
      have hζ := (hbound k).2 x hx' (ε k) (hε k)
      have hΦ := hΦdec x hx' (ε k) hYk
      rw [norm_mul, norm_neg, norm_neg]
      have hε2 : (ε k) ^ 2 = (T k) ^ 2 := by
        rw [← sq_abs (ε k), hε k]
      rw [hε2] at hΦ
      have hζ' : ‖logDeriv riemannZeta ((x : ℂ) + (ε k) * I)‖ ≤ C * Real.log (T k) ^ 2 := by
        rw [logDeriv_apply]
        exact hζ
      exact mul_le_mul hζ' hΦ (norm_nonneg _) (by positivity)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C * Real.log (T k) ^ 2 * (CΦ / (T k) ^ 2))
      (f := fun x : ℝ => -logDeriv riemannZeta ((x : ℂ) + (ε k) * I) *
        (-(Φ (-((x : ℂ) + (ε k) * I))))) hptw
    refine h1.trans ?_
    rw [show C * Real.log (T k) ^ 2 * (CΦ / (T k) ^ 2) * |σR - σL|
        = C * CΦ * |σR - σL| * (Real.log (T k) ^ 2 / (T k) ^ 2) by ring]

/-- A sequence of heights carrying the U6a log-derivative bound, by choice from the
banked classical target. Inherits the `sorryAx` of
`exists_arbitrarily_large_horizontalSegmentLogDerivBound` until the external
derivation lands. -/
lemma exists_logDerivBound_seq (σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ → ℝ, Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 3 ≤ T k) ∧ ∀ k, horizontalSegmentLogDerivBound σ₁ σ₂ (T k) C := by
  obtain ⟨C, hC0, hC⟩ := exists_arbitrarily_large_horizontalSegmentLogDerivBound σ₁ σ₂
  choose T hT1 hT2 hT3 using fun k : ℕ => hC (k : ℝ)
  exact ⟨C, hC0, T, tendsto_atTop_mono hT1 tendsto_natCast_atTop_atTop, hT2, hT3⟩

end Kadiri
