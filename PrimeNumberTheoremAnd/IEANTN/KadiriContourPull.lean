/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import PrimeNumberTheoremAnd.IEANTN.KadiriContourShift
import PrimeNumberTheoremAnd.IEANTN.KadiriFunctionalEquation
import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeights
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

/-! ## The good-heights bound (sub-unit U6a) -/

/-- A height `T` is good for the strip `[σ₁, σ₂]` when both horizontal segments at
`Im z = ±T` avoid the zeros of `ζ` and the pole at `1`, and `ζ'/ζ` satisfies the
classical `O(log² T)` bound along them. -/
def horizontalSegmentLogDerivBound (σ₁ σ₂ T C : ℝ) : Prop :=
  horizontalSegmentZeroFree σ₁ σ₂ T ∧
  ∀ x ∈ Set.uIcc σ₁ σ₂, ∀ t : ℝ, |t| = T →
    ‖deriv riemannZeta ((x : ℂ) + t * I) / riemannZeta ((x : ℂ) + t * I)‖
      ≤ C * Real.log T ^ 2

/-- Sub-unit U6a (banked gap; classical target): there exist arbitrarily large heights
`T` at which `‖ζ'/ζ(σ + iT)‖ ≤ C·log²T` uniformly on the strip `σ ∈ [σ₁, σ₂]`.
Classically this follows from the partial-fraction expansion of `ζ'/ζ` over the zeros
in unit boxes around height `T` (the in-tree crude counting majorant
`Backlund.zetaCounting_crude_majorant` bounds the number of such zeros) after choosing
`T` to stay `≫ 1/log T` away from every zero ordinate; the in-tree bounds
`LogDerivZetaBnd`/`LogDerivZetaBndUnif` cover the part of the segment with
`σ ≥ 1 - A/log⁹T`, and the functional-equation transport of
`KadiriFunctionalEquation` covers `σ ≤ 0`; the critical-strip middle is the open
part. A panel derivation of this bound is in flight as the cross-check. -/
lemma exists_arbitrarily_large_horizontalSegmentLogDerivBound (σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentLogDerivBound σ₁ σ₂ T C := by
  sorry

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

end Kadiri
