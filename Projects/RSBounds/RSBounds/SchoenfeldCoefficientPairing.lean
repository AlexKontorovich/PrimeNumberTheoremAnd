import RSBounds.SchoenfeldZeroSymmetry

/-!
# Coefficient bounds with the exact high-zero half count

A low coefficient bound is used for the member of a reflected pair to the
left of the critical line. A possibly different coefficient bound is used
for its partner. Finite RH is used only at ordinates at most 1894439.
-/

open Complex Finset Real
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.SchoenfeldCoefficientPairing

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open SchoenfeldZeroSymmetry RS75ZeroFree1975

/-- Choose the low coefficient on the member whose real part is at most one half. -/
theorem pair_le_sqrt_add {x β α C D f g : ℝ} (hx : 1 ≤ x)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hβ : β ≤ α) (hβ' : 1 - β ≤ α)
    (hfC : f ≤ C * x ^ β) (hgC : g ≤ C * x ^ (1 - β))
    (hfD : f ≤ D * x ^ β) (hgD : g ≤ D * x ^ (1 - β)) :
    f + g ≤ C * Real.sqrt x + D * x ^ α := by
  by_cases hh : β ≤ 1 / 2
  · have h1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx hh) hC
    have h2 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx hβ') hD
    rw [← Real.sqrt_eq_rpow] at h1
    exact add_le_add (hfC.trans h1) (hgD.trans h2)
  · have h1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx hβ) hD
    have h2 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (show 1 - β ≤ 1 / 2 by linarith)) hC
    rw [← Real.sqrt_eq_rpow] at h2
    linarith [hfD.trans h1, hgC.trans h2]

/-- The finite-RH premise gives the actual low rectangle zeros' real parts. -/
theorem low_re_eq_half (hRH : Goals.FiniteRH 1894439) {T : ℝ} (hT : 0 < T)
    {ρ : ℂ} (hρ : ρ ∈ zerosRectD zetaF T) (hA : |ρ.im| ≤ 1894439) :
    ρ.re = 1 / 2 := by
  have hz := (mem_zerosRectD_zetaF_iff_xi hT).mp hρ
  have hs := xiF_zero_re_strip hz.1
  exact hRH ρ ((mem_zerosRectD_zetaF_iff hT).mp hρ).1 hs.1 hs.2 hA

/-- The positive-height allowance is exactly the inclusive weighted count. -/
theorem sum_positive_high_eq_weightedSum {T : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (A : ℝ) (w : ℝ → ℝ) :
    (∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) *
      (if A < ρ.im then w ρ.im else 0)) = WeightedZetaZeros.weightedSum A T w := by
  classical
  calc
    _ = ∑ ρ ∈ positiveZeros T, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
        (if A < ρ.im then w ρ.im else 0) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hr : ρ ∈ zerosRectD zetaF T := by
        have hh : ρ ∈ (zerosRectD zetaF T).filter (fun z => 0 < z.im) := by
          rw [positive_filter_eq hT]
          exact hρ
        exact (Finset.mem_filter.mp hh).1
      rw [multRectD_zetaF_eq_analyticOrder hT hr]
    _ = _ := by
      rw [positiveZeros_eq_closed_of_goodHeight hT hg]
      unfold WeightedZetaZeros.weightedSum
      simp only [mul_ite, mul_zero]

/-- Splitting at an inclusive height preserves the exact analytic multiplicities. -/
theorem weightedSum_split_ite {a b T : ℝ} (hb : 0 < b) (hab : a ≤ b) (hbT : b ≤ T)
    (f g : ℝ → ℝ) :
    WeightedZetaZeros.weightedSum a T (fun t => if t ≤ b then f t else g t) =
      WeightedZetaZeros.weightedSum a b f + WeightedZetaZeros.weightedSum b T g := by
  classical
  unfold WeightedZetaZeros.weightedSum
  rw [← WeightedZetaZeros.filter_closedPositiveZeros hb hbT, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hρb : ρ.im ≤ b
  · have hbn : ¬ b < ρ.im := not_lt.mpr hρb
    by_cases haρ : a < ρ.im <;> simp [hρb, hbn, haρ]
  · have hbρ : b < ρ.im := lt_of_not_ge hρb
    have haρ : a < ρ.im := hab.trans_lt hbρ
    simp [hρb, hbρ, haρ]

/-- Constant factors can be taken outside the actual weighted sum. -/
theorem weightedSum_const_mul (a b c : ℝ) (f : ℝ → ℝ) :
    WeightedZetaZeros.weightedSum a b (fun t => c * f t) =
      c * WeightedZetaZeros.weightedSum a b f := by
  classical
  unfold WeightedZetaZeros.weightedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hρ : a < ρ.im <;> simp [hρ] <;> ring

/--
An actual finite multiplicity sum has one full critical-line allowance and
one positive-height high allowance. The high allowance has no factor two.
-/
theorem norm_sum_le_critical_and_high
    (hRH : Goals.FiniteRH 1894439) {T x : ℝ} (hT : 0 < T) (hx : 1 ≤ x)
    (K : ℂ → ℂ) (C D : ℝ → ℝ)
    (hC : ∀ t, 0 ≤ t → 0 ≤ C t) (hD : ∀ t, 0 ≤ t → 0 ≤ D t)
    (hKC : ∀ ρ ∈ zerosRectD zetaF T, ‖K ρ‖ ≤ C |ρ.im| * x ^ ρ.re)
    (hKD : ∀ ρ ∈ zerosRectD zetaF T, 1894439 < |ρ.im| →
      ‖K ρ‖ ≤ D |ρ.im| * x ^ ρ.re) :
    ‖∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℂ) * K ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (C |ρ.im| * Real.sqrt x)) +
      ∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) *
        (if 1894439 < ρ.im then D ρ.im *
          (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (ρ.im / 17))) else 0) := by
  classical
  let f : ℂ → ℝ := fun ρ => (multRectD zetaF T ρ : ℝ) * ‖K ρ‖
  have hn : ‖∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℂ) * K ρ‖ ≤
      ∑ ρ ∈ zerosRectD zetaF T, f ρ := by
    refine (norm_sum_le _ _).trans_eq ?_
    apply Finset.sum_congr rfl
    intro ρ _
    simp only [f, norm_mul, Complex.norm_natCast]
  refine hn.trans (sum_le_low_and_high hT f
    (fun t => C t * Real.sqrt x)
    (fun t => if 1894439 < t then D t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17))) else 0) ?_)
  intro ρ hρ
  have hr := reflect_mem_zerosRectD hT hρ
  have hm : 0 ≤ (multRectD zetaF T ρ : ℝ) := Nat.cast_nonneg _
  have hc := hKC ρ hρ
  have hc' := hKC (1 - conj ρ) hr
  simp only [sub_re, one_re, Complex.conj_re, sub_im, one_im, Complex.conj_im,
    zero_sub, neg_neg] at hc'
  simp only [f, multRectD_reflect hT hρ]
  by_cases hA : 1894439 < |ρ.im|
  · simp only [if_pos hA]
    have hz := (mem_zerosRectD_zetaF_iff_xi hT).mp hρ
    have hz' := (mem_zerosRectD_zetaF_iff_xi hT).mp hr
    have hb := (xi_zero_re_lt hz.1 hA.le).le
    have hb' : 1 - ρ.re ≤
        1 - 1 / (9.645908801 * Real.log (|ρ.im| / 17)) := by
      simpa using (xi_zero_re_lt hz'.1 (by simpa using hA.le)).le
    have hd := hKD ρ hρ hA
    have hd' := hKD (1 - conj ρ) hr (by simpa using hA)
    simp only [sub_re, one_re, Complex.conj_re, sub_im, one_im, Complex.conj_im,
      zero_sub, neg_neg] at hd'
    have hp := pair_le_sqrt_add hx (hC _ (abs_nonneg _)) (hD _ (abs_nonneg _)) hb hb' hc hc' hd hd'
    rw [rpow_boundary_eq (by linarith : 0 < x) hA.le] at hp
    have hpm := mul_le_mul_of_nonneg_left hp hm
    have hlow : 0 ≤ (multRectD zetaF T ρ : ℝ) * (C |ρ.im| * Real.sqrt x) :=
      mul_nonneg hm (mul_nonneg (hC _ (abs_nonneg _)) (Real.sqrt_nonneg _))
    nlinarith only [hpm, hlow]
  · simp only [if_neg hA, mul_zero, add_zero]
    have hb := low_re_eq_half hRH hT hρ (not_lt.mp hA)
    rw [hb, ← Real.sqrt_eq_rpow] at hc
    have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hb, hhalf, ← Real.sqrt_eq_rpow] at hc'
    have h1 := mul_le_mul_of_nonneg_left hc hm
    have h2 := mul_le_mul_of_nonneg_left hc' hm
    nlinarith only [h1, h2]

/-- The same coefficient estimate expressed through the actual weighted zero count. -/
theorem norm_sum_le_critical_and_weighted_high
    (hRH : Goals.FiniteRH 1894439) {T x : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x)
    (K : ℂ → ℂ) (C D : ℝ → ℝ)
    (hC : ∀ t, 0 ≤ t → 0 ≤ C t) (hD : ∀ t, 0 ≤ t → 0 ≤ D t)
    (hKC : ∀ ρ ∈ zerosRectD zetaF T, ‖K ρ‖ ≤ C |ρ.im| * x ^ ρ.re)
    (hKD : ∀ ρ ∈ zerosRectD zetaF T, 1894439 < |ρ.im| →
      ‖K ρ‖ ≤ D |ρ.im| * x ^ ρ.re) :
    ‖∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℂ) * K ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (C |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894439 T (fun t => D t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hh := norm_sum_le_critical_and_high hRH hT hx K C D hC hD hKC hKD
  rwa [sum_positive_high_eq_weightedSum hT hg 1894439 (fun t => D t *
    (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17))))] at hh

end TernaryGoldbach.RSBounds.SchoenfeldCoefficientPairing
