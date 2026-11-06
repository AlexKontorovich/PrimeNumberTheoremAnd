import RSBounds.PolynomialZeroCountBridge
import RSBounds.PolynomialKernelScaling
import RSBounds.PolynomialLowerKernel
import RSBounds.PolynomialLeftKernel
import RSBounds.WeightedZetaZeros

/-!
# Finite conjugation/reflection pairing for the polynomial zero sums

The high-zero factor `x+1` is proved for the actual rectangle zeros and
their analytic multiplicities. The last two theorems apply directly to the
actual upper and lower averaged zero coefficients. No RH, zero-free region,
or assumed multiplicity symmetry is used.
-/

open Complex Set
open scoped BigOperators ComplexConjugate

namespace TernaryGoldbach.RSBounds.PolynomialZeroPairing

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open PolynomialZeroKernel PolynomialAveraged PolynomialKernelScaling

private theorem mem_rect_of_positive {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ positiveZeros T) : ρ ∈ zerosRectD zetaF T := by
  have hh : ρ ∈ (zerosRectD zetaF T).filter (fun z => 0 < z.im) := by
    rw [positive_filter_eq hT]
    exact hρ
  exact (Finset.mem_filter.mp hh).1

/-- Conjugation halves every conjugation-invariant real finite sum. -/
theorem sum_eq_two_sum_positive {T : ℝ} (hT : 0 < T) (f : ℂ → ℝ)
    (hf : ∀ ρ ∈ zerosRectD zetaF T, f (conj ρ) = f ρ) :
    (∑ ρ ∈ zerosRectD zetaF T, f ρ) = 2 * ∑ ρ ∈ positiveZeros T, f ρ := by
  classical
  have hn :
      (∑ ρ ∈ (zerosRectD zetaF T).filter (fun z => ¬ 0 < z.im), f ρ) =
        ∑ ρ ∈ (zerosRectD zetaF T).filter (fun z => 0 < z.im), f ρ := by
    apply Finset.sum_bij (fun ρ _ => conj ρ)
    · intro ρ hρ
      obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hρ
      have hn := ((mem_zerosRectD_zetaF_iff hT).mp hr).2.1
      refine Finset.mem_filter.mpr ⟨conj_mem_zerosRectD hT hr, ?_⟩
      simp only [Complex.conj_im, neg_pos]
      rcases lt_or_eq_of_le (not_lt.mp hi) with h | h
      · exact h
      · exact (hn h).elim
    · intro ρ _ σ _ he
      simpa using congrArg (starRingEnd ℂ) he
    · intro ρ hρ
      obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hρ
      refine ⟨conj ρ, Finset.mem_filter.mpr ⟨conj_mem_zerosRectD hT hr, ?_⟩, by simp⟩
      simp
      linarith
    · intro ρ hρ
      exact (hf ρ (Finset.mem_filter.mp hρ).1).symm
  have hs := Finset.sum_filter_add_sum_filter_not (zerosRectD zetaF T)
    (fun z => 0 < z.im) f
  rw [hn, positive_filter_eq hT] at hs
  linarith

/-- Exact halving for arbitrary ordinate weights, with actual multiplicities. -/
theorem sum_ordinate_weight_eq_two {T : ℝ} (hT : 0 < T) (w : ℝ → ℝ) :
    (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) * w |ρ.im|) =
      2 * ∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) * w ρ.im := by
  rw [sum_eq_two_sum_positive hT _ (by
    intro ρ hρ
    rw [multRectD_conj hT hρ]
    simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [abs_of_pos ((mem_positiveZeros_iff_zeta hT).mp hρ).2.1]

private theorem reflect_mem_positive {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ positiveZeros T) : 1 - conj ρ ∈ positiveZeros T := by
  rw [← positive_filter_eq hT]
  exact Finset.mem_filter.mpr ⟨reflect_mem_zerosRectD hT (mem_rect_of_positive hT hρ),
    by simpa using ((mem_positiveZeros_iff_zeta hT).mp hρ).2.1⟩

private theorem sum_positive_reflect {T : ℝ} (hT : 0 < T) (f : ℂ → ℝ) :
    (∑ ρ ∈ positiveZeros T, f (1 - conj ρ)) = ∑ ρ ∈ positiveZeros T, f ρ := by
  classical
  apply Finset.sum_bij (fun ρ _ => 1 - conj ρ)
  · exact fun ρ hρ => reflect_mem_positive hT hρ
  · intro ρ _ σ _ he
    have hh := congrArg (fun z : ℂ => 1 - conj z) he
    simpa using hh
  · intro ρ hρ
    exact ⟨1 - conj ρ, reflect_mem_positive hT hρ, by simp⟩
  · intro ρ _
    rfl

/-- A bounded low-ordinate sum of coefficient norms is twice its positive half. -/
theorem sum_norm_low_eq_two_closed {T A : ℝ} (hA : 0 < A) (hAT : A < T)
    (K : ℂ → ℂ)
    (hK : ∀ ρ ∈ zerosRectD zetaF T, ‖K (conj ρ)‖ = ‖K ρ‖) :
    (∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ A),
      (multRectD zetaF T ρ : ℝ) * ‖K ρ‖) =
      2 * ∑ ρ ∈ closedPositiveZeros A,
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * ‖K ρ‖ := by
  classical
  have hT : 0 < T := lt_trans hA hAT
  have hh := sum_eq_two_sum_positive hT
    (fun ρ => if |ρ.im| ≤ A then (multRectD zetaF T ρ : ℝ) * ‖K ρ‖ else 0) (by
      intro ρ hρ
      rw [multRectD_conj hT hρ, hK ρ hρ]
      simp)
  have hp :
      (∑ ρ ∈ positiveZeros T,
        if |ρ.im| ≤ A then (multRectD zetaF T ρ : ℝ) * ‖K ρ‖ else 0) =
      ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ A),
        (multRectD zetaF T ρ : ℝ) * ‖K ρ‖ := by
    rw [← positive_filter_eq hT]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hi : 0 < ρ.im
    · simp [hi, abs_of_pos hi]
    · simp [hi]
  rw [hp, sum_multRectD_closed_filter hA hAT (fun ρ => ‖K ρ‖)] at hh
  simpa only [Finset.sum_filter] using hh

/-- The low part of an actual complex zero sum is controlled by its positive half. -/
theorem norm_low_sum_le_two_closed {T A : ℝ} (hA : 0 < A) (hAT : A < T)
    (K : ℂ → ℂ)
    (hK : ∀ ρ ∈ zerosRectD zetaF T, ‖K (conj ρ)‖ = ‖K ρ‖) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ A),
      (multRectD zetaF T ρ : ℂ) * K ρ‖ ≤
      2 * ∑ ρ ∈ closedPositiveZeros A,
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * ‖K ρ‖ := by
  classical
  calc
    _ ≤ ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ A),
        ‖(multRectD zetaF T ρ : ℂ) * K ρ‖ := norm_sum_le _ _
    _ = ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ A),
        (multRectD zetaF T ρ : ℝ) * ‖K ρ‖ := by
      apply Finset.sum_congr rfl
      intro ρ _
      rw [norm_mul, Complex.norm_natCast]
    _ = _ := sum_norm_low_eq_two_closed hA hAT K hK

/-- The elementary reflection estimate needs only the closed critical strip. -/
theorem rpow_pair_le {x β : ℝ} (hx : 1 ≤ x) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    x ^ β + x ^ (1 - β) ≤ x + 1 := by
  have hx0 : 0 < x := by linarith
  have h1 := Real.one_le_rpow hx hβ0
  have h2 := Real.one_le_rpow hx (by linarith : 0 ≤ 1 - β)
  have hm : x ^ β * x ^ (1 - β) = x := by
    rw [← Real.rpow_add hx0, show β + (1 - β) = 1 by ring, Real.rpow_one]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- Conjugation and critical-line reflection together give the factor `x+1`. -/
theorem sum_rpow_ordinate_weight_le {T x : ℝ} (hT : 0 < T) (hx : 1 ≤ x)
    (w : ℝ → ℝ) (hw : ∀ t, 0 < t → 0 ≤ w t) :
    (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) * x ^ ρ.re * w |ρ.im|) ≤
      (x + 1) * ∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) * w ρ.im := by
  classical
  have hhalf :
      (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) * x ^ ρ.re * w |ρ.im|) =
        2 * ∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) * x ^ ρ.re * w ρ.im := by
    rw [sum_eq_two_sum_positive hT _ (by
      intro ρ hρ
      rw [multRectD_conj hT hρ]
      simp)]
    congr 1
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [abs_of_pos ((mem_positiveZeros_iff_zeta hT).mp hρ).2.1]
  have href :
      (∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) * x ^ (1 - ρ.re) * w ρ.im) =
        ∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) * x ^ ρ.re * w ρ.im := by
    convert sum_positive_reflect hT
      (fun ρ => (multRectD zetaF T ρ : ℝ) * x ^ ρ.re * w ρ.im) using 1
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [multRectD_reflect hT (mem_rect_of_positive hT hρ)]
    simp
  have hp :
      (∑ ρ ∈ positiveZeros T, ((multRectD zetaF T ρ : ℝ) * x ^ ρ.re * w ρ.im +
        (multRectD zetaF T ρ : ℝ) * x ^ (1 - ρ.re) * w ρ.im)) ≤
      ∑ ρ ∈ positiveZeros T, (x + 1) * ((multRectD zetaF T ρ : ℝ) * w ρ.im) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    have hr := xiF_zero_re_strip ((mem_positiveZeros_iff hT).mp hρ).1
    have hi := ((mem_positiveZeros_iff_zeta hT).mp hρ).2.1
    have hh := mul_le_mul_of_nonneg_left (rpow_pair_le hx hr.1.le hr.2.le)
      (mul_nonneg (Nat.cast_nonneg (multRectD zetaF T ρ) : (0 : ℝ) ≤ _) (hw _ hi))
    convert hh using 1 <;> ring
  rw [Finset.sum_add_distrib, href, ← Finset.mul_sum] at hp
  rw [hhalf]
  linarith

private noncomputable def highWeight (A t : ℝ) : ℝ := if A < t then 1 / t ^ 5 else 0

/-- Actual finite high-ordinate pairing in the inclusive count convention. -/
theorem sum_rpow_high_le_weightedSum {T x : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (A : ℝ) :
    (∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
      (multRectD zetaF T ρ : ℝ) * x ^ ρ.re / |ρ.im| ^ 5) ≤
      (x + 1) * WeightedZetaZeros.weightedSum A T (fun t => 1 / t ^ 5) := by
  classical
  have hh := sum_rpow_ordinate_weight_le hT hx (highWeight A) (by
    intro t ht
    unfold highWeight
    split_ifs <;> positivity)
  have hl :
      (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) * x ^ ρ.re * highWeight A |ρ.im|) =
      ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
        (multRectD zetaF T ρ : ℝ) * x ^ ρ.re / |ρ.im| ^ 5 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    unfold highWeight
    split_ifs <;> simp_all <;> ring
  have hr : (∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) * highWeight A ρ.im) =
      WeightedZetaZeros.weightedSum A T (fun t => 1 / t ^ 5) := by
    calc
      _ = ∑ ρ ∈ positiveZeros T, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * highWeight A ρ.im := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [multRectD_zetaF_eq_analyticOrder hT (mem_rect_of_positive hT hρ)]
      _ = _ := by
        rw [positiveZeros_eq_closed_of_goodHeight hT hg]
        unfold WeightedZetaZeros.weightedSum
        apply Finset.sum_congr rfl
        intro ρ _
        simp only [highWeight, mul_ite, mul_zero]
  rwa [hl, hr] at hh

private theorem high_denominator_le {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (him : ρ.im ≠ 0) :
    R4 δ / (δ ^ 4 * ‖rising ρ 4‖) ≤ R4 δ / (δ ^ 4 * |ρ.im| ^ 5) := by
  apply div_le_div_of_nonneg_left (by unfold R4; positivity)
    (mul_pos (pow_pos hδ 4) (pow_pos (abs_pos.mpr him) 5))
  exact mul_le_mul_of_nonneg_left
    (PolynomialLeftKernel.abs_im_pow_le_norm_rising_four ρ) (by positivity)

theorem norm_zeroCoefficient_upper_le_high {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    {ρ : ℂ} (hr : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient x (δ * x) ρ‖ ≤ (R4 δ / δ ^ 4) * x ^ ρ.re / |ρ.im| ^ 5 := by
  rw [zeroCoefficient_upper hx hδ, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((norm_upperKernel_le_high hδ hr).trans (high_denominator_le hδ him))
    (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

theorem norm_zeroCoefficient_lower_le_high {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ4 : 4 * δ < 1) {ρ : ℂ} (hr : 0 ≤ ρ.re) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ‖ ≤
      (R4 δ / δ ^ 4) * x ^ ρ.re / |ρ.im| ^ 5 := by
  rw [zeroCoefficient_lower hx hδ hδ4, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((PolynomialLowerKernel.norm_lower_difference_le_high_common hδ hδ4 hr).trans
      (high_denominator_le hδ him)) (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

/-- Generic finite high-zero domination, after bounding an actual coefficient. -/
theorem norm_high_sum_le_of_bound {T x C : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T)
    (hx : 1 ≤ x) (hC : 0 ≤ C) (A : ℝ) (K : ℂ → ℂ)
    (hK : ∀ ρ ∈ zerosRectD zetaF T, A < |ρ.im| →
      ‖K ρ‖ ≤ C * x ^ ρ.re / |ρ.im| ^ 5) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * K ρ‖ ≤
      C * (x + 1) * WeightedZetaZeros.weightedSum A T (fun t => 1 / t ^ 5) := by
  classical
  calc
    _ ≤ ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
        ‖(multRectD zetaF T ρ : ℂ) * K ρ‖ := norm_sum_le _ _
    _ ≤ C * ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
        (multRectD zetaF T ρ : ℝ) * x ^ ρ.re / |ρ.im| ^ 5 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hr, hA⟩ := Finset.mem_filter.mp hρ
      rw [norm_mul, Complex.norm_natCast]
      have hh := mul_le_mul_of_nonneg_left (hK ρ hr hA) (Nat.cast_nonneg (multRectD zetaF T ρ))
      convert hh using 1 <;> ring
    _ ≤ C * ((x + 1) * WeightedZetaZeros.weightedSum A T (fun t => 1 / t ^ 5)) :=
      mul_le_mul_of_nonneg_left (sum_rpow_high_le_weightedSum hT hg hx A) hC
    _ = _ := by ring

/-- The high part of the actual upper averaged zero sum, with no RH premise. -/
theorem norm_high_sum_upper_le {T x δ : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T)
    (hx : 1 ≤ x) (hδ : 0 < δ) (A : ℝ) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ ≤
      (R4 δ / δ ^ 4) * (x + 1) *
        WeightedZetaZeros.weightedSum A T (fun t => 1 / t ^ 5) := by
  apply norm_high_sum_le_of_bound hT hg hx (by unfold R4; positivity) A
  intro ρ hρ _
  have hr := xiF_zero_re_strip ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
  exact norm_zeroCoefficient_upper_le_high (by linarith) hδ hr.2.le
    ((mem_zerosRectD_zetaF_iff hT).mp hρ).2.1

/-- The same high-zero bound for the actual lower averaged coefficient. -/
theorem norm_high_sum_lower_le {T x δ : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T)
    (hx : 1 ≤ x) (hδ : 0 < δ) (hδ4 : 4 * δ < 1) (A : ℝ) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ‖ ≤
      (R4 δ / δ ^ 4) * (x + 1) *
        WeightedZetaZeros.weightedSum A T (fun t => 1 / t ^ 5) := by
  apply norm_high_sum_le_of_bound hT hg hx (by unfold R4; positivity) A
  intro ρ hρ _
  have hr := xiF_zero_re_strip ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
  exact norm_zeroCoefficient_lower_le_high (by linarith) hδ hδ4 hr.1.le
    ((mem_zerosRectD_zetaF_iff hT).mp hρ).2.1

end TernaryGoldbach.RSBounds.PolynomialZeroPairing
