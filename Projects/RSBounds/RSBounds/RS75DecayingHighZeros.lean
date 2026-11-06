import RSBounds.RS75ZeroPowerDecay
import RSBounds.PolynomialZeroPairing
import RSBounds.RosserCubicTail

/-!
# Decaying high-zero bounds for both actual quartic smoothings

All sums below are over the actual contour zeros, with their analytic
multiplicities. Conjugation contributes exactly a factor of two. The
unconditional RS75 region supplies decay for every zero above 1894439;
the already proved reciprocal-cube tail supplies the numerical allowance.
No finite-RH hypothesis is needed for this high-zero part.
-/

open Complex Finset
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.RS75DecayingHighZeros

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open PolynomialZeroPairing PolynomialZeroKernel PolynomialAveraged RS75ZeroPowerDecay

noncomputable def highConstant (x δ : ℝ) : ℝ :=
  (R4 δ / δ ^ 4) * x * decay x / 289

theorem highConstant_pos {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    0 < highConstant x δ := by
  unfold highConstant R4 decay
  positivity

/-- Exact conjugation and count conversion for any filtered ordinate weight. -/
theorem sum_filtered_weight_eq_two {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T)
    (A : ℝ) (w : ℝ → ℝ) :
    (∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
      (multRectD zetaF T ρ : ℝ) * w |ρ.im|) =
      2 * WeightedZetaZeros.weightedSum A T w := by
  classical
  have hh := sum_ordinate_weight_eq_two hT (fun t => if A < t then w t else 0)
  have hl :
      (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) *
        (if A < |ρ.im| then w |ρ.im| else 0)) =
      ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
        (multRectD zetaF T ρ : ℝ) * w |ρ.im| := by
    simp only [Finset.sum_filter, mul_ite, mul_zero]
  have hr :
      (∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) *
        (if A < ρ.im then w ρ.im else 0)) =
        WeightedZetaZeros.weightedSum A T w := by
    calc
      _ = ∑ ρ ∈ positiveZeros T, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
          (if A < ρ.im then w ρ.im else 0) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        have hmem : ρ ∈ zerosRectD zetaF T := by
          have hh : ρ ∈ (zerosRectD zetaF T).filter (fun z => 0 < z.im) := by
            rw [positive_filter_eq hT]
            exact hρ
          exact (Finset.mem_filter.mp hh).1
        rw [multRectD_zetaF_eq_analyticOrder hT hmem]
      _ = _ := by
        rw [positiveZeros_eq_closed_of_goodHeight hT hg]
        unfold WeightedZetaZeros.weightedSum
        simp only [mul_ite, mul_zero]
  rwa [hl, hr] at hh

/-- A pointwise reciprocal-cube majorant transfers to the actual complex sum. -/
theorem norm_high_sum_le_of_cube_bound {T C : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (A : ℝ) (K : ℂ → ℂ)
    (hK : ∀ ρ ∈ zerosRectD zetaF T, A < |ρ.im| → ‖K ρ‖ ≤ C / |ρ.im| ^ 3) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * K ρ‖ ≤
      2 * C * WeightedZetaZeros.weightedSum A T (fun t => 1 / t ^ 3) := by
  classical
  calc
    _ ≤ ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
        ‖(multRectD zetaF T ρ : ℂ) * K ρ‖ := norm_sum_le _ _
    _ ≤ C * ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => A < |ρ.im|),
        (multRectD zetaF T ρ : ℝ) * (1 / |ρ.im| ^ 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hr, hA⟩ := Finset.mem_filter.mp hρ
      rw [norm_mul, Complex.norm_natCast]
      have hh := mul_le_mul_of_nonneg_left (hK ρ hr hA)
        (Nat.cast_nonneg (multRectD zetaF T ρ))
      convert hh using 1 <;> ring
    _ = _ := by
      rw [sum_filtered_weight_eq_two hT hg A (fun t : ℝ => 1 / t ^ 3)]
      ring

theorem norm_upper_coefficient_le_decay {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ)
    {ρ : ℂ} (hρ : xiF ρ = 0) (hA : 1894439 ≤ |ρ.im|) :
    ‖zeroCoefficient x (δ * x) ρ‖ ≤ highConstant x δ / |ρ.im| ^ 3 := by
  have hx0 : 0 < x := by linarith
  have him : ρ.im ≠ 0 := by intro h; norm_num [h] at hA
  have hr := xiF_zero_re_strip hρ
  have hk := norm_zeroCoefficient_upper_le_high hx0 hδ hr.2.le him
  have hc : 0 ≤ R4 δ / δ ^ 4 := by unfold R4; positivity
  have hz := mul_le_mul_of_nonneg_left (zero_power_weight_le hx hρ hA) hc
  calc
    _ ≤ (R4 δ / δ ^ 4) * x ^ ρ.re / |ρ.im| ^ 5 := hk
    _ ≤ (R4 δ / δ ^ 4) * (x * decay x / (289 * |ρ.im| ^ 3)) := by
      convert hz using 1 <;> ring
    _ = _ := by unfold highConstant; ring

theorem norm_lower_coefficient_le_decay {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ)
    (hδ4 : 4 * δ < 1) {ρ : ℂ} (hρ : xiF ρ = 0) (hA : 1894439 ≤ |ρ.im|) :
    ‖zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ‖ ≤ highConstant x δ / |ρ.im| ^ 3 := by
  have hx0 : 0 < x := by linarith
  have him : ρ.im ≠ 0 := by intro h; norm_num [h] at hA
  have hr := xiF_zero_re_strip hρ
  have hk := norm_zeroCoefficient_lower_le_high hx0 hδ hδ4 hr.1.le him
  have hc : 0 ≤ R4 δ / δ ^ 4 := by unfold R4; positivity
  have hz := mul_le_mul_of_nonneg_left (zero_power_weight_le hx hρ hA) hc
  calc
    _ ≤ (R4 δ / δ ^ 4) * x ^ ρ.re / |ρ.im| ^ 5 := hk
    _ ≤ (R4 δ / δ ^ 4) * (x * decay x / (289 * |ρ.im| ^ 3)) := by
      convert hz using 1 <;> ring
    _ = _ := by unfold highConstant; ring

theorem norm_high_sum_upper_lt {T x δ : ℝ} (hT : 1894439 ≤ T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 1894439 < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ <
      2 * highConstant x δ * 3e-13 := by
  have hT0 : 0 < T := by linarith
  have hb := norm_high_sum_le_of_cube_bound hT0 hg 1894439
    (fun ρ => zeroCoefficient x (δ * x) ρ) (fun ρ hρ hA =>
      norm_upper_coefficient_le_decay hx hδ
        ((mem_zerosRectD_zetaF_iff_xi hT0).mp hρ).1 hA.le)
  exact hb.trans_lt (mul_lt_mul_of_pos_left (RosserCubicTail.cubic_sum_A_lt hT)
    (by have hc := highConstant_pos (by linarith : 0 < x) hδ; positivity))

theorem norm_high_sum_lower_lt {T x δ : ℝ} (hT : 1894439 ≤ T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) (hδ4 : 4 * δ < 1) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 1894439 < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ‖ <
      2 * highConstant x δ * 3e-13 := by
  have hT0 : 0 < T := by linarith
  have hb := norm_high_sum_le_of_cube_bound hT0 hg 1894439
    (fun ρ => zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ) (fun ρ hρ hA =>
      norm_lower_coefficient_le_decay hx hδ hδ4
        ((mem_zerosRectD_zetaF_iff_xi hT0).mp hρ).1 hA.le)
  exact hb.trans_lt (mul_lt_mul_of_pos_left (RosserCubicTail.cubic_sum_A_lt hT)
    (by have hc := highConstant_pos (by linarith : 0 < x) hδ; positivity))

end TernaryGoldbach.RSBounds.RS75DecayingHighZeros
