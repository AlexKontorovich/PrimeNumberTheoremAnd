import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# An integrable majorant for the quartic left remainder

The fixed split point 65536 is above the reciprocal of the historical
step 0.0000211. Coarse bounds are intentional: their full real-line integral
is below 50000, sufficient for an absolute remainder below 0.1 at x >= exp 23.
No zeta or zero-location hypothesis enters this scalar integration module.
-/

open MeasureTheory Set Real
open scoped Interval Topology

namespace TernaryGoldbach.RSBounds.PolynomialRemainderMajorant

noncomputable def cutoff : ℝ := 65536

noncomputable def tail (t : ℝ) : ℝ :=
  19 * cutoff ^ 4 * (1300 + 80 * t / cutoff) / t ^ 5

noncomputable def positiveMajorant (t : ℝ) : ℝ :=
  if t ≤ 1 then 748 else if t ≤ cutoff then 1430 / t else tail t

noncomputable def majorant (t : ℝ) : ℝ := positiveMajorant |t|

theorem cutoff_pos : 0 < cutoff := by norm_num [cutoff]
theorem one_le_cutoff : 1 ≤ cutoff := by norm_num [cutoff]

theorem log_cutoff_le : Real.log cutoff ≤ 12 := by
  rw [show cutoff = (2 : ℝ) ^ 16 by norm_num [cutoff], Real.log_pow]
  have := Real.log_two_lt_d9
  norm_num only [Nat.cast_ofNat]
  linarith

theorem reciprocal_step_le_cutoff : (1 : ℝ) / 0.0000211 ≤ cutoff := by
  norm_num [cutoff]

private theorem tail_eq_powers (t : ℝ) (ht : 0 < t) :
    tail t = (19 * cutoff ^ 4 * 1300) * (t ^ 5)⁻¹ +
      (19 * cutoff ^ 4 * 80 / cutoff) * (t ^ 4)⁻¹ := by
  unfold tail
  field_simp [ht.ne', cutoff_pos.ne']

private theorem integrableOn_inv_pow (n : ℕ) (hn : 2 ≤ n) :
    IntegrableOn (fun t : ℝ => (t ^ n)⁻¹) (Ioi cutoff) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -(n : ℝ))
    (by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith) cutoff_pos
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  change t ^ (-(n : ℝ)) = (t ^ n)⁻¹
  rw [Real.rpow_neg (cutoff_pos.trans ht).le, Real.rpow_natCast]

private theorem integral_inv_pow (n : ℕ) (hn : 2 ≤ n) :
    (∫ t : ℝ in Ioi cutoff, (t ^ n)⁻¹) =
      1 / ((n - 1 : ℕ) * cutoff ^ (n - 1)) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have he : -(n : ℝ) + 1 = -((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have h := integral_Ioi_rpow_of_lt (a := -(n : ℝ)) (by linarith) cutoff_pos
  rw [he, Real.rpow_neg cutoff_pos.le, Real.rpow_natCast] at h
  have heq : (fun t : ℝ => t ^ (-(n : ℝ))) =ᵐ[volume.restrict (Ioi cutoff)]
      fun t : ℝ => (t ^ n)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.rpow_neg (cutoff_pos.trans ht).le, Real.rpow_natCast]
  rw [integral_congr_ae heq] at h
  rw [h]
  simp only [div_neg, neg_div, neg_neg]
  rw [one_div, mul_inv_rev, div_eq_mul_inv]

private theorem integrableOn_tail : IntegrableOn tail (Ioi cutoff) := by
  have hi : IntegrableOn (fun t : ℝ =>
      (19 * cutoff ^ 4 * 1300) * (t ^ 5)⁻¹ +
      (19 * cutoff ^ 4 * 80 / cutoff) * (t ^ 4)⁻¹) (Ioi cutoff) :=
    ((integrableOn_inv_pow 5 (by omega)).const_mul (19 * cutoff ^ 4 * 1300)).add
    ((integrableOn_inv_pow 4 (by omega)).const_mul (19 * cutoff ^ 4 * 80 / cutoff))
  exact hi.congr_fun (fun t ht => (tail_eq_powers t (cutoff_pos.trans ht)).symm)
    measurableSet_Ioi

private theorem integral_tail : (∫ t : ℝ in Ioi cutoff, tail t) = 20045 / 3 := by
  calc
    (∫ t : ℝ in Ioi cutoff, tail t) =
        ∫ t : ℝ in Ioi cutoff,
          (19 * cutoff ^ 4 * 1300) * (t ^ 5)⁻¹ +
            (19 * cutoff ^ 4 * 80 / cutoff) * (t ^ 4)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact tail_eq_powers t (cutoff_pos.trans ht)
    _ = _ := by
      rw [integral_add
        ((integrableOn_inv_pow 5 (by omega)).const_mul _)
        ((integrableOn_inv_pow 4 (by omega)).const_mul _),
        integral_const_mul, integral_const_mul,
        integral_inv_pow 5 (by omega), integral_inv_pow 4 (by omega)]
      norm_num [cutoff]

private theorem integrableOn_positive_low :
    IntegrableOn positiveMajorant (Ioc (0 : ℝ) 1) := by
  refine (integrableOn_const (C := (748 : ℝ)) (hs := by simp)).congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp [positiveMajorant, ht.2]

private theorem integrableOn_positive_middle :
    IntegrableOn positiveMajorant (Ioc (1 : ℝ) cutoff) := by
  have hi : IntegrableOn (fun t : ℝ => 1430 / t) (Icc 1 cutoff) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.div continuousOn_id (fun t ht => by linarith [ht.1])
  refine (hi.mono_set Ioc_subset_Icc_self).congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp [positiveMajorant, not_le.mpr ht.1, ht.2]

private theorem integrableOn_positive_tail :
    IntegrableOn positiveMajorant (Ioi cutoff) := by
  refine integrableOn_tail.congr_fun (fun t ht => ?_) measurableSet_Ioi
  change cutoff < t at ht
  have ht1 : ¬ t ≤ 1 := by linarith [one_le_cutoff]
  simp [positiveMajorant, ht1, not_le.mpr ht]

private theorem integrableOn_positive_above_one :
    IntegrableOn positiveMajorant (Ioi (1 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi one_le_cutoff]
  exact integrableOn_positive_middle.union integrableOn_positive_tail

theorem integrableOn_positiveMajorant :
    IntegrableOn positiveMajorant (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact integrableOn_positive_low.union integrableOn_positive_above_one

private theorem integral_positive_low :
    (∫ t : ℝ in Ioc (0 : ℝ) 1, positiveMajorant t) = 748 := by
  calc
    _ = ∫ t : ℝ in Ioc (0 : ℝ) 1, (748 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp [positiveMajorant, ht.2]
    _ = _ := by simp

private theorem integral_positive_middle :
    (∫ t : ℝ in Ioc (1 : ℝ) cutoff, positiveMajorant t) = 1430 * Real.log cutoff := by
  calc
    _ = ∫ t : ℝ in Ioc (1 : ℝ) cutoff, 1430 * t⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp [positiveMajorant, not_le.mpr ht.1, ht.2, div_eq_mul_inv]
    _ = _ := by
      rw [← intervalIntegral.integral_of_le one_le_cutoff,
        intervalIntegral.integral_const_mul,
        integral_inv_of_pos (by norm_num) cutoff_pos]
      simp

private theorem integral_positive_tail :
    (∫ t : ℝ in Ioi cutoff, positiveMajorant t) = 20045 / 3 := by
  rw [← integral_tail]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change cutoff < t at ht
  have ht1 : ¬ t ≤ 1 := by linarith [one_le_cutoff]
  simp [positiveMajorant, ht1, not_le.mpr ht]

theorem integral_positiveMajorant_le :
    (∫ t : ℝ in Ioi (0 : ℝ), positiveMajorant t) ≤ 25000 := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (by exact Set.disjoint_left.mpr (fun t h1 h2 => not_lt_of_ge h1.2 h2))
      measurableSet_Ioi integrableOn_positive_low integrableOn_positive_above_one]
  rw [← Ioc_union_Ioi_eq_Ioi one_le_cutoff,
    setIntegral_union (by exact Set.disjoint_left.mpr (fun t h1 h2 => not_lt_of_ge h1.2 h2))
      measurableSet_Ioi integrableOn_positive_middle integrableOn_positive_tail,
    integral_positive_low, integral_positive_middle, integral_positive_tail]
  linarith [log_cutoff_le]

theorem majorant_nonneg (t : ℝ) : 0 ≤ majorant t := by
  unfold majorant positiveMajorant
  split_ifs
  · norm_num
  · positivity
  · unfold tail cutoff
    positivity

theorem integrable_majorant : Integrable majorant := by
  change Integrable (fun t : ℝ => positiveMajorant |t|)
  have hpos : IntegrableOn (fun t : ℝ => positiveMajorant |t|) (Ioi 0) := by
    refine integrableOn_positiveMajorant.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos ht]
  have hneg : IntegrableOn (fun t : ℝ => positiveMajorant |t|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun t : ℝ => -t := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hi := hneg.union hpos
  simpa only [Iic_union_Ioi, IntegrableOn, Measure.restrict_univ, majorant] using hi

theorem integral_majorant_le : (∫ t : ℝ, majorant t) ≤ 50000 := by
  unfold majorant
  rw [integral_comp_abs]
  linarith [integral_positiveMajorant_le]

/-- A coarse numerical margin, sufficient for the b = 23 application. -/
theorem scaled_majorant_lt {x : ℝ} (hx : Real.exp 23 ≤ x) :
    25000 / (Real.pi * x ^ (1 / 2 : ℝ)) < 0.1 := by
  have hx0 : 0 < x := (Real.exp_pos 23).trans_le hx
  have hex : (2.7 : ℝ) ^ 23 ≤ Real.exp 23 := by
    calc
      (2.7 : ℝ) ^ 23 ≤ (Real.exp 1) ^ 23 := by
        gcongr
        linarith [Real.exp_one_gt_d9]
      _ = Real.exp 23 := by rw [← Real.exp_nat_mul]; norm_num
  have hxlarge : (85000 : ℝ) ^ 2 ≤ x := by
    have hnum : (85000 : ℝ) ^ 2 ≤ (2.7 : ℝ) ^ 23 := by norm_num
    exact hnum.trans (hex.trans hx)
  have hsqrt : 85000 ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num) hx0.le).mpr
    exact hxlarge
  rw [← Real.sqrt_eq_rpow]
  apply (div_lt_iff₀ (mul_pos Real.pi_pos (Real.sqrt_pos.mpr hx0))).mpr
  nlinarith [Real.pi_gt_three]


/-- The fully integrated scalar majorant, including the contour normalization. -/
theorem scaled_integral_majorant_lt {x : ℝ} (hx : Real.exp 23 ≤ x) :
    x ^ (-1 / 2 : ℝ) / (2 * Real.pi) * (∫ t : ℝ, majorant t) < 0.1 := by
  have hx0 : 0 < x := (Real.exp_pos 23).trans_le hx
  have hs : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hp : x ^ (-1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx0.le]
  calc
    x ^ (-1 / 2 : ℝ) / (2 * Real.pi) * (∫ t : ℝ, majorant t)
        ≤ x ^ (-1 / 2 : ℝ) / (2 * Real.pi) * 50000 := by
      exact mul_le_mul_of_nonneg_left integral_majorant_le (by positivity)
    _ = 25000 / (Real.pi * x ^ (1 / 2 : ℝ)) := by
      rw [hp]
      field_simp
      <;> ring
    _ < 0.1 := scaled_majorant_lt hx

end TernaryGoldbach.RSBounds.PolynomialRemainderMajorant
