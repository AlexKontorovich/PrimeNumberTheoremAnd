import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Abelian normalization for the first Mertens error

The normalized logarithmic derivative tends to minus Euler's constant at the
pole. A bounded function with a limit at infinity has the same Mellin-Abelian
average. These facts identify the first Mertens constant once convergence and
the summation-by-parts identity have been supplied; they do not assume either.
-/

open Complex Set Filter MeasureTheory
open scoped Topology

namespace TernaryGoldbach.RSBounds.MertensAbelianNormalization

theorem normalized_logDeriv_tendsto :
    Tendsto (fun s : ℝ => -(logDeriv riemannZeta (s : ℂ)).re - 1 / (s - 1))
      (𝓝[>] 1) (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro he
      have he' := congrArg Complex.re he
      simp at he'
      exact ne_of_gt hs he'
  have h := ((Asymptotics.isLittleO_one_iff ℂ).mp
    log_deriv_riemannZeta_add_inv_sub_sub_isLittleO).comp hc
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  have hneg := hr.neg.sub_const Real.eulerMascheroniConstant
  convert hneg using 1
  · ext s
    simp only [Function.comp_apply, Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    have he : ((s : ℂ) - 1)⁻¹ = ((s - 1)⁻¹ : ℝ) := by push_cast; rfl
    rw [he]
    simp only [Complex.ofReal_re, logDeriv_apply, one_div]
    ring
  · simp

theorem mellin_average_zero {f : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hm : AEStronglyMeasurable f (volume.restrict (Ioi 1)))
    (hb : ∀ x, 1 ≤ x → |f x| ≤ B) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun s : ℝ => (s - 1) * ∫ x in Ioi 1, f x * x ^ (-s))
      (𝓝[>] 1) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |f x| < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hf) (ε / 2) (by positivity)
    simpa only [Real.dist_eq, sub_zero, eventually_atTop] using h
  let X := max X₀ 2
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXpos : 0 < X := by linarith
  have hXm : 0 ≤ X - 1 := by linarith
  have htail : ∀ x, X ≤ x → |f x| ≤ ε / 2 :=
    fun x hx => (hX₀ x ((le_max_left _ _).trans hx)).le
  refine ⟨min 1 (ε / (2 * (B * (X - 1) + 1))), by positivity, ?_⟩
  intro s hs hdist
  have hs1 : 1 < s := hs
  have hs0 : 0 < s - 1 := sub_pos.mpr hs1
  have hsne : s - 1 ≠ 0 := ne_of_gt hs0
  have hsr : s - 1 < ε / (2 * (B * (X - 1) + 1)) := by
    rw [Real.dist_eq, abs_of_pos hs0] at hdist
    exact hdist.trans_le (min_le_right _ _)
  have hi : IntegrableOn (fun x : ℝ => |f x| * x ^ (-s)) (Ioi 1) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt
      (by linarith : -s < -1) (by norm_num : (0 : ℝ) < 1)).const_mul B) ?_ ?_
    · exact hm.norm.mul (by fun_prop)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := le_trans zero_le_one hx.le
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)]
      exact mul_le_mul_of_nonneg_right (hb x hx.le) (Real.rpow_nonneg hx0 _)
  have hi₁ := hi.mono_set (show Ioc 1 X ⊆ Ioi (1 : ℝ) from Ioc_subset_Ioi_self)
  have hi₂ := hi.mono_set (Ioi_subset_Ioi (show (1 : ℝ) ≤ X by linarith))
  have hsplit : (∫ x in Ioi 1, |f x| * x ^ (-s)) =
      (∫ x in Ioc 1 X, |f x| * x ^ (-s)) + ∫ x in Ioi X, |f x| * x ^ (-s) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (1 : ℝ) ≤ X by linarith)]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi₁ hi₂
  have hfirst : (∫ x in Ioc 1 X, |f x| * x ^ (-s)) ≤ B * (X - 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => B) (Ioc 1 X) := integrableOn_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    calc
      _ ≤ ∫ _x in Ioc 1 X, B := by
        apply setIntegral_mono_on hi₁ hconst measurableSet_Ioc
        intro x hx
        have hp : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.1.le (by linarith)
        calc |f x| * x ^ (-s) ≤ B * 1 :=
          mul_le_mul (hb x hx.1.le) hp (Real.rpow_nonneg (by linarith [hx.1]) _) hB
          _ = B := mul_one _
      _ = B * (X - 1) := by simp [max_eq_left hXm, mul_comm]
  have hsecond : (∫ x in Ioi X, |f x| * x ^ (-s)) ≤
      ε / 2 * (X ^ (1 - s) / (s - 1)) := by
    have hpow := integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) hXpos
    have hval : (∫ x in Ioi X, x ^ (-s)) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) hXpos]
      rw [show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
      congr 2 <;> ring
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hi₂ (hpow.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    exact mul_le_mul_of_nonneg_right (htail x hx.le) (Real.rpow_nonneg (hXpos.le.trans hx.le) _)
  have hpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hsecond' : (s - 1) * (∫ x in Ioi X, |f x| * x ^ (-s)) ≤ ε / 2 := by
    calc
      _ ≤ (s - 1) * (ε / 2 * (X ^ (1 - s) / (s - 1))) :=
        mul_le_mul_of_nonneg_left hsecond hs0.le
      _ = ε / 2 * X ^ (1 - s) := by field_simp
      _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ε / 2 := mul_one _
  have hnorm : |(s - 1) * ∫ x in Ioi 1, f x * x ^ (-s)| ≤
      (s - 1) * ∫ x in Ioi 1, |f x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hs0]
    apply mul_le_mul_of_nonneg_left _ hs0.le
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change ‖f x * x ^ (-s)‖ = |f x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx.le) _)]
  have hfirst' : (s - 1) * (B * (X - 1)) < ε / 2 := by
    have hden : 0 < 2 * (B * (X - 1) + 1) := by positivity
    have hmul := (lt_div_iff₀ hden).mp hsr
    nlinarith
  rw [Real.dist_eq, sub_zero]
  calc
    _ ≤ (s - 1) * ∫ x in Ioi 1, |f x| * x ^ (-s) := hnorm
    _ = (s - 1) * (∫ x in Ioc 1 X, |f x| * x ^ (-s)) +
        (s - 1) * ∫ x in Ioi X, |f x| * x ^ (-s) := by rw [hsplit, mul_add]
    _ ≤ (s - 1) * (B * (X - 1)) + ε / 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hs0.le) hsecond'
    _ < ε := by linarith

end TernaryGoldbach.RSBounds.MertensAbelianNormalization
