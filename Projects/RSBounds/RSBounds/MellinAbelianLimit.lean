import RSBounds.MertensAbelianNormalization

/-! A bounded function's Mellin-Abelian average has its limit at infinity. -/

open Real Set Filter MeasureTheory
open scoped Topology

namespace TernaryGoldbach.RSBounds.MellinAbelianLimit

open MertensAbelianNormalization

theorem integrable_mul_rpow {f : ℝ → ℝ} {B s : ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict (Ioi 1)))
    (hb : ∀ x, 1 ≤ x → |f x| ≤ B) (hs : 1 < s) :
    IntegrableOn (fun x => f x * x ^ (-s)) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt
    (by linarith : -s < -1) (by norm_num : (0 : ℝ) < 1)).const_mul B) ?_ ?_
  · exact hm.mul (by fun_prop)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx.le) _)]
    exact mul_le_mul_of_nonneg_right (hb x hx.le) (Real.rpow_nonneg (zero_le_one.trans hx.le) _)

theorem average_const {s : ℝ} (hs : 1 < s) (C : ℝ) :
    (s - 1) * (∫ x in Ioi (1 : ℝ), C * x ^ (-s)) = C := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s < -1)
    (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
  have hsne : -s + 1 ≠ 0 := by linarith
  field_simp
  <;> ring

theorem average_tendsto {f : ℝ → ℝ} {B C : ℝ}
    (hB : 0 ≤ B) (hm : AEStronglyMeasurable f (volume.restrict (Ioi 1)))
    (hb : ∀ x, 1 ≤ x → |f x| ≤ B) (hlim : Tendsto f atTop (𝓝 C)) :
    Tendsto (fun s : ℝ => (s - 1) * ∫ x in Ioi 1, f x * x ^ (-s))
      (𝓝[>] 1) (𝓝 C) := by
  have hcenter : Tendsto (fun x => f x - C) atTop (𝓝 0) := by
    simpa using hlim.sub_const C
  have hbound : ∀ x : ℝ, 1 ≤ x → |f x - C| ≤ B + |C| := by
    intro x hx
    exact (abs_sub _ _).trans (add_le_add (hb x hx) (le_refl |C|))
  have havg := mellin_average_zero (by positivity : 0 ≤ B + |C|)
    (hm.sub aestronglyMeasurable_const) hbound hcenter
  have heq {s : ℝ} (hs : 1 < s) :
      (s - 1) * (∫ x in Ioi 1, (f x - C) * x ^ (-s)) + C =
        (s - 1) * (∫ x in Ioi 1, f x * x ^ (-s)) := by
    have hi : (∫ x in Ioi 1, (f x - C) * x ^ (-s)) =
        (∫ x in Ioi 1, f x * x ^ (-s)) - ∫ x in Ioi 1, C * x ^ (-s) := by
      rw [show (fun x : ℝ => (f x - C) * x ^ (-s)) =
        (fun x : ℝ => f x * x ^ (-s) - C * x ^ (-s)) from by
          funext x; exact sub_mul _ _ _]
      exact integral_sub (integrable_mul_rpow hm hb hs)
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1)
          (by norm_num : (0 : ℝ) < 1)).const_mul C)
    rw [hi, mul_sub, average_const hs C]
    ring
  have h := havg.add_const C
  simp only [zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact heq hs

end TernaryGoldbach.RSBounds.MellinAbelianLimit
