import RSBounds.BacklundCircleMajorantDef
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-! Real-part majorants have identical upper and lower semicircle integrals. -/

open Complex Real MeasureTheory Set
open scoped Interval

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

theorem real_circleMap (c r θ : ℝ) :
    (circleMap (c : ℂ) r θ).re = c + r * Real.cos θ := by
  simp [circleMap]

theorem circleIntegrable_re_of_upper {f : ℝ → ℝ} {c r : ℝ}
    (hi : IntervalIntegrable (fun θ => f (c + r * Real.cos θ)) volume 0 Real.pi) :
    CircleIntegrable (fun z : ℂ => f z.re) (c : ℂ) r := by
  let u : ℝ → ℝ := fun θ => f (c + r * Real.cos θ)
  change IntervalIntegrable u volume 0 Real.pi at hi
  have he : ∀ θ, u (-θ) = u θ := by intro θ; simp [u]
  have hp : Function.Periodic u (2 * Real.pi) := by intro θ; simp [u]
  have hn : IntervalIntegrable u volume (-Real.pi) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hi
    simpa only [neg_zero, he] using h.symm
  have hfull : IntervalIntegrable u volume (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    convert hn.trans hi using 1
    ring
  have hi' := hp.intervalIntegrable (by positivity : 2 * Real.pi ≠ 0) hfull 0 (2 * Real.pi)
  simpa only [CircleIntegrable, real_circleMap, u] using hi'

theorem circleAverage_re_eq_upper {f : ℝ → ℝ} {c r : ℝ}
    (hi : IntervalIntegrable (fun θ => f (c + r * Real.cos θ)) volume 0 Real.pi) :
    circleAverage (fun z : ℂ => f z.re) (c : ℂ) r =
      (∫ θ in (0 : ℝ)..Real.pi, f (c + r * Real.cos θ)) / Real.pi := by
  let u : ℝ → ℝ := fun θ => f (c + r * Real.cos θ)
  change IntervalIntegrable u volume 0 Real.pi at hi
  have he : ∀ θ, u (-θ) = u θ := by intro θ; simp [u]
  have hn : IntervalIntegrable u volume (-Real.pi) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hi
    simpa only [neg_zero, he] using h.symm
  have hneg : (∫ θ in -Real.pi..(0 : ℝ), u θ) = ∫ θ in (0 : ℝ)..Real.pi, u θ := by
    have h := intervalIntegral.integral_comp_neg (f := u) (a := 0) (b := Real.pi)
    simpa only [neg_zero, he] using h.symm
  rw [circleAverage_eq_integral_add (η := -Real.pi)]
  simp only [real_circleMap]
  change (2 * Real.pi)⁻¹ • (∫ θ in (0 : ℝ)..2 * Real.pi, u (θ + -Real.pi)) = _
  rw [intervalIntegral.integral_comp_add_right]
  norm_num only [zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring]
  rw [← intervalIntegral.integral_add_adjacent_intervals hn hi, hneg]
  simp only [smul_eq_mul]
  dsimp [u]
  field_simp [Real.pi_ne_zero]
  ring

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
