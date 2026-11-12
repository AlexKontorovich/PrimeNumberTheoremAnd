/-
The rectangle-and-damping argument adapts Mathlib's Phragmen–Lindelof proof.
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0; see licenses/PrimeNumberTheoremAnd-LICENSE.
Adaptation to an upper half-strip with quadratic growth: 2026 OpenAI.
-/
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # A half-strip maximum principle for Backlund's normalization

The lower horizontal edge is retained explicitly. Gaussian damping proves the
maximum principle from a quadratic growth bound, so no boundary condition at
infinity or unproved half-strip interpolation principle is assumed.
-/

open Complex Real Set Filter Metric
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundHalfStrip

private theorem gaussian_top_tendsto {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (ε * (1 - t ^ 2)) * (C * t ^ 2))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => ε * t ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop hε
  have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hp).const_mul
    (C * Real.exp ε / ε)
  convert hh using 1
  · funext t
    simp only [Function.comp_apply, pow_one]
    rw [show ε * (1 - t ^ 2) = ε + -(ε * t ^ 2) by ring, Real.exp_add]
    field_simp
  · ring

/-- The maximum principle on `0≤Re z≤1`, `a≤Im z`, assuming only quadratic
growth and a bound of one on the three finite boundary pieces. -/
theorem norm_le_one {f : ℂ → ℂ} {a : ℝ} (ha : 1 ≤ a)
    (hd : DiffContOnCl ℂ f (Ioo (0 : ℝ) 1 ×ℂ Ioi a))
    (hleft : ∀ z : ℂ, z.re = 0 → a ≤ z.im → ‖f z‖ ≤ 1)
    (hright : ∀ z : ℂ, z.re = 1 → a ≤ z.im → ‖f z‖ ≤ 1)
    (hbottom : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → z.im = a → ‖f z‖ ≤ 1)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      0 ≤ z.re → z.re ≤ 1 → a ≤ z.im → ‖f z‖ ≤ C * z.im ^ 2)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (hza : a ≤ z.im) :
    ‖f z‖ ≤ 1 := by
  obtain ⟨C, hC, hgrowth⟩ := hgrowth
  suffices h : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖ ≤ 1 by
    apply le_of_tendsto _ h
    convert (((Complex.continuous_ofReal.mul continuous_const).cexp.mul
      continuous_const).norm.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds using 1 <;> simp
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  let g : ℂ → ℂ := fun w => Complex.exp ((ε : ℂ) * w ^ 2) * f w
  have he (w : ℂ) : ‖g w‖ =
      Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) * ‖f w‖ := by
    simp only [g, norm_mul, Complex.norm_exp]
    congr 2
    simp [pow_two]
  obtain ⟨R, hRz, hRa, hR⟩ : ∃ R : ℝ, z.im < R ∧ a < R ∧
      Real.exp (ε * (1 - R ^ 2)) * (C * R ^ 2) ≤ 1 := by
    have hevent := (gaussian_top_tendsto hε0 C).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact ((eventually_gt_atTop z.im).and
      ((eventually_gt_atTop a).and hevent)).exists
  have hgd : DiffContOnCl ℂ g (Ioo (0 : ℝ) 1 ×ℂ Ioo a R) := by
    have hgexp : Differentiable ℂ (fun w : ℂ => Complex.exp ((ε : ℂ) * w ^ 2)) :=
      ((differentiable_id.pow 2).const_mul _).cexp
    simpa only [smul_eq_mul] using (hgexp.diffContOnCl.smul hd).mono
      (fun w hw => ⟨hw.1, hw.2.1⟩)
  have hweight (w : ℂ) (hw0 : 0 ≤ w.re) (hw1 : w.re ≤ 1) (hwa : a ≤ w.im) :
      Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply mul_nonpos_of_nonneg_of_nonpos hε0.le
    have hr2 : w.re ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
    nlinarith
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (0 : ℝ) 1).reProdIm (isBounded_Ioo a R)) hgd
  · intro w hw
    rw [frontier_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
      closure_Ioo hRa.ne, frontier_Ioo (by norm_num : (0 : ℝ) < 1),
      frontier_Ioo hRa] at hw
    simp only [mem_union, mem_reProdIm, mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with ⟨⟨hw0, hw1⟩, hwa | hwR⟩ | ⟨hw0 | hw1, ⟨hwa, _⟩⟩
    · rw [he]
      exact mul_le_one₀ (hweight w hw0 hw1 hwa.ge) (norm_nonneg _)
        (hbottom w hw0 hw1 hwa)
    · rw [he, hwR]
      have hr2 : w.re ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
      calc
        _ ≤ Real.exp (ε * (1 - R ^ 2)) * (C * R ^ 2) := by
          apply mul_le_mul
          · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hε0.le)
          · simpa [hwR] using hgrowth w hw0 hw1 (by linarith)
          · exact norm_nonneg _
          · positivity
        _ ≤ 1 := hR
    · rw [he]
      exact mul_le_one₀ (hweight w hw0.ge (by linarith) hwa) (norm_nonneg _)
        (hleft w hw0 hwa)
    · rw [he]
      exact mul_le_one₀ (hweight w (by linarith) hw1.le hwa) (norm_nonneg _)
        (hright w hw1 hwa)
  · rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioo hRa.ne]
    exact ⟨⟨hz0, hz1⟩, ⟨hza, hRz.le⟩⟩

end TernaryGoldbach.RSBounds.BacklundHalfStrip
