/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Improper-integral estimates

Elementary power-integral evaluations and convergence criteria for interval integrals on
half-lines.
-/

@[expose] public section

open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology

theorem integral_interval_rpow_neg_one_sub {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) = (m ^ (-ε) - n ^ (-ε)) / ε := by
  have h0notIcc : (0 : ℝ) ∉ Set.Icc m n := by
    intro hx
    exact (not_le.mpr (lt_of_lt_of_le zero_lt_one hm)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc m n := by simpa [uIcc_of_le hmn] using h0notIcc
  have hrne : (-1 - ε) ≠ (-1 : ℝ) := by
    intro h
    exact (ne_of_gt hε) (by linarith [h])
  have hint : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := by
    simpa using integral_rpow (a := m) (b := n) (r := -1 - ε) (Or.inr ⟨hrne, h0not⟩)
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := hint
    _ = (n ^ (-ε) - m ^ (-ε)) / (-ε) := by
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = (m ^ (-ε) - n ^ (-ε)) / ε := by ring

theorem integral_interval_rpow_neg_le {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  rw [integral_interval_rpow_neg_one_sub hε hm hmn, div_eq_mul_one_div, mul_comm]
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (le_trans zero_le_one (le_trans hm hmn)) _)

theorem intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (g : ℝ → ℝ) (c : ℝ)
    (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioi c)))
    (hbound : ∀ᵐ u ∂MeasureTheory.volume.restrict (Ioi c), ‖f u‖ ≤ g u)
    (hg : MeasureTheory.IntegrableOn g (Ioi c) MeasureTheory.volume) :
    Tendsto (fun N : ℕ => ∫ u in c..N, f u) atTop (𝓝 (∫ u in Ioi c, f u)) :=
  intervalIntegral_tendsto_integral_Ioi c (MeasureTheory.IntegrableOn.mono' hg hfm hbound)
    tendsto_natCast_atTop_atTop

/-- `∫_{1}^∞ u^{-re s - 1} = 1 / re s` for `0 < re s`. -/
theorem integral_Ioi_rpow_neg_re_sub_one {s : ℂ} (hs : 0 < s.re) :
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
  have ha : (-s.re - 1) < -1 := by linarith
  have hc : 0 < (1 : ℝ) := zero_lt_one
  have h := integral_Ioi_rpow_of_lt (a := (-s.re - 1)) ha (c := (1 : ℝ)) hc
  have h' : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = - (1 : ℝ) ^ (-s.re) / (-s.re) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)
        = - (1 : ℝ) ^ (-s.re) / (-s.re) := h'
    _ = - (1 : ℝ) / (-s.re) := by simp [Real.one_rpow]
    _ = 1 / s.re := by simp
