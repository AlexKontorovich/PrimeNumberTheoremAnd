import RSBounds.InfiniteTrapezoid
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Calculus for the three real zeta log moments

This supplies the actual derivatives, convexity, vanishing endpoints and
integrals needed for the positive trapezoidal tail at the cutoff 64.
The L-series summability input is kept separate from these calculus facts.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace TernaryGoldbach.RSBounds.RS75MomentCalculus

noncomputable def momentFn (s : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  Real.log t ^ j * t ^ (-s)

noncomputable def momentDeriv (s : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ((j : ℝ) * Real.log t ^ (j - 1) - s * Real.log t ^ j) * t ^ (-s) / t

noncomputable def momentSecond (s : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (s * (s + 1) * Real.log t ^ j - (j : ℝ) * (2 * s + 1) * Real.log t ^ (j - 1) +
    (j : ℝ) * ((j - 1 : ℕ) : ℝ) * Real.log t ^ (j - 2)) * t ^ (-s) / t ^ 2

noncomputable def tailPrimitive (s : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  match j with
  | 0 => momentFn (s - 1) 0 t / (s - 1)
  | 1 => momentFn (s - 1) 1 t / (s - 1) + momentFn (s - 1) 0 t / (s - 1) ^ 2
  | 2 => momentFn (s - 1) 2 t / (s - 1) +
      2 * momentFn (s - 1) 1 t / (s - 1) ^ 2 +
      2 * momentFn (s - 1) 0 t / (s - 1) ^ 3
  | _ => 0

theorem hasDerivAt_momentFn (s : ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (momentFn s j) (momentDeriv s j t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hp := Real.hasDerivAt_rpow_const (x := t) (p := -s) (Or.inl ht.ne')
  unfold momentFn momentDeriv
  convert (hl.pow j).mul hp using 1
  all_goals try { funext u; rfl }
  all_goals dsimp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq]
  all_goals rw [Real.rpow_sub_one ht.ne']
  all_goals field_simp [ht.ne']
  all_goals ring

theorem hasDerivAt_momentDeriv (s : ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (momentDeriv s j) (momentSecond s j t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hp := Real.hasDerivAt_rpow_const (x := t) (p := -s) (Or.inl ht.ne')
  have hpol := ((hl.pow (j - 1)).const_mul (j : ℝ)).sub ((hl.pow j).const_mul s)
  unfold momentDeriv momentSecond
  convert (hpol.mul hp).div (hasDerivAt_id t) ht.ne' using 1
  all_goals try { funext u; rfl }
  all_goals dsimp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq]
  all_goals simp only [Nat.sub_sub, Nat.reduceAdd]
  all_goals rw [Real.rpow_sub_one ht.ne']
  all_goals field_simp [ht.ne']
  all_goals ring

theorem log_gt_four {t : ℝ} (ht : 64 ≤ t) : 4 < Real.log t := by
  have hlog : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 64) ht
  rw [hlog] at hm
  linarith [Real.log_two_gt_d9]

theorem momentFn_nonneg {s t : ℝ} (j : ℕ) (ht : 1 ≤ t) :
    0 ≤ momentFn s j t := by
  unfold momentFn
  exact mul_nonneg (pow_nonneg (Real.log_nonneg ht) j)
    (Real.rpow_nonneg (by linarith) _)

theorem momentSecond_nonneg {s t : ℝ} (hs : 1.6 ≤ s) (hs' : s ≤ 1.7)
    (j : ℕ) (hj : j ≤ 2) (ht : 64 ≤ t) : 0 ≤ momentSecond s j t := by
  have ht0 : 0 < t := by linarith
  have hl : 4 ≤ Real.log t := (log_gt_four ht).le
  have hs0 : 0 ≤ s := by linarith
  have hss : 4 ≤ s * (s + 1) := by nlinarith
  have hpoly : 0 ≤ s * (s + 1) * Real.log t ^ j -
      (j : ℝ) * (2 * s + 1) * Real.log t ^ (j - 1) +
      (j : ℝ) * ((j - 1 : ℕ) : ℝ) * Real.log t ^ (j - 2) := by
    interval_cases j
    · norm_num; positivity
    · norm_num
      have h := mul_nonneg (sub_nonneg.mpr hss) (show 0 ≤ Real.log t by linarith)
      nlinarith
    · norm_num
      have h₁ := mul_nonneg (sub_nonneg.mpr hss) (sq_nonneg (Real.log t))
      have h₂ := mul_nonneg (show 0 ≤ 9 - (4 * s + 2) by linarith)
        (show 0 ≤ Real.log t by linarith)
      have h₃ := mul_nonneg (show 0 ≤ Real.log t - 4 by linarith)
        (show 0 ≤ Real.log t by linarith)
      nlinarith
  unfold momentSecond
  exact div_nonneg (mul_nonneg hpoly (Real.rpow_pos_of_pos ht0 _).le) (sq_nonneg _)

theorem continuousOn_momentSecond (s : ℝ) (j : ℕ) :
    ContinuousOn (momentSecond s j) (Ici (64 : ℝ)) := by
  intro t ht
  change (64 : ℝ) ≤ t at ht
  have ht0 : 0 < t := by linarith
  have hl : ContinuousAt Real.log t := (Real.hasDerivAt_log ht0.ne').continuousAt
  have hp : ContinuousAt (fun u : ℝ => u ^ (-s)) t :=
    (Real.hasDerivAt_rpow_const (x := t) (p := -s) (Or.inl ht0.ne')).continuousAt
  have h₁ : ContinuousAt (fun u : ℝ => s * (s + 1) * Real.log u ^ j) t :=
    (hl.pow j).const_mul (s * (s + 1))
  have h₂ : ContinuousAt (fun u : ℝ => (j : ℝ) * (2 * s + 1) *
      Real.log u ^ (j - 1)) t :=
    (hl.pow (j - 1)).const_mul ((j : ℝ) * (2 * s + 1))
  have h₃ : ContinuousAt (fun u : ℝ => (j : ℝ) * ((j - 1 : ℕ) : ℝ) *
      Real.log u ^ (j - 2)) t :=
    (hl.pow (j - 2)).const_mul ((j : ℝ) * ((j - 1 : ℕ) : ℝ))
  exact ((((h₁.sub h₂).add h₃).mul hp).div
    (continuousAt_id.pow 2) (pow_ne_zero 2 ht0.ne')).continuousWithinAt

/-- Every fixed nonnegative logarithmic power is dominated by every positive
real power; this is the checked Mathlib asymptotic used for all endpoints. -/
theorem tendsto_momentFn {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Tendsto (momentFn s j) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (j : ℝ) hs).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [momentFn, Real.rpow_natCast, Real.rpow_neg ht.le, div_eq_mul_inv]

theorem tendsto_momentDeriv {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Tendsto (momentDeriv s j) atTop (𝓝 0) := by
  have h₁ := (tendsto_momentFn (show 0 < s + 1 by linarith) (j - 1)).const_mul (j : ℝ)
  have h₂ := (tendsto_momentFn (show 0 < s + 1 by linarith) j).const_mul s
  have h := h₁.sub h₂
  simp only [mul_zero, sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  unfold momentFn momentDeriv
  rw [show -(s + 1) = -s - 1 by ring, Real.rpow_sub_one ht.ne']
  ring

theorem tendsto_tailPrimitive {s : ℝ} (hs : 1 < s) (j : ℕ) :
    Tendsto (tailPrimitive s j) atTop (𝓝 0) := by
  have h₀ := tendsto_momentFn (show 0 < s - 1 by linarith) 0
  have h₁ := tendsto_momentFn (show 0 < s - 1 by linarith) 1
  have h₂ := tendsto_momentFn (show 0 < s - 1 by linarith) 2
  rcases j with _ | _ | _ | j
  · change Tendsto (fun t => momentFn (s - 1) 0 t / (s - 1)) atTop (𝓝 0)
    simpa only [zero_div] using h₀.div_const (s - 1)
  · change Tendsto (fun t => momentFn (s - 1) 1 t / (s - 1) +
      momentFn (s - 1) 0 t / (s - 1) ^ 2) atTop (𝓝 0)
    simpa only [zero_div, add_zero] using
      (h₁.div_const (s - 1)).add (h₀.div_const ((s - 1) ^ 2))
  · change Tendsto (fun t => momentFn (s - 1) 2 t / (s - 1) +
      2 * momentFn (s - 1) 1 t / (s - 1) ^ 2 +
      2 * momentFn (s - 1) 0 t / (s - 1) ^ 3) atTop (𝓝 0)
    simpa only [zero_div, mul_zero, add_zero] using
      ((h₂.div_const (s - 1)).add ((h₁.const_mul 2).div_const ((s - 1) ^ 2))).add
        ((h₀.const_mul 2).div_const ((s - 1) ^ 3))
  · change Tendsto (fun _ : ℝ => 0) atTop (𝓝 0)
    exact tendsto_const_nhds

theorem hasDerivAt_neg_tailPrimitive {s : ℝ} (hs : s ≠ 1) (j : ℕ) (hj : j ≤ 2)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -tailPrimitive s j t) (momentFn s j t) t := by
  have h₀ := hasDerivAt_momentFn (s - 1) 0 ht
  have h₁ := hasDerivAt_momentFn (s - 1) 1 ht
  have h₂ := hasDerivAt_momentFn (s - 1) 2 ht
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hp : t ^ (-(s - 1)) = t ^ (-s) * t := by
    rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  interval_cases j
  · convert (h₀.div_const (s - 1)).neg using 1
    · funext u; rfl
    · unfold momentDeriv momentFn
      simp only [Nat.cast_zero, pow_zero, zero_mul, zero_sub, one_mul]
      rw [hp]
      field_simp [hs1, ht.ne']
      <;> ring
  · convert ((h₁.div_const (s - 1)).add (h₀.div_const ((s - 1) ^ 2))).neg using 1
    · funext u; rfl
    · unfold momentDeriv momentFn
      norm_num only [Nat.cast_zero, Nat.cast_one, Nat.reduceSub, pow_zero, pow_one,
        zero_mul, zero_sub, one_mul]
      rw [hp]
      field_simp [hs1, ht.ne']
      <;> ring
  · convert (((h₂.div_const (s - 1)).add ((h₁.const_mul 2).div_const ((s - 1) ^ 2))).add
      ((h₀.const_mul 2).div_const ((s - 1) ^ 3))).neg using 1
    · funext u; rfl
    · unfold momentDeriv momentFn
      norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Nat.reduceSub,
        pow_zero, pow_one, zero_mul, zero_sub, one_mul]
      rw [hp]
      field_simp [hs1, ht.ne']
      <;> ring

theorem integrableOn_momentFn {s : ℝ} (hs : 1 < s) (j : ℕ) (hj : j ≤ 2) :
    IntegrableOn (momentFn s j) (Ioi (64 : ℝ)) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => hasDerivAt_neg_tailPrimitive hs.ne' j hj (by have ht' : (64 : ℝ) ≤ t := ht; linarith))
    (fun t ht => momentFn_nonneg j (by have ht' : (64 : ℝ) < t := ht; linarith))
    ((tendsto_tailPrimitive hs j).neg)

theorem integral_momentFn {s : ℝ} (hs : 1 < s) (j : ℕ) (hj : j ≤ 2) :
    (∫ t in Ioi (64 : ℝ), momentFn s j t) = tailPrimitive s j 64 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => hasDerivAt_neg_tailPrimitive hs.ne' j hj (by have ht' : (64 : ℝ) ≤ t := ht; linarith))
    (integrableOn_momentFn hs j hj) ((tendsto_tailPrimitive hs j).neg)
  simpa using h

/-- The actual convergent log-moment sum, before its finite scalar certificate
is substituted. Summability is supplied by the separate L-series bridge. -/
theorem moment_bounds {s : ℝ} (hs : 1.6 ≤ s) (hs' : s ≤ 1.7)
    (j : ℕ) (hj : j ≤ 2) (hsum : Summable (fun n : ℕ => momentFn s j n)) :
    (∑ n ∈ Finset.range 64, momentFn s j n) + momentFn s j 64 / 2 +
        tailPrimitive s j 64 ≤ ∑' n : ℕ, momentFn s j n ∧
      (∑' n : ℕ, momentFn s j n) ≤
        (∑ n ∈ Finset.range 64, momentFn s j n) + momentFn s j 64 / 2 +
          tailPrimitive s j 64 - momentDeriv s j 64 / 8 := by
  have hs1 : 1 < s := by linarith
  have h := InfiniteTrapezoid.infinite_bounds (f := momentFn s j)
    (g := momentDeriv s j) (h := momentSecond s j) 64
    (fun t ht => hasDerivAt_momentFn s j (by norm_num at ht; linarith))
    (fun t ht => hasDerivAt_momentDeriv s j (by norm_num at ht; linarith))
    (by simpa using continuousOn_momentSecond s j)
    (fun t ht => momentSecond_nonneg hs hs' j hj (by simpa using ht))
    hsum.hasSum.tendsto_sum_nat
    ((tendsto_momentFn (show 0 < s by linarith) j).comp tendsto_natCast_atTop_atTop)
    ((tendsto_momentDeriv (show 0 < s by linarith) j).comp tendsto_natCast_atTop_atTop)
    (by simpa using integrableOn_momentFn hs1 j hj)
  simpa only [Nat.cast_ofNat, integral_momentFn hs1 j hj] using h

end TernaryGoldbach.RSBounds.RS75MomentCalculus
