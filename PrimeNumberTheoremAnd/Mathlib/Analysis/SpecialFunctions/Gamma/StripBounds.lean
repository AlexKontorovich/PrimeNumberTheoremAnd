/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module


public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.GammaBounds
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.GammaStirlingAux



/-!
# Gamma bounds in half-planes

Bounds for `Complex.Gamma` and Deligne's real Gamma factor `Complex.Gammaℝ`, used
in finite-order estimates for completed zeta functions.
-/

@[expose] public section

noncomputable section

open Complex Real Set Metric


/-! ## Stirling-type bounds for the complex Gamma function

This section provides Stirling-type bounds on `Complex.Gamma` and the archimedean factor `Gammaℝ`
in regions of the complex plane that arise naturally in the analytic theory of
the completed zeta function, Hadamard factorization, and the Selberg class.
-/

namespace Real.Stirling

/-- For `x ≥ 1`, `log (1 + x) ≥ log 2`. -/
lemma log_one_add_ge_log_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ Real.log (1 + x) := by
  have h₂ : (0 : ℝ) < 2 := by norm_num
  have hle : (2 : ℝ) ≤ 1 + x := by linarith
  exact Real.log_le_log h₂ hle

/-- For `x ≥ 1`, `log (1 + x) > 0`. -/
lemma log_one_add_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < Real.log (1 + x) := Real.log_pos (by linarith)

/-- `√π < 2`. -/
lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)]
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le hπ4
    _ = 2 := h4

/-- For `x ≥ 1`, `log 2 ≤ x * log (1 + x)`. -/
lemma log_two_le_mul_log_one_add {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ x * Real.log (1 + x) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_le := log_one_add_ge_log_two hx
  have hx_mul : x * Real.log 2 ≤ x * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left hlog2_le (by linarith)
  have hx_ge : Real.log 2 ≤ x * Real.log 2 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hx hlog2_pos.le
  exact le_trans hx_ge hx_mul

/-- For `x ≥ 1`, `log 3 ≤ (log 3 / log 2) * log (1 + x)`. -/
lemma log_three_le_coef_mul_log_one_add {x : ℝ} (hx : 1 ≤ x) :
    Real.log 3 ≤ (Real.log 3 / Real.log 2) * Real.log (1 + x) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hcoef_nonneg : 0 ≤ Real.log 3 / Real.log 2 := div_nonneg hlog3_pos.le hlog2_pos.le
  have hscaled :
      (Real.log 3 / Real.log 2) * Real.log 2 ≤
        (Real.log 3 / Real.log 2) * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left (log_one_add_ge_log_two hx) hcoef_nonneg
  simpa [div_mul_cancel₀ _ hlog2_ne] using hscaled

/-- Absorbs the `s ↦ s/2 + 1` shift in half-plane Stirling bounds. -/
noncomputable def half_shift_log_constant : ℝ :=
  (3 / 2 : ℝ) * (Real.log 3 / Real.log 2 + 1)

lemma half_shift_log_constant_pos : 0 < half_shift_log_constant := by
  have hthree : 0 < (3 / 2 : ℝ) := by norm_num
  have hcoef : 0 < Real.log 3 / Real.log 2 + 1 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have hcoef_nonneg : 0 ≤ Real.log 3 / Real.log 2 :=
      div_nonneg hlog3_pos.le hlog2_pos.le
    linarith
  simpa [half_shift_log_constant] using mul_pos hthree hcoef

end Real.Stirling

namespace Complex.Gamma

open Real

/-- For `‖s‖ ≥ 1`, `‖s + 1‖ ≤ 2 * ‖s‖`. -/
lemma norm_add_one_le_two_mul_norm {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s + 1‖ ≤ 2 * ‖s‖ := by
  have h1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s (1 : ℂ)
  nlinarith [h1, hs]

/-- For `‖s‖ ≥ 1`, `‖s/2 + 1‖ ≤ (3/2) * ‖s‖`. -/
lemma norm_div_two_add_one_le_three_halves_mul {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s / 2 + 1‖ ≤ (3 / 2) * ‖s‖ := by
  have h1 : ‖s / 2 + 1‖ ≤ ‖s / 2‖ + 1 := by simpa using norm_add_le (s / 2) (1 : ℂ)
  have h1' : ‖s / 2 + 1‖ ≤ ‖s‖ / 2 + 1 := by simpa using h1
  nlinarith [h1', hs]

/-- For `‖s‖ ≥ 1`, `log(1 + ‖s + 1‖) ≤ log 2 + log(1 + ‖s‖)`. -/
lemma log_one_add_norm_add_one_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    Real.log (1 + ‖s + 1‖) ≤ Real.log 2 + Real.log (1 + ‖s‖) := by
  have hpos : 0 < (1 + ‖s + 1‖ : ℝ) := by linarith [norm_nonneg (s + 1)]
  have hle : (1 + ‖s + 1‖ : ℝ) ≤ 2 * (1 + ‖s‖) := by
    have hn : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s (1 : ℂ)
    nlinarith [hn, hs]
  have hlog' : Real.log (1 + ‖s + 1‖) ≤ Real.log (2 * (1 + ‖s‖)) :=
    Real.log_le_log hpos (by linarith)
  have hmul : Real.log (2 * (1 + ‖s‖)) = Real.log 2 + Real.log (1 + ‖s‖) := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have h1 : (1 + ‖s‖ : ℝ) ≠ 0 := by linarith [norm_nonneg s]
    simpa [mul_assoc] using Real.log_mul h2 h1
  simpa [hmul] using hlog'

/-- For `‖s‖ ≥ 1`, `log(1 + ‖s/2 + 1‖) ≤ log 3 + log(1 + ‖s‖)`. -/
lemma log_one_add_norm_div_two_add_one_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    Real.log (1 + ‖s / 2 + 1‖) ≤ Real.log 3 + Real.log (1 + ‖s‖) := by
  have hpos : 0 < (1 + ‖s / 2 + 1‖ : ℝ) := by linarith [norm_nonneg (s / 2 + 1)]
  have hle : (1 + ‖s / 2 + 1‖ : ℝ) ≤ 3 * (1 + ‖s‖) := by
    nlinarith [norm_div_two_add_one_le_three_halves_mul hs]
  have hlog' : Real.log (1 + ‖s / 2 + 1‖) ≤ Real.log (3 * (1 + ‖s‖)) :=
    Real.log_le_log hpos (by linarith)
  have hmul : Real.log (3 * (1 + ‖s‖)) = Real.log 3 + Real.log (1 + ‖s‖) := by
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have h1 : (1 + ‖s‖ : ℝ) ≠ 0 := by linarith [norm_nonneg s]
    simpa [mul_assoc] using Real.log_mul h3 h1
  simpa [hmul] using hlog'

/-- For `‖s‖ ≥ 1`, the `s ↦ s + 1` shift in the Stirling exponent is absorbed by a factor `4`. -/
lemma norm_mul_log_shift_add_one_bound {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s + 1‖ * Real.log (1 + ‖s + 1‖) ≤ 4 * (‖s‖ * Real.log (1 + ‖s‖)) := by
  have hlog2_le := Real.Stirling.log_one_add_ge_log_two hs
  have hlog_add_le : Real.log (1 + ‖s + 1‖) ≤ 2 * Real.log (1 + ‖s‖) := by
    nlinarith [log_one_add_norm_add_one_le hs, hlog2_le]
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s + 1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s + 1)])
  calc
    ‖s + 1‖ * Real.log (1 + ‖s + 1‖)
        ≤ (2 * ‖s‖) * Real.log (1 + ‖s + 1‖) :=
          mul_le_mul_of_nonneg_right (norm_add_one_le_two_mul_norm hs) hlog_nonneg
    _ ≤ (2 * ‖s‖) * (2 * Real.log (1 + ‖s‖)) :=
          mul_le_mul_of_nonneg_left hlog_add_le (by positivity)
    _ = 4 * (‖s‖ * Real.log (1 + ‖s‖)) := by ring

/-- For `‖s‖ ≥ 1`, the `s ↦ s/2 + 1` shift in the half-plane Stirling exponent. -/
lemma norm_mul_log_shift_half_bound {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤
      Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s / 2 + 1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s / 2 + 1)])
  have hlog_w' :
      Real.log (1 + ‖s / 2 + 1‖) ≤
        (Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖) := by
    nlinarith [log_one_add_norm_div_two_add_one_le hs,
      Real.Stirling.log_three_le_coef_mul_log_one_add hs]
  calc
    ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)
        ≤ ((3 / 2 : ℝ) * ‖s‖) * Real.log (1 + ‖s / 2 + 1‖) :=
          mul_le_mul_of_nonneg_right (norm_div_two_add_one_le_three_halves_mul hs) hlog_nonneg
    _ ≤ Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
      have hstep2 :
          ((3 / 2 : ℝ) * ‖s‖) * Real.log (1 + ‖s / 2 + 1‖) ≤
            ((3 / 2 : ℝ) * ‖s‖) * ((Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖)) :=
        mul_le_mul_of_nonneg_left hlog_w' (by positivity)
      have hEq :
          ((3 / 2 : ℝ) * ‖s‖) * ((Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖)) =
            Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
        simp [Real.Stirling.half_shift_log_constant, mul_assoc, mul_left_comm, mul_comm]
      exact le_trans hstep2 (by simp [hEq])

/-- From `Γ(z + 1) = z Γ(z)` and `1/2 ≤ ‖z‖`, bound `‖Γ(z)‖` by `2 * ‖Γ(z + 1)‖`. -/
lemma norm_Gamma_le_two_mul_norm_Gamma_add_one {z : ℂ} (hz : z ≠ 0) (hz_lb : (1 / 2 : ℝ) ≤ ‖z‖) :
    ‖Gamma z‖ ≤ 2 * ‖Gamma (z + 1)‖ := by
  have hfunc := Gamma_add_one z hz
  have hnorm_mul : ‖Gamma (z + 1)‖ = ‖z‖ * ‖Gamma z‖ := by
    calc
      ‖Gamma (z + 1)‖ = ‖z * Gamma z‖ := by simp [hfunc]
      _ = ‖z‖ * ‖Gamma z‖ := by simp
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz_lb
  have hz_ne : ‖z‖ ≠ 0 := ne_of_gt hz_pos
  have h_inv : 1 / ‖z‖ ≤ (2 : ℝ) := by
    have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    simpa using one_div_le_one_div_of_le hhalf_pos hz_lb
  have : ‖Gamma z‖ = ‖Gamma (z + 1)‖ / ‖z‖ := by
    calc
      ‖Gamma z‖ = (‖z‖ * ‖Gamma z‖) / ‖z‖ := by field_simp [hz_ne]
      _ = ‖Gamma (z + 1)‖ / ‖z‖ := by simp [hnorm_mul]
  rw [this, div_eq_mul_inv]
  have :
      (‖Gamma (z + 1)‖ : ℝ) * (1 / ‖z‖) ≤ ‖Gamma (z + 1)‖ * 2 :=
    mul_le_mul_of_nonneg_left h_inv (norm_nonneg _)
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

/-- `Gamma` is bounded on any compact set that does not contain non-positive integers. -/
lemma norm_bounded_on_compact_of_no_poles {K : Set ℂ}
    (hK : IsCompact K)
    (h_poles : ∀ s ∈ K, ∀ n : ℕ, s ≠ -n) :
    ∃ M : ℝ, ∀ s ∈ K, ‖Gamma s‖ ≤ M := by
  have h_cont : ContinuousOn Gamma K := by
    refine continuousOn_of_forall_continuousAt ?_
    intro s hs
    exact (differentiableAt_Gamma s (h_poles s hs)).continuousAt
  rcases hK.exists_bound_of_continuousOn h_cont with ⟨M, hM⟩
  exact ⟨M, fun s hs => hM s hs⟩

/-- When `0 < a ≤ re w ≤ 1`, we have `‖Γ(w)‖ ≤ 1 / a + √π`. -/
theorem norm_le_strip {w : ℂ} {a : ℝ}
    (ha : 0 < a) (hw_lo : a ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi :=
  Complex.Gamma.norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le ha hw_lo hw_hi

/-- For `1/2 ≤ re w ≤ 1`, `‖Γ(w)‖ ≤ 4`. -/
lemma norm_le_four_of_re_half_to_one {w : ℂ}
    (hw_lo : (1 / 2 : ℝ) ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 4 := by
  have h := norm_le_strip (w := w) (a := (1 / 2 : ℝ)) (by norm_num) hw_lo hw_hi
  calc ‖Gamma w‖ ≤ 1 / (1 / 2 : ℝ) + Real.sqrt Real.pi := h
    _ = 2 + Real.sqrt Real.pi := by norm_num
    _ ≤ 2 + 2 := by linarith [Real.Stirling.sqrt_pi_lt_two]
    _ = 4 := by norm_num

/-- For any `s : ℂ`, the real part of `s' := s - ⌊Re(s)⌋` lies in `[0, 1)`. -/
lemma floor_shift_re_in_strip {s : ℂ} :
    let s' := s - (⌊s.re⌋ : ℂ)
    0 ≤ s'.re ∧ s'.re < 1 := by
  intro s'
  have h₁ : 0 ≤ s.re - (⌊s.re⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have h₂ : s.re - (⌊s.re⌋ : ℝ) < 1 := by
    have h := Int.lt_floor_add_one (s.re)
    exact (sub_lt_iff_lt_add).mpr (by simp [add_comm])
  constructor
  · simp [s']
  · simpa [s'] using h₂

/-- For `re s ≥ 1`, `‖Γ(s)‖` is bounded by a polynomial in `‖s‖`. -/
theorem norm_bound_re_ge_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖Gamma s‖ ≤ C * (1 + ‖s‖) ^ (‖s‖ + 1) := by
  refine ⟨1, by norm_num, ?_⟩
  intro s hs_re
  classical
  by_cases hs_small : s.re < 2
  · -- On the strip `1 ≤ re s ≤ 2`, we have the sharp bound `‖Γ(s)‖ ≤ 1`.
    have hΓ : ‖Gamma s‖ ≤ 1 := Complex.Gamma.norm_le_one hs_re
      (le_of_lt hs_small)
    have hpow : (1 : ℝ) ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := by
      have hbase : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have hexp : (0 : ℝ) ≤ ‖s‖ + 1 := by linarith [norm_nonneg s]
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hexp
      simpa [Real.one_rpow] using h
    simpa [one_mul] using le_trans hΓ hpow
  · -- For `2 ≤ re s`, shift into `[1,2)` using the functional equation.
    have hs_ge_two : 2 ≤ s.re := le_of_not_gt hs_small
    let m : ℕ := ⌊s.re⌋₊ - 1
    have h_floor_ge2 : 2 ≤ ⌊s.re⌋₊ := Nat.le_floor (by exact_mod_cast hs_ge_two)
    have h_floor_le : (⌊s.re⌋₊ : ℝ) ≤ s.re := Nat.floor_le (by linarith : (0 : ℝ) ≤ s.re)
    have h_floor_gt : s.re < (⌊s.re⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one s.re)
    have hm_eq : (m : ℝ) = (⌊s.re⌋₊ : ℝ) - 1 := by
      have : (1 : ℕ) ≤ ⌊s.re⌋₊ := by omega
      simp [m, Nat.cast_sub this, Nat.cast_one]
    have hm_pos : 0 < m := by simp [m]; omega
    have h_re_lo : 1 ≤ (s - (m : ℂ)).re := by
      simp [sub_re, hm_eq]
      linarith [h_floor_le]
    have h_re_hi : (s - (m : ℂ)).re < 2 := by
      simp [sub_re, hm_eq]
      linarith [h_floor_gt]
    have h_k_bound : ∀ k < m, (k : ℝ) + 1 < s.re := by
      intro k hk
      calc (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.lt_iff_add_one_le.mp hk)
        _ = (⌊s.re⌋₊ : ℝ) - 1 := hm_eq
        _ < (⌊s.re⌋₊ : ℝ) := by linarith
        _ ≤ s.re := h_floor_le
    have prod_norm_le_pow :
        ‖∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ ≤ ‖s‖ ^ m := by
      simpa using Stirling.GammaAux.prod_norm_le_pow (s := s) (m := m) h_k_bound
    have Gamma_iterate :
        Gamma s = Gamma (s - (m : ℂ)) * ∏ k ∈ Finset.range m, (s - 1 - (k : ℂ)) := by
      have hs_nonzero : ∀ k < m, s - 1 - (k : ℂ) ≠ 0 := by
        intro k hk hk0
        have : (s - 1 - (k : ℂ)).re = 0 := by simp [hk0]
        have hk' : (k : ℝ) + 1 < s.re := h_k_bound k hk
        simp [Complex.sub_re] at this
        linarith
      simpa using Stirling.GammaAux.Gamma_iterate (s := s) (n := m) hs_nonzero
    have h_gamma_base : ‖Gamma (s - (m : ℂ))‖ ≤ 1 :=
      Complex.Gamma.norm_le_one h_re_lo (le_of_lt h_re_hi)
    have hΓ_le_pow : ‖Gamma s‖ ≤ ‖s‖ ^ m := by
      calc
        ‖Gamma s‖ =
            ‖Gamma (s - (m : ℂ)) * ∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ := by
              simp [Gamma_iterate]
        _ =
            ‖Gamma (s - (m : ℂ))‖ *
              ‖∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ := by
              simp
        _ ≤ 1 * ‖s‖ ^ m :=
            mul_le_mul h_gamma_base prod_norm_le_pow (norm_nonneg _) (by norm_num)
        _ = ‖s‖ ^ m := by ring
    have hm_le_norm : (m : ℝ) ≤ ‖s‖ := by
      have hm_le_floor : m ≤ ⌊s.re⌋₊ := Nat.sub_le _ _
      have hm_le_re : (m : ℝ) ≤ s.re := by
        have h_floor_le' : (⌊s.re⌋₊ : ℝ) ≤ s.re :=
          Nat.floor_le (by linarith : (0 : ℝ) ≤ s.re)
        exact le_trans (by exact_mod_cast hm_le_floor) h_floor_le'
      exact le_trans hm_le_re (Complex.re_le_norm s)
    have hpow_le : ‖s‖ ^ m ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := by
      have hx0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.cast_nonneg m)
      have hbase_le : ‖s‖ ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have h1 : (‖s‖ : ℝ) ^ m = (‖s‖ : ℝ) ^ (m : ℝ) := by
        simp [Real.rpow_natCast]
      have h2 : (‖s‖ : ℝ) ^ (m : ℝ) ≤ (1 + ‖s‖) ^ (m : ℝ) :=
        Real.rpow_le_rpow hx0 hbase_le hm0
      have hbase1 : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have hm_le : (m : ℝ) ≤ ‖s‖ + 1 := by linarith [hm_le_norm]
      have h3 : (1 + ‖s‖) ^ (m : ℝ) ≤ (1 + ‖s‖) ^ (‖s‖ + 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase1 hm_le
      calc
        ‖s‖ ^ m = (‖s‖ : ℝ) ^ (m : ℝ) := h1
        _ ≤ (1 + ‖s‖) ^ (m : ℝ) := h2
        _ ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := h3
    have : ‖Gamma s‖ ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := le_trans hΓ_le_pow hpow_le
    simpa [one_mul] using this

/-- **Main Stirling bound** for `Re(s) ≥ 0`.

There exists a constant `C` such that for any `s` with `re s ≥ 0` and
`‖s‖ ≥ 1` we have `‖Γ(s)‖ ≤ exp (C · ‖s‖ · log (1 + ‖s‖))`. -/
theorem stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  classical
  rcases norm_bound_re_ge_one with ⟨C₁, hC₁_pos, hC₁⟩
  have hlog2_pos : 0 < Real.log 2 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact Real.log_pos this
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  let K : ℝ := |Real.log C₁| + 1
  have hK_pos : 0 < K := by
    have : 0 ≤ |Real.log C₁| := abs_nonneg _
    linarith [K]
  have hC₁_exp : C₁ ≤ Real.exp K := by
    have hlog : Real.log C₁ ≤ |Real.log C₁| + 1 := by
      have : Real.log C₁ ≤ |Real.log C₁| := le_abs_self _
      linarith
    have h := Real.exp_le_exp.mpr hlog
    simpa [K, Real.exp_log hC₁_pos] using h
  let Cbase : ℝ := K / Real.log 2 + 2
  have hCbase_pos : 0 < Cbase := by
    have hK_div_nonneg : 0 ≤ K / Real.log 2 := div_nonneg hK_pos.le hlog2_pos.le
    linarith [Cbase, hK_div_nonneg]
  let C : ℝ := 4 * Cbase
  refine ⟨C, by nlinarith [hCbase_pos], ?_⟩
  have h_re_ge_one :
      ∀ z : ℂ, 1 ≤ z.re →
        ‖Gamma z‖ ≤ Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) := by
    intro z hz_re
    have hz_norm : (1 : ℝ) ≤ ‖z‖ := le_trans hz_re (Complex.re_le_norm z)
    have hx_pos : 0 < (1 + ‖z‖ : ℝ) := by linarith [norm_nonneg z]
    have hL_nonneg : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    have hlog2_le_log : Real.log 2 ≤ Real.log (1 + ‖z‖) :=
      Real.Stirling.log_one_add_ge_log_two hz_norm
    have hlog2_le : Real.log 2 ≤ ‖z‖ * Real.log (1 + ‖z‖) := by
      have hx_mul : ‖z‖ * Real.log 2 ≤ ‖z‖ * Real.log (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_left hlog2_le_log (by linarith)
      have hx_ge : Real.log 2 ≤ ‖z‖ * Real.log 2 := by
        have := mul_le_mul_of_nonneg_right hz_norm hlog2_pos.le
        simpa [one_mul] using this
      exact le_trans hx_ge hx_mul
    have hcoef_nonneg : 0 ≤ K / Real.log 2 := div_nonneg hK_pos.le hlog2_pos.le
    have hscaled :
        (K / Real.log 2) * Real.log 2 ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left hlog2_le hcoef_nonneg
    have hK_le : K ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by
      have : (K / Real.log 2) * Real.log 2 = K := by field_simp [hlog2_ne]
      simpa [this] using hscaled
    have hlin :
        Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
          2 * (‖z‖ * Real.log (1 + ‖z‖)) := by
      have hz_le : ‖z‖ + 1 ≤ 2 * ‖z‖ := by linarith [hz_norm]
      have hmul :
          Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
            Real.log (1 + ‖z‖) * (2 * ‖z‖) :=
        mul_le_mul_of_nonneg_left hz_le hL_nonneg
      -- rewrite
      simpa [mul_assoc, mul_left_comm, mul_comm, two_mul] using hmul
    -- Convert the polynomial bound into an exponential bound.
    have hpoly : ‖Gamma z‖ ≤ C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) := hC₁ z hz_re
    have hnonneg_rpow : 0 ≤ (1 + ‖z‖) ^ (‖z‖ + 1) :=
      Real.rpow_nonneg (by linarith [norm_nonneg z]) _
    have hmul :
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) ≤
          Real.exp K * (1 + ‖z‖) ^ (‖z‖ + 1) :=
      mul_le_mul_of_nonneg_right hC₁_exp hnonneg_rpow
    have hrpow :
        (1 + ‖z‖) ^ (‖z‖ + 1) =
          Real.exp (Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
      simp [Real.rpow_def_of_pos hx_pos, mul_comm]
    have hexp1 :
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) ≤
          Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
      calc
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1)
            ≤ Real.exp K * (1 + ‖z‖) ^ (‖z‖ + 1) := hmul
        _ = Real.exp K * Real.exp (Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by simp [hrpow]
        _ = Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
              simp [Real.exp_add]
    have hexp2 :
        Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1))
          ≤ Real.exp (Cbase * (‖z‖ * Real.log (1 + ‖z‖))) := by
      apply Real.exp_le_exp.mpr
      have hsum :
          K + Real.log (1 + ‖z‖) * (‖z‖ + 1)
            ≤ (K / Real.log 2 + 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by
        -- split into the constant term and the rpow term
        have hK_term : K ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by
          -- `‖z‖ * log(1+‖z‖)` is ≥ log 2, so we can scale
          -- (we already proved it with `hK_le`, but written with `‖z‖*log` instead of `log*‖z‖`)
          simpa [mul_assoc] using hK_le
        have h2_term :
            Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤ 2 * (‖z‖ * Real.log (1 + ‖z‖)) := hlin
        -- combine
        have :
            K + Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
              (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) +
                2 * (‖z‖ * Real.log (1 + ‖z‖)) := by
          nlinarith [hK_term, h2_term]
        -- factor
        simpa [Cbase, add_mul, mul_add, two_mul, mul_assoc, mul_left_comm, mul_comm] using this
      simpa [Cbase, mul_assoc] using hsum
    have hexp3 :
        Real.exp (Cbase * (‖z‖ * Real.log (1 + ‖z‖)))
          = Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) := by ring_nf
    have : ‖Gamma z‖ ≤ Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) :=
      le_trans hpoly (le_trans hexp1 (le_trans hexp2 (by simp [hexp3] )))
    simpa [mul_assoc] using this
  intro s hs_re hs_norm
  have hs0 : s ≠ 0 := (norm_pos_iff).1 (lt_of_lt_of_le (by norm_num) hs_norm)
  by_cases hs_ge_one : 1 ≤ s.re
  · have h1 := h_re_ge_one s hs_ge_one
    -- upgrade from `Cbase` to `C = 4*Cbase`
    have hmul_nonneg : 0 ≤ ‖s‖ * Real.log (1 + ‖s‖) := by
      have : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
      exact mul_nonneg (norm_nonneg _) this
    have hC_le : Cbase * (‖s‖ * Real.log (1 + ‖s‖)) ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
      have : Cbase ≤ C := by simp [C, le_mul_of_one_le_left, hCbase_pos.le]
      exact mul_le_mul_of_nonneg_right this hmul_nonneg
    have h2 : Real.exp (Cbase * ‖s‖ * Real.log (1 + ‖s‖))
        ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
      apply Real.exp_le_exp.mpr
      -- rewrite to use `hC_le`
      have hleft : Cbase * ‖s‖ * Real.log (1 + ‖s‖) = Cbase * (‖s‖ * Real.log (1 + ‖s‖)) := by ring
      have hright : C * ‖s‖ * Real.log (1 + ‖s‖) = C * (‖s‖ * Real.log (1 + ‖s‖)) := by ring
      -- `simp` both sides
      simpa [hleft, hright] using hC_le
    exact le_trans h1 h2
  · have hs_lt_one : s.re < 1 := lt_of_not_ge hs_ge_one
    -- relate `Γ(s)` to `Γ(s+1)` and bound using the `re≥1` case.
    have hnorm_eq : ‖Gamma s‖ = ‖Gamma (s + 1)‖ / ‖s‖ := by
      have h := Complex.Gamma_add_one s hs0
      have hn : ‖Gamma (s + 1)‖ = ‖s‖ * ‖Gamma s‖ := by
        calc
          ‖Gamma (s + 1)‖ = ‖s * Gamma s‖ := by simp [h]
          _ = ‖s‖ * ‖Gamma s‖ := by simp
      have hs_norm_ne : ‖s‖ ≠ 0 := (norm_ne_zero_iff).2 hs0
      calc
        ‖Gamma s‖ = (‖s‖ * ‖Gamma s‖) / ‖s‖ := by field_simp [hs_norm_ne]
        _ = ‖Gamma (s + 1)‖ / ‖s‖ := by simp [hn]
    have hdiv : ‖Gamma s‖ ≤ ‖Gamma (s + 1)‖ := by
      rw [hnorm_eq]
      exact div_le_self (norm_nonneg _) hs_norm
    have hs1 : (1 : ℝ) ≤ (s + 1).re := by
      -- `re(s+1) = re(s)+1`
      simp [Complex.add_re]
      linarith [hs_re]
    have hG1 : ‖Gamma (s + 1)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
      have h0 := h_re_ge_one (s + 1) hs1
      have hshift := norm_mul_log_shift_add_one_bound hs_norm
      have hC_nonneg : 0 ≤ Cbase := le_of_lt hCbase_pos
      have hCshift :
          Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖)) ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        calc
          Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖))
              ≤ Cbase * (4 * (‖s‖ * Real.log (1 + ‖s‖))) := by
                    exact mul_le_mul_of_nonneg_left hshift hC_nonneg
          _ = C * (‖s‖ * Real.log (1 + ‖s‖)) := by simp [C, mul_assoc, mul_left_comm, mul_comm]
      have h0' :
          Cbase * ‖s + 1‖ * Real.log (1 + ‖s + 1‖) =
            Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖)) := by
        ring
      have h1' :
          C * ‖s‖ * Real.log (1 + ‖s‖) =
            C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        ring
      exact le_trans h0 (by
        apply Real.exp_le_exp.mpr
        simpa [h0', h1'] using hCshift)
    exact le_trans hdiv hG1

/-- Stirling bound specialized to `Γ(s/2)` for `re s ≥ 0`. -/
theorem half_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  classical
  rcases stirling_bound_re_ge_zero with ⟨C₀, hC₀_pos, hC₀⟩
  let A : ℝ := Real.Stirling.half_shift_log_constant
  have hA_pos := Real.Stirling.half_shift_log_constant_pos
  let C : ℝ := 1 + C₀ * A
  refine ⟨C, by nlinarith [hC₀_pos, hA_pos], ?_⟩
  intro s hs_re hs_norm
  have hs0 : s ≠ 0 := (norm_pos_iff).1 (lt_of_lt_of_le (by norm_num) hs_norm)
  have hs2_neq : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num : (2 : ℂ) ≠ 0)
  have hs2_lb : (1 / 2 : ℝ) ≤ ‖s / 2‖ := by
    simpa using (show (1 / 2 : ℝ) ≤ ‖s‖ / 2 by nlinarith)
  have hdiv := norm_Gamma_le_two_mul_norm_Gamma_add_one hs2_neq hs2_lb
  have hz_re : 0 ≤ (s / 2 + 1).re := by simp [Complex.add_re]; linarith
  have hz_norm : (1 : ℝ) ≤ ‖s / 2 + 1‖ := by
    have : (1 : ℝ) ≤ (s / 2 + 1).re := by simp [Complex.add_re]; linarith
    exact le_trans this (Complex.re_le_norm (s / 2 + 1))
  have hΓz :
      ‖Gamma (s / 2 + 1)‖ ≤
        Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) :=
    hC₀ (s / 2 + 1) hz_re hz_norm
  have hprod_w :
      ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤ A * (‖s‖ * Real.log (1 + ‖s‖)) := by
    simpa [A] using norm_mul_log_shift_half_bound hs_norm
  have hlog2_le_xlog := Real.Stirling.log_two_le_mul_log_one_add hs_norm
  -- Put everything together.
  have hmain :
      ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
    -- from `‖Γ(s/2)‖ ≤ 2‖Γ(s/2+1)‖`
    have htmp :
        ‖Gamma (s / 2)‖ ≤
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) :=
      le_trans hdiv (mul_le_mul_of_nonneg_left hΓz (by norm_num))
    -- rewrite `2 = exp(log 2)`
    -- convert to a single exponential and compare exponents
    have htmp' :
        2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
          = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
      have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
        have : (0 : ℝ) < 2 := by norm_num
        simp [Real.exp_log this]
      -- `exp(log 2) * exp(A) = exp(log 2 + A)`
      calc
        2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            = Real.exp (Real.log 2) *
                Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
                simp [htwo, mul_assoc]
        _ = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
              simp [Real.exp_add]
    refine le_trans htmp (by
      -- compare exponents
      have hexp_le :
          Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)
            ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        have hC0_nonneg : 0 ≤ C₀ := le_of_lt hC₀_pos
        have hA_term :
            C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤
              (C₀ * A) * (‖s‖ * Real.log (1 + ‖s‖)) := by
          -- use `hprod_w`
          have := mul_le_mul_of_nonneg_left hprod_w hC0_nonneg
          -- rearrange
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
        have hlog2_term : Real.log 2 ≤ 1 * (‖s‖ * Real.log (1 + ‖s‖)) := by
          simpa using hlog2_le_xlog
        -- combine and expand `C = 1 + C₀*A`
        nlinarith [hA_term, hlog2_term, C]
      -- apply exp monotonicity
      have h_exp :
          Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) :=
        Real.exp_le_exp.mpr hexp_le
      -- rewrite the left-hand side using `htmp'`
      have :
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) := by
        calc
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
              = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := htmp'
          _ ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) := h_exp
      simpa [mul_assoc] using this)
  -- final rewriting of the exponent
  simpa [mul_assoc] using hmain

end Complex.Gamma

namespace Complex.Gammaℝ.Stirling

open Real

/-- The norm of `π^{-s/2}` is at most `1` when `Re(s) ≥ 0`. -/
lemma norm_cpow_pi_neg_half_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi_pos]
  have h_re : (-s / 2).re = -s.re / 2 := by simp [Complex.neg_re]
  rw [h_re]
  have h_exp : -s.re / 2 ≤ 0 := by linarith
  have hpi_gt_1 : (1 : ℝ) < Real.pi := by
    calc (1 : ℝ) < 3 := by norm_num
      _ < Real.pi := Real.pi_gt_three
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_gt_1) h_exp

/-- The norm of `(2π)^{-w}` is at most `1` when `Re(w) ≥ 0`. -/
lemma norm_cpow_two_mul_pi_neg_le_one {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1 := by
  have hbase_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hbase : (1 : ℝ) ≤ 2 * Real.pi := by
    have : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three, Real.pi_pos]
    exact le_of_lt this
  have hnorm : ‖(2 * π : ℂ) ^ (-w)‖ = (2 * Real.pi) ^ ((-w : ℂ).re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := 2 * Real.pi) hbase_pos (-w)
  rw [hnorm]
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase (neg_nonpos.mpr hw)

/-- **Stirling bound for the archimedean factor** `Γ_ℝ = π^{-s/2} · Γ(s/2)`. -/
theorem bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := Complex.Gamma.half_bound_re_ge_zero
  refine ⟨C₁ + 2, by linarith, ?_⟩
  intro s hs_re hs_norm
  have hdef : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    simp [Complex.Gammaℝ_def]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) :=
    hC₁ s hs_re hs_norm
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := norm_cpow_pi_neg_half_le_one hs_re
  have h1 : ‖Complex.Gammaℝ s‖ ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
    rw [hdef]; exact norm_mul_le _ _
  have h2 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := by
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * ‖Complex.Gamma (s / 2)‖ := mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
      _ = ‖Complex.Gamma (s / 2)‖ := by ring
      _ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := hΓ
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hnorm_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
  have hC_le : C₁ * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C₁ + 2) * ‖s‖ * Real.log (1 + ‖s‖) := by
    apply mul_le_mul_of_nonneg_right _ hlog_nonneg
    apply mul_le_mul_of_nonneg_right _ hnorm_nonneg
    linarith
  exact le_trans (le_trans h1 h2) (Real.exp_le_exp.mpr hC_le)

/-- Finite order bound for Γ_ℝ. -/
theorem finite_order :
    ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (A * ‖s‖ ^ B) := by
  obtain ⟨C, hC_pos, hC⟩ := bound_re_ge_zero
  use C + 1, 2
  refine ⟨by linarith, by norm_num, ?_⟩
  intro s hs_re hs_norm
  have h := hC s hs_re hs_norm
  apply le_trans h
  apply Real.exp_le_exp.mpr
  -- log(1 + |s|) ≤ |s| for |s| ≥ 1, so C|s|log(1+|s|) ≤ C|s|² ≤ (C+1)|s|²
  have h_log : Real.log (1 + ‖s‖) ≤ ‖s‖ := by
    have h1 : 0 < 1 + ‖s‖ := by linarith [norm_nonneg s]
    have h2 : ‖s‖ + 1 ≤ Real.exp ‖s‖ := Real.add_one_le_exp ‖s‖
    have h2' : 1 + ‖s‖ ≤ Real.exp ‖s‖ := by linarith
    rw [Real.log_le_iff_le_exp (by linarith [norm_nonneg s])]
    exact h2'
  have step1 : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ C * ‖s‖ * ‖s‖ := by
    apply mul_le_mul_of_nonneg_left h_log
    apply mul_nonneg (by linarith) (norm_nonneg s)
  have step2 : C * ‖s‖ * ‖s‖ = C * ‖s‖ ^ 2 := by ring
  have step3 : C * ‖s‖ ^ 2 ≤ (C + 1) * ‖s‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h_combined : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C + 1) * ‖s‖ ^ 2 := by
    calc C * ‖s‖ * Real.log (1 + ‖s‖)
        ≤ C * ‖s‖ * ‖s‖ := step1
      _ = C * ‖s‖ ^ 2 := step2
      _ ≤ (C + 1) * ‖s‖ ^ 2 := step3
  -- Convert from ℕ exponent (^ 2) to ℝ exponent (^ (2 : ℝ))
  -- The goal is (C + 1) * ‖s‖ ^ (2 : ℝ), which equals (C + 1) * ‖s‖ ^ (2 : ℕ)
  -- This type coercion is handled by norm_cast
  have hconv : (C + 1) * ‖s‖ ^ 2 = (C + 1) * ‖s‖ ^ (2 : ℝ) := by norm_cast
  rw [← hconv]
  exact h_combined

end Complex.Gammaℝ.Stirling
end
