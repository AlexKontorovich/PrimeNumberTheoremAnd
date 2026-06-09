/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Real.Pi.Irrational

/-!
## Special values of the completed Riemann zeta function

This file records elementary special values used by applications of the completed zeta function,
including the value at `2` and the functional-equation relation `Λ₀(0) = Λ₀(1)`.  The explicit
Euler-Mascheroni formula for `Λ₀(1)` is in `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`.

## References

* [titchmarsh1986] and [edwards1974] for completed-zeta special values and the functional equation
-/

@[expose] public section

open Complex Set

open scoped BigOperators

private lemma twenty_seven_div_fifty_lt_eulerMascheroniConstant :
    (27 / 50 : ℝ) < Real.eulerMascheroniConstant := by
  have hseq : (27 / 50 : ℝ) < Real.eulerMascheroniSeq 20 := by
    have hval : Real.eulerMascheroniSeq 20 =
        (55835135 / 15519504 : ℝ) - Real.log 21 := by
      rw [Real.eulerMascheroniSeq]
      norm_num
    rw [hval, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt',
      Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 21)]
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hseq.trans (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 20)

private lemma exp_one_hundred_twenty_seven_div_fifty_gt :
    (7854 / 625 : ℝ) < Real.exp (127 / 50 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (127 / 50 : ℝ)) 12
  have hpoly :
      (7854 / 625 : ℝ) <
        ∑ i ∈ Finset.range 12, (127 / 50 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hpoly.trans_le h

private lemma log_four_mul_pi_lt_one_hundred_twenty_seven_div_fifty :
    Real.log (4 * Real.pi) < 127 / 50 := by
  rw [Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 4 * Real.pi)]
  have hpi : 4 * Real.pi < 7854 / 625 := by
    nlinarith [Real.pi_lt_d4]
  exact hpi.trans exp_one_hundred_twenty_seven_div_fifty_gt

/-- The completed Riemann zeta factor has value `π / 6` at `2`. -/
theorem completedRiemannZeta_two :
    completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ) / 6 := by
  have hs : (1 : ℝ) < Complex.re (2 : ℂ) := by norm_num
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htsum :
      completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ)⁻¹ * (∑' n : ℕ, ((n : ℂ) ^ 2)⁻¹) := by
    simpa [Complex.cpow_neg_one] using
      (completedZeta_eq_tsum_of_one_lt_re (s := (2 : ℂ)) hs)
  have hzeta : riemannZeta (2 : ℂ) = ∑' n : ℕ, ((n : ℂ) ^ 2)⁻¹ := by
    simpa using (zeta_eq_tsum_one_div_nat_cpow (s := (2 : ℂ)) hs)
  have hζ2 : riemannZeta (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6 := by
    simpa using (riemannZeta_two : riemannZeta (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6)
  have hΛ2' : completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ)⁻¹ * riemannZeta (2 : ℂ) := by
    simpa [hzeta] using htsum
  calc
    completedRiemannZeta (2 : ℂ)
        = (Real.pi : ℂ)⁻¹ * ((Real.pi : ℂ) ^ 2 / 6) := by
            simpa [hζ2] using hΛ2'
    _ = (Real.pi : ℂ) / 6 := by
            field_simp [hpi0]

/-- The entire completed zeta function `Λ₀` has value `(π - 3) / 6` at `2`. -/
theorem completedRiemannZeta₀_two :
    completedRiemannZeta₀ (2 : ℂ) = ((Real.pi : ℂ) - 3) / 6 := by
  have h := completedRiemannZeta_eq (2 : ℂ)
  have h' :
      completedRiemannZeta (2 : ℂ) + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ)) =
        completedRiemannZeta₀ (2 : ℂ) := by
    have := congrArg (fun x => x + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ))) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have h'' :
      completedRiemannZeta₀ (2 : ℂ) =
        completedRiemannZeta (2 : ℂ) + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ)) := by
    simpa [add_assoc, add_left_comm, add_comm] using h'.symm
  have hden : (1 : ℂ) / (1 - (2 : ℂ)) = (-1 : ℂ) := by norm_num
  simpa [h'', completedRiemannZeta_two, hden] using (by ring :
    (Real.pi : ℂ) / 6 + (1 : ℂ) / 2 + (-1 : ℂ) = ((Real.pi : ℂ) - 3) / 6)

/-- The entire completed zeta function `Λ₀` is not identically zero. -/
theorem completedRiemannZeta₀_nontrivial : ∃ z : ℂ, completedRiemannZeta₀ z ≠ 0 := by
  refine ⟨(2 : ℂ), ?_⟩
  have hpi_ne3 : (Real.pi : ℂ) ≠ (3 : ℂ) := by
    intro h'
    have hpi' : (Real.pi : ℝ) = (3 : ℝ) := by
      simpa using congrArg Complex.re h'
    have hirr : Irrational Real.pi := by simp
    exact (hirr.ne_nat 3) (by simp at hpi')
  have hnum : ((Real.pi : ℂ) - 3) ≠ 0 := sub_ne_zero.2 hpi_ne3
  have hden : (6 : ℂ) ≠ 0 := by norm_num
  have : ((Real.pi : ℂ) - 3) / 6 ≠ 0 := div_ne_zero hnum hden
  simpa [completedRiemannZeta₀_two] using this

/-- The functional equation identifies the values of the entire completed zeta function `Λ₀`
at `0` and `1`. -/
theorem completedRiemannZeta₀_zero_eq_one :
    completedRiemannZeta₀ (0 : ℂ) = completedRiemannZeta₀ (1 : ℂ) := by
  have h := completedRiemannZeta₀_one_sub (0 : ℂ)
  simpa using h.symm

/-- The entire completed zeta function `Λ₀` is nonzero at `1`.

This uses the Euler-Mascheroni formula for `Λ₀(1)` from `ZetaAsymp`, the lower bound
`27 / 50 < γ`, and an elementary numerical bound `log (4π) < 127 / 50`. -/
theorem completedRiemannZeta₀_one_ne_zero :
    completedRiemannZeta₀ (1 : ℂ) ≠ 0 := by
  have hpos :
      0 < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 := by
    have hγ : (27 / 50 : ℝ) < Real.eulerMascheroniConstant :=
      twenty_seven_div_fifty_lt_eulerMascheroniConstant
    have hlog : Real.log (4 * Real.pi) < 127 / 50 :=
      log_four_mul_pi_lt_one_hundred_twenty_seven_div_fifty
    linarith
  have hreal :
      ((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  rw [completedRiemannZeta₀_one]
  simpa [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi), sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm] using hreal

/-- The entire completed zeta function `Λ₀` is nonzero at `0`, by the functional equation and the
nonvanishing at `1`. -/
theorem completedRiemannZeta₀_zero_ne_zero :
    completedRiemannZeta₀ (0 : ℂ) ≠ 0 := by
  simpa [completedRiemannZeta₀_zero_eq_one] using completedRiemannZeta₀_one_ne_zero
