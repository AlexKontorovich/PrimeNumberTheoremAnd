module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/
public import Zeta23.FromPNTPlus.ZetaBounds
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Complex Set MeasureTheory Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Analyticity away from the pole -/

/-- ζ is analytic on a neighbourhood of every set not containing 1. -/
theorem analyticOnNhd_riemannZeta {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ riemannZeta S := by
  have h : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  exact h.mono (Set.subset_compl_singleton_iff.mpr hS)

/-! ## The half-plane bound  [Tit86, (2.1.4) with N = 1] -/

/-- **Explicit half-plane bound.** For 0 < Re s and s ≠ 1,
‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s.
Proof: `Zeta0EqZeta` (PNT+ port) with N = 1 gives ζ(s) = 1/2 − 1/(1−s) + s∫_1^∞ (⌊x⌋+1/2−x)x^{−s−1}dx,
and `ZetaBnd_aux1b` bounds the integral by 1/Re s. -/
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hint := ZetaBnd_aux1b 1 le_rfl (σ := s.re) (t := s.im) hσ
  rw [re_add_im] at hint
  simp only [Nat.cast_one, Real.one_rpow] at hint
  rw [← Zeta0EqZeta (N := 1) one_pos hσ hs]
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  calc ‖(1 : ℂ) + -1 / (1 - s) + -1 / 2 + s * J‖
      = ‖(1 / 2 : ℂ) + -(1 / (1 - s)) + s * J‖ := by ring_nf
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖-(1 / (1 - s))‖ + ‖s * J‖ := norm_add₃_le
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * ‖J‖ := by
        simp [norm_neg]
    _ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * (1 / s.re) := by gcongr
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by ring

/-! ## Linear growth in σ ≥ δ  [Tit86, §5.1] -/

/-- **Linear growth of ζ in every right half-plane σ ≥ δ > 0**, explicit constant:
‖ζ(s)‖ ≤ (5/2 + δ⁻¹)·|Im s| for Re s ≥ δ, |Im s| ≥ 1. -/
theorem riemannZeta_linear_growth {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : δ ≤ s.re)
    (ht : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ (5 / 2 + δ⁻¹) * |s.im| := by
  have hσpos : 0 < s.re := lt_of_lt_of_le hδ hσ
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at ht
  have h := norm_riemannZeta_le_of_re_pos hσpos hs1
  have him : |s.im| ≤ ‖1 - s‖ := by
    simpa using Complex.abs_im_le_norm (1 - s)
  have h1 : 1 / ‖1 - s‖ ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h2 : ‖s‖ / s.re ≤ 1 + δ⁻¹ * |s.im| := by
    have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hσpos] at hn
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / δ := by gcongr
      _ = 1 + δ⁻¹ * |s.im| := by rw [div_eq_inv_mul]
  have h3 : (5 / 2 : ℝ) ≤ 5 / 2 * |s.im| := by nlinarith
  nlinarith [h, h1, h2, h3]

/-- ∃-constant form: for every δ > 0 there is C > 0 with
‖ζ(s)‖ ≤ C·|Im s| whenever Re s ≥ δ and |Im s| ≥ 1. -/
theorem zeta_growth {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| := by
  refine ⟨5 / 2 + δ⁻¹, by positivity, fun s hσ ht => riemannZeta_linear_growth hδ hσ ht⟩

/-- Polynomial-growth form (the shape used in Zeta23/WeilEF/Landau.lean):
∃ A C, 0 < C ∧ ∀ s, 1/4 ≤ Re s → Re s ≤ 2 → 1 ≤ |Im s| → ‖ζ s‖ ≤ C·|Im s|^A  (we give A = 1;
the upper constraint on Re s is not used). -/
theorem zeta_growth_quarter :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨C, hC, h⟩ := zeta_growth (δ := 1 / 4) (by norm_num)
  refine ⟨1, C, hC, fun s h₁ _ h₃ => ?_⟩
  simpa [Real.rpow_one] using h s h₁ h₃

/-- **Consumer interface (Zeta23/RvM/LocalCount.lean).** Polynomial growth to
the right of σ = 0.15, uniform down to small |Im s| as long as s keeps distance ≥ 1 from the pole:
∃ A C, 0 < C ∧ ∀ s, 0.15 ≤ Re s → 1 ≤ ‖s − 1‖ → ‖ζ s‖ ≤ C·(|Im s| + 3)^A.  (We give A = 1, C = 20/3.) -/
theorem zeta_growth_right_at (s : ℂ) (hσ : (0.15 : ℝ) ≤ s.re) (h1 : 1 ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ 20 / 3 * (|s.im| + 3) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have hσpos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at h1
  have h := norm_riemannZeta_le_of_re_pos hσpos hs1
  have h1' : 1 / ‖1 - s‖ ≤ 1 := by
    rw [norm_sub_rev] at h1
    rw [div_le_one (by linarith)]
    exact h1
  have hσ' : (3 : ℝ) / 20 ≤ s.re := by
    have := hσ; norm_num at this ⊢; linarith
  have h2 : ‖s‖ / s.re ≤ 1 + 20 / 3 * |s.im| := by
    have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hσpos] at hn
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / (3 / 20) := by gcongr
      _ = 1 + 20 / 3 * |s.im| := by ring
  have ht : 0 ≤ |s.im| := abs_nonneg _
  linarith [h, h1', h2, ht]

theorem zeta_growth_right :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A :=
  ⟨1, 20 / 3, by norm_num, zeta_growth_right_at⟩

/-! ## Bounds on Re s ≥ 2 (the Jensen disc centre)  -/

/-- For Re s ≥ 2: ‖ζ(s) − 1‖ ≤ Σ_{n≥2} n^{−2} = π²/6 − 1. -/
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  -- the shifted Dirichlet series  f n := 1/(n+1)^s,  ζ s = ∑' f n
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hsum : Summable f := by
    have h0 := Complex.summable_one_div_nat_cpow.mpr hs1
    have := (summable_nat_add_iff 1).mpr h0
    simpa [f] using this
  have hzeta : riemannZeta s = ∑' n, f n := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hf0 : f 0 = 1 := by simp [f]
  have hsplit : riemannZeta s - 1 = ∑' n, f (n + 1) := by
    rw [hzeta, hsum.tsum_eq_zero_add, hf0]; ring
  -- termwise comparison with 1/(n+2)^2
  have hle : ∀ n : ℕ, ‖f (n + 1)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have hpos : 0 < n + 2 := by omega
    have hf1 : f (n + 1) = 1 / ((n + 2 : ℕ) : ℂ) ^ s := by
      simp only [f]
      congr 2
      push_cast
      ring
    rw [hf1, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos]
    have hbase : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hpow : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_two] at hpow
    have h2pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) ^ 2 := by positivity
    calc 1 / ((n + 2 : ℕ) : ℝ) ^ s.re ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 :=
          one_div_le_one_div_of_le h2pos hpow
      _ = 1 / ((n : ℝ) + 2) ^ 2 := by push_cast; ring
  have htwo : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun fun n => by ring
  rw [hsplit]
  have hsum' : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  calc ‖∑' n, f (n + 1)‖ ≤ ∑' n, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsum'.norm
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := hsum'.norm.tsum_le_tsum hle htwo.summable
    _ = Real.pi ^ 2 / 6 - 1 := htwo.tsum_eq

/-- π²/6 − 1 < 1 (π < 3.15 ⇒ π² < 9.93 < 12). -/
lemma pi_sq_div_six_sub_one_lt_one : Real.pi ^ 2 / 6 - 1 < 1 := by
  have := Real.pi_lt_d2  -- π < 3.15
  nlinarith [Real.pi_pos]

/-- Lower bound at the Jensen disc centre: 0 < 2 − π²/6 ≤ ‖ζ(s)‖ for Re s ≥ 2. -/
theorem norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - riemannZeta s‖ ≤ ‖riemannZeta s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith

lemma two_sub_pi_sq_div_six_pos : 0 < 2 - Real.pi ^ 2 / 6 := by
  linarith [pi_sq_div_six_sub_one_lt_one]

/-- 1/3 < 2 − π²/6 (π < 3.15 ⇒ π²/6 < 1.654). -/
lemma one_third_lt_two_sub_pi_sq_div_six : (1 / 3 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- **Consumer interface.** ‖ζ(2 + it)‖ ≥ 1/3 for all real t. -/
theorem zeta_lower_bound_two : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := by
  intro t
  have h := norm_riemannZeta_ge_of_two_le_re (s := 2 + t * I) (by simp)
  linarith [one_third_lt_two_sub_pi_sq_div_six]

/-- ζ does not vanish on Re s ≥ 2 (of course Mathlib has this for Re s ≥ 1:
`riemannZeta_ne_zero_of_one_le_re`; restated for convenience). -/
theorem riemannZeta_ne_zero_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by linarith)

/-- Upper bound on Re s ≥ 2: ‖ζ(s)‖ ≤ π²/6. -/
theorem norm_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := by
    simpa using norm_le_norm_sub_add (riemannZeta s) (1 : ℂ)
  simp only [norm_one] at h'
  linarith

end RvM
end Zeta23
