module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Mu.lean — the remaining H-Γ fields from the digamma series.  Canonical text: the paper [eq:mufacts]:
"μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1, μ(τ) = (1/2π)log(|τ|/2π)
+ O(τ⁻²), μ′(τ) ≪ |τ|⁻¹ (|τ| ≥ 1)" plus the [eq:muints] integrals.
The ψ-toolkit is developed at a parametrized abscissa
a ∈ (0,1) (covers ζ's a = 1/4 and, composed with the recurrence, Theorem E's
a = 1/4 + κ/2).  Foundation: Zeta23.DigammaSeries.
-/
public import Zeta23.Analytic.Stirling
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

noncomputable section

namespace Zeta23
namespace MuFields

open Complex Filter Topology

variable {a : ℝ}

/-- Points a + it with a ∈ (0,1) avoid the integers. -/
lemma abscissa_mem (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    ((a : ℂ) + Complex.I * (t : ℂ)) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by rw [hre]; exact ha0
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by rw [hre]; exact ha1
    exact_mod_cast h
  omega

/-- The real part of the n-th series term on the vertical line Re = a. -/
lemma re_term_eq (t : ℝ) (n : ℕ) :
    ((1 : ℂ) / ((n : ℂ) + 1) - 1 / (((a : ℂ) + Complex.I * t) + n + 1)).re
      = 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) := by
  rw [Complex.sub_re]
  congr 1
  · rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) / ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((((1 : ℝ) / ((n : ℝ) + 1)) : ℝ) : ℂ) by
        push_cast
        ring]
    exact Complex.ofReal_re _
  · rw [one_div, Complex.inv_re]
    have hre : (((a : ℂ) + Complex.I * t) + n + 1).re = (n : ℝ) + 1 + a := by
      simp
      ring
    have him : (((a : ℂ) + Complex.I * t) + n + 1).im = t := by simp
    rw [hre, Complex.normSq_apply, hre, him]
    ring

/-- Re(1/z) on the line. -/
lemma re_inv_eq (t : ℝ) :
    ((1 : ℂ) / ((a : ℂ) + Complex.I * t)).re = a / (a ^ 2 + t ^ 2) := by
  rw [one_div, Complex.inv_re]
  have hre : ((a : ℂ) + Complex.I * t).re = a := by simp
  have him : ((a : ℂ) + Complex.I * t).im = t := by simp
  rw [hre, Complex.normSq_apply, hre, him]
  ring

/-- Summability of the real series. -/
lemma summable_re_terms (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    Summable (fun n : ℕ =>
      1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hs := Zeta23.DigammaSeries.summable_digamma_series (abscissa_mem ha0 ha1 t)
  have hmap := hs.map Complex.reCLM Complex.continuous_re
  refine hmap.congr fun n => ?_
  exact re_term_eq t n

/-- **The real digamma series on vertical lines** (the paper's display in [eq:mufacts]):
Re ψ(a+it) = −γ − a/(a²+t²) + Σₙ (1/(n+1) − (n+1+a)/((n+1+a)²+t²)). -/
theorem re_digamma_vertical (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re
      = -Real.eulerMascheroniConstant - a / (a ^ 2 + t ^ 2)
        + ∑' n : ℕ,
          (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hmem := abscissa_mem ha0 ha1 t
  have h := Zeta23.DigammaSeries.digamma_series hmem
  have hre := congrArg Complex.re h
  rw [hre]
  rw [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
  congr 1
  · congr 1
    exact re_inv_eq t
  · -- re of the tsum = tsum of re
    have hs := Zeta23.DigammaSeries.summable_digamma_series hmem
    have hmap := Complex.reCLM.map_tsum hs
    rw [show (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)
        - 1 / (((a : ℂ) + Complex.I * t) + n + 1))).re
      = Complex.reCLM (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)
        - 1 / (((a : ℂ) + Complex.I * t) + n + 1))) from rfl, hmap]
    congr 1
    funext n
    exact re_term_eq t n

/-! ### Monotonicity on the vertical line, and the μ order facts -/

/-- Re ψ(a + it) is monotone in t on t ≥ 0. -/
theorem re_digamma_mono (ha0 : 0 < a) (ha1 : a < 1) :
    MonotoneOn (fun t : ℝ => (Complex.digamma ((a : ℂ) + Complex.I * t)).re)
      (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  simp only
  rw [re_digamma_vertical ha0 ha1, re_digamma_vertical ha0 ha1]
  have ht1 : (0 : ℝ) ≤ t₁ := h₁
  have hsq : t₁ ^ 2 ≤ t₂ ^ 2 := by nlinarith
  have hmono1 : a / (a ^ 2 + t₂ ^ 2) ≤ a / (a ^ 2 + t₁ ^ 2) :=
    div_le_div_of_nonneg_left ha0.le (by positivity) (by linarith)
  have hterm : ∀ n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₁ ^ 2))
        ≤ 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₂ ^ 2) := by
    intro n
    have hna : (0 : ℝ) < (n : ℝ) + 1 + a := by positivity
    have h2 : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₂ ^ 2)
        ≤ ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₁ ^ 2) :=
      div_le_div_of_nonneg_left hna.le (by positivity) (by linarith)
    linarith
  have hsum := (summable_re_terms ha0 ha1 t₁).tsum_le_tsum hterm
    (summable_re_terms ha0 ha1 t₂)
  linarith

/-- Bridge to Zeta23.mu: μ(τ) in terms of the parametrized line at a = 1/4, t = τ/2. -/
lemma mu_eq (τ : ℝ) :
    Zeta23.mu τ = (1 / (2 * Real.pi))
        * (Complex.digamma ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
      - Real.log Real.pi / (2 * Real.pi) := by
  unfold Zeta23.mu
  congr 3
  push_cast
  ring

/-- [eq:mufacts] "increasing in |τ|": μ is monotone on τ ≥ 0. -/
theorem mu_monotoneOn : MonotoneOn Zeta23.mu (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  rw [mu_eq, mu_eq]
  have hmono := re_digamma_mono (a := 1 / 4) (by norm_num) (by norm_num)
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₁] : (0 : ℝ) ≤ t₁ / 2))
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₂] : (0 : ℝ) ≤ t₂ / 2))
    (by linarith)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2π : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hmono h2π
  linarith

/-- [eq:mufacts] "μ ≥ μ(0)". -/
theorem mu_zero_le (τ : ℝ) : Zeta23.mu 0 ≤ Zeta23.mu τ := by
  have heven := Zeta23.mu_even
  rcases le_total 0 τ with h | h
  · exact mu_monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  · have h1 : Zeta23.mu τ = Zeta23.mu (-τ) := (heven τ).symm
    rw [h1]
    exact mu_monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith)) (by linarith)

/-- [eq:mufacts] "μ(0) > −1". -/
theorem neg_one_lt_mu_zero : (-1 : ℝ) < Zeta23.mu 0 := by
  rw [mu_eq]
  rw [show ((0 : ℝ) / 2 : ℝ) = (0 : ℝ) by norm_num]
  have hre := re_digamma_vertical (a := 1 / 4) (by norm_num) (by norm_num) 0
  rw [hre]
  have hS : (0 : ℝ) ≤ ∑' n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2)) := by
    refine tsum_nonneg fun n => ?_
    have hna : (0 : ℝ) < (n : ℝ) + 1 + 1 / 4 := by positivity
    have h1 : ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2)
        = 1 / ((n : ℝ) + 1 + 1 / 4) := by
      rw [show (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2) = ((n : ℝ) + 1 + 1 / 4) ^ 2 by ring]
      rw [sq]
      rw [div_mul_eq_div_div]
      rw [div_self hna.ne']
    rw [h1]
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : 1 / ((n : ℝ) + 1 + 1 / 4) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le h2 (by linarith)
    linarith
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ3 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have hlogπ : Real.log Real.pi < 1.4 := by
    have h1 : Real.log Real.pi < Real.log 4 := Real.log_lt_log Real.pi_pos hπ4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h3 := Real.log_two_lt_d9
    nlinarith
  have hquarter : (1 / 4 : ℝ) / ((1 / 4 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 4 := by norm_num
  rw [hquarter]
  set S : ℝ := ∑' n : ℕ,
    (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2))
    with hSdef
  have hform : 1 / (2 * Real.pi) * (-Real.eulerMascheroniConstant - 4 + S)
        - Real.log Real.pi / (2 * Real.pi)
      = (-Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi) * (1 / (2 * Real.pi)) := by
    ring
  rw [hform]
  have hX : -(2 * Real.pi)
      < -Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi := by
    have hnorm : (1.4 : ℝ) = 14 / 10 := by norm_num
    linarith
  calc (-1 : ℝ) = -(2 * Real.pi) * (1 / (2 * Real.pi)) := by
        field_simp
    _ < (-Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi) * (1 / (2 * Real.pi)) :=
        mul_lt_mul_of_pos_right hX (by positivity)

/-! ### The derivative bound μ′ ≪ 1/|τ|  (via the trigamma series) -/

/-- Trigamma tail bound on the quarter line: Σ'ₙ ((1/4+n)² + t²)⁻¹ ≤ 12/|t| for |t| ≥ 1/2. -/
lemma trigamma_tail_le {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹ ≤ 12 / |t| := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have htsq : (0 : ℝ) < t ^ 2 := by
    have := sq_abs t
    nlinarith
  set N : ℕ := ⌈|t|⌉₊ + 2 with hN
  have hNt : |t| ≤ (N : ℝ) := by
    calc |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (N : ℝ) := by
          rw [hN]
          push_cast
          linarith
  have hNle : (N : ℝ) ≤ |t| + 3 := by
    rw [hN]
    push_cast
    have := Nat.ceil_lt_add_one (abs_nonneg t)
    linarith
  have hsummable : Summable (fun n : ℕ => (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹) := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) ?_ ?_
    · have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at h3
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      nlinarith
  rw [← hsummable.sum_add_tsum_nat_add N]
  have hhead : ∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹
      ≤ (N : ℝ) * (t ^ 2)⁻¹ := by
    have h1 : ∀ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ := by
      intro i _
      gcongr
      nlinarith [sq_nonneg ((1 / 4 : ℝ) + i)]
    calc ∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹
        ≤ ∑ _i ∈ Finset.range N, (t ^ 2)⁻¹ := Finset.sum_le_sum h1
      _ = (N : ℝ) * (t ^ 2)⁻¹ := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
  have htail : ∑' i : ℕ, (((1 / 4 : ℝ) + ((i + N : ℕ) : ℝ)) ^ 2 + t ^ 2)⁻¹
      ≤ ((N : ℝ) - 1)⁻¹ := by
    have hN2 : (2 : ℕ) ≤ N := by
      rw [hN]
      omega
    push_cast
    refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun K => ?_
    have hterm : ∀ i : ℕ, (((1 / 4 : ℝ) + (i + N)) ^ 2 + t ^ 2)⁻¹
        ≤ ((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹ := by
      intro i
      have hiN1 : (1 : ℝ) ≤ (i : ℝ) + N - 1 := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        have := Nat.cast_nonneg (α := ℝ) i
        linarith
      have hpos1 : (0 : ℝ) < (i : ℝ) + N - 1 := by linarith
      have hpos2 : (0 : ℝ) < (i : ℝ) + N := by linarith
      have hsub : ((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹
          = (((i : ℝ) + N - 1) * ((i : ℝ) + N))⁻¹ := by
        rw [inv_sub_inv hpos1.ne' hpos2.ne']
        ring_nf
      rw [hsub]
      have hd1 : (0 : ℝ) < ((i : ℝ) + N - 1) * ((i : ℝ) + N) := mul_pos hpos1 hpos2
      have hd2 : ((i : ℝ) + N - 1) * ((i : ℝ) + N)
          ≤ ((1 / 4 : ℝ) + ((i : ℝ) + (N : ℝ))) ^ 2 + t ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) i, sq_nonneg t]
      have h3 := one_div_le_one_div_of_le hd1 hd2
      simpa [one_div] using h3
    calc ∑ i ∈ Finset.range K, (((1 / 4 : ℝ) + (i + N)) ^ 2 + t ^ 2)⁻¹
        ≤ ∑ i ∈ Finset.range K, (((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ((N : ℝ) - 1)⁻¹ - ((K : ℝ) + N - 1)⁻¹ := by
          have htel := Finset.sum_range_sub' (f := fun i : ℕ => ((i : ℝ) + N - 1)⁻¹) K
          simp only [Nat.cast_zero, zero_add] at htel
          rw [← htel]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hx : (((i + 1 : ℕ) : ℝ) + N - 1)⁻¹ = ((i : ℝ) + N)⁻¹ := by
            push_cast
            ring_nf
          rw [hx]
      _ ≤ ((N : ℝ) - 1)⁻¹ := by
          have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
          have : (0 : ℝ) < (K : ℝ) + N - 1 := by
            have := Nat.cast_nonneg (α := ℝ) K
            linarith
          have : (0 : ℝ) ≤ ((K : ℝ) + N - 1)⁻¹ := by positivity
          linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have h2 : (2 : ℕ) ≤ N := by
      rw [hN]
      omega
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hNm1 : |t| ≤ (N : ℝ) - 1 := by
    rw [hN]
    push_cast
    have := Nat.le_ceil |t|
    linarith
  have htail2 : ((N : ℝ) - 1)⁻¹ ≤ |t|⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le ht0 hNm1
  have hhead2 : (N : ℝ) * (t ^ 2)⁻¹ ≤ 10 / |t| := by
    have hts : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [hts]
    rw [div_eq_mul_inv]
    have h1 : (N : ℝ) ≤ 7 * |t| := by linarith
    calc (N : ℝ) * ((|t| ^ 2)⁻¹) ≤ 7 * |t| * ((|t| ^ 2)⁻¹) := by
          gcongr
      _ = 7 * |t|⁻¹ := by
          field_simp
      _ ≤ 10 * |t|⁻¹ := by
          have : (0 : ℝ) ≤ |t|⁻¹ := by positivity
          linarith
  calc (∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹)
        + ∑' i : ℕ, (((1 / 4 : ℝ) + ((i + N : ℕ) : ℝ)) ^ 2 + t ^ 2)⁻¹
      ≤ (N : ℝ) * (t ^ 2)⁻¹ + ((N : ℝ) - 1)⁻¹ := add_le_add hhead htail
    _ ≤ 10 / |t| + |t|⁻¹ := add_le_add hhead2 htail2
    _ ≤ 12 / |t| := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have : (0 : ℝ) ≤ |t|⁻¹ := by positivity
        linarith

/-- Summability of the quarter-line trigamma comparison series. -/
lemma summable_quarter_line (t : ℝ) :
    Summable (fun n : ℕ => (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) ?_ ?_
  · have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
    have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
      funext n
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [heq] at h3
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    nlinarith

set_option backward.isDefEq.respectTransparency false in
/-- [eq:mufacts] "μ′(τ) ≪ |τ|⁻¹" (the GammaFacts.deriv_bound field shape). -/
theorem mu_deriv_bound : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv Zeta23.mu τ| ≤ C / |τ| := by
  refine ⟨24 / Real.pi, fun τ hτ => ?_⟩
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  set zA : ℂ := (1 / 4 : ℂ) + (Complex.I / 2) * (τ : ℂ) with hzA
  have hzA_eq : zA = ((1 / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ) := by
    rw [hzA]
    push_cast
    ring
  have hmem : zA ∈ Complex.integerComplement := by
    rw [hzA_eq]
    exact abscissa_mem (by norm_num) (by norm_num) (τ / 2)
  have hψd : DifferentiableAt ℂ Complex.digamma zA :=
    Zeta23.Stirling.differentiableAt_digamma hmem
  -- chain rule: μ has derivative (1/2π)·Re(ψ′(zA)·(I/2)) at τ
  have hginner : HasDerivAt (fun x : ℝ => (1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))
      (Complex.I / 2) τ := by
    have h1 : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) 1 τ := Complex.ofRealCLM.hasDerivAt
    have h2 := (h1.const_mul (Complex.I / 2)).const_add ((1 / 4 : ℂ))
    simpa using h2
  have hcompd : HasDerivAt
      (fun x : ℝ => Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ)))
      ((Complex.I / 2) • deriv Complex.digamma zA) τ := by
    have h3 := HasDerivAt.scomp τ hψd.hasDerivAt hginner
    exact h3
  have hre : HasDerivAt
      (fun x : ℝ => (Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))).re)
      (((Complex.I / 2) • deriv Complex.digamma zA).re) τ :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ hcompd)
  have hmuD : HasDerivAt Zeta23.mu
      (1 / (2 * Real.pi) * (((Complex.I / 2) • deriv Complex.digamma zA).re)) τ := by
    have h4 := (hre.const_mul (1 / (2 * Real.pi))).sub_const (Real.log Real.pi / (2 * Real.pi))
    have h5 : Zeta23.mu = fun x : ℝ =>
        1 / (2 * Real.pi) * (Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))).re
          - Real.log Real.pi / (2 * Real.pi) := by
      funext x
      unfold Zeta23.mu
      rw [show ((1 / 4 : ℂ) + Complex.I * (x : ℂ) / 2)
          = (1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ) from by ring]
    rw [h5]
    exact h4
  rw [hmuD.deriv]
  -- bound the derivative value by the trigamma tail
  have htri := Zeta23.Stirling.hasSum_trigamma hmem
  have hnorm_term : ∀ n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖
      = (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
    intro n
    have hre2 : (zA + n).re = (1 / 4 : ℝ) + n := by
      rw [hzA_eq]
      simp
    have him2 : (zA + n).im = τ / 2 := by
      rw [hzA_eq]
      simp
    rw [norm_div, norm_one, norm_pow, one_div]
    congr 1
    rw [show ‖zA + (n : ℂ)‖ ^ 2 = Complex.normSq (zA + n) from Complex.sq_norm _,
      Complex.normSq_apply, hre2, him2]
    ring
  have hsummable_norm : Summable (fun n : ℕ => ‖(1 : ℂ) / (zA + n) ^ 2‖) := by
    refine (summable_quarter_line (τ / 2)).congr fun n => ?_
    exact (hnorm_term n).symm
  have hψ'bound : ‖deriv Complex.digamma zA‖ ≤ 24 / |τ| := by
    have h6 : deriv Complex.digamma zA = ∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2 := htri.tsum_eq.symm
    rw [h6]
    calc ‖∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsummable_norm
      _ = ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
          congr 1
          funext n
          exact hnorm_term n
      _ ≤ 12 / |τ / 2| := trigamma_tail_le (by
          rw [abs_div]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          linarith)
      _ = 24 / |τ| := by
          rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
          field_simp
          norm_num
  -- |Re((I/2)•ψ′)| ≤ ‖ψ′‖/2
  have hval : |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ ‖deriv Complex.digamma zA‖ / 2 := by
    calc |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
        ≤ ‖(Complex.I / 2) • deriv Complex.digamma zA‖ := Complex.abs_re_le_norm _
      _ = ‖Complex.I / 2‖ * ‖deriv Complex.digamma zA‖ := norm_smul _ _
      _ = ‖deriv Complex.digamma zA‖ / 2 := by
          rw [norm_div, Complex.norm_I]
          rw [show ‖(2 : ℂ)‖ = 2 from by
            rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (by norm_num)]]
          ring
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ 1 / (2 * Real.pi) * (‖deriv Complex.digamma zA‖ / 2) := by
        gcongr
    _ ≤ 1 / (2 * Real.pi) * ((24 / |τ|) / 2) := by
        gcongr
    _ ≤ (24 / Real.pi) / |τ| := by
        rw [div_div, div_mul_eq_mul_div, one_mul]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        have e1 : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ hπ.ne'
        have e2 : |τ| * |τ|⁻¹ = 1 := mul_inv_cancel₀ hτ0.ne'
        nlinarith [e1, e2]

end MuFields
end Zeta23
