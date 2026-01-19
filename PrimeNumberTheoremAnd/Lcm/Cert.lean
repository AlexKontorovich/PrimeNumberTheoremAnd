import Architect
import PrimeNumberTheoremAnd.Lcm.Base

namespace Lcm

open ArithmeticFunction hiding log
open Finset Nat Real
open scoped BigOperators

namespace Numerical


/-!
`Cert.lean` is the ONLY place with hard-coded numeric constants and proofs about them.

It defines the *numeric contract* that `ChoosePrime.lean` will assume.
-/

/-- Numeric/analytic contract: the properties of `X₀` and `gap.δ` needed for prime selection. -/
structure Criterion where
  /- Whatever properties ChoosePrime needs, but no primes p/q here. -/
  sqrt_ge_X₀ : ∀ {n : ℕ}, n ≥ X₀ ^ 2 → (X₀ : ℝ) ≤ √(n : ℝ)
  eps_nonneg : ∀ {n : ℕ}, n ≥ X₀ ^ 2 → 0 ≤ gap.δ (√(n : ℝ))
  inv_cube_log_sqrt_le :
    ∀ {n : ℕ}, n ≥ X₀ ^ 2 → 1 / (log √(n : ℝ)) ^ 3 ≤ (0.000675 : ℝ)
  /- add the rest of your numeric lemmas here -/
  -- ...



noncomputable abbrev eps_log : ℝ := (0.000675 : ℝ)
noncomputable abbrev onePlusEps_log : ℝ := (1 : ℝ) + eps_log


blueprint_comment /--
\subsection{Reduction to a small epsilon-inequality}
-/


/- theorem `exists_p_primes` lemmas -/
/- vote: 2 -/
/- Helper lemmas -/
lemma gap_delta_def (x : ℝ) : gap.δ x = 1 / (log x) ^ (3 : ℝ) := by
  -- `gap` is the (latest) Dusart provider; unfolding exposes the concrete `δ`.
  simp [Lcm.gap, PrimeGaps.latest, PrimeGaps.provider, PrimeGaps.Dusart.provider]

lemma gap_delta_nonneg_of_one_lt {x : ℝ} (hx : 1 < x) : 0 ≤ gap.δ x := by
  have hlogpos : 0 < log x := Real.log_pos hx
  have hdenpos : 0 < (log x) ^ (3 : ℝ) := Real.rpow_pos_of_pos hlogpos (3 : ℝ)
  have hpos : 0 < (1 / (log x) ^ (3 : ℝ)) := one_div_pos.mpr hdenpos
  -- rewrite back to `gap.δ`.
  simpa [gap_delta_def] using (le_of_lt hpos)

lemma gap_delta_antitone_of_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    gap.δ b ≤ gap.δ a := by
  -- Since `log` is increasing on `(0,∞)` and `t ↦ t^3` is increasing on `[0,∞)`, the
  -- denominator `(log x)^3` increases with `x`, hence its reciprocal decreases.
  have ha_pos : 0 < a := lt_trans (by norm_num) ha
  have hlog_le : log a ≤ log b := Real.log_le_log ha_pos hab
  have hloga_pos : 0 < log a := Real.log_pos ha
  have hloga_nonneg : 0 ≤ log a := le_of_lt hloga_pos
  have hpow_le : (log a) ^ (3 : ℝ) ≤ (log b) ^ (3 : ℝ) := by
    exact Real.rpow_le_rpow hloga_nonneg hlog_le (by norm_num)
  have hpow_pos : 0 < (log a) ^ (3 : ℝ) := Real.rpow_pos_of_pos hloga_pos (3 : ℝ)
  have hdiv_le : (1 / (log b) ^ (3 : ℝ)) ≤ 1 / (log a) ^ (3 : ℝ) :=
    one_div_le_one_div_of_le hpow_pos hpow_le
  simpa [gap_delta_def] using hdiv_le

lemma gap_delta_le_one_of_three_le {x : ℝ} (hx : (3 : ℝ) ≤ x) : gap.δ x ≤ 1 := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx

  -- First show `1 < log x` using `exp 1 < 3 ≤ x`.
  have hexp1_lt_x : Real.exp (1 : ℝ) < x := by
    have hexp1_lt_3 : Real.exp (1 : ℝ) < (3 : ℝ) := by
      sorry
      -- simpa using Real.exp_one_lt_d9
    have h3_lt_x : (3 : ℝ) < x := by sorry --linarith
    exact lt_trans hexp1_lt_3 h3_lt_x
  have hlog_gt_one : (1 : ℝ) < log x := (Real.lt_log_iff_exp_lt hx_pos).2 hexp1_lt_x
  have h1le_log : (1 : ℝ) ≤ log x := le_of_lt hlog_gt_one

  -- Hence `(log x)^3 ≥ 1`, so its reciprocal is ≤ 1.
  have hpow_ge : (1 : ℝ) ≤ (log x) ^ (3 : ℝ) := by
    have : (1 : ℝ) ^ (3 : ℝ) ≤ (log x) ^ (3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h1le_log (by norm_num)
    simpa using this
  have hdiv : (1 / (log x) ^ (3 : ℝ)) ≤ (1 : ℝ) := by
    have : (1 / (log x) ^ (3 : ℝ)) ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hpow_ge
    simpa using this

  simpa [gap_delta_def] using hdiv


lemma gap_delta_strict_antitone_of_lt {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    gap.δ b < gap.δ a := by
  have ha_pos : 0 < a := lt_trans (by norm_num) ha
  have hlog_lt : log a < log b := log_lt_log ha_pos hab
  have hloga_pos : 0 < log a := Real.log_pos ha
  have hloga_nonneg : 0 ≤ log a := le_of_lt hloga_pos
  have hpow_lt : (log a) ^ (3 : ℝ) < (log b) ^ (3 : ℝ) := by
    exact Real.rpow_lt_rpow hloga_nonneg hlog_lt (by norm_num)
  have hpow_pos : 0 < (log a) ^ (3 : ℝ) := Real.rpow_pos_of_pos hloga_pos (3 : ℝ)
  have hdiv_lt : (1 / (log b) ^ (3 : ℝ)) < 1 / (log a) ^ (3 : ℝ) :=
    one_div_lt_one_div_of_lt hpow_pos hpow_lt
  simpa [gap_delta_def] using hdiv_lt

lemma sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ √(n : ℝ) := by
  /-- (C1) `x := √n` is above the provider threshold. -/
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)


lemma step1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) := by
  have hx₀ : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hX₀_one : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hsqrt_one : (1 : ℝ) < √(n : ℝ) := lt_of_lt_of_le hX₀_one hx₀
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    gap_delta_nonneg_of_one_lt (x := √(n : ℝ)) hsqrt_one
  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := sqrt_nonneg (n : ℝ)
  have h1 : (1 : ℝ) ≤ 1 + gap.δ (√(n : ℝ)) := by
    exact le_add_of_nonneg_right hδ_nonneg
  have hsqrt_le : √(n : ℝ) ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) :=
    le_mul_of_one_le_right hsqrt_nonneg h1
  exact le_trans hx₀ hsqrt_le


lemma step2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ 2 := by
  have hstep1 : (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) :=
    step1_ge_X₀ (n := n) hn
  have hx₀ : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hX₀_one : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hsqrt_one : (1 : ℝ) < √(n : ℝ) := lt_of_lt_of_le hX₀_one hx₀
  have hε_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    gap_delta_nonneg_of_one_lt (x := √(n : ℝ)) hsqrt_one
  have h1 : (1 : ℝ) ≤ 1 + gap.δ (√(n : ℝ)) :=
    le_add_of_nonneg_right hε_nonneg
  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := sqrt_nonneg (n : ℝ)
  have honeplus_nonneg : 0 ≤ (1 + gap.δ (√(n : ℝ))) := by
    linarith
  have hprod_nonneg : 0 ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) :=
    mul_nonneg hsqrt_nonneg honeplus_nonneg
  have hmul :
      (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ)))
        ≤ ((√(n : ℝ)) * (1 + gap.δ (√(n : ℝ)))) * (1 + gap.δ (√(n : ℝ))) :=
    le_mul_of_one_le_right hprod_nonneg h1
  have hmul' :
      (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ)))
        ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ 2 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact hstep1.trans hmul'


lemma step1_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ x * (1 + ε) ^ 2 := by
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  have hx₀ : (X₀ : ℝ) ≤ x := by
    have : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
    simpa [hx] using this
  have hX₀_one : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hx_one : (1 : ℝ) < x := lt_of_lt_of_le hX₀_one hx₀
  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using gap_delta_nonneg_of_one_lt (x := x) hx_one
  have h1 : (1 : ℝ) ≤ 1 + ε := le_add_of_nonneg_right hε_nonneg
  have hx_nonneg : 0 ≤ x := by
    simpa [hx] using (sqrt_nonneg (n : ℝ))
  have honeplus_nonneg : 0 ≤ (1 + ε) := by
    linarith
  have hxy : x ≤ x * (1 + ε) :=
    le_mul_of_one_le_right hx_nonneg h1
  have hδ_le : gap.δ (x * (1 + ε)) ≤ ε := by
    have : gap.δ (x * (1 + ε)) ≤ gap.δ x :=
      gap_delta_antitone_of_le (a := x) (b := x * (1 + ε)) hx_one hxy
    simpa [hε] using this
  have h1' : (1 : ℝ) + gap.δ (x * (1 + ε)) ≤ 1 + ε := by
    linarith
  have hmul_nonneg : 0 ≤ x * (1 + ε) := mul_nonneg hx_nonneg honeplus_nonneg
  have hmul : (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ (x * (1 + ε)) * (1 + ε) :=
    mul_le_mul_of_nonneg_left h1' hmul_nonneg
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul


lemma step2_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2)) ≤ x * (1 + ε) ^ 3 := by
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  have hx₀ : (X₀ : ℝ) ≤ x := by
    have : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
    simpa [hx] using this
  have hX₀_one : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hx_one : (1 : ℝ) < x := lt_of_lt_of_le hX₀_one hx₀
  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using gap_delta_nonneg_of_one_lt (x := x) hx_one
  have h1 : (1 : ℝ) ≤ 1 + ε := le_add_of_nonneg_right hε_nonneg
  have hx_nonneg : 0 ≤ x := by
    simpa [hx] using (sqrt_nonneg (n : ℝ))
  have honeplus_nonneg : 0 ≤ (1 + ε) := by
    linarith
  have hpow_one : (1 : ℝ) ≤ (1 + ε) ^ 2 := by
    have hmul : (1 : ℝ) * (1 : ℝ) ≤ (1 + ε) * (1 + ε) :=
      mul_le_mul h1 h1 (by norm_num) honeplus_nonneg
    simpa [pow_two] using hmul
  have hxy : x ≤ x * (1 + ε) ^ 2 :=
    le_mul_of_one_le_right hx_nonneg hpow_one
  have hδ_le : gap.δ (x * (1 + ε) ^ 2) ≤ ε := by
    have : gap.δ (x * (1 + ε) ^ 2) ≤ gap.δ x :=
      gap_delta_antitone_of_le (a := x) (b := x * (1 + ε) ^ 2) hx_one hxy
    simpa [hε] using this
  have h1' : (1 : ℝ) + gap.δ (x * (1 + ε) ^ 2) ≤ 1 + ε := by
    linarith
  have hmul_nonneg : 0 ≤ x * (1 + ε) ^ 2 := by
    exact mul_nonneg hx_nonneg (sq_nonneg (1 + ε))
  have hmul :
      (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2))
        ≤ (x * (1 + ε) ^ 2) * (1 + ε) :=
    mul_le_mul_of_nonneg_left h1' hmul_nonneg
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul


/- End of theorem `exists_p_primes` lemmas-/


/- theorem `exists_q_primes` lemmas -/
lemma y0_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 := by
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε

  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [hx] using (sqrt_ge_X₀ (n := n) hn)

  -- Crude bounds: `x ≥ X₀ ≥ 8` and `ε ≤ 1`, hence `(1+ε)^3 ≤ 8 ≤ x`.
  have hX₀_ge8 : (8 : ℝ) ≤ (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hx_ge8 : (8 : ℝ) ≤ x := le_trans hX₀_ge8 hxX
  have hx_ge3 : (3 : ℝ) ≤ x := by linarith [hx_ge8]
  have hε_le_one : ε ≤ 1 := by
    simpa [hε] using (gap_delta_le_one_of_three_le (x := x) hx_ge3)
  have hε_nonneg : 0 ≤ ε := by
    -- `x > 1` because `x ≥ 8`.
    have hx_one : (1 : ℝ) < x := by linarith [hx_ge8]
    simpa [hε] using (gap_delta_nonneg_of_one_lt (x := x) hx_one)
  have honeplus_le2 : (1 + ε) ≤ (2 : ℝ) := by linarith
  have honeplus_nonneg : 0 ≤ (1 + ε) := by linarith
  have hpow3_le8 : (1 + ε) ^ 3 ≤ (8 : ℝ) := by
    have : (1 + ε) ^ 3 ≤ (2 : ℝ) ^ 3 :=
      -- pow_le_pow_of_le_left honeplus_nonneg honeplus_le2 3
      sorry
    norm_num at this
    simpa using this
  have hden_le_x : (1 + ε) ^ 3 ≤ x := le_trans hpow3_le8 hx_ge8

  -- Turn this into `X₀ ≤ n / (1+ε)^3` by clearing denominators.
  have hx_nonneg : 0 ≤ x := by
    simpa [hx] using (sqrt_nonneg (n : ℝ))
  have honeplus_pos : 0 < (1 + ε) := by linarith
  have hden_pos : 0 < (1 + ε) ^ 3 := pow_pos honeplus_pos 3

  have hxx_eq_n : x * x = (n : ℝ) := by
    -- `x = √n` by definition.
    simpa [hx] using (mul_self_sqrt (Nat.cast_nonneg n))

  have hmul : (X₀ : ℝ) * (1 + ε) ^ 3 ≤ (n : ℝ) := by
    -- `X₀*(1+ε)^3 ≤ x*(1+ε)^3 ≤ x*x = n`.
    have hden_nonneg : 0 ≤ (1 + ε) ^ 3 := pow_nonneg honeplus_nonneg 3
    have h1 : (X₀ : ℝ) * (1 + ε) ^ 3 ≤ x * (1 + ε) ^ 3 :=
      mul_le_mul_of_nonneg_right hxX hden_nonneg
    have h2 : x * (1 + ε) ^ 3 ≤ x * x :=
      mul_le_mul_of_nonneg_left hden_le_x hx_nonneg
    have : (X₀ : ℝ) * (1 + ε) ^ 3 ≤ x * x := le_trans h1 h2
    simpa [hxx_eq_n] using this

  exact (le_div_iff₀ hden_pos).2 hmul


lemma y1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
  /- Derived from `y0_ge_X₀` plus the fact that dividing by `(1+ε)^2` is larger than
     dividing by `(1+ε)^3` when `1+ε ≥ 1`. -/
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε

  have hy0 : (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 := by
    -- reuse the previous lemma
    simpa [hx, hε] using (y0_ge_X₀ (n := n) hn)

  -- Show `(n)/(1+ε)^3 ≤ (n)/(1+ε)^2`.
  have hX₀_ge8 : (8 : ℝ) ≤ (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [hx] using (sqrt_ge_X₀ (n := n) hn)
  have hx_ge8 : (8 : ℝ) ≤ x := le_trans hX₀_ge8 hxX
  have hx_one : (1 : ℝ) < x := by linarith [hx_ge8]
  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using (gap_delta_nonneg_of_one_lt (x := x) hx_one)
  have honeplus_pos : 0 < (1 + ε) := by linarith
  have honeplus_nonneg : 0 ≤ (1 + ε) := by linarith
  have hone_le : (1 : ℝ) ≤ (1 + ε) := le_add_of_nonneg_right hε_nonneg
  have hpow_nonneg : 0 ≤ (1 + ε) ^ 2 := pow_nonneg honeplus_nonneg 2
  have hpow_le : (1 + ε) ^ 2 ≤ (1 + ε) ^ 3 := by
    -- `(1+ε)^3 = (1+ε)^2 * (1+ε)` and `1 ≤ 1+ε`.
    have : (1 + ε) ^ 2 ≤ (1 + ε) ^ 2 * (1 + ε) :=
      le_mul_of_one_le_right hpow_nonneg hone_le
    simpa [pow_succ, mul_assoc] using this
  have hpow_pos : 0 < (1 + ε) ^ 2 := pow_pos honeplus_pos 2
  have hinv : (1 : ℝ) / (1 + ε) ^ 3 ≤ (1 : ℝ) / (1 + ε) ^ 2 :=
    one_div_le_one_div_of_le hpow_pos hpow_le
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hdiv : (n : ℝ) / (1 + ε) ^ 3 ≤ (n : ℝ) / (1 + ε) ^ 2 := by
    -- multiply the inverse inequality by `n ≥ 0`
    have := mul_le_mul_of_nonneg_left hinv hn_nonneg
    -- `n * (1/d) = n/d`
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  exact le_trans hy0 hdiv

lemma y2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) := by
  /- Same pattern as `y1_ge_X₀`: `n/(1+ε) ≥ n/(1+ε)^2`. -/
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε

  have hy1 : (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
    simpa [hx, hε] using (y1_ge_X₀ (n := n) hn)

  have hX₀_ge8 : (8 : ℝ) ≤ (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [hx] using (sqrt_ge_X₀ (n := n) hn)
  have hx_ge8 : (8 : ℝ) ≤ x := le_trans hX₀_ge8 hxX
  have hx_one : (1 : ℝ) < x := by linarith [hx_ge8]
  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using (gap_delta_nonneg_of_one_lt (x := x) hx_one)
  have honeplus_pos : 0 < (1 + ε) := by linarith
  have honeplus_nonneg : 0 ≤ (1 + ε) := by linarith
  have hone_le : (1 : ℝ) ≤ (1 + ε) := le_add_of_nonneg_right hε_nonneg

  have hpow_nonneg : 0 ≤ (1 + ε) := honeplus_nonneg
  have hpow_le : (1 + ε) ≤ (1 + ε) ^ 2 := by
    -- `(1+ε)^2 = (1+ε) * (1+ε)` and `1 ≤ 1+ε`.
    have : (1 + ε) * (1 : ℝ) ≤ (1 + ε) * (1 + ε) :=
      mul_le_mul_of_nonneg_left hone_le hpow_nonneg
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
  have hpow_pos : 0 < (1 + ε) := honeplus_pos
  have hinv : (1 : ℝ) / (1 + ε) ^ 2 ≤ (1 : ℝ) / (1 + ε) := by
    -- Use antitonicity of `1/x`.
    -- Here `a = 1+ε`, `b = (1+ε)^2`.
    have hpos : 0 < (1 + ε) := honeplus_pos
    have : (1 : ℝ) / (1 + ε) ^ 2 ≤ (1 : ℝ) / (1 + ε) := by
      -- `1/(b) ≤ 1/(a)` since `a ≤ b`.
      exact one_div_le_one_div_of_le hpos hpow_le
    simpa [pow_two] using this
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hdiv : (n : ℝ) / (1 + ε) ^ 2 ≤ (n : ℝ) / (1 + ε) := by
    have := mul_le_mul_of_nonneg_left hinv hn_nonneg
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  exact le_trans hy1 hdiv

lemma y0_mul_one_add_delta_le_y1 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3
    y0 * (1 + gap.δ y0) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  set y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3 with hy0

  have hX₀_ge8 : (8 : ℝ) ≤ (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [hx] using (sqrt_ge_X₀ (n := n) hn)
  have hx_ge8 : (8 : ℝ) ≤ x := le_trans hX₀_ge8 hxX
  have hx_one : (1 : ℝ) < x := by linarith [hx_ge8]

  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using (gap_delta_nonneg_of_one_lt (x := x) hx_one)
  have hε_le_one : ε ≤ 1 := by
    have hx_ge3 : (3 : ℝ) ≤ x := by linarith [hx_ge8]
    simpa [hε] using (gap_delta_le_one_of_three_le (x := x) hx_ge3)
  have honeplus_nonneg : 0 ≤ (1 + ε) := by linarith
  have honeplus_pos : 0 < (1 + ε) := by linarith
  have honeplus_le2 : (1 + ε) ≤ (2 : ℝ) := by linarith
  have hpow3_le8 : (1 + ε) ^ 3 ≤ (8 : ℝ) := by
    have : (1 + ε) ^ 3 ≤ (2 : ℝ) ^ 3 :=
      sorry
      -- pow_le_pow_of_le_left honeplus_nonneg honeplus_le2 3
    norm_num at this
    simpa using this
  have hden_le_x : (1 + ε) ^ 3 ≤ x := le_trans hpow3_le8 hx_ge8
  have hx_nonneg : 0 ≤ x := by
    simpa [hx] using (sqrt_nonneg (n : ℝ))

  -- First show `x ≤ y0`.
  have hxx_eq_n : x * x = (n : ℝ) := by
    simpa [hx] using (mul_self_sqrt (Nat.cast_nonneg n))
  have hx_le_y0 : x ≤ y0 := by
    -- `x ≤ n / (1+ε)^3` iff `x*(1+ε)^3 ≤ n`.
    have hmul : x * (1 + ε) ^ 3 ≤ (n : ℝ) := by
      have : x * (1 + ε) ^ 3 ≤ x * x :=
        mul_le_mul_of_nonneg_left hden_le_x hx_nonneg
      simpa [hxx_eq_n] using this
    -- clear denominators
    have hden_pos : 0 < (1 + ε) ^ 3 := pow_pos honeplus_pos 3
    exact (le_div_iff₀ hden_pos).2 hmul

  -- Hence `δ(y0) ≤ δ(x) = ε`.
  have hδy0_le : gap.δ y0 ≤ ε := by
    -- We can use antitonicity on `(1,∞)`.
    have : gap.δ y0 ≤ gap.δ x :=
      gap_delta_antitone_of_le (a := x) (b := y0) hx_one hx_le_y0
    simpa [hε] using this

  -- Multiply out: `y0*(1+δ y0) ≤ y0*(1+ε)`.
  have hy0_nonneg : 0 ≤ y0 := by
    -- `n ≥ X₀^2` ensures `n > 0`, and the denominator is positive.
    have hnpos : 0 < (n : ℝ) := by
      have hX0pos : 0 < X₀ := by
        unfold X₀
        norm_num
      have hnpos_nat : 0 < n :=
        lt_of_lt_of_le (pow_pos hX0pos 2) hn
      exact_mod_cast hnpos_nat
    have hdenpos : 0 < (1 + ε) ^ 3 := pow_pos honeplus_pos 3
    -- `y0 = n / (1+ε)^3`.
    have : 0 ≤ (n : ℝ) / (1 + ε) ^ 3 := by
      exact div_nonneg hnpos.le (le_of_lt hdenpos)
    simpa [hy0] using this

  have hmul_le : y0 * (1 + gap.δ y0) ≤ y0 * (1 + ε) := by
    -- `1 + δ y0 ≤ 1 + ε` and `y0 ≥ 0`.
    have : (1 + gap.δ y0) ≤ (1 + ε) := by linarith
    exact mul_le_mul_of_nonneg_left this hy0_nonneg

  -- Finally `y0*(1+ε) = n/(1+ε)^2`.
  have halg : y0 * (1 + ε) = (n : ℝ) / (1 + ε) ^ 2 := by
    sorry
    -- -- Expand `y0` and cancel one factor of `1+ε`.
    -- -- `y0*(1+ε) = n/(1+ε)^3 * (1+ε) = n/(1+ε)^2`.
    -- have hne : (1 + ε) ≠ 0 := by linarith
    -- -- Use `field_simp` for clean cancellation.
    -- -- (`field_simp` needs the nonzero of `1+ε`.)
    -- field_simp [hy0, hne, pow_succ, mul_assoc, mul_left_comm, mul_comm]
  -- Put everything together.
  have := le_trans hmul_le (le_of_eq halg)
  simpa [hy0] using this


lemma y1_mul_one_add_delta_le_y2 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2
    y1 * (1 + gap.δ y1) ≤ (n : ℝ) / (1 + ε) := by
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  set y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2 with hy1

  have hX₀_ge8 : (8 : ℝ) ≤ (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [hx] using (sqrt_ge_X₀ (n := n) hn)
  have hx_ge8 : (8 : ℝ) ≤ x := le_trans hX₀_ge8 hxX
  have hx_one : (1 : ℝ) < x := by linarith [hx_ge8]
  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using (gap_delta_nonneg_of_one_lt (x := x) hx_one)
  have honeplus_pos : 0 < (1 + ε) := by linarith
  have honeplus_nonneg : 0 ≤ (1 + ε) := by linarith

  -- First show `x ≤ y1`.
  have hpow_le : (1 + ε) ^ 2 ≤ x := by
    -- As before, a crude bound `(1+ε)^2 ≤ 4 ≤ x`.
    have hx_ge3 : (3 : ℝ) ≤ x := by linarith [hx_ge8]
    have hε_le_one : ε ≤ 1 := by
      simpa [hε] using (gap_delta_le_one_of_three_le (x := x) hx_ge3)
    have honeplus_le2 : (1 + ε) ≤ (2 : ℝ) := by linarith
    have hpow2_le4 : (1 + ε) ^ 2 ≤ (4 : ℝ) := by
      have : (1 + ε) ^ 2 ≤ (2 : ℝ) ^ 2 :=
        sorry
        -- pow_le_pow_of_le_left honeplus_nonneg honeplus_le2 2
      norm_num at this
      simpa using this
    have hx_ge4 : (4 : ℝ) ≤ x := by linarith [hx_ge8]
    exact le_trans hpow2_le4 hx_ge4

  have hx_nonneg : 0 ≤ x := by
    simpa [hx] using (sqrt_nonneg (n : ℝ))
  have hxx_eq_n : x * x = (n : ℝ) := by
    simpa [hx] using (mul_self_sqrt (Nat.cast_nonneg n))

  have hx_le_y1 : x ≤ y1 := by
    -- `x ≤ n/(1+ε)^2` iff `x*(1+ε)^2 ≤ n`.
    have hmul : x * (1 + ε) ^ 2 ≤ (n : ℝ) := by
      have : x * (1 + ε) ^ 2 ≤ x * x :=
        mul_le_mul_of_nonneg_left hpow_le hx_nonneg
      simpa [hxx_eq_n] using this
    have hden_pos : 0 < (1 + ε) ^ 2 := pow_pos honeplus_pos 2
    exact (le_div_iff₀ hden_pos).2 hmul

  -- Hence `δ(y1) ≤ δ(x) = ε`.
  have hδy1_le : gap.δ y1 ≤ ε := by
    have : gap.δ y1 ≤ gap.δ x :=
      gap_delta_antitone_of_le (a := x) (b := y1) hx_one hx_le_y1
    simpa [hε] using this

  -- Multiply out and simplify.
  have hy1_nonneg : 0 ≤ y1 := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hden_pos : 0 < (1 + ε) ^ 2 := pow_pos honeplus_pos 2
    have : 0 ≤ (n : ℝ) / (1 + ε) ^ 2 := div_nonneg hn_nonneg (le_of_lt hden_pos)
    simpa [hy1] using this
  have hmul_le : y1 * (1 + gap.δ y1) ≤ y1 * (1 + ε) := by
    have : (1 + gap.δ y1) ≤ (1 + ε) := by linarith
    exact mul_le_mul_of_nonneg_left this hy1_nonneg
  have halg : y1 * (1 + ε) = (n : ℝ) / (1 + ε) := by
    sorry
    -- have hne : (1 + ε) ≠ 0 := by linarith
    -- field_simp [hy1, hne, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have := le_trans hmul_le (le_of_eq halg)
  simpa [hy1] using this

lemma y2_mul_one_add_delta_lt_n {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y2 : ℝ := (n : ℝ) / (1 + ε)
    y2 * (1 + gap.δ y2) < (n : ℝ) := by
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  set y2 : ℝ := (n : ℝ) / (1 + ε) with hy2

  have hX₀_ge8 : (8 : ℝ) ≤ (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [hx] using (sqrt_ge_X₀ (n := n) hn)
  have hx_ge8 : (8 : ℝ) ≤ x := le_trans hX₀_ge8 hxX
  have hx_one : (1 : ℝ) < x := by linarith [hx_ge8]

  have hx_ge3 : (3 : ℝ) ≤ x := by linarith [hx_ge8]
  have hε_le_one : ε ≤ 1 := by
    simpa [hε] using (gap_delta_le_one_of_three_le (x := x) hx_ge3)
  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using (gap_delta_nonneg_of_one_lt (x := x) hx_one)
  have honeplus_pos : 0 < (1 + ε) := by linarith
  have honeplus_nonneg : 0 ≤ (1 + ε) := by linarith

  -- Show `y2 > x` using the crude bound `1+ε ≤ 2 < x`.
  have honeplus_le2 : (1 + ε) ≤ (2 : ℝ) := by linarith
  have hx_gt2 : (2 : ℝ) < x := by linarith [hx_ge8]
  have honeplus_lt_x : (1 + ε) < x := lt_of_le_of_lt honeplus_le2 hx_gt2

  have hxx_eq_n : x * x = (n : ℝ) := by
    simpa [hx] using (mul_self_sqrt (Nat.cast_nonneg n))

  have hx_lt_y2 : x < y2 := by
    -- `x < n/(1+ε)` iff `x*(1+ε) < n`.
    have hmul : x * (1 + ε) < (n : ℝ) := by
      -- `x*(1+ε) < x*x = n` since `1+ε < x` and `x > 0`.
      have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_ge8
      have : x * (1 + ε) < x * x := by
        exact mul_lt_mul_of_pos_left honeplus_lt_x hx_pos
      simpa [hxx_eq_n] using this
    have hden_pos : 0 < (1 + ε) := honeplus_pos
    exact (lt_div_iff₀ hden_pos).2 hmul

  -- Hence `δ(y2) < δ(x) = ε` by strict antitonicity.
  have hδy2_lt : gap.δ y2 < ε := by
    have : gap.δ y2 < gap.δ x :=
      gap_delta_strict_antitone_of_lt (a := x) (b := y2) hx_one hx_lt_y2
    simpa [hε] using this

  -- Multiply: `y2*(1+δ y2) < y2*(1+ε) = n`.
  have hy2_pos : 0 < y2 := by
    -- `y2 = n/(1+ε)` is positive since `n > 0` and `1+ε > 0`.
    have hnpos : 0 < (n : ℝ) := by
      have hnpos_nat : 0 < n := by
        -- `n ≥ X₀^2` and `X₀^2 > 0`.
        have hX0pos : 0 < X₀ := by
          unfold X₀
          norm_num
        have : 0 < X₀ ^ 2 := pow_pos hX0pos 2
        exact lt_of_lt_of_le this hn
      exact_mod_cast hnpos_nat
    have : 0 < (n : ℝ) / (1 + ε) := div_pos hnpos honeplus_pos
    simpa [hy2] using this
  have hmul_lt : y2 * (1 + gap.δ y2) < y2 * (1 + ε) := by
    have : (1 + gap.δ y2) < (1 + ε) := by linarith
    exact mul_lt_mul_of_pos_left this hy2_pos
  have halg : y2 * (1 + ε) = (n : ℝ) := by
    sorry
    -- have hne : (1 + ε) ≠ 0 := by linarith
    -- field_simp [hy2, hne, mul_assoc, mul_left_comm, mul_comm]

  have hfinal : y2 * (1 + gap.δ y2) < (n : ℝ) := by
    -- Rewrite `y2 * (1+ε)` as `n`.
    simpa [halg] using hmul_lt

  -- Final rewrite back to the original `y2`.
  simpa [hy2] using hfinal

/- End of theorem `exists_q_primes` lemmas-/


/- theorem `prod_q_ge` lemmas -/
noncomputable abbrev b (n : ℕ) : ℝ := 1 + gap.δ (√(n : ℝ))
/--
`b(n)` is the “1 + δ(√n)” base that appears everywhere in q-side bounds.
We do *not* export `b` into theorem statements; it’s just a local convenience for Cert lemmas.
Try moving this entirely into `prod_q_ge` if possible.
-/

/- *** This lemma is likely not used *** -/
lemma b_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < b n := by
  unfold b
  have hx₀ : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hX₀ : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hsqrt : (1 : ℝ) < √(n : ℝ) := lt_of_lt_of_le hX₀ hx₀
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    gap_delta_nonneg_of_one_lt (x := √(n : ℝ)) hsqrt
  linarith


lemma prod_q_rhs_reindex (n : ℕ) :
    (∏ i : Fin 3, (1 + (b n) ^ ((i : ℕ) + 1 : ℝ) / n))
      =
    (∏ i : Fin 3, (1 + (b n) ^ ((3 : ℝ) - (i : ℕ)) / n)) := by
  /-- Reindexing trick for `Fin 3`: convert exponents `i+1` to `3 - i`.
    This is *structural*, but it’s noisy; keeping it in Cert keeps Main clean. -/
  /- *** Proof idea ***:
  exactly your current proof: `rw [Fin.prod_univ_three, Fin.prod_univ_three]` + the `conv` blocks + `ring`,
  just replacing `1 + 1/(log √n)^3` by `b n`.
  copy/paste your existing `Fin.prod_univ_three`/`conv` proof
  with `b n` in place of `(1 + 1/(log √n)^3)`
  -/
  sorry



lemma inv_le_rpow_div_of_lower_bound {n : ℕ} (hn : n ≥ X₀ ^ 2)
    {t : ℝ} {q : ℕ}
    (hq : (n : ℝ) * (b n) ^ (-t) ≤ (q : ℝ)) :
    (1 : ℝ) / (q : ℝ) ≤ (b n) ^ t / n := by
  have hX0pos : 0 < X₀ := by
    unfold X₀
    norm_num
  have hX0sqpos : 0 < X₀ ^ 2 := pow_pos hX0pos 2
  have hnpos_nat : 0 < n := lt_of_lt_of_le hX0sqpos hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos_nat

  have hbpos : 0 < b n := b_pos (n := n) hn
  have hb_nonneg : 0 ≤ b n := le_of_lt hbpos
  have hpowpos : 0 < (b n) ^ (-t) := Real.rpow_pos_of_pos hbpos (-t)
  have hmulpos : 0 < (n : ℝ) * (b n) ^ (-t) := mul_pos hnpos hpowpos

  have hdiv :
      (1 : ℝ) / (q : ℝ) ≤ (1 : ℝ) / ((n : ℝ) * (b n) ^ (-t)) :=
    one_div_le_one_div_of_le hmulpos hq

  -- rewrite RHS
  have : (1 : ℝ) / ((n : ℝ) * (b n) ^ (-t)) = (b n) ^ t / n := by
    calc
      (1 : ℝ) / ((n : ℝ) * (b n) ^ (-t))
          = (1 : ℝ) / ((n : ℝ) * ((b n) ^ t)⁻¹) := by
              simp [Real.rpow_neg hb_nonneg]
      _ = (1 : ℝ) / ((n : ℝ) / (b n) ^ t) := by
              simp [div_eq_mul_inv, mul_assoc]
      _ = (b n) ^ t / (n : ℝ) := by
              simpa [one_div_div]
      _ = (b n) ^ t / n := by simp

  simpa [this] using hdiv


/- End of theorem `prod_q_ge` lemmas-/



/- theorem `prod_p_ge` lemmas -/
lemma one_add_delta_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < (1 + gap.δ (√(n : ℝ))) := by
  have hx₀ : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hX₀ : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hsqrt : (1 : ℝ) < √(n : ℝ) := lt_of_lt_of_le hX₀ hx₀
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    gap_delta_nonneg_of_one_lt (x := √(n : ℝ)) hsqrt
  linarith



lemma p_mul_padd1_le_bound
    {n : ℕ} (hn : n ≥ X₀ ^ 2)
    {p : Fin 3 → ℕ}
    (hp_prime : ∀ i, Nat.Prime (p i))
    (hp_mono : StrictMono p)
    (hp_ub :
      ∀ i, (p i : ℝ) ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (i + 1 : ℝ))
    (hsqrt_lt_p0 : √(n : ℝ) < p 0) :
    ∀ i : Fin 3,
      ((p i * (p i + 1) : ℕ) : ℝ)
        ≤ (1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n) := by
  /-- Key denominator bound for the `p`-product:
      Given `p : Fin 3 → ℕ` satisfying the same hypotheses as `exists_p_primes` exports,
      we bound `p_i(p_i+1)` above by the RHS denominator.
      No `log` appears in the statement; only `gap.δ`. -/
  /- *** Proof sketch (copy/paste from your old `prod_p_ge` inner proof): ***
  From `hsqrt_lt_p0` and `hp_mono`, deduce `√n < p i` for all `i`.
  From `hp_ub i`, square to get `(p i : ℝ)^2 ≤ (n : ℝ) * (1+δ(√n))^(2*i+2)`.
  From `√n < p i`, show `(p i : ℝ) + 1 ≤ (p i : ℝ) * ((n+√n)/n)`
    via your existing `field_simp; linear_combination` trick.
  Multiply and rearrange, then cast `p i * (p i + 1)` into `ℝ`.
  -/
  sorry

/- End of theorem `prod_p_ge` lemmas-/

/- theorem `pq_ratio_ge` lemmas -/

lemma n_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : (0 : ℝ) < (n : ℝ) := by
  /- Cast-positivity of `n` from the assumption `n ≥ X₀²`. -/
  /- **Proof idea:**
  `X₀ ≥ 1` (or just `X₀^2 > 0`) so `n > 0` in `ℕ`, then cast to `ℝ`. -/
  sorry



lemma pq_ratio_rhs_as_fraction {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
      =
    ((4 : ℝ) * ∏ i : Fin 3,
        (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ))
      /
    (∏ i : Fin 3,
        (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ ((3 : ℕ) - (i : ℕ))) := by
    /- RHS rewrite for `pq_ratio_ge`** (this is the key “plumbing lemma”).
      It rewrites the analytic bound
      `4 * (1 + δ(√n))^12 / n^(3/2)`
      into a ratio of two *products* that match the pointwise bounds exported by
      `exists_p_primes` and `exists_q_primes`. -/
    /- **Proof idea:** let `b := 1 + gap.δ(√n)` (note `b>0`).
    Compute explicitly over `Fin 3`:
    - `∏ i, √n * b^((i:ℕ)+1) = n^(3/2) * b^6`
    - `∏ i, (n:ℝ) / b^((3:ℕ)-(i:ℕ)) = n^3 * b^(-6)`
    Then combine to get the ratio equals `b^12 / n^(3/2)` and multiply by `4`. -/
  sorry
/- End of theorem `pq_ratio_ge` lemmas-/


/-
Final criterion structure in Main.lean
-/

/- `hn` lemmas -/
lemma one_le_X₀_sq : (1 : ℕ) ≤ X₀ ^ 2 := by
  /-
  Proof idea:
  - for the current `PrimeGaps.latest`, `X₀` is a concrete positive numeral (89693),
    so this is `decide`/`norm_num`.
  -/
  sorry
/- End of `hn` lemmas-/

/- `h_ord_2` lemmas -/
lemma ord2_mid {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ)
      <
    (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ) := by
  /- (Cert) The key “middle inequality” used in `h_ord_2`: upper bound for `p₂` is below lower bound for `q₀`. -/
  /- *** Proof idea *** :
  - Let b := 1 + δ(√n). From `delta_sqrt_le` get b ≤ 1.000675.
  - Then b^6 ≤ (1.000675)^6 < 2 (checked by `norm_num`).
  - Also from `hn : n ≥ X₀^2` we know √n ≥ X₀, and for the concrete X₀ we have 2 ≤ √n.
  - So b^6 < √n, which is equivalent to √n*b^3 < n/b^3 (algebra, using n = (√n)^2).
  -/
  sorry
/- End of `h_ord_2` lemmas -/

/- `h_crit` lemmas -/
theorem main_ineq_delta_form {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
      ≤
    (∏ i : Fin 3,
        (1 + 1 /
          ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  /-
   *** Proof outline (exactly your write-up) *** :
  1) Use `delta_sqrt_le` to bound `gap.δ(√n) ≤ 0.000675`, hence `1+gap.δ(√n) ≤ 1.000675`.
  2) Use `inv_n_pow_3_div_2_le_X₀` to replace `1/n^(3/2)` by `(1/X₀)*(1/n)`.
  3) Use `inv_n_add_sqrt_ge_X₀` to replace `1/(n+√n)` by `(1/(1+1/X₀))*(1/n)`.
  4) Set `ε := 1/n` and use the hypotheses `0 ≤ ε` and `ε ≤ 1/(X₀^2)` (derived from `hn`).
  5) Apply `prod_epsilon_le`, `prod_epsilon_ge`, and `final_comparison` to finish.
  -/
  sorry


lemma delta_prod_mul_nonneg {n : ℕ} (hn : n ≥ Lcm.X₀ ^ 2) :
    0 ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + Lcm.gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ)
              * ((n : ℝ) + √(n : ℝ)) )))
        * (1 + (3 : ℝ) / (8 * (n : ℝ))) := by
  /- *** Proof idea ***:
  1) `hn` ⇒ `0 < (n:ℝ)`; hence also `0 < (n:ℝ) + √(n:ℝ)`.
  2) `one_add_delta_pos hn` ⇒ `0 < 1 + δ(√n)` ⇒ `0 < (1+δ(√n))^(...)` by `Real.rpow_pos_of_pos`.
  3) Therefore the denominator in each factor is positive, so `1 / denom ≥ 0`,
     hence each factor `1 + ... ≥ 0`, so the product is ≥ 0.
  4) Also `1 + 3/(8*n) ≥ 0`. Multiply nonnegatives.
  -/
  sorry

lemma delta_ratio_term_nonneg {n : ℕ} (hn : n ≥ Lcm.X₀ ^ 2) :
    0 ≤ 1 - 4 * (1 + Lcm.gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  /- *** Proof idea (in Cert) ***:
  - Use `delta_sqrt_le hn : gap.δ(√n) ≤ 0.000675` so `(1+δ)^12 ≤ (1.000675)^12`.
  - Use `inv_n_pow_3_div_2_le_X₀ hn : 1/n^(3/2) ≤ (1/X₀)*(1/n)`.
  - Combine to show `4*(1+δ)^12 / n^(3/2) ≤ 4*(1.000675)^12*(1/X₀)*(1/n)`.
  - Then use `hn` (so `1/n ≤ 1/X₀^2`) and `norm_num` (after `dsimp [X₀]`)
    to show the RHS ≤ 1.
  - Conclude `0 ≤ 1 - (...)` i.e. the subtracted term is ≤ 1.
  -/
  sorry

/- End of `h_crit` lemmas-/

/- Lemmas that are possibly useful in the intermediate bridge -/
lemma delta_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    gap.δ (√(n : ℝ)) ≤ (0.000675 : ℝ) := by
  /-- (Cert) Numerical bound on the prime-gap delta at √n: `δ(√n) ≤ 0.000675` for `n ≥ X₀^2`. -/
  /- *** Proof idea (Dusart provider) *** :
  - unfold `gap := PrimeGaps.latest` and the definition of δ;
  - use monotonicity of `x ↦ 1/(log x)^3` for x ≥ X₀ and the numerical estimate at X₀;
  - convert `hn : n ≥ X₀^2` into `√n ≥ X₀`, then finish by monotonicity + `norm_num`.
  -/
  sorry

lemma inv_n_pow_3_div_2_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (89693 : ℝ)) * (1 / n) := by
  /- (Cert) Bound `1/n^(3/2)` by `(1/89693) * (1/n)` for `n ≥ X₀^2`. -/
  /- *** Proof idea *** :
  - rewrite `n^(3/2) = n*√n`;
  - from `hn` get `√n ≥ 89693`;
  - conclude `1/(n*√n) ≤ (1/n)*(1/89693)`.
  -/
  sorry

lemma inv_n_pow_3_div_2_le_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
  /- *** Proof idea *** :
  - rewrite `n^(3/2) = n*√n`;
  - from `hn` get `√n ≥ 89693`;
  - conclude `1/(n*√n) ≤ (1/n)*(1/89693)`.
  -/
  sorry

lemma inv_n_add_sqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) + √(n : ℝ)) ≥ (1 / (1 + 1 / (89693 : ℝ))) * (1 / n) := by
  /- (Cert) Lower bound for `1/(n+√n)` in terms of `1/n`. -/
  /- *** Proof idea *** :
  - show `n + √n ≤ (1 + 1/89693)*n` using `√n ≤ n/89693` from `√n ≥ 89693`;
  - invert (monotone since positive) to obtain the displayed inequality.
  -/
  sorry

lemma inv_n_add_sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / ((n : ℝ) + √(n : ℝ))) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  /- *** Proof idea *** :
  - from `√n ≥ X₀` deduce `√n ≤ (n:ℝ) / X₀` (since `n = (√n)^2`)
  - so `n + √n ≤ n + n/X₀ = (1+1/X₀)*n`
  - invert both sides (positive) to get the lower bound for `1/(n+√n)`
  -/
  sorry

lemma inv_n_le_inv_X₀_sq {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (X₀ ^ 2 : ℕ) := by
  /- *** Proof idea *** :
  - cast `hn` to reals: `(X₀^2 : ℝ) ≤ (n : ℝ)`
  - use `one_div_le_one_div_of_le` with positivity of `(X₀^2 : ℝ)`
  -/
  sorry


/- End of lemmas that are possibly useful in the intermediate bridge -/



/- Lemmas that are possibly useful in the proof of theorems in Cert.lean -/
lemma sqrt_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < √(n : ℝ) := by
  /- positivity of `x := √n`. -/
  -- can be `lt_of_lt_of_le (show (0:ℝ) < (X₀:ℝ) from ...) (sqrt_ge_X₀ hn)`
  -- or whatever you currently do
  sorry


lemma eps_nonneg {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤ gap.δ (√(n : ℝ)) := by
  /-- nonnegativity of `ε := δ(x)` at `x := √n`. -/
  -- Dusart: follows from `0 < log x` hence `(log x)^3 > 0` hence `1/(...) ≥ 0`.
  -- Other providers: whatever you can prove.
  sorry


lemma crit_rhs_nonneg {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤ 1 - 4 * (1 + (0.000675 : ℝ)) ^ 12 * ((1 / (X₀ : ℝ)) * (1 / (n : ℝ))) := by
  /-
  Proof idea:
  - Use `hn` to replace `n` by `X₀^2` as worst case (since 1/n decreases with n).
  - Then unfold `X₀` (to 89693) *inside this lemma only* and let `norm_num` finish.
  -/
  -- typical proof outline:
  --   have hx : (1/(n:ℝ)) ≤ 1/((X₀^2:ℕ):ℝ) := inv_n_le_inv_X₀_sq hn
  --   bound the expression using monotonicity in (1/n)
  --   simp [X₀] at the end; norm_num
  sorry


/- End of lemmas that are possibly useful in the proof of theorem in Cert.lean -/


/- Lemmas that are `possibly` not useful -/
lemma hx₀_pos : (0 : ℝ) < X₀ := by
    unfold X₀; norm_num
@[simp] lemma X₀_pos : (0 : ℝ) < (X₀ : ℝ) := by
  exact hx₀_pos

lemma hsqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ X₀ := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)

lemma log_X₀_gt : Real.log X₀ > 11.4 := by
  dsimp [X₀]
  rw [gt_iff_lt, show (11.4 : ℝ) = 57 / (5 : ℕ) by norm_num, div_lt_iff₀ (by norm_num),
    mul_comm, ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num

lemma hlog {n : ℕ} (hn : n ≥ X₀ ^ 2) : log √(n : ℝ) ≥ 11.4 := by
  have hpos : (0 : ℝ) < X₀ := by
    -- try without unfolding first
   unfold X₀
   norm_num
  calc log √(n : ℝ) ≥ log (X₀ : ℝ) :=
        log_le_log hpos (hsqrt_ge hn)
    _ ≥ 11.4 := log_X₀_gt.le


lemma hε_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < 1 + 1 / (log √(n : ℝ)) ^ 3 := by
  positivity [hlog hn]

lemma log_X₀_pos : 0 < Real.log X₀ := by linear_combination log_X₀_gt



/- Original Cert lemmas -/

theorem inv_cube_log_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (log √(n : ℝ)) ^ 3 ≤ eps_log := by
    sorry


theorem prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith


theorem prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]
  dsimp [X₀] at *
  nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4]


theorem final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
    dsimp [X₀] at *
    nlinarith

/- End of Original Cert lemmas -/




/-- The certified package (built from the concrete numerals in this file). -/
noncomputable def criterion : Criterion := by
  classical
  refine
    { sqrt_ge_X₀ := ?_
      eps_nonneg := ?_
      inv_cube_log_sqrt_le := ?_
      -- ...
    }
  · intro n hn; sorry
  · intro n hn; sorry
  · intro n hn; sorry

end Numerical

end Lcm
