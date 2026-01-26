import PrimeNumberTheoremAnd.PrimeGaps.Provider
import PrimeNumberTheoremAnd.Dusart
import PrimeNumberTheoremAnd.SecondarySummary
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic



namespace PrimeGaps
namespace RS

abbrev X₀ : ℕ := 10726905042
@[simp] lemma X₀_eq : X₀ = 10726905042 := rfl


/-- The constant from your theorem. -/
noncomputable def c : ℝ := (1 : ℝ) / 28314000
@[simp] lemma c_def : c = (1 : ℝ) / 28314000 := rfl

/-- `c/(1-c)` simplified: equals `1/28313999`. -/
noncomputable def α : ℝ := (1 : ℝ) / 28313999
@[simp] lemma α_def : α = (1 : ℝ) / 28313999 := rfl

/-- A strictly decreasing, nonnegative `δ` on `[X₀,∞)` that is always ≥ `c/(1-c)`. -/
noncomputable def δ (x : ℝ) : ℝ := α + x⁻¹
@[simp] lemma δ_def (x : ℝ) : δ x = α + x⁻¹ := rfl









theorem primeGap_backward :
  ∀ {x : ℝ}, (10726905041 : ℝ) < x →
    ∃ p : ℕ, Nat.Prime p ∧
      x * (1 - (1 : ℝ) / 28314000) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  intro x hx
  rcases RamareSaouter2003.has_prime_in_interval x hx with ⟨p, hp, hxp, hple⟩
  refine ⟨p, hp, ?_, ?_⟩
  · -- `HasPrimeInInterval` gives the lower-endpoint bound.
    simpa [one_div] using hxp
  · -- `HasPrimeInInterval` gives the additive upper-endpoint bound.
    have hple' : (p : ℝ) ≤ x * (1 - (28314000 : ℝ)⁻¹) + x / 28314000 := by
      simpa [one_div] using hple

    have hx_endpoint : x * (1 - (28314000 : ℝ)⁻¹) + x / 28314000 = x := by
      ring_nf

    simpa [hx_endpoint] using hple'



/- TO-DO: Some of the lemmas, especially the theorem comparison ones
    can probably be made more elegant by using `Real.rpow` lemmas
    instead of unfolding the definition each time.  -/
lemma h_X₀ : X₀ > 1 := by norm_num [X₀]

lemma δ_nonneg {x : ℝ} (hx : (X₀ : ℝ) ≤ x) : 0 ≤ δ x := by
  have hX0_pos : (0 : ℝ) < (X₀ : ℝ) := by
    norm_num [X₀]
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hX0_pos hx
  have hα_nonneg : (0 : ℝ) ≤ α := by
    norm_num [α]
  have hxinv_nonneg : (0 : ℝ) ≤ x⁻¹ :=
    inv_nonneg.mpr (le_of_lt hxpos)
  simpa [δ] using add_nonneg hα_nonneg hxinv_nonneg

lemma δ_strictly_decreasing {x y : ℝ}
  (hx : (X₀ : ℝ) ≤ x) (_hy : (X₀ : ℝ) ≤ y) (hxy : x < y) :
    δ y < δ x := by
  have hX0_pos : (0 : ℝ) < (X₀ : ℝ) := by
    norm_num [X₀]
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hX0_pos hx
  have hinv' : (1 : ℝ) / y < (1 : ℝ) / x :=
    one_div_lt_one_div_of_lt hxpos hxy
  have hinv : y⁻¹ < x⁻¹ := by
    simpa [one_div] using hinv'
  have : y⁻¹ + α < x⁻¹ + α := add_lt_add_left hinv α
  simpa [δ, add_comm, add_left_comm, add_assoc] using this



lemma delta_sixth_power_lt_sqrt {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 + δ (√(n : ℝ))) ^ (6 : ℕ) < Real.sqrt (n : ℝ) := by
  /-∀ n : ℕ, n ≥ X₀ ^ 2 →
    (1 + gap.δ (√(n : ℝ))) ^ 6 < √(n : ℝ)-/
  -- First turn `hn : n ≥ X₀^2` into `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    -- `√(X₀^2) = X₀` since `X₀ ≥ 0`.
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  -- Positivity of `n` (hence `√n > 0`).
  have hn_pos_nat : 0 < n := by
    have hX0_pos : 0 < X₀ := by
      norm_num [X₀]
    have hX0sq_pos : 0 < X₀ ^ 2 := by
      exact pow_pos hX0_pos 2
    exact lt_of_lt_of_le hX0sq_pos hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hsqrt_pos : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn_pos

  -- Bound `δ(√n) < 1`, hence `1 + δ(√n) < 2`.
  have hX0_pos : (0 : ℝ) < (X₀ : ℝ) := by
    norm_num [X₀]
  have hsqrt_inv_le : (√(n : ℝ))⁻¹ ≤ (X₀ : ℝ)⁻¹ := by
    have : (1 : ℝ) / √(n : ℝ) ≤ (1 : ℝ) / (X₀ : ℝ) :=
      one_div_le_one_div_of_le hX0_pos hX0_le_sqrt
    simpa [one_div] using this
  have hδ_le : δ (√(n : ℝ)) ≤ α + (X₀ : ℝ)⁻¹ := by
    simpa [δ] using (add_le_add_left hsqrt_inv_le α)
  have hδ_lt1 : δ (√(n : ℝ)) < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num [α, X₀])
  have hδ_nonneg : 0 ≤ δ (√(n : ℝ)) := by
    exact δ_nonneg hX0_le_sqrt
  have h1δ_lt2 : (1 + δ (√(n : ℝ))) < (2 : ℝ) := by
    linarith
  have h1δ_nonneg : 0 ≤ (1 + δ (√(n : ℝ))) := by
    linarith

  -- Thus `(1+δ(√n))^6 < 2^6 = 64`.
  have hpow_lt : (1 + δ (√(n : ℝ))) ^ (6 : ℕ) < (2 : ℝ) ^ (6 : ℕ) := by
    exact pow_lt_pow_left₀ h1δ_lt2 h1δ_nonneg (n := 6) (by decide)
  have h2pow : (2 : ℝ) ^ (6 : ℕ) = (64 : ℝ) := by
    norm_num
  have hL : (1 + δ (√(n : ℝ))) ^ (6 : ℕ) < (64 : ℝ) := by
    simpa [h2pow] using hpow_lt

  -- And `64 < X₀ ≤ √n` since `X₀ = 89693`.
  have h64_lt_X0 : (64 : ℝ) < (X₀ : ℝ) := by
    norm_num [X₀]
  have h64_lt_sqrt : (64 : ℝ) < Real.sqrt (n : ℝ) :=
    lt_of_lt_of_le h64_lt_X0 hX0_le_sqrt

  exact lt_trans hL h64_lt_sqrt



lemma delta_twelfth_power_le_n_pow_3_div_2 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
     4 * (1 + δ (√(n : ℝ))) ^ 12 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
  -- First turn `hn : n ≥ X₀^2` into `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  -- Positivity facts.
  have hn_pos_nat : 0 < n := by
    have hX0_pos : 0 < X₀ := by
      norm_num [X₀]
    have hX0sq_pos : 0 < X₀ ^ 2 := by
      exact pow_pos hX0_pos _
    exact lt_of_lt_of_le hX0sq_pos hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := hn_pos.le
  have hsqrt_pos : 0 < √(n : ℝ) := by
    simpa [Real.sqrt_eq_rpow] using (Real.rpow_pos_of_pos hn_pos (1 / 2 : ℝ))

  -- Bound `δ(√n) < 1` using the explicit formula `δ x = α + x⁻¹`.
  have hX0_pos : (0 : ℝ) < (X₀ : ℝ) := by
    norm_num [X₀]
  have hsqrt_inv_le : (√(n : ℝ))⁻¹ ≤ (X₀ : ℝ)⁻¹ := by
    have : (1 : ℝ) / √(n : ℝ) ≤ (1 : ℝ) / (X₀ : ℝ) :=
      one_div_le_one_div_of_le hX0_pos hX0_le_sqrt
    simpa [one_div] using this
  have hδ_le : δ (√(n : ℝ)) ≤ α + (X₀ : ℝ)⁻¹ := by
    simpa [δ] using (add_le_add_left hsqrt_inv_le α)
  have hδ_lt1 : δ (√(n : ℝ)) < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num [α, X₀])
  have hδ_nonneg : 0 ≤ δ (√(n : ℝ)) := by
    exact δ_nonneg hX0_le_sqrt
  have hδ_le1 : δ (√(n : ℝ)) ≤ 1 := le_of_lt hδ_lt1

  -- Hence `1 + δ(√n) ≤ 2`, so the LHS is bounded by `4 * 2^12`.
  have h1δ_nonneg : 0 ≤ (1 + δ (√(n : ℝ))) := by
    linarith
  have h1δ_le2 : (1 + δ (√(n : ℝ))) ≤ (2 : ℝ) := by
    linarith
  have hpow_le : (1 + δ (√(n : ℝ))) ^ 12 ≤ (2 : ℝ) ^ 12 := by
    exact pow_le_pow_left₀ h1δ_nonneg h1δ_le2 (n := 12)
  have hlhs_le : 4 * (1 + δ (√(n : ℝ))) ^ 12 ≤ 4 * (2 : ℝ) ^ 12 := by
    exact mul_le_mul_of_nonneg_left hpow_le (by norm_num)

  -- Show `4 * 2^12 ≤ (n:ℝ)^(3/2)` by `4*2^12 = 16384 ≤ n ≤ n^(3/2)`.
  have h16384_le_X0sq : (16384 : ℕ) ≤ X₀ ^ 2 := by
    norm_num [X₀]
  have h16384_le_n_nat : (16384 : ℕ) ≤ n :=
    le_trans h16384_le_X0sq hn
  have h16384_le_n : (16384 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast h16384_le_n_nat

  have hsqrt_ge1 : (1 : ℝ) ≤ √(n : ℝ) := by
    have hn1_nat : (1 : ℕ) ≤ n := Nat.succ_le_iff.mp hn_pos_nat
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn1_nat
    have : √(1 : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hn1
    simpa using this

  have hn_le_rpow : (n : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    -- Rewrite `n^(3/2)` as `n * √n`.
    have hsplit : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * (√(n : ℝ)) := by
      have h : (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) := by ring
      calc
        (n : ℝ) ^ (3 / 2 : ℝ)
          = (n : ℝ) ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by simp [h]
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
          simp [Real.rpow_add hn_pos]
        _ = (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by simp [Real.rpow_one]
        _ = (n : ℝ) * (√(n : ℝ)) := by
            -- `√x = x^(1/2)`.
            simp [Real.sqrt_eq_rpow]
    -- Now use `1 ≤ √n`.
    rw [hsplit]
    have : (n : ℝ) * (1 : ℝ) ≤ (n : ℝ) * √(n : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt_ge1 hn_nonneg
    simpa [mul_one] using this

  have hconst : (4 : ℝ) * (2 : ℝ) ^ 12 = (16384 : ℝ) := by
    norm_num

  have hconst_le_rpow : 4 * (2 : ℝ) ^ 12 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    -- chain: 4*2^12 = 16384 ≤ n ≤ n^(3/2)
    have : (4 : ℝ) * (2 : ℝ) ^ 12 ≤ (n : ℝ) := by
      simpa [hconst] using h16384_le_n
    exact le_trans this hn_le_rpow

  exact le_trans hlhs_le hconst_le_rpow


/- Lemmas to prove the final criterion theorem main_ineq_delta_form -/


noncomputable abbrev eps_log : ℝ := (0.000675 : ℝ)
noncomputable abbrev onePlusEps_log : ℝ := (1 : ℝ) + eps_log


/- `main_ineq_delta_form_lhs` `main_ineq_delta_form_rhs` sub-lemmas -/
lemma eps_log_bound {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    δ (√(n : ℝ)) ≤ (0.000675 : ℝ) := by
  -- First turn `hn : n ≥ X₀^2` into `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  have hX0_pos : (0 : ℝ) < (X₀ : ℝ) := by
    norm_num [X₀]

  have hsqrt_inv_le : (√(n : ℝ))⁻¹ ≤ (X₀ : ℝ)⁻¹ := by
    have : (1 : ℝ) / √(n : ℝ) ≤ (1 : ℝ) / (X₀ : ℝ) :=
      one_div_le_one_div_of_le hX0_pos hX0_le_sqrt
    simpa [one_div] using this

  have hδ_le : δ (√(n : ℝ)) ≤ α + (X₀ : ℝ)⁻¹ := by
    simpa [δ] using (add_le_add_left hsqrt_inv_le α)

  have hαX0_le : α + (X₀ : ℝ)⁻¹ ≤ (0.000675 : ℝ) := by
    norm_num [α, X₀]

  exact le_trans hδ_le hαX0_le

lemma inv_n_pow_3_div_2_le_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
  -- First turn `hn : n ≥ X₀^2` into `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  have hn_pos_nat : 0 < n := by
    have hX0_pos : 0 < X₀ := by
      norm_num [X₀]
    have hX0sq_pos : 0 < X₀ ^ 2 := by
      exact pow_pos hX0_pos _
    exact lt_of_lt_of_le hX0sq_pos hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := hn_pos.le
  have hX0_pos : 0 < (X₀ : ℝ) := by
    norm_num [X₀]
  have hsqrt_pos : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn_pos

  -- Rewrite the exponent `3/2` as `1 + 1/2`.
  have hsplit : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * √(n : ℝ) := by
    have h : (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) := by ring
    calc
      (n : ℝ) ^ (3 / 2 : ℝ)
          = (n : ℝ) ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by simp [h]
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
          simp [Real.rpow_add hn_pos]
      _ = (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by simp [Real.rpow_one]
      _ = (n : ℝ) * √(n : ℝ) := by
          simp [Real.sqrt_eq_rpow]

  -- Compare denominators: `n*X₀ ≤ n*√n`.
  have hdenom_le : (n : ℝ) * (X₀ : ℝ) ≤ (n : ℝ) * √(n : ℝ) := by
    exact mul_le_mul_of_nonneg_left hX0_le_sqrt hn_nonneg

  -- Now invert the inequality.
  have h_inv : (1 : ℝ) / ((n : ℝ) * √(n : ℝ)) ≤ (1 : ℝ) / ((n : ℝ) * (X₀ : ℝ)) := by
    have hdenom_pos : 0 < (n : ℝ) * (X₀ : ℝ) := mul_pos hn_pos hX0_pos
    simpa [one_div] using (one_div_le_one_div_of_le hdenom_pos hdenom_le)

  -- Put everything in the desired form.
  -- Left side: `1 / n^(3/2) = 1 / (n*√n)`.
  -- Right side: `(1/X₀) * (1/n) = 1 / (n*X₀)`.
  simpa [hsplit, one_div_mul_one_div, mul_comm, mul_left_comm, mul_assoc] using h_inv

lemma inv_n_add_sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / ((n : ℝ) + √(n : ℝ))) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  -- Turn `hn : X₀^2 ≤ n` into `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  have hn_pos_nat : 0 < n := by
    have hX0_pos : 0 < X₀ := by
      norm_num [X₀]
    have hX0sq_pos : 0 < X₀ ^ 2 := by
      exact pow_pos hX0_pos _
    exact lt_of_lt_of_le hX0sq_pos hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := hn_pos.le
  have hX0_pos : 0 < (X₀ : ℝ) := by
    norm_num [X₀]

  -- From `X₀ ≤ √n` we get `√n ≤ n / X₀`.
  have hsqrt_le_div : √(n : ℝ) ≤ (n : ℝ) / (X₀ : ℝ) := by
    -- Use `a ≤ b` ⇒ `a*c ≤ b*c` with `c = √n ≥ 0`.
    have hsqrt_nonneg : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have hmul : (X₀ : ℝ) * √(n : ℝ) ≤ √(n : ℝ) * √(n : ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_right hX0_le_sqrt hsqrt_nonneg)
    have hmul' : (X₀ : ℝ) * √(n : ℝ) ≤ (n : ℝ) := by
      -- `√n * √n = n`.
      simpa [mul_comm, mul_left_comm, mul_assoc, Real.sq_sqrt hn_nonneg, sq] using hmul
    -- Divide by `X₀ > 0`.
    refine (le_div_iff₀ hX0_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'

  -- Denominator comparison: `n + √n ≤ (1 + 1/X₀) * n`.
  have hdenom_le : (n : ℝ) + √(n : ℝ) ≤ (1 + 1 / (X₀ : ℝ)) * (n : ℝ) := by
    have : (n : ℝ) + √(n : ℝ) ≤ (n : ℝ) + (n : ℝ) / (X₀ : ℝ) := by
      gcongr
    -- Simplify the right-hand side.
    simpa [div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using this

  -- Invert the inequality (since all denominators are positive).
  have hpos : 0 < (n : ℝ) + √(n : ℝ) := by
    have hsqrt_nonneg : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    exact add_pos_of_pos_of_nonneg hn_pos hsqrt_nonneg
  have hinv : (1 : ℝ) / ((1 + 1 / (X₀ : ℝ)) * (n : ℝ)) ≤ (1 : ℝ) / ((n : ℝ) + √(n : ℝ)) := by
    simpa [one_div] using (one_div_le_one_div_of_le hpos hdenom_le)

  -- Rewrite the RHS in the desired product form.
  -- Goal is `1/(n+√n) ≥ (1/(1+1/X₀))*(1/n)`.
  -- So we show the product is ≤ `1/(n+√n)`.
  have : (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) ≤ 1 / ((n : ℝ) + √(n : ℝ)) := by
    simpa [one_div_mul_one_div, mul_comm, mul_left_comm, mul_assoc] using hinv
  exact this

/- End of `main_ineq_delta_form_lhs` `main_ineq_delta_form_rhs` sub-lemmas -/

lemma main_ineq_delta_form_lhs {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
      ≤ (∏ i : Fin 3,
        (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ))) := by
  /- *** Proof idea ***
  We use lemma `eps_log_bound` to bound `δ(√n)` by `0.000675`, hence
  `1 + δ(√n) ≤ 1 + 0.000675 = onePlusEps_log`.
  Then we compare the three factors term-by-term and multiply.
  -/
  classical

  -- First turn `hn : n ≥ X₀^2` into `X₀ ≤ √n` (needed for `δ_nonneg`).
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  have hn_pos_nat : 0 < n := by
    have hX0_pos : 0 < X₀ := by
      norm_num [X₀]
    have hX0sq_pos : 0 < X₀ ^ 2 := by
      exact pow_pos hX0_pos _
    exact lt_of_lt_of_le hX0sq_pos hn
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.zero_le n)
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat

  have hδ_le_eps : δ (√(n : ℝ)) ≤ eps_log := by
    simpa [eps_log] using (eps_log_bound (n := n) hn)
  have hδ_nonneg : 0 ≤ δ (√(n : ℝ)) := by
    exact δ_nonneg hX0_le_sqrt

  have hbase_le : (1 + δ (√(n : ℝ))) ≤ onePlusEps_log := by
    -- `1 + δ(√n) ≤ 1 + eps_log`.
    linarith [hδ_le_eps]
  have hbase_nonneg : 0 ≤ (1 + δ (√(n : ℝ))) := by
    linarith
  have heps_nonneg : 0 ≤ onePlusEps_log := by
    -- `onePlusEps_log = 1 + eps_log`.
    norm_num [onePlusEps_log, eps_log]

  -- Pointwise comparison of the factors.
  refine Finset.prod_le_prod (fun _ _ => by positivity) ?_
  intro i _
  -- Compare the rpow terms.
  have hexp_nonneg : 0 ≤ ((i : ℕ) + 1 : ℝ) := by
    exact_mod_cast (Nat.zero_le ((i : ℕ) + 1))
  have hrpow_le : (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ)
      ≤ onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) := by
    exact Real.rpow_le_rpow hbase_nonneg hbase_le hexp_nonneg
  have hdiv_le : (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)
      ≤ onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ) := by
    exact div_le_div_of_nonneg_right hrpow_le hn_nonneg
  -- Add 1 on both sides.
  linarith


-- Packaging the (very large) LHS/RHS expressions as `def`s avoids a deterministic
-- heartbeat timeout during `whnf` on the lemma statement.
noncomputable def main_ineq_delta_form_rhs_LHS (n : ℕ) : ℝ :=
    (∏ i : Fin 3,
        (1 + 1 /
          ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (1 + δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ))

noncomputable def main_ineq_delta_form_rhs_RHS (n : ℕ) : ℝ :=
    (∏ i : Fin 3,
        (1 + 1 /
          ((onePlusEps_log) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (onePlusEps_log) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ)))

lemma main_ineq_delta_form_rhs {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    main_ineq_delta_form_rhs_LHS n ≥ main_ineq_delta_form_rhs_RHS n := by
  -- Unfold the packaged definitions (lightweight: avoids `dsimp` reducing inside the terms).
  unfold main_ineq_delta_form_rhs_LHS main_ineq_delta_form_rhs_RHS
  /- *** Proof idea ***
  Compare term-by-term in the product using positivity of all terms.
  For the product part, we bound `(1+δ(√n))` by `onePlusEps_log` and
  `1/(n+√n)` by `1/(1+1/X₀) * 1/n`.
  For the last factor, we combine `delta_twelfth_power_le_n_pow_3_div_2`,
  `inv_n_pow_3_div_2_le_X₀`, and the bound on `δ(√n)`.
  -/
  classical

  -- Basic facts about `n`.
  have hn_pos_nat : 0 < n := by
    have hX0_pos : 0 < X₀ := by
      norm_num [X₀]
    have hX0sq_pos : 0 < X₀ ^ 2 := by
      exact pow_pos hX0_pos _
    exact lt_of_lt_of_le hX0sq_pos hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := hn_pos.le

  -- Turn `hn : X₀^2 ≤ n` into `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  have hδ_nonneg : 0 ≤ δ (√(n : ℝ)) := by
    exact δ_nonneg hX0_le_sqrt
  have hδ_le_eps : δ (√(n : ℝ)) ≤ eps_log := by
    simpa [eps_log] using (eps_log_bound (n := n) hn)
  have hbase_le : (1 + δ (√(n : ℝ))) ≤ onePlusEps_log := by
    linarith [hδ_le_eps]
  have hbase_nonneg : 0 ≤ (1 + δ (√(n : ℝ))) := by
    linarith
  have hbase_pos : 0 < (1 + δ (√(n : ℝ))) := by
    linarith

  have heps_nonneg : 0 ≤ onePlusEps_log := by
    norm_num [onePlusEps_log, eps_log]
  have heps_pos : 0 < onePlusEps_log := by
    norm_num [onePlusEps_log, eps_log]

  -- Product comparison: RHS product ≤ LHS product.
  have hprod :
      (∏ i : Fin 3,
          (1 + 1 /
            ((onePlusEps_log) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ))))) := by
    -- Compare factors pointwise, then multiply.
    refine Finset.prod_le_prod (fun _ _ => by positivity) ?_
    intro i _
    -- It suffices to compare the reciprocals.
    suffices
        (1 : ℝ) / ((onePlusEps_log) ^ (2 * (i : ℕ) + 2 : ℝ)) * (1 / (1 + 1 / (X₀ : ℝ))) *
            (1 / (n : ℝ))
          ≤ (1 : ℝ) /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ))) by
      -- Add 1 on both sides.
      have h := add_le_add_left this 1
      simpa [add_comm, add_left_comm, add_assoc] using h

    -- First, compare the `rpow` denominators.
    let k : ℝ := (2 * (i : ℕ) + 2 : ℝ)
    have hk_nonneg : 0 ≤ k := by
      dsimp [k]
      exact_mod_cast (Nat.zero_le (2 * (i : ℕ) + 2))
    have hrpow_le : (1 + δ (√(n : ℝ))) ^ k ≤ onePlusEps_log ^ k := by
      exact Real.rpow_le_rpow hbase_nonneg hbase_le hk_nonneg
    have hinv_rpow : (1 : ℝ) / (onePlusEps_log ^ k) ≤ (1 : ℝ) / ((1 + δ (√(n : ℝ))) ^ k) := by
      -- `a ≤ b` with `0 < a` gives `1/b ≤ 1/a`.
      have hpos : 0 < (1 + δ (√(n : ℝ))) ^ k :=
        Real.rpow_pos_of_pos hbase_pos _
      simpa [one_div] using (one_div_le_one_div_of_le hpos hrpow_le)

    -- Second, compare `1/(n+√n)` using the previously proved lemma.
    have hinv_sum : (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) ≤ (1 : ℝ) / ((n : ℝ) + √(n : ℝ)) := by
      -- `a ≥ b` is `b ≤ a`.
      simpa [mul_assoc, mul_left_comm, mul_comm] using (inv_n_add_sqrt_ge_X₀ (n := n) hn)

    -- Multiply the two bounds.
    have hmul :
        ((1 : ℝ) / (onePlusEps_log ^ k)) * ((1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)))
          ≤ ((1 : ℝ) / ((1 + δ (√(n : ℝ))) ^ k)) * ((1 : ℝ) / ((n : ℝ) + √(n : ℝ))) := by
      refine mul_le_mul hinv_rpow hinv_sum (by positivity) (by positivity)

    -- Rewrite into the target form.
    -- RHS: `(1/a) * (1/b) = 1/(a*b)`.
    -- LHS: reassociate products.
    simpa [k, mul_assoc, mul_left_comm, mul_comm, one_div_mul_one_div] using hmul

  -- Last factor comparison.
  -- Define the two "bad" terms we subtract.
  set a : ℝ := 4 * (1 + δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
  set b : ℝ := 4 * (onePlusEps_log) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ))

  have ha_le_hb : a ≤ b := by
    -- Use `inv_n_pow_3_div_2_le_X₀` and the monotonicity of `pow`.
    have hpow12 : (1 + δ (√(n : ℝ))) ^ 12 ≤ (onePlusEps_log) ^ 12 := by
      have h1δ_nonneg : 0 ≤ (1 + δ (√(n : ℝ))) := by linarith
      exact pow_le_pow_left₀ h1δ_nonneg hbase_le (n := 12)
    have hinv : (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
      simpa using (inv_n_pow_3_div_2_le_X₀ (n := n) hn)
    -- Combine: `(1+δ)^12 * 1/n^(3/2) ≤ (onePlusEps)^12 * (1/X₀) * (1/n)`.
    have hmul :
        ((1 + δ (√(n : ℝ))) ^ 12) * (1 / (n : ℝ) ^ (3 / 2 : ℝ))
          ≤ ((onePlusEps_log) ^ 12) * ((1 / (X₀ : ℝ)) * (1 / n)) := by
      refine mul_le_mul hpow12 hinv (by positivity) (by positivity)
    -- Multiply by 4 and rewrite divisions.
    have hmul4 :
        4 * (((1 + δ (√(n : ℝ))) ^ 12) * (1 / (n : ℝ) ^ (3 / 2 : ℝ)))
          ≤ 4 * (((onePlusEps_log) ^ 12) * ((1 / (X₀ : ℝ)) * (1 / n))) := by
      exact mul_le_mul_of_nonneg_left hmul (by norm_num)
    -- Match `a` and `b`.
    -- Note: `a = 4*(1+δ)^12 * (1/n^(3/2))` and `b = 4*(onePlusEps)^12*(1/X₀)*(1/n)`.
    simpa [a, b, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul4

  have hC'le : (1 - b) ≤ (1 - a) := by
    -- `a ≤ b` implies `1 - b ≤ 1 - a`.
    exact sub_le_sub_left ha_le_hb 1

  -- We will need `0 ≤ 1 - b`.
  have hb_le_one : b ≤ 1 := by
    -- Crude bound: `onePlusEps_log ≤ 2`, so `(onePlusEps_log)^12 ≤ 2^12`.
    have heps_le2 : onePlusEps_log ≤ (2 : ℝ) := by
      norm_num [onePlusEps_log, eps_log]
    have hpow_le : (onePlusEps_log) ^ 12 ≤ (2 : ℝ) ^ 12 :=
      pow_le_pow_left₀ heps_nonneg heps_le2 (n := 12)
    -- Also `1/n ≤ 1/X₀^2`.
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hX0sq_pos : 0 < (X₀ ^ 2 : ℝ) := by
      have hX0_pos_nat : 0 < X₀ := by norm_num [X₀]
      have : 0 < (X₀ ^ 2 : ℕ) := pow_pos hX0_pos_nat _
      exact_mod_cast this
    have hinv_n : (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (X₀ ^ 2 : ℝ) := by
      -- From `X₀^2 ≤ n`.
      simpa [one_div] using (one_div_le_one_div_of_le hX0sq_pos hn')
    -- Put everything together via monotonicity.
    have hb_le' : b ≤ 4 * (2 : ℝ) ^ 12 * (1 / (X₀ : ℝ)) * ((1 : ℝ) / (n : ℝ)) := by
      -- only using `hpow_le`.
      have : 4 * (onePlusEps_log) ^ 12 ≤ 4 * (2 : ℝ) ^ 12 :=
        mul_le_mul_of_nonneg_left hpow_le (by norm_num)
      -- multiply by the remaining nonnegative factor
      have hnn : 0 ≤ (1 / (X₀ : ℝ)) * ((1 : ℝ) / (n : ℝ)) := by positivity
      have : (4 * (onePlusEps_log) ^ 12) * ((1 / (X₀ : ℝ)) * ((1 : ℝ) / (n : ℝ)))
          ≤ (4 * (2 : ℝ) ^ 12) * ((1 / (X₀ : ℝ)) * ((1 : ℝ) / (n : ℝ))) :=
        mul_le_mul_of_nonneg_right this hnn
      -- rearrange to match `b`
      simpa [b, mul_assoc, mul_left_comm, mul_comm] using this
    have hb_le'' : 4 * (2 : ℝ) ^ 12 * (1 / (X₀ : ℝ)) * ((1 : ℝ) / (n : ℝ))
        ≤ 4 * (2 : ℝ) ^ 12 * (1 / (X₀ : ℝ)) * ((1 : ℝ) / (X₀ ^ 2 : ℝ)) := by
      have hnn : 0 ≤ 4 * (2 : ℝ) ^ 12 * (1 / (X₀ : ℝ)) := by positivity
      exact mul_le_mul_of_nonneg_left hinv_n hnn
    have hb_le''' : 4 * (2 : ℝ) ^ 12 * (1 / (X₀ : ℝ)) * ((1 : ℝ) / (X₀ ^ 2 : ℝ)) ≤ 1 := by
      -- Numerical check: `4*2^12 = 16384` and `X₀` is huge.
      dsimp [X₀] at *
      norm_num
    exact le_trans (le_trans hb_le' hb_le'') hb_le'''

  have hC'_nonneg : 0 ≤ (1 - b) := by
    exact sub_nonneg.2 hb_le_one

  -- Now combine everything.
  -- Rewrite the goal as a ≤ b for easier multiplication.
  have hB_nonneg : 0 ≤ (1 + (3 : ℝ) / (8 * (n : ℝ))) := by positivity
  have hA_nonneg : 0 ≤
      (∏ i : Fin 3,
        (1 + 1 /
          ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ))))) := by
    positivity

  -- First multiply the product comparison by the common middle and right factors.
  have h1 :
      (∏ i : Fin 3,
          (1 + 1 /
            ((onePlusEps_log) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
        * ((1 + (3 : ℝ) / (8 * (n : ℝ))) * (1 - b))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * ((1 + (3 : ℝ) / (8 * (n : ℝ))) * (1 - b)) := by
    have hBC'_nonneg : 0 ≤ (1 + (3 : ℝ) / (8 * (n : ℝ))) * (1 - b) := by
      exact mul_nonneg hB_nonneg hC'_nonneg
    exact mul_le_mul_of_nonneg_right hprod hBC'_nonneg

  -- Then compare the rightmost factor `1 - b ≤ 1 - a`.
  have h2 : (1 + (3 : ℝ) / (8 * (n : ℝ))) * (1 - b)
        ≤ (1 + (3 : ℝ) / (8 * (n : ℝ))) * (1 - a) :=
    mul_le_mul_of_nonneg_left hC'le hB_nonneg

  have h3 :
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * ((1 + (3 : ℝ) / (8 * (n : ℝ))) * (1 - b))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * ((1 + (3 : ℝ) / (8 * (n : ℝ))) * (1 - a)) :=
    mul_le_mul_of_nonneg_left h2 hA_nonneg

  have hfinal := le_trans h1 h3

  -- Unfold `a` and `b` and reassociate.
  -- Also rewrite `≥` as `≤`.
  -- The original statement has the form `LHS ≥ RHS`.
  -- We have proved `RHS ≤ LHS`.
  refine (ge_iff_le).2 ?_
  simpa [a, b, mul_assoc] using hfinal


lemma prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith


lemma prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]
  dsimp [X₀] at *
  nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4]

lemma final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
    dsimp [X₀] at *
    nlinarith

theorem main_ineq_delta_form {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
          (1 + (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1 + δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  /- *** Proof idea ***
    We bound the LHS from above (main_ineq_delta_form_lhs)
    and the RHS from below (main_ineq_delta_form_rhs),
    then reduce to comparing polynomials in ε = 1/n,
    which is done via prod_epsilon_le, prod_epsilon_ge, and final_comparison.
  -/

  classical

  -- Work with ε = 1/n.
  set ε : ℝ := (1 : ℝ) / (n : ℝ) with hεdef

  have hn_pos_nat : 0 < n := by
    have hX0_pos : 0 < X₀ := by
      norm_num [X₀]
    have hX0sq_pos : 0 < X₀ ^ 2 := by
      exact pow_pos hX0_pos _
    exact lt_of_lt_of_le hX0sq_pos hn

  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat

  have hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ) := by
    have hε_nonneg : 0 ≤ ε := by
      -- `ε = 1/n` with `n > 0`.
      have : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
      simp [hεdef]

    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hX0sq_pos : 0 < (X₀ ^ 2 : ℝ) := by
      have hX0_pos : 0 < X₀ := by
        norm_num [X₀]
      have : 0 < (X₀ ^ 2 : ℕ) := by
        exact pow_pos hX0_pos _
      exact_mod_cast this

    have hε_le : ε ≤ 1 / (X₀ ^ 2 : ℝ) := by
      -- From `X₀^2 ≤ n`, invert to get `1/n ≤ 1/X₀^2`.
      have : (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (X₀ ^ 2 : ℝ) := by
        simpa using (one_div_le_one_div_of_le hX0sq_pos hn')
      simpa [hεdef] using this
    exact ⟨hε_nonneg, hε_le⟩

  -- Upper bound the LHS by replacing `δ(√n)` with `eps_log`.
  have hL0 := main_ineq_delta_form_lhs (n := n) hn
  have hL :
      (∏ i : Fin 3,
          (1 + (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε)) := by
    simpa [hεdef, div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using hL0

  -- Lower bound the RHS via the packaged comparison lemma.
  have hR0 : main_ineq_delta_form_rhs_RHS n ≤ main_ineq_delta_form_rhs_LHS n := by
    simpa [ge_iff_le] using (main_ineq_delta_form_rhs (n := n) hn)

  have hpoly_ge :
      (1 + 3.36683 * ε - 0.01 * ε ^ 2)
        ≤
      main_ineq_delta_form_rhs_RHS n := by
    have h := prod_epsilon_ge (ε := ε) hε
    -- Normalize the exponent forms used in the product.
    have hmul2 : ∀ i : Fin 3, ((i : ℕ) + 1 : ℝ) * 2 = (i : ℕ) * 2 + 2 := by
      intro i
      ring
    -- Convert `≥` to `≤` and rewrite into `main_ineq_delta_form_rhs_RHS`.
    have h' : (1 + 3.36683 * ε - 0.01 * ε ^ 2) ≤
        (∏ i : Fin 3,
            (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1 / X₀))))
          * (1 + (3 : ℝ) / 8 * ε)
          * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) := by
      simpa [ge_iff_le] using h
    -- Match the expression with `main_ineq_delta_form_rhs_RHS n`.
    simpa [main_ineq_delta_form_rhs_RHS, hεdef, div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm, hmul2]
      using h'

  -- Now chain everything.
  calc
    (∏ i : Fin 3,
        (1 + (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤ (∏ i : Fin 3, (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε)) := hL
    _ ≤ 1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 :=
        prod_epsilon_le (ε := ε) hε
    _ ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 :=
        final_comparison (ε := ε) hε
    _ ≤ main_ineq_delta_form_rhs_RHS n := hpoly_ge
    _ ≤ main_ineq_delta_form_rhs_LHS n := hR0
    _ = (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1 + δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        simp [main_ineq_delta_form_rhs_LHS, mul_assoc]


theorem delta_ineq {n : ℕ} (hn : X₀ ^ 2 ≤ n) :
    (∏ i : Fin 3,
          (1 + (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1 + δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  have hn' : n ≥ X₀ ^ 2 := by
    simpa [ge_iff_le] using hn
  simpa using (main_ineq_delta_form (n := n) hn')



lemma one_add_α_mul_one_sub_c : (1 + α) * (1 - c) = (1 : ℝ) := by
  -- This is a pure rational identity: (1 + 1/28313999) * (1 - 1/28314000) = 1
  -- `norm_num` can do it.
  norm_num [α, c]

lemma c_lt_one : c < (1 : ℝ) := by
  norm_num [c]

lemma one_sub_c_pos : (0 : ℝ) < (1 - c) := by
  exact sub_pos.mpr c_lt_one

lemma α_nonneg : (0 : ℝ) ≤ α := by
  have : (0 : ℝ) < α := by
    -- α = 1/28313999 > 0
    norm_num [α]
  exact le_of_lt this

/-- `prime_in_Icc` derived from the backward theorem by the `y = x*(1+δ x)` trick. -/
theorem prime_in_Icc_of_primeGap_backward
    (primeGap_backward :
      ∀ {x : ℝ}, (10726905041 : ℝ) < x →
        ∃ p : ℕ, Nat.Prime p ∧
          x * (1 - (1 : ℝ) / 28314000) < (p : ℝ) ∧ (p : ℝ) ≤ x) :
    ∀ {x : ℝ}, (X₀ : ℝ) ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * (1 + δ x) := by
  intro x hx
  set y : ℝ := x * (1 + δ x) with hy

  have hxpos : (0 : ℝ) < x := by
    -- since x ≥ X₀ and X₀>0
    have : (0 : ℝ) < (X₀ : ℝ) := by
      -- X₀ is a huge numeral
      norm_num [X₀]
    exact lt_of_lt_of_le this hx

  have hδ_nonneg : (0 : ℝ) ≤ δ x := by
    -- δ x = α + x⁻¹, both nonneg since x>0
    have hxinv_nonneg : (0 : ℝ) ≤ x⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt hxpos)
    exact add_nonneg α_nonneg hxinv_nonneg

  have h1_le : (1 : ℝ) ≤ (1 + δ x) := by linarith [hδ_nonneg]

  have hx_le_y : x ≤ y := by
    -- x = x*1 ≤ x*(1+δ x) = y
    have : x * (1 : ℝ) ≤ x * (1 + δ x) :=
      mul_le_mul_of_nonneg_left h1_le (le_of_lt hxpos)
    simpa [y, mul_one] using this

  have hB_lt_x : (10726905041 : ℝ) < x := by
    -- since x ≥ 10726905042
    have : (10726905041 : ℝ) < (X₀ : ℝ) := by
      norm_num [X₀]
    exact lt_of_lt_of_le this hx

  have hB_lt_y : (10726905041 : ℝ) < y := lt_of_lt_of_le hB_lt_x hx_le_y

  -- Apply backward theorem at y
  obtain ⟨p, hpPrime, hp_low, hp_high⟩ := primeGap_backward (x := y) hB_lt_y

  refine ⟨p, hpPrime, ?_, ?_⟩
  · -- prove x < p
    -- show x < y*(1-c)
    have hxinv_pos : (0 : ℝ) < x⁻¹ := inv_pos.mpr hxpos
    have h1_lt_mul : (1 : ℝ) < (1 + δ x) * (1 - c) := by
      -- Expand and use (1+α)*(1-c)=1 plus a positive bump from x⁻¹*(1-c)
      have hpos : (0 : ℝ) < x⁻¹ * (1 - c) := mul_pos hxinv_pos one_sub_c_pos
      have : (1 : ℝ) < (1 : ℝ) + x⁻¹ * (1 - c) := by
        simpa using (lt_add_of_pos_right (1 : ℝ) hpos)
      have hone_eq : (1 : ℝ) = (1 + α) * (1 - c) := by
        simpa using (one_add_α_mul_one_sub_c).symm
      -- rewrite RHS to (1+δ x)*(1-c)
      -- (1+δ x) = (1+α)+x⁻¹
      calc
        (1 : ℝ) < (1 : ℝ) + x⁻¹ * (1 - c) := this
        _ = (1 + α) * (1 - c) + x⁻¹ * (1 - c) := by
          simpa using congrArg (fun t : ℝ => t + x⁻¹ * (1 - c)) hone_eq
        _ = ((1 + α) + x⁻¹) * (1 - c) := by
              -- reverse of `add_mul`
              symm
              simp [add_mul]
        _ = (1 + δ x) * (1 - c) := by
              simp [δ, add_left_comm, add_comm]
    have hx_lt_y_mul : x < y * (1 - c) := by
      -- multiply `1 < (1+δ x)*(1-c)` by x>0 and rewrite
      have : x * (1 : ℝ) < x * ((1 + δ x) * (1 - c)) :=
        mul_lt_mul_of_pos_left h1_lt_mul hxpos
      -- rewrite x*((1+δ x)*(1-c)) = (x*(1+δ x))*(1-c) = y*(1-c)
      simpa [y, mul_one, mul_assoc, mul_left_comm, mul_comm] using this
    -- now chain: x < y*(1-c) < p
    -- note `hp_low` is `y * (1 - 1/28314000) < p`; and `c = 1/28314000`
    have hp_low' : y * (1 - c) < (p : ℝ) := by
      simpa [c] using hp_low
    exact lt_trans hx_lt_y_mul hp_low'
  · -- prove p ≤ x*(1+δ x)
    simpa [y] using hp_high


theorem prime_in_Icc {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * (1 + δ x) := by
  exact prime_in_Icc_of_primeGap_backward (primeGap_backward := primeGap_backward) (x := x) hx




noncomputable def provider : PrimeGaps.Provider :=
{ X₀ := X₀
  δ := δ
  h_X₀ := by exact h_X₀
  δ_nonneg := by
    intro x hx
    exact δ_nonneg hx
  δ_strictly_decreasing := by
    intro x y hx hy hxy
    exact δ_strictly_decreasing hx hy hxy
  delta_sixth_power_lt_sqrt := by
    intro n hn
    exact delta_sixth_power_lt_sqrt hn
  delta_twelfth_power_le_n_pow_3_div_2 := by
    intro n hn
    exact delta_twelfth_power_le_n_pow_3_div_2 hn
  delta_ineq := by
    intro n hn
    exact main_ineq_delta_form hn
  prime_in_Icc := by
    intro x hx
    exact prime_in_Icc (x := x) hx }

end RS
end PrimeGaps
