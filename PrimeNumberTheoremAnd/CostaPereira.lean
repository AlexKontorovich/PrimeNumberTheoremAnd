import PrimeNumberTheoremAnd.SecondaryDefinitions

open Chebyshev Finset Nat Real Filter

blueprint_comment /--
\section{An inequality of Costa-Pereira}

We record here an inequality relating the Chebyshev functions $\psi(x)$ and $\theta(x)$ due to
Costa Pereira \cite{costa-pereira}, namely
$$ \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/7}) \leq \psi(x) - \theta(x) \leq \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) . $$
-/

namespace CostaPereira

@[blueprint
  "costa-pereira-sublemma-1-1"
  (title := "Costa-Pereira Sublemma 1.1")
  (statement := /-- For every $x > 0$ we have $\psi(x) = \sum_{k \geqslant 1} \theta(x^{1/k})$. -/)
  (proof := /-- This follows directly from the definitions of $\psi$ and $\theta$. -/)
  (latexEnv := "sublemma")
  (discussion := 676)]
theorem sublemma_1_1 {x : ℝ} (hx : 0 < x) : ψ x = ∑' (k : ℕ), θ (x ^ (1 / ((k.succ : ℕ) : ℝ))) := by
  have theta_zero_large_k : ∀ k : ℕ, ⌊log x / Real.log 2⌋₊ ≤ k →
      θ (x ^ (1 / ((k.succ : ℕ) : ℝ))) = 0 := by
    refine fun k hk ↦ theta_eq_zero_of_lt_two ?_
    by_cases hx1 : x < 1
    · linarith [rpow_le_one hx.le hx1.le <| one_div_cast_nonneg k.succ]
    have : log x / Real.log 2 < k.succ := by
      calc log x / Real.log 2 < ⌊log x / Real.log 2⌋₊ + 1 := lt_floor_add_one _
        _ ≤ k + 1 := by exact_mod_cast Nat.add_le_add_right hk 1
        _ = (k.succ : ℝ) := by simp [succ_eq_add_one]
    have : Real.log x < k.succ * Real.log 2 := by
      linarith [(div_lt_iff₀ <| log_pos <| one_lt_two).mp this]
    have : Real.log x < Real.log (2 ^ (k.succ : ℕ)) := by rw [Real.log_pow]; exact this
    have : x < 2 ^ (k.succ : ℕ) := (log_lt_log_iff hx (by positivity)).mp this
    calc x ^ (1 / ((k.succ : ℕ) : ℝ)) = x ^ (((k.succ : ℕ) : ℝ)⁻¹) := by rw [one_div]
      _ < (2 ^ (k.succ : ℕ)) ^ (((k.succ : ℕ) : ℝ)⁻¹) := rpow_lt_rpow hx.le this <| inv_pos.mpr <| cast_pos.mpr k.succ_pos
      _ = 2 := by rw [← rpow_natCast, ← rpow_mul zero_le_two, mul_inv_cancel₀, rpow_one]; positivity
  rw [tsum_eq_sum (s := Iio ⌊log x / Real.log 2⌋₊) (fun k hk ↦ theta_zero_large_k k (not_lt.mp (mem_Iio.not.mp hk)))]
  by_cases hx1 : x < 1
  · have : ψ x = 0 := psi_eq_zero_of_lt_two <| by linarith
    refine this ▸ (sum_eq_zero fun k _ ↦ theta_eq_zero_of_lt_two ?_).symm
    linarith [rpow_le_one hx.le hx1.le <| one_div_cast_nonneg k.succ]
  have h_eq : ∑ k ∈ Iio ⌊log x / Real.log 2⌋₊, θ (x ^ (1 / (↑k.succ : ℝ))) =
      ∑ k ∈ Icc 1 ⌊log x / Real.log 2⌋₊, θ (x ^ (1 / (↑k : ℝ))) := by
    refine sum_bij' (fun k _ ↦ k.succ) (fun k _ ↦ k.pred)
        (fun k hk ↦ mem_Icc.mpr ⟨k.succ_pos, mem_Iio.mp hk⟩)
        (fun k hk ↦ by have ⟨hk1, hk2⟩ := mem_Icc.mp hk; exact mem_Iio.mpr (pred_lt_pred
          (one_le_iff_ne_zero.mp hk1) (lt_succ_of_le hk2))) (fun k _ ↦ Nat.pred_succ k)
            (fun k hk ↦ succ_pred_eq_of_pos (mem_Icc.mp hk).1) (fun _ _ ↦ rfl)
  rw [h_eq]
  simpa using psi_eq_sum_theta hx.le

@[blueprint
  "costa-pereira-sublemma-1-2"
  (title := "Costa-Pereira Sublemma 1.2")
  (statement := /-- For every $x > 0$ and $n$ we have $\psi(x^{1/n}) = \sum_{k \geqslant 1} \theta(x^{1/nk})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-1} and substitution.-/)
  (latexEnv := "sublemma")
  (discussion := 677)]
theorem sublemma_1_2 {x : ℝ} (hx : 0 < x) (n : ℝ) :
    ψ (x ^ (1 / n : ℝ)) = ∑' (k : ℕ), θ (x ^ (1 / (n * ((k.succ : ℕ) : ℝ)))) := by
  simp_rw [sublemma_1_1 (rpow_pos_of_pos hx _), ← rpow_mul (le_of_lt hx), _root_.div_mul_div_comm,
    one_mul]

@[blueprint
  "costa-pereira-sublemma-1-3"
  (title := "Costa-Pereira Sublemma 1.3")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) = \theta(x) + \psi(x^{1/2}) + \sum_{k \geqslant 1} \theta(x^{1/(2k+1)}).
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-1} and Sublemma \ref{costa-pereira-sublemma-1-2}. -/)
  (latexEnv := "sublemma")
  (discussion := 678)]
theorem sublemma_1_3 {x : ℝ} (hx : 0 < x) :
    ψ x = θ x + ψ (x ^ (1 / 2 : ℝ)) + ∑' (k : ℕ), θ (x ^ (1 / (2 * (k.succ : ℝ) + 1))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-4"
  (title := "Costa-Pereira Sublemma 1.4")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) = \psi(x^{1/2}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-3)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-1)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k+1)}).
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-3} and rearranging the sum. -/)
  (latexEnv := "sublemma")
  (discussion := 679)]
theorem sublemma_1_4 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x = ψ (x ^ (1 / 2 : ℝ)) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ) - 3))) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ) - 1))) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ) + 1))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-5"
  (title := "Costa-Pereira Sublemma 1.5")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x^{1/3}) = \sum_{k \geqslant 1} \theta(x^{1/(6k-3)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k)}).
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-2} and substitution. -/)
  (latexEnv := "sublemma")
  (discussion := 680)]
theorem sublemma_1_5 {x : ℝ} (hx : 0 < x) :
    ψ (x ^ (1 / 3 : ℝ)) = ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ) - 3))) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ)))) := by
  rw [sublemma_1_2 hx (3 : ℝ)]
  have eventually_theta_eq_zero {x : ℝ} (hx : 0 < x) :
      ∀ᶠ k : ℕ in atTop, θ (x ^ (1 / (3 * (2 * k : ℝ)))) = 0 := by
    have h_lim : Tendsto (fun k : ℕ ↦ x ^ (1 / (6 * k) : ℝ)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.rpow
        (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_id.nsmul_atTop (by norm_num)))
        (by grind)
    filter_upwards [h_lim.eventually (gt_mem_nhds one_lt_two)] with k hk
      using theta_eq_zero_of_lt_two <| by ring_nf at *; linarith
  have theta_one_equals_zero : θ 1 = 0 := by norm_num [theta, sum_filter, sum_range_succ]
  have summable_of_eventually_zero {f : ℕ → ℝ} (hf : ∀ᶠ n in atTop, f n = 0) : Summable f := by
    rw [eventually_atTop] at hf
    obtain ⟨N, hN⟩ := hf
    exact summable_nat_add_iff N |>.1 <| by exact ⟨_, hasSum_single 0 <| by grind⟩
  have summable_even {x : ℝ} {hx : 0 < x} : Summable (fun k : ℕ ↦ θ (x ^ (1 / (3 * (2 * k : ℝ))))) := by
    convert summable_of_eventually_zero (eventually_theta_eq_zero hx) using 1
  have summable_test_odd {x : ℝ} (hx : 0 < x) : Summable (fun k : ℕ ↦ θ (x ^ (1 / (3 * (↑(2 * k + 1) : ℝ))))) := by
    apply summable_of_eventually_zero
    have : Tendsto (fun k : ℕ ↦ (2 * (k : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop zero_lt_two)
    have : Tendsto (fun k : ℕ ↦ (3 * (2 * (k : ℝ) + 1))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp <| this.const_mul_atTop (by positivity)
    have : Tendsto (fun k : ℕ ↦ x ^ (1 / (3 * (↑(2 * k + 1) : ℝ)))) atTop (nhds 1) := by
      simp only [one_div]
      rw [show (fun k : ℕ ↦ x ^ (3 * (↑(2 * k + 1) : ℝ))⁻¹) =
        (fun k : ℕ ↦ x ^ (3 * (2 * (k : ℝ) + 1))⁻¹) from funext fun k ↦ by congr 1; push_cast; ring]
      convert tendsto_const_nhds.rpow this (Or.inl hx.ne') using 1
      simp [rpow_zero]
    filter_upwards [this.eventually (gt_mem_nhds one_lt_two)] with k hk
    exact theta_eq_zero_of_lt_two hk
  have : Summable (fun n : ℕ ↦ θ (x ^ (1 / (3 * n) : ℝ))) := by
    apply summable_of_eventually_zero
    have h_lim : Tendsto (fun n : ℕ ↦ x ^ (1 / (3 * n) : ℝ)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.rpow (tendsto_inv_atTop_nhds_zero_nat.comp
        (tendsto_id.nsmul_atTop (by positivity))) (by grind)
    filter_upwards [h_lim.eventually (gt_mem_nhds one_lt_two)] with n hn
    exact theta_eq_zero_of_lt_two hn
  have step1 : ∑' k : ℕ, θ (x ^ (1 / (3 * k.succ) : ℝ)) = ∑' n : ℕ, θ (x ^ (1 / (3 * n) : ℝ)) := by
    rw [Summable.tsum_eq_zero_add this, cast_zero, mul_zero, div_zero, rpow_zero, theta_one_equals_zero, zero_add]
  rw [step1]
  set f : ℕ → ℝ := fun n ↦ θ (x ^ ((1 : ℝ) / (3 * n))) with hf
  have : Summable (f ∘ (2 * ·)) := by
    convert summable_even (x := x) (hx := hx) using 2 with k
    simp only [hf, Function.comp_apply]; congr 2; push_cast; ring
  have split := tsum_even_add_odd this <| hf ▸ summable_test_odd hx
  simp only [hf, cast_mul, cast_ofNat, cast_add, cast_one] at split
  rw [← split, add_comm]
  congr 1
  · exact tsum_congr fun k ↦ by congr 2; push_cast; ring
  · rw [Summable.tsum_eq_zero_add (summable_even (x := x) (hx := hx))]
    simp only [mul_zero, cast_zero, div_zero, rpow_zero, theta_one_equals_zero, zero_add]
    exact tsum_congr fun k ↦ by congr 2; push_cast; ring

@[blueprint
  "costa-pereira-sublemma-1-6"
  (title := "Costa-Pereira Sublemma 1.6")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) = \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-1)}) - \sum_{k \geqslant 1} \theta(x^{1/(6k)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k+1)}).
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-4} and Sublemma \ref{costa-pereira-sublemma-1-5}. -/)
  (latexEnv := "sublemma")
  (discussion := 681)]
theorem sublemma_1_6 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x =
      ψ (x ^ (1 / 2:ℝ)) +
      ψ (x ^ (1 / 3:ℝ)) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ  : ℕ) : ℝ) - 1))) -
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ  : ℕ) : ℝ)))) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ  : ℕ) : ℝ) + 1))) := by
  rw [sublemma_1_4 hx, sublemma_1_5 hx]; ring

@[blueprint
  "costa-pereira-sublemma-1-7"
  (title := "Costa-Pereira Sublemma 1.7")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) \leqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/5k}
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-6} and the fact that $\theta$
  is an increasing function. -/)
  (latexEnv := "sublemma")
  (discussion := 682)]
theorem sublemma_1_7 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≤ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ∑' (k : ℕ), θ (x ^ (1 / (5 * ((k.succ  : ℕ) : ℝ)))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-8"
  (title := "Costa-Pereira Sublemma 1.8")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) \geqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/7k}
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-6} and the fact that $\theta$
  is an increasing function. -/)
  (latexEnv := "sublemma")
  (discussion := 683)]
theorem sublemma_1_8 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≥ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ∑' (k : ℕ), θ (x ^ (1 / (7 * ((k.succ : ℕ) : ℝ)))) := by sorry

@[blueprint
  "costa-pereira-theorem-1a"
  (title := "Costa-Pereira Theorem 1a")
  (statement := /-- For every $x > 0$ we have
  $\psi(x) - \theta(x) \leqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-7} and
  Sublemma \ref{costa-pereira-sublemma-1-2}. -/)
  (latexEnv := "theorem")
  (discussion := 684)]
theorem theorem_1a {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≤ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ψ (x ^ (1 / 5 : ℝ)) :=
  sublemma_1_2 hx 5 ▸ sublemma_1_7 hx

@[blueprint
  "costa-pereira-theorem-1b"
  (title := "Costa-Pereira Theorem 1b")
  (statement := /-- For every $x > 0$ we have
  $\psi(x) - \theta(x) \geqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/7})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-8} and
  Sublemma \ref{costa-pereira-sublemma-1-2}. -/)
  (latexEnv := "theorem")
  (discussion := 685)]
theorem theorem_1b {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≥ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ψ (x ^ (1 / 7 : ℝ)) :=
  sublemma_1_2 hx 7 ▸ sublemma_1_8 hx

end CostaPereira
