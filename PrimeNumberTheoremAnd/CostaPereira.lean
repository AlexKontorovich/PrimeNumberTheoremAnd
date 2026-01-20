import PrimeNumberTheoremAnd.SecondaryDefinitions

open Chebyshev Finset Nat Real

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
theorem sublemma_1_1 {x : ℝ} (hx : 0 < x) : ψ x = ∑' (k : ℕ), θ (x ^ (1 / (k : ℝ))) := by
  have theta_zero_large_k : ∀ k, k ∉ Icc 0 ⌊log x / Real.log 2⌋₊ → θ (x ^ (1 / (k : ℝ))) = 0 := by
    intro k hk
    simp only [mem_Icc, zero_le, true_and, not_le] at hk
    apply theta_eq_zero_of_lt_two
    by_cases hk0 : k = 0
    · simp [hk0, CharP.cast_eq_zero, div_zero, rpow_zero, one_lt_ofNat]
    have hk_pos : (k : ℝ) > 0 := cast_pos.mpr <| pos_of_ne_zero hk0
    by_cases hx1 : x < 1
    · linarith [rpow_le_one hx.le hx1.le <| one_div_cast_nonneg k]
    have h1 : log x / Real.log 2 < k := by
      calc log x / Real.log 2 < ⌊log x / Real.log 2⌋₊ + 1 := lt_floor_add_one _
        _ ≤ k := by exact_mod_cast hk
    have : Real.log x < k * Real.log 2 := by linarith [(div_lt_iff₀ <| log_pos <| one_lt_two).mp h1]
    have : Real.log x < Real.log (2 ^ (k : ℕ)) := by rw [Real.log_pow]; exact this
    have : x < 2 ^ (k : ℕ) := (Real.log_lt_log_iff hx (by positivity)).mp this
    calc x ^ (1 / (k : ℝ)) = x ^ ((k : ℝ)⁻¹) := by rw [one_div]
      _ < (2 ^ (k : ℕ)) ^ ((k : ℝ)⁻¹) := rpow_lt_rpow hx.le this <| inv_pos.mpr hk_pos
      _ = 2 ^ ((k : ℕ) * (k : ℝ)⁻¹) := by rw [← rpow_natCast, ← rpow_mul <| zero_le_two]
      _ = 2 ^ (1 : ℝ) := by congr 1; field_simp
      _ = 2 := rpow_one 2
  rw [tsum_eq_sum (s := Icc 0 ⌊log x / Real.log 2⌋₊) theta_zero_large_k]
  by_cases hx1 : x < 1
  · have hpsi : ψ x = 0 := psi_eq_zero_of_lt_two (by linarith)
    refine hpsi ▸ (sum_eq_zero fun k _ ↦ theta_eq_zero_of_lt_two ?_).symm
    have h_exp_le : x ^ (1 / (k : ℝ)) ≤ 1 := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · exact rpow_le_one hx.le hx1.le <| one_div_cast_nonneg k
    linarith
  rw [sum_eq_sum_diff_singleton_add (i := 0) <| insert_eq_self.mp rfl]
  have : θ (x ^ (1 / (0 : ℕ) : ℝ)) = 0 := by
    rw [cast_zero, div_zero, rpow_zero]; exact theta_eq_zero_of_lt_two <| by grind
  simp only [this, add_zero]
  have h_eq : Icc 0 ⌊log x / Real.log 2⌋₊ \ {0} = Icc 1 ⌊log x / Real.log 2⌋₊ := ((fun {_} ↦ val_inj.mp) rfl).symm
  simpa [h_eq, theta, psi] using psi_eq_sum_theta hx.le

@[blueprint
  "costa-pereira-sublemma-1-2"
  (title := "Costa-Pereira Sublemma 1.2")
  (statement := /-- For every $x > 0$ and $n$ we have $\psi(x^{1/n}) = \sum_{k \geqslant 1} \theta(x^{1/nk})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-1} and substitution.-/)
  (latexEnv := "sublemma")
  (discussion := 677)]
theorem sublemma_1_2 {x : ℝ} (hx : 0 < x) (n : ℝ) : ψ (x ^ (1 / n:ℝ)) = ∑' (k : ℕ), θ (x ^ (1 / (n * (k:ℝ)))) := by
  simp_rw [sublemma_1_1 (rpow_pos_of_pos hx _), ← rpow_mul (le_of_lt hx), _root_.div_mul_div_comm, one_mul]

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
    ψ x = θ x + ψ (x ^ (1 / 2:ℝ)) + ∑' k, θ (x ^ (1 / (2 * (k:ℝ) + 1))) := by sorry

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
    ψ x - θ x =
      ψ (x ^ (1 / 2:ℝ)) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) - 3))) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) - 1))) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) + 1))) := by sorry

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
    ψ (x ^ (1 / 3:ℝ)) =
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) - 3))) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ)))) := by sorry

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
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) - 1))) -
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ)))) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) + 1))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-7"
  (title := "Costa-Pereira Sublemma 1.7")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) \leqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/5k}
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-6} and the fact that $\theta$ is an increasing function. -/)
  (latexEnv := "sublemma")
  (discussion := 682)]
theorem sublemma_1_7 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≤ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ∑' k, θ (x ^ (1 / (5 * (k : ℝ)))) := by
  by_contra h_contra
  have : Summable (fun k : ℝ ↦ θ (x ^ (1 / (5 * k)))) := by
    contrapose! h_contra
    rw [tsum_eq_zero_of_not_summable h_contra, sublemma_1_6]
    · rw [tsum_eq_zero_of_not_summable, tsum_eq_zero_of_not_summable,
          tsum_eq_zero_of_not_summable] <;> norm_num
      · contrapose! h_contra
        convert h_contra.comp_injective (show Function.Injective (fun k : ℝ ↦ (5 * k - 1) / 6)
          from fun a b h ↦ by ring_nf at h; linarith) using 2; norm_num; ring_nf
      · contrapose! h_contra
        convert h_contra.comp_injective (show (fun k : ℝ ↦ k * (5 / 6)).Injective from
          fun a b h ↦ by grind) using 2; norm_num; ring_nf
      · contrapose! h_contra
        convert h_contra.comp_injective (show (fun k : ℝ ↦ (5 * k + 1) / 6).Injective from
          fun a b h ↦ by grind) using 2; norm_num; ring_nf
    · exact RCLike.ofReal_pos.mp hx
  replace := (this.tendsto_cofinite_zero).eventually (gt_mem_nhds <| show 0 < θ x from ?_)
  · refine this.not_infinite <| Set.infinite_of_injective_forall_mem (fun a b h ↦ ?_)
        (fun n : ℕ ↦ show (1 / (5 * (n + 1)) : ℝ) ∈ _ from ?_) <;> norm_num at *
    · exact add_right_cancel (congrFun (congrArg HAdd.hAdd h) a)
    · ring_nf
      refine sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, (mem_filter.mp hp).2⟩
        · exact (mem_Ioc.mp (mem_filter.mp hp).1).1
        · exact (mem_Ioc.mp (mem_filter.mp hp).1).2.trans
            (floor_mono <| le_trans (by norm_num) <| rpow_le_rpow_of_exponent_le (le_of_not_gt fun h ↦ by
                rw [floor_eq_zero.mpr <| by grind] at hp; aesop) (by linarith : (1 + n : ℝ) ≥ 1))
      · exact fun _ _ _ ↦ log_nonneg <| one_le_cast.2 <| Prime.pos <| by grind
  · by_cases h₂ : x < 2
    · have hψ2 : ψ (x ^ (1 / 2 : ℝ)) = 0 := psi_eq_zero_of_lt_two <|
        calc x ^ (1 / 2 : ℝ) < 2 ^ (1 / 2 : ℝ) := rpow_lt_rpow hx.le h₂ (by norm_num)
          _ < 2 := by simpa using rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num : (1 : ℝ) / 2 < 1)
      have hψ3 : ψ (x ^ (1 / 3 : ℝ)) = 0 := psi_eq_zero_of_lt_two <|
        calc x ^ (1 / 3 : ℝ) < 2 ^ (1 / 3 : ℝ) := rpow_lt_rpow hx.le h₂ (by norm_num: (0 : ℝ) < 1 / 3)
          _ < 2 := by simpa using rpow_lt_rpow_of_exponent_lt (by grind) (by norm_num : (1 : ℝ) / 3 < 1)
      simp only [psi_eq_zero_of_lt_two h₂, hψ2, hψ3, theta_eq_zero_of_lt_two h₂, add_zero, sub_zero, zero_add] at h_contra
      exact (h_contra (tsum_nonneg fun k : ℝ ↦ theta_nonneg _)).elim
    · exact sum_pos (fun p hp ↦ log_pos <| one_lt_cast.2 <| Prime.one_lt <| by aesop)
        ⟨2, mem_filter.2 ⟨mem_Icc.2 ⟨by norm_num, le_floor <| by grind⟩, prime_two⟩⟩

@[blueprint
  "costa-pereira-sublemma-1-8"
  (title := "Costa-Pereira Sublemma 1.8")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) \geqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/7k}
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-6} and the fact that $\theta$ is an increasing function. -/)
  (latexEnv := "sublemma")
  (discussion := 683)]
theorem sublemma_1_8 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≥
      ψ (x ^ (1 / 2:ℝ)) +
      ψ (x ^ (1 / 3:ℝ)) +
      ∑' (k : ℕ), θ (x ^ (1 / (7 * (k:ℝ)))) := by sorry

@[blueprint
  "costa-pereira-theorem-1a"
  (title := "Costa-Pereira Theorem 1a")
  (statement := /-- For every $x > 0$ we have
  $\psi(x) - \theta(x) \leqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-7} and Sublemma \ref{costa-pereira-sublemma-1-2}. -/)
  (latexEnv := "theorem")
  (discussion := 684)]
theorem theorem_1a {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≤ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ψ (x ^ (1 / 5 : ℝ)) := by
  rw [show ψ (x ^ (1 / 5 : ℝ)) = ∑' k : ℕ, θ (x ^ (1 / (5 * (k : ℝ)))) from by
    simp only [sublemma_1_1 <| rpow_pos_of_pos hx .., ← rpow_mul hx.le]; congr! 2; field_simp]
  exact sublemma_1_7 hx

@[blueprint
  "costa-pereira-theorem-1b"
  (title := "Costa-Pereira Theorem 1b")
  (statement := /-- For every $x > 0$ we have
  $\psi(x) - \theta(x) \geqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/7})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-8} and Sublemma \ref{costa-pereira-sublemma-1-2}. -/)
  (latexEnv := "theorem")
  (discussion := 685)]
theorem theorem_1b {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≥ ψ (x ^ (1 / 2:ℝ)) + ψ (x ^ (1 / 3:ℝ)) + ψ (x ^ (1 / 7:ℝ)) := by
  rw [show ψ (x ^ (1 / 7 : ℝ)) = ∑' k : ℕ, θ (x ^ (1 / (7 * (k : ℝ)))) from by
    simp only [sublemma_1_1 <| rpow_pos_of_pos hx .., ← rpow_mul hx.le]; congr! 2; field_simp]
  exact sublemma_1_8 hx

end CostaPereira
