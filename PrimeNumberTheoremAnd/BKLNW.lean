import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Tactic.NormNum.Prime
import PrimeNumberTheoremAnd.FioriKadiriSwidinsky
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.CostaPereira
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime
import PrimeNumberTheoremAnd.BKLNW_app
import PrimeNumberTheoremAnd.BKLNW_tables
import PrimeNumberTheoremAnd.Buthe

blueprint_comment /--
\section{Tools from BKLNW}
In this file we record the results from \cite{BKLNW}, excluding Appendix A which is treated elsewhere.  These results convert an initial estimate on $E_\psi(x)$ (provided by Appendix A) to estimates on $E_\theta(x)$.  One first obtains estimates on $E_\theta(x)$ that do not decay in $x$, and then obtain further estimates that decay like $1/\log^k x$ for some $k=1,\dots 5$.
-/

open Chebyshev Finset Real

namespace BKLNW

blueprint_comment /--
\subsection{Bounding Etheta uniformly}

We first focus on getting bounds on $E_\theta(x)$ that do not decay in $x$.  A key input, provided by Appendix A, is a bound on $E_\psi(x)$ of the form
$$ E_\psi(x) \leq \varepsilon(b) \quad \text{for } x \geq e^b.$$
We also assume a numerical verification $\theta(x) < x$ for $x \leq x_1$ for some $x_1 \geq e^7$.
-/

structure Pre_inputs where
  ε : ℝ → ℝ
  hε : ∀ b ≥ 0, ∀ x ≥ exp b, |ψ x - x| ≤ ε b * x
  x₁ : ℝ
  hx₁ : x₁ ≥ exp 7
  hx₁' : ∀ x ∈ Set.Ioc 0 x₁, θ x < x

lemma Pre_inputs.epsilon_nonneg (I : Pre_inputs) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ I.ε b := by
  have := I.hε b hb (exp b) (by grind)
  grw [←abs_nonneg] at this
  apply nonneg_of_mul_nonneg_left this (by positivity)

@[blueprint
  "from-buthe-eq-1-7"
  (title := "A consequence of Buthe equation (1.7)")
  (statement := /-- $\theta(x) < x$ for all $1 \leq x \leq 10^{19}$. -/)
  (latexEnv := "sublemma")
  (proof := /-- This follows from Theorem \ref{buthe-theorem-2c}. -/)
  (discussion := 787)]
theorem buthe_eq_1_7 : ∀ x ∈ Set.Ioc 0 1e19, θ x < x := by
  intro x hx
  have hx':= (Set.mem_Ioc).1 hx
  have hlb := hx'.left
  have hub:= hx'.right
  have hub' : x ≤ 10^19 := by linarith
  by_cases h : x < 1
  · have hworse: x < 2 := by linarith
    have htheta: theta x = 0 := by apply Chebyshev.theta_eq_zero_of_lt_two hworse
    linarith
  · have hnewlb : x≥ 1 := by simpa using h
    have hineq : x - θ x ≥ 5e-2 * √x := by exact Buthe.theorem_2c hnewlb hub'
    have hsqrtpos: 0 < sqrt x := by exact Real.sqrt_pos.mpr hlb
    linarith

@[blueprint
  "bklnw-pre-inputs"
  (title := "Default pre-input parameters")
  (statement := /-- We take $\varepsilon$ as in Table 8 of \cite{BKLNW}, and $x_1 = 10^{19}$. -/)]
noncomputable def Pre_inputs.default : Pre_inputs := {
  ε := BKLNW_app.table_8_ε
  hε := BKLNW_app.theorem_2
  x₁ := 1e19
  hx₁ := by grw [← exp_one_rpow, rpow_ofNat, exp_one_lt_three]; norm_num
  hx₁' := buthe_eq_1_7
}

@[blueprint
  "bklnw-lemma-11a"
  (title := "BKLNW Lemma 11a")
  (statement := /-- With the hypotheses as above, we have $\theta(x) \leq (1+\eps(\log x_1)) x)$ for all $x > 0$.-/)
  (proof := /-- Follows immediately from the given hypothesis $\theta(x) \leq \psi(x)$, splitting into the cases $x ≥ x_1$ and $x < x_1$. -/)
  (latexEnv := "lemma")
  (discussion := 788)]
theorem lemma_11a (I : Pre_inputs) {x : ℝ} (hx : x > 0) : θ x ≤ (1 + I.ε (log I.x₁)) * x := by
  have hx₁_pos : 1 ≤ I.x₁ := (one_le_exp (7).ofNat_nonneg).trans I.hx₁
  by_cases h : x ≤ I.x₁
  · grw [I.hx₁' x ⟨hx, h⟩, ← I.epsilon_nonneg (Real.log_nonneg hx₁_pos), add_zero, one_mul]
  · grw [add_mul, theta_le_psi, ← I.hε _ (Real.log_nonneg hx₁_pos)] <;> grind [exp_log]

@[blueprint
  "bklnw-lemma-11b"
  (title := "BKLNW Lemma 11b")
  (statement := /-- With the hypotheses as above, we have
  $$ (1 - \eps(b) - c_0(e^{-b/2} + e^{-2b/3} + e^{-4b/5})) x \leq \theta(x)$$
   for all $x \geq e^b$ and $b>0$, where $c_0 = 1.03883$ is the constant from \cite[Theorem 12]{rs-prime}. -/)
  (proof := /-- From Theorem \ref{costa-pereira-theorem-1a} we have $\psi(x) - \theta(x) ≤ \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5})$.  Now apply the hypothesis on $\psi(x)$ and  Theorem \ref{rs-psi-upper}. -/)
  (latexEnv := "lemma")
  (discussion := 789)]
theorem lemma_11b (I : Pre_inputs) {b x : ℝ} (hb : 0 < b) (hx : x ≥ exp b) :
    (1 - I.ε b - RS_prime.c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5))) * x ≤ θ x := by
  have hx_pos : 0 < x := lt_of_lt_of_le (exp_pos b) hx
  have hlog_x : b ≤ log x := (log_exp b).symm ▸ log_le_log (exp_pos b) hx
  have hψ_half : ψ (x ^ (1 / 2 : ℝ)) < RS_prime.c₀ * x ^ (1 / 2 : ℝ) :=
    RS_prime.theorem_12 <| rpow_pos_of_pos (lt_of_lt_of_le (exp_pos b) hx) _
  have hψ_third : ψ (x ^ (1 / 3 : ℝ)) < RS_prime.c₀ * x ^ (1 / 3 : ℝ) :=
    RS_prime.theorem_12 <| rpow_pos_of_pos hx_pos _
  have hψ_fifth : ψ (x ^ (1 / 5 : ℝ)) < RS_prime.c₀ * x ^ (1 / 5 : ℝ) :=
    RS_prime.theorem_12 <| rpow_pos_of_pos hx_pos _
  have hψ_lower : (1 - I.ε b) * x ≤ ψ x := by grind [I.hε b hb.le x hx]
  have hψ_upper : ψ x ≤ θ x + ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ψ (x ^ (1 / 5 : ℝ)) := by
    grind [CostaPereira.theorem_1a hx_pos]
  have h_half : x ^ (1 / 2 : ℝ) ≤ x * exp (-b / 2) := by
    rw [← log_le_log_iff (rpow_pos_of_pos hx_pos _) (mul_pos hx_pos (exp_pos _)),
        log_rpow hx_pos, log_mul hx_pos.ne' (exp_pos _).ne', log_exp]
    grind
  have h_third : x ^ (1 / 3 : ℝ) ≤ x * exp (-2 * b / 3) := by
    rw [← log_le_log_iff (rpow_pos_of_pos hx_pos _) (mul_pos hx_pos (exp_pos _)),
        log_rpow hx_pos, log_mul hx_pos.ne' (exp_pos _).ne', log_exp]
    grind
  have h_fifth : x ^ (1 / 5 : ℝ) ≤ x * exp (-4 * b / 5) := by
    rw [← log_le_log_iff (rpow_pos_of_pos hx_pos _) (mul_pos hx_pos (exp_pos _)),
        log_rpow hx_pos, log_mul hx_pos.ne' (exp_pos _).ne', log_exp]
    grind
  have hc₀_nonneg : 0 ≤ RS_prime.c₀ := le_of_lt (by norm_num : (0 : ℝ) < 1.03883)
  nlinarith


@[blueprint
  "bklnw-thm-1a"
  (title := "BKLNW Theorem 1a")
  (statement := /--  For any fixed $X_0 \geq 1$, there exists $m_0 > 0$ such that, for all $x \geq X_0$
  $$ x(1 - m_0) \leq \theta(x). $$
  For any fixed $X_1 \geq 1$, there exists $M_0 > 0$ such that, for all $x \geq X_1$
  $$ \theta(x) \leq x(1 + M_0). $$
  For $X_0, X_1 \geq e^{20}$, we have
  $$ m_0 = \varepsilon(\log X_0) + 1.03883 \left( X_0^{-1/2} + X_0^{-2/3} + X_0^{-4/5} \right) $$
  and
  $$ M_0 = \varepsilon(\log X_1). $$
  -/)
  (proof := /-- Combine Lemmas \ref{bklnw-lemma-11a} with $b = \log X_1$ for the upper bound, and and \ref{bklnw-lemma-11b} with $b = \log X_0$ for the lower bound. -/)
  (latexEnv := "theorem")
  (discussion := 790)]
theorem thm_1a {X₀ X₁ x : ℝ} (hX₀ : X₀ ≥ exp 20) (hX₁ : X₁ ≥ exp 20) (hx₀ : x ≥ X₀) (hx₁ : x ≥ X₁) :
    let m₀ := Pre_inputs.default.ε (log X₀) + RS_prime.c₀ * (X₀^(-1/2:ℝ) + X₀^(-2/3:ℝ) + X₀^(-4/5:ℝ))
    let M₀ := Pre_inputs.default.ε (log X₁)
    x * (1 - m₀) ≤ θ x ∧ θ x ≤ x * (1 + M₀) := by
  have hX₀' : X₀ > 1 := by linarith [add_one_le_exp 20]
  have hX₁' : X₁ > 1 := by linarith [add_one_le_exp 20]
  have h_psi_bounds : ψ x ≤ x * (1 + Pre_inputs.default.ε (log X₁)) := by
    have := BKLNW_app.theorem_2 (log X₁) (log_nonneg hX₁'.le) x (by rw [exp_log (by linarith)]; linarith)
    rw [mul_add, mul_one, abs_le] at *
    linarith!
  have h_theta_bounds : θ x ≥ (1 - Pre_inputs.default.ε (log X₀) -
      RS_prime.c₀ * (exp (-log X₀ / 2) + exp (-2 * log X₀ / 3) +
        exp (-4 * log X₀ / 5))) * x := by
    grind [lemma_11b Pre_inputs.default (log_pos (hX₀')) ((exp_log (by positivity)).symm ▸ hx₀)]
  refine ⟨?_, by grind [theta_le_psi x]⟩
  convert h_theta_bounds.le using 1
  grind [rpow_def_of_pos (by linarith : 0 < X₀)]

@[blueprint
  "bklnw-thm-1a-checked"
  (statement := /-- One has $x(1-m) \leq \theta(x) \leq x(1+M)$ whenever $x \geq e^b$ and $b,M,m$ obey the condition that $b \geq 20$, $\eps(b) \leq M$, and $\eps(b) + c_0 (e^{-b/2} + e^{-2b/3} + e^{-4b/5}) \leq m$. -/)
  (latexEnv := "theorem")
  (discussion := 801)]
theorem thm_1a_crit {b M m : ℝ} (h_check : check_row_prop (b, M, m)) {x : ℝ} (hx : x ≥ exp b) :
    x * (1 - m) ≤ θ x ∧ θ x ≤ x * (1 + M) := by
  obtain ⟨hb, hM, hm⟩ := h_check
  have := thm_1a (exp_le_exp.mpr hb) (exp_le_exp.mpr hb) hx hx
  simp only at hm hM this
  simp only [log_exp b, rpow_def_of_pos (exp_pos b)] at this
  have h : 0 ≤ x := (exp_pos b).le.trans hx
  grw [← hm, ← hM]
  rw [show Pre_inputs.default.ε = BKLNW_app.table_8_ε by rfl] at this
  grind

@[blueprint
  "bklnw-thm-1a-table"
  (statement := /-- The previous theorem holds with $(b,M,m)$ given by the values in \cite[Table 14]{BKLNW}. -/)
  (latexEnv := "theorem")]
theorem thm_1a_table {b M m : ℝ} (h_table : (b, M, m) ∈ table_14) {x : ℝ} (hx : x ≥ exp b) :
    x * (1 - m) ≤ θ x ∧ θ x ≤ x * (1 + M) := thm_1a_crit (table_14_check h_table) hx


@[blueprint
  "bklnw-cor-2-1"
  (title := "BKLNW Corollary 2.1")
  (statement := /-- $\theta(x) \leq (1 + 1.93378 \times 10^{-8}) x$. -/)
  (proof := /-- We combine together Theorem \ref{from-buthe-eq-1-7} and Theorem \ref{bklnw-thm-1a-table} with $X_1 = 10^{19}$. -/)
  (latexEnv := "corollary")
  (discussion := 791)]
theorem cor_2_1 : ∀ x > 0, θ x ≤ (1 + (1.93378e-8*BKLNW_app.table_8_margin)) * x := by
  intro x hx_pos
  by_cases hx : x ≤ 1e19
  · exact le_trans (le_of_lt (buthe_eq_1_7 x ⟨hx_pos, hx⟩)) (le_mul_of_one_le_left hx_pos.le (by norm_num))
  · push_neg at hx
    have h_exp20 : 1e19 ≥ exp 20 := by grw [← exp_one_rpow 20, Real.exp_one_lt_d9]; norm_num only
    suffices Pre_inputs.default.ε (log 1e19) ≤ 1.93378e-8 * BKLNW_app.table_8_margin by
      grw [(thm_1a h_exp20 h_exp20 hx.le hx.le).2, this, mul_comm]
    unfold Pre_inputs.default
    suffices 43 < log 1e19 ∧ log 1e19 < 44 by
      change BKLNW_app.table_8_ε (log 1e19) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
      grw [BKLNW_app.table_8_ε.le_simp (log 1e19) (by grind)]
      grind [BKLNW_app.table_8_ε']
    rw [lt_log_iff_exp_lt (by positivity), log_lt_iff_lt_exp (by positivity),
      ← exp_one_rpow 43, ← exp_one_rpow 44]
    exact ⟨by grw [Real.exp_one_lt_d9]; norm_num only, by grw [← Real.exp_one_gt_d9]; norm_num only⟩

structure Inputs extends Pre_inputs where
  α : ℝ
  hα : ∀ x > 0, θ x ≤ (1 + α) * x


@[blueprint
  "bklnw-inputs"
  (title := "Default input parameters")
  (statement := /-- We take $\alpha = 1.93378 \times 10^{-8}$, so that we have $\theta(x) \leq (1 + \alpha) x$ for all $x$. -/)]
noncomputable def Inputs.default : Inputs := {
  toPre_inputs := Pre_inputs.default
  α := 1.93378e-8 * BKLNW_app.table_8_margin
  hα := cor_2_1
}

blueprint_comment /--
\subsection{Bounding psi minus theta}

In this section we obtain bounds of the shape
$$ \psi(x) - \theta(x) \leq a_1 x^{1/2} + a_2 x^{1/3}$$
for all $x \geq x_0$ and various $a_1, a_2, x_0$.
-/

@[blueprint
  "bklnw-eq-2-4"
  (title := "BKLNW Equation 2.4")
  (statement := /--
  $$ f(x) := \sum_{k=3}^{\lfloor \log x / \log 2 \rfloor} x^{1/k - 1/3}.$$
  -/)]
noncomputable def f (x : ℝ) : ℝ := ∑ k ∈ Icc 3 ⌊ (log x)/(log 2) ⌋₊, x^(1/k - 1/3 : ℝ)

@[blueprint
  "bklnw-prop-3-sub-1"
  (title := "BKLNW Proposition 3, substep 1")
  (statement := /-- Let $x \geq x_0$ and let $\alpha$ be admissible. Then
\[
\frac{\psi(x) - \theta(x) - \theta(x^{1/2})}{x^{1/3}} \leq (1 + \alpha) \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} x^{\frac{1}{k} - \frac{1}{3}}.
\]
-/)
  (proof := /-- Bound each $\theta(x^{1/k})$ term by $(1 + \alpha)x^{1/k}$ in Sublemma \ref{costa-pereira-sublemma-1-1}. -/)
  (latexEnv := "sublemma")
  (discussion := 630)]
theorem prop_3_sub_1 (I : Inputs) {x₀ x : ℝ} (hx₀ : x₀ ≥ 1)
    (hx : x ≥ x₀) :
    (ψ x - θ x - θ (x^(1/2))) / x^(1/3) ≤ (1 + I.α) * f x := by sorry

@[blueprint
  "bklnw-prop-3-sub-2"
  (title := "BKLNW Proposition 3, substep 2")
  (statement := /-- $f$ decreases on $[2^n, 2^{n+1})$.-/)
  (proof := /-- Clear. -/)
  (latexEnv := "sublemma")
  (discussion := 632)]
theorem prop_3_sub_2 (n : ℕ) (hn : n ≥ 4) : StrictAntiOn f (Set.Ico (2^n) (2^(n + 1))) := by
  have hlog2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hfloor : ∀ x ∈ Set.Ico (2^n : ℝ) (2^(n+1)), ⌊log x / log 2⌋₊ = n := fun x ⟨hlo, hhi⟩ ↦ by
    rw [Nat.floor_eq_iff <| div_nonneg (log_pos <| lt_of_lt_of_le (by
      norm_cast; exact Nat.one_lt_two_pow (by omega)) hlo).le hlog2.le, le_div_iff₀ hlog2,
        div_lt_iff₀ hlog2]
    refine ⟨?_, ?_⟩
    · calc (n : ℝ) * log 2 = log ((2 : ℝ)^n) := (log_pow 2 n).symm
        _ ≤ log x := log_le_log (by positivity) hlo
    · calc log x < log ((2 : ℝ)^(n+1)) := log_lt_log (lt_of_lt_of_le (by positivity : (0 : ℝ) < 2^n) hlo) hhi
        _ = (↑n + 1) * log 2 := by rw [log_pow]; push_cast; ring
  intro a ha b hb hab
  simp only [f, hfloor a ha, hfloor b hb]
  refine sum_lt_sum (fun k hk ↦ ?_) ⟨4, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  · rcases eq_or_ne k 3 with rfl | hk3
    · simp
    · have hk' : 3 < k := by simp only [mem_Icc] at hk; omega
      exact (rpow_lt_rpow_of_neg (lt_of_lt_of_le (by positivity) ha.1) hab
        (by have : (k:ℝ) > 3 := mod_cast hk'; field_simp; linarith)).le
  · exact rpow_lt_rpow_of_neg (lt_of_lt_of_le (by positivity) ha.1) hab (by norm_num)

noncomputable def u (n : ℕ) : ℝ := ∑ k ∈ Icc 4 n, 2^((n/k:ℝ) - (n/3:ℝ))

@[blueprint
  "bklnw-prop-3-sub-3"
  (title := "BKLNW Proposition 3, substep 3")
  (statement := /-- $f(2^n) = 1 + u_n$.-/)
  (proof := /-- Clear. -/)
  (latexEnv := "sublemma")
  (discussion := 633)]
theorem prop_3_sub_3 (n : ℕ) (hn : n ≥ 3) : f (2^n) = 1 + u n := by
  have sum_bound : ⌊ (log (2 ^ n)) / (log 2) ⌋₊ = n := by norm_num
  rw [f, u, sum_bound, ← add_sum_Ioc_eq_sum_Icc hn,
    ← Icc_add_one_left_eq_Ioc, Nat.cast_ofNat, sub_self, rpow_zero]
  congr with k
  rw [← rpow_natCast _ n, ← rpow_mul (by norm_num)]
  field_simp

noncomputable def summand (k n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((n + 1 : ℝ) / k) * ((2 : ℝ) ^ (1 / 3 - 1 / k : ℝ) - 1)

lemma summand_pos.aux {k : ℕ} (hk : 3 < k) : 0 < (2 : ℝ) ^ (1 / 3 - 1 / k : ℝ) - 1 :=
  sub_pos.mpr <| Real.one_lt_rpow (by grind) <|
    sub_pos.mpr <| one_div_lt_one_div_of_lt (by grind) (by exact_mod_cast hk)

lemma summand_pos {k : ℕ} (hk : 3 < k) (n : ℕ) : 0 < summand k n :=
  mul_pos (by positivity) (summand_pos.aux hk)

lemma summand_mono {k : ℕ} (hk : 3 < k) : StrictMono (summand k) :=
  (Real.strictMono_rpow_of_base_gt_one (by grind : (1 : ℝ) < 2))
  |>.comp (Nat.strictMono_cast.add_const 1 |>.div_const (by positivity))
  |>.mul_const (summand_pos.aux hk)

lemma sum_gt.aux (k : ℕ) (a b : ℝ) (hk : 3 < k := by decide) (hb1 : 0 ≤ b - 1 := by norm_num only)
    (ha : a ^ k ≤ 1024 := by norm_num only) (hb : b ^ (3 * k) ≤ 2 ^ (k - 3) := by norm_num only) :
    a * (b - 1) ≤ summand k 9 := by
  have ha_bound : a ≤ 2 ^ (10 / k : ℝ) := calc
    a ≤ (1024 : ℝ) ^ (1 / k : ℝ) := by
      contrapose! ha
      calc
        _ ≤ ((1024 : ℝ) ^ (1 / k : ℝ)) ^ k := by
          rw [← rpow_mul_natCast (by positivity), one_div_mul_cancel (by positivity), rpow_one]
        _ < _ := pow_lt_pow_left₀ ha (by positivity) (by positivity)
    _ = _ := by norm_num [div_eq_mul_inv, rpow_mul]
  have hb_bound : b - 1 ≤ 2 ^ (1 / 3 - 1 / k : ℝ) - 1 := calc
    _ ≤ ((2 : ℝ) ^ (k - 3 : ℝ)) ^ (1 / (3 * k : ℝ)) - 1 := by
      gcongr
      contrapose! hb
      calc
        _ ≤ (((2 : ℝ) ^ (k - 3 : ℝ)) ^ (1 / (3 * k : ℝ))) ^ (3 * k) := by
          rw [← rpow_mul_natCast (by positivity), ← Real.rpow_natCast, Nat.cast_sub hk.le]
          simp
          field_simp
          simp
        _ < _ := pow_lt_pow_left₀ hb (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_mul (by positivity), mul_one_div]; field_simp
  grw [ha_bound, hb_bound]
  norm_num [summand]

lemma sum_gt {n : ℕ} (hn : 9 ≤ n) : 2.12 < ∑ k ∈ Icc 4 n, summand k n := calc
  _ < ∑ k ∈ Icc 4 9, summand k 9 := by
    simp only [Nat.reduceLeDiff, sum_Icc_succ_top, Icc_self, sum_singleton]
    grw [← sum_gt.aux 4 5.65 1.05, ← sum_gt.aux 5 4 1.09, ← sum_gt.aux 6 3.17 1.12,
      ← sum_gt.aux 7 2.69 1.14, ← sum_gt.aux 8 2.37 1.155, ← sum_gt.aux 9 2.16 1.1665]
    norm_num
  _ ≤ ∑ k ∈ Icc 4 n, summand k 9 :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hn) fun k _ _ ↦
      (summand_pos (by grind) 9).le
  _ ≤ _ := sum_le_sum fun k hk ↦ (summand_mono (by grind)).le_iff_le.mpr hn

lemma u_diff_factored {n : ℕ} (hn : 4 ≤ n) :
    u (n + 1) - u n = 2 ^ (-(n + 1) / 3 : ℝ) * (2 - ∑ k ∈ Icc 4 n, summand k n) := calc
  u (n + 1) - u n = (∑ k ∈ Icc 4 n,
      (2 : ℝ) ^ ((n + 1) / (k : ℝ) - (n + 1) / 3) * (1 - 2 ^ (1 / (3 : ℝ) - 1 / ↑k)))
      + 2 ^ (1 - (n + 1) / (3 : ℝ)) := by
    rw [u, u, sum_Icc_succ_top (Nat.le_add_right_of_le hn), div_self (by norm_cast),
      ← sub_add_eq_add_sub, ← sum_sub_distrib, Nat.cast_add, Nat.cast_one]
    congr with x
    rw [mul_sub, mul_one, ← rpow_add two_pos]
    grind
  _ = _ := by
    rw [mul_sub, mul_sum, ← rpow_add_one two_pos.ne', neg_div, neg_add_eq_sub,
      ← neg_add_eq_sub _ (2 ^ _), ← sum_neg_distrib]
    congr with x
    rw [summand, ← mul_assoc, ← rpow_add two_pos]
    grind

@[blueprint
  "bklnw-prop-3-sub-4"
  (title := "BKLNW Proposition 3, substep 4")
  (statement := /-- $u_{n+1} < u_n$ for $n \geq 9$.-/)
  (proof := /-- We have
\begin{equation}
u_{n+1} - u_n = \sum_{k=4}^{n} 2^{\frac{n+1}{k} - \frac{n+1}{3}}(1 - 2^{\frac{1}{3} - \frac{1}{k}}) + 2^{1 - \frac{n+1}{3}} = 2^{-\frac{n+1}{3}} \left( 2 - \sum_{k=4}^{n} 2^{\frac{n+1}{k}}(2^{\frac{1}{3} - \frac{1}{k}} - 1) \right).
\end{equation}
Define $s(k, n) := 2^{\frac{n+1}{k}}(2^{\frac{1}{3} - \frac{1}{k}} - 1)$. Note that $s(k, n)$ is monotone increasing in $n$ for each fixed $k \geq 4$. By numerical computation (using the trick $x \le 2 ^ {p / q} \iff x ^ q \le 2 ^ p$ to verify decimal lower bounds $x$), $\sum_{k=4}^{n} s(k, n) \ge \sum_{k=4}^{9} s(k, 9) > 2.12 > 2$. Thus $u_{n+1} - u_n < 0$. -/)
  (latexEnv := "sublemma")
  (discussion := 634)]
theorem prop_3_sub_4 (n : ℕ) (hn : 9 ≤ n) : u (n + 1) < u n := by
  grw [← sub_neg, u_diff_factored (by grind), ← sum_gt hn]
  norm_num
  positivity

@[blueprint
  "bklnw-prop-3-sub-5"
  (title := "BKLNW Proposition 3, substep 5")
  (statement := /-- $f(2^n) > f(2^{n+1})$ for $n \geq 9$. -/)
  (proof := /-- This follows from Sublemmas \ref{bklnw-prop-3-sub-3} and \ref{bklnw-prop-3-sub-4}. -/)
  (latexEnv := "sublemma")
  (discussion := 635)]
theorem prop_3_sub_5 (n : ℕ) (hn : n ≥ 9) : f (2^n) > f (2^(n + 1)) := by
  rw [prop_3_sub_3 n (Nat.le_of_add_left_le hn), prop_3_sub_3 (n + 1) (by omega)]
  linarith [prop_3_sub_4 n hn]

@[blueprint
  "bklnw-prop-3-sub-6"
  (title := "BKLNW Proposition 3, substep 6")
  (statement := /-- $f(x) \leq f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$ on $[2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1}, \infty)$. -/)
  (proof := /-- Follows from Sublemmas \ref{bklnw-prop-3-sub-2} and \ref{bklnw-prop-3-sub-5}. -/)
  (latexEnv := "sublemma")
  (discussion := 636)]
theorem prop_3_sub_6 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ≥ 2 ^ (⌊(log x₀) / (log 2)⌋₊ + 1)) :
    f x ≤ f (2 ^ (⌊(log x₀)/(log 2)⌋₊ + 1)) := by
  have hlog2 : log 2 > 0 := log_pos one_lt_two
  have hx_pos : x > 0 := lt_of_lt_of_le (by positivity) hx
  set m := ⌊(log x₀) / (log 2)⌋₊; set n := ⌊log x / log 2⌋₊
  have hm : m ≥ 9 := Nat.le_floor <| (le_div_iff₀ hlog2).mpr <| by
    rw [← log_pow]; exact Real.log_le_log (by positivity) hx₀
  have hn : n ≥ m + 1 := Nat.le_floor <| (le_div_iff₀ hlog2).mpr <| by
    rw [← log_pow]; exact Real.log_le_log (by positivity) hx
  have key : x = 2 ^ (log x / log 2) := by
    rw [rpow_def_of_pos two_pos, mul_comm, div_mul_cancel₀ _ hlog2.ne', exp_log hx_pos]
  have hdiv : 0 ≤ log x / log 2 :=
    div_nonneg (log_nonneg (hx.trans' (one_le_pow₀ one_le_two))) hlog2.le
  have hlo : (2:ℝ)^n ≤ x := by
    rw [key, ← rpow_natCast]; exact rpow_le_rpow_of_exponent_le one_le_two (Nat.floor_le hdiv)
  have hhi : x < 2^(n+1) := by
    rw [key, ← rpow_natCast]
    exact rpow_lt_rpow_of_exponent_lt one_lt_two (by exact_mod_cast Nat.lt_floor_add_one _)
  have hf_x : f x ≤ f (2^n) := by
    by_cases hx_eq : x = 2^n; · simp [hx_eq]
    exact (prop_3_sub_2 n (by omega)
      ⟨le_rfl, by exact_mod_cast Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self n)⟩
      ⟨hlo, hhi⟩ (hlo.lt_of_ne' hx_eq)).le
  calc f x ≤ f (2^n) := hf_x
    _ ≤ f (2^(m+1)) := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hn
      rw [hd]; clear hd
      induction d with
      | zero => rfl
      | succ d ih =>
        have hmd : m + 1 + d ≥ 9 := by omega
        exact (prop_3_sub_5 _ hmd).le.trans ih

@[blueprint
  "bklnw-prop-3-sub-7"
  (title := "BKLNW Proposition 3, substep 7")
  (statement := /-- $f(x) \leq f(x_0)$ for $x \in [x_0, 2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$. -/)
  (proof := /-- Follows since $f(x)$ decreases on $[2^{\lfloor \frac{\log x_0}{\log 2} \rfloor}, 2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$. -/)
  (latexEnv := "sublemma")
  (discussion := 637)]
theorem prop_3_sub_7 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ∈ Set.Ico x₀ (2 ^ (⌊(log x₀) / (log 2)⌋₊ + 1))) :
    f x ≤ f x₀ := by
  obtain ⟨hx_lo, hx_hi⟩ := hx
  have hx₀_pos : 0 < x₀ := by positivity
  have hlog2 : log 2 > 0 := log_pos one_lt_two
  set n := ⌊(log x₀) / (log 2)⌋₊
  have key : (2:ℝ)^((log x₀) / (log 2)) = x₀ := by
    rw [rpow_def_of_pos (by norm_num), mul_comm, div_mul_cancel₀ _ hlog2.ne', exp_log hx₀_pos]
  have hx₀_ge : x₀ ≥ 2^n := by
    have : (n:ℝ) ≤ log x₀ / log 2 := Nat.floor_le (div_nonneg (log_nonneg (by linarith)) hlog2.le)
    calc x₀ = 2^(log x₀ / log 2) := key.symm
      _ ≥ 2^(n:ℝ) := rpow_le_rpow_of_exponent_le one_le_two this
      _ = 2^n := rpow_natCast 2 n
  have hx₀_lt : x₀ < 2^(n+1) := by
    have : log x₀ / log 2 < n + 1 := Nat.lt_floor_add_one _
    calc x₀ = 2^(log x₀ / log 2) := key.symm
      _ < 2^((n:ℝ)+1) := rpow_lt_rpow_of_exponent_lt one_lt_two (by exact_mod_cast this)
      _ = 2^(n+1) := by rw [← rpow_natCast]; norm_cast
  have hn_ge : n ≥ 4 := by
    by_contra hcon; push_neg at hcon
    have : (2 : ℝ) ^ (n + 1) ≤ 2^9 := pow_le_pow_right₀ one_le_two <| by omega
    linarith [hx₀, hx₀_lt]
  rcases hx_lo.eq_or_lt with rfl | hlt
  · rfl
  · exact (prop_3_sub_2 n hn_ge ⟨hx₀_ge, hx₀_lt⟩ ⟨hx₀_ge.trans hx_lo, hx_hi⟩ hlt).le

@[blueprint
  "bklnw-prop-3-sub-8"
  (title := "BKLNW Proposition 3, substep 8")
  (statement := /--  $f(x) \leq \max\left(f(x_0), f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})\right)$. -/)
  (proof := /-- Combines previous sublemmas. -/)
  (latexEnv := "sublemma")
  (discussion := 638)]
theorem prop_3_sub_8 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ≥ x₀) :
    f x ≤ max (f x₀) (f (2 ^ (⌊ (log x₀)/(log 2) ⌋₊ + 1))) := by
  by_cases hcase : x < 2 ^ (⌊(log x₀) / (log 2)⌋₊ + 1)
  · exact (prop_3_sub_7 x₀ hx₀ x ⟨hx, hcase⟩).trans (le_max_left _ _)
  · exact (prop_3_sub_6 x₀ hx₀ x (not_lt.mp hcase)).trans (le_max_right _ _)

@[blueprint
  "bklnw-prop-3"
  (title := "BKLNW Proposition 3")
  (statement := /--  Let $x_0 \geq 2^9$. Let $\alpha > 0$ exist such that $\theta(x) \leq (1 + \alpha)x$ for $x > 0$. Then for $x \geq x_0$,
\begin{equation}
\sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k}) \leq \eta x^{1/3},
\end{equation}
where
\begin{equation}
\eta = \eta(x_0) = (1 + \alpha) \max\left(f(x_0), f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})\right)
\end{equation}
with
\begin{equation}
f(x) := \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} x^{\frac{1}{k} - \frac{1}{3}}.
\end{equation}
 -/)
  (proof := /-- Combines previous sublemmas. -/)
  (latexEnv := "proposition")
  (discussion := 639)]
theorem prop_3 (I : Inputs) {x₀ x : ℝ} (hx₀ : x₀ ≥ 2 ^ 9) (hx : x ≥ x₀) :
    ∑ k ∈ Icc 3 ⌊(log x)/(log 2)⌋₊, θ (x^(1/(k:ℝ))) ≤
      (1 + I.α) * max (f x₀) (f (2^(⌊(log x₀)/(log 2)⌋₊ + 1))) * x^(1/3:ℝ) := by
  have h_sum_le : ∑ k ∈ Icc 3 ⌊(log x) / (log 2)⌋₊, θ (x^(1 / k : ℝ)) ≤
      (1 + I.α) * f x * x^(1 / 3 : ℝ) := by
    have h_sum_le' : ∑ k ∈ Icc 3 ⌊(log x) / (log 2)⌋₊, θ (x^(1 / k : ℝ)) ≤
        ∑ k ∈ Icc 3 ⌊(log x) / (log 2)⌋₊, (1 + I.α) * x^(1 / k : ℝ) := sum_le_sum fun i hi ↦ by
      have := I.hα (x ^ (1 / (i : ℝ))) (rpow_pos_of_pos (by grind) _)
      norm_num [log_rpow (by positivity)] at *
      exact this
    convert h_sum_le' using 1
    norm_num [f, mul_sum .., mul_assoc, mul_comm, mul_left_comm, sum_mul]
    refine sum_bij (fun k hk ↦ k) ?_ ?_ ?_ ?_ <;> norm_num
    intro a ha₁ ha₂; rw [← rpow_add (by grind)]; grind
  apply le_trans h_sum_le ?_
  gcongr
  · exact rpow_nonneg (by grind) _
  · have := I.hα 1
    grind [show 0 ≤ θ 1 from sum_nonneg fun _ _ ↦ log_nonneg <| Nat.one_le_cast.2 <|
      Nat.Prime.pos <| by grind only [= mem_filter]]
  · exact prop_3_sub_8 x₀ hx₀ x hx

@[blueprint
  "bklnw-cor-3-1"
  (title := "BKLNW Corollary 3.1")
  (statement := /--  Let $b \geq 7$. Assume $x \geq e^b$. Then we have
\[
\psi(x) - \theta(x) - \theta(x^{1/2}) \leq \eta x^{1/3},
\]
where
\begin{equation}
\eta = (1 + \alpha) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right)
\end{equation}
 -/)
  (proof := /-- We apply Proposition \ref{bklnw-prop-3} with $x_0 = e^b$ where we observe that $x_0 = e^b \geq e^7 > 2^9$.
 -/)
  (latexEnv := "corollary")
  (discussion := 640)]
theorem cor_3_1 (I : Inputs) {b x : ℝ} (hb : b ≥ 7) (x : ℝ) (hx : x ≥ exp b) :
    ψ x - θ x - θ (x^(1/2:ℝ)) ≤
      (1 + I.α) * max (f (exp b)) (f (2^(⌊b / (log 2)⌋ + 1))) * x^(1/3:ℝ) := by
  let x₀ := exp b
  have : x₀ ≥ 2 ^ 9 := by
    refine le_trans ?_ (exp_le_exp_of_le hb)
    rw [← exp_one_rpow]
    refine le_trans ?_ (rpow_le_rpow (by norm_num) exp_one_gt_d9.le (by norm_num))
    norm_num
  calc
    _ = ∑ n ∈ Icc 2 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) - θ (x ^ (1/2 : ℝ)) := by
      rw [Chebyshev.psi_eq_theta_add_sum_theta (by linarith)]; ring
    _ = ∑ n ∈ Icc 3 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) := by
      have : ⌊log x / log 2⌋₊ ≥ 2 := calc
          _ ≥ ⌊b / log 2⌋₊ := by gcongr; rw [← log_exp b]; exact log_le_log (by linarith) hx
          _ ≥ 2 := by apply Nat.le_floor; field_simp; norm_num; linarith [log_two_lt_d9, hb]
      rw [← add_sum_Ioc_eq_sum_Icc this, ← Icc_add_one_left_eq_Ioc]; ring_nf
    _ = ∑ n ∈ Icc 3 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) := by
      refine sum_bij (fun n _ ↦ n) ?_ ?_ ?_ ?_
      · intro n hn; simp only [mem_Icc] at hn ⊢
        exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
      · intro _ _ _ _ h; simp only at h; exact h
      · intro n hn; simp only [mem_Icc] at hn ⊢
        refine ⟨n, ?_, rfl⟩
        exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
      · intro _ _; simp only [one_div]
    _ ≤ (1 + I.α) * max (f x₀) (f (2 ^ (⌊log x₀ / log 2⌋₊ + 1))) * x ^ (1/3 : ℝ) := by
      exact prop_3 I this hx
    _ ≤ (1 + I.α) * max (f (exp b)) (f (2 ^ (⌊b / log 2⌋ + 1))) * x ^ (1/3 : ℝ) := by
      gcongr
      · exact rpow_nonneg (le_trans (by linarith) hx) _
      · have := I.hα 1
        grind [show 0 ≤ θ 1 from sum_nonneg fun _ _ ↦ log_nonneg <| Nat.one_le_cast.2 <|
          Nat.Prime.pos <| by grind only [= mem_filter]]
      · simp only [x₀, log_exp]
        rw [← Int.natCast_floor_eq_floor (div_nonneg (by linarith) (log_nonneg (by norm_num)))]
        rfl

@[blueprint
  "bklnw-prop-4-a"
  (title := "BKLNW Proposition 4, part a")
  (statement := /--  If $7 \leq b \leq 2\log x_1$, then we have
\begin{equation}
\theta(x^{1/2}) \leq (1 + \varepsilon(\log x_1))x^{1/2} \quad \text{for } x \geq e^b.
\end{equation}
 -/)
  (proof := /--
Note that in the paper, the inequality in Proposition 4 is strict, but the
argument can only show nonstrict inequalities.
If $e^b \leq x \leq x_1^2$, then $x^{1/2} \leq x_1$, and thus
\[
\theta(x^{1/2}) < x^{1/2} \quad \text{for } e^b \leq x \leq x_1^2.
\]
On the other hand, if $x^{1/2} > x_1 = e^{\log x_1}$, then we have by (2.7)
\[
\theta(x^{1/2}) \leq \psi(x^{1/2}) \leq (1 + \varepsilon(\log x_1))x^{1/2},
\]
since $\log x_1 \geq 7$. The last two inequalities for $\theta(x^{1/2})$ combine to establish (2.8).
 -/)
  (latexEnv := "proposition")
  (discussion := 641)]
theorem prop_4_a (I : Inputs) {b x : ℝ} (hx : exp b ≤ x) :
    θ (x ^ (1 / 2 : ℝ)) ≤ (1 + I.ε (log I.x₁)) * x ^ (1 / 2 : ℝ) := by
  have ha : 1 < I.x₁ := by linarith [I.hx₁, (one_lt_exp_iff.2 (by linarith) : 1 < exp 7)]
  have hb : 0 < log I.x₁ := log_pos (by linarith)
  by_cases! hp : x ^ (1 / 2 : ℝ) ≤ I.x₁
  · have hq : 0 < x ^ (1 / 2 : ℝ) := by
      suffices 0 < x from rpow_pos_of_pos this _
      exact (exp_pos b).trans_le hx
    refine (I.hx₁' (x ^ (1 / 2 : ℝ)) ⟨hq, hp⟩).le.trans ?_
    nth_rw 1 [← one_mul (x ^ (1 / 2 : ℝ))]
    gcongr
    linarith [I.epsilon_nonneg hb.le]
  · calc
    _ ≤ ψ (x ^ (1 / 2 : ℝ)) := theta_le_psi _
    _ ≤ (1 + I.ε (log I.x₁)) * x ^ (1 / 2 : ℝ) := by
      have := (le_abs_self (ψ (x ^ (1 / 2 : ℝ)) - x ^ (1 / 2 : ℝ))).trans <|
        I.hε (log I.x₁) hb.le (x ^ (1 / 2 : ℝ)) (exp_log (by linarith : 0 < I.x₁) ▸ hp).le
      linarith

@[blueprint
  "bklnw-prop-4-b"
  (title := "BKLNW Proposition 4, part b")
  (statement := /--  If $b > 2\log x_1$, then we have
\[
\theta(x^{1/2}) \leq (1 + \varepsilon(b/2))x^{1/2} \quad \text{for } x \geq e^b.
\]
 -/)
  (proof := /-- Note that in the paper, the inequality in Proposition 4 is strict, but the
argument can only show nonstrict inequalities. As in the above subcase, we have for $x \geq e^b$
\[
\theta(x^{1/2}) \leq \psi(x^{1/2}) \leq (1 + \varepsilon(b/2))x^{1/2},
\]
since $x^{1/2} > e^{b/2} > x_1 \geq e^7$.
 -/)
  (latexEnv := "proposition")
  (discussion := 642)]
theorem prop_4_b (I : Inputs) {b x : ℝ} (hb : 7 ≤ b) (hx : exp b ≤ x) :
    θ (x ^ (1 / 2 : ℝ)) ≤ (1 + I.ε (b / 2)) * x ^ (1 / 2 : ℝ) := calc
  _ ≤ ψ (x ^ (1 / 2 : ℝ)) := theta_le_psi _
  _ ≤ (1 + I.ε (b / 2)) * x ^ (1 / 2 : ℝ) := by
    have : exp (b / 2) ≤ x ^ (1 / 2 : ℝ) := by
      rw [exp_half, ← sqrt_eq_rpow]
      exact sqrt_monotone hx
    have := (le_abs_self _).trans <| I.hε (b / 2) (by linarith) (x ^ (1 / 2 : ℝ)) this
    linarith

@[blueprint
  "bklnw-def-a-1"
  (title := "Definition of a1")
  (statement := /--  $a_1$ is equal to $1 + \varepsilon(\log x_1)$ if $b \leq 2\log x_1$, and equal to $1 + \varepsilon(b/2)$ if $b > 2\log x_1$. -/)]
noncomputable def Inputs.a₁ (I : Inputs) (b : ℝ) : ℝ :=
  if b ≤ 2 * log I.x₁ then 1 + I.ε (log I.x₁)
  else 1 + I.ε (b / 2)

@[blueprint
  "bklnw-def-a-2"
  (title := "Definition of a2")
  (statement := /--  $a_2$ is defined by
\[
a_2 = (1 + \alpha) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right).
\]
 -/)]
noncomputable def Inputs.a₂ (I : Inputs) (b : ℝ) : ℝ :=
  (1 + I.α) * (max (f (exp b)) (f (2^(⌊ b / (log 2) ⌋₊ + 1))))

@[blueprint
  "bklnw-thm-5"
  (title := "BKLNW Theorem 5")
  (statement := /--  Let $\alpha > 0$ exist such that
\[
\theta(x) \leq (1 + \alpha)x \quad \text{for all } x > 0.
\]
Assume for every $b \geq 7$ there exists a positive constant $\varepsilon(b)$ such that
\[
\psi(x) - x \leq \varepsilon(b)x \quad \text{for all } x \geq e^b.
\]
Assume there exists $x_1 \geq e^7$ such that
\begin{equation}
\theta(x) < x \quad \text{for } x \leq x_1.
\end{equation}
Let $b \geq 7$. Then, for all $x \geq e^b$ we have
\[
\psi(x) - \theta(x) < a_1 x^{1/2} + a_2 x^{1/3},
\]
where
\[
a_1 = \begin{cases}
1 + \varepsilon(\log x_1) & \text{if } b \leq 2\log x_1, \\
1 + \varepsilon(b/2) & \text{if } b > 2\log x_1,
\end{cases}
\]
and
\[
a_2 = (1 + \alpha) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right).
\]
  -/)
  (proof := /-- We have $\psi(x) - \theta(x) = \theta(x^{1/2}) + \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k})$. For any $b \geq 7$, setting $x_0 = e^b$ in Proposition 4, we bound $\sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k})$ by $\eta x^{1/3}$ as defined in (2.3). We bound $\theta(x^{1/2})$ with Proposition \ref{bklnw-prop-4} by taking either $a_1 = 1 + \varepsilon(\log x_1)$ for $b \leq 2\log x_1$ or $a_1 = 1 + \varepsilon(b/2)$ for $b > 2\log x_1$.
 -/)
  (latexEnv := "theorem")
  (discussion := 643)]
theorem thm_5 (I : Inputs) {b x : ℝ} (hb : b ≥ 7) (hx : x ≥ exp b) :
    ψ x - θ x ≤ I.a₁ b * x^(1/2:ℝ) + I.a₂ b * x^(1/3:ℝ) := calc
  _ = θ (x ^ (1/2 : ℝ)) + (ψ x - θ x - θ (x ^ (1/2 : ℝ))) := by ring
  _ ≤ I.a₁ b * x^(1/2:ℝ) + I.a₂ b * x^(1/3:ℝ) := by
    gcongr
    · unfold Inputs.a₁
      by_cases h : b ≤ 2 * log I.x₁
      · simp only [if_pos h, prop_4_a I hx]
      · simp only [if_neg h, prop_4_b I hb hx]
    · unfold Inputs.a₂
      convert cor_3_1 I hb x hx
      · rw [← Int.natCast_floor_eq_floor (div_nonneg (by linarith) (log_nonneg (by norm_num)))]; rfl
      · tauto

noncomputable def a₁ : ℝ → ℝ := Inputs.default.a₁

noncomputable def a₂ : ℝ → ℝ := Inputs.default.a₂

@[blueprint
  "bklnw-cor-5-1"
  (title := "BKLNW Corollary 5.1")
  (statement := /--  Let $b \geq 7$. Then for all $x \geq e^b$ we have $\psi(x) - \vartheta(x) < a_1 x^{1/2} + a_2 x^{1/3}$, where $a_1 = a_1(b) = 1 + 1.93378 \times 10^{-8}$ if $b \leq 38 \log 10$, $1 + \varepsilon(b/2)$ if $b > 38 \log 10$, and $a_2 = a_2(b) = (1 + 1.93378 \times 10^{-8}) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right)$, where $f$ is defined by (2.4) and values for $\varepsilon(b/2)$ are from Table 8. -/)
  (proof := /-- This is Theorem 5 applied to the default inputs in Definition \ref{bklnw-inputs}. -/)
  (latexEnv := "corollary")
  (discussion := 743)]
theorem cor_5_1 {b x : ℝ} (hb : b ≥ 7) (hx : x ≥ exp b) :
    ψ x - θ x ≤ a₁ b * x ^ (1 / 2 : ℝ) + a₂ b * x ^ (1 / 3 : ℝ) :=
  thm_5 Inputs.default hb hx

def table_cor_5_1 : List (ℝ × ℝ × ℕ) :=
  [(20, 1.4263, 4)
  , (25, 1.2196, 4)
  , (30, 1.1211, 4)
  , (35, 1.07086, 5)
  , (40, 1.04320, 5)
  , (43, 1.03253, 5)
  , (100, 1 + 2.421e-4, 7)
  , (150, 1 + 3.749e-6, 8)
  , (200, 1 + 7.712e-8, 9)
  , (250, 1 + 2.024e-8, 9)
  , (300, 1 + 1.936e-8, 9)
 ]

@[blueprint
  "bklnw-cor-5-1-rem"
  (title := "Remark after BKLNW Corollary 5.1")
  (statement := /--  We have the following values for $a_2$, given by the table after \cite[Corollary 5.1]{BKLNW}. -/)
  (latexEnv := "remark")
  (discussion := 853)]
theorem cor_5_1_rem (b a₂b : ℝ) (m : ℕ) (hb : (b, a₂b, m) ∈ table_cor_5_1) :
    a₂ b ∈ Set.Icc a₂b (a₂b + 10^(-m:ℝ)) := by sorry



blueprint_comment /--
\subsection{Bounding theta(x)-x with a logarithmic decay, I: large x}

In this section and the next ones we obtain bounds of the shape
$$ x \left(1 - \frac{m_k}{\log^k x}\right) \leq \theta(x)$$
for all $x \geq X_0$ and
$$ \theta(x) \leq x \left(1 + \frac{M_k}{\log^k x}\right)$$
for all $x \geq X_1$, for various $k, m_k, M_k, X_0, X_1$, with $k \in \{1,\dots,5\}$.

For this section we focus on estimates that are useful when $x$ is extremely large, e.g., $x \geq e^{25000}$.
-/

/-
Show that the function g in the proof of the following lemma is decreasing
-/
lemma g_decreasing_interval (A C : ℝ) (hA : 0 < A) (hC : 0 < C) (u v : ℝ) (hu : 4 * A ^ 2 / C ^ 2 ≤ u) (huv : u ≤ v) :
    v ^ A * Real.exp (-C * Real.sqrt v) ≤ u ^ A * Real.exp (-C * Real.sqrt u) := by
      -- Let $f(t) = t^A e^{-C\sqrt{t}}$. The derivative is $f'(t) = t^{A-1} e^{-C\sqrt{t}} (A - \frac{C}{2}\sqrt{t})$.
      set f := fun t : ℝ => t ^ A * Real.exp (-C * Real.sqrt t)
      have h_deriv : ∀ t > 0, deriv f t = t ^ (A - 1) * Real.exp (-C * Real.sqrt t) * (A - C / 2 * Real.sqrt t) := by
        intro t ht; norm_num [ f, ht.ne', Real.sqrt_eq_rpow, Real.rpow_sub ht ] ; ring;
        rw [ show ( -1 / 2 : ℝ ) = ( 1 / 2 : ℝ ) - 1 by norm_num, Real.rpow_sub ht ] ; norm_num ; ring;
      -- Since $4A^2/C^2 \le u \le v$, we have $f'(t) \le 0$ for $t \ge 4A^2/C^2$.
      have h_deriv_nonpos : ∀ t > 0, 4 * A ^ 2 / C ^ 2 ≤ t → deriv f t ≤ 0 := by
        intro t ht ht'; rw [ h_deriv t ht ] ; exact mul_nonpos_of_nonneg_of_nonpos ( mul_nonneg ( Real.rpow_nonneg ht.le _ ) ( Real.exp_nonneg _ ) ) ( sub_nonpos_of_le <| by rw [ div_le_iff₀ <| by positivity ] at *; nlinarith [ show 0 ≤ Real.sqrt t * C by positivity, Real.mul_self_sqrt ht.le ] ) ;
      by_contra h_contra;
      -- Apply the mean value theorem to $f$ on the interval $[u, v]$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo u v, deriv f c = (f v - f u) / (v - u) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact huv.lt_of_ne ( by rintro rfl; linarith );
        · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.mul ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inr <| by linarith ) <| ContinuousAt.rexp <| ContinuousAt.mul continuousAt_const <| Real.continuous_sqrt.continuousAt;
        · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.mul ( DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) ( by linarith [ hx.1, show 0 < u by exact lt_of_lt_of_le ( by positivity ) hu ] ) ) ( DifferentiableAt.exp ( DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.sqrt ( differentiableAt_id ) ( by linarith [ hx.1, show 0 < u by exact lt_of_lt_of_le ( by positivity ) hu ] ) ) ) ) );
      simp +zetaDelta only [gt_iff_lt, neg_mul, ge_iff_le, not_le, Set.mem_Ioo] at *
      rw [ eq_div_iff ] at hc <;> nlinarith [ h_deriv_nonpos c ( by linarith [ show 0 < u by exact lt_of_lt_of_le ( by positivity ) hu ] ) ( by linarith ) ]


@[blueprint
  "bklnw-lem-6"
  (title := "BKLNW Lemma 6")
  (statement := /--  Suppose there exists $c_1, c_2, c_3, c_4 > 0$ such that
\begin{equation}\label{bklnw_3.3}
|\theta(x) - x| \leq c_1 x (\log x)^{c_2} \exp(-c_3 (\log x)^{\frac{1}{2}}) \quad \text{for all } x \geq c_4.
\end{equation}
Let $k > 0$ and let $b \geq \max\left(\log c_4, \log\left(\frac{4(c_2 + k)^2}{c_3^2}\right)\right)$. Then for all $x \geq e^b$ we have
$$
|\theta(x) - x| \leq \frac{\mathcal{A}_k(b) x}{(\log x)^k},
$$
where
$$
\mathcal{A}_k(b) = c_1 \cdot b^{c_2 + k} e^{-c_3\sqrt{b}}.
$$ -/)
  (proof := /-- We denote $g(x) = (\log x)^{c_2 + k} \exp(-c_3 (\log x)^{\frac{1}{2}})$. By \eqref{bklnw_3.3}, $|\theta(x) - x| < \frac{c_1 g(x) x}{(\log x)^k}$ for all $x \geq c_4$. It suffices to bound $g$: by calculus, $g(x)$ decreases when $x \geq \frac{4(c_2 + k)^2}{c_3^2}$. Therefore $|\theta(x) - x| \leq \frac{c_1 g(e^b) x}{(\log x)^k}$. Note that $c_1 g(e^b) = \mathcal{A}_k(b)$ and the condition on $b$ follows from the conditions $e^b \geq c_4$ and $e^b \geq \frac{4(c_2 + k)^2}{c_3^2}$. -/)
  (latexEnv := "lemma")
  (discussion := 854)]
theorem lem_6 {c₁ c₂ c₃ c₄ k b x : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄)
    (hθ : Eθ.classicalBound c₁ c₂ c₃ 1 c₄)
    (hk : 0 < k)
    (hb : b ≥ max (log c₄) (((4 * (c₂ + k) ^ 2) / (c₃ ^ 2))))
    (hx : x ≥ exp b) :
    let A := c₁ * b ^ (c₂ + k) * exp (-c₃ * sqrt b)
    Eθ x ≤ A / (log x) ^ k := by
      /-NOTE: the hypothesis `hb` is modified from the original source material \cite{BKLNW}, from b ≥ log ((4 * (c₂ + k) ^ 2) / (c₃ ^ 2))) to b ≥ ((4 * (c₂ + k) ^ 2) / (c₃ ^ 2))).
      This corresponds to the fact that in the proof sketch above, the claim "$g(x)$ decreases when $x \geq \frac{4(c_2 + k)^2}{c_3^2}$" should be "$g(x)$ decreases when $\log x \geq \frac{4(c_2 + k)^2}{c_3^2}$."  -/
      -- By `hθ`, we have $E_\theta(x) \le c_1 (\log x)^{c_2} e^{-c_3\sqrt{\log x}}$.
      have h_bound : Eθ x ≤ c₁ * (Real.log x) ^ c₂ * Real.exp (-c₃ * Real.sqrt (Real.log x)) := by
        convert hθ x _ using 1 <;> norm_num;
        · unfold admissible_bound ; norm_num;
          exact Or.inl <| Or.inl <| Real.sqrt_eq_rpow _;
        · exact le_trans ( Real.log_le_iff_le_exp ( by positivity ) |>.1 ( le_trans ( le_max_left _ _ ) hb ) ) hx;
      -- By `g_decreasing_interval` with $A = c_2+k$ and $C = c_3$, $g$ is decreasing on $[4(c_2+k)^2/c_3^2, \infty)$.
      have h_decreasing : ∀ u v : ℝ, 4 * (c₂ + k) ^ 2 / c₃ ^ 2 ≤ u → u ≤ v → v ^ (c₂ + k) * Real.exp (-c₃ * Real.sqrt v) ≤ u ^ (c₂ + k) * Real.exp (-c₃ * Real.sqrt u) := by
        -- Apply the lemma g_decreasing_interval with A = c₂ + k and C = c₃.
        apply g_decreasing_interval (c₂ + k) c₃ (by linarith) (by linarith);
      -- Since $b \ge 4(c_2+k)^2/c_3^2$, we have $b \le \log x$.
      have h_log_x_ge_b : b ≤ Real.log x := by
        exact le_trans ( by norm_num ) ( Real.log_le_log ( by positivity ) hx );
      have := h_decreasing b ( Real.log x ) ( by linarith [ le_max_right ( Real.log c₄ ) ( 4 * ( c₂ + k ) ^ 2 / c₃ ^ 2 ) ] ) h_log_x_ge_b; simp_all +decide only [ge_iff_le, sup_le_iff, neg_mul,
        Real.rpow_add
            (show 0 < Real.log x from
              lt_of_lt_of_le
                (by
                  linarith [le_max_left (Real.log c₄) (4 * (c₂ + k) ^ 2 / c₃ ^ 2),
                    le_max_right (Real.log c₄) (4 * (c₂ + k) ^ 2 / c₃ ^ 2),
                    show 0 < 4 * (c₂ + k) ^ 2 / c₃ ^ 2 by positivity])
                h_log_x_ge_b)]
      rw [ le_div_iff₀ ( Real.rpow_pos_of_pos ( show 0 < Real.log x from lt_of_lt_of_le ( by linarith [ show 0 < 4 * ( c₂ + k ) ^ 2 / c₃ ^ 2 by positivity ] ) h_log_x_ge_b ) _ ) ] ; nlinarith [ Real.rpow_pos_of_pos ( show 0 < Real.log x from lt_of_lt_of_le ( by linarith [ show 0 < 4 * ( c₂ + k ) ^ 2 / c₃ ^ 2 by positivity ] ) h_log_x_ge_b ) k ] ;


@[blueprint
  "bklnw-cor-14-1"
  (title := "BKLNW Corollary 14.1")
  (statement := /--  Suppose one has an asymptotic bound $E_\psi$ with parameters $A,B,C,R,e^{x_0}$ (which need to satisfy some additional bounds) with $x_0 \geq 1000$.  Then $E_\theta$ obeys an asymptotic bound with parameters $A', B, C, R, e^{x_0}$, where
  $$ A' := A (1 + \frac{1}{A} (\frac{R}{x_0})^B \exp(C \sqrt{\frac{x_0}{R}}) (a_1(x_0) \exp(\frac{-x_0}{2}) + a_2(x_0) \exp(\frac{-2 x_0}{3}))) $$
  and $a_1(x_0), a_2(x_0)$ are as in Corollary \ref{bklnw-cor-5-1}. -/)
  (proof := /-- We write $\theta(x) - x = \psi(x) - x + \theta(x) - \psi(x)$, apply the triangle inequality, and invoke Corollary \ref{bklnw-cor-5-1} to obtain
$$
E_\theta(x) \leq A (\frac{\log x}{R})^B \exp(-C (\frac{\log x}{R})^{\frac{1}{2}}) + a_1(x_0) x^{-\frac{1}{2}} + a_2(x_0) x^{-\frac{2}{3}}$$
$$ \leq A (\frac{\log x}{R})^B \exp(-C (\frac{\log x}{R})^{\frac{1}{2}}) (1 + \frac{a_1(x_0) \exp(C \sqrt{\frac{\log x}{R}})}{A \sqrt{x} (\frac{\log x}{R})^B} + \frac{a_2(x_0) \exp(C \sqrt{\frac{\log x}{R}})}{A x^{\frac{2}{3}} (\frac{\log x}{R})^B}).$$
The function in brackets decreases for $x \geq e^{x_0}$ with $x_0 \geq 1000$ (assuming reasonable hypotheses on $A,B,C,R$) and thus we obtain the desired bound with $A'$ as above.
 -/)
  (latexEnv := "corollary")
  (discussion := 855)]
theorem cor_14_1 {A B C R x₀ : ℝ} (hx₀ : x₀ ≥ 1000)
    (hEψ : Eψ.classicalBound A B C R x₀)
    (hA : A > 0)
    (hB : B ∈ Set.Icc (3 / 2) (7 / 4))
    (hC : C ∈ Set.Icc (2 / 3) 2)
    (hR : R ∈ Set.Icc 1 10) -- some plausible placeholder (and mild) hypotheses on B,C,R here, consistent with actual values.  Feel free to adjust as needed
    :
    let A' := A * (1 + (1 / A) * (R / x₀) ^ B * exp (C * sqrt (x₀ / R)) *
      (a₁ x₀ * exp (-x₀ / 2) + a₂ x₀ * exp (-2 * x₀ / 3)))
    Eθ.classicalBound A' B C R x₀ := by
      sorry

blueprint_comment /--
\subsection{Bounding theta(x)-x with a logarithmic decay, II: medium x}

In this section we tackle medium $x$.

TODO: formalize Lemma 8 and Corollary 8.1
-/

blueprint_comment /--
\subsection{Bounding theta(x)-x with a logarithmic decay, III: small x}

In this section we tackle small $x$.

TODO: formalize (3.17), (3.18), Lemma 9, Corollary 9.1
-/


blueprint_comment /--
\subsection{Bounding theta(x)-x with a logarithmic decay, IV: very small x}

In this section we tackle very small $x$.

TODO: Formalize Lemma 10
-/


blueprint_comment /--
\subsection{Final bound on Etheta(x)}

Now we put everything together.

TODO: Section 3.7.1; 3.7.2; 3.7.3; 3.7.4
-/


noncomputable def Table_15 : List (ℝ × (Fin 5 → ℝ)) := [
  (0, ![1.2323e0, 3.9649e0, 2.0829e1, 1.5123e2, 1.3441e5]),
  (log 1e5, ![5.5316e-2, 6.4673e-1, 7.5612e0, 8.9346e1, 1.3441e5]),
  (log 5e5, ![2.6724e-2, 3.5744e-1, 4.7808e0, 6.3944e1, 1.3441e5]),
  (log 1e6, ![2.3240e-2, 3.2309e-1, 4.4916e0, 6.2444e1, 1.3441e5]),
  (log 5e6, ![1.0236e-2, 1.5952e-1, 2.4860e0, 5.7184e1, 1.3441e5]),
  (log 1e7, ![8.4725e-3, 1.3675e-1, 2.2071e0, 5.7184e1, 1.3441e5]),
  (log 5e7, ![3.8550e-3, 6.8701e-2, 1.2244e0, 5.7184e1, 1.3441e5]),
  (log 1e8, ![2.7457e-3, 5.0612e-2, 9.4259e-1, 5.7184e1, 1.3441e5]),
  (log 1e9, ![9.5913e-4, 2.0087e-2, 4.2065e-1, 5.7184e1, 1.3441e5]),
  (log 1e10, ![3.7787e-4, 8.7526e-3, 2.0274e-1, 5.7184e1, 1.3441e5]),
  (log 19035709163, ![2.6773e-4, 6.3370e-3, 1.5000e-1, 5.7184e1, 1.3441e5]),
  (log 2e10, ![2.4601e-4, 5.8365e-3, 1.3848e-1, 5.7184e1, 1.3441e5]),
  (log 5e10, ![1.8556e-4, 4.5722e-3, 1.1266e-1, 5.7184e1, 1.3441e5]),
  (log 1e11, ![1.3392e-4, 3.4053e-3, 8.6589e-2, 5.7184e1, 1.3441e5]),
  (log 2e11, ![7.8683e-5, 2.0591e-3, 5.3886e-2, 5.7184e1, 1.3441e5]),
  (log 3e11, ![7.0193e-5, 1.8758e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 4e11, ![7.0193e-5, 1.8758e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 5e11, ![6.9322e-5, 1.8717e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 6e11, ![6.9322e-5, 1.8717e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (28, ![4.3555e-5, 1.2196e-3, 3.4148e-2, 5.7184e1, 1.3441e5]),
  (29, ![2.7336e-5, 7.9272e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (30, ![1.7139e-5, 5.1415e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (31, ![1.0735e-5, 3.3277e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (32, ![7.0053e-6, 2.2417e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (33, ![4.3798e-6, 1.4454e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (34, ![2.7360e-6, 9.3023e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (35, ![1.7078e-6, 5.9771e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (36, ![1.0652e-6, 3.8345e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (37, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (38, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (39, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (40, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (41, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (42, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (43, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (19 * log 10, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (44, ![7.8163e-7, 3.5174e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (45, ![5.0646e-7, 2.3298e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (46, ![3.2935e-7, 1.5480e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (47, ![2.1308e-7, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (48, ![1.3791e-7, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (49, ![8.9140e-8, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (50, ![5.7545e-8, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (55, ![6.3417e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (60, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (65, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (70, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (80, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (90, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (100, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (200, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (300, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (400, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (500, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (600, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (700, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (800, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (900, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (1000, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (1500, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (2000, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (2500, ![2.2885e-9, 5.7783e-6, 1.4591e-2, 3.6840e1, 9.3021e4]),
  (3000, ![1.3915e-10, 4.2091e-7, 1.2733e-3, 3.8516e0, 1.1651e4]),
  (3500, ![8.7646e-12, 3.0896e-8, 1.0891e-4, 3.8390e-1, 1.3533e3]),
  (4000, ![5.7410e-13, 2.3108e-9, 9.3007e-6, 3.7436e-2, 1.5068e2]),
  (5000, ![2.8715e-15, 1.4645e-11, 7.4687e-8, 3.8091e-4, 1.9426e0]),
  (6000, ![1.7952e-17, 1.0951e-13, 6.6798e-10, 4.0747e-6, 2.4856e-2]),
  (7000, ![1.4744e-19, 1.0468e-15, 7.4322e-12, 5.2769e-8, 3.7466e-4]),
  (8000, ![1.6007e-21, 1.2966e-17, 1.0502e-13, 8.5065e-10, 6.8903e-6]),
  (9000, ![2.2253e-23, 2.0250e-19, 1.8428e-15, 1.6769e-11, 1.5260e-7]),
  (10000, ![3.8228e-25, 3.8610e-21, 3.8997e-17, 3.9387e-13, 3.9780e-9]),
  (11000, ![7.9284e-27, 8.8005e-23, 9.7685e-19, 1.0844e-14, 1.2036e-10]),
  (12000, ![1.9331e-28, 2.3390e-24, 2.8302e-20, 3.4245e-16, 4.1437e-12]),
  (13000, ![5.5830e-30, 7.5371e-26, 1.0175e-21, 1.3737e-17, 1.8544e-13]),
  (14000, ![1.8399e-31, 2.7598e-27, 4.1396e-23, 6.2094e-19, 9.3141e-15]),
  (15000, ![6.5712e-33, 1.0514e-28, 1.6823e-24, 2.6916e-20, 4.3065e-16]),
  (16000, ![2.5739e-34, 4.3756e-30, 7.4384e-26, 1.2646e-21, 2.1497e-17]),
  (17000, ![1.1168e-35, 2.0101e-31, 3.6182e-27, 6.5127e-23, 1.1723e-18]),
  (18000, ![5.3739e-37, 1.0211e-32, 1.9400e-28, 3.6860e-24, 7.0033e-20]),
  (19000, ![2.7357e-38, 5.4714e-34, 1.0943e-29, 2.1886e-25, 4.3772e-21]),
  (20000, ![1.5041e-39, 3.1585e-35, 6.6329e-31, 1.3929e-26, 2.9251e-22]),
  (21000, ![9.0606e-41, 1.9934e-36, 4.3853e-32, 9.6477e-28, 2.1225e-23]),
  (22000, ![5.6101e-42, 1.2904e-37, 2.9678e-33, 6.8258e-29, 1.5700e-24]),
  (23000, ![3.7554e-43, 9.0129e-39, 2.1631e-34, 5.1915e-30, 1.2460e-25]),
  (24000, ![2.6756e-44, 6.6889e-40, 1.6723e-35, 4.1806e-31, 1.0452e-26]),
  (25000, ![7.5635e-45, 1.8909e-40, 4.7272e-36, 1.1818e-31, 2.9545e-27])
]

/- [FIX]: This fixes a typo in the original paper https://arxiv.org/pdf/2002.11068. -/
@[blueprint
  "bklnw-thm-1b"
  (title := "Theorem 1b")
  (statement := /--  Let $k$ be an integer with $1 \leq k \leq 5$. For any fixed $X_0 > 1$, there exists $m_k > 0$ such that, for all $x \geq X_0$
  $$ x(1 - \frac{m_k}{(\log x)^k}) \leq \theta(x). $$
  For any fixed $X_1 > 1$, there exists $M_k > 0$ such that, for all $x \geq X_1$
  $$ \theta(x) \leq x(1 + \frac{M_k}{(\log x)^k}). $$
  In the case $k = 0$ and $X_0, X_1 \geq e^{20}$, we have
  $$ m_0 = \varepsilon(\log X_0) + 1.03883 \left( X_0^{-1/2} + X_0^{-2/3} + X_0^{-4/5} \right) $$
  and
  $$ M_0 = \varepsilon(\log X_1). $$
  -/)
  (latexEnv := "theorem")]
theorem thm_1b (k : ℕ) (hk : k ≤ 5) {X₀ X₁ x : ℝ} (hX₀ : X₀ > 1) (hX₁ : X₁ > 1) (hx₀ : x ≥ X₀)
    (hx₁ : x ≥ X₁) : ∃ mₖ Mₖ, (x * (1 - mₖ / (log x)^k) ≤ θ x) ∧ (θ x ≤ x * (1 + Mₖ / (log x)^k)) := by
  sorry

/- [FIX]: This fixes a typo in the original paper https://arxiv.org/pdf/2002.11068. -/
@[blueprint
  "bklnw-thm-1b-table"
  (title := "BKLNW Theorem 1b, table form")
  (statement := /--  See \cite[Table 15]{BKLNW} for values of $m_k$ and $M_k$, for $k \in \{1,2,3,4,5\}$.
  -/)
  (latexEnv := "theorem")]
theorem thm_1b_table {X₀ : ℝ} (hX₀ : X₀ > 1) {M : Fin 5 → ℝ} (h : (X₀, M) ∈ Table_15) (k : Fin 5) {x : ℝ} (hx : x ≥ X₀) :
  x * (1 - M k / (log x)^(k.val + 1)) ≤ θ x ∧ θ x ≤ x * (1 + M k / (log x)^(k.val + 1)) :=
  by sorry


blueprint_comment /--
\subsection{Computational examples}

Now we apply the previous theorem.

TODO: Corollary 11.1, 11.2
-/


end BKLNW
