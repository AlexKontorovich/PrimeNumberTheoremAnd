import PrimeNumberTheoremAnd.SecondaryDefinitions

blueprint_comment /--
\section{Chebyshev's estimates}\label{chebyshev-estimates-sec}

We record Chebyshev's estimates on $\psi$. The material here is adapted from the presentation of Diamond -/

namespace Chebyshev

open Real
open ArithmeticFunction hiding log

@[blueprint
  "cheby-def-T"
  (title := "The function $T$")
  (statement := /-- $T(x) := \sum_{n \leq x} \log n$. -/)]
noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

@[blueprint
  "cheby-T-upper"
  (title := "Upper bound on $T$")
  (statement := /-- For $x \geq 1$, we have $T(x) \leq x \log x - x + 1 + \log x$. -/)
  (proof := /-- Upper bound $\log n$ by $\int_n^{n+1} \log t\ dt$ for $n < x-1$ and by $\log x$ for $x-1 < n \leq x$ to bound
  $$T(x) \leq \int_1^x \log t\ dt + \log x$$
  giving the claim. -/)
  (latexEnv := "lemma")
  (discussion := 831)]
theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Finset.Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    Finset.sum_insert Finset.right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    have : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 1) (continuous_mul_log.sub continuous_id).continuousOn
        (fun t ht ↦ by
          simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
          exact ((differentiableAt_id.mul (differentiableAt_log (by grind))).sub
            differentiableAt_id).differentiableWithinAt)
        (fun t ht ↦ by
          simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
          have : DifferentiableAt ℝ (fun t ↦ t * log t) t :=
            differentiableAt_id.mul (differentiableAt_log <| by grind)
          have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
            simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
              deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
          exact hderiv ▸ log_nonneg (le_of_lt ht))
    exact this (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

@[blueprint
  "cheby-T-lower"
  (title := "Lower bound on $T$")
  (statement := /-- For $x \geq 1$, we have $T(x) \leq x \log x - x + 1 - \log x$. -/)
  (proof := /-- Drop the $n=1$ term. Lower bound $\log n$ by $\int_{n-1}^{n} \log t\ dt$ for $2 \leq n < x$ to bound
  $$T(x) \geq \int_1^{\lfloor x \rfloor} \log t\ dt \geq \int_1^x \log t\ dt - \log x $$
  giving the claim. -/)
  (latexEnv := "lemma")
  (discussion := 832)]
theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Finset.Ico_insert_right hone_le_floor, Finset.sum_insert Finset.right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have sum_shift : ∑ i ∈ Finset.Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) = log ⌊x⌋₊ + ∑ i ∈ Finset.Ico 1 ⌊x⌋₊, log i := by
    have : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ Finset.Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Finset.Ico 1 n, log i := by
      intro n hn
      induction n with
      | zero => omega
      | succ m ihm =>
        cases m with
        | zero => simp
        | succ k =>
          conv_lhs => rw [Nat.Ico_succ_right_eq_insert_Ico (by omega), Finset.sum_insert Finset.right_notMem_Ico]
          conv_rhs => rw [Nat.Ico_succ_right_eq_insert_Ico (by omega), Finset.sum_insert Finset.right_notMem_Ico]
          have h_ih := ihm (by omega)
          simp only [Nat.cast_succ] at h_ih ⊢
          linarith [h_ih]
    exact this ⌊x⌋₊ hone_le_floor
  have int_le_T : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n := by
    linarith [mono_log.integral_le_sum_Ico hone_le_floor, sum_shift]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have target_le_int : x * log x - x + 1 - log x ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    have : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
      calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
          ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x :=
            intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith) intervalIntegral.intervalIntegrable_log'
              intervalIntegrable_const fun t ht ↦ log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2
        _ = (x - ⌊x⌋₊) * log x := by simp
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith [int_le_T, int_eq, target_le_int]

@[blueprint
  "cheby-T-Lambda"
  (title := "Relating $T$ and von Mangoldt")
  (statement := /-- For $x \geq 0$, we have $T(x) = \sum_{n \leq x} \Lambda(n) \lfloor x/n \rfloor$. -/)
  (proof := /-- This follows from the identity $\log n = \sum_{d|n} \Lambda(d)$ and rearranging sums. -/)
  (latexEnv := "lemma")
  (discussion := 833)]
theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Finset.Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp_rw [Nat.floor_div_natCast]

@[blueprint
  "cheby-E"
  (title := "$E$ function")
  (statement := /-- If $\nu : \N \to \R$, let $E: \R \to \R$ denote the function $E(x):= \sum_m \nu(m) \lfloor x / m \rfloor$. -/)]
noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

@[blueprint
  "cheby-T-E"
  (title := "Relating a weighted sum of $T$ to an $E$-weighted sum of von Mangoldt")
  (statement := /-- If $\nu : \N \to \R$ is finitely supported, then
$$ \sum_m \nu(m) T(x/m) = \sum_{n \leq x} E(x/n) \Lambda(n).$$ -/)
  (latexEnv := "lemma")
  (discussion := 834)]
theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← Finsupp.sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases! hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by simp; grind
  by_cases! hx : x < 1
  · simp only [Nat.lt_one_iff, Nat.floor_eq_zero, hx, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
    convert Finset.sum_empty
    simp only [Finset.Icc_eq_empty_iff, Nat.one_le_floor_iff, not_le]
    exact div_lt_one (by linarith)|>.mpr (by linarith)
  apply Finset.sum_subset_zero_on_sdiff
  · apply Finset.Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · intros; ring_nf

open Finsupp in
@[blueprint
  "cheby-nu"
  (title := "Chebyshev's weight $\nu$")
  (statement := /-- $\nu = e_1 - e_2 - e_3 - e_5 + e_{30}$, where $e_n$ is the Kronecker delta at $n$. -/)]
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

@[blueprint
  "cheby-nu-cancel"
  (title := "Cancellation property of $\nu$")
  (statement := /-- One has $\sum_n \nu(n)/n = 0$ -/)
  (proof := /-- This follows from direct computation. -/)
  (latexEnv := "lemma")]
theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  norm_num [ν, add_div, Finsupp.sum_add_index', sub_div, Finsupp.sum_sub_index]

@[blueprint
  "cheby-E-1"
  (title := "$E$ initially constant")
  (statement := /-- One has $E(x)=1$ for $1 \leq x < 6$. -/)
  (proof := /-- This follows from direct computation. -/)
  (latexEnv := "lemma")
  (discussion := 835)]
theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  have : E ν x = ⌊x⌋₊ - ⌊x / 2⌋₊ - ⌊x / 3⌋₊ - ⌊x / 5⌋₊ + ⌊x / 30⌋₊ := by
    rw [E, ν, Finsupp.sum_add_index' (by grind) (by grind), Finsupp.sum_sub_index (by grind),
      Finsupp.sum_sub_index (by grind), Finsupp.sum_sub_index (by grind)]; simp
  obtain ⟨h1, h6⟩ := hx
  simp only [this, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have : 2 * ⌊x / 2⌋₊ ≤ ⌊x⌋₊ ∧ ⌊x⌋₊ ≤ 2 * ⌊x / 2⌋₊ + 1 := by
    refine ⟨Nat.le_floor (by push_cast; linarith [Nat.floor_le (by positivity : 0 ≤ x / 2)]), ?_⟩
    have : ⌊x⌋₊ < 2 * ⌊x / 2⌋₊ + 2 := Nat.floor_lt' (by omega) |>.mpr (by grind [Nat.lt_floor_add_one (x / 2)])
    omega
  have : 3 * ⌊x / 3⌋₊ ≤ ⌊x⌋₊ ∧ ⌊x⌋₊ ≤ 3 * ⌊x / 3⌋₊ + 2 := by
    have := Nat.lt_floor_add_one (x / 3)
    refine ⟨Nat.le_floor (by push_cast; linarith [Nat.floor_le (by positivity : 0 ≤ x / 3)]), ?_⟩
    have : ⌊x⌋₊ < 3 * ⌊x / 3⌋₊ + 3 := Nat.floor_lt' (by omega) |>.mpr (by grind)
    omega
  have : 5 * ⌊x / 5⌋₊ ≤ ⌊x⌋₊ ∧ ⌊x⌋₊ ≤ 5 * ⌊x / 5⌋₊ + 4 := by
    refine ⟨Nat.le_floor (by push_cast; linarith [Nat.floor_le (by positivity : 0 ≤ x / 5)]), ?_⟩
    have : ⌊x⌋₊ < 5 * ⌊x / 5⌋₊ + 5 := Nat.floor_lt' (by grind) |>.mpr (by grind [Nat.lt_floor_add_one (x / 5)])
    omega
  simp only [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega, Nat.cast_add]
  ring

@[blueprint
  "cheby-E-periodic"
  (title := "$E$ is periodic")
  (statement := /-- One has $E(x+30) = E(x)$. -/)
  (proof := /-- This follows from direct computation. -/)
  (latexEnv := "lemma")]
theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have : ∀ y, E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := fun _ ↦ by
    rw [E, ν, Finsupp.sum_add_index' (by simp) (by intros; ring), Finsupp.sum_sub_index
      (by intros; ring), Finsupp.sum_sub_index (by intros; ring), Finsupp.sum_sub_index
      (by intros; ring)]; simp
  simp only [this, show ⌊x + 30⌋₊ = ⌊x⌋₊ + 30 from Nat.floor_add_natCast hx 30, Nat.cast_add,
    show ⌊(x + 30) / 2⌋₊ = ⌊x / 2⌋₊ + 15 by
      rw [show (x + 30) / 2 = x / 2 + (15 : ℕ) by ring, Nat.floor_add_natCast (by positivity)],
    show ⌊(x + 30) / 3⌋₊ = ⌊x / 3⌋₊ + 10 by
      rw [show (x + 30) / 3 = x / 3 + (10 : ℕ) by ring, Nat.floor_add_natCast (by positivity)],
    show ⌊(x + 30) / 5⌋₊ = ⌊x / 5⌋₊ + 6 by
      rw [show (x + 30) / 5 = x / 5 + (6 : ℕ) by ring, Nat.floor_add_natCast (by positivity)],
    show ⌊(x + 30) / 30⌋₊ = ⌊x / 30⌋₊ + 1 by
      rw [show (x + 30) / 30 = x / 30 + (1 : ℕ) by ring, Nat.floor_add_natCast (by positivity)],
    Nat.cast_one]
  ring

@[blueprint
  "cheby-E-val"
  (title := "$E$ lies between $0$ and $1$")
  (statement := /-- One has $0 \leq E(x) \leq 1$ for all $x \geq 0$. -/)
  (proof := /-- This follows from direct computation for $0 \leq x < 30$, and then by periodicity for larger $x$. -/)
  (latexEnv := "lemma")
  (discussion := 836)]
theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by sorry

@[blueprint
  "cheby-U-def"
  (title := "The $U$ function")
  (statement := /-- We define $U(x) := \sum_m \nu(m) T(x/m)$. -/)]
noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

@[blueprint
  "cheby-psi-lower"
  (title := "Lower bounding $\\psi$ by a weighted sum of $T$")
  (statement := /-- For any $x > 0$, one has $\psi(x) \geq U(x)$. -/)
  (proof := /-- Use Lemma \ref{cheby-T-E} and Lemma \ref{cheby-E-val}. -/)
  (latexEnv := "proposition")
  (discussion := 837)]
theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Finset.Ioc_eq_Icc]
  gcongr
  expose_names
  have := E_nu_bound (x / i) <| div_nonneg hx.le (by simp)
  grw [this.2, mul_one]
  exact vonMangoldt_nonneg

@[blueprint
  "cheby-psi-diff"
  (title := "Upper bounding a difference of $\\psi$ by a weighted sum of $T$")
  (statement := /-- For any $x > 0$, one has $\psi(x) - \psi(x/6) \leq U(x)$. -/)
  (proof := /-- Use Lemma \ref{cheby-T-E}, Lemma \ref{cheby-E-val}, and Lemma \ref{cheby-E-1}. -/)
  (latexEnv := "proposition")
  (discussion := 838)]
theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by sorry

@[blueprint
  "a-def"
  (title := "The constant $a$")
  (statement := /-- We define $a := -\sum_m \nu(m) \log m / m$. -/)]
noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

@[blueprint
  "a-val"
  (title := "Numerical value of $a$")
  (statement := /-- We have $0.92129 \leq a \leq 0.92130$. -/)
  (latexEnv := "lemma")
  (discussion := 839)]
theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by sorry

@[blueprint
  "U-bounds"
  (title := "Bounds for $U$")
  (statement := /-- For $x \geq 30$, we have $|U(x) - ax| \leq 5\log x - 5$. -/)
  (proof := /-- Use Lemma \ref{cheby-T-upper}, Lemma \ref{cheby-T-lower}, the definition of $a$, and the triangle inequality, also using that $\log(2)+\log(3)+\log(5)+\log(30) \geq 6$. -/)
  (latexEnv := "lemma")
  (discussion := 840)]
theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by sorry

@[blueprint
  "psi-lower"
  (title := "Lower bound for $\\psi$")
  (statement := /-- For $x \geq 30$, we have $\psi(x) \geq ax - 5\log x - 1$. -/)
  (proof := /-- Use Lemma \ref{U-bounds} and Proposition \ref{cheby-psi-lower}.-/)
  (latexEnv := "theorem")
  (discussion := 841)]
theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by sorry

@[blueprint
  "psi-diff-upper"
  (title := "Upper bound for $\\psi$ difference")
  (statement := /-- For $x \geq 30$, we have $\psi(x) - \psi(x/6) \leq ax + 5\log x - 5$. -/)
  (proof := /-- Use Lemma \ref{U-bounds} and Proposition \ref{cheby-psi-upper}.-/)
  (latexEnv := "proposition")
  (discussion := 842)]
theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by sorry

@[blueprint
  "psi-num"
  (title := "Numerical bound for $\\psi(x)$ for very small $x$")
  (statement := /-- For $0 < x \leq 30$, we have $\psi(x) \leq 1.015 x$. -/)
  (proof := /-- Numerical check (the maximum occurs at $x=19$).  One only needs to check the case when $x$ is a prime power.-/)
  (latexEnv := "sublemma")]
theorem psi_num (x : ℝ) (hx : x > 0) (hx2 : x ≤ 30) : ψ x ≤ 1.015 * x := by sorry

@[blueprint
  "psi-upper"
  (title := "Upper bound for $\\psi$")
  (statement := /-- For $x \geq 30$, we have $\psi(x) \leq 6ax/5 + (\log (x/5) / \log 6) (5 \log x - 5)$. -/)
  (proof := /-- Iterate Lemma \ref{psi-diff-upper} using Sublemma \ref{psi-num} .-/)
  (latexEnv := "theorem")
  (discussion := 843)]
theorem psi_upper (x : ℝ) (hx : 30 ≤ x) : ψ x ≤ 6 * a * x / 5 + (log (x/5) / log 6) * (5 * log x - 5) := by sorry

@[blueprint
  "psi-num-2"
  (title := "Numerical bound for $\\psi(x)$ for medium $x$")
  (statement := /-- For $0 < x \leq 11723$, we have $\psi(x) \leq 1.11 x$. -/)
  (proof := /-- From Lemma \ref{psi-num} we can take $x \geq 30$. If one considers the sequence $x_1,x_2,\dots$ defined by $27, 32, 37, 43, 50, 58, 67, 77, 88, 100, 114, 129, 147, 166, 187, 211, 238, 268, 302, 340, 381, 427, 479, 536, 600, 671, 750, 839, 938, 1048, 1172, 1310, 1464, 1636, 1827, 2041, 2279, 2544, 2839, 3167, 3534, 3943, 4398, 4905, 5471, 6101, 6803, 7586, 8458, 9431, 10515, 11723$ then one should have $\psi(x_{j+1}-1) \leq 1.11 x_j$ for all $j$, which suffices.-/)
  (latexEnv := "sublemma")]
theorem psi_num_2 (x : ℝ) (hx : x > 0) (hx2 : x ≤ 11723) : ψ x ≤ 1.11 * x := by sorry

@[blueprint
  "psi-upper-clean"
  (title := "Clean upper bound for $\\psi$")
  (statement := /-- For $x > 0$, we have $\psi(x) \leq 1.11 x$. -/)
  (proof := /-- Strong induction on $x$.  For $x \leq 11723$ one can use Sublemma \ref{psi-num-2}.  Otherwise, we can use Proposition \ref{psi-diff-upper} and the triangle inequality. -/)
  (latexEnv := "theorem")
  (discussion := 844)]
theorem psi_upper_clean (x : ℝ) (hx : x > 0) : ψ x ≤ 1.11 * x := by sorry














end Chebyshev
