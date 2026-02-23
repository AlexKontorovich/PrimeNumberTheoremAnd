import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.NormNum.BigOperators
import PrimeNumberTheoremAnd.LogTables
import PrimeNumberTheoremAnd.SecondaryDefinitions
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Tactic.IntervalAuto

blueprint_comment /--
\section{Chebyshev's estimates}\label{chebyshev-estimates-sec}

We record Chebyshev's estimates on $\psi$. The material here is adapted from the presentation of Diamond \cite{diamond}. -/

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
  (statement := /-- For $x \geq 1$, we have $T(x) \geq x \log x - x + 1 - \log x$. -/)
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
theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    have expand : E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
      rw [E, ν, Finsupp.sum_add_index' (by grind) (by grind), Finsupp.sum_sub_index (by grind),
        Finsupp.sum_sub_index (by grind), Finsupp.sum_sub_index (by grind)]; simp
    simp only [expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero, add_zero]
    have := Nat.floor_le hy0; have := Nat.lt_floor_add_one y
    have := Nat.floor_le (by positivity : 0 ≤ y/2); have := Nat.lt_floor_add_one (y/2)
    have := Nat.floor_le (by positivity : 0 ≤ y/3); have := Nat.lt_floor_add_one (y/3)
    have := Nat.floor_le (by positivity : 0 ≤ y/5); have := Nat.lt_floor_add_one (y/5)
    have : 2 * ⌊y/2⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < 2 * ⌊y/2⌋₊ + 2 :=
      ⟨Nat.le_floor (by grind), by exact_mod_cast (by linarith : (⌊y⌋₊ : ℝ) < 2*⌊y/2⌋₊ + 2)⟩
    have : 3 * ⌊y/3⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < 3 * ⌊y/3⌋₊ + 3 :=
      ⟨Nat.le_floor (by grind), by exact_mod_cast (by linarith : (⌊y⌋₊ : ℝ) < 3*⌊y/3⌋₊ + 3)⟩
    have : 5 * ⌊y/5⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < 5 * ⌊y/5⌋₊ + 5 :=
      ⟨Nat.le_floor (by grind), by exact_mod_cast (by linarith : (⌊y⌋₊ : ℝ) < 5*⌊y/5⌋₊ + 5)⟩
    have : ⌊y⌋₊ < 30 := by exact_mod_cast (by linarith : (⌊y⌋₊ : ℝ) < 30)
    exact ⟨by linarith [show (⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℝ) ≤ ⌊y⌋₊ from by exact_mod_cast (by omega)],
      by linarith [show (⌊y⌋₊ : ℝ) ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 from by exact_mod_cast (by omega)]⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

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
theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Finset.Ioc_eq_Icc]
  have subset : Finset.Ioc 0 ⌊x / 6⌋₊ ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    apply Finset.Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← Finset.sum_sdiff_eq_sub subset, ← Finset.sum_sdiff subset]
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun n hn ↦ ?_) (Finset.sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1


@[blueprint
  "a-def"
  (title := "The constant $a$")
  (statement := /-- We define $a := -\sum_m \nu(m) \log m / m$. -/)]
noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, Finsupp.single_apply]
  rw [show ν.support = { 1, 2, 3, 5, 30 } from ?_]
  · norm_num [Finset.sum, ν]
    grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]
  · norm_num [ν, Finset.ext_iff]; grind

@[blueprint
  "a-val"
  (title := "Numerical value of $a$")
  (statement := /-- We have $0.92129 \leq a \leq 0.92130$. -/)
  (latexEnv := "lemma")
  (discussion := 839)]
theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by
  norm_num [Chebyshev.a_simpl]
  constructor <;> nlinarith [LogTables.log_2_gt, LogTables.log_2_lt,
    LogTables.log_3_gt, LogTables.log_3_lt, LogTables.log_5_gt, LogTables.log_5_lt]

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
theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_ge_weighted x (by linarith), h2.1]

@[blueprint
  "psi-diff-upper"
  (title := "Upper bound for $\\psi$ difference")
  (statement := /-- For $x \geq 30$, we have $\psi(x) - \psi(x/6) \leq ax + 5\log x - 5$. -/)
  (proof := /-- Use Lemma \ref{U-bounds} and Proposition \ref{cheby-psi-upper}.-/)
  (latexEnv := "proposition")
  (discussion := 842)]
theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_diff_le_weighted x (by linarith), h2.2]

set_option maxHeartbeats 400000 in
-- Proof splits into many cases
@[blueprint
  "psi-num"
  (title := "Numerical bound for $\\psi(x)$ for very small $x$")
  (statement := /-- For $0 < x \leq 30$, we have $\psi(x) \leq 1.015 x$. -/)
  (proof := /-- Numerical check (the maximum occurs at $x=19$).  One only needs to check the case when $x$ is a prime power.-/)
  (latexEnv := "sublemma")]
theorem psi_num (x : ℝ) (hx : x > 0) (hx2 : x ≤ 30) : ψ x ≤ 1.015 * x := by
  suffices ∀ n ∈ Finset.Icc (0 : ℕ) 30, ψ n ≤ 1.015 * n by
    rw [psi_eq_psi_coe_floor]
    grw [this]
    · gcongr
      exact Nat.floor_le hx.le
    · simp only [Finset.mem_Icc, zero_le, true_and]
      exact Nat.floor_le_of_le hx2
  unfold psi
  have primes : Λ 2 = log 2 ∧ Λ 3 = log 3 ∧ Λ 5 = log 5 ∧ Λ 7 = log 7 ∧ Λ 11 = log 11 ∧ Λ 13 = log 13 ∧ Λ 17 = log 17 ∧ Λ 19 = log 19 ∧ Λ 23 = log 23 ∧ Λ 29 = log 29 := by
    split_ands <;> exact vonMangoldt_apply_prime (by decide)
  have lam_pow : (Λ (2 ^ 2) = log 2) ∧ Λ (2 ^ 3) = log 2 ∧ Λ (2 ^ 4) = log 2 ∧ Λ (3 ^ 2) = log 3 ∧ Λ (3 ^ 3) = log 3 ∧ Λ (5 ^ 2) = log 5:= by
    split_ands <;> rw [vonMangoldt_apply_pow (by norm_num)] <;> (try rw [primes.1]) <;> simp_all
  have comps : Λ 6 = 0 ∧ Λ 10 = 0 ∧ Λ 12 = 0 ∧ Λ 14 = 0 ∧ Λ 15 = 0 ∧ Λ 18 = 0 ∧ Λ 20 = 0 ∧ Λ 21 = 0 ∧ Λ 22 = 0 ∧ Λ 24 = 0 ∧ Λ 26 = 0 ∧ Λ 28 = 0 ∧ Λ 30 = 0 := by
    split_ands <;> rw [vonMangoldt_eq_zero_iff, isPrimePow_nat_iff_bounded_log] <;> decide
  have log7bound : log 7 < 1.946 := by linarith [LogTables.log_7_lt]
  have log11bound : log 11 < 2.398 := by linarith [LogTables.log_11_lt]
  have : (log 13 < 2.57) ∧ (log 17 < 2.84) ∧ (log 19 < 2.95) :=
    ⟨by linarith [LogTables.log_13_lt], by linarith [LogTables.log_17_lt],
     by linarith [LogTables.log_19_lt]⟩
  have log23bound : log 23 ≤ (3 : ℕ) * log 2 + log 3 := by
    rw [← log_pow, ← log_mul] <;> norm_num
    gcongr
    norm_num
  have log29bound : log 29 ≤ log 2 + log 3 + log 5 := by
    rw [← log_mul, ← log_mul]<;> norm_num
    gcongr
    norm_num
  intro n hn
  fin_cases hn
  · simp
  · simp; norm_num
  all_goals
    simp_all [Finset.sum_Ioc_succ_top]
    linarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_lt]

@[blueprint
  "psi-upper"
  (title := "Upper bound for $\\psi$")
  (statement := /-- For $x \geq 30$, we have $\psi(x) \leq 6ax/5 + (\log (x/5) / \log 6) (5 \log x - 5)$. -/)
  (proof := /-- Iterate Lemma \ref{psi-diff-upper} using Sublemma \ref{psi-num} .-/)
  (latexEnv := "theorem")
  (discussion := 843)]
theorem psi_upper (x : ℝ) (hx : 30 ≤ x) : ψ x ≤ 6 * a * x / 5 + (log (x/5) / log 6) * (5 * log x - 5) := by
  have telescope (n : ℕ) : ψ x - ψ (x / 6 ^ n) = ∑ i ∈ Finset.Ico 0 n, (ψ (x / 6 ^ i) - ψ (x / 6 ^ (i + 1))) := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [Finset.sum_Ico_succ_top <| Nat.zero_le n, ← hn]
      ring
  have bound (n : ℕ) (h : ∀ i < n, 30 ≤ x / 6 ^ i) : ψ x - ψ (x / 6 ^ n) ≤ ∑ i ∈ Finset.Ico 0 n, (a * x / 6 ^i + 5 * log (x / 6 ^ i) - 5) := by
    rw [telescope]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    convert psi_diff_upper (x / 6 ^ i) (by grind) using 3
    · field
    · ring
  replace bound (n : ℕ) (h : ∀ i < n, 30 ≤ x / 6 ^ i) : ψ x - ψ (x / 6 ^ n) ≤ ∑ i ∈ Finset.Ico 0 n, (a * x / 6 ^i + 5 * log x - 5) := by
    grw [bound n h]
    apply Finset.sum_le_sum fun i hi ↦ ?_
    gcongr
    bound
  let n := ⌊log (x / 5) / log 6⌋₊
  specialize bound n ?_
  · intro i hi
    apply le_div_iff₀ (by simp)|>.mpr
    trans (30 * 6 ^ (n-1))
    · gcongr <;> grind
    · trans (30 * 6 ^ (log (x / 5) / log 6 - 1))
      · rw [← rpow_natCast, Nat.cast_sub]
        · gcongr
          · norm_num
          · refine Nat.floor_le <| div_nonneg ?_ ?_ <;> apply log_nonneg <;> linarith
          · norm_cast
        · apply Nat.le_floor
          norm_cast
          apply le_div_iff₀ (log_pos (by norm_num))|>.mpr
          rw [one_mul]
          gcongr
          linarith
      · rw [rpow_def_of_pos (by norm_num)]
        field_simp
        rw [exp_sub, exp_log, exp_log] <;> linarith
  simp_rw [← add_sub, Finset.sum_add_distrib, Finset.sum_const, Nat.Ico_zero_eq_range, Finset.card_range, nsmul_eq_mul, tsub_le_iff_right] at bound
  apply bound.trans
  conv => lhs; arg 1; arg 1; arg 2; ext i; rw [← mul_one_div, ←one_div_pow]
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num)]
  norm_num
  have : x / 6 ^ n ≤ 30 := by
    apply div_le_iff₀ (by simp)|>.mpr
    trans 30 * 6 ^ (log (x / 5) / log 6 - 1)
    · rw [rpow_def_of_pos (by norm_num)]
      field_simp
      rw [exp_sub, exp_log, exp_log] <;> linarith
    · rw [← rpow_natCast]
      gcongr
      · norm_num
      · exact Nat.sub_one_lt_floor _|>.le
  grw [psi_num _ (by simp; linarith) this]
  calc
  _ = 6 * a * x / 5 - x * (1 / 6) ^ n * (a * 1 / (5 / 6) - 1.015) + ↑n * (5 * log x - 5) := by
    ring_nf
    congr
    field
  _ ≤6 * a * x / 5 + n * (5 * log x - 5) := by
    gcongr
    simp only [one_div, inv_pow, mul_one, tsub_le_iff_right, le_add_iff_nonneg_right]
    refine mul_nonneg (mul_nonneg (by linarith) (by simp)) ?_
    grw [← a_bound.1]
    norm_num
  _ ≤ _ := by
    gcongr
    · simp only [sub_nonneg, Nat.ofNat_pos, le_mul_iff_one_le_right]
      exact le_log_iff_exp_le (by linarith)|>.mpr (by linarith [exp_one_lt_three])
    · exact Nat.floor_le (by bound)

set_option linter.style.nativeDecide false in
open LeanCert.Engine.ChebyshevPsi in
/-- The incremental checker verifies ψ(N) ≤ 1.11 N for all N = 1, …, 11723.
    Note: the sparse checkpoint ladder indicated in the blueprint is not needed;
    brute-force enumeration via `native_decide` suffices. -/
private theorem allChecks_11723 : checkAllPsiLeMulWith 11723 (111 / 100) 20 = true :=
  by native_decide

@[blueprint
  "psi-num-2"
  (title := "Numerical bound for $\\psi(x)$ for medium $x$")
  (statement := /-- For $0 < x \leq 11723$, we have $\psi(x) \leq 1.11 x$. -/)
  (proof := /-- Verified by brute-force: an $O(N)$ incremental checker confirms $\psi(N) \leq 1.11 N$ for every integer $N = 1, \ldots, 11723$ via \texttt{native\_decide}. The sparse checkpoint ladder originally described here is not needed. The real-variable case follows by monotonicity of $\psi$. -/)
  (latexEnv := "sublemma")]
theorem psi_num_2 (x : ℝ) (hx : x > 0) (hx2 : x ≤ 11723) : ψ x ≤ 1.11 * x := by
  open LeanCert.Engine.ChebyshevPsi in
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  have hnn : (0 : ℝ) ≤ x := le_of_lt hx
  have hfloor_le : ⌊x⌋₊ ≤ 11723 := Nat.floor_le_of_le hx2
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with hf | hf
  · simp only [hf, Nat.cast_zero]
    rw [Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (0:ℝ) < 2)]
    linarith
  · have hcheck := checkAllPsiLeMulWith_implies_checkPsiLeMulWith
      11723 (111 / 100) 20 allChecks_11723 ⌊x⌋₊ hf hfloor_le
    have h1 := psi_le_of_checkPsiLeMulWith ⌊x⌋₊ 20 (111 / 100) hcheck
    have hcast : ((111 / 100 : ℚ) : ℝ) = 111 / 100 := by norm_num
    rw [hcast] at h1
    calc ψ (⌊x⌋₊ : ℝ) ≤ 111 / 100 * ⌊x⌋₊ := h1
      _ ≤ 111 / 100 * x := by gcongr; exact Nat.floor_le hnn
      _ = 1.11 * x := by norm_num

@[blueprint
  "psi-upper-clean"
  (title := "Clean upper bound for $\\psi$")
  (statement := /-- For $x > 0$, we have $\psi(x) \leq 1.11 x$. -/)
  (proof := /-- Strong induction on $x$.  For $x \leq 11723$ one can use Sublemma \ref{psi-num-2}.  Otherwise, we can use Proposition \ref{psi-diff-upper} and the triangle inequality. -/)
  (latexEnv := "theorem")
  (discussion := 844)]
theorem psi_upper_clean (x : ℝ) (hx : x > 0) : ψ x ≤ 1.11 * x := by
  have hlog_large : ∀ y : ℝ, 11723 < y → 5 * log y - 5 ≤ (37 / 10000 : ℝ) * y := by
    intro y hy
    have hlog_y : log y ≤ log 11723 + (y / 11723 - 1) := by
      calc log y = log (11723 * (y / 11723)) := by
              rw [mul_div_cancel₀ _ (by norm_num : (11723 : ℝ) ≠ 0)]
        _ = log 11723 + log (y / 11723) :=
              Real.log_mul (by norm_num) (by positivity)
        _ ≤ log 11723 + (y / 11723 - 1) := by
              linarith [Real.log_le_sub_one_of_pos (show 0 < y / 11723 by positivity)]
    have hlog_11723 : log (11723 : ℝ) ≤ 937 / 100 := by interval_decide
    calc 5 * log y - 5
        ≤ 5 * (937 / 100 + (y / 11723 - 1)) - 5 := by linarith
      _ = 5 / 11723 * y + 3685 / 100 := by ring
      _ ≤ 37 / 10000 * y := by linarith
  have hNat : ∀ n : ℕ, ψ (n : ℝ) ≤ 1.11 * n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    by_cases hn0 : n = 0
    · subst hn0; simp [Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (0 : ℝ) < 2)]
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      by_cases hsmall : (n : ℝ) ≤ 11723
      · exact psi_num_2 n (by exact_mod_cast hn) hsmall
      · push_neg at hsmall
        let m : ℕ := ⌊(n : ℝ) / 6⌋₊
        have hm_lt_n : m < n := by
          exact_mod_cast show (m : ℝ) < n from
            lt_of_le_of_lt (Nat.floor_le (by positivity)) (by nlinarith)
        have hpsi_div : ψ ((n : ℝ) / 6) ≤ 1.11 * ((n : ℝ) / 6) := calc
          ψ ((n : ℝ) / 6) = ψ (m : ℝ) := by simp [m, Chebyshev.psi_eq_psi_coe_floor]
          _ ≤ 1.11 * (m : ℝ) := ih m hm_lt_n
          _ ≤ 1.11 * ((n : ℝ) / 6) := by nlinarith [Nat.floor_le (by positivity : 0 ≤ (n : ℝ) / 6)]
        calc ψ (n : ℝ)
            ≤ ψ ((n : ℝ) / 6) + a * n + 5 * log (n : ℝ) - 5 := by
                linarith [psi_diff_upper (n : ℝ) (by linarith)]
          _ ≤ 1.11 * ((n : ℝ) / 6) + 0.92130 * n + (37 / 10000 : ℝ) * n := by
                nlinarith [hpsi_div, hlog_large (n : ℝ) hsmall, a_bound.2,
                  show (0 : ℝ) < n from by exact_mod_cast hn]
          _ = 1.11 * n := by ring
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  calc ψ (⌊x⌋₊ : ℝ) ≤ 1.11 * ⌊x⌋₊ := hNat ⌊x⌋₊
    _ ≤ 1.11 * x := by nlinarith [Nat.floor_le hx.le]

end Chebyshev
