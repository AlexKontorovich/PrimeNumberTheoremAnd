import RSBounds.MertensFiniteScalars
import TernaryGoldbach.Prelim.SmallMertensProd

/-!
# Exact finite checks for the RS62 weighted-prime Mertens inequality

The state records fixed-point bounds for `log n` and a lower bound for
`∑_{p≤n} log p/p`. The logarithm increments and primality test are reused
from the independently audited upstream finite product certificate.
No asymptotic prime estimate or zero assumption enters this module.
-/

open Finset Real

namespace TernaryGoldbach.RSBounds.MertensFiniteWalk

open TernaryGoldbach.Prelim.LogWalk
open TernaryGoldbach.Prelim.MertProd (isP isP_iff)
open MertensFiniteScalars

structure WS where
  Llo : ℕ
  Lhi : ℕ
  Slo : ℕ
deriving DecidableEq

noncomputable def Sp (n : ℕ) : ℝ :=
  ∑ p ∈ Icc 0 n, if p.Prime then Real.log p / p else 0

theorem Sp_eq_primeWeightedSum (n : ℕ) : Sp n = primeWeightedSum n := by
  simp only [Sp, primeWeightedSum, Nat.floor_natCast, sum_filter]

def Ok (n : ℕ) : Prop :=
  Real.log ((n : ℝ) + 1) - 1.3 - 1 / (2 * Real.log ((n : ℝ) + 1)) < Sp n

def Inv (n : ℕ) (s : WS) : Prop :=
  (s.Llo : ℝ) ≤ 10 ^ 30 * Real.log n ∧
  10 ^ 30 * Real.log n ≤ (s.Lhi : ℝ) ∧
  (s.Slo : ℝ) ≤ 10 ^ 30 * Sp n ∧
  ∀ N, 2 ≤ N → N < n → Ok N

def step (n : ℕ) (s : WS) : WS :=
  let lo := s.Llo + incrLo n
  let hi := s.Lhi + incrHi n
  ⟨lo, hi, s.Slo + if isP (n + 1) then lo / (n + 1) else 0⟩

def check (hi slo : ℕ) : Prop :=
  20 * hi ^ 2 < 20 * hi * slo + 26 * 10 ^ 30 * hi + 10 * (10 ^ 30) ^ 2

instance (hi slo : ℕ) : Decidable (check hi slo) := by
  unfold check
  infer_instance

def walk : ℕ → ℕ → WS → Option WS
  | _, 0, s => some s
  | n, len + 1, s =>
    if s.Llo + s.Lhi + s.Slo < 10 ^ 100 ∧
        (n < 2 ∨ check (s.Lhi + incrHi n) s.Slo) then
      walk (n + 1) len (step n s) else none

/-- The integer comparison is the cross-multiplied logarithmic inequality. -/
theorem check_sound {L S : ℝ} {hi slo : ℕ} (hL : 0 < L)
    (hhi : 10 ^ 30 * L ≤ (hi : ℝ)) (hslo : (slo : ℝ) ≤ 10 ^ 30 * S)
    (hc : check hi slo) : L - 1.3 - 1 / (2 * L) < S := by
  let d : ℝ := 10 ^ 30
  have hd : 0 < d := by norm_num [d]
  have hhip : (0 : ℝ) < hi := lt_of_lt_of_le (mul_pos hd hL) hhi
  have hc' : 20 * (hi : ℝ) ^ 2 <
      20 * (hi : ℝ) * slo + 26 * d * hi + 10 * d ^ 2 := by
    unfold check at hc
    dsimp only [d]
    exact_mod_cast hc
  have hr : L ≤ (hi : ℝ) / d := (le_div_iff₀ hd).mpr (by nlinarith [hhi])
  have hsr : (slo : ℝ) / d ≤ S := (div_le_iff₀ hd).mpr (by nlinarith [hslo])
  have hq : (hi : ℝ) / d - 1.3 - (slo : ℝ) / d < d / (2 * hi) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * hi)]
    apply (mul_lt_mul_iff_right₀ hd).mp
    have heq : d * (((hi : ℝ) / d - 1.3 - (slo : ℝ) / d) * (2 * hi)) =
        2 * (hi : ℝ) ^ 2 - 2.6 * d * hi - 2 * hi * slo := by
      field_simp [ne_of_gt hd]
      <;> ring
    rw [heq]
    nlinarith
  have hinv : d / (2 * (hi : ℝ)) ≤ 1 / (2 * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hhi]
  linarith

theorem Inv_step {n : ℕ} (hn : 1 ≤ n) {s : WS} (h : Inv n s)
    (hc : n < 2 ∨ check (s.Lhi + incrHi n) s.Slo) : Inv (n + 1) (step n s) := by
  obtain ⟨l1, l2, s1, hok⟩ := h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i1, i2⟩ := incr_bounds hn
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) =
      Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_mul hn0.ne' (by positivity)]
    congr 1
    push_cast
    field_simp
  let lo := s.Llo + incrLo n
  let hi := s.Lhi + incrHi n
  have hlo : (lo : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [hlog]
    dsimp [lo]
    push_cast
    linarith
  have hhi : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ (hi : ℝ) := by
    rw [hlog]
    dsimp [hi]
    push_cast
    linarith
  have hsum : Sp (n + 1) = Sp n +
      if (n + 1).Prime then Real.log (n + 1) / (n + 1) else 0 := by
    rw [Sp, Sp, sum_Icc_succ_top (by omega)]
    push_cast
    rfl
  refine ⟨hlo, hhi, ?_, ?_⟩
  · change ((s.Slo + if isP (n + 1) then lo / (n + 1) else 0 : ℕ) : ℝ) ≤ _
    by_cases hp : isP (n + 1) = true
    · have hp' : (n + 1).Prime := (isP_iff _).mp hp
      rw [if_pos hp, hsum, if_pos hp', Nat.cast_add]
      have hf := (floor_div_bounds lo (n + 1) (by omega)).1
      have hdiv := div_le_div_of_nonneg_right hlo (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))
      push_cast at hf hdiv
      have heq : 10 ^ 30 * (Sp n + Real.log (n + 1) / (n + 1)) =
          10 ^ 30 * Sp n + 10 ^ 30 * Real.log (n + 1) / (n + 1) := by ring
      rw [heq]
      linarith
    · have hp' : ¬ (n + 1).Prime := fun h => hp ((isP_iff _).mpr h)
      simp only [if_neg hp, hsum, if_neg hp', add_zero]
      exact s1
  · intro N hN hNn
    rcases Nat.lt_or_ge N n with hlt | hge
    · exact hok N hN hlt
    · have heq : N = n := by omega
      subst N
      rcases hc with hsmall | hc
      · omega
      · have hL : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
        unfold Ok
        apply check_sound hL (hi := hi) (slo := s.Slo)
        · simpa only [Nat.cast_add, Nat.cast_one] using hhi
        · exact s1
        · exact hc

theorem walk_spec : ∀ (len n : ℕ) (s s' : WS), 1 ≤ n → Inv n s →
    walk n len s = some s' → Inv (n + len) s' := by
  intro len
  induction len with
  | zero =>
    intro n s s' hn h hw
    simp only [walk, Option.some.injEq] at hw
    subst hw
    simpa using h
  | succ len ih =>
    intro n s s' hn h hw
    rw [walk] at hw
    split_ifs at hw with hc
    rw [show n + (len + 1) = n + 1 + len by ring]
    exact ih (n + 1) _ _ (by omega) (Inv_step hn h hc.2) hw

theorem Inv_one : Inv 1 ⟨0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · have hSp : (0 : ℝ) ≤ Sp 1 := by
      unfold Sp
      apply Finset.sum_nonneg
      intro p hp
      split_ifs
      · exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
      · exact le_rfl
    simpa only [Nat.cast_zero] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10 ^ 30) hSp)
  · intro N hN hN1
    omega

theorem mertens_lower_le_two {x : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) :
    Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x := by
  have hlog := Real.log_lt_sub_one_of_pos (by linarith : 0 < x) (by linarith : x ≠ 1)
  have he := mertensE_lt_neg_thirteen_tenths
  have hl : 0 < Real.log x := Real.log_pos hx
  have hp : 0 < 1 / (2 * Real.log x) := by positivity
  have hs : 0 ≤ primeWeightedSum x := by
    unfold primeWeightedSum
    exact Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  linarith

/-- A completed natural walk covers every real point, including prime jumps. -/
theorem mertens_lower_of_Inv {N : ℕ} {s : WS} (h : Inv N s)
    {x : ℝ} (hx : 1 < x) (hxN : x < N) :
    Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x := by
  by_cases hx2 : x ≤ 2
  · exact mertens_lower_le_two hx hx2
  · have hx0 : 0 ≤ x := by linarith
    have hn2 : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by norm_num; linarith)
    have hnN : ⌊x⌋₊ < N := (Nat.floor_lt hx0).mpr hxN
    have hok := h.2.2.2 ⌊x⌋₊ hn2 hnN
    apply mertens_lower_of_block (a := (⌊x⌋₊ : ℝ)) (b := (⌊x⌋₊ : ℝ) + 1)
    · exact_mod_cast (show 1 < ⌊x⌋₊ by omega)
    · exact Nat.floor_le hx0
    · exact (Nat.lt_floor_add_one x).le
    · simpa only [Ok, Sp_eq_primeWeightedSum] using hok

end TernaryGoldbach.RSBounds.MertensFiniteWalk
