import RSBounds.PsiSieveBlockReduction
import RSBounds.PsiFinite.LogBounds

/-!
# One block of the walk

`Encl A s` says that `s` encloses `D ψ(A)` and `D log A`. `blockStep_sound`:
if `blockStep num den A h c ppLo ppHi s = some s'`, `Encl A s` holds, `c` is the
number of primes in `(A, A+h]` and `ppLo ≤ D Σ Λ(m) ≤ ppHi` over the proper prime
powers `m` there, then `Encl (A+h) s'` holds and
`|ψ x - x| ≤ (num/den) √x` on `[A, A+h]`.
-/

namespace PsiFinite

open Real Finset
open scoped ArithmeticFunction.vonMangoldt

/-- `s` encloses `D ψ(A)` and `D log A`. -/
def Encl (A : ℕ) (s : St) : Prop :=
  (s.plo : ℝ) ≤ D * Chebyshev.psi A ∧ D * Chebyshev.psi A ≤ s.phi ∧
    (s.llo : ℝ) ≤ D * Real.log A ∧ D * Real.log A ≤ s.lhi

theorem psi_natCast (n : ℕ) : Chebyshev.psi n = ∑ m ∈ Ioc 0 n, (Λ m : ℝ) := by
  simp [Chebyshev.psi]

theorem psi_add_nat (A n : ℕ) :
    Chebyshev.psi ((A + n : ℕ) : ℝ) = Chebyshev.psi A + ∑ m ∈ Ioc A (A + n), (Λ m : ℝ) := by
  rw [psi_natCast, psi_natCast, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le A) (Nat.le_add_right A n)]

/-- `Λ` splits into its prime part and its proper-prime-power part. -/
theorem vonMangoldt_split (m : ℕ) :
    (Λ m : ℝ) = (if m.Prime then Real.log m else 0) +
      (if IsPrimePow m ∧ ¬ m.Prime then (Λ m : ℝ) else 0) := by
  by_cases hp : m.Prime
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · by_cases hpp : IsPrimePow m
    · simp [hp, hpp]
    · simp [hp, hpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]

/-- The prime part of a block of even left end, as a sum over the odd numbers. -/
theorem prime_part_block (A : ℕ) (hA : Even A) (hA2 : 2 ≤ A) : ∀ W : ℕ,
    ∑ m ∈ Ioc A (A + 2 * W), (if m.Prime then Real.log m else 0) =
      ∑ j ∈ range W, (if (A + 1 + 2 * j).Prime then Real.log ((A + 1 + 2 * j : ℕ) : ℝ) else 0) := by
  intro W
  induction W with
  | zero => simp
  | succ W ih =>
    rw [show A + 2 * (W + 1) = (A + 2 * W + 1) + 1 by ring, Finset.sum_Ioc_succ_top (by omega),
      Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ]
    have hev : ¬ (A + 2 * W + 1 + 1).Prime := by
      intro hp
      rcases hp.eq_two_or_odd with h | h
      · omega
      · obtain ⟨k, hk⟩ := hA; omega
    rw [ite_eq_right hev, add_zero, show A + 2 * W + 1 = A + 1 + 2 * W by ring]

theorem prime_part_bounds (A W : ℕ) (hA : 1 ≤ A) :
    (∑ j ∈ range W, (if (A + 1 + 2 * j).Prime then (1 : ℝ) else 0)) * Real.log A ≤
      ∑ j ∈ range W, (if (A + 1 + 2 * j).Prime then Real.log ((A + 1 + 2 * j : ℕ) : ℝ) else 0) ∧
    ∑ j ∈ range W, (if (A + 1 + 2 * j).Prime then Real.log ((A + 1 + 2 * j : ℕ) : ℝ) else 0) ≤
      (∑ j ∈ range W, (if (A + 1 + 2 * j).Prime then (1 : ℝ) else 0)) * Real.log (A + 2 * W) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  rw [Finset.sum_mul, Finset.sum_mul]
  constructor
  · apply Finset.sum_le_sum; intro j hj
    split_ifs
    · rw [one_mul]; apply Real.log_le_log hA0; push_cast; linarith
    · simp
  · apply Finset.sum_le_sum; intro j hj
    have hj' := Finset.mem_range.mp hj
    split_ifs
    · rw [one_mul]; apply Real.log_le_log (by positivity); push_cast
      have : (j : ℝ) + 1 ≤ W := by exact_mod_cast hj'
      linarith
    · simp

/-- The guard is the integer form of `SignedEndpointSafe`. -/
theorem guardUp_safe {num den point up : ℕ} (h : guardUp num den point up = true) :
    TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.SignedEndpointSafe point D num den ((up : ℤ) - (point : ℤ) * D) := by
  unfold guardUp at h
  unfold TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.SignedEndpointSafe
  rcases Bool.or_eq_true_iff.mp h with h | h
  · left; have := Nat.le_of_ble_eq_true h; omega
  · by_cases hle : up ≤ point * D
    · left; omega
    · right
      have h' := Nat.le_of_ble_eq_true h
      have habs : ((up : ℤ) - (point : ℤ) * D).natAbs = up - point * D := by omega
      rw [habs]
      calc (up - point * D) ^ 2 * den ^ 2 = (up - point * D) * (up - point * D) * (den * den) := by ring
        _ ≤ num * num * point * (D * D) := h'
        _ = num ^ 2 * point * D ^ 2 := by ring

theorem guardLow_safe {num den point low : ℕ} (h : guardLow num den point low = true) :
    TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.SignedEndpointSafe point D num den ((point : ℤ) * D - low) := by
  unfold guardLow at h
  unfold TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.SignedEndpointSafe
  rcases Bool.or_eq_true_iff.mp h with h | h
  · left; have := Nat.le_of_ble_eq_true h; omega
  · by_cases hle : point * D ≤ low
    · left; omega
    · right
      have h' := Nat.le_of_ble_eq_true h
      have habs : ((point : ℤ) * D - low).natAbs = point * D - low := by omega
      rw [habs]
      calc (point * D - low) ^ 2 * den ^ 2 = (point * D - low) * (point * D - low) * (den * den) := by
            ring
        _ ≤ num * num * point * (D * D) := h'
        _ = num ^ 2 * point * D ^ 2 := by ring

/-- Soundness of one block. -/
theorem blockStep_sound {num den A W c ppLo ppHi : ℕ} {s s' : St}
    (hnum : 0 < num) (hden : 0 < den) (hA : Even A) (hA2 : 2 ≤ A) (hW : 1 ≤ W)
    (hstep : blockStep num den A (2 * W) c ppLo ppHi s = some s') (hs : Encl A s)
    (hc : (c : ℝ) = ∑ j ∈ range W, (if (A + 1 + 2 * j).Prime then (1 : ℝ) else 0))
    (hppLo : (ppLo : ℝ) ≤ D * ∑ m ∈ Ioc A (A + 2 * W),
      (if IsPrimePow m ∧ ¬ m.Prime then (Λ m : ℝ) else 0))
    (hppHi : D * ∑ m ∈ Ioc A (A + 2 * W),
      (if IsPrimePow m ∧ ¬ m.Prime then (Λ m : ℝ) else 0) ≤ ppHi) :
    Encl (A + 2 * W) s' ∧ ∀ x : ℝ, (A : ℝ) ≤ x → x ≤ ((A + 2 * W : ℕ) : ℝ) →
      |Chebyshev.psi x - x| ≤ ((num : ℝ) / den) * Real.sqrt x := by
  unfold blockStep at hstep
  simp only at hstep
  set lhi' := s.lhi + logIncHi A (2 * W)
  set plo' := s.plo + c * s.llo + ppLo
  set phi' := s.phi + c * lhi' + ppHi
  cases hg : (guardUp num den A phi' && guardLow num den (A + 2 * W) s.plo) with
  | false => rw [hg] at hstep; simp at hstep
  | true =>
  rw [hg] at hstep
  simp only [Bool.cond_true, Option.some.injEq] at hstep
  subst hstep
  obtain ⟨hgu, hgl⟩ := Bool.and_eq_true_iff.mp hg
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hA1 : 1 ≤ A := by omega
  obtain ⟨li1, li2⟩ := logInc_bounds (h := 2 * W) hA1 (by omega)
  have hD := D_pos
  set PP := ∑ m ∈ Ioc A (A + 2 * W), (if IsPrimePow m ∧ ¬ m.Prime then (Λ m : ℝ) else 0)
  set PR := ∑ j ∈ range W, (if (A + 1 + 2 * j).Prime then Real.log ((A + 1 + 2 * j : ℕ) : ℝ) else 0)
  have hpsi : Chebyshev.psi ((A + 2 * W : ℕ) : ℝ) = Chebyshev.psi A + PR + PP := by
    rw [psi_add_nat]
    have : ∑ m ∈ Ioc A (A + 2 * W), (Λ m : ℝ) =
        ∑ m ∈ Ioc A (A + 2 * W), (if m.Prime then Real.log m else 0) + PP := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun m _ => vonMangoldt_split m
    rw [this, prime_part_block A hA hA2 W]; ring
  obtain ⟨pb1, pb2⟩ := prime_part_bounds A W hA1
  rw [← hc] at pb1 pb2
  have hcast : ((A + 2 * W : ℕ) : ℝ) = (A : ℝ) + ((2 * W : ℕ) : ℝ) := by push_cast; ring
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hlogA : Real.log ((A + 2 * W : ℕ) : ℝ) = Real.log A + (Real.log (A + ((2 * W : ℕ) : ℝ)) -
      Real.log A) := by rw [hcast]; ring
  -- the new enclosures
  have hPlo : (plo' : ℝ) ≤ D * Chebyshev.psi ((A + 2 * W : ℕ) : ℝ) := by
    rw [hpsi]
    have : (c : ℝ) * s.llo ≤ D * PR := by
      calc (c : ℝ) * s.llo ≤ c * (D * Real.log A) := mul_le_mul_of_nonneg_left h3 hc0
        _ = D * (c * Real.log A) := by ring
        _ ≤ D * PR := mul_le_mul_of_nonneg_left pb1 hD.le
    simp only [plo']; push_cast; nlinarith
  have hPhi : D * Chebyshev.psi ((A + 2 * W : ℕ) : ℝ) ≤ phi' := by
    rw [hpsi]
    have hl : D * Real.log ((A + 2 * W : ℕ) : ℝ) ≤ lhi' := by
      rw [hlogA]; simp only [lhi']; push_cast; push_cast at li2; linarith
    have : D * PR ≤ (c : ℝ) * lhi' := by
      calc D * PR ≤ D * (c * Real.log (A + 2 * W)) := mul_le_mul_of_nonneg_left pb2 hD.le
        _ = c * (D * Real.log ((A + 2 * W : ℕ) : ℝ)) := by push_cast; ring
        _ ≤ c * lhi' := mul_le_mul_of_nonneg_left hl hc0
    simp only [phi']; push_cast; nlinarith
  refine ⟨⟨hPlo, hPhi, ?_, ?_⟩, ?_⟩
  · show ((s.llo + logIncLo A (2 * W) : ℕ) : ℝ) ≤ _
    rw [hlogA]; push_cast; push_cast at li1; linarith
  · show _ ≤ ((s.lhi + logIncHi A (2 * W) : ℕ) : ℝ)
    rw [hlogA]; push_cast; push_cast at li2; linarith
  · intro x hx1 hx2
    have hDn : 0 < D := by norm_num [D]
    refine TernaryGoldbach.RSBounds.PsiSieveBlockReduction.psi_block_abs_le_of_guards (lowerAtA := s.plo) (upperAtB := phi')
      (by omega) hDn hnum hden hx1 hx2 ?_ ?_ (guardUp_safe hgu) (guardLow_safe hgl)
    · rw [div_le_iff₀ hD]; linarith
    · rw [le_div_iff₀ hD]; linarith

end PsiFinite
