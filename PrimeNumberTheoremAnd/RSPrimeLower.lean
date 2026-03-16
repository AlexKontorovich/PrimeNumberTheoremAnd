import PrimeNumberTheoremAnd.Dusart
import PrimeNumberTheoremAnd.PrimeTables
import PrimeNumberTheoremAnd.LogTables

open Real Chebyshev Nat

namespace RS_prime_helper

lemma count_prime_le_imp_le_nth (m k : ℕ) (h : Nat.count Nat.Prime m ≤ k) :
    m ≤ Nat.nth Nat.Prime k := by
  by_contra hlt; push_neg at hlt
  have hp := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime k + 1) = k + 1 := by
    rw [Nat.count_succ, if_pos hp, Nat.count_nth_of_infinite Nat.infinite_setOf_prime]
  linarith [h1 ▸ Nat.count_monotone Nat.Prime hlt]

lemma nth_prime_gt_bound (n m : ℕ)
    (hcount : Nat.count Nat.Prime m ≤ n - 1)
    (hbound : (n : ℝ) * (Real.log n + Real.log (Real.log n) - 3 / 2) < m) :
    (nth_prime' n : ℝ) > n * (Real.log n + Real.log (Real.log n) - 3 / 2) :=
  hbound.trans_le (by exact_mod_cast count_prime_le_imp_le_nth m (n - 1) hcount)

lemma p_n_lower_small (n : ℕ) (hn1 : n > 1) (hn2 : n ≤ 31) :
    (nth_prime' n : ℝ) > n * (Real.log n + Real.log (Real.log n) - 3 / 2) := by
  interval_cases n
  · exact nth_prime_gt_bound 2 3 count_prime_3_le_1 (by interval_auto)
  · exact nth_prime_gt_bound 3 5 count_prime_5_le_2 (by interval_auto)
  · exact nth_prime_gt_bound 4 7 count_prime_7_le_3 (by interval_auto)
  · exact nth_prime_gt_bound 5 11 count_prime_11_le_4 (by interval_auto)
  · exact nth_prime_gt_bound 6 13 count_prime_13_le_5 (by interval_auto)
  · exact nth_prime_gt_bound 7 17 count_prime_17_le_6 (by interval_auto)
  · exact nth_prime_gt_bound 8 19 count_prime_19_le_7 (by interval_auto)
  · exact nth_prime_gt_bound 9 23 count_prime_23_le_8 (by interval_auto)
  · exact nth_prime_gt_bound 10 29 count_prime_29_le_9 (by interval_auto)
  · exact nth_prime_gt_bound 11 31 count_prime_31_le_10 (by interval_auto)
  · exact nth_prime_gt_bound 12 37 count_prime_37_le_11 (by interval_auto)
  · exact nth_prime_gt_bound 13 41 count_prime_41_le_12 (by interval_auto)
  · exact nth_prime_gt_bound 14 43 count_prime_43_le_13 (by interval_auto)
  · exact nth_prime_gt_bound 15 47 count_prime_47_le_14 (by interval_auto)
  · exact nth_prime_gt_bound 16 53 count_prime_53_le_15 (by interval_auto)
  · exact nth_prime_gt_bound 17 59 count_prime_59_le_16 (by interval_auto)
  · exact nth_prime_gt_bound 18 61 count_prime_61_le_17 (by interval_auto)
  · exact nth_prime_gt_bound 19 67 count_prime_67_le_18 (by interval_auto)
  · exact nth_prime_gt_bound 20 71 count_prime_71_le_19 (by interval_auto)
  · exact nth_prime_gt_bound 21 73 count_prime_73_le_20 (by interval_auto)
  · exact nth_prime_gt_bound 22 79 count_prime_79_le_21 (by interval_auto)
  · exact nth_prime_gt_bound 23 83 count_prime_83_le_22 (by interval_auto)
  · exact nth_prime_gt_bound 24 89 count_prime_89_le_23 (by interval_auto)
  · exact nth_prime_gt_bound 25 97 count_prime_97_le_24 (by interval_auto)
  · exact nth_prime_gt_bound 26 101 count_prime_101_le_25 (by interval_auto)
  · exact nth_prime_gt_bound 27 103 count_prime_103_le_26 (by interval_auto)
  · exact nth_prime_gt_bound 28 107 count_prime_107_le_27 (by interval_auto)
  · exact nth_prime_gt_bound 29 109 count_prime_109_le_28 (by interval_auto)
  · exact nth_prime_gt_bound 30 113 count_prime_113_le_29 (by interval_auto)
  · exact nth_prime_gt_bound 31 127 count_prime_127_le_30 (by interval_auto)

lemma pi_nth_prime' (n : ℕ) (hn : n ≥ 1) :
    pi (nth_prime' n) = n := by
  have h_pi_eq : pi (nth_prime' n) = Nat.primeCounting (nth_prime' n) := by norm_num [pi]
  have h_prime_counting : primeCounting (nth_prime' n) = count Nat.Prime (nth_prime' n + 1) :=
    add_zero (List.countP.go (fun b ↦ decide (Nat.Prime b)) (List.range (nth_prime' n + 1)) 0)
  have h_count : count Nat.Prime (nth_prime' n) = n - 1 := by
    convert count_nth_of_infinite (infinite_setOf_prime) (n - 1) using 1
  rcases n <;> simp_all [count_succ]

lemma p_n_lower_large (n : ℕ) (hn : n ≥ 32) :
    (nth_prime' n : ℝ) > n * (Real.log n + Real.log (Real.log n) - 3 / 2) := by
  have h_dusart : (nth_prime' n : ℝ) ≥ n * (Real.log (nth_prime' n) - 1.112) := by
    have h_pi_le : (n : ℝ) ≤ (nth_prime' n) / (Real.log (nth_prime' n) - 1.112) := by
      have h_pi_le :
          pi (nth_prime' n) ≤ (nth_prime' n : ℝ) / (Real.log (nth_prime' n) - 1.112) := by
        convert Dusart.corollary_5_3_b _ using 1
        have h_step1 : (nth_prime' n : ℝ) ≥ n + 1 := by
          norm_cast
          have h_step1 : ∀ n ≥ 1, nth_prime' n ≥ n + 1 := by
            intro n hn
            induction n, hn using Nat.le_induction with
            | base =>
              exact Prime.two_le (prime_nth_prime 0) |> succ_le_of_lt |> le_trans <| le_refl _
            | succ n _ ih =>
              exact succ_le_of_lt (lt_of_le_of_lt ih (nth_strictMono (infinite_setOf_prime) (pred_lt (by positivity))))
          exact h_step1 n (by linarith)
        generalize_proofs at *
        have h_exp_approx : Real.exp 1.112 < 33 := by linarith [LogTables.exp_1_112_lt]
        linarith [show (n : ℝ) ≥ 32 by norm_cast]
      convert h_pi_le using 1
      exact_mod_cast Eq.symm (pi_nth_prime' n (by linarith))
    rwa [le_div_iff₀ (sub_pos.mpr <| by
      contrapose! h_pi_le
      exact lt_of_le_of_lt
        (div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr h_pi_le))
        (by positivity))] at h_pi_le
  have h_log_pn :
      Real.log (nth_prime' n) ≥ Real.log n + Real.log (Real.log n - 1.112) := by
    have h_pn_ge : (nth_prime' n : ℝ) ≥ n * (Real.log n - 1.112) := by
      refine le_trans ?_ h_dusart
      generalize_proofs at *; (
      gcongr;
      refine Nat.le_induction ?_ ?_ n (show n ≥ 1 from by linarith) <;>
        intros <;> simp_all only [nth_prime']
      · exact Prime.pos (prime_nth_prime 0) |> one_le_of_lt
      · exact nth_strictMono (infinite_setOf_prime) (by omega) |> lt_of_le_of_lt (by omega))
    have h_log_gt : Real.log n > 1.112 := by
      have : Real.log 32 > 1.112 := by linarith [LogTables.log_32_gt]
      exact this.trans_le (Real.log_le_log (by norm_num) (mod_cast hn)) |> lt_of_lt_of_le <| le_rfl
    have h_log_pn_ge :
        Real.log (nth_prime' n) ≥ Real.log (n * (Real.log n - 1.112)) :=
      Real.log_le_log (mul_pos (by positivity) (sub_pos.mpr h_log_gt)) h_pn_ge
    have h_log_split :
        Real.log (n * (Real.log n - 1.112)) =
          Real.log n + Real.log (Real.log n - 1.112) := by
      rw [Real.log_mul] <;> norm_num
      · aesop
      · linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 32) (by norm_cast),
          LogTables.log_32_gt]
    linarith [h_log_pn_ge, h_log_split]
  have h_loglog : Real.log (Real.log n - 1.112) > 0.85 := by
    have h_log_n_ge : Real.log n ≥ Real.log 32 :=
      Real.log_le_log (by norm_num) (by norm_cast)
    have h_log_32 : Real.log 32 > 3.465 := by linarith [LogTables.log_32_gt]
    have h_log_2_353 : log 2.353 > 0.85 := by linarith [LogTables.log_2_353_gt]
    exact (h_log_2_353.trans_le
      (Real.log_le_log (by norm_num) (by linarith))).trans_le' (by norm_num)
  have h_pn_ge2 : (nth_prime' n : ℝ) ≥ n * (Real.log n + 0.85 - 1.112) :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)) h_dusart
  have h_log_32_bound : Real.log 32 - 0.262 > 3.2 := by linarith [LogTables.log_32_gt]
  have h_pn_ge3 : (nth_prime' n : ℝ) ≥ n * 3.2 := by
    have : Real.log n - 0.262 ≥ Real.log 32 - 0.262 :=
      sub_le_sub_right (Real.log_le_log (by norm_num) (by norm_cast)) _
    exact le_trans (mul_le_mul_of_nonneg_left (by linarith) (cast_nonneg _)) h_pn_ge2
  have h_pn_gt_nlogn : (nth_prime' n : ℝ) > n * Real.log n := by
    have h_log_pn_gt : Real.log (nth_prime' n) > Real.log n + 1.16 := by
      have : Real.log (nth_prime' n) ≥ Real.log n + Real.log (3.2) := by
        rw [← log_mul (by positivity) (by positivity)]
        exact log_le_log (by positivity) (by linarith)
      have : log (3.2) > 1.16 := by linarith [LogTables.log_3_2_gt]
      linarith
    have : (nth_prime' n : ℝ) ≥ n * (Real.log n + 1.16 - 1.112) :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (cast_nonneg _)) h_dusart
    linarith [show (n : ℝ) ≥ 32 by norm_cast]
  have h_log_sum : Real.log (nth_prime' n) > Real.log n + log (log n) := by
    rw [← log_mul (by positivity) (by exact ne_of_gt <| log_pos <| by norm_cast; linarith)]
    exact log_lt_log (by exact mul_pos (by positivity) <| log_pos <| by norm_cast; linarith) h_pn_gt_nlogn
  nlinarith [show (n : ℝ) ≥ 32 by norm_cast]

end RS_prime_helper
