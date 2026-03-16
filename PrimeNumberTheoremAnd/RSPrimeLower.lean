import PrimeNumberTheoremAnd.Dusart

open Real Chebyshev Nat

set_option linter.style.nativeDecide false

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
  · exact nth_prime_gt_bound 2 3 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 3 5 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 4 7 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 5 11 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 6 13 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 7 17 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 8 19 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 9 23 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 10 29 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 11 31 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 12 37 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 13 41 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 14 43 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 15 47 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 16 53 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 17 59 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 18 61 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 19 67 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 20 71 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 21 73 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 22 79 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 23 83 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 24 89 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 25 97 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 26 101 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 27 103 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 28 107 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 29 109 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 30 113 (by native_decide) (by interval_auto)
  · exact nth_prime_gt_bound 31 127 (by native_decide) (by interval_auto)

lemma pi_nth_prime' (n : ℕ) (hn : n ≥ 1) :
    pi (nth_prime' n) = n := by
      have h_pi_eq : pi (nth_prime' n) = Nat.primeCounting (nth_prime' n) := by
        unfold pi; norm_num;
      have h_prime_counting : Nat.primeCounting (nth_prime' n) = Nat.count Nat.Prime (nth_prime' n + 1) :=
        add_zero (List.countP.go (fun b ↦ decide (Nat.Prime b)) (List.range (nth_prime' n + 1)) 0)
      have h_count : Nat.count Nat.Prime (nth_prime' n) = n - 1 := by
        convert Nat.count_nth_of_infinite ( Nat.infinite_setOf_prime ) ( n - 1 ) using 1;
      rcases n <;> simp_all +decide [ Nat.count_succ ]

lemma p_n_lower_large (n : ℕ) (hn : n ≥ 32) :
    (nth_prime' n : ℝ) > n * (Real.log n + Real.log (Real.log n) - 3 / 2) := by
      have h_step5 : (nth_prime' n : ℝ) ≥ n * (Real.log (nth_prime' n) - 1.112) := by
        have h_pi_le : (n : ℝ) ≤ (nth_prime' n) / (Real.log (nth_prime' n) - 1.112) := by
          have h_pi_le : pi (nth_prime' n) ≤ (nth_prime' n : ℝ) / (Real.log (nth_prime' n) - 1.112) := by
            convert Dusart.corollary_5_3_b _ using 1;
            have h_step1 : (nth_prime' n : ℝ) ≥ n + 1 := by
              norm_cast
              have h_step1 : ∀ n ≥ 1, nth_prime' n ≥ n + 1 := by
                intro n hn
                induction' n, hn using Nat.le_induction with n ih
                generalize_proofs at *; (
                exact Nat.Prime.two_le ( Nat.prime_nth_prime 0 ) |> Nat.succ_le_of_lt |> Nat.le_trans <| Nat.le_refl _;);
                exact Nat.succ_le_of_lt ( lt_of_le_of_lt ‹_› ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( Nat.pred_lt ( ne_bot_of_gt ih ) ) ) )
              exact h_step1 n (by linarith)
            generalize_proofs at *; (
            have h_exp_approx : Real.exp 1.112 < 33 := by
              rw [ ← Real.log_lt_log_iff ( by positivity ) ] <;> norm_num [ Real.log_exp ];
              rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
              have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 139 = ( Real.exp 1 ) ^ 139 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
            generalize_proofs at *; (
            linarith [ show ( n : ℝ ) ≥ 32 by norm_cast ]));
          convert h_pi_le using 1;
          exact_mod_cast Eq.symm ( pi_nth_prime' n ( by linarith ) );
        rwa [ le_div_iff₀ ( sub_pos.mpr <| by
          contrapose! h_pi_le;
          exact lt_of_le_of_lt ( div_nonpos_of_nonneg_of_nonpos ( Nat.cast_nonneg _ ) ( sub_nonpos.mpr h_pi_le ) ) ( by positivity ) ) ] at h_pi_le
      have h_step6 : Real.log (nth_prime' n) ≥ Real.log n + Real.log (Real.log n - 1.112) := by
        have h_step6 : (nth_prime' n : ℝ) ≥ n * (Real.log n - 1.112) := by
          refine le_trans ?_ h_step5
          generalize_proofs at *; (
          gcongr;
          refine' Nat.le_induction _ _ n ( show n ≥ 1 from by linarith ) <;> intros <;> simp_all +decide ; (
                                            exact Nat.Prime.pos ( Nat.prime_nth_prime 0 ) |> Nat.one_le_of_lt;);
          exact Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( by omega ) |> lt_of_le_of_lt ( by omega ) ;)
        have h_step7 : Real.log (nth_prime' n) ≥ Real.log (n * (Real.log n - 1.112)) := by
          apply Real.log_le_log; exact (by
          have h_step7 : Real.log n > 1.112 := by
            have h_step7 : Real.log 32 > 1.112 := by
              rw [ show ( 32 : ℝ ) = 2 ^ 5 by norm_num, Real.log_pow ] ; norm_num ; have := Real.log_two_gt_d9 ; norm_num at * ; linarith [ Real.log_le_log ( by norm_num ) ( by norm_num : ( 2 : ℝ ) ≤ 32 ) ] ;
            exact h_step7.trans_le ( Real.log_le_log ( by norm_num ) ( mod_cast hn ) ) |> lt_of_lt_of_le <| le_rfl;
          exact mul_pos (by positivity) (sub_pos.mpr h_step7)); exact h_step6;
        have h_step8 : Real.log (n * (Real.log n - 1.112)) = Real.log n + Real.log (Real.log n - 1.112) := by
          rw [ Real.log_mul ] <;> norm_num ; aesop;
          have h_log_n_ge_log_32 : Real.log n ≥ Real.log 32 := by
            exact Real.log_le_log ( by norm_num ) ( by norm_cast );
          rw [ show ( 32 : ℝ ) = 2 ^ 5 by norm_num, Real.log_pow ] at h_log_n_ge_log_32 ; norm_num at * ; linarith [ Real.log_two_gt_d9 ] ;
        linarith [h_step7, h_step8]
      have h_step7 : Real.log (Real.log n - 1.112) > 0.85 := by
        have h_log_n_ge_log_32 : Real.log n ≥ Real.log 32 := by
          exact Real.log_le_log ( by norm_num ) ( by norm_cast )
        have h_log_32_gt_3_465 : Real.log 32 > 3.465 := by
          rw [ show ( 32 : ℝ ) = 2 ^ 5 by norm_num, Real.log_pow ] ; norm_num ; have := Real.log_two_gt_d9 ; norm_num at this ; linarith;
        have h_log_32_minus_1_112_gt_2_353 : Real.log 32 - 1.112 > 2.353 := by
          linarith [ show ( 3.465 : ℝ ) = 3.465 by norm_num ] ;
        have h_log_2_353_gt_0_85 : Real.log 2.353 > 0.85 := by
          norm_num [ Real.lt_log_iff_exp_lt ] at *;
          have h_exp : Real.exp 17 < (2353 / 1000) ^ 20 := by
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 17 = ( Real.exp 1 ) ^ 17 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
          contrapose! h_exp; rw [ show Real.exp 17 = ( Real.exp ( 17 / 20 ) ) ^ 20 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact pow_le_pow_left₀ ( by positivity ) h_exp 20;
        have h_log_log_n_minus_1_112_gt_0_85 : Real.log (Real.log n - 1.112) > 0.85 := by
          exact h_log_2_353_gt_0_85.trans_le ( Real.log_le_log ( by norm_num ) ( by linarith ) ) ;
        exact h_log_log_n_minus_1_112_gt_0_85.trans_le' (by norm_num)
      have h_step8 : (nth_prime' n : ℝ) ≥ n * (Real.log n + 0.85 - 1.112) := by
        exact le_trans ( mul_le_mul_of_nonneg_left ( by linarith ) ( Nat.cast_nonneg _ ) ) h_step5
      have h_step9 : Real.log n - 0.262 ≥ Real.log 32 - 0.262 := by
        exact sub_le_sub_right ( Real.log_le_log ( by norm_num ) ( by norm_cast ) ) _
      have h_step10 : Real.log 32 - 0.262 > 3.2 := by
        rw [ show ( 32 : ℝ ) = 2 ^ 5 by norm_num, Real.log_pow ] ; norm_num ; have := Real.log_two_gt_d9 ; norm_num at this ; linarith;
      have h_step11 : (nth_prime' n : ℝ) ≥ n * 3.2 := by
        exact le_trans ( mul_le_mul_of_nonneg_left ( by linarith ) ( Nat.cast_nonneg _ ) ) h_step8
      have h_step12 : Real.log (nth_prime' n) > Real.log n + Real.log (Real.log n) := by
        have h_step12 : (nth_prime' n : ℝ) > n * Real.log n := by
          have h_step12 : Real.log (nth_prime' n) > Real.log n + 1.16 := by
            have h_step12 : Real.log (nth_prime' n) ≥ Real.log n + Real.log (3.2) := by
              rw [ ← Real.log_mul ( by positivity ) ( by positivity ) ] ; exact Real.log_le_log ( by positivity ) ( by linarith ) ;
            have h_step13 : Real.log (3.2) > 1.16 := by
              norm_num [ Real.lt_log_iff_exp_lt ] at *;
              have h_exp : Real.exp 29 < (16 / 5) ^ 25 := by
                have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 29 = ( Real.exp 1 ) ^ 29 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
              generalize_proofs at *; (
              contrapose! h_exp; rw [ show Real.exp 29 = ( Real.exp ( 29 / 25 ) ) ^ 25 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact pow_le_pow_left₀ ( by positivity ) h_exp 25;) -- This contradicts our assumption that $Real.exp (29 / 25) \geq 16 / 5$. Hence, $Real.exp (29 / 25) < 16 / 5$.
            linarith [h_step12, h_step13]
          have h_step13 : (nth_prime' n : ℝ) ≥ n * (Real.log n + 1.16 - 1.112) := by
            exact le_trans ( mul_le_mul_of_nonneg_left ( by linarith ) ( Nat.cast_nonneg _ ) ) h_step5 |> le_trans <| by norm_num;
          have h_step14 : (nth_prime' n : ℝ) > n * Real.log n := by
            linarith [ show ( n : ℝ ) ≥ 32 by norm_cast ]
          exact h_step14;
        rw [ ← Real.log_mul ( by positivity ) ( by exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith ) ] ; exact Real.log_lt_log ( by exact mul_pos ( by positivity ) <| Real.log_pos <| by norm_cast; linarith ) h_step12;
      have h_step13 : (nth_prime' n : ℝ) > n * (Real.log n + Real.log (Real.log n) - 3 / 2) := by
        nlinarith [ show ( n : ℝ ) ≥ 32 by norm_cast ] ;
      exact h_step13

end RS_prime_helper
