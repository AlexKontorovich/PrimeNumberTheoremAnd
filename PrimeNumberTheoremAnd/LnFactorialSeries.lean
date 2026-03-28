import Mathlib

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false

/-!
Upper and lower bounds on the series S = Σₙ (log 2)^(n+1) / ((n+1) · (n+1)!)

# Key theorems

- hs_lo : (0.834438 : ℝ) ≤ ∑' n : ℕ, (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial)
- hs_hi : ∑' n : ℕ, (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) ≤ 0.834462

# Notes

Lower bound (hs_lo): 0.834438 ≤ S

  Strategy: partial sum underestimates the series.

  Since every term is non-negative, the partial sum of the first 8 terms is ≤ the full series (Summable.sum_le_tsum). Then norm_num evaluates the finite sum symbolically in
  terms of powers of log 2, and nlinarith closes the gap using log 2 > 0.6931471803 (from mathlib's Real.log_two_gt_d9) together with positivity of (log 2)^k for k = 2..6.

Upper bound (hs_hi): S ≤ 0.834462

  Strategy: partial sum + geometric tail bound.

  This is harder because you need to bound the series from above. The proof splits the series into two pieces:

  1. First 10 terms: a computable finite sum.
  2. Tail from n = 11 onward: bounded in two steps:
    - Drop the (n+11) factor in the denominator (since 1/(n·n!) ≤ 1/n!), loosening the tail to Σₙ (log 2)^(n+11) / (n+11)!.
    - Factor out (log 2)^11 / 11! and bound the remaining sum Σₙ (log 2)^n / n! by recognizing it equals exp(log 2) = 2 (the full exponential series).

  So the tail is bounded by (log 2)^11 / 11! · 2, which is tiny (~3.5 × 10⁻⁹). The finite sum plus this tail is then shown to be ≤ 0.834462 via nlinarith using log 2 <
  0.6931471806 (Real.log_two_lt_d9) and powers of log 2.

-/
open Real Finset BigOperators
noncomputable def seriesTerm (n : ℕ) : ℝ :=
  (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial)
lemma log_two_pos : (0 : ℝ) < Real.log 2 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 2)
lemma log_two_nonneg : (0 : ℝ) ≤ Real.log 2 := le_of_lt log_two_pos
lemma seriesTerm_nonneg (n : ℕ) : 0 ≤ seriesTerm n := by
  unfold seriesTerm
  apply div_nonneg
  · exact pow_nonneg log_two_nonneg _
  · apply mul_nonneg
    · positivity
    · positivity
lemma summable_seriesTerm : Summable seriesTerm := by
  refine .of_nonneg_of_le ( fun n => ?_) ( fun n => ?_ ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_pow_div_factorial <| Real.log 2 );
  · exact div_nonneg ( pow_nonneg ( Real.log_nonneg one_le_two ) _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) );
  · exact div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( mod_cast Nat.le_mul_of_pos_left _ ( Nat.succ_pos _ ) )

lemma hs_lo : (0.834438 : ℝ) ≤
    ∑' n : ℕ, (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
  have h_sum_le_tsum : (∑ n ∈ Finset.range 8, (Real.log 2) ^ (n + 1) / ((n + 1) * (n + 1).factorial)) ≤ ∑' n : ℕ, (Real.log 2) ^ (n + 1) / ((n + 1) * (n + 1).factorial) := by
    exact Summable.sum_le_tsum ( Finset.range 8 ) ( fun _ _ => div_nonneg ( by positivity ) ( by positivity ) ) ( by
      convert summable_seriesTerm using 1;
      exact funext fun n => by unfold seriesTerm; norm_cast; );
  norm_num [ Finset.sum_range_succ, Nat.factorial ] at * ; have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ pow_pos ( Real.log_pos one_lt_two ) 2, pow_pos ( Real.log_pos one_lt_two ) 3, pow_pos ( Real.log_pos one_lt_two ) 4, pow_pos ( Real.log_pos one_lt_two ) 5, pow_pos ( Real.log_pos one_lt_two ) 6 ] ;

set_option maxHeartbeats 800000 in
lemma hs_hi :
  ∑' n : ℕ, (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) ≤
    0.834462 := by
  by_contra h_contra;
  suffices h_simp : (∑' n : ℕ, (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial)) ≤ (∑ n ∈ Finset.range 10, (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial)) + (∑' n : ℕ, (Real.log 2) ^ (n + 11) / ((↑(n + 11) : ℝ) * ↑(n + 11).factorial)) by
    have h_tail : (∑' n : ℕ, (Real.log 2) ^ (n + 11) / ((↑(n + 11) : ℝ) * ↑(n + 11).factorial)) ≤ (∑' n : ℕ, (Real.log 2) ^ (n + 11) / (↑(n + 11).factorial)) := by
      refine Summable.tsum_le_tsum ?_ ?_ ?_;
      · exact fun n => by gcongr ; norm_cast ; nlinarith [ Nat.factorial_pos ( n + 11 ) ] ;
      · exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by exact div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) <| le_mul_of_one_le_left ( by positivity ) <| mod_cast Nat.le_add_left _ _ ) <| by simpa using summable_nat_add_iff 11 |>.2 <| Real.summable_pow_div_factorial _;
      · exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| add_left_injective _;
    have h_tail_further : (∑' n : ℕ, (Real.log 2) ^ (n + 11) / (↑(n + 11).factorial)) ≤ (Real.log 2) ^ 11 / (↑(11).factorial) * (∑' n : ℕ, (Real.log 2) ^ n / (↑(n).factorial)) := by
      rw [ ← tsum_mul_left ]
      refine Summable.tsum_le_tsum ?_ ?_ ?_
      · intro n
        norm_num [ pow_add, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Nat.factorial_succ ]
        ring_nf ; norm_num
        field_simp
        norm_cast; nlinarith only [ sq ( n ^ 5 ), sq ( n ^ 4 ), sq ( n ^ 3 ), sq ( n ^ 2 ) ]
      · exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| add_left_injective _
      · exact Summable.mul_left _ <| Real.summable_pow_div_factorial _
    have h_exp_series : (∑' n : ℕ, (Real.log 2) ^ n / (↑(n).factorial)) = Real.exp (Real.log 2) := by
      simp +decide [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ];
    norm_num [ Finset.sum_range_succ, Nat.factorial_succ ] at *;
    have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ Real.log_nonneg one_le_two, pow_pos ( Real.log_pos one_lt_two ) 2, pow_pos ( Real.log_pos one_lt_two ) 3, pow_pos ( Real.log_pos one_lt_two ) 4, pow_pos ( Real.log_pos one_lt_two ) 5, pow_pos ( Real.log_pos one_lt_two ) 6, pow_pos ( Real.log_pos one_lt_two ) 7, pow_pos ( Real.log_pos one_lt_two ) 8, pow_pos ( Real.log_pos one_lt_two ) 9, pow_pos ( Real.log_pos one_lt_two ) 10, pow_pos ( Real.log_pos one_lt_two ) 11, Real.exp_log zero_lt_two ] ;
  rw [ ← Summable.sum_add_tsum_nat_add ];
  exact ( by contrapose! h_contra; erw [ tsum_eq_zero_of_not_summable h_contra ] ; norm_num )
