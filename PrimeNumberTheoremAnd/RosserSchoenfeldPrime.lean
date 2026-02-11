import Architect
import Mathlib.MeasureTheory.Measure.Stieltjes
import PrimeNumberTheoremAnd.MediumPNT
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime_tables

blueprint_comment /--
\section{The prime number bounds of Rosser and Schoenfeld}\label{rs-prime-sec}
-/

blueprint_comment /--
In this section we formalize the prime number bounds of Rosser and Schoenfeld \cite{rs-prime}.

TODO: Add more results and proofs here, and reorganize the blueprint
-/

namespace RS_prime

open scoped Topology
open Chebyshev Finset Nat Real MeasureTheory Filter Asymptotics

theorem pntBigO : (θ - id) =O[atTop] fun (x : ℝ) ↦ x / log x ^ 2 := by
  obtain ⟨c, hc⟩ := MediumPNT
  have hl : (ψ - id) =O[atTop] fun (x : ℝ) ↦ x / log x ^ 2 := by
    have h_exp : (fun x : ℝ => exp (-c * (log x) ^ (1 / 10 : ℝ))) =O[atTop]
      (fun x : ℝ => (log x) ^ (-2 : ℝ)) := by
      -- This lemma is autoformalized by Aristotle.
      have h_exp : Tendsto (fun x : ℝ => exp (-c * (log x) ^ (1 / 10 : ℝ)) * (log x) ^ 2)
        atTop (𝓝 0) := by
        suffices h_y : Tendsto (fun y : ℝ => exp (-c * y) * y ^ 20) atTop (nhds 0) by
          have h_subst : Tendsto (fun x : ℝ => exp (-c * (log x) ^ (1 / 10 : ℝ)) *
          ((log x) ^ (1 / 10 : ℝ)) ^ 20) atTop (𝓝 0) :=
          h_y.comp (tendsto_rpow_atTop (by norm_num) |> Tendsto.comp <| tendsto_log_atTop)
          refine h_subst.congr' ?_
          filter_upwards [eventually_gt_atTop 1] with x hx
          rw [← rpow_natCast, ← rpow_mul (log_nonneg hx.le)]
          norm_num
        suffices h_z : Tendsto (fun z : ℝ => exp (-z) * (z / c) ^ 20) atTop (nhds 0) by
          convert h_z.comp (tendsto_id.const_mul_atTop hc.1) using 2
          norm_num [hc.1.ne']
        convert (tendsto_pow_mul_exp_neg_atTop_nhds_zero 20).div_const (c ^ 20) using 2 <;> ring
      rw [isBigO_iff]
      obtain ⟨M, hM⟩ := eventually_atTop.mp (h_exp.eventually (Metric.ball_mem_nhds _ zero_lt_one))
      norm_cast
      norm_num
      refine ⟨1, Max.max M 2, fun x hx => ?_⟩
      rw [← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos <| log_pos <| by grind [le_max_right M 2])]
      have := abs_lt.mp (hM x <| le_trans (le_max_left M 2) hx)
      norm_num at *
      nlinarith
    refine hc.2.trans ?_
    convert (isBigO_refl (fun x : ℝ => x) atTop).mul h_exp using 2
    simp [field]
  have : θ - id = (ψ - id) + (θ - ψ) := by ring
  refine this ▸ hl.add (isBigO_iff.2 ⟨432, ?_⟩)
  filter_upwards [Ioi_mem_atTop 1] with x hx
  simp only [Pi.sub_apply, norm_eq_abs, norm_div, norm_pow, sq_abs, mul_div]
  have nonnegx : 0 ≤ x := by grind
  calc
  _ ≤ 2 * √x * log x := by rw [← neg_sub, abs_neg]; exact abs_psi_sub_theta_le_sqrt_mul_log hx.le
  _ ≤ _ := by
    rw [le_div_iff₀ (sq_pos_of_pos (log_pos hx)), mul_assoc, ← pow_succ' _ 2]
    simp only [reduceAdd]
    have : log x ^ 3 ≤ 216 * x ^ (1 / 2 : ℝ) := by
      have := rpow_le_rpow (log_nonneg hx.le) (log_le_rpow_div nonnegx
        (by grind : 0 < 1 / (6 : ℝ))) (by grind : 0 ≤ (3 : ℝ))
      simp only [rpow_ofNat, one_div, div_inv_eq_mul, mul_comm,
        mul_rpow (by grind : 0 ≤ (6 : ℝ)) (rpow_nonneg nonnegx _), ← rpow_mul nonnegx] at this
      norm_num at this
      exact this
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (by simp : 0 ≤ (2 : ℝ)) (by simp : 0 ≤ √x))
    rw [← sqrt_eq_rpow, mul_comm 216 √x, ← mul_assoc, mul_assoc 2 √x √x, mul_self_sqrt nonnegx,
      ← mul_comm 216, ← mul_assoc] at this
    nth_rewrite 3 [← abs_of_nonneg nonnegx] at this
    norm_num at this
    exact this

@[blueprint
  "rs-pnt"
  (title := "A medium version of the prime number theorem")
  (statement := /-- $\vartheta(x) = x + O( x / \log^2 x)$. -/)
  (proof := /-- This in principle follows by establishing an analogue of Theorem \ref{chebyshev-asymptotic}, using mediumPNT in place of weakPNT. -/)
  (latexEnv := "theorem")
  (discussion := 597)]
theorem pnt : ∃ C ≥ 0, ∀ x ≥ 2, |θ x - x| ≤ C * x / log x ^ 2 := by
  obtain ⟨c, hc⟩ := isBigO_iff'.1 pntBigO
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc.2
  by_cases! hn : 2 ≤ N
  · refine ⟨max c (4 * (θ N + N)), le_max_of_le_left hc.1.le, fun x hx => ?_⟩
    by_cases! h : x ≤ N
    · suffices |θ x - x| * log x ^ 2 / x ≤ 4 * (θ N + N) from by
        rw [le_div_iff₀ (sq_pos_of_pos (log_pos (by linarith))), ← div_le_iff₀ (by linarith)]
        exact this.trans (le_max_right c (4 * (θ N + N)))
      have : |θ x - x| ≤ θ N + N := calc
        _ ≤ |θ x| + |x| := abs_sub _ _
        _ = θ x + x := by rw [abs_of_nonneg (theta_nonneg _), abs_of_nonneg (by linarith)]
        _ ≤ _ := by gcongr; exact theta_mono h
      calc
      _ ≤ (θ N + N) * log x ^ 2 / x := by gcongr
      _ ≤ (θ N + N) * (x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 / x := by
        gcongr
        · exact add_nonneg (theta_nonneg _) (by linarith)
        · exact log_nonneg (by linarith)
        · exact log_le_rpow_div (by linarith) (by linarith)
      _ = _ := by rw [← sqrt_eq_rpow, div_pow, sq_sqrt (by linarith)]; field_simp; ring
    · simpa [abs_of_nonneg (by grind : 0 ≤ x), mul_div] using (hN x h.le).trans <|
        mul_le_mul_of_nonneg_right (le_max_left c (4 * (θ N + N))) (norm_nonneg _)
  · refine ⟨c, hc.1.le, fun x hx => ?_⟩
    simpa [abs_of_nonneg (by grind : 0 ≤ x), mul_div] using hN x (hn.le.trans hx)

@[blueprint
  "theta-stieltjes"
  (title := "The Chebyshev function is Stieltjes")
  (statement := /-- The function $\vartheta(x) = \sum_{p \leq x} \log p$ defines a Stieltjes function (monotone and right continuous). -/)
  (proof := /-- Trivial -/)
  (latexEnv := "sublemma")
  (discussion := 598)]
noncomputable def θ.Stieltjes : StieltjesFunction ℝ := {
  toFun := θ
  mono' := theta_mono
  right_continuous' := fun x ↦ by
    rw [ContinuousWithinAt, theta_eq_theta_coe_floor x]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    obtain hx | hx := le_total 0 x
    · filter_upwards [Ico_mem_nhdsGE_of_mem ⟨floor_le hx, lt_floor_add_one x⟩] with y hy
      rw [theta_eq_theta_coe_floor y, floor_eq_on_Ico _ _ hy]
    · filter_upwards [Ico_mem_nhdsGE (by grind : x < 1)] with y hy
      simp [floor_of_nonpos hx, theta_eq_theta_coe_floor y, floor_eq_zero.mpr hy.2]
}

lemma theta_succ_sub (k : ℕ) : (θ (k + 1) - θ k) = if Nat.Prime (k + 1) then Real.log (k + 1) else 0  := by
  simp [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, Nat.floor_add_one, Finset.sum_Icc_succ_top]

lemma theta_one : θ 1 = 0 := by
  simp [theta, Finset.sum_filter]

lemma theta_two : θ 2 = Real.log 2 := by
  simp [theta, Finset.sum_filter, Finset.sum_Ioc_succ_top, Nat.prime_two]

lemma leftLim_theta_succ (k : ℕ) : Function.leftLim θ (k + 1) = θ k := by
  rw [leftLim_eq_of_tendsto (y := θ ↑k)]
  · exact Filter.NeBot.ne'
  · rw [nhdsWithin_restrict (t := Set.Ioo ↑k ↑(k + 2))]
    · rw [Set.Iio_inter_Ioo]
      apply tendsto_nhdsWithin_congr (f := fun _ => θ ↑k)
      · intro y hy
        have floor_k_eq: ⌊(k : ℝ)⌋₊ = ⌊(y: ℝ)⌋₊ := by
          rw [eq_comm, Nat.floor_eq_iff]
          · simp
            grind
          · simp at hy
            linarith
        rw [Chebyshev.theta_eq_theta_coe_floor]
        rw [Chebyshev.theta_eq_theta_coe_floor (x := y)]
        congr
      · simp
    · simp
    · exact isOpen_Ioo

theorem summable_pre413 {f : ℝ → ℝ} {s : Set ℝ} (hs : Bornology.IsBounded s) (hs_measureable : MeasurableSet s) :
  Summable fun (n: ℕ) ↦ ∫ (x : ℝ) in n..(n + 1), f x ∂«θ».Stieltjes.measure.restrict s := by

  by_cases s_empty: s = ∅
  · rw [summable_congr (g := 0)]
    · apply summable_zero
    · simp [s_empty, intervalIntegral.integral_of_le]

  apply summable_of_finite_support
  apply Set.Finite.subset (s := Finset.Icc (⌊sInf s⌋₊ - 1) (⌈sSup s⌉₊ + 1))
  · apply finite_toSet
  · intro a ha
    simp only [Function.mem_support, ne_eq] at ha
    rw [← ne_eq] at ha
    by_contra!
    rw [intervalIntegral.integral_zero_ae] at ha
    · simp at ha
    · rw [MeasureTheory.ae_iff]
      rw [Measure.restrict_apply']
      · simp only [le_add_iff_nonneg_right, zero_le_one, Set.uIoc_of_le, Set.mem_Ioc,
          and_imp, Classical.not_imp]
        rw [Set.setOf_and]
        rw [Set.setOf_and]
        rw [← Set.inter_assoc]
        nth_rw 1 [Set.inter_assoc]
        rw [Set.inter_comm]
        rw [Set.inter_assoc]
        apply MeasureTheory.measure_inter_null_of_null_right
        · conv =>
            arg 1
            arg 2
            equals ∅ =>
              ext c
              simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
                not_and, not_le]
              intro c_mem a_lt
              simp only [coe_Icc, Set.mem_Icc, not_and_or] at this
              cases this
              · rename_i le_a
                rw [tsub_le_iff_right, not_le] at le_a
                apply Nat.lt_of_lt_floor at le_a
                simp at le_a
                have := csInf_le (hs.bddBelow) c_mem
                linarith
              · rename_i a_le
                rw [not_le] at a_le
                apply LT.lt.le at a_le
                rw [Order.add_one_le_iff] at a_le
                apply LT.lt.le at a_le
                apply Nat.le_of_ceil_le at a_le
                grw [le_csSup hs.bddAbove c_mem] at a_lt
                linarith
          simp
      · apply hs_measureable

lemma support_pre413 {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) :
  (Function.support fun (n: ℕ) ↦ ∫ (x : ℝ) in ↑n..↑n + 1, f x ∂«θ».Stieltjes.measure.restrict (Set.Icc 2 x)) ⊆
    (Finset.Ico 1 ⌊x⌋₊) := by
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  rw [intervalIntegral.integral_of_le (by simp), ← ne_eq, ← abs_pos] at hn
  grw [MeasureTheory.abs_integral_le_integral_abs] at hn
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae] at hn
  · simp only [measurableSet_Ioc, Measure.restrict_restrict, measurableSet_Icc,
      MeasurableSet.inter, Measure.restrict_apply'] at hn
    by_cases n_eq: n = 0
    · simp only [n_eq, CharP.cast_eq_zero, zero_add] at hn
      conv at hn =>
        pattern _ ∩ _
        rhs
        equals ∅ => grind
      simp at hn
    by_contra!
    conv at hn =>
      rhs
      arg 2
      rhs
      equals (Set.Ioc ↑n x) =>
        ext a
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
        refine ⟨?_, ?_⟩
        · intro ha
          refine ⟨by grind, ?_⟩
          grind
        · intro ha
          simp only [coe_Ico, Set.mem_Ico, not_and_or] at this
          refine ⟨?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · grind
            · cases this
              · grind
              · rename_i n_le
                simp at n_le
                grw [ha.2]
                grw [Nat.lt_floor_add_one (a := x)]
                simpa using n_le
          · refine ⟨?_, by grind⟩
            have le_x: (2: ℕ) ≤ x := by norm_cast
            apply Nat.le_floor at le_x
            conv =>
              lhs
              equals ↑(2: ℕ) => simp

            simp only [not_le, lt_one_iff, n_eq, not_lt, false_or] at this
            grw [le_x, this]
            linarith

    apply _root_.ne_of_lt at hn
    rw [ne_eq, eq_comm] at hn
    rw [measure_inter_null_of_null_right] at hn
    · simp at hn
    · simp only [«θ».Stieltjes, StieltjesFunction.measure_Ioc, ENNReal.ofReal_eq_zero, tsub_le_iff_right, zero_add]
      rw [theta_eq_theta_coe_floor]
      apply Monotone.imp (by exact theta_mono)
      simp only [coe_Ico, Set.mem_Ico, not_and, not_lt] at this
      simp [this (by omega)]
  · apply Filter.Eventually.of_forall
    intro y
    simp
  · apply MeasureTheory.Integrable.of_integral_ne_zero
    grind

lemma pre_413_measure_inter {x : ℝ} (hx : 2 ≤ x) (y : Finset.Ico 1 ⌊x⌋₊) :
    «θ».Stieltjes.measure.real (Set.Ioc (↑↑y) (↑↑y + 1) ∩ Set.Icc 2 x) = if Nat.Prime (y + 1) then Real.log (↑y + 1) else 0 := by
  by_cases y_eq: y.val = 1
  · simp only [y_eq, cast_one, reduceAdd]
    norm_num
    conv =>
      arg 1
      arg 2
      equals Set.Icc 2 2 =>
        ext a
        simp
        have foo := y.prop
        rw [Finset.mem_Ico] at foo
        grind
    rw [Measure.real_def]
    simp only [«θ».Stieltjes, Set.Icc_self, StieltjesFunction.measure_singleton,
      theta_two]
    conv =>
      lhs
      arg 1
      arg 1
      rhs
      arg 2
      equals ↑(1: ℕ) + (1: ℝ) => norm_num
    rw [leftLim_theta_succ]
    simp [theta_one, Real.log_nonneg]
  · rw [Measure.real_def, MeasureTheory.measure_eq_measure_of_null_diff (t := Set.Ioc (↑↑y) (↑↑y + 1))]
    · simp only [«θ».Stieltjes, StieltjesFunction.measure_Ioc, theta_succ_sub,
      ENNReal.toReal_ofReal_eq_iff]
      split_ifs
      · simp [Real.log_nonneg]
      · simp
    · simp
    · simp
      conv =>
        arg 1
        arg 2
        equals ∅ =>
          ext a
          simp only [Set.mem_diff, Set.mem_Ioc, Set.mem_Icc, not_and, not_le,
            Set.mem_empty_iff_false, iff_false, Classical.not_imp, not_lt, and_imp]
          intro ha hb
          have y_prop := y.property
          rw [Finset.mem_Ico] at y_prop

          have y_lt: (2: ℝ) ≤ y.val := by
            norm_cast
            omega
          refine ⟨?_, ?_⟩
          · grw [y_lt]
            linarith
          · grw [hb]
            have bar := y_prop.2
            rw [← Nat.add_one_le_iff] at bar
            norm_cast
            grw [bar]
            apply Nat.floor_le
            linarith
      simp

@[blueprint
  "rs-pre-413"
  (title := "RS-prime display before (4.13)")
  (statement := /-- $\sum_{p \leq x} f(p) = \int_{2}^x \frac{f(y)}{\log y}\ d\vartheta(y)$. -/)
  (proof := /-- This follows from the definition of the Stieltjes integral. -/)
  (latexEnv := "sublemma")
  (discussion := 599)]
theorem pre_413 {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousOn f (Set.Icc 2 (x + 1))) (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p =
      ∫ y in Set.Icc 2 x, f y / log y ∂θ.Stieltjes.measure := by
  rw [← (MeasureTheory.Integrable.hasSum_intervalIntegral _ 0).tsum_eq]
  · rw [tsum_of_nat_of_neg_add_one]
    · conv =>
        rhs
        rhs
        arg 1
        intro n
        rw [intervalIntegral.integral_of_le (by simp)]
        rw [MeasureTheory.setIntegral_measure_zero]
        . skip
        . tactic =>
            rw [Measure.restrict_apply]
            apply MeasureTheory.measure_inter_null_of_null_left
            simp only [«θ».Stieltjes, neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg,
              Int.cast_one, Int.cast_natCast, zero_add, neg_add_cancel_comm,
              StieltjesFunction.measure_Ioc, theta, ENNReal.ofReal_eq_zero, tsub_le_iff_right]
            rw [Finset.Ioc_eq_empty_of_le]
            · rw [Finset.Ioc_eq_empty_of_le]
              simp
              linarith
            · simp
              linarith
            · simp
      simp only [Int.cast_natCast, zero_add, tsum_zero, add_zero]
      rw [tsum_eq_sum' (s := Finset.Ico 1 ⌊x⌋₊)]
      · conv =>
          rhs
          arg 2
          intro k
          rw [intervalIntegral.integral_congr_ae_restrict (g := fun _ => (f (k + 1)) / (Real.log (k + 1))) (by
            rw [Set.uIoc_of_le (by simp)]
            conv =>
              pattern Set.Ioc _ _
              equals (Set.Ioo ↑k ↑(k + 1)) ∪ {↑(k + 1)} => simp
            rw [MeasureTheory.ae_restrict_union_eq]
            unfold Filter.EventuallyEq
            rw [Filter.eventually_sup, ← Filter.EventuallyEq]
            refine ⟨?_, ?_⟩
            · unfold Filter.EventuallyEq
              rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply', Set.inter_comm]
              apply MeasureTheory.measure_inter_null_of_null_left
              · rw [MeasureTheory.Measure.restrict_apply']
                · apply MeasureTheory.measure_inter_null_of_null_left
                  simp [«θ».Stieltjes, leftLim_theta_succ]
                · simp
              · simp
            · rw [Measure.restrict_restrict (by simp)]
              by_cases k_succ_mem: ↑k + (1: ℝ) ∈ Set.Icc (2: ℝ) x
              · simp only [cast_add, cast_one, Set.singleton_inter_of_mem k_succ_mem,
                  Measure.restrict_singleton, StieltjesFunction.measure_singleton, «θ».Stieltjes, leftLim_theta_succ, theta_succ_sub]
                split_ifs
                · rename_i k_prime
                  rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff]
                  · simp
                  · have := k_prime.two_le
                    simp_rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
                    apply Real.log_pos
                    simp
                    grind
                · simp
              · rw [Set.singleton_inter_of_notMem]
                · simp
                · simp
                  simp at k_succ_mem
                  grind
          )]
        simp_rw [intervalIntegral.integral_const']
        simp only [measurableSet_Ioc, measureReal_restrict_apply, add_lt_iff_neg_left, not_lt,
          zero_le_one, Set.Ioc_eq_empty, measureReal_empty, sub_zero, smul_eq_mul]
        nth_rw 2 [← Finset.sum_coe_sort]
        simp_rw [pre_413_measure_inter hx]
        simp only [ite_mul, zero_mul]
        have log_succ (y: Finset.Ico 1 ⌊x⌋₊) : Real.log (y + 1) ≠ 0 := by
          have foo := y.property
          simp
          norm_cast
          grind
        field_simp [log_succ]
        rw [Finset.sum_coe_sort (f := fun y => (if Nat.Prime (y + 1) then (f (↑y + 1)) else 0)),
            Finset.sum_Ico_eq_sum_range]
        norm_cast
        ring
        conv =>
          rhs
          arg 1
          arg 1
          equals ⌊x⌋₊ + 1 - 2 => simp
        rw [← Finset.sum_Ico_eq_sum_range (m := 2) (f := fun x => if Nat.Prime (x) then f ↑(x) else 0)]
        conv =>
          rhs
          arg 1
          equals Finset.Icc 2 ⌊x⌋₊ =>
            ext a
            simp
        rw [Finset.sum_filter, Finset.Iic_eq_Icc]
        rw [← Finset.sum_subset (s₁ := Finset.Icc 2 ⌊x⌋₊)]
        · intro a ha
          simp at ha
          simp
          omega
        · intro a ha a_not
          simp at a_not
          simp at ha
          have a_lt: a < 2 := by omega
          have not_prime : ¬ Nat.Prime a := by
            by_cases a_eq: a = 0
            · simp [a_eq, Nat.not_prime_zero]
            · by_cases a_eq: a = 1
              · simp [a_eq, Nat.not_prime_one]
              · omega
          simp [not_prime]
      · apply support_pre413 hx
    · simp only [Int.cast_natCast, zero_add]
      apply summable_pre413 (by exact Metric.isBounded_Icc 2 x) (by exact
        measurableSet_Icc)
    · rw [summable_congr (g := 0)]
      · apply summable_zero
      · intro n
        rw [intervalIntegral.integral_of_le (by simp)]
        have inter_empty: Set.Ioc (-1 + -(n: ℝ)) (-↑n) ∩ Set.Icc 2 x = ∅ := by
          ext a
          simp only [Set.mem_inter_iff, Set.mem_Ioc, add_neg_lt_iff_lt_add, Set.mem_Icc,
            Set.mem_empty_iff_false, iff_false, not_and, not_le, and_imp]
          intros
          linarith
        simp [inter_empty]
  · apply ContinuousOn.integrableOn_Icc
    intro a ha
    have a_ne: a ≠ 0 := by grind
    apply ContinuousWithinAt.div
    · apply hf.mono (t := Set.Icc _ _)
      · intro a ha
        simp
        simp at ha
        grind
      · simpa using ha
    · apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
    · simp
      grind

@[blueprint
  "rs-413"
  (title := "RS equation (4.13)")
  (statement := /-- $\sum_{p \leq x} f(p) = \frac{f(x) \vartheta(x)}{\log x} - \int_2^x \vartheta(y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-pre-413} and integration by parts. -/)
  (latexEnv := "sublemma")
  (discussion := 650)]
theorem eq_413 {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) (hf : DifferentiableOn ℝ f (Set.Icc 2 x)) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p = f x * θ x / log x -
      ∫ y in 2..x, θ y * deriv (fun t ↦ f t / log t) y := by
  sorry

@[blueprint
  "rs-414"
  (title := "RS equation (4.14)")
  (statement := /--
  $$\sum_{p \leq x} f(p) = \int_2^x \frac{f(y)\ dy}{\log y} + \frac{2 f(2)}{\log 2} $$
  $$ + \frac{f(x) (\vartheta(x) - x)}{\log x} - \int_2^x (\vartheta(y) - y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-413} and integration by parts. -/)
  (latexEnv := "sublemma")
  (discussion := 600)]
theorem eq_414 {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) (hf : DifferentiableOn ℝ f (Set.Icc 2 x))
    (hd : IntervalIntegrable (fun t => deriv (fun s ↦ f s / log s) t) volume 2 x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p =
    (∫ y in 2..x, f y / log y) + 2 * f 2 / Real.log 2 +
    f x * (θ x - x) / log x -
    ∫ y in 2..x, (θ y - y) * deriv (fun s ↦ f s / log s) y :=
  let hcc := Set.uIcc_of_le hx
  let hoc := Set.uIoc_of_le hx
  have hm : Set.Ioo 2 x ∈ ae (volume.restrict (Set.Ioc 2 x)) := by
    by_cases hp : 2 < x
    · rw [mem_ae_iff, Measure.restrict_apply' measurableSet_Ioc, ← Set.diff_eq_compl_inter,
        Set.Ioc_diff_Ioo_same hp, volume_singleton]
    · simp_all
  have hae : (fun t ↦ deriv (fun s ↦ f s / log s) t) =ᶠ[ae (volume.restrict (Set.Ioc 2 x))]
    derivWithin (fun t ↦ f t / log t) (Set.uIcc 2 x) := by
    filter_upwards [hm] with y hy
    have : Set.Icc 2 x ∈ 𝓝 y := mem_nhds_iff.2
      ⟨Set.Ioo 2 x, Set.Ioo_subset_Icc_self, ⟨isOpen_Ioo, hy⟩⟩
    refine (DifferentiableAt.derivWithin ?_ (uniqueDiffWithinAt_of_mem_nhds (hcc ▸ this))).symm
    refine ((hf y (Set.Ioo_subset_Icc_self hy)).differentiableAt this).fun_div
      (differentiableAt_log (by simp_all; linarith)) ?_
    linarith [Real.log_pos (by simp_all; linarith)]
  calc
  _ = f x * (θ x - x) / log x + x * f x / log x -
    (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
    ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
    rw [eq_413 hx hf, ← tsub_add_eq_tsub_tsub, ← intervalIntegral.integral_add _
      (hd.continuousOn_mul (by fun_prop))]
    · ring_nf
    · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 ?_
      have hb : ∀ᵐ y ∂volume.restrict (Set.Ioc 2 x), ‖θ y - y‖ ≤ θ x + x := by
        refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
        calc
        _ ≤ ‖θ y‖ + ‖y‖ := by bound
        _ = θ y + y := by rw [norm_of_nonneg (theta_nonneg y), norm_of_nonneg (by grind : 0 ≤ y)]
        _ ≤ θ x + x := add_le_add (theta_mono hy.2) hy.2
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 hd).bdd_mul
        (theta_mono.measurable.aestronglyMeasurable.sub (by fun_prop)) hb
  _ = f x * (θ x - x) / log x +
    ((∫ y in 2..x, 1 * (f y / log y) + y * derivWithin (fun t ↦ f t / log t) (Set.uIcc 2 x) y) +
    2 * f 2 / log (2 : ℝ)) -
    (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
    ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
    rw [← sub_add_cancel (x * f x / log x) (2 * f 2 / log (2 : ℝ)),
      intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt, mul_div, mul_div]
    · intro y _; exact (hasDerivAt_id' y).hasDerivWithinAt
    · refine fun y hy => (hcc ▸ (hf y (hcc ▸ hy)).fun_div ?_ ?_).hasDerivWithinAt
      · exact (differentiableAt_log (by simp_all; linarith)).differentiableWithinAt
      · linarith [Real.log_pos (by simp_all; linarith)]
    · exact intervalIntegral.intervalIntegrable_const
    · exact hd.congr_ae (hoc ▸ hae)
  _ = f x * (θ x - x) / log x +
    ((∫ y in 2..x, f y / log y) + (∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y) +
    2 * f 2 / log (2 : ℝ)) -
    (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
    ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
    have : (fun y ↦ y * deriv (fun t ↦ f t / log t) y) =ᶠ[ae (volume.restrict (Set.Ioc 2 x))]
      fun y ↦ y * derivWithin (fun t ↦ f t / log t) (Set.uIcc 2 x) y := by
      filter_upwards [Filter.eventually_iff.1 hae.eventually] with y hy
      grind
    have hi := intervalIntegral.integral_congr_ae_restrict (hoc ▸ this)
    simp only [one_mul, sub_left_inj, add_right_inj, add_left_inj, hi]
    refine intervalIntegral.integral_add (ContinuousOn.intervalIntegrable_of_Icc hx ?_) ?_
    · exact ContinuousOn.div₀ (by fun_prop) (continuousOn_log.mono (by grind))
        (fun x hx => by linarith [Real.log_pos (by simp_all; linarith)])
    · exact (hd.continuousOn_mul (by fun_prop)).congr_ae (hoc ▸ this)
  _ = _ := by ring

@[blueprint
  "rs-416"
  (title := "RS equation (4.16)")
  (statement := /--
  $$L_f := \frac{2f(2)}{\log 2} - \int_2^\infty (\vartheta(y) - y) \frac{d}{dy} (\frac{f(y)}{\log y})\ dy.$$ -/)]
noncomputable def L (f : ℝ → ℝ) : ℝ :=
    2 * f 2 / Real.log 2 - ∫ y in Set.Ioi 2, (θ y - y) * deriv (fun t ↦ f t / log t) y

open intervalIntegral in
theorem _root_.intervalIntegral.interval_add_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f : ℝ → E} {μ : Measure ℝ} (ha : IntegrableOn f (Set.Ioi a) μ)
    (hb : IntegrableOn f (Set.Ioi b) μ) :
    ∫ (x : ℝ) in a..b, f x ∂μ + ∫ (x : ℝ) in Set.Ioi b, f x ∂μ
    = ∫ (x : ℝ) in Set.Ioi a, f x ∂μ := by
  wlog hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab)]; grind
  rw [integral_of_le hab, ← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (ha.mono_set Set.Ioc_subset_Ioi_self) hb, Set.Ioc_union_Ioi_eq_Ioi hab]

theorem intervalIntegrable_inv_log_pow (n : ℕ) (m : ℕ) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    IntegrableOn (fun t ↦ 1 / (t ^ n * Real.log t ^ m)) (Set.Ioc x y) volume := by
  by_cases h : x < y
  · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine ContinuousOn.div₀ (by fun_prop) (ContinuousOn.mul (by fun_prop) ?_) ?_
    · exact (continuousOn_log.mono (by grind)).pow m
    · simp_all; grind
  · simp_all

theorem ioiIntegrable_inv_log_pow {n : ℕ} (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t ↦ 1 / (t * Real.log t ^ n)) (Set.Ioi x) volume := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (log x ^ (1 - (n : ℝ)) / (n - 1)) x
    (fun k => ?_) tendsto_natCast_atTop_atTop ?_
  · simpa using intervalIntegrable_inv_log_pow 1 n hx k
  · have : 0 < (n : ℝ) - 1 := by linarith [(one_lt_cast (α := ℝ)).2 hn]
    refine Tendsto.congr' (f₁ := fun i : ℕ => (log i : ℝ) ^ (1 - (n : ℝ)) / (1 - (n : ℝ)) -
      (log x) ^ (1 - (n : ℝ)) / (1 - (n : ℝ))) ?_ ?_
    · have := tendsto_def.1 tendsto_natCast_atTop_atTop (Set.Ici x) (Ici_mem_atTop x)
      filter_upwards [this] with i hi
      refine (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun r => log r ^ (1 - (n : ℝ)) / (1 - (n : ℝ))) (fun z hz => ?_) ?_).symm
      · simp_all only [preimage_Ici, Set.mem_Ici, ceil_le, Set.uIcc_of_le, Set.mem_Icc]
        have := Real.log_pos (by linarith)
        rw [norm_of_nonneg <| one_div_nonneg.2 (mul_nonneg (by grind) (pow_nonneg this.le n))]
        refine (((hasDerivAt_log (by grind)).rpow_const (by grind)).div_const _).congr_deriv ?_
        have : 1 - (n : ℝ) ≠ 0 := by linarith
        simp [field]
      · apply IntervalIntegrable.norm
        simpa using (intervalIntegrable_iff_integrableOn_Ioc_of_le hi).2
          (intervalIntegrable_inv_log_pow 1 n hx i)
    · suffices h : Tendsto (fun i : ℕ ↦ Real.log i ^ (1 - (n : ℝ)) / (1 - n)) atTop (𝓝 0) from by
        have : (log x ^ (1 - (n : ℝ)) / (n - 1)) = 0 - (log x ^ (1 - (n : ℝ)) / (1 - n)) := by grind
        exact this ▸ h.sub_const (log x ^ (1 - (n : ℝ)) / (1 - n))
      simpa using (((tendsto_rpow_neg_atTop this).comp tendsto_log_atTop).comp
        tendsto_natCast_atTop_atTop).div_const (1 - (n : ℝ))

theorem bound_deriv {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {C : ℝ}
    (hC : ∀ x ∈ Set.Ici 2, |f x| ≤ C / x ∧ |deriv f x| ≤ C / x ^ 2) :
    ∀ᵐ (a : ℝ) ∂volume.restrict (Set.Ioi 2), ‖deriv (fun t ↦ f t / log t) a‖ ≤
    C * (1 / (a ^ 2 * log a) + 1 / (a ^ 2 * log a ^ 2)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  calc
  _ = ‖deriv f a / log a - f a / (a * log a ^ 2)‖ := by
    congr
    rw [deriv_fun_div, deriv_log]
    · field_simp
    · exact hf.differentiableAt (mem_nhds_iff.2 ⟨Set.Ioi 2, Set.Ioi_subset_Ici_self,
        ⟨isOpen_Ioi, ha⟩⟩)
    · exact differentiableAt_log_iff.2 (by grind)
    · simp_all; grind
  _ ≤ ‖deriv f a‖ / ‖log a‖ + ‖f a‖ / ‖a * log a ^ 2‖ := by rw [← norm_div, ← norm_div]; bound
  _ = |deriv f a| / ‖log a‖ + |f a| / ‖a * log a ^ 2‖ := by simp
  _ ≤ C / a ^ 2 / ‖log a‖ + C / a / ‖a * log a ^ 2‖ := by
    gcongr
    exacts [(hC a (Set.Ioi_subset_Ici_self ha)).2, (hC a (Set.Ioi_subset_Ici_self ha)).1]
  _ = C / a ^ 2 / log a + C / a / (a * log a ^ 2) := by
    congr <;> rw [norm_of_nonneg]
    · exact log_nonneg (by grind)
    · exact mul_nonneg (by grind) (pow_nonneg (log_nonneg (by grind)) 2)
  _ = _ := by field_simp

theorem integrableOn_deriv {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {C : ℝ}
    (hC : ∀ x ∈ Set.Ici 2, |f x| ≤ C / x ∧ |deriv f x| ≤ C / x ^ 2) :
    IntegrableOn (fun y ↦ (θ y - y) * deriv (fun t ↦ f t / log t) y) (Set.Ioi 2) volume
    ∧ ∀ x ≥ 2, IntervalIntegrable (fun t ↦ deriv (fun s ↦ f s / Real.log s) t) volume 2 x := by
  obtain ⟨A, hA⟩ := pnt
  refine ⟨Integrable.mono' (g := fun t => (A * C) * (1 / (t * log t ^ 3) + 1 / (t * log t ^ 4)))
    ?_ ?_ ?_, fun x hx => ?_⟩
  · refine ((ioiIntegrable_inv_log_pow ?_ ?_).add (ioiIntegrable_inv_log_pow ?_ ?_)).const_mul
      (A * C) <;> linarith
  · exact (theta_mono.measurable.aestronglyMeasurable.sub (by fun_prop)).mul
      (aestronglyMeasurable_deriv _ _)
  · filter_upwards [bound_deriv hf hC, ae_restrict_mem measurableSet_Ioi] with a ha ho
    calc
    _ = |(θ a - a)| * ‖deriv (fun t ↦ f t / log t) a‖ := by simp
    _ ≤ A * a / log a ^ 2 * (C * (1 / (a ^ 2 * log a) + 1 / (a ^ 2 * log a ^ 2))) := by
      gcongr
      · exact div_nonneg (mul_nonneg hA.1 (by grind)) (pow_nonneg (log_nonneg (by grind)) 2)
      · exact hA.2 a (Set.mem_Ioi.1 ho).le
    _ = _ := by field_simp
  · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 (Integrable.mono'
      (Integrable.const_mul (Integrable.add ?_ ?_) C) (aestronglyMeasurable_deriv _ _)
      (ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Ioi_self (bound_deriv hf hC)))
    · simpa using intervalIntegrable_inv_log_pow 2 1 (by linarith : 1 < (2 : ℝ)) x
    · simpa using intervalIntegrable_inv_log_pow 2 2 (by linarith : 1 < (2 : ℝ)) x

@[blueprint
  "rs-415"
  (title := "RS equation (4.15)")
  (statement := /--
  $$\sum_{p \leq x} f(p) = \int_2^x \frac{f(y)\ dy}{\log y} + L_f $$
  $$ + \frac{f(x) (\vartheta(x) - x)}{\log x} + \int_x^\infty (\vartheta(y) - y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-414} and Definition \ref{rs-416}. -/)
  (latexEnv := "sublemma")
  (discussion := 601)]
theorem eq_415 {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {x : ℝ} (hx : 2 ≤ x)
    (hft : IntegrableOn (fun y ↦ (θ y - y) * deriv (fun t ↦ f t / log t) y) (Set.Ioi 2) volume)
    (hfi : IntervalIntegrable (fun t ↦ deriv (fun s ↦ f s / Real.log s) t) volume 2 x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p = (∫ y in 2..x, f y / log y) + L f +
    f x * (θ x - x) / log x + ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ f s / log s) y := by
  rw [eq_414 hx (hf.mono Set.Icc_subset_Ici_self) hfi, L, ← intervalIntegral.interval_add_Ioi hft
    (hft.mono_set (Set.Ioi_subset_Ioi hx))]
  ring

@[blueprint
  "rs-417"
  (title := "RS equation (4.17)")
  (statement := /--
  $$\pi(x) = \frac{\vartheta(x)}{\log x} + \int_2^x \frac{\vartheta(y)\ dy}{y \log^2 y}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = 1$. -/)
  (latexEnv := "sublemma")
  (discussion := 602)]
theorem eq_417 {x : ℝ} (hx : 2 ≤ x) :
    pi x = θ x / log x + ∫ y in 2..x, θ y / (y * log y ^ 2) := by
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

@[blueprint
  "rs-418"
  (title := "RS equation (4.18)")
  (statement := /--
  $$\sum_{p \leq x} \frac{1}{p} = \frac{\vartheta(x)}{x \log x} + \int_2^x \frac{\vartheta(y) (1 + \log y)\ dy}{y^2 \log^2 y}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = 1/t$. -/)
  (latexEnv := "sublemma")
  (discussion := 652)]
theorem eq_418 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) = θ x / (x * log x) +
    ∫ y in 2..x, θ y * (1 + log y) / (y ^ 2 * log y ^ 2) := by
  have : DifferentiableOn ℝ (fun y : ℝ ↦ 1 / y) (Set.Icc 2 x) :=
    fun y hy => by simpa [one_div] using differentiableWithinAt_inv (by grind) (Set.Icc 2 x)
  rw [eq_413 (f := fun x => 1 / x) hx this, mul_comm_div, one_mul, div_div, sub_eq_add_neg,
    ← intervalIntegral.integral_neg, add_left_cancel_iff]
  refine intervalIntegral.integral_congr fun y hy => ?_
  have hy := Set.uIcc_of_le hx ▸ hy
  have := deriv_fun_inv'' (y.hasDerivAt_mul_log (by grind)).differentiableAt
    (mul_ne_zero_iff.2 ⟨by grind, by linarith [Real.log_pos (by grind : 1 < y)]⟩)
  simp only [neg_mul_eq_mul_neg, mul_div_assoc, mul_left_cancel_iff_of_pos
    (theta_pos hy.1), div_div, fun t : ℝ => one_div (t * log t), this,
    deriv_mul_log (by grind : y ≠ 0)]
  ring

theorem ioiIntegral_tendsto_zero {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {μ : Measure ℝ} (a : ℝ) (hfi : IntegrableOn f (Set.Ioi a) μ)
    {l : Filter ι} {b : ι → ℝ} [IsCountablyGenerated l] (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in Set.Ioi (b i), f x ∂μ) l (𝓝 0) := by
  have : ∀ᶠ i in l, ∫ x in Set.Ioi a, f x ∂μ - ∫ x in a..b i, f x ∂μ =
    ∫ x in Set.Ioi (b i), f x ∂μ := by
    filter_upwards [hb.eventually_mem (Ici_mem_atTop a)] with i hi
    rw [sub_eq_iff_eq_add', intervalIntegral.interval_add_Ioi hfi
      (hfi.mono_set (Set.Ioi_subset_Ioi hi))]
  exact Tendsto.congr' this (sub_self (∫ x in Set.Ioi a, f x ∂μ) ▸ (Tendsto.const_sub _ <|
    intervalIntegral_tendsto_integral_Ioi a hfi hb))

@[blueprint
  "Meissel-Mertens-constant"
  (title := "Meissel-Mertens constant B")
  (statement := /--
  $B := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{1}{p} - \log \log x \right)$. -/)]
noncomputable def _root_.meisselMertensConstant : ℝ := - log (log 2) + L (fun x => 1 / x)

theorem integrableOn_deriv_inv_div_log : IntegrableOn (fun y ↦ (θ y - y) *
    deriv (fun t ↦ 1 / t / Real.log t) y) (Set.Ioi 2) volume ∧
    ∀ x ≥ 2, IntervalIntegrable (fun t ↦ deriv (fun s ↦ 1 / s / Real.log s) t) volume 2 x := by
  refine integrableOn_deriv (C := 1) (by fun_prop (disch := grind)) (fun x hx => ⟨?_, ?_⟩)
  · rw [abs_of_nonneg (one_div_nonneg.2 (by grind))]
  · rw [deriv_fun_div (differentiableAt_const 1) differentiableAt_id (by grind), abs_div]
    simp

theorem meisselMertensConstant_identity {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) =
    log (log x) + meisselMertensConstant + (θ x - x) / (x * log x) +
    ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ 1 / s / Real.log s) y := by
  have integral_eq_loglog : ∫ y in 2..x, 1 / y / log y = log (log x) - log (log 2) := by
    have {y} (hy : y ∈ Set.uIcc 2 x) := (Set.uIcc_of_le hx ▸ hy).1
    have {y} (hy : y ∈ Set.uIcc 2 x) : log y ≠ 0 :=
      log_ne_zero_of_pos_of_ne_one (by grind) (by grind)
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.log ∘ log) (fun y hy => ?_) ?_
    · convert (hasDerivAt_log (this hy)).comp y (hasDerivAt_log (by grind)) using 1
      field_simp
    · exact ContinuousOn.intervalIntegrable_of_Icc hx (by fun_prop (disch := aesop))
  rw [eq_415 (by fun_prop (disch := grind)) hx integrableOn_deriv_inv_div_log.1
    (integrableOn_deriv_inv_div_log.2 x hx), integral_eq_loglog, meisselMertensConstant]
  ring

@[blueprint
  "rs-419"]
theorem mertens_second_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) - log (log x)) (𝓝 meisselMertensConstant) := by
  have lem : ∀ᶠ x in atTop, meisselMertensConstant + ((θ x - x) / (x * log x) +
    ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ 1 / s / Real.log s) y) =
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) - log (log x):= by
    filter_upwards [Ici_mem_atTop 2] with y hy
    rw [meisselMertensConstant_identity hy]
    ring
  rw [← add_zero meisselMertensConstant, ← add_zero 0]
  refine (tendsto_const_nhds.add (Tendsto.add ?_
    (ioiIntegral_tendsto_zero 2 integrableOn_deriv_inv_div_log.1 tendsto_id))).congr' lem
  · obtain ⟨C, hC⟩ := pnt
    refine squeeze_zero_norm' (a := fun x => C / Real.log x ^ 3) ?_ ?_
    · filter_upwards [Ici_mem_atTop 2] with y hy
      have h1 {y : ℝ} (hy : y ∈ Set.Ici 2) : 0 < y := by grind
      have h2 {y : ℝ} (hy : y ∈ Set.Ici 2) : 0 ≤ log y := log_nonneg (by grind)
      simp only [norm_div, norm_mul, norm_of_nonneg (h1 hy).le, norm_eq_abs, norm_of_nonneg (h2 hy)]
      grw [hC.2 y hy]
      · rw [div_right_comm, ← div_div, mul_div_cancel_right₀ _ (by grind)]; field_simp; rfl
      · exact mul_nonneg (h1 hy).le (h2 hy)
    · exact ((tendsto_pow_atTop (by linarith : 3 ≠ 0)).comp tendsto_log_atTop).const_div_atTop C

@[blueprint
  "rs-419"
  (title := "RS equation (4.19) and Mertens' second theorem")
  (statement := /--
  $$\sum_{p \leq x} \frac{1}{p} = \log \log x + B + \frac{\vartheta(x) - x}{x \log x} $$
  $$ - \int_2^x \frac{(\vartheta(y)-y) (1 + \log y)\ dy}{y^2 \log^2 y}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = 1/t$. One can also use this identity to demonstrate convergence of the limit defining $B$.-/)
  (latexEnv := "sublemma")
  (discussion := 603)]
theorem eq_419 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) =
    log (log x) + meisselMertensConstant + (θ x - x) / (x * log x)
    - ∫ y in Set.Ioi x, (θ y - y) * (1 + log y) / (y ^ 2 * log y ^ 2) := by
  simp_rw [meisselMertensConstant_identity hx, sub_eq_add_neg _ (∫ y in Set.Ioi x, _),
    ← integral_neg, ← div_neg, mul_div_assoc]
  have : ∫ (y : ℝ) in Set.Ioi x, (θ y - y) * deriv (fun s ↦ 1 / s / Real.log s) y =
    ∫ (a : ℝ) in Set.Ioi x, (θ a - a) * ((1 + Real.log a) / -(a ^ 2 * Real.log a ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => mul_eq_mul_left_iff.2 (Or.inl ?_)
    have := deriv_fun_inv'' (y.hasDerivAt_mul_log (by grind)).differentiableAt
      (mul_ne_zero_iff.2 ⟨by grind, by linarith [Real.log_pos (by grind : 1 < y)]⟩)
    simp_all [deriv_mul_log (by grind : y ≠ 0), div_eq_mul_inv, mul_comm]
    ring
  congr

@[blueprint
  "rs-419"]
theorem mertens_second_theorem' :
    ∃ C, ∀ x ≥ 2, |∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) - log (log x)| ≤ C := by
  obtain ⟨C, hC⟩ := pnt
  refine ⟨|meisselMertensConstant| + C / Real.log 2 ^ 3 +
    ∫ y in Set.Ioi 2, |(θ y - y) * deriv (fun t ↦ 1 / t / Real.log t) y|, fun x hx => ?_⟩
  calc
  _ ≤ |meisselMertensConstant + (θ x - x) / (x * log x)
    + ∫ y in Set.Ioi x, (θ y - y) * deriv (fun t ↦ 1 / t / Real.log t) y| := by
    rw [meisselMertensConstant_identity hx]; ring_nf; rfl
  _ ≤ |meisselMertensConstant| + |(θ x - x) / (x * log x)|
    + ∫ y in Set.Ioi x, |(θ y - y) * deriv (fun t ↦ 1 / t / Real.log t) y| := by
    grw [sub_eq_add_neg, abs_add_le, abs_add_le, abs_integral_le_integral_abs]
  _ ≤ _ := by
    gcongr
    · grw [abs_div, hC.2 x hx, abs_of_nonneg (mul_nonneg (by grind) (log_nonneg (by grind))),
        div_right_comm, ← div_div, mul_div_cancel_right₀ _ (by grind)]
      ring_nf
      gcongr
      · exact hC.1
      · exact inv_nonneg.2 (log_nonneg (by grind))
    · filter_upwards with a
      apply abs_nonneg
    · exact integrableOn_deriv_inv_div_log.1.abs

@[blueprint
  "Mertens-constant"
  (title := "Mertens constant E")
  (statement := /--
  $E := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{\log p}{p} - \log x \right)$. -/)]
noncomputable def _root_.mertensConstant : ℝ := - Real.log 2 + L (fun x => log x / x)

lemma log_div_log_eq {x : ℝ} (hx : 1 < x) : log x / x / log x = x⁻¹ := by
  have : log x ≠ 0 := by simp; grind
  grind

lemma deriv_eq {x} (hx : 2 ≤ x) : deriv (fun s ↦ Real.log s / s / log s) x = -(x ^ 2)⁻¹ :=
  (Set.EqOn.deriv (s := Set.Ioi (1 : ℝ)) (fun s hs => log_div_log_eq hs) isOpen_Ioi
    (by grind : 1 < x)).trans deriv_inv

lemma intervalIntegral_eq {x} (hx : 2 ≤ x) : ∫ (y : ℝ) in 2..x, Real.log y / y / Real.log y =
    ∫ (y : ℝ) in 2..x, 1 / y :=
  intervalIntegral.integral_congr fun t ht =>
    (by simpa using log_div_log_eq (by grind [Set.uIcc_of_le hx ▸ ht] : 1 < t))

theorem integrableOn_deriv_inv : IntegrableOn (fun y ↦ - ((θ y - y) / y ^ 2)) (Set.Ioi 2) volume ∧
    ∀ x ≥ 2, IntervalIntegrable (fun t ↦ -(t ^ 2)⁻¹) volume 2 x := by
  obtain ⟨C, hC⟩ := pnt
  refine ⟨Integrable.mono' (g := fun t => C / (t * log t ^ 2)) ?_ ?_ ?_, fun x hx =>
    ContinuousOn.intervalIntegrable (Set.uIcc_of_le hx ▸ by fun_prop (disch := simp_all; grind))⟩
  · simp only [fun t => div_eq_mul_one_div C (t * Real.log t ^ 2)]
    exact (ioiIntegrable_inv_log_pow (by grind) (by grind)).const_mul C
  · exact ((theta_mono.measurable.sub (by fun_prop)).div (by fun_prop)).neg.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    calc
    _ = |(θ a - a)| / ‖a ^ 2‖ := by simp
    _ ≤ C * a / Real.log a ^ 2 / a ^ 2 := by grw [hC.2 a ha.le]; simp
    _ = _ := by field_simp

@[blueprint
  "rs-420"
  (title := "RS equation (4.19) and Mertens' first theorem")
  (statement := /--
  $$\sum_{p \leq x} \frac{\log p}{p} = \log x + E + \frac{\vartheta(x) - x}{x} $$
  $$ - \int_2^x \frac{(\vartheta(y)-y)\ dy}{y^2}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = \log t / t$.  Convergence will need Theorem \ref{rs-pnt}. -/)
  (latexEnv := "sublemma")
  (discussion := 604)]
theorem eq_420 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), Real.log p / p =
    log x + mertensConstant + (θ x - x) / x - ∫ y in Set.Ioi x, (θ y - y) / (y ^ 2) := by
  have diff_log_inv_id : DifferentiableOn ℝ (fun x => Real.log x / x) (Set.Ici 2) := by
    fun_prop (disch := grind)
  have ioiIntegral_eq : ∫ (y : ℝ) in Set.Ioi x, (θ y - y) * deriv (fun s ↦
    Real.log s / s / Real.log s) y = ∫ (y : ℝ) in Set.Ioi x, - ((θ y - y) / y ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    simp [field, deriv_eq (by grind : 2 ≤ y)]
  have integral_eq_log : ∫ y in 2..x, 1 / y = log x - Real.log 2 := by
    have {y} (hy : y ∈ Set.uIcc 2 x) := (Set.uIcc_of_le hx ▸ hy).1
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.log) (fun y hy => ?_) ?_
    · simpa using hasDerivAt_log (by grind)
    · exact ContinuousOn.intervalIntegrable_of_Icc hx (by fun_prop (disch := grind))
  rw [eq_415 diff_log_inv_id hx, mertensConstant, mul_div_right_comm, log_div_log_eq (by grind),
    ioiIntegral_eq, intervalIntegral_eq hx, integral_eq_log, integral_neg]
  · ring
  · refine integrableOn_deriv_inv.1.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp [field, deriv_eq (by grind : 2 ≤ y)]
  · exact (integrableOn_deriv_inv.2 x hx).congr fun y hy =>
      (deriv_eq (Set.uIoc_of_le hx ▸ hy).1.le).symm

@[blueprint
  "rs-420"]
theorem mertens_first_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), Real.log p / p - log x) (𝓝 mertensConstant) := by
  have lem : ∀ᶠ x in atTop, mertensConstant + (θ x - x) / x
    + ∫ y in Set.Ioi x, - ((θ y - y) / (y ^ 2)) =
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), Real.log p / p - log x := by
    filter_upwards [Ici_mem_atTop 2] with y hy
    rw [eq_420 hy, integral_neg]
    ring
  rw [← add_zero mertensConstant, ← add_zero (_ + _)]
  refine ((tendsto_const_nhds.add ?_).add
    (ioiIntegral_tendsto_zero 2 integrableOn_deriv_inv.1 tendsto_id)).congr' lem
  · obtain ⟨C, hC⟩ := pnt
    refine squeeze_zero_norm' (a := fun x => C / Real.log x ^ 2) ?_ ?_
    · filter_upwards [Ici_mem_atTop 2] with y hy
      simp only [norm_div, norm_of_nonneg (by grind : 0 ≤ y), norm_eq_abs]
      grw [hC.2 y hy]
      · rw [div_right_comm, mul_div_cancel_right₀ _ (by grind)]
      · grind
    · exact ((tendsto_pow_atTop (by linarith : 2 ≠ 0)).comp tendsto_log_atTop).const_div_atTop C

@[blueprint
  "rs-420"]
theorem mertens_first_theorem' :
    ∃ C, ∀ x ≥ 2, |∑ p ∈ filter Prime (Iic ⌊x⌋₊), Real.log p / p - Real.log x| ≤ C := by
  obtain ⟨C, hC⟩ := pnt
  refine ⟨|mertensConstant| + C / Real.log 2 ^ 2 +
    ∫ y in Set.Ioi 2, |(θ y - y) / (y ^ 2)|, fun x hx => ?_⟩
  calc
  _ ≤ |mertensConstant + (θ x - x) / x - ∫ y in Set.Ioi x, (θ y - y) / (y ^ 2)| := by
    rw [eq_420 hx]; ring_nf; rfl
  _ ≤ |mertensConstant| + |(θ x - x) / x| + ∫ y in Set.Ioi x, |(θ y - y) / (y ^ 2)| := by
    grw [sub_eq_add_neg, abs_add_le, abs_add_le, abs_neg, abs_integral_le_integral_abs]
  _ ≤ _ := by
    gcongr
    · grw [abs_div, hC.2 x hx, abs_of_nonneg (by grind), div_right_comm,
        mul_div_cancel_right₀ _ (by grind)]
      ring_nf
      gcongr
      · exact hC.1
      · exact inv_nonneg.2 (log_nonneg (by grind))
    · filter_upwards with a
      apply abs_nonneg
    · simpa using integrableOn_deriv_inv.1.abs



@[blueprint
  "rs-psi-upper"
  (title := "RS Theorem 12")
  (statement := /-- We have $\psi(x) < c_0 x$ for all $x>0$. -/)]
theorem theorem_12 {x : ℝ} (hx : 0 < x) : ψ x < c₀ * x := by sorry

end RS_prime
