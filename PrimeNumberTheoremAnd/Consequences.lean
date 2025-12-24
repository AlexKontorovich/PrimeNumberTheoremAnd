import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Polynomial.Basic

import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeNumberTheoremAnd.Wiener

set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Ico a b ⊆ Set.Ico c d := by
  intro z hz
  have hz' := Set.Ico_subset_Icc_self.trans h hz
  have hcd : c ≤ d := by
    contrapose! hz'
    rw [Icc_eq_empty_of_lt hz']
    exact notMem_empty _
  simp only [mem_Ico, mem_Icc] at *
  refine ⟨hz'.1, hz'.2.eq_or_lt.resolve_left ?_⟩
  rintro rfl
  apply hz.2.not_ge
  have := h <| right_mem_Icc.mpr (hz.1.trans hz.2.le)
  simp only [mem_Icc] at this
  exact this.2

-- AkraBazzi.lean
lemma deriv_smoothingFn' {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) := by
  have : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx_pos hx
  rw [deriv_fun_inv''] <;> aesop

lemma deriv_smoothingFn {x : ℝ} (hx : 1 < x) : deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) :=
  deriv_smoothingFn' (by positivity) (ne_of_gt hx)

theorem extracted_2 (x : ℝ) (z : ℝ) (hz_pos : 0 < z) (hz : z ≠ 1) :
    ContinuousWithinAt (fun x ↦ (x * log x ^ 2)⁻¹) (Set.Icc (3 / 2) x) z := by
  apply ContinuousAt.continuousWithinAt
  have : z ≠ 0 := by linarith
  have : z * log z ^ 2 ≠ 0 := by
    apply mul_ne_zero this
    apply pow_ne_zero _ <| log_ne_zero_of_pos_of_ne_one hz_pos hz
  fun_prop (disch := assumption)

theorem extracted_1 (x : ℝ) :
    IntegrableOn
      (fun t ↦ (θ t) / (t * log t ^ 2))
      (Set.Icc 2 x) volume := by
  conv => arg 1; ext; rw [Chebyshev.theta_eq_sum_Icc, div_eq_mul_one_div, mul_comm, sum_filter]
  apply integrableOn_mul_sum_Icc _ (by norm_num)
  apply ContinuousOn.integrableOn_Icc
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have : x ≠ 0 := by linarith [hx.1]
  have : x * log x ^ 2 ≠ 0 := by
    apply mul_ne_zero this
    apply pow_ne_zero _ <| log_ne_zero_of_pos_of_ne_one _ _ <;> linarith [hx.1]
  fun_prop (disch := assumption)

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * (Real.log t) ^ 2) := by
  trans θ x / log x + ∫ t in Set.Icc (3 / 2) x, θ t / (t * (Real.log t) ^ 2)
  swap
  · congr 1
    have : Set.Icc (3/2) x = Set.Ico (3/2) 2 ∪ Set.Icc 2 x := by
      exact Set.Ico_union_Icc_eq_Icc (by norm_num) hx |>.symm
    rw [this, setIntegral_union _ measurableSet_Icc _ _]
    · simp only [add_eq_right]
      apply integral_eq_zero_of_ae
      simp only [measurableSet_Ico, ae_restrict_eq]
      refine eventuallyEq_inf_principal_iff.mpr ?_
      filter_upwards [] with y hy
      simp [Chebyshev.theta_eq_zero_of_lt_two hy.2]
    · rw [Set.disjoint_iff, Set.subset_empty_iff]
      ext y
      simp (config := {contextual := true})
    · rw [integrableOn_congr_fun (g := 0) _ measurableSet_Ico]
      · exact integrableOn_zero
      · intro y hy
        simp only [Set.mem_Ico] at hy
        have := Chebyshev.theta_eq_zero_of_lt_two hy.2
        simp_all
    · apply extracted_1 _
  let a : ℕ → ℝ := Set.indicator (setOf Nat.Prime) (fun n => log n)
  have floor32 : ⌊(3/2 : ℝ)⌋₊ = 1 := by rw [floor_div_ofNat, Nat.floor_ofNat]
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  rw [card_eq_sum_ones, range_succ_eq_Icc_zero]
  trans ∑ x ∈ Ioc ⌊(3/2 : ℝ)⌋₊ ⌊x⌋₊ with Nat.Prime x, 1
  · norm_cast
    congr 1
    ext p
    constructor <;> intro h
    · simp_all only [mem_filter, mem_Icc, _root_.zero_le, true_and, mem_Ioc, and_true]
      apply h.2.one_lt
    · simp_all
  rw [sum_filter]
  trans ∑ n ∈ Ioc ⌊(3/2 : ℝ)⌋₊ ⌊x⌋₊, (1 / log n) * a n
  · refine sum_congr rfl fun n hn ↦ ?_
    unfold a
    split_ifs with h
    · simp [h]
      have : log n ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one <;> norm_cast
        exacts [h.pos, h.ne_one]
      field
    simp [h]
  rw [sum_mul_eq_sub_sub_integral_mul a (f := fun n ↦ 1 / log n) (by norm_num) (by linarith), floor32, show Icc 0 1 = {0, 1} by ext; simp; omega]
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, mem_singleton, zero_ne_one,
      not_false_eq_true, sum_insert, CharP.cast_eq_zero, log_zero, ite_self, sum_singleton, cast_one,
      log_one, add_zero, mul_zero, sub_zero, Chebyshev.theta_eq_sum_Icc, a, sum_filter]
    have h8 (f : ℝ → ℝ) :
      ∫ (u : ℝ) in Set.Ioc (3 / 2) x, deriv (fun x ↦ 1 / log x) u * f u =
      ∫ (u : ℝ) in Set.Icc (3 / 2) x, f u * -(u * log u ^ 2)⁻¹ := by
      rw [← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_ae measurableSet_Icc
      refine Eventually.of_forall (fun u hu => ?_)
      simp only [one_div, mul_inv_rev, mul_neg]
      rw [deriv_smoothingFn (by linarith [hu.1])]
      ring
    simp_rw [h8, mul_neg, MeasureTheory.integral_neg]
    ring_nf!
  · intro z hz
    have : z ≠ 0 := by linarith [hz.1]
    have : log z ≠ 0 := by
      apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
    fun_prop (disch := assumption)
  · simp only [one_div]
    have : ∀ y ∈ Set.Icc (3 / 2) x, deriv (fun x ↦ (log x)⁻¹) y = -(y * log y ^ 2)⁻¹:= by
      intro y hy
      rw [deriv_smoothingFn, mul_inv, ← div_eq_mul_inv, neg_div]
      linarith [hy.1]
    apply ContinuousOn.integrableOn_Icc
    intro z hz
    apply ContinuousWithinAt.congr (f := fun x => - (x * log x ^ 2)⁻¹)
    · apply ContinuousWithinAt.neg
      apply extracted_2 <;> linarith [hz.1]
    · apply this
    · apply this z hz

/-%%
\begin{lemma}[finsum_range_eq_sum_range]\label{finsum_range_eq_sum_range}\lean{finsum_range_eq_sum_range}\leanok For any arithmetic function $f$ and real number $x$, one has
$$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
and
$$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
\end{lemma}
%%-/
lemma finsum_range_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_ : n ≤ x), f n = ∑ n ∈ Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero

/-%%
\begin{proof}\leanok Straightforward. \end{proof}
%%-/

lemma log2_pos : 0 < log 2 := by
  rw [Real.log_pos_iff zero_le_two]
  exact one_lt_two


/-- If u ~ v and w-u = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'
    {α : Type*} {β : Type*} [NormedAddCommGroup β] {u : α → β} {v : α → β} {w : α → β}
    {l : Filter α} (huv : Asymptotics.IsEquivalent l u v) (hwu : (w - u) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← add_sub_cancel u w]
  exact add_isLittleO huv hwu

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO''
    {α : Type*} {β : Type*} [NormedAddCommGroup β] {u : α → β} {v : α → β} {w : α → β}
    {l : Filter α} (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) = (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets, ge_iff_le,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop, ge_iff_le]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-%%
\begin{theorem}[chebyshev_asymptotic]\label{chebyshev_asymptotic}\lean{chebyshev_asymptotic}\leanok  One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$
\end{theorem}
%%-/
theorem chebyshev_asymptotic :
    θ ~[atTop] id := by
  apply WeakPNT''.add_isLittleO''
  apply IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log)
  · rw [isBigO_iff']
    use 1
    simp only [gt_iff_lt, zero_lt_one, Pi.sub_apply, norm_eq_abs, one_mul,
      eventually_atTop, ge_iff_le, true_and]
    use 2
    intro x hx
    nth_rewrite 2 [abs_of_nonneg (by bound)]
    exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)
  simp_rw [mul_assoc]
  apply IsLittleO.const_mul_left
  apply isLittleO_mul_iff_isLittleO_div _|>.mpr
  · simp_rw [div_sqrt, sqrt_eq_rpow]
    apply isLittleO_log_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop 0] with x hx
  apply sqrt_ne_zero _|>.mpr <;> linarith

theorem chebyshev_asymptotic_finsum :
    (fun x ↦ ∑ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), log p) ~[atTop] fun x ↦ x := by
  sorry

theorem chebyshev_asymptotic' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun t ↦ ε * t)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ (x : ℝ), θ x = x + f x := by
  have H := chebyshev_asymptotic
  rw [IsEquivalent, isLittleO_iff] at H
  let f := (fun x ↦ θ x - x)
  have integrable (x : ℝ) (hx : 2 ≤ x) : IntegrableOn f (Set.Icc 2 x) := by
    rw [IntegrableOn]
    refine Integrable.sub ?_ (ContinuousOn.integrableOn_Icc (continuousOn_id' _))
    refine extracted_1 x |>.mul_continuousOn (g' := fun t => t * log t ^ 2)
      (ContinuousOn.mul (continuousOn_id' _) (ContinuousOn.pow (continuousOn_log |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) 2)) isCompact_Icc |>.congr_fun_ae ?_
    simp only [measurableSet_Icc, ae_restrict_eq, EventuallyEq, eventually_inf_principal]
    refine .of_forall fun t ⟨ht1, _⟩ => ?_
    rw [div_mul_cancel₀]
    simpa only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      log_eq_zero, or_self_left, not_or] using ⟨by linarith, by linarith, by linarith⟩
  refine ⟨f, fun ε hε ↦ ?_, integrable, ?_⟩
  · rw [isLittleO_iff]
    intro c hc
    specialize @H (c * ε) (mul_pos hc hε)
    simp only [Pi.sub_apply, norm_eq_abs, mul_assoc, eventually_atTop, ge_iff_le, norm_mul,
      abs_of_pos hε, f] at H ⊢
    exact H
  refine fun r => by simp [f]

theorem chebyshev_asymptotic'' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun _ ↦ ε)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ x > (0 : ℝ), θ x = x + x * (f x) := by
  obtain ⟨f, hf1, inte, hf2⟩ := chebyshev_asymptotic'
  refine ⟨fun t => f t / t, fun ε hε ↦ ?_, ?_, ?_⟩
  · simp only [isLittleO_iff, norm_eq_abs, norm_mul, eventually_atTop, ge_iff_le,
      norm_div] at hf1 ⊢
    intro r hr
    replace hf1 := hf1 ε hε
    obtain ⟨N, hN⟩ := hf1 hr
    use |N| + 1
    intro x hx
    have hx' : |N| + 1 ≤ |x| := by rwa [abs_of_nonneg (a := x) (le_trans (by positivity) hx)]
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hx'), mul_assoc]
    exact hN x (le_trans (le_trans (le_abs_self N) (by linarith)) hx)

  · intro x hx
    refine inte x hx |>.mul_continuousOn (g' := fun t : ℝ => t⁻¹) (continuousOn_inv₀ |>.mono <| by
      rintro t ⟨ht1, _⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith) isCompact_Icc |>.congr_fun_ae <| .of_forall <| by simp [div_eq_mul_inv]
  intro x hx
  rw [hf2, mul_div_cancel₀]
  linarith

-- one could also consider adding a version with p < x instead of p \leq x

/-%%
\begin{proof}
\uses{WeakPNT, finsum_range_eq_sum_range}\leanok
From the prime number theorem we already have
$$ \sum_{n \leq x} \Lambda(n) = x + o(x)$$
so it suffices to show that
$$ \sum_{j \geq 2} \sum_{p^j \leq x} \log p = o(x).$$
Only the terms with $j \leq \log x / \log 2$ contribute, and each $j$ contributes at most $\sqrt{x} \log x$ to the sum, so the left-hand side is $O( \sqrt{x} \log^2 x ) = o(x)$ as required.
\end{proof}
%%-/

/-%%
\begin{corollary}[primorial_bounds]  \label{primorial_bounds}\lean{primorial_bounds}\leanok
We have
  $$ \prod_{p \leq x} p = \exp( x + o(x) )$$
\end{corollary}
%%-/
theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, p = exp (x + E x) := by
  use (fun x ↦ ∑ p ∈ (filter Nat.Prime (Iic ⌊x⌋₊)), log p - x)
  constructor
  · exact Asymptotics.IsEquivalent.isLittleO chebyshev_asymptotic
  intro x
  simp only [cast_prod, add_sub_cancel, exp_sum]
  apply Finset.prod_congr rfl
  intros x hx
  rw[Real.exp_log]
  rw[Finset.mem_filter] at hx
  norm_cast
  exact Nat.Prime.pos hx.right

theorem primorial_bounds_finprod :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), p = exp (x + E x) := by
  sorry

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  have := ContinuousOn.comp (f := fun t => t * log t ^ 2) (g := fun t => -t⁻¹)
    (s := {0, 1, -1}ᶜ) (t := {0}ᶜ)
    (ContinuousOn.comp (f := fun t : ℝ => t⁻¹) (g := fun t : ℝ => -t)
        (continuousOn_neg (s := {0}ᶜ))
        (continuousOn_inv₀ |>.mono <| by
          intro x hx
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
          tauto)
        (by
          intro x hx
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
            inv_eq_iff_eq_inv, inv_zero] at hx ⊢
          tauto))
    (ContinuousOn.mul (continuousOn_id' _)
      (by
        simp_rw [pow_two]
        apply ContinuousOn.mul <;>
        refine continuousOn_log |>.mono ?_ <;>
        intro x hx <;>
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx ⊢ <;>
        tauto))
    (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
        _root_.mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        log_eq_zero, or_self_left] at hx ⊢
      tauto)
  convert this using 1
  ext x
  simp only [Function.comp_apply, mul_inv_rev]
  rw [mul_comm x]
  field_simp

lemma continuousOn_log1 : ContinuousOn (fun x ↦ (log x ^ 2)⁻¹ * x⁻¹) {0, 1, -1}ᶜ := by
  refine continuousOn_log0.comp (f := fun x : ℝ ↦ -x) ?_ ?_ |>.congr fun x hx ↦ ?_
  · exact continuousOn_neg
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, neg_eq_zero,
      neg_inj] at hx ⊢
    rw [neg_eq_iff_eq_neg]
    tauto

  simp

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  rw [le_iff_lt_or_eq] at hb
  rcases hb with hb | rfl; swap
  · simp only [intervalIntegral.integral_same, sub_self, add_zero]
  · have := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x => (log x)⁻¹)
      (u' := fun x => -1 / (x * (log x)^2))
      (v := fun x => x)
      (v' := fun _ => 1) (a := a) (b := b)
      (fun x hx => by
        rw [Set.uIcc_eq_union, Set.Icc_eq_empty (lt_iff_not_ge |>.1 hb), Set.union_empty] at hx
        obtain ⟨hx1, _⟩ := hx
        simp only
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := fun t => t⁻¹) (x := x)
        · simpa using HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x) (hasDerivAt_id' (log x))
            (by simp only [ne_eq, log_eq_zero, not_or]; refine ⟨?_, ?_, ?_⟩ <;> linarith)
        · apply hasDerivAt_log; linarith)
      (fun x _ => hasDerivAt_id' x)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hb)]
        apply ContinuousOn.integrableOn_Icc
        refine continuousOn_log0.mono fun x hx ↦ ?_
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> linarith)
      (by
        constructor <;>
        apply MeasureTheory.integrable_const)
    simp only [mul_one] at this
    rw [this]
    simp_rw [neg_div, neg_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [intervalIntegral.integral_of_le (le_of_lt hb),
      intervalIntegral.integral_of_le (le_of_lt hb),
      ← MeasureTheory.integral_neg]
    simp_rw [neg_neg]
    refine integral_congr_ae ?_
    · rw [ae_restrict_eq, eventuallyEq_inf_principal_iff]
      · refine .of_forall fun x hx => ?_
        simp only [Set.mem_Ioc, one_div, mul_inv_rev, mul_assoc] at hx ⊢
        rw [inv_mul_cancel₀, mul_one]
        linarith
      exact measurableSet_Ioc

lemma integral_log_inv' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  have := integral_log_inv a b ha hb
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos hb, Set.uIoc_of_le hb,
    smul_eq_mul, one_mul] at this
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  rw [this]

lemma integral_log_inv'' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    (log a)⁻¹ * a + ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) + ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  rw [integral_log_inv' a b ha hb]
  group

lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  classical
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · simp only [Function.support_inv, measurableSet_Icc, Measure.restrict_apply']
    rw [show Function.support log ∩ Set.Icc 2 x = Set.Icc 2 x by
      rw [Set.inter_eq_right]
      intro t ht
      simp only [Set.mem_Icc, Function.mem_support, ne_eq, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩]
    simpa
  · simp only [measurableSet_Icc, ae_restrict_eq, EventuallyLE, eventually_inf_principal]
    refine .of_forall fun t (ht : _ ∧ _) => ?_
    simpa only [Pi.zero_apply, inv_nonneg] using log_nonneg (by linarith)
  · apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀
    · exact (continuousOn_log).mono <| by aesop

    · rintro t ⟨ht, -⟩
      simp only [ne_eq, log_eq_zero, not_or]
      exact ⟨by linarith, by linarith, by linarith⟩

lemma integral_log_inv_ne_zero (x : ℝ) (hx : 2 < x) :
    ∫ t in Set.Icc 2 x, (log t)⁻¹ ≠ 0 := by
  have := integral_log_inv_pos x hx
  linarith

/-%%
\begin{proof}\leanok
\uses{chebyshev_asymptotic}
  Exponentiate Theorem \ref{chebyshev_asymptotic}.
\end{proof}
%%-/
lemma pi_asymp_aux (x : ℝ) (hx : 2 ≤ x) : Nat.primeCounting ⌊x⌋₊ =
    (log x)⁻¹ * θ x + ∫ t in Set.Icc 2 x, θ t * (t * log t ^ 2)⁻¹ := by
  rw [th43_b _ hx]
  simp_rw [div_eq_mul_inv, Chebyshev.theta_eq_sum_Icc]
  ring_nf!

theorem pi_asymp'' :
    (fun x => (((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / (log t)) - (1 : ℝ))) =o[atTop]
    fun _ => (1 : ℝ) := by
  obtain ⟨f, hf, f_int, hf'⟩ := chebyshev_asymptotic''
  have eq1 : ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      (∫ t in Set.Icc 2 x,
        (t + t * f t) * (t * log t ^ 2)⁻¹) := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    rw [pi_asymp_aux x hx, hf' x (by linarith)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [hf' t (by grind)]

  replace eq1 :
    ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      ((∫ t in Set.Icc 2 x, (log t ^ 2)⁻¹) +
        (∫ t in Set.Icc 2 x, (f t) * (log t ^ 2)⁻¹)) := by
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1]
    congr
    simp_rw [mul_inv_rev, add_mul]
    rw [MeasureTheory.integral_add]
    · congr 1
      all_goals
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        field [show t ≠ 0 by grind]
    · apply IntegrableOn.mul_continuousOn
        (hg := ContinuousOn.integrableOn_Icc <| continuousOn_id' _)
        (hK := isCompact_Icc)
      apply continuousOn_log1.mono ?_
      intro y h
      simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at h ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [show (fun t ↦ t * f t * ((log t ^ 2)⁻¹ * t⁻¹)) =
        fun t ↦ f t * (t * (log t ^ 2)⁻¹ * t⁻¹) by ext; ring]
      apply IntegrableOn.mul_continuousOn (hK := isCompact_Icc)
      · apply f_int x (by linarith)
      · simp_rw [mul_assoc]
        refine ContinuousOn.mul (continuousOn_id' (Set.Icc 2 x)) ?_
        apply continuousOn_log1.mono ?_
        intro y h
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at h ⊢
        exact ⟨by linarith, by linarith, by linarith⟩

  simp_rw [mul_add] at eq1
  simp_rw [show ∀ (x : ℝ),
    (log x)⁻¹ * x + (log x)⁻¹ * (x * f x) +
    ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) =
    ((log x)⁻¹ * x + (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
    ((log x)⁻¹ * (x * f x) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)
    by intros; ring] at eq1

  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
      ((log x)⁻¹ * (x * f x) +
        ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) +
      C := by
    use ((log 2)⁻¹ * 2)
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1, ← integral_log_inv'' _ _ (by rfl) hx]
    ring
  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      (⌊x⌋₊.primeCounting / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - 1 =
      ((log x)⁻¹ * (x * f x) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) +
      C / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
    obtain ⟨C, hC⟩ := eq1
    use C
    filter_upwards [hC, eventually_gt_atTop 2] with x hC hx
    rw [hC]
    field [integral_log_inv_ne_zero]
  simp_rw [isLittleO_iff, eventually_atTop] at hf
  choose M hM using hf

  choose C hC using eq1
  simp only [eventually_atTop, ge_iff_le] at hC
  choose L hL using hC

  have ineq1 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c) (x : ℝ)
    (hx : max 2 (M ε hε hc) < x) :
    (log x)⁻¹ * x * |f x| ≤ c * ε * ((log x)⁻¹ * x) := by
    simp only [ge_iff_le, norm_eq_abs] at hM
    simp only [max_lt_iff] at hx
    specialize hM ε hε hc x (by linarith)
    rw [abs_of_pos hε] at hM
    rw [mul_comm (c * ε)]
    gcongr
    bound

  have ineq2 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c)  :
    ∃ (D : ℝ),
      ∀ (x : ℝ) (hx : max 2 (M ε hε hc) < x),
      |∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹| ≤
      c * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) + D := by
    have ineq (x : ℝ) (hx : max 2 (M ε hε hc) < x) :=
      calc |∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹|
        _ ≤ ∫ (t : ℝ) in Set.Icc 2 x, |f t * (log t ^ 2)⁻¹| :=
          norm_integral_le_integral_norm fun a ↦ f a * (log a ^ 2)⁻¹
        _ = ∫ (t : ℝ) in Set.Icc 2 x, |f t| * (log t ^ 2)⁻¹ := by
          apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
          rw [abs_mul, abs_of_nonneg (a := (log t ^ 2)⁻¹)]
          norm_num
          apply pow_nonneg
          exact log_nonneg <| by grind
        _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) +
            (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
            |f t| * (log t ^ 2)⁻¹) := by
          rw [← integral_union_ae, Set.Icc_union_Icc_eq_Icc]
          · exact le_max_left ..
          · exact le_of_lt hx
          · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton, volume_singleton]
            · exact le_max_left ..
            · exact le_of_lt hx
          · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
          · apply IntegrableOn.mul_continuousOn
            · simp_rw [← norm_eq_abs]
              rw [IntegrableOn, integrable_norm_iff (hf := f_int x (by
                  simp only [max_lt_iff] at hx
                  linarith) |>.mono _ le_rfl |>.1)]
              swap
              · apply Set.Icc_subset_Icc_right hx.le
              · refine f_int x (by
                  simp only [max_lt_iff] at hx
                  linarith) |>.mono ?_ le_rfl
                apply Set.Icc_subset_Icc_right hx.le
            · refine ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
              · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and,
                  not_le, isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
              · intro t ht
                simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                  pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
                exact ⟨by linarith, by linarith, by linarith⟩
            · exact isCompact_Icc
          · apply IntegrableOn.mul_continuousOn
            · simp_rw [← norm_eq_abs]
              rw [IntegrableOn, integrable_norm_iff (hf := f_int x (by
                  simp only [max_lt_iff] at hx
                  linarith) |>.mono _ le_rfl |>.1)]
              swap
              · apply Set.Icc_subset_Icc_left <| le_max_left ..
              · refine f_int x (by
                  simp only [max_lt_iff] at hx
                  linarith) |>.mono ?_ le_rfl
                apply Set.Icc_subset_Icc_left <| le_max_left ..
            · refine ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
              · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, max_le_iff, not_and,
                  not_le, isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
              · intro t ht
                simp only [Set.mem_Icc, max_le_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                  pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
                exact ⟨by linarith, by linarith, by linarith⟩
            · exact isCompact_Icc
        _ ≤ (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) +
            (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
            (c * ε) * (log t ^ 2)⁻¹) := by
            gcongr 1
            apply setIntegral_mono_on
            · apply IntegrableOn.mul_continuousOn
              · simp_rw [← norm_eq_abs]
                rw [IntegrableOn, integrable_norm_iff (hf := f_int x (by
                    simp only [max_lt_iff] at hx
                    linarith) |>.mono (Set.Icc_subset_Icc_left <| le_max_left 2 _) le_rfl |>.1)]
                exact f_int x (by
                    simp only [max_lt_iff] at hx
                    linarith) |>.mono (Set.Icc_subset_Icc_left <| le_max_left 2 _) le_rfl
              · refine ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
                · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, max_le_iff, not_and,
                    not_le, isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
                · intro t ht
                  simp only [Set.mem_Icc, max_le_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                    pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
                  exact ⟨by linarith, by linarith, by linarith⟩
              · exact isCompact_Icc
            · rw [IntegrableOn, integrable_const_mul_iff]
              · refine ContinuousOn.integrableOn_Icc <|
                  ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
                · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, max_le_iff, not_and, not_le,
                    isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
                · intro t ht
                  simp only [Set.mem_Icc, max_le_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                    pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
                  exact ⟨by linarith, by linarith, by linarith⟩
              · simp only [isUnit_iff_ne_zero, ne_eq, _root_.mul_eq_zero, not_or]
                exact ⟨by linarith, by linarith⟩
            · exact measurableSet_Icc
            · intro t ht
              simp only [Set.mem_Icc, sup_le_iff] at ht
              apply mul_le_mul_of_nonneg_right
              · refine hM ε hε hc t ht.1.2 |>.trans ?_
                simp only [norm_eq_abs, abs_of_pos hε, le_refl]
              · norm_num
                refine pow_nonneg (log_nonneg <| by linarith) 2
        _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) +
            ((c * ε) * ∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) := by
            congr 1
            exact integral_const_mul (c * ε) _
        _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) +
            ((c * ε) *
              ((∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) +
              ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) -
              ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
            simp only [add_sub_cancel_right]
        _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) +
            ((c * ε) *
              ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) -
                ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
            congr 3
            rw [add_comm, ← integral_union_ae, Set.Icc_union_Icc_eq_Icc]
            · exact le_max_left ..
            · exact le_of_lt hx
            · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton, volume_singleton]
              · exact le_max_left ..
              · exact le_of_lt hx
            · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
            · refine ContinuousOn.integrableOn_Icc <|
                ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
              · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le,
                  isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
              · intro t ht
                simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                  pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
                exact ⟨by linarith, by linarith, by linarith⟩
            · refine ContinuousOn.integrableOn_Icc <|
                ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
              · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, max_le_iff, not_and, not_le,
                  isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
              · intro t ht
                simp only [Set.mem_Icc, max_le_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                  pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
                exact ⟨by linarith, by linarith, by linarith⟩
          _ = ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) -
            (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) +
            ((c * ε) * (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) := by ring
          _ = ((c * ε) * (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) -
            (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
            ring
          _ = ((c * ε) * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
                ((log 2)⁻¹ * 2) - ((log x)⁻¹ * x))) +
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) -
            (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
            congr 2
            rw [integral_log_inv']
            · ring
            · rfl
            · simp only [max_lt_iff] at hx
              linarith
          _ = (c * ε) * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - ((log x)⁻¹ * x)) +
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
            |f t| * (log t ^ 2)⁻¹) -
            (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹) +
            (c * ε) * (((log 2)⁻¹ * 2))) := by
            ring

    exact ⟨_, fun x hx => ineq x hx⟩

  choose D hD using ineq2

  have ineq4 (const : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, |const / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| ≤ 1/2 * ε := by
    by_cases hconst : const = 0
    · subst hconst
      simp only [zero_div, abs_zero, one_div, inv_pos, ofNat_pos, mul_nonneg_iff_of_pos_left,
        eventually_atTop, ge_iff_le]
      use 0
      intro x _
      exact le_of_lt hε
    have ineq (x : ℝ) (hx : 2 < x) :=
      calc (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)
        _ ≥ (∫ (_ : ℝ) in Set.Icc 2 x, (log x)⁻¹) := by
          refine integral_mono_ae ?_ ?_ ?_
          · exact integrable_const _
          · refine ContinuousOn.integrableOn_Icc <|
              ContinuousOn.inv₀ (continuousOn_log |>.mono ?_) ?_
            · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le,
              isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
            · intro t ht
              simp only [Set.mem_Icc, ne_eq, log_eq_zero, not_or] at ht ⊢
              exact ⟨by linarith, by linarith, by linarith⟩
          · simp only [EventuallyLE, measurableSet_Icc, ae_restrict_eq, eventually_inf_principal,
            Set.mem_Icc, and_imp]
            refine .of_forall fun t ht1 ht2 => ?_
            rw [inv_le_inv₀]
            · exact strictMonoOn_log.monotoneOn (a := t) (b := x)
                (by simpa only [Set.mem_Ioi] using (by linarith))
                (by simpa only [Set.mem_Ioi] using (by linarith)) ht2
            · rw [Real.log_pos_iff] <;> linarith
            · rw [Real.log_pos_iff] <;> linarith
        _ = (x - 2) * (log x)⁻¹ := by
          rw [MeasureTheory.integral_const]
          simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, volume_Icc,
            smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff, sub_nonneg,
            inv_eq_zero, log_eq_zero, Measure.real]
          refine Or.inl (le_of_lt hx)

    simp_rw [abs_div]
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| / ((x - 2) * (log x)⁻¹) := by
      apply div_le_div₀
      · exact abs_nonneg _
      · rfl
      · apply mul_pos
        · linarith
        · norm_num
          rw [Real.log_pos_iff]
          · linarith
          · linarith
      · rw [abs_of_pos (integral_log_inv_pos _ hx)]
        exact ineq x hx
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| * (log x / ((x - 2))) := by
      refine ineq x hx |>.trans <| le_of_eq ?_
      field_simp
    have lim := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 (by norm_num)
    simp only [pow_one, one_mul, ← sub_eq_add_neg] at lim
    rw [tendsto_atTop_nhds] at lim
    specialize lim (Metric.ball 0 ((1/2) * ε / |const| : ℝ)) (by
      simp only [Metric.mem_ball, dist_self]
      apply _root_.div_pos
      · linarith
      · simpa only [abs_pos, ne_eq]) Metric.isOpen_ball
    obtain ⟨M, hM⟩ := lim
    rw [eventually_atTop]
    refine ⟨max 3 M, ?_⟩
    intro x hx
    simp only [Metric.mem_ball, dist_zero_right, max_le_iff, norm_eq_abs] at hM hx
    refine ineq x (by linarith) |>.trans ?_
    specialize hM x hx.2
    rw [abs_of_nonneg (by
      apply div_nonneg
      · refine log_nonneg (by linarith)
      · linarith)] at hM
    have ineq' : |const| * (log x / (x - 2)) < |const| * ((1/2) * ε / |const|) := by
      rw [mul_lt_mul_iff_right₀]
      · exact hM
      · simpa only [abs_pos, ne_eq]
    rw [mul_div_cancel₀] at ineq'
    · refine le_of_lt ineq'
    · simpa only [ne_eq, abs_eq_zero]

  simp only [eventually_atTop, ge_iff_le] at ineq4

  rw [isLittleO_iff]
  intro ε hε
  specialize ineq4 (|D ε hε (1/2) (by linarith)| + |C|) ε hε
  obtain ⟨B, hB⟩ := ineq4
  simp only [one_div, norm_eq_abs, norm_one, mul_one, eventually_atTop, ge_iff_le]
  use max 3 (max (L + 1) (max B (max 3 (@M ε hε (1/2) (by linarith) + 1))))

  intro x hx
  simp only [one_div, max_le_iff] at hx
  specialize hL x (by linarith)
  rw [hL]
  calc _
    _ ≤ |((log x)⁻¹ * (x * f x) / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      apply abs_add_three
    _ = |(log x)⁻¹ * (x * f x)| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      rw [abs_div, abs_div, abs_div]
    _ = |(log x)⁻¹ * (x * f x)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
        congr
        rw [abs_of_pos]
        apply integral_log_inv_pos
        linarith
    _ = |(log x)⁻¹ * (x * f x)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
        congr
        rw [abs_of_pos]
        apply integral_log_inv_pos
        linarith
    _ = |(log x)⁻¹ * (x * f x)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        congr
        rw [abs_of_pos]
        apply integral_log_inv_pos
        linarith
    _ = ((log x)⁻¹ * x * |f x|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        congr
        rw [abs_mul, abs_mul, abs_of_nonneg, abs_of_nonneg, mul_assoc]
        · linarith
        norm_num
        refine log_nonneg ?_
        linarith
    _ ≤ ((1/2) * ε * ((log x)⁻¹ * x)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        apply _root_.add_le_add (h₂ := le_rfl)
        apply _root_.add_le_add (h₂ := le_rfl)
        apply div_le_div₀
        · apply mul_nonneg <;> try apply mul_nonneg <;> try linarith
          norm_num; exact log_nonneg <| by linarith
        · exact ineq1 ε hε (1/2) (by linarith) x (by simpa using ⟨by linarith, by linarith⟩)
        · apply integral_log_inv_pos
          linarith
        · rfl
    _ ≤ ((1/2) * ε * ((log x)⁻¹ * x)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        ((1/2) * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) +
          D ε hε (1/2) (by linarith)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        apply _root_.add_le_add (h₂ := le_rfl)
        apply _root_.add_le_add (h₁ := le_rfl)
        apply div_le_div₀
        · exact le_trans (abs_nonneg _) <|
            hD ε hε (1/2) (by linarith) x (by simpa using ⟨by linarith, by linarith⟩)
        · exact hD ε hε (1/2) (by linarith) x (by simpa using ⟨by linarith, by linarith⟩)
        · apply integral_log_inv_pos
          linarith
        · rfl
    _ ≤ (((1/2) * ε * ((log x)⁻¹ * x)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        ((1/2) * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x)) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹))  +
        (D ε hε (1/2) (by linarith) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) := by
        rw [_root_.add_div, ← add_assoc, ← add_assoc]
    _ = ((1/2) * ε * ((log x)⁻¹ * x + (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x)) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (D ε hε (1/2) (by linarith) + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      simp only [← _root_.add_div, ← _root_.mul_add]
      congr 1
      ring
    _ = ((1/2) * ε * (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (D ε hε (1/2) (by linarith) + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      congr 1
      ring
    _ = (1/2) * ε + (D ε hε (1/2) (by linarith) + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      congr 1
      rw [mul_div_assoc, div_self, mul_one]
      apply integral_log_inv_ne_zero
      linarith
    _ ≤ (1/2) * ε + (|D ε hε (1/2) (by linarith)| + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      apply _root_.add_le_add (h₁ := le_rfl)
      apply div_le_div₀
      · apply add_nonneg <;> exact abs_nonneg _
      · apply _root_.add_le_add (h₂ := le_rfl); exact le_abs_self _
      · apply integral_log_inv_pos; linarith
      · rfl
    _ ≤ (1/2) * ε + (1/2) * ε := by
      apply _root_.add_le_add (h₁ := le_rfl)
      specialize hB x (by linarith)
      rw [abs_div, abs_of_nonneg, abs_of_pos (a := ∫ _ in _, _)] at hB
      · exact hB
      · apply integral_log_inv_pos; linarith
      · apply add_nonneg <;> apply abs_nonneg
    _ = ε := by
      rw [← mul_two, mul_comm _ ε, _root_.mul_assoc]
      simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel, mul_one]

/-%%
\begin{theorem}[pi_asymp]\label{pi_asymp}\lean{pi_asymp}\leanok
There exists a function $c(x)$ such that $c(x) = o(1)$ as $x \to \infty$ and
$$ \pi(x) = (1 + c(x)) \int_2^x \frac{dt}{\log t}$$
for all $x$ large enough.
\end{theorem}
%%-/
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  simp only [one_div, add_sub_cancel, eventually_atTop, ge_iff_le]
  refine ⟨3, fun x hx => ?_⟩
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, div_mul_cancel₀]
  exact (integral_log_inv_pos x (by linarith)).ne'

/-%%
\begin{proof}\leanok
\uses{chebyshev_asymptotic}
We have the identity
$$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
+ \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
as can be proven by interchanging the sum and integral and using the fundamental theorem of calculus.  For any $\eps$, we know from Theorem \ref{chebyshev_asymptotic} that there is $x_\eps$ such that
$\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
$$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
+ \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate this after an integration by parts as
$$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
$$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
for $x$ large enough, giving the claim.
\end{proof}
%%-/

lemma pi_alt_Oaux1 : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc 2 √x, 1 / log t ^ 2 ≤ c * √x := by
  use 1 / (log 2) ^ 2
  rw [eventually_atTop]
  use 4
  intro b hb
  simp only [one_div]
  trans ((log 2) ^ 2)⁻¹ * (b.sqrt - 2)
  · have hb : 2 ≤ √b := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]
        norm_num; linarith
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb]
    trans ∫ (t : ℝ) in (2)..√b, (log 2 ^ 2)⁻¹
    · apply intervalIntegral.integral_mono_on hb
      · apply ContinuousOn.intervalIntegrable_of_Icc hb
        apply ContinuousOn.inv₀
        · apply ContinuousOn.pow
          apply ContinuousOn.log continuousOn_id
          intro x hx
          simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
          linarith
        · intro x hx
          simp at hx ⊢
          constructor <;> try linarith
          constructor <;> linarith
      · apply intervalIntegral.intervalIntegrable_const
      · intro x hx
        simp only [Set.mem_Icc] at hx
        rw [inv_le_inv₀]
        · apply pow_le_pow_left₀
          · apply log_nonneg (by linarith)
          · rw [log_le_log_iff] <;> linarith
        · apply pow_pos
          rw [Real.log_pos_iff] <;> linarith
        · apply pow_pos
          rw [Real.log_pos_iff] <;> linarith
    · rw [intervalIntegral.integral_const, smul_eq_mul]
      linarith
  · rw [mul_sub]
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right, ofNat_pos,
      mul_nonneg_iff_of_pos_right, inv_nonneg]
    positivity

lemma pi_alt_Oaux2 : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc (√x) x, 1 / log t ^ 2 ≤ c * (x / log x ^ 2) := by
  use 4
  rw [eventually_atTop]
  use 4
  intro b hb
  simp only [one_div]
  trans ((log √b) ^ 2)⁻¹ * (b - b.sqrt)
  · have hb : 2 ≤ √b ∧ √b ≤ b := by
        constructor
        · rw [Real.le_sqrt (by norm_num) (by linarith)]
          norm_num; linarith
        · rw [Real.sqrt_le_left (by linarith)]
          apply le_self_pow₀ <;> linarith
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.2]
    trans ∫ (t : ℝ) in √b..b, (log √b ^ 2)⁻¹
    · apply intervalIntegral.integral_mono_on hb.2
      · apply ContinuousOn.intervalIntegrable_of_Icc hb.2
        apply ContinuousOn.inv₀
        · apply ContinuousOn.pow
          apply ContinuousOn.log continuousOn_id
          intro x hx
          simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
          linarith
        · intro x hx
          simp at hx ⊢
          constructor <;> try linarith
          constructor <;> linarith
      · apply intervalIntegral.intervalIntegrable_const
      · intro x hx
        simp only [Set.mem_Icc] at hx
        rw [inv_le_inv₀]
        · apply pow_le_pow_left₀
          · apply log_nonneg (by linarith)
          · rw [log_le_log_iff] <;> linarith
        · apply pow_pos
          rw [Real.log_pos_iff] <;> linarith
        · apply pow_pos
          rw [Real.log_pos_iff] <;> linarith
    · rw [intervalIntegral.integral_const, smul_eq_mul]
      linarith
  · rw [mul_sub, Real.log_sqrt (by linarith), div_pow, ← one_div, one_div_div, mul_comm, mul_div,
      mul_comm, mul_div, show (2 : ℝ) ^ 2 = 4 by norm_num]
    suffices 0 ≤ 4 / log b ^ 2 * √b by linarith
    positivity

lemma inv_div_log_asy : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2 ≤ c * (x / log x ^ 2) := by
  obtain ⟨c1, hc1⟩ := pi_alt_Oaux1
  obtain ⟨c2, hc2⟩ := pi_alt_Oaux2
  have h := @isLittleO_log_rpow_rpow_atTop (1 / 2) 2 (by norm_num)
  rw [isLittleO_iff] at h
  specialize h (show 0 < 1 by norm_num)
  rw [eventually_atTop] at h hc1 hc2
  obtain ⟨c0, hc0⟩ := h
  obtain ⟨c1', hc1⟩ := hc1
  obtain ⟨c2', hc2⟩ := hc2
  use c1 + c2
  rw [eventually_atTop]
  use max 5 (max c0 (max c1' c2'))
  intro x hx
  have hx' : 2 < √x ∧ √x ≤ x := by
    constructor
    · rw [Real.lt_sqrt (by norm_num)]
      linarith [(le_of_max_le_left hx)]
    · rw [Real.sqrt_le_left (by linarith [(le_of_max_le_left hx)])]
      apply le_self_pow₀ <;> linarith [(le_of_max_le_left hx)]
  calc
  _ = (∫ (t : ℝ) in (2)..(√x), 1 / log t ^ 2) + ∫ (t : ℝ) in (√x)..x, 1 / log t ^ 2 := by
    simp only [one_div]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [(le_of_max_le_left hx)]),
      ← intervalIntegral.integral_add_adjacent_intervals (b := √x)]
    · apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [hx'.1])
      apply ContinuousOn.inv₀
      · apply ContinuousOn.pow
        apply ContinuousOn.log continuousOn_id
        intro x hx
        simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
        linarith
      · intro x hx
        simp at hx ⊢
        constructor <;> try linarith
        constructor <;> linarith
    · apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [hx'.2])
      apply ContinuousOn.inv₀
      · apply ContinuousOn.pow
        apply ContinuousOn.log continuousOn_id
        intro x hx
        simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
        linarith
      · intro x hx
        simp at hx ⊢
        constructor <;> try linarith
        constructor <;> linarith
  _ ≤ c1 * √x + c2 * (x / log x ^ 2) := by
    specialize hc1 x (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hx)))
    specialize hc2 x (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hx)))
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [hx'.1]) ] at hc1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx'.2] at hc2
    apply _root_.add_le_add hc1 hc2
  _ ≤ (c1 + c2) * (x / log x ^ 2) := by
    specialize hc0 x (le_of_max_le_left (le_of_max_le_right hx))
    simp only [rpow_two, norm_pow, norm_eq_abs, sq_abs, one_mul] at hc0
    rw [abs_eq_self.2] at hc0
    · rw [add_mul]
      apply _root_.add_le_add _ (by linarith)
      rw [mul_le_mul_iff_of_pos_left]
      · rw [le_div_iff₀]
        · trans √x * x ^ (1 / 2 : ℝ)
          · apply mul_le_mul (by linarith) hc0 (by positivity) (by positivity)
          · rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt (by linarith)]
        · apply pow_pos
          apply Real.log_pos
          linarith
      · by_contra! h
        specialize hc1 x (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hx)))
        have : ∫ (t : ℝ) in Set.Icc 2 √x, 1 / log t ^ 2 > 0 := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le]
          · apply intervalIntegral.intervalIntegral_pos_of_pos_on
            · simp only [one_div]
              apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
              apply ContinuousOn.inv₀
              · apply ContinuousOn.pow
                apply ContinuousOn.log continuousOn_id
                intro x hx
                simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
                linarith
              · intro x hx
                simp at hx ⊢
                constructor <;> try linarith
                constructor <;> linarith
            · intro x hx
              simp only [Set.mem_Ioo, one_div, inv_pos] at hx ⊢
              apply pow_pos
              apply Real.log_pos
              linarith
            · linarith
          · linarith
        have : c1 * √x ≤ 0 := by
          apply mul_nonpos_of_nonpos_of_nonneg h (by positivity)
        linarith
    · apply rpow_nonneg
      linarith

lemma integral_log_inv_pialt (x : ℝ) (hx : 4 ≤ x) : ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t =
    x / log x - 2 / log 2 + ∫ (t : ℝ) in Set.Icc 2 x, 1 / (log t) ^ 2 := by
  have := integral_log_inv 2 x (by norm_num) (by linarith)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [hx]),
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [hx]),
    ← mul_one_div, one_div, ← mul_one_div, one_div]
  simp only [one_div, this, mul_comm]

lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  obtain ⟨c, hc⟩ := inv_div_log_asy
  use fun x => ((∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2) - 2 / log 2) * log x / x
  constructor
  · rw [isLittleO_iff]
    intro m hm
    rw [eventually_atTop] at *
    obtain ⟨a, ha⟩ := hc
    have h1 : ∃ N, ∀ x ≥ N, |2 / log 2 * log x / x| ≤ m / 2 := by
      have h := Real.isLittleO_log_id_atTop
      rw [isLittleO_iff] at h
      have h' : log 2 * m / 4 > 0 := by
        apply _root_.div_pos _ (by norm_num)
        apply mul_pos _ hm
        apply Real.log_pos (by norm_num)
      specialize h h'
      rw [eventually_atTop] at h
      obtain ⟨a, ha⟩ := h
      use max a 1
      intro x hx
      specialize ha x (by aesop)
      rw [abs_div, div_le_iff₀]
      · simp only [norm_eq_abs, id_eq] at ha
        rw [abs_mul, mul_comm, ← le_div_iff₀]
        · suffices log 2 * m / 4 * |x| =  m / 2 * |x| / |2 / log 2| by rwa [← this]
          rw [abs_div, show (4 : ℝ) = 2 * 2 by norm_num, show |(2 : ℝ)| = 2 by norm_num,
            show |log 2| = log 2 by simp only [abs_eq_self]; apply log_nonneg; norm_num]
          field_simp
        · simp only [abs_pos, ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, log_eq_zero,
          OfNat.ofNat_ne_one, false_or]
          norm_num
      · simp only [abs_pos, ne_eq]
        linarith [le_of_max_le_right hx]
    have h2 : ∃ N, ∀ x ≥ N, |c| / |log x| ≤ m / 2 := by
      use max 2 (Real.exp (2 * |c| / m))
      intro x hx
      rw [div_le_iff₀, mul_comm, ← div_le_iff₀ (by linarith)]
      · rw [← div_mul, mul_comm, mul_div]
        nth_rw 2 [abs_eq_self.2]
        · rw [Real.le_log_iff_exp_le (by linarith [le_of_max_le_left hx])]
          linarith [le_of_max_le_right hx]
        · apply log_nonneg
          linarith [le_of_max_le_left hx]
      · simp only [abs_pos, ne_eq, log_eq_zero, not_or]
        have : 2 ≤ x := by aesop
        constructor <;> try linarith
        constructor <;> linarith
    obtain ⟨N, hN⟩ := h1
    obtain ⟨N', hN'⟩ := h2
    use max (max a 2) (max N N')
    intro x hx
    rw [sub_mul, sub_div]
    simp only [norm_eq_abs, norm_one, mul_one]
    trans |(∫ (t : ℝ) in Set.Icc 2 x, 1/ (log t ^ 2)) * log x / x| + |2 / log 2 * log x / x|
    · exact abs_sub _ _
    · specialize ha x (by aesop)
      specialize hN x (by aesop)
      specialize hN' x (by aesop)
      calc
      _ ≤ |c| * |x / log x ^ 2| * |log x / x| + |2 / log 2 * log x / x| := by
        apply _root_.add_le_add _ (by linarith)
        rw [← mul_div, abs_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        trans |c * (x / log x ^ 2)|
        · apply abs_le_abs_of_nonneg _ ha
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
            (by aesop)]
          apply intervalIntegral.integral_nonneg (by aesop)
          intro y _
          positivity
        · rw [abs_mul]
      _ ≤ m / 2 + m / 2 := by
        apply _root_.add_le_add _ hN
        rw [mul_assoc, ← abs_mul,
          show x / log x ^ 2 * (log x / x) = (x * log x) / (x * log x) / log x by ring, div_self]
        · rwa [← abs_mul, mul_one_div, abs_div]
        · apply mul_ne_zero
          · suffices 2 ≤ x by linarith
            aesop
          · have : 2 ≤ x := by aesop
            apply log_ne_zero_of_pos_of_ne_one <;> linarith
      _ ≤ m := by linarith
  · rw [eventually_atTop] at *
    obtain ⟨a, _⟩ := hc
    use max 4 a
    intro x hx
    rw [integral_log_inv_pialt x (le_of_max_le_left hx), add_mul, _root_.add_div, sub_add, sub_eq_add_neg,
      one_mul, neg_sub]
    congr
    rw [← mul_div, ← mul_div, mul_assoc]
    nth_rw 1 [← mul_one (a := (∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2) - 2 / log 2)]
    congr
    rw [div_mul_eq_mul_div, mul_div, div_div, mul_comm, div_self]
    apply mul_ne_zero
    · linarith [le_of_max_le_left hx]
    · simp only [ne_eq, log_eq_zero, not_or]
      constructor <;> try linarith [le_of_max_le_left hx]
      constructor <;> linarith [le_of_max_le_left hx]

/-%%
\begin{corollary}[pi_alt]\label{pi_alt}\lean{pi_alt}\leanok  One has
$$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
as $x \to \infty$.
\end{corollary}
%%-/
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  obtain ⟨f, hf, h⟩ := pi_asymp
  obtain ⟨f', hf', h'⟩ := integral_div_log_asymptotic
  rw [eventually_atTop] at h h'
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  set C := max 2 (max c c')
  use (fun x => if x < C then (log x / x) * ⌊x⌋₊.primeCounting - 1 else (f x + f' x + (f x) * (f' x)))
  constructor
  · rw [isLittleO_iff] at *
    intro m hm
    rw [eventually_atTop]
    set C' := min (m / 4) 1
    have h1 : 0 < C' := by
      apply lt_min
      · linarith
      · norm_num
    specialize hf h1
    specialize hf' h1
    rw [eventually_atTop] at hf hf'
    obtain ⟨a1, hf⟩ := hf
    obtain ⟨a2, hf'⟩ := hf'
    use max C (max a1 a2)
    intro x hx
    have hC : C ≤ x := by linarith [le_of_max_le_left hx]
    rw [← not_lt] at hC
    simp only [hC, ↓reduceIte, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      ge_iff_le]
    trans |f x + f' x| + |f x| * |f' x|
    · rw [← abs_mul]
      exact abs_add_le _ _
    · trans |f x| + |f' x| + |f x| * |f' x|
      · apply _root_.add_le_add _ (by linarith)
        exact abs_add_le _ _
      · specialize hf x (le_of_max_le_left (le_of_max_le_right hx))
        specialize hf' x (le_of_max_le_right (le_of_max_le_right hx))
        simp only [norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at hf hf'
        have h1 : |f x| ≤ m / 4 := by aesop
        have h2 : |f' x| ≤ m / 4 := by aesop
        have h3 : |f x| * |f' x| ≤ m / 4 := by
          trans |f x|
          · suffices |f' x| ≤ 1 by
              apply mul_le_of_le_one_right (by positivity) this
            aesop
          · exact h1
        linarith
  · intro x
    by_cases hx : x < C
    · simp only [hx, ↓reduceIte, add_sub_cancel]
      by_cases hx' : x = 0 ∨ |x| = 1
      · rcases hx' with (rfl | hx)
        · simp only [floor_zero, primeCounting_zero, CharP.cast_eq_zero, log_zero, div_zero,
            mul_zero]
        · have hx := eq_or_eq_neg_of_abs_eq hx
          rcases hx with (hx | hx)
          · simp only [hx, floor_one, primeCounting_one, CharP.cast_eq_zero, log_one,
            div_one, mul_zero, mul_one, div_zero]
          · simp only [hx, log_neg_eq_log, log_one, zero_div, zero_mul,
            mul_neg, mul_one, neg_zero, div_zero, cast_eq_zero,
            primeCounting_eq_zero_iff, ge_iff_le]
            suffices ⌊(-1 : ℝ)⌋₊ = 0  by rw [this]; linarith
            rw [Nat.floor_eq_zero]
            norm_num
      · simp only [not_or] at hx'
        rw [← mul_div, mul_comm, ← mul_assoc, mul_div, div_mul_eq_mul_div (a := x), div_div]
        nth_rw 2 [mul_comm]
        rw [div_self, one_mul]
        apply mul_ne_zero
        · simp only [ne_eq, log_eq_zero, not_or]
          rw [show (1 : ℝ) = |1| by simp, abs_eq_abs] at hx'
          simp only [not_or] at hx'
          exact hx'
        · exact hx'.1
    · simp only [hx, ↓reduceIte]
      simp only [not_lt] at hx
      specialize hc x (le_of_max_le_left (le_of_max_le_right hx))
      specialize hc' x (le_of_max_le_right (le_of_max_le_right hx))
      rw [intervalIntegral.integral_of_le ((le_max_left _ _).trans hx),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hc
      rw [hc, hc', mul_div]
      congr 1
      ring

/-%%
\begin{proof}\leanok
\uses{pi_asymp}
An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} + \int_2^x \frac{dt}{\log^2 t}.$$
We have the crude bounds
$$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
and
$$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
and combining all this we obtain
$$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
$$ = (1+o(1)) \frac{x}{\log x}$$
and the claim then follows from Theorem \ref{pi_asymp}.
\end{proof}
%%-/

/-%%
Let $p_n$ denote the $n^{th}$ prime.

\begin{proposition}[pn_asymptotic]\label{pn_asymptotic}\lean{pn_asymptotic}\leanok
 One has
  $$ p_n = (1+o(1)) n \log n$$
as $n \to \infty$.
\end{proposition}
%%-/

set_option maxHeartbeats 300000 in
-- A large number of limit calculations necessitated a heartbeat limit increase. -
open Filter in
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, n > 1 → Nat.nth Nat.Prime n = (1 + c n) * n * log n := by
  let c : ℕ → ℝ := fun n ↦ (Nat.nth Nat.Prime n) / (n * log n) - 1
  refine ⟨c, ?_, ?_⟩
  swap
  · intro n hn
    have : log n ≠ 0 := by rw [Real.log_ne_zero]; rify at hn; grind
    simp [c]
    field_simp
  rw [Asymptotics.isLittleO_one_iff, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ c', hc', hcount ⟩ := pi_alt
  have hlog := Tendsto.comp Real.tendsto_log_atTop tendsto_natCast_atTop_atTop

  have h1 : ∀ᶠ n:ℕ in atTop, n > 0 := by
    rw [eventually_atTop]; use 1; grind
  have h2 : ∀ᶠ n:ℕ in atTop, log n > 0 := by
    rw [eventually_atTop]; use 2; intro n hn; apply Real.log_pos; norm_num; linarith

  have h3 : ∀ᶠ n:ℕ in atTop, ε < 1 → (1 + c' ((1 - ε) * n * log n)) * ((1 - ε) * n * log n) / log ((1 - ε) * n * log n) ≤ n := by
    rcases lt_or_ge ε 1 with hε' | hε'
    swap
    · apply Filter.Eventually.of_forall
      grind
    suffices ∀ᶠ n:ℕ in atTop, ((1 + c' ((1 - ε) * n * log n)) * (1 - ε)) * (log n / log ((1 - ε) * n * log n)) ≤ 1 by
      apply Eventually.mono this
      intro n hn _
      replace hn := mul_le_mul_of_nonneg_right hn (show 0 ≤ (n:ℝ) by positivity)
      convert hn using 1 <;> ring
    apply Tendsto.eventually_le_const (show 1-ε < 1 by linarith)
    convert Tendsto.mul (a := 1-ε) (b := 1) ?_ ?_ using 2
    · simp
    · convert Tendsto.mul_const (c := 1) (b := 1-ε) ?_ using 2
      · simp
      convert Tendsto.const_add (c := 0) (b := 1) (f := fun (n:ℕ) ↦ c' ((1-ε) * n * log n)) ?_ using 2
      · simp
      rw [Asymptotics.isLittleO_one_iff] at hc'
      apply Tendsto.comp hc'
      apply Tendsto.atTop_mul_atTop₀ _ hlog
      apply Tendsto.const_mul_atTop' (by linarith) tendsto_natCast_atTop_atTop
    rw [←tendsto_inv_iff₀ (by positivity)]
    simp only [inv_div, inv_one]
    suffices Tendsto (fun n:ℕ ↦ (log (1 - ε)/log n) + (log (log n) / log n) + 1) atTop (nhds 1) by
      apply (Filter.tendsto_congr' _).mp this
      filter_upwards [h1, h2]
      intro n h1n h2n
      field_simp
      have : 1-ε ≠ 0 := by linarith
      rw [Real.log_mul, Real.log_mul] <;> try positivity
    convert Tendsto.add_const (c := 0) (b := 1) (f := fun (n:ℕ) ↦ (log (1 - ε)/log n) + (log (log n) / log n) ) ?_
    · simp
    convert Tendsto.add (a := 0) (b := 0) (f := fun (n:ℕ) ↦ (log (1 - ε)/log n)) ?_ ?_
    · simp
    · apply Filter.Tendsto.const_div_atTop hlog
    apply Tendsto.comp (g := fun x ↦ log x / x) _ hlog
    convert Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by positivity) with n <;> simp
  have h4 : ∀ᶠ n:ℕ in atTop, 1 < (1+ε) * n * log n := by
    rw [eventually_atTop]; use 3; intro n hn
    apply_rules [one_lt_mul_of_lt_of_le]
    · linarith
    · norm_num; omega
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    rify at hn; linarith
  have h2a : ∀ᶠ n:ℕ in atTop, log ((1+ε)*(log n)*n) > 0 := by
    filter_upwards [h4]
    intro n hn
    apply Real.log_pos
    convert hn using 1
    ring
  have h5 : ∀ᶠ n:ℕ in atTop, n < (1 + c' ((1 + ε) * n * log n - 1)) * ((1 + ε) * n * log n - 1) / log ((1 + ε) * n * log n - 1) := by
      suffices ∀ᶠ n:ℕ in atTop, (1 + c' ((1 + ε) * n * log n - 1)) * (((1 + ε) * log n - 1/n) / log ((1 + ε) * n * log n - 1)) > 1 by
        filter_upwards [h1, this]
        intro n hn₀ hn
        replace hn := mul_lt_mul_of_pos_right hn (show 0 < (n:ℝ) by  positivity)
        convert hn using 1 <;> field_simp
      apply Tendsto.eventually_const_lt (show 1+ε > 1 by linarith)
      convert Tendsto.mul (a := 1) (b := 1+ε) ?_ ?_ using 2
      · simp
      · convert Tendsto.const_add (c := 0) (b := 1) (f := fun (n:ℕ) ↦ c' ((1+ε) * n * log n - 1)) ?_ using 2
        · simp
        rw [Asymptotics.isLittleO_one_iff] at hc'
        apply Tendsto.comp hc'
        apply Tendsto.comp (g := fun x ↦ (1+ε) * x * log x - 1) _ tendsto_natCast_atTop_atTop
        convert Tendsto.comp (g := fun x ↦ (1+ε) * x - 1) (y := Filter.atTop) (f := fun x ↦ x * log x) ?_ ?_ using 2 with x
        · grind
        · have deg_1 : (1:ℕ) ≤ ((1 + ε) • Polynomial.X - 1: Polynomial ℝ).degree := by
            apply Polynomial.le_degree_of_ne_zero
            simp [Polynomial.coeff_one]
            grind
          have deg_2 : ((1 + ε) • Polynomial.X - 1: Polynomial ℝ).degree ≤ (1:ℕ) := by
            apply (Polynomial.degree_sub_le _ _).trans
            simp only [Polynomial.degree_one, cast_one, sup_le_iff, zero_le_one, and_true]
            apply (Polynomial.degree_smul_le _ _).trans
            simp
          have deg_3 : ((1 + ε) • Polynomial.X - 1: Polynomial ℝ).degree = (1:ℕ) := by order
          have deg_4 : ((1 + ε) • Polynomial.X - 1: Polynomial ℝ).natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some deg_3
          convert Polynomial.tendsto_atTop_of_leadingCoeff_nonneg ((1+ε) • Polynomial.X - 1: Polynomial ℝ) ?_ ?_ with x
          · simp
          · simp [deg_3]
          simp [←Polynomial.coeff_natDegree, deg_4, Polynomial.coeff_one]
          linarith
        apply Filter.Tendsto.atTop_mul_atTop₀ _ Real.tendsto_log_atTop
        exact fun ⦃U⦄ a ↦ a
      let f1 : ℕ → ℝ := fun x ↦ 1 - ((1+ε)* x * log x)⁻¹
      let f2 : ℕ → ℝ := fun x ↦ log ((1+ε)*x*log x - 1) / log ((1+ε)*x*log x)
      let f3 : ℕ → ℝ := fun x ↦ log ((1+ε)*x*log x) / log x
      have h6 : Tendsto (fun n:ℕ ↦ (1 + ε) * n * log n) atTop atTop := by
        apply Tendsto.comp (g := fun x ↦ (1+ε)*x*log x) _ tendsto_natCast_atTop_atTop
        apply Tendsto.atTop_mul_atTop₀ _ Real.tendsto_log_atTop
        apply Tendsto.const_mul_atTop' (by linarith)
        exact fun ⦃U⦄ a ↦ a

      suffices Tendsto (fun n ↦ (1+ε) * ((f1 n) / (f2 n * f3 n))) Filter.atTop (nhds (1+ε)) by
        apply (Filter.tendsto_congr' _).mp this
        filter_upwards [h1, h2, h2a]
        intro n h1n h2n h2an
        simp [f1, f2, f3]
        field_simp
      convert Tendsto.const_mul (c := 1) (b := 1+ε) ?_ using 2
      · simp
      convert Tendsto.div (a:=1) (b:=1) (f:=f1) (g:=f2*f3) ?_ ?_ (by positivity)
      · simp
      · unfold f1
        convert Tendsto.const_sub 1 (c := 0) (f := fun (x:ℕ) ↦ ((1+ε)*x*log x)⁻¹) ?_
        · simp
        apply Tendsto.comp tendsto_inv_atTop_zero h6
      convert Tendsto.mul (a := 1) (b := 1) (f := f2) ?_ ?_ using 2
      · simp
      · suffices Tendsto (fun n:ℕ ↦ log (1 - ((1+ε)*n*log n)⁻¹) / log ((1+ε)*n*log n) + 1) atTop (nhds 1) by
          apply (Filter.tendsto_congr' _).mp this
          filter_upwards [h1, h2, h2a]
          intro n h1n h2n h2an
          have : log ((1 + ε) * n * log n) > 0 := by convert h2an using 2; ring
          have : 1 < (1+ε)*n*log n := by
            rw [←Real.log_pos_iff]
            · order
            positivity
          unfold f2; field_simp
          rw [←Real.log_mul] <;> try grind
          congr
          field_simp
        convert Tendsto.add_const (c := 0) (b := 1) (f := fun n:ℕ ↦ log (1 - ((1 + ε) * n * log n)⁻¹) / log ((1 + ε) * n * log n)) ?_
        · simp
        apply Tendsto.div_atTop (a := 0)
        · convert Filter.Tendsto.log (x := 1) ?_ (by positivity)
          · simp
          convert Tendsto.const_sub 1 (c := 0) (f := fun (x:ℕ) ↦ ((1+ε)*x*log x)⁻¹) ?_
          · simp
          apply Tendsto.comp tendsto_inv_atTop_zero h6
        apply Tendsto.comp Real.tendsto_log_atTop h6
      suffices Tendsto (fun n:ℕ ↦ (log (1 + ε)/log n) + (log (log n) / log n) + 1) atTop (nhds 1) by
        apply (Filter.tendsto_congr' _).mp this
        filter_upwards [h1, h2]
        intro n h1n h2n
        unfold f3; field_simp
        rw [Real.log_mul, Real.log_mul] <;> try positivity
      convert Tendsto.add_const (c := 0) (b := 1) (f := fun (n:ℕ) ↦ (log (1 + ε)/log n) + (log (log n) / log n) ) ?_
      · simp
      convert Tendsto.add (a := 0) (b := 0) (f := fun (n:ℕ) ↦ (log (1 + ε)/log n)) ?_ ?_
      · simp
      · apply Filter.Tendsto.const_div_atTop hlog
      apply Tendsto.comp (g := fun x ↦ log x / x) _ hlog
      convert Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by positivity) with n <;> simp
  filter_upwards [h1, h2, h3, h4, h5]
  intro n h1n h2n h3n h4n h5n

  have hpn : nth Nat.Prime n > 0 := by
    have := Nat.add_two_le_nth_prime n
    linarith
  simp only [dist_zero_right, norm_eq_abs, abs_lt, neg_lt_sub_iff_lt_add, c]
  constructor
  · rcases lt_or_ge ε 1 with hε' | hε'
    swap
    · have : 0 < (nth Nat.Prime n) / (n * log n) := by positivity
      grind
    let x := ⌊ (1-ε) * n * log n ⌋₊
    suffices h: x+1 ≤ nth Nat.Prime n by
      grw [←h]
      rw [←sub_lt_iff_lt_add', lt_div_iff₀ (by positivity)]
      simp only [cast_add, cast_one]
      convert Nat.lt_floor_add_one ((1 - ε) * (↑n * log ↑n)) using 4
      ring
    rw [←Nat.count_le_iff_le_nth Nat.infinite_setOf_prime]
    change x.primeCounting ≤ n
    rify; rw [hcount]; grind
  let x := ⌊ (1+ε) * n * log n ⌋₊
  suffices h: nth Nat.Prime n < x by
    calc
      _ < x / (↑n * log ↑n) - 1 := by gcongr
      _ ≤ _ := by
        rw [sub_le_iff_le_add', div_le_iff₀ (by positivity)]
        convert Nat.floor_le _ using 1
        · ring
        positivity
  apply Nat.nth_lt_of_lt_count
  replace : x = ⌊ (1+ε) * n * log n - 1⌋₊+1 := by
    rw [←Nat.floor_add_one]
    · unfold x; congr; linarith
    linarith
  rw [this]; change n < ⌊ (1+ε) * n * log n - 1⌋₊.primeCounting
  rify; rwa [hcount]

/-%%
\begin{proof}
\uses{pi_alt}\leanok
Use Corollary \ref{pi_alt} to show that for any $\eps>0$, and for $n$ sufficiently large, the number of primes up to $(1-\eps) n \log n$ is less than $n$, and the number of primes up to $(1+\eps) n \log n$ is greater than $n$.
\end{proof}
%%-/

/-%%
\begin{corollary}[pn_pn_plus_one] \label{pn_pn_plus_one}\lean{pn_pn_plus_one}\leanok
We have $p_{n+1} - p_n = o(p_n)$
  as $n \to \infty$.
\end{corollary}
%%-/

theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = (c n) * Nat.nth Nat.Prime n := by
  use (fun n => (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n) / Nat.nth Nat.Prime n)
  refine ⟨?_, ?_⟩
  · obtain ⟨k, k_o1, p_n_eq⟩ := pn_asymptotic
    simp only [isLittleO_one_iff]
    rw [Filter.tendsto_congr' (f₂ := fun n ↦ ((1 + k (n+1))*(n+1)*log (n+1) - (1 + k n)*n*log n) / ((1 + k n)*n*log n))]
    swap
    · simp only [EventuallyEq, eventually_atTop, ge_iff_le]
      use 2; intro n hn
      rw [p_n_eq n (by linarith), p_n_eq (n+1) (by linarith)]
      grind
    simp_rw [sub_div]
    have zero_eq_minus: (0 : ℝ) = 1 - 1 := by
      simp
    rw [zero_eq_minus]
    apply Filter.Tendsto.sub
    · conv =>
        arg 1
        intro n
        equals ((1 + k (n + 1)) / (1 + k n) ) * ((↑n + 1) * log (↑n + 1) / (↑n * log ↑n)) =>
          field_simp
      nth_rw 6 [← (one_mul 1)]
      apply Filter.Tendsto.mul
      · have one_div: nhds 1 = nhds ((1: ℝ) / 1) := by simp
        rw [one_div]
        apply Filter.Tendsto.div
        · nth_rw 3 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · simp
          · rw [Filter.tendsto_add_atTop_iff_nat]
            rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
            · simp only [div_one] at k_o1
              exact k_o1
            · simp
        · nth_rw 2 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · simp
          · rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
            · simp only [div_one] at k_o1
              exact k_o1
            · simp

        simp
      · conv =>
          arg 1
          intro x
          equals ((↑x + 1) / x) * (log (↑x + 1) / (log ↑x)) =>
            field_simp
        nth_rw 3 [← (one_mul 1)]
        apply Filter.Tendsto.mul
        · simp_rw [add_div]
          nth_rw 2 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · rw [← Filter.tendsto_add_atTop_iff_nat 1]
            field_simp
            simp
          · simp only [one_div]
            exact tendsto_inv_atTop_nhds_zero_nat
        · have log_eq: ∀ (n: ℕ), log (↑n + 1) = log ↑n + log (1 + 1/n) := by
            intro n
            by_cases n_eq_zero: n = 0
            · simp [n_eq_zero]
            · calc
                _ = log (n * (1 + 1 / n)) := by field_simp
                _ = log n + log (1 + 1/n) := by
                  rw [Real.log_mul]
                  · simpa
                  · simp only [one_div, ne_eq]
                    positivity

          simp_rw [log_eq]
          simp_rw [add_div]
          nth_rw 3 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · rw [← Filter.tendsto_add_atTop_iff_nat 2]
            have log_not_zero: ∀ n: ℕ, log (n + 2) ≠ 0 := by
              intro n
              simp only [ne_eq, log_eq_zero, not_or]
              refine ⟨?_, ?_, ?_⟩
              · norm_cast
              · norm_cast
                simp
              · norm_cast
            simp [log_not_zero]
          · rw [← Filter.tendsto_add_atTop_iff_nat 2]
            apply squeeze_zero (g := fun (n: ℕ) => (log 2 / log (n + 2)))
            · intro n
              have log_plus_nonzero: 0 ≤ log (1 + 1 / ↑(n + 2)) := by
                apply log_nonneg
                simp only [cast_add, cast_ofNat, one_div, le_add_iff_nonneg_right, inv_nonneg]
                norm_cast
                simp only [le_add_iff_nonneg_left, _root_.zero_le]
              exact div_nonneg log_plus_nonzero (log_natCast_nonneg (n + 2))
            · intro n
              norm_cast
              have log_le_2: log (1 + 1 / ↑(n + 2)) ≤ log 2 := by
                apply Real.log_le_log
                · positivity
                · have two_eq_one_plus_one: (2 : ℝ) = 1 + 1 := by
                    norm_num
                  rw [two_eq_one_plus_one]
                  simp only [cast_add, cast_ofNat, one_div, add_le_add_iff_left, ge_iff_le]
                  apply inv_le_one_of_one_le₀
                  linarith

              rw [div_le_div_iff_of_pos_right]
              · exact log_le_2
              · apply Real.log_pos
                norm_cast
                simp
            · apply Filter.Tendsto.div_atTop (l := atTop) (a := log 2)
              · simp
              · norm_cast
                have shift_fn := Filter.tendsto_add_atTop_iff_nat (f := fun n => log (n)) (l := atTop) 2
                rw [shift_fn]
                apply Filter.Tendsto.comp Real.tendsto_log_atTop
                exact tendsto_natCast_atTop_atTop

    · have eventually_nonzero: ∃ t, t > 2 ∧ ∀ n, 1 + k (n + t) ≠ 0 := by
        rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
        · rw [NormedAddCommGroup.tendsto_nhds_zero] at k_o1
          specialize k_o1 ((1 : ℝ) / 2)
          simp only [one_div, gt_iff_lt, inv_pos, ofNat_pos, div_one, norm_eq_abs, eventually_atTop,
            ge_iff_le, forall_const] at k_o1
          obtain ⟨a, ha⟩ := k_o1
          use (a + 3)
          refine ⟨by simp, ?_⟩
          intro n
          specialize ha (n + (a + 3))
          have a_le_plus: a ≤ n + (a + 3) := by omega
          simp only [a_le_plus, forall_const] at ha

          by_contra!
          rw [add_eq_zero_iff_eq_neg] at this
          rw [← abs_neg] at ha
          rw [← this] at ha
          simp only [abs_one] at ha
          have two_inv_lt := inv_lt_one_of_one_lt₀ (a := (2 : ℝ)) (by simp)
          linarith
        · simp

      obtain ⟨t, t_gt_2, ht⟩ := eventually_nonzero
      rw [← Filter.tendsto_add_atTop_iff_nat t]
      have denom_nonzero: ∀ n, ((1 + k (n + t)) * ↑(n + t) * log ↑(n + t)) ≠ 0 := by
        intro n
        simp only [cast_add, ne_eq, _root_.mul_eq_zero, log_eq_zero, not_or]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · exact ht n
        · norm_cast
          omega
        · norm_cast
          omega
        · refine ⟨?_, by norm_cast⟩
          norm_cast
          omega
      conv =>
        arg 1
        intro n
        rw [div_self (denom_nonzero n)]
      simp
  · intro n
    have nth_nonzero: Nat.nth Nat.Prime n ≠ 0 := by
      exact Nat.Prime.ne_zero (prime_nth_prime n)
    simp [nth_nonzero]

/-%%
\begin{proof}
\uses{pn_asymptotic}\leanok
  Easy consequence of preceding proposition.
\end{proof}
%%-/

/-%%
\begin{corollary}[prime_between]  \label{prime_between}\lean{prime_between}\leanok
For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for all sufficiently large $x$.
\end{corollary}
%%-/

lemma prime_in_gap' (a b : ℕ) (h : a.primeCounting < b.primeCounting)
    : ∃ (p : ℕ), p.Prime ∧ (a + 1) ≤ p ∧ p < (b + 1) := by
  obtain ⟨p, hp, pp⟩ := exists_of_count_lt_count h
  exact ⟨p, pp, hp.left, hp.right⟩

lemma prime_in_gap (a b : ℝ) (ha : 0 < a)
    (h : ⌊a⌋₊.primeCounting < ⌊b⌋₊.primeCounting)
    : ∃(p : ℕ), p.Prime ∧ a < p ∧ p ≤ b := by

  have hab : ⌊a⌋₊ < ⌊b⌋₊ := Monotone.reflect_lt Nat.monotone_primeCounting h
  obtain ⟨w, h, ha, hb⟩ := prime_in_gap' ⌊a⌋₊ ⌊b⌋₊ h
  refine ⟨w, h, lt_of_floor_lt ha, ?_⟩
  have : a < b := by
    by_contra h
    cases lt_or_eq_of_le <| le_of_not_gt h with
    | inl hh => linarith [floor_le_floor <| le_of_lt hh]
    | inr hh =>
      rw [hh] at hab
      rwa [←lt_self_iff_false ⌊a⌋₊]
  by_contra h
  have : ⌊b⌋₊ < w := floor_lt (by linarith) |>.mpr (lt_of_not_ge h)
  have : ⌊b⌋₊ + 1 ≤ w := by linarith
  linarith

lemma bound_f_second_term (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 + f x) < (1 + δ)  := by
  have bound_one_plus_f: ∀ y: ℝ, ∀ z: ℝ, |f y| < z → 1 + (f y) < 1 + z := by
    intro y z hf
    by_cases f_pos: 0 < f y
    · rw [abs_of_pos f_pos] at hf
      linarith
    · rw [not_lt] at f_pos
      rw [abs_of_nonpos f_pos] at hf
      linarith

  have f_small := NormedAddCommGroup.tendsto_nhds_zero.mp hf δ hδ
  simp only [norm_eq_abs, eventually_atTop, ge_iff_le] at f_small
  obtain ⟨p, hp⟩ := f_small

  let a := ((max 1 p) : ℝ)
  have ha: ∀ b: ℝ, a ≤ b → |f b| < δ := by
    intro b hb
    have b_ge_p: p ≤ b := by
      have a_ge_p: p ≤ a := by simp [a]
      linarith
    exact hp b b_ge_p

  rw [Filter.eventually_atTop]

  use a
  intro b hb
  exact bound_one_plus_f b δ (ha b (by linarith))


lemma bound_f_first_term {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 + f ((1 + ε) * x)) > (1 - δ)  := by
  have bound_one_plus_f: ∀ y: ℝ, ∀ z: ℝ, |f y| < z → 1 + (f y) > 1 - z := by
    intro y z hf
    by_cases f_pos: 0 < f y
    · rw [abs_of_pos f_pos] at hf
      linarith
    · rw [not_lt] at f_pos
      rw [abs_of_nonpos f_pos] at hf
      linarith

  have f_small := NormedAddCommGroup.tendsto_nhds_zero.mp hf δ hδ
  simp only [norm_eq_abs, eventually_atTop, ge_iff_le] at f_small
  obtain ⟨p, hp⟩ := f_small

  let a := ((max 1 p) : ℝ)
  have ha: ∀ b: ℝ, a ≤ b → |f b| < δ := by
    intro b hb
    have b_ge_p: p ≤ b := by
      have a_ge_p: p ≤ a := by simp [a]
      linarith
    exact hp b b_ge_p


  rw [Filter.eventually_atTop]

  use a
  intro b hb

  have a_pos: 0 < a := by
    simp [a]

  have pos_mul: ∀ x y z : ℝ, 0 < x → 0 < y → 1 < z → x ≤ y → x < y * z := by
    intro x y z _ hy hz hlt
    have y_lt: y < y * z := by
      exact (lt_mul_iff_one_lt_right hy).mpr hz
    linarith

  have mul_increase: a ≤ (1 + ε) * b := by
    simp only [ge_iff_le, a] at hb
    have a_le := pos_mul a b (1 + ε) a_pos (by linarith) (by linarith) (by linarith)
    linarith

  exact bound_one_plus_f ((1 + ε) * b) δ (ha ((1 + ε) * b) mul_increase)

lemma smaller_terms {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ)
    (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 - δ) * (((1 + ε) * x / (Real.log ((1 + ε) * x)))) < (1 + f ((1 + ε) * x)) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) := by
  have first_term := bound_f_first_term hε f hf δ hδ
  simp only [gt_iff_lt, eventually_atTop, ge_iff_le] at first_term
  obtain ⟨p, hp⟩ := first_term
  simp only [eventually_atTop, ge_iff_le]
  let a := max p 1
  have ha: ∀ (b : ℝ), a ≤ b → 1 - δ < 1 + f ((1 + ε) * b) := by
    intro b hb
    have a_ge_p: p ≤ a := by
      simp [a]
    specialize hp b (by linarith)
    exact hp
  use a
  intro b hb
  rw [mul_lt_mul_iff_left₀]
  · exact ha b hb
  · simp only [sup_le_iff, a] at hb
    have b_ge_one: 1 ≤ b := hb.2
    have log_pos: Real.log ((1 + ε) *b) > 0 := by
      have one_pplus_pos: 1 < (1 + ε) := by linarith
      refine (Real.log_pos_iff ?_).mpr ?_
      · positivity
      · exact one_lt_mul_of_lt_of_le one_pplus_pos b_ge_one

    positivity

lemma second_smaller_terms (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 + δ) * (( x / (Real.log (x)))) > (1 + f ( x)) * ( x / (Real.log (x))) := by
  have first_term := bound_f_second_term f hf δ hδ

  simp only [_root_.add_lt_add_iff_left, eventually_atTop, ge_iff_le] at first_term
  obtain ⟨p, hp⟩ := first_term
  simp only [gt_iff_lt, eventually_atTop, ge_iff_le]
  let a := max p 2
  have ha: ∀ (b : ℝ), a ≤ b → 1 + δ > 1 + f ( b) := by
    intro b hb
    have a_ge_p: p <= a := by simp [a]
    specialize hp b (by linarith)
    linarith
  use a
  intro b hb
  specialize ha b hb
  have rhs_nonzero:  b / log ( b) > 0 := by
    simp only [sup_le_iff, a] at hb
    obtain ⟨_, hb2⟩ := hb
    have log_pos: Real.log (b) > 0 := by
      refine (Real.log_pos_iff ?_).mpr ?_
      · positivity
      · linarith
    positivity
  rw [mul_lt_mul_iff_left₀]
  · exact ha
  · linarith

lemma x_log_x_atTop : Filter.Tendsto (fun x => x / Real.log x) Filter.atTop Filter.atTop := by
  have inv_log_x_div := Filter.Tendsto.comp (f := fun x => Real.log x / x) (g := fun x => x⁻¹) (x := Filter.atTop) (y := (nhdsWithin 0 (Set.Ioi 0))) (z := Filter.atTop) ?_ ?_
  · simp_rw [Function.comp_def, inv_div] at inv_log_x_div
    exact inv_log_x_div
  · exact tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have log_div_x := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by simp)
      simp only [pow_one, one_mul, add_zero] at log_div_x
      exact log_div_x
    · simp only [Set.mem_Ioi, eventually_atTop, ge_iff_le]
      use 2
      intro x hx
      have log_pos: 0 < Real.log x := by
        refine (Real.log_pos_iff ?_).mpr ?_ <;> linarith
      positivity


lemma tendsto_by_squeeze (ε : ℝ) (hε : ε > 0) :
    Tendsto (fun (x : ℝ) => (Nat.primeCounting ⌊(1 + ε) * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop := by
  obtain ⟨c, hc, pi_x_eq⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  conv =>
    arg 1
    intro x
    rw [pi_x_eq]
    rw [pi_x_eq]
  simp only [div_one] at hc

  -- (1 + δ) * (( x / (Real.log (x)))) > (1 + f ( x)) * ( x / (Real.log (x)))

  let d: ℝ := ε/(2*(2 + ε))
  have hd: 0 < d := by positivity
  have first_helper := smaller_terms hε c hc (d) hd
  have second_helper := second_smaller_terms c hc d hd

  apply Filter.tendsto_atTop_mono' (f₁ := fun x => (
      ((1 - d) * ((1 + ε) * x / log ((1 + ε) * x)))
      -
      ((1 + d) * (x / log x)))
    )
  · rw [Filter.EventuallyLE]

    simp only [eventually_atTop, ge_iff_le] at first_helper
    simp only [gt_iff_lt, eventually_atTop, ge_iff_le] at second_helper

    obtain ⟨a1, ha1⟩ := first_helper
    obtain ⟨a2, ha2⟩ := second_helper

    simp only [eventually_atTop]

    use (max a1 a2)
    intro b hb

    have lt_compare: ∀ a b c d : ℝ, a < c ∧ b > d → a - b ≤ c - d := by
      intro a b c d h_lt
      obtain ⟨a_lt, b_gt⟩ := h_lt
      linarith

    apply lt_compare
    simp only [ge_iff_le, sup_le_iff] at hb
    specialize ha1 b hb.1
    specialize ha2 b hb.2
    field_simp
    field_simp at ha1 ha2
    exact ⟨ha1, ha2⟩
  · rw [← Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
    have log_split: ∀ x: Set.Ioi 1, x.val / log ((1 + ε) * x.val) = x.val / (log (1 + ε) + log (x.val)) := by
      intro x
      have x_ge_one: 1 < x.val := Set.mem_Ioi.mp x.property
      rw [Real.log_mul (by linarith) (by linarith)]

    have log_factor: ∀ x: Set.Ioi 1, x.val / (log (1 + ε) + log (x.val)) = x.val / ((1 + (log (1 + ε)/(log x.val))) * (log x.val)) := by
      intro x
      have : log (x.val) ≠ 0 := by
        have pos := Real.log_pos x.property
        linarith
      field_simp
      rw [add_comm]

    conv at log_factor =>
      intro x
      rhs
      rw [div_mul_eq_div_mul_one_div]

    conv =>
      arg 1
      intro x
      lhs
      rw [mul_div_assoc]
      rw [log_split x]

    conv =>
      arg 1
      intro x
      lhs
      rw [log_factor]

    suffices Tendsto (fun x : Set.Ioi (1 : ℝ) ↦ (1 - d) * ((1 + ε) * x) / ((1 + log (1 + ε) / log x) * log x) - (1 + d) * x / log x) atTop atTop by
      field_simp at this ⊢
      exact this
    conv =>
      arg 1
      intro x
      rw [sub_eq_add_neg]
      rw [← neg_div]
      rw [div_add_div]
      · skip
      tactic =>
        simp only [ne_eq, _root_.mul_eq_zero, log_eq_zero, not_or]
        have x_pos := x.property
        simp_rw [Set.Ioi, Set.mem_setOf_eq] at x_pos
        refine ⟨?_, by linarith, by linarith, by linarith⟩
        have log_num_pos: 0 < log (1 + ε) := by
          exact Real.log_pos (by linarith)
        have log_denom_pos: 0 < log x := by
          exact Real.log_pos x.property
        positivity
      tactic =>
        have pos := Real.log_pos (x.property)
        linarith

    conv =>
      arg 1
      intro x
      equals ↑x * (log ↑x * ((1 + ε) * (1 - d)) - (1 + log (1 + ε) / log ↑x) * ((1 + d) * log ↑x)) /
      (log ↑x * ((1 + log (1 + ε) / log ↑x) * log ↑x)) =>
        ring

    simp only [mul_div_mul_comm]
    conv =>
      arg 1
      intro x
      rw [mul_comm]

    apply Filter.Tendsto.pos_mul_atTop (C := (1 + ε) * (1 - d) - (1 + d))
    · simp only [d, sub_pos]
      field_simp
      ring_nf
      rw [add_assoc]
      rw [add_lt_add_iff_left]
      apply lt_of_sub_pos
      ring_nf
      positivity
    · conv =>
        arg 1
        intro x
        lhs
        rhs
        equals (log x.val) * ((1 + log (1 + ε) / log ↑x) * ((1 + d))) =>
          ring

      simp_rw [← mul_sub]
      conv =>
        arg 1
        intro x
        rhs
        rw [mul_comm]

      simp only [mul_div_mul_comm]
      conv =>
        arg 1
        intro x
        lhs
        equals 1 =>
          have log_pos := Real.log_pos x.property
          field_simp

      simp only [one_mul]
      conv =>
        arg 3
        equals nhds (((1 + ε) * (1 - d) - (1 + d)) / 1) => simp

      apply Filter.Tendsto.div
      · apply Filter.Tendsto.sub
        · simp
        · conv =>
            arg 3
            equals nhds (1 * (1 + d)) => simp
          apply Filter.Tendsto.mul
          · conv =>
              arg 3
              equals nhds (1 + 0) => simp
            apply Filter.Tendsto.add
            · simp
            · apply Filter.Tendsto.div_atTop (a := log (1 + ε))
              · simp
              · simp only [tendsto_comp_val_Ioi_atTop]
                exact tendsto_log_atTop
          · simp
      · conv =>
          arg 3
          equals nhds (1 + 0) => simp
        apply Filter.Tendsto.add
        · simp
        · apply Filter.Tendsto.div_atTop (a := log (1 + ε))
          · simp
          · simp only [tendsto_comp_val_Ioi_atTop]
            exact tendsto_log_atTop
      · simp
    · let x_div_log (x: ℝ) := x / Real.log x
      conv =>
        arg 1
        equals (fun (x : Set.Ioi 1) => x_div_log x.val) => rfl

      rw [Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
      exact x_log_x_atTop

theorem prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
  have squeeze := tendsto_by_squeeze (ε/2) (by linarith)
  rw [Filter.tendsto_iff_forall_eventually_mem] at squeeze
  specialize squeeze (Set.Ici 1) (by exact Ici_mem_atTop 1)
  simp only [Set.mem_Ici, eventually_atTop, ge_iff_le] at squeeze
  obtain ⟨a, ha⟩ := squeeze
  rw [eventually_atTop]
  use (max a 1)
  intro b hb
  rw [ge_iff_le, sup_le_iff] at hb
  specialize ha b hb.1

  have val_lt: (⌊b⌋₊.primeCounting : ℝ) < ⌊(1 + ε/2) * b⌋₊.primeCounting := by linarith
  norm_cast at val_lt

  have jump := prime_in_gap b ((1 + ε/2) * b) (by linarith) val_lt
  obtain ⟨p, hp, b_lt_p, p_le⟩ := jump
  have p_lt: p < (1 + ε) * b := by
    linarith
  use p

/-%%
\begin{proof}
\uses{pi_alt}\leanok
Use Corollary \ref{pi_alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity as $x \to \infty$.
\end{proof}
%%-/

/-%%
\begin{proposition}\label{mun}\lean{sum_mobius_div_self_le}\leanok
We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \leq 1$.
\end{proposition}
%%-/
theorem sum_mobius_div_self_le (N : ℕ) : |∑ n ∈ range N, μ n / (n : ℚ)| ≤ 1 := by
  cases N with
  | zero => simp only [range_zero, sum_empty, abs_zero, zero_le_one]
  | succ N =>
  /- simple cases -/
  obtain rfl | hN := N.eq_zero_or_pos
  · simp
  /- annoying case -/
  have h_sum : 1 = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1), μ d * Int.fract (N / d : ℚ) := calc
    (1 : ℚ) = ∑ m ∈ Ioc 0 N, ∑ d ∈ m.divisors, μ d := by
      have (x : ℕ) (hx : x ∈ Ioc 0 N) : ∑ d ∈ divisors x, μ d = if x = 1 then 1 else 0 := by
        rw [mem_Ioc] at hx
        rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
      rw [sum_congr rfl this]
      simp [hN.ne']
    _ = ∑ d ∈ range (N + 1), μ d * (N / d : ℕ) := by
      simp_rw [← coe_mul_zeta_apply, ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
      rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (add_one_pos _),
        sum_insert (by simp), Ico_add_one_add_one_eq_Ioc]
      simp
    _ = ∑ d ∈ range (N + 1), (μ d : ℚ) * ⌊(N / d : ℚ)⌋ := by
      simp_rw [Rat.floor_natCast_div_natCast]
      simp [← Int.natCast_ediv]
    _ = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1), μ d * Int.fract (N / d : ℚ) := by
      simp_rw [sum_mul, ← sum_sub_distrib, mul_comm_div, ← mul_sub, Int.self_sub_fract]
  rw [eq_sub_iff_add_eq, eq_comm, ← eq_div_iff (by norm_num [Nat.pos_iff_ne_zero.mp hN])] at h_sum

  /- Next, we establish bounds for the error term -/
  have hf' (d : ℕ) : |Int.fract ((N : ℚ) / d)| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact Int.fract_lt_one _
  have h_bound : |∑ d ∈ range (N + 1), μ d * Int.fract ((N : ℚ) / d)| ≤ N - 1 := by
    /- range (N + 1) → Icc 1 N + part that evals to 0 -/
    rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (by simp), sum_insert (by simp),
      ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, zero_add,
      Finset.Ico_add_one_right_eq_Icc, zero_add]
    /- Ico 1 (N + 1) → Ico 1 N ∪ {N + 1} that evals to 0 -/
    rw [← Ico_insert_right hN, sum_insert (by simp), div_self (by simp; grind), Int.fract_one,
      mul_zero, zero_add]
    /- bound sum -/
    have (d : ℕ) : |μ d * Int.fract ((N : ℚ) / d)| ≤ 1 := by
      rw [abs_mul, ← one_mul 1]
      refine mul_le_mul ?_ (hf' _).le (abs_nonneg _) zero_le_one
      norm_cast
      exact abs_moebius_le_one
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum fun d _ ↦ this d).trans
    simp [cast_sub (one_le_iff_ne_zero.mpr hN.ne')]

  rw [h_sum, abs_le]
  rw [abs_le, neg_sub] at h_bound
  constructor
  <;> simp only [le_div_iff₀, div_le_iff₀, cast_pos.mpr hN]
  <;> linarith [h_bound.left]

/-%%
\begin{proof}\leanok
From M\"obius inversion $1_{n=1} = \sum_{d|n} \mu(d)$ and summing we have
  $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
  for any $x \geq 1$. Since $\lfloor \frac{x}{d} \rfloor = \frac{x}{d} - \epsilon_d$ with
  $0 \leq \epsilon_d < 1$ and $\epsilon_x = 0$, we conclude that
  $$ 1 ≥ x \sum_{d \leq x} \frac{\mu(d)}{d} - (x - 1)$$
  and the claim follows.
\end{proof}
%%-/

/-%%
\begin{proposition}[M\"obius form of prime number theorem]\label{mu-pnt}\lean{mu_pnt}\leanok  We have $\sum_{n \leq x} \mu(n) = o(x)$.
\end{proposition}
%%-/

theorem mu_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, μ n) =o[atTop] fun x ↦ x := by sorry

/-%%
\begin{proof}
\uses{mun, WeakPNT}
From the Dirichlet convolution identity
  $$ \mu(n) \log n = - \sum_{d|n} \mu(d) \Lambda(n/d)$$
and summing we obtain
$$ \sum_{n \leq x} \mu(n) \log n = - \sum_{d \leq x} \mu(d) \sum_{m \leq x/d} \Lambda(m).$$
For any $\eps>0$, we have from the prime number theorem that
$$ \sum_{m \leq x/d} \Lambda(m) = x/d + O(\eps x/d) + O_\eps(1)$$
(divide into cases depending on whether $x/d$ is large or small compared to $\eps$).
We conclude that
$$ \sum_{n \leq x} \mu(n) \log n = - x \sum_{d \leq x} \frac{\mu(d)}{d} + O(\eps x \log x) + O_\eps(x).$$
Applying \eqref{mun} we conclude that
$$ \sum_{n \leq x} \mu(n) \log n = O(\eps x \log x) + O_\eps(x).$$
and hence
$$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x) + O( \sum_{n \leq x} (\log x - \log n) ).$$
From Stirling's formula one has
$$  \sum_{n \leq x} (\log x - \log n) = O(x)$$
thus
$$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x)$$
and thus
$$ \sum_{n \leq x} \mu(n) = O(\eps x) + O_\eps(\frac{x}{\log x}).$$
Sending $\eps \to 0$ we obtain the claim.
\end{proof}
%%-/


/-%%
\begin{proposition}\label{lambda-pnt}\lean{lambda_pnt}\leanok
We have $\sum_{n \leq x} \lambda(n) = o(x)$.
\end{proposition}
%%-/

theorem lambda_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (-1)^(Ω n)) =o[atTop] fun x ↦ x := by
  sorry

/-%%
\begin{proof}
\uses{mu-pnt}
From the identity
  $$ \lambda(n) = \sum_{d^2|n} \mu(n/d^2)$$
and summing, we have
$$ \sum_{n \leq x} \lambda(n) = \sum_{d \leq \sqrt{x}} \sum_{n \leq x/d^2} \mu(n).$$
For any $\eps>0$, we have from Proposition \ref{mu-pnt} that
$$ \sum_{n \leq x/d^2} \mu(n) = O(\eps x/d^2) + O_\eps(1)$$
and hence on summing in $d$
$$ \sum_{n \leq x} \lambda(n) = O(\eps x) + O_\eps(x^{1/2}).$$
Sending $\eps \to 0$ we obtain the claim.
\end{proof}

%%-/

/-%%
\begin{proposition}[Alternate M\"obius form of prime number theorem]\label{mu-pnt-alt}\lean{mu_pnt_alt}\leanok  We have $\sum_{n \leq x} \mu(n)/n = o(1)$.
\end{proposition}
%%-/

theorem mu_pnt_alt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ) / n) =o[atTop] fun x ↦ (1 : ℝ) := by
  sorry

/-%%
\begin{proof}
\uses{mu-pnt}
As in the proof of Theorem \ref{mun}, we have
  $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
  $$ = x \sum_{d \leq x} \frac{\mu(d)}{d} - \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \}$$
so it will suffice to show that
$$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = o(x).$$
Let $N$  be a natural number.  It suffices to show that
$$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = O(x/N).$$
if $x$ is large enough depending on $N$.
We can split the left-hand side as the sum of
$$ \sum_{d \leq x/N} \mu(d) \{ \frac{x}{d} \} $$
and
$$ \sum_{j=1}^{N-1} \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j).$$
The first term is clearly $O(x/N)$.  For the second term, we can use Theorem \ref{mu-pnt} and summation by parts (using the fact that $x/d-j$ is monotone and bounded) to find that
$$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = o(x)$$
for any given $j$, so in particular
$$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = O(x/N^2)$$
for all $j=1,\dots,N-1$ if $x$ is large enough depending on $N$.  Summing all the bounds, we obtain the claim.
\end{proof}
%%-/

/-%%
\section{Consequences of the PNT in arithmetic progressions}

\begin{theorem}[Prime number theorem in AP]\label{chebyshev_asymptotic_pnt}\lean{chebyshev_asymptotic_pnt}\leanok  If $a\ (q)$ is a primitive residue class, then one has
  $$ \sum_{p \leq x: p = a\ (q)} \log p = \frac{x}{\phi(q)} + o(x).$$
\end{theorem}
%%-/

proof_wanted chebyshev_asymptotic_pnt {q:ℕ} {a:ℕ} (hq: q ≥ 1) (ha: Nat.Coprime a q) (ha': a < q) :
    (fun x ↦ ∑ p ∈ (filter Nat.Prime (Iic ⌊x⌋₊)), if (p % q = a) then log p else 0) ~[atTop] (fun x ↦ x / (Nat.totient q))

/-%%
\begin{proof}
\uses{chebyshev_asymptotic}
This is a routine modification of the proof of Theorem \ref{chebyshev_asymptotic}.
\end{proof}
%%-/

/-%%
\begin{corollary}[Dirichlet's theorem]\label{dirichlet_thm}\lean{dirichlet_thm}\leanok  Any primitive residue class contains an infinite number of primes.
\end{corollary}
%%-/

proof_wanted dirichlet_thm {q:ℕ} {a:ℕ} (hq: q ≥ 1) (ha: Nat.Coprime a q) (ha': a < q) : Infinite { p // p.Prime ∧ p % q = a }

/-%%
\begin{proof}
\uses{chebyshev_asymptotic_pnt}
If this were not the case, then the sum $\sum_{p \leq x: p = a\ (q)} \log p$ would be bounded in $x$, contradicting Theorem \ref{chebyshev_asymptotic_pnt}.
\end{proof}
-/

/-%%
\section{Consequences of the Chebotarev density theorem}

%%-/

/-%%
\begin{lemma}[Cyclotomic Chebotarev]\label{Chebotarev-cyclic}  For any $a$ coprime to $m$,
$$ \sum_{N \mathfrak{p} \leq x; N \mathfrak{p} = a\ (m)} \log N \mathfrak{p}  =
\frac{1}{|G|} \sum_{N \mathfrak{p} \leq x} \log N \mathfrak{p}.$$
\end{lemma}
%%-/

/-%%
\begin{proof}\uses{Dedekind-PNT, WeakPNT_AP} This should follow from Lemma \ref{Dedekind-PNT} by a Fourier expansion.
\end{proof}
%%-/
