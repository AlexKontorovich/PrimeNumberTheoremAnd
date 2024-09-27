import PrimeNumberTheoremAnd.Wiener
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory

lemma abel_summation {a : ArithmeticFunction ℝ} (x y : ℝ) (hx : 0 < x) (hxy : x < y)
    (ϕ : ℝ → ℝ) (hϕ : ContDiff ℝ 1 ϕ) :
    ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (a n : ℝ) * ϕ n =
      (∑ n ∈ Iic ⌊y⌋₊, a n) * ϕ y - (∑ n ∈ Iic ⌊x⌋₊, a n) * ϕ x -
        ∫ u in Set.Icc x y, (∑ n ∈ Iic ⌊u⌋₊, a n) * (deriv ϕ) u := by
  let m := ⌊x⌋₊
  let k := ⌊y⌋₊
  have hky : k ≤ y := by simp [k, Nat.floor_le, (hx.trans hxy).le]
  have : m ≤ k := by simp [m, k, Nat.floor_le_floor hxy.le]
  cases this.eq_or_lt with
  | inl hmk =>
    simp only [m, k] at hmk
    rw [hmk,Ioc_self, sum_empty, ← mul_sub, eq_comm, sub_eq_zero,
      ← intervalIntegral.integral_deriv_eq_sub, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le hxy.le, integral_Ioc_eq_integral_Ioo,
      integral_Icc_eq_integral_Ioo]
    apply setIntegral_congr
    · exact measurableSet_Ioo
    · intro z hz
      have : ⌊z⌋₊ = ⌊y⌋₊ := by
        simp only [Set.mem_Ioo] at hz
        apply le_antisymm
        · exact Nat.floor_le_floor hz.2.le
        · rw [← hmk]
          exact Nat.floor_le_floor hz.1.le
      simp only [this]
    · intros
      exact hϕ.differentiable le_rfl |>.differentiableAt
    · exact hϕ.continuous_deriv le_rfl |>.continuousOn |>.intervalIntegrable
  | inr hmk =>
  let A (z : ℝ) := ∑ j ∈ Iic ⌊z⌋₊, a j
  have hA (z : ℝ) : A z = A ⌊z⌋₊ := by simp only [floor_natCast, A]
  have hint' (a b : ℝ) (h : Set.uIoc a b ⊆ Set.Icc ⌊a⌋₊ (⌊a⌋₊ + 1)) :
      ∫ t in a..b, A t * deriv ϕ t = A a * (ϕ b - ϕ a) := by
    rw [← intervalIntegral.integral_deriv_eq_sub]
    · rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae ?_
      apply eventually_iff.mpr
      simp only [le_add_iff_nonneg_right, zero_le_one, Set.uIoc_of_le, Set.mem_Ioc,
        mul_eq_mul_right_iff, and_imp]
      rw [mem_ae_iff, ← nonpos_iff_eq_zero, ← volume_singleton (a := ⌊a⌋₊ + 1)]
      apply measure_mono
      intro z hz
      simp only [mem_Ioo, Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_imp, not_or,
        Set.mem_singleton_iff] at hz ⊢
      have hz0 := h hz.1
      simp only [Set.mem_Icc] at hz0
      apply hz0.2.eq_or_lt.resolve_right
      intro hz'
      have : ⌊z⌋₊ = ⌊a⌋₊ := by
        rw [Nat.floor_eq_iff ((Nat.cast_nonneg _).trans hz0.1)]
        exact ⟨hz0.1, hz'⟩
      apply hz.2.1
      simp only [← this, A, floor_natCast]
    · intros
      exact hϕ.differentiable le_rfl |>.differentiableAt
    · exact hϕ.continuous_deriv le_rfl |>.continuousOn |>.intervalIntegrable
  have hIntegrableOn (n : ℕ) (b c : ℝ) (hbc : b ≤ c) (h : Set.uIoc b c ⊆ Set.Icc n (n + 1)) :
      IntegrableOn (fun t ↦ A t * deriv ϕ t) (Set.Ico b c) volume := by
    obtain rfl | hbc := hbc.eq_or_lt
    · simp
    have h' : Set.Icc b c ⊆ Set.Icc n (n + 1) := by
      rwa [← closure_Ioc hbc.ne, ← Set.uIoc_of_le hbc.le, isClosed_Icc.closure_subset_iff]
    apply IntegrableOn.mul_continuousOn_of_subset ?_ ?_
      measurableSet_Ico CompactIccSpace.isCompact_Icc Set.Ico_subset_Icc_self
    · simp only [cast_add, cast_one, A]
      rw [IntegrableOn]
      apply MeasureTheory.Integrable.congr (MeasureTheory.integrable_const (∑ j ∈ Iic n, a j))
      · simp only [measurableSet_Ico, ae_restrict_eq]
        rw [eventuallyEq_inf_principal_iff]
        apply Eventually.of_forall
        intro z hz
        replace hz : ⌊z⌋₊ = n := by
          have := Set.Ico_subset_Icc_self.trans h' hz
          simp only [Set.mem_Icc] at this
          rw [Nat.floor_eq_iff (n.cast_nonneg.trans this.1)]
          refine ⟨this.1, ?_⟩
          apply lt_of_le_of_ne this.2
          rintro rfl
          have : n + 1 < c := by simp only [Set.mem_Ico] at hz; exact hz.2
          apply this.not_le
          have := h' <| Set.right_mem_Icc.mpr hbc.le
          simp only [Set.mem_Icc] at this
          exact this.2
        simp [hz]
    · exact hϕ.continuous_deriv le_rfl |>.continuousOn
  have hIntervalIntegrable (n : ℕ) (b c : ℝ) (hbc : b ≤ c) (h : Set.uIoc b c ⊆ Set.Icc n (n + 1)) :
      IntervalIntegrable (fun t ↦ A t * deriv ϕ t) volume b c := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le hbc]
    apply hIntegrableOn n b c hbc h

  calc
    _ = ∑ n ∈ Ioc m k, (A n - A (n - 1)) * ϕ n := ?_
    _ = ∑ n ∈ Ioc m k, A n * ϕ n - ∑ n ∈ Ico m k, A n * ϕ (n + 1) := ?_
    _ = ∑ n ∈ Ioo m k, A n * (ϕ n - ϕ (n + 1)) + A k * ϕ k - A m * ϕ (m + 1) := ?_
    _ = - ∑ n ∈ Ioo m k, (∫ t in (n : ℝ)..(n + 1), A t * deriv ϕ t) + A k * ϕ k - A m * ϕ (m + 1) := ?_
    _ = - (∫ t in (m + 1 : ℝ)..k, A t * deriv ϕ t) + A k * ϕ k - A m * ϕ (m + 1) := ?_
    _ = - (∫ t in (m + 1 : ℝ)..k, A t * deriv ϕ t)
          + A y * ϕ y
          - (∫ t in (k : ℝ)..y, A t * deriv ϕ t)
          - A x * ϕ x
          - (∫ t in (x : ℝ)..(m + 1), A t * deriv ϕ t) := ?_
    _ = A y * ϕ y - A x * ϕ x - (
          (∫ t in (x : ℝ)..(m + 1), A t * deriv ϕ t) +
          (∫ t in (m + 1 : ℝ)..k, A t * deriv ϕ t) +
          (∫ t in (k : ℝ)..y, A t * deriv ϕ t)) := ?_
    _ = A y * ϕ y - A x * ϕ x - (∫ t in x..y, A t * deriv ϕ t) := ?_
  · have h1 (n : ℕ) (hn : n ≠ 0) : A n - A (n - 1) = a n := by
      obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero hn
      simp only [succ_eq_add_one, cast_add, cast_one, cast_nonneg, floor_add_one, floor_natCast,
        add_sub_cancel_right, A]
      rw [Iic_eq_Icc]
      simp only [bot_eq_zero', _root_.zero_le, ← Icc_insert_succ_right, mem_Icc,
        add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true,
        sum_insert, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [mem_Ioc] at hn
    rw [h1 _ (not_eq_zero_of_lt hn.1)]
  · simp_rw [sub_mul, sum_sub_distrib]
    congr 1
    apply sum_bij (fun n hn => n - 1)
    · intro n hn
      simp only [mem_Ioc] at hn
      obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (not_eq_zero_of_lt hn.1)
      simp_all only [floor_natCast, succ_eq_add_one, Nat.lt_add_one_iff, add_one_le_iff,
        add_tsub_cancel_right, mem_Ico, and_self]
    · intro n₁ hn₁ n₂ hn₂ h
      simp_all only [floor_natCast, mem_Ioc]
      apply pred_inj (pos_of_gt hn₁.1) (pos_of_gt hn₂.1) h
    · intro n hn
      use n + 1
      simp_all only [floor_natCast, mem_Ico, add_tsub_cancel_right, mem_Ioc, Nat.lt_add_one_iff,
        add_one_le_iff, and_self, exists_const]
    · intro n hn
      simp only [mem_Ioc] at hn
      have := pos_of_gt hn.1
      rw [← cast_add_one]
      rw [Nat.sub_add_cancel this]
      rw [cast_pred this]
  · rw [← Ioo_insert_right hmk, ← Ioo_insert_left hmk]
    rw [sum_insert left_not_mem_Ioo, sum_insert right_not_mem_Ioo]
    simp_rw [mul_sub, sum_sub_distrib]
    abel
  · -- FTC-2
    rw [← sum_neg_distrib]
    congr 2
    apply sum_congr rfl fun n _ => ?_
    rw [hint' n]
    · rw [neg_mul_eq_mul_neg, neg_sub]
    · intro z hz
      simp only [le_add_iff_nonneg_right, zero_le_one, Set.uIoc_of_le, Set.mem_Ioc, floor_natCast,
        Set.mem_Icc] at hz ⊢
      exact ⟨hz.1.le, hz.2⟩
  · congr 2
    rw [← Ico_succ_left]
    have : m.succ ≤ k := by
      rwa [Nat.succ_le_iff]
    simp_rw [← Nat.cast_add_one]
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico this]
    intro n _
    have hn := Nat.cast_le (α := ℝ).mpr n.lt_add_one.le
    apply hIntervalIntegrable n _ _ hn
    rw [Set.uIoc_of_le hn, Nat.cast_add_one]
    exact Set.Ioc_subset_Icc_self
  · rw [hA x, hA y]
    have hy : ∫ t in ↑k..y, A t * deriv ϕ t = A k * (ϕ y - ϕ k) := by
      apply hint'
      intros z hz
      simp only [hky, Set.uIoc_of_le, Set.mem_Ioc, floor_natCast, Set.mem_Icc, k] at hz ⊢
      exact ⟨hz.1.le, hz.2.trans (Nat.lt_floor_add_one _).le⟩
    have hx : ∫ t in x..m + 1, A t * deriv ϕ t = A x * (ϕ (m + 1) - ϕ x) := by
      apply hint'
      intros z hz
      have : x ≤ m + 1 := by simp only [(Nat.lt_floor_add_one x).le, m]
      simp only [this, Set.uIoc_of_le, Set.mem_Ioc, Set.mem_Icc, m] at hz ⊢
      refine ⟨(floor_le hx.le).trans hz.1.le, hz.2⟩
    rw [hy, hx]
    simp only [k, m, hA x]
    ring
  · ring
  · have hab : IntervalIntegrable (fun t ↦ A t * deriv ϕ t) volume x (↑m + 1) := by
      apply hIntervalIntegrable m _ _ (lt_floor_add_one x).le
      simp only [(lt_floor_add_one x).le, Set.uIoc_of_le]
      apply Set.Ioc_subset_Icc_self.trans
      apply Set.Icc_subset_Icc_left (floor_le hx.le)
    have hbc : IntervalIntegrable (fun t ↦ A t * deriv ϕ t) volume (↑m + 1) ↑k := by
      rw [intervalIntegrable_iff_integrableOn_Ico_of_le]
      swap
      · norm_cast
      have : Set.Ico (m + 1 : ℝ) k = ⋃ i ∈ Ico (m + 1) k, Set.Ico (i : ℝ) (i + 1) := by
        ext n
        simp only [Set.mem_Ico, mem_Ico, Set.mem_iUnion, Nat.lt_add_one_iff, exists_and_left,
          exists_prop]
        constructor
        · rintro ⟨h1, h2⟩
          use ⌊n⌋₊
          have : 0 ≤ n := by
            rw [← Nat.cast_add_one] at h1
            exact (Nat.cast_nonneg _).trans h1
          simp [Nat.floor_le, Nat.floor_lt, this, lt_floor_add_one, h2, le_floor, h1]
        · rintro ⟨n', h⟩
          have : (m + 1 : ℝ) ≤ n' := by
            rw [← Nat.cast_add_one, Nat.cast_le]
            exact h.2.1.1
          refine ⟨this.trans h.1, h.2.2.trans_le ?_⟩
          rw [← Nat.cast_add_one, Nat.cast_le, Nat.add_one_le_iff]
          exact h.2.1.2
      rw [this]
      apply MeasureTheory.integrableOn_finset_iUnion.mpr
      intro n _
      have hn' : (n : ℝ) ≤ n + 1 := by
        rw [← Nat.cast_add_one, Nat.cast_le]
        exact n.lt_add_one.le
      apply hIntegrableOn n _ _ hn'
      rw [Set.uIoc_of_le hn']
      exact Set.Ioc_subset_Icc_self
    have hcd : IntervalIntegrable (fun t ↦ A t * deriv ϕ t) volume (↑k) y := by
      apply hIntervalIntegrable k _ _ hky
      simp only [hky, Set.uIoc_of_le]
      apply Set.Ioc_subset_Icc_self.trans
      refine Set.Icc_subset_Icc_right ?h.h
      simp only [k, (lt_floor_add_one y).le]
    rw [intervalIntegral.integral_add_adjacent_intervals hab hbc,
      intervalIntegral.integral_add_adjacent_intervals (hab.trans hbc) hcd]
  simp [A, intervalIntegral.integral_of_le hxy.le, MeasureTheory.integral_Icc_eq_integral_Ioc]

lemma nth_prime_one_eq_three : nth Nat.Prime 1 = 3 := nth_count prime_three

@[simp]
lemma Nat.primeCounting'_eq_zero_iff {n : ℕ} : n.primeCounting' = 0 ↔ n ≤ 2 := by
  refine ⟨?_, ?_⟩
  · contrapose!
    intro h
    replace h : 3 ≤ n := by omega
    have := monotone_primeCounting' h
    have := nth_prime_one_eq_three ▸ primeCounting'_nth_eq 1
    omega
  · intro hn
    have := zeroth_prime_eq_two ▸ primeCounting'_nth_eq 0
    have := monotone_primeCounting' hn
    omega


@[simp]
lemma Nat.primeCounting_eq_zero_iff {n : ℕ} : n.primeCounting = 0 ↔ n ≤ 1 := by
  simp [Nat.primeCounting]

@[simp]
lemma Nat.primeCounting_zero : Nat.primeCounting 0 = 0 :=
  Nat.primeCounting_eq_zero_iff.mpr zero_le_one

@[simp]
lemma Nat.primeCounting_one : Nat.primeCounting 1 = 0 :=
  Nat.primeCounting_eq_zero_iff.mpr le_rfl


-- @[simps]
-- def ArithmeticFunction.primeCounting : ArithmeticFunction ℝ where
--   toFun x := Nat.primeCounting ⌊x⌋₊
--   map_zero' := by simp [Nat.primeCounting_zero]

-- AkraBazzi.lean
lemma deriv_smoothingFn' {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) := by
  have : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx_pos hx
  rw [deriv_inv''] <;> aesop

lemma deriv_smoothingFn {x : ℝ} (hx : 1 < x) : deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) :=
  deriv_smoothingFn' (by positivity) (ne_of_gt hx)

noncomputable def th (x : ℝ) := ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, Real.log p

lemma th_def' (x : ℝ) :
    th x = ∑ n ∈ Iic ⌊x⌋₊, Set.indicator (setOf Nat.Prime) (fun n => log n) n := by
  unfold th
  rw [sum_filter]
  refine sum_congr rfl fun n _ => ?_
  simp [Set.indicator_apply]

lemma th_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : th x = 0 := by
  unfold th
  convert sum_empty
  ext y
  simp only [mem_filter, mem_Iic, not_mem_empty, iff_false, not_and]
  intro hy
  have : y < 2 := by
    cases lt_or_le x 0 with
    | inl hx' =>
      have := Nat.floor_of_nonpos hx'.le
      rw [this, nonpos_iff_eq_zero] at hy
      rw [hy]
      norm_num
    | inr hx' =>
      rw [← Nat.cast_lt_ofNat (α := ℝ)]
      apply lt_of_le_of_lt ?_ hx
      refine (le_floor_iff hx').mp hy
  contrapose! this
  exact this.two_le

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      th x / log x + ∫ t in Set.Icc 2 x, th t / (t * (Real.log t) ^ 2) := by
  trans th x / log x + ∫ t in Set.Icc (3 / 2) x, th t / (t * (Real.log t) ^ 2)
  swap
  · congr 1
    have : Set.Icc (3/2) x = Set.Ico (3/2) 2 ∪ Set.Icc 2 x := by
      symm
      apply Set.Ico_union_Icc_eq_Icc ?_ hx
      norm_num
    rw [this, integral_union]
    · simp only [add_left_eq_self]
      apply integral_eq_zero_of_ae
      simp only [measurableSet_Ico, ae_restrict_eq]
      refine eventuallyEq_inf_principal_iff.mpr ?_
      apply Eventually.of_forall
      intro y hy
      simp only [Set.mem_Ico] at hy
      have := th_eq_zero_of_lt_two hy.2
      simp_all
    · rw [Set.disjoint_iff, Set.subset_empty_iff]
      ext y
      simp (config := {contextual := true})
    · exact measurableSet_Icc
    · rw [integrableOn_congr_fun (g := 0)]
      exact integrableOn_zero
      · intro y hy
        simp only [Set.mem_Ico] at hy
        have := th_eq_zero_of_lt_two hy.2
        simp_all
      · exact measurableSet_Ico
    · unfold th
      -- fun_prop
      sorry

  -- have h1 (r : ℝ) : ∑ p ∈ (Iic ⌊r⌋₊).filter Nat.Prime, Real.log p =
  --     ∑ p ∈ (Iic ⌊r⌋₊), if p.Prime then Real.log p else 0 := by
  --   rw [sum_filter]
  let a : ArithmeticFunction ℝ := {
    toFun := Set.indicator (setOf Nat.Prime) (fun n => log n)
    map_zero' := by simp
  }
  have h3 (n : ℕ) : a n * (log n)⁻¹ = if n.Prime then 1 else 0 := by
    simp only [coe_mk, ite_mul, zero_mul, a]
    simp [Set.indicator_apply]
    split_ifs with h
    · refine mul_inv_cancel₀ ?_
      refine log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> norm_cast
      exacts [h.pos, h.ne_one]
    · rfl
  have h2 := abel_summation (ϕ := fun x => (log x)⁻¹) (a := a) (3 / 2) x
  have h4 : ⌊(3/2 : ℝ)⌋₊ = 1 := by rw [@floor_div_ofNat]; rw [Nat.floor_ofNat]
  have h5 : Iic 1 = {0, 1} := by ext; simp; omega
  have h6 (N : ℕ) : (filter Nat.Prime (Ioc 1 N)).card = Nat.primeCounting N := by
    have : filter Nat.Prime (Ioc 1 N) = filter Nat.Prime (range (N + 1)) := by
      ext n
      simp only [mem_filter, mem_Ioc, mem_range, and_congr_left_iff]
      intro hn
      simp [lt_succ, hn.one_lt]
    rw [this]
    simp [primeCounting, primeCounting', count_eq_card_filter_range]
  have h7 : a 1 = 0 := by
    simp [a]
  have h8 (f : ℝ → ℝ) :
    ∫ (u : ℝ) in Set.Icc (3 / 2) x, f u * deriv (fun x ↦ (log x)⁻¹) u =
    ∫ (u : ℝ) in Set.Icc (3 / 2) x, f u * -(u * log u ^ 2)⁻¹ := by
    apply setIntegral_congr_ae
    · exact measurableSet_Icc
    refine Eventually.of_forall (fun u hu => ?_)
    have hu' : 1 < u := by
      simp at hu
      calc
        (1 : ℝ) < 3/2 := by norm_num
        _ ≤ u := hu.1
    rw [deriv_smoothingFn hu']
    congr
    simp [div_eq_mul_inv, mul_comm]
  have h9 : 3/2 < x := calc
    3/2 < 2 := by norm_num
    _ ≤ x := hx

  simp [h3, h4, h5, h6, h7, h8, h9, integral_neg] at h2
  rw [h2]
  simp [a, ← th_def', div_eq_mul_inv]
  rw [contDiff_one_iff_deriv]
  sorry

-- lemma th43_b' (x : ℝ) (hx : 2 ≤ x) :
--     Nat.primeCounting ⌊x⌋₊ =
--     (Real.log x)⁻¹ * ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, Real.log p +
--       ∫ t in Set.Icc 2 x,
--         (∑ p ∈ (Iic ⌊t⌋₊).filter Nat.Prime, Real.log p) * (t * (Real.log t) ^ 2)⁻¹ := by
--   have h1 (r : ℝ) : ∑ p ∈ (Iic ⌊r⌋₊).filter Nat.Prime, Real.log p =
--       ∑ p ∈ (Iic ⌊r⌋₊), if p.Prime then Real.log p else 0 := by
--     rw [sum_filter]
--   -- simp_rw [h1]
--   have h2 := abel_summation (ϕ := fun x => (log x)⁻¹) (a := ArithmeticFunction.primeCounting) (3 / 2) x
--   simp [ArithmeticFunction.primeCounting] at h2
--   have : ⌊(3/2 : ℝ)⌋₊ = 1 := by rw [@floor_div_ofNat]; rw [Nat.floor_ofNat]
--   simp [this] at h2
--   have : Iic 1 = {0, 1} := by ext; simp; omega
--   simp [this] at h2
--   rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq] at h2
--   -- rw [← sub_mul] at h2
--   -- rw [← Finset.sum_sdiff_eq_sub] at h2
--   have := deriv_smoothingFn (one_lt_two.trans_le hx)
--   have :
--     ∫ (u : ℝ) in Set.Icc (3 / 2) x, (∑ x ∈ Iic ⌊u⌋₊, ↑x.primeCounting) * deriv (fun x ↦ (log x)⁻¹) u =
--     ∫ (u : ℝ) in Set.Icc (3 / 2) x, (∑ x ∈ Iic ⌊u⌋₊, ↑x.primeCounting) * -(u * log u ^ 2)⁻¹ := by
--     apply setIntegral_congr_ae
--     · exact measurableSet_Icc
--     refine Eventually.of_forall (fun u hu => ?_)
--     have hu' : 1 < u := by
--       simp at hu
--       calc
--         (1 : ℝ) < 3/2 := by norm_num
--         _ ≤ u := hu.1
--     rw [deriv_smoothingFn hu']
--     congr
--     simp [div_eq_mul_inv, mul_comm]
--   simp [this, ← sum_mul] at h2


--   done
-- #exit
/-%%
\begin{lemma}\label{range-eq-range}\lean{finsum_range_eq_sum_range, finsum_range_eq_sum_range'}\leanok For any arithmetic function $f$ and real number $x$, one has
$$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
and
$$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
\end{lemma}
%%-/
lemma finsum_range_eq_sum_range {R: Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n in range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R: Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n ≤ x), f n = ∑ n in Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero

/-%%
\begin{proof}\leanok Straightforward. \end{proof}
%%-/

lemma log2_pos : 0 < log 2 := by
  rw [Real.log_pos_iff zero_lt_two]
  exact one_lt_two

/-- Auxiliary lemma I for `chebyshev_asymptotic`: Expressing the sum over Λ up to N as a double sum over primes and exponents. -/
lemma sum_von_mangoldt_as_double_sum (x : ℝ) (hx: 0 ≤ x) :
  ∑ n in Iic ⌊x⌋₊, Λ n =
    ∑ k in Icc 1 ⌊ log x / log 2⌋₊,
      ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p := calc
    _ = ∑ n in Iic ⌊x⌋₊, ∑ k in Icc 1 ⌊ log x / log 2⌋₊, ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), if n = p^k then log p else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Iic, Nat.le_floor_iff hx] at hn
      rw [ArithmeticFunction.vonMangoldt_apply]
      by_cases h : IsPrimePow n
      . simp [h]
        rw [isPrimePow_def] at h
        obtain ⟨ p, k, ⟨ h1, h2, h3 ⟩ ⟩ := h
        rw [<- h3]
        replace h1 := h1.nat_prime
        calc
          _ = log p := by
            congr
            apply Nat.Prime.pow_minFac h1 (not_eq_zero_of_lt h2)
          _ = ∑ k' in Icc 1 ⌊ log x / log 2⌋₊, if k' = k then log p else 0 := by
            simp
            have h : k ≤ ⌊x.log / log 2⌋₊ := by
              have h5 : 2^k ≤ n := by
                rw [<-h3]
                apply Nat.pow_le_pow_of_le_left (Prime.two_le h1)
              have h6 : 1 ≤ x := by
                apply LE.le.trans _ hn
                simp only [one_le_cast]
                exact LE.le.trans Nat.one_le_two_pow h5
              have h7 : 0 < x := by linarith
              rw [Nat.le_floor_iff, le_div_iff₀ log2_pos, le_log_iff_exp_le h7, mul_comm, exp_mul, exp_log zero_lt_two]
              . apply LE.le.trans _ hn
                norm_cast
              apply div_nonneg (Real.log_nonneg h6) (le_of_lt log2_pos)
            have : 1 ≤ k ∧ k ≤ ⌊x.log / log 2⌋₊ := ⟨ h2, h ⟩
            simp [this]
          _ = ∑ k' in Icc 1 ⌊ log x / log 2⌋₊,
      ∑ p' in filter Nat.Prime (Iic ⌊ x^((k':ℝ)⁻¹) ⌋₊), if k'=k ∧ p'=p then log p else 0 := by
            apply Finset.sum_congr rfl
            intro k' _
            by_cases h : k' = k
            . have : p ≤ ⌊x ^ (k:ℝ)⁻¹⌋₊ := by
                rw [Nat.le_floor_iff]
                . rw [le_rpow_inv_iff_of_pos (cast_nonneg p) hx (cast_pos.mpr h2)]
                  apply LE.le.trans _ hn
                  rw [<-h3]
                  norm_num
                positivity
              simp [h, h1, this]
            simp [h]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k' _
            apply Finset.sum_congr rfl
            intro p' hp'
            by_cases h : p ^ k = p' ^ k'
            . simp at hp'
              have : (k' = k ∧ p' = p) := by
                have := eq_of_prime_pow_eq h1.prime hp'.2.prime h2 h
                rw [<-this, pow_right_inj] at h
                . exact ⟨ h.symm, this.symm ⟩
                . exact Prime.pos h1
                exact Nat.Prime.ne_one h1
              simp [h, this]
            have :¬ (k' = k ∧ p' = p) := by
              contrapose! h
              rw [h.1, h.2]
            simp [h, this]
      simp [h]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      apply Finset.sum_eq_zero
      intro p hp
      simp at hp ⊢
      intro hn'
      contrapose! h; clear h
      rw [isPrimePow_def]
      use p, k
      refine ⟨ Nat.Prime.prime hp.2, ⟨ ?_, hn'.symm ⟩ ⟩
      simp at hk
      exact hk.1
    _ = ∑ k in Icc 1 ⌊ log x / log 2⌋₊, ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), ∑ n in Iic ⌊x⌋₊, if n = p^k then log p else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro p hp
      simp at hk hp ⊢
      intro hpk
      rw [Nat.floor_lt hx] at hpk
      rw [Nat.le_floor_iff (rpow_nonneg hx (k:ℝ)⁻¹), Real.le_rpow_inv_iff_of_pos (cast_nonneg p) hx (cast_pos.mpr hk.1)] at hp
      simp at hpk hp
      linarith [hp.1]

/-- Auxiliary lemma II for `chebyshev_asymptotic`: Controlling the error. -/
lemma sum_von_mangoldt_sub_sum_primes_le (x : ℝ) (hx: 2 ≤ x) :
  |∑ n in Iic ⌊x⌋₊, Λ n - ∑ p in filter Nat.Prime (Iic ⌊ x⌋₊), log p| ≤ (x.log / log 2) * ((x ^ (2:ℝ)⁻¹ + 1) * x.log) := by
  have hx_one : 1 ≤ x := one_le_two.trans hx
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_two hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hlogx_nonneg : 0 ≤ log x := log_nonneg hx_one

  calc
    _ = |∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p + ∑ p in filter Nat.Prime (Iic ⌊ x^((1:ℝ)⁻¹) ⌋₊), log p - ∑ p in filter Nat.Prime (Iic ⌊ x⌋₊), log p| := by
      rw [sum_von_mangoldt_as_double_sum x hx_nonneg]
      congr
      have h : 1 ∈ Icc 1 ⌊ log x / log 2⌋₊ := by
        simp only [mem_Icc, le_refl, one_le_floor_iff, true_and]
        rwa [le_div_iff₀ log2_pos, one_mul, le_log_iff_exp_le hx_pos, exp_log zero_lt_two]
      set s := Icc 2 ⌊ log x / log 2⌋₊
      convert (Finset.sum_erase_add _ _ h).symm
      . ext n
        simp only [mem_Icc, Icc_erase_left, mem_Ioc, and_congr_left_iff, s]
        intro _
        rfl
      exact Eq.symm cast_one
    _ = |∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p| := by
        congr
        convert add_sub_cancel_right _ (∑ p in filter Nat.Prime (Iic ⌊ x⌋₊), log p)
        simp only [inv_one, rpow_one]
    _ ≤ ∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      |∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), |log p| := by
        apply sum_le_sum
        intro k _
        exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      ∑ _p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log x := by
        apply sum_le_sum
        intro k hk
        apply sum_le_sum
        intro p hp
        simp at hk hp
        have hp' : 1 ≤ p := Nat.Prime.one_le hp.2
        have hp'': p ≠ 0 := not_eq_zero_of_lt hp'
        replace hp := (Nat.le_floor_iff' hp'').mp hp.1
        rw [abs_of_nonneg, log_le_log_iff _ hx_pos]
        . apply hp.trans
          calc
            _ ≤ x^(1:ℝ) := by
              apply rpow_le_rpow_of_exponent_le hx_one
              apply inv_le_one
              simp only [one_le_cast]
              exact one_le_two.trans hk.1
            _ = _ := by
              simp only [rpow_one]
        . simpa only [cast_pos]
        apply log_nonneg
        simp only [one_le_cast, hp']
    _ ≤ ∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      (x^((2:ℝ)⁻¹)+1) * log x := by
        apply sum_le_sum
        intro k hk
        simp only [sum_const, nsmul_eq_mul]
        gcongr
        rw [<- Nat.le_floor_iff]
        . apply (Finset.card_filter_le _ _).trans
          rw [card_Iic, Nat.floor_add_one]
          . apply Nat.add_le_add _ NeZero.one_le
            apply floor_le_floor
            apply rpow_le_rpow_of_exponent_le hx_one
            simp at hk
            rw [inv_le_inv _ zero_lt_two]
            . exact ofNat_le_cast.mpr hk.1
            simp only [cast_pos]
            exact lt_of_lt_of_le zero_lt_two hk.1
          exact rpow_nonneg hx_nonneg 2⁻¹
        exact add_nonneg (rpow_nonneg hx_nonneg (2:ℝ)⁻¹) zero_le_one
    _ ≤ _ := by
      simp only [sum_const, card_Icc, reduceSubDiff, nsmul_eq_mul]
      gcongr
      apply LE.le.trans _ (Nat.floor_le _)
      simp only [cast_le, tsub_le_iff_right, le_add_iff_nonneg_right, _root_.zero_le]
      exact div_nonneg hlogx_nonneg (le_of_lt log2_pos)




theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β] {u : α → β} {v : α → β} {w : α → β} {l : Filter α} (huv : Asymptotics.IsEquivalent l u v) (hwu : (w-u) =o[l] v) :
Asymptotics.IsEquivalent l w v := by
  rw [<- add_sub_cancel u w]
  exact add_isLittleO huv hwu

theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β] {u : α → β} {v : α → β} {w : α → β} {l : Filter α} (huv : Asymptotics.IsEquivalent l u v) (hwu : (u-w) =o[l] v) :
Asymptotics.IsEquivalent l w v := by
  rw [<- sub_sub_self u w]
  exact sub_isLittleO huv hwu

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : a > 0) :
Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  convert squeeze_zero' (f := fun x ↦ log x ^ b / x^a) (g := fun x ↦ (log x ^ ⌈ b/a ⌉₊ / x)^a ) (t₀ := atTop) ?_ ?_ ?_
  . simp
    use 1
    intro x hx
    apply div_nonneg
    . apply rpow_nonneg
      exact log_nonneg hx
    apply rpow_nonneg
    apply zero_le_one.trans hx
  . simp
    use exp 1
    intro x hx
    have h0 : 0 < x := by
      apply lt_of_lt_of_le _ hx
      exact exp_pos 1
    have h1 : 1 ≤ log x := by
      rwa [le_log_iff_exp_le h0]
    rw [div_rpow _ (le_of_lt h0)]
    . rw [div_le_div_right (rpow_pos_of_pos h0 _), <-rpow_natCast, <-rpow_mul (zero_le_one.trans h1)]
      apply rpow_le_rpow_of_exponent_le h1
      rw [<-div_le_iff₀ ha]
      exact le_ceil _
    apply pow_nonneg
    apply zero_le_one.trans h1
  rw [(zero_rpow (_root_.ne_of_lt ha).symm).symm]
  apply Tendsto.rpow_const
  . have := tendsto_pow_log_div_mul_add_atTop 1 0 ⌈b/a⌉₊ zero_ne_one.symm
    simp at this
    exact this
  right
  exact le_of_lt ha

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n in Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n in Iic N, Λ n) / N) = (fun N ↦ (∑ n in range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [<-Finset.sum_erase_add _ _ this, <-Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, <-(AddLeftCancelMonoid.add_zero 1)]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  . intro N
    simp
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  . intro N
    simp
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : (fun x ↦ ∑ n in (Iic ⌊x⌋₊), Λ n) ~[atTop] (fun x ↦ x) := by
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    . rw [isEquivalent_iff_tendsto_one]
      . convert Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets, ge_iff_le,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [<-isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    . apply LE.le.trans _ ((inv_pos_le_iff_one_le_mul' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-%%
\begin{theorem}\label{chebyshev-asymptotic}\lean{chebyshev_asymptotic}\leanok  One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$
\end{theorem}
%%-/
theorem chebyshev_asymptotic :
    (fun x ↦ ∑ p in (filter Nat.Prime (Iic ⌊x⌋₊)), log p) ~[atTop] (fun x ↦ x) := by
  apply WeakPNT''.add_isLittleO''
  apply IsBigO.trans_isLittleO (g := fun x ↦ (x.log / log 2) * ((x ^ (2:ℝ)⁻¹ + 1) * x.log))
  . rw [isBigO_iff']
    use 1
    simp only [gt_iff_lt, zero_lt_one, Pi.sub_apply, norm_eq_abs, norm_div, one_mul,
      eventually_atTop, ge_iff_le, true_and]
    use 2
    intro x hx
    exact (sum_von_mangoldt_sub_sum_primes_le x hx).trans (le_abs_self _)
  apply Asymptotics.isLittleO_of_tendsto
  . intro x hx
    simp [hx]
  suffices h : Tendsto (fun x:ℝ ↦ ((x.log^2 / x ^ (2:ℝ)⁻¹) / log 2 + (x.log^2 / x) / log 2)) atTop (nhds 0) by
    apply Filter.Tendsto.congr' _ h
    simp [EventuallyEq]
    use 2
    intro x hx
    field_simp
    ring_nf
    rw [<-Real.rpow_mul_natCast]
    . simp
      ring
    linarith
  have h1 : (0:ℝ) = 0 + 0 := self_eq_add_right.mpr rfl
  have h2 : (0:ℝ) = 0 / log 2 := (zero_div _).symm
  rw [h1]
  apply Tendsto.add
  . rw [h2]
    apply Tendsto.div_const
    convert Real.tendsto_pow_log_div_pow_atTop (2:ℝ)⁻¹ 2 (by positivity) with x
    exact (rpow_two x.log).symm
  rw [h2]
  apply Tendsto.div_const
  convert Real.tendsto_pow_log_div_pow_atTop 1 2 (by positivity) with x
  . exact (rpow_two x.log).symm
  exact (rpow_one x).symm


-- one could also consider adding a version with p < x instead of p \leq x

/-%%
\begin{proof}
\uses{WeakPNT, range-eq-range}\leanok
From the prime number theorem we already have
$$ \sum_{n \leq x} \Lambda(n) = x + o(x)$$
so it suffices to show that
$$ \sum_{j \geq 2} \sum_{p^j \leq x} \log p = o(x).$$
Only the terms with $j \leq \log x / \log 2$ contribute, and each $j$ contributes at most $\sqrt{x} \log x$ to the sum, so the left-hand side is $O( \sqrt{x} \log^2 x ) = o(x)$ as required.
\end{proof}
%%-/

/-%%
\begin{corollary}[Bounds on primorial]  \label{primorial-bounds}\lean{primorial_bounds}\leanok
We have
  $$ \prod_{p \leq x} p = \exp( x + o(x) )$$
\end{corollary}
%%-/
theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
    ∀ x : ℝ, ∏ p in (filter Nat.Prime (Iic ⌊x⌋₊)), p = exp ( x + E x ) := by
  sorry

/-%%
\begin{proof}
\uses{chebyshev-asymptotic}
  Exponentiate Theorem \ref{chebyshev-asymptotic}.
\end{proof}
%%-/

/-%%
Let $\pi(x)$ denote the number of primes up to $x$.

\begin{theorem}\label{pi-asymp}\lean{pi_asymp}\leanok  One has
  $$ \pi(x) = (1+o(1)) \int_2^x \frac{dt}{\log t}$$
as $x \to \infty$.
\end{theorem}
%%-/
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in Set.Icc 2 x, 1 / (log t) ∂ volume := by
  have h0 (x : ℝ) :
    ∫ t in Set.Icc 2 x,
        (∑ p ∈ (Iic ⌊t⌋₊).filter Nat.Prime, Real.log p) * (t * (Real.log t) ^ 2)⁻¹ = 0 := by
    simp_rw [sum_mul]
    convert
      @MeasureTheory.integral_finset_sum
      ℝ
      _
      _
      _
      _
      (volume.restrict (Set.Icc (2 : ℝ) x))
      ℕ
      ((Iic ⌊x⌋₊).filter Nat.Prime)
      (fun i t => log ↑i * (t * log t ^ 2)⁻¹)
      ?_
      using 1
      with u
    done
  have h1 (x : ℝ) : Nat.primeCounting ⌊x⌋₊ =
    (Real.log x)⁻¹ * ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, Real.log p +
      ∫ t in Set.Icc 2 x,
        (∑ p ∈ (Iic ⌊t⌋₊).filter Nat.Prime, Real.log p) * (t * (Real.log t) ^ 2)⁻¹ := by
    -- can be proven by interchanging the sum and integral and using the fundamental theorem of
    -- calculus
    simp_rw [sum_mul]
    rw [@MeasureTheory.integral_finset_sum
      ℝ
      _
      _
      _
      _
      (volume.restrict (Set.Icc (2 : ℝ) x))
      ℕ
      ((Iic ⌊x⌋₊).filter Nat.Prime)
      fun i t => log ↑i * (t * log t ^ 2)⁻¹
      ]

    rw [← MeasureTheory.integral_subtype]

    rw [@MeasureTheory.integral_finset_sum
      (Set.Icc 2 x)
      _
      _
      _
      _
      volume
      (ι := ℕ) (s := (Iic ⌊x⌋₊).filter Nat.Prime)
      ]
    sorry
  #check chebyshev_asymptotic
  -- have h2 (ε : ℝ) : ∃ xε := chebyshev_asymptotic
  sorry

/-%%
\begin{proof}
\uses{chebyshev-asymptotic}
We have the identity
$$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
+ \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
as can be proven by interchanging the sum and integral and using the fundamental theorem of calculus.  For any $\eps$, we know from Theorem \ref{chebyshev-asymptotic} that there is $x_\eps$ such that
$\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
$$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
+ \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate this after an integration by parts as
$$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
$$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
for $x$ large enough, giving the claim.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{pi-alt}\lean{pi_alt}\leanok  One has
$$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
as $x \to \infty$.
\end{corollary}
%%-/
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  sorry

/-%%
\begin{proof}
\uses{pi-asymp}
An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} + \int_2^x \frac{dt}{\log^2 t}.$$
We have the crude bounds
$$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
and
$$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
and combining all this we obtain
$$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
$$ = (1+o(1)) \frac{x}{\log x}$$
and the claim then follows from Theorem \ref{pi-asymp}.
\end{proof}
%%-/

/-%%
Let $p_n$ denote the $n^{th}$ prime.

\begin{proposition}\label{pn-asymptotic}\lean{pn_asymptotic}\leanok
 One has
  $$ p_n = (1+o(1)) n \log n$$
as $n \to \infty$.
\end{proposition}
%%-/
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime n = (1 + c n) * n * log n := by
  sorry

/-%%
\begin{proof}
\uses{pi-alt}
Use Corollary \ref{pi-alt} to show that for any $\eps>0$, and for $x$ sufficiently large, the number of primes up to $(1-\eps) n \log n$ is less than $n$, and the number of primes up to $(1+\eps) n \log n$ is greater than $n$.
\end{proof}
%%-/

/-%%
\begin{corollary} \label{pn-pnPlus1}\lean{pn_pn_plus_one}\leanok
We have $p_{n+1} - p_n = o(p_n)$
  as $n \to \infty$.
\end{corollary}
%%-/

theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n = (c n) * Nat.nth Nat.Prime n := by
  sorry

/-%%
\begin{proof}
\uses{pn-asymptotic}
  Easy consequence of preceding proposition.
\end{proof}
%%-/

/-%%
\begin{corollary}  \label{prime-between}\lean{prime_between}\leanok
For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for all sufficiently large $x$.
\end{corollary}
%%-/

theorem prime_between {ε:ℝ} (hε: 0 < ε): ∀ᶠ x:ℝ in atTop, ∃ p:ℕ, Nat.Prime p ∧
    x < p ∧ p < (1+ε)* x := by
  sorry


/-%%
\begin{proof}
\uses{pi-alt}
Use Corollary \ref{pi-alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity as $x \to \infty$.
\end{proof}
%%-/

/-%%
\begin{proposition}\label{mun}\lean{sum_mobius_div_self_le}\leanok
We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \leq 1$.
\end{proposition}
%%-/
theorem sum_mobius_div_self_le (N : ℕ) : |∑ n in range N, μ n / (n : ℚ)| ≤ 1 := by
  cases' N with N
  /- simple cases -/
  simp only [range_zero, sum_empty, abs_zero, zero_le_one]
  by_cases hN : 1 ≤ N; swap
  · simp only [not_le, lt_one_iff] at hN
    subst hN
    simp
  /- annoying case -/
  have h_sum : 1 = ∑ d in range (N + 1), (μ d : ℚ) * (N / d : ℕ) := by calc
    (1 : ℚ) = ∑ m in Icc 1 N, ∑ d in m.divisors, μ d := by
      have {N : ℕ} : (1 : ArithmeticFunction _) N = ∑ d in N.divisors, μ d := by
        rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta]
      rw [Icc_eq_cons_Ioc hN, Finset.sum_cons, divisors_one, sum_singleton, moebius_apply_one]
      have {x : ℕ} (hx : x ∈ Ioc 1 N) : ∑ d in divisors x, μ d = 0 := by
        rw [mem_Ioc] at hx
        simp only [← this, one_apply, hx.left.ne.symm, if_false]
      rw [sum_congr rfl (fun _ ↦ this), sum_const, smul_zero, add_zero, Int.cast_one]
    _ = ∑ d in range (N + 1), μ d * (N / d) := by
      simp_rw [← coe_mul_zeta_apply, ArithmeticFunction.sum_Icc_mul_zeta, nsmul_eq_mul, mul_comm]
      rw [range_eq_Ico, ← Ico_insert_succ_left (succ_pos _), sum_insert, ArithmeticFunction.map_zero,
        mul_zero, zero_add]
      · congr
      · simp
    _ = ∑ d in range (N + 1), (μ d : ℚ) * (N / d : ℕ) := by
      norm_num [Int.cast_sum]
      rfl

  /- rewrite Nat division (N / d) as ⌊N / d⌋ -/
  rw [sum_congr rfl (g := fun d ↦ (μ d : ℚ) * ⌊(N : ℚ) / (d : ℚ)⌋)] at h_sum
  swap
  intros
  rw [show (N : ℚ) = ((N : ℤ) : ℚ) by norm_cast, Rat.floor_int_div_nat_eq_div]
  congr

  /- Next, we establish bounds for the error term -/
  have hf' (d : ℕ) : |Int.fract ((N : ℚ) / d)| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact Int.fract_lt_one _
  have h_bound : |∑ d in range (N + 1), μ d * Int.fract ((N : ℚ) / d)| ≤ N - 1 := by
    /- range (N + 1) → Icc 1 N + part that evals to 0 -/
    rw [range_eq_Ico, ← Ico_insert_succ_left, sum_insert, ArithmeticFunction.map_zero,
      Int.cast_zero, zero_mul, zero_add, Ico_succ_right]
    all_goals simp
    /- Ico 1 (N + 1) → Ico 1 N ∪ {N + 1} that evals to 0 -/
    rw [← Ico_insert_right, sum_insert, div_self, Int.fract_one, mul_zero]
    all_goals simp [hN, Nat.pos_iff_ne_zero.mp hN]
    /- bound sum -/
    have (d : ℕ) : |μ d * Int.fract ((N : ℚ) / d)| ≤ 1 := by
      rw [abs_mul, ← one_mul 1]
      apply mul_le_mul ?_ (hf' _).le (abs_nonneg _) zero_le_one
      norm_cast
      simp [moebius]
      split_ifs <;> simp only [abs_zero, zero_le_one, abs_pow, abs_neg, abs_one, one_pow, le_refl]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum fun d _ ↦ this d).trans
    all_goals simp [sum_ite, cast_sub hN]

  rw [sum_congr rfl (g := fun d : ℕ ↦ μ d * ((N : ℚ) / d - Int.fract ((N : ℚ) / d)))
    fun d _ ↦ by simp only [Int.fract, sub_sub_self]] at h_sum
  simp_rw (config := {singlePass := true}) [mul_sub] at h_sum
  simp_rw [← mul_comm_div, sum_sub_distrib, ← sum_mul] at h_sum
  rw [eq_sub_iff_add_eq, eq_comm, ← eq_div_iff (by norm_num [Nat.pos_iff_ne_zero.mp hN])] at h_sum

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

theorem mu_pnt : (fun x:ℝ ↦ ∑ n in range ⌊ x ⌋₊, μ n) =o[atTop] (fun x ↦ x) := by sorry

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

theorem lambda_pnt : (fun x:ℝ ↦ ∑ n in range ⌊ x ⌋₊, (-1)^(Ω n)) =o[atTop] (fun x ↦ x) := by
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

theorem mu_pnt_alt : (fun x:ℝ ↦ ∑ n in range ⌊ x ⌋₊, (μ n: ℝ) / n) =o[atTop] (fun x ↦ (1:ℝ)) := by sorry

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
