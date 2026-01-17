import Architect
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.Bounds
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
lemma deriv_smoothingFn' {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) :
    deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) := by
  have : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx_pos hx
  rw [deriv_fun_inv''] <;> aesop

lemma deriv_smoothingFn {x : ℝ} (hx : 1 < x) :
    deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) :=
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
  rw [sum_mul_eq_sub_sub_integral_mul a (f := fun n ↦ 1 / log n) (by norm_num) (by linarith),
    floor32, show Icc 0 1 = {0, 1} by ext; simp; omega]
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, mem_singleton, zero_ne_one,
      not_false_eq_true, sum_insert, CharP.cast_eq_zero, log_zero, ite_self, sum_singleton,
      cast_one, log_one, add_zero, mul_zero, sub_zero, Chebyshev.theta_eq_sum_Icc, a, sum_filter]
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
    have : ∀ y ∈ Set.Icc (3 / 2) x,
        deriv (fun x ↦ (log x)⁻¹) y = -(y * log y ^ 2)⁻¹ := by
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

@[blueprint
  (title := "finsum-range-eq-sum-range")
  (statement := /--
   For any arithmetic function $f$ and real number $x$, one has
  $$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
  and
  $$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
  -/)
  (proof := /-- Straightforward. -/)
  (latexEnv := "lemma")]
lemma finsum_range_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R}
    (x : ℝ) : ∑ᶠ (n : ℕ) (_ : n ≤ x), f n = ∑ n ∈ Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero


lemma log2_pos : 0 < log 2 := by
  rw [Real.log_pos_iff zero_le_two]
  exact one_lt_two


/-- If u ~ v and w-u = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (w - u) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← add_sub_cancel u w]
  exact add_isLittleO huv hwu

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
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

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

/-- `(⌊x⌋₊ + 1) / x → 1` as `x → ∞`. -/
lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  have h := Asymptotics.isEquivalent_nat_floor (R := ℝ)
  have h' : IsEquivalent atTop (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) + 1) _root_.id :=
    h.add_isLittleO (isLittleO_const_id_atTop 1)
  rwa [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx a; simp only [_root_.id] at a; linarith)] at h'

/-- `x =Θ x / c` for nonzero constant `c`. -/
lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  have : (fun x : ℝ ↦ x / c) = fun x ↦ c⁻¹ * x := by ext x; ring
  exact this ▸ (isTheta_const_mul_left (inv_ne_zero hc)).mpr (isTheta_refl ..) |>.symm

/-- Filtered sum over `Iic n` equals filtered sum over `Icc 1 n` for primes. -/
lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  ext p; simp only [mem_filter, mem_Iic, mem_Icc, and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ ⟨hp.one_lt.le, h⟩, fun ⟨_, h⟩ ↦ h⟩

/-- `Icc 0 n = insert 0 (Icc 1 n)` -/
lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m; simp [mem_Icc]; omega

@[blueprint "chebyshev-asymptotic"
  (title := "chebyshev-asymptotic")
  (statement := /--
  One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$
  -/)
  (proof := /--
  From the prime number theorem we already have
  $$ \sum_{n \leq x} \Lambda(n) = x + o(x)$$
  so it suffices to show that
  $$ \sum_{j \geq 2} \sum_{p^j \leq x} \log p = o(x).$$
  Only the terms with $j \leq \log x / \log 2$ contribute, and each $j$ contributes at most
  $\sqrt{x} \log x$ to the sum, so the left-hand side is $O( \sqrt{x} \log^2 x ) = o(x)$ as
  required.
  -/)]
theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop, ge_iff_le]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using isLittleO_sqrt_mul_log.const_mul_left 2

theorem chebyshev_asymptotic_finsum :
    (fun x ↦ ∑ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), log p) ~[atTop] fun x ↦ x := by
  have hReal :
      (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) ~[atTop]
        fun x ↦ x := by
    have h x : ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ) = θ x := by
      rw [Chebyshev.theta_eq_sum_Icc]
      have hfin : {p : ℕ | (p : ℝ) ≤ x ∧ p.Prime}.Finite :=
        (Iic ⌊x⌋₊).finite_toSet.subset fun p ⟨hpx, _⟩ ↦ mem_Iic.mpr (Nat.le_floor hpx)
      calc ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)
          = ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x ∧ p.Prime), log (p : ℝ) :=
            finsum_congr fun p ↦ by by_cases hp : p.Prime <;> simp [hp]
        _ = ∑ p ∈ hfin.toFinset, log (p : ℝ) := finsum_mem_eq_finite_toFinset_sum _ hfin
        _ = _ := sum_congr (by ext p; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq,
            mem_filter, mem_Icc, and_congr_left_iff]; exact fun hp ↦
            ⟨fun hpx ↦ ⟨Nat.zero_le _, Nat.le_floor hpx⟩, fun ⟨_, hpn⟩ ↦
              (le_or_gt 0 x).elim
                (fun hx ↦ (Nat.floor_le hx).trans' (Nat.cast_le.mpr hpn)) fun hx ↦
                absurd (Nat.le_zero.mp (Nat.floor_eq_zero.mpr (hx.trans_le zero_le_one) ▸ hpn))
                  hp.ne_zero⟩) (fun _ _ ↦ rfl)
    have heq :
        (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) =ᶠ[atTop] θ :=
      Filter.Eventually.of_forall h
    exact chebyshev_asymptotic.congr_left heq.symm
  simp only [IsEquivalent,
    show (fun n : ℕ ↦ ∑ᶠ (p : ℕ) (_ : p ≤ n) (_ : p.Prime), log (p : ℝ)) =
      (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) ∘ Nat.cast
    from funext fun _ ↦ finsum_congr fun _ ↦ by simp]
  exact hReal.isLittleO.comp_tendsto tendsto_natCast_atTop_atTop

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
    refine inte x hx |>.mul_continuousOn (g' := fun t : ℝ => t⁻¹)
      (continuousOn_inv₀ |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) isCompact_Icc |>.congr_fun_ae <| .of_forall <| by simp [div_eq_mul_inv]
  intro x hx
  rw [hf2, mul_div_cancel₀]
  linarith

-- one could also consider adding a version with p < x instead of p \leq x


@[blueprint
  (title := "primorial-bounds")
  (statement := /--
  We have
    $$ \prod_{p \leq x} p = \exp( x + o(x) )$$
  -/)
  (proof := /-- Exponentiate Theorem \ref{chebyshev_asymptotic}. -/)
  (latexEnv := "corollary")]
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
  obtain ⟨E, hE, hprod⟩ := primorial_bounds
  refine ⟨E, hE, fun x ↦ ?_⟩
  have hfin : {p : ℕ | (p : ℝ) ≤ x ∧ p.Prime}.Finite :=
    (Iic ⌊x⌋₊).finite_toSet.subset fun p ⟨hpx, _⟩ ↦ mem_Iic.mpr <| le_floor hpx
  have heq : ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), p =
      ∏ p ∈ (Iic ⌊x⌋₊).filter Prime, p := by
    calc ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), p
        = ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x ∧ p.Prime), p :=
      finprod_congr fun p ↦ by by_cases hp : p.Prime <;> simp [hp]
      _ = ∏ p ∈ hfin.toFinset, p := finprod_mem_eq_finite_toFinset_prod _ hfin
      _ = _ := prod_congr (by ext p; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq,
          mem_filter, mem_Iic, and_congr_left_iff]; exact fun hp ↦
          ⟨le_floor, fun hpn ↦ (le_or_gt 0 x).elim
          (fun hx ↦ (Nat.floor_le hx).trans' (cast_le.mpr hpn)) fun hx ↦
          absurd (le_zero.mp (floor_eq_zero.mpr (hx.trans_le zero_le_one) ▸ hpn))
          hp.ne_zero⟩) (fun _ _ ↦ rfl)
  simp only [heq, hprod]

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma continuousOn_log1 : ContinuousOn (fun x ↦ (log x ^ 2)⁻¹ * x⁻¹) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

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
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by
          rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := fun t => t⁻¹) (x := x)
        · simpa using HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x)
            (hasDerivAt_id' (log x))
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

lemma pi_asymp_aux (x : ℝ) (hx : 2 ≤ x) : Nat.primeCounting ⌊x⌋₊ =
    (log x)⁻¹ * θ x + ∫ t in Set.Icc 2 x, θ t * (t * log t ^ 2)⁻¹ := by
  rw [th43_b _ hx]
  simp_rw [div_eq_mul_inv, Chebyshev.theta_eq_sum_Icc]
  ring_nf!

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
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
  simp_rw [isLittleO_iff] at hf
  choose C hC using eq1
  simp_rw [← one_div] at hC
  apply isLittleO_congr hC (by rfl) |>.mpr
  have ineq1 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c) : ∀ᶠ(x : ℝ) in atTop,
    (log x)⁻¹ * x * |f x| ≤ c * ε * ((log x)⁻¹ * x) := by
    filter_upwards [eventually_ge_atTop 2, hf ε hε hc] with x hx hM
    simp only [norm_eq_abs] at hM
    rw [abs_of_pos hε] at hM
    rw [mul_comm (c * ε)]
    gcongr
    bound
  have int_flog {a b : ℝ} (ha: 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ |f t| * (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    apply IntegrableOn.mul_continuousOn
    · apply Integrable.abs <| f_int b hb |>.mono (Set.Icc_subset_Icc_left ha) (by rfl)
    · refine ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
      · simp
        grind
      · intro t ht
        simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
        exact ⟨by linarith, by linarith, by linarith⟩
    · exact isCompact_Icc
  have int_inv_log_sq {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    refine ContinuousOn.integrableOn_Icc <|
      ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
    · grind
    · intro t ht
      simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
  simp_rw [eventually_atTop] at hf
  choose M hM using hf
  have ineq2 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c)  :
    ∃ (D : ℝ),
      ∀ᶠ (x : ℝ) in atTop,
      |∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹| ≤
      c * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) + D := by
    use (((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), |f t| * (log t ^ 2)⁻¹) -
              c * ε * ∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹) +
            c * ε * ((log 2)⁻¹ * 2))
    filter_upwards [eventually_gt_atTop (max 2 (M ε hε hc))] with x hx
    calc _
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
        rw [← integral_union_ae, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
        · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le, volume_singleton]
        · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
        · apply int_flog (by rfl) (le_max_left ..)
        · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ ≤ (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          (c * ε) * (log t ^ 2)⁻¹) := by
          gcongr 1
          apply setIntegral_mono_on
          · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
          · rw [IntegrableOn, integrable_const_mul_iff]
            · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
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
        ring
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) -
              ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
          congr 3
          rw [add_comm, ← integral_union_ae, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
          · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le,
              volume_singleton]
          · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
          · apply int_inv_log_sq (by rfl) (le_max_left ..)
          · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
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
        rw [integral_log_inv' _ _ (by rfl)]
        · ring
        · simp only [max_lt_iff] at hx
          linarith
      _ = _ := by ring
  choose D hD using ineq2

  have ineq4 (const : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, |const / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| ≤ 1/2 * ε := by
    obtain rfl|hconst := eq_or_ne const 0
    · filter_upwards with x
      simp[hε.le]
    have ineq (x : ℝ) (hx : 2 < x) :=
      calc (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)
        _ ≥ (∫ (_ : ℝ) in Set.Icc 2 x, (log x)⁻¹) := by
          apply setIntegral_mono_on (integrable_const _)
          · refine ContinuousOn.integrableOn_Icc <|
              ContinuousOn.inv₀ (continuousOn_log |>.mono ?_) ?_
            · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le,
              isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
            · intro t ht
              simp only [Set.mem_Icc, ne_eq, log_eq_zero, not_or] at ht ⊢
              exact ⟨by linarith, by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ⟨ht1, ht2⟩
            gcongr
            bound
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
      apply div_le_div₀ (abs_nonneg _) (by rfl)
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
  rw [isLittleO_iff]
  intro ε hε
  specialize ineq4 (|D ε hε (1/2) (by linarith)| + |C|) ε hε
  simp only [one_div, norm_eq_abs, norm_one, mul_one]
  filter_upwards [eventually_gt_atTop 2, ineq4, ineq1 ε hε (1 / 2) (by norm_num),
      hD ε hε (1 / 2) (by norm_num)] with x hx hB ineq1 hD
  have := integral_log_inv_pos x (by linarith) |>.le
  calc _
    _ ≤ |((log x)⁻¹ * (x * f x) / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      apply abs_add_three
    _ = |(log x)⁻¹ * (x * f x)| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      rw [abs_div, abs_div, abs_div]
    _ = |(log x)⁻¹ * (x * f x)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        repeat rw [abs_of_pos <| integral_log_inv_pos _ (by linarith)]
    _ = ((log x)⁻¹ * x * |f x|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        congr
        rw [abs_mul, abs_mul, abs_of_nonneg (by bound), abs_of_nonneg (by linarith), mul_assoc]
    _ ≤ ((1/2) * ε * ((log x)⁻¹ * x)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        ((1/2) * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) +
          D ε hε (1/2) (by linarith)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        gcongr
    _ = ((1/2) * ε * (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (D ε hε (1/2) (by linarith) + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      ring
    _ = (1/2) * ε + (D ε hε (1/2) (by linarith) + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      congr 1
      rw [mul_div_assoc, div_self, mul_one]
      apply integral_log_inv_ne_zero
      linarith
    _ ≤ (1/2) * ε + (|D ε hε (1/2) (by linarith)| + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      gcongr
      apply le_abs_self
    _ ≤ (1/2) * ε + (1/2) * ε := by
      rw [abs_div, abs_of_nonneg, abs_of_pos (a := ∫ _ in _, _)] at hB
      · gcongr
      · apply integral_log_inv_pos; linarith
      · positivity
    _ = ε := by
      field

@[blueprint
  (title := "pi-asymp")
  (statement := /--
  There exists a function $c(x)$ such that $c(x) = o(1)$ as $x \to \infty$ and
  $$ \pi(x) = (1 + c(x)) \int_2^x \frac{dt}{\log t}$$
  for all $x$ large enough.
  -/)
  (proof := /--
  We have the identity
  $$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
  + \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
  as can be proven by interchanging the sum and integral and using the fundamental theorem of
  calculus.  For any $\eps$, we know from Theorem \ref{chebyshev_asymptotic} that there is $x_\eps$
  such that $\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
  $$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
  + \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
  where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate
  this after an integration by parts as
  $$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
  $$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
  for $x$ large enough, giving the claim.
  -/)]
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  field [(integral_log_inv_pos x (by linarith)).ne']


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
  _ = (∫ (t : ℝ) in (2)..(√x), 1 / log t ^ 2) +
        ∫ (t : ℝ) in (√x)..x, 1 / log t ^ 2 := by
    simp only [one_div]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [(le_of_max_le_left hx)]),
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
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx'.1]) ] at hc1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx'.2] at hc2
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
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx]),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx]),
    ← mul_one_div, one_div, ← mul_one_div, one_div]
  simp only [one_div, this, mul_comm]

lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  obtain ⟨c, hc⟩ := inv_div_log_asy
  use fun x => ((∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2) - 2 / log 2) * log x / x
  constructor
  · simp_rw [mul_div_assoc, mul_comm]
    apply isLittleO_mul_iff_isLittleO_div _|>.mpr
    · simp_rw [one_div_div]
      apply IsLittleO.sub
      · apply IsBigO.trans_isLittleO (g := (fun x ↦ x / log x ^ 2))
        · rw [isBigO_iff]
          use c
          filter_upwards [eventually_ge_atTop 2, hc] with x hx hc
          simp only [norm_eq_abs]
          rwa [abs_of_nonneg, abs_of_nonneg]
          · bound
          · apply setIntegral_nonneg measurableSet_Icc fun t ht ↦ (by bound)
        apply isLittleO_of_tendsto
        · simp
        apply tendsto_log_atTop.inv_tendsto_atTop.congr'
        filter_upwards [eventually_ne_atTop 0] with x hx
        simp only [Pi.inv_apply]
        field
      apply isLittleO_mul_iff_isLittleO_div _|>.mp
      · conv => arg 2; ext; rw [mul_comm]
        apply IsLittleO.const_mul_left isLittleO_log_id_atTop
      · filter_upwards [eventually_ge_atTop 2] with x hx
        simp; grind
    filter_upwards [eventually_ge_atTop 2] with x hx
    simp
    grind
  · filter_upwards [eventually_ge_atTop 4] with x hx
    rw [integral_log_inv_pialt x hx]
    field [show log x ≠ 0 by simp; grind]

@[blueprint
  (title := "pi-alt")
  (statement := /--
    One has
  $$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
  as $x \to \infty$.
  -/)
  (proof := /--
  An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} +
  \int_2^x \frac{dt}{\log^2 t}.$$
  We have the crude bounds
  $$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
  and
  $$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
  and combining all this we obtain
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
  $$ = (1+o(1)) \frac{x}{\log x}$$
  and the claim then follows from Theorem \ref{pi_asymp}.
  -/)
  (latexEnv := "corollary")]
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  obtain ⟨f, hf, h⟩ := pi_asymp
  obtain ⟨f', hf', h'⟩ := integral_div_log_asymptotic
  use (fun x => (log x / x) * ⌊x⌋₊.primeCounting - 1)
  constructor
  · apply IsLittleO.congr' (f₁ := (fun x ↦ f x + f x * f' x + f' x)) _ _ (by rfl)
    · apply IsLittleO.add _ hf'
      apply IsLittleO.add hf
      convert hf.mul hf'
      ring
    · filter_upwards [eventually_ge_atTop 2, h, h'] with x hx h h'
      rw [h, intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc, h']
      have : log x ≠ 0 := by simp; grind
      field
  · intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

theorem pi_alt' :
    (fun (x : ℝ) ↦ (primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / log x) := by
  obtain ⟨f, ⟨hf1, hf2⟩⟩ := pi_alt
  simp_rw [hf2, IsEquivalent]
  have : ((fun x ↦ (1 + f x) * x / log x) - fun x ↦ x / log x) =
      (fun x ↦ f x * x / log x) := by
    ext
    simp
    ring
  rw [this]
  convert hf1.mul_isBigO (f₂ := (fun x ↦ x / log x)) (g₂ := (fun x ↦ x /log x))
      (isBigO_refl ..) using 2
  all_goals ring


blueprint_comment /--
Let $p_n$ denote the $n^{th}$ prime.
-/

noncomputable abbrev nth_prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma pi_nth_prime (n : ℕ) :
    primeCounting (nth_prime n) = n + 1 := by
  rw [primeCounting, primeCounting', count_nth_succ_of_infinite infinite_setOf_prime]

lemma tendsto_nth_prime_atTop : Tendsto nth_prime atTop atTop :=
  nth_strictMono infinite_setOf_prime |>.tendsto_atTop

lemma pi_nth_prime_asymp :
    (fun n ↦ (nth_prime n) / (log (nth_prime n))) ~[atTop] (fun (n : ℕ) ↦ (n : ℝ)) := by
  trans (fun (n : ℕ) ↦ ( n + 1 : ℝ))
  · have : Tendsto (fun n ↦ ((Nat.nth Nat.Prime n) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_iff.mpr tendsto_nth_prime_atTop
    convert pi_alt'.comp_tendsto this |>.symm
    simp only [Function.comp_apply, floor_natCast]
    rw [pi_nth_prime]
    norm_cast
  · apply IsEquivalent.add_isLittleO (by rfl)
    exact isLittleO_const_id_atTop (1 : ℝ) |>.natCast_atTop

lemma log_nth_prime_asymp : (fun n ↦ log (nth_prime n)) ~[atTop] (fun n ↦ log n) := by
  have := pi_nth_prime_asymp.log tendsto_natCast_atTop_atTop
  · apply IsEquivalent.trans _ this
    apply IsEquivalent.congr_right (v := (fun n ↦ log (nth_prime n) - log (log (nth_prime n))))
    swap
    · filter_upwards with n
      rw [log_div]
      · exact_mod_cast prime_nth_prime n |>.ne_zero
      · apply log_ne_zero.mpr ⟨?_, ?_, ?_⟩
        <;> norm_cast<;> linarith [prime_nth_prime n |>.two_le]
    symm
    apply IsEquivalent.sub_isLittleO (by rfl)
    apply IsLittleO.comp_tendsto isLittleO_log_id_atTop
    have : Tendsto (fun n ↦ ((Nat.nth Nat.Prime n) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_iff.mpr tendsto_nth_prime_atTop
    apply tendsto_log_atTop.comp this

lemma nth_prime_asymp : (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ n * log n) := by
  have := pi_nth_prime_asymp.mul log_nth_prime_asymp
  convert this using 1
  ext n
  simp only [Pi.mul_apply]
  have : log (nth_prime n) ≠ 0 :=by
    apply log_ne_zero.mpr ⟨?_, ?_, ?_⟩
      <;> norm_cast<;> linarith [prime_nth_prime n |>.two_le]
  field

@[blueprint
  (title := "pn-asymptotic")
  (statement := /--
   One has
    $$ p_n = (1+o(1)) n \log n$$
  as $n \to \infty$.
  -/)
  (proof := /--
    Use Corollary \ref{pi_alt} to show that $n=\pi(p_n)\sim p_n/\log p_n$
    Taking logs gives $\log n \sim \log p_n - \log\log p_n \sim \log p_n$.
    Multiplying these gives $p_n\sim n\log n$ from which the result follows.
  -/)
  (latexEnv := "proposition")]
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, n > 1 → Nat.nth Nat.Prime n = (1 + c n) * n * log n := by
  let c : ℕ → ℝ := fun n ↦ (Nat.nth Nat.Prime n) / (n * log n) - 1
  refine ⟨c, ?_, ?_⟩
  swap
  · intro n hn
    have : log n ≠ 0 := by rw [Real.log_ne_zero]; rify at hn; grind
    simp [c]
    field_simp
  apply isLittleO_of_tendsto
  · simp
  simp only [div_one]
  unfold c
  have := isEquivalent_iff_tendsto_one ?_|>.mp nth_prime_asymp
  swap
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simp
    norm_cast
    grind
  convert this.add_const (-1 : ℝ) using 2
  norm_num


@[blueprint
  (title := "pn-pn-plus-one")
  (statement := /--
  We have $p_{n+1} - p_n = o(p_n)$
    as $n \to \infty$.
  -/)
  (proof := /-- Easy consequence of preceding proposition. -/)
  (latexEnv := "corollary")]
theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = (c n) * Nat.nth Nat.Prime n := by
  use (fun n => (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n) / Nat.nth Nat.Prime n)
  refine ⟨?_, ?_⟩
  · obtain ⟨k, k_o1, p_n_eq⟩ := pn_asymptotic
    simp only [isLittleO_one_iff]
    rw [Filter.tendsto_congr' (f₂ := fun n ↦
        ((1 + k (n+1))*(n+1)*log (n+1) - (1 + k n)*n*log n) / ((1 + k n)*n*log n))]
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
                have shift_fn :=
                  Filter.tendsto_add_atTop_iff_nat (f := fun n => log (n)) (l := atTop) 2
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
    ∀ᶠ x : ℝ in atTop, (1 + f x) < (1 + δ) := by
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


lemma bound_f_first_term {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
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
    ∀ᶠ x : ℝ in atTop, (1 - δ) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) <
      (1 + f ((1 + ε) * x)) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) := by
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
    ∀ᶠ x : ℝ in atTop,
      (1 + δ) * (x / Real.log x) > (1 + f x) * (x / Real.log x) := by
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
  have inv_log_x_div := Filter.Tendsto.comp (f := fun x => Real.log x / x) (g := fun x => x⁻¹)
    (x := Filter.atTop) (y := (nhdsWithin 0 (Set.Ioi 0))) (z := Filter.atTop) ?_ ?_
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
    Tendsto (fun (x : ℝ) => (Nat.primeCounting ⌊(1 + ε) * x⌋₊ : ℝ) -
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop := by
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
    have log_split: ∀ x: Set.Ioi 1, x.val / log ((1 + ε) * x.val) =
      x.val / (log (1 + ε) + log (x.val)) := by
      intro x
      have x_ge_one: 1 < x.val := Set.mem_Ioi.mp x.property
      rw [Real.log_mul (by linarith) (by linarith)]

    have log_factor: ∀ x: Set.Ioi 1, x.val / (log (1 + ε) + log (x.val)) =
      x.val / ((1 + (log (1 + ε)/(log x.val))) * (log x.val)) := by
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

    suffices Tendsto (fun x : Set.Ioi (1 : ℝ) ↦ (1 - d) * ((1 + ε) * x) /
      ((1 + log (1 + ε) / log x) * log x) - (1 + d) * x / log x) atTop atTop by
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
      equals ↑x * (log ↑x * ((1 + ε) * (1 - d)) -
          (1 + log (1 + ε) / log ↑x) * ((1 + d) * log ↑x)) /
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

@[blueprint
  (title := "prime-between")
  (statement := /-- For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for
  all sufficiently large $x$. -/)
  (proof := /-- Use Corollary \ref{pi_alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity
  as $x \to \infty$. -/)
  (latexEnv := "corollary")]
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

  have val_lt : (⌊b⌋₊.primeCounting : ℝ) < ⌊(1 + ε/2) * b⌋₊.primeCounting := by linarith
  norm_cast at val_lt

  have jump := prime_in_gap b ((1 + ε/2) * b) (by linarith) val_lt
  obtain ⟨p, hp, b_lt_p, p_le⟩ := jump
  have p_lt: p < (1 + ε) * b := by
    linarith
  use p


@[blueprint
  "mun"
  (statement := /-- We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \leq 1$. -/)
  (proof := /--
  From M\"obius inversion $1_{n=1} = \sum_{d|n} \mu(d)$ and summing we have
    $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
    for any $x \geq 1$. Since $\lfloor \frac{x}{d} \rfloor = \frac{x}{d} - \epsilon_d$ with
    $0 \leq \epsilon_d < 1$ and $\epsilon_x = 0$, we conclude that
    $$ 1 ≥ x \sum_{d \leq x} \frac{\mu(d)}{d} - (x - 1)$$
    and the claim follows.
  -/)
  (latexEnv := "proposition")]
theorem sum_mobius_div_self_le (N : ℕ) : |∑ n ∈ range N, μ n / (n : ℚ)| ≤ 1 := by
  cases N with
  | zero => simp only [range_zero, sum_empty, abs_zero, zero_le_one]
  | succ N =>
  /- simple cases -/
  obtain rfl | hN := N.eq_zero_or_pos
  · simp
  /- annoying case -/
  have h_sum : 1 = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
      μ d * Int.fract (N / d : ℚ) := calc
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
    _ = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
        μ d * Int.fract (N / d : ℚ) := by
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



lemma sum_mobius_mul_floor (x : ℝ) (hx : 1 ≤ x) :
  ∑ n ∈ Iic ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) * (⌊x/n⌋ : ℝ) = 1 := by
  norm_cast
  convert ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum μ ⌊x⌋₊ |>.symm using 1
  · rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp)]
    simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, div_zero, Int.floor_zero, mul_zero,
      zero_add, Int.natCast_ediv]
    refine sum_congr rfl fun n hn ↦ ?_
    congr
    norm_cast
    rw [← floor_div_natCast, Int.natCast_floor_eq_floor]
    positivity
  · simpa [moebius_mul_coe_zeta, one_apply]

noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x

noncomputable def M (x : ℝ) : ℝ := ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)

noncomputable def mu_log : ArithmeticFunction ℝ :=
    ⟨(fun n ↦ μ n * ArithmeticFunction.log n), (by simp)⟩

lemma mu_log_apply (n : ℕ) : mu_log n = μ n * ArithmeticFunction.log n := by
  rfl

lemma mu_log_mul_zeta : mu_log * ArithmeticFunction.zeta = -Λ := by
  ext n
  rw [coe_mul_zeta_apply]
  simp_rw [mu_log_apply]
  rw [sum_moebius_mul_log_eq]
  rfl

lemma mu_log_eq_mu_mul_neg_lambda : mu_log = μ * -Λ := by
  rw [← mu_log_mul_zeta, mul_comm, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

lemma ArithmeticFunction.neg_apply {R : Type*} [NegZeroClass R] {f : ArithmeticFunction R} {n : ℕ}
    : (-f) n = -f n := by
  rfl

lemma sum_mu_Lambda (x : ℝ) : ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) * log n = - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x/k) := by
  rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp), ← add_sum_Ioc_eq_sum_Icc (by simp)]
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, CharP.cast_eq_zero, log_zero, mul_zero,
    zero_add, div_zero, zero_mul]
  simp_rw [← log_apply, ← mu_log_apply, mu_log_eq_mu_mul_neg_lambda]
  rw [sum_Ioc_mul_eq_sum_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  simp_rw [ArithmeticFunction.neg_apply, sum_neg_distrib]
  ring_nf
  congr 2
  unfold Psi
  congr
  rw [← floor_div_natCast]
  rfl

lemma M_log_identity (x : ℝ) (hx : 1 ≤ x) : M x * log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (log (x/k) - Psi (x/k)) := by
  have h_log_identity : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k) = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    rw [Finset.sum_mul _ _ _]
    rw [← Finset.sum_sub_distrib] ; refine Finset.sum_congr rfl fun i hi => ?_ ; by_cases hi' : i = 0 <;> simp +decide [*, Real.log_div, ne_of_gt (zero_lt_one.trans_le hx)] ; ring
  generalize_proofs at *
  have h_log_identity' : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k = -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
    convert sum_mu_Lambda x using 1
  have h_psi_identity :
      (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k)) =
        -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    simpa [neg_neg] using (congrArg Neg.neg h_log_identity').symm
  unfold M
  symm
  calc
    (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Psi (x / k))) =
        (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
          simp [mul_sub, Finset.sum_sub_distrib]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
          simp [h_log_identity]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          (-∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) := by
          simp [h_psi_identity]
    _ = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x := by ring

noncomputable def R (x : ℝ) : ℝ := Psi x - x

lemma R_isLittleO : R =o[atTop] id := by
  have h_pnt : (fun x => Psi x - x) =o[atTop] (fun x => x) := by
    have h_psi : (fun x => Psi x) ~[atTop] (fun x => x) := by
      simpa [Psi] using WeakPNT''
    exact h_psi
  convert h_pnt using 1

lemma sum_mobius_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
  have h_abs : ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) / n| ≤ 1 := by
    intros x hx
    have h_sum : ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ) / n = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n := by
      rw [Finset.range_eq_Ico] ; rfl
    have := sum_mobius_div_self_le (⌊x⌋₊ + 1) ; simp_all +decide [Finset.sum_range_succ']
    norm_cast at *
  rw [Asymptotics.isBigO_iff]
  use 1; filter_upwards [Filter.eventually_ge_atTop 1] with x hx; simp_all +decide [div_eq_mul_inv, mul_assoc, mul_comm]
  simpa only [← Finset.mul_sum _ _ _, abs_mul] using mul_le_of_le_one_right (abs_nonneg x) (h_abs x hx)

lemma sum_log_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, log (x / k)) =O[atTop] id := by
  have h_sum_log : ∀ x : ℝ, 1 ≤ x → |∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k)| ≤ 2 * x := by
    have h_sum_log_le_x : ∀ x : ℝ, 1 ≤ x → ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) ≤ x := by
      intro x hx
      have h_sum_log : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (k : ℝ)) ≤ Real.log (x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊) := by
        rw [← Real.log_prod]
        · norm_num [Finset.prod_div_distrib]
          erw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
        · exact fun n hn => div_ne_zero (by positivity) (Nat.cast_ne_zero.mpr <| by linarith [Finset.mem_Icc.mp hn])
      have h_exp_bound : x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊ ≤ Real.exp x := by
        have h_term : x ^ ⌊x⌋₊ / (⌊x⌋₊! : ℝ) ≤ ∑' k : ℕ, x ^ k / (k ! : ℝ) := by
          exact Summable.le_tsum (show Summable _ from Real.summable_pow_div_factorial x) ⌊x⌋₊ (fun _ _ => by positivity)
        simpa [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using h_term
      exact h_sum_log.trans (Real.log_le_iff_le_exp (by positivity) |>.2 h_exp_bound)
    intros x hx
    have h_sum_eq : ∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) := by
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
    rw [abs_of_nonneg] <;> linarith [h_sum_log_le_x x hx, show 0 ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) from Finset.sum_nonneg fun _ _ => Real.log_nonneg <| by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| by linarith [Finset.mem_Icc.mp ‹_›]] ; linarith [Nat.floor_le <| show 0 ≤ x by linarith, show (↑‹ℕ› : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp ‹_› |>.2]]
  rw [Asymptotics.isBigO_iff]
  exact ⟨2, Filter.eventually_atTop.mpr ⟨1, fun x hx => le_trans (h_sum_log x hx) (by norm_num [abs_of_nonneg (by linarith : 0 ≤ x)])⟩⟩

lemma R_locally_bounded (K : ℝ) (hK : 0 ≤ K) : ∃ C, ∀ y ∈ Set.Icc 0 K, |R y| ≤ C := by
  have hR_bounded : BddAbove (Set.image (fun y => |R y|) (Set.Icc 0 K)) := by
    have hR_bounded : ∀ y ∈ Set.Icc 0 K, |R y| ≤ ∑ p ∈ Iic ⌊K⌋₊, log p + K := by
      intro y hy
      simp only [R, Psi, Chebyshev.psi_eq_sum_Icc]
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · refine le_trans (sub_le_self _ hy.1) ?_
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr <| Nat.floor_mono hy.2) fun ?_ ?_ ?_ => ?_) ?_
        · exact vonMangoldt_nonneg
        · refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i hi => ?_) hK
          exact vonMangoldt_le_log
      · refine le_trans ?_ (le_add_of_nonneg_left ?_)
        · exact le_trans (sub_le_self _ <| Finset.sum_nonneg fun _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg) hy.2
        · exact Finset.sum_nonneg fun _ _ => Real.log_natCast_nonneg _
    exact ⟨_, Set.forall_mem_image.2 hR_bounded⟩
  exact ⟨hR_bounded.choose, fun y hy => hR_bounded.choose_spec <| Set.mem_image_of_mem _ hy⟩

lemma sum_bounded_of_linear_bound {f : ℝ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (h : ∀ y, 1 ≤ y → |f y| ≤ ε * y + C) (x : ℝ) (hx : 1 ≤ x) :
  ∑ k ∈ Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * (log x + 1) + C * x := by
    have h_sum_bound : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) + C * ⌊x⌋₊ := by
      have h_sum_bound : ∀ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x / k + C := by
        exact fun k hk => by simpa only [mul_div_assoc] using h (x / k) (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| Finset.mem_Icc.mp hk |>.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), show (k : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp hk |>.2])
      convert Finset.sum_le_sum h_sum_bound using 1 ; norm_num [div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_comm]
    have h_harmonic : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ)) ≤ Real.log n + 1 := by
      intro n _hn
      have h := harmonic_le_one_add_log n
      simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        one_div, add_comm, add_left_comm, add_assoc] using h
    have h_harmonic_x :
        ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) ≤ Real.log x + 1 := by
      refine (h_harmonic _ <| Nat.floor_pos.mpr hx).trans ?_
      have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
        refine Real.log_le_log (Nat.cast_pos.mpr <| Nat.floor_pos.mpr hx) ?_
        exact Nat.floor_le (by positivity)
      simpa using add_le_add_right hlog 1
    have h_term1 : ε * x * (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ))) ≤ ε * x * (Real.log x + 1) := by
      refine mul_le_mul_of_nonneg_left h_harmonic_x ?_
      exact mul_nonneg hε (by positivity)
    have h_term2 : C * (⌊x⌋₊ : ℝ) ≤ C * x := by
      refine mul_le_mul_of_nonneg_left ?_ hC
      exact Nat.floor_le (by positivity)
    exact h_sum_bound.trans (add_le_add h_term1 h_term2)

lemma sum_abs_R_isLittleO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  have h_eps : ∀ ε > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ ε * x * Real.log x := by
    intro ε hε_pos
    obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y ≥ A, |R y| ≤ (ε / 2) * y := by
      have := R_isLittleO
      rw [Asymptotics.isLittleO_iff] at this
      norm_num at *
      exact Exists.elim (this (half_pos hε_pos)) fun A hA => ⟨Max.max A 1, by positivity, fun y hy => by simpa only [abs_of_nonneg (by linarith [le_max_right A 1] : 0 ≤ y)] using hA y (le_trans (le_max_left A 1) hy)⟩
    obtain ⟨C_A, hC_A⟩ : ∃ C_A : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ C_A := by
      exact ⟨_, fun y hy => R_locally_bounded A hA.1.le |> Classical.choose_spec |> fun h => h y hy⟩
    have h_sum_bound : ∀ x ≥ max A 2, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ (ε / 2) * x * (Real.log x + 1) + C_A * x := by
      intros x hx
      have h_sum_bound : ∀ y ≥ 1, |R y| ≤ (ε / 2) * y + C_A := by
        intros y hy
        by_cases hyA : y ≥ A
        · exact le_add_of_le_of_nonneg (hA.right y hyA) (by
          exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩))
        · exact le_add_of_nonneg_of_le (by
          positivity) (hC_A y ⟨by
          linarith, by
            linarith⟩)
      have := sum_bounded_of_linear_bound (show 0 ≤ ε / 2 by positivity) (show 0 ≤ C_A by exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩)) (fun y hy => h_sum_bound y hy) x (by linarith [le_max_right A 2]) ; aesop
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, (ε / 2) * (Real.log x + 1) + C_A ≤ ε * Real.log x := by
      exact ⟨Real.exp (2 * (C_A / ε + 1)), fun x hx => by nlinarith [Real.log_exp (2 * (C_A / ε + 1)), Real.log_le_log (by positivity) hx, mul_div_cancel₀ C_A hε_pos.ne']⟩
    exact ⟨Max.max x₀ (Max.max A 2), fun x hx => le_trans (h_sum_bound x (le_trans (le_max_right _ _) hx)) (by nlinarith [hx₀ x (le_trans (le_max_left _ _) hx), le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2, Real.log_nonneg (show x ≥ 1 by linarith [le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2])])⟩
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h_sum_eq : ∀ x : ℝ, x ≥ 1 → (∑ k ∈ Finset.Iic ⌊x⌋₊, |R (x / k)|) = (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) := by
      intro x hx
      have h0 : (0 : ℕ) ∈ Finset.Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
      have hI : (Finset.Iic ⌊x⌋₊).erase 0 = Finset.Icc 1 ⌊x⌋₊ := by
        ext n
        simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
      rw [← Finset.sum_erase_add (Finset.Iic ⌊x⌋₊) (fun k => |R (x / k)|) h0]
      simp [hI, R, Psi, Chebyshev.psi_eq_sum_Icc]
    rw [Metric.tendsto_nhds]
    simp +zetaDelta only [gt_iff_lt, ge_iff_le, dist_zero_right, norm_div, norm_eq_abs, norm_mul,
    eventually_atTop] at *
    intro ε hε; obtain ⟨x₀, hx₀⟩ := h_eps (ε / 2) (half_pos hε) ; use Max.max x₀ 2; intro x hx; rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), abs_of_nonneg (by linarith [le_max_right x₀ 2]), abs_of_nonneg (Real.log_nonneg (by linarith [le_max_right x₀ 2]))] ; rw [div_lt_iff₀] <;> nlinarith [hx₀ x (le_trans (le_max_left x₀ 2) hx), Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x), mul_pos (by linarith [le_max_right x₀ 2] : 0 < x) (Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x)), h_sum_eq x (by linarith [le_max_right x₀ 2])]
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' (by nlinarith [Real.log_pos hx])

lemma R_linear_bound (ε : ℝ) (hε : 0 < ε) : ∃ C, 0 ≤ C ∧ ∀ y, 1 ≤ y → |R y| ≤ ε * y + C := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, A ≤ y → |R y| ≤ ε * y := by
    have := R_isLittleO.def hε
    rw [Filter.eventually_atTop] at this; rcases this with ⟨A, hA⟩ ; exact ⟨Max.max A 1, by positivity, fun y hy => by simpa [abs_of_nonneg (show 0 ≤ y by linarith [le_max_right A 1])] using hA y (le_trans (le_max_left A 1) hy)⟩
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ CA := by
    exact R_locally_bounded A hA.1.le |> fun ⟨CA, hCA⟩ => ⟨CA, fun y hy => hCA y hy⟩
  exact ⟨Max.max CA 0, by positivity, fun y hy => if hy' : y ≤ A then le_trans (hCA y ⟨by linarith, by linarith⟩) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith]) else le_trans (hA.2 y (by linarith)) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith])⟩

lemma sum_abs_R_isLittleO' : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  apply sum_abs_R_isLittleO

lemma M_isLittleO : M =o[atTop] id := by
  have h_identity : ∀ x ≥ 1, M x * Real.log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Psi (x / k)) := by
    exact fun x a => M_log_identity x a
  have h_term1 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) =O[atTop] id := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k) := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * Real.log (x / k)| ≤ Real.log (x / k) := by
        intros k hk
        have h_abs : |(μ k : ℝ)| ≤ 1 := by
          norm_num [ArithmeticFunction.moebius]
          split_ifs <;> norm_num
        by_cases hk0 : k = 0
        · rw [hk0] ; norm_num [ArithmeticFunction.map_zero, Nat.cast_zero, Real.log_zero, div_zero, abs_zero]
        · have hx_pos : 0 < x := by positivity
          have hk_pos : 0 < (k : ℝ) := by positivity
          rw [Real.log_div hx_pos.ne' hk_pos.ne']
          simp only [abs_mul, ge_iff_le]
          simp_all only [ge_iff_le, mem_Iic]
          exact le_trans (mul_le_of_le_one_left (abs_nonneg _) h_abs) (by rw [abs_of_nonneg] ; exact sub_nonneg_of_le <| Real.log_le_log hk_pos (Nat.cast_le.mpr hk |>.trans (Nat.floor_le hx_pos.le)))
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_log : (fun x => ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k)) =O[atTop] id := by
      convert sum_log_div_isBigO using 1
    rw [Asymptotics.isBigO_iff] at *
    exact ⟨h_sum_log.choose, by filter_upwards [h_sum_log.choose_spec, Filter.eventually_ge_atTop 1] with x hx₁ hx₂ using le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)⟩
  have h_term2 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
    convert sum_mobius_div_isBigO using 1
  have h_term3 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) =o[atTop] (fun x => x * Real.log x) := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)| := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * R (x / k)| ≤ |R (x / k)| := by
        norm_num [abs_mul]
        intro k hk; exact mul_le_of_le_one_left (abs_nonneg _) (mod_cast by exact abs_moebius_le_one)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_abs_R : (fun x => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * Real.log x) := by
      exact sum_abs_R_isLittleO
    rw [Asymptotics.isLittleO_iff] at *
    intro c hc; filter_upwards [h_sum_abs_R hc, Filter.eventually_ge_atTop 1] with x hx₁ hx₂; exact le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)
  have h_combined : (fun x => M x * Real.log x) =o[atTop] (fun x => x * Real.log x) := by
    have h_combined : (fun x => M x * Real.log x) = (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) := by
      ext x; by_cases hx : 1 ≤ x <;> simp_all +decide only [ge_iff_le, mul_sub, sum_sub_distrib, not_le, Pi.sub_apply]
      · simp +decide [sub_sub, mul_sub, Finset.sum_sub_distrib, Psi, R]
      · unfold M R; norm_num [Nat.floor_eq_zero.mpr hx]
        norm_num [Finset.Iic_eq_Icc]
    rw [h_combined]
    refine Asymptotics.IsLittleO.sub ?_ h_term3
    refine Asymptotics.IsLittleO.sub ?_ ?_
    · refine h_term1.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> norm_num at hx⟩
    · refine h_term2.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> linarith⟩
  rw [Asymptotics.isLittleO_iff_tendsto'] at *
  · refine h_combined.congr' (by filter_upwards [Filter.eventually_gt_atTop 1] with x hx using by rw [mul_div_mul_right _ _ (ne_of_gt <| Real.log_pos hx)] ; rfl)
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' <| ne_of_gt <| mul_pos (by positivity) <| Real.log_pos hx
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using by nlinarith [Real.log_pos hx]
  · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'

lemma M_isLittleO' : M =o[atTop] id := by
  exact M_isLittleO


@[blueprint
  "mu-pnt"
  (title := "M\\\"obius form of prime number theorem")
  (statement := /-- We have $\sum_{n \leq x} \mu(n) = o(x)$. -/)
  (proof := /--
  From the Dirichlet convolution identity
    $$ \mu(n) \log n = - \sum_{d|n} \mu(d) \Lambda(n/d)$$
  and summing we obtain
  $$ \sum_{n \leq x} \mu(n) \log n = - \sum_{d \leq x} \mu(d) \sum_{m \leq x/d} \Lambda(m).$$
  For any $\eps>0$, we have from the prime number theorem that
  $$ \sum_{m \leq x/d} \Lambda(m) = x/d + O(\eps x/d) + O_\eps(1)$$
  (divide into cases depending on whether $x/d$ is large or small compared to $\eps$).
  We conclude that
  $$ \sum_{n \leq x} \mu(n) \log n
    = - x \sum_{d \leq x} \frac{\mu(d)}{d} + O(\eps x \log x) + O_\eps(x).$$
  Applying \eqref{mun} we conclude that
  $$ \sum_{n \leq x} \mu(n) \log n = O(\eps x \log x) + O_\eps(x).$$
  and hence
  $$ \sum_{n \leq x} \mu(n) \log x
    = O(\eps x \log x) + O_\eps(x) + O( \sum_{n \leq x} (\log x - \log n) ).$$
  From Stirling's formula one has
  $$  \sum_{n \leq x} (\log x - \log n) = O(x)$$
  thus
  $$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x)$$
  and thus
  $$ \sum_{n \leq x} \mu(n) = O(\eps x) + O_\eps(\frac{x}{\log x}).$$
  Sending $\eps \to 0$ we obtain the claim.
  -/)
  (proofUses := ["WeakPNT", "mun"])
  (latexEnv := "proposition")]
theorem mu_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, μ n) =o[atTop] fun x ↦ x := by
  have h_moebius_sum : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
    have h_bound : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
      have h_sum : (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
        have h_moebius_sum : (fun x : ℝ => ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
          convert M_isLittleO using 1
        simpa only [Finset.range_eq_Ico] using h_moebius_sum
      have h_mu_floor : (fun x : ℝ => (μ ⌊x⌋₊ : ℝ)) =o[atTop] (fun x : ℝ => x) := by
        rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
        · refine squeeze_zero_norm (a := fun x : ℝ => 1 / |x|) ?_ ?_
          · intro x; norm_num [abs_div]
            exact mul_le_of_le_one_left (by positivity) (mod_cast by exact abs_moebius_le_one)
          · exact tendsto_const_nhds.div_atTop (tendsto_norm_atTop_atTop)
        · exact ⟨1, by intros; linarith⟩
      simpa [Finset.sum_range_succ] using h_sum.sub h_mu_floor
    convert h_bound using 1
  rw [Asymptotics.isLittleO_iff] at *
  simp_all +decide [Norm.norm]


lemma lambda_eq_sum_sq_dvd_mu (n : ℕ) (hn : n ≠ 0) :
    ((-1 : ℝ) ^ (Ω n)) = ∑ d ∈ (Icc 1 n).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
      set a : ℕ → ℕ := fun p => Nat.factorization n p with ha
      have hn_factor : n = ∏ p ∈ Nat.primeFactors n, p ^ a p := by
        exact Eq.symm ( Nat.factorization_prod_pow_eq_self hn );
      have h_sum_factor : (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (μ (n / d^2) : ℝ)) = (∏ p ∈ Nat.primeFactors n, (∑ d ∈ Finset.range (a p / 2 + 1), (μ (p^(a p - 2 * d)) : ℝ))) := by
        have h_mult : ∀ {m n : ℕ}, Nat.gcd m n = 1 → (∑ d ∈ Finset.filter (fun d => d^2 ∣ m * n) (Finset.Icc 1 (m * n)), (μ (m * n / d^2) : ℝ)) = (∑ d ∈ Finset.filter (fun d => d^2 ∣ m) (Finset.Icc 1 m), (μ (m / d^2) : ℝ)) * (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (μ (n / d^2) : ℝ)) := by
          intros m n h_coprime
          have h_filter : Finset.filter (fun d => d^2 ∣ m * n) (Finset.Icc 1 (m * n)) = Finset.image (fun (d : ℕ × ℕ) => d.1 * d.2) (Finset.filter (fun d => d^2 ∣ m) (Finset.Icc 1 m) ×ˢ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n)) := by
            ext d
            simp only [mem_filter, mem_Icc, mem_image, mem_product, Prod.exists]
            constructor
            · intro h
              obtain ⟨d1, d2, hd1, hd2, hd⟩ : ∃ d1 d2 : ℕ, d1^2 ∣ m ∧ d2^2 ∣ n ∧ d = d1 * d2 := by
                have h_factor : d^2 ∣ m * n → ∃ d1 d2 : ℕ, d1^2 ∣ m ∧ d2^2 ∣ n ∧ d = d1 * d2 := by
                  intro h_div
                  obtain ⟨d1, d2, hd1, hd2, hd⟩ : ∃ d1 d2 : ℕ, d1 ∣ m ∧ d2 ∣ n ∧ d = d1 * d2 := by
                    exact Exists.imp ( by tauto ) ( Nat.dvd_mul.mp ( dvd_of_mul_left_dvd h_div ) );
                  refine ⟨ d1, d2, ?_, ?_, hd ⟩
                  · apply Nat.Coprime.dvd_of_dvd_mul_right
                    · exact Nat.Coprime.pow_left 2 (Nat.Coprime.coprime_dvd_left hd1 h_coprime)
                    · exact dvd_trans (pow_dvd_pow_of_dvd (hd.symm ▸ dvd_mul_right _ _) 2) h_div
                  · subst hd
                    apply Nat.Coprime.dvd_of_dvd_mul_left
                    · exact Nat.Coprime.pow_left _ (Nat.Coprime.symm <| Nat.Coprime.coprime_dvd_right hd2 h_coprime)
                    · exact dvd_trans ⟨d1 ^ 2, by ring⟩ h_div
                exact h_factor h.2;
              refine ⟨ d1, d2, ?_, ?_ ⟩ <;> norm_num [ hd ]
              exact ⟨ ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by rintro rfl; linarith ) ) ( dvd_of_mul_left_dvd hd1 ) ⟩, hd1 ⟩, ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by rintro rfl; linarith ) ) ( dvd_of_mul_left_dvd hd2 ) ⟩, hd2 ⟩;
            · intro h
              rcases h with ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, ⟨ ⟨ hb₁, hb₂ ⟩, hb₃ ⟩ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith, by nlinarith ⟩, by convert Nat.mul_dvd_mul ha₃ hb₃ using 1 ; ring ⟩ ;
          rw [ h_filter, Finset.sum_image ];
          · rw [ Finset.sum_product, Finset.sum_mul ];
            simp +decide only [Finset.mul_sum _ _ _];
            refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
            rw [show m * n / (x * y) ^ 2 = (m / x ^ 2) * (n / y ^ 2) by
              have hx' : x ^ 2 ∣ m := by
                simpa only [sq] using (Finset.mem_filter.mp hx).2
              have hy' : y ^ 2 ∣ n := by
                simpa only [sq] using (Finset.mem_filter.mp hy).2
              simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
                (Nat.div_mul_div_comm (a := m) (b := x ^ 2) (c := n) (d := y ^ 2) hx' hy').symm]
            norm_cast
            apply ArithmeticFunction.IsMultiplicative.map_mul_of_coprime;
            · exact ArithmeticFunction.isMultiplicative_moebius;
            · exact Nat.Coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd <| Finset.mem_filter.mp hx |>.2 ) <| Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd <| Finset.mem_filter.mp hy |>.2 ) h_coprime;
          · intros x hx y hy; simp +contextual only [ne_eq, coe_product, coe_filter, mem_Icc, Set.mem_prod, Set.mem_setOf_eq] at *;
            intro hxy
            have h_eq1 : x.1 = y.1 := by
              exact Nat.dvd_antisymm ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( x.1 ) ( y.2 ) from Nat.Coprime.coprime_dvd_left ( dvd_of_mul_left_dvd hx.1.2 ) <| Nat.Coprime.coprime_dvd_right ( dvd_of_mul_left_dvd hy.2.2 ) h_coprime ) <| hxy.symm ▸ dvd_mul_right _ _ ) ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( y.1 ) ( x.2 ) from Nat.Coprime.coprime_dvd_left ( dvd_of_mul_left_dvd hy.1.2 ) <| Nat.Coprime.coprime_dvd_right ( dvd_of_mul_left_dvd hx.2.2 ) h_coprime ) <| hxy.symm ▸ dvd_mul_right _ _ )
            have h_eq2 : x.2 = y.2 := by
              nlinarith
            exact Prod.ext h_eq1 h_eq2;
        have h_prod : (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (μ (n / d^2) : ℝ)) = (∏ p ∈ Nat.primeFactors n, (∑ d ∈ Finset.filter (fun d => d^2 ∣ p^(a p)) (Finset.Icc 1 (p^(a p))), (μ (p^(a p) / d^2) : ℝ))) := by
          have h_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → (∑ d ∈ Finset.filter (fun d => d^2 ∣ ∏ p ∈ S, p^(a p)) (Finset.Icc 1 (∏ p ∈ S, p^(a p))), (μ ((∏ p ∈ S, p^(a p)) / d^2) : ℝ)) = (∏ p ∈ S, (∑ d ∈ Finset.filter (fun d => d^2 ∣ p^(a p)) (Finset.Icc 1 (p^(a p))), (μ (p^(a p) / d^2) : ℝ))) := by
            intro S hS; induction S using Finset.induction <;> norm_num at *;
            · norm_num [ Finset.sum_filter ];
            · rw [ Finset.prod_insert ‹_›, h_mult ];
              · rw [ Finset.prod_insert ‹_›, ‹ ( ∀ p ∈ _, Nat.Prime p ) → ∑ d ∈ Finset.Icc 1 ( ∏ p ∈ _, p ^ a p ) with d ^ 2 ∣ ∏ p ∈ _, p ^ a p, ( μ ( ( ∏ p ∈ _, p ^ a p ) / d ^ 2 ) : ℝ ) = ∏ p ∈ _, ∑ d ∈ Finset.Icc 1 ( p ^ a p ) with d ^ 2 ∣ p ^ a p, ( μ ( p ^ a p / d ^ 2 ) : ℝ ) › hS.2 ];
              · exact Nat.Coprime.prod_right fun p hp => Nat.coprime_pow_primes _ _ hS.1 ( hS.2 p hp ) <| by rintro rfl; exact ‹¬_› hp;
          convert h_prod fun p hp => Nat.prime_of_mem_primeFactors hp;
        have h_divisors : ∀ p ∈ Nat.primeFactors n, Finset.filter (fun d => d^2 ∣ p^(a p)) (Finset.Icc 1 (p^(a p))) = Finset.image (fun k => p^k) (Finset.Icc 0 (a p / 2)) := by
          intro p hp
          ext d
          simp only [mem_filter, mem_Icc, mem_image, _root_.zero_le, true_and]
          constructor;
          · intro hd;
            have : d ∣ p ^ a p := dvd_of_mul_left_dvd hd.2; ( rw [ Nat.dvd_prime_pow ( Nat.prime_of_mem_primeFactors hp ) ] at this; obtain ⟨ k, hk ⟩ := this; use k; simp +decide only [ hk, and_true ] at hd ⊢; );
            rw [ Nat.le_div_iff_mul_le zero_lt_two ] ; rw [ ← pow_mul ] at hd ; exact Nat.le_of_not_lt fun h => absurd ( Nat.le_of_dvd ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ) hd.2 ) ( by exact not_le_of_gt ( pow_lt_pow_right₀ ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) ( by linarith ) ) ) ;
          · rintro ⟨ k, hk₁, rfl ⟩ ; exact ⟨ ⟨ Nat.one_le_pow _ _ ( Nat.pos_of_mem_primeFactors hp ), Nat.pow_le_pow_right ( Nat.pos_of_mem_primeFactors hp ) ( by omega ) ⟩, by rw [ ← pow_mul ] ; exact pow_dvd_pow _ ( by omega ) ⟩ ;
        rw [ h_prod, Finset.prod_congr rfl ];
        intro p hp; rw [ show ( Finset.filter ( fun d => d ^ 2 ∣ p ^ a p ) ( Finset.Icc 1 ( p ^ a p ) ) ) = Finset.image ( fun k => p ^ k ) ( Finset.Icc 0 ( a p / 2 ) ) from h_divisors p hp ] ; rw [ Finset.sum_image ] <;> norm_num [ pow_mul', Nat.div_eq_of_lt ] ;
        · rw [Finset.range_eq_Ico, ← Order.succ_eq_add_one, Finset.Ico_succ_right_eq_Icc]
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [← pow_mul', Nat.mul_comm]
          have hx_pos : 0 < p ^ (x * 2) := pow_pos (Nat.pos_of_mem_primeFactors hp) _
          have hx_eq : p ^ a p = p ^ (a p - x * 2) * p ^ (x * 2) := by
            rw [← pow_add, Nat.sub_add_cancel (by linarith [Finset.mem_Icc.mp hx, Nat.div_mul_le_self (a p) 2])]
          rw [Nat.div_eq_of_eq_mul_left hx_pos hx_eq]
        · exact fun x hx y hy hxy => Nat.pow_right_injective ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) hxy;
      have h_inner_sum : ∀ p ∈ Nat.primeFactors n, (∑ d ∈ Finset.range (a p / 2 + 1), (μ (p^(a p - 2 * d)) : ℝ)) = (-1 : ℝ) ^ (a p) := by
        intro p hp
        have h_inner_sum_cases : ∀ d ∈ Finset.range (a p / 2 + 1), (μ (p^(a p - 2 * d)) : ℝ) = if a p - 2 * d = 0 then 1 else if a p - 2 * d = 1 then -1 else 0 := by
          simp +zetaDelta only [ne_eq, mem_primeFactors, mem_range] at *
          intro d hd
          rcases k : (n.factorization p - 2 * d) with (_ | _ | k)
          · simp +decide only [pow_zero, isUnit_iff_eq_one, IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg,
              cardFactors_one, Int.cast_one, ↓reduceIte]
          · simp +decide only [zero_add, pow_one, ↓reduceIte]
            norm_num [hp.1, ArithmeticFunction.moebius]
            exact hp.1.squarefree
          · simp +decide only [Nat.add_eq_zero_iff, and_false, and_self, ↓reduceIte, Nat.add_eq_right, Int.cast_eq_zero]
            exact
              ArithmeticFunction.moebius_eq_zero_of_not_squarefree
                (by rw [Nat.squarefree_pow_iff] <;> norm_num [hp.1.ne_one, hp.1.ne_zero])
        rw [ Finset.sum_congr rfl h_inner_sum_cases ] ; norm_num [ Finset.sum_ite ] ; rcases Nat.even_or_odd' ( a p ) with ⟨ k, hk | hk ⟩ <;> norm_num [ hk, pow_add, pow_mul ]
        · ring_nf
          norm_num [ show ∀ x : ℕ, k * 2 - x * 2 = 0 ↔ x ≥ k by intro x; exact ⟨ fun hx => by contrapose! hx; exact Nat.ne_of_gt <| Nat.sub_pos_of_lt <| by linarith, fun hx => Nat.sub_eq_zero_of_le <| by linarith ⟩ ];
          rw [ show Finset.filter ( fun x => k ≤ x ) ( Finset.range ( 1 + k ) ) = { k } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith, by linarith ⟩, fun x hx => by linarith [ Finset.mem_filter.mp hx, Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ] ⟩ ] ; norm_num;
          intros; omega;
        · ring_nf
          norm_num [ Nat.add_div ];
          rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
          · rw [ Finset.card_eq_one ] ; use k ; ext x ; norm_num ; omega;
          · intros; omega;
      rw [ h_sum_factor, Finset.prod_congr rfl h_inner_sum ];
      rw [ Finset.prod_pow_eq_pow_sum ];
      rw [ ArithmeticFunction.cardFactors_apply ];
      rw [ ← Multiset.coe_card, ← Multiset.toFinset_sum_count_eq ];
      norm_num +zetaDelta

lemma sum_lambda_eq_sum_mu_div_sq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((-1 : ℝ) ^ (Ω n)) =
    ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ) := by
      have h_sum_rewrite : ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Ω n) = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
        have h_sum_rewrite : ∀ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Ω n) = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
          intro n hn
          have h_lambda_eq : ((-1 : ℝ) ^ (Ω n)) = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
            convert lambda_eq_sum_sq_dvd_mu n ( by linarith [ Finset.mem_Icc.mp hn ] ) using 1;
          rw [ h_lambda_eq, Finset.sum_subset ];
          · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2, Finset.mem_Icc.mp hn |>.2 ] ⟩, Finset.mem_filter.mp hx |>.2 ⟩;
          · simp +zetaDelta only [mem_Icc, mem_filter, not_and, and_imp, Int.cast_eq_zero] at *
            exact fun x hx₁ hx₂ hx₃ hx₄ => False.elim <| hx₄ hx₁ ( by nlinarith [ Nat.le_of_dvd ( by linarith ) hx₃ ] ) hx₃;
        exact Finset.sum_congr rfl h_sum_rewrite;
      rw [ h_sum_rewrite, Finset.sum_sigma' ];
      have h_reindex : ∑ x ∈ (Finset.Icc 1 N).sigma fun (n : ℕ) => {d ∈ Finset.Icc 1 N | d ^ 2 ∣ n}, (μ (x.fst / x.snd ^ 2) : ℝ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d ^ 2), (μ k : ℝ) := by
        have : Finset.filter (fun x => x.snd ^ 2 ∣ x.fst) (Finset.Icc 1 N ×ˢ Finset.Icc 1 N) = Finset.biUnion (Finset.Icc 1 (Nat.sqrt N)) (fun d => Finset.image (fun k => (d ^ 2 * k, d)) (Finset.Icc 1 (N / d ^ 2))) := by
          ext ⟨n, d⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
          constructor
          · intro ⟨⟨⟨hn1, hn2⟩, hd1, hd2⟩, hdiv⟩
            exact ⟨d, ⟨hd1, by rw [Nat.le_sqrt]; nlinarith [Nat.le_of_dvd (by linarith) hdiv]⟩, n / d ^ 2, ⟨Nat.div_pos (Nat.le_of_dvd (by linarith) hdiv) (by nlinarith), Nat.div_le_div_right hn2⟩, Nat.mul_div_cancel' hdiv, rfl⟩
          · rintro ⟨a, ⟨ha₁, ha₂⟩, b, ⟨hb₁, hb₂⟩, hn, hd⟩
            rw [← hn, ← hd]
            exact ⟨⟨⟨by nlinarith, by nlinarith [Nat.div_mul_le_self N (a ^ 2)]⟩, ha₁, by nlinarith [Nat.sqrt_le N]⟩, dvd_mul_right _ _⟩
        rw [ Finset.sum_sigma' ];
        apply Finset.sum_bij (fun x _ => ⟨x.snd, x.fst / x.snd ^ 2⟩);
        · simp_all +decide only [Finset.ext_iff, mem_filter, mem_product, mem_Icc, mem_biUnion, mem_image, Prod.forall,
            Prod.mk.injEq, ↓existsAndEq, and_true, exists_and_left, mem_sigma, true_and, and_imp]
          exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ by nlinarith [ Nat.le_of_dvd ( by linarith ) hx₅, Nat.lt_succ_sqrt N ], Nat.div_pos ( Nat.le_of_dvd ( by linarith ) hx₅ ) ( by positivity ), Nat.div_le_div_right hx₂ ⟩;
        · simp +contextual [ Finset.mem_sigma, Finset.mem_filter ];
          aesop;
        · simp +zetaDelta only [mem_sigma, mem_Icc, mem_filter, exists_prop, Sigma.exists, and_imp] at *
          exact fun b hb₁ hb₂ hb₃ hb₄ => ⟨ b.fst ^ 2 * b.snd, b.fst, ⟨ ⟨ by nlinarith, by nlinarith [ Nat.div_mul_le_self N ( b.fst ^ 2 ) ] ⟩, ⟨ by nlinarith, by nlinarith [ Nat.div_mul_le_self N ( b.fst ^ 2 ) ] ⟩, by norm_num ⟩, by simp +decide [ Nat.mul_div_cancel_left _ ( by nlinarith : 0 < b.fst ^ 2 ) ] ⟩;
        · aesop;
      convert h_reindex using 1


lemma sum_mu_div_sq_isLittleO : (fun N : ℕ ↦ ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ)) =o[atTop] (fun N ↦ (N : ℝ)) := by
  have h_sum_rewrite : ∀ N : ℕ, (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ))) = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (M (N / d^2) : ℝ)) := by
    intro N
    simp only [M]
    refine Finset.sum_congr rfl ?_
    intro x hx
    erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
    rw [ show ⌊ ( N : ℝ ) / x ^ 2⌋₊ = N / x ^ 2 from Nat.floor_eq_iff ( by positivity ) |>.2 ⟨ by rw [ le_div_iff₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hx ] ) ] ; norm_cast; linarith [ Nat.div_mul_le_self N ( x ^ 2 ) ], by rw [ div_lt_iff₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hx ] ) ] ; norm_cast; linarith [ Nat.div_add_mod N ( x ^ 2 ), Nat.mod_lt N ( show x ^ 2 > 0 by nlinarith [ Finset.mem_Icc.mp hx ] ) ] ⟩ ] ; erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ] ;
  have h_bound : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d ∈ Finset.Icc 1 (Nat.sqrt N), |M (N / d^2)| ≤ ε * (N / d^2) + N₀ := by
    have h_bound : ∀ ε > 0, ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |M x| ≤ ε * x + C := by
      have h_bound : ∀ ε > 0, ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |M x| ≤ ε * x + C := by
        intro ε hε
        have := M_isLittleO'
        rw [ Asymptotics.isLittleO_iff ] at this;
        norm_num +zetaDelta at *;
        obtain ⟨ a, ha ⟩ := this hε;
        obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ Set.Icc 1 a, |M x| ≤ C := by
          have h_bounded : BddAbove (Set.image (fun x => |M x|) (Set.Icc 1 a)) := by
            have h_bounded : BddAbove (Set.image (fun x => |∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)|) (Set.Icc 1 a)) := by
              have h_finite : Set.Finite (Set.image (fun x => ⌊x⌋₊) (Set.Icc 1 a)) := by
                exact Set.finite_iff_bddAbove.mpr ⟨ ⌊a⌋₊, Set.forall_mem_image.mpr fun x hx => Nat.floor_mono hx.2 ⟩
              have h_bounded : BddAbove (Set.image (fun n : ℕ => |∑ k ∈ Finset.Iic n, (μ k : ℝ)|) (Set.image (fun x => ⌊x⌋₊) (Set.Icc 1 a))) := by
                exact Set.Finite.bddAbove <| h_finite.image _;
              exact ⟨ h_bounded.choose, Set.forall_mem_image.2 fun x hx => h_bounded.choose_spec <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx ⟩;
            convert h_bounded using 1;
          exact ⟨ h_bounded.choose, fun x hx => h_bounded.choose_spec ⟨ x, hx, rfl ⟩ ⟩;
        exact ⟨ Max.max C 0, fun x hx => if hx' : x ≤ a then le_trans ( hC x ⟨ hx, hx' ⟩ ) ( le_max_left _ _ ) |> le_trans <| le_add_of_nonneg_left <| by positivity else le_trans ( ha x <| le_of_not_ge hx' ) <| by rw [ abs_of_nonneg <| by linarith ] ; exact le_add_of_nonneg_right <| by positivity ⟩;
      assumption;
    intro ε hε
    obtain ⟨C, hC⟩ := h_bound ε hε
    refine ⟨⌈C⌉₊ + 1, ?_⟩
    intro N hN d hd
    specialize hC (N / d ^ 2)
    rcases eq_or_ne d 0 with rfl | hd0
    · simp_all +decide only [gt_iff_lt, ge_iff_le, mem_Icc, _root_.zero_le, and_true]
    · simp_all +decide only [gt_iff_lt, ge_iff_le, mem_Icc, ne_eq, cast_add, cast_one]
      exact
        le_trans
            (hC <|
              by
                rw [le_div_iff₀ <| by positivity]
                nlinarith [show (d : ℝ) ^ 2 ≤ N by norm_cast; nlinarith [Nat.sqrt_le N]])
          (by linarith [Nat.le_ceil C])
  have h_sum_bound : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |∑ d ∈ Finset.Icc 1 (Nat.sqrt N), M (N / d^2)| ≤ ε * N * (∑' k : ℕ, (1 : ℝ) / (k^2)) + N₀ * Nat.sqrt N := by
    intros ε hε_pos
    obtain ⟨N₀, hN₀⟩ := h_bound ε hε_pos
    use N₀
    intro N hN
    have h_sum_bound : |∑ d ∈ Finset.Icc 1 (Nat.sqrt N), M (N / d^2)| ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ε * (N / d^2) + N₀) := by
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun x hx => hN₀ N hN x hx );
    refine le_trans h_sum_bound ?_;
    norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
    rw [ ← Finset.mul_sum _ _ _, ← Finset.mul_sum _ _ _ ];
    exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( Summable.sum_le_tsum ( Finset.Icc 1 N.sqrt ) ( fun _ _ => by positivity ) ( by simp ) ) ( Nat.cast_nonneg _ ) ) hε_pos.le;
  rw [ Asymptotics.isLittleO_iff ];
  intro c hc
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ε * (∑' k : ℕ, (1 : ℝ) / (k^2)) < c / 2 := by
    exact ⟨ ( c / 2 ) / ( ∑' k : ℕ, 1 / ( k : ℝ ) ^ 2 + 1 ), div_pos ( half_pos hc ) ( add_pos_of_nonneg_of_pos ( tsum_nonneg fun _ => by positivity ) zero_lt_one ), by rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ show 0 ≤ ∑' k : ℕ, 1 / ( k : ℝ ) ^ 2 from tsum_nonneg fun _ => by positivity ] ⟩;
  obtain ⟨ N₀, hN₀ ⟩ := h_sum_bound ε hε_pos;
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N ≥ N₁, N₀ * Nat.sqrt N ≤ (c / 2) * N := by
    have h_sqrt_growth : ∃ N₁ : ℕ, ∀ N ≥ N₁, (N₀ : ℝ) * Real.sqrt N ≤ (c / 2) * N := by
      have h_sqrt_bound : Filter.Tendsto (fun N : ℕ => (N₀ : ℝ) * Real.sqrt N / N) Filter.atTop (nhds 0) := by
        simpa [ mul_div_assoc, Real.sqrt_div_self ] using tendsto_const_nhds.mul ( tendsto_inv_atTop_nhds_zero_nat.sqrt )
      exact Filter.eventually_atTop.mp ( h_sqrt_bound.eventually ( gt_mem_nhds <| show 0 < c / 2 by positivity ) ) |> fun ⟨ N₁, hN₁ ⟩ ↦ ⟨ N₁ + 1, fun N hN ↦ by have := hN₁ N ( by linarith ) ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ show ( N : ℝ ) ≥ N₁ + 1 by exact_mod_cast hN ] ⟩;
    exact ⟨ h_sqrt_growth.choose, fun N hN => le_trans ( mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _ ) <| Nat.cast_nonneg _ ) <| h_sqrt_growth.choose_spec N hN ⟩;
  filter_upwards [ Filter.eventually_ge_atTop N₀, Filter.eventually_ge_atTop N₁ ] with N hN₀' hN₁' using by rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ; rw [ h_sum_rewrite ] ; exact le_trans ( hN₀ _ hN₀' ) ( by nlinarith [ hN₁ _ hN₁', show ( N : ℝ ) ≥ 0 by positivity ] ) ;


@[blueprint
  "lambda-pnt"
  (statement := /-- We have $\sum_{n \leq x} \lambda(n) = o(x)$. -/)
  (proof := /--
  From the identity
    $$ \lambda(n) = \sum_{d^2|n} \mu(n/d^2)$$
  and summing, we have
  $$ \sum_{n \leq x} \lambda(n) = \sum_{d \leq \sqrt{x}} \sum_{n \leq x/d^2} \mu(n).$$
  For any $\eps>0$, we have from Proposition \ref{mu-pnt} that
  $$ \sum_{n \leq x/d^2} \mu(n) = O(\eps x/d^2) + O_\eps(1)$$
  and hence on summing in $d$
  $$ \sum_{n \leq x} \lambda(n) = O(\eps x) + O_\eps(x^{1/2}).$$
  Sending $\eps \to 0$ we obtain the claim.
  -/)
  (proofUses := ["mu-pnt"])
  (latexEnv := "proposition")]
theorem lambda_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (-1)^(Ω n)) =o[atTop] fun x ↦ x := by
  have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
    have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
      have h_lambda_pnt : (fun N : ℕ => ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
        exact sum_mu_div_sq_isLittleO
      convert h_lambda_pnt using 2;
      convert sum_lambda_eq_sum_mu_div_sq _;
      exact Eq.symm cardFactors_eq_sum_factorization
    have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
      rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
      · convert h_lambda_pnt.add ( show Filter.Tendsto ( fun x : ℕ => ( 1 : ℝ ) / x ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) using 2 <;> norm_num [ Finset.sum_Ico_eq_sum_range ];
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ; ring_nf;
      · exact ⟨ 1, by aesop ⟩;
      · exact ⟨ 1, by aesop ⟩;
    simp_all +decide only [Finset.sum_range_succ]
    have := h_lambda_pnt.sub ( show ( fun N : ℕ => ( -1 : ℝ ) ^ N.factorization.sum fun p k => k ) =o[Filter.atTop] fun N : ℕ => ( N : ℝ ) from ?_ );
    · aesop;
    · rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
      · exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa using tendsto_inv_atTop_nhds_zero_nat );
      · exact ⟨ 1, fun n hn => by positivity ⟩;
  have h_floor : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun x : ℝ => (⌊x⌋₊ : ℝ)) := by
    rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
    · exact h_lambda_pnt.comp <| tendsto_nat_floor_atTop;
    · exact ⟨ 1, by aesop ⟩;
    · exact ⟨ 1, by intros; linarith ⟩;
  rw [ Asymptotics.isLittleO_iff ] at *;
  intro c hc
  filter_upwards [h_floor (half_pos hc), Filter.eventually_gt_atTop 1] with x hx₁ hx₂
  refine le_trans ?_ (le_trans hx₁ ?_)
  · norm_num [ Norm.norm ];
    convert le_rfl using 2;
    congr! 2;
    exact Eq.symm cardFactors_eq_sum_factorization
  · norm_num [ abs_of_nonneg, Nat.floor_le, hx₂.le ];
    rw [ abs_of_nonneg ( by positivity ) ] ; nlinarith [ Nat.floor_le ( by positivity : 0 ≤ x ) ]


lemma sum_mobius_floor (x : ℝ) (hx : 1 ≤ x) : ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = 1 := by
  classical
  have h := sum_mobius_mul_floor x hx
  have h0 : (0 : ℕ) ∈ Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
  have hI : (Iic ⌊x⌋₊).erase 0 = Icc 1 ⌊x⌋₊ := by
    ext n
    simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
  rw [← Finset.sum_erase_add (Iic ⌊x⌋₊) (fun n => (μ n : ℝ) * (⌊x / n⌋ : ℝ)) h0] at h
  simpa [hI] using h

lemma sum_mobius_floor_tail_isLittleO (K : ℕ) (hK : 0 < K) :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)) =o[atTop] fun x => x := by
      have h_group : ∀ x : ℝ, x ≥ 1 → ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, k * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) := by
        intro x hx
        have h_group : ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ) * k := by
          have h_group : Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊ = Finset.biUnion (Finset.Ico 1 K) (fun k => Finset.Ioc (⌊x / (k + 1 : ℝ)⌋₊) (⌊x / (k : ℝ)⌋₊)) := by
            ext n
            simp only [mem_Ioc, mem_biUnion, mem_Ico]
            constructor
            · intro hn
              refine ⟨⌊x / n⌋₊, ?_, ?_, ?_⟩
              all_goals generalize_proofs at *
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [show (n : ℝ) ≥ 1 by norm_cast; linarith]
                exact ⟨by rw [le_div_iff₀ (Nat.cast_pos.mpr <| by linarith)] ; nlinarith [Nat.floor_le (show 0 ≤ x by linarith), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2], by rw [Nat.floor_lt (by positivity)] at *; rw [div_lt_iff₀ (by positivity)] at *; norm_num at *; linarith⟩
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [Nat.lt_floor_add_one (x / n)]
                nlinarith [Nat.lt_floor_add_one (x / n), show (n : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (n : ℝ) ≠ 0 by norm_cast; linarith)]
              · refine Nat.le_floor ?_
                rw [le_div_iff₀] <;> norm_num
                · exact le_trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)) (by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr <| by linarith)])
                · exact Nat.floor_pos.mpr (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| pos_of_gt hn.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2, div_mul_cancel₀ x (show (K : ℝ) ≠ 0 by positivity)])
            · field_simp
              rintro ⟨a, ⟨ha₁, ha₂⟩, ha₃, ha₄⟩
              refine ⟨lt_of_le_of_lt ?_ ha₃, ha₄.trans ?_⟩
              · gcongr ; norm_cast
              · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast ha₁
          rw [h_group, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun n hn => ?_
            simp +zetaDelta only [ge_iff_le, mem_Ico, mem_Ioc, mul_eq_mul_left_iff, Int.cast_eq_zero] at *
            rw [Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity)] at *
            exact Or.inl <| mod_cast Int.floor_eq_iff.mpr ⟨by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)], by rw [div_lt_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)]⟩
          · intros k hk l hl hkl; simp_all +decide [Finset.disjoint_left]
            field_simp
            intro a ha₁ ha₂ ha₃; contrapose! hkl
            rw [Nat.le_floor_iff (by positivity), Nat.floor_lt (by positivity)] at *
            rw [div_lt_iff₀ (by positivity), le_div_iff₀ (by norm_cast; linarith)] at *
            exact Nat.le_antisymm (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith }) (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith })
        simpa only [mul_comm, Finset.mul_sum _ _ _] using h_group
      have h_M_x_over_k : ∀ k : ℕ, 1 ≤ k → k < K → (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
        have h_M : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
          have h_M : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
            convert mu_pnt using 1
            norm_cast
            ext; simp [Asymptotics.IsLittleO]
            norm_num [Asymptotics.IsBigOWith]
            norm_num [Norm.norm]
          have h_M : (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ)) =o[atTop] (fun x => x) := by
            simp_all +decide only [ge_iff_le, Finset.sum_range_succ]
            refine h_M.add ?_
            rw [Asymptotics.isLittleO_iff_tendsto] <;> norm_num
            refine squeeze_zero_norm' (a := fun x : ℝ => 1 / |x|) ?_ ?_
            · norm_num [abs_div]
              exact ⟨1, fun x hx => mul_le_of_le_one_left (by positivity) (mod_cast by exact abs_moebius_le_one)⟩
            · exact tendsto_const_nhds.div_atTop (tendsto_norm_atTop_atTop)
          convert h_M.sub (show (fun x : ℝ => (μ 0 : ℝ)) =o[Filter.atTop] fun x : ℝ => x from ?_) using 2 <;> norm_num [Finset.sum_range_succ']
          erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
        intros k hk_pos hk_lt_K
        have h_M_x_over_k : (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) = (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) - (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k + 1 : ℝ)⌋₊, (μ n : ℝ)) := by
          ext x
          simp only [Pi.sub_apply]
          rw [eq_sub_iff_add_eq']
          simp only [show Finset.Icc (1 : ℕ) (⌊x / (↑k + 1)⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / (↑k + 1)⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / (↑k + 1)⌋₊)),
            show Finset.Icc (1 : ℕ) (⌊x / ↑k⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / ↑k⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / ↑k⌋₊))]
          rw [Finset.sum_Ioc_consecutive] <;> norm_num

          by_cases hx : 0 ≤ x <;> simp_all +decide only [ge_iff_le, floor_div_natCast, not_le]
          · rw [Nat.le_div_iff_mul_le (by positivity)]
            exact Nat.le_floor <| by push_cast; nlinarith [Nat.floor_le (show 0 ≤ x / (k + 1) by positivity), Nat.lt_floor_add_one (x / (k + 1)), mul_div_cancel₀ x (by positivity : (k + 1 : ℝ) ≠ 0)]
          · rw [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx.le (by positivity)), Nat.floor_of_nonpos hx.le] ; norm_num
        rw [h_M_x_over_k]
        refine Asymptotics.IsLittleO.sub ?_ ?_
        · field_simp
          refine h_M.comp_tendsto (Filter.tendsto_id.atTop_mul_const (by positivity)) |> fun h => h.trans_isBigO ?_
          exact Asymptotics.isBigO_iff.mpr ⟨(k : ℝ) ⁻¹, Filter.eventually_atTop.mpr ⟨1, fun x hx => by simp +decide ; ring_nf; norm_num [show k ≠ 0 by linarith]⟩⟩
        · have := h_M.comp_tendsto (show Filter.Tendsto (fun x : ℝ => x / (k + 1)) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_div_const (by positivity))
          rw [Asymptotics.isLittleO_iff] at *
          intro c hc; filter_upwards [this (show 0 < c * (k + 1) by positivity), Filter.eventually_gt_atTop 0] with x hx₁ hx₂; simp_all +decide only [ge_iff_le, norm_eq_abs, eventually_atTop, Function.comp_apply, norm_div, cast_nonneg,
    zero_le_one, add_nonneg, abs_of_nonneg]
          exact hx₁.trans (by rw [mul_assoc, mul_div_cancel₀ _ (by positivity)])
      have h_sum_o_x : (fun x : ℝ => ∑ k ∈ Finset.Ico 1 K, (k : ℝ) * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ))) =o[atTop] (fun x => x) := by
        rw [Asymptotics.isLittleO_iff_tendsto']
        · have h_sum_little_o : ∀ k ∈ Finset.Ico 1 K, Filter.Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) / x) Filter.atTop (nhds 0) := by
            intro k hk; specialize h_M_x_over_k k (Finset.mem_Ico.mp hk |>.1) (Finset.mem_Ico.mp hk |>.2) ; rw [Asymptotics.isLittleO_iff_tendsto'] at h_M_x_over_k <;> aesop
          simpa [Finset.sum_div _ _ _, mul_div_assoc] using tendsto_finset_sum _ fun k hk => h_sum_little_o k hk |> Filter.Tendsto.const_mul _
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      exact h_sum_o_x.congr'
        (by filter_upwards [Filter.eventually_ge_atTop 1] with x hx using by rw [h_group x hx])
        (by norm_num)


lemma sum_mobius_div_approx (x : ℝ) (K : ℕ) (hK : 0 < K) (hx : 1 ≤ x) :
  |x * (∑ n ∈ Icc 1 ⌊x/K⌋₊, (μ n : ℝ) / n) - 1| ≤ x/K + |∑ n ∈ Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
    have h_split : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = (∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) + (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) := by
      erw [Finset.sum_Ioc_consecutive] <;> norm_num
      · rfl
      · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast hK
    have h_floor : ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) / (n : ℝ) - ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋) := by
      rw [Finset.mul_sum _ _ _] ; rw [← Finset.sum_sub_distrib] ; exact Finset.sum_congr rfl fun _ _ => by ring
    have h_bound : |∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ ⌊x / (K : ℝ)⌋₊ := by
      have h_bound : ∀ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, |(μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ 1 := by
        norm_num [abs_mul]
        exact fun n hn₁ hn₂ => mul_le_one₀ (mod_cast by exact abs_moebius_le_one) (abs_nonneg _) (abs_le.mpr ⟨by linarith [Int.fract_nonneg (x / n)], by linarith [Int.fract_lt_one (x / n)]⟩)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum h_bound) (by norm_num))
    have h_sum_floor : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = 1 := by
      convert sum_mobius_floor x hx using 1
    cases abs_cases (x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ) ⌋₊, (μ n : ℝ) / n - 1) <;> cases abs_cases (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ) ⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ) ⌋) <;> linarith [abs_le.mp h_bound, Nat.floor_le (show 0 ≤ x / (K : ℝ) by positivity), Nat.lt_floor_add_one (x / (K : ℝ))]



@[blueprint
  "mu-pnt-alt"
  (title := "Alternate M\\\"obius form of prime number theorem")
  (statement := /-- We have $\sum_{n \leq x} \mu(n)/n = o(1)$. -/)
  (proof := /--
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
  The first term is clearly $O(x/N)$.  For the second term, we can use Theorem \ref{mu-pnt}
  and summation by parts (using the fact that $x/d-j$ is monotone and bounded) to find that
  $$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = o(x)$$
  for any given $j$, so in particular
  $$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = O(x/N^2)$$
  for all $j=1,\dots,N-1$ if $x$ is large enough depending on $N$.
  Summing all the bounds, we obtain the claim.
  -/)
  (proofUses := ["mu-pnt"])
  (latexEnv := "proposition")]
theorem mu_pnt_alt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ) / n) =o[atTop] fun _ ↦ (1 : ℝ) := by
  rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    set S : ℝ → ℝ := fun y => ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (μ n : ℝ) / n
    have h_bound : ∀ K : ℕ, 0 < K → ∀ x : ℝ, 1 ≤ x → |S (x / K)| ≤ 1 / K + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x := by
      intros K hK x hx
      have h_approx : |x * S (x / K) - 1| ≤ x / K + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
        convert sum_mobius_div_approx x K hK hx using 1
      rw [abs_le] at *
      ring_nf at *
      constructor <;> nlinarith [inv_pos.2 (by positivity : 0 < x), mul_inv_cancel₀ (by positivity : x ≠ 0), abs_nonneg (∑ n ∈ Finset.Ioc ⌊ (K : ℝ) ⁻¹ * x⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x * (n : ℝ) ⁻¹⌋)]
    have h_tail_zero : ∀ K : ℕ, 0 < K → Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
      intro K hK
      have h_tail_zero : Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
        have := sum_mobius_floor_tail_isLittleO K hK
        rw [Asymptotics.isLittleO_iff_tendsto'] at this
        · simpa [abs_div] using this.abs.congr' (by filter_upwards [Filter.eventually_gt_atTop 0] with x hx using by rw [abs_div, abs_of_nonneg hx.le])
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      convert h_tail_zero using 1
    have h_eps : ∀ ϵ > 0, ∃ Y : ℝ, ∀ y ≥ Y, |S y| < ϵ := by
      intros ϵ hϵ_pos
      obtain ⟨K, hK_pos, hK⟩ : ∃ K : ℕ, 0 < K ∧ 1 / (K : ℝ) < ϵ / 3 := by
        exact ⟨⌊ϵ⁻¹ * 3⌋₊ + 1, Nat.succ_pos _, by rw [div_lt_iff₀] <;> push_cast <;> nlinarith [Nat.lt_floor_add_one (ϵ⁻¹ * 3), mul_inv_cancel₀ hϵ_pos.ne']⟩
      obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ x ≥ Y, |S (x / K)| < ϵ := by
        have h_tail_zero : Filter.Tendsto (fun x : ℝ => 1 / (K : ℝ) + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds (1 / (K : ℝ))) := by
          simpa using Filter.Tendsto.add (tendsto_const_nhds.add (tendsto_inv_atTop_zero)) (h_tail_zero K hK_pos)
        exact Filter.eventually_atTop.mp (h_tail_zero.eventually (gt_mem_nhds <| by linarith)) |> fun ⟨Y, hY⟩ ↦ ⟨Max.max Y 1, fun x hx ↦ lt_of_le_of_lt (h_bound K hK_pos x <| le_trans (le_max_right _ _) hx) <| hY x <| le_trans (le_max_left _ _) hx⟩
      use Y / K; intros y hy; specialize hY (y * K) (by nlinarith [show (K : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Y (by positivity : (K : ℝ) ≠ 0)]) ; simp_all +decide [ne_of_gt]
    exact Metric.tendsto_atTop.mpr fun ε hε => by simpa using h_eps ε hε
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    convert h_sum_zero using 2 ; erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
  simpa [Finset.sum_range_succ] using h_sum_zero.sub (show Filter.Tendsto (fun x : ℝ => (μ ⌊x⌋₊ : ℝ) / ⌊x⌋₊) Filter.atTop (nhds 0) from tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => by positivity) (fun x => by simpa using div_le_div_of_nonneg_right (show |(μ ⌊x⌋₊ : ℝ)| ≤ 1 from mod_cast by { unfold ArithmeticFunction.moebius; aesop }) <| Nat.cast_nonneg _) <| tendsto_inv_atTop_zero.comp <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop)


blueprint_comment /--
\section{Consequences of the PNT in arithmetic progressions}
-/

@[blueprint
  (title := "Prime number theorem in AP")
  (statement := /--
  If $a\ (q)$ is a primitive residue class, then one has
  $$ \sum_{p \leq x: p = a\ (q)} \log p = \frac{x}{\phi(q)} + o(x).$$
  -/)
  (proof := /--
  This is a routine modification of the proof of Theorem \ref{chebyshev_asymptotic}.
  -/)
  (proofUses := ["chebyshev_asymptotic"])
  (latexEnv := "theorem")]
theorem chebyshev_asymptotic_pnt
    {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0) ~[atTop]
      fun x ↦ x / q.totient := by
  let ψ_aq : ℝ → ℝ := fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else 0
  have htot_pos : (0 : ℝ) < q.totient := cast_pos.mpr (totient_pos.mpr hq)
  have hψ_equiv : ψ_aq ~[atTop] fun x ↦ x / q.totient := by
    have hW := WeakPNT_AP hq ha ha'
    simp only [cumsum, ← Iio_eq_range] at hW
    have hψ_eq x : ψ_aq x = ∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0 := by
      simp only [ψ_aq, show Icc 1 ⌊x⌋₊ = (Iio (⌊x⌋₊ + 1)).filter (1 ≤ ·) by
        ext n; simp [mem_Icc, mem_filter]; tauto, sum_filter]
      refine sum_congr rfl fun n _ ↦ ?_
      by_cases hn : 1 ≤ n <;> simp only [hn, ↓reduceIte]
      push_neg at hn; interval_cases n; simp
    refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx; exact div_ne_zero (by linarith) htot_pos.ne'
    have hlim1 : Tendsto (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
        (⌊x⌋₊ + 1 : ℝ)) atTop (nhds (1 / q.totient)) := by
      have heq : (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
          (⌊x⌋₊ + 1 : ℝ)) = (fun N ↦ (∑ n ∈ Iio N, if n % q = a then Λ n else 0) / N) ∘
          (fun x : ℝ ↦ ⌊x⌋₊ + 1) := by ext x; simp [Function.comp_apply]
      exact heq ▸ hW.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    have hgoal_eq : (ψ_aq / fun x ↦ x / (q.totient : ℝ)) =
        fun x ↦ ψ_aq x / x * q.totient := by ext x; simp only [Pi.div_apply, div_div_eq_mul_div]; ring
    rw [hgoal_eq, show (1 : ℝ) = 1 / q.totient * 1 * q.totient by field_simp]
    refine Tendsto.mul ?_ tendsto_const_nhds
    have heq' : (fun x ↦ ψ_aq x / x) =ᶠ[atTop]
        fun x ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) / (⌊x⌋₊ + 1 : ℝ) * ((⌊x⌋₊ + 1 : ℝ) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [hψ_eq]; field_simp
    exact Tendsto.congr' heq'.symm (hlim1.mul tendsto_floor_add_one_div_self)
  refine hψ_equiv.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, eventually_atTop.mpr ⟨2, fun x hx ↦ ?_⟩⟩
    simp only [Pi.sub_apply, norm_eq_abs, one_mul]
    have hdiff_nonneg : 0 ≤ ψ_aq x - ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0 := by
      simp only [ψ_aq, sub_nonneg]
      calc (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ))
          ≤ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) :=
            sum_le_sum fun p hp ↦ by split_ifs <;> simp [vonMangoldt_apply_prime (mem_filter.mp hp).2]
        _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else (0 : ℝ) :=
            sum_le_sum_of_subset_of_nonneg
              (fun p hp ↦ by simp only [mem_filter, mem_Iic, mem_Icc] at hp ⊢; exact ⟨hp.2.one_lt.le, hp.1⟩)
              (fun n _ _ ↦ by split_ifs <;> [exact vonMangoldt_nonneg; rfl])
    have hdiff_le : ψ_aq x - (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) ≤ ψ x - θ x := by
      simp only [ψ_aq, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
      conv_rhs => rw [Icc_zero_eq_insert, sum_insert (by simp : (0 : ℕ) ∉ Icc 1 ⌊x⌋₊),
        show Λ 0 = 0 by simp only [ArithmeticFunction.map_zero], zero_add,
        show filter Nat.Prime (insert 0 (Icc 1 ⌊x⌋₊)) = filter Nat.Prime (Icc 1 ⌊x⌋₊) by
          simp [filter_insert, Nat.not_prime_zero]]
      rw [filter_prime_Iic_eq_Icc, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) =
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) from
          sum_congr rfl fun p hp ↦ by simp only [mem_filter] at hp; split_ifs <;> simp [vonMangoldt_apply_prime hp.2],
        ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p) = ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), log p from
          sum_congr rfl fun p hp ↦ vonMangoldt_apply_prime (mem_filter.mp hp).2]
      have h1 : (∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), if n % q = a then Λ n else (0 : ℝ)) ≤
          ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), Λ n :=
        sum_le_sum fun n _ ↦ by split_ifs <;> [exact le_refl _; exact vonMangoldt_nonneg]
      linarith
    rw [abs_of_nonneg hdiff_nonneg, abs_of_nonneg (by bound)]
    exact hdiff_le.trans ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)))
  · simpa only [mul_assoc] using
      (isLittleO_sqrt_mul_log.const_mul_left 2).trans_isTheta (isTheta_self_div_const htot_pos.ne')

@[blueprint
  (title := "Dirichlet's theorem")
  (statement := /-- Any primitive residue class contains an infinite number of primes. -/)
  (proof := /--
  If this were not the case, then the sum $\sum_{p \leq x: p = a\ (q)} \log p$
  would be bounded in $x$, contradicting Theorem \ref{chebyshev_asymptotic_pnt}.
  -/)
  (proofUses := ["chebyshev_asymptotic_pnt"])
  (latexEnv := "corollary")]
theorem dirichlet_thm {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) :
    Infinite { p // p.Prime ∧ p % q = a } := by
  have : {p | p.Prime ∧ p % q = a}.Infinite := by
    have : {p | p.Prime ∧ p ≡ a [MOD q]}.Infinite := by
      have := @infinite_setOf_prime_and_eq_mod
      specialize @this q <| NeZero.of_pos hq
      simp_all only [isUnit_iff_exists_inv, forall_exists_index, ← ZMod.natCast_eq_natCast_iff]
      exact this (IsUnit.exists_right_inv (show IsUnit (a : ZMod q) from by
        rwa [ZMod.isUnit_iff_coprime])).choose (IsUnit.exists_right_inv (show IsUnit (a : ZMod q)
          from by rwa [ZMod.isUnit_iff_coprime])).choose_spec
    exact this.mono fun p hp ↦ ⟨hp.1, by simpa [ModEq, mod_eq_of_lt ha'] using hp.2⟩
  exact Set.infinite_coe_iff.mpr this

blueprint_comment /--
\section{Consequences of the Chebotarev density theorem}

-/

blueprint_comment /--
\begin{lemma}[Cyclotomic Chebotarev]\label{Chebotarev-cyclic}  For any $a$ coprime to $m$,
$$ \sum_{N \mathfrak{p} \leq x; N \mathfrak{p} = a\ (m)} \log N \mathfrak{p}  =
\frac{1}{|G|} \sum_{N \mathfrak{p} \leq x} \log N \mathfrak{p}.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}\uses{Dedekind-PNT, WeakPNT-AP} This should follow from Lemma \ref{Dedekind-PNT} by a Fourier expansion.
\end{proof}
-/
