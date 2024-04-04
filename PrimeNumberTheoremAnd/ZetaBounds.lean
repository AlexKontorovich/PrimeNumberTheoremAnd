import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Algebra.Group.Basic
import EulerProducts.PNT
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.CauchyIntegral

-- only importing the following for the MeasurableDiv₂ ℝ instance.
-- should remove eventually
import PrimeNumberTheoremAnd.PerronFormula

open BigOperators Complex Topology Filter Interval

-- move near `Real.differentiableAt_rpow_const_of_ne`
theorem Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun (x : ℝ) => (x : ℂ) ^ s) x := by
  sorry

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← Complex.cpow_add]
  simp only [add_left_neg, Complex.cpow_zero]
  exact_mod_cast x_ne

-- No longer used
theorem ContDiffOn.hasDeriv_deriv {φ : ℝ → ℂ} {s : Set ℝ} (φDiff : ContDiffOn ℝ 1 φ s) {x : ℝ}
    (x_in_s : s ∈ nhds x) : HasDerivAt φ (deriv φ x) x :=
  (ContDiffAt.hasStrictDerivAt (φDiff.contDiffAt x_in_s) (by simp)).hasDerivAt

-- No longer used
theorem ContDiffOn.continuousOn_deriv {φ : ℝ → ℂ} {a b : ℝ}
    (φDiff : ContDiffOn ℝ 1 φ (Set.uIoo a b)) :
    ContinuousOn (deriv φ) (Set.uIoo a b) := by
  apply ContDiffOn.continuousOn (𝕜 := ℝ) (n := 0)
  exact (fun h => ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).1 h).2) φDiff

theorem LinearDerivative_ofReal (x : ℝ) (a b : ℂ) : HasDerivAt (fun (t : ℝ) ↦ a * t + b) a x := by
  refine HasDerivAt.add_const ?_ b
  have := @ContinuousLinearMap.hasDerivAt (e := Complex.ofRealCLM) x
  have := this.const_mul (c := a)
  convert this using 1; simp

-- No longer used
section
-- from Floris van Doorn

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {a b : ℝ}

set_option autoImplicit false in
open BigOperators Interval Topology Set intervalIntegral MeasureTheory in
theorem integral_deriv_mul_eq_sub' {u v u' v' : ℝ → A}
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a := by
  have h2u : ContinuousOn u [[a, b]] :=
    fun x hx ↦ (hu x hx).continuousWithinAt
  have h2v : ContinuousOn v [[a, b]] :=
    fun x hx ↦ (hv x hx).continuousWithinAt
  apply integral_eq_sub_of_hasDeriv_right (h2u.mul h2v)
  · exact fun x hx ↦ (hu x <| mem_Icc_of_Ioo hx).mul (hv x <| mem_Icc_of_Ioo hx) |>.hasDerivAt
      (Icc_mem_nhds hx.1 hx.2) |>.hasDerivWithinAt
  · exact (hu'.mul_continuousOn h2v).add (hv'.continuousOn_mul h2u)

end

lemma sum_eq_int_deriv_aux2 {φ : ℝ → ℂ} {a b : ℝ} (c : ℂ)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∫ (x : ℝ) in a..b, (c - x) * deriv φ x =
      (c - b) * φ b - (c - a) * φ a + ∫ (x : ℝ) in a..b, φ x := by
  set u := fun (x : ℝ) ↦ c - x
  set u' := fun (x : ℝ) ↦ (-1 : ℂ)
  have hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x := by
    intros x _
    convert LinearDerivative_ofReal x (-1 : ℂ) c; ring
  have hu' : IntervalIntegrable u' MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    continuity
  have hv' : IntervalIntegrable (deriv φ) MeasureTheory.volume a b :=
    derivφCont.intervalIntegrable
  convert intervalIntegral.integral_mul_deriv_eq_deriv_mul hu φDiff hu' hv' using 1
  simp [u]

lemma sum_eq_int_deriv_aux_eq {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ}
    (b_eq_kpOne : b = k + 1) (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n in Finset.Ioc k ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  have flb_eq_k : ⌊b⌋ = k + 1 := Int.floor_eq_iff.mpr ⟨by exact_mod_cast b_eq_kpOne.symm.le,
    by rw [b_eq_kpOne]; simp⟩
  simp only [flb_eq_k, Finset.Icc_self, Finset.sum_singleton, Int.cast_add, Int.cast_one]
  rw [sum_eq_int_deriv_aux2 (k + 1 / 2) φDiff derivφCont, b_eq_kpOne]
  ring_nf
  have : Finset.Ioc k (1 + k) = {k + 1} := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · intro ⟨h₁, h₂⟩
      rw [add_comm] at h₂
      exact Int.le_antisymm h₂ h₁
    · exact fun h ↦ ⟨by simp [h], by simp [h, add_comm]⟩
  simp_rw [this]
  simp only [Finset.sum_singleton, Int.cast_add, Int.cast_one, add_comm]

lemma sum_eq_int_deriv_aux_lt {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (k_le_a : k ≤ a) (a_lt_b : a < b)
    (b_lt_kpOne : b < k + 1) (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n in Finset.Ioc k ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  have flb_eq_k : ⌊b⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  simp only [flb_eq_k, gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, Finset.Icc_eq_empty_of_lt,
    Finset.sum_empty]
  rw [sum_eq_int_deriv_aux2 (k + 1 / 2) φDiff derivφCont]
  have : Finset.Ioc k k = {} := by
    simp only [ge_iff_le, le_refl, Finset.Ioc_eq_empty_of_le]
  simp only [this, Finset.sum_empty, one_div]
  ring_nf

lemma sum_eq_int_deriv_aux1 {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (k_le_a : k ≤ a) (a_lt_b : a < b)
    --(a_lt_kpOne : a < k + 1)
    (b_le_kpOne : b ≤ k + 1) (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n in Finset.Ioc k ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  by_cases h : b = k + 1
  · exact sum_eq_int_deriv_aux_eq h φDiff derivφCont
  · refine sum_eq_int_deriv_aux_lt k_le_a a_lt_b ?_ φDiff derivφCont
    refine (Ne.lt_of_le h b_le_kpOne)

/-%%
\begin{lemma}[sum_eq_int_deriv_aux]\label{sum_eq_int_deriv_aux}\lean{sum_eq_int_deriv_aux}\leanok
  Let $k \le a < b\le k+1$, with $k$ an integer, and let $\phi$ be continuously differentiable on
  $[a, b]$.
  Then
  \[
  \sum_{a < n \le b} \phi(n) = \int_a^b \phi(x) \, dx + \left(\lfloor b \rfloor + \frac{1}{2} - b\right) \phi(b) - \left(\lfloor a \rfloor + \frac{1}{2} - a\right) \phi(a) - \int_a^b \left(\lfloor x \rfloor + \frac{1}{2} - x\right) \phi'(x) \, dx.
  \]
\end{lemma}
%%-/
lemma sum_eq_int_deriv_aux {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (k_le_a : k ≤ a) (a_lt_b : a < b)
    (b_le_kpOne : b ≤ k + 1) (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n in Finset.Ioc ⌊a⌋ ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (⌊a⌋ + 1 / 2 - a) * φ a
      - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  have fl_a_eq_k : ⌊a⌋ = k := Int.floor_eq_iff.mpr ⟨k_le_a, by linarith⟩
  convert sum_eq_int_deriv_aux1 k_le_a a_lt_b b_le_kpOne φDiff derivφCont using 2
  · rw [fl_a_eq_k]
  · congr
  · apply intervalIntegral.integral_congr_ae
    have : ∀ᵐ (x : ℝ) ∂MeasureTheory.volume, x ≠ b := by
      convert Set.Countable.ae_not_mem (s := {b}) (by simp) (μ := MeasureTheory.volume) using 1
    filter_upwards [this]
    intro x x_ne_b hx
    rw [Set.uIoc_of_le a_lt_b.le, Set.mem_Ioc] at hx
    congr
    exact Int.floor_eq_iff.mpr ⟨by linarith, by have := Ne.lt_of_le x_ne_b hx.2; linarith⟩
/-%%
\begin{proof}\leanok
Partial integration.
\end{proof}
%%-/

-- Thanks to Arend Mellendijk

lemma interval_induction_aux_int (n : ℕ) : ∀ (P : ℝ → ℝ → Prop)
    (_ : ∀ a b : ℝ, ∀ k : ℤ, k ≤ a → a < b → b ≤ k + 1 → P a b)
    (_ : ∀ (a : ℝ) (k : ℤ) (c : ℝ), a < k → k < c → P a k → P k c → P a c)
    (a b : ℝ) (_ : a < b) (_ : n = ⌊b⌋ - ⌊a⌋),
    P a b := by
  induction n using Nat.case_strong_induction_on with
  | hz =>
    intro P base _ a b hab hn
    apply base a b ⌊a⌋ (Int.floor_le a) hab
    simp only [CharP.cast_eq_zero] at hn
    rw [(by linarith : ⌊a⌋ = ⌊b⌋)]
    exact (Int.lt_floor_add_one b).le
  | hi n ih =>
    intro P base step a b _ hn
    have Pa : P a (⌊a⌋ + 1) :=
      base a (⌊a⌋ + 1) ⌊a⌋ (Int.floor_le a) (Int.lt_floor_add_one a) (le_of_eq rfl)
    by_cases b_le_flaP1 : b = ⌊a⌋ + 1
    · rwa [b_le_flaP1]
    have flaP1_lt_b : ⌊a⌋ + 1 < b := by
      simp only [Nat.cast_succ] at hn
      have := Int.floor_le b
      have : 0 ≤ n := Nat.zero_le n
      have : ⌊a⌋ + 1 ≤ ⌊b⌋ := by linarith
      have : (⌊a⌋ : ℝ) + 1 ≤ ⌊b⌋ := by exact_mod_cast this
      push_neg at b_le_flaP1
      exact Ne.lt_of_le (id (Ne.symm b_le_flaP1)) (by linarith : ⌊a⌋ + 1 ≤ b)
    have Pfla_b : P (⌊a⌋ + 1) b := by
      apply ih n (le_of_eq rfl) P base step (⌊a⌋ + 1) b flaP1_lt_b
      simp only [Int.floor_add_one, Int.floor_intCast, Nat.cast_succ] at hn ⊢
      rw [sub_eq_add_neg, neg_add, ← add_assoc, ← sub_eq_add_neg (a := ⌊b⌋), ← hn]
      ring
    refine step a (⌊a⌋ + 1) b ?_ (by exact_mod_cast flaP1_lt_b) (by exact_mod_cast Pa)
      (by exact_mod_cast Pfla_b)
    have := Int.lt_floor_add_one a
    exact_mod_cast this

lemma interval_induction (P : ℝ → ℝ → Prop)
    (base : ∀ a b : ℝ, ∀ k : ℤ, k ≤ a → a < b → b ≤ k + 1 → P a b)
    (step : ∀ (a : ℝ) (k : ℤ) (b : ℝ), a < k → k < b → P a k → P k b → P a b)
    (a b : ℝ) (hab : a < b) : P a b := by
  set n := ⌊b⌋ - ⌊a⌋ with hn
  clear_value n
  have : 0 ≤ n := by
    have : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_le_floor _ _ (hab.le)
    simp only [hn, sub_nonneg, ge_iff_le]
    exact this
  lift n to ℕ using this
  exact interval_induction_aux_int n P base step a b hab hn

/-%%
\begin{lemma}[sum_eq_int_deriv]\label{sum_eq_int_deriv}\lean{sum_eq_int_deriv}\leanok
  Let $a < b$, and let $\phi$ be continuously differentiable on $[a, b]$.
  Then
  \[
  \sum_{a < n \le b} \phi(n) = \int_a^b \phi(x) \, dx + \left(\lfloor b \rfloor + \frac{1}{2} - b\right) \phi(b) - \left(\lfloor a \rfloor + \frac{1}{2} - a\right) \phi(a) - \int_a^b \left(\lfloor x \rfloor + \frac{1}{2} - x\right) \phi'(x) \, dx.
  \]
\end{lemma}
%%-/
/-- ** Partial summation ** (TODO : Add to Mathlib). -/

-- stupid lemma -- what's the better way to do this?
lemma add_two {a b c d : ℂ} (h : a = b) (h' : c = d) : a + c = b + d := by
  exact Mathlib.Tactic.LinearCombination.add_pf h h'

-- In Yaël Dillies's API (https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Finset.2Esum_add_adjacent_intervals/near/430127101)
lemma Finset.sum_Ioc_add_sum_Ioc {a b c : ℤ} (f : ℤ → ℂ) (h : a ≤ b) (h' : b ≤ c) :
  (∑ n in Finset.Ioc a b, f n) + (∑ n in Finset.Ioc b c, f n) = ∑ n in Finset.Ioc a c, f n := by
  sorry

theorem integrability_aux₀ {a b : ℝ} (a_lt_b : a < b) :
    ∀ᵐ (x : ℝ) ∂MeasureTheory.Measure.restrict MeasureTheory.volume [[a, b]],
      ‖(⌊x⌋ : ℂ)‖ ≤ max ‖a‖ ‖b‖ + 1 := by
  rw [MeasureTheory.ae_restrict_iff']
  swap; · exact measurableSet_Icc
  refine MeasureTheory.ae_of_all _ (fun x hx ↦ ?_)
  rw [Set.uIcc_of_le a_lt_b.le, Set.mem_Icc] at hx
  simp only [norm_int, Real.norm_eq_abs]
  have : |x| ≤ max |a| |b| := by
    rw [abs_le]
    cases' abs_cases a with ha ha
    · cases' abs_cases b with hb hb
      · simp only [ha.1, hb.1, le_max_iff]
        have : 0 ≤ max a b := by simp [ha.2, hb.2]
        refine ⟨by linarith, by right; linarith⟩
      · simp only [ha.1, hb.1, le_max_iff]
        have : 0 ≤ max a (-b) := by simp [ha.2, hb.2]
        refine ⟨by linarith, by linarith⟩
    · cases' abs_cases b with hb hb
      · simp only [ha.1, hb.1, ← min_neg_neg, neg_neg, min_le_iff, le_max_iff]
        refine ⟨by left; exact hx.1, by right; exact hx.2⟩
      · simp only [ha.1, hb.1, ← min_neg_neg, neg_neg, min_le_iff, le_max_iff]
        refine ⟨by left; exact hx.1, by right; linarith⟩
  have aux1 : ⌊x⌋ ≤ x := Int.floor_le x
  have aux2 : x ≤ ⌊x⌋ + 1 := (Int.lt_floor_add_one x).le
  cases' abs_cases x with hx hx
  · have : (0 : ℝ) ≤ ⌊x⌋ := by
      exact_mod_cast Int.floor_nonneg.mpr hx.2
    rw [_root_.abs_of_nonneg this]
    linarith
  · have : (⌊x⌋ : ℝ) ≤ 0 := by
      exact_mod_cast Int.floor_nonpos hx.2.le
    rw [_root_.abs_of_nonpos this]
    linarith

lemma integrability_aux₁ {a b : ℝ} (a_lt_b : a < b) :
    IntervalIntegrable (fun (x : ℝ) ↦ (⌊x⌋ : ℂ)) MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := max ‖a‖ ‖b‖ + 1)
  · simp only [Real.volume_interval, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  · apply Measurable.aestronglyMeasurable
    apply Measurable.comp
    · exact fun ⦃t⦄ _ ↦ trivial
    · exact Int.measurable_floor
  · exact integrability_aux₀ a_lt_b

lemma integrability_aux₂ {a b : ℝ} :
    IntervalIntegrable (fun (x : ℝ) ↦ (1 : ℂ) / 2 - x) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply Continuous.continuousOn
  exact Continuous.sub continuous_const Complex.ofRealCLM.continuous

lemma integrability_aux {a b : ℝ} (a_lt_b : a < b) :
    IntervalIntegrable (fun (x : ℝ) ↦ (⌊x⌋ : ℂ) + 1 / 2 - x) MeasureTheory.volume a b := by
  convert (integrability_aux₁ a_lt_b).add integrability_aux₂ using 2; ring

theorem sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n in Finset.Ioc ⌊a⌋ ⌊b⌋, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (⌊a⌋ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  let P : ℝ → ℝ → Prop := fun a₁ b₁ ↦ (∀ x ∈ [[a₁, b₁]], HasDerivAt φ (deriv φ x) x) →
    (ContinuousOn (deriv φ) [[a₁, b₁]]) →
    ∑ n in Finset.Ioc ⌊a₁⌋ ⌊b₁⌋, φ n =
    (∫ x in a₁..b₁, φ x) + (⌊b₁⌋ + 1 / 2 - b₁) * φ b₁ - (⌊a₁⌋ + 1 / 2 - a₁) * φ a₁
      - ∫ x in a₁..b₁, (⌊x⌋ + 1 / 2 - x) * deriv φ x
  apply interval_induction P ?_ ?_ a b a_lt_b φDiff derivφCont
  · exact fun _ _ _ k_le_a₁ a₁_lt_b₁ b₁_le_k1 φDiff₁ derivφCont₁ ↦
      sum_eq_int_deriv_aux k_le_a₁ a₁_lt_b₁ b₁_le_k1 φDiff₁ derivφCont₁
  · intro a₁ k₁ b₁ a_lt_k₁ k_lt_b₁ ih₁ ih₂ φDiff₁ derivφCont₁
    have φDiff₁₁ : ∀ x ∈ [[a₁, k₁]], HasDerivAt φ (deriv φ x) x := by
      intro x hx
      refine φDiff₁ x ?_
      rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at hx ⊢
      refine ⟨by linarith, by linarith⟩
    have derivφCont₁₁ : ContinuousOn (deriv φ) [[a₁, k₁]] := by
      apply derivφCont₁.mono
      rw [Set.uIcc_of_le a_lt_k₁.le, Set.uIcc_of_le (by linarith)]
      apply Set.Icc_subset_Icc (by linarith) (by linarith)
    have s₁ := ih₁ φDiff₁₁ derivφCont₁₁
    have φDiff₁₂ : ∀ x ∈ [[(k₁ : ℝ), b₁]], HasDerivAt φ (deriv φ x) x := by
      intro x hx
      refine φDiff₁ x ?_
      rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at hx ⊢
      refine ⟨by linarith, by linarith⟩
    have derivφCont₁₂ : ContinuousOn (deriv φ) [[(k₁ : ℝ), b₁]] := by
      apply derivφCont₁.mono
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      apply Set.Icc_subset_Icc (by linarith) (by linarith)
    have s₂ := ih₂ φDiff₁₂ derivφCont₁₂
    convert add_two s₁ s₂ using 1
    · rw [← Finset.sum_Ioc_add_sum_Ioc]
      · exact Int.floor_mono a_lt_k₁.le
      · exact Int.floor_mono k_lt_b₁.le
    · set I₁ := ∫ (x : ℝ) in a₁..b₁, φ x
      set I₂ := ∫ (x : ℝ) in a₁..k₁, φ x
      set I₃ := ∫ (x : ℝ) in k₁..b₁, φ x
      set J₁ := ∫ (x : ℝ) in a₁..b₁, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x
      set J₂ := ∫ (x : ℝ) in a₁..k₁, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x
      set J₃ := ∫ (x : ℝ) in k₁..b₁, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x
      have : I₂ + I₃ = I₁ := by
        apply intervalIntegral.integral_add_adjacent_intervals <;>
        apply ContinuousOn.intervalIntegrable
        · exact HasDerivAt.continuousOn φDiff₁₁
        · exact HasDerivAt.continuousOn φDiff₁₂
      rw [← this]
      have : J₂ + J₃ = J₁ := by
        apply intervalIntegral.integral_add_adjacent_intervals <;>
        apply IntervalIntegrable.mul_continuousOn
        · apply integrability_aux a_lt_k₁
        · exact derivφCont₁₁
        · apply integrability_aux k_lt_b₁
        · exact derivφCont₁₂
      rw [← this]
      ring
/-%%
\begin{proof}\uses{sum_eq_int_deriv_aux}\leanok
  Apply Lemma \ref{sum_eq_int_deriv_aux} in blocks of length $\le 1$.
\end{proof}
%%-/

lemma xpos_of_uIcc {a b : ℕ} (apos : 0 < a) (a_lt_b : a < b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [Set.uIcc_of_le (by exact_mod_cast a_lt_b.le), Set.mem_Icc] at x_in
  have : (0 : ℝ) < a := by exact_mod_cast apos
  linarith

lemma neg_s_ne_neg_one {s : ℂ} (s_ne_one : s ≠ 1) : -s ≠ -1 := by
  intro hs
  have : s = 1 := neg_inj.mp hs
  exact s_ne_one this

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (apos : 0 < a) (a_lt_b : a < b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · apply intervalIntegral.integral_congr
    intro x hx
    simp only
    apply one_div_cpow_eq
    exact xpos_of_uIcc apos a_lt_b hx
  · norm_cast
    rw [(by ring : -s + 1 = 1 - s)]
  · right; refine ⟨neg_s_ne_neg_one s_ne_one, ?_⟩
    rw [Set.uIcc_of_le (by exact_mod_cast a_lt_b.le), Set.mem_Icc]
    push_neg
    intro ha
    norm_cast at ha ⊢
    linarith

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  apply hasDerivAt_deriv_iff.mpr
  apply DifferentiableAt.div
  · fun_prop
  · exact Real.differentiableAt_cpow_const_of_ne s xpos.ne'
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast xpos.ne' : (x : ℂ) ≠ 0) s]
  apply Complex.exp_ne_zero

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s / (x : ℂ) ^ (s + 1)) x := by
  let r := -s - 1
  have s_eq : s = -r - 1 := by ring
  have r_ne_neg1 : r ≠ -1 := by
    intro hr
    have : s = 0 := by
      rw [hr] at s_eq
      convert s_eq; ring
    exact s_ne_zero this
  have r_add1_ne_zero : r + 1 ≠ 0 := by
    intro hr
    have : r = -1 := by sorry
    exact r_ne_neg1 this
  have hasDeriv := hasDerivAt_ofReal_cpow xpos.ne' r_ne_neg1
  have diffAt := hasDeriv.differentiableAt
  have := deriv_const_mul (-s) diffAt
  rw [hasDeriv.deriv] at this
  convert this using 2
  · ext y
    by_cases y_zero : y = 0
    · simp only [y_zero, ofReal_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have y_ne : (y : ℂ) ≠ 0 := by exact_mod_cast y_zero
      have : (y : ℂ) ^ s ≠ 0 := by sorry
      field_simp
      rw [s_eq, mul_assoc, ← Complex.cpow_add _ _ y_ne, (by ring : r + 1 + (-r - 1) = 0), Complex.cpow_zero]
      ring
  · simp only [neg_mul]
    rw [div_eq_mul_inv, ← one_div]


#exit
  have := @deriv_const_mul
  sorry

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_one : s ≠ 1) {a b : ℕ} (apos : 0 < a) (a_lt_b : a < b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  sorry

/-%%
\begin{lemma}[ZetaSum_aux1]\label{ZetaSum_aux1}\lean{ZetaSum_aux1}\leanok
  Let $0 < a < b$ be natural numbers and $s\in \C$ with $s \ne 1$.
  Then
  \[
  \sum_{a < n \le b} \frac{1}{n^s} =  \frac{b^{1-s} - a^{1-s}}{1-s} + \frac{b^{-s}-a^{-s}}{2} + s \int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx.
  \]
\end{lemma}
%%-/
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (apos : 0 < a) (a_lt_b : a < b) :
    ∑ n in Finset.Ioc (a : ℤ) b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s / (x : ℂ) ^ (s + 1)
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc apos a_lt_b hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x := fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := fun x hx ↦ ZetaSum_aux1φderiv s_ne_one (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_one apos a_lt_b
  have : (a : ℝ) < (b : ℝ) := by exact_mod_cast a_lt_b
  convert sum_eq_int_deriv this φDiff derivφCont using 1
  · congr
    · simp only [Int.floor_natCast]
    · simp only [Int.floor_natCast]
  · rw [Int.floor_natCast, Int.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, mul_comm s _, ← mul_div]
    rw [ZetaSum_aux1₁ s_ne_one apos a_lt_b]
    set int1 := ∫ (x : ℝ) in (a : ℝ)..b, ((⌊x⌋ : ℂ) + 1 / 2 - x) * deriv φ x
    rw [sub_eq_add_neg (b := int1)]
    set int2 := ∫ (x : ℝ) in a..b, (⌊x⌋ + 1 / 2 - x) * (s / ↑x ^ (s + 1))
    have : int2 = - int1 := by
      rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
      intro x hx
      simp_rw [φderiv x hx]
      simp only [φ']
      ring
    rw [this]
    norm_cast
    set term1 := (b + 1 / 2 - b) * φ b
    set term2 := (a + 1 / 2 - a) * φ a
    have : term1 = 1 / 2 * (1 / b ^ s) := by
      ring_nf
      congr
    rw [this]
    have : term2 = 1 / 2 * (1 / a ^ s) := by
      ring_nf
      congr
    rw [this]
/-%%
\begin{proof}\uses{sum_eq_int_deriv}
  Apply Lemma \ref{sum_eq_int_deriv} to the function $x \mapsto x^{-s}$.
\end{proof}
%%-/

lemma ZetaSum_aux1a_aux1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a,b]])
    : x > 0 := by
  rcases hx with ⟨h, _⟩
  have : a ⊓ b > 0 := by
    rw [inf_eq_min]
    have : b > 0 := by
      exact lt_of_lt_of_le apos (le_of_lt a_lt_b)
    exact lt_min apos this
  exact lt_of_lt_of_le this h

lemma ZetaSum_aux1a_aux1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Set.Icc a b)
    : x > 0 := by
  rcases hx with ⟨h, _⟩
  exact lt_of_lt_of_le apos h

lemma ZetaSum_aux1a_aux2a  {x r : ℝ} (hx : x > 0) : 1 / x^r = x^(-r) := by
  have h : x^(-r) * x^(r) = 1 := by
    rw [← Real.rpow_add hx (-r) (r)]
    simp only [add_left_neg, Real.rpow_zero]
  have h' : x^r ≠ 0 := by
    intro h'
    rw [h', mul_zero] at h
    exact zero_ne_one h
  exact div_eq_of_eq_mul h' h.symm

lemma ZetaSum_aux1a_aux2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1/x^(c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  have : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c) := by
    ring
  rw [this]
  have : -c-1 ≠ -1 := by
    simp only [ne_eq, sub_eq_neg_self, neg_eq_zero]
    exact h.1
  have : -c-1 ≠ -1 ∧ 0 ∉ [[a, b]] := ⟨ this, h.2 ⟩
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr this)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x h
  simp only
  have : x > 0 := by
    exact ZetaSum_aux1a_aux1 apos a_lt_b h
  rw [ZetaSum_aux1a_aux2a this]
  congr
  ring

lemma ZetaSum_aux1a_aux3a (x : ℝ) : -(1/2) < ⌊ x ⌋ + 1/2 - x := by
  have : 0 < (⌊ x ⌋ + 1) - x := by
    exact sub_pos_of_lt (Int.lt_floor_add_one x)
  calc
    _ = -1/2 := by norm_num
    _ < -1/2 + ((⌊ x ⌋ + 1) - x) := lt_add_of_pos_right (-1/2) this
    _ = _ := by ring

lemma ZetaSum_aux1a_aux3b (x : ℝ) : ⌊x⌋ + 1/2 - x ≤ 1/2 := by
  have : ⌊x⌋ - x ≤ 0 := by
    exact sub_nonpos.mpr (Int.floor_le x)
  ring_nf
  exact add_le_of_nonpos_right this

lemma ZetaSum_aux1a_aux3 (x : ℝ) : |(⌊x⌋ + 1/2 - x)| ≤ 1/2 := by
  apply abs_le.mpr
  constructor
  · exact le_of_lt (ZetaSum_aux1a_aux3a x)
  exact ZetaSum_aux1a_aux3b x

lemma ZetaSum_aux1a_aux4a (x : ℝ) (c : ℂ) (s : ℂ) (hx : 0 < x) : (Complex.abs (c / ((x : ℂ) ^ (s+1)))) = (Complex.abs c) / x^((s + 1).re) := by
  simp only [map_div₀, abs_ofReal]
  congr
  exact Complex.abs_cpow_eq_rpow_re_of_pos hx (s+1)

lemma ZetaSum_aux1a_aux4b (c : ℝ) : (Complex.abs c) = |c| := by
  exact abs_ofReal c

lemma ZetaSum_aux1a_aux4b' (x : ℝ) : (Complex.abs (⌊x⌋ + 1 / 2 - x)) = |⌊x⌋ + 1 / 2 - x| := by
  have := ZetaSum_aux1a_aux4b (⌊x⌋ + 1 / 2 - x)
  rw [← this]
  simp only [one_div, ofReal_sub, ofReal_add, ofReal_int_cast, ofReal_inv, ofReal_ofNat]

lemma ZetaSum_aux1a_aux4c (x : ℝ) (hx : 0 < x) (s : ℂ) : Complex.abs ((⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ)^(s + 1)) = |⌊x⌋ + 1 / 2 - x| / x^((s + 1).re) := by
  calc
    _ = (Complex.abs (⌊x⌋ + 1 / 2 - x)) / x^((s + 1).re) := by
      exact ZetaSum_aux1a_aux4a x (⌊x⌋ + 1 / 2 - x) s hx
    _ = |⌊x⌋ + 1 / 2 - x| / x^((s + 1).re) := by
      congr
      exact ZetaSum_aux1a_aux4b' x

theorem ZetaSum_aux1a_aux4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, Complex.abs ((↑⌊x⌋ + 1 / 2 - ↑x) / ↑x ^ (s + 1)) =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  intro x hx
  simp only
  exact ZetaSum_aux1a_aux4c x (ZetaSum_aux1a_aux1 apos a_lt_b hx) s

theorem ZetaSum_aux1a_aux5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Set.Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · calc
    _ ≤ 1/2 := ZetaSum_aux1a_aux3 x
    _ ≤ 1 := by norm_num
  · apply Real.rpow_nonneg
    exact le_of_lt (ZetaSum_aux1a_aux1' apos h)

theorem ZetaSum_aux1a_aux5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc (le_of_lt a_lt_b) _
  apply ContinuousOn.div
  · apply continuousOn_const
  · apply ContinuousOn.rpow_const
    · apply continuousOn_id
    · intro x hx
      have : x > 0 := by
        exact ZetaSum_aux1a_aux1' apos hx
      exact Or.inl (ne_of_gt this)
  · intro x hx
    by_contra h
    have h1 : x > 0 := by
      exact (ZetaSum_aux1a_aux1' apos hx)
    have : s.re + 1 ≠ 0 := by
      exact ne_of_gt (add_pos σpos zero_lt_one)
    have := (Real.rpow_eq_zero (le_of_lt h1) this).mp h
    exact (ne_of_gt h1) this


theorem ZetaSum_aux1a_aux5c {a b : ℝ} {s : ℂ} :
  let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
  MeasureTheory.AEStronglyMeasurable g (MeasureTheory.Measure.restrict MeasureTheory.volume (Ι a b)) := by
  intro g
  let g1 : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u|;
  let g2 : ℝ → ℝ := fun u ↦ u ^ (s.re + 1);
  have : g = g1 / g2 := by
    ext x
    simp only [Pi.div_apply]
  rw [this]
  apply Measurable.aestronglyMeasurable
  apply Measurable.div
  · apply (_root_.continuous_abs).measurable.comp
    · apply Measurable.sub
      · apply Measurable.add
        · apply Measurable.comp
          · exact fun _ _ ↦ trivial
          · exact Int.measurable_floor
        · exact measurable_const
      · exact measurable_id
  · exact measurable_id.pow_const _

theorem ZetaSum_aux1a_aux5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  suffices IntervalIntegrable g MeasureTheory.volume a b
    by exact this
  apply IntervalIntegrable.mono_fun (ZetaSum_aux1a_aux5b apos a_lt_b σpos)
  · exact ZetaSum_aux1a_aux5c
  simp
  show (fun x ↦ |g x|) ≤ᶠ[MeasureTheory.Measure.ae (MeasureTheory.Measure.restrict MeasureTheory.volume (Ι a b))] fun x ↦
  |x ^ (s.re + 1)|⁻¹
  filter_upwards
  unfold_let
  intro x
  simp only
  rw [abs_div, div_eq_mul_inv]
  nth_rw 2 [← one_mul |x ^ (s.re + 1)|⁻¹]
  apply mul_le_mul
  · rw [_root_.abs_abs]
    calc
      _ ≤ 1/2 := ZetaSum_aux1a_aux3 x
      _ ≤ 1 := by norm_num
  · simp only [le_refl]
  · simp only [inv_nonneg, abs_nonneg]
  · norm_num

theorem ZetaSum_aux1a_aux5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on _ _ _
  · exact ZetaSum_aux1a_aux5a apos
  · exact le_of_lt a_lt_b
  · exact ZetaSum_aux1a_aux5d apos a_lt_b σpos
  · exact ZetaSum_aux1a_aux5b apos a_lt_b σpos

/-%%
\begin{lemma}[ZetaSum_aux1a]\label{ZetaSum_aux1a}\lean{ZetaSum_aux1a}\leanok
For any $0 < a < b$ and  $s \in \C$ with $\sigma=\Re(s)>0$,
$$
\left|\int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx\right|
\le \frac{a^{-\sigma}-b^{-\sigma}}{\sigma}.
$$
\end{lemma}
%%-/
lemma ZetaSum_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    Complex.abs (∫ x in a..b, (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1)) ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ ≤ ∫ x in a..b, Complex.abs ((⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1)) :=
        intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
          (a := a) (b := b) (f := λ x => (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1)) (le_of_lt a_lt_b)
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x^((s+1).re) := by
      exact ZetaSum_aux1a_aux4 apos a_lt_b
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x^(s.re + 1) := by rfl
    _ ≤ ∫ x in a..b, 1 / x^(s.re + 1) := by
      exact ZetaSum_aux1a_aux5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
      have h1 : s.re ≠ 0 := by
        exact ne_of_gt σpos
      have h2 : 0 ∉ [[a,b]] := by
        by_contra h
        rw [Set.mem_uIcc] at h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact not_le_of_lt apos h
        have : a < a := by
          calc
            a < b := a_lt_b
            _ ≤ 0 := h
            _ < a := apos
        exact lt_irrefl a this
      apply ZetaSum_aux1a_aux2 (c := s.re) apos a_lt_b ⟨ h1, h2 ⟩

/-%%
\begin{proof}
Apply the triangle inequality
$$
\left|\int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx\right|
\le \int_a^b \frac{1}{x^{\sigma+1}} \, dx,
$$
and evaluate the integral.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaSum_aux2]\label{ZetaSum_aux2}\lean{ZetaSum_aux2}\leanok
  Let $N$ be a natural number and $s\in \C$, $\Re(s)>1$.
  Then
  \[
  \sum_{N < n} \frac{1}{n^s} =  \frac{- N^{1-s}}{1-s} + \frac{-N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx.
  \]
\end{lemma}
%%-/
lemma ZetaSum_aux2 {N : ℕ} {s : ℂ} (s_re_pos : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Set.Ici (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1) := by
  sorry
/-%%
\begin{proof}\uses{ZetaSum_aux1, ZetaSum_aux1a}
  Apply Lemma \ref{ZetaSum_aux1} with $a=N$ and $b\to \infty$.
\end{proof}
%%-/

/-%%
\begin{definition}[RiemannZeta0]\label{RiemannZeta0}\lean{RiemannZeta0}\leanok
\uses{ZetaSum_aux2}
For any natural $N\ge1$, we define
$$
\zeta_0(N,s) :=
\sum_{1\le n < N} \frac1{n^s}
+
\frac{- N^{1-s}}{1-s} + \frac{-N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
$$
\end{definition}
%%-/
noncomputable def RiemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n in Finset.Icc 1 (N - 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Set.Ici (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1)

/-%%
\begin{lemma}[ZetaBnd_aux1]\label{ZetaBnd_aux1}\lean{ZetaBnd_aux1}\leanok
For any $N\ge1$ and $s\in \C$, $\sigma=\Re(s)\in[1/2,2]$,
$$
\left| s\int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx \right|
\ll |t| \frac{N^{-\sigma}}{\sigma},
$$
as $|t|\to\infty$.
\end{lemma}
%%-/
lemma ZetaBnd_aux1 {N : ℕ} (Npos : 1 ≤ N) {σ : ℝ} (σ_ge : 1 / 2 ≤ σ) (σ_le : σ ≤ 2) :
    (fun (t : ℝ) ↦ Complex.abs ((σ + t * I) *
      ∫ x in Set.Ici (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^((σ + t * I) + 1)))
      =O[cocompact ℝ] fun (t : ℝ) ↦ |t| * N ^ (-σ) / σ := by
  have := @ZetaSum_aux1a (a := N)
  sorry
/-%%
\begin{proof}\uses{ZetaSum_aux1a}
Apply Lemma \ref{ZetaSum_aux1a} with $a=N$ and $b\to \infty$, and estimate $|s|\ll |t|$.
\end{proof}
%%-/

/-%%
\begin{lemma}[Zeta0EqZeta]\label{Zeta0EqZeta}\lean{Zeta0EqZeta}\leanok
For $\Re(s)>0$, $s\ne1$, and for any $N$,
$$
\zeta_0(N,s) = \zeta(s).
$$
\end{lemma}
%%-/
lemma Zeta0EqZeta (N : ℕ) (s : ℂ) (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    RiemannZeta0 N s = riemannZeta s := by
  sorry
/-%%
\begin{proof}
\uses{ZetaSum_aux2, RiemannZeta0, ZetaBnd_aux1, ZetaBndAux}
Use Lemma \ref{ZetaSum_aux2} and the Definition \ref{RiemannZeta0}.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaBnd_aux2]\label{ZetaBnd_aux2}\lean{ZetaBnd_aux2}\leanok
Given $n ≤ t$ and $\sigma$ with $1-A/\log t \le \sigma$, we have
that
$$
|n^{-s}| \le n^{-1} e^A.
$$
\end{lemma}
%%-/
lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ t)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    Complex.abs (n ^ (-(σ + t * I))) ≤ (n : ℝ)⁻¹ * Real.exp A := by
  by_cases n0 : n = 0
  · simp [n0]
    sorry
  sorry
/-%%
\begin{proof}
Use $|n^{-s}| = n^{-\sigma}
= e^{-\sigma \log n}
\le
\exp(-\left(1-\frac{A}{\log t}\right)\log n)
\le
n^{-1} e^A$,
since $n\le t$.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaUpperBnd]\label{ZetaUpperBnd}\lean{ZetaUpperBnd}\leanok
For any $s\in \C$, $1/2 \le \Re(s)=\sigma\le 2$,
and any $A>0$ sufficiently small, and $1-A/\log t \le \sigma$, we have
$$
|\zeta(s)| \ll \log t,
$$
as $|t|\to\infty$.
\end{lemma}
%%-/
lemma ZetaUpperBnd :
    ∃ (A : ℝ) (Apos : 0 < A) (C : ℝ) (Cpos : 0 < C), ∀ (σ : ℝ) (t : ℝ) (t_ge : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (σ_le : σ ≤ 2),
    Complex.abs (riemannZeta (σ + t * I)) ≤ C * Real.log |t| := by
  refine ⟨1/2, by norm_num, 10, by norm_num, ?_⟩ -- placeholder values for `A` and `C`
  intro σ t t_ge σ_ge σ_le
  set N := ⌊ Real.log |t| ⌋₊
  have σPos :  0 < (↑σ + ↑t * I).re := by
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    have : 1 < Real.log |t| := by
      sorry
    -- nlinarith
    sorry
  have neOne : ↑σ + ↑t * I ≠ 1 := by
    sorry
  rw [← Zeta0EqZeta N (σ + t * I) σPos neOne]
  sorry
/-%%
\begin{proof}\uses{ZetaBnd_aux1, ZetaBnd_aux2}
First replace $\zeta(s)$ by $\zeta_0(N,s)$ for $N = \lfloor |t| \rfloor$.
We estimate:
$$
|\zeta_0(N,s)| \ll
\sum_{1\le n < |t|} |n^{-s}|
+
\frac{- |t|^{1-\sigma}}{|1-s|} + \frac{-|t|^{-\sigma}}{2} +
|t| * |t| ^ (-σ) / σ
$$
$$
\ll
e^A \sum_{1\le n < |t|} n^{-1}
+|t|^{1-\sigma}
$$
,
where we used Lemma \ref{ZetaBnd_aux2} and Lemma \ref{ZetaBnd_aux1}.
The first term is $\ll \log |t|$.
For the second term, estimate
$$
|t|^{1-\sigma}
\le |t|^{1-(1-A/\log |t|)}
= |t|^{A/\log |t|} \ll 1.
$$
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaDerivUpperBnd]\label{ZetaDerivUpperBnd}\lean{ZetaDerivUpperBnd}\leanok
For any $s\in \C$, $1/2 \le \Re(s)=\sigma\le 2$,
there is an $A>0$ so that for $1-A/\log t \le \sigma$, we have
$$
|\zeta'(s)| \ll \log^2 t,
$$
as $|t|\to\infty$.
\end{lemma}
%%-/
lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (Apos : 0 < A) (C : ℝ) (Cpos : 0 < C), ∀ (σ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (σ_le : σ ≤ 2),
    Complex.abs (deriv riemannZeta (σ + t * I)) ≤ C * (Real.log |t|) ^ 2 := by
  sorry
/-%%
\begin{proof}\uses{ZetaBnd_aux1, ZetaBnd_aux2}
First replace $\zeta(s)$ by $\zeta_0(N,s)$ for $N = \lfloor |t| \rfloor$.
Differentiating term by term, we get:
$$
\zeta'(s) = -\sum_{1\le n < N} n^{-s} \log n
-
\frac{N^{1 - s}}{1 - s)^2} + \frac{N^{1 - s} \log N} {1 - s}
+ \frac{-N^{-s}\log N}{2} +
\int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
-
s(s+1) \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+2}} \, dx
.
$$
Estimate as before, with an extra factor of $\log |t|$.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaNear1Bnd]\label{ZetaNear1Bnd}\lean{ZetaNear1Bnd}\leanok
As $\sigma\to1^+$,
$$
|\zeta(\sigma)| \ll 1/(\sigma-1).
$$
\end{lemma}
%%-/
lemma ZetaNear1Bnd :
    (fun σ : ℝ ↦ riemannZeta σ) =O[𝓝[>](1 : ℝ)] (fun σ ↦ (1 : ℂ) / (σ - 1)) := by
  have : Tendsto (fun (x : ℝ) ↦ x - 1) (𝓝[>](1 : ℝ)) (𝓝[>](0 : ℝ)) := by
    refine tendsto_iff_forall_eventually_mem.mpr ?_
    intro s hs
    sorry
  have := riemannZeta_isBigO_near_one_horizontal.comp_tendsto this
  convert this using 1 <;> {ext1 _; simp}
/-%%
\begin{proof}\uses{ZetaBnd_aux1, Zeta0EqZeta}
Zeta has a simple pole at $s=1$. Equivalently, $\zeta(s)(s-1)$ remains bounded near $1$.
Lots of ways to prove this.
Probably the easiest one: use the expression for $\zeta_0 (N,s)$ with $N=1$ (the term $N^{1-s}/(1-s)$ being the only unbounded one).
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaInvBound1]\label{ZetaInvBound1}\lean{ZetaInvBound1}\leanok
For all $\sigma>1$,
$$
1/|\zeta(\sigma+it)| \le |\zeta(\sigma)|^{3/4}|\zeta(\sigma+2it)|^{1/4}
$$
\end{lemma}
%%-/
lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / Complex.abs (riemannZeta (σ + t * I)) ≤
      Complex.abs (riemannZeta σ) ^ ((3 : ℝ) / 4) *
        Complex.abs (riemannZeta (σ + 2 * t * I)) ^ ((1 : ℝ) / 4) := by
  sorry -- use `norm_zeta_product_ge_one`
/-%%
\begin{proof}
The identity
$$
1 \le |\zeta(\sigma)|^3 |\zeta(\sigma+it)|^4 |\zeta(\sigma+2it)|
$$
for $\sigma>1$
is already proved by Michael Stoll in the EulerProducts PNT file.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaInvBound2]\label{ZetaInvBound2}\lean{ZetaInvBound2}\leanok
For $\sigma>1$ (and $\sigma \le 2$),
$$
1/|\zeta(\sigma+it)| \ll (\sigma-1)^{3/4}(\log |t|)^{1/4},
$$
as $|t|\to\infty$.
\end{lemma}
%%-/
lemma ZetaInvBound2 {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    (fun (t : ℝ) ↦ 1 / Complex.abs (riemannZeta (σ + t * I))) =O[cocompact ℝ]
      fun (t : ℝ) ↦ (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  sorry
/-%%
\begin{proof}\uses{ZetaInvBound1, ZetaNear1Bnd, ZetaUpperBnd}
Combine Lemma \ref{ZetaInvBound1} with the bounds in Lemmata \ref{ZetaNear1Bnd} and
\ref{ZetaUpperBnd}.
\end{proof}
%%-/

/-%%
\begin{lemma}[Zeta_eq_int_derivZeta]\label{Zeta_eq_int_derivZeta}\lean{Zeta_eq_int_derivZeta}
\leanok
For any $t\ne0$ (so we don't pass through the pole), and $\sigma_1 < \sigma_2$,
$$
\int_{\sigma_1}^{\sigma_2}\zeta'(\sigma + it) dt =
\zeta(\sigma_2+it) - \zeta(\sigma_1+it).
$$
\end{lemma}
%%-/
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (σ₁_lt_σ₂ : σ₁ < σ₂) (t_ne_zero : t ≠ 0) :
    (∫ σ in Set.Icc σ₁ σ₂, deriv riemannZeta (σ + t * I)) =
      riemannZeta (σ₂ + t * I) - riemannZeta (σ₁ + t * I) := by
  sorry
/-%%
\begin{proof}
This is the fundamental theorem of calculus.
\end{proof}
%%-/

/-%%
\begin{lemma}[Zeta_diff_Bnd]\label{Zeta_diff_Bnd}\lean{Zeta_diff_Bnd}\leanok
For any $A>0$ sufficiently small, there is a constant $C>0$ so that
whenever $1- A / \log t \le \sigma_1 < \sigma_2\le 2$, we have that:
$$
|\zeta (\sigma_2 + it) - \zeta (\sigma_1 + it)|
\le C (\log |t|)^2 (\sigma_2 - \sigma_1).
$$
\end{lemma}
%%-/
lemma Zeta_diff_Bnd :
    ∃ (A : ℝ) (Apos : 0 < A) (C : ℝ) (Cpos : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (σ₁_ge : 1 - A / Real.log |t| ≤ σ₁) (σ₁_le : σ₁ ≤ 2)
    (σ₂_ge : 1 - A / Real.log |t| ≤ σ₂) (σ₂_le : σ₂ ≤ 2) (σ₁_lt_σ₂ : σ₁ < σ₂),
    Complex.abs (riemannZeta (σ₂ + t * I) - riemannZeta (σ₁ + t * I)) ≤
      C * (Real.log |t|) ^ 2 * (σ₂ - σ₁) := by
  obtain ⟨A, Apos, C, Cpos, hC⟩ := ZetaDerivUpperBnd
  refine ⟨A, Apos, C, Cpos, ?_⟩
  intro σ₁ σ₂ t t_gt σ₁_ge σ₁_le σ₂_ge σ₂_le σ₁_lt_σ₂
  have : t ≠ 0 := by sorry
  rw [← Zeta_eq_int_derivZeta σ₁_lt_σ₂ this]
  sorry
/-%%
\begin{proof}
\uses{Zeta_eq_int_derivZeta, ZetaDerivUpperBnd}
Use Lemma \ref{Zeta_eq_int_derivZeta} and
estimate trivially using Lemma \ref{ZetaDerivUpperBnd}.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaInvBnd]\label{ZetaInvBnd}\lean{ZetaInvBnd}\leanok
For any $A>0$ sufficiently small, there is a constant $C>0$ so that
whenever $1- A / \log^9 |t| \le \sigma < 1$, we have that:
$$
1/|\zeta(\sigma+it)| \le C \log^7 |t|.
$$
\end{lemma}
%%-/
lemma ZetaInvBnd :
    ∃ (A : ℝ) (Apos : 0 < A) (C : ℝ) (Cpos : 0 < C), ∀ (σ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / (Real.log |t|) ^ 9 ≤ σ) (σ_lt : σ < 1),
    1 / Complex.abs (riemannZeta (σ + t * I)) ≤ C * (Real.log |t|) ^ 7 := by
  sorry
/-%%
\begin{proof}
\uses{Zeta_diff_Bnd, ZetaInvBound2}
Let $\sigma$ be given in the prescribed range, and set $\sigma' := 1+ A / \log^9 |t|$.
Then
$$
|\zeta(\sigma+it)| \ge
|\zeta(\sigma'+it)| - |\zeta(\sigma+it) - \zeta(\sigma'+it)|
\ge
C (\sigma'-1)^{-3/4}\log |t|^{-1/4} - C \log^2 |t| (\sigma'-\sigma)
$$
$$
\ge
C A^{-3/4} \log |t|^{-7} - C \log^2 |t| (2 A / \log^9 |t|),
$$
where we used Lemma \ref{ZetaInvBound2}  and Lemma \ref{Zeta_diff_Bnd}.
Now by making $A$ sufficiently small (in particular, something like $A = 1/16$ should work), we can guarantee that
$$
|\zeta(\sigma+it)| \ge \frac C 2 (\log |t|)^{-7},
$$
as desired.
\end{proof}
%%-/

/-%%
\begin{lemma}[LogDerivZetaBnd]\label{LogDerivZetaBnd}\lean{LogDerivZetaBnd}\leanok
There is an $A>0$ so that for $1-A/\log^9 |t| \le \sigma < 1$,
$$
|\frac {\zeta'}{\zeta} (\sigma+it)| \ll \log^9 |t|.
$$
\end{lemma}
%%-/
lemma LogDerivZetaBnd :
    ∃ (A : ℝ) (Apos : 0 < A) (C : ℝ) (Cpos : 0 < C), ∀ (σ : ℝ) (t : ℝ) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / (Real.log |t|) ^ 9 ≤ σ) (σ_lt : σ < 1),
    Complex.abs (deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)) ≤
      C * (Real.log |t|) ^ 9 := by
  obtain ⟨A, hA, C, hC, h⟩ := ZetaInvBnd
  obtain ⟨A', hA', C', hC', h'⟩ := ZetaDerivUpperBnd
  use min A A', lt_min hA hA', C * C', mul_pos hC hC'
  intro σ t t_gt σ_ge σ_lt
  have logt_gt : (1 : ℝ) < Real.log |t| := by
    refine (Real.lt_log_iff_exp_lt (by linarith)).mpr (lt_trans ?_ t_gt)
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have σ_ge' : 1 - A / Real.log |t| ^ 9 ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div hA.le (min_le_left A A') ?_ (by rfl)
    exact pow_pos (lt_trans (by norm_num) logt_gt) 9
  have σ_ge'' : 1 - A' / Real.log |t| ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div hA'.le (min_le_right A A') (lt_trans (by norm_num) logt_gt) ?_
    exact le_self_pow logt_gt.le (by norm_num)
  replace h := h σ t t_gt σ_ge' σ_lt
  replace h' := h' σ t t_gt σ_ge'' (by linarith)
  simp only [map_div₀]
  convert mul_le_mul h h' (by simp [apply_nonneg]) ?_ using 1 <;> ring_nf
  exact le_trans (by simp only [one_div, inv_nonneg, apply_nonneg]) h
/-%%
\begin{proof}\leanok
\uses{ZetaInvBnd, ZetaDerivUpperBnd}
Combine the bound on $|\zeta'|$ from Lemma \ref{ZetaDerivUpperBnd} with the bound on $1/|\zeta|$ from Lemma \ref{ZetaInvBnd}.
\end{proof}
%%-/
