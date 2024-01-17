import PrimeNumberTheoremAnd.EulerProducts.LSeries
import PrimeNumberTheoremAnd.EulerProducts.Logarithm

/-!
### Auxiliary stuff
-/

lemma DifferentiableAt.bounded_near_root {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hz : f z = 0) :
    ∃ ε > 0, ∃ C > 0, ∀ w : ℂ, ‖w‖ < ε → ‖f (z + w)‖ ≤ C * ‖w‖ := by
  have H := hz ▸ hf.isBigO_sub
  rw [Asymptotics.isBigO_iff'] at H
  obtain ⟨C, hC, H⟩ := H
  rw [Metric.eventually_nhds_iff] at H
  obtain ⟨ε, hε, H⟩ := H
  refine ⟨ε, hε, C, hC, fun w hw ↦ ?_⟩
  convert H (y := z + w) ?_ using 2
  · exact (sub_zero _).symm
  · simp only [add_sub_cancel']
  · simp only [dist_self_add_left, hw]

/-!
### Statement of a version of the Wiener-Ikehara Theorem
-/

open Filter Nat ArithmeticFunction in
/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/
def WienerIkeharaTheorem : Prop :=
  ∀ {f : ArithmeticFunction ℝ} {A : ℝ} {F : ℂ → ℂ}, (∀ n, 0 ≤ f n) →
    Set.EqOn F (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re} →
    ContinuousOn F {s | 1 ≤ s.re} →
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum f) / N) atTop (nhds A)

/-!
### The Riemann Zeta Function does not vanish on Re(s) = 1
-/

open Complex

local notation (name := rzeta) "ζ" => riemannZeta

lemma summable_neg_log_one_sub_prime_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ -log (1 - (p : ℂ) ^ (-s)) := by
  refine Summable.neg_log_one_sub <| Summable.of_norm ?_
  conv => enter [1, a]; rw [norm_ofNat_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
  refine Nat.Primes.summable_rpow.mpr ?_
  simp only [neg_re, neg_lt_neg_iff, hs]

lemma log_re_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
      0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1
  · simp only [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1
  · rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1
  · rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  have H₀ := (Complex.hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3
  have H₁ := (Complex.hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4
  have H₂ := Complex.hasSum_re <| hasSum_taylorSeries_neg_log hac₂
  rw [← ((H₀.add H₁).add H₂).tsum_eq]; clear H₀ H₁ H₂
  refine tsum_nonneg fun n ↦ ?_
  simp_rw [mul_pow, ← ofReal_pow]
  simp only [div_nat_cast_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have Hz : (z ^ n).im ^ 2 = 1 - (z ^ n).re ^ 2
  · rw [← sq_abs_sub_sq_re, ← norm_eq_abs, norm_pow, hz, one_pow, one_pow]
  field_simp
  refine div_nonneg ?_ n.cast_nonneg
  rw [mul_comm 3, ← mul_assoc, mul_comm 4, mul_assoc, ← mul_add, ← mul_add]
  refine mul_nonneg (pow_nonneg ha₀ n) ?_
  rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, Hz]
  rw [show 3 + 4 * (z ^ n).re + ((z ^ n).re ^ 2 - (1 - (z ^ n).re ^ 2)) = 2 * ((z ^ n).re + 1) ^ 2
    by ring]
  positivity

lemma log_re_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (hx : 1 < x) (hy : y ≠ 0) :
    0 ≤ 3 * (-log (1 - n ^ (-x : ℂ))).re + 4 * (-log (1 - n ^ (-(x + I * y)))).re +
          (-log (1 - n ^ (-(x + 2 * I * y)))).re := by
  have ha₀ : 0 ≤ (n : ℝ) ^ (-x) := sorry --Real.rpow_nonneg_of_nonneg n.cast_nonneg _
  have ha₁ : (n : ℝ) ^ (-x) < 1
  · simpa only [Real.rpow_lt_one_iff n.cast_nonneg, Nat.cast_eq_zero, Nat.one_lt_cast,
    Left.neg_neg_iff, Nat.cast_lt_one, Left.neg_pos_iff] using
      Or.inr <| Or.inl ⟨hn, zero_lt_one.trans hx⟩
  have hz : ‖(n : ℂ) ^ (-(I * y))‖ = 1
  · rw [norm_eq_abs, abs_cpow_of_imp fun h ↦ False.elim <| by linarith [Nat.cast_eq_zero.mp h, hn]]
    simp [hy]
  convert log_re_comb_nonneg' ha₀ ha₁ hz using 6
  · congr 2
    exact_mod_cast (ofReal_cpow n.cast_nonneg (-x)).symm
  · congr 2
    rw [neg_add, cpow_add _ _ <| by norm_cast; linarith, ← ofReal_neg]
    congr 1
    exact (ofReal_cpow n.cast_nonneg (-x)).symm
  · rw [neg_add, cpow_add _ _ <| by norm_cast; linarith, ← ofReal_neg]
    congr 1
    · exact (ofReal_cpow n.cast_nonneg (-x)).symm
    · rw [mul_assoc, ← mul_neg, show (2 : ℂ) = (2 : ℕ) from rfl, cpow_nat_mul]

lemma norm_zeta_product_ge_one {x y : ℝ} (hx : 1 < x) (hy : y ≠ 0) :
    ‖ζ x ^ 3 * ζ (x + I * y) ^ 4 * ζ (x + 2 * I * y)‖ ≥ 1 := by
  have h₀ : 1 < (x : ℂ).re
  · simp only [ofReal_re, hx]
  have h₁ : 1 < (x + I * y).re
  · simp [hx]
  have h₂ : 1 < (x + 2 * I * y).re
  · simp [hx]
  have hsum₀ := (summable_re <| summable_neg_log_one_sub_prime_cpow h₀).mul_left 3
  have hsum₁ := (summable_re <| summable_neg_log_one_sub_prime_cpow h₁).mul_left 4
  have hsum₂ := summable_re <| summable_neg_log_one_sub_prime_cpow h₂
  repeat rw [← riemannZeta_eulerProduct' <| by assumption]
  rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add, norm_eq_abs, abs_exp]
  simp only [Nat.cast_ofNat, add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
    Real.one_le_exp_iff]
  rw [re_tsum <| summable_neg_log_one_sub_prime_cpow h₀,
    re_tsum <| summable_neg_log_one_sub_prime_cpow h₁,
    re_tsum <| summable_neg_log_one_sub_prime_cpow h₂, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_add hsum₀ hsum₁, ← tsum_add (hsum₀.add hsum₁) hsum₂]
  exact tsum_nonneg fun p ↦ log_re_comb_nonneg p.prop.two_le hx hy

lemma riemannZeta_bounded_near_one : ∃ ε > 0, ∀ w, ‖w‖ < ε → ‖ζ (1 + w) * w‖ ≤ 2 := by
  have := riemannZeta_residue_one
  rw [Metric.tendsto_nhdsWithin_nhds] at this
  obtain ⟨ε, hε, H⟩ := this 1 zero_lt_one
  refine ⟨ε, hε, fun w hw ↦ ?_⟩
  rw [mul_comm]
  rcases eq_or_ne w 0 with rfl | h
  · simp [zero_le_two]
  conv => enter [1, 1]; rw [←sub_add_cancel (w * _) 1]
  refine (norm_add_le ..).trans ?_
  rw [norm_one, ← le_sub_iff_add_le]
  convert (H (x := 1 + w) ?_ ?_).le using 1
  · rw [dist_eq_norm_sub, add_sub_cancel']
  · norm_num
  · simp [h]
  · rwa [dist_eq_norm_sub, add_sub_cancel']

lemma riemannZeta_locally_bounded_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    ∃ ε > 0, ∃ C > 0, ∀ w : ℂ, ‖w‖ < ε → ‖ζ (z + w)‖ ≤ C := by
  have := (differentiableAt_riemannZeta hz).continuousAt
  rw [Metric.continuousAt_iff] at this
  obtain ⟨ε, hε, H⟩ := this 1 zero_lt_one
  refine ⟨ε, hε, ‖ζ z‖ + 1, by positivity, fun w hw ↦ ?_⟩
  have h : dist (z + w) z < ε
  · simpa [dist_self_add_left] using hw
  specialize H h
  refine (norm_le_norm_add_norm_sub (ζ z) _).trans <| add_le_add_left ?_ _
  rw [norm_sub_rev]
  exact H.le

open Filter Topology in
/-- The Riemann Zeta Function does not vanish on the closed half-plane `re z ≥ 1`. -/
lemma zeta_ne_zero_of_one_le_re ⦃z : ℂ⦄ (hz : z ≠ 1) (hz' : 1 ≤ z.re) : ζ z ≠ 0 := by
  refine hz'.eq_or_lt.elim (fun h H ↦ ?_) riemannZeta_ne_zero
  -- We assume that `ζ z = 0` and `z.re = 1` and derive a contradiction.
  have hz₀ : z.im ≠ 0
  · rw [← re_add_im z, ← h, ofReal_one] at hz
    simpa only [ne_eq, add_right_eq_self, mul_eq_zero, ofReal_eq_zero, I_ne_zero, or_false]
      using hz
  have hxy : 1 + 2 * I * z.im ≠ 1
  · simp [hz₀, I_ne_zero]
  -- The key step: the vanishing assumption implies that the zeta product below
  -- also vanishes at `z`. We only need the right-hand limit keeping the imaginary part fixed.
  obtain ⟨δ, hδ₀, hδ⟩ : ∃ δ > 0, ∀ {x : ℝ}, 1 < x → x - 1 < δ →
      ‖ζ ↑x ^ 3 * ζ (↑x + I * ↑z.im) ^ 4 * ζ (↑x + 2 * I * ↑z.im)‖ ≤ 1 / 2
  · obtain ⟨ε, hε₀, C, hC₀, H₁⟩ := (differentiableAt_riemannZeta hz).bounded_near_root H
    obtain ⟨ε', hε'₀, C', hC'₀, H₂⟩ := riemannZeta_locally_bounded_of_ne_one hxy
    obtain ⟨ε'', hε''₀, H₃⟩ := riemannZeta_bounded_near_one
    let δ := min (min ε'' (1 / (16 * C ^ 4 * C'))) (min ε ε')
    refine ⟨δ, by positivity, fun {x} hx hxδ ↦ ?_⟩
    have hx₁ := sub_pos.mpr hx
    have hxn : ‖(x - 1 : ℂ)‖ = x - 1
    ·  rw [← ofReal_one, ← ofReal_sub, norm_eq_abs, abs_ofReal, abs_of_pos hx₁]
    have Hx₀ : 0 < ‖(x - 1 : ℂ)‖ ^ 3 := hxn.symm ▸ pow_pos hx₁ 3
    have Hx₁ : ‖(x - 1 : ℂ)‖ < ε :=
      hxn.symm ▸ hxδ.trans_le <| (min_le_right ..).trans <| min_le_left ..
    have Hx₂ : ‖(x - 1 : ℂ)‖ < ε' :=
      hxn.symm ▸ hxδ.trans_le <| (min_le_right ..).trans <| min_le_right ..
    have Hx₃ : ‖(x - 1 : ℂ)‖ < ε'' :=
      hxn.symm ▸ hxδ.trans_le <| (min_le_left ..).trans <| min_le_left ..
    have Hx₄ : ‖(x - 1 : ℂ)‖ < 1 / (16 * C ^ 4 * C') :=
      hxn.symm ▸ hxδ.trans_le <| (min_le_left ..).trans <| min_le_right ..
    -- The point is that the quadruple zero of the second factor over-compensates
    -- the triple pole of the first.
    rw [show ζ x ^ 3 * ζ (x + I * z.im) ^ 4 =
          ζ x ^ 3 * (x - 1) ^ 3 * (ζ (x + I * z.im) ^ 4 / (x - 1) ^ 3)
        by field_simp [sub_ne_zero.mpr (ofReal_ne_one.mpr hx.ne')]; ring,
      norm_mul, norm_mul, ← mul_pow, norm_pow]
    calc ‖ζ x * (x - 1)‖ ^ 3 * ‖ζ (x + I * z.im) ^ 4 / (x - 1) ^ 3‖ * ‖ζ (x + 2 * I * z.im)‖
      _ ≤ 2 ^ 3 * (C ^ 4 * ‖(x - 1 : ℂ)‖) * C' := by
          gcongr
          · convert H₃ (x - 1) Hx₃ using 1
            simp only [add_sub_cancel'_right]
          · rw [norm_div, norm_pow, norm_pow, div_le_iff Hx₀, mul_assoc, ← pow_succ, ← mul_pow]
            refine pow_le_pow_left (norm_nonneg _) ?_ 4
            convert H₁ (x - 1) Hx₁ using 3
            rw [← re_add_im z, ← h]
            simp only [ofReal_one, add_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
              I_re, mul_zero, add_zero, zero_add]
            ring
          · convert H₂ (x - 1) Hx₂ using 3
            ring
      _ = 8 * C ^ 4 * C' * ‖(x - 1 : ℂ)‖ := by ring
      _ ≤ 8 * C ^ 4 * C' * (1 / (16 * C ^ 4 * C')) := by gcongr
      _ = 1 / 2 := by field_simp; ring
  have hδ' : 1 + δ / 2 ∈ Set.Ioi 1
  · simp only [Set.mem_Ioi, lt_add_iff_pos_right, half_pos hδ₀]
  have hδ'' : (1 + δ / 2) - 1 < δ
  · linarith only [hδ₀]
  exact (((norm_zeta_product_ge_one hδ' hz₀).le.trans <| hδ hδ' hδ'').trans_lt
    one_half_lt_one).false

/-!
### The logarithmic derivative of ζ has a simple pole at s = 1 with residue -1

We show that `s ↦ ζ' s / ζ s + 1 / (s - 1)` (or rather, its negative, which is the function
we need for the Wiener-Ikehara Theorem) is continuous outside the zeros of `ζ`.
-/

/-- The function obtained by "multiplying away" the pole of `ζ`. Its (negative) logarithmic
derivative is the function used in the Wiener-Ikehara Theorem to prove the Prime Number
Theorem. -/
noncomputable def ζ₁ : ℂ → ℂ := Function.update (fun z ↦ ζ z * (z - 1)) 1 1

lemma ζ₁_apply_of_ne_one {z : ℂ} (hz : z ≠ 1) : ζ₁ z = ζ z * (z - 1) := by
  simp [ζ₁, hz]

lemma ζ₁_differentiable : Differentiable ℂ ζ₁ := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨?_, ?_⟩
  · simp only [ζ₁]
    refine DifferentiableOn.congr (f := fun z ↦ ζ z * (z - 1)) ?_ ?_
    · intros z hz
      refine DifferentiableAt.differentiableWithinAt ?_
      simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hz
      exact (differentiableAt_riemannZeta hz).mul <| (differentiableAt_id').sub <|
        differentiableAt_const 1
    · intros z hz
      simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hz
      simp only [ne_eq, hz, not_false_eq_true, Function.update_noteq]
  · refine continuousWithinAt_compl_self.mp ?_
    simp only [ζ₁]
    conv in (_ * _) => rw [mul_comm]
    simp only [continuousWithinAt_compl_self, continuousAt_update_same]
    exact riemannZeta_residue_one

lemma deriv_ζ₁_apply_of_ne_one  {z : ℂ} (hz : z ≠ 1) :
    deriv ζ₁ z = deriv ζ z * (z - 1) + ζ z := by
  have H : deriv ζ₁ z = deriv (fun w ↦ ζ w * (w - 1)) z
  · refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{w | w ≠ 1}, IsOpen.mem_nhds isOpen_ne hz, fun w hw ↦ ?_⟩
    simp only [ζ₁, ne_eq, Set.mem_setOf.mp hw, not_false_eq_true, Function.update_noteq]
  rw [H, deriv_mul (differentiableAt_riemannZeta hz) <|
    DifferentiableAt.sub differentiableAt_id' <| differentiableAt_const 1,
    deriv_sub_const, deriv_id'', mul_one]

lemma neg_logDeriv_ζ₁_eq {z : ℂ} (hz₁ : z ≠ 1) (hz₂ : ζ z ≠ 0) :
    -deriv ζ₁ z / ζ₁ z = -deriv ζ z / ζ z - 1 / (z - 1) := by
  rw [ζ₁_apply_of_ne_one hz₁, deriv_ζ₁_apply_of_ne_one hz₁]
  field_simp [sub_ne_zero.mpr hz₁]
  ring

lemma continuousOn_neg_logDeriv_ζ₁ :
    ContinuousOn (fun z ↦ -deriv ζ₁ z / ζ₁ z) {z | z = 1 ∨ ζ z ≠ 0} := by
  simp_rw [neg_div]
  refine ContinuousOn.neg ?_
  refine ContinuousOn.div ?_ ?_ ?_
  · refine Continuous.continuousOn <| ContDiff.continuous_deriv ?_ le_rfl
    exact Differentiable.contDiff ζ₁_differentiable
  · exact Continuous.continuousOn <| Differentiable.continuous ζ₁_differentiable
  · intro w hw
    rcases eq_or_ne w 1 with rfl | hw'
    · simp only [ζ₁, Function.update_same, ne_eq, one_ne_zero, not_false_eq_true]
    · simp only [ne_eq, Set.mem_setOf_eq, hw', false_or] at hw
      simp only [ζ₁, ne_eq, hw', not_false_eq_true, Function.update_noteq, _root_.mul_eq_zero, hw,
        false_or]
      exact sub_ne_zero.mpr hw'

/-!
### Derivation of the Prime Number Theorem from the Wiener-Ikehara Theorem
-/

open Filter Nat ArithmeticFunction in
/-- The *Wiener-Ikehara Theorem* implies the *Prime Number Theorem* in the form that
`ψ x ∼ x`, where `ψ x = ∑ n < x, Λ n` and `Λ` is the von Mangoldt function. -/
theorem PNT_vonMangoldt (WIT : WienerIkeharaTheorem) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (nhds 1) := by
  have hnv := zeta_ne_zero_of_one_le_re
  refine WIT (F := fun z ↦ -deriv ζ₁ z / ζ₁ z) (fun _ ↦ vonMangoldt_nonneg) (fun s hs ↦ ?_) ?_
  · have hs₁ : s ≠ 1
    · rintro rfl
      simp at hs
    simp only [ne_eq, hs₁, not_false_eq_true, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
      ofReal_one]
    exact neg_logDeriv_ζ₁_eq hs₁ <| hnv hs₁ (Set.mem_setOf.mp hs).le
  · refine continuousOn_neg_logDeriv_ζ₁.mono fun s _ ↦ ?_
    specialize @hnv s
    simp at *
    tauto
