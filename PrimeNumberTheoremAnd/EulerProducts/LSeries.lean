import PrimeNumberTheoremAnd.EulerProducts.Auxiliary
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.LSeries
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.InfiniteSum

/-!
# More results on L-series
-/

/-!
### Coercion from real-valued to complex-valued arithmetic functions
-/

namespace Nat.ArithmeticFunction

open Complex

/-- Coerce an arithmetic function with values in `ℝ` to one with values in `ℂ`.
We cannot inline this in `intCoe` because it gets unfolded too much. -/
@[coe] def ofReal (f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ where
  toFun n := f n
  map_zero' := by simp only [map_zero, ofReal_zero]

instance realCoe : Coe (ArithmeticFunction ℝ) (ArithmeticFunction ℂ) := ⟨ofReal⟩

@[simp]
lemma realCoe_apply {f : ArithmeticFunction ℝ} {n : ℕ} :
    (f : ArithmeticFunction ℂ) n = f n := rfl

lemma ofReal_injective : Function.Injective ofReal := by
  intro f g hfg
  ext n
  simpa only [realCoe_apply, ofReal_inj] using congr_arg (· n) hfg

@[simp, norm_cast]
lemma ofReal_inj {f g : ArithmeticFunction ℝ} : ofReal f = ofReal g ↔ f = g :=
  ofReal_injective.eq_iff

-- Is there a simpler way for the following?
-- (And do we have to repeat this for addition etc.?)

@[simp, norm_cast]
lemma realCoe_mul {f g : ArithmeticFunction ℝ} :
    (↑(f * g) : ArithmeticFunction ℂ) = ↑f * g := by
  ext n
  simp

@[simp, norm_cast]
lemma realCoe_natCoe_mul {f : ArithmeticFunction ℝ} {g : ArithmeticFunction ℕ} :
    (↑(f * g) : ArithmeticFunction ℂ) = ↑f * g := by
  ext n
  simp

@[simp, norm_cast]
lemma natCoe_realCoe_mul {f : ArithmeticFunction ℕ} {g : ArithmeticFunction ℝ} :
    (↑(f * g) : ArithmeticFunction ℂ) = ↑f * g := by
  ext n
  simp

@[simp, norm_cast]
lemma realCoe_intCoe_mul {f : ArithmeticFunction ℝ} {g : ArithmeticFunction ℤ} :
    (↑(f * g) : ArithmeticFunction ℂ) = ↑f * g := by
  ext n
  simp

@[simp, norm_cast]
lemma intCoe_realCoe_mul {f : ArithmeticFunction ℤ} {g : ArithmeticFunction ℝ} :
    (↑(f * g) : ArithmeticFunction ℂ) = ↑f * g := by
  ext n
  simp

@[simp, norm_cast]
lemma realCoe_pmul {f g : ArithmeticFunction ℝ} :
    (↑(pmul f g) : ArithmeticFunction ℂ) = pmul (ofReal f) g := by
  ext n
  simp

@[simp, norm_cast]
lemma realCoe_natCoe_pmul {f : ArithmeticFunction ℝ} {g : ArithmeticFunction ℕ} :
    (↑(pmul f g) : ArithmeticFunction ℂ) = pmul (ofReal f) g := by
  ext n
  simp

@[simp, norm_cast]
lemma natCoe_realCoe_pmul {f : ArithmeticFunction ℕ} {g : ArithmeticFunction ℝ} :
    (↑(pmul (f : ArithmeticFunction ℝ) g) : ArithmeticFunction ℂ) = pmul (ofReal f) g := by
  ext n
  simp

@[simp, norm_cast]
lemma realCoe_intCoe_pmul {f : ArithmeticFunction ℝ} {g : ArithmeticFunction ℤ} :
    (↑(pmul f g) : ArithmeticFunction ℂ) = pmul (ofReal f) g := by
  ext n
  simp

@[simp, norm_cast]
lemma intCoe_realCoe_pmul {f : ArithmeticFunction ℤ} {g : ArithmeticFunction ℝ} :
    (↑(pmul (f : ArithmeticFunction ℝ) g) : ArithmeticFunction ℂ) = pmul (ofReal f) g := by
  ext n
  simp

/-!
### Convergence of L-series
-/

lemma LSeriesTerm_norm_eq (f : ArithmeticFunction ℂ) (s : ℂ) (n : ℕ) :
    ‖f n / n ^ s‖ = ‖f n‖ / n ^ s.re := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [map_zero, zero_div, norm_zero, zero_mul]
  rw [norm_div, norm_ofNat_cpow_of_pos hn]

/-- This states that the L-series of the arithmetic function `f` converges at `s` to `a`. -/
def LSeriesHasSum (f : ArithmeticFunction ℂ) (s a : ℂ) : Prop :=
  HasSum (fun (n : ℕ) => f n / n ^ s) a

lemma LSeriesHasSum.LSeriesSummable {f : ArithmeticFunction ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeriesSummable f s :=
  h.summable

lemma LSeriesHasSum.LSeries_eq {f : ArithmeticFunction ℂ} {s a : ℂ}
    (h : LSeriesHasSum f s a) : LSeries f s = a :=
  h.tsum_eq

lemma LSeriesSummable.LSeriesHasSum {f : ArithmeticFunction ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    LSeriesHasSum f s (LSeries f s) :=
  h.hasSum

lemma norm_LSeriesTerm_le_of_re_le_re (f : Nat.ArithmeticFunction ℂ) {w : ℂ} {z : ℂ}
    (h : w.re ≤ z.re) (n : ℕ) : ‖f n / n ^ z‖ ≤ ‖f n / n ^ w‖ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn' := norm_ofNat_cpow_pos_of_pos hn w
  simp_rw [norm_div]
  suffices : ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖
  · exact div_le_div (norm_nonneg _) le_rfl hn' this
  refine (one_le_div hn').mp ?_
  rw [← norm_div, ← cpow_sub _ _ <| Nat.cast_ne_zero.mpr hn.ne', norm_ofNat_cpow_of_pos hn]
  exact Real.one_le_rpow (one_le_cast.mpr hn) <| by simp only [sub_re, sub_nonneg, h]

lemma norm_log_mul_LSeriesTerm_le_of_re_lt_re (f : Nat.ArithmeticFunction ℂ) {w : ℂ} {z : ℂ}
    (h : w.re < z.re) (n : ℕ) :
    ‖log n * f n / n ^ z‖ ≤ (z.re - w.re)⁻¹ * ‖f n / n ^ w‖ := by
  have hwz : 0 < z.re - w.re := sub_pos.mpr h
  rw [mul_div_assoc, norm_mul, log_apply, ofReal_log n.cast_nonneg]
  refine mul_le_mul_of_nonneg_right (norm_log_ofNat_le_rpow n hwz) (norm_nonneg _) |>.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ <| inv_nonneg.mpr hwz.le
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp_rw [norm_div, norm_ofNat_cpow_of_pos hn]
  rw [mul_div_left_comm, ← Real.rpow_sub <| Nat.cast_pos.mpr hn, sub_sub_cancel_left,
    Real.rpow_neg n.cast_nonneg, div_eq_mul_inv]

lemma LSeriesSummable.of_re_le_re {f : Nat.ArithmeticFunction ℂ} {w : ℂ} {z : ℂ} (h : w.re ≤ z.re)
    (hf : LSeriesSummable f w) : LSeriesSummable f z := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_LSeriesTerm_le_of_re_le_re f h)

/-- The abscissa `x : EReal` of absolute convergence of the L-series associated to `f`:
the series converges absolutely at `s` when `re s > x` and does not converge absolutely
when `re s < x`. -/
noncomputable def abscissaOfAbsConv (f : ArithmeticFunction ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | LSeriesSummable f x}

lemma LSeriesSummable_of_abscissaOfAbsConv_lt_re {f : ArithmeticFunction ℂ} {s : ℂ}
    (hs : abscissaOfAbsConv f < s.re) : LSeriesSummable f s := by
  simp only [abscissaOfAbsConv, sInf_lt_iff, Set.mem_image, Set.mem_setOf_eq,
    exists_exists_and_eq_and, EReal.coe_lt_coe_iff] at hs
  obtain ⟨y, hy, hys⟩ := hs
  exact hy.of_re_le_re <| ofReal_re y ▸ hys.le

lemma LSeriesSummable_re_lt_of_abscissaOfAbsConv_lt_re {f : ArithmeticFunction ℂ} {s : ℂ}
    (hs : abscissaOfAbsConv f < s.re) :
    ∃ x : ℝ, x < s.re ∧ LSeriesSummable f x := by
  obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hs
  refine ⟨x, EReal.coe_lt_coe_iff.mp hx₂, LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁⟩

lemma LSeriesSummable.abscissaOfAbsConv_le {f : ArithmeticFunction ℂ} {s : ℂ}
    (h : LSeriesSummable f s) : abscissaOfAbsConv f ≤ s.re := by
  refine sInf_le <| Membership.mem.out ?_
  simp only [Set.mem_setOf_eq, Set.mem_image, EReal.coe_eq_coe_iff, exists_eq_right]
  exact h.of_re_le_re <| by simp only [ofReal_re, le_refl]

lemma abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : ArithmeticFunction ℂ} {x : ℝ}
    (h : ∀ y : ℝ, x < y → LSeriesSummable f y) :
    abscissaOfAbsConv f ≤ x := by
  refine sInf_le_iff.mpr fun y hy ↦ ?_
  simp only [mem_lowerBounds, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hy
  have H (a : EReal) : x < a → y ≤ a
  · induction' a using EReal.rec with a₀
    · simp only [not_lt_bot, le_bot_iff, IsEmpty.forall_iff]
    · exact_mod_cast fun ha ↦ hy a₀ (h a₀ ha)
    · simp only [EReal.coe_lt_top, le_top, forall_true_left]
  exact Set.Ioi_subset_Ici_iff.mp H

lemma abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : ArithmeticFunction ℂ} {x : EReal}
    (h : ∀ y : ℝ, x < y → LSeriesSummable f y) :
    abscissaOfAbsConv f ≤ x := by
  induction' x using EReal.rec with y
  · refine le_of_eq <| sInf_eq_bot.mpr fun y hy ↦ ?_
    induction' y using EReal.rec with z
    · simp only [gt_iff_lt, lt_self_iff_false] at hy
    · refine ⟨z - 1, ?_, by norm_cast; exact sub_one_lt z⟩
      simp only [Set.mem_image, Set.mem_setOf_eq]
      exact ⟨z-1, h (z - 1) <| EReal.bot_lt_coe _, rfl⟩
    · refine ⟨0, ?_, EReal.zero_lt_top⟩
      simp only [Set.mem_image, Set.mem_setOf_eq]
      refine ⟨0, h 0 <| EReal.bot_lt_coe 0, rfl⟩
  · exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable <| by exact_mod_cast h
  · exact le_top

lemma LSeriesSummable.le_const_mul_rpow {f : ArithmeticFunction ℂ} {s : ℂ}
    (h : LSeriesSummable f s) : ∃ C, ∀ n, ‖f n‖ ≤ C * n ^ s.re := by
  replace h := h.norm
  by_contra! H
  obtain ⟨n, hn⟩ := H (tsum fun n ↦ ‖f n / n ^ s‖)
  have hn₀ : 0 < n
  · refine n.eq_zero_or_pos.resolve_left ?_
    rintro rfl
    rw [map_zero, norm_zero, Nat.cast_zero, mul_neg_iff] at hn
    sorry
    -- have hsre := Real.rpow_nonneg_of_nonneg (le_refl 0) s.re
    -- replace hn := hn.resolve_left <| fun hh ↦ hh.2.not_le hsre
    -- exact hn.1.not_le <| tsum_nonneg (fun _ ↦ norm_nonneg _)
  have := le_tsum h n fun _ _ ↦ norm_nonneg _
  rw [LSeriesTerm_norm_eq, div_le_iff <| Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn₀) _] at this
  exact (this.trans_lt hn).false.elim

lemma LSeriesSummable_of_le_const_mul_rpow {f : ArithmeticFunction ℂ} {x : ℝ} {s : ℂ}
    (hs : x < s.re) (h : ∃ C, ∀ n, ‖f n‖ ≤ C * n ^ (x - 1)) :
    LSeriesSummable f s := by
  obtain ⟨C, hC⟩ := h
  have hC₀ : 0 ≤ C
  · specialize hC 1
    simp only [cast_one, Real.one_rpow, mul_one] at hC
    exact (norm_nonneg _).trans hC
  have hsum : Summable fun n : ℕ ↦ ‖(C : ℂ) / n ^ (s + (1 - x))‖
  · simp_rw [div_eq_mul_inv, norm_mul, ← cpow_neg]
    have hsx : -s.re + x - 1 < -1
    · linarith only [hs]
    refine Summable.mul_left _ <|
      Summable.of_norm_bounded_eventually_nat (fun n ↦ (n : ℝ) ^ (-s.re + x - 1)) ?_ ?_
    · simp [hsx]
    · simp only [neg_add_rev, neg_sub, norm_norm, Filter.eventually_atTop]
      refine ⟨1, fun n hn ↦ ?_⟩
      simp only [norm_ofNat_cpow_of_pos hn, add_re, sub_re, neg_re, ofReal_re, one_re]
      convert le_refl ?_ using 2
      ring
  refine Summable.of_norm <| Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hsum
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [map_zero, zero_div, norm_zero, norm_nonneg]
  have hn' : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  simp_rw [norm_div, norm_ofNat_cpow_of_pos hn,
    div_le_iff hn', add_re, sub_re, one_re, ofReal_re,
    Real.rpow_add <| Nat.cast_pos.mpr hn, div_eq_mul_inv, mul_inv]
  rw [mul_assoc, mul_comm _ ((n : ℝ) ^ s.re), ← mul_assoc ((n : ℝ) ^ s.re), mul_inv_cancel hn'.ne',
    ← Real.rpow_neg n.cast_nonneg, norm_eq_abs (C : ℂ), abs_ofReal, _root_.abs_of_nonneg hC₀,
    neg_sub, one_mul]
  exact hC n

/-- If `‖f n‖` is bounded by a constant times `n^x`, then the abscissa of absolute convergence
of `f` is bounded by `x + 1`. -/
lemma abscissaOfAbsConv_le_of_le_const_mul_rpow {f : ArithmeticFunction ℂ} {x : ℝ}
    (h : ∃ C, ∀ n, ‖f n‖ ≤ C * n ^ x) : abscissaOfAbsConv f ≤ x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_le_const_mul_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
    |>.abscissaOfAbsConv_le.trans_lt hy₂).false

/-- If `f` is bounded, the the abscissa of absolute convergence of `f` is bounded above by `1`. -/
lemma abscissaOfAbsConv_le_of_le_const {f : ArithmeticFunction ℂ}
    (h : ∃ C, ∀ n, ‖f n‖ ≤ C) : abscissaOfAbsConv f ≤ 1 := by
  convert abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) ?_
  · norm_num
  · simpa only [norm_eq_abs, Real.rpow_zero, mul_one] using h

/-- If the L-series of `f` is summable at `w` and `re w < re z`, then the L-series of the
point-wise product of `log` with `f` is summable at `z`. -/
lemma LSeriesSummable.log_pmul_of_re_lt_re {f : ArithmeticFunction ℂ} {w : ℂ} {z : ℂ}
    (h : w.re < z.re) (hf : LSeriesSummable f w) : LSeriesSummable (pmul log f) z := by
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  exact (hf.mul_left _).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_log_mul_LSeriesTerm_le_of_re_lt_re f h)

/-- If the L-series of the point-wise product of `log` with `f` is summable at `z`, then
so is the L-series of `f`. -/
lemma LSeriesSummable.of_LSeriesSummable_pmul_log  {f : ArithmeticFunction ℂ} {z : ℂ}
    (h : LSeriesSummable (pmul log f) z) : LSeriesSummable f z := by
  refine h.norm.of_norm_bounded_eventually_nat (fun n ↦ ‖(log n * f n / n ^ z : ℂ)‖) ?_
  simp only [norm_div, log_apply, ofNat_log, norm_mul, Filter.eventually_atTop]
  refine ⟨3, fun n hn ↦ ?_⟩
  conv => enter [1, 1]; rw [← one_mul (‖f n‖)]
  gcongr
  rw [← ofNat_log, norm_eq_abs, abs_ofReal,
    _root_.abs_of_nonneg <| Real.log_nonneg <| by norm_cast; linarith]
  calc 1
    _ = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log 3 := Real.log_le_log (by positivity) <|
                       (Real.exp_one_lt_d9.trans <| by norm_num).le
    _ ≤ Real.log n := Real.log_le_log zero_lt_three <| by exact_mod_cast hn

/-- The abscissa of absolute convergence of the point-wise product of `log` and `f`
is the same as that of `f`. -/
lemma abscissaOfAbsConv_pmul_log {f : ArithmeticFunction ℂ} :
    abscissaOfAbsConv (pmul log f) = abscissaOfAbsConv f := by
  refine le_antisymm ?_ ?_
  · refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ ?_
    obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hy
    have hx₁' : abscissaOfAbsConv f < ↑((x : ℂ).re)
    · simp only [ofReal_re, hx₁]
    have hx₂' : (x : ℂ).re < (y : ℂ).re
    · simp only [ofReal_re, EReal.coe_lt_coe_iff.mp hx₂]
    exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁').log_pmul_of_re_lt_re hx₂'
  · refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y hy ↦ ?_
    have hy' : abscissaOfAbsConv (pmul (↑log) f) < ↑((y : ℂ).re)
    · simp only [ofReal_re, hy]
    exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re hy').of_LSeriesSummable_pmul_log

/-!
### Differentiability and derivatives of L-series
-/

/-- The derivative of the terms of an L-series. -/
lemma LSeriesTerm_deriv (f : ArithmeticFunction ℂ) (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z ↦ f n / n ^ z) (-(↑(Real.log n) * f n / n ^ s)) s := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [hasDerivAt_const]
    rw [← neg_div, ← neg_mul, mul_comm, mul_div_assoc]
    simp_rw [div_eq_mul_inv, ← cpow_neg]
    refine HasDerivAt.const_mul (f n) ?_
    rw [mul_comm, ← mul_neg_one (Real.log n : ℂ), ← mul_assoc, ofReal_log n.cast_nonneg]
    exact (hasDerivAt_neg' s).const_cpow (Or.inl <| Nat.cast_ne_zero.mpr hn.ne')

/-- If `re z` is greater than the abscissa of absolute convergence of `f`, then the L-series
of `f` is differentiable with derivative the negative of the L-series of the point-wise
prodict of `log` with `f`. -/
lemma LSeries.hasDerivAt {f : Nat.ArithmeticFunction ℂ} {z : ℂ} (h : abscissaOfAbsConv f < z.re) :
    HasDerivAt (LSeries f) (- LSeries (pmul log f) z) z := by
  -- The L-series of `f` is summable at some real `x < re z`.
  obtain ⟨x, h', hf⟩ := LSeriesSummable_re_lt_of_abscissaOfAbsConv_lt_re h
  change HasDerivAt (fun s ↦ LSeries f s) ..
  simp only [LSeries, pmul_apply, realCoe_apply, log_apply, ← tsum_neg]
  -- We work in the right half-plane `re s > (x + re z)/2`.
  let S : Set ℂ := {s | (x + z.re) / 2 < s.re}
  have hop : IsOpen S := isOpen_lt continuous_const continuous_re
  have hpr : IsPreconnected S := (convex_halfspace_re_gt _).isPreconnected
  have hmem : z ∈ S
  · simp only [Set.mem_setOf_eq]
    linarith only [h']
  -- To get a uniform summable bound for the derivative series, we use that we
  -- have summability of the L-series of `pmul log f` at some `(x + z)/2`.
  have hx : (x : ℂ).re < ((x + z) / 2).re
  · simp only [add_re, ofReal_re, div_ofNat_re, sub_re]
    linarith only [h']
  have hf' := hf.log_pmul_of_re_lt_re hx
  rw [LSeriesSummable, ← summable_norm_iff] at hf'
  -- Show that the terms have the correct derivative.
  have hderiv (n : ℕ) :
      ∀ s ∈ S, HasDerivAt (fun z ↦ f n / n ^ z) (-(↑(Real.log n) * f n / n ^ s)) s
  · exact fun s _ ↦ LSeriesTerm_deriv f n s
  refine hasDerivAt_tsum_of_isPreconnected (F := ℂ) hf' hop hpr hderiv
    (fun n s hs ↦ ?_) hmem ?_ hmem
  · -- Show that the derivative series is uniformly bounded term-wise.
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    simp only [norm_neg, norm_div, norm_mul, pmul_apply, realCoe_apply, log_apply]
    refine div_le_div_of_le_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_ ?_
    · exact norm_ofNat_cpow_pos_of_pos hn _
    · refine norm_ofNat_cpow_le_norm_ofNat_cpow_of_pos hn <| le_of_lt ?_
      simpa only [add_re, ofReal_re, div_ofNat_re, sub_re] using hs
  · exact hf.of_re_le_re <| ofReal_re x ▸ h'.le

/-- If `re z` is greater than the abscissa of absolute convergence of `f`, then
the derivative of this L-series is the negative of the L-series of `pmul log f`. -/
lemma LSeries_deriv {f : Nat.ArithmeticFunction ℂ} {z : ℂ} (h : abscissaOfAbsConv f < z.re) :
    deriv (LSeries f) z = - LSeries (pmul log f) z :=
  (LSeries.hasDerivAt h).deriv

/-- The L-series of `f` is complex differentiable in its open half-plane of absolute
convergence. -/
lemma LSeries.differentiableOn {f : ArithmeticFunction ℂ} :
    DifferentiableOn ℂ (LSeries f) {z | abscissaOfAbsConv f < z.re} :=
  fun _ hz ↦ (LSeries.hasDerivAt hz).differentiableAt.differentiableWithinAt

/-!
### Multiplication of L-series
-/

/-- The L-series of the convolution product `f * g` of two arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeriesHasSum.mul {f g : ArithmeticFunction ℂ} {s a b : ℂ}
    (hf : LSeriesHasSum f s a) (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f * g) s (a * b) := by
  simp only [LSeriesHasSum, mul_apply, sum_eq_tsum_indicator, ← tsum_subtype]
  let m : ℕ × ℕ → ℕ := fun (n₁, n₂) ↦ n₁ * n₂
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  convert HasSum.tsum_fibers m (HasSum.mul hf hg hsum) with n
  rcases n.eq_zero_or_pos with rfl | hn
  · trans 0 -- show that both sides vanish when `n = 0`
    · -- by definition, the left hand sum is over the empty set
      rw [tsum_congr_set_coe (fun x ↦ f x.1 * g x.2) <|
            congrArg Finset.toSet divisorsAntidiagonal_zero]
      simp only [Finset.coe_sort_coe, tsum_empty, zero_div]
    · -- the right hand sum is over the union below, but in each term, one factor is always zero
      have hS : m ⁻¹' {0} = {0} ×ˢ Set.univ ∪ (Set.univ \ {0}) ×ˢ {0}
      · ext
        simp only [m, Set.mem_preimage, Set.mem_singleton_iff, _root_.mul_eq_zero, Set.mem_union,
          Set.mem_prod, Set.mem_univ, Set.mem_diff]
        tauto
      let h : ℕ × ℕ → ℂ := fun x ↦ f x.1 / x.1 ^ s * (g x.2 / x.2 ^ s)
      rw [tsum_congr_set_coe h hS,
        tsum_union_disjoint (Set.Disjoint.set_prod_left Set.disjoint_sdiff_right ..)
          (hsum.subtype _) (hsum.subtype _),
        tsum_setProd_singleton_left 0 _ h, tsum_setProd_singleton_right _ 0 h]
      simp only [map_zero, zero_div, zero_mul, tsum_zero, mul_zero, add_zero]
  -- now `n > 0`
  have H : n.divisorsAntidiagonal = m ⁻¹' {n}
  · ext x
    replace hn := hn.ne' -- for `tauto` below
    simp only [Finset.mem_coe, mem_divisorsAntidiagonal, m, Set.mem_preimage,
      Set.mem_singleton_iff]
    tauto
  rw [tsum_congr_set_coe (fun x ↦ f x.1 * g x.2) H, ← tsum_div_const]
  refine tsum_congr (fun x ↦ ?_)
  -- `rw [...]` does not work directly on the goal ("motive not type correct")
  conv =>
    enter [1, 2]
    rw [← Set.mem_singleton_iff.mp <| Set.mem_preimage.mp x.prop]
    simp only [m, Nat.cast_mul, mul_cpow_ofNat]
  field_simp

/-- The L-series of the convolution product `f * g` of two arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
lemma LSeries_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeries (f * g) s = LSeries f s * LSeries g s :=
  (LSeriesHasSum.mul hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

/-- The L-series of the convolution product `f * g` of two arithmetic functions `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
lemma LSeries_mul' {f g : ArithmeticFunction ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) :
    LSeries (f * g) s = LSeries f s * LSeries g s :=
  LSeries_mul (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

/-- The L-series of the convolution product `f * g` of two arithmetic functions `f` and `g`
is summable when both L-series are summable. -/
lemma LSeriesSummable_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f * g) s :=
  (LSeriesHasSum.mul hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

/-!
### L-series of specific arithmetic functions
-/

/-- The L-series of the arithmetic function `1` (taking the value `1` at `1` and zero else)
is the constant function `1`. -/
lemma LSeries.one : LSeries 1 = 1 := by
  ext s
  simp only [LSeries, one_apply]
  have H (n : ℕ) : (if n = 1 then 1 / (n : ℂ) ^ s else 0) = if n = 1 then 1 else 0 :=
    ite_congr rfl (fun h ↦ by simp [h]) (fun _ ↦ rfl)
  conv => enter [1, 1, n]; simp only [apply_ite (· / (n : ℂ) ^ s), zero_div, H]
  exact tsum_ite_eq 1 1

/-- The abscissa of convergence of `ζ` is `1`. -/
lemma abscissaOfAbsConv_zeta : abscissaOfAbsConv ζ = 1 := by
  simpa only [abscissaOfAbsConv, zeta_LSeriesSummable_iff_one_lt_re, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

/-- The L-series of the arithmetic function `ζ` equals the Riemann Zeta Function on its
domain of convergence `1 < re s`. -/
lemma LSeries.zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries ζ s = riemannZeta s := by
  simp only [LSeries, natCoe_apply, zeta_apply, cast_ite, CharP.cast_eq_zero, cast_one]
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [ne_zero_of_one_lt_re hs]
  simp only [hn.ne', ite_false]

lemma LSeriesHasSum_zeta {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum ζ s (riemannZeta s) :=
  LSeries.zeta_eq_riemannZeta hs ▸ (zeta_LSeriesSummable_iff_one_lt_re.mpr hs).LSeriesHasSum

-- Rename `zeta_LSeriesSummable_iff_one_lt_re` → `zeta_LSeriesSummable_iff`

lemma not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable μ 1 := by
  by_contra! h
  refine not_summable_one_div_on_primes <| summable_ofReal.mp <| Summable.of_neg ?_
  simp only [← Pi.neg_def, indicator_ofReal, ofReal_inv, ofReal_nat_cast]
  convert h.indicator {n | n.Prime} using 1
  ext n
  by_cases hn : n ∈ {p | p.Prime}
  · simpa [Set.indicator_of_mem hn, moebius_apply_prime hn] using neg_div' (n : ℂ) 1
  · simp [Set.indicator_of_not_mem hn]

lemma moebius_LSeriesSummable_iff {s : ℂ} : LSeriesSummable μ s ↔ 1 < s.re := by
  refine ⟨fun H ↦? _, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n ↦ ?_⟩
  · by_contra! h
    have h' : s.re ≤ (1 : ℂ).re := by simp only [one_re, h]
    exact not_LSeriesSummable_moebius_at_one <| LSeriesSummable.of_re_le_re h' H
  · rw [intCoe_apply, ← int_cast_abs, ← Int.cast_abs]
    norm_cast
    rcases eq_or_ne (μ n) 0 with h | h
    · simp [h]
    · rcases moebius_ne_zero_iff_eq_or.mp h with h | h <;> simp [h]

lemma abscissaOfAbsConv_mu : abscissaOfAbsConv μ = 1 := by
  simpa only [abscissaOfAbsConv, moebius_LSeriesSummable_iff, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _

lemma LSeries.zeta_mul_mu_eq_one {s : ℂ} (hs : 1 < s.re) : LSeries ζ s * LSeries μ s = 1 := by
  rw [← LSeries_mul (zeta_LSeriesSummable_iff_one_lt_re.mpr hs)
          (moebius_LSeriesSummable_iff.mpr hs),
    coe_zeta_mul_coe_moebius]
  exact congrFun LSeries.one s

lemma LSeries.zeta_ne_zero {s : ℂ} (hs : 1 < s.re) : LSeries ζ s ≠ 0 :=
  fun h ↦ by simpa [h] using LSeries.zeta_mul_mu_eq_one hs

/-- The Riemann Zeta Function does not vanish on the half-plane `re s > 1`. -/
lemma _root_.riemannZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  LSeries.zeta_eq_riemannZeta hs ▸ LSeries.zeta_ne_zero hs

/-- The L-series of the von Mangoldt function `Λ` is summable at `s` when `re s > 1`. -/
lemma LSeriesSummable_vonMangoldt {s : ℂ} (hs : 1 < s.re) : LSeriesSummable Λ s := by
  let s' : ℂ := 1 + (s.re - 1) / 2
  have Hs : s'.re ∈ Set.Ioo 1 s.re
  · simp only [add_re, one_re, div_ofNat_re, sub_re, ofReal_re, Set.mem_Ioo]
    constructor <;> linarith
  have hf := (zeta_LSeriesSummable_iff_one_lt_re.mpr Hs.1).log_pmul_of_re_lt_re Hs.2
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  rw [pmul_zeta] at hf
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hf
  simp only [norm_div]
  refine div_le_div_of_le (norm_nonneg _) ?_
  simp only [realCoe_apply, norm_eq_abs, abs_ofReal, log_apply]
  rw [_root_.abs_of_nonneg vonMangoldt_nonneg, _root_.abs_of_nonneg <| Real.log_nat_cast_nonneg n]
  exact vonMangoldt_le_log

/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the L-series of the arithmetic function `ζ` on its domain of convergence `1 < re s`. -/
lemma LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries Λ s = - deriv (LSeries ζ) s / LSeries ζ s := by
  have hs' : abscissaOfAbsConv ζ < s.re
  · rwa [abscissaOfAbsConv_zeta, ← EReal.coe_one, EReal.coe_lt_coe_iff]
  rw [eq_div_iff <| LSeries.zeta_ne_zero hs,
    ← LSeries_mul (LSeriesSummable_vonMangoldt hs) (zeta_LSeriesSummable_iff_one_lt_re.mpr hs),
    ← neg_eq_iff_eq_neg, LSeries_deriv hs']
  congr
  norm_cast
  simp only [vonMangoldt_mul_zeta, pmul_zeta]

/-- The L-series of the von Mangoldt function `Λ` equals the negative logarithmic derivative
of the Riemann zeta function on its domain of convergence `1 < re s`. -/
lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    LSeries Λ s = - deriv riemannZeta s / riemannZeta s := by
  convert LSeries_vonMangoldt_eq hs using 2
  · refine neg_inj.mpr <| Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs, ?_⟩
    exact fun _ hz ↦ (LSeries.zeta_eq_riemannZeta hz).symm
  · exact (LSeries.zeta_eq_riemannZeta hs).symm
