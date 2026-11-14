/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZetaBounds
public import PrimeNumberTheoremAnd.ZeroDensity.Dirichlet
public import PrimeNumberTheoremAnd.ZeroDensity.BohrLandau

/-!
# Mean square of ζ on Re s = σ, 1 / 2 < σ < 1 (reduction to a tail lemma)
-/

open Complex MeasureTheory Set intervalIntegral

@[expose] public noncomputable section
namespace ZeroDensity

variable {σ : ℝ}

/-- point on the line -/
abbrev sl (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

/-- Euler–Maclaurin tail integral. -/
def tailI (N : ℕ) (s : ℂ) : ℂ := ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- Tail mean-square bound; proved for all σ > 0 in `ZeroDensity.Tail` (`tailMeanSquare`). -/
def TailMeanSquare (σ K : ℝ) : Prop :=
  ∀ N : ℕ, 0 < N → ∀ T : ℝ, 0 ≤ T →
    (∫ t in (0:ℝ)..T, ‖tailI N (sl σ t)‖ ^ 2) ≤ K * (N : ℝ) ^ (-2 * σ)

def coefA (σ : ℝ) (n : ℕ) : ℂ := (n : ℂ) ^ (-(σ : ℂ))
def Dp (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 N, coefA σ n * (n : ℂ) ^ (-((t : ℂ) * I))
def Ap (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ := (-(N : ℂ) ^ (1 - sl σ t)) / (1 - sl σ t)
def Bp (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ := (-(N : ℂ) ^ (-sl σ t)) / 2

lemma sl_ne_one (hσ1 : σ < 1) (t : ℝ) : sl σ t ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith

lemma sl_ne_zero (hσ0 : 0 < σ) (t : ℝ) : sl σ t ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith

lemma one_div_cpow_split {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    1 / (n : ℂ) ^ (sl σ t) = coefA σ n * (n : ℂ) ^ (-((t : ℂ) * I)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [one_div, ← Complex.cpow_neg, coefA, ← Complex.cpow_add _ _ hn0, sl, neg_add]

lemma sum_range_eq_Dp (hσ0 : 0 < σ) (N : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ (sl σ t)) = Dp σ N t := by
  have hr : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hr, Finset.sum_insert (by simp), Dp]
  have h0 : (1 / ((0:ℕ):ℂ) ^ (sl σ t)) = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow (sl_ne_zero hσ0 t)]; simp
  rw [h0, zero_add]
  exact Finset.sum_congr rfl fun n hn => one_div_cpow_split (Finset.mem_Icc.1 hn).1 t

/-- Approximate formula on the line (from vendored `Zeta0EqZeta`). -/
lemma zeta_decomp (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    riemannZeta (sl σ t) = Dp σ N t + Ap σ N t + Bp σ N t + sl σ t * tailI N (sl σ t) := by
  rw [← Zeta0EqZeta hN (by simp only [sl, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; exact hσ0) (sl_ne_one hσ1 t), riemannZeta0,
    sum_range_eq_Dp hσ0, Ap, Bp, tailI]

lemma norm_add4_sq (a b c d : ℂ) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
    (norm_add_le _ _).trans (by gcongr; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _))
  have h0 : 0 ≤ ‖a + b + c + d‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖), norm_nonneg a,
    norm_nonneg b, norm_nonneg c, norm_nonneg d]

lemma norm_natCast_cpow' {N : ℕ} (hN : 0 < N) (z : ℂ) : ‖(N : ℂ) ^ z‖ = (N : ℝ) ^ z.re :=
  Complex.norm_natCast_cpow_of_pos hN z

lemma norm_Ap_sq_le (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    ‖Ap σ N t‖ ^ 2 ≤ (N : ℝ) ^ (2 - 2 * σ) / (1 - σ) ^ 2 * (1 + t ^ 2)⁻¹ := by
  have h1 : ‖(N : ℂ) ^ (1 - sl σ t)‖ = (N : ℝ) ^ (1 - σ) := by
    rw [norm_natCast_cpow']; · simp [sl]
    exact hN
  have h2 : ‖1 - sl σ t‖ ^ 2 = (1 - σ) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply, sl]; ring
  have hd : 0 < 1 - σ := by linarith
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have h3 : ((N : ℝ) ^ (1 - σ)) ^ 2 = (N : ℝ) ^ (2 - 2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
  rw [Ap, norm_div, norm_neg, h1, div_pow, h2, h3]
  have hp : 0 ≤ (N : ℝ) ^ (2 - 2 * σ) := by positivity
  have ha : 0 < (1 - σ) ^ 2 := by positivity
  have key : (1 - σ) ^ 2 * (1 + t ^ 2) ≤ (1 - σ) ^ 2 + t ^ 2 := by
    have : (1 - σ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg t)]
  rw [show (N : ℝ) ^ (2 - 2 * σ) / (1 - σ) ^ 2 * (1 + t ^ 2)⁻¹ =
      (N : ℝ) ^ (2 - 2 * σ) / ((1 - σ) ^ 2 * (1 + t ^ 2)) by field_simp]
  exact div_le_div_of_nonneg_left hp (by positivity) key

lemma norm_Bp_sq_le (hσ0 : 0 < σ) {N : ℕ} (hN : 0 < N) (t : ℝ) : ‖Bp σ N t‖ ^ 2 ≤ 1 / 4 := by
  have h1 : ‖(N : ℂ) ^ (-sl σ t)‖ ≤ 1 := by
    rw [norm_natCast_cpow' hN]; simp only [sl, neg_add_rev, add_re, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, neg_zero, zero_add]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
  rw [Bp, norm_div, norm_neg]
  have : ‖(2:ℂ)‖ = 2 := by simp
  rw [this, div_pow]
  have h0 := norm_nonneg ((N : ℂ) ^ (-sl σ t))
  nlinarith

lemma norm_sl_sq_le (hσ0 : 0 < σ) (hσ1 : σ < 1) {t T : ℝ} (ht : t ∈ Icc 0 T) :
    ‖sl σ t‖ ^ 2 ≤ (1 + T) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply, sl]
  nlinarith [ht.1, ht.2]

lemma continuous_zeta_line (hσ1 : σ < 1) : Continuous fun t : ℝ => riemannZeta (sl σ t) :=
  continuous_iff_continuousAt.2 fun t =>
    (differentiableAt_riemannZeta (sl_ne_one hσ1 t)).continuousAt.comp (by fun_prop)

lemma continuous_Dp (N : ℕ) : Continuous (Dp σ N) := by
  unfold Dp
  refine continuous_finsetSum _ fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

lemma continuous_Ap (hσ1 : σ < 1) {N : ℕ} (hN : 0 < N) : Continuous (Ap σ N) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold Ap
  refine Continuous.div (Continuous.const_cpow (by fun_prop) (Or.inl hN0)).neg
    (by fun_prop) fun t => sub_ne_zero.2 (sl_ne_one hσ1 t).symm

lemma continuous_Bp {N : ℕ} (hN : 0 < N) : Continuous (Bp σ N) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold Bp
  exact (Continuous.const_cpow (by fun_prop) (Or.inl hN0)).neg.div_const _

lemma continuous_tail (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 0 < N) :
    Continuous fun t : ℝ => tailI N (sl σ t) := by
  have e : (fun t : ℝ => tailI N (sl σ t)) = fun t =>
      (riemannZeta (sl σ t) - Dp σ N t - Ap σ N t - Bp σ N t) / sl σ t := by
    funext t; rw [zeta_decomp hσ0 hσ1 hN t]; field_simp [sl_ne_zero hσ0 t]; ring
  rw [e]
  exact (((continuous_zeta_line hσ1).sub (continuous_Dp N)).sub (continuous_Ap hσ1 hN)).sub
    (continuous_Bp hN) |>.div (by fun_prop) (sl_ne_zero hσ0)

/-- **Explicit mean-square bound** (conditional only on the tail lemma). -/
theorem mean_square_explicit (hσ0 : 0 < σ) (hσ1 : σ < 1) {K : ℝ} (hK : TailMeanSquare σ K)
    {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, ‖riemannZeta (sl σ t)‖ ^ 2) ≤
      4 * ((T + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖coefA σ n‖ ^ 2
        + (N : ℝ) ^ (2 - 2 * σ) / (1 - σ) ^ 2 * Real.arctan T + T / 4
        + (1 + T) ^ 2 * (K * (N : ℝ) ^ (-2 * σ))) := by
  set c := (N : ℝ) ^ (2 - 2 * σ) / (1 - σ) ^ 2
  have cD : Continuous fun t : ℝ => ‖Dp σ N t‖ ^ 2 := (continuous_Dp (σ := σ) N).norm.pow 2
  have cT : Continuous fun t : ℝ => ‖tailI N (sl σ t)‖ ^ 2 := (continuous_tail hσ0 hσ1 hN).norm.pow 2
  have cR : Continuous fun t : ℝ => ‖Dp σ N t‖ ^ 2 + c * (1 + t ^ 2)⁻¹ + 1 / 4
      + (1 + T) ^ 2 * ‖tailI N (sl σ t)‖ ^ 2 := by
    refine ((cD.add (continuous_const.mul ?_)).add continuous_const).add (continuous_const.mul cT)
    exact Continuous.inv₀ (by fun_prop) fun t => by positivity
  have step : (∫ t in (0:ℝ)..T, ‖riemannZeta (sl σ t)‖ ^ 2) ≤
      ∫ t in (0:ℝ)..T, 4 * (‖Dp σ N t‖ ^ 2 + c * (1 + t ^ 2)⁻¹ + 1 / 4
        + (1 + T) ^ 2 * ‖tailI N (sl σ t)‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on hT
    · exact ((continuous_zeta_line hσ1).norm.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul cR).intervalIntegrable _ _
    intro t ht
    rw [zeta_decomp hσ0 hσ1 hN t]
    refine (norm_add4_sq _ _ _ _).trans ?_
    gcongr
    · exact norm_Ap_sq_le hσ0 hσ1 hN t
    · exact norm_Bp_sq_le hσ0 hN t
    · rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (norm_sl_sq_le hσ0 hσ1 ht) (by positivity)
  have i1 := cD.intervalIntegrable (μ := volume) 0 T
  have i2 : IntervalIntegrable (fun t : ℝ => c * (1 + t ^ 2)⁻¹) volume 0 T :=
    (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun t => by positivity)).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun t : ℝ => (1 + T) ^ 2 * ‖tailI N (sl σ t)‖ ^ 2) volume 0 T :=
    (continuous_const.mul cT).intervalIntegrable _ _
  have eq : (∫ t in (0:ℝ)..T, 4 * (‖Dp σ N t‖ ^ 2 + c * (1 + t ^ 2)⁻¹ + 1 / 4
        + (1 + T) ^ 2 * ‖tailI N (sl σ t)‖ ^ 2)) =
      4 * ((∫ t in (0:ℝ)..T, ‖Dp σ N t‖ ^ 2) + c * Real.arctan T + T / 4
        + (1 + T) ^ 2 * ∫ t in (0:ℝ)..T, ‖tailI N (sl σ t)‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((i1.add i2).add intervalIntegrable_const) i4,
      intervalIntegral.integral_add (i1.add i2) intervalIntegrable_const,
      intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_inv_one_add_sq]
    simp; ring
  have hMV := mean_value_dirichlet_log N (Finset.Icc 1 N) subset_rfl (coefA σ) T
  have hD : (∫ t in (0:ℝ)..T, ‖Dp σ N t‖ ^ 2) ≤
      (T + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖coefA σ n‖ ^ 2 := by
    have := (abs_le.1 hMV).2; unfold Dp; nlinarith
  have hTl := hK N hN T hT
  rw [eq] at step
  refine step.trans ?_
  gcongr

lemma norm_coefA_sq {n : ℕ} (hn : 1 ≤ n) : ‖coefA σ n‖ ^ 2 = (n : ℝ) ^ (-2 * σ) := by
  rw [coefA, Complex.norm_natCast_cpow_of_pos (by omega)]
  simp only [neg_re, ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num; ring_nf

lemma sum_coefA_le (hσ : 1 / 2 < σ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖coefA σ n‖ ^ 2 ≤ ∑' n : ℕ, (n : ℝ) ^ (-2 * σ) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ)) := Real.summable_nat_rpow.2 (by linarith)
  rw [Finset.sum_congr rfl fun n hn => norm_coefA_sq (σ := σ) (Finset.mem_Icc.1 hn).1]
  exact hs.sum_le_tsum _ fun n _ => by positivity

/-- **Mean square bound** `∫_0^T |ζ(σ+it)|² ≤ C T` for 1 / 2 < σ < 1, conditional only on
`TailMeanSquare σ K`. -/
@[blueprint
  "zd-mean-square-tail"
  (title := "Mean square of zeta from a tail bound")
  (statement := /--
    Let $1/2<\sigma<1$. If the Euler--Maclaurin tail satisfies
    $\int_0^T|\mathrm{tail}_N(\sigma+it)|^2\,dt\le K N^{-2\sigma}$ for all $N\ge 1$ and $T\ge 0$
    (the hypothesis `TailMeanSquare`), then there is a constant $C$ such that
    $\int_0^T|\zeta(\sigma+it)|^2\,dt\le C T$ for all $T\ge 2$.
  -/)]
theorem meanSquareBound_of_tail (hσ : 1 / 2 < σ) (hσ1 : σ < 1) {K : ℝ}
    (hK : TailMeanSquare σ K) :
    ∃ C, MeanSquareBound σ C := by
  have hσ0 : 0 < σ := by linarith
  have hK0 : 0 ≤ K := by
    have := hK 1 one_pos 0 le_rfl; simpa using this
  set a : ℝ := (1 + 1 / (2 * σ)) / 2 with ha_def
  have h2σ : 1 / (2 * σ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have ha1 : a < 1 := by rw [ha_def]; linarith
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have haσ : 2 - 2 * a * σ ≤ 1 := by
    have : 2 * a * σ = σ + 1 / 2 := by rw [ha_def]; field_simp
    linarith
  have haσ2 : a * (2 - 2 * σ) ≤ 1 := by nlinarith
  set S := ∑' n : ℕ, (n : ℝ) ^ (-2 * σ)
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by positivity
  refine ⟨4 * (S * (5 + 4 / (1 - a)) + 1 / (1 - σ) ^ 2 * (Real.pi / 2) + 1 / 4 + 16 * K), ?_⟩
  intro T hT
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  set x := T ^ a with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hT1 ha0.le
  have hxT : x ≤ T := by
    calc x ≤ T ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 ha1.le
      _ = T := Real.rpow_one T
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx1)
  have hN : 0 < N := hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hNx2 : x / 2 ≤ N := by
    have := Nat.lt_floor_add_one x
    have : (1:ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · have hc : Continuous fun t : ℝ => ‖riemannZeta (sl σ t)‖ ^ 2 :=
      (continuous_zeta_line hσ1).norm.pow 2
    exact (hc.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self
  have hE := mean_square_explicit hσ0 hσ1 hK hN hT0.le
  change (∫ t in (0:ℝ)..T, ‖riemannZeta (sl σ t)‖ ^ 2) ≤ _
  refine hE.trans ?_
  -- term bounds
  have hsum := sum_coefA_le hσ N
  have hlog : Real.log T ≤ T ^ (1 - a) / (1 - a) := Real.log_le_rpow_div hT0.le (by linarith)
  have hlogN : Real.log N ≤ Real.log T :=
    Real.log_le_log hNpos (hNx.trans hxT)
  have hxlog : x * Real.log T ≤ T / (1 - a) := by
    calc x * Real.log T ≤ x * (T ^ (1 - a) / (1 - a)) :=
          mul_le_mul_of_nonneg_left hlog (by linarith)
      _ = T / (1 - a) := by
          rw [hx, mul_div_assoc', ← Real.rpow_add hT0]; norm_num
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have t1 : T + 4 * N * (1 + Real.log N) ≤ T * (5 + 4 / (1 - a)) := by
    have : (N : ℝ) * Real.log N ≤ x * Real.log T :=
      mul_le_mul hNx hlogN hlogN0 (by linarith)
    have e : T * (5 + 4 / (1 - a)) = 5 * T + 4 * (T / (1 - a)) := by ring
    rw [e]; linarith
  have t2 : (N : ℝ) ^ (2 - 2 * σ) ≤ T := by
    calc (N : ℝ) ^ (2 - 2 * σ) ≤ x ^ (2 - 2 * σ) :=
          Real.rpow_le_rpow hNpos.le hNx (by linarith)
      _ = T ^ (a * (2 - 2 * σ)) := by rw [hx, ← Real.rpow_mul hT0.le]
      _ ≤ T ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 haσ2
      _ = T := Real.rpow_one T
  have t3 : Real.arctan T ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two T).le
  have t4 : (1 + T) ^ 2 * (N : ℝ) ^ (-2 * σ) ≤ 16 * T := by
    have hx2 : 0 < x / 2 := by linarith
    have p1 : (N : ℝ) ^ (-2 * σ) ≤ (x / 2) ^ (-2 * σ) :=
      Real.rpow_le_rpow_of_nonpos hx2 hNx2 (by linarith)
    have p2 : (x / 2) ^ (-2 * σ) = T ^ (-2 * a * σ) * 2 ^ (2 * σ) := by
      rw [Real.div_rpow (by linarith) (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        hx, ← Real.rpow_mul hT0.le]
      ring_nf
    have p3 : (2:ℝ) ^ (2 * σ) ≤ 4 := by
      calc (2:ℝ) ^ (2 * σ) ≤ 2 ^ (2:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have p4 : T ^ (2:ℝ) * T ^ (-2 * a * σ) ≤ T := by
      rw [← Real.rpow_add hT0]
      calc T ^ ((2:ℝ) + -2 * a * σ) ≤ T ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
        _ = T := Real.rpow_one T
    have p5 : (1 + T) ^ 2 ≤ 4 * T ^ (2:ℝ) := by
      rw [Real.rpow_two]
      have := mul_le_mul hT1 hT1 zero_le_one (by linarith)
      have := mul_le_mul_of_nonneg_left hT1 hT0.le
      linarith
    have q0 : 0 ≤ T ^ (-2 * a * σ) := by positivity
    have q1 : 0 ≤ (N : ℝ) ^ (-2 * σ) := by positivity
    calc (1 + T) ^ 2 * (N : ℝ) ^ (-2 * σ) ≤ (4 * T ^ (2:ℝ)) * (4 * T ^ (-2 * a * σ)) := by
          apply mul_le_mul p5 _ q1 (by positivity)
          exact p1.trans (by rw [p2]; linarith [mul_le_mul_of_nonneg_left p3 q0])
      _ = 16 * (T ^ (2:ℝ) * T ^ (-2 * a * σ)) := by ring
      _ ≤ 16 * T := by linarith
  have hd : 0 < (1 - σ) ^ 2 := pow_pos (by linarith) 2
  have hc0 : 0 ≤ (N : ℝ) ^ (2 - 2 * σ) / (1 - σ) ^ 2 := by positivity
  have hsum0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖coefA σ n‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hA0 : 0 ≤ T + 4 * N * (1 + Real.log N) := by positivity
  have b1 : (T + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖coefA σ n‖ ^ 2 ≤
      T * (5 + 4 / (1 - a)) * S := by
    have h1a : 0 < 1 - a := by linarith
    exact mul_le_mul t1 hsum hsum0 (by positivity)
  have b2 : (N : ℝ) ^ (2 - 2 * σ) / (1 - σ) ^ 2 * Real.arctan T ≤ T / (1 - σ) ^ 2 * (Real.pi / 2) := by
    have hat : 0 ≤ Real.arctan T := by
      have := Real.arctan_strictMono.monotone hT0.le; simpa using this
    exact mul_le_mul (div_le_div_of_nonneg_right t2 hd.le) t3 hat (by positivity)
  have b4 : (1 + T) ^ 2 * (K * (N : ℝ) ^ (-2 * σ)) ≤ 16 * K * T := by
    linarith [mul_le_mul_of_nonneg_left t4 hK0]
  have e : 4 * (S * (5 + 4 / (1 - a)) + 1 / (1 - σ) ^ 2 * (Real.pi / 2) + 1 / 4 + 16 * K) * T =
      4 * (T * (5 + 4 / (1 - a)) * S + T / (1 - σ) ^ 2 * (Real.pi / 2) + T / 4 + 16 * K * T) := by
    ring
  rw [e]; linarith [b1, b2, b4]

end ZeroDensity

