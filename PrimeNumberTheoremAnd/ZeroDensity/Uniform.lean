/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZeroDensity.Tail

/-!
# Mean square of ζ on vertical segments, uniformly for `σ₀ ≤ x ≤ 4`, heights `t ≥ 2`
-/

open Complex MeasureTheory Set intervalIntegral

@[expose] public noncomputable section
namespace ZeroDensity

lemma sl_ne_one' (x : ℝ) {t : ℝ} (ht : t ≠ 0) : sl x t ≠ 1 := by
  intro h; have := congrArg Complex.im h; simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add, one_im] at this; exact ht this

lemma zeta_decomp' {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ≠ 0) :
    riemannZeta (sl x t) = Dp x N t + Ap x N t + Bp x N t + sl x t * tailI N (sl x t) := by
  rw [← Zeta0EqZeta hN (by simp only [sl, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; exact hx) (sl_ne_one' x ht), riemannZeta0,
    sum_range_eq_Dp hx, Ap, Bp, tailI]

lemma norm_Ap_sq_le' {x : ℝ} {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 1 ≤ t) :
    ‖Ap x N t‖ ^ 2 ≤ 2 * (N : ℝ) ^ (2 - 2 * x) * (1 + t ^ 2)⁻¹ := by
  have h1 : ‖(N : ℂ) ^ (1 - sl x t)‖ = (N : ℝ) ^ (1 - x) := by
    rw [norm_natCast_cpow' hN]; simp [sl]
  have h2 : ‖1 - sl x t‖ ^ 2 = (1 - x) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply, sl]; ring
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have h3 : ((N : ℝ) ^ (1 - x)) ^ 2 = (N : ℝ) ^ (2 - 2 * x) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num; ring_nf
  rw [Ap, norm_div, norm_neg, h1, div_pow, h2, h3]
  have hp : 0 ≤ (N : ℝ) ^ (2 - 2 * x) := by positivity
  rw [show 2 * (N : ℝ) ^ (2 - 2 * x) * (1 + t ^ 2)⁻¹ = (N : ℝ) ^ (2 - 2 * x) / ((1 + t ^ 2) / 2) by
    field_simp]
  exact div_le_div_of_nonneg_left hp (by positivity) (by nlinarith [sq_nonneg (1 - x)])

lemma continuousOn_zeta_line (x : ℝ) {α β : ℝ} (hα : 0 < α) :
    ContinuousOn (fun t : ℝ => riemannZeta (sl x t)) (Icc α β) := by
  intro t ht
  have h0 : t ≠ 0 := by linarith [ht.1]
  exact ((differentiableAt_riemannZeta (sl_ne_one' x h0)).continuousAt.comp
    (by fun_prop : Continuous fun t : ℝ => sl x t).continuousAt).continuousWithinAt

lemma continuous_tail' {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 0 < N) :
    Continuous fun t : ℝ => tailI N (sl x t) := by
  have : (fun t : ℝ => tailI N (sl x t)) = FT (tg x N) := funext (tailI_eq_FT x N hN)
  rw [this]; exact FT_continuous _ (integrable_tg x hx N)

lemma norm_coefA_sq_le {x σ₀ : ℝ} (hx : σ₀ ≤ x) {n : ℕ} (hn : 1 ≤ n) :
    ‖coefA x n‖ ^ 2 ≤ (n : ℝ) ^ (-2 * σ₀) := by
  rw [norm_coefA_sq hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- Explicit bound on a segment `[α, β]`, `2 ≤ α`. -/
lemma seg_explicit {x : ℝ} (hx0 : 0 < x) (hx4 : x ≤ 4) {N : ℕ} (hN : 0 < N) {α β : ℝ}
    (hα : 2 ≤ α) (hαβ : α ≤ β) :
    (∫ t in α..β, ‖riemannZeta (sl x t)‖ ^ 2) ≤
      4 * ((β + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖coefA x n‖ ^ 2
        + 2 * (N : ℝ) ^ (2 - 2 * x) * (Real.pi / 2) + β / 4
        + (4 + β) ^ 2 * ((2 * Real.pi * Real.exp 1 / (8 * x)) * (N : ℝ) ^ (-2 * x))) := by
  set c := 2 * (N : ℝ) ^ (2 - 2 * x)
  have hβ0 : 0 ≤ β := by linarith
  have cD : Continuous fun t : ℝ => ‖Dp x N t‖ ^ 2 := (continuous_Dp (σ := x) N).norm.pow 2
  have cT : Continuous fun t : ℝ => ‖tailI N (sl x t)‖ ^ 2 := (continuous_tail' hx0 hN).norm.pow 2
  have cI : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => by positivity
  set F : ℝ → ℝ := fun t => 4 * (‖Dp x N t‖ ^ 2 + c * (1 + t ^ 2)⁻¹ + 1 / 4
      + (4 + β) ^ 2 * ‖tailI N (sl x t)‖ ^ 2) with hF
  have cF : Continuous F :=
    continuous_const.mul (((cD.add (continuous_const.mul cI)).add continuous_const).add
      (continuous_const.mul cT))
  have step1 : (∫ t in α..β, ‖riemannZeta (sl x t)‖ ^ 2) ≤ ∫ t in α..β, F t := by
    apply intervalIntegral.integral_mono_on hαβ
    · exact ((continuousOn_zeta_line x (by linarith)).norm.pow 2).intervalIntegrable_of_Icc hαβ
    · exact cF.intervalIntegrable _ _
    intro t ht
    have ht2 : 2 ≤ t := hα.trans ht.1
    rw [zeta_decomp' hx0 hN (by linarith : t ≠ 0)]
    refine (norm_add4_sq _ _ _ _).trans ?_
    simp only [hF]
    gcongr
    · exact norm_Ap_sq_le' hN (by linarith)
    · exact norm_Bp_sq_le hx0 hN t
    · rw [norm_mul, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply, sl]
      nlinarith [ht.2]
  have hF0 : ∀ t, 0 ≤ F t := fun t => by simp only [hF]; positivity
  have step2 : (∫ t in α..β, F t) ≤ ∫ t in (0:ℝ)..β, F t :=
    intervalIntegral.integral_mono_interval (by linarith) hαβ le_rfl
      (Filter.Eventually.of_forall hF0) (cF.intervalIntegrable _ _)
  have i1 := cD.intervalIntegrable (μ := volume) 0 β
  have i2 : IntervalIntegrable (fun t : ℝ => c * (1 + t ^ 2)⁻¹) volume 0 β :=
    (continuous_const.mul cI).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun t : ℝ => (4 + β) ^ 2 * ‖tailI N (sl x t)‖ ^ 2) volume 0 β :=
    (continuous_const.mul cT).intervalIntegrable _ _
  have eq : (∫ t in (0:ℝ)..β, F t) =
      4 * ((∫ t in (0:ℝ)..β, ‖Dp x N t‖ ^ 2) + c * Real.arctan β + β / 4
        + (4 + β) ^ 2 * ∫ t in (0:ℝ)..β, ‖tailI N (sl x t)‖ ^ 2) := by
    simp only [hF]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((i1.add i2).add intervalIntegrable_const) i4,
      intervalIntegral.integral_add (i1.add i2) intervalIntegrable_const,
      intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_inv_one_add_sq]
    simp; ring
  have hMV := mean_value_dirichlet_log N (Finset.Icc 1 N) subset_rfl (coefA x) β
  have hD : (∫ t in (0:ℝ)..β, ‖Dp x N t‖ ^ 2) ≤
      (β + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖coefA x n‖ ^ 2 := by
    have := (abs_le.1 hMV).2; unfold Dp; linarith
  have hTl := tailMeanSquare x hx0 N hN β hβ0
  have hat : Real.arctan β ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two β).le
  have hc0 : 0 ≤ c := by positivity
  refine (step1.trans step2).trans ?_
  rw [eq]
  have := mul_le_mul_of_nonneg_left hat hc0
  have := mul_le_mul_of_nonneg_left hTl (by positivity : (0:ℝ) ≤ (4 + β) ^ 2)
  linarith

/-- **Uniform mean square**: for `1 / 2 < σ₀ < 1` there is `C` with
`∫_α^β |ζ(x+it)|² dt ≤ C β` for all `σ₀ ≤ x ≤ 4`, `2 ≤ α ≤ β`. -/
@[blueprint
  "zd-uniform-ms"
  (title := "Uniform mean square")
  (statement := /--
    For $1/2<\sigma_0<1$ there is a constant $C=C(\sigma_0)$ such that
    $\int_\alpha^\beta|\zeta(x+it)|^2\,dt\le C\beta$ for all $\sigma_0\le x\le 4$ and $2\le\alpha\le\beta$.
  -/)]
theorem uniformMeanSquare {σ₀ : ℝ} (hσ : 1 / 2 < σ₀) (hσ1 : σ₀ < 1) :
    ∃ C, ∀ x, σ₀ ≤ x → x ≤ 4 → ∀ α β, 2 ≤ α → α ≤ β →
      (∫ t in α..β, ‖riemannZeta (sl x t)‖ ^ 2) ≤ C * β := by
  have hσ0 : 0 < σ₀ := by linarith
  set a : ℝ := (1 + 1 / (2 * σ₀)) / 2 with ha_def
  have h2σ : 1 / (2 * σ₀) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have ha1 : a < 1 := by rw [ha_def]; linarith
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have haσ : 2 - 2 * a * σ₀ ≤ 1 := by
    have : 2 * a * σ₀ = σ₀ + 1 / 2 := by rw [ha_def]; field_simp
    linarith
  have haσ2 : a * (2 - 2 * σ₀) ≤ 1 := by nlinarith
  set S := ∑' n : ℕ, (n : ℝ) ^ (-2 * σ₀)
  have hSs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ₀)) := Real.summable_nat_rpow.2 (by linarith)
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by positivity
  set K₀ := 2 * Real.pi * Real.exp 1 / (8 * σ₀)
  have hK₀ : 0 ≤ K₀ := by positivity
  refine ⟨4 * (S * (5 + 4 / (1 - a)) + Real.pi + 1 / 4 + 36 * K₀), ?_⟩
  intro x hx hx4 α T hα hαT
  have hx0 : 0 < x := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  set y := T ^ a with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hT1 ha0.le
  have hyT : y ≤ T := by
    calc y ≤ T ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 ha1.le
      _ = T := Real.rpow_one T
  set N := ⌊y⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hy1)
  have hN : 0 < N := hN1
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hNy2 : y / 2 ≤ N := by
    have := Nat.lt_floor_add_one y
    have : (1:ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hN1r : (1:ℝ) ≤ N := by exact_mod_cast hN1
  refine (seg_explicit hx0 hx4 hN hα hαT).trans ?_
  have hsum : ∑ n ∈ Finset.Icc 1 N, ‖coefA x n‖ ^ 2 ≤ S :=
    (Finset.sum_le_sum fun n hn => norm_coefA_sq_le hx (Finset.mem_Icc.1 hn).1).trans
      (hSs.sum_le_tsum _ fun n _ => by positivity)
  have hlog : Real.log T ≤ T ^ (1 - a) / (1 - a) := Real.log_le_rpow_div hT0.le (by linarith)
  have hlogN : Real.log N ≤ Real.log T := Real.log_le_log hNpos (hNy.trans hyT)
  have hylog : y * Real.log T ≤ T / (1 - a) := by
    calc y * Real.log T ≤ y * (T ^ (1 - a) / (1 - a)) :=
          mul_le_mul_of_nonneg_left hlog (by linarith)
      _ = T / (1 - a) := by
          rw [hy, mul_div_assoc', ← Real.rpow_add hT0]; norm_num
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1r
  have t1 : T + 4 * N * (1 + Real.log N) ≤ T * (5 + 4 / (1 - a)) := by
    have : (N : ℝ) * Real.log N ≤ y * Real.log T := mul_le_mul hNy hlogN hlogN0 (by linarith)
    have e : T * (5 + 4 / (1 - a)) = 5 * T + 4 * (T / (1 - a)) := by ring
    rw [e]; nlinarith
  have t2 : (N : ℝ) ^ (2 - 2 * x) ≤ T := by
    calc (N : ℝ) ^ (2 - 2 * x) ≤ (N : ℝ) ^ (2 - 2 * σ₀) :=
          Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      _ ≤ y ^ (2 - 2 * σ₀) := Real.rpow_le_rpow hNpos.le hNy (by linarith)
      _ = T ^ (a * (2 - 2 * σ₀)) := by rw [hy, ← Real.rpow_mul hT0.le]
      _ ≤ T ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 haσ2
      _ = T := Real.rpow_one T
  have t4 : (4 + T) ^ 2 * (N : ℝ) ^ (-2 * x) ≤ 36 * T := by
    have hy2 : 0 < y / 2 := by linarith
    have p0 : (N : ℝ) ^ (-2 * x) ≤ (N : ℝ) ^ (-2 * σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have p1 : (N : ℝ) ^ (-2 * σ₀) ≤ (y / 2) ^ (-2 * σ₀) :=
      Real.rpow_le_rpow_of_nonpos hy2 hNy2 (by linarith)
    have p2 : (y / 2) ^ (-2 * σ₀) = T ^ (-2 * a * σ₀) * 2 ^ (2 * σ₀) := by
      rw [Real.div_rpow (by linarith) (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        hy, ← Real.rpow_mul hT0.le]
      ring_nf
    have p3 : (2:ℝ) ^ (2 * σ₀) ≤ 4 := by
      calc (2:ℝ) ^ (2 * σ₀) ≤ 2 ^ (2:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have p4 : T ^ (2:ℝ) * T ^ (-2 * a * σ₀) ≤ T := by
      rw [← Real.rpow_add hT0]
      calc T ^ ((2:ℝ) + -2 * a * σ₀) ≤ T ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
        _ = T := Real.rpow_one T
    have p5 : (4 + T) ^ 2 ≤ 9 * T ^ (2:ℝ) := by
      rw [Real.rpow_two]; nlinarith
    have q0 : 0 ≤ T ^ (-2 * a * σ₀) := by positivity
    have q1 : 0 ≤ (N : ℝ) ^ (-2 * x) := by positivity
    calc (4 + T) ^ 2 * (N : ℝ) ^ (-2 * x) ≤ (9 * T ^ (2:ℝ)) * (4 * T ^ (-2 * a * σ₀)) := by
          apply mul_le_mul p5 _ q1 (by positivity)
          exact p0.trans (p1.trans (by rw [p2]; linarith [mul_le_mul_of_nonneg_left p3 q0]))
      _ = 36 * (T ^ (2:ℝ) * T ^ (-2 * a * σ₀)) := by ring
      _ ≤ 36 * T := by linarith
  have hK : 2 * Real.pi * Real.exp 1 / (8 * x) ≤ K₀ :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hsum0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖coefA x n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have b1 : (T + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖coefA x n‖ ^ 2 ≤
      T * (5 + 4 / (1 - a)) * S := by
    have h1a : 0 < 1 - a := by linarith
    exact mul_le_mul t1 hsum hsum0 (by positivity)
  have hpi := Real.pi_pos
  have b2 : 2 * (N : ℝ) ^ (2 - 2 * x) * (Real.pi / 2) ≤ T * Real.pi := by nlinarith
  have b4 : (4 + T) ^ 2 * ((2 * Real.pi * Real.exp 1 / (8 * x)) * (N : ℝ) ^ (-2 * x)) ≤
      36 * K₀ * T := by
    have q1 : 0 ≤ (N : ℝ) ^ (-2 * x) := by positivity
    have : (4 + T) ^ 2 * ((2 * Real.pi * Real.exp 1 / (8 * x)) * (N : ℝ) ^ (-2 * x)) ≤
        (4 + T) ^ 2 * (K₀ * (N : ℝ) ^ (-2 * x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK q1) (by positivity)
    linarith [mul_le_mul_of_nonneg_left t4 hK₀]
  have e : 4 * (S * (5 + 4 / (1 - a)) + Real.pi + 1 / 4 + 36 * K₀) * T =
      4 * (T * (5 + 4 / (1 - a)) * S + T * Real.pi + T / 4 + 36 * K₀ * T) := by ring
  rw [e]; linarith [b1, b2, b4]

end ZeroDensity

