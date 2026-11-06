import TernaryGoldbach.Explicit.PsiExplicit

/-!
# The Gaussian explicit formula with an explicit finite-RH height

The finite RH premise is a theorem argument. Nothing in this module supplies
an RH certificate, and no hypothesis at height `3e10` is imported implicitly.
The proof adapts `Explicit/PsiExplicit.lean` from pinned upstream
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt
open TernaryGoldbach.Explicit

namespace TernaryGoldbach.RSBounds

/-- All nontrivial zeta zeros through a specified height lie on the critical line. -/
def RHUpToHeight (H : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2

theorem RHUpToHeight.mono {H K : ℝ} (hHK : H ≤ K) (hRH : RHUpToHeight K) :
    RHUpToHeight H := by
  intro ρ hz h0 h1 hH
  exact hRH ρ hz h0 h1 (hH.trans hHK)

theorem RHUpToHeight_three_e10_iff : RHUpToHeight 3e10 ↔ TernaryGoldbach.RHUpTo := Iff.rfl

noncomputable def lineBound (H a b δ : ℝ) : ℝ :=
  (Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (b / 2))) *
    (2 * ∑ m ∈ Finset.range (JlH 6 H), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ))))

noncomputable def tailBound (H a δ : ℝ) : ℝ :=
  EBg a δ H * (2 * Z3g BPz2 H / (1 - rhoG δ H) + 2 * c3g 10 H / (1 - rhoG δ H) ^ 2)

/-- **The explicit-formula bound for the smoothed sum.** -/
theorem smoothed_error_finiteRH {H : ℝ} (hRH : RHUpToHeight H) (hH : 0 < H) {a b δ x : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 ≤ x) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fun u => (gsm a b δ u : ℂ)) x - Mg a b δ 1 * x‖ ≤
      √x * lineBound H a b δ + x * tailBound H a δ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hM : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hgood hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      √x * lineBound H a b δ + x * tailBound H a δ := by
    intro T
    set Z := zerosRectD zetaF T with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
    have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
        ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0, hM]
    refine h1.trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ H)]
    refine add_le_add ?_ ?_
    · -- the line zeros
      set S := Z.filter (fun u => |u.im| ≤ H) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have hre : ∀ u ∈ S, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
        exact hRH u hz hr1 hr2 hu2
      have him : ∀ u ∈ S, |u.im| ≤ H := fun u hu => (Finset.mem_filter.1 hu).2
      have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
        intro u hu
        rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine line_sum_leH hH.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) S hSZ hre him
        (fun u => ‖Mg a b δ u‖) (fun u _ => norm_nonneg _) (by positivity) (fun u hu => ?_)
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hu']
      have := norm_Mg_line_le' a b δ u.im
      simpa using this
    · -- zeros above `3·10¹⁰`
      set S := Z.filter (fun u => ¬ |u.im| ≤ H) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have him : ∀ u ∈ S, H < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
      exact tail_sum_gauss hH hδ hb hx S hSZ him
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * lineBound H a b δ + x * tailBound H a δ :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k => hbound (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤ x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hZeta_gsm hδ hab hx0) (by positivity)
  have e : SsumG (1 : DirichletCharacter ℂ 1) φ x - Mg a b δ 1 * x =
      -((mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0) +
        (1 / (2 * π) : ℂ) * I0) := by rw [hM]; ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- The total explicit-formula error. -/
noncomputable def errorBound (H a b δ x : ℝ) : ℝ :=
  √x * lineBound H a b δ + x * tailBound H a δ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π)

theorem smoothed_sum_error_finiteRH {H : ℝ} (hRH : RHUpToHeight H) (hH : 0 < H) {a b δ x : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 ≤ x) :
    |∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x| ≤ errorBound H a b δ x := by
  have h := smoothed_error_finiteRH hRH hH hδ hab hb hx
  rw [SsumG_one_ofReal, Mg_one] at h
  rw [show ((∑' n : ℕ, Λ n * gsm a b δ (n / x) : ℝ) : ℂ) -
      ((Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) : ℝ) : ℂ) * (x : ℂ) =
      ((∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **Upper bound for `ψ`.** -/
theorem psi_upper_finiteRH {H : ℝ} (hRH : RHUpToHeight H) (hH : 0 < H) {δ K y0 x : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hK1 : 2 * Real.exp (-(K ^ 2 / 2)) < 1)
    (hy0 : 0 < y0) (hx : 1 ≤ x) (hYx : y0 * Real.exp (K * δ) ≤ x) :
    psiR x ≤ 4 * (y0 * Real.exp (K * δ)) +
      (Real.exp (δ ^ 2 / 2 + K * δ) * x + errorBound H (K * δ) (Real.log (y0 / x)) δ x) /
        (1 - 2 * Real.exp (-(K ^ 2 / 2))) := by
  have hx0 : 0 < x := by linarith
  have hb : Real.log (y0 / x) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one hx0).2
    (le_trans (le_mul_of_one_le_right hy0.le (Real.one_le_exp (by positivity))) hYx))
  have hab : Real.log (y0 / x) ≤ K * δ := hb.trans (by positivity)
  have hS := sandwich_upper hδ hK hy0 hx0 hYx (summable_gsm hδ hab hx0)
  have hT := smoothed_sum_error_finiteRH hRH hH hδ hab hb hx
  have hc : 0 < 1 - 2 * Real.exp (-(K ^ 2 / 2)) := by linarith
  have hmain : Real.exp (δ ^ 2 / 2) * (Real.exp (K * δ) - Real.exp (Real.log (y0 / x))) * x ≤
      Real.exp (δ ^ 2 / 2 + K * δ) * x := by
    rw [Real.exp_add]
    have hp : 0 < Real.exp (δ ^ 2 / 2) * Real.exp (Real.log (y0 / x)) * x :=
      mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hx0
    have e : Real.exp (δ ^ 2 / 2) * (Real.exp (K * δ) - Real.exp (Real.log (y0 / x))) * x =
        Real.exp (δ ^ 2 / 2) * Real.exp (K * δ) * x - Real.exp (δ ^ 2 / 2) * Real.exp (Real.log (y0 / x)) * x := by
      ring
    rw [e]; linarith
  have hsum : ∑' n : ℕ, Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) ≤
      Real.exp (δ ^ 2 / 2 + K * δ) * x + errorBound H (K * δ) (Real.log (y0 / x)) δ x := by
    have := (abs_le.1 hT).2; linarith
  have hY := psiR_le (y := y0 * Real.exp (K * δ)) (by positivity)
  have h1 : psiR x - psiR (y0 * Real.exp (K * δ)) ≤
      (Real.exp (δ ^ 2 / 2 + K * δ) * x + errorBound H (K * δ) (Real.log (y0 / x)) δ x) / (1 - 2 * Real.exp (-(K ^ 2 / 2))) := by
    rw [le_div_iff₀ hc]; nlinarith
  linarith

/-- **Lower bound for `ψ`.** -/
theorem psi_lower_finiteRH {H : ℝ} (hRH : RHUpToHeight H) (hH : 0 < H) {δ K y0 x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hKδ : δ ≤ K) (hy0 : 0 < y0)
    (hx : 1 ≤ x) (hb : Real.log (y0 / x) ≤ -(K * δ)) :
    Real.exp (-(K * δ)) * x - 2 * y0 - errorBound H (-(K * δ)) (Real.log (y0 / x)) δ x -
      4 * x * Real.exp (-(K ^ 2 / 2)) ≤ psiR x := by
  have hx0 : 0 < x := by linarith
  have hb0 : Real.log (y0 / x) ≤ 0 := hb.trans (by have : 0 ≤ K * δ := by nlinarith
                                                   linarith)
  have hS := sandwich_lower hδ hKδ hx0 hb
  have hT := smoothed_sum_error_finiteRH hRH hH hδ hb hb0 hx
  have he : Real.exp (Real.log (y0 / x)) = y0 / x := Real.exp_log (by positivity)
  rw [he] at hT
  have hd : Real.exp (δ ^ 2 / 2) ≤ 2 := by
    have : Real.exp (δ ^ 2 / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : Real.exp (1 / 2) ≤ 2 := by
      have := Real.exp_one_lt_d9
      have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    linarith
  have hd1 : 1 ≤ Real.exp (δ ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hmain : Real.exp (-(K * δ)) * x - 2 * y0 ≤
      Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) - y0 / x) * x := by
    have e : Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) - y0 / x) * x =
        Real.exp (δ ^ 2 / 2) * Real.exp (-(K * δ)) * x - Real.exp (δ ^ 2 / 2) * y0 := by
      field_simp
    rw [e]
    have hq : 0 ≤ Real.exp (-(K * δ)) * x := (mul_pos (Real.exp_pos _) hx0).le
    have h1 : 1 * (Real.exp (-(K * δ)) * x) ≤ Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) * x) :=
      mul_le_mul_of_nonneg_right hd1 hq
    have h2 : Real.exp (δ ^ 2 / 2) * y0 ≤ 2 * y0 := mul_le_mul_of_nonneg_right hd hy0.le
    have e2 : Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) * x) = Real.exp (δ ^ 2 / 2) * Real.exp (-(K * δ)) * x := by ring
    rw [e2, one_mul] at h1
    linarith
  have := (abs_le.1 hT).1
  linarith

end TernaryGoldbach.RSBounds
