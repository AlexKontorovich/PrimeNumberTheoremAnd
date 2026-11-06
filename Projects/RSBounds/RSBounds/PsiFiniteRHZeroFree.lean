import TernaryGoldbach.Explicit.PsiLarge
import RSBounds.PsiFiniteRH
import RSBounds.Theta

/-!
# The explicit formula using finite RH through height 1894439

The line zeros use only `RHUpToHeight 1894439`; the middle zeros use the
unconditional `R = 20` zero-free region proved in `RSBounds.Theta`.
The existing count through `3e10` is an upper bound for a subset, not an RH
premise at that height. The conclusion is a smoothed formula, not the b=23 row.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt
open TernaryGoldbach.Explicit

namespace TernaryGoldbach.RSBounds

/-- `x^β ≤ x e^{−log x/(20 log Γ)}` for zeros with `1894439 ≤ |γ| ≤ Γ`. -/
theorem rpow_re_le_zf_rs {x Γ : ℝ} (hx : 1 < x) {u : ℂ} (hu : xiF u = 0) (h1 : 1894439 ≤ |u.im|) (h2 : |u.im| ≤ Γ) :
    x ^ u.re ≤ x * Real.exp (-(Real.log x / (20 * Real.log Γ))) := by
  have hzf := zero_free_rs_height hu h1
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlg : 0 < Real.log |u.im| := Real.log_pos (by linarith)
  have hlΓ : Real.log |u.im| ≤ Real.log Γ := Real.log_le_log (by linarith) h2
  have hle : x ^ u.re ≤ x ^ (1 - 1 / (20 * Real.log |u.im|)) := Real.rpow_le_rpow_of_exponent_le hx.le hzf
  have e : x ^ (1 - 1 / (20 * Real.log |u.im|)) = x * Real.exp (-(Real.log x / (20 * Real.log |u.im|))) := by
    rw [Real.rpow_sub hx0, Real.rpow_one, Real.rpow_def_of_pos hx0, div_eq_mul_inv x, ← Real.exp_neg]
    congr 2; ring
  rw [e] at hle
  refine hle.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hx0.le)
  apply neg_le_neg
  apply div_le_div_of_nonneg_left hlx.le (by positivity)
  linarith

noncomputable def MidB0RS (a δ H₁ Γ x : ℝ) : ℝ :=
  2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (20 * Real.log Γ))) *
    ((⌊(Γ - H₁) / 4.4⌋₊ + 1) * (2 * Z3g BPz2 H₁ + 2 * c3g 10 H₁ * (⌊(Γ - H₁) / 4.4⌋₊ + 1)))

/-- The zero-free-region estimate for the zeros with `H₁ < |γ| ≤ Γ`, `H₁ ≥ 1894439`. -/
theorem mid_sum_le_rs {a b δ x H₁ Γ T : ℝ} (hb : b ≤ 0) (hx : 1 < x) (hH₁ : 1894439 ≤ H₁) (S : Finset ℂ)
    (hS : S ⊆ zerosRectD zetaF T) (him : ∀ u ∈ S, H₁ < |u.im| ∧ |u.im| ≤ Γ) :
    ∑ u ∈ S, (multRectD zetaF T u : ℝ) * (‖Mg a b δ u‖ * x ^ u.re) ≤ x * MidB0RS a δ H₁ Γ x := by
  have hH0 : 0 < H₁ := by linarith
  set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
  have hcount := count_mid hH0 S hS him
  have hpt : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
      m u * (2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (20 * Real.log Γ))) * x) := by
    intro u hu
    obtain ⟨hz, hr1, hr2, hxi⟩ := zerosRectD_zetaF_strip (hS hu)
    obtain ⟨hH, hG⟩ := him u hu
    have hγ0 : u.im ≠ 0 := by intro h; rw [h, abs_zero] at hH; linarith
    have hMs := norm_Mg_strip_le (a := a) (δ := δ) hb hr1 hr2 hγ0
    have hγ : 0 < |u.im| := abs_pos.2 hγ0
    have hMb : ‖Mg a b δ u‖ ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ := by
      have hg1 : Real.exp (-(δ ^ 2 * u.im ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have := sq_nonneg (δ * u.im); nlinarith)
      have : ‖Mg a b δ u‖ * |u.im| ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) := by
        have := mul_le_mul_of_nonneg_left hg1 (by positivity : (0:ℝ) ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|))
        linarith
      rw [le_div_iff₀ hH0]
      calc ‖Mg a b δ u‖ * H₁ ≤ ‖Mg a b δ u‖ * |u.im| := mul_le_mul_of_nonneg_left hH.le (norm_nonneg _)
        _ ≤ _ := this
    have hxr := rpow_re_le_zf_rs hx hxi (by linarith) hG
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖Mg a b δ u‖ * x ^ u.re ≤ (2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁) *
        (x * Real.exp (-(Real.log x / (20 * Real.log Γ)))) :=
          mul_le_mul hMb hxr (by positivity) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_mul]
  unfold MidB0RS
  have hC0 : 0 ≤ 2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (20 * Real.log Γ))) * x := by
    positivity
  calc (∑ u ∈ S, m u) * (2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (20 * Real.log Γ))) * x)
      ≤ ((⌊(Γ - H₁) / 4.4⌋₊ + 1) * (2 * Z3g BPz2 H₁ + 2 * c3g 10 H₁ * (⌊(Γ - H₁) / 4.4⌋₊ + 1))) *
        (2 * Real.exp (δ ^ 2 / 2 + |a|) / H₁ * Real.exp (-(Real.log x / (20 * Real.log Γ))) * x) :=
        mul_le_mul_of_nonneg_right hcount hC0
    _ = _ := by ring

/-- **The explicit-formula bound with the zero-free region.** -/
theorem smoothed_error_zf_rs (hRH : RHUpToHeight 1894439) {a b δ x Γ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 < x)
    (hΓ : 3e12 ≤ Γ) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fun u => (gsm a b δ u : ℂ)) x - Mg a b δ 1 * x‖ ≤
      √x * LineB a δ + x * MidB0RS a δ 1894439 Γ x + x * TailBG a δ Γ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hM : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hgood hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      √x * LineB a δ + x * MidB0RS a δ 1894439 Γ x + x * TailBG a δ Γ := by
    intro T
    set Z := zerosRectD zetaF T with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
    have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
        ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0, hM]
    refine h1.trans ?_
    set Z1 := Z.filter fun u => ¬ |u.im| ≤ 1894439 with hZ1
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ 1894439),
      ← Finset.sum_filter_add_sum_filter_not Z1 (fun u => |u.im| ≤ Γ)]
    have hZ1Z : Z1 ⊆ Z := Finset.filter_subset _ _
    have hA : ∑ u ∈ Z.filter (fun u => |u.im| ≤ 1894439), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤ √x * LineB a δ := by
      -- the line zeros (as in `SsumG_gsm_err`)
      set S := Z.filter (fun u => |u.im| ≤ 1894439) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have hre : ∀ u ∈ S, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
        exact hRH u hz hr1 hr2 hu2
      have him : ∀ u ∈ S, |u.im| ≤ 3e10 := fun u hu =>
        ((Finset.mem_filter.1 hu).2).trans (by norm_num)
      have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
        intro u hu
        rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine line_sum_le (by norm_num) S hSZ hre him (fun u => ‖Mg a b δ u‖) (fun u _ => norm_nonneg _)
        (by positivity) (fun u hu => ?_)
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hu']
      have := norm_Mg_line_le (δ := δ) hab hb u.im
      simpa using this
    have hB : ∑ u ∈ Z1.filter (fun u => |u.im| ≤ Γ), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * MidB0RS a δ 1894439 Γ x := by
      refine mid_sum_le_rs hb hx (by norm_num) _ ((Finset.filter_subset _ _).trans hZ1Z) fun u hu => ?_
      exact ⟨not_le.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hu).1).2, (Finset.mem_filter.1 hu).2⟩
    have hC : ∑ u ∈ Z1.filter (fun u => ¬ |u.im| ≤ Γ), m u * (‖Mg a b δ u‖ * x ^ u.re) ≤
        x * TailBG a δ Γ := by
      have hSZ := (Finset.filter_subset (fun u => ¬ |u.im| ≤ Γ) Z1).trans hZ1Z
      have him : ∀ u ∈ Z1.filter (fun u => ¬ |u.im| ≤ Γ), Γ < |u.im| := fun u hu =>
        not_le.1 (Finset.mem_filter.1 hu).2
      exact tail_sum_gauss (by linarith) hδ hb hx.le _ hSZ him
    linarith
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * LineB a δ + x * MidB0RS a δ 1894439 Γ x + x * TailBG a δ Γ :=
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

/-- The tsum version of `SsumG_gsm_err_zf`. -/
theorem smoothed_sum_error_zf_rs (hRH : RHUpToHeight 1894439) {a b δ x Γ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 < x) (hΓ : 3e12 ≤ Γ) :
    |∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x| ≤
      √x * LineB a δ + x * MidB0RS a δ 1894439 Γ x + x * TailBG a δ Γ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have h := smoothed_error_zf_rs hRH hδ hab hb hx hΓ
  rw [SsumG_one_ofReal, Mg_one] at h
  rw [show ((∑' n : ℕ, Λ n * gsm a b δ (n / x) : ℝ) : ℂ) -
      ((Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) : ℝ) : ℂ) * (x : ℂ) =
      ((∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end TernaryGoldbach.RSBounds
