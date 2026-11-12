module

public import HardyFirstZero.Spine
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The phase of `Γℝ` turns slowly (hunt `hardy_first_zero`, route P)

`Spine.lean` reduces the first zero to two inequalities. This file proves the one
about `Γ`, for any `0 < a < b` whose gap is small enough, with no evaluation of
`Γ` anywhere:

    0 < Re (Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib)).

**The route.** Write `z = 1/4 + ia/2`, `w = 1/4 - ib/2`, `δ = (b - a)/2`,
`K = ab/4` and `c_j = j + 1/4`. Up to the positive factor `π^{-1/2}`, the
product is `V = π^{iδ} Γ(z) Γ(w)`, and Euler's limit (`Complex.GammaSeq_tendsto_Gamma`)
gives `V = lim V_n` with `V_n = π^{iδ} GammaSeq z n · GammaSeq w n`. Each `V_n` is
explicit: `(z + j)(w + j) = (c_j² + K) - i δ c_j`, so

    V_n = R_n · exp(i φ_n),   φ_n = δ log π - δ log n + Σ_{j ≤ n} arctan(δ c_j / (c_j² + K)),

with `R_n > 0`. Elementary bounds (`arctan x ≤ x`, `arctan x ≥ x - x³`, the
harmonic-number bounds of `Mathlib.NumberTheory.Harmonic.Bounds`, `Σ 1/j² ≤ 2`)
confine every `φ_n`, `n ≥ 1`, to `[-(δ(1 + 2K) + 66 δ³), δ(π + 4)]`, so
`Re V_n ≥ cos L · ‖V_n‖` with `L < π/2`, and the inequality survives the limit.

The window is crude on purpose: at `a = 14.13`, `b = 14.14` the true phase
increment is `-0.00405` while the window is `[-0.5045, 0.0357]`. Nothing here
needs the digamma function or Stirling's formula.
-/

open Complex Finset Filter
open scoped ComplexConjugate Topology

namespace HardyFirstZero

/-! ### One factor in polar form -/

/-- `A - iB = √(A² + B²) · exp(-i · arctan(B/A))` for `A > 0`. -/
lemma polar_of_re_pos {A B : ℝ} (hA : 0 < A) :
    ((A : ℂ) - (B : ℂ) * I)
      = ((Real.sqrt (A ^ 2 + B ^ 2) : ℝ) : ℂ) * exp (-(Real.arctan (B / A) : ℂ) * I) := by
  set θ := Real.arctan (B / A) with hθ
  have hsq : Real.sqrt (A ^ 2 + B ^ 2) = A * Real.sqrt (1 + (B / A) ^ 2) := by
    rw [show A ^ 2 + B ^ 2 = A ^ 2 * (1 + (B / A) ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le]
  have hs1 : 0 < Real.sqrt (1 + (B / A) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcos : Real.cos θ = 1 / Real.sqrt (1 + (B / A) ^ 2) := Real.cos_arctan _
  have hsin : Real.sin θ = B / A / Real.sqrt (1 + (B / A) ^ 2) := Real.sin_arctan _
  have hexp : exp (-(θ : ℂ) * I) = ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * I := by
    rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hexp, hcos, hsin, hsq]
  apply Complex.ext <;> simp <;> field_simp

/-! ### The data of the partial products -/

/-- `δ = (b - a)/2`. -/
noncomputable def dl (a b : ℝ) : ℝ := (b - a) / 2

/-- `c_j = j + 1/4`. -/
noncomputable def cj (j : ℕ) : ℝ := j + 1 / 4

/-- `A_j = c_j² + ab/4`, the real part of `(z + j)(w + j)`. -/
noncomputable def Aj (a b : ℝ) (j : ℕ) : ℝ := cj j ^ 2 + a * b / 4

/-- The phase contributed by the `j`-th factor. -/
noncomputable def psi (a b : ℝ) (j : ℕ) : ℝ := Real.arctan (dl a b * cj j / Aj a b j)

/-- The modulus of the `j`-th factor. -/
noncomputable def rj (a b : ℝ) (j : ℕ) : ℝ := Real.sqrt (Aj a b j ^ 2 + (dl a b * cj j) ^ 2)

/-- The partial phase `φ_n = δ log π - δ log n + Σ_{j ≤ n} ψ_j`. -/
noncomputable def phi (a b : ℝ) (n : ℕ) : ℝ :=
  dl a b * Real.log Real.pi - dl a b * Real.log n + ∑ j ∈ range (n + 1), psi a b j

/-- `z = 1/4 + ia/2`, half of `1/2 + ia`. -/
noncomputable def zA (a : ℝ) : ℂ := 1 / 4 + ((a / 2 : ℝ) : ℂ) * I

/-- `w = 1/4 - ib/2`, the conjugate of half of `1/2 + ib`. -/
noncomputable def wB (b : ℝ) : ℂ := 1 / 4 - ((b / 2 : ℝ) : ℂ) * I

/-- The constant `π^{-1/2 + iδ}`, written as an exponential. -/
noncomputable def cpi (a b : ℝ) : ℂ :=
  exp ((Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I))

lemma cj_pos (j : ℕ) : 0 < cj j := by unfold cj; positivity

lemma Aj_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : ℕ) : 0 < Aj a b j := by
  unfold Aj; have := cj_pos j; positivity

lemma zA_re (a : ℝ) : (zA a).re = 1 / 4 := by simp [zA]

lemma wB_re (b : ℝ) : (wB b).re = 1 / 4 := by simp [wB]

/-- `(z + j)(w + j) = A_j - i δ c_j`. -/
lemma factor_eq (a b : ℝ) (j : ℕ) :
    (zA a + j) * (wB b + j) = (Aj a b j : ℂ) - ((dl a b * cj j : ℝ) : ℂ) * I := by
  unfold zA wB Aj dl cj
  push_cast
  linear_combination (-(a : ℂ) * b / 4) * Complex.I_sq

/-- Each factor in polar form. -/
lemma factor_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : ℕ) :
    (zA a + j) * (wB b + j) = (rj a b j : ℂ) * exp (-(psi a b j : ℂ) * I) := by
  rw [factor_eq]
  exact polar_of_re_pos (Aj_pos ha hb j)

/-- The product of the factors in polar form. -/
lemma prod_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (∏ j ∈ range (n + 1), (zA a + j)) * (∏ j ∈ range (n + 1), (wB b + j))
      = ((∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
        * exp (-(((∑ j ∈ range (n + 1), psi a b j : ℝ)) : ℂ) * I) := by
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun j _ => factor_polar ha hb j),
    Finset.prod_mul_distrib, Complex.ofReal_prod]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]

/-- `n^z n^w = exp(log n · (1/2 - iδ))` for `n ≥ 1`. -/
lemma cpow_pair {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    (n : ℂ) ^ zA a * (n : ℂ) ^ wB b
      = exp ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← cpow_add _ _ hn', cpow_def_of_ne_zero hn', ← Complex.natCast_log]
  congr 1
  unfold zA wB dl
  push_cast
  ring

/-- The partial product `V_n = π^{-1/2+iδ} GammaSeq z n · GammaSeq w n`. -/
noncomputable def Vn (a b : ℝ) (n : ℕ) : ℂ :=
  cpi a b * (GammaSeq (zA a) n * GammaSeq (wB b) n)

lemma factor_ne_zero_A (a : ℝ) (j : ℕ) : zA a + j ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [zA] at this
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

lemma factor_ne_zero_B (b : ℝ) (j : ℕ) : wB b + j ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [wB] at this
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- **`V_n` in polar form**: a positive real times `exp(x + iφ_n)`. -/
lemma Vn_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    Vn a b n = (((n.factorial : ℝ) ^ 2 / ∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
      * exp (((Real.log n - Real.log Real.pi) / 2 : ℝ) + (phi a b n : ℂ) * I) := by
  have hPA : (∏ j ∈ range (n + 1), (zA a + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => factor_ne_zero_A a j
  have hPB : (∏ j ∈ range (n + 1), (wB b + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => factor_ne_zero_B b j
  have hr : (((∏ j ∈ range (n + 1), rj a b j : ℝ)) : ℂ) ≠ 0 := by
    have hpp := prod_polar ha hb n
    intro h0
    rw [h0, zero_mul] at hpp
    exact mul_ne_zero hPA hPB hpp
  have hsplit : Vn a b n
      = cpi a b * ((n : ℂ) ^ zA a * (n : ℂ) ^ wB b) * ((n.factorial : ℂ) ^ 2)
        / ((∏ j ∈ range (n + 1), (zA a + j)) * (∏ j ∈ range (n + 1), (wB b + j))) := by
    unfold Vn GammaSeq
    field_simp
  rw [hsplit, cpow_pair hn, prod_polar ha hb n]
  have hE : ((((Real.log n - Real.log Real.pi) / 2 : ℝ) : ℂ) + (phi a b n : ℂ) * I)
      = (Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I)
        + ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I)
        + ((∑ j ∈ range (n + 1), psi a b j : ℝ) : ℂ) * I) := by
    unfold phi
    push_cast
    ring
  rw [hE, Complex.exp_add, Complex.exp_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  unfold cpi
  set X := exp ((Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I))
  set Y := exp ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I))
  set Θ : ℂ := ((∑ j ∈ range (n + 1), psi a b j : ℝ) : ℂ)
  set P : ℂ := ((∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
  have hinv : exp (Θ * I) = (exp (-Θ * I))⁻¹ := by
    rw [← Complex.exp_neg, neg_mul, neg_neg]
  have hne : exp (-Θ * I) ≠ 0 := Complex.exp_ne_zero _
  rw [hinv]
  field_simp

/-- `Re (R e^{x + iy}) = ‖R e^{x + iy}‖ cos y` for `R ≥ 0`. -/
lemma re_eq_norm_mul_cos {R : ℝ} (hR : 0 ≤ R) (x y : ℝ) :
    ((R : ℂ) * exp ((x : ℂ) + (y : ℂ) * I)).re
      = ‖(R : ℂ) * exp ((x : ℂ) + (y : ℂ) * I)‖ * Real.cos y := by
  rw [Complex.re_ofReal_mul, Complex.exp_re, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hR]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  ring

lemma Vn_re {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    (Vn a b n).re = ‖Vn a b n‖ * Real.cos (phi a b n) := by
  have hR : 0 ≤ (n.factorial : ℝ) ^ 2 / ∏ j ∈ range (n + 1), rj a b j :=
    div_nonneg (by positivity)
      (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _)
  rw [Vn_polar ha hb hn]
  exact re_eq_norm_mul_cos hR _ _

/-! ### Elementary bounds on the partial phase -/

lemma arctan_ge_sub_cube {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 ≤ Real.arctan x := by
  have h1 : Real.sin (Real.arctan x) ≤ Real.arctan x :=
    Real.sin_le (Real.arctan_nonneg.mpr hx)
  rw [Real.sin_arctan] at h1
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hs : Real.sqrt (1 + x ^ 2) ≤ 1 + x ^ 2 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by nlinarith [sq_nonneg x]))
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hpos
  have h2 : x / (1 + x ^ 2) ≤ x / Real.sqrt (1 + x ^ 2) :=
    div_le_div_of_nonneg_left hx hspos hs
  have h3 : x - x ^ 3 ≤ x / (1 + x ^ 2) := by
    rw [le_div_iff₀ hpos]
    nlinarith [pow_nonneg hx 5, sq_nonneg x]
  linarith

/-- `x_j = δ c_j / A_j`, the argument of the `j`-th arctangent. -/
noncomputable def xj (a b : ℝ) (j : ℕ) : ℝ := dl a b * cj j / Aj a b j

lemma xj_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : 0 ≤ xj a b j := by
  unfold xj dl
  have := Aj_pos ha (ha.trans hab) j
  have := cj_pos j
  have : 0 ≤ b - a := by linarith
  positivity

lemma xj_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : xj a b j ≤ dl a b / cj j := by
  have hc := cj_pos j
  have hA := Aj_pos ha (ha.trans hab) j
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  unfold xj
  rw [div_le_div_iff₀ hA hc]
  have : cj j ^ 2 ≤ Aj a b j := by
    unfold Aj; have : 0 ≤ a * b := mul_nonneg ha (ha.trans hab); linarith
  nlinarith

/-- `x_j ≥ δ (1/c_j - K/c_j³)`. -/
lemma xj_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) :
    dl a b * (1 / cj j - (a * b / 4) / cj j ^ 3) ≤ xj a b j := by
  have hc := cj_pos j
  have hA := Aj_pos ha (ha.trans hab) j
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hK : 0 ≤ a * b / 4 := by have := mul_nonneg ha (ha.trans hab); linarith
  have hx : xj a b j = dl a b * (cj j / Aj a b j) := by unfold xj; ring
  rw [hx]
  refine mul_le_mul_of_nonneg_left ?_ hd
  have hA' : Aj a b j = cj j ^ 2 + a * b / 4 := rfl
  have he : 1 / cj j - (a * b / 4) / cj j ^ 3 = (cj j ^ 2 - a * b / 4) / cj j ^ 3 := by
    field_simp
  rw [he, div_le_div_iff₀ (pow_pos hc 3) hA, hA']
  nlinarith [sq_nonneg (a * b / 4), pow_pos hc 4]

lemma psi_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : psi a b j ≤ xj a b j :=
  Real.arctan_le_self (xj_nonneg ha hab j)

lemma psi_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) :
    xj a b j - xj a b j ^ 3 ≤ psi a b j :=
  arctan_ge_sub_cube (xj_nonneg ha hab j)

/-- `Σ_{j<n} 1/(j+1)² ≤ 2`, in the form the induction wants. -/
lemma sum_inv_sq_le_aux (n : ℕ) :
    ∑ j ∈ range (n + 1), 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have key : 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2
        ≤ 1 / ((n : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at key ⊢
    linarith

lemma sum_inv_sq_le (n : ℕ) : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  rcases n with _ | n
  · simp
  · have := sum_inv_sq_le_aux n
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- `Σ_{j ≤ n} 1/c_j ≤ 5 + log n`. -/
lemma sum_inv_cj_le (n : ℕ) : ∑ j ∈ range (n + 1), 1 / cj j ≤ 5 + Real.log n := by
  rw [Finset.sum_range_succ']
  have h0 : 1 / cj 0 = 4 := by unfold cj; norm_num
  have hterm : ∀ j ∈ range n, 1 / cj (j + 1) ≤ 1 / ((j : ℝ) + 1) := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hH : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) = (harmonic n : ℝ) := by
    simp [harmonic]
  have := harmonic_le_one_add_log n
  have := Finset.sum_le_sum hterm
  rw [h0]
  linarith

/-- `Σ_{j ≤ n} 1/c_j³ ≤ 66`. -/
lemma sum_inv_cj_cube_le (n : ℕ) : ∑ j ∈ range (n + 1), 1 / cj j ^ 3 ≤ 66 := by
  rw [Finset.sum_range_succ']
  have h0 : 1 / cj 0 ^ 3 = 64 := by unfold cj; norm_num
  have hterm : ∀ j ∈ range n, 1 / cj (j + 1) ^ 3 ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    have h2 : (j : ℝ) + 1 ≤ (j : ℝ) + 1 + 1 / 4 := by linarith
    calc ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 3 := by
          nlinarith [pow_le_pow_right₀ h1 (show 2 ≤ 3 by norm_num)]
      _ ≤ ((j : ℝ) + 1 + 1 / 4) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
  have := Finset.sum_le_sum hterm
  have := sum_inv_sq_le n
  rw [h0]
  linarith

/-- `Σ_{j<n} 1/c_{j+1} ≥ log n - 1` for `n ≥ 1`. -/
lemma sum_inv_cj_succ_ge {n : ℕ} (hn : n ≠ 0) :
    Real.log n - 1 ≤ ∑ j ∈ range n, 1 / cj (j + 1) := by
  have hterm : ∀ j ∈ range n, 1 / ((j : ℝ) + 2) ≤ 1 / cj (j + 1) := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hH : (harmonic (n + 1) : ℝ) = 1 + ∑ j ∈ range n, 1 / ((j : ℝ) + 2) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [Finset.sum_range_succ']
    push_cast
    rw [add_comm]
    congr 1
    · norm_num
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_div]
      ring_nf
  have hlog := log_add_one_le_harmonic (n + 1)
  have hmono : Real.log n ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have := Finset.sum_le_sum hterm
  push_cast at hlog hmono
  linarith

/-- **Upper end of the window**: `φ_n ≤ δ(log π + 5)`. -/
lemma phi_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    phi a b n ≤ dl a b * (Real.log Real.pi + 5) := by
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have h1 : ∑ j ∈ range (n + 1), psi a b j ≤ ∑ j ∈ range (n + 1), dl a b * (1 / cj j) :=
    Finset.sum_le_sum fun j _ =>
      (psi_le ha hab j).trans ((xj_le ha hab j).trans (by rw [mul_one_div]))
  rw [← Finset.mul_sum] at h1
  have h2 := mul_le_mul_of_nonneg_left (sum_inv_cj_le n) hd
  unfold phi
  nlinarith

/-- **Lower end of the window**: `φ_n ≥ δ(log π - 1 - 2K) - 66 δ³` for `n ≥ 1`. -/
lemma le_phi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {n : ℕ} (hn : n ≠ 0) :
    dl a b * (Real.log Real.pi - 1 - 2 * (a * b / 4)) - 66 * dl a b ^ 3 ≤ phi a b n := by
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hK : 0 ≤ a * b / 4 := by have := mul_nonneg ha (ha.trans hab); linarith
  -- the arctangents against the linear terms, minus the cubes
  have h1 : ∑ j ∈ range (n + 1), (xj a b j - xj a b j ^ 3) ≤ ∑ j ∈ range (n + 1), psi a b j :=
    Finset.sum_le_sum fun j _ => psi_ge ha hab j
  rw [Finset.sum_sub_distrib] at h1
  -- the cubes
  have h2 : ∑ j ∈ range (n + 1), xj a b j ^ 3 ≤ dl a b ^ 3 * 66 := by
    have : ∀ j ∈ range (n + 1), xj a b j ^ 3 ≤ dl a b ^ 3 * (1 / cj j ^ 3) := by
      intro j _
      have hx := xj_le ha hab j
      have hx0 := xj_nonneg ha hab j
      calc xj a b j ^ 3 ≤ (dl a b / cj j) ^ 3 := pow_le_pow_left₀ hx0 hx 3
        _ = dl a b ^ 3 * (1 / cj j ^ 3) := by rw [div_pow]; ring
    calc ∑ j ∈ range (n + 1), xj a b j ^ 3
        ≤ ∑ j ∈ range (n + 1), dl a b ^ 3 * (1 / cj j ^ 3) := Finset.sum_le_sum this
      _ = dl a b ^ 3 * ∑ j ∈ range (n + 1), 1 / cj j ^ 3 := by rw [Finset.mul_sum]
      _ ≤ dl a b ^ 3 * 66 :=
          mul_le_mul_of_nonneg_left (sum_inv_cj_cube_le n) (pow_nonneg hd 3)
  -- the linear terms, dropping `j = 0`
  have h3 : ∑ j ∈ range n, xj a b (j + 1) ≤ ∑ j ∈ range (n + 1), xj a b j := by
    rw [Finset.sum_range_succ' (fun j => xj a b j)]
    linarith [xj_nonneg ha hab 0]
  have h4 : ∑ j ∈ range n, dl a b * (1 / cj (j + 1) - (a * b / 4) / cj (j + 1) ^ 3)
      ≤ ∑ j ∈ range n, xj a b (j + 1) :=
    Finset.sum_le_sum fun j _ => xj_ge ha hab (j + 1)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at h4
  have h5 : ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3 ≤ (a * b / 4) * 2 := by
    have : ∀ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3 ≤ (a * b / 4) * (1 / ((j : ℝ) + 1) ^ 2) := by
      intro j _
      rw [div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ hK
      unfold cj
      push_cast
      apply one_div_le_one_div_of_le (by positivity)
      have h1' : (1 : ℝ) ≤ (j : ℝ) + 1 := by
        have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      calc ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 3 := by
            nlinarith [pow_le_pow_right₀ h1' (show 2 ≤ 3 by norm_num)]
        _ ≤ ((j : ℝ) + 1 + 1 / 4) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    calc ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3
        ≤ ∑ j ∈ range n, (a * b / 4) * (1 / ((j : ℝ) + 1) ^ 2) := Finset.sum_le_sum this
      _ = (a * b / 4) * ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (a * b / 4) * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le n) hK
  have h6 := sum_inv_cj_succ_ge hn
  have h7 : dl a b * (Real.log n - 1 - (a * b / 4) * 2)
      ≤ dl a b * (∑ j ∈ range n, 1 / cj (j + 1) - ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hd
  unfold phi
  nlinarith

/-! ### From the partial products to `Γℝ` -/

lemma sOf_half (t : ℝ) : sOf t / 2 = zA t := by
  unfold sOf zA; push_cast; ring

lemma conj_sOf_half (t : ℝ) : conj (sOf t / 2) = wB t := by
  unfold sOf wB
  rw [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    map_div₀, map_one, map_ofNat]
  push_cast
  ring

/-- `Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib) = π^{-1/2 + iδ} Γ(z) Γ(w)`. -/
lemma gammaR_prod (a b : ℝ) :
    Gammaℝ (sOf a) * conj (Gammaℝ (sOf b)) = cpi a b * (Gamma (zA a) * Gamma (wB b)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlog : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj, sOf_half, conj_sOf_half,
    cpow_def_of_ne_zero hpi, cpow_def_of_ne_zero hpi, hlog, ← Complex.exp_conj]
  have hc : exp ((Real.log Real.pi : ℂ) * (-sOf a / 2))
      * exp (conj ((Real.log Real.pi : ℂ) * (-sOf b / 2))) = cpi a b := by
    rw [← Complex.exp_add]
    unfold cpi
    congr 1
    rw [map_mul, Complex.conj_ofReal, map_div₀, map_neg, map_ofNat]
    unfold sOf dl
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]
    push_cast
    ring
  rw [← hc]
  ring

lemma tendsto_Vn (a b : ℝ) :
    Tendsto (Vn a b) atTop (𝓝 (cpi a b * (Gamma (zA a) * Gamma (wB b)))) :=
  ((GammaSeq_tendsto_Gamma _).mul (GammaSeq_tendsto_Gamma _)).const_mul _

/-- **The phase lemma.** If the explicit window `[-L, L]` with `L < π/2` holds the
two ends of the partial-phase bounds, the product of the two `Γℝ` values has
positive real part. No value of `Γ` is used. -/
theorem gammaR_re_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {L : ℝ}
    (hL : L < Real.pi / 2)
    (hup : dl a b * (Real.log Real.pi + 5) ≤ L)
    (hlo : -L ≤ dl a b * (Real.log Real.pi - 1 - 2 * (a * b / 4)) - 66 * dl a b ^ 3) :
    0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re := by
  rw [gammaR_prod]
  set V := cpi a b * (Gamma (zA a) * Gamma (wB b)) with hVdef
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hL0 : 0 ≤ L := le_trans (mul_nonneg hd (by linarith)) hup
  have hcosL : 0 < Real.cos L :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hL⟩
  have hev : ∀ᶠ n in atTop, Real.cos L * ‖Vn a b n‖ ≤ (Vn a b n).re := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : n ≠ 0 := by omega
    rw [Vn_re ha (ha.trans hab) hn0]
    have hphi : |phi a b n| ≤ L :=
      abs_le.mpr ⟨hlo.trans (le_phi ha hab hn0), (phi_le ha hab n).trans hup⟩
    have hcos : Real.cos L ≤ Real.cos (phi a b n) := by
      rw [← Real.cos_abs (phi a b n)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) hphi
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
  have hlim := tendsto_Vn a b
  have hre : Tendsto (fun n => (Vn a b n).re) atTop (𝓝 V.re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  have hnorm : Tendsto (fun n => Real.cos L * ‖Vn a b n‖) atTop (𝓝 (Real.cos L * ‖V‖)) :=
    hlim.norm.const_mul _
  have hle : Real.cos L * ‖V‖ ≤ V.re := le_of_tendsto_of_tendsto hnorm hre hev
  have hV : V ≠ 0 := by
    refine mul_ne_zero (by unfold cpi; exact Complex.exp_ne_zero _) (mul_ne_zero ?_ ?_)
    · exact Gamma_ne_zero_of_re_pos (by rw [zA_re]; norm_num)
    · exact Gamma_ne_zero_of_re_pos (by rw [wB_re]; norm_num)
  have : 0 < Real.cos L * ‖V‖ := mul_pos hcosL (norm_pos_iff.mpr hV)
  linarith

/-- **The phase lemma at the planned endpoints** `a = 14.13`, `b = 14.14`, with
`L = 11/20`: the window is `[-0.5045, 0.0357]` against the true increment
`-0.00405` (`sizing.py`). -/
theorem gammaR_re_pos_first :
    0 < (Gammaℝ (sOf (1413 / 100)) * conj (Gammaℝ (sOf (707 / 50)))).re := by
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogpi' : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  refine gammaR_re_pos (L := 11 / 20) (by norm_num) (by norm_num) (by linarith) ?_ ?_
  · unfold dl; nlinarith
  · unfold dl; nlinarith

/-- **The target, conditional on one inequality.** A zero of `ζ` on the critical line
with ordinate strictly between `14.13` and `14.14`, given only that
`ζ(1/2 + 14.13i) · conj ζ(1/2 + 14.14i)` has negative real part. That hypothesis is
the open work of the hunt (`RESULTS.md`, section 5); this theorem is not the target
until it is discharged. -/
theorem first_zero_on_line_of_zeta_product
    (hX : (riemannZeta (sOf (1413 / 100)) * conj (riemannZeta (sOf (707 / 50)))).re < 0) :
    ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50), riemannZeta (1 / 2 + t * I) = 0 :=
  exists_zero_of_sign_data (by norm_num) hX gammaR_re_pos_first

end HardyFirstZero
