import PrimeNumberTheoremAnd.IEANTN.KadiriU6aFarTail
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# U6a count atom: the local zero count `N(t+1) - N(t) = O(log t)`

This file discharges `Kadiri.U6aLocalZeroCountLogHypothesis`, the single
analytic atom left open by `KadiriU6aFarTail`.  The chain:

1. Euler reflection at the critical line: `‖Γ(1/2 + iu)‖² = π / cosh(πu)`,
   via `Γ(z)Γ(1-z) = π/sin(πz)` and `1 - z = conj z` on `Re z = 1/2`.
2. Gronwall transport of `‖Γ‖` across the strip `Re ∈ [1/2, 7/2]` along the
   digamma logarithmic-derivative bound `‖ψ(σ+it)‖ ≤ C log(|t|+2)`.
3. The packaged product `‖Γ(s) cos(πs/2)‖ ≤ √π (|Im s|+2)^B` on the strip:
   the exponential decay of `Γ` at the left edge exactly cancels the
   exponential growth of `cos`, through `cosh(x)² ≤ cosh(2x)`.
4. The functional equation then gives polynomial growth of `ζ` on
   `Re ∈ [-5/2, 1/2]`; the Abel-summation bound covers `Re ∈ [1/2, 13/2]`.
5. A Jensen disk of radius `9/4` centered at `2 + it` (max-modulus form of
   the divisor-mass bound, fed by the band estimate and the Dirichlet-series
   lower bound `‖ζ(2+it)‖ ≥ 1/4`) counts the order-weighted zeros in the
   Kadiri window, yielding `u6aNearbyZeroCount (-1) 2 t ≤ C log |t|`.
-/

namespace Kadiri

open Complex

noncomputable section

/-! ## Reflection at the critical line -/

private lemma u6aCA_one_sub_eq_conj (u : ℝ) :
    (1 : ℂ) - (1 / 2 + u * I) = starRingEnd ℂ (1 / 2 + u * I) := by
  apply Complex.ext
  · simp
    norm_num
  · simp

/-- Euler reflection on the critical line: `‖Γ(1/2 + iu)‖² = π / cosh(πu)`. -/
theorem u6aCA_norm_sq_gamma_half (u : ℝ) :
    ‖Complex.Gamma (1 / 2 + u * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * u) := by
  set z : ℂ := 1 / 2 + u * I with hz
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  rw [hz] at hrefl
  rw [u6aCA_one_sub_eq_conj u] at hrefl
  rw [Complex.Gamma_conj, Complex.mul_conj] at hrefl
  have hsin : Complex.sin (↑Real.pi * (1 / 2 + u * I)) = ↑(Real.cosh (Real.pi * u)) := by
    have hexp : (↑Real.pi : ℂ) * (1 / 2 + u * I) =
        ↑Real.pi / 2 + ↑(Real.pi * u) * I := by
      push_cast
      ring
    rw [hexp, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
      Complex.cos_mul_I, Complex.ofReal_cosh]
    ring
  rw [hsin, ← Complex.ofReal_div] at hrefl
  have hreal : Complex.normSq (Complex.Gamma (1 / 2 + u * I)) =
      Real.pi / Real.cosh (Real.pi * u) := by
    exact_mod_cast hrefl
  rw [← Complex.normSq_eq_norm_sq]
  exact hreal

/-- The cosine grows at most like `cosh` of the imaginary part. -/
theorem u6aCA_norm_cos_le_cosh (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ ≤
      Real.exp (-z.im) + Real.exp z.im := by
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_exp, Complex.norm_exp]
    have he1 : (z * I).re = -z.im := Complex.mul_I_re z
    have he2 : (-z * I).re = z.im := by
      rw [neg_mul, Complex.neg_re, Complex.mul_I_re]
      ring
    rw [he1, he2]
  rw [norm_div, Real.cosh_eq]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have h3 : Real.exp (-z.im) + Real.exp z.im = Real.exp z.im + Real.exp (-z.im) := by ring
  rw [h3] at h1
  linarith

/-- The exact cancellation: the critical-line value of `‖Γ‖` times the cosh
growth of the half-angle cosine stays below `√π`. -/
theorem u6aCA_norm_gamma_half_mul_cosh_le (u : ℝ) :
    ‖Complex.Gamma (1 / 2 + u * I)‖ * Real.cosh (Real.pi * u / 2) ≤
      Real.sqrt Real.pi := by
  have hsq := u6aCA_norm_sq_gamma_half u
  have hcosh2 : Real.cosh (Real.pi * u / 2) ^ 2 ≤ Real.cosh (Real.pi * u) := by
    have hdouble := Real.cosh_two_mul (Real.pi * u / 2)
    have h2 : 2 * (Real.pi * u / 2) = Real.pi * u := by ring
    rw [h2] at hdouble
    nlinarith [sq_nonneg (Real.sinh (Real.pi * u / 2))]
  have hpos : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
  rw [Real.le_sqrt (by positivity) Real.pi_pos.le]
  have hexpand : (‖Complex.Gamma (1 / 2 + u * I)‖ * Real.cosh (Real.pi * u / 2)) ^ 2 =
      Real.pi / Real.cosh (Real.pi * u) * Real.cosh (Real.pi * u / 2) ^ 2 := by
    rw [mul_pow, hsq]
  rw [hexpand, div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [hcosh2, Real.pi_pos]

/-! ## Gronwall transport across the strip -/

/-- The vertical line `Re = σ` parametrization of `Γ` is differentiable in
`σ`, with logarithmic derivative `digamma`. -/
private lemma u6aCA_hasDerivAt_gamma_line {u : ℝ} (t : ℝ) (hu : 1 / 2 ≤ u) :
    HasDerivAt (fun v : ℝ => Complex.Gamma (↑v + ↑t * I))
      (Complex.Gamma (↑u + ↑t * I) * Complex.digamma (↑u + ↑t * I)) u := by
  have hz : ∀ m : ℕ, (↑u + ↑t * I : ℂ) ≠ -↑m := by
    intro m hc
    have hre := congrArg Complex.re hc
    simp at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hdiff : DifferentiableAt ℂ Complex.Gamma (↑u + ↑t * I) :=
    Complex.differentiableAt_Gamma _ hz
  have hΓval : Complex.Gamma (↑u + ↑t * I) * Complex.digamma (↑u + ↑t * I) =
      deriv Complex.Gamma (↑u + ↑t * I) := by
    rw [Complex.digamma_def, logDeriv_apply,
      mul_div_cancel₀ _ (Complex.Gamma_ne_zero hz)]
  have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma (↑u + ↑t * I))
      (↑u + ↑t * I) := hdiff.hasDerivAt
  have hshift : HasDerivAt (fun w : ℂ => w + ↑t * I) 1 ↑u :=
    (hasDerivAt_id (↑u : ℂ)).add_const _
  have hcomp : HasDerivAt (fun w : ℂ => Complex.Gamma (w + ↑t * I))
      (deriv Complex.Gamma (↑u + ↑t * I) * 1) ↑u := by
    have := HasDerivAt.comp (h₂ := Complex.Gamma) (h := fun w : ℂ => w + ↑t * I)
      ((↑u : ℂ)) hΓ hshift
    simpa [Function.comp_def] using this
  rw [mul_one] at hcomp
  have hreal := HasDerivAt.comp_ofReal (e := fun w : ℂ => Complex.Gamma (w + ↑t * I))
    (e' := deriv Complex.Gamma (↑u + ↑t * I)) (z := u) hcomp
  rw [← hΓval] at hreal
  exact hreal

/-- Gronwall transport of `‖Γ‖` from the critical line across `Re ∈ [1/2, 7/2]`:
the digamma strip bound is the Gronwall constant, so the strip only costs a
polynomial factor `(|t|+2)^(3K)`. -/
theorem u6aCA_exists_gamma_transport :
    ∃ K : ℝ, 0 < K ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 7 / 2 →
      ‖Complex.Gamma (↑σ + ↑t * I)‖ ≤
        ‖Complex.Gamma (1 / 2 + ↑t * I)‖ * (|t| + 2) ^ (3 * K) := by
  obtain ⟨K, hK0, hψ⟩ := Complex.exists_norm_digamma_le_log (a := 1 / 2) (b := 7 / 2)
    (by norm_num)
  refine ⟨K, hK0, fun σ t hσ1 hσ2 => ?_⟩
  have hlog2 : 0 < Real.log (|t| + 2) :=
    Real.log_pos (by linarith [abs_nonneg t])
  have hcont : ContinuousOn (fun v : ℝ => Complex.Gamma (↑v + ↑t * I))
      (Set.Icc (1 / 2 : ℝ) (7 / 2)) := fun v hv =>
    ((u6aCA_hasDerivAt_gamma_line t hv.1).continuousAt).continuousWithinAt
  have hder : ∀ v ∈ Set.Ico (1 / 2 : ℝ) (7 / 2),
      HasDerivWithinAt (fun v : ℝ => Complex.Gamma (↑v + ↑t * I))
        (Complex.Gamma (↑v + ↑t * I) * Complex.digamma (↑v + ↑t * I))
        (Set.Ici v) v := fun v hv =>
    (u6aCA_hasDerivAt_gamma_line t hv.1).hasDerivWithinAt
  have hbound : ∀ v ∈ Set.Ico (1 / 2 : ℝ) (7 / 2),
      ‖Complex.Gamma (↑v + ↑t * I) * Complex.digamma (↑v + ↑t * I)‖ ≤
        K * Real.log (|t| + 2) * ‖Complex.Gamma (↑v + ↑t * I)‖ + 0 := by
    intro v hv
    rw [norm_mul, add_zero]
    have hre : (↑v + ↑t * I : ℂ).re = v := by simp
    have him : (↑v + ↑t * I : ℂ).im = t := by simp
    have hψv := hψ (↑v + ↑t * I) (by rw [hre]; exact hv.1) (by rw [hre]; exact hv.2.le)
    rw [him] at hψv
    calc ‖Complex.Gamma (↑v + ↑t * I)‖ * ‖Complex.digamma (↑v + ↑t * I)‖
        ≤ ‖Complex.Gamma (↑v + ↑t * I)‖ * (K * Real.log (|t| + 2)) :=
          mul_le_mul_of_nonneg_left hψv (norm_nonneg _)
      _ = K * Real.log (|t| + 2) * ‖Complex.Gamma (↑v + ↑t * I)‖ := by ring
  have key := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun v : ℝ => Complex.Gamma (↑v + ↑t * I))
    (f' := fun v : ℝ => Complex.Gamma (↑v + ↑t * I) * Complex.digamma (↑v + ↑t * I))
    (δ := ‖Complex.Gamma (↑(1 / 2 : ℝ) + ↑t * I)‖) (K := K * Real.log (|t| + 2))
    (ε := 0) (a := 1 / 2) (b := 7 / 2) hcont hder le_rfl hbound
  have hσKey := key σ ⟨hσ1, hσ2⟩
  rw [gronwallBound_ε0] at hσKey
  have hhalf : (↑(1 / 2 : ℝ) : ℂ) + ↑t * I = 1 / 2 + ↑t * I := by norm_num
  rw [hhalf] at hσKey
  refine le_trans hσKey ?_
  have hexp : Real.exp (K * Real.log (|t| + 2) * (σ - 1 / 2)) ≤ (|t| + 2) ^ (3 * K) := by
    rw [Real.rpow_def_of_pos (by linarith [abs_nonneg t])]
    apply Real.exp_le_exp.mpr
    have h3 : σ - 1 / 2 ≤ 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos hK0 hlog2).le]
  exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)

/-! ## The packaged product `Γ(s) cos(πs/2)` -/

/-- On the strip `Re ∈ [1/2, 7/2]` the product `Γ(s) cos(πs/2)` grows at most
polynomially in `Im s`: the exponential decay of `Γ` cancels the exponential
growth of `cos` exactly, leaving the Gronwall polynomial factor. -/
theorem u6aCA_exists_norm_gamma_mul_cos :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 2 →
      ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ ≤
        Real.sqrt Real.pi * (|s.im| + 2) ^ B := by
  obtain ⟨K, hK0, htrans⟩ := u6aCA_exists_gamma_transport
  refine ⟨3 * K, by positivity, fun s h1 h2 => ?_⟩
  have hs : (↑s.re : ℂ) + ↑s.im * I = s := Complex.re_add_im s
  have hΓ : ‖Complex.Gamma s‖ ≤
      ‖Complex.Gamma (1 / 2 + ↑s.im * I)‖ * (|s.im| + 2) ^ (3 * K) := by
    have := htrans s.re s.im h1 h2
    rwa [hs] at this
  have hcos : ‖Complex.cos (↑Real.pi * s / 2)‖ ≤ Real.cosh (Real.pi * s.im / 2) := by
    have hbound := u6aCA_norm_cos_le_cosh (↑Real.pi * s / 2)
    have him : (↑Real.pi * s / 2).im = Real.pi * s.im / 2 := by
      have hrw : (↑Real.pi : ℂ) * s / 2 = ↑(Real.pi / 2) * s := by
        push_cast
        ring
      rw [hrw]
      simp [Complex.mul_im]
      ring
    rwa [him] at hbound
  have hrpow : (0 : ℝ) ≤ (|s.im| + 2) ^ (3 * K) :=
    Real.rpow_nonneg (by positivity) _
  calc ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖
      = ‖Complex.Gamma s‖ * ‖Complex.cos (↑Real.pi * s / 2)‖ := norm_mul _ _
    _ ≤ (‖Complex.Gamma (1 / 2 + ↑s.im * I)‖ * (|s.im| + 2) ^ (3 * K)) *
        Real.cosh (Real.pi * s.im / 2) :=
        mul_le_mul hΓ hcos (norm_nonneg _) (by positivity)
    _ = (‖Complex.Gamma (1 / 2 + ↑s.im * I)‖ * Real.cosh (Real.pi * s.im / 2)) *
        (|s.im| + 2) ^ (3 * K) := by ring
    _ ≤ Real.sqrt Real.pi * (|s.im| + 2) ^ (3 * K) :=
        mul_le_mul_of_nonneg_right (u6aCA_norm_gamma_half_mul_cosh_le s.im) hrpow

/-! ## Polynomial growth of zeta on the band -/

/-- Linear growth of `ζ` right of the critical line, from the Abel-summation
continuation bound. -/
theorem u6aCA_norm_riemannZeta_le_right {s : ℂ} (h1 : 1 / 2 ≤ s.re)
    (h2 : s.re ≤ 13 / 2) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8 * (|s.im| + 2) := by
  have hs1 : s ≠ 1 := by
    intro hc
    rw [hc] at him
    norm_num at him
  have hdom : s ∈ zetaAbelContinuationDomain :=
    ⟨hs1, lt_of_lt_of_le (lt_of_lt_of_le zetaAbelContinuationReLower_lt_half
      (by norm_num)) h1⟩
  have hb := norm_riemannZeta_le s hdom
  have hp1 : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hge : 1 ≤ ‖s - 1‖ := by
      have him' : |(s - 1).im| = |s.im| := by simp
      calc (1 : ℝ) ≤ |s.im| := him
        _ = |(s - 1).im| := him'.symm
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    rw [div_le_one (by linarith)]
    exact hge
  have hp2 : ‖s‖ / s.re ≤ 13 + 2 * |s.im| := by
    have hre : (0 : ℝ) < s.re := by linarith
    have hnorm : ‖s‖ ≤ 13 / 2 + |s.im| := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      have habs : |s.re| ≤ 13 / 2 := abs_le.mpr ⟨by linarith, h2⟩
      linarith
    rw [div_le_iff₀ hre]
    nlinarith [abs_nonneg s.im]
  have hfinal : (1 : ℝ) + 1 + (13 + 2 * |s.im|) ≤ 8 * (|s.im| + 2) := by
    nlinarith [abs_nonneg s.im]
  calc ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := hb
    _ ≤ 1 + 1 + (13 + 2 * |s.im|) := by linarith
    _ ≤ 8 * (|s.im| + 2) := hfinal

/-- Polynomial growth of `ζ` left of the critical line, through the
functional equation and the packaged `Γ cos` bound. -/
theorem u6aCA_exists_norm_riemannZeta_le_left :
    ∃ B : ℝ, 0 < B ∧ ∀ w : ℂ, -5 / 2 ≤ w.re → w.re ≤ 1 / 2 → 1 ≤ |w.im| →
      ‖riemannZeta w‖ ≤ 16 * Real.sqrt Real.pi * (|w.im| + 2) ^ (B + 1) := by
  obtain ⟨B, hB0, hΓcos⟩ := u6aCA_exists_norm_gamma_mul_cos
  refine ⟨B, hB0, fun w hw1 hw2 him => ?_⟩
  set s : ℂ := 1 - w with hsdef
  have hsre : s.re = 1 - w.re := by simp [hsdef]
  have hsim : |s.im| = |w.im| := by
    have : s.im = -w.im := by simp [hsdef]
    rw [this, abs_neg]
  have hsre1 : 1 / 2 ≤ s.re := by rw [hsre]; linarith
  have hsre2 : s.re ≤ 7 / 2 := by rw [hsre]; linarith
  have hpoles : ∀ n : ℕ, s ≠ -↑n := by
    intro n hc
    have hre := congrArg Complex.re hc
    rw [hsre] at hre
    simp at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hs1 : s ≠ 1 := by
    intro hc
    have him' := congrArg Complex.im hc
    have : s.im = -w.im := by simp [hsdef]
    rw [this] at him'
    simp at him'
    rw [him'] at him
    norm_num at him
  have hFE := riemannZeta_one_sub (s := s) hpoles hs1
  have hw_eq : (1 : ℂ) - s = w := by rw [hsdef]; ring
  rw [hw_eq] at hFE
  rw [hFE]
  have hregroup : (2 : ℂ) * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) * riemannZeta s =
      (2 * (2 * ↑Real.pi) ^ (-s)) *
        ((Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)) * riemannZeta s) := by
    ring
  have e1 : ‖((2 : ℂ) * (2 * ↑Real.pi) ^ (-s)) *
      ((Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)) * riemannZeta s)‖ =
      ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-s)‖ *
        ‖(Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)) * riemannZeta s‖ :=
    norm_mul _ _
  have e2 : ‖(Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)) * riemannZeta s‖ =
      ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ * ‖riemannZeta s‖ :=
    norm_mul _ _
  rw [hregroup, e1, e2]
  have hpre : ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-s)‖ ≤ 2 := by
    rw [norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hbase : ((2 : ℂ) * ↑Real.pi) = ↑(2 * Real.pi : ℝ) := by push_cast; ring
    have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hcpow : ‖((2 : ℂ) * ↑Real.pi) ^ (-s)‖ = (2 * Real.pi) ^ ((-s).re) := by
      rw [hbase]
      exact Complex.norm_cpow_eq_rpow_re_of_pos hpos _
    have hle1 : (2 * Real.pi) ^ ((-s).re) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · nlinarith [Real.pi_gt_three]
      · rw [Complex.neg_re]; linarith
    rw [h2, hcpow]
    nlinarith
  have hΓcosb : ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ ≤
      Real.sqrt Real.pi * (|w.im| + 2) ^ B := by
    have := hΓcos s hsre1 hsre2
    rwa [hsim] at this
  have hζb : ‖riemannZeta s‖ ≤ 8 * (|w.im| + 2) := by
    have := u6aCA_norm_riemannZeta_le_right (s := s) hsre1 (by linarith) (by
      rw [hsim]; exact him)
    rwa [hsim] at this
  have hx2 : (0 : ℝ) < |w.im| + 2 := by positivity
  have hrpadd : (|w.im| + 2) ^ B * (|w.im| + 2) = (|w.im| + 2) ^ (B + 1) := by
    rw [Real.rpow_add hx2, Real.rpow_one]
  have hΓnn : (0 : ℝ) ≤ ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ :=
    norm_nonneg _
  have hrpnn : (0 : ℝ) ≤ Real.sqrt Real.pi * (|w.im| + 2) ^ B := by positivity
  calc ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-s)‖ *
      (‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ * ‖riemannZeta s‖)
      ≤ 2 * ((Real.sqrt Real.pi * (|w.im| + 2) ^ B) * (8 * (|w.im| + 2))) := by
        apply mul_le_mul hpre
        · exact mul_le_mul hΓcosb hζb (norm_nonneg _) hrpnn
        · positivity
        · norm_num
    _ = 16 * Real.sqrt Real.pi * ((|w.im| + 2) ^ B * (|w.im| + 2)) := by ring
    _ = 16 * Real.sqrt Real.pi * (|w.im| + 2) ^ (B + 1) := by rw [hrpadd]

/-- Polynomial growth of `ζ` on the whole band `Re ∈ [-5/2, 13/2]` needed by
the Jensen disk, away from the real axis. -/
theorem u6aCA_exists_norm_riemannZeta_le_band :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧ ∀ w : ℂ, -5 / 2 ≤ w.re → w.re ≤ 13 / 2 →
      1 ≤ |w.im| → ‖riemannZeta w‖ ≤ A * (|w.im| + 2) ^ B := by
  obtain ⟨B, hB0, hleft⟩ := u6aCA_exists_norm_riemannZeta_le_left
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  refine ⟨16 * Real.sqrt Real.pi + 8, B + 1, by nlinarith, by linarith,
    fun w h1 h2 him => ?_⟩
  have hx1 : (1 : ℝ) ≤ |w.im| + 2 := by linarith [abs_nonneg w.im]
  have hrpnn : (0 : ℝ) ≤ (|w.im| + 2) ^ (B + 1) := Real.rpow_nonneg (by positivity) _
  rcases le_total w.re (1 / 2) with hsplit | hsplit
  · have hb := hleft w h1 hsplit him
    nlinarith
  · have hb := u6aCA_norm_riemannZeta_le_right (s := w) hsplit h2 him
    have hmono : (|w.im| + 2 : ℝ) ≤ (|w.im| + 2) ^ (B + 1) := by
      calc (|w.im| + 2 : ℝ) = (|w.im| + 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (|w.im| + 2) ^ (B + 1) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    nlinarith

end

end Kadiri
