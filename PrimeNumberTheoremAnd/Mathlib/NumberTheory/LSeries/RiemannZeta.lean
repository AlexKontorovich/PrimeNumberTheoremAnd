/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Extra Riemann zeta API

Vertical lines, prime-power bounds, and Euler-product identities supporting strip
and convexity bounds in `RiemannZetaConvexity`.

## Main results

* `verticalLine`, `verticalLine_re`, `verticalLine_add_const`
* `Nat.Primes.norm_one_sub_cpow_neg_vertical_le` and companions
* `riemannZeta_div_riemannZeta_eq_tprod_inv_one_add`, `norm_riemannZeta_div_riemannZeta`
* `norm_riemannZeta_eulerProduct`, `tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine`
-/

@[expose] public section

open scoped BigOperators Topology
open Complex Filter Real Set

/-- The point `σ + it` on the vertical line with real part `σ`. -/
def verticalLine (σ t : ℝ) : ℂ := σ + t * Complex.I

lemma verticalLine_re (σ t : ℝ) : (verticalLine σ t).re = σ := by
  simp only [verticalLine, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero]
  ring

lemma verticalLine_im (σ t : ℝ) : (verticalLine σ t).im = t := by
  simp only [verticalLine, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero]
  ring

lemma verticalLine_add_const (s : ℂ) (h t : ℝ) :
    s + (h : ℂ) + t * Complex.I = verticalLine (s.re + h) (s.im + t) := by
  apply Complex.ext
  · simp [verticalLine, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      add_assoc, add_comm]
  · simp [verticalLine, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, add_assoc, add_comm]

namespace Nat.Primes

/-- For a prime `p` and `s` with real part `> 1`, `‖p^{-s}‖ < 1`. -/
lemma norm_cpow_neg_lt_one (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have hx1 : 1 < ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (p.2.two_le : 2 ≤ (p : ℕ))
    exact lt_of_lt_of_le one_lt_two h2
  have hx0 : 0 < ((p : ℕ) : ℝ) := lt_trans zero_lt_one hx1
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s)
  have hz : -s.re < 0 := neg_lt_zero.mpr (lt_trans zero_lt_one hs)
  simpa [hnorm] using Real.rpow_lt_one_of_one_lt_of_neg hx1 hz

/-- `‖p^{-s}‖ = p^{- re s}` for a prime `p`. -/
lemma norm_cpow_neg_eq_rpow_neg_re (p : Nat.Primes) (s : ℂ) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  have hx : 0 < ((p : ℕ) : ℝ) := Nat.cast_pos.mpr p.property.pos
  simpa [Complex.ofReal_natCast, Complex.neg_re] using
    Complex.norm_cpow_eq_rpow_re_of_pos hx (-s)

/-- `(p : ℝ)^(-r)` coerces to `(p : ℂ)^(-r)` for a prime `p` and real exponent `r`. -/
lemma cpow_neg_ofReal (p : Nat.Primes) (r : ℝ) :
    (((((p : ℕ) : ℝ) ^ (-r)) : ℝ) : ℂ) = ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)) := by
  have hp : 0 ≤ ((p : ℕ) : ℝ) := by positivity
  simpa using Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hp) (y := -r)

/-- `(1 + p^{-r})⁻¹` in `ℂ` equals the real inverse cast from `ℝ`. -/
lemma cast_inv_one_add (p : Nat.Primes) (r : ℝ) :
    ((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹) =
      (((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ : ℝ) : ℂ) := by
  calc
    ((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹)
        = ((1 + (((((p : ℕ) : ℝ) ^ (-r)) : ℝ) : ℂ))⁻¹) := by rw [← cpow_neg_ofReal p r]
    _ = (((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ : ℝ) : ℂ) := by
      simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]

lemma norm_cast_inv_one_add (p : Nat.Primes) (r : ℝ) :
    ‖((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹)‖ = (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  have hden : 0 ≤ 1 + ((p : ℕ) : ℝ) ^ (-r) := by positivity
  rw [cast_inv_one_add, Complex.norm_real]
  exact Real.norm_of_nonneg (inv_nonneg.mpr hden)

/-- On the vertical line `σ + it`, `‖1 - p^{-s}‖ ≤ 1 + p^{-σ}`. -/
lemma norm_one_sub_cpow_neg_vertical_le (p : Nat.Primes) (σ t : ℝ) :
    ‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖ ≤ 1 + ((p : ℕ) : ℝ) ^ (-σ) := by
  set s := verticalLine σ t
  have hre : s.re = σ := verticalLine_re σ t
  calc
    ‖1 - ((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 + ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
      simpa [sub_eq_add_neg, norm_one, norm_neg] using
        norm_add_le (1 : ℂ) (-((p : ℕ) : ℂ) ^ (-s))
    _ = 1 + ((p : ℕ) : ℝ) ^ (-σ) := by rw [norm_cpow_neg_eq_rpow_neg_re, hre]

/-- On the vertical line `σ + it` with `1 < σ`, the Euler factor `1 - p^{-s}` is nonzero. -/
lemma one_sub_cpow_neg_vertical_ne_zero (p : Nat.Primes) (σ t : ℝ) (hσ : 1 < σ) :
    1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t) ≠ 0 := by
  intro h
  set s := verticalLine σ t
  have hs : 1 < s.re := by rw [verticalLine_re]; exact hσ
  have hp_eq_one : ((p : ℕ) : ℂ) ^ (-s) = 1 := by
    rw [sub_eq_zero] at h; exact h.symm
  have h_abs_lt : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := norm_cpow_neg_lt_one p s hs
  rw [hp_eq_one, show ‖(1 : ℂ)‖ = 1 from by simp] at h_abs_lt
  exact lt_irrefl 1 h_abs_lt

/-- Compare inverse Euler factors on the vertical line `σ + it` with `1 < σ`. -/
lemma inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical (p : Nat.Primes) (σ t : ℝ)
    (hσ : 1 < σ) :
    (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤
      (‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖)⁻¹ := by
  have hpos : 0 < ‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖ :=
    norm_pos_iff.mpr (one_sub_cpow_neg_vertical_ne_zero p σ t hσ)
  simpa [one_div] using one_div_le_one_div_of_le hpos (norm_one_sub_cpow_neg_vertical_le p σ t)

lemma multipliable_inv_one_add (r : ℝ) (hr : 1 < r) :
    Multipliable fun p : Nat.Primes => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  have hsum : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-r) := by
    rw [Nat.Primes.summable_rpow]
    linarith
  have hlog : Summable fun p : Nat.Primes => Real.log (1 + ((p : ℕ) : ℝ) ^ (-r)) :=
    Real.summable_log_one_add_of_summable hsum
  exact Real.multipliable_of_summable_log (fun _ => by positivity)
    (by simpa [Real.log_inv, neg_mul] using hlog.neg)

lemma multipliable_complex_inv_one_add (r : ℝ) (hr : 1 < r) :
    Multipliable fun p : Nat.Primes => (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  have hu := multipliable_inv_one_add r hr
  have hmap := hu.map Complex.ofRealHom Complex.continuous_ofReal
  have h_eq :
      (fun p : Nat.Primes => (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹) =
        (fun x : ℝ => (x : ℂ)) ∘ fun p : Nat.Primes => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
    funext p
    exact cast_inv_one_add p r
  simpa [h_eq, Function.comp_def] using hmap

/-- **`(1 - z²)⁻¹ = (1 - z)⁻¹ · (1 + z)⁻¹`** for `‖z‖ < 1`. -/
lemma inv_one_sub_sq_eq_mul_inv_one_sub_one_add (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - z ^ 2)⁻¹ = (1 - z)⁻¹ * (1 + z)⁻¹ := by
  have hz0 : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := (sub_eq_zero.mp h).symm
    simp [this, norm_one] at hz
  have hz1 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := by exact Eq.symm (neg_eq_of_add_eq_zero_right h)
    simp [this, norm_neg, norm_one] at hz
  calc
    (1 - z ^ 2)⁻¹ = ((1 - z) * (1 + z))⁻¹ := by ring
    _ = (1 + z)⁻¹ * (1 - z)⁻¹ := by simp [mul_inv_rev]
    _ = (1 - z)⁻¹ * (1 + z)⁻¹ := by ring

lemma eulerFactor_two_mul (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ =
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
  set z := ((p : ℕ) : ℂ) ^ (-s)
  have hz : ‖z‖ < 1 := norm_cpow_neg_lt_one p s hs
  have hpow : ((p : ℕ) : ℂ) ^ (-(2 * s)) = z ^ 2 := by
    simp only [z]
    rw [show -(2 * s) = (2 : ℂ) * (-s) by ring,
      show (2 : ℂ) * (-s) = ((2 : ℕ) : ℂ) * (-s) by norm_num, Complex.cpow_nat_mul]
  calc
    (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ = (1 - z ^ 2)⁻¹ := by rw [hpow]
    _ = (1 - z)⁻¹ * (1 + z)⁻¹ := inv_one_sub_sq_eq_mul_inv_one_sub_one_add z hz
    _ = (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by simp [z]

end Nat.Primes

section RiemannZetaEulerProduct

open Nat.Primes

/-- **`ζ(2r) = ζ(r) · ∏_p (1 + p^{-r})⁻¹`** for real `r > 1`. -/
theorem riemannZeta_eq_mul_tprod_inv_one_add (r : ℝ) (hr : 1 < r) :
    riemannZeta (2 * (r : ℂ)) =
      riemannZeta (r : ℂ) * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hs : 1 < s.re := by simpa [s] using hr
  have hs2 : 1 < (2 * s).re := by
    simp [s, Complex.mul_re, Complex.ofReal_re]
    linarith
  have hζ := (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hμ := multipliable_complex_inv_one_add r hr
  calc
    riemannZeta (2 * s)
        = ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
          (riemannZeta_eulerProduct_tprod hs2).symm
    _ = ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      refine tprod_congr fun p => eulerFactor_two_mul p s hs
    _ = (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) *
          ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [Multipliable.tprod_mul hζ hμ]
    _ = riemannZeta s * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [← riemannZeta_eulerProduct_tprod hs]

/-- **`ζ(2r)/ζ(r) = ∏_p (1 + p^{-r})⁻¹`** for real `r > 1`. -/
theorem riemannZeta_div_riemannZeta_eq_tprod_inv_one_add (r : ℝ) (hr : 1 < r) :
    riemannZeta (2 * (r : ℂ)) / riemannZeta (r : ℂ) =
      ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hs : 1 < s.re := by simpa [s] using hr
  have hzeta_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  calc
    riemannZeta (2 * s) / riemannZeta s
        = (riemannZeta s * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹) / riemannZeta s := by
          rw [riemannZeta_eq_mul_tprod_inv_one_add r hr]
    _ = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [mul_div_cancel_left₀ _ hzeta_ne]

theorem norm_riemannZeta_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    ‖riemannZeta s‖ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
  calc
    ‖riemannZeta s‖ = ‖∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      rw [riemannZeta_eulerProduct_tprod hs]
    _ = ∏' p : Nat.Primes, ‖(1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      exact Multipliable.norm_tprod (riemannZeta_eulerProduct_hasProd hs).multipliable
    _ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
      congr 1; ext p; simp [norm_inv]

theorem norm_riemannZeta_div_riemannZeta (r : ℝ) (hr : 1 < r) :
    ‖riemannZeta (2 * (r : ℂ)) / riemannZeta (r : ℂ)‖ =
      ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hw := multipliable_complex_inv_one_add r hr
  calc
    ‖riemannZeta (2 * s) / riemannZeta s‖ = ‖∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      simpa [s] using congrArg norm (riemannZeta_div_riemannZeta_eq_tprod_inv_one_add r hr)
    _ = ∏' p : Nat.Primes, ‖(1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := Multipliable.norm_tprod hw
    _ = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
      refine tprod_congr fun p => norm_cast_inv_one_add p r

private lemma multipliable_norm_eulerFactor_inv {ι : Type*} (g : ι → ℂ)
    (h : Multipliable fun i => (1 - g i)⁻¹) :
    Multipliable fun i => (‖1 - g i‖)⁻¹ := by
  simpa [norm_inv] using Multipliable.norm h

private lemma hasProd_nonneg_of_pos {ι : Type*} (f : ι → ℝ) (hf₀ : ∀ i, 0 < f i) (a : ℝ)
    (ha : HasProd f a) : 0 ≤ a :=
  ge_of_tendsto ha <| Filter.Eventually.of_forall fun _ =>
    le_of_lt <| Finset.prod_pos fun i _ => hf₀ i

private lemma hasProd_nnreal_of_coe {ι : Type*} (g : ι → NNReal) (b : NNReal)
    (h : HasProd (fun i => (g i : ℝ)) (b : ℝ)) : HasProd g b := by
  have h_eq : (fun s => ∏ i ∈ s, (g i : ℝ)) = fun s => ↑(∏ i ∈ s, g i) := by
    ext s; exact (NNReal.coe_prod s g).symm
  exact
    (NNReal.isEmbedding_coe.tendsto_nhds_iff.mpr <| by
      change Filter.Tendsto (fun s => ↑(∏ i ∈ s, g i)) Filter.atTop (𝓝 (b : ℝ))
      rw [← h_eq]
      exact h)

private lemma multipliable_toNNReal {ι : Type*} (f : ι → ℝ) (hf₀ : ∀ i, 0 < f i)
    (hf : Multipliable f) : Multipliable fun i => (⟨f i, (hf₀ i).le⟩ : NNReal) := by
  obtain ⟨a, ha⟩ := hf
  let a_nnreal : NNReal := ⟨a, hasProd_nonneg_of_pos f hf₀ a ha⟩
  exact ⟨a_nnreal, hasProd_nnreal_of_coe _ _ (by simpa [a_nnreal] using ha)⟩

private lemma nnreal_coe_tprod {ι : Type*} (f : ι → NNReal) (hf : Multipliable f) :
    ∏' i, (↑(f i) : ℝ) = ↑(∏' i, f i) :=
  (HasProd.map (Multipliable.hasProd hf) NNReal.toRealHom NNReal.continuous_coe).tprod_eq

private lemma nnreal_tprod_le_coe {ι : Type*} (f g : ι → NNReal) (hf : Multipliable f)
    (hg : Multipliable g) (h : ∏' i, f i ≤ ∏' i, g i) :
    ∏' i, (f i : ℝ) ≤ ∏' i, (g i : ℝ) := by
  rw [nnreal_coe_tprod f hf, nnreal_coe_tprod g hg]
  exact NNReal.coe_le_coe.mpr h

/-- On the vertical line `re s = σ > 1`, the real product `∏_p (1 + p^{-σ})^{-1}` is dominated
by the Euler product at `σ + it`. -/
theorem tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine (σ t : ℝ) (hσ : 1 < σ) :
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤
      ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖)⁻¹ := by
  set s := verticalLine σ t
  have hs : 1 < s.re := by rw [verticalLine_re]; exact hσ
  have hf₀ : ∀ p : Nat.Primes, 0 < (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := fun _ => by positivity
  have hg₀ : ∀ p : Nat.Primes, 0 < (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := fun p =>
    inv_pos.mpr (norm_pos_iff.mpr (Nat.Primes.one_sub_cpow_neg_vertical_ne_zero p σ t hσ))
  let f : Nat.Primes → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹, (hf₀ p).le⟩
  let g : Nat.Primes → NNReal := fun p => ⟨(‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹, (hg₀ p).le⟩
  have hf := multipliable_toNNReal _ hf₀ <| Nat.Primes.multipliable_inv_one_add σ hσ
  have hg := multipliable_toNNReal _ hg₀ <|
    multipliable_norm_eulerFactor_inv (g := fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s))
      (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hle : ∏' p, f p ≤ ∏' p, g p :=
    Multipliable.tprod_le_tprod (fun p =>
      Nat.Primes.inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical p σ t hσ) hf hg
  calc
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹
        = ∏' p, (f p : ℝ) := tprod_congr fun p => by unfold f; rfl
    _ ≤ ∏' p, (g p : ℝ) := nnreal_tprod_le_coe f g hf hg hle
    _ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ :=
        tprod_congr fun p => by unfold g; rfl

end RiemannZetaEulerProduct

/-- `1 / (n : ℂ) ^ s` rewrites to `(n : ℂ) ^ (-s)` away from `n = 0`. -/
theorem one_div_natCast_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · simp [h, one_div, Complex.cpow_neg]

end
