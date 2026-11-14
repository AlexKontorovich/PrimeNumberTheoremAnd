/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZeroDensity.Jensen

/-!
# Unconditional Bohr–Landau: `N(σ,T) = O(T)` for every fixed `σ > 1 / 2`

Assembly of `uniformMeanSquare` (uniform mean square of ζ on vertical lines)
and `high_count` (Jensen's formula on discs, integrated over the centre height).
-/

open Complex Set Metric MeasureTheory Filter MeromorphicOn

@[expose] public noncomputable section
namespace ZeroDensity

lemma zeroSet_finite {σ : ℝ} (hσ : 0 < σ) (T : ℝ) : (zeroSet σ T).Finite := by
  set D := divisor riemannZeta₁ (closedBall (0:ℂ) (T + 2))
  refine (D.finiteSupport (isCompact_closedBall _ _)).subset ?_
  rintro ρ ⟨h0, hre, him, hT⟩
  have hre1 : ρ.re < 1 := by
    by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h0
  have hne : ρ ≠ 1 := by intro e; rw [e] at him; simp at him
  have hmem : ρ ∈ closedBall (0:ℂ) (T + 2) := by
    rw [mem_closedBall, dist_zero_right]
    have := Complex.norm_le_abs_re_add_abs_im ρ
    rw [abs_of_pos (by linarith), abs_of_pos him] at this; linarith
  have hz : riemannZeta₁ ρ = 0 := by rw [zg_eq hne, h0, mul_zero]
  have := one_le_divisor_zg hmem hz
  change D ρ ≠ 0
  intro e; rw [e] at this; norm_num at this

/-- **Bohr–Landau (unconditional).** For every `σ > 1 / 2`, `N(σ,T) = O(T)`. -/
@[blueprint
  "zd-bohr-landau"
  (title := "Bohr--Landau theorem")
  (statement := /--
    For every $\sigma>1/2$ there is a constant $A=A(\sigma)$ such that $N(\sigma,T)\le A T$
    for all $T\ge 2$, where $N(\sigma,T)$ counts zeros of $\zeta$ with $\Re\rho\ge\sigma$ and
    $0<\Im\rho\le T$ (without multiplicity).
  -/)]
theorem bohr_landau {σ : ℝ} (hσ : 1 / 2 < σ) : ∃ A, ∀ T ≥ 2, Nzeros σ T ≤ A * T := by
  rcases le_or_gt 1 σ with h1 | h1
  · refine ⟨0, fun T _ => ?_⟩
    have : zeroSet σ T = ∅ := by
      ext ρ; simp only [mem_empty_iff_false, iff_false]
      rintro ⟨h0, hre, -, -⟩
      exact riemannZeta_ne_zero_of_one_le_re (h1.trans hre) h0
    simp [Nzeros, this]
  set σ₀ := (σ + 1 / 2) / 2 with hσ₀
  obtain ⟨C, hC⟩ := uniformMeanSquare (σ₀ := σ₀) (by linarith) (by linarith)
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hU : ∀ x, σ₀ ≤ x → x ≤ 4 → ∀ α β, 2 ≤ α → α ≤ β →
      (∫ t in α..β, ‖riemannZeta (sl x t)‖ ^ 2) ≤ C' * β := fun x h1 h2 α β h3 h4 =>
    (hC x h1 h2 α β h3 h4).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  set R := 2 - σ₀ with hR
  set d := 2 - σ with hd
  set r := (d + R) / 2 with hr
  set h := r - d with hh
  have hh0 : 0 < h := by simp only [hh, hr, hd, hR, hσ₀]; linarith
  have hrpos : 0 < r := by linarith
  have hrR : r < R := by linarith
  have hdr : (2 - σ) ^ 2 + h ^ 2 ≤ r ^ 2 := by
    have : r = d + h := by ring
    rw [this, ← hd]; nlinarith
  have hL : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hrpos).2 hrR)
  set L := Real.log (R / r)
  set τ₀ := R + h + 3
  set M₀ : ℝ := ((zeroSet σ τ₀).ncard : ℝ)
  set K := (R + 2) * (2 * h + 1) + C' * (2 * R + 2 * h + 3) / 2
  set s := (R + 2) + C' / 2
  have hK : 0 ≤ K := add_nonneg (mul_nonneg (by linarith) (by linarith))
    (div_nonneg (mul_nonneg hC' (by linarith)) (by norm_num))
  have hM : 0 ≤ M₀ := by positivity
  have hD : 0 < 2 * h * L := by positivity
  refine ⟨M₀ / 2 + (K / 2 + s) / (2 * h * L), fun T hT => ?_⟩
  have hσ0 : 0 < σ := by linarith
  set H := {ρ ∈ zeroSet σ T | τ₀ ≤ ρ.im}
  have hHf : H.Finite := (zeroSet_finite hσ0 T).subset (fun _ h => h.1)
  have hsub : zeroSet σ T ⊆ zeroSet σ τ₀ ∪ H := by
    intro ρ hρ
    rcases le_or_gt τ₀ ρ.im with h' | h'
    · exact Or.inr ⟨hρ, h'⟩
    · exact Or.inl ⟨hρ.1, hρ.2.1, hρ.2.2.1, h'.le⟩
  have hsplit : Nzeros σ T ≤ M₀ + (H.ncard : ℝ) := by
    have := Set.ncard_le_ncard hsub ((zeroSet_finite hσ0 τ₀).union hHf)
    have h2 := Set.ncard_union_le (zeroSet σ τ₀) H
    unfold Nzeros; simp only [M₀]; exact_mod_cast this.trans h2
  have hHc : (H.ncard : ℝ) * (2 * h * L) ≤ K + s * T := by
    rw [Set.ncard_eq_toFinset_card H hHf]
    have := high_count (σ₀ := σ₀) (by linarith) hdr hrpos hrR hh0 (by linarith) (by linarith)
      hC' hU T (by linarith) hHf.toFinset (by
        intro ρ hρ
        rw [Set.Finite.mem_toFinset] at hρ
        exact ⟨hρ.1.1, hρ.1.2.1, hρ.2, hρ.1.2.2.2⟩)
    have e : ((hHf.toFinset.card : ℝ)) * (2 * h) * L = (hHf.toFinset.card : ℝ) * (2 * h * L) := by
      ring
    rw [← e]; refine this.trans (le_of_eq ?_); simp only [K, s]; ring
  have hHle : (H.ncard : ℝ) ≤ (K + s * T) / (2 * h * L) := (le_div_iff₀ hD).2 hHc
  have hfin : (K + s * T) / (2 * h * L) ≤ (K / 2 + s) / (2 * h * L) * T := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hD.le
    nlinarith
  nlinarith

end ZeroDensity

