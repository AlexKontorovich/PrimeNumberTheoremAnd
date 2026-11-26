/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import RSBounds.IEANTNDigamma

/-!
# IEANTN's same-height digamma difference bound

The following two proved lemmas are copied from
`teorth/IEANTN@466b41b28ecc224398cf53a99c5fe9618131398b`,
`Solutions/CH2.v1/Section81Titch.lean`, lines 88--183.
Only the import list is changed to the already-vendored Gauss-series proof.
No challenge declaration or analytical hypothesis is imported.
-/

open Complex Filter Topology Set MeasureTheory
namespace CH2Section81

/-- `∑_{k ≥ 0} 1/(k+y)² ≤ 1/y² + 1/y` for `y ≥ 1`, by telescoping. -/
theorem hasSum_telescope_inv {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ ↦ 1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y)) (1 / y) := by
  have hpos : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y) := by
    intro k
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [sub_nonneg]; apply one_div_le_one_div_of_le (by positivity); linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hpos]
  have e : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y))
      = 1 / y - 1 / ((n : ℝ) + y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  simp_rw [e]
  have : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + y)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ y tendsto_natCast_atTop_atTop)
  simpa using tendsto_const_nhds.sub this

theorem norm_digamma_sub_le {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re) (him : z₁.im = z₂.im)
    (hy : 2 ≤ z₁.im) :
    ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ ‖z₁ - z₂‖ * (4 / z₁.im) := by
  set y := z₁.im with hy_def
  have hy0 : 0 < y := by linarith
  have hn1 : ∀ n : ℕ, z₁ ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn2 : ∀ n : ℕ, z₂ ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hs1 := GammaSolution.summable_gaussTerm hn1
  have hs2 := GammaSolution.summable_gaussTerm hn2
  have hdiff : Complex.digamma z₁ - Complex.digamma z₂
      = ∑' k, (GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k) := by
    rw [GammaSolution.digamma_eq_gaussSum h1, GammaSolution.digamma_eq_gaussSum h2,
      GammaSolution.gaussSum, GammaSolution.gaussSum, hs1.tsum_sub hs2]
    ring
  -- the termwise bound
  have hk : ∀ k : ℕ, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖
      ≤ ‖z₁ - z₂‖ * 2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1))) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h ↦ hn1 k (by linear_combination h)
    have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h ↦ hn2 k (by linear_combination h)
    have e : GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k
        = (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
      simp only [GammaSolution.gaussTerm]; field_simp; ring
    have hnorm : ∀ z : ℂ, 0 < z.re → z.im = y → (k : ℝ) ^ 2 + y ^ 2 ≤ ‖(k : ℂ) + z‖ ^ 2 := by
      intro z hz hzi
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, zero_add, hzi]
      nlinarith
    have hp1 := hnorm z₁ h1 rfl
    have hp2 := hnorm z₂ h2 him.symm
    have hprod : ((k : ℝ) + y) ^ 2 / 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
      rw [norm_mul]
      have ha := norm_nonneg ((k : ℂ) + z₁)
      have hb := norm_nonneg ((k : ℂ) + z₂)
      have : ((k : ℝ) + y) ^ 2 / 2 ≤ (k : ℝ) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg ((k:ℝ) - y)]
      have hc1 : Real.sqrt ((k : ℝ) ^ 2 + y ^ 2) ≤ ‖(k : ℂ) + z₁‖ := by
        have := Real.sqrt_le_sqrt hp1; rwa [Real.sqrt_sq ha] at this
      have hc2 : Real.sqrt ((k : ℝ) ^ 2 + y ^ 2) ≤ ‖(k : ℂ) + z₂‖ := by
        have := Real.sqrt_le_sqrt hp2; rwa [Real.sqrt_sq hb] at this
      have hmm := mul_le_mul hc1 hc2 (Real.sqrt_nonneg _) ha
      rw [Real.mul_self_sqrt (by positivity)] at hmm
      linarith
    have htel : 2 / ((k : ℝ) + y) ^ 2 ≤ 2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1))) := by
      have hky : 0 < (k : ℝ) + (y - 1) := by linarith
      have hky' : 0 < (k : ℝ) + y := by linarith
      have h3 : 1 / ((k : ℝ) + y) ^ 2 ≤ 1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1)) := by
        rw [show (k : ℝ) + 1 + (y - 1) = (k : ℝ) + y by ring, div_sub_div _ _ hky.ne' hky'.ne',
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e2 : 2 / ((k : ℝ) + y) ^ 2 = 2 * (1 / ((k : ℝ) + y) ^ 2) := by ring
      rw [e2]; linarith
    rw [e, norm_div]
    calc ‖z₁ - z₂‖ / ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖
        ≤ ‖z₁ - z₂‖ / (((k : ℝ) + y) ^ 2 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hprod
      _ = ‖z₁ - z₂‖ * (2 / ((k : ℝ) + y) ^ 2) := by field_simp
      _ ≤ ‖z₁ - z₂‖ * (2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1)))) :=
          mul_le_mul_of_nonneg_left htel (norm_nonneg _)
      _ = _ := by ring
  have htele := (hasSum_telescope_inv (y := y - 1) (by linarith)).mul_left (‖z₁ - z₂‖ * 2)
  have hsumn : Summable fun k : ℕ ↦ ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hk htele.summable
  rw [hdiff]
  calc _ ≤ ∑' k, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ := norm_tsum_le_tsum_norm hsumn
    _ ≤ ‖z₁ - z₂‖ * 2 * (1 / (y - 1)) := by
        rw [← htele.tsum_eq]; exact Summable.tsum_le_tsum hk hsumn htele.summable
    _ ≤ ‖z₁ - z₂‖ * (4 / y) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have : 1 / (y - 1) ≤ 2 / y := by rw [div_le_div_iff₀ (by linarith) hy0]; nlinarith
        have e : 4 / y = 2 * (2 / y) := by ring
        rw [e]; linarith


end CH2Section81
