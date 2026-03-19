import Mathlib
import PrimeNumberTheoremAnd.ZetaDefinitions

open Real

/-- RH_up_to is antitone: verifying RH to a greater height implies it for smaller heights. -/
lemma RH_up_to_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) (hRH : riemannZeta.RH_up_to T₂) :
    riemannZeta.RH_up_to T₁ := by
  apply Classical.byContradiction
  intro h_nonempty_T₁
  obtain ⟨ρ, hρ⟩ := not_isEmpty_iff.mp h_nonempty_T₁
  exact hRH.elim ⟨ρ, hρ.1, ⟨hρ.2.1.1, hρ.2.1.2.trans h⟩, hρ.2.2⟩

/-- classicalZeroFree is monotone in R (for positive R₁): a zero-free region with smaller R
    implies one with larger R, since larger R means a narrower zero-free region. -/
lemma classicalZeroFree_mono {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (h : R₁ ≤ R₂)
    (hR : riemannZeta.classicalZeroFree R₁) :
    riemannZeta.classicalZeroFree R₂ := by
  intro σ t ht hσ
  apply hR σ t ht
  linarith [one_div_le_one_div_of_le
    (by exact mul_pos hR₁ (Real.log_pos (by linarith)))
    (by exact mul_le_mul_of_nonneg_right h (Real.log_nonneg (by linarith)) :
      R₂ * Real.log t ≥ R₁ * Real.log t)]
