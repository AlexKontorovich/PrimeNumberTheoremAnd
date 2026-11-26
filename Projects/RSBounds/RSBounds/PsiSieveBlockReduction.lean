import RSBounds.PsiSieveEndpointReduction

/-!
# Cross-endpoint certificates for blocks containing prime-power jumps

An upper enclosure of psi at the right endpoint and a lower enclosure at
the left endpoint control the whole block, provided the two directed
cross-checks hold. No prime-power-free gap hypothesis is required.

The proof reuses the normalized-error monotonicity already formalized in
`PsiSieveEndpointReduction.constant_gap_abs_le`: for each x, take the
nonnegative constant C = psi(x), then bound C by monotonicity of psi.
This module proves a certificate reduction, not a numerical sieve campaign.
-/

namespace TernaryGoldbach.RSBounds.PsiSieveBlockReduction

open PsiSieveEndpointReduction

/-- Two cross-endpoint checks control every real point of a closed block,
including all prime-power jumps inside it. -/
theorem psi_block_abs_le {a b x k : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hupper : Chebyshev.psi b - a ≤ k * Real.sqrt a)
    (hlower : b - Chebyshev.psi a ≤ k * Real.sqrt b) :
    |Chebyshev.psi x - x| ≤ k * Real.sqrt x := by
  apply constant_gap_abs_le ha hax hxb (Chebyshev.psi_nonneg x)
  · exact (sub_le_sub_right (Chebyshev.psi_mono hxb) a).trans hupper
  · exact (sub_le_sub_left (Chebyshev.psi_mono hax) b).trans hlower

/-- Exact integer guards for a block. The upper enclosure is evaluated at b
but checked against a; the lower enclosure is evaluated at a but checked
against b. The scale and positive rational coefficient are arbitrary. -/
theorem psi_block_abs_le_of_guards
    {a b lowerAtA upperAtB scaleN numerator denominator : ℕ} {x : ℝ}
    (ha : 0 < a) (hscale : 0 < scaleN)
    (hnum : 0 < numerator) (hden : 0 < denominator)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hlowerA : (lowerAtA : ℝ) / scaleN ≤ Chebyshev.psi a)
    (hupperB : Chebyshev.psi b ≤ (upperAtB : ℝ) / scaleN)
    (hupper : SignedEndpointSafe a scaleN numerator denominator
      ((upperAtB : ℤ) - (a : ℤ) * scaleN))
    (hlower : SignedEndpointSafe b scaleN numerator denominator
      ((b : ℤ) * scaleN - lowerAtA)) :
    |Chebyshev.psi x - x| ≤
      ((numerator : ℝ) / denominator) * Real.sqrt x := by
  have hu := upperEndpointSafe_real_generic hscale hnum hden hupper
  have hl := lowerEndpointSafe_real_generic hscale hnum hden hlower
  apply psi_block_abs_le (by exact_mod_cast ha) hax hxb
  · exact (sub_le_sub_right hupperB (a : ℝ)).trans hu
  · exact (sub_le_sub_left hlowerA (b : ℝ)).trans hl

/-- The 4/5 specialization used for the proposed finite sqrt-error campaign. -/
theorem psi_block_abs_le_four_fifths_of_guards
    {a b lowerAtA upperAtB scaleN : ℕ} {x : ℝ}
    (ha : 0 < a) (hscale : 0 < scaleN)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hlowerA : (lowerAtA : ℝ) / scaleN ≤ Chebyshev.psi a)
    (hupperB : Chebyshev.psi b ≤ (upperAtB : ℝ) / scaleN)
    (hupper : SignedEndpointSafe a scaleN 4 5
      ((upperAtB : ℤ) - (a : ℤ) * scaleN))
    (hlower : SignedEndpointSafe b scaleN 4 5
      ((b : ℤ) * scaleN - lowerAtA)) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  simpa only [Nat.cast_ofNat] using psi_block_abs_le_of_guards ha hscale
    (by norm_num : 0 < (4 : ℕ)) (by norm_num : 0 < (5 : ℕ))
    hax hxb hlowerA hupperB hupper hlower

end TernaryGoldbach.RSBounds.PsiSieveBlockReduction
