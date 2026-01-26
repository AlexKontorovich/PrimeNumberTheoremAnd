import PrimeNumberTheoremAnd.PrimeGaps.Latest

namespace Lcm
noncomputable abbrev gap : PrimeGaps.Provider := PrimeGaps.latest
noncomputable abbrev X₀ : ℕ := gap.X₀

@[simp] lemma X₀_def : X₀ = gap.X₀ := rfl
@[simp] lemma X₀_eq : X₀ = PrimeGaps.X₀ := rfl
@[simp] lemma X₀_cast : ((X₀ : ℕ) : ℝ) = (gap.X₀ : ℝ) := rfl

noncomputable abbrev δ (x : ℝ) : ℝ := gap.δ x
@[simp] lemma δ_def (x : ℝ) : δ x = gap.δ x := rfl

end Lcm
