import RSBounds.MellinAbelianLimit
import RSBounds.MertensAbelIdentity

/-!
# Identification of a convergent first Mertens error

Convergence is an explicit input to this theorem. Its limiting value is proved
to be minus Euler's constant using the actual von Mangoldt series and Mathlib's
Laurent expansion, not assumed as a normalization of the zero-sum formula.
-/

open Real Complex Set Filter MeasureTheory
open scoped Topology

namespace TernaryGoldbach.RSBounds.MertensLimitNormalization

open TernaryGoldbach.PNTMertens MertensAbelianNormalization MertensAbelIdentity
  MellinAbelianLimit

theorem limit_eq_neg_euler {C : ℝ} (hlim : Tendsto E₁Λ atTop (𝓝 C)) :
    C = -Real.eulerMascheroniConstant := by
  obtain ⟨B, hB, hb⟩ := E₁Λ.bounded'
  have hm : Measurable E₁Λ := by fun_prop
  have hC := average_tendsto hB.le hm.aestronglyMeasurable.restrict hb hlim
  have hγ : Tendsto (fun s : ℝ => (s - 1) * ∫ x in Ioi 1, E₁Λ x * x ^ (-s))
      (𝓝[>] 1) (𝓝 (-Real.eulerMascheroniConstant)) := by
    refine normalized_logDeriv_tendsto.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (error_abel_identity hs).symm
  exact tendsto_nhds_unique hC hγ

end TernaryGoldbach.RSBounds.MertensLimitNormalization
