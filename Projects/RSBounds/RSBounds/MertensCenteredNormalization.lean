import RSBounds.MellinAbelianLimit
import RSBounds.MertensPsiAbel

/-!
# Normalization of the convergent signed psi integral

The centered quantity `D(x) = E₁Λ(x) - psi(x)/x` has Abel average tending
to `-gamma-1`. Thus any limit at infinity must equal this value. This needs
no prime number theorem: convergence of D is the separate zero-sum result.
-/

open Real Complex Set Filter MeasureTheory
open scoped Topology

namespace TernaryGoldbach.RSBounds.MertensCenteredNormalization

open MertensAbelianNormalization MellinAbelianLimit MertensPsiAbel

theorem centered_average_tendsto :
    Tendsto (fun s : ℝ => (s - 1) * ∫ x in Ioi 1, D x * x ^ (-s))
      (𝓝[>] 1) (𝓝 (-Real.eulerMascheroniConstant - 1)) := by
  have h := (normalized_logDeriv_tendsto.sub_const 1).div
    (tendsto_id.mono_left (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds))
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  change (-(logDeriv riemannZeta (s : ℂ)).re - 1 / (s - 1) - 1) / s = _
  rw [D_abel_identity hs]
  ring

theorem centered_limit_eq {C : ℝ} (hlim : Tendsto D atTop (𝓝 C)) :
    C = -Real.eulerMascheroniConstant - 1 := by
  have hB : 0 ≤ 2 * (Real.log 4 + 4) := by positivity
  have h := average_tendsto hB measurable_D.aestronglyMeasurable.restrict
    (fun x hx => D_bound hx) hlim
  exact tendsto_nhds_unique h centered_average_tendsto

end TernaryGoldbach.RSBounds.MertensCenteredNormalization
