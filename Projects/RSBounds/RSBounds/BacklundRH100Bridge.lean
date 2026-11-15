import RSBounds.BacklundCountEndpoint
import RHHeight100.Main100

/-!
# The replayed public height-100 certificate in the Backlund count convention

The imported certificate is the 99-module closure of
`teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`.
It proves completeness and simplicity of the first 29 zeros, without RH
or zero-count hypotheses. This module identifies its closed-strip set with
our inclusive positive-ordinate count, including analytic multiplicity.
-/

open Complex Set

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

/-- Every nonreal zeta zero lies in the open critical strip. -/
theorem zeta_zero_re_strip {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (him : ρ.im ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  xiF_zero_re_strip (xiF_eq_zero_of_zeta_zero him hz)

/-- Exact set bridge; no finite-height certificate is needed here. -/
theorem coe_closedPositiveZeros_eq_stripZerosUpTo {T : ℝ} (hT : 0 < T) :
    (closedPositiveZeros T : Set ℂ) = RHHeight.stripZerosUpTo T := by
  ext ρ
  rw [Finset.mem_coe, mem_closedPositiveZeros_iff hT, RHHeight.mem_stripZerosUpTo]
  constructor
  · rintro ⟨hz, hi, hT⟩
    obtain ⟨hr0, hr1⟩ := zeta_zero_re_strip hz hi.ne'
    exact ⟨hz, hr0, hr1, hi, hT⟩
  · rintro ⟨hz, _, _, hi, hT⟩
    exact ⟨hz, hi, hT⟩

/-- The checked height-100 certificate gives simplicity for every actual
zeta zero of positive ordinate at most 100. -/
theorem zero_simple_below_hundred {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hi : 0 < ρ.im) (h100 : ρ.im ≤ 100) :
    ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1 := by
  obtain ⟨hr0, hr1⟩ := zeta_zero_re_strip hz hi.ne'
  exact RHHeight100.rh_height_hundred ρ hz hr0 hr1 hi h100

/-- On the verified finite range, counting with analytic multiplicity is
the same as counting distinct zeros. -/
theorem closed_count_eq_card {T : ℝ} (hT : 0 < T) (h100 : T ≤ 100) :
    N_le T = (closedPositiveZeros T).card := by
  classical
  unfold N_le
  calc
    _ = ∑ ρ ∈ closedPositiveZeros T, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      obtain ⟨hz, hi, hρT⟩ := (mem_closedPositiveZeros_iff hT).mp hρ
      rw [(zero_simple_below_hundred hz hi (hρT.trans h100)).2]
      rfl
    _ = _ := by simp

/-- Exactly 29 positive-ordinate zeros up to and including height 100,
counted with their actual analytic multiplicities. -/
theorem closed_count_hundred : N_le 100 = 29 := by
  rw [closed_count_eq_card (by norm_num) le_rfl,
    ← Set.ncard_coe_finset, coe_closedPositiveZeros_eq_stripZerosUpTo (by norm_num)]
  exact RHHeight100.zero_count_hundred

end TernaryGoldbach.RSBounds.BacklundCountIdentity
