import RSBounds.MertensPotentialDecay
import RSBounds.MertensDecayScalars

/-! The variable-cutoff signed-tail estimate bound to the actual psi integral.
Finite RH through 1894439 is the only unproved numerical premise. -/

namespace TernaryGoldbach.RSBounds.MertensLargeBudget

open MertensPotentialDecay MertensSignedLimit MertensDecayScalars

noncomputable def cutoffRoot (x : ℝ) : ℝ := Real.sqrt (Real.log x / 10)
noncomputable def cutoffHeight (x : ℝ) : ℝ := 17 * Real.exp (cutoffRoot x)

theorem cutoffRoot_ge {x : ℝ} (hL : 2400 ≤ Real.log x) : 15 ≤ cutoffRoot x := by
  unfold cutoffRoot
  exact Real.le_sqrt_of_sq_le (by nlinarith only [hL])

theorem cutoffRoot_sq {x : ℝ} (hL : 2400 ≤ Real.log x) :
    10 * (cutoffRoot x) ^ 2 = Real.log x := by
  unfold cutoffRoot
  rw [Real.sq_sqrt (by linarith : 0 ≤ Real.log x / 10)]
  ring

theorem actual_envelope_eq {x : ℝ} (hx : 0 < x) (hL : 2400 ≤ Real.log x) :
    cutoffEnvelope x (cutoffHeight x) + 6000 * x ^ (-3 / 2 : ℝ) +
      Real.log (2 * Real.pi) / x = scalarEnvelope (cutoffRoot x) := by
  have hs := cutoffRoot_sq hL
  have hs0 : 0 < cutoffRoot x := by linarith [cutoffRoot_ge hL]
  have hheight : Real.log (cutoffHeight x / 17) = cutoffRoot x := by
    unfold cutoffHeight
    rw [mul_div_cancel_left₀ _ (by norm_num : (17 : ℝ) ≠ 0), Real.log_exp]
  have hpower : cutoffPower x (cutoffHeight x) = Real.exp (-cutoffRoot x) := by
    unfold cutoffPower
    rw [hheight, Real.rpow_def_of_pos hx]
    congr 1
    field_simp [hs0.ne']
    nlinarith only [hs]
  have hlo : x ^ (-1 / 2 : ℝ) = Real.exp (-5 * (cutoffRoot x) ^ 2) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    nlinarith only [hs]
  have hleft : x ^ (-3 / 2 : ℝ) = Real.exp (-15 * (cutoffRoot x) ^ 2) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    nlinarith only [hs]
  have hex : Real.exp (10 * (cutoffRoot x) ^ 2) = x := by
    rw [hs, Real.exp_log hx]
  have hsq : RosserSquareTail.squareAllowance (cutoffHeight x) =
      squareExpr (17 * Real.exp (cutoffRoot x)) := by rfl
  unfold cutoffEnvelope scalarEnvelope
  rw [hpower, hlo, hleft, hsq, hex]

theorem norm_signedLimit_lt {x u : ℝ} (hx : 1 ≤ x) (hL : 2400 ≤ Real.log x)
    (hxu : x ≤ u) (hRH : Goals.FiniteRH 1894439) :
    ‖signedLimit u‖ < 1 / (Real.log x) ^ 2 := by
  have hT : 1894439 ≤ cutoffHeight x := cutoff_height (cutoffRoot_ge hL)
  have h := norm_signedLimit_le_cutoff hx hxu hT hRH
  rw [actual_envelope_eq (by linarith : 0 < x) hL] at h
  have hs := scalarEnvelope_lt (cutoffRoot_ge hL)
  rw [cutoffRoot_sq hL] at hs
  exact h.trans_lt hs

theorem abs_J_lt {x u : ℝ} (hx : 1 ≤ x) (hL : 2400 ≤ Real.log x)
    (hxu : x ≤ u) (hRH : Goals.FiniteRH 1894439) :
    |MertensSecondSigned.J u| < 1 / (Real.log x) ^ 2 := by
  rw [MertensDLimit.J_eq_signedLimit (hx.trans hxu)]
  exact (Complex.abs_re_le_norm _).trans_lt (norm_signedLimit_lt hx hL hxu hRH)

theorem mertens_lower_of_weak_psi {x : ℝ} (hx : 1 ≤ x)
    (hL : 2400 ≤ Real.log x) (hRH : Goals.FiniteRH 1894439)
    (hpsi : |Chebyshev.psi x - x| ≤ 0.1 * x / Real.log x) :
    Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x := by
  have hL0 : 0 < Real.log x := by linarith
  have hx1 : 1 < x := (Real.log_pos_iff (by linarith : 0 ≤ x)).mp hL0
  apply MertensDLimit.mertens_lower_of_errors hx1
    (e := 0.1 / Real.log x) (j := 1 / (Real.log x) ^ 2)
  · convert hpsi using 1 <;> ring
  · exact (norm_signedLimit_lt hx hL le_rfl hRH).le
  · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log x)).mpr
    have heq : (0.1 / Real.log x + 1 / (Real.log x) ^ 2) * (2 * Real.log x) =
        0.2 + 2 / Real.log x := by field_simp [hL0.ne']; ring
    rw [heq]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2400) hL
    simp only [div_eq_mul_inv, one_mul] at hi ⊢
    linarith

end TernaryGoldbach.RSBounds.MertensLargeBudget
