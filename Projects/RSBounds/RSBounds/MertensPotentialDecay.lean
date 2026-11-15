import RSBounds.MertensPotentialBound
import RSBounds.RS75ZeroPowerDecay

/-!
# A variable-cutoff envelope for the actual signed Mertens tail

The cutoff T is independent of the variable u in the tail u≥x. Finite RH
controls the head through A=1894439, the proved RS75 zero-free region controls
the middle window, and the actual reciprocal-square tail controls the rest.
No PNT or unproved zero-density statement is supplied as an input.
-/

open Complex Set Filter
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.MertensPotentialDecay

open TernaryGoldbach.Explicit BacklundCountIdentity MertensZeroPotential MertensPotentialBound
  RosserSquareTail RS75ZeroPowerDecay

noncomputable def cutoffPower (x T : ℝ) : ℝ :=
  x ^ (-1 / (10 * Real.log (T / 17)))

noncomputable def cutoffEnvelope (x T : ℝ) : ℝ :=
  0.0463 * x ^ (-1 / 2 : ℝ) + 0.0463 * cutoffPower x T + 2 * squareAllowance T

/-- The absolute coefficient envelope decreases in the real argument. -/
theorem norm_coefficient_le_at_lower {x u : ℝ} (hx : 1 ≤ x) (hxu : x ≤ u)
    (ρ : Zero) : ‖coefficient u ρ‖ ≤ x ^ (ρ.val.re - 1) * moment ρ := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < u := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos hx0 hxu
    (show ρ.val.re - 1 ≤ 0 by linarith [(zero_re_strip ρ).2])
  exact (norm_coefficient_le_power_moment hu0 ρ).trans
    (mul_le_mul_of_nonneg_right hp (moment_nonneg ρ))

/-- The actual zero-free region gives one common exponent in a finite window. -/
theorem zero_power_le_cutoff {x T : ℝ} (hx : 1 ≤ x) (ρ : Zero)
    (hA : 1894439 ≤ |ρ.val.im|) (hT : |ρ.val.im| ≤ T) :
    x ^ (ρ.val.re - 1) ≤ cutoffPower x T := by
  have him : 0 < |ρ.val.im| := lt_of_lt_of_le (by norm_num) hA
  have hγ := log_height_pos hA
  have hlog : Real.log (|ρ.val.im| / 17) ≤ Real.log (T / 17) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right hT (by norm_num)
  have hi := one_div_le_one_div_of_le (by positivity :
      (0 : ℝ) < 10 * Real.log (|ρ.val.im| / 17))
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 10))
  have hz := zero_re_le_ten
    (xiF_eq_zero_of_zeta_zero ρ.property.2 ρ.property.1) hA
  apply Real.rpow_le_rpow_of_exponent_le hx
  change ρ.val.re - 1 ≤ -1 / (10 * Real.log (T / 17))
  rw [neg_div]
  linarith

/-- A single head/middle/tail bound, uniformly for every u≥x. -/
theorem norm_coefficient_le_cutoff {x u T : ℝ} (hx : 1 ≤ x) (hxu : x ≤ u)
    (hRH : Goals.FiniteRH 1894439) (ρ : Zero) :
    ‖coefficient u ρ‖ ≤
      x ^ (-1 / 2 : ℝ) * moment ρ + cutoffPower x T * moment ρ + tailMoment T ρ := by
  have hx0 : 0 < x := by linarith
  have hm := moment_nonneg ρ
  have hlow : 0 ≤ x ^ (-1 / 2 : ℝ) * moment ρ := by positivity
  have hmid : 0 ≤ cutoffPower x T * moment ρ := by
    unfold cutoffPower
    positivity
  have htail := tailMoment_nonneg T ρ
  by_cases hA : |ρ.val.im| ≤ 1894439
  · have hre := hRH ρ.val ρ.property.1 (zero_re_strip ρ).1 (zero_re_strip ρ).2 hA
    have h := norm_coefficient_le_at_lower hx hxu ρ
    rw [hre, show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] at h
    linarith
  · by_cases hT : |ρ.val.im| ≤ T
    · have hp := zero_power_le_cutoff hx ρ (le_of_lt (lt_of_not_ge hA)) hT
      have h := (norm_coefficient_le_at_lower hx hxu ρ).trans
        (mul_le_mul_of_nonneg_right hp hm)
      linarith
    · have h := norm_coefficient_le_moment (hx.trans hxu) ρ
      rw [tailMoment, if_pos (lt_of_not_ge hT)]
      linarith

/-- An actual-zero cutoff envelope, valid uniformly on the whole real tail. -/
theorem norm_potential_le_cutoff {x u T : ℝ} (hx : 1 ≤ x) (hxu : x ≤ u)
    (hT : 1894439 ≤ T) (hRH : Goals.FiniteRH 1894439) :
    ‖potential u‖ ≤ cutoffEnvelope x T := by
  have hx0 : 0 < x := by linarith
  have hn : Summable (fun ρ : Zero => ‖coefficient u ρ‖) :=
    summable_moment.of_norm_bounded (fun ρ => by
      rw [norm_norm]
      exact norm_coefficient_le_moment (hx.trans hxu) ρ)
  have h1 := summable_moment.mul_left (x ^ (-1 / 2 : ℝ))
  have h2 := summable_moment.mul_left (cutoffPower x T)
  have h3 := summable_tailMoment T
  have hb := (h1.add h2).add h3
  calc
    ‖potential u‖ ≤ ∑' ρ : Zero, ‖coefficient u ρ‖ := by
      change ‖∑' ρ : Zero, coefficient u ρ‖ ≤ _
      exact norm_tsum_le_tsum_norm hn
    _ ≤ ∑' ρ : Zero, (x ^ (-1 / 2 : ℝ) * moment ρ +
          cutoffPower x T * moment ρ + tailMoment T ρ) :=
      hn.tsum_le_tsum (norm_coefficient_le_cutoff hx hxu hRH) hb
    _ = x ^ (-1 / 2 : ℝ) * (∑' ρ : Zero, moment ρ) +
        cutoffPower x T * (∑' ρ : Zero, moment ρ) +
        ∑' ρ : Zero, tailMoment T ρ := by
      rw [Summable.tsum_add (h1.add h2) h3, Summable.tsum_add h1 h2,
        tsum_mul_left, tsum_mul_left]
    _ ≤ cutoffEnvelope x T := by
      have hlow : 0 ≤ x ^ (-1 / 2 : ℝ) := by positivity
      have hmid : 0 ≤ cutoffPower x T := by unfold cutoffPower; positivity
      have hm1 := mul_le_mul_of_nonneg_left tsum_moment_lt.le hlow
      have hm2 := mul_le_mul_of_nonneg_left tsum_moment_lt.le hmid
      have ht := tsum_tailMoment_le (by linarith : (7 : ℝ) ≤ T)
      unfold cutoffEnvelope
      nlinarith only [hm1, hm2, ht]

/-- The same cutoff bounds the actual improper signed integral for every u≥x. -/
theorem norm_signedLimit_le_cutoff {x u T : ℝ} (hx : 1 ≤ x) (hxu : x ≤ u)
    (hT : 1894439 ≤ T) (hRH : Goals.FiniteRH 1894439) :
    ‖MertensSignedLimit.signedLimit u‖ ≤ cutoffEnvelope x T +
      6000 * x ^ (-3 / 2 : ℝ) + Real.log (2 * Real.pi) / x := by
  have hx0 : 0 < x := by linarith
  have hs := MertensSignedLimit.norm_signedLimit_le (hx.trans hxu)
  have hp := norm_potential_le_cutoff hx hxu hT hRH
  have hf := Real.rpow_le_rpow_of_nonpos hx0 hxu (by norm_num : (-3 / 2 : ℝ) ≤ 0)
  have hl : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hi := div_le_div_of_nonneg_left hl hx0 hxu
  linarith

/-- The variable-cutoff estimate is bound to the actual signed Mertens function. -/
theorem abs_J_le_cutoff {x u T : ℝ} (hx : 1 ≤ x) (hxu : x ≤ u)
    (hT : 1894439 ≤ T) (hRH : Goals.FiniteRH 1894439) :
    |MertensSecondSigned.J u| ≤ cutoffEnvelope x T +
      6000 * x ^ (-3 / 2 : ℝ) + Real.log (2 * Real.pi) / x := by
  rw [MertensDLimit.J_eq_signedLimit (hx.trans hxu)]
  exact (Complex.abs_re_le_norm _).trans (norm_signedLimit_le_cutoff hx hxu hT hRH)

end TernaryGoldbach.RSBounds.MertensPotentialDecay
