import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary Laplace bounds in Schoenfeld's Theorem 11

The two integrals obtained on putting `u = log(t/17)` admit elementary
majorant primitives. Their endpoint values give the main integral terms in
Schoenfeld (1976), equations (7.11) and (7.18), without introducing incomplete
Bessel functions. All statements below are unconditional real calculus.
-/

open Real Set MeasureTheory
open scoped Interval

namespace TernaryGoldbach.RSBounds.SchoenfeldLaplaceTails

noncomputable def integrand (a d m u : ℝ) : ℝ :=
  (u + d) * Real.exp (-(m * u + a / u))

noncomputable def nearPrimitive (a d u : ℝ) : ℝ :=
  u ^ 2 * (u + d) / a * Real.exp (-a / u)

noncomputable def farPrimitive (a d m u : ℝ) : ℝ :=
  (u + d + 1 / m) * u ^ 2 / (m * u ^ 2 - a) * Real.exp (-(m * u + a / u))

/-- The near primitive has the desired derivative plus a nonnegative remainder. -/
theorem hasDerivAt_nearPrimitive {a d u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    HasDerivAt (nearPrimitive a d)
      (integrand a d 0 u +
        Real.exp (-a / u) * u * (3 * u + 2 * d) / a) u := by
  have hi := hasDerivAt_id u
  have he := (((hasDerivAt_const u (-a)).div hi hu.ne').exp)
  have hp := (((hi.pow 2).mul (hi.add_const d)).div_const a).mul he
  convert hp using 1
  · rfl
  · simp only [integrand, zero_mul, zero_add, id_eq, Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.neg_apply, neg_div]
    field_simp [ha.ne', hu.ne']
    <;> ring

/-- The negative far primitive has the desired derivative plus a nonnegative remainder. -/
theorem hasDerivAt_neg_farPrimitive {a d m u : ℝ}
    (hm : 0 < m) (hu : 0 < u) (hq : 0 < m * u ^ 2 - a) :
    HasDerivAt (fun u => -farPrimitive a d m u)
      (integrand a d m u + Real.exp (-(m * u + a / u)) *
        (a * (m * u ^ 2 + a + 2 * m * d * u + 2 * u) /
          (m * (m * u ^ 2 - a) ^ 2))) u := by
  have hi := hasDerivAt_id u
  have hq' := ((hi.pow 2).const_mul m).sub_const a
  have he := (((hi.const_mul m).add
    ((hasDerivAt_const u a).div hi hu.ne')).neg).exp
  have hp := (((hi.add_const d).add_const (1 / m)).mul (hi.pow 2)).div hq' hq.ne'
  have hq2 : -(u ^ 2 * m * a * 2) + u ^ 4 * m ^ 2 + a ^ 2 ≠ 0 := by
    convert pow_ne_zero 2 hq.ne' using 1 <;> ring
  convert (hp.mul he).neg using 1
  · rfl
  · simp only [integrand, id_eq, Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.neg_apply, neg_div]
    field_simp [hm.ne', hu.ne', hq.ne']
    ring_nf
    have hcancel := congrArg (fun z : ℝ => (u * m + m * d) * z) (mul_inv_cancel₀ hq2)
    nlinarith only [hcancel]

private theorem continuousOn_integrand {a d m l r : ℝ} (hl : 0 < l) :
    ContinuousOn (integrand a d m) (Icc l r) := by
  intro u hu
  have hu0 : 0 < u := hl.trans_le hu.1
  unfold integrand
  fun_prop (disch := positivity)

/-- Finite near-tail integral, with a bound independent of its lower endpoint. -/
theorem integral_near_le {a d l r : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hl : 0 < l) (hlr : l ≤ r) :
    (∫ u in l..r, integrand a d 0 u) ≤ nearPrimitive a d r := by
  have hderiv := fun u (hu : u ∈ Ioo l r) =>
    (hasDerivAt_nearPrimitive (d := d) ha (hl.trans hu.1)).hasDerivWithinAt (s := Ioi u)
  have hcont : ContinuousOn (nearPrimitive a d) (Icc l r) := by
    intro u hu
    exact (hasDerivAt_nearPrimitive ha (hl.trans_le hu.1)).continuousAt.continuousWithinAt
  have he := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hlr hcont hderiv
    (continuousOn_integrand (a := a) (d := d) (m := 0) hl).integrableOn_Icc (fun u hu => by
      have hu0 : 0 < u := hl.trans hu.1
      have : 0 ≤ Real.exp (-a / u) * u * (3 * u + 2 * d) / a := by positivity
      linarith)
  have hp : 0 ≤ nearPrimitive a d l := by unfold nearPrimitive; positivity
  exact he.trans (sub_le_self _ hp)

/-- Finite far-tail integral, with a bound independent of its upper endpoint. -/
theorem integral_far_le {a d m l r : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hm : 0 < m) (hl : 0 < l) (hlr : l ≤ r) (hq : a < m * l ^ 2) :
    (∫ u in l..r, integrand a d m u) ≤ farPrimitive a d m l := by
  have hqu : ∀ u, l ≤ u → 0 < m * u ^ 2 - a := by
    intro u hlu
    have hs := pow_le_pow_left₀ hl.le hlu 2
    have hmuls := mul_le_mul_of_nonneg_left hs hm.le
    linarith
  have hderiv := fun u (hu : u ∈ Ioo l r) =>
    (hasDerivAt_neg_farPrimitive (d := d) hm (hl.trans hu.1) (hqu u hu.1.le)).hasDerivWithinAt (s := Ioi u)
  have hcont : ContinuousOn (fun u => -farPrimitive a d m u) (Icc l r) := by
    intro u hu
    exact (hasDerivAt_neg_farPrimitive hm (hl.trans_le hu.1)
      (hqu u hu.1)).continuousAt.continuousWithinAt
  have he := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hlr hcont hderiv
    (continuousOn_integrand (a := a) (d := d) (m := m) hl).integrableOn_Icc (fun u hu => by
      have hu0 : 0 < u := hl.trans hu.1
      have hqu0 := hqu u hu.1.le
      have : 0 ≤ Real.exp (-(m * u + a / u)) *
          (a * (m * u ^ 2 + a + 2 * m * d * u + 2 * u) /
            (m * (m * u ^ 2 - a) ^ 2)) := by positivity
      linarith)
  have hp : 0 ≤ farPrimitive a d m r := by
    have hr0 := hl.trans_le hlr
    have hqr := hqu r hlr
    unfold farPrimitive
    positivity
  linarith

/-- The near integral endpoint in the notation of (7.11), with `G0=v²(v+d/X)`. -/
theorem integral_near_Xv_le {X d v l : ℝ} (hX : 0 < X) (hd : 0 ≤ d)
    (hv : 0 < v) (hl : 0 < l) (hlv : l ≤ v * X) :
    (∫ u in l..v * X, integrand (X ^ 2) d 0 u) ≤
      v ^ 2 * (v + d / X) * X * Real.exp (-X / v) := by
  have he := integral_near_le (sq_pos_of_pos hX) hd hl hlv
  convert he using 1
  unfold nearPrimitive
  have hex : -(X ^ 2) / (v * X) = -X / v := by field_simp <;> ring
  rw [hex]
  field_simp [hX.ne', hv.ne']
  <;> ring

/-- The far integral endpoint in (7.18), specialized to the optimal order `m=2`. -/
theorem integral_far_Xv_le {X d v r : ℝ} (hX : 0 < X) (hd : 0 ≤ d)
    (hv : 0 < v) (hv2 : 1 < 2 * v ^ 2) (hvr : v * X ≤ r) :
    (∫ u in v * X..r, integrand (X ^ 2) d 2 u) ≤
      (v ^ 2 * (v + (1 + 2 * d) / (2 * X)) / (2 * v ^ 2 - 1)) *
        X * Real.exp (-(2 * v * X + X / v)) := by
  have hq : X ^ 2 < 2 * (v * X) ^ 2 := by
    have := mul_lt_mul_of_pos_right hv2 (sq_pos_of_pos hX)
    nlinarith
  have he := integral_far_le (sq_nonneg X) hd (by norm_num : (0 : ℝ) < 2)
    (mul_pos hv hX) hvr hq
  convert he using 1
  unfold farPrimitive
  have hex : -(2 * (v * X) + X ^ 2 / (v * X)) = -(2 * v * X + X / v) := by
    field_simp <;> ring
  rw [hex]
  field_simp [hX.ne', hv.ne', (by linarith : 2 * v ^ 2 - 1 ≠ 0),
    (by linarith : 2 * (v * X) ^ 2 - X ^ 2 ≠ 0)]
  <;> ring

end TernaryGoldbach.RSBounds.SchoenfeldLaplaceTails
