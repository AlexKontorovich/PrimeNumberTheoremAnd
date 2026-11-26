import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite integration by parts from an integral primitive

The primitive identity is enough; no derivative of `J` at a discontinuity of
`f` is required.  In the intended application `f` contains the Chebyshev
function, whose jumps occur at prime powers.

The auxiliary primitive `Q(t) = Ja - ∫ a..t, f` is absolutely continuous.
Its derivative is `-f` almost everywhere, so Mathlib's integration by parts
theorem for absolutely continuous functions applies.
-/

open MeasureTheory Set Filter

namespace TernaryGoldbach.RSBounds.MertensFiniteParts

/-- A function given by a constant minus an interval integral is absolutely
continuous on the same finite interval. -/
theorem absolutelyContinuousOnInterval_of_primitive
    {a b Ja : ℝ} {f J : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hJ : ∀ t ∈ uIcc a b, Ja - J t = ∫ u in a..t, f u) :
    AbsolutelyContinuousOnInterval J a b := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => Ja) a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => Ja) (uIcc a b))
  have hprim := hf.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by simp)
  apply (hconst.sub hprim).congr
  intro t ht
  change Ja - (∫ u in a..t, f u) = J t
  linarith [hJ t ht]

/-- Finite integration by parts, formulated with an integral primitive and an
almost-everywhere derivative of the absolutely continuous weight. -/
theorem integral_mul_eq_boundary_add_of_primitive
    {a b Ja : ℝ} {f J w w' : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hJ : ∀ t ∈ uIcc a b, Ja - J t = ∫ u in a..t, f u)
    (hw : AbsolutelyContinuousOnInterval w a b)
    (hw' : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt w (w' t) t) :
    (∫ t in a..b, f t * w t) =
      J a * w a - J b * w b + ∫ t in a..b, J t * w' t := by
  let Q : ℝ → ℝ := fun t => Ja - ∫ u in a..t, f u
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => Ja) a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => Ja) (uIcc a b))
  have hQ : AbsolutelyContinuousOnInterval Q a b :=
    hconst.sub (hf.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) (by simp))
  have hQJ : EqOn Q J (uIcc a b) := by
    intro t ht
    dsimp [Q]
    linarith [hJ t ht]
  have hQ' : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt Q (-f t) t := by
    filter_upwards [hf.ae_hasDerivAt_integral] with t ht hmem
    exact (ht hmem a (by simp)).const_sub Ja
  have hleft : (∫ t in a..b, Q t * deriv w t) =
      ∫ t in a..b, J t * w' t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hw'] with t ht hmem
    have hmem' := uIoc_subset_uIcc hmem
    rw [hQJ hmem', (ht hmem').deriv]
  have hright : (∫ t in a..b, deriv Q t * w t) =
      -(∫ t in a..b, f t * w t) := by
    calc
      _ = ∫ t in a..b, -(f t * w t) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hQ'] with t ht hmem
        rw [(ht (uIoc_subset_uIcc hmem)).deriv, neg_mul]
      _ = _ := intervalIntegral.integral_neg
  have hparts := hQ.integral_mul_deriv_eq_deriv_mul hw
  rw [hleft, hright, hQJ (by simp : b ∈ uIcc a b),
    hQJ (by simp : a ∈ uIcc a b)] at hparts
  linarith

/-- A convenient smooth-weight form of finite integration by parts.  No
separate integrability hypothesis for `w'` is needed. -/
theorem integral_mul_eq_boundary_add_of_contDiffOn
    {a b Ja : ℝ} {f J w w' : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hJ : ∀ t ∈ uIcc a b, Ja - J t = ∫ u in a..t, f u)
    (hw : ContDiffOn ℝ 1 w (uIcc a b))
    (hw' : ∀ t ∈ uIcc a b, HasDerivAt w (w' t) t) :
    (∫ t in a..b, f t * w t) =
      J a * w a - J b * w b + ∫ t in a..b, J t * w' t :=
  integral_mul_eq_boundary_add_of_primitive hf hJ
    hw.absolutelyContinuousOnInterval (Filter.Eventually.of_forall hw')

end TernaryGoldbach.RSBounds.MertensFiniteParts
