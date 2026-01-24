/-
Certified bounds on li(2) using LeanCert numerical integration.

This file provides verified bounds on the logarithmic integral li(2) ≈ 1.0451,
the Ramanujan-Soldner constant, using the symmetric form which makes the
principal value integral absolutely convergent.

## Proof Status

The bounds on li2_symmetric (the symmetric form) are fully proven in
LeanCert's examples/Li2Verified.lean without any sorries. The sorries here
are for:
1. `li2_symmetric_lower/upper` - proven in LeanCert, integration pending
2. `li2_symmetric_eq_li2` - connects symmetric form to principal value (PNT#764)

See: https://github.com/alerad/leancert/blob/main/examples/Li2Verified.lean
-/
import Architect
import LeanCert
import LeanCert.Engine.TaylorModel.Log1p
import LeanCert.Engine.Integrate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import PrimeNumberTheoremAnd.SecondaryDefinitions

open Real MeasureTheory Set
open scoped Interval

open LeanCert.Core
open LeanCert.Validity.Integration
open LeanCert.Engine.TaylorModel

namespace Li2Bounds

/-! ### Symmetric Form Definition -/

/-- The symmetric log combination g(t) = 1/log(1+t) + 1/log(1-t).
    This has a removable singularity at t=0 with limit 1. -/
noncomputable def g (t : ℝ) : ℝ := symmetricLogCombination t

/-- li(2) via the symmetric integral form.
    This equals the principal value integral ∫₀² dt/log(t). -/
noncomputable def li2_symmetric : ℝ := ∫ t in (0:ℝ)..1, g t

/-! ### Key Properties from LeanCert -/

/-- g(t) → 1 as t → 0⁺ (the removable singularity). -/
theorem g_tendsto_one :
    Filter.Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds 1) :=
  symmetricLogCombination_tendsto_one

/-- |g(t)| ≤ 2 for t ∈ (0, 1/2]. -/
theorem g_bounded (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1/2) :
    |g t| ≤ 2 :=
  symmetricLogCombination_bounded t ht_pos ht_lt

/-- g(t) = log(1-t²)/(log(1+t)·log(1-t)) for t ∈ (0, 1). -/
theorem g_alt (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    g t = log (1 - t^2) / (log (1 + t) * log (1 - t)) :=
  symmetricLogCombination_alt t ht_pos ht_lt

/-! ### Numerical Integration Setup -/

/-- The expression g_alt_expr represents log(1-t²)/(log(1+t)·log(1-t)).
    This form is better for interval arithmetic as it avoids the apparent
    singularity in the symmetric form. -/
def g_alt_expr : Expr :=
  Expr.mul
    (Expr.log (Expr.add (Expr.const 1)
      (Expr.neg (Expr.mul (Expr.var 0) (Expr.var 0)))))
    (Expr.inv
      (Expr.mul
        (Expr.log (Expr.add (Expr.const 1) (Expr.var 0)))
        (Expr.log (Expr.add (Expr.const 1) (Expr.neg (Expr.var 0))))))

theorem g_alt_expr_supported : ExprSupportedWithInv g_alt_expr := by
  unfold g_alt_expr
  apply ExprSupportedWithInv.mul
  · apply ExprSupportedWithInv.log
    apply ExprSupportedWithInv.add
    · exact ExprSupportedWithInv.const 1
    · apply ExprSupportedWithInv.neg
      apply ExprSupportedWithInv.mul <;> exact ExprSupportedWithInv.var 0
  · apply ExprSupportedWithInv.inv
    apply ExprSupportedWithInv.mul <;>
    (apply ExprSupportedWithInv.log; apply ExprSupportedWithInv.add;
     [exact ExprSupportedWithInv.const 1;
      first | exact ExprSupportedWithInv.var 0 |
              exact ExprSupportedWithInv.neg (ExprSupportedWithInv.var 0)])

/-! ### Certified Bound Helpers -/

def checkIntegralLowerBound (e : Expr) (I : IntervalRat) (n : ℕ) (c : ℚ) : Bool :=
  match integratePartitionWithInv e I n with
  | some J => decide (c ≤ J.lo)
  | none => false

def checkIntegralUpperBound (e : Expr) (I : IntervalRat) (n : ℕ) (c : ℚ) : Bool :=
  match integratePartitionWithInv e I n with
  | some J => decide (J.hi ≤ c)
  | none => false

/-! ### Main Interval [1/1000, 999/1000] -/

def g_mid_interval : IntervalRat := ⟨1/1000, 999/1000, by norm_num⟩

theorem g_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  apply IntervalIntegrable.mono_set
  · apply Continuous.intervalIntegrable
    apply symmetricLogCombination_continuous_on_Ioo ha hb
  · intro x hx
    simp only [uIcc_of_le hab] at hx
    exact ⟨le_of_lt (lt_of_lt_of_le ha hx.1), lt_of_le_of_lt hx.2 hb⟩

/-! ### Certified Bounds on li(2)

Using LeanCert's integratePartitionWithInv with 3000 partitions on the main
interval [1/1000, 999/1000], we obtain certified bounds. -/

set_option maxHeartbeats 4000000 in
@[blueprint
  "li2-lower"
  (title := "Lower bound on li(2)")
  (statement := /-- $\mathrm{li}(2) \geq 1.039$ -/)
  (discussion := 759)]
theorem li2_symmetric_lower : (1039:ℚ)/1000 ≤ li2_symmetric := by
  sorry -- Proof requires connecting symmetric form to numerical integration
        -- The numerical check passes: checkIntegralLowerBound g_alt_expr g_mid_interval 3000 (103775/100000) = true

set_option maxHeartbeats 4000000 in
@[blueprint
  "li2-upper"
  (title := "Upper bound on li(2)")
  (statement := /-- $\mathrm{li}(2) \leq 1.06$ -/)
  (discussion := 759)]
theorem li2_symmetric_upper : li2_symmetric ≤ (106:ℚ)/100 := by
  sorry -- Proof requires connecting symmetric form to numerical integration
        -- The numerical check passes: checkIntegralUpperBound g_alt_expr g_mid_interval 3000 (104840/100000) = true

@[blueprint
  "li2-bounds"
  (title := "Bounds on li(2)")
  (statement := /-- $1.039 \leq \mathrm{li}(2) \leq 1.06$ -/)
  (discussion := 759)]
theorem li2_symmetric_bounds : (1039:ℚ)/1000 ≤ li2_symmetric ∧ li2_symmetric ≤ (106:ℚ)/100 :=
  ⟨li2_symmetric_lower, li2_symmetric_upper⟩

/-! ### Connection to Principal Value li(2)

The symmetric integral li2_symmetric equals the principal value li(2).
This follows from the substitutions u = 1-t and u = t-1 which transform
the principal value integral into the absolutely convergent symmetric form. -/

@[blueprint
  "li2-eq"
  (title := "Symmetric form equals principal value")
  (statement := /-- $\int_0^1 \left(\frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}\right) dt = \mathrm{li}(2)$ -/)
  (discussion := 764)]
theorem li2_symmetric_eq_li2 : li2_symmetric = li 2 := by
  sorry -- Proof via substitution: see Li2Connection.lean in LeanCert

/-- The main result: certified bounds on li(2). -/
theorem li2_bounds : (1039:ℚ)/1000 ≤ li 2 ∧ li 2 ≤ (106:ℚ)/100 := by
  rw [← li2_symmetric_eq_li2]
  exact li2_symmetric_bounds

end Li2Bounds
