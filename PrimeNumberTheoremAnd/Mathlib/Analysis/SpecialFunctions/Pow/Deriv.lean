/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Extra complex-power derivative API from the WF branch. -/

@[expose] public section

namespace Complex

/-- `(u : ℂ) ^ r` is continuous on `[a, b]` when `a > 0`. -/
theorem continuousOn_ofReal_cpow {r : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) :=
  (continuous_ofReal.continuousOn.cpow continuousOn_const
    (fun _ hu => (ofReal_mem_slitPlane).2 (lt_of_lt_of_le ha hu.1))).mono Set.Subset.rfl

theorem deriv_ofReal_cpow_neg (s : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (fun (t : ℝ) => (t : ℂ) ^ (-s)) x = -s * (x : ℂ) ^ (-s - 1) := by
  by_cases hs : s = 0
  · simp [hs, deriv_const, cpow_zero, sub_eq_add_neg]
  · simpa [sub_eq_add_neg] using deriv_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)

theorem continuousOn_deriv_ofReal_cpow_neg (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv (fun (t : ℝ) => (t : ℂ) ^ (-s))) (Set.Icc a b) :=
    ((continuousOn_const : ContinuousOn (fun (_ : ℝ) => (-s : ℂ)) (Set.Icc a b)).mul
      (continuousOn_ofReal_cpow (r := -s - 1) ha)).congr fun t ht =>
    deriv_ofReal_cpow_neg s (lt_of_lt_of_le ha ht.1)

theorem ofReal_cpow_mul_cpow_neg_sub_one (s : ℂ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
  have hx : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  calc
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [cpow_one]
    _ = (u : ℂ) ^ (-s) := by rw [← cpow_add _ _ hx]; ring_nf

theorem natCast_mul_cpow_neg_eq_cpow_one_sub (N : ℕ) (s : ℂ) (hN : N ≠ 0) :
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 : ℂ) * (N : ℂ) ^ (-s) := by simp [cpow_one]
    _ = (N : ℂ) ^ (1 - s) := by rw [← cpow_add _ _ hN']; ring_nf

theorem HasDerivAt.const_mul_ofReal_cpow_neg_sub_one (a : ℂ) {u : ℝ} (hu : 0 < u) (z : ℂ) :
    HasDerivAt (fun w => a * (u : ℂ) ^ (-w - 1))
      (-a * (Complex.log u) * (u : ℂ) ^ (-z - 1)) z := by
  set huC : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hf : HasDerivAt (fun w => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_id z).neg.sub_const (1 : ℂ)
  have hbase : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) hf (Or.inl huC)
  have hbase' : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (ofReal_log (x := u) (hx := le_of_lt hu))
  simpa [hlog, mul_comm, mul_left_comm, mul_assoc] using hbase'.const_mul a

end Complex
