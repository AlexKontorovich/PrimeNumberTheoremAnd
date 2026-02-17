import Mathlib.Algebra.Order.Interval.Set.Group

open Set Function

example (a p : ℝ) :
    Pairwise (Disjoint on fun n : ℤ => Ioc (a + n • p) (a + (n + 1) • p)) := by
  simpa using (pairwise_disjoint_Ioc_add_zsmul a p)
