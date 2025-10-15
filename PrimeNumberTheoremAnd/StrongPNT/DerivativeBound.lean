/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.AbsMax

theorem derivativeBound {R M r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
  (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (f_zero_at_zero : f 0 = 0)
  (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
  (pos_r : 0 < r) (z_in_r : z ∈ Metric.closedBall 0 r)
  (r_le_r' : r < r') (r'_le_R : r' < R) :
  ‖(deriv f) z‖ ≤ 2 * M * (r')^2 / ((R - r') * (r' - r)^2) := by sorry
