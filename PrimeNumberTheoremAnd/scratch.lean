import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Group.Basic
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.MellinCalculus
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Order.Group.Lattice
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Bound

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set

example (a b c : ℂ) : a * b / c = a * (b / c) := by
  exact mul_div_assoc a b c

rw[mul_div_assoc]
    apply Asymptotics.IsBigO.const_mul_left
