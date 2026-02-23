import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Complex
example : Filter.Tendsto (fun x : ℂ ↦ sin x / x) (𝓝 0) (𝓝 1) := tendsto_sin_div_id
