-- import Mathlib.Analysis.Calculus.Deriv.Basic
--import Mathlib.Data.Complex.Basic
--import Mathlib.Analysis.Complex.Schwarz
--import Mathlib.MeasureTheory.Measure.Restrict
--import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.Filter.AtTopBot
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Set Filter

example (f g : ℝ → ℝ) (g_integrableOn : IntegrableOn g (Ioi (0 : ℝ)))
    (f_le_g_atTop : f =O[atTop] g) : IntegrableOn f (Ioi (0 : ℝ)) := by
  sorry

#exit

example (r : ℝ) (hr : 0 < r) : ∀ᵐ (a : ℝ) ∂volume.restrict (Ioi (1 : ℝ)),
    |Real.log a| ≤ |a ^ r| := by
  have' := isLittleO_log_rpow_atTop hr
  have' := Asymptotics.IsLittleO.eventuallyLE this
  convert this.filter_mono ?_ using 1
  intro s hs
  simp only [Filter.mem_atTop_sets, ge_iff_le] at hs
  simp only [measurableSet_Ioi, ae_restrict_eq]
  obtain ⟨a, ha⟩ := hs
  apply Filter.mem_inf_of_inter (s := s) (t := s)
  · rw [MeasureTheory.mem_ae_iff]


  sorry

#exit

example (s : ℂ) : HasDerivAt id 1 s := by
  exact hasDerivAt_id s
  sorry

#exit

example : MeasurableSet {x : ℝ | 0 < x} := by
  apply (isOpen_lt' 0).measurableSet
  exac

example (s : Set ℝ) (hs : MeasurableSet s) (P : ℝ → Prop) (hP : ∀ x ∈ s, P x) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict s), P x := by

  filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
  exact hP
