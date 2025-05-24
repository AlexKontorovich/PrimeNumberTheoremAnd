import Mathlib.LinearAlgebra.Dimension.FiniteDimensional
import Mathlib.LinearAlgebra.LinearMap.Basic
import Mathlib.LinearAlgebra.Submodule.Basic

open LinearMap Submodule FiniteDimensional

variable {𝕜 : Type*} [Field 𝕜] (V : Type*) [AddCommGroup V] [Module 𝕜 V]

/-- Let T be a linear operator on a 3-dimensional vector space V.
    Suppose that every 2-dimensional subspace of V is T-invariant.
    Then T is a scalar multiple of the identity operator. -/
theorem linear_operator_with_invariant_subspaces
    [FiniteDimensional 𝕜 V] (h_dim : finrank 𝕜 V = 3)
    (T : V →ₗ[𝕜] V)
    (h_invariant : ∀ (W : Submodule 𝕜 V), finrank 𝕜 W = 2 → T.mapsTo W W) :
    ∃ (c : 𝕜), T = c • LinearMap.id :=

  sorry










#exit
-- import Mathlib.Analysis.Calculus.Deriv.Basic
--import Mathlib.Data.Complex.Basic
--import Mathlib.Analysis.Complex.Schwarz
--import Mathlib.MeasureTheory.Measure.Restrict
--import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.Filter.AtTopBot
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Set Filter

/-%
Want to say:
$f(x , t) \ll g(x, t)$ as $x \to \infy$
%-/

example (f g : ℝ → ℝ) (param : ℝ)


#exit

example (f : ℝ → ℝ) (a b c : ℝ) : ∫ x in a..b, f x = ∫ x in a..c, f x + ∫ x in c..b, f x := by
  rw [integral_add_adjacent_intervals f a c b]
  exact integral_add

theorem Real.log_monotoneOn : MonotoneOn (fun x : ℝ ↦ log x) { x | 0 < x } := by
  -- TODO: can be strengthened to exp (-1) ≤ x
  simp only [MonotoneOn, mem_setOf_eq]
  intro x hex y hey hxy
  exact (log_le_log_iff hex hey).mpr hxy
  refine (log_le_log_iff ?h ?h₁).mpr hxy


#exit

example (n : ℝ ) : n^ 2 = n * n := by
  exact pow_two n

#exit

lemma norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by
  have := Complex.ofReal_log (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [(by simp : ((n : ℝ) : ℂ) = (n : ℂ))] at this
  rw [← this, Complex.norm_eq_abs, Complex.abs_of_nonneg]
  exact Real.log_natCast_nonneg n



#exit
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
