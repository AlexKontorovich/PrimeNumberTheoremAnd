import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Basic
import PrimeNumberTheoremAnd.MediumPNT
--import Mathlib.Analysis.Analytic.Basic
--import Mathlib.NumberTheory.ZetaFunction

open Complex ComplexConjugate

lemma conj_riemannZeta_conj_aux1 (s : ℂ) (hs : 1 < s.re) : conj (riemannZeta (conj s)) = riemannZeta s := by
  rw[zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw[zeta_eq_tsum_one_div_nat_add_one_cpow]
  swap
  simpa
  rw [conj_tsum]
  congr
  ext n
  have : n + 1 ≠ 0 := by linarith
  have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast this
  rw[cpow_def_of_ne_zero this]
  rw[cpow_def_of_ne_zero this]
  rw[RCLike.conj_div, map_one, ← exp_conj, map_mul, conj_conj]
  norm_cast
  rw[conj_ofReal]

theorem conj_riemannZeta_conj_analytic : AnalyticOnNhd ℂ (fun s ↦ (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) s))) {1}ᶜ :=
  by sorry


theorem conj_riemannZeta_conj (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by
  by_cases hs1 : s = 1
  · subst hs1
    rw[map_one, conj_eq_iff_real]
    rw[riemannZeta_one]
    use (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
    norm_cast
    rw[← ofReal_log]
    norm_cast
    push_cast
    rfl
    positivity
  · let U : Set ℂ := {1}ᶜ
    let f := riemannZeta
    let g := fun s ↦ conj (riemannZeta (conj s))
    suffices Set.EqOn g f U by
      apply this
      rwa[Set.mem_compl_singleton_iff]
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2)
    · simp[U]
    · rw [Filter.eventuallyEq_iff_exists_mem]
      use {s : ℂ | s.re > 1}
      constructor
      · have := isOpen_re_gt_EReal (1 : ℝ)
        norm_cast at this
        exact (isOpen_iff_mem_nhds.mp this) 2 (by simp)
      · intro s hs
        exact conj_riemannZeta_conj_aux1 s hs
    swap
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      exact (differentiableAt_riemannZeta hs₁).differentiableWithinAt
    · exact conj_riemannZeta_conj_analytic
    · refine (?_ : IsConnected ({1}ᶜ : Set ℂ)).isPreconnected
      refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
      simp
