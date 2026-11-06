import RSBounds.BacklundCountRectangle

/-!
# Identification with nontrivial zeta zeros and their actual orders

These bridges identify the concrete finite count with zeros of zeta, counted
with analytic multiplicity; no simple-zero hypothesis is made.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

theorem xiF_eq_zero_of_zeta_zero {ρ : ℂ} (him : ρ.im ≠ 0)
    (hz : riemannZeta ρ = 0) : xiF ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by intro h; apply him; simp [h]
  have hρ1 : ρ ≠ 1 := by intro h; apply him; simp [h]
  have hG : Gammaℝ ρ ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := Gammaℝ_eq_zero_iff.mp h
    apply him
    rw [hm]
    simp
  have hΛ : completedRiemannZeta ρ = 0 := by
    rw [riemannZeta_def_of_ne_zero hρ0] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hG
  have he : completedRiemannZeta₀ ρ = completedRiemannZeta ρ +
      1 / ρ + 1 / (1 - ρ) := by
    rw [completedRiemannZeta_eq]
    ring
  rw [xiF, he, hΛ]
  have h1 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr hρ1.symm
  field_simp
  ring

theorem mem_positiveZeros_iff_zeta {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
    ρ ∈ positiveZeros T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im < T := by
  rw [mem_positiveZeros_iff hT]
  constructor
  · rintro ⟨hz, h0, hT⟩
    have hre := xiF_zero_re_strip hz
    exact ⟨(xiF_eq_zero_iff hre.1 hre.2).mp hz, h0, hT⟩
  · rintro ⟨hz, h0, hT⟩
    exact ⟨xiF_eq_zero_of_zeta_zero h0.ne' hz, h0, hT⟩

theorem analyticOrderAt_xi_eq_zeta {ρ : ℂ} (hρ : xiF ρ = 0) :
    analyticOrderAt xiF ρ = analyticOrderAt riemannZeta ρ := by
  have hre := xiF_zero_re_strip hρ
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hre
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hre
  have hloc : xiF =ᶠ[𝓝 ρ] fun s => (s * Gammaℝ s * (s - 1)) * riemannZeta s := by
    have hu : {s : ℂ | 0 < s.re ∧ s ≠ 1} ∈ 𝓝 ρ :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne).mem_nhds ⟨hre.1, hρ1⟩
    filter_upwards [hu] with s hs
    rw [xiF_eq hs.1 hs.2, zetaF_of_ne hs.2]
    ring
  have hGamma : AnalyticAt ℂ Gammaℝ ρ := by
    apply DifferentiableOn.analyticOnNhd (s := {s : ℂ | 0 < s.re}) _
      (isOpen_lt continuous_const Complex.continuous_re) ρ hre.1
    intro s hs
    change 0 < s.re at hs
    have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m h
      have hr := congrArg Complex.re h
      simp at hr
      have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hd : DifferentiableAt ℂ
        (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) s :=
      (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)).mul
        ((Complex.differentiableAt_Gamma _ hm).comp s (differentiableAt_id.div_const 2))
    exact hd.differentiableWithinAt
  have he : AnalyticAt ℂ (fun s : ℂ => s * Gammaℝ s * (s - 1)) ρ :=
    (analyticAt_id.mul hGamma).mul (analyticAt_id.sub analyticAt_const)
  have hen : ρ * Gammaℝ ρ * (ρ - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hρ0 (Gammaℝ_ne_zero_of_re_pos hre.1)) (sub_ne_zero.mpr hρ1)
  rw [analyticOrderAt_congr hloc,
    show (fun s : ℂ => (s * Gammaℝ s * (s - 1)) * riemannZeta s) =
      (fun s : ℂ => s * Gammaℝ s * (s - 1)) * riemannZeta from rfl,
    analyticOrderAt_mul he (analyticOn_riemannZeta ρ hρ1),
    he.analyticOrderAt_eq_zero.mpr hen, zero_add]

theorem N_eq_sum_zetaMultiplicity {T : ℝ} (hT : 0 < T) :
    N T = ∑ ρ ∈ positiveZeros T, (analyticOrderAt riemannZeta ρ).toNat := by
  rw [N_eq_sum_analyticOrder hT]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [analyticOrderAt_xi_eq_zeta ((mem_positiveZeros_iff hT).mp hρ).1]

end TernaryGoldbach.RSBounds.BacklundCountIdentity
