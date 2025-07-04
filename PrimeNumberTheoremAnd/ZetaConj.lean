import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Topology.EMetricSpace.Paracompact

open scoped Complex ComplexConjugate


/-$$
Let $f : \mathbb{C} \to \mathbb{C}$ be a complex differentiable function at $p \in \mathbb{C}$ with derivative $a$.
Then the function $g(z) = \overline{f(\overline{z})}$ is complex differentiable at $\overline{p}$ with derivative $\overline{a}$.
$$-/
theorem hasDerivAt_conj_conj {f : ℂ → ℂ} {p a : ℂ} (hf : HasDerivAt f a p) :
    HasDerivAt (fun z ↦ conj (f (conj z))) (conj a) (conj p) := by
  rw [hasDerivAt_iff_tendsto] at hf ⊢
  have := Complex.continuous_conj.tendsto (conj p)
  rw [Complex.conj_conj] at this
  have := Filter.Tendsto.comp hf this
  convert this with z
  simp only [Complex.conj_conj, smul_eq_mul, Function.comp_apply]
  congr 1
  · congr 1
    rw[← Complex.norm_conj]
    simp
  · rw[← Complex.norm_conj]
    simp

/-$$
Let $s \in \mathbb{C}$ with $\Re(s) > 1$.
Then $\overline{\zeta(\overline{s})} = \zeta(s)$.
$$-/
lemma conj_riemannZeta_conj_aux1 (s : ℂ) (hs : 1 < s.re) : conj (riemannZeta (conj s)) = riemannZeta s := by
  rw[zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw[zeta_eq_tsum_one_div_nat_add_one_cpow]
  swap
  simpa
  rw [Complex.conj_tsum]
  congr
  ext n
  have : n + 1 ≠ 0 := by linarith
  have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast this
  rw[Complex.cpow_def_of_ne_zero this]
  rw[Complex.cpow_def_of_ne_zero this]
  rw[RCLike.conj_div, map_one, ← Complex.exp_conj, map_mul, Complex.conj_conj]
  norm_cast
  rw[Complex.conj_ofReal]

/-$$
Let $s \in \mathbb{C}$.
Then $\overline{\zeta(\overline{s})} = \zeta(s)$.
We prove this by analytic continuation from the region $\Re(s) > 1$, using the previous lemma.
$$-/
theorem conj_riemannZeta_conj (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by
  by_cases hs1 : s = 1
  · subst hs1
    rw[map_one, Complex.conj_eq_iff_real]
    rw[riemannZeta_one]
    use (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
    norm_cast
    rw[← Complex.ofReal_log]
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
      set V := Complex.re ⁻¹' (Set.Ioi 1)
      use V
      constructor
      · have Vopen : IsOpen V := Continuous.isOpen_preimage Complex.continuous_re _ isOpen_Ioi
        have two_in_V : 2 ∈ V := by simp[V]
        exact IsOpen.mem_nhds Vopen two_in_V
      · intro s hs
        exact conj_riemannZeta_conj_aux1 s hs
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      have hs₁' : conj s₁ ≠ 1 := (map_ne_one_iff (starRingEnd ℂ) (RingHom.injective (starRingEnd ℂ))).mpr hs₁
      convert (hasDerivAt_conj_conj (differentiableAt_riemannZeta hs₁').hasDerivAt).differentiableAt.differentiableWithinAt (s := U)
      rw[Complex.conj_conj]
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      exact (differentiableAt_riemannZeta hs₁).differentiableWithinAt
    · refine (?_ : IsConnected ({1}ᶜ : Set ℂ)).isPreconnected
      refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
      simp

theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rw [← conj_riemannZeta_conj, Complex.conj_conj]
