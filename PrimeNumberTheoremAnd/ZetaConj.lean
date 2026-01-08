import Architect
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate

blueprint_comment /--
Already on Mathlib (with a shortened proof):
-/
@[blueprint
  (title := "hasDerivAt-conj-conj")
  (statement := /--
  Let $f : \mathbb{C} \to \mathbb{C}$ be a complex differentiable function at $p \in \mathbb{C}$ with derivative $a$.
  Then the function $g(z) = \overline{f(\overline{z})}$ is complex differentiable at $\overline{p}$ with derivative $\overline{a}$.
  -/)
  (proof := /-- We expand the definition of the derivative and compute. -/)]
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

blueprint_comment /--
Submitted to Mathlib:
-/
@[blueprint
  (title := "deriv-conj-conj")
  (statement := /--
  Let $f : \mathbb{C} \to \mathbb{C}$ be a function at $p \in \mathbb{C}$ with derivative $a$.
  Then the derivative of the function $g(z) = \overline{f(\overline{z})}$ at $\overline{p}$ is $\overline{a}$.
  -/)
  (proof := /--
  We proceed by case analysis on whether $f$ is differentiable at $p$.
  If $f$ is differentiable at $p$, then we can apply the previous theorem.
  If $f$ is not differentiable at $p$, then neither is $g$, and both derivatives have the default value of zero.
  -/)]
theorem deriv_conj_conj (f : ℂ → ℂ) (p : ℂ) :
  deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  -- Case analysis on whether f is differentiable at p
  set g := fun z ↦ conj (f (conj z))
  by_cases hf : DifferentiableAt ℂ f p
  · exact (hasDerivAt_conj_conj hf.hasDerivAt).deriv
  · by_cases hg : DifferentiableAt ℂ g (conj p)
    · -- If the conjugated function were differentiable, then f would be differentiable
      have : DifferentiableAt ℂ f p := by
        convert (hasDerivAt_conj_conj hg.hasDerivAt).differentiableAt using 2 <;> simp[g]
      contradiction
    · -- Both derivatives are zero when the functions are not differentiable
      rw [deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt hf, map_zero]


@[blueprint
  (title := "conj-riemannZeta-conj-aux1")
  (statement := /--
  Conjugation symmetry of the Riemann zeta function in the half-plane of convergence.
  Let $s \in \mathbb{C}$ with $\Re(s) > 1$.
  Then $\overline{\zeta(\overline{s})} = \zeta(s)$.
  -/)
  (proof := /-- We expand the definition of the Riemann zeta function as a series and find that the two sides are equal term by term. -/)]
lemma conj_riemannZeta_conj_aux1 (s : ℂ) (hs : 1 < s.re) : conj (riemannZeta (conj s)) = riemannZeta s := by
  rw[zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw[zeta_eq_tsum_one_div_nat_add_one_cpow]
  swap
  · simpa
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


blueprint_comment /--
% TODO: Submit this and the following corollaries to Mathlib.
-/
@[blueprint
  (title := "conj-riemannZeta-conj")
  (statement := /--
  Conjugation symmetry of the Riemann zeta function.
  Let $s \in \mathbb{C}$.
  Then $$\overline{\zeta(\overline{s})} = \zeta(s).$$
  -/)
  (proof := /-- By the previous lemma, the two sides are equal on the half-plane $\{s \in \mathbb{C} : \Re(s) > 1\}$. Then, by analytic continuation, they are equal on the whole complex plane. -/)]
theorem conj_riemannZeta_conj (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by
  by_cases hs1 : s = 1
  · subst hs1
    rw[map_one, Complex.conj_eq_iff_real]
    rw[riemannZeta_one]
    use (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
    norm_cast
    rw[← Complex.ofReal_log]
    · push_cast
      rfl
    · positivity
  · let U : Set ℂ := {1}ᶜ
    let g := fun s ↦ conj (riemannZeta (conj s))
    suffices Set.EqOn g riemannZeta U by
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
    · refine (?_ : IsConnected U).isPreconnected
      refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
      simp



@[blueprint
  (title := "riemannZeta-conj")
  (statement := /--
  Conjugation symmetry of the Riemann zeta function.
  Let $s \in \mathbb{C}$.
  Then $$\zeta(\overline{s}) = \overline{\zeta(s)}.$$
  -/)
  (proof := /-- This follows as an immediate corollary of Theorem \ref{conj_riemannZeta_conj}. -/)]
theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rw [← conj_riemannZeta_conj, Complex.conj_conj]




@[blueprint
  (title := "deriv-riemannZeta-conj")
  (statement := /--
  Conjugation symmetry of the derivative of the Riemann zeta function.
  Let $s \in \mathbb{C}$.
  Then $$\zeta'(\overline{s}) = \overline{\zeta'(s)}.$$
  -/)
  (proof := /-- We apply the derivative conjugation symmetry to the Riemann zeta function and use the conjugation symmetry of the Riemann zeta function itself. -/)]
theorem deriv_riemannZeta_conj (s : ℂ) : deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp[← deriv_conj_conj, conj_riemannZeta_conj]



theorem logDerivZeta_conj (s : ℂ) : (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp[deriv_riemannZeta_conj, riemannZeta_conj]

theorem logDerivZeta_conj' (s : ℂ) : (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s


blueprint_comment /--
% TODO: Submit this to Mathlib.
-/
@[blueprint
  (title := "intervalIntegral-conj")
  (statement := /--
  The conjugation symmetry of the interval integral.
  Let $f : \mathbb{R} \to \mathbb{C}$ be a measurable function, and let $a, b \in \mathbb{R}$.
  Then $$\int_{a}^{b} \overline{f(x)} \, dx = \overline{\int_{a}^{b} f(x) \, dx}.$$
  -/)
  (proof := /-- We unfold the interval integral into an integral over a uIoc and use the conjugation property of integrals. -/)]
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} : ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj]
  rw [← RCLike.conj_smul, ← intervalIntegral.intervalIntegral_eq_integral_uIoc]
