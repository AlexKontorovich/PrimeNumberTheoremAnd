import EulerProducts.PNT
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.Support
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.FunProp.AEMeasurable
import Mathlib.Tactic.FunProp.Measurable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics

open Nat Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries Asymptotics
open Complex hiding log
-- note: the opening of ArithmeticFunction introduces a notation σ that seems impossible to hide, and hence parameters that are traditionally called σ will have to be called σ' instead in this file.

open scoped Topology

-- This version makes the support of Ψ explicit, and this is easier for some later proofs
lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3: c < d) :
    ∃ Ψ : ℝ → ℝ, (∀ n, ContDiff ℝ n Ψ) ∧ (HasCompactSupport Ψ) ∧ Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧
    Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧ (Function.support Ψ = Set.Ioo a d) := by

  have := exists_msmooth_zero_iff_one_iff_of_isClosed
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici)
    (isClosed_Icc)
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc,
        Set.mem_empty_iff_false, and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)

  rcases this with ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩

  simp only [Set.EqOn, Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici,
    ContMDiffMap.coeFn_mk, Pi.zero_apply, Set.mem_Icc, Pi.one_apply, and_imp] at *
  use Ψ
  constructor
  · rw [contDiff_all_iff_nat, ←contDiff_top]
    exact ContMDiff.contDiff hΨSmooth
  · constructor
    · rw [hasCompactSupport_def]
      apply IsCompact.closure_of_subset (K := Set.Icc a d) isCompact_Icc
      simp_rw [Function.support_subset_iff, ne_eq, <-hΨ0]
      intro x hx
      contrapose! hx
      simp only [Set.mem_Icc, not_and_or] at hx
      by_contra! h'
      cases' hx <;> linarith
    · constructor
      · intro x
        rw [Set.indicator_apply]
        split_ifs with h
        · simp only [Set.mem_Icc, Pi.one_apply] at *
          simp_rw [hΨ1 x] at h
          exact Eq.le (_root_.id h.symm)
        · have : Ψ x ∈ Set.range Ψ := by simp only [Set.mem_range, exists_apply_eq_apply]
          have : Ψ x ∈ Set.Icc 0 1 := hΨrange this
          exact this.left
      · constructor
        · intro x
          rw [Set.indicator_apply]
          split_ifs with h
          · have : Ψ x ∈ Set.range Ψ := by simp only [Set.mem_range, exists_apply_eq_apply]
            have : Ψ x ∈ Set.Icc 0 1 := by exact hΨrange this
            simpa using this.2
          · simp only [Set.mem_Ioo, Pi.one_apply] at *
            simp only [not_and_or, not_lt] at h
            simp_rw [hΨ0 x] at h
            exact Eq.le h
        · simp_rw [Function.support, ne_eq, ←hΨ0]
          push_neg
          simp [Set.ext_iff]
  done


/-%%
The Fourier transform of an absolutely integrable function $\psi: \R \to \C$ is defined by the formula
$$ \hat \psi(u) := \int_\R e(-tu) \psi(t)\ dt$$
where $e(\theta) := e^{2\pi i \theta}$.

Let $f: \N \to \C$ be an arithmetic function such that $\sum_{n=1}^\infty \frac{|f(n)|}{n^\sigma} < \infty$ for all $\sigma>1$.  Then the Dirichlet series
$$ F(s) := \sum_{n=1}^\infty \frac{f(n)}{n^s}$$
is absolutely convergent for $\sigma>1$.
%%-/

noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} {σ' : ℝ} {n : ℕ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

variable {f : ArithmeticFunction ℂ}

@[simp]
theorem nnnorm_eq_of_mem_circle (z : circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp)

@[simp]
theorem nnnorm_circle_smul (z : circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

lemma hf_coe1 {σ' : ℝ} (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hσ : 1 < σ') : ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

lemma first_fourier_aux1 {ψ : ℝ → ℂ} (hψ: Continuous ψ) {x : ℝ} (n : ℕ) : Measurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖₊ : ENNReal) := by
  -- TODO: attribute [fun_prop] Real.continuous_fourierChar once `fun_prop` bugfix is merged
  refine Measurable.comp ?_ (by fun_prop) |>.smul (by fun_prop)
    |>.nnnorm |>.coe_nnreal_ennreal
  exact Continuous.measurable Real.continuous_fourierChar

lemma first_fourier_aux2a {x y : ℝ} {n : ℕ} :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num; exact pi_ne_zero), one_mul]

lemma first_fourier_aux2 {ψ : ℝ → ℂ} {σ' x y : ℝ} (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 [-(y * (1 / (2 * π) * Real.log (n / x)))] • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0 ; simp [term, hn]
  simp only [term, hn, ↓reduceIte, fourierChar_apply]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) / ↑((n : ℝ) ^ σ'))) • ψ y := by
      have : ((↑n : ℂ) ^ (σ' : ℂ) : ℂ) = ((↑n : ℝ) ^ (σ' : ℝ) : ℝ) := by
        rw [Complex.cpow_def_of_ne_zero (by simp [hn]), Real.rpow_def_of_nonneg (cast_nonneg n)]
        simp [hn]
      simp [smul_eq_mul, mul_assoc, this] ; ring_nf
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

/-%%
\begin{lemma}[First Fourier identity]\label{first-fourier}\lean{first_fourier}\leanok  If $\psi: \R \to \C$ is continuous and compactly supported and $x > 0$, then for any $\sigma>1$
  $$ \sum_{n=1}^\infty \frac{f(n)}{n^\sigma} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) = \int_\R F(\sigma + it) \psi(t) x^{it}\ dt.$$
\end{lemma}
%%-/
lemma first_fourier {ψ : ℝ → ℂ} (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcont: Continuous ψ) (hsupp: HasCompactSupport ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 ψ (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by
/-%%
\begin{proof}\leanok  By the definition of the Fourier transform, the left-hand side expands as
$$ \sum_{n=1}^\infty \int_\R \frac{f(n)}{n^\sigma} \psi(t) e( - \frac{1}{2\pi} t \log \frac{n}{x})\ dt$$
while the right-hand side expands as
$$ \int_\R \sum_{n=1}^\infty \frac{f(n)}{n^{\sigma+it}} \psi(t) x^{it}\ dt.$$
Since
$$\frac{f(n)}{n^\sigma} \psi(t) e( - \frac{1}{2\pi} t \log \frac{n}{x}) = \frac{f(n)}{n^{\sigma+it}} \psi(t) x^{it}$$
the claim then follows from Fubini's theorem.
\end{proof}
%%-/
  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) / ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by rfl
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) / ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_mul_left]
    _ = ∫ (v : ℝ), ∑' (n : ℕ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) / ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · -- TODO: attribute [fun_prop] Real.continuous_fourierChar once `fun_prop` bugfix is merged
        refine fun _ ↦ Measurable.aestronglyMeasurable ?_
        refine Measurable.mul (by fun_prop) ((Measurable.comp ?_ (by fun_prop)).smul (by fun_prop))
        exact Continuous.measurable Real.continuous_fourierChar
      · simp_rw [nnnorm_mul]
        push_cast
        simp_rw [lintegral_const_mul _ (first_fourier_aux1 hcont _)]
        calc
          _ = (∑' (i : ℕ), (‖term f σ' i‖₊ : ENNReal)) * ∫⁻ (a : ℝ), ‖ψ a‖₊ ∂volume := by
            simp [ENNReal.tsum_mul_right]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt (hcont.integrable_of_hasCompactSupport hsupp).2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← tsum_smul_const]
      · congr with n ; exact first_fourier_aux2 hx n
      · apply Summable.of_norm
        convert hf σ' hσ with n
        by_cases h : n = 0
        · simp [nterm, term, h]
        · simp [nterm, term, h]
          have : (n : ℂ) ≠ 0 := by simp [h]
          simp [Complex.abs_cpow_of_ne_zero this]

/-%%
\begin{lemma}[Second Fourier identity]\label{second-fourier}\lean{second_fourier}\leanok If $\psi: \R \to \C$ is continuous and compactly supported and $x > 0$, then for any $\sigma>1$
$$ \int_{-\log x}^\infty e^{-u(\sigma-1)} \hat \psi(\frac{u}{2\pi})\ du = x^{\sigma - 1} \int_\R \frac{1}{\sigma+it-1} \psi(t) x^{it}\ dt.$$
\end{lemma}
%%-/

@[continuity]
lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

attribute [fun_prop] measurable_coe_nnreal_ennreal

lemma second_fourier_integrable_aux1a {x σ' : ℝ} (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x), integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 {ψ : ℝ → ℂ}
    (hcont: Continuous ψ) (hsupp: HasCompactSupport ψ) {σ' x : ℝ} (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    apply MeasureTheory.measurable_uncurry_of_continuous_of_measurable <;> intro i
    swap; apply Continuous.measurable
    all_goals exact Continuous.smul (by fun_prop) <|
      (Continuous.subtype_val (by continuity)).smul (by fun_prop)
  · let f1 : ℝ → ENNReal := fun a1 ↦ ↑‖cexp (-(↑a1 * (↑σ' - 1)))‖₊
    let f2 : ℝ → ENNReal := fun a2 ↦ ↑‖ψ a2‖₊
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by simpa [Function.uncurry, HasFiniteIntegral]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> unfold_let f1 f2; fun_prop; fun_prop
    exact ENNReal.mul_lt_top (ne_top_of_lt (second_fourier_integrable_aux1a hσ).2)
      (ne_top_of_lt (hcont.integrable_of_hasCompactSupport hsupp).2)

lemma second_fourier_integrable_aux2 {σ' t x : ℝ} (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.abs_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux {x σ' t : ℝ} (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

lemma second_fourier {ψ : ℝ → ℂ} (hcont: Continuous ψ) (hsupp: HasCompactSupport ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 ψ (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by
/-%%
\begin{proof}\leanok
The left-hand side expands as
$$ \int_{-\log x}^\infty \int_\R e^{-u(\sigma-1)} \psi(t) e(-\frac{tu}{2\pi})\ dt\ du =
x^{\sigma - 1} \int_\R \frac{1}{\sigma+it-1} \psi(t) x^{it}\ dt$$
so by Fubini's theorem it suffices to verify the identity
\begin{align*}
\int_{-\log x}^\infty e^{-u(\sigma-1)} e(-\frac{tu}{2\pi})\ du
&= \int_{-\log x}^\infty e^{(it - \sigma + 1)u}\ du \\
&= \frac{1}{it - \sigma + 1} e^{(it - \sigma + 1)u}\ \Big|_{-\log x}^\infty \\
&= x^{\sigma - 1} \frac{1}{\sigma+it-1} x^{it}
\end{align*}
\end{proof}
%%-/
  conv in ↑(rexp _) * _ => { rw [Real.fourierIntegral_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap (second_fourier_integrable_aux1 hcont hsupp hσ),
    ← integral_mul_left]
  congr 1; ext t
  simp_rw [fourierChar_apply, smul_eq_mul, ← mul_assoc _ _ (ψ _), integral_mul_right]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      -↑u * (↑σ' - 1) + 2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num; exact pi_ne_zero)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c] ; intro h ; linarith
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ abs (cexp (c * ↑x)) / abs c) atTop (𝓝 (0 / abs c)) by simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (. * (1 - σ')) atTop atBot by simpa [Complex.abs_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_neg_const (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx

/-%%
Now let $A \in \C$, and suppose that there is a continuous function $G(s)$ defined on $\mathrm{Re} s \geq 1$ such that $G(s) = F(s) - \frac{A}{s-1}$ whenever $\mathrm{Re} s > 1$.  We also make the Chebyshev-type hypothesis
\begin{equation}\label{cheby}
\sum_{n \leq x} |f(n)| \ll x
\end{equation}
for all $x \geq 1$ (this hypothesis is not strictly necessary, but simplifies the arguments and can be obtained fairly easily in applications).
%%-/

variable {A : ℝ} {G : ℂ → ℂ}

theorem HasCompactSupport.integral_deriv_eq_zero {u : ℝ → ℂ} (h1 : ContDiff ℝ 1 u) (h2 : HasCompactSupport u) :
    ∫ x, deriv u x = 0 := by
  have l1 : Tendsto (fun i ↦ u i - u (-i)) atTop (𝓝 (∫ x, deriv u x)) := by
    have e1 : Integrable (deriv u) := (contDiff_one_iff_deriv.1 h1).2 |>.integrable_of_hasCompactSupport h2.deriv
    have e2 (i : ℝ) : ∫ x in -i..i, deriv u x = u i - u (-i) :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => h1.differentiable le_rfl x) e1.intervalIntegrable
    simpa [← e2] using intervalIntegral_tendsto_integral e1 tendsto_neg_atTop_atBot tendsto_id
  have l2 : Tendsto (fun i => u i - u (-i)) atTop (𝓝 0) := by
    have e1 : Tendsto u atTop (𝓝 0) := h2.is_zero_at_infty.mono_left _root_.atTop_le_cocompact
    have e2 : Tendsto (fun i => u (-i)) atTop (𝓝 0) :=
      h2.is_zero_at_infty.mono_left _root_.atBot_le_cocompact |>.comp tendsto_neg_atTop_atBot
    simpa using e1.sub e2
  exact tendsto_nhds_unique l1 l2

theorem HasCompactSupport.integral_mul_deriv {u v : ℝ → ℂ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (h : HasCompactSupport v) : ∫ x, u x * deriv v x = - ∫ x, deriv u x * v x := by
  have l1 : Integrable fun x ↦ u x * deriv v x :=
    hu.continuous.mul (contDiff_one_iff_deriv.1 hv).2 |>.integrable_of_hasCompactSupport h.deriv.mul_left
  have l2 : Integrable fun x ↦ deriv u x * v x :=
    (contDiff_one_iff_deriv.1 hu).2.mul hv.continuous |>.integrable_of_hasCompactSupport h.mul_left
  have l3 (a : ℝ) : deriv u a * v a + u a * deriv v a = deriv (u * v) a := by
    rw [← deriv_mul (hu.differentiable le_rfl a) (hv.differentiable le_rfl a)] ; rfl
  rw [eq_neg_iff_add_eq_zero, add_comm, ← integral_add l2 l1]
  simp_rw [l3]
  exact HasCompactSupport.integral_deriv_eq_zero (hu.mul hv) (h.mul_left)

theorem hasDerivAt_fourierChar' {u x : ℝ} : let e v := 𝐞 [-v * u];
    HasDerivAt e (-2 * π * u * I * e x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1 ; simp ; ring

theorem contDiff_fourierChar' {u : ℝ} : ContDiff ℝ 1 (fun v => 𝐞 [-v * u]) := by
  have l3 (x : ℝ) := (hasDerivAt_fourierChar' (u := u) (x := x)).deriv
  refine contDiff_one_iff_deriv.mpr ⟨fun x => hasDerivAt_fourierChar'.differentiableAt, ?_⟩
  rw [(funext l3 : deriv _ = _)]
  exact continuous_const.mul <| continuous_iff_continuousAt.mpr (fun x => hasDerivAt_fourierChar'.continuousAt)

lemma decay_bounds_aux3 {ψ : ℝ → ℂ} (h1 : ContDiff ℝ 1 ψ) (h2 : HasCompactSupport ψ) {u : ℝ} :
    𝓕 (deriv ψ) u = 2 * π * I * u * 𝓕 ψ u := by
  let e (v : ℝ) := 𝐞 [-v * u]
  simp_rw [Real.fourierIntegral_real_eq]
  convert_to ∫ (v : ℝ), e v * deriv ψ v = 2 * ↑π * I * ↑u * ∫ (v : ℝ), e v * ψ v
  · simp only [e, neg_mul, ofAdd_neg, map_inv, coe_inv_unitSphere, smul_eq_mul]
  · simp only [e, neg_mul, ofAdd_neg, map_inv, coe_inv_unitSphere, smul_eq_mul]
  have l3 (x : ℝ) : deriv e x = -2 * π * u * I * e x := hasDerivAt_fourierChar'.deriv
  simp_rw [h2.integral_mul_deriv contDiff_fourierChar' h1, l3, ← integral_mul_left, ← integral_neg]
  congr ; ext ; ring

lemma decay_bounds_aux4 {u : ℝ} {ψ : ℝ → ℂ} (h1 : ContDiff ℝ 2 ψ) (h2 : HasCompactSupport ψ) :
    u ^ 2 * 𝓕 ψ u = - (1 / (4 * π ^ 2) * 𝓕 (deriv^[2] ψ) u) := by
  have l1 : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp h1).2
  simp_rw [iterate, decay_bounds_aux3 l1 h2.deriv, decay_bounds_aux3 h1.of_succ h2]
  field_simp [pi_ne_zero] ; ring_nf ; simp

lemma decay_bounds_aux2 {u : ℝ} {ψ : ℝ → ℂ} (h1 : ContDiff ℝ 2 ψ) (h2 : HasCompactSupport ψ) :
    u ^ 2 * 𝓕 ψ u = - (1 / (4 * π ^ 2) * ∫ (t : ℝ), deriv^[2] ψ t * 𝐞 [-t * u]) := by
  convert decay_bounds_aux4 h1 h2 ; congr ; ext ; field_simp

lemma decay_bounds_aux1 {ψ : ℝ → ℂ} (h1 : ContDiff ℝ 2 ψ) (h2 : HasCompactSupport ψ) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 ψ u = ∫ (t : ℝ), (ψ t - (1 / (4 * π ^ 2)) * deriv^[2] ψ t) * 𝐞 [-t * u] := by
  have l0 : Continuous fun t ↦ 𝐞 [-t * u] := contDiff_fourierChar'.continuous
  have l1 : Integrable fun t ↦ 𝐞 [-t * u] * ψ t :=
    l0.mul h1.continuous |>.integrable_of_hasCompactSupport h2.mul_left
  have l2 : Integrable fun t ↦ 1 / (4 * π ^ 2) * (deriv^[2] ψ t * 𝐞 [-t * u]) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ h2.deriv.deriv.mul_right.mul_left
    exact continuous_const.mul <| (h1.iterate_deriv' 0 2).continuous.mul l0
  simp_rw [sub_mul, mul_assoc, add_mul, one_mul, mul_comm (ψ _)]
  rw [integral_sub l1 l2, integral_mul_left, sub_eq_add_neg, ← decay_bounds_aux2 h1 h2]
  simp [Real.fourierIntegral_real_eq]

lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

/-%%
\begin{lemma}[Decay bounds]\label{decay}\lean{decay_bounds}\leanok  If $\psi:\R \to \C$ is $C^2$ and obeys the bounds
  $$ |\psi(t)|, |\psi''(t)| \leq A / (1 + |t|^2)$$
  for all $t \in \R$, then
$$ |\hat \psi(u)| \leq C A / (1+|u|^2)$$
for all $u \in \R$, where $C$ is an absolute constant.
\end{lemma}
%%-/

lemma decay_bounds {ψ : ℝ → ℂ} {A u : ℝ} (h1 : ContDiff ℝ 2 ψ) (h2 : HasCompactSupport ψ)
    (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2)) (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 ψ u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have key := decay_bounds_aux1 h1 h2 u
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Complex.norm_eq_abs, Complex.abs_ofReal, abs_eq_self.2 l1.le]
  rw [le_div_iff l1, mul_comm, l2, ← norm_mul, key]
  let f (t : ℝ) := (ψ t - 1 / (4 * π ^ 2) * deriv^[2] ψ t) * 𝐞 [-t * u]
  let g (t : ℝ) := A * (1 + 1 / (4 * π ^ 2)) / (1 + t ^ 2)
  have l5 (t : ℝ) : ‖fourierChar [-t * u]‖ = 1 := by simp
  have l4 (t : ℝ) : ‖f t‖ ≤ g t := by
    simp only [f, g, norm_mul, l5, mul_one, mul_add, _root_.add_div]
    refine (norm_sub_le _ _).trans <| _root_.add_le_add (hA t) ?_
    rw [norm_mul]
    convert mul_le_mul_of_nonneg_left (hA' t) (norm_nonneg _) using 1 ; field_simp
  have l5 : Integrable g := by simpa [g, div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul _
  convert norm_integral_le_of_norm_le l5 (eventually_of_forall l4)
  simp_rw [g, div_eq_mul_inv, integral_mul_left, integral_univ_inv_one_add_sq]
  field_simp [pi_ne_zero] ; ring

lemma decay_bounds_cor_aux {ψ : ℝ → ℂ} (h1 : Continuous ψ) (h2 : HasCompactSupport ψ) :
    ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by exact h2.mul_left
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by continuity)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  simp only [norm_mul, Complex.norm_eq_abs, Complex.abs_ofReal, abs_eq_self.mpr (one_add_sq_pos u).le] at hC
  rwa [le_div_iff' (one_add_sq_pos _)]

lemma decay_bounds_cor {ψ : ℝ → ℂ} (h1 : ContDiff ℝ 2 ψ) (h2 : HasCompactSupport ψ) :
    ∃ C : ℝ, ∀ u, ‖𝓕 ψ u‖ ≤ C / (1 + u ^ 2) := by
  obtain ⟨C₁, hC₁⟩ := decay_bounds_cor_aux h1.continuous h2
  obtain ⟨C₂, hC₂⟩ := decay_bounds_cor_aux (ContDiff.iterate_deriv' 0 2 h1).continuous h2.deriv.deriv
  refine ⟨(π + 1 / (4 * π)) * (C₁ ⊔ C₂), fun u => decay_bounds h1 h2 (fun u => ?_) (fun u => ?_)⟩
  · exact hC₁ u |>.trans ((div_le_div_right (one_add_sq_pos _)).mpr le_sup_left)
  · exact hC₂ u |>.trans ((div_le_div_right (one_add_sq_pos _)).mpr le_sup_right)

/-%%
\begin{proof} From two integration by parts we obtain the identity
$$ (1+u^2) \hat \psi(u) = \int_{\bf R} (\psi(t) - \frac{u}{4\pi^2} \psi''(t)) e(-tu)\ dt.$$
Now apply the triangle inequality and the identity $\int_{\bf R} \frac{dt}{1+t^2}\ dt = \pi$ to obtain the claim with $C = \pi + 1 / 4 \pi$.
\end{proof}
%%-/

/-%%
\begin{lemma}[Limiting Fourier identity]\label{limiting}\lean{limiting_fourier}\leanok  If $\psi: \R \to \C$ is $C^2$ and compactly supported and $x \geq 1$, then
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) - A \int_{-\log x}^\infty \hat \psi(\frac{u}{2\pi})\ du =  \int_\R G(1+it) \psi(t) x^{it}\ dt.$$
\end{lemma}
%%-/

variable {ψ : ℝ → ℂ} {x : ℝ}

lemma continuous_LSeries_aux {f : ArithmeticFunction ℂ} {σ' : ℝ}  (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using continuous_const.div (continuous_const.cpow (by continuity) (by simp [h])) (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · field_simp [h, nterm, cpow_add _ _ (cast_ne_zero.mpr h)]
      rw [← Complex.norm_eq_abs, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
      simp
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hψ : ContDiff ℝ 2 ψ)
    (hsupp : HasCompactSupport ψ) (hx : 1 ≤ x) (σ' : ℝ) (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 ψ (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 ψ (u / (2 * π)) =
    ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by

  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hψ.continuous hsupp l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier hψ.continuous hsupp l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul hψ.continuous).mul l8
  have l4 : Integrable fun t ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) :=
    l6.integrable_of_hasCompactSupport hsupp.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp [← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul hψ.continuous).mul l8
    continuity
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact hsupp.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_mul_left, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply eventually_of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  field_simp [e2] ; left ; left
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i in Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- TODO nnabla is redundant -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_succ]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) := funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u := fun _ => Finset.sum_nonneg (fun i _ => hu i)

lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} : nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_succ, add_comm]

lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} : shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 - cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x in Finset.range (n + 1), A (x + 1) * b x = ∑ x in Finset.range n, A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x in Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x in Finset.range n, A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp [cumsum, shift, ha, nabla, sub_mul, mul_sub, l1, l2] ; abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp [Finset.sum_shift_back])

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) : Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) : Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp [BoundedAtFilter] ; constructor <;> intro h ; rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp [BoundedAtFilter, isBigO_iff] ; constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (m := N) (by linarith) ; subst n
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by linarith)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) : BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel <| NeZero.one_le.trans hn.le
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla] using hAb.add h

lemma continuous_FourierIntegral {ψ : ℝ → ℂ} (h1 : Continuous ψ) (h2 : HasCompactSupport ψ) :
    Continuous (𝓕 ψ) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar (by exact continuous_mul) <|
    h1.integrable_of_hasCompactSupport h2

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp [v, h, this] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_nat_cast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by filter_upwards [l7, l8] with n l2 l8 ; dsimp [u] ; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) := l3.comp_tendsto <| Nat.tendsto_pow_atTop_atTop_of_one_lt le.refl
  filter_upwards [l5, l8] with k l5 l8 ; field_simp [u, l5] ; ring

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) : Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right  _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ} (hf : Tendsto f atTop atTop) :
    (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isBigO_pow_pow_of_le {m n : ℕ} (h : m ≤ n) : (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with x l1
  simpa [abs_eq_self.mpr (zero_le_one.trans l1)] using pow_le_pow_right l1 h

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) : (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) : Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x ; field_simp [ha.ne.symm] ; rw [mul_div_assoc, mul_div_cancel'] ; linarith

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) : (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1 ; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) : f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff''] ; refine ⟨2⁻¹, by norm_num, ?_⟩ ; filter_upwards [h] with x h ; simp at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop (two_ne_zero)).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp at htx ; rw [nabla, ← htx, inv_le_inv (by linarith) hx] ; linarith

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 + (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx ; field_simp ; ring
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO (by simpa using (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

-- XXX THE REFACTOR LINE IS HERE

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) : Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop <| tendsto_atTop_add_const_left _ _ <| (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) : ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop, nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv, mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul (by linarith))
    · apply eventually_of_mem (Ici_mem_atTop 2) ; intro n (hn : 2 ≤ n)
      have e1 : n ≠ 0 := by linarith
      have e2 : n ≠ 1 := by linarith
      have e3 : n ≠ -1 := by linarith
      simp [e1, e2, e3]

  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff] ; use 1
    have e1 : ∀ᶠ n in atTop, 0 < d n := by
      apply eventually_of_mem (Ici_mem_atTop 1) ; intro n (hn : 1 ≤ n)
      have r1 : 0 < n := by linarith
      have r2 : 0 < (2 * π) ^ 2 := by apply sq_pos_of_ne_zero ; norm_num [pi_ne_zero]
      have r3 : 0 ≤ Real.log (↑n / x) ^ 2 := sq_nonneg _
      apply mul_pos r1 (by linarith)
    have e2 : ∀ᶠ n in atTop, 0 < d (n + 1) := (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually e1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      have : ∀ᶠ n in atTop, x ≤ n := by simpa using eventually_ge_atTop x
      filter_upwards [this] with n hn
      have e2 : 1 ≤ n / x := (one_le_div (by linarith)).mpr hn
      have e3 : n ≤ n + 1 := by linarith
      have e4 : 0 ≤ n + 1 := by linarith
      dsimp [d]
      gcongr
      exact Real.log_nonneg e2
    filter_upwards [e1, e2, e3] with n e1 e2 e3
    simp_rw [one_mul, Real.norm_eq_abs, abs_inv, abs_eq_self.mpr e1.le, abs_eq_self.mpr e2.le, inv_le_inv e2 e1]
    exact e3

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using (nnabla_mul_log_sq ((2 * π) ^ 2) (by linarith))

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  apply eventually_of_mem (Ici_mem_atTop 2) ; intro n (hn : 2 ≤ n)

  have : Real.log n ≠ 0 := by
    have e1 : n ≠ 0 := by linarith
    have e2 : n ≠ 1 := by linarith
    have e3 : n ≠ -1 := by linarith
    simp [e1, e2, e3]
  field_simp ; ring

lemma nnabla_bound {C x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp [div_eq_mul_inv]
  apply IsBigO.const_mul_left
  field_simp
  exact nnabla_bound_aux hx

/-- XXX THIS IS THE HIDING SCREEN -/

lemma limiting_fourier_lim1_aux (hcheby : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ))
    (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    field_simp [BoundedAtFilter]
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ (2 * π) ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp [abs_eq_self.mpr hC, abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this]
    apply div_le_of_nonneg_of_le_mul this hC
    gcongr
    apply le_add_of_le_of_nonneg le_rfl (sq_nonneg _)
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := nnabla_bound hx

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := by linarith
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div (by linarith)).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp only [ne_eq, log_eq_zero]
      push_neg
      refine ⟨this, ?_, ?_⟩ <;> linarith
    field_simp ; ring

theorem limiting_fourier_lim1 (hcheby : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ))
    (hψ : ContDiff ℝ 2 ψ) (hsupp : HasCompactSupport ψ) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦ ∑' n, term f σ' n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, term f 1 n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor hψ hsupp
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp [term, h]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply eventually_of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (cast_nonneg _))
    by_cases h : n = 0 <;> simp [h, nterm]
    have : 1 ≤ (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr h
    refine div_le_div (by simp only [apply_nonneg]) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ |x| * (C / (1 + (t / (2 * π)) ^ 2))) (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (hψ : ContDiff ℝ 2 ψ) (hsupp : HasCompactSupport ψ) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) * ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 ψ (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 ψ (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor hψ hsupp
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal' (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ (limiting_fourier_lim2_aux x C) ?_
    · apply eventually_of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral hψ.continuous hsupp
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsWithin_Ioi ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply eventually_of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) (abs_nonneg _)
        simp [Complex.abs_exp]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        apply (Real.exp_monotone this).trans
        simp [Real.exp_log (zero_lt_one.trans_le hx), abs_eq_self.mpr (zero_le_one.trans hx)]
    · apply eventually_of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hψ : ContDiff ℝ 2 ψ) (hsupp : HasCompactSupport ψ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅ ; simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := Set.reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm hsupp.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, hz, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  obtain ⟨Mψ, hMψ⟩ := hsupp.exists_bound_of_continuous hψ.continuous
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsWithin_Ioi (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by continuity) (by simp [hu.1])).mul hψ.continuous
    · apply Continuous.const_cpow (by continuity) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsWithin_Ioi (by simp))
    intro u hu
    apply eventually_of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [abs_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport hsupp.norm.mul_left
    have := hψ.continuous ; continuity
  · apply eventually_of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

lemma limiting_fourier (hcheby : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ))
    (hG: ContinuousOn G {s | 1 ≤ s.re}) (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hψ : ContDiff ℝ 2 ψ) (hsupp : HasCompactSupport ψ) (hx : 1 ≤ x) :
    ∑' n, term f 1 n * 𝓕 ψ (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 ψ (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby hψ hsupp (by linarith)
  have l2 := limiting_fourier_lim2 A hψ hsupp hx
  have l3 := limiting_fourier_lim3 hG hψ hsupp hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using eventually_of_forall (limiting_fourier_aux hG' hf hψ hsupp hx)

-- XXX THE REFACTOR TARGET IS HERE

/-%%
\begin{proof}
\uses{first-fourier,second-fourier,decay}
 By the preceding two lemmas, we know that for any $\sigma>1$, we have
  $$ \sum_{n=1}^\infty \frac{f(n)}{n^\sigma} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) - A x^{1-\sigma} \int_{-\log x}^\infty e^{-u(\sigma-1)} \hat \psi(\frac{u}{2\pi})\ du =  \int_\R G(\sigma+it) \psi(t) x^{it}\ dt.$$
  Now take limits as $\sigma \to 1$ using dominated convergence together with \eqref{cheby} and Lemma \ref{decay} to obtain the result.
\end{proof}
%%-/

/-%%
\begin{corollary}[Corollary of limiting identity]\label{limiting-cor}\lean{limiting_cor}\leanok  With the hypotheses as above, we have
  $$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) = A \int_{-\infty}^\infty \hat \psi(\frac{u}{2\pi})\ du + o(1)$$
  as $x \to \infty$.
\end{corollary}
%%-/

open Filter

lemma limiting_cor {ψ:ℝ → ℂ} (hψ: ContDiff ℝ 2 ψ) (hsupp: HasCompactSupport ψ) : Tendsto (fun x : ℝ ↦ ∑' n, f n / n * fourierIntegral ψ (1/(2*π) * log (n/x)) - A * ∫ u in Set.Ici (-log x), fourierIntegral ψ (u / (2*π)) ∂ volume) atTop (nhds 0) := by sorry

/-%%
\begin{proof}
\uses{limiting}
 Immediate from the Riemann-Lebesgue lemma, and also noting that $\int_{-\infty}^{-\log x} \hat \psi(\frac{u}{2\pi})\ du = o(1)$.
\end{proof}
%%-/

/-%%
\begin{lemma}[Smooth Urysohn lemma]\label{smooth-ury}\lean{smooth_urysohn}\leanok  If $I$ is a closed interval contained in an open interval $J$, then there exists a smooth function $\Psi: \R \to \R$ with $1_I \leq \Psi \leq 1_J$.
\end{lemma}
%%-/

lemma smooth_urysohn {a b c d:ℝ} (h1: a < b) (h2: b<c) (h3: c < d) : ∃ Ψ:ℝ → ℝ, (∀ n, ContDiff ℝ n Ψ) ∧ (HasCompactSupport Ψ) ∧ Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by
  have := exists_smooth_zero_one_of_isClosed (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici)
    (isClosed_Icc)
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc,
        Set.mem_empty_iff_false, and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  rcases this with ⟨⟨Ψ, hΨcontMDiff⟩, hΨ0, hΨ1, hΨ01⟩
  simp only [Set.EqOn, Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici,
    ContMDiffMap.coeFn_mk, Pi.zero_apply, Set.mem_Icc, Pi.one_apply, and_imp] at *
  use Ψ
  constructor
  · rw [contDiff_all_iff_nat, ←contDiff_top]
    exact ContMDiff.contDiff hΨcontMDiff
  · constructor
    · rw [hasCompactSupport_def]
      apply IsCompact.closure_of_subset (K := Set.Icc a d) isCompact_Icc
      rw [Function.support_subset_iff]
      intro x hx
      contrapose! hx
      simp only [Set.mem_Icc, not_and_or] at hx
      apply hΨ0
      by_contra! h'
      cases' hx <;> linarith
    · constructor
      · intro x
        rw [Set.indicator_apply]
        split_ifs with h
        simp only [Set.mem_Icc, Pi.one_apply] at *
        rw [hΨ1 h.left h.right]
        exact (hΨ01 x).left
      · intro x
        rw [Set.indicator_apply]
        split_ifs with h
        simp at *
        exact (hΨ01 x).right
        rw [hΨ0]
        simp only [Set.mem_Ioo, not_and_or] at h
        by_contra! h'
        cases' h <;> linarith
  done


/-%%
\begin{proof}  \leanok
A standard analysis lemma, which can be proven by convolving $1_K$ with a smooth approximation to the identity for some interval $K$ between $I$ and $J$. Note that we have ``SmoothBumpFunction''s on smooth manifolds in Mathlib, so this shouldn't be too hard...
\end{proof}
%%-/

/-%%
\begin{lemma}[Limiting identity for Schwartz functions]\label{schwarz-id}\lean{limiting_cor_schwartz}\leanok  The previous corollary also holds for functions $\psi$ that are assumed to be in the Schwartz class, as opposed to being $C^2$ and compactly supported.
\end{lemma}
%%-/

lemma limiting_cor_schwartz {ψ: SchwartzMap ℝ ℂ} : Tendsto (fun x : ℝ ↦ ∑' n, f n / n * fourierIntegral ψ (1/(2*π) * log (n/x)) - A * ∫ u in Set.Ici (-log x), fourierIntegral ψ (u / (2*π)) ∂ volume) atTop (nhds 0) := by sorry

/-%%
\begin{proof}
\uses{limiting-cor, smooth-ury}
For any $R>1$, one can use a smooth cutoff function (provided by Lemma \ref{smooth-ury} to write $\psi = \psi_{\leq R} + \psi_{>R}$, where $\psi_{\leq R}$ is $C^2$ (in fact smooth) and compactly supported (on $[-R,R]$), and $\psi_{>R}$ obeys bounds of the form
$$ |\psi_{>R}(t)|, |\psi''_{>R}(t)| \ll R^{-1} / (1 + |t|^2) $$
where the implied constants depend on $\psi$.  By Lemma \ref{decay} we then have
$$ \hat \psi_{>R}(u) \ll R^{-1} / (1+|u|^2).$$
Using this and \eqref{cheby} one can show that
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi_{>R}( \frac{1}{2\pi} \log \frac{n}{x} ), A \int_{-\infty}^\infty \hat \psi_{>R} (\frac{u}{2\pi})\ du \ll R^{-1} $$
(with implied constants also depending on $A$), while from Lemma \ref{limiting-cor} one has
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi_{\leq R}( \frac{1}{2\pi} \log \frac{n}{x} ) = A \int_{-\infty}^\infty \hat \psi_{\leq R} (\frac{u}{2\pi})\ du + o(1).$$
Combining the two estimates and letting $R$ be large, we obtain the claim.
\end{proof}
%%-/

/-%%
\begin{lemma}[Bijectivity of Fourier transform]\label{bij}\lean{fourier_surjection_on_schwartz}\leanok  The Fourier transform is a bijection on the Schwartz class.
\end{lemma}
%%-/

-- just the surjectivity is stated here, as this is all that is needed for the current application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : SchwartzMap ℝ ℂ) : ∃ g : SchwartzMap ℝ ℂ, fourierIntegral g = f := by sorry

/-%%
\begin{proof}
\uses{MellinInversion}
 This is a standard result in Fourier analysis.
It can be proved here by appealing to Mellin inversion, Theorem \ref{MellinInversion}.
In particular, given $f$ in the Schwartz class, let $F : \R_+ \to \C : x \mapsto f(\log x)$ be a function in the ``Mellin space''; then the Mellin transform of $F$ on the imaginary axis $s=it$ is the Fourier transform of $f$.  The Mellin inversion theorem gives Fourier inversion.
\end{proof}
%%-/

/-%%
\begin{corollary}[Smoothed Wiener-Ikehara]\label{WienerIkeharaSmooth}\lean{wiener_ikehara_smooth}\leanok
  If $\Psi: (0,\infty) \to \C$ is smooth and compactly supported away from the origin, then, then
$$ \sum_{n=1}^\infty f(n) \Psi( \frac{n}{x} ) = A x \int_0^\infty \Psi(y)\ dy + o(x)$$
as $u \to \infty$.
\end{corollary}
%%-/

lemma wiener_ikehara_smooth {Ψ: ℝ → ℂ} (hsmooth: ∀ n, ContDiff ℝ n Ψ) (hsupp: HasCompactSupport Ψ) (hplus: closure (Function.support Ψ) ⊆ Set.Ioi (0:ℝ)): Tendsto (fun x : ℝ ↦ (∑' n, f n / n * Ψ (n/x))/x - A * ∫ y in Set.Ioi 0, Ψ y ∂ volume) atTop (nhds 0) := by sorry

/-%%
\begin{proof}
\uses{bij,schwarz-id}
 By Lemma \ref{bij}, we can write
$$ y \Psi(y) = \hat \psi( \frac{1}{2\pi} \log y )$$
for all $y>0$ and some Schwartz function $\psi$.  Making this substitution, the claim is then equivalent after standard manipulations to
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) = A \int_{-\infty}^\infty \hat \psi(\frac{u}{2\pi})\ du + o(1)$$
and the claim follows from Lemma \ref{schwarz-id}.
\end{proof}
%%-/


/-%%
Now we add the hypothesis that $f(n) \geq 0$ for all $n$.

\begin{proposition}[Wiener-Ikehara in an interval]
\label{WienerIkeharaInterval}\lean{WienerIkeharaInterval}\leanok
  For any closed interval $I \subset (0,+\infty)$, we have
  $$ \sum_{n=1}^\infty f(n) 1_I( \frac{n}{x} ) = A x |I|  + o(x).$$
\end{proposition}
%%-/

-- variable (hpos: ∀ n, 0 ≤ f n)

lemma WienerIkeharaInterval (a b:ℝ) (ha: 0 < a) (hb: a < b) : Tendsto (fun x : ℝ ↦ ∑' n, f n / n * (Set.indicator (Set.Icc a b) 1 (n/x))/x - A * (b-a)) atTop (nhds 0) := by
  sorry

/-%%
\begin{proof}
\uses{smooth-ury, WienerIkeharaSmooth}
  Use Lemma \ref{smooth-ury} to bound $1_I$ above and below by smooth compactly supported functions whose integral is close to the measure of $|I|$, and use the non-negativity of $f$.
\end{proof}
%%-/

/-%%
\begin{corollary}[Wiener-Ikehara theorem]\label{WienerIkehara}\lean{WienerIkeharaTheorem'}\leanok
  We have
$$ \sum_{n\leq x} f(n) = A x |I|  + o(x).$$
\end{corollary}
%%-/
open Filter Nat ArithmeticFunction in
/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/
theorem WienerIkeharaTheorem' {f : ArithmeticFunction ℝ} {A : ℝ} {F : ℂ → ℂ} (hf : ∀ n, 0 ≤ f n)
    (hF : Set.EqOn F (fun s ↦ LSeries (fun n => f n) s - A / (s - 1)) {s | 1 < s.re})
    (hF' : ContinuousOn F {s | 1 ≤ s.re}) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum f) / N) atTop (nhds A) := by
  sorry
/-%%
\begin{proof}
\uses{WienerIkeharaInterval}
  Apply the preceding proposition with $I = [\varepsilon,1]$ and then send $\varepsilon$ to zero (using \eqref{cheby} to control the error).
\end{proof}
%%-/

/-%%
\section{Weak PNT}

\begin{theorem}[Weak PNT]\label{WeakPNT}\lean{WeakPNT}\leanok  We have
$$ \sum_{n \leq x} \Lambda(n) = x + o(x).$$
\end{theorem}
%%-/
theorem WeakPNT :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (nhds 1) := by
  sorry
/-%%
\begin{proof}
\uses{WienerIkehara, ChebyshevPsi}
  Already done by Stoll, assuming Wiener-Ikehara.
\end{proof}
%%-/
