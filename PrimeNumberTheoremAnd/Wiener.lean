import EulerProducts.PNT
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.Support
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.FunProp.AEMeasurable
import Mathlib.Tactic.FunProp.Measurable

open Nat Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
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

variable {f : ArithmeticFunction ℂ} (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))

lemma nterm_eq_norm_term {f : ℕ → ℂ} {σ' : ℝ} {n : ℕ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

@[simp]
theorem nnnorm_eq_of_mem_circle (z : circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp)

@[simp]
theorem nnnorm_circle_smul (z : circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

lemma hf_coe1 {σ' : ℝ} (hσ : 1 < σ') : ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
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
lemma first_fourier {ψ : ℝ → ℂ} (hcont: Continuous ψ) (hsupp: HasCompactSupport ψ)
    {x σ':ℝ} (hx: 0 < x) (hσ: 1 < σ') :
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
  have : c ≠ 0 := by simpa [Complex.ext_iff] using fun h ↦ False.elim (by linarith)
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ abs (cexp (c * ↑x)) / abs c) atTop (𝓝 (0 / abs c)) by simpa
    apply Filter.Tendsto.div_const
    suffices Tendsto (. * (1 - σ')) atTop atBot by simpa [Complex.abs_exp, mul_comm (1 - σ')]
    exact Tendsto.atTop_mul_neg_const (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa using second_fourier_aux hx

/-%%
Now let $A \in \C$, and suppose that there is a continuous function $G(s)$ defined on $\mathrm{Re} s \geq 1$ such that $G(s) = F(s) - \frac{A}{s-1}$ whenever $\mathrm{Re} s > 1$.  We also make the Chebyshev-type hypothesis
\begin{equation}\label{cheby}
\sum_{n \leq x} |f(n)| \ll x
\end{equation}
for all $x \geq 1$ (this hypothesis is not strictly necessary, but simplifies the arguments and can be obtained fairly easily in applications).
%%-/

variable {A:ℝ} {G:ℂ → ℂ} (hG: ContinuousOn G {s | 1 ≤ s.re}) (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})

-- variable (hcheby: ∃ C:ℝ, ∀ x:ℕ, ∑ n in Finset.Iic x, |f n| ≤ C * x)

theorem HasCompactSupport.integral_deriv_eq_zero {u : ℝ → ℂ} (h1 : ContDiff ℝ 1 u) (h2 : HasCompactSupport u) :
    ∫ x, deriv u x = 0 := by sorry

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
  · simp only [neg_mul, ofAdd_neg, map_inv, coe_inv_unitSphere, smul_eq_mul]
  · simp only [neg_mul, ofAdd_neg, map_inv, coe_inv_unitSphere, smul_eq_mul]
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
  have l1 : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Complex.norm_eq_abs, Complex.abs_ofReal, abs_eq_self.2 l1.le]
  rw [le_div_iff l1, mul_comm, l2, ← norm_mul, key]
  let f (t : ℝ) := (ψ t - 1 / (4 * π ^ 2) * deriv^[2] ψ t) * 𝐞 [-t * u]
  let g (t : ℝ) := A * (1 + 1 / (4 * π ^ 2)) / (1 + t ^ 2)
  have l5 (t : ℝ) : ‖fourierChar [-t * u]‖ = 1 := by simp
  have l4 (t : ℝ) : ‖f t‖ ≤ g t := by
    simp only [norm_mul, l5, mul_one, mul_add, _root_.add_div]
    refine (norm_sub_le _ _).trans <| _root_.add_le_add (hA t) ?_
    rw [norm_mul]
    convert mul_le_mul_of_nonneg_left (hA' t) (norm_nonneg _) using 1 ; field_simp
  have l5 : Integrable g := by simpa [g, div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul _
  convert norm_integral_le_of_norm_le l5 (eventually_of_forall l4)
  simp_rw [div_eq_mul_inv, integral_mul_left, integral_univ_inv_one_add_sq]
  field_simp [pi_ne_zero] ; ring

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

lemma limiting_fourier_aux (σ' : ℝ) (hσ' : 1 < σ') (hψ : ContDiff ℝ 2 ψ) (hsupp : HasCompactSupport ψ) (hx : 1 ≤ x) :
    ∑' n, term f σ' n * 𝓕 ψ (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 ψ (u / (2 * π)) =
    ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by

  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hψ.continuous hsupp l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier hψ.continuous hsupp l3 hσ'
  have l4 : Integrable fun t ↦ LSeries (⇑f) (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := sorry
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := sorry

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_mul_left, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply eventually_of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  have e2 : ↑σ' + ↑u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  field_simp [e2] ; left ; left
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

lemma limiting_fourier (hψ : ContDiff ℝ 2 ψ) (hsupp : HasCompactSupport ψ) (hx : 1 ≤ x) :
    ∑' n, term f 1 n * 𝓕 ψ (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 ψ (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + I * t)) * (ψ t) * x ^ (I * t) := by

  have key (σ') (hσ' : 1 < σ') := limiting_fourier_aux hf hG' σ' hσ' hψ hsupp hx

  sorry

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
