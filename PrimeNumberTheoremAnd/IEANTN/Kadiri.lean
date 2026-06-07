import Architect
import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta

blueprint_comment /--
\section{An explicit zero-free region for \texorpdfstring{$\zeta$}{zeta}}\label{kadiri-sec}
-/

blueprint_comment /--
In this section we begin a formalisation of the zero-free region for the Riemann zeta function
of Kadiri \cite{Kadiri2005}, who proved that $\zeta(s)$ has no zeros in the region
$$ \Re s \geq 1 - \frac{1}{5.70176 \log |\Im s|}, \qquad |\Im s| \geq 2. $$

The initial target is the explicit formula \cite[(5)]{Kadiri2005} for
$\Re \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n)$ expressed as a sum over the non-trivial
zeros of $\zeta$, where $f$ is a suitable smooth, compactly supported test function and $s$ a
complex parameter.
-/

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log

/-! ## Precursor definitions for Proposition 2.1

`vonMangoldt` (with notation `Λ`), `Complex.Gamma` / `Complex.digamma`, and `riemannZeta`
are all in Mathlib. The set of zeros of `ζ` (and the rect-filtered variant
`riemannZeta.zeroes_rect`) are already defined in `ZetaDefinitions.lean`; the non-trivial zeros
are `riemannZeta.zeroes_rect (Set.Ioo 0 1) Set.univ`. A general Laplace transform is not yet in
Mathlib, so we introduce it ad hoc for the (compactly-supported) Kadiri test functions. -/

/-- Laplace transform of a real-valued function `f`:
`F(s) = ∫₀^∞ e^{-s · t} f(t) dt`. -/
noncomputable def laplaceTransform (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in (.Ioi (0:ℝ)), exp (-s * (t : ℂ)) * (f t : ℂ) ∂volume

/-! ## Helper: finite support of `f ∘ log` -/

private lemma f_log_support_finite {d : ℝ} {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ .Ico 0 d) :
    (Function.support (fun n : ℕ ↦ f (Real.log n))).Finite := by
  apply Set.Finite.subset (Set.finite_Iic ⌊Real.exp d⌋₊)
  intro n hn
  obtain ⟨_, h_lt⟩ := hf_supp (subset_tsupport f hn)
  rw [Set.mem_Iic]
  apply Nat.le_floor
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact_mod_cast (Real.exp_pos d).le
  · rw [← Real.exp_log (Nat.cast_pos.mpr hn0), Real.exp_le_exp]
    exact h_lt.le

/-- Corollary: any pointwise product `g n · f (Real.log n)` (in `ℂ`) is summable. -/
private lemma summable_f_log {d : ℝ} {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ .Ico 0 d)
    (g : ℕ → ℂ) : Summable (fun n : ℕ ↦ g n * ((f (Real.log n) : ℝ) : ℂ)) := by
  apply summable_of_hasFiniteSupport
  refine (f_log_support_finite hf_supp).subset fun n hn ↦ ?_
  simp only [Function.mem_support] at hn ⊢
  exact fun h ↦ hn (by rw [h, Complex.ofReal_zero, mul_zero])

/-! ## Precursor results for Proposition 2.1

Three ingredients of the proof of \ref{kadiri-prop-2-1}: the Hadamard constant $B$
(\ref{kadiri-hadamard-B}), the Hadamard expansion of $-\zeta'/\zeta$
(\ref{kadiri-hadamard-identity}), and the intermediate identity (16) of \cite{Kadiri2005}
obtained by applying the Weil-type explicit formula to a specific test function
(\ref{kadiri-identity-16}). All three are stated below with `sorry` proofs.
\ref{kadiri-prop-2-1} below is stated on the half-plane $\Re s > 1$, which is enough for
Kadiri's downstream zero-free region argument; the harmonic-extension principle that would
lift it to all of $\mathbb{C}$ is no longer needed and is commented out below
(see \ref{kadiri-re-agree-extension}). -/

blueprint_comment /--
The constant $B \in \mathbb{C}$ is the derivative of the degree-one polynomial in the
genus-one Hadamard product for Riemann's entire xi function:
$$ \xi(s) = e^{A + Bs}
     \prod_{\rho \in Z(\zeta)} \left(1 - \tfrac{s}{\rho}\right) e^{s/\rho}. $$
Here we take an explicit xi Hadamard polynomial `P` and use
`Polynomial.eval 0 P.derivative`; there is deliberately no global Lean constant `hadamardB`
until the zero-set reindexing and uniqueness layers identify Kadiri's traditional notation
with that theorem-level data.

The theorem `existsUnique_hadamardB` below is the canonical formulation: it proves that the
candidate value extracted from any no-monomial xi Hadamard polynomial is unique.
-/

@[blueprint
  "kadiri-hadamard-B"
  (title := "Canonical xi Hadamard constant")
  (statement := /-- There is a unique complex number obtained as the derivative at the origin of
  the degree-one polynomial in a no-monomial genus-one Hadamard factorisation of Riemann's entire
  xi function:
  $$ \xi(s) = e^{P(s)}
       \prod_{\rho} \left(1 - \tfrac{s}{\rho}\right)e^{s/\rho},
  \qquad \deg P \le 1. $$
  This unique value is Kadiri's Hadamard constant $B$, stated theorem-theoretically rather than
  introduced by a global choice. -/)
  (proof := /-- Existence is the genus-one Hadamard factorisation for `riemannXi`, with the origin
  monomial removed by `riemannXi 0 \ne 0`.  Uniqueness follows by taking logarithmic derivatives of
  two such factorisations at `0`: the divisor-indexed zero product has the same logarithmic
  derivative in both identities, and `0` is not among the nonzero divisor indices. -/)
  (latexEnv := "lemma")
  (discussion := 1474)]
theorem existsUnique_hadamardB :
    ∃! B : ℂ, ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      (∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      B = Polynomial.eval 0 P.derivative :=
  existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero

/-- Kadiri's Hadamard constant `B`: the canonical value `P'(0)`, common to every degree-≤1
no-monomial xi Hadamard polynomial `P` (well-defined by `existsUnique_hadamardB`).  This replaces
the previously free `B` parameter in `hadamard_identity` / `re_hadamardB_eq`, which made those
statements unprovable as written (true only for this canonical constant). -/
noncomputable def hadamardB : ℂ := existsUnique_hadamardB.exists.choose

/-- The defining property of `hadamardB`: it is `P'(0)` for some degree-≤1 no-monomial xi
Hadamard polynomial `P`. -/
theorem hadamardB_spec :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      (∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      hadamardB = Polynomial.eval 0 P.derivative :=
  existsUnique_hadamardB.exists.choose_spec

/-! ## The zeros of `ξ` are exactly the non-trivial zeros of `ζ`

The imported Hadamard pipeline produces sums indexed by the divisor zeros of Riemann's entire
`ξ` (`Complex.Hadamard.divisorZeroIndex₀ riemannXi`).  Kadiri's explicit formula is phrased over
the non-trivial zeros of `ζ`, i.e.\ `riemannZeta.zeroes_rect (.Ioo 0 1) .univ`.  The classical
fact reconciling the two indexings is that every zero of `ξ` lies in the open critical strip
`0 < \Re s < 1`, and there `ξ(s) = 0 ↔ ζ(s) = 0`.  These lemmas establish that correspondence;
they are the foundation for the (multiplicity-aware) reindexing of the divisor-indexed zero sum
onto `zeroes_rect`. -/

/-- For `\Re s > 0`, the completed zeta function factors as `Λ(s) = Γ_ℝ(s) · ζ(s)`
(valid throughout the right half-plane, not just on `Ω = {\Re s > 1/2}`). -/
private lemma completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos {s : ℂ}
    (hs : 0 < s.re) : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hdef : riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  rw [eq_div_iff hΓ] at hdef
  rw [← hdef]; ring

/-- Inside the open critical strip, `ξ` vanishes exactly where `ζ` does. -/
private lemma riemannXi_eq_zero_iff_riemannZeta_of_mem_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hXi : riemannXi s = (s * (s - 1) * Gammaℝ s / 2) * riemannZeta s := by
    rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
        completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos h0]
    ring
  have hpre : s * (s - 1) * Gammaℝ s / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hΓ) (by norm_num)
  rw [hXi, mul_eq_zero]
  simp [hpre]

/-- `ξ` does not vanish on the closed half-plane `\Re s ≥ 1`. -/
private lemma riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · have h10 : riemannXi (1 : ℂ) = riemannXi 0 := by
      have := riemannXi_one_sub (1 : ℂ); simpa using this.symm
    rw [h10, riemannXi_zero]; norm_num
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num [Complex.zero_re] at hs
    have h0 : (0 : ℝ) < s.re := lt_of_lt_of_le one_pos hs
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
    have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
        completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos h0]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (mul_ne_zero hΓ hζ)) (by norm_num)

/-- `ξ` does not vanish on the closed half-plane `\Re s ≤ 0` (by the functional equation). -/
private lemma riemannXi_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub]
  refine riemannXi_ne_zero_of_one_le_re ?_
  rw [Complex.sub_re, Complex.one_re]; linarith

/-- **ξ–ζ zero correspondence.** Riemann's entire `ξ` vanishes precisely at the non-trivial
zeros of `ζ`: at points of the open critical strip `0 < \Re s < 1` where `ζ` vanishes. -/
theorem riemannXi_eq_zero_iff_mem_nontrivial {s : ℂ} :
    riemannXi s = 0 ↔ (0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0) := by
  constructor
  · intro hXi
    grind only [hadamardB_spec, riemannXi_ne_zero_of_re_le_zero,
      riemannXi_eq_zero_iff_riemannZeta_of_mem_strip, riemannXi_ne_zero_of_one_le_re]
  · rintro ⟨h0, h1, hz⟩
    exact (riemannXi_eq_zero_iff_riemannZeta_of_mem_strip h0 h1).mpr hz

/-- The zero set of `ξ` is exactly `riemannZeta.zeroes_rect (.Ioo 0 1) .univ`. -/
theorem riemannXi_eq_zero_iff_mem_zeroes_rect {s : ℂ} :
    riemannXi s = 0 ↔ s ∈ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) := by
  rw [riemannXi_eq_zero_iff_mem_nontrivial]
  simp only [riemannZeta.zeroes_rect, riemannZeta.zeroes, Set.mem_setOf_eq, Set.mem_Ioo,
    Set.mem_univ, true_and]
  tauto

/-- At any point where `ζ` is analytic (`z ≠ 1`), Kadiri's integer multiplicity
`riemannZeta.order z` coincides with the analytic (ℕ-valued) order of `ζ`.  This identifies the
order-weighting used in `riemannZeta.zeroes_sum` with the analytic multiplicity that the Hadamard
divisor counts.  (The identity holds even in the vacuous `⊤`/identically-zero case, where both
sides are `0`.) -/
theorem riemannZeta_order_eq_analyticOrderNatAt {z : ℂ} (hz : z ≠ 1) :
    riemannZeta.order z = (analyticOrderNatAt riemannZeta z : ℤ) := by
  have han : AnalyticAt ℂ riemannZeta z :=
    riemannZeta_analyticOn_compl_one z (Set.mem_compl_singleton_iff.mpr hz)
  simp only [riemannZeta.order, analyticOrderNatAt]
  cases h : analyticOrderAt riemannZeta z with
  | top => simp [han.meromorphicOrderAt_eq, h]
  | coe n =>
    rw [han.meromorphicOrderAt_eq, h]
    rfl

/-! ### Order matching: `ξ` and `ζ` have equal multiplicity in the strip

The Hadamard divisor of `ξ` counts each zero with its analytic multiplicity
`analyticOrderNatAt riemannXi`.  In the open critical strip this equals the analytic order of
`ζ`, hence (via `riemannZeta_order_eq_analyticOrderNatAt`) Kadiri's `riemannZeta.order`.  This is
the multiplicity half of the divisor→order-weighted reindexing of the Hadamard zero sum. -/

/-- `Γ_ℝ` is analytic on the right half-plane `0 < Re s`: its reciprocal is entire
(`differentiable_Gammaℝ_inv`) and nonvanishing there. -/
private lemma analyticAt_Gammaℝ_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Gammaℝ z := by
  have hinv : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) z :=
    differentiable_Gammaℝ_inv.analyticAt z
  have hne : (Gammaℝ z)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz)
  have h2 : AnalyticAt ℂ (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) z := hinv.inv hne
  have heq : (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) = Gammaℝ := by funext s; rw [inv_inv]
  rwa [heq] at h2

/-- In the open critical strip, the analytic (ℕ-valued) order of `ξ` equals that of `ζ`:
near such a point `ξ = (s(s-1)/2 · Γ_ℝ) · ζ`, with the prefactor an analytic non-vanishing
unit (so it contributes order `0`). -/
theorem analyticOrderNatAt_riemannXi_eq_riemannZeta {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderNatAt riemannXi z = analyticOrderNatAt riemannZeta z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at h0
  have hz1 : z ≠ 1 := by rintro rfl; simp at h1
  have hΓ_an : AnalyticAt ℂ Gammaℝ z := analyticAt_Gammaℝ_of_re_pos h0
  have hpoly : Differentiable ℂ (fun w : ℂ => w * (w - 1) / 2) := by fun_prop
  have hpoly_an : AnalyticAt ℂ (fun w : ℂ => w * (w - 1) / 2) z := hpoly.analyticAt z
  have hg_an : AnalyticAt ℂ (fun w : ℂ => w * (w - 1) / 2 * Gammaℝ w) z := hpoly_an.mul hΓ_an
  have hζ_an : AnalyticAt ℂ riemannZeta z :=
    riemannZeta_analyticOn_compl_one z (Set.mem_compl_singleton_iff.mpr hz1)
  have hEq : riemannXi =ᶠ[nhds z] (fun w : ℂ => w * (w - 1) / 2 * Gammaℝ w) * riemannZeta := by
    have hV : {w : ℂ | 0 < w.re ∧ w.re < 1} ∈ nhds z :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨h0, h1⟩
    filter_upwards [hV] with w hw
    obtain ⟨hw0, hw1⟩ := hw
    have hwne0 : w ≠ 0 := by rintro rfl; simp at hw0
    have hwne1 : w ≠ 1 := by rintro rfl; simp at hw1
    simp only [Pi.mul_apply]
    rw [riemannXi_eq_mul_completedRiemannZeta hwne0 hwne1,
        completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos hw0]
    ring
  have hg_ne : (fun w : ℂ => w * (w - 1) / 2 * Gammaℝ w) z ≠ 0 := by
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero hz0 (sub_ne_zero.mpr hz1)) (by norm_num))
      (Gammaℝ_ne_zero_of_re_pos h0)
  dsimp only [analyticOrderNatAt]
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul hg_an hζ_an,
      hg_an.analyticOrderAt_eq_zero.mpr hg_ne, zero_add]

/-- In the open critical strip, the analytic multiplicity of `ξ` (what the Hadamard divisor
counts) is exactly Kadiri's integer order weight `riemannZeta.order`.  This is the per-zero
weight identity underlying the divisor→`riemannZeta.zeroes_sum` reindexing. -/
theorem analyticOrderNatAt_riemannXi_eq_order {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    (analyticOrderNatAt riemannXi z : ℤ) = riemannZeta.order z := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at h1
  rw [analyticOrderNatAt_riemannXi_eq_riemannZeta h0 h1,
      riemannZeta_order_eq_analyticOrderNatAt hz1]

@[blueprint
  "kadiri-hadamard-identity"
  (title := "Hadamard expansion of $-\\zeta'/\\zeta$ (after equation (16))")
  (statement := /-- For every $s \in \mathbb{C}$ that is neither $1$ nor a non-trivial zero
  of $\zeta$,
  $$ -\frac{\zeta'}{\zeta}(s) = -B - \tfrac{1}{2} \log \pi + \frac{1}{s - 1}
       + \tfrac{1}{2} \frac{\Gamma'}{\Gamma}\!\left(\tfrac{s}{2} + 1\right)
       - \sum_{\rho \in Z(\zeta)} \left(\frac{1}{\rho} + \frac{1}{s - \rho}\right), $$
  where $B$ is the xi Hadamard constant (\ref{kadiri-hadamard-B}). This is obtained by
  differentiating the genus-one Hadamard factorisation of `riemannXi` and then using
  $\xi(s) = (s - 1)\pi^{-s/2}\Gamma(s/2+1)\zeta(s)$ on $\Re s > 1$
  (\cite[Chapter 12]{Davenport2000}). -/)
  (proof := /-- Differentiate the xi Hadamard product (\ref{kadiri-hadamard-B})
  logarithmically; the derivative of the degree-one Hadamard polynomial is the constant
  $B$. The $\tfrac{1}{s-1}$ term comes from the pole factor in
  $\xi(s) = (s - 1)\pi^{-s/2}\Gamma(s/2+1)\zeta(s)$, and the
  $\tfrac{1}{2} \Gamma'/\Gamma$ term comes from the shifted gamma factor. The Lean bridge
  is through `riemannXi`, not through a Hadamard product for $(s - 1)\zeta(s)`. -/)
  (latexEnv := "lemma")
  (discussion := 1474)]
theorem hadamard_identity (B : ℂ) (s : ℂ) (hs1 : s ≠ 1)
    (hsZ : s ∉ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ)) :
    -deriv riemannZeta s / riemannZeta s =
      -B - (1 / 2 : ℂ) * Real.log Real.pi + 1 / (s - 1) +
      (1 / 2 : ℂ) * digamma (s / 2 + 1) -
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (s - ρ.val)) := by
  sorry

/-- Proven xi-substrate version of the Hadamard log-derivative bridge, using an explicit
degree-one xi Hadamard polynomial and its derivative at the origin.  Bridge for the blueprint
statement `hadamard_identity`; translating the divisor-indexed xi zeros
to `riemannZeta.zeroes_rect` is the remaining zero-set reindexing layer. -/
theorem neg_zeta_logDeriv_eq_of_riemannXi_hadamardPolynomial
    {P : Polynomial ℂ}
    (hdeg : P.degree ≤ 1)
    (hfac : ∀ z : ℂ, Complex.riemannXi z =
      Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi (Set.univ : Set ℂ) z)
    (s : ℂ)
    (hs : 1 < s.re)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    -deriv riemannZeta s / riemannZeta s =
      -Polynomial.eval 0 P.derivative
      - ∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p)
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  have h :=
    neg_zeta_logDeriv_eq_of_riemannXi_polynomial_hadamard
      (P := P) s hs hΓdiff hΓ hfac hz
  rw [Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hdeg s] at h
  exact h

@[blueprint
  "kadiri-thm-3-1-q1"
  (title := "Theorem 3.1 of \\cite{Kadiri2005}, case $q = 1$, $\\chi$ trivial")
  (statement := /-- Let $\varphi \colon \mathbb{R} \to \mathbb{C}$ be $C^1$ and suppose there
  exists $b > 0$ such that both $\varphi(x) e^{x/2}$ and $\varphi'(x) e^{x/2}$ are
  $O(e^{-(1/2 + b)|x|})$ as $|x| \to \infty$. Define the Laplace transform
  $\Phi(z) := \int_0^{\infty} \varphi(y) e^{-zy}\, dy$. Then
  $$ \sum_{n \geq 1} \Lambda(n)\, \varphi(\log n)
     = \Phi(-1) + \Phi(0) - \sum_{\rho \in Z(\zeta)} \Phi(-\rho)
       - \varphi(0)\, \log \pi
       + \sum_{n \geq 1} \tfrac{\Lambda(n)}{n}\, \varphi(-\log n)
       + \tfrac{1}{2 \pi i} \int_{1/2 - i\infty}^{1/2 + i\infty}
           \Re \tfrac{\Gamma'}{\Gamma}\!\left( \tfrac{z}{2} \right) \Phi(-z)\, dz, $$
  where the $\rho$-sum runs over the non-trivial zeros of $\zeta$.

  This is the $q = 1$, $\chi$ trivial case of the Weil-type explicit formula of
  \cite[Theorem 3.1]{Kadiri2005}. The $\Phi(-1)$ term comes from the simple pole of $\zeta$
  at $z = 1$ (and is absent for non-trivial $\chi$); the $\varphi(0)\log\pi$ term and the
  $\Gamma$-integral come from the gamma factor in the functional equation of $\zeta$; the
  $\sum_n \tfrac{\Lambda(n)}{n}\varphi(-\log n)$ term is the contribution from the reflected
  ($z \leftrightarrow 1 - z$) Dirichlet series. -/)
  (proof := /-- Classical Weil-style argument. Write the LHS as a Mellin contour integral
  $\tfrac{1}{2\pi i} \int_{(c)} (-\zeta'/\zeta)(z)\, \Phi(-z)\, dz$ for some $c > 1$, using
  the Dirichlet series $-\zeta'/\zeta(z) = \sum_n \Lambda(n) n^{-z}$ on $\Re z > 1$ together
  with the Mellin inversion $\varphi(\log n) = \tfrac{1}{2\pi i} \int_{(c)} n^z \Phi(-z)\, dz$.
  Contour-shift to $\Re z = -1 - a$ for some $0 < a < b$, picking up residues at: $z = 1$
  (the simple pole of $\zeta$, contributing $\Phi(-1)$); $z = 0$ (contributing $\Phi(0)$ via
  the Laurent expansion of $-\zeta'/\zeta$ at $0$); and each non-trivial zero $z = \rho$
  (contributing $-\Phi(-\rho)$). Then use the functional equation
  $\zeta(z) \Gamma(z/2) \pi^{-z/2} = \zeta(1-z) \Gamma((1-z)/2) \pi^{-(1-z)/2}$
  to rewrite the integral on $\Re z = -1 - a$ as the reflected Dirichlet series
  $\sum_n \tfrac{\Lambda(n)}{n} \varphi(-\log n)$ plus the $\Gamma'/\Gamma$ contour integral
  on $\Re z = 1/2$, with the $\pi^{z/2}$ factor producing $-\varphi(0)\log\pi$. To be
  formalised. -/)
  (latexEnv := "theorem")]
theorem kadiri_thm_3_1_q1 {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    let Φ : ℂ → ℂ := fun z ↦ ∫ y in (.Ioi (0 : ℝ)), φ y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      Φ (-1) + Φ 0
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ), Φ (-ρ.val)
        - φ 0 * ((Real.log Real.pi : ℝ) : ℂ)
        + ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ) * I)) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I)) := by
  sorry

/-! ## Machinery for deriving (16) from Theorem 3.1

Three sublemmas (\ref{kadiri-laplace-ibp}, \ref{kadiri-test-fn-contDiff} +
\ref{kadiri-test-fn-decay}, \ref{kadiri-test-fn-laplace}) reduce the proof of
\ref{kadiri-identity-16} (given \ref{kadiri-thm-3-1-q1}) to algebraic glue. The first one
(\ref{kadiri-laplace-ibp}) is also a precursor for \ref{kadiri-laplace-re-decay}. -/

@[blueprint
  "kadiri-laplace-ibp"
  (title := "Two-integration-by-parts form of the Laplace transform")
  (statement := /-- For $f$ satisfying the hypotheses $(H_1)$ of \ref{kadiri-prop-2-1}: for
  every $w \in \mathbb{C}$ with $w \neq 0$,
  $$ F(w) = \frac{f(0)}{w} + \frac{F_2(w)}{w^2}, $$
  where $F_2(w) := \int_0^d e^{-wy} f''(y)\, dy$ is the Laplace transform of $f''$. -/)
  (proof := /-- Two successive integrations by parts on
  $F(w) = \int_0^d e^{-wy} f(y)\, dy$. The first gives
  $F(w) = \tfrac{f(0)}{w} - \tfrac{f(d) e^{-w d}}{w}
        + \tfrac{1}{w} \int_0^d e^{-wy} f'(y)\, dy$;
  using $f(d) = 0$ from $(H_1)$ kills the boundary term, leaving
  $\tfrac{f(0)}{w} + \tfrac{1}{w} \int_0^d e^{-wy} f'(y)\, dy$. The second IBP on the
  remaining integral gives
  $\tfrac{1}{w} \int_0^d e^{-wy} f'(y)\, dy
   = \tfrac{f'(0)}{w^2} - \tfrac{f'(d) e^{-w d}}{w^2}
     + \tfrac{1}{w^2} \int_0^d e^{-wy} f''(y)\, dy$;
  using $f'(0) = f'(d) = 0$ from $(H_1)$ kills both boundary terms, leaving
  $F_2(w)/w^2$. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1483)]
theorem laplaceTransform_ibp {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (_hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (_hf_supp : tsupport f ⊆ .Ico 0 d)
    (_hf_d : f d = 0)
    (_hf_deriv_0 : deriv f 0 = 0)
    (_hf_deriv_d : deriv f d = 0)
    {w : ℂ} (_hw : w ≠ 0) :
    laplaceTransform f w =
      (f 0 : ℂ) / w + laplaceTransform (fun u ↦ deriv (deriv f) u) w / w ^ 2 := by
  sorry

@[blueprint
  "kadiri-test-fn"
  (title := "The Kadiri test function")
  (statement := /-- The $s$-parametrised test function
  $\varphi(y;\, s) := (f(0) - f(y))\, e^{-y s}\, \mathbf{1}_{y \geq 0}$ used to derive
  \ref{kadiri-identity-16} from \ref{kadiri-thm-3-1-q1}. -/)
  (latexEnv := "definition")
  (discussion := 1484)]
noncomputable def kadiriTestFn (f : ℝ → ℝ) (s : ℂ) : ℝ → ℂ := fun y ↦
  if 0 ≤ y then ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)) else 0

@[blueprint
  "kadiri-test-fn-contDiff"
  (title := "The Kadiri test function is $C^1$")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and any
  $s \in \mathbb{C}$, the Kadiri test function $\mathrm{kadiriTestFn}\, f\, s$
  (\ref{kadiri-test-fn}) is $C^1$ on $\mathbb{R}$. -/)
  (proof := /-- The function $\varphi(\cdot;\, s)$ is smooth on each of the three open pieces:
  on $(-\infty, 0)$ it is $\equiv 0$; on $(0, d)$ it equals $(f(0) - f(y)) e^{-sy}$, $C^2$
  from $f \in C^2$ on $[0, d]$; on $(d, \infty)$ it equals $f(0) e^{-sy}$ (using
  $\mathrm{supp}\, f \subseteq [0, d)$), smooth. At the seam $y = 0$: the right-limits of
  $\varphi$ and $\varphi'$ are $(f(0) - f(0)) \cdot 1 = 0$ and
  $-f'(0) - s(f(0) - f(0)) = 0$ respectively (using $f'(0) = 0$ from $(H_1)$), matching the
  left-limits $0$. At the seam $y = d$: the left-limits of $\varphi$ and $\varphi'$ are
  $(f(0) - f(d)) e^{-sd} = f(0) e^{-sd}$ (using $f(d) = 0$) and
  $-f'(d) e^{-sd} - s(f(0) - f(d)) e^{-sd} = -s f(0) e^{-sd}$ (using $f(d) = f'(d) = 0$),
  matching the right-limits. Hence $\varphi$ is $C^1$ globally. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1484)]
theorem kadiriTestFn_contDiff {d : ℝ} (_hd : 0 < d) {f : ℝ → ℝ}
    (_hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (_hf_supp : tsupport f ⊆ .Ico 0 d)
    (_hf_d : f d = 0)
    (_hf_deriv_0 : deriv f 0 = 0)
    (_hf_deriv_d : deriv f d = 0)
    (_s : ℂ) :
    ContDiff ℝ 1 (kadiriTestFn f _s) := by
  sorry

@[blueprint
  "kadiri-test-fn-decay"
  (title := "Decay condition (B) for the Kadiri test function")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and
  $s \in \mathbb{C}$ with $\Re s > 1$, the Kadiri test function
  $\varphi(\cdot;\, s) = \mathrm{kadiriTestFn}\, f\, s$ (\ref{kadiri-test-fn}) satisfies
  decay condition (B) of \ref{kadiri-thm-3-1-q1}: there exists $b > 0$
  (any $0 < b < \Re s - 1$ works) such that both $\varphi(x;\, s) e^{x/2}$ and
  $\varphi'(x;\, s) e^{x/2}$ are $O(e^{-(1/2 + b)|x|})$ as $|x| \to \infty$. -/)
  (proof := /-- For $x < 0$ both $\varphi(x;\, s)$ and $\varphi'(x;\, s)$ are identically
  $0$, so the bound holds trivially at $-\infty$. For $x > d$ (above the support of $f$),
  $\varphi(x;\, s) = f(0)\, e^{-x s}$ and $\varphi'(x;\, s) = -s\, f(0)\, e^{-x s}$, so
  $|\varphi(x;\, s) e^{x/2}| = |f(0)|\, e^{-x(\Re s - 1/2)}$ and similarly for the
  derivative with an extra factor $|s|$; both are $O(e^{-(1/2 + b) x})$ as $x \to +\infty$
  precisely when $\Re s - 1/2 \geq 1/2 + b$, i.e.\ $b \leq \Re s - 1$. Take any
  $0 < b < \Re s - 1$. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1485)]
theorem kadiriTestFn_decay {d : ℝ} {f : ℝ → ℝ} (_hf_supp : tsupport f ⊆ .Ico 0 d)
    {s : ℂ} (_hs : 1 < s.re) :
    ∃ b > 0,
      ((fun x : ℝ ↦ kadiriTestFn f s x * exp ((x : ℂ) / 2))
          =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) ∧
      ((fun x : ℝ ↦ deriv (kadiriTestFn f s) x * exp ((x : ℂ) / 2))
          =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) := by
  sorry

@[blueprint
  "kadiri-test-fn-laplace"
  (title := "Laplace transform of the Kadiri test function (shift identity)")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and
  $s, z \in \mathbb{C}$ with $\Re(s + z) > 0$,
  $$ \int_0^{\infty} \varphi(y;\, s)\, e^{-z y}\, dy
     = \frac{f(0)}{s + z} - F(s + z), $$
  where $\varphi(\cdot;\, s) = \mathrm{kadiriTestFn}\, f\, s$ (\ref{kadiri-test-fn}) and
  $F$ is the file's `laplaceTransform` of $f$. -/)
  (proof := /-- Direct expansion of the integrand on $y > 0$:
  $\varphi(y;\, s) e^{-zy} = (f(0) - f(y)) e^{-(s+z) y}$. Split the integral:
  $\int_0^{\infty} f(0)\, e^{-(s+z) y}\, dy = f(0)/(s + z)$ converges by
  $\Re(s + z) > 0$; $\int_0^{\infty} f(y)\, e^{-(s+z) y}\, dy = F(s + z)$ unconditionally
  since $\mathrm{supp}\, f \subseteq [0, d]$ makes the integral compactly-supported. To be
  formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1486)]
theorem kadiriTestFn_laplaceTransform {d : ℝ} (_hd : 0 < d) {f : ℝ → ℝ}
    (_hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (_hf_supp : tsupport f ⊆ .Ico 0 d)
    (s z : ℂ) (_hsz : 0 < (s + z).re) :
    (∫ y in (.Ioi (0 : ℝ)), kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s + z) - laplaceTransform f (s + z) := by
  sorry

/-! ### Evaluation helpers for `kadiriTestFn`

Pointwise unfoldings of \ref{kadiri-test-fn} used inside the proof of
\ref{kadiri-identity-16} to dispatch the vanishing terms ($\varphi(0;\, s) = 0$,
$\varphi(-\log n;\, s) = 0$) and to rewrite $\varphi(\log n;\, s)$ as
$(f(0) - f(\log n)) / n^s$. Trivial unfoldings of the definition; left non-blueprinted. -/

@[simp]
theorem kadiriTestFn_zero (f : ℝ → ℝ) (s : ℂ) : kadiriTestFn f s 0 = 0 := by
  simp [kadiriTestFn]

theorem kadiriTestFn_neg_log (f : ℝ → ℝ) (s : ℂ) (n : ℕ) :
    kadiriTestFn f s (-Real.log n) = 0 := by
  dsimp only [kadiriTestFn]
  split
  · next h =>
    have hz : Real.log (n : ℝ) = 0 :=
      le_antisymm (by linarith) (Real.log_natCast_nonneg n)
    simp [hz]
  · rfl

theorem kadiriTestFn_log (f : ℝ → ℝ) (s : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    kadiriTestFn f s (Real.log n) =
      ((f 0 : ℂ) - (f (Real.log n) : ℂ)) / (n : ℂ) ^ s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcpow : (n : ℂ) ^ s = Complex.exp ((Real.log (n : ℝ) : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.ofReal_log (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
  have hexp : Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) = ((n : ℂ) ^ s)⁻¹ := by
    rw [hcpow, ← Complex.exp_neg]
    congr 1
    ring
  dsimp only [kadiriTestFn]
  rw [if_pos (Real.log_natCast_nonneg n), hexp, div_eq_mul_inv]

/-! ### Auxiliary: complex (pre-`Re`) form of equation (16)

We split the proof of \ref{kadiri-identity-16} in two. The auxiliary `identity_16_complex`
below carries the mathematical content — apply \ref{kadiri-thm-3-1-q1} to the Kadiri test
function, substitute the four $\Phi$-values via \ref{kadiri-test-fn-laplace}, rewrite the
$F$-occurrences at $w = s$ and $w = s - z$ (inside the contour integral) into the
$F_2$-form via \ref{kadiri-laplace-ibp}, and algebraically rearrange. Then `identity_16`
itself just takes real parts of both sides and distributes $\Re$ over $+$, $-$, and the
$\rho$-tsum. -/

private theorem identity_16_complex {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : deriv f 0 = 0)
    (hf_deriv_d : deriv f d = 0)
    (hf_deriv2_d : deriv (deriv f) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)) =
      (f 0 : ℂ) * ((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s)
                    - 1 / (s - 1)
                    + ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
                        1 / (s - ρ.val))
      + laplaceTransform f (s - 1)
      - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          laplaceTransform f (s - ρ.val)
      + ((1 / (2 * (Real.pi : ℂ) * I)) *
          (∫ t : ℝ,
            ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
              laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I))
              / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
          + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2) := by
  sorry

@[blueprint
  "kadiri-identity-16"
  (title := "Equation (16) of \\cite{Kadiri2005}: intermediate identity")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}: for every
  $s \in \mathbb{C}$ with $\Re s > 1$,
  $$ \Re \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n)
   = f(0) \Re \Bigl( \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} - \frac{1}{s - 1}
                     + \sum_{\rho \in Z(\zeta)} \frac{1}{s - \rho} \Bigr)
   + \Re F(s - 1) - \sum_{\rho \in Z(\zeta)} \Re F(s - \rho)
   + \Re \Bigl( \frac{1}{2\pi i} \int_{1/2 - i\infty}^{1/2 + i\infty}
       \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{z}{2}\right) \frac{F_2(s - z)}{(s - z)^2}\, dz
       + \frac{F_2(s)}{s^2} \Bigr). $$
  This is the form obtained from \ref{kadiri-thm-3-1-q1} (the Weil-type explicit formula,
  specialized to $q = 1$, $\chi$ trivial) by taking the parametrised test function
  $\varphi(y) = (f(0) - f(y)) e^{-y s} \mathbf{1}_{y \geq 0}$. The restriction $\Re s > 1$
  is where the Dirichlet series for $-\zeta'/\zeta(s)$ converges absolutely and the
  $\sum_\rho 1/(s - \rho)$ regularization makes sense; this is also the range used in
  Kadiri's downstream zero-free region argument, so we do not extend further. -/)
  (proof := /-- Apply \ref{kadiri-thm-3-1-q1} to the Kadiri test function
  $\varphi(\cdot;\, s) = \mathrm{kadiriTestFn}\, f\, s$ (\ref{kadiri-test-fn}); its hypotheses
  are discharged by \ref{kadiri-test-fn-contDiff} ($\varphi$ is $C^1$) and
  \ref{kadiri-test-fn-decay} (decay (B) with any $0 < b < \Re s - 1$, requiring
  $\Re s > 1$). The Laplace transform of $\varphi$ is computed by
  \ref{kadiri-test-fn-laplace}: $\Phi(z;\, s) = f(0)/(s+z) - F(s+z)$. In particular
  $\Phi(-1) = f(0)/(s-1) - F(s-1)$, $\Phi(-\rho) = f(0)/(s-\rho) - F(s-\rho)$,
  $\Phi(0) = f(0)/s - F(s)$, and $\Phi(-z) = f(0)/(s-z) - F(s-z)$ at $z = 1/2 + it$.
  Rewriting $F(s) = f(0)/s + F_2(s)/s^2$ via \ref{kadiri-laplace-ibp} (and likewise at
  $w = s - z$) collapses $\Phi(0) = -F_2(s)/s^2$ and $\Phi(-z) = -F_2(s-z)/(s-z)^2$ used
  inside the contour integral. Three terms of \ref{kadiri-thm-3-1-q1}'s conclusion vanish
  for this $\varphi$: $\varphi(0;\, s) = 0$ kills the $\varphi(0) \log \pi$ term, and
  $\varphi(-\log n;\, s) = 0$ for every $n \geq 1$ kills the reflected discrete sum.
  Unfolding the LHS as
  $\sum_n \Lambda(n) \varphi(\log n;\, s) = f(0) \sum_n \Lambda(n)/n^s
                                            - \sum_n \Lambda(n) f(\log n)/n^s$, solving for
  $\sum_n \Lambda(n) f(\log n)/n^s$, substituting the $\Phi$ values, and taking real parts,
  yields the right-hand side of (16). To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1488)]
theorem identity_16 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : deriv f 0 = 0)
    (hf_deriv_d : deriv f d = 0)
    (hf_deriv2_d : deriv (deriv f) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)).re =
      f 0 * ((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s)
              - 1 / (s - 1)
              + ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
                  1 / (s - ρ.val)).re
        + (laplaceTransform f (s - 1)).re
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
            (laplaceTransform f (s - ρ.val)).re
        + ((1 / (2 * (Real.pi : ℂ) * I)) *
            (∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                laplaceTransform (fun u ↦ deriv (deriv f) u)
                  (s - (1 / 2 + (t : ℂ) * I))
                / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
            + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2).re := by
  -- Reduce to the complex (pre-`Re`) form, then distribute `Re` over `+`, `-`, the
  -- $(f(0) : \mathbb{C}) \cdot ?$ factor (since $f(0) \in \mathbb{R}$), and the
  -- $\rho$-tsum (via `Complex.reCLM`).
  have hcomplex := identity_16_complex hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d
    hf_deriv2_d hs
  -- Complex summability of `∑ρ F(s − ρ)`. Pending: derive from `summable_lap_re_at_zeros`
  -- together with an analogous Im-summability — would need a `laplaceTransform_im_decay`
  -- lemma paralleling `kadiri-laplace-re-decay`.
  have hSumm : Summable
      (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
        laplaceTransform f (s - ρ.val)) := by
    sorry
  -- Commute the ρ-tsum with `.re` via the continuous linear map `Complex.reCLM`.
  have htsum_re :
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          laplaceTransform f (s - ρ.val)).re =
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (laplaceTransform f (s - ρ.val)).re := by
    simpa using ContinuousLinearMap.map_tsum Complex.reCLM hSumm
  -- Substitute the complex form and distribute `.re`.
  rw [hcomplex]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
             Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, htsum_re]

-- Kept (commented out) as a stub for potential future use. The current Kadiri chain
-- (`identity_16`, `re_inner_eq`, `prop_2_1`, `eq_5`) is stated and proved on the
-- half-plane $\Re s > 1$, which is enough for the downstream zero-free region argument
-- and avoids the meromorphic-extension subtlety: the RHS of `prop_2_1` has poles at the
-- trivial zeros $s = -2, -4, \ldots$ (digamma factor) and at $s = 1$ (the $1/(s-1)$
-- term), so the "entire" hypothesis below cannot be discharged directly in those
-- formulations.
/-
@[blueprint
  "kadiri-re-agree-extension"
  (title := "Real-part agreement on a half-plane extends to $\\mathbb{C}$")
  (statement := /-- If $F, G \colon \mathbb{C} \to \mathbb{C}$ are entire and
  $\Re F(s) = \Re G(s)$ for every $s$ with $\Re s > 1$, then $\Re F(s) = \Re G(s)$ for all
  $s \in \mathbb{C}$. -/)
  (proof := /-- Let $H = F - G$. Then $H$ is entire and $\Re H \equiv 0$ on the open
  half-plane $\{\Re s > 1\}$. The function $\Re H$ is harmonic on $\mathbb{C}$, and
  vanishes on a non-empty open set; by the identity principle for real-analytic (or
  harmonic) functions on the connected domain $\mathbb{C}$, $\Re H \equiv 0$ everywhere.
  (Equivalently: $H$ is locally constant on the half-plane via Cauchy-Riemann, hence
  $H$ is a purely imaginary constant, hence $\Re H = 0$ everywhere.) -/)
  (latexEnv := "lemma")
  (discussion := 1475)]
theorem re_eq_of_entire_agree_on_halfplane {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hagree : ∀ s : ℂ, 1 < s.re → (F s).re = (G s).re) :
    ∀ s : ℂ, (F s).re = (G s).re := by
  sorry
-/

/-! ## Auxiliaries glueing the three precursors to Proposition 2.1

Two facts not in the three precursors above are needed: \ref{kadiri-re-hadamardB-eq} (the
closed form $\Re B = -\sum_\rho \Re(1/\rho)$, conjectured from the Hadamard product) and
\ref{kadiri-summable-lap-at-zeros} (summability of the residue sum at the non-trivial zeros).
They combine with \ref{kadiri-hadamard-identity} to give \ref{kadiri-re-inner-eq}
(collapsing the $f(0)$-coefficient of equation (16) into the $T_1$ form on the half-plane
$\Re s > 1$). After that, \ref{kadiri-prop-2-1} is a two-line `rw` chain combining
\ref{kadiri-identity-16} with \ref{kadiri-re-inner-eq} on the same half-plane.
All three are stated below with `sorry` proofs. The summability auxiliary in turn rests on
two further inputs, also stated below: Backlund's explicit Riemann--von Mangoldt bound
(\ref{kadiri-backlund-bound}), giving $N(T) \ll T \log T$, and the $1/y^2$ decay of $\Re F$
on vertical strips (\ref{kadiri-laplace-re-decay}), giving the per-term bound
$|\Re F(s - \rho)| \ll 1/\gamma^2$. -/

@[blueprint
  "kadiri-re-hadamardB-eq"
  (title := "Real part of the Hadamard constant")
  (statement := /-- $\Re B = -\sum_{\rho \in Z(\zeta)} \Re \tfrac{1}{\rho}$, where $B$ is the
  Hadamard constant (\ref{kadiri-hadamard-B}). -/)
  (proof := /-- Subtract $\tfrac{1}{s-1}$ from \ref{kadiri-hadamard-identity}, take $s \to 1$
  using the Laurent expansion $-\zeta'/\zeta(s) = \tfrac{1}{s-1} - \gamma + O(s - 1)$ near $s = 1$
  and the value $\Gamma'/\Gamma(3/2)$, then symmetrise the resulting sum
  $\sum_\rho (1/\rho + 1/(1-\rho))$ using $\rho \leftrightarrow 1 - \bar\rho$ to relate
  $\sum_\rho 1/\rho$ to $\Re B$. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1476)]
theorem re_hadamardB_eq (B : ℂ) :
    B.re =
    -∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ)).re := by
  sorry

@[blueprint
  "kadiri-backlund-bound"
  (title := "Backlund's explicit Riemann--von Mangoldt bound")
  (statement := /-- Backlund's explicit zero-counting bound (\cite{Backlund1918}, cited in
  \cite[page 24]{Kadiri2005}): the constants $(b_1, b_2, b_3) = (0.137, 0.443, 6.1)$ satisfy
  the project's \ref{Riemann-von-Mangoldt-estimate}, i.e.\ for every $T \geq 2$,
  $$ \bigl| N(T) - \bigl( \tfrac{T}{2\pi} \log \tfrac{T}{2\pi} - \tfrac{T}{2\pi}
                          + \tfrac{7}{8} \bigr) \bigr|
     \leq 0.137 \log T + 0.443 \log \log T + 6.1. $$
  Backlund's original (\cite[page 24]{Kadiri2005}) bounds the difference from the simpler
  main term $\tfrac{T}{2\pi} \log \tfrac{T}{2\pi e}$ by
  $0.137 \log T + 0.443 \log \log T + 5.225$; absorbing the $\tfrac{7}{8}$ offset between the
  two main-term conventions gives the project-form constant $5.225 + \tfrac{7}{8} = 6.1$.
  For $T \in [2, t_1)$ (below the first non-trivial zero $t_1 \approx 14.1347$) the LHS reduces
  to the main-term absolute value, which is well within the (loose) RHS bound. -/)
  (proof := /-- Classical Backlund 1918 (\cite{Backlund1918}). The
  \cite[Theorem of Backlund]{Backlund1918} variant is the form cited at
  \cite[page 24]{Kadiri2005} as the starting point for the explicit estimates
  $N_1(u), N_2(u)$ of (34)-(35) there. To be formalised. -/)
  (latexEnv := "lemma")]
theorem backlund_bound : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1 := by
  sorry

@[blueprint
  "kadiri-laplace-re-decay"
  (title := "$1/y^2$ decay of $\\Re F$ on a vertical strip")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}: for every closed vertical
  strip $\sigma_0 \leq \Re s \leq \sigma_1$ there is a constant
  $C = C(\sigma_0, \sigma_1, f)$ such that for every $s \in \mathbb{C}$ with
  $\sigma_0 \leq \Re s \leq \sigma_1$ and $|\Im s| \geq 1$,
  $$ |\Re F(s)| \leq \frac{C}{(\Im s)^2}. $$
  Note that this is sharper than the elementary $|F(s)| = O(1/|s|)$ from a single integration
  by parts: the cancellation $\Re(1/s) = \sigma/(\sigma^2 + y^2) = O(1/y^2)$ for bounded
  $\sigma$ saves one power of $|y|$ once the real part is taken. -/)
  (proof := /-- Apply \ref{kadiri-laplace-ibp} to get
  $F(s) = f(0)/s + F_2(s)/s^2$, where $F_2$ is the Laplace transform of $f''$. Taking real
  parts at $s = \sigma + iy$:
  $\Re F(s) = \dfrac{f(0)\, \sigma}{\sigma^2 + y^2}
              + \Re \dfrac{F_2(s)}{s^2}$. The first summand is bounded by
  $|f(0)| \cdot \max(|\sigma_0|, |\sigma_1|) / y^2$; the second by absolute values is at most
  $\dfrac{1}{y^2} \cdot d \cdot \max(1, e^{-\sigma_0 d}) \cdot \|f''\|_\infty$ (using
  $\mathrm{supp}\, f'' \subseteq [0, d]$). Both depend only on $\sigma_0, \sigma_1, d, f$;
  take $C$ to be their sum. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1487)]
theorem laplaceTransform_re_decay {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : deriv f 0 = 0)
    (hf_deriv_d : deriv f d = 0)
    (hf_deriv2_d : deriv (deriv f) d = 0)
    (σ₀ σ₁ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 1 ≤ |s.im| →
      |(laplaceTransform f s).re| ≤ C / s.im ^ 2 := by
  sorry

@[blueprint
  "kadiri-summable-lap-at-zeros"
  (title := "Summability of $\\sum_\\rho \\Re F(s - \\rho)$")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}, the sum
  $\sum_{\rho \in Z(\zeta)} \Re F(s - \rho)$ over the non-trivial zeros of $\zeta$ is
  convergent (Lean: `Summable`). -/)
  (proof := /-- Combine \ref{kadiri-laplace-re-decay} (giving $|\Re F(s-\rho)| \leq
  C/|\Im(s-\rho)|^2 = C/(\Im s - \gamma)^2$ for $|\gamma|$ large, since the real part
  $\Re(s-\rho) = \Re s - \beta$ stays in the bounded strip $[\Re s - 1, \Re s]$) with
  \ref{kadiri-backlund-bound} (giving $N(T) \ll T \log T$, hence by Abel summation
  $\sum_{|\gamma| \geq 1} 1/|\gamma|^2 < \infty$). Bound finitely many small-$|\gamma|$
  terms by hand. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1477)]
theorem summable_lap_re_at_zeros {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : deriv f 0 = 0)
    (hf_deriv_d : deriv f d = 0)
    (hf_deriv2_d : deriv (deriv f) d = 0)
    (s : ℂ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
                (laplaceTransform f (s - ρ.val)).re) := by
  sorry

@[blueprint
  "kadiri-re-inner-eq"
  (title := "Inner real-part identity: collapsing to $T_1$")
  (statement := /-- For every $s \in \mathbb{C}$ with $\Re s > 1$,
  $$ \Re \Bigl( \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} - \frac{1}{s - 1}
                + \sum_{\rho \in Z(\zeta)} \frac{1}{s - \rho} \Bigr)
   = -\tfrac{1}{2} \log \pi
     + \tfrac{1}{2} \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{s}{2}+1\right). $$
  This is the identity that turns the $f(0)$-coefficient of equation (16) into the $T_1$
  form of \ref{kadiri-prop-2-1}. -/)
  (proof := /-- For $\Re s > 1$ the Dirichlet series gives
  $\sum \Lambda(n)/n^s = -\zeta'/\zeta(s)$; apply \ref{kadiri-hadamard-identity} to rewrite
  the LHS (treating the equation as one in $\mathbb{C}$, not yet taking $\Re$). The
  $1/(s-1)$ and $\sum_\rho 1/(s-\rho)$ terms cancel, leaving
  $-B - \tfrac{1}{2}\log\pi + \tfrac{1}{2}\Gamma'/\Gamma(s/2+1) - \sum_\rho 1/\rho$.
  Taking real parts and applying \ref{kadiri-re-hadamardB-eq} cancels
  $\Re B + \sum_\rho \Re(1/\rho)$, leaving the claim. -/)
  (latexEnv := "lemma")
  (discussion := 1478)]
theorem re_inner_eq {s : ℂ} (hs : 1 < s.re) :
    ((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1) +
       ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
         1 / (s - ρ.val)).re =
    -(1 / 2 : ℝ) * Real.log Real.pi +
      (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re := by
  sorry

/-! ## Proposition 2.1 of `Kadiri2005` (the explicit formula)

Assembled from \ref{kadiri-identity-16}, \ref{kadiri-re-inner-eq}, and
\ref{kadiri-summable-lap-at-zeros}. -/

@[blueprint
  "kadiri-prop-2-1"
  (title := "Explicit formula (Kadiri 2005, Prop.~2.1)")
  (statement := /-- Let $d > 0$ and let $f \colon [0, d] \to \mathbb{R}$ be a non-negative
  function of class $C^2$ on $[0, d]$, compactly supported in $[0, d)$, satisfying the boundary
  conditions $f(d) = f'(0) = f'(d) = f''(d) = 0$ (hypothesis $(H_1)$ of \cite{Kadiri2005}).
  Let $F$ denote its Laplace transform $F(s) = \int_0^d e^{-s t} f(t)\, dt$, and let $F_2$
  denote the Laplace transform of $f''$. Then for every $s \in \mathbb{C}$ with $\Re s > 1$,
  the sum $\sum_{\rho \in Z(\zeta)} \Re F(s - \rho)$ over the non-trivial zeros is convergent,
  and
  $$ \Re \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n)
    = f(0) \left( -\tfrac{1}{2} \log \pi
        + \tfrac{1}{2} \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{s}{2} + 1\right) \right)
    + \Re F(s - 1) - \sum_{\rho \in Z(\zeta)} \Re F(s - \rho)
    + \Re \left( \frac{1}{2 \pi i} \int_{1/2 - i \infty}^{1/2 + i \infty}
        \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{z}{2}\right) \frac{F_2(s - z)}{(s - z)^2}\, dz
        + \frac{F_2(s)}{s^2} \right), $$
  where $Z(\zeta)$ is the set of non-trivial zeros of $\zeta$ (those in the open critical strip
  $0 < \Re \rho < 1$). The half-plane $\Re s > 1$ is the range used in Kadiri's downstream
  zero-free region argument; the harmonic-extension step that would lift the identity to all
  of $\mathbb{C}$ is not needed for that application. -/)
  (proof := /-- The `Summable` conjunct is \ref{kadiri-summable-lap-at-zeros}.
  For the identity, combine \ref{kadiri-identity-16} (the (16)-form on $\Re s > 1$) with
  \ref{kadiri-re-inner-eq} (which substitutes the $T_1$ form for the $f(0)$-coefficient
  $\Re$-expression, also on $\Re s > 1$). The result is a two-line `rw` chain. -/)
  (latexEnv := "proposition")
  (discussion := 1478)]
theorem prop_2_1 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : deriv f 0 = 0)
    (hf_deriv_d : deriv f d = 0)
    (hf_deriv2_d : deriv (deriv f) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
                (laplaceTransform f (s - ρ.val)).re) ∧
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)).re =
      f 0 * (-(1 / 2 : ℝ) * Real.log Real.pi
              + (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re)
        + (laplaceTransform f (s - 1)).re
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
            (laplaceTransform f (s - ρ.val)).re
        + ((1 / (2 * (Real.pi : ℂ) * I)) *
            (∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                laplaceTransform (fun u ↦ deriv (deriv f) u)
                  (s - (1 / 2 + (t : ℂ) * I))
                / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
            + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2).re := by
  refine ⟨summable_lap_re_at_zeros hd hf_nonneg hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d
      hf_deriv2_d s, ?_⟩
  rw [identity_16 hd hf_nonneg hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hf_deriv2_d hs,
      re_inner_eq hs]

/-! ## Definitions for equation (5) of `Kadiri2005`

The "gamma" term `T₁`, the "remainder" term `T₂`, and the difference operators `D`, `Δ₁`, `Δ₂`
are introduced in \cite[§2.1]{Kadiri2005} to package the RHS of (4) for use in the trigonometric
positivity argument. These are real-valued functions of a complex parameter. -/

/-- $T_1(s) := -\tfrac{1}{2} \log \pi + \tfrac{1}{2} \Re(\Gamma'/\Gamma)(s/2 + 1)$ — the "gamma"
contribution to the RHS of \cite[(4)]{Kadiri2005} (the term multiplied by $f(0)$ there). -/
noncomputable def T1 (s : ℂ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log Real.pi + (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re

/-- $T_2(s)$ — the contour-integral and boundary contributions to the RHS of
\cite[(4)]{Kadiri2005}, expressed via $F_2$, the Laplace transform of $f''$. -/
noncomputable def T2 (f : ℝ → ℝ) (s : ℂ) : ℝ :=
  ((1 / (2 * (Real.pi : ℂ) * I)) *
    (∫ t : ℝ,
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I))
        / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
    + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2).re

/-- $D_{\kappa, \delta}(s) := \Re F(s) - \kappa \Re F(s + \delta)$ — the "difference operator"
applied to $\Re F$ from \cite[§2.1]{Kadiri2005}. -/
noncomputable def D (f : ℝ → ℝ) (κ δ : ℝ) (s : ℂ) : ℝ :=
  (laplaceTransform f s).re - κ * (laplaceTransform f (s + (δ : ℂ))).re

/-- $\Delta_1(s) := T_1(s) - \kappa T_1(s + \delta)$ — the difference operator applied to $T_1$. -/
noncomputable def Δ1 (κ δ : ℝ) (s : ℂ) : ℝ :=
  T1 s - κ * T1 (s + (δ : ℂ))

/-- $\Delta_2(s) := T_2(s) - \kappa T_2(s + \delta)$ — the difference operator applied to $T_2$. -/
noncomputable def Δ2 (f : ℝ → ℝ) (κ δ : ℝ) (s : ℂ) : ℝ :=
  T2 f s - κ * T2 f (s + (δ : ℂ))

/-! ## Equation (5) of `Kadiri2005`: the "damped" explicit formula -/

@[blueprint
  "kadiri-eq-5"
  (title := "Damped explicit formula (Kadiri 2005, eq.~(5))")
  (statement := /-- For $f$ as in \ref{kadiri-prop-2-1}, real parameters $\kappa, \delta$, and
  $s \in \mathbb{C}$, set
  $$ \Delta_1(s) := T_1(s) - \kappa T_1(s + \delta), \qquad
     \Delta_2(s) := T_2(s) - \kappa T_2(s + \delta), \qquad
     D(s) := \Re F(s) - \kappa \Re F(s + \delta), $$
  where $T_1, T_2$ are the "gamma" and "remainder" contributions to the RHS of
  \ref{kadiri-prop-2-1}. Then
  $$ \Re \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n) \left( 1 - \frac{\kappa}{n^\delta} \right)
       = f(0) \Delta_1(s) + D(s - 1) - \sum_{\rho \in Z(\zeta)} D(s - \rho) + \Delta_2(s). $$
  -/)
  (proof := /-- Direct substitution: apply \ref{kadiri-prop-2-1} at $s$ and at $s + \delta$,
  multiply the latter by $\kappa$, subtract, and use the identity
  $n^{-s} - \kappa n^{-(s + \delta)} = n^{-s} (1 - \kappa n^{-\delta})$ to combine the LHS,
  while the definitions of $\Delta_1, \Delta_2, D$ combine the corresponding RHS terms. -/)
  (latexEnv := "lemma")
  (discussion := 1478)]
theorem eq_5 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ} (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d)) (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0) (hf_deriv_0 : deriv f 0 = 0) (hf_deriv_d : deriv f d = 0)
    (hf_deriv2_d : deriv (deriv f) d = 0) (κ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, Λ n / n ^ s * f (Real.log n) * ((1 : ℂ) - κ / n ^ (δ : ℂ))).re =
      f 0 * Δ1 κ δ s + D f κ δ (s - 1)
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ, D f κ δ (s - ρ.val) + Δ2 f κ δ s := by
  have hsδ : 1 < (s + δ).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have h1 := prop_2_1 hd hf_nonneg hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hf_deriv2_d hs
  have h2 := prop_2_1 hd hf_nonneg hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hf_deriv2_d hsδ
  have hLHS :
      (∑' n : ℕ, Λ n / n ^ s * f (Real.log n) * ((1 : ℂ) - κ / n ^ (δ : ℂ))).re =
      (∑' n : ℕ, Λ n / (n : ℂ) ^ s * f (Real.log n)).re
        - κ * (∑' n : ℕ, Λ n / (n : ℂ) ^ (s + δ) * f (Real.log n)).re := by
    have hpoint (n : ℕ) :
        Λ n / n ^ s * f (Real.log n) * ((1 : ℂ) - κ / n ^ (δ : ℂ)) =
        Λ n / n ^ s * f (Real.log n) - κ * (Λ n / n ^ (s + δ) * f (Real.log n)) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [cpow_add s (δ : ℂ) (Nat.cast_ne_zero.mpr hn)]
        field_simp
    have h_complex :
        (∑' n : ℕ, Λ n / n ^ s * f (Real.log n) * ((1 : ℂ) - κ / n ^ (δ : ℂ))) =
        (∑' n : ℕ, Λ n / (n : ℂ) ^ s * f (Real.log n)) -
        (κ : ℂ) * (∑' n : ℕ, Λ n/ (n : ℂ) ^ (s + δ) * f (Real.log n)) := by
      simp_rw [hpoint]
      rw [((summable_f_log hf_supp _).hasSum.sub ((summable_f_log hf_supp _).mul_left
        (κ : ℂ)).hasSum).tsum_eq, tsum_mul_left]
    rw [h_complex, Complex.sub_re, Complex.re_ofReal_mul]
  have hZeros :
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ, D f κ δ (s - ρ.val)) =
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
          (laplaceTransform f (s - ρ.val)).re)
        - κ * (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
                 (laplaceTransform f ((s + δ) - ρ.val)).re) := by
    have harg : ∀ ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (s - ρ.val) + δ = s + δ - ρ.val := fun _ ↦ by ring
    simp_rw [D, harg, (h1.1.hasSum.sub (h2.1.mul_left κ).hasSum).tsum_eq, tsum_mul_left]
  rw [hLHS, h1.2, h2.2, hZeros]
  simp only [Δ1, Δ2, D, T1, T2]
  ring_nf

end Kadiri
