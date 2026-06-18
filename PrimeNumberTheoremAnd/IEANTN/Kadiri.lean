import Architect
import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import PrimeNumberTheoremAnd.LaplaceInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.RiemannZeta

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
open Filter
open scoped Topology

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

@[blueprint
  "kadiri-hadamard-B"
  (title := "Hadamard constant $B$")
  (statement := /-- The constant $B \in \mathbb{C}$ appearing in the Hadamard product
  factorisation of the Riemann zeta function:
  $$ (s - 1) \zeta(s) = \tfrac{1}{2} e^{B s}
       \prod_{\rho \in Z(\zeta)} \left(1 - \tfrac{s}{\rho}\right) e^{s/\rho}. $$
  Concretely $B = -\tfrac{\gamma}{2} - 1 + \tfrac{1}{2} \log (4\pi)$ in terms of the
  Euler-Mascheroni constant $\gamma$ (\cite[Chapter 12]{Davenport2000}). For our purposes it
  appears only as the additive constant in \ref{kadiri-hadamard-identity}, and the identity
  $\Re B = -\sum_{\rho \in Z(\zeta)} \Re \tfrac{1}{\rho}$ used in the derivation of
  \ref{kadiri-prop-2-1}.

  Formally, $B$ is extracted from the Hadamard factorisation of Riemann's xi function
  $\xi(s) = (s-1)\, \pi^{-s/2}\, \Gamma(\tfrac{s}{2}+1)\, \zeta(s)$: there is a unique
  $B \in \mathbb{C}$ arising as $P'(0)$ for a degree-one polynomial $P$ with
  $\xi(z) = e^{P(z)} \prod_\rho (1 - z/\rho) e^{z/\rho}$ (the genus-one canonical product
  over the xi divisor, with multiplicity), and the displayed product expansion of
  $(s-1)\zeta(s)$ is that factorisation with the archimedean factors moved across. -/)
  (latexEnv := "definition")
  (discussion := 1474)]
noncomputable def hadamardB : ℂ :=
  Classical.choose existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero.exists

/-- Choice specification for `hadamardB`: some degree-one polynomial `P` realizes the
no-monomial xi Hadamard factorization with `hadamardB = P.derivative.eval 0`. -/
theorem hadamardB_spec :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      (∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      hadamardB = Polynomial.eval 0 P.derivative :=
  Classical.choose_spec existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero.exists

@[blueprint
  "kadiri-hadamard-identity"
  (title := "Hadamard expansion of $-\\zeta'/\\zeta$ (after equation (16))")
  (statement := /-- For every $s \in \mathbb{C}$ that is neither $1$ nor a non-trivial zero
  of $\zeta$,
  $$ -\frac{\zeta'}{\zeta}(s) = -B - \tfrac{1}{2} \log \pi + \frac{1}{s - 1}
       + \tfrac{1}{2} \frac{\Gamma'}{\Gamma}\!\left(\tfrac{s}{2} + 1\right)
       - \sum_{\rho \in Z(\zeta)} \left(\frac{1}{\rho} + \frac{1}{s - \rho}\right), $$
  where $B$ is the Hadamard constant (\ref{kadiri-hadamard-B}). This is the logarithmic
  derivative of the Hadamard factorisation of $\zeta$
  (\cite[Chapter 12]{Davenport2000}). -/)
  (proof := /-- Differentiate the Hadamard product (\ref{kadiri-hadamard-B}) logarithmically;
  the linear-in-$s$ term in the exponential collapses to the constant $B$. The
  $\tfrac{1}{s-1}$ term comes from the $(s-1)\zeta(s)$ prefactor and the
  $\tfrac{1}{2} \Gamma'/\Gamma$ term from the gamma factor. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1474)]
theorem hadamard_identity (s : ℂ) (hs1 : s ≠ 1)
    (hsZ : s ∉ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ)) :
    -deriv riemannZeta s / riemannZeta s =
      -hadamardB - (1 / 2 : ℂ) * Real.log Real.pi + 1 / (s - 1) +
      (1 / 2 : ℂ) * digamma (s / 2 + 1) -
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (s - ρ.val)) := by
  sorry

/-! ## Sublemmas for the proof of Theorem 3.1

The proof of \ref{kadiri-thm-3-1-q1} (Kadiri 2005, \S 3.1, pp.~11--13) decomposes into
several explicit steps. We state each as its own blueprinted sublemma below, with `sorry`
proofs to be filled in. The displayed equation before \cite[(11)]{Kadiri2005} is the
underlying Laplace-inversion identity; equations (11)--(15) are the explicit steps. -/

@[blueprint
  "kadiri-thm-3-1-q1-laplace-inversion"
  (title := "Laplace inversion of $\\varphi$ at $y = \\log n$ for $n \\geq 1$")
  (statement := /-- For $\varphi$ satisfying hypotheses (A) and (B) of
  \ref{kadiri-thm-3-1-q1}, and any real $a$ with $0 < a < b$ and $a < 1$: for every
  positive integer $n \geq 1$,
  $$ \varphi(\log n)
     = \frac{1}{2\pi i}
       \int_{-(1 + a) - i\infty}^{-(1 + a) + i\infty}
       \Phi(s)\, n^{s}\, ds, $$
  where $\Phi(s) := \int_0^{\infty} \varphi(y)\, e^{-sy}\, dy$ is the Laplace transform of
  $\varphi$. The contour $\sigma = -(1 + a)$ lies inside the strip of holomorphy of
  $\Phi$ given by (B). This is the displayed equation just before
  \cite[(11)]{Kadiri2005}. -/)
  (proof := /-- Standard inverse-Laplace theorem (e.g.\ Widder, \emph{The Laplace
  Transform}, Ch.~III, Theorem~7.3). Hypotheses (A) (regularity / mean-value condition at
  jumps) and (B) (the $O(1/|t|)$ decay of $\Phi$ on the strip) provide exactly what is
  needed for the inversion integral to converge absolutely and recover $\varphi$ at
  $y = \log n \geq 0$. To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1535)]
theorem kadiri_thm_3_1_q1_laplace_inversion {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    {n : ℕ} (_hn : 1 ≤ n) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (φ (Real.log n) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ,
          Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
            ((n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  sorry

@[blueprint
  "kadiri-thm-3-1-q1-eq-11"
  (title := "Equation (11) of \\cite{Kadiri2005}: LHS as a Mellin contour integral")
  (statement := /-- For $\varphi$ satisfying (A) and (B) of \ref{kadiri-thm-3-1-q1},
  and any real $a$ with $0 < a < b$ and $a < 1$,
  $$ \sum_{n \geq 1} \Lambda(n)\, \varphi(\log n)
     = \frac{1}{2 \pi i}
       \int_{1 + a - i\infty}^{1 + a + i\infty}
         \left(-\frac{\zeta'}{\zeta}\right)(s)\, \Phi(-s)\, ds, $$
  with $\Phi$ as in \ref{kadiri-thm-3-1-q1-laplace-inversion}. This is equation~(11) of
  \cite{Kadiri2005}, page~11, specialized to $q = 1$. -/)
  (proof := /-- Corollary of \ref{kadiri-thm-3-1-q1-laplace-inversion}: multiply that
  identity by $\Lambda(n)$, sum over $n \geq 1$, and exchange sum and integral
  (justified by absolute convergence of the Dirichlet series for $-\zeta'/\zeta$ on
  $\sigma > 1$ combined with the $O(1/|t|)$ decay of $\Phi$ from (B)). The Dirichlet
  series identity $-\zeta'/\zeta(s) = \sum_n \Lambda(n) n^{-s}$ converts the sum into a
  factor of $-\zeta'/\zeta(s)$ in the integrand. Finally, change of variable
  $s \mapsto -s$ maps the contour $\sigma = -(1 + a)$ to $\sigma = 1 + a$ (with the
  orientation-flip cancelling the sign from $ds$). To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1536)]
theorem kadiri_thm_3_1_q1_eq_11 {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ,
          (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  sorry

@[blueprint
  "kadiri-thm-3-1-q1-I"
  (title := "Truncated contour integral $I(T)$ on $\\sigma = 1 + a$")
  (statement := /-- Kadiri's $I(T)$ from \cite[p.~12]{Kadiri2005}: the truncated contour
  integral
  $$ I(T) \;:=\; \frac{1}{2\pi i} \int_{1+a-iT}^{1+a+iT}
              \!\!\!\! \left(-\frac{\zeta'}{\zeta}\right)\!(s)\, \Phi(-s)\, ds, $$
  where $\Phi(s) := \int_0^\infty \varphi(y) e^{-sy}\, dy$ is the Laplace transform of
  $\varphi$. The $T \to \infty$ limit of $I(T)$ is the Mellin-contour identity of
  \ref{kadiri-thm-3-1-q1-eq-11}, and its rectangle decomposition is equation~(12) of
  \cite{Kadiri2005} (\ref{kadiri-thm-3-1-q1-eq-12}). -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
          riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
        Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I))

@[blueprint
  "kadiri-thm-3-1-q1-eq-12"
  (title := "Equation (12) of \\cite{Kadiri2005}: rectangle decomposition of $I(T)$")
  (statement := /-- Under the hypotheses of \ref{kadiri-thm-3-1-q1-eq-11}: for every
  $T > 0$,
  $$ I(T) \;=\; \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
                    \!\!\!\! \left(-\frac{\zeta'}{\zeta}\right)\!(s)\, \Phi(-s)\, ds
             \;+\; \frac{1}{2\pi i} \int_{-a + iT}^{1+a + iT}
                    \!\!\!\! \left(-\frac{\zeta'}{\zeta}\right)\!(s)\, \Phi(-s)\, ds
             \;-\; \frac{1}{2\pi i} \int_{-a - iT}^{1+a - iT}
                    \!\!\!\! \left(-\frac{\zeta'}{\zeta}\right)\!(s)\, \Phi(-s)\, ds
             \;+\; \Phi(-1) \;-\; \!\!\!\!\!\!
                    \sum_{\substack{\rho \in Z(\zeta) \\ |\Im \rho| < T}}
                    \!\!\!\! \mathrm{ord}_\zeta(\rho)\, \Phi(-\rho). $$
  This is equation (12) of \cite{Kadiri2005}, page~12, specialized to $q = 1$
  ($\delta_{q,1} = 1$, $\mathfrak{a} = 0$, so the residue contribution
  $-(-\delta_{q,1}\Phi(-1) + \tfrac{1}{2}(1-\delta_{q,1})(1-\mathfrak{a})\Phi(0)
  + \sum_\rho \Phi(-\rho))$ collapses to
  $\Phi(-1) - \sum_\rho \mathrm{ord}_\zeta(\rho)\, \Phi(-\rho)$); the
  $\rho$-sum is over the non-trivial zeros enclosed by the rectangle (i.e.\ those with
  $|\Im \rho| < T$), weighted by their multiplicity
  $\mathrm{ord}_\zeta(\rho) := -\mathrm{ord}\,\zeta\!\restriction_{\rho}$
  (the order of $\rho$ as a zero of $\zeta$). -/)
  (proof := /-- Apply the residue theorem to $(-\zeta'/\zeta)(s) \Phi(-s)$ on the
  counterclockwise rectangle with vertices $1+a-iT$, $1+a+iT$, $-a+iT$, $-a-iT$.
  Between $\sigma = -a$ and $\sigma = 1+a$, the integrand has poles only at $s = 1$
  (a simple pole of $-\zeta'/\zeta$ with residue $+\Phi(-1)$, from the simple pole of
  $\zeta$ at $s = 1$) and at each non-trivial zero $s = \rho \in Z(\zeta)$ with
  $|\Im \rho| < T$ (a pole of $-\zeta'/\zeta$ with residue
  $-\mathrm{ord}_\zeta(\rho)\, \Phi(-\rho)$, weighted by the multiplicity of $\rho$).
  [Note: $\zeta(0) = -1/2 \neq 0$, so there is no pole at $s = 0$; the trivial zeros
  at $s = -2, -4, \ldots$ all lie to the left of $\sigma = -a$ and are not enclosed.]
  To be formalised. -/)
  (latexEnv := "sublemma")
   (discussion := 1537)]
theorem kadiri_thm_3_1_q1_eq_12 {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    {T : ℝ} (_hT : 0 < T) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    kadiri_thm_3_1_q1_I φ a T =
      -- (1/(2πi)) ∫ on σ = -a from -iT to +iT
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t in Set.Ioo (-T) T,
          (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)))
      -- + (1/(2πi)) ∫ top horizontal from -a+iT to 1+a+iT
      + (1 / (2 * (Real.pi : ℂ) * I)) *
        (∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
              riemannZeta ((σ : ℂ) + (T : ℂ) * I)) *
            Φ (-((σ : ℂ) + (T : ℂ) * I)))
      -- − (1/(2πi)) ∫ bottom horizontal from -a-iT to 1+a-iT
      - (1 / (2 * (Real.pi : ℂ) * I)) *
        (∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
              riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) *
            Φ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I)))
      + Φ (-1)
      - riemannZeta.zeroes_sum (.Ioo 0 1) (.Ioo (-T) T) (fun ρ ↦ Φ (-ρ)) := by
  sorry

@[blueprint
  "kadiri-thm-3-1-q1-top-horizontal-vanishes"
  (title := "Top horizontal integral in eq.~(12) of \\cite{Kadiri2005} vanishes as $T \\to \\infty$")
  (statement := /-- Under the hypotheses of \ref{kadiri-thm-3-1-q1-eq-11}:
  $$ \lim_{T \to \infty}
       \frac{1}{2\pi i} \int_{-a + iT}^{1 + a + iT}
         \!\!\!\! \left(-\frac{\zeta'}{\zeta}\right)\!(s)\, \Phi(-s)\, ds \;=\; 0. $$
  This is one of the two assertions on \cite[p.~12]{Kadiri2005} that "les deux
  dernières intégrales tendent vers $0$ lorsque $T$ tend vers $\infty$." -/)
  (proof := /-- The integrand has $|\Phi(-s)| = O(1/|t|) = O(1/T)$ on the horizontal arc
  (by (B), uniformly on the closed strip $-a \leq \sigma \leq 1 + a$), and
  $-\zeta'/\zeta(s)$ grows at most polynomially in $\log|\Im s| = \log T$ on this strip.
  The horizontal arc has fixed length $1 + 2a$, so the integral is bounded by
  $O((\log T)^k / T) \to 0$ as $T \to \infty$. To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1538)]
theorem kadiri_thm_3_1_q1_top_horizontal_vanishes
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ ↦
        (1 / (2 * (Real.pi : ℂ) * I)) *
          ∫ σ in Set.Ioo (-a) (1 + a),
            (-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
                riemannZeta ((σ : ℂ) + (T : ℂ) * I)) *
              Φ (-((σ : ℂ) + (T : ℂ) * I)))
      Filter.atTop (nhds 0) := by
  sorry

@[blueprint
  "kadiri-thm-3-1-q1-bot-horizontal-vanishes"
  (title := "Bottom horizontal integral in eq.~(12) of \\cite{Kadiri2005} vanishes as $T \\to \\infty$")
  (statement := /-- Under the hypotheses of \ref{kadiri-thm-3-1-q1-eq-11}:
  $$ \lim_{T \to \infty}
       \frac{1}{2\pi i} \int_{-a - iT}^{1 + a - iT}
         \!\!\!\! \left(-\frac{\zeta'}{\zeta}\right)\!(s)\, \Phi(-s)\, ds \;=\; 0. $$
  Companion to \ref{kadiri-thm-3-1-q1-top-horizontal-vanishes}. -/)
  (proof := /-- Identical argument to \ref{kadiri-thm-3-1-q1-top-horizontal-vanishes},
  with $T$ replaced by $-T$ (the decay bound on $\Phi$ is symmetric in $t$, and the
  growth bound on $-\zeta'/\zeta$ depends only on $|t|$). To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1539)]
theorem kadiri_thm_3_1_q1_bot_horizontal_vanishes
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ ↦
        (1 / (2 * (Real.pi : ℂ) * I)) *
          ∫ σ in Set.Ioo (-a) (1 + a),
            (-deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
                riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) *
              Φ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I)))
      Filter.atTop (nhds 0) := by
  sorry

private lemma zetaPiFactor_eq_cpow (s : ℂ) :
    zetaPiFactor s = (Real.pi : ℂ) ^ (-(s / 2)) := by
  unfold zetaPiFactor
  rw [Complex.cpow_def_of_ne_zero, Complex.ofReal_log Real.pi_pos.le]
  · ring_nf
  · exact_mod_cast Real.pi_ne_zero

private lemma completedZetaFactor_eq_mul_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hΓhalf : Gamma (s / 2) ≠ 0) :
    completedZetaFactor s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  have hGamma :
      Gamma (s / 2 + 1) = (s / 2) * Gamma (s / 2) := by
    exact Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero)
  rw [completedZetaFactor, zetaPoleFactor, zetaGammaFactor, zetaPiFactor_eq_cpow,
    hGamma, riemannZeta_def_of_ne_zero hs0, Gammaℝ_def]
  field_simp [hs0, hΓhalf]

private lemma gamma_half_avoid_neg_nat_of_shift {s : ℂ} (hs0 : s ≠ 0)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    ∀ m : ℕ, s / 2 ≠ -m := by
  intro m hm
  cases m with
  | zero =>
      apply hs0
      rw [show s = 2 * (s / 2) by ring, hm]
      ring
  | succ m =>
      have hbad : s / 2 + 1 = -(m : ℂ) := by
        rw [hm]
        norm_num
      exact hΓdiff m hbad

private lemma gamma_half_ne_zero_of_shift {s : ℂ} (hs0 : s ≠ 0)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    Gamma (s / 2) ≠ 0 :=
  Gamma_ne_zero (gamma_half_avoid_neg_nat_of_shift hs0 hΓdiff)

private theorem completedZetaFactor_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓhalf : Gamma (s / 2) ≠ 0) (hΓhalf_ref : Gamma ((1 - s) / 2) ≠ 0) :
    completedZetaFactor (1 - s) = completedZetaFactor s := by
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 := by rw [h]; ring
  rw [completedZetaFactor_eq_mul_completedRiemannZeta h1s0 hΓhalf_ref,
    completedZetaFactor_eq_mul_completedRiemannZeta hs0 hΓhalf, completedRiemannZeta_one_sub]
  ring

private lemma differentiableAt_completedZetaFactor {s : ℂ}
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    DifferentiableAt ℂ completedZetaFactor s := by
  unfold completedZetaFactor zetaPoleFactor zetaPiFactor zetaGammaFactor
  exact (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s - 1) s).mul
      (by
        rw [show (fun s : ℂ => Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))) =
          Complex.exp ∘ (fun s : ℂ => -(s / 2) * (Real.log Real.pi : ℂ)) by rfl]
        exact Complex.differentiableAt_exp.comp s (by fun_prop))).mul
      ((differentiableAt_Gamma _ hΓdiff).comp s (by fun_prop))).mul
    (differentiableAt_riemannZeta hs1)

private theorem logDeriv_completedZetaFactor_one_sub {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓdiff_s : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓdiff_ref : ∀ m : ℕ, (1 - s) / 2 + 1 ≠ -m) :
    logDeriv completedZetaFactor (1 - s) = -logDeriv completedZetaFactor s := by
  let R : ℂ → ℂ := fun z => 1 - z
  have hΓhalf_s : Gamma (s / 2) ≠ 0 :=
    gamma_half_ne_zero_of_shift hs0 hΓdiff_s
  have hΓhalf_ref_s : Gamma ((1 - s) / 2) ≠ 0 :=
    gamma_half_ne_zero_of_shift (by
      intro h
      apply hs1
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 := by rw [h]; ring) hΓdiff_ref
  have hΓhalf_near : ∀ᶠ z in 𝓝 s, Gamma (z / 2) ≠ 0 := by
    have hdiff : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s :=
      (differentiableAt_Gamma _ (gamma_half_avoid_neg_nat_of_shift hs0 hΓdiff_s)).comp
        s (by fun_prop)
    have hcont : ContinuousAt (fun z : ℂ => Gamma (z / 2)) s := hdiff.continuousAt
    exact (hcont.ne_iff_eventually_ne continuousAt_const).mp hΓhalf_s
  have hΓhalf_ref_near : ∀ᶠ z in 𝓝 s, Gamma ((1 - z) / 2) ≠ 0 := by
    have hdiff : DifferentiableAt ℂ (fun z : ℂ => Gamma ((1 - z) / 2)) s :=
      (differentiableAt_Gamma _ (gamma_half_avoid_neg_nat_of_shift (by
        intro h
        apply hs1
        calc
          s = 1 - (1 - s) := by ring
          _ = 1 := by rw [h]; ring) hΓdiff_ref)).comp s (by fun_prop)
    have hcont : ContinuousAt (fun z : ℂ => Gamma ((1 - z) / 2)) s := hdiff.continuousAt
    exact (hcont.ne_iff_eventually_ne continuousAt_const).mp hΓhalf_ref_s
  have hsym_near :
      (completedZetaFactor ∘ R) =ᶠ[𝓝 s] completedZetaFactor := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1, hΓhalf_near,
      hΓhalf_ref_near] with z hz0 hz1 hΓz hΓrefz
    exact completedZetaFactor_one_sub hz0 hz1 hΓz hΓrefz
  have hcomp :
      logDeriv (completedZetaFactor ∘ R) s =
        logDeriv completedZetaFactor (R s) * deriv R s := by
    rw [logDeriv_comp]
    · exact differentiableAt_completedZetaFactor
        (by simpa [R] using sub_ne_zero.mpr hs0.symm) hΓdiff_ref
    · dsimp [R]
      fun_prop
  have hderivR : deriv R s = -1 := by
    dsimp [R]
    simp
  have hlog_eq :
      logDeriv (completedZetaFactor ∘ R) s = logDeriv completedZetaFactor s := by
    rw [logDeriv_apply, logDeriv_apply]
    rw [Filter.EventuallyEq.deriv_eq hsym_near]
    exact congrArg (fun z => deriv completedZetaFactor s / z) hsym_near.eq_of_nhds
  rw [hcomp, hderivR] at hlog_eq
  calc
    logDeriv completedZetaFactor (1 - s)
        = -(logDeriv completedZetaFactor (R s) * -1) := by simp [R]
    _ = -logDeriv completedZetaFactor s := by rw [hlog_eq]

private theorem neg_logDeriv_zeta_left_eq_reflected {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hζz : riemannZeta z ≠ 0)
    (hζref : riemannZeta (1 - z) ≠ 0)
    (hΓz_diff : ∀ m : ℕ, z / 2 + 1 ≠ -m)
    (hΓref_diff : ∀ m : ℕ, (1 - z) / 2 + 1 ≠ -m)
    (hΓz : zetaGammaFactor z ≠ 0)
    (hΓref : zetaGammaFactor (1 - z) ≠ 0) :
    -deriv riemannZeta z / riemannZeta z =
      deriv riemannZeta (1 - z) / riemannZeta (1 - z)
        + 1 / (z - 1) + 1 / ((1 - z) - 1)
        - (Real.log Real.pi : ℂ)
        + (1 / 2 : ℂ) * digamma (z / 2 + 1)
        + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1) := by
  have href1 : 1 - z ≠ 1 := by
    intro h
    apply hz0
    calc
      z = 1 - (1 - z) := by ring
      _ = 0 := by rw [h]; ring
  have hleft := neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv z hz1 hΓz_diff hΓz hζz
  have hright := neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv (1 - z) href1
    hΓref_diff hΓref hζref
  have htransport := logDeriv_completedZetaFactor_one_sub hz0 hz1 hΓz_diff hΓref_diff
  have hnegLD :
      -logDeriv completedZetaFactor z =
        deriv riemannZeta (1 - z) / riemannZeta (1 - z)
          + 1 / ((1 - z) - 1)
          - (1 / 2 : ℂ) * Real.log Real.pi
          + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1) := by
    rw [htransport] at hright
    have hright' := congrArg Neg.neg hright
    ring_nf at hright' ⊢
    rw [hright']
    ring
  rw [hleft, hnegLD]
  ring

private lemma zetaGammaFactor_shift_avoid_of_not_zero {s : ℂ}
    (hsZ : s ∉ riemannZeta.zeroes) :
    ∀ m : ℕ, s / 2 + 1 ≠ -m := by
  intro m hm
  apply hsZ
  have hs_eq : s = -2 * ((m : ℂ) + 1) := by
    calc
      s = 2 * (s / 2 + 1) - 2 := by ring
      _ = 2 * (-(m : ℂ)) - 2 := by rw [hm]
      _ = -2 * ((m : ℂ) + 1) := by ring
  rw [riemannZeta.zeroes]
  simpa [hs_eq, Nat.cast_add, Nat.cast_one] using
    riemannZeta_neg_two_mul_nat_add_one m

private theorem functional_eq_correct_sign {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0)
    (hζref : riemannZeta (1 - s) ≠ 0)
    (hΓs_diff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓref_diff : ∀ m : ℕ, (1 - s) / 2 + 1 ≠ -m) :
    -deriv riemannZeta s / riemannZeta s =
      ((-Real.log Real.pi : ℝ) : ℂ)
      + deriv riemannZeta (1 - s) / riemannZeta (1 - s)
      + (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) := by
  have h1s0 : (1 : ℂ) - s ≠ 0 := by
    intro h
    apply hs1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 := by rw [h]; ring
  have hΓs : zetaGammaFactor s ≠ 0 := by
    unfold zetaGammaFactor
    exact Gamma_ne_zero hΓs_diff
  have hΓref : zetaGammaFactor (1 - s) ≠ 0 := by
    unfold zetaGammaFactor
    exact Gamma_ne_zero hΓref_diff
  have hFE := neg_logDeriv_zeta_left_eq_reflected hs0 hs1 hζs hζref
    hΓs_diff hΓref_diff hΓs hΓref
  have hψs : digamma (s / 2 + 1) = digamma (s / 2) + (s / 2)⁻¹ :=
    digamma_apply_add_one _ (gamma_half_avoid_neg_nat_of_shift hs0 hΓs_diff)
  have hψref : digamma ((1 - s) / 2 + 1) = digamma ((1 - s) / 2) + ((1 - s) / 2)⁻¹ :=
    digamma_apply_add_one _ (gamma_half_avoid_neg_nat_of_shift h1s0 hΓref_diff)
  have hcancel :
      1 / (s - 1) + 1 / (1 - s - 1)
        + (1 / 2 : ℂ) * (s / 2)⁻¹ + (1 / 2 : ℂ) * ((1 - s) / 2)⁻¹ = 0 := by
    have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [show (1 : ℂ) - s - 1 = -s by ring]
    field_simp [hs0, hs_sub]
    ring_nf
  rw [hFE, hψs, hψref, Complex.ofReal_neg]
  linear_combination hcancel

@[blueprint
  "kadiri-thm-3-1-q1-functional-eq"
  (title := "Functional equation of $-\\zeta'/\\zeta$ in log-derivative form")
  (statement := /-- For every $s \in \mathbb{C}$ such that $\zeta(s) \neq 0$,
  $\zeta(1 - s) \neq 0$, $s \neq 1$, and $s \neq 0$,
  $$ -\frac{\zeta'}{\zeta}(s) \;=\; \log\frac{1}{\pi}
                                 \;+\; \frac{\zeta'}{\zeta}(1-s)
                                 \;+\; \frac{1}{2}\!\left\{
                                       \frac{\Gamma'}{\Gamma}\!\Big(\frac{s}{2}\Big)
                                     + \frac{\Gamma'}{\Gamma}\!\Big(\frac{1-s}{2}\Big)
                                       \right\}. $$
  This is the displayed equation just before $I_1, I_2, I_3$ are defined on
  \cite[p.~12]{Kadiri2005}, specialized from the general Dirichlet $L$-function form to
  $q = 1$ (so $L = \zeta$, $\bar\chi = \chi$, $\mathfrak{a} = 0$). The hypotheses
  $\zeta(s), \zeta(1-s) \neq 0$ exclude both the non-trivial zeros (those in the
  critical strip) and the trivial zeros $s, 1-s \in \{-2, -4, \ldots\}$ where the
  $\zeta'/\zeta$ terms would otherwise be degenerate. -/)
  (proof := /-- Take the logarithmic derivative of the completed-zeta functional equation
  $\zeta(s)\, \Gamma(s/2)\, \pi^{-s/2}
      = \zeta(1-s)\, \Gamma((1-s)/2)\, \pi^{-(1-s)/2}$
  (with appropriate $(s-1)$ regularization at $s = 1$). Differentiating both sides with
  respect to $s$ gives
  $\zeta'/\zeta(s) + \tfrac{1}{2}\Gamma'/\Gamma(s/2) - \tfrac{1}{2}\log\pi
   = -\zeta'/\zeta(1-s) - \tfrac{1}{2}\Gamma'/\Gamma((1-s)/2) + \tfrac{1}{2}\log\pi$,
  and solving for $-\zeta'/\zeta(s)$ yields the stated identity (note the chain-rule
  sign from $d(1-s)/ds = -1$ giving the $+\zeta'/\zeta(1-s)$ term).
  To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1540)]
theorem kadiri_thm_3_1_q1_functional_eq {s : ℂ}
    (_hs1 : s ≠ 1) (_hs0 : s ≠ 0)
    (_hζs : riemannZeta s ≠ 0)
    (_hζ1s : riemannZeta (1 - s) ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      ((-Real.log Real.pi : ℝ) : ℂ)
      + deriv riemannZeta (1 - s) / riemannZeta (1 - s)
      + (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) := by
  exact functional_eq_correct_sign _hs0 _hs1 _hζs _hζ1s
    (zetaGammaFactor_shift_avoid_of_not_zero
      (by simpa [riemannZeta.zeroes] using _hζs))
    (zetaGammaFactor_shift_avoid_of_not_zero
      (by simpa [riemannZeta.zeroes] using _hζ1s))

private lemma riemannZeta_neg_real_Ioo_ne_zero {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    riemannZeta (((-a : ℝ) : ℂ)) ≠ 0 := by
  let w : ℂ := ((1 + a : ℝ) : ℂ)
  have hw_zeta : riemannZeta w ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [w]
    linarith
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have hre : w.re = (-(n : ℂ)).re := congrArg Complex.re hn
    simp [w] at hre
    have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    linarith
  have hw_ne_one : w ≠ 1 := by
    intro h
    have hre : w.re = (1 : ℂ).re := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [w]
    linarith
  have hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hre : (↑Real.pi * w / 2).re =
        (((2 * (k : ℂ) + 1) * ↑Real.pi / 2).re) :=
      congrArg Complex.re hk
    have hmain : 1 + a = (2 * k + 1 : ℝ) := by
      have hscaled : Real.pi * (1 + a) / 2 =
          (2 * (k : ℝ) + 1) * Real.pi / 2 := by
        simpa [w, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hre
      nlinarith [Real.pi_pos]
    have haeq : a = (2 * k : ℝ) := by linarith
    cases le_or_gt k 0 with
    | inl hk_nonpos =>
        have hkreal : (2 * k : ℝ) ≤ 0 := by
          exact_mod_cast
            (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℤ) ≤ 2) hk_nonpos)
        linarith
    | inr hk_pos =>
        have hk_one : (1 : ℤ) ≤ k := by omega
        have hkreal : (2 : ℝ) ≤ 2 * k := by
          exact_mod_cast (mul_le_mul_of_nonneg_left hk_one (by norm_num : (0 : ℤ) ≤ 2))
        linarith
  have hfactor : 2 * (2 * ↑Real.pi : ℂ) ^ (-w) * Complex.Gamma w *
      Complex.cos (↑Real.pi * w / 2) * riemannZeta w ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos)
      hw_zeta
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  have hone : 1 - w = (((-a : ℝ) : ℂ)) := by
    dsimp [w]
    apply Complex.ext <;> simp
  rw [hone] at hfe
  rw [hfe]
  exact hfactor

private theorem kadiri_thm_3_1_q1_shifted_pointwise_functional_eq
    {φ : ℝ → ℂ} {a T : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ t ∈ Set.Ioo (-T) T,
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      (-deriv riemannZeta s / riemannZeta s) * Φ (-s) =
        ((-Real.log Real.pi : ℝ) : ℂ) * Φ (-s)
          + (deriv riemannZeta (1 - s) / riemannZeta (1 - s)) * Φ (-s)
          + ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) * Φ (-s) := by
  intro t _ht
  dsimp
  let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = (1 : ℂ).re := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    have hre : s.re = (0 : ℂ).re := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hζref : riemannZeta (1 - s) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [s]
    linarith
  have hζs : riemannZeta s ≠ 0 := by
    by_cases ht : t = 0
    · subst ht
      simpa [s] using riemannZeta_neg_real_Ioo_ne_zero ha ha1
    · apply riemannZeta_ne_zero_of_re_nonpos_im_ne_zero
      · simp [s]
        linarith
      · simp [s, ht]
  have hfe := kadiri_thm_3_1_q1_functional_eq (s := s) hs1 hs0 hζs hζref
  calc
    (-deriv riemannZeta s / riemannZeta s) *
        (∫ y, φ y * exp (-(-s) * (y : ℂ)) ∂volume) =
        (((-Real.log Real.pi : ℝ) : ℂ)
          + deriv riemannZeta (1 - s) / riemannZeta (1 - s)
          + (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) *
          (∫ y, φ y * exp (-(-s) * (y : ℂ)) ∂volume) := by
      rw [hfe]
    _ = ((-Real.log Real.pi : ℝ) : ℂ) *
          (∫ y, φ y * exp (-(-s) * (y : ℂ)) ∂volume)
        + deriv riemannZeta (1 - s) / riemannZeta (1 - s) *
          (∫ y, φ y * exp (-(-s) * (y : ℂ)) ∂volume)
        + (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) *
          (∫ y, φ y * exp (-(-s) * (y : ℂ)) ∂volume) := by
      ring

@[blueprint
  "kadiri-thm-3-1-q1-I-1"
  (title := "Kadiri's $I_1(T)$: the constant $\\log(1/\\pi)$ piece")
  (statement := /-- Kadiri's $I_1(T)$ from \cite[p.~12]{Kadiri2005}: the constant-prefactor
  piece of the functional-equation rewrite of the $\sigma = -a$ integral,
  $$ I_1(T) \;:=\; \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
                  \log\!\Big(\frac{1}{\pi}\Big)\, \Phi(-s)\, ds. $$
  Its $T \to \infty$ limit is given by \ref{kadiri-thm-3-1-q1-eq-13}. -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I_1 (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      ((-Real.log Real.pi : ℝ) : ℂ) *
        Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))

@[blueprint
  "kadiri-thm-3-1-q1-I-2"
  (title := "Kadiri's $I_2(T)$: the reflected Dirichlet-series piece")
  (statement := /-- Kadiri's $I_2(T)$ from \cite[p.~12]{Kadiri2005}: the reflected
  Dirichlet-series piece of the functional-equation rewrite of the $\sigma = -a$
  integral,
  $$ I_2(T) \;:=\; \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
                  \frac{\zeta'}{\zeta}(1-s)\, \Phi(-s)\, ds. $$

  \emph{Sign:} the $+\zeta'/\zeta(1-s)$ integrand comes from substituting the
  (corrected) functional equation
  $-\zeta'/\zeta(s) = -\log\pi + \zeta'/\zeta(1-s) + \tfrac{1}{2}\{\Gamma'/\Gamma(s/2)
  + \Gamma'/\Gamma((1-s)/2)\}$ (see \ref{kadiri-thm-3-1-q1-functional-eq}) into the
  integrand of the $\sigma = -a$ integral and reading off the middle term. The paper
  states the integrand with a leading minus, which is a typo (matching the sign typo
  in the functional equation on \cite[p.~12]{Kadiri2005}). Its $T \to \infty$ limit
  is given by \ref{kadiri-thm-3-1-q1-eq-14}. -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I_2 (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
        Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))

@[blueprint
  "kadiri-thm-3-1-q1-I-3"
  (title := "Kadiri's $I_3(T)$: the gamma-factor piece")
  (statement := /-- Kadiri's $I_3(T)$ from \cite[p.~12]{Kadiri2005}: the gamma-factor
  piece of the functional-equation rewrite of the $\sigma = -a$ integral,
  $$ I_3(T) \;:=\; \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
                  \frac{1}{2}\Big\{
                    \frac{\Gamma'}{\Gamma}\!\Big(\frac{s}{2}\Big)
                  + \frac{\Gamma'}{\Gamma}\!\Big(\frac{1-s}{2}\Big)
                  \Big\}\, \Phi(-s)\, ds. $$
  Its $T \to \infty$ limit is given by \ref{kadiri-thm-3-1-q1-eq-15}: shifting the
  contour to the critical line $\Re s = 1/2$ picks up a $+\Phi(0)$ residue at $s = 0$
  (from the pole of $\Gamma'/\Gamma(s/2)$ at the origin), and the
  $\Gamma'/\Gamma$-symmetrization (\ref{kadiri-thm-3-1-q1-gamma-symmetrization}) on
  $\Re s = 1/2$ collapses the two gamma terms into $\Re[\Gamma'/\Gamma(s/2)]$. -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I_3 (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      ((1 / 2 : ℂ) *
        (digamma ((((-a : ℝ) : ℂ) + (t : ℂ) * I) / 2)
         + digamma ((1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) / 2))) *
        Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))

/-- The finite-segment continuity of the gamma-factor coefficient on the shifted contour. -/
private def U1541ShiftedDigammaCoefficientContinuousHypothesis (a T : ℝ) : Prop :=
  ContinuousOn
    (fun t : ℝ =>
      (1 / 2 : ℂ) *
        (digamma ((((-a : ℝ) : ℂ) + (t : ℂ) * I) / 2)
         + digamma ((1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) / 2)))
    (Set.Icc (-T) T)

/-- The shifted contour avoids the digamma poles, so the gamma-factor coefficient is continuous
on every finite ordinate interval. -/
private theorem u1541_shifted_digamma_coefficient_continuous {a T : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    U1541ShiftedDigammaCoefficientContinuousHypothesis a T := by
  set z : ℝ → ℂ := fun t ↦ (((-a : ℝ) : ℂ) + (t : ℂ) * I) / 2
  set r : ℝ → ℂ := fun t ↦ (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) / 2
  have hz_cont : Continuous z := by
    dsimp [z]
    fun_prop
  have hr_cont : Continuous r := by
    dsimp [r]
    fun_prop
  have hz_shift_cont : Continuous fun t : ℝ => z t + 1 := hz_cont.add continuous_const
  have hψ_shift : Continuous fun t : ℝ => digamma (z t + 1) := by
    rw [continuous_iff_continuousAt]
    intro t
    refine (Complex.continuousAt_digamma_of_re_pos ?_).comp
      (hz_shift_cont.continuousAt (x := t))
    dsimp [z]
    norm_num [Complex.add_re, Complex.mul_re, Complex.div_re]
    linarith
  have hψ_ref : Continuous fun t : ℝ => digamma (r t) := by
    rw [continuous_iff_continuousAt]
    intro t
    refine (Complex.continuousAt_digamma_of_re_pos ?_).comp (hr_cont.continuousAt (x := t))
    dsimp [r]
    norm_num [Complex.add_re, Complex.mul_re, Complex.div_re]
    linarith
  have hz_inv_cont : ContinuousOn (fun t : ℝ => (z t)⁻¹) (Set.Icc (-T) T) := by
    exact hz_cont.continuousOn.inv₀ fun t _ht hzero => by
      have hre := congrArg Complex.re hzero
      dsimp [z] at hre
      norm_num [Complex.add_re, Complex.mul_re, Complex.div_re] at hre
      linarith
  have hrewrite : ContinuousOn
      (fun t : ℝ =>
        (1 / 2 : ℂ) * ((digamma (z t + 1) - (z t)⁻¹) + digamma (r t)))
      (Set.Icc (-T) T) := by
    exact continuousOn_const.mul ((hψ_shift.continuousOn.sub hz_inv_cont).add hψ_ref.continuousOn)
  refine hrewrite.congr fun t _ht => ?_
  have hpoles : ∀ n : ℕ, z t ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    dsimp [z] at hre
    norm_num [Complex.add_re, Complex.mul_re, Complex.div_re] at hre
    cases n with
    | zero =>
        norm_num at hre
        linarith
    | succ n =>
        have hn : (1 : ℝ) ≤ (Nat.succ n : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        norm_num at hre
        linarith
  have hrec : digamma (z t) = digamma (z t + 1) - (z t)⁻¹ := by
    have h := digamma_apply_add_one (z t) hpoles
    rw [h]
    ring
  dsimp [z, r]
  rw [hrec]

private lemma u1541_shifted_I3_summand_integrable_of_transform_continuous {φ : ℝ → ℂ}
    {a T : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hΦ : ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        Φ (-s))
      (Set.Icc (-T) T)) :
    Integrable (fun t : ℝ =>
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) * Φ (-s))
        (volume.restrict (Set.Ioo (-T) T)) := by
  have hΓ := u1541_shifted_digamma_coefficient_continuous (T := T) ha ha1
  have hcont : ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) * Φ (-s))
      (Set.Icc (-T) T) := by
    exact hΓ.mul hΦ
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self

private lemma kadiri_laplace_positive_line_weight_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b : ℝ}
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * ψ y) := by
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) * ψ y
  have hF_cont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF_loc : LocallyIntegrable F volume := hF_cont.locallyIntegrable
  have hshape : ∀ x : ℝ,
      ‖F x‖ = Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖ := by
    intro x
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : (-(↑a * ↑x) : ℂ).re = -a * x := by
      norm_num [Complex.mul_re]
    have h2 : ((x : ℂ) / 2).re = x / 2 := by
      norm_num
    rw [h1, h2]
    calc
      Real.exp (-a * x) * ‖ψ x‖
          = (Real.exp (-(a + 1 / 2) * x) * Real.exp (x / 2)) * ‖ψ x‖ := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ = Real.exp (-(a + 1 / 2) * x) * (‖ψ x‖ * Real.exp (x / 2)) := by ring_nf
  have htop_decay := hψ_decay.mono (show Filter.atTop ≤ Filter.cocompact ℝ from
    atTop_le_cocompact)
  have hbot_decay := hψ_decay.mono (show Filter.atBot ≤ Filter.cocompact ℝ from
    atBot_le_cocompact)
  have htop : F =O[Filter.atTop] fun x : ℝ => Real.exp (-(a + b + 1) * x) := by
    rw [Asymptotics.isBigO_iff] at htop_decay ⊢
    obtain ⟨C, hC⟩ := htop_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with x hxC hxpos
    rw [hshape]
    calc
      Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp (-(a + 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp (-(a + b + 1) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_pos hxpos]
            calc
              Real.exp (-(a + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * x))
                  = C * (Real.exp (-(a + 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * x)) := by ring_nf
              _ = C * Real.exp (-(a + 1 / 2) * x + (-(1 / 2 + b) * x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp (-(a + b + 1) * x) := by ring_nf
  have hbot : F =O[Filter.atBot] fun x : ℝ => Real.exp ((b - a) * x) := by
    rw [Asymptotics.isBigO_iff] at hbot_decay ⊢
    obtain ⟨C, hC⟩ := hbot_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
    rw [hshape]
    calc
      Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp (-(a + 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp ((b - a) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
            calc
              Real.exp (-(a + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * -x))
                  = C * (Real.exp (-(a + 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * -x)) := by ring_nf
              _ = C * Real.exp (-(a + 1 / 2) * x + (-(1 / 2 + b) * -x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp ((b - a) * x) := by ring_nf
  have htop_int : IntegrableAtFilter (fun x : ℝ => Real.exp (-(a + b + 1) * x))
      Filter.atTop volume := by
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    exact exp_neg_integrableOn_Ioi 0 (show 0 < a + b + 1 by linarith)
  have hbot_int : IntegrableAtFilter (fun x : ℝ => Real.exp ((b - a) * x))
      Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      convert! (MeasurableEquiv.neg ℝ).map_symm.symm using 1; simp
    rw [hvol, Function.comp_def]
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hab) using 1
    ext x
    ring_nf
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

private lemma kadiri_laplace_positive_line_weight_integrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
  kadiri_laplace_positive_line_weight_integrable_of_continuous hφ.continuous hφ_decay ha hab

private lemma kadiri_laplace_shifted_vertical_segment_continuousOn
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (_ha1 : a < 1) :
    ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        Φ (-s))
      (Set.Icc (-T) T) := by
  have h_weighted :
      Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
    kadiri_laplace_positive_line_weight_integrable hφ hφ_decay ha hab
  have hcont :=
    continuous_laplaceIntegral_verticalLine_of_integrable
      (f := φ) (sigma := a) hφ.continuous h_weighted
  refine hcont.continuousOn.congr ?_
  intro t _ht
  dsimp [laplaceIntegral]
  apply integral_congr_ae
  filter_upwards with y
  apply congrArg (fun z : ℂ => φ y * exp (-z * (y : ℂ)))
  simp [sub_eq_add_neg, add_comm]

private lemma u1541_shifted_I1_summand_integrable_of_transform_continuous {φ : ℝ → ℂ}
    {a T : ℝ}
    (hΦ : ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        Φ (-s))
      (Set.Icc (-T) T)) :
    Integrable (fun t : ℝ =>
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      ((-Real.log Real.pi : ℝ) : ℂ) * Φ (-s)) (volume.restrict (Set.Ioo (-T) T)) := by
  have hcont : ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        ((-Real.log Real.pi : ℝ) : ℂ) * Φ (-s))
      (Set.Icc (-T) T) := by
    exact continuousOn_const.mul hΦ
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self

private lemma u1541_reflected_zeta_logDeriv_continuous {a : ℝ} (ha : 0 < a) :
    Continuous fun t : ℝ =>
      deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro t
  let w : ℂ := 1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)
  have hw1 : w ≠ 1 := by
    intro h
    have hre : w.re = (1 : ℂ).re := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hζw : riemannZeta w ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [w]
    linarith
  have hquot : ContinuousAt (fun z : ℂ => deriv riemannZeta z / riemannZeta z) w :=
    (differentiableAt_deriv_riemannZeta hw1).continuousAt.div
      (differentiableAt_riemannZeta hw1).continuousAt hζw
  have hpath : ContinuousAt (fun x : ℝ =>
      1 - (((-a : ℝ) : ℂ) + (x : ℂ) * I)) t := by
    fun_prop
  have hcomp := ContinuousAt.comp_of_eq hquot hpath (by simp [w])
  simpa [Function.comp_def] using hcomp

private lemma u1541_shifted_I2_summand_integrable_of_transform_continuous {φ : ℝ → ℂ}
    {a T : ℝ} (ha : 0 < a)
    (hΦ : ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        Φ (-s))
      (Set.Icc (-T) T)) :
    Integrable (fun t : ℝ =>
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      (deriv riemannZeta (1 - s) / riemannZeta (1 - s)) * Φ (-s))
        (volume.restrict (Set.Ioo (-T) T)) := by
  have hζ : ContinuousOn
      (fun t : ℝ =>
        deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)))
      (Set.Icc (-T) T) :=
    (u1541_reflected_zeta_logDeriv_continuous ha).continuousOn
  have hcont : ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        (deriv riemannZeta (1 - s) / riemannZeta (1 - s)) * Φ (-s))
      (Set.Icc (-T) T) := by
    exact hζ.mul hΦ
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self

/-- Algebraic split of the shifted contour integral into `I_1 + I_2 + I_3`, once the
pointwise functional-equation identity and the three finite-segment integrability facts
are supplied. This isolates the formal content of
`kadiri_thm_3_1_q1_shifted_eq_I123` from the separate analytic obligations. -/
private theorem kadiri_thm_3_1_q1_shifted_eq_I123_of_pointwise_integrable
    {φ : ℝ → ℂ} {a T : ℝ}
    (hpoint : ∀ t ∈ Set.Ioo (-T) T,
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      (-deriv riemannZeta s / riemannZeta s) * Φ (-s) =
        ((-Real.log Real.pi : ℝ) : ℂ) * Φ (-s)
          + (deriv riemannZeta (1 - s) / riemannZeta (1 - s)) * Φ (-s)
          + ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) * Φ (-s))
    (hI1 : Integrable (fun t : ℝ =>
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      ((-Real.log Real.pi : ℝ) : ℂ) * Φ (-s)) (volume.restrict (Set.Ioo (-T) T)))
    (hI2 : Integrable (fun t : ℝ =>
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      (deriv riemannZeta (1 - s) / riemannZeta (1 - s)) * Φ (-s))
        (volume.restrict (Set.Ioo (-T) T)))
    (hI3 : Integrable (fun t : ℝ =>
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) * Φ (-s))
        (volume.restrict (Set.Ioo (-T) T))) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ t in Set.Ioo (-T) T,
        (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
            riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
          Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))) =
      kadiri_thm_3_1_q1_I_1 φ a T
      + kadiri_thm_3_1_q1_I_2 φ a T
      + kadiri_thm_3_1_q1_I_3 φ a T := by
  dsimp
  set S : Set ℝ := Set.Ioo (-T) T
  set Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  set c : ℂ := 1 / (2 * (Real.pi : ℂ))
  set f0 : ℝ → ℂ := fun t ↦
    (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
      Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))
  set f1 : ℝ → ℂ := fun t ↦
    ((-Real.log Real.pi : ℝ) : ℂ) *
      Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))
  set f2 : ℝ → ℂ := fun t ↦
    (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
      Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))
  set f3 : ℝ → ℂ := fun t ↦
    ((1 / 2 : ℂ) *
      (digamma ((((-a : ℝ) : ℂ) + (t : ℂ) * I) / 2)
       + digamma ((1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) / 2))) *
      Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))
  change c * (∫ t in S, f0 t) =
    c * (∫ t in S, f1 t) + c * (∫ t in S, f2 t) + c * (∫ t in S, f3 t)
  have hf1 : Integrable f1 (volume.restrict S) := by
    simpa [S, Φ, f1] using hI1
  have hf2 : Integrable f2 (volume.restrict S) := by
    simpa [S, Φ, f2] using hI2
  have hf3 : Integrable f3 (volume.restrict S) := by
    simpa [S, Φ, f3] using hI3
  have hcong : ∫ t in S, f0 t = ∫ t in S, (f1 t + f2 t) + f3 t := by
    refine setIntegral_congr_fun (by simp [S]) ?_
    intro t ht
    have h := hpoint t (by simpa [S] using ht)
    simpa [Φ, f0, f1, f2, f3, add_assoc] using h
  have hadd :
      ∫ t in S, (f1 t + f2 t) + f3 t =
        (∫ t in S, f1 t) + (∫ t in S, f2 t) + (∫ t in S, f3 t) := by
    rw [MeasureTheory.integral_add (f := fun t ↦ f1 t + f2 t) (g := f3)
        (hf1.add hf2) hf3,
      MeasureTheory.integral_add (f := f1) (g := f2) hf1 hf2]
  calc
    c * (∫ t in S, f0 t) =
        c * ((∫ t in S, f1 t) + (∫ t in S, f2 t) + (∫ t in S, f3 t)) := by
      rw [hcong, hadd]
    _ = c * (∫ t in S, f1 t)
        + c * (∫ t in S, f2 t)
        + c * (∫ t in S, f3 t) := by
      ring

/-- Conditional shifted-contour decomposition with the digamma continuity atom discharged.
The remaining finite-segment inputs are the Laplace-transform continuity and the `I₁`/`I₂`
integrability facts supplied by the Laplace side. -/
private theorem kadiri_thm_3_1_q1_shifted_eq_I123_of_transform_continuous
    {φ : ℝ → ℂ} {a T : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hΦ : ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        Φ (-s))
      (Set.Icc (-T) T))
    (hI1 : Integrable (fun t : ℝ =>
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      ((-Real.log Real.pi : ℝ) : ℂ) * Φ (-s)) (volume.restrict (Set.Ioo (-T) T)))
    (hI2 : Integrable (fun t : ℝ =>
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
      (deriv riemannZeta (1 - s) / riemannZeta (1 - s)) * Φ (-s))
        (volume.restrict (Set.Ioo (-T) T))) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ t in Set.Ioo (-T) T,
        (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
            riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
          Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))) =
      kadiri_thm_3_1_q1_I_1 φ a T
      + kadiri_thm_3_1_q1_I_2 φ a T
      + kadiri_thm_3_1_q1_I_3 φ a T := by
  exact kadiri_thm_3_1_q1_shifted_eq_I123_of_pointwise_integrable
    (kadiri_thm_3_1_q1_shifted_pointwise_functional_eq ha ha1)
    hI1 hI2 (u1541_shifted_I3_summand_integrable_of_transform_continuous ha ha1 hΦ)

@[blueprint
  "kadiri-thm-3-1-q1-shifted-eq-I123"
  (title := "Functional-equation decomposition of the $\\sigma = -a$ integral")
  (statement := /-- Under the hypotheses of \ref{kadiri-thm-3-1-q1-eq-11}: for every
  $T > 0$,
  $$ \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
       \!\!\!\! \left(-\frac{\zeta'}{\zeta}\right)\!(s)\, \Phi(-s)\, ds
     \;=\; I_1(T) + I_2(T) + I_3(T), $$
  where $I_1, I_2, I_3$ are the three pieces produced by applying
  \ref{kadiri-thm-3-1-q1-functional-eq} to the integrand. -/)
  (proof := /-- Apply \ref{kadiri-thm-3-1-q1-functional-eq} pointwise inside the
  integral. The hypotheses of the functional equation hold on the entire contour
  $\sigma = -a$: $s = -a + it \neq 1$ (since $\Re s = -a \leq 0$), $s \neq 0$ (since
  $a > 0$), $s \notin Z(\zeta)$ (since $\Re s = -a < 0$ but non-trivial zeros have
  $\Re \rho \in (0, 1)$), and $1 - s \notin Z(\zeta)$ (since $\Re(1 - s) = 1 + a > 1$).
  Linearity of the integral splits it into the three pieces of the definitions of
  $I_1, I_2, I_3$. To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1541)]
theorem kadiri_thm_3_1_q1_shifted_eq_I123
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (T : ℝ) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ t in Set.Ioo (-T) T,
        (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
            riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
          Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))) =
      kadiri_thm_3_1_q1_I_1 φ a T
      + kadiri_thm_3_1_q1_I_2 φ a T
      + kadiri_thm_3_1_q1_I_3 φ a T := by
  have hΦ := kadiri_laplace_shifted_vertical_segment_continuousOn
    (φ := φ) hφ hb hφ_decay ha hab ha1 (T := T)
  exact kadiri_thm_3_1_q1_shifted_eq_I123_of_transform_continuous ha ha1 hΦ
    (u1541_shifted_I1_summand_integrable_of_transform_continuous hΦ)
    (u1541_shifted_I2_summand_integrable_of_transform_continuous ha hΦ)

@[blueprint
  "kadiri-thm-3-1-q1-eq-13"
  (title := "Equation (13) of \\cite{Kadiri2005}: limit of $I_1(T)$")
  (statement := /-- Under the hypotheses of \ref{kadiri-thm-3-1-q1-eq-11}:
  $$ \lim_{T \to \infty} I_1(T) \;=\; \varphi(0)\, \log\!\Big(\frac{1}{\pi}\Big)
                                   \;=\; -\,\varphi(0)\, \log \pi. $$
  Specialization of equation~(13) of \cite{Kadiri2005}, page~12, to $q = 1$ (so
  $\log(q/\pi) = -\log\pi$). -/)
  (proof := /-- The constant prefactor $\log(1/\pi)$ pulls out of the integral. The
  remaining $\tfrac{1}{2\pi i} \int_{-a - iT}^{-a + iT} \Phi(-s)\, ds$ tends to
  $\varphi(0)$ as $T \to \infty$ by the Laplace-inversion identity at $y = 0$
  (\ref{kadiri-thm-3-1-q1-laplace-inversion} specialized to $n = 1$, with a
  change of variable $s \mapsto -s$ that maps the $\sigma = -a$ contour back to
  $\sigma = a$). To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1542)]
theorem kadiri_thm_3_1_q1_eq_13
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_1 φ a T)
      Filter.atTop (nhds (φ 0 * ((-Real.log Real.pi : ℝ) : ℂ))) := by
  sorry

@[blueprint
  "kadiri-thm-3-1-q1-eq-14"
  (title := "Equation (14) of \\cite{Kadiri2005}: limit of $I_2(T)$")
  (statement := /-- Under the hypotheses of \ref{kadiri-thm-3-1-q1-eq-11}:
  $$ \lim_{T \to \infty} I_2(T) \;=\;
       -\sum_{n \geq 1} \frac{\Lambda(n)}{n}\, \varphi(-\log n). $$
  Specialization of equation~(14) of \cite{Kadiri2005}, page~12, to $q = 1$ (so
  $\bar\chi = \chi = 1$ and the reflected Dirichlet series reduces to
  $\sum_n \Lambda(n)/n^{1-s}$).

  \emph{Sign correction:} The paper states this limit as $+\sum_n \Lambda(n)/n
  \cdot \varphi(-\log n)$, but this is a downstream consequence of the sign typo in
  the paper's functional equation on \cite[p.~12]{Kadiri2005}, which we correct in
  \ref{kadiri-thm-3-1-q1-functional-eq}. With the corrected functional equation
  (sign $+\zeta'/\zeta(1-s)$ rather than $-\zeta'/\zeta(1-s)$), $I_2(T)$ has
  integrand $+\zeta'/\zeta(1-s)\, \Phi(-s)$, the Dirichlet expansion contributes
  an extra minus sign, and the limit picks up the corresponding minus. See the
  parallel correction in \ref{kadiri-thm-3-1-q1}'s main statement (the
  $-\sum_n \Lambda(n)/n \cdot \varphi(-\log n)$ term). -/)
  (proof := /-- On the contour $\sigma = -a$, write $1 - s = (1 + a) - i\Im s$ so
  $\Re(1 - s) = 1 + a > 1$, and use the Dirichlet series
  $\zeta'/\zeta(1-s) = -\sum_n \Lambda(n) n^{-(1-s)}$ (von Mangoldt with a leading
  minus). The integrand $\zeta'/\zeta(1-s)\, \Phi(-s)$ thus expands as
  $-\sum_n \Lambda(n) n^{-(1-s)} \Phi(-s)$. Exchange sum and integral (justified by
  absolute convergence and the $O(1/|t|)$ decay of $\Phi$); apply
  \ref{kadiri-thm-3-1-q1-laplace-inversion} at $y = -\log n$ to identify the inner
  integral as $n^a \varphi(-\log n)$, and combine with the $n^{-(1+a)}$ from the
  Dirichlet series and the overall minus to get $-\sum_n (\Lambda(n)/n)\,
  \varphi(-\log n)$. To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1543)]
theorem kadiri_thm_3_1_q1_eq_14
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  sorry

/-- The digamma function commutes with complex conjugation. Mathlib's junk-value
conventions make this unconditional: `Complex.Gamma_conj` holds at every point,
`deriv` returns `0` at non-differentiable points on both sides of the symmetry,
and `conj` fixes `0`. In the application below the argument `s / 2` has real
part `1 / 4`, away from the poles of `Γ` in any case. -/
private lemma digamma_conj (z : ℂ) :
    digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (digamma z) := by
  have hΓ : (starRingEnd ℂ) ∘ Gamma ∘ (starRingEnd ℂ) = Gamma := by
    funext w
    simp [Function.comp_apply, Gamma_conj]
  have hd : deriv Gamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv Gamma z) := by
    conv_lhs => rw [← hΓ, deriv_conj_conj]
    simp [Function.comp_apply]
  rw [digamma_def, logDeriv_apply, logDeriv_apply, hd, Gamma_conj, ← map_div₀]

@[blueprint
  "kadiri-thm-3-1-q1-gamma-symmetrization"
  (title := "$\\Gamma'/\\Gamma$ symmetrization on the critical line")
  (statement := /-- For every $s \in \mathbb{C}$ with $\Re s = 1/2$,
  $$ \frac{1}{2}\!\left\{
       \frac{\Gamma'}{\Gamma}\!\Big(\frac{s}{2}\Big)
     + \frac{\Gamma'}{\Gamma}\!\Big(\frac{1-s}{2}\Big)
       \right\}
     \;=\; \Re\!\left[\frac{\Gamma'}{\Gamma}\!\Big(\frac{s}{2}\Big)\right]. $$
  Used to identify the integrand of $I_3$ after shifting to the critical line
  (\cite[p.~13]{Kadiri2005}, displayed equation between (14) and (15)). -/)
  (proof := /-- On $\Re s = 1/2$, $1 - s = \bar s$, hence $(1 - s)/2 = \overline{s/2}$.
  Since $\Gamma'/\Gamma$ has real Taylor coefficients away from its poles, it commutes
  with complex conjugation: $\Gamma'/\Gamma((1-s)/2) = \overline{\Gamma'/\Gamma(s/2)}$.
  Then $\tfrac{1}{2}(z + \bar z) = \Re z$ with $z = \Gamma'/\Gamma(s/2)$. To be
  formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1544)]
theorem kadiri_thm_3_1_q1_gamma_symmetrization {s : ℂ} (_hs : s.re = 1 / 2) :
    (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) =
      ((digamma (s / 2)).re : ℂ) := by
  have h1s : 1 - s = (starRingEnd ℂ) s := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, _hs]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring
  have hconj : (1 - s) / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, map_ofNat, h1s]
  rw [hconj, digamma_conj, Complex.add_conj]
  push_cast
  ring

@[blueprint
  "kadiri-thm-3-1-q1-eq-15"
  (title := "Equation (15) of \\cite{Kadiri2005}: limit of $I_3(T)$")
  (statement := /-- Under the hypotheses of \ref{kadiri-thm-3-1-q1-eq-11}:
  $$ \lim_{T \to \infty} I_3(T) \;=\;
       \Phi(0)
       \;+\; \frac{1}{2 \pi i}
              \int_{1/2 - i\infty}^{1/2 + i\infty}
                \Re\!\left[\frac{\Gamma'}{\Gamma}\!\Big(\frac{s}{2}\Big)\right]
                  \Phi(-s)\, ds. $$
  Specialization of equation~(15) of \cite{Kadiri2005}, page~13, to $q = 1$
  ($\mathfrak{a} = 0$, so $(1 - \mathfrak{a})\Phi(0) = \Phi(0)$ in Kadiri's
  $\mathfrak{a}$-dependent form). -/)
  (proof := /-- Shift the contour of $I_3(T)$ from $\sigma = -a$ to $\sigma = 1/2$.
  The integrand $\tfrac{1}{2}\{\Gamma'/\Gamma(s/2) + \Gamma'/\Gamma((1-s)/2)\}\, \Phi(-s)$
  has a simple pole at $s = 0$ from $\Gamma'/\Gamma(s/2) \sim -2/s$ near $s = 0$, with
  residue $+\Phi(0)$ contributed by the leftward shift; no other poles lie in
  $-a < \Re s < 1/2$. The horizontal arcs vanish as $T \to \infty$ by (B). On
  $\Re s = 1/2$, apply \ref{kadiri-thm-3-1-q1-gamma-symmetrization} to identify the
  integrand as $\Re[\Gamma'/\Gamma(s/2)]\, \Phi(-s)$. The Bochner integral in the limit
  value is well-defined precisely under the explicit integrability hypothesis on the
  $\Gamma$-contour integrand (otherwise the integral evaluates to $0$ by Mathlib's
  convention and the statement is vacuous); this same hypothesis is carried by
  \ref{kadiri-thm-3-1-q1}. To be formalised. -/)
  (latexEnv := "sublemma")
  (discussion := 1545)]
theorem kadiri_thm_3_1_q1_eq_15
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (_hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_3 φ a T)
      Filter.atTop
      (nhds (Φ 0
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I)))) := by
  sorry

/-! ## Theorem 3.1 of \cite{Kadiri2005}, specialized to $q = 1$, $\chi$ trivial

Composition of the eleven sublemmas above. -/

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
       - \sum_{n \geq 1} \tfrac{\Lambda(n)}{n}\, \varphi(-\log n)
       + \tfrac{1}{2 \pi i} \int_{1/2 - i\infty}^{1/2 + i\infty}
           \Re \tfrac{\Gamma'}{\Gamma}\!\left( \tfrac{z}{2} \right) \Phi(-z)\, dz, $$
  where the $\rho$-sum runs over the non-trivial zeros of $\zeta$.

  This is the $q = 1$, $\chi$ trivial case of the Weil-type explicit formula of
  \cite[Theorem 3.1]{Kadiri2005}. The $\Phi(-1)$ term comes from the simple pole of $\zeta$
  at $z = 1$ (and is absent for non-trivial $\chi$); the $\varphi(0)\log\pi$ term and the
  $\Gamma$-integral come from the gamma factor in the functional equation of $\zeta$; the
  $-\sum_n \tfrac{\Lambda(n)}{n}\varphi(-\log n)$ term is the contribution from the
  reflected ($z \leftrightarrow 1 - z$) Dirichlet series.

  \emph{Typo correction:} \cite[Theorem 3.1, p.~11]{Kadiri2005} states this identity with
  $+\sum_n \tfrac{\Lambda(n)}{n}\varphi(-\log n)$ (positive sign), but this is a downstream
  consequence of the sign typo in the paper's functional equation on \cite[p.~12]{Kadiri2005}
  (see \ref{kadiri-thm-3-1-q1-functional-eq}). Numerical verification (e.g.\ at $s = 2$)
  confirms the sign here is negative. The paper's downstream applications, including
  equation (16) and the chapter's main zero-free-region argument, are unaffected by this
  typo because they specialize to a test function for which $\varphi(-\log n) = 0$ for all
  $n \geq 1$. -/)
  (proof := /-- Composition of the eleven preceding sublemmas. Pick any
  $0 < a < \min(b, 1)$ and any $T > 0$.

  By \ref{kadiri-thm-3-1-q1-eq-11} the LHS equals
  $\tfrac{1}{2\pi i} \int_{(1+a)} (-\zeta'/\zeta)(s)\, \Phi(-s)\, ds$, which is the
  $T \to \infty$ limit of \ref{kadiri-thm-3-1-q1-I}'s $I(T)$ by dominated convergence on
  the $O(1/|t|)$ decay of $\Phi$.

  By \ref{kadiri-thm-3-1-q1-eq-12} this $I(T)$ equals the sum of the $\sigma = -a$
  integral, the two horizontal arcs, $\Phi(-1)$, and the truncated $\rho$-sum
  $\sum_{|\Im\rho| < T} \Phi(-\rho)$. The two horizontals vanish in the limit by
  \ref{kadiri-thm-3-1-q1-top-horizontal-vanishes} and
  \ref{kadiri-thm-3-1-q1-bot-horizontal-vanishes}, while the truncated $\rho$-sum
  extends to the full $\sum_{\rho \in Z(\zeta)} \Phi(-\rho)$ as $T \to \infty$
  (using summability of the complex sum).

  The $\sigma = -a$ integral equals $I_1(T) + I_2(T) + I_3(T)$ by
  \ref{kadiri-thm-3-1-q1-shifted-eq-I123}, with $T \to \infty$ limits given by
  \ref{kadiri-thm-3-1-q1-eq-13} ($\to -\varphi(0) \log\pi$),
  \ref{kadiri-thm-3-1-q1-eq-14} ($\to -\sum_n \tfrac{\Lambda(n)}{n}\varphi(-\log n)$),
  and \ref{kadiri-thm-3-1-q1-eq-15} ($\to \Phi(0) +
  \tfrac{1}{2\pi i} \int_{(1/2)} \Re[\Gamma'/\Gamma(s/2)]\, \Phi(-s)\, ds$).

  Combining yields the stated identity. The residual `sorry` covers the remaining
  technical limit-management steps (interchange of $T \to \infty$ with the integrals
  and the $\rho$-sum); the sublemma signatures already type-check the composition. -/)
  (latexEnv := "theorem")
  (discussion := 1546)]
theorem kadiri_thm_3_1_q1 {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hΦ_sum : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (∫ y, φ y * exp (ρ.val * (y : ℂ)) ∂volume) *
        (riemannZeta.order ρ.val : ℂ)))
    (hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    let Φ : ℂ → ℂ := fun z ↦ ∫ y, φ y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      Φ (-1) + Φ 0
        - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ Φ (-ρ))
        - φ 0 * ((Real.log Real.pi : ℝ) : ℂ)
        - ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I)) := by
  intro Φ
  -- Pick `a := (min b 1) / 2` so that `0 < a < min(b, 1)`.
  have hbmin1 : 0 < min b 1 := lt_min hb one_pos
  set a : ℝ := min b 1 / 2 with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; linarith
  have ha_lt_b : a < b := by
    rw [ha_def]
    have h : min b 1 ≤ b := min_le_left b 1
    linarith
  have ha_lt_1 : a < 1 := by
    rw [ha_def]
    have h : min b 1 ≤ 1 := min_le_right b 1
    linarith
  -- Each sublemma's conclusion, ready for assembly:
  -- · `heq11`: LHS as Mellin contour integral on σ = 1 + a (kadiri-thm-3-1-q1-eq-11).
  have heq11 :=
    kadiri_thm_3_1_q1_eq_11 hφ hb hφ_decay hφ'_decay ha_pos ha_lt_b ha_lt_1
  -- · `htop`, `hbot`: horizontal integrals → 0 as T → ∞.
  have htop :=
    kadiri_thm_3_1_q1_top_horizontal_vanishes
      hφ hb hφ_decay hφ'_decay ha_pos ha_lt_b ha_lt_1
  have hbot :=
    kadiri_thm_3_1_q1_bot_horizontal_vanishes
      hφ hb hφ_decay hφ'_decay ha_pos ha_lt_b ha_lt_1
  -- · `h13`, `h14`, `h15`: limits of I₁(T), I₂(T), I₃(T) as T → ∞.
  have h13 :=
    kadiri_thm_3_1_q1_eq_13 hφ hb hφ_decay hφ'_decay ha_pos ha_lt_b ha_lt_1
  have h14 :=
    kadiri_thm_3_1_q1_eq_14 hφ hb hφ_decay hφ'_decay ha_pos ha_lt_b ha_lt_1
  have h15 :=
    kadiri_thm_3_1_q1_eq_15 hφ hb hφ_decay hφ'_decay ha_pos ha_lt_b ha_lt_1 hΓ_int
  -- The two intermediate limit facts; both are technical limit-management steps left as
  -- `sorry` for now (dominated convergence + summability across the $T \to \infty$ limit).

  -- (i) `lim_{T → ∞} I(T) = ∑' Λ(n) φ(log n)`. The truncated integral defining `I(T)`
  -- approaches the un-truncated integral on $\sigma = 1 + a$ by dominated convergence on
  -- the $O(1/|t|)$ decay of $\Phi$ from (B); the latter integral equals the LHS by `heq11`.
  have lim_I_from_eq11 :
      Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I φ a T) Filter.atTop
        (nhds (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
    sorry

  -- (ii) `lim_{T → ∞} I(T) = (the assembled RHS pieces)`. By `heq12` (the rectangle
  -- decomposition), `I(T)` splits into the $\sigma = -a$ integral + the two horizontals
  -- + $\Phi(-1)$ + the truncated $\rho$-sum. The two horizontals vanish in the limit
  -- (`htop`, `hbot`), the $\sigma = -a$ piece splits as $I_1 + I_2 + I_3$
  -- (`kadiri_thm_3_1_q1_shifted_eq_I123`) whose limits are given by `h13, h14, h15`,
  -- and the truncated $\rho$-sum extends to the full sum (by summability).
  have lim_I_from_pieces :
      Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I φ a T) Filter.atTop
        (nhds
          (φ 0 * ((-Real.log Real.pi : ℝ) : ℂ)
          + (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))
          + (Φ 0
            + (1 / (2 * (Real.pi : ℂ))) *
                ∫ t : ℝ,
                  ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                    Φ (-(1 / 2 + (t : ℂ) * I)))
          + Φ (-1)
          - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ Φ (-ρ)))) := by
    sorry

  -- The two limits agree (both are `lim I(T)`), giving the desired equation.
  have heq := tendsto_nhds_unique lim_I_from_eq11 lim_I_from_pieces
  rw [heq]
  push_cast
  -- `ring_nf` normalizes the outer arithmetic, but cannot reach inside the opaque
  -- `Φ(...)` and `(digamma _).re` applications. The remaining difference is purely
  -- `mul_comm` on `(t : ℂ) * I` vs `I * (t : ℂ)` inside the integrand; unify by an
  -- explicit `simp_rw` before normalization.
  simp_rw [show ∀ (t : ℝ), (t : ℂ) * I = I * (t : ℂ) from fun _ => mul_comm _ _]
  ring

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
private lemma laplaceKernel_hasDerivAt (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => exp (-w * (y : ℂ)))
      (-w * exp (-w * (x : ℂ))) x := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id x).ofReal_comp.const_mul (-w)).cexp

private lemma laplaceKernel_antideriv_hasDerivAt {w : ℂ} (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -exp (-w * (y : ℂ)) / w)
      (exp (-w * (x : ℂ))) x := by
  have h := (laplaceKernel_hasDerivAt w x).neg.div_const w
  convert! h using 1
  field_simp [hw]

private lemma eq_zero_of_tsupport_subset_Ico_right {d : ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (hdx : d ≤ x) :
    f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  exact not_lt_of_ge hdx (hf_supp hx).2

private lemma deriv_eq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ}
    (hx : x ∉ tsupport f) : deriv f x = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have hmem : (tsupport f)ᶜ ∈ nhds x := hopen.mem_nhds hx
  have hzero : f =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [hmem] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [Filter.EventuallyEq.deriv_eq hzero, deriv_const]

private lemma deriv_deriv_eq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ}
    (hx : x ∉ tsupport f) : deriv (deriv f) x = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have hmem : (tsupport f)ᶜ ∈ nhds x := hopen.mem_nhds hx
  have hzero : deriv f =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [hmem] with y hy
    exact deriv_eq_zero_of_notMem_tsupport hy
  rw [Filter.EventuallyEq.deriv_eq hzero, deriv_const]

private lemma deriv_deriv_eq_zero_of_tsupport_subset_Ico {d : ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (hdx : d ≤ x) :
    deriv (deriv f) x = 0 := by
  apply deriv_deriv_eq_zero_of_notMem_tsupport
  intro hx
  exact not_lt_of_ge hdx (hf_supp hx).2

private lemma laplaceTransform_eq_interval_of_tsupport_subset_Ico {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ Set.Ico 0 d) (w : ℂ) :
    laplaceTransform f w =
      ∫ t in (0 : ℝ)..d, exp (-w * (t : ℂ)) * (f t : ℂ) := by
  unfold laplaceTransform
  rw [intervalIntegral.integral_of_le hd.le]
  exact setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self (fun x hx => by
      have hxpos : 0 < x := hx.1
      have hdx : d ≤ x := by
        by_contra hnot
        exact hx.2 ⟨hxpos, le_of_not_ge hnot⟩
      simp [eq_zero_of_tsupport_subset_Ico_right hf_supp hdx])

private lemma laplaceTransform_deriv_deriv_eq_interval_of_tsupport_subset_Ico {d : ℝ}
    (hd : 0 < d) {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ Set.Ico 0 d) (w : ℂ) :
    laplaceTransform (fun u => deriv (deriv f) u) w =
      ∫ t in (0 : ℝ)..d,
        exp (-w * (t : ℂ)) * ((deriv (deriv f) t : ℝ) : ℂ) := by
  unfold laplaceTransform
  rw [intervalIntegral.integral_of_le hd.le]
  exact setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self (fun x hx => by
      have hxpos : 0 < x := hx.1
      have hdx : d ≤ x := by
        by_contra hnot
        exact hx.2 ⟨hxpos, le_of_not_ge hnot⟩
      simp [deriv_deriv_eq_zero_of_tsupport_subset_Ico hf_supp hdx])

theorem laplaceTransform_ibp {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0)
    {w : ℂ} (hw : w ≠ 0) :
    laplaceTransform f w =
      (f 0 : ℂ) / w + laplaceTransform (fun u => deriv (deriv f) u) w / w ^ 2 := by
  let I : Set ℝ := Set.Icc 0 d
  let K : ℝ → ℂ := fun t => exp (-w * (t : ℂ))
  let A : ℝ → ℂ := fun t => -K t / w
  let df : ℝ → ℝ := fun t => derivWithin f I t
  let d2f : ℝ → ℝ := fun t => derivWithin df I t
  have hdf_C1 : ContDiffOn ℝ 1 df I := by
    simpa [df, I] using hf_C2.derivWithin (uniqueDiffOn_Icc hd) (by norm_num)
  have hK_int : IntervalIntegrable K volume 0 d := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hdf_int : IntervalIntegrable (fun t => (df t : ℂ)) volume 0 d := by
    have hdf_cont : ContinuousOn (fun t => (df t : ℂ)) (Set.uIcc (0 : ℝ) d) := by
      have hreal : ContinuousOn df I :=
        hdf_C1.continuousOn
      simpa [I, Set.uIcc_of_le hd.le] using! continuous_ofReal.comp_continuousOn hreal
    exact hdf_cont.intervalIntegrable
  have hd2f_int : IntervalIntegrable (fun t => (d2f t : ℂ)) volume 0 d := by
    have hd2f_cont : ContinuousOn (fun t => (d2f t : ℂ)) (Set.uIcc (0 : ℝ) d) := by
      have hreal : ContinuousOn d2f I := by
        simpa [d2f] using hdf_C1.continuousOn_derivWithin (uniqueDiffOn_Icc hd) (by norm_num)
      simpa [I, Set.uIcc_of_le hd.le] using! continuous_ofReal.comp_continuousOn hreal
    exact hd2f_cont.intervalIntegrable
  have hA_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) d, HasDerivWithinAt A (K x) (Set.uIcc (0 : ℝ) d) x := by
    intro x _hx
    simpa [A, K] using (laplaceKernel_antideriv_hasDerivAt (w := w) hw x).hasDerivWithinAt
  have hf_deriv :
      ∀ x ∈ Set.uIcc (0 : ℝ) d,
        HasDerivWithinAt (fun y : ℝ => (f y : ℂ)) ((df x : ℝ) : ℂ) (Set.uIcc (0 : ℝ) d) x := by
    intro x hx
    have hxI : x ∈ I := by
      simpa [I, Set.uIcc_of_le hd.le] using hx
    have hreal : HasDerivWithinAt f (df x) I x := by
      simpa [df] using (hf_C2.differentiableOn (by norm_num) x hxI).hasDerivWithinAt
    simpa [I, Set.uIcc_of_le hd.le] using hreal.ofReal_comp
  have hdf_deriv :
      ∀ x ∈ Set.uIcc (0 : ℝ) d,
        HasDerivWithinAt (fun y : ℝ => ((df y : ℝ) : ℂ)) ((d2f x : ℝ) : ℂ)
          (Set.uIcc (0 : ℝ) d) x := by
    intro x hx
    have hxI : x ∈ I := by
      simpa [I, Set.uIcc_of_le hd.le] using hx
    have hreal : HasDerivWithinAt df (d2f x) I x := by
      simpa [d2f] using (hdf_C1.differentiableOn (by norm_num) x hxI).hasDerivWithinAt
    simpa [I, Set.uIcc_of_le hd.le] using hreal.ofReal_comp
  have hA_df :
      ∫ t in (0 : ℝ)..d, A t * (df t : ℂ) =
        -(∫ t in (0 : ℝ)..d, K t * (df t : ℂ)) / w := by
    calc
      ∫ t in (0 : ℝ)..d, A t * (df t : ℂ)
          = ∫ t in (0 : ℝ)..d, -(K t * (df t : ℂ)) / w := by
            apply intervalIntegral.integral_congr
            intro t _ht
            simp [A]
            ring
      _ = -(∫ t in (0 : ℝ)..d, K t * (df t : ℂ)) / w := by
            rw [intervalIntegral.integral_div, intervalIntegral.integral_neg]
  have hA_d2f :
      ∫ t in (0 : ℝ)..d, A t * (d2f t : ℂ) =
        -(∫ t in (0 : ℝ)..d, K t * (d2f t : ℂ)) / w := by
    calc
      ∫ t in (0 : ℝ)..d, A t * (d2f t : ℂ)
          = ∫ t in (0 : ℝ)..d, -(K t * (d2f t : ℂ)) / w := by
            apply intervalIntegral.integral_congr
            intro t _ht
            simp [A]
            ring
      _ = -(∫ t in (0 : ℝ)..d, K t * (d2f t : ℂ)) / w := by
            rw [intervalIntegral.integral_div, intervalIntegral.integral_neg]
  have hibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := d) (u := A) (v := fun t : ℝ => (f t : ℂ))
    (u' := K) (v' := fun t : ℝ => (df t : ℂ)) hA_deriv hf_deriv hK_int hdf_int
  have hfirst :
      ∫ t in (0 : ℝ)..d, K t * (f t : ℂ) =
        (f 0 : ℂ) / w + (∫ t in (0 : ℝ)..d, K t * (df t : ℂ)) / w := by
    have hsolve :
        ∫ t in (0 : ℝ)..d, K t * (f t : ℂ) =
          A d * (f d : ℂ) - A 0 * (f 0 : ℂ) -
            ∫ t in (0 : ℝ)..d, A t * (df t : ℂ) := by
      rw [hibp1]
      abel
    rw [hsolve, hA_df, hf_d]
    simp [A, K]
    field_simp [hw]
    ring
  have hibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := d) (u := A) (v := fun t : ℝ => ((df t : ℝ) : ℂ))
    (u' := K) (v' := fun t : ℝ => (d2f t : ℂ)) hA_deriv hdf_deriv hK_int hd2f_int
  have hsecond :
      ∫ t in (0 : ℝ)..d, K t * (df t : ℂ) =
        (∫ t in (0 : ℝ)..d, K t * (d2f t : ℂ)) / w := by
    have hsolve :
        ∫ t in (0 : ℝ)..d, K t * (df t : ℂ) =
          A d * (df d : ℂ) - A 0 * (df 0 : ℂ) -
            ∫ t in (0 : ℝ)..d, A t * (d2f t : ℂ) := by
      rw [hibp2]
      abel
    have hdf0 : df 0 = 0 := by simpa [df, I] using hf_derivWithin_0
    have hdfd : df d = 0 := by simpa [df, I] using hf_derivWithin_d
    rw [hsolve, hA_d2f, hdf0, hdfd]
    simp [A, K]
    field_simp [hw]
  have hd2f_interval_eq :
      ∫ t in (0 : ℝ)..d, K t * (d2f t : ℂ) =
        ∫ t in (0 : ℝ)..d, K t * ((deriv (deriv f) t : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le hd.le, intervalIntegral.integral_of_le hd.le]
    apply integral_congr_ae
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    have hdf_eq : df =ᶠ[nhds x] deriv f := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact derivWithin_of_mem_nhds (s := I) (Icc_mem_nhds hy.1 hy.2)
    have hd2_eq : d2f x = deriv (deriv f) x := by
      calc
        d2f x = derivWithin df I x := rfl
        _ = deriv df x := derivWithin_of_mem_nhds (s := I) (Icc_mem_nhds hx.1 hx.2)
        _ = deriv (deriv f) x := Filter.EventuallyEq.deriv_eq hdf_eq
    simp [hd2_eq]
  rw [laplaceTransform_eq_interval_of_tsupport_subset_Ico hd hf_supp w,
    laplaceTransform_deriv_deriv_eq_interval_of_tsupport_subset_Ico hd hf_supp w]
  calc
    ∫ t in (0 : ℝ)..d, K t * (f t : ℂ)
        = (f 0 : ℂ) / w + (∫ t in (0 : ℝ)..d, K t * (df t : ℂ)) / w := hfirst
    _ = (f 0 : ℂ) / w + ((∫ t in (0 : ℝ)..d, K t * (d2f t : ℂ)) / w) / w := by
      rw [hsecond]
    _ = (f 0 : ℂ) / w +
          (∫ t in (0 : ℝ)..d, K t * ((deriv (deriv f) t : ℝ) : ℂ)) / w ^ 2 := by
      rw [hd2f_interval_eq]
      field_simp [hw]


@[blueprint
  "kadiri-test-fn"
  (title := "The Kadiri test function")
  (statement := /-- The $s$-parametrised test function
  $\varphi(y;\, s) := (f(0) - f(y))\, e^{-y s}\, \mathbf{1}_{y \geq 0}$ used to derive
  \ref{kadiri-identity-16} from \ref{kadiri-thm-3-1-q1}. -/)
  (latexEnv := "definition")]
noncomputable def kadiriTestFn (f : ℝ → ℝ) (s : ℂ) : ℝ → ℂ := fun y ↦
  if 0 ≤ y then ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)) else 0

section

open scoped Topology

/-- Bundled `(H₁)` hypotheses used by the `kadiriTestFn` C¹ chain below.
The endpoint conditions are interval derivatives on `Set.Icc 0 d`, matching
`laplaceTransform_ibp`. -/
private structure KadiriH1 (d : ℝ) (f : ℝ → ℝ) : Prop where
  contDiffOn_two : ContDiffOn ℝ 2 f (Set.Icc 0 d)
  tsupport_subset : tsupport f ⊆ Set.Ico 0 d
  value_d : f d = 0
  derivWithin_zero : derivWithin f (Set.Icc 0 d) 0 = 0
  derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0

private noncomputable def kadiriTestFnInterior (f : ℝ → ℝ) (s : ℂ) : ℝ → ℂ :=
  (fun y : ℝ => (f 0 : ℂ) - (f y : ℂ)) * fun y : ℝ => exp (-s * (y : ℂ))

private noncomputable def kadiriTestFnRightTail (f : ℝ → ℝ) (s : ℂ) : ℝ → ℂ :=
  (fun _ : ℝ => (f 0 : ℂ)) * fun y : ℝ => exp (-s * (y : ℂ))

private lemma laplaceKernel_contDiff (s : ℂ) :
    ContDiff ℝ 1 (fun y : ℝ => exp (-s * (y : ℂ))) := by
  have hofReal : ContDiff ℝ 1 (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hlinear : ContDiff ℝ 1 (fun y : ℝ => -s * (y : ℂ)) := by
    simpa using (contDiff_const.mul hofReal : ContDiff ℝ 1 (fun y : ℝ => -s * (y : ℂ)))
  exact hlinear.cexp

private lemma kadiriTestFn_contDiffOn_left {f : ℝ → ℝ} {s : ℂ} :
    ContDiffOn ℝ 1 (kadiriTestFn f s) (Set.Iio 0) := by
  refine (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => (0 : ℂ)) (Set.Iio 0)).congr ?_
  intro y hy
  have hylt : y < 0 := by simpa using hy
  simp [kadiriTestFn, not_le_of_gt hylt]

private lemma kadiriTestFnInterior_contDiffOn_Icc {d : ℝ} {f : ℝ → ℝ}
    (hf : KadiriH1 d f) (s : ℂ) :
    ContDiffOn ℝ 1 (kadiriTestFnInterior f s) (Set.Icc 0 d) := by
  have hf1 : ContDiffOn ℝ 1 f (Set.Icc 0 d) := by
    exact hf.contDiffOn_two.of_le (by norm_num)
  have hfc : ContDiffOn ℝ 1 (fun y : ℝ => (f y : ℂ)) (Set.Icc 0 d) := by
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hf1
  have hfirst : ContDiffOn ℝ 1 (fun y : ℝ => (f 0 : ℂ) - (f y : ℂ)) (Set.Icc 0 d) := by
    exact contDiffOn_const.sub hfc
  have hexp : ContDiffOn ℝ 1 (fun y : ℝ => exp (-s * (y : ℂ))) (Set.Icc 0 d) := by
    exact (laplaceKernel_contDiff s).contDiffOn
  exact hfirst.mul hexp

private lemma kadiriTestFn_contDiffOn_middle {d : ℝ} {f : ℝ → ℝ}
    (hf : KadiriH1 d f) (s : ℂ) :
    ContDiffOn ℝ 1 (kadiriTestFn f s) (Set.Ioo 0 d) := by
  refine (kadiriTestFnInterior_contDiffOn_Icc hf s).congr_mono ?_ ?_
  · intro y hy
    simp [kadiriTestFn, kadiriTestFnInterior, le_of_lt hy.1]
  · exact Set.Ioo_subset_Icc_self

private lemma kadiriTestFnRightTail_contDiff (f : ℝ → ℝ) (s : ℂ) :
    ContDiff ℝ 1 (kadiriTestFnRightTail f s) := by
  exact contDiff_const.mul (laplaceKernel_contDiff s)

private lemma kadiriTestFn_contDiffOn_right {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    ContDiffOn ℝ 1 (kadiriTestFn f s) (Set.Ioi d) := by
  refine (kadiriTestFnRightTail_contDiff f s).contDiffOn.congr ?_
  intro y hy
  have hy0 : 0 ≤ y := le_trans hd.le hy.le
  have hfy : f y = 0 := eq_zero_of_tsupport_subset_Ico_right hf.tsupport_subset hy.le
  simp [kadiriTestFn, kadiriTestFnRightTail, hy0, hfy]

private theorem kadiriTestFn_H1_contDiffAt_off_seams {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) {x : ℝ}
    (hx0 : x ≠ 0) (hxd : x ≠ d) :
    ContDiffAt ℝ 1 (kadiriTestFn f s) x := by
  rcases lt_trichotomy x 0 with hxlt | hxeq | hxgt
  · exact kadiriTestFn_contDiffOn_left.contDiffAt (isOpen_Iio.mem_nhds hxlt)
  · exact (hx0 hxeq).elim
  · rcases lt_trichotomy x d with hxlt_d | hxeq_d | hxd_lt
    · exact (kadiriTestFn_contDiffOn_middle hf s).contDiffAt
        (isOpen_Ioo.mem_nhds ⟨hxgt, hxlt_d⟩)
    · exact (hxd hxeq_d).elim
    · exact (kadiriTestFn_contDiffOn_right hd hf s).contDiffAt (isOpen_Ioi.mem_nhds hxd_lt)

private lemma kadiriTestFn_eventuallyEq_zero_left {f : ℝ → ℝ} {s : ℂ} :
    kadiriTestFn f s =ᶠ[𝓝[Set.Iic (0 : ℝ)] (0 : ℝ)] fun _ => (0 : ℂ) := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  by_cases hy0 : 0 ≤ y
  · have hyeq : y = 0 := le_antisymm hy hy0
    simp [kadiriTestFn, hyeq]
  · simp [kadiriTestFn, hy0]

private lemma kadiriTestFn_eventuallyEq_interior_zero {d : ℝ} {f : ℝ → ℝ} {s : ℂ} :
    kadiriTestFn f s =ᶠ[𝓝[Set.Icc 0 d] (0 : ℝ)] kadiriTestFnInterior f s := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [kadiriTestFn, kadiriTestFnInterior, hy.1]

private lemma kadiriTestFn_eventuallyEq_interior_d {d : ℝ} (_hd : 0 < d)
    {f : ℝ → ℝ} {s : ℂ} :
    kadiriTestFn f s =ᶠ[𝓝[Set.Icc 0 d] d] kadiriTestFnInterior f s := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : 0 ≤ y := hy.1
  simp [kadiriTestFn, kadiriTestFnInterior, hy0]

private lemma kadiriTestFn_eventuallyEq_rightTail_d {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ Set.Ico 0 d) {s : ℂ} :
    kadiriTestFn f s =ᶠ[𝓝[Set.Ici d] d] kadiriTestFnRightTail f s := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : 0 ≤ y := le_trans hd.le hy
  have hfy : f y = 0 := eq_zero_of_tsupport_subset_Ico_right hf_supp hy
  simp [kadiriTestFn, kadiriTestFnRightTail, hy0, hfy]

private lemma kadiriTestFnInterior_hasDerivWithinAt_zero {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    HasDerivWithinAt (kadiriTestFnInterior f s) 0 (Set.Icc 0 d) 0 := by
  have hx : (0 : ℝ) ∈ Set.Icc 0 d := Set.left_mem_Icc.mpr hd.le
  have hf_real :
      HasDerivWithinAt f (derivWithin f (Set.Icc 0 d) 0) (Set.Icc 0 d) 0 := by
    simpa using (hf.contDiffOn_two.differentiableOn (by norm_num) 0 hx).hasDerivWithinAt
  have hf_real_zero : HasDerivWithinAt f 0 (Set.Icc 0 d) 0 := by
    simpa [hf.derivWithin_zero] using hf_real
  have hf_complex :
      HasDerivWithinAt (fun y : ℝ => (f y : ℂ)) 0 (Set.Icc 0 d) 0 := by
    simpa using hf_real_zero.ofReal_comp
  have hfirst :
      HasDerivWithinAt (fun y : ℝ => (f 0 : ℂ) - (f y : ℂ)) 0 (Set.Icc 0 d) 0 := by
    simpa using hf_complex.const_sub (f 0 : ℂ)
  have hexp :
      HasDerivWithinAt (fun y : ℝ => exp (-s * (y : ℂ)))
        (-s * exp (-s * (0 : ℂ))) (Set.Icc 0 d) 0 := by
    simpa using (laplaceKernel_hasDerivAt s 0).hasDerivWithinAt
  have hprod := hfirst.mul hexp
  simpa [kadiriTestFnInterior] using hprod

private lemma kadiriTestFnInterior_hasDerivWithinAt_d {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    HasDerivWithinAt (kadiriTestFnInterior f s)
      ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) (Set.Icc 0 d) d := by
  have hx : d ∈ Set.Icc 0 d := Set.right_mem_Icc.mpr hd.le
  have hf_real :
      HasDerivWithinAt f (derivWithin f (Set.Icc 0 d) d) (Set.Icc 0 d) d := by
    simpa using (hf.contDiffOn_two.differentiableOn (by norm_num) d hx).hasDerivWithinAt
  have hf_real_zero : HasDerivWithinAt f 0 (Set.Icc 0 d) d := by
    simpa [hf.derivWithin_d] using hf_real
  have hf_complex :
      HasDerivWithinAt (fun y : ℝ => (f y : ℂ)) 0 (Set.Icc 0 d) d := by
    simpa using hf_real_zero.ofReal_comp
  have hfirst :
      HasDerivWithinAt (fun y : ℝ => (f 0 : ℂ) - (f y : ℂ)) 0 (Set.Icc 0 d) d := by
    simpa using hf_complex.const_sub (f 0 : ℂ)
  have hexp :
      HasDerivWithinAt (fun y : ℝ => exp (-s * (y : ℂ)))
        (-s * exp (-s * (d : ℂ))) (Set.Icc 0 d) d := by
    simpa using (laplaceKernel_hasDerivAt s d).hasDerivWithinAt
  have hprod := hfirst.mul hexp
  simpa [kadiriTestFnInterior, hf.value_d] using hprod

private lemma kadiriTestFnRightTail_hasDerivWithinAt_d {d : ℝ} {f : ℝ → ℝ} (s : ℂ) :
    HasDerivWithinAt (kadiriTestFnRightTail f s)
      ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) (Set.Ici d) d := by
  have hexp :
      HasDerivWithinAt (fun y : ℝ => exp (-s * (y : ℂ)))
        (-s * exp (-s * (d : ℂ))) (Set.Ici d) d := by
    simpa using (laplaceKernel_hasDerivAt s d).hasDerivWithinAt
  simpa [kadiriTestFnRightTail] using! hexp.const_mul (f 0 : ℂ)

private theorem kadiriTestFn_H1_seam_derivatives {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    kadiriTestFn f s 0 = 0 ∧
    HasDerivWithinAt (kadiriTestFn f s) 0 (Set.Iic 0) 0 ∧
    HasDerivWithinAt (kadiriTestFn f s) 0 (Set.Icc 0 d) 0 ∧
    HasDerivWithinAt (kadiriTestFn f s)
      ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) (Set.Icc 0 d) d ∧
    HasDerivWithinAt (kadiriTestFn f s)
      ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) (Set.Ici d) d := by
  have hleft_value : kadiriTestFn f s 0 = 0 := by
    simp [kadiriTestFn]
  have hleft_deriv :
      HasDerivWithinAt (kadiriTestFn f s) 0 (Set.Iic 0) 0 := by
    exact (hasDerivWithinAt_const (0 : ℝ) (Set.Iic 0) (0 : ℂ)).congr_of_eventuallyEq
      kadiriTestFn_eventuallyEq_zero_left hleft_value
  have hzero_deriv :
      HasDerivWithinAt (kadiriTestFn f s) 0 (Set.Icc 0 d) 0 := by
    exact (kadiriTestFnInterior_hasDerivWithinAt_zero hd hf s).congr_of_eventuallyEq
      kadiriTestFn_eventuallyEq_interior_zero (by simp [kadiriTestFn, kadiriTestFnInterior])
  have hd_value : kadiriTestFn f s d = kadiriTestFnInterior f s d := by
    have hd0 : 0 ≤ d := hd.le
    simp [kadiriTestFn, kadiriTestFnInterior, hd0]
  have hd_interior_deriv :
      HasDerivWithinAt (kadiriTestFn f s)
        ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) (Set.Icc 0 d) d := by
    exact (kadiriTestFnInterior_hasDerivWithinAt_d hd hf s).congr_of_eventuallyEq
      (kadiriTestFn_eventuallyEq_interior_d hd) hd_value
  have hd_tail_value : kadiriTestFn f s d = kadiriTestFnRightTail f s d := by
    have hd0 : 0 ≤ d := hd.le
    simp [kadiriTestFn, kadiriTestFnRightTail, hd0, hf.value_d]
  have hd_tail_deriv :
      HasDerivWithinAt (kadiriTestFn f s)
        ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) (Set.Ici d) d := by
    exact (kadiriTestFnRightTail_hasDerivWithinAt_d (d := d) (f := f) s).congr_of_eventuallyEq
      (kadiriTestFn_eventuallyEq_rightTail_d hd hf.tsupport_subset) hd_tail_value
  exact ⟨hleft_value, hleft_deriv, hzero_deriv, hd_interior_deriv, hd_tail_deriv⟩

private theorem kadiriTestFn_H1_seam_hasDerivAt {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    HasDerivAt (kadiriTestFn f s) 0 0 ∧
    HasDerivAt (kadiriTestFn f s)
      ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) d := by
  rcases kadiriTestFn_H1_seam_derivatives hd hf s with
    ⟨_, hleft, hzero, hd_interior, hd_tail⟩
  have h0_nhds : Set.Iic (0 : ℝ) ∪ Set.Icc 0 d ∈ 𝓝 (0 : ℝ) := by
    refine Filter.mem_of_superset
      (Ioo_mem_nhds (show -(d / 2) < (0 : ℝ) by linarith)
        (show (0 : ℝ) < d / 2 by linarith)) ?_
    intro y hy
    rcases le_or_gt y 0 with hy0 | hy0
    · exact Or.inl hy0
    · exact Or.inr ⟨le_of_lt hy0, by linarith [hy.2, hd]⟩
  have hd_nhds : Set.Icc 0 d ∪ Set.Ici d ∈ 𝓝 d := by
    refine Filter.mem_of_superset
      (Ioo_mem_nhds (show d / 2 < d by linarith)
        (show d < d + 1 by linarith)) ?_
    intro y hy
    by_cases hyd : y ≤ d
    · exact Or.inl ⟨by linarith [hy.1, hd], hyd⟩
    · exact Or.inr (le_of_not_ge hyd)
  exact ⟨(hleft.union hzero).hasDerivAt h0_nhds,
    (hd_interior.union hd_tail).hasDerivAt hd_nhds⟩

private theorem kadiriTestFn_H1_differentiable {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    Differentiable ℝ (kadiriTestFn f s) := by
  intro x
  rcases kadiriTestFn_H1_seam_hasDerivAt hd hf s with ⟨hzero, hdseam⟩
  by_cases hx0 : x = 0
  · simpa [hx0] using hzero.differentiableAt
  by_cases hxd : x = d
  · simpa [hxd] using hdseam.differentiableAt
  exact (kadiriTestFn_H1_contDiffAt_off_seams hd hf s hx0 hxd).differentiableAt_one

private theorem kadiriTestFn_H1_seam_continuity {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    ContinuousAt (kadiriTestFn f s) 0 ∧ ContinuousAt (kadiriTestFn f s) d := by
  rcases kadiriTestFn_H1_seam_derivatives hd hf s with
    ⟨_, hleft, hzero, hd_interior, hd_tail⟩
  have h0_nhds : Set.Iic (0 : ℝ) ∪ Set.Icc 0 d ∈ 𝓝 (0 : ℝ) := by
    refine Filter.mem_of_superset
      (Ioo_mem_nhds (show -(d / 2) < (0 : ℝ) by linarith)
        (show (0 : ℝ) < d / 2 by linarith)) ?_
    intro y hy
    rcases le_or_gt y 0 with hy0 | hy0
    · exact Or.inl hy0
    · exact Or.inr ⟨le_of_lt hy0, by linarith [hy.2, hd]⟩
  have hd_nhds : Set.Icc 0 d ∪ Set.Ici d ∈ 𝓝 d := by
    refine Filter.mem_of_superset
      (Ioo_mem_nhds (show d / 2 < d by linarith)
        (show d < d + 1 by linarith)) ?_
    intro y hy
    by_cases hyd : y ≤ d
    · exact Or.inl ⟨by linarith [hy.1, hd], hyd⟩
    · exact Or.inr (le_of_not_ge hyd)
  exact ⟨(hleft.continuousWithinAt.union hzero.continuousWithinAt).continuousAt h0_nhds,
    (hd_interior.continuousWithinAt.union hd_tail.continuousWithinAt).continuousAt hd_nhds⟩

private lemma kadiriTestFn_H1_deriv_zero {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    deriv (kadiriTestFn f s) 0 = 0 := by
  exact (kadiriTestFn_H1_seam_hasDerivAt hd hf s).1.deriv

private lemma kadiriTestFn_H1_deriv_d {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    deriv (kadiriTestFn f s) d =
      (f 0 : ℂ) * (-s * exp (-s * (d : ℂ))) := by
  exact (kadiriTestFn_H1_seam_hasDerivAt hd hf s).2.deriv

private lemma kadiriTestFn_H1_deriv_of_lt_zero {f : ℝ → ℝ} (s : ℂ) {x : ℝ} (hx : x < 0) :
    deriv (kadiriTestFn f s) x = 0 := by
  have heq : kadiriTestFn f s =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    have hylt : y < 0 := by simpa using hy
    simp [kadiriTestFn, not_le_of_gt hylt]
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

private lemma kadiriTestFn_H1_deriv_eq_interior_of_mem {d : ℝ}
    {f : ℝ → ℝ} (s : ℂ) {x : ℝ} (hx : x ∈ Set.Ioo 0 d) :
    deriv (kadiriTestFn f s) x = deriv (kadiriTestFnInterior f s) x := by
  have heq : kadiriTestFn f s =ᶠ[𝓝 x] kadiriTestFnInterior f s := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    simp [kadiriTestFn, kadiriTestFnInterior, le_of_lt hy.1]
  exact Filter.EventuallyEq.deriv_eq heq

private lemma kadiriTestFn_H1_deriv_eq_rightTail_of_gt {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) {x : ℝ} (hx : d < x) :
    deriv (kadiriTestFn f s) x = deriv (kadiriTestFnRightTail f s) x := by
  have heq : kadiriTestFn f s =ᶠ[𝓝 x] kadiriTestFnRightTail f s := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy0 : 0 ≤ y := le_trans hd.le hy.le
    have hfy : f y = 0 := eq_zero_of_tsupport_subset_Ico_right hf.tsupport_subset hy.le
    simp [kadiriTestFn, kadiriTestFnRightTail, hy0, hfy]
  exact Filter.EventuallyEq.deriv_eq heq

private lemma kadiriTestFn_H1_deriv_eq_interiorWithin_near_zero {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    deriv (kadiriTestFn f s)
      =ᶠ[𝓝[Set.Icc 0 d] (0 : ℝ)]
        derivWithin (kadiriTestFnInterior f s) (Set.Icc 0 d) := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hd)]
    with y hy hyd
  rcases lt_or_eq_of_le hy.1 with hypos | rfl
  · have hyI_nhds : Set.Icc 0 d ∈ 𝓝 y := Icc_mem_nhds hypos hyd
    have hwithin :
        derivWithin (kadiriTestFnInterior f s) (Set.Icc 0 d) y =
          deriv (kadiriTestFnInterior f s) y := derivWithin_of_mem_nhds hyI_nhds
    exact (kadiriTestFn_H1_deriv_eq_interior_of_mem s ⟨hypos, hyd⟩).trans hwithin.symm
  · have hglobal : deriv (kadiriTestFn f s) 0 = 0 :=
      kadiriTestFn_H1_deriv_zero hd hf s
    have hwithin :
        derivWithin (kadiriTestFnInterior f s) (Set.Icc 0 d) 0 = 0 :=
      (kadiriTestFnInterior_hasDerivWithinAt_zero hd hf s).derivWithin
        (uniqueDiffOn_Icc hd 0 (Set.left_mem_Icc.mpr hd.le))
    exact hglobal.trans hwithin.symm

private lemma kadiriTestFn_H1_deriv_eq_interiorWithin_near_d {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    deriv (kadiriTestFn f s)
      =ᶠ[𝓝[Set.Icc 0 d] d]
        derivWithin (kadiriTestFnInterior f s) (Set.Icc 0 d) := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hd)]
    with y hy hypos
  rcases lt_or_eq_of_le hy.2 with hylt | hyeq
  · have hyI_nhds : Set.Icc 0 d ∈ 𝓝 y := Icc_mem_nhds hypos hylt
    have hwithin :
        derivWithin (kadiriTestFnInterior f s) (Set.Icc 0 d) y =
          deriv (kadiriTestFnInterior f s) y := derivWithin_of_mem_nhds hyI_nhds
    exact (kadiriTestFn_H1_deriv_eq_interior_of_mem s ⟨hypos, hylt⟩).trans hwithin.symm
  · subst y
    have hglobal := kadiriTestFn_H1_deriv_d hd hf s
    have hwithin :
        derivWithin (kadiriTestFnInterior f s) (Set.Icc 0 d) d =
          (f 0 : ℂ) * (-s * exp (-s * (d : ℂ))) :=
      (kadiriTestFnInterior_hasDerivWithinAt_d hd hf s).derivWithin
        (uniqueDiffOn_Icc hd d (Set.right_mem_Icc.mpr hd.le))
    exact hglobal.trans hwithin.symm

private lemma kadiriTestFn_H1_deriv_eq_rightTail_near_d {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    deriv (kadiriTestFn f s)
      =ᶠ[𝓝[Set.Ici d] d] deriv (kadiriTestFnRightTail f s) := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyd : d ≤ y := by simpa using hy
  rcases lt_or_eq_of_le hyd with hylt | hyeq
  · exact kadiriTestFn_H1_deriv_eq_rightTail_of_gt hd hf s hylt
  · subst y
    have hglobal := kadiriTestFn_H1_deriv_d hd hf s
    have hright :
        deriv (kadiriTestFnRightTail f s) d =
          (f 0 : ℂ) * (-s * exp (-s * (d : ℂ))) := by
      have hright_deriv :
          HasDerivAt (kadiriTestFnRightTail f s)
            ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) d := by
        simpa [kadiriTestFnRightTail] using!
          (laplaceKernel_hasDerivAt s d).const_mul (f 0 : ℂ)
      exact hright_deriv.deriv
    exact hglobal.trans hright.symm

private lemma kadiriTestFn_H1_deriv_continuousWithinAt_zero_left {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Iic 0) (0 : ℝ) := by
  have hconst :
      ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Set.Iic 0) (0 : ℝ) :=
    continuous_const.continuousAt.continuousWithinAt
  refine hconst.congr_of_eventuallyEq_of_mem ?_ Set.self_mem_Iic
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : y ≤ 0 := by simpa using hy
  rcases lt_or_eq_of_le hy0 with hylt | hyeq
  · exact kadiriTestFn_H1_deriv_of_lt_zero s hylt
  · subst y
    exact kadiriTestFn_H1_deriv_zero hd hf s

private lemma kadiriTestFn_H1_deriv_continuousWithinAt_zero_right {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Ici 0) (0 : ℝ) := by
  have hcontIcc :
      ContinuousWithinAt
        (derivWithin (kadiriTestFnInterior f s) (Set.Icc 0 d))
        (Set.Icc 0 d) (0 : ℝ) :=
    ((kadiriTestFnInterior_contDiffOn_Icc hf s).continuousOn_derivWithin
      (uniqueDiffOn_Icc hd) le_rfl) 0 (Set.left_mem_Icc.mpr hd.le)
  have hglobalIcc :
      ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Icc 0 d) (0 : ℝ) :=
    hcontIcc.congr_of_eventuallyEq_of_mem
      (kadiriTestFn_H1_deriv_eq_interiorWithin_near_zero hd hf s)
      (Set.left_mem_Icc.mpr hd.le)
  have hIcc_mem : Set.Icc 0 d ∈ 𝓝[Set.Ici 0] (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hd)]
      with y hy0 hyd
    exact ⟨hy0, le_of_lt hyd⟩
  exact hglobalIcc.mono_of_mem_nhdsWithin hIcc_mem

private lemma kadiriTestFn_H1_deriv_continuousWithinAt_d_left {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Iic d) d := by
  have hcontIcc :
      ContinuousWithinAt
        (derivWithin (kadiriTestFnInterior f s) (Set.Icc 0 d))
        (Set.Icc 0 d) d :=
    ((kadiriTestFnInterior_contDiffOn_Icc hf s).continuousOn_derivWithin
      (uniqueDiffOn_Icc hd) le_rfl) d (Set.right_mem_Icc.mpr hd.le)
  have hglobalIcc :
      ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Icc 0 d) d :=
    hcontIcc.congr_of_eventuallyEq_of_mem
      (kadiriTestFn_H1_deriv_eq_interiorWithin_near_d hd hf s)
      (Set.right_mem_Icc.mpr hd.le)
  have hIcc_mem : Set.Icc 0 d ∈ 𝓝[Set.Iic d] d := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hd)]
      with y hyd hy0
    exact ⟨le_of_lt hy0, hyd⟩
  exact hglobalIcc.mono_of_mem_nhdsWithin hIcc_mem

private lemma kadiriTestFn_H1_deriv_continuousWithinAt_d_right {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Ici d) d := by
  have htail :
      ContinuousWithinAt (deriv (kadiriTestFnRightTail f s)) (Set.Ici d) d :=
    ((kadiriTestFnRightTail_contDiff f s).continuous_deriv le_rfl).continuousAt.continuousWithinAt
  exact htail.congr_of_eventuallyEq_of_mem
    (kadiriTestFn_H1_deriv_eq_rightTail_near_d hd hf s) Set.self_mem_Ici

private theorem kadiriTestFn_H1_continuous_deriv {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : KadiriH1 d f) (s : ℂ) :
    Continuous (deriv (kadiriTestFn f s)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx0 : x = 0
  · subst x
    exact continuousAt_iff_continuous_left_right.2
      ⟨kadiriTestFn_H1_deriv_continuousWithinAt_zero_left hd hf s,
        kadiriTestFn_H1_deriv_continuousWithinAt_zero_right hd hf s⟩
  by_cases hxd : x = d
  · subst x
    exact continuousAt_iff_continuous_left_right.2
      ⟨kadiriTestFn_H1_deriv_continuousWithinAt_d_left hd hf s,
        kadiriTestFn_H1_deriv_continuousWithinAt_d_right hd hf s⟩
  exact ((kadiriTestFn_H1_contDiffAt_off_seams hd hf s hx0 hxd).derivWithin
    (m := 0) (by norm_num)).continuousAt

end

@[blueprint
  "kadiri-test-fn-contDiff"
  (title := "The Kadiri test function is $C^1$")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and any
  $s \in \mathbb{C}$, the Kadiri test function $\varphi$
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
theorem kadiriTestFn_contDiff {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (s : ℂ) :
    ContDiff ℝ 1 (kadiriTestFn f s) := by
  rw [contDiff_one_iff_deriv]
  have hf : KadiriH1 d f := ⟨hf_C2, hf_supp, hf_d, hf_deriv_0, hf_deriv_d⟩
  exact ⟨kadiriTestFn_H1_differentiable hd hf s,
    kadiriTestFn_H1_continuous_deriv hd hf s⟩

private lemma kadiriTestFn_deriv_of_gt_max {d : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (s : ℂ) {x : ℝ} (hx : max d 0 < x) :
    deriv (kadiriTestFn f s) x = (f 0 : ℂ) * (-s * exp (-s * (x : ℂ))) := by
  have heq : kadiriTestFn f s =ᶠ[nhds x] fun y : ℝ => (f 0 : ℂ) * exp (-s * (y : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy0 : (0 : ℝ) ≤ y := ((le_max_right d 0).trans_lt hy).le
    have hfy : f y = 0 :=
      eq_zero_of_tsupport_subset_Ico_right hf_supp ((le_max_left d 0).trans_lt hy).le
    simp [kadiriTestFn, hy0, hfy]
  rw [heq.deriv_eq]
  exact ((laplaceKernel_hasDerivAt s x).const_mul (f 0 : ℂ)).deriv

@[blueprint
  "kadiri-test-fn-decay"
  (title := "Decay condition (B) for the Kadiri test function")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and
  $s \in \mathbb{C}$ with $\Re s > 1$, the Kadiri test function
  $\varphi$ satisfies
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
theorem kadiriTestFn_decay {d : ℝ} {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ .Ico 0 d)
    {s : ℂ} (hs : 1 < s.re) :
    ∃ b > 0,
      ((fun x : ℝ ↦ kadiriTestFn f s x * exp ((x : ℂ) / 2))
          =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) ∧
      ((fun x : ℝ ↦ deriv (kadiriTestFn f s) x * exp ((x : ℂ) / 2))
          =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) := by
  have hb : (0 : ℝ) < (s.re - 1) / 2 := by linarith
  have hre : ∀ x : ℝ, (-s * (x : ℂ)).re = -(s.re * x) := fun x => by
    simp [Complex.mul_re]
  have hre2 : ∀ x : ℝ, ((x : ℂ) / 2).re = x / 2 := fun x => by
    have : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  have hexp : ∀ x : ℝ, max d 0 < x →
      -(s.re * x) + x / 2 ≤ -(1 / 2 + (s.re - 1) / 2) * |x| := by
    intro x hx
    have hx0 : (0 : ℝ) < x := (le_max_right d 0).trans_lt hx
    rw [abs_of_pos hx0]
    nlinarith [mul_nonneg hx0.le (sub_nonneg.2 hs.le)]
  refine ⟨(s.re - 1) / 2, hb, ?_, ?_⟩
  · rw [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup]
    constructor
    · have h0 : (fun x : ℝ ↦ kadiriTestFn f s x * exp ((x : ℂ) / 2))
          =ᶠ[Filter.atBot] fun _ => (0 : ℂ) := by
        filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with x hx
        simp [kadiriTestFn, not_le_of_gt hx]
      exact h0.trans_isBigO (Asymptotics.isBigO_zero _ _)
    · rw [Asymptotics.isBigO_iff]
      refine ⟨‖(f 0 : ℂ)‖, ?_⟩
      filter_upwards [Filter.eventually_gt_atTop (max d 0)] with x hx
      have hx0 : (0 : ℝ) < x := (le_max_right d 0).trans_lt hx
      have hfx : f x = 0 :=
        eq_zero_of_tsupport_subset_Ico_right hf_supp ((le_max_left d 0).trans_lt hx).le
      have hval : kadiriTestFn f s x = (f 0 : ℂ) * exp (-s * (x : ℂ)) := by
        simp [kadiriTestFn, hx0.le, hfx]
      rw [hval, mul_assoc, ← Complex.exp_add, norm_mul, Complex.norm_exp,
        Real.norm_eq_abs, Real.abs_exp, Complex.add_re, hre, hre2]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hexp x hx)) (norm_nonneg _)
  · rw [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup]
    constructor
    · have h0 : (fun x : ℝ ↦ deriv (kadiriTestFn f s) x * exp ((x : ℂ) / 2))
          =ᶠ[Filter.atBot] fun _ => (0 : ℂ) := by
        filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with x hx
        simp [kadiriTestFn_H1_deriv_of_lt_zero s hx]
      exact h0.trans_isBigO (Asymptotics.isBigO_zero _ _)
    · rw [Asymptotics.isBigO_iff]
      refine ⟨‖(f 0 : ℂ)‖ * ‖s‖, ?_⟩
      filter_upwards [Filter.eventually_gt_atTop (max d 0)] with x hx
      rw [kadiriTestFn_deriv_of_gt_max hf_supp s hx]
      have hnorm : ‖(f 0 : ℂ) * (-s * exp (-s * (x : ℂ))) * exp ((x : ℂ) / 2)‖ =
          ‖(f 0 : ℂ)‖ * ‖s‖ * Real.exp (-(s.re * x) + x / 2) := by
        rw [mul_assoc, mul_assoc, ← Complex.exp_add, norm_mul, norm_mul, norm_neg,
          Complex.norm_exp, Complex.add_re, hre, hre2]
        ring
      rw [hnorm, Real.norm_eq_abs, Real.abs_exp]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hexp x hx)) (by positivity)

@[blueprint
  "kadiri-test-fn-laplace"
  (title := "Laplace transform of the Kadiri test function (shift identity)")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and
  $s, z \in \mathbb{C}$ with $\Re(s + z) > 0$,
  $$ \int_0^{\infty} \varphi(y;\, s)\, e^{-z y}\, dy
     = \frac{f(0)}{s + z} - F(s + z), $$
  where $F$ is the Laplace transform of $f$. -/)
  (proof := /-- Direct expansion of the integrand on $y > 0$:
  $\varphi(y;\, s) e^{-zy} = (f(0) - f(y)) e^{-(s+z) y}$. Split the integral:
  $\int_0^{\infty} f(0)\, e^{-(s+z) y}\, dy = f(0)/(s + z)$ converges by
  $\Re(s + z) > 0$; $\int_0^{\infty} f(y)\, e^{-(s+z) y}\, dy = F(s + z)$ unconditionally
  since $\mathrm{supp}\, f \subseteq [0, d]$ makes the integral compactly-supported. To be
  formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1486)]
theorem kadiriTestFn_laplaceTransform {d : ℝ} (_hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (s z : ℂ) (hsz : 0 < (s + z).re) :
    (∫ y, kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s + z) - laplaceTransform f (s + z) := by
  -- Bridge from two-sided to one-sided: `kadiriTestFn f s` vanishes on $(-\infty, 0]$
  -- (it is $0$ for $y < 0$ by the `if 0 ≤ y` branch, and equals $f(0) - f(0) = 0$ at
  -- $y = 0$). Hence the integrand equals its $\mathrm{Ioi}\, 0$-indicator, and the
  -- two integrals agree.
  have heq_indicator :
      (fun y => kadiriTestFn f s y * exp (-z * (y : ℂ))) =
      (Set.Ioi (0 : ℝ)).indicator (fun y => kadiriTestFn f s y * exp (-z * (y : ℂ))) := by
    ext y
    by_cases hy : y ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      rw [Set.mem_Ioi, not_lt] at hy
      rcases lt_or_eq_of_le hy with hy' | hy'
      · simp [kadiriTestFn, not_le.mpr hy']
      · simp [kadiriTestFn, ← hy']
  have hbridge : (∫ y, kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume) =
      ∫ y in Set.Ioi (0 : ℝ), kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume := by
    conv_lhs => rw [heq_indicator]
    exact MeasureTheory.integral_indicator measurableSet_Ioi
  rw [hbridge]
  set w := s + z with hw
  have hw0 : w ≠ 0 := fun h => by simp [h] at hsz
  have hsplit : Set.EqOn (fun y : ℝ => kadiriTestFn f s y * exp (-z * (y : ℂ)))
      (fun y : ℝ => (f 0 : ℂ) * exp (-w * (y : ℂ)) - exp (-w * (y : ℂ)) * (f y : ℂ))
      (Set.Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := (Set.mem_Ioi.1 hy).le
    have hmerge : exp (-s * (y : ℂ)) * exp (-z * (y : ℂ)) = exp (-w * (y : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hw]
      ring
    simp only [kadiriTestFn, if_pos hy0]
    calc ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)) * exp (-z * (y : ℂ))
        = ((f 0 : ℂ) - (f y : ℂ)) * (exp (-s * (y : ℂ)) * exp (-z * (y : ℂ))) := by ring
      _ = ((f 0 : ℂ) - (f y : ℂ)) * exp (-w * (y : ℂ)) := by rw [hmerge]
      _ = (f 0 : ℂ) * exp (-w * (y : ℂ)) - exp (-w * (y : ℂ)) * (f y : ℂ) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit]
  have hiexp : IntegrableOn (fun y : ℝ => exp (-w * (y : ℂ))) (Set.Ioi 0) := by
    refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
    suffices h : IntegrableOn (fun y : ℝ => Real.exp (-w.re * y)) (Set.Ioi 0) by
      simpa [Complex.norm_exp, neg_mul] using! h
    exact exp_neg_integrableOn_Ioi 0 hsz
  have hiA : IntegrableOn (fun y : ℝ => (f 0 : ℂ) * exp (-w * (y : ℂ))) (Set.Ioi 0) :=
    hiexp.const_mul _
  have hiB : IntegrableOn (fun y : ℝ => exp (-w * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0) := by
    have hsupp : Function.support (fun y : ℝ => exp (-w * (y : ℂ)) * (f y : ℂ)) ⊆
        Set.Icc 0 d := by
      intro y hy
      have hfy : f y ≠ 0 := by
        intro h0
        apply hy
        simp [h0]
      exact Set.Ico_subset_Icc_self (hf_supp (subset_tsupport f hfy))
    have hcont : ContinuousOn (fun y : ℝ => exp (-w * (y : ℂ)) * (f y : ℂ)) (Set.Icc 0 d) := by
      apply ContinuousOn.mul
      · exact Continuous.continuousOn (by fun_prop)
      · exact Complex.continuous_ofReal.comp_continuousOn hf_C2.continuousOn
    have hIcc : IntegrableOn (fun y : ℝ => exp (-w * (y : ℂ)) * (f y : ℂ)) (Set.Icc 0 d) :=
      hcont.integrableOn_compact isCompact_Icc
    exact ((integrableOn_iff_integrable_of_support_subset hsupp).mp hIcc).integrableOn
  rw [integral_sub hiA hiB]
  have hB : (∫ y in Set.Ioi (0 : ℝ), exp (-w * (y : ℂ)) * (f y : ℂ)) =
      laplaceTransform f w := rfl
  have hA : (∫ y in Set.Ioi (0 : ℝ), (f 0 : ℂ) * exp (-w * (y : ℂ))) = (f 0 : ℂ) / w := by
    rw [integral_const_mul]
    have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun y : ℝ => -exp (-w * (y : ℂ)) / w) (exp (-w * (x : ℂ))) x :=
      fun x _ => laplaceKernel_antideriv_hasDerivAt hw0 x
    have htend : Filter.Tendsto (fun y : ℝ => -exp (-w * (y : ℂ)) / w)
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have heq : (fun y : ℝ => ‖-exp (-w * (y : ℂ)) / w‖) =
          fun y : ℝ => Real.exp (-w.re * y) / ‖w‖ := by
        funext y
        rw [norm_div, norm_neg, Complex.norm_exp]
        congr 2
        simp [Complex.mul_re]
      rw [heq]
      have hnum : Filter.Tendsto (fun y : ℝ => Real.exp (-w.re * y))
          Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp
          ((Filter.tendsto_const_mul_atBot_of_neg (neg_lt_zero.2 hsz)).2 Filter.tendsto_id)
      simpa using hnum.div_const ‖w‖
    have hint : (∫ y in Set.Ioi (0 : ℝ), exp (-w * (y : ℂ))) = 1 / w := by
      calc (∫ y in Set.Ioi (0 : ℝ), exp (-w * (y : ℂ)))
          = 0 - (-exp (-w * ((0 : ℝ) : ℂ)) / w) :=
            MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hiexp htend
        _ = 1 / w := by
            norm_num [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_sub, neg_div,
              neg_neg]
    rw [hint, mul_one_div]
  rw [hA, hB]

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
  simp only [kadiriTestFn, Left.nonneg_neg_iff, ofReal_neg, natCast_log, mul_neg, neg_mul, neg_neg,
    ite_eq_right_iff, mul_eq_zero, exp_ne_zero, or_false]
  intro h
  rw [Real.log_nonpos_iff (by positivity)] at h
  simp only [Nat.cast_le_one, Nat.le_one_iff_eq_zero_or_eq_one] at h
  rcases h with rfl | rfl <;> simp

theorem kadiriTestFn_log (f : ℝ → ℝ) (s : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    kadiriTestFn f s (Real.log n) =
      ((f 0 : ℂ) - (f (Real.log n) : ℂ)) / (n : ℂ) ^ s := by
  have : 0 ≤ Real.log n := by positivity
  have hn0 : (n:ℂ) ≠ 0 := by norm_cast; positivity
  simp only [kadiriTestFn, this, ↓reduceIte, natCast_log, neg_mul, exp_neg,
    Complex.cpow_def_of_ne_zero hn0, division_def, mul_eq_mul_left_iff, inv_inj]
  left; ring_nf


/-- Weighted complex form of equation (16), derived from the explicit formula
`kadiri_thm_3_1_q1` at the Kadiri test function. The zero sum carries the
multiplicities that the residue calculus produces; the set-sum form of
`identity_16_complex` follows when every zero in the strip is simple. The two
hypotheses are the explicit formula's convergence inputs, instantiated at the
test function (dischargeable through the `F₂(s-z)/(s-z)²` representation). -/
theorem identity_16_complex_weighted {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re)
    (hΦ_sum : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (∫ y, kadiriTestFn f s y * exp (ρ.val * (y : ℂ)) ∂volume) *
        (riemannZeta.order ρ.val : ℂ)))
    (hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, kadiriTestFn f s y *
          exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)) =
      (f 0 : ℂ) * ((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1))
      + riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
          (fun ρ ↦ (f 0 : ℂ) / (s - ρ) - laplaceTransform f (s - ρ))
      + laplaceTransform f (s - 1)
      + ((1 / (2 * (Real.pi : ℂ))) *
          (∫ t : ℝ,
            ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
              laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I))
              / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
          + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  -- the explicit formula at the test function
  obtain ⟨b, hb, hdecay, hdecay'⟩ := kadiriTestFn_decay hf_supp hs
  have hform := kadiri_thm_3_1_q1
    (kadiriTestFn_contDiff hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s)
    hb hdecay hdecay' hΦ_sum hΓ_int
  dsimp only at hform
  -- the pole value
  have hΦ1 : (∫ y, kadiriTestFn f s y *
      exp (-(-1 : ℂ) * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s - 1) - laplaceTransform f (s - 1) := by
    have hre : (0 : ℝ) < (s + (-1 : ℂ)).re := by
      simp only [Complex.add_re, Complex.neg_re, Complex.one_re]
      linarith
    rw [kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s (-1) hre,
      show s + (-1 : ℂ) = s - 1 by ring]
  -- the value at zero, collapsed by integration by parts
  have hΦ0 : (∫ y, kadiriTestFn f s y *
      exp (-(0 : ℂ) * (y : ℂ)) ∂volume) =
      -(laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2) := by
    have hre : (0 : ℝ) < (s + (0 : ℂ)).re := by
      simp only [Complex.add_re, Complex.zero_re]
      linarith
    rw [kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s 0 hre,
      show s + (0 : ℂ) = s by ring,
      laplaceTransform_ibp hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hs0]
    ring
  -- the zero packet values
  have hzero : riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
      (fun ρ ↦ ∫ y, kadiriTestFn f s y *
        exp (-(-ρ) * (y : ℂ)) ∂volume) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ (f 0 : ℂ) / (s - ρ) - laplaceTransform f (s - ρ)) := by
    unfold riemannZeta.zeroes_sum
    refine tsum_congr fun ρ ↦ ?_
    change (∫ y, kadiriTestFn f s y *
        exp (-(-ρ.val) * (y : ℂ)) ∂volume) * (riemannZeta.order ρ.val : ℂ) =
      ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)) *
        (riemannZeta.order ρ.val : ℂ)
    congr 1
    have hlt : (ρ.val : ℂ).re < 1 := ρ.property.1.2
    have hre : (0 : ℝ) < (s + -ρ.val).re := by
      simp only [Complex.add_re, Complex.neg_re]
      linarith
    rw [kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s (-ρ.val) hre,
      show s + -ρ.val = s - ρ.val by ring]
  -- the test function vanishes at zero
  have hφ0 : kadiriTestFn f s 0 = 0 := by
    simp [kadiriTestFn]
  -- the reflected sum vanishes
  have hrefl : (∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * kadiriTestFn f s (-Real.log n)) = 0 := by
    have hterm : ∀ n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * kadiriTestFn f s (-Real.log n) = 0 := by
      intro n
      match n with
      | 0 => simp
      | 1 => simp [Nat.cast_one, Real.log_one, neg_zero, hφ0]
      | (k + 2) =>
        have hlog : (0 : ℝ) < Real.log ((k : ℝ) + 2) := by
          apply Real.log_pos
          have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        have hle : ¬ Real.log ((k : ℝ) + 2) ≤ 0 := not_le.mpr hlog
        simp [kadiriTestFn, hle]
    rw [tsum_congr hterm, tsum_zero]
  -- the contour integrand, collapsed by integration by parts
  have hcont : (∫ t : ℝ, ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, kadiriTestFn f s y *
          exp (-(-(1 / 2 + (t : ℂ) * I)) * (y : ℂ)) ∂volume) =
      -(∫ t : ℝ, ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
          laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
            (s - (1 / 2 + (t : ℂ) * I)) ^ 2) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    change ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        (∫ y, kadiriTestFn f s y *
          exp (-(-(1 / 2 + (t : ℂ) * I)) * (y : ℂ)) ∂volume) =
      -(((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
          laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
            (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
    have h12 : ((1 : ℂ) / 2 + (t : ℂ) * I).re = 1 / 2 := by
      simp [Complex.add_re, Complex.mul_re]
    have hre : (0 : ℝ) < (s + -(1 / 2 + (t : ℂ) * I)).re := by
      simp only [Complex.add_re, Complex.neg_re, h12]
      linarith
    have hwne : s - (1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro h
      have : (s - (1 / 2 + (t : ℂ) * I)).re = 0 := by rw [h]; rfl
      rw [Complex.sub_re, h12] at this
      linarith
    rw [kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s (-(1 / 2 + (t : ℂ) * I)) hre,
      show s + -(1 / 2 + (t : ℂ) * I) = s - (1 / 2 + (t : ℂ) * I) by ring,
      laplaceTransform_ibp hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hwne]
    ring
  rw [hΦ1, hΦ0, hzero, hφ0, hrefl, hcont] at hform
  -- the Dirichlet-side split
  have hS1 : Summable (fun n : ℕ ↦ (Λ n : ℂ) / (n : ℂ) ^ s) := by
    refine (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn]
  have hS2 := summable_f_log hf_supp (fun n : ℕ ↦ (Λ n : ℂ) / (n : ℂ) ^ s)
  have hLHS : (∑' n : ℕ, (Λ n : ℂ) * kadiriTestFn f s (Real.log n)) =
      (f 0 : ℂ) * (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) -
        ∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ) := by
    rw [← tsum_mul_left, ← Summable.tsum_sub (hS1.mul_left _) hS2]
    refine tsum_congr fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [kadiriTestFn_log f s hn]
      have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
  rw [hLHS] at hform
  linear_combination -hform

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
theorem re_hadamardB_eq :
    hadamardB.re =
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
private lemma deriv_deriv_eq_derivWithin_derivWithin_of_mem_Ioo {d : ℝ} {f : ℝ → ℝ}
    {t : ℝ} (ht : t ∈ Set.Ioo 0 d) :
    deriv (deriv f) t =
      derivWithin (fun y => derivWithin f (Set.Icc 0 d) y) (Set.Icc 0 d) t := by
  have hmem : Set.Icc 0 d ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have heq : deriv f =ᶠ[nhds t] fun y => derivWithin f (Set.Icc 0 d) y := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)).symm
  rw [Filter.EventuallyEq.deriv_eq heq]
  exact (derivWithin_of_mem_nhds hmem).symm

theorem laplaceTransform_re_decay {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (_hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (_hf_deriv2_d : derivWithin (fun x => derivWithin f (Set.Icc 0 d) x) (Set.Icc 0 d) d = 0)
    (σ₀ σ₁ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 1 ≤ |s.im| →
      |(laplaceTransform f s).re| ≤ C / s.im ^ 2 := by
  have hdf_C1 : ContDiffOn ℝ 1 (fun y => derivWithin f (Set.Icc 0 d) y) (Set.Icc 0 d) :=
    hf_C2.derivWithin (uniqueDiffOn_Icc hd) (by norm_num)
  have hg_cont : ContinuousOn
      (fun x => derivWithin (fun y => derivWithin f (Set.Icc 0 d) y) (Set.Icc 0 d) x)
      (Set.Icc 0 d) :=
    hdf_C1.continuousOn_derivWithin (uniqueDiffOn_Icc hd) le_rfl
  obtain ⟨K0, hK0⟩ := isCompact_Icc.exists_bound_of_continuousOn hg_cont
  have hK00 : 0 ≤ K0 := (norm_nonneg _).trans (hK0 0 (Set.left_mem_Icc.2 hd.le))
  set B : ℝ := max 0 (-σ₀) with hB
  set M : ℝ := Real.exp (B * d) * K0 * d with hMdef
  have hM0 : 0 ≤ M := mul_nonneg (mul_nonneg (Real.exp_pos _).le hK00) hd.le
  have hMbound : ∀ s : ℂ, σ₀ ≤ s.re →
      ‖laplaceTransform (fun u => deriv (deriv f) u) s‖ ≤ M := by
    intro s hs0
    rw [laplaceTransform_deriv_deriv_eq_interval_of_tsupport_subset_Ico hd hf_supp s]
    have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) d,
        ‖exp (-s * (t : ℂ)) * ((deriv (deriv f) t : ℝ) : ℂ)‖ ≤ Real.exp (B * d) * K0 := by
      intro t ht
      rw [Set.uIoc_of_le hd.le] at ht
      rw [norm_mul, Complex.norm_exp]
      have hre : (-s * (t : ℂ)).re = -(s.re * t) := by simp [Complex.mul_re]
      have hexp_le : Real.exp ((-s * (t : ℂ)).re) ≤ Real.exp (B * d) := by
        rw [hre]
        apply Real.exp_le_exp.2
        have hBge : -s.re ≤ B := le_trans (neg_le_neg hs0) (le_max_right 0 (-σ₀))
        have hB0 : (0 : ℝ) ≤ B := le_max_left 0 (-σ₀)
        calc -(s.re * t) = -s.re * t := (neg_mul _ _).symm
          _ ≤ B * t := mul_le_mul_of_nonneg_right hBge ht.1.le
          _ ≤ B * d := mul_le_mul_of_nonneg_left ht.2 hB0
      have hfpp : ‖((deriv (deriv f) t : ℝ) : ℂ)‖ ≤ K0 := by
        rw [Complex.norm_real]
        by_cases htd : t = d
        · rw [htd, deriv_deriv_eq_zero_of_tsupport_subset_Ico hf_supp le_rfl]
          simpa using hK00
        · have htlt : t < d := lt_of_le_of_ne ht.2 htd
          rw [deriv_deriv_eq_derivWithin_derivWithin_of_mem_Ioo ⟨ht.1, htlt⟩]
          simpa using hK0 t ⟨ht.1.le, ht.2⟩
      exact mul_le_mul hexp_le hfpp (norm_nonneg _) (Real.exp_pos _).le
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hpt) ?_
    rw [sub_zero, abs_of_pos hd]
  refine ⟨|f 0| * max |σ₀| |σ₁| + M, ?_⟩
  intro s hs0 hs1 him
  have him0 : s.im ≠ 0 := by
    intro h
    rw [h] at him
    norm_num at him
  have hs : s ≠ 0 := fun h => him0 (by rw [h]; rfl)
  have him2 : (0 : ℝ) < s.im ^ 2 := by positivity
  have hns : s.im ^ 2 ≤ Complex.normSq s := by
    rw [Complex.normSq_apply]
    nlinarith [mul_self_nonneg s.re]
  rw [laplaceTransform_ibp hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hs, Complex.add_re]
  have hA : |s.re| ≤ max |σ₀| |σ₁| := by
    rw [abs_le]
    constructor
    · calc -(max |σ₀| |σ₁|) ≤ -|σ₀| := neg_le_neg (le_max_left _ _)
        _ ≤ σ₀ := neg_abs_le σ₀
        _ ≤ s.re := hs0
    · calc s.re ≤ σ₁ := hs1
        _ ≤ |σ₁| := le_abs_self σ₁
        _ ≤ max |σ₀| |σ₁| := le_max_right _ _
  have h1 : |(((f 0 : ℝ) : ℂ) / s).re| ≤ |f 0| * max |σ₀| |σ₁| / s.im ^ 2 := by
    have hre : (((f 0 : ℝ) : ℂ) / s).re = f 0 * s.re / Complex.normSq s := by
      rw [Complex.div_re]
      simp
    rw [hre, abs_div, abs_of_nonneg (Complex.normSq_nonneg s), abs_mul]
    have hnpos : (0 : ℝ) < Complex.normSq s := Complex.normSq_pos.2 hs
    calc |f 0| * |s.re| / Complex.normSq s
        ≤ |f 0| * max |σ₀| |σ₁| / Complex.normSq s := by gcongr
      _ ≤ |f 0| * max |σ₀| |σ₁| / s.im ^ 2 := by gcongr
  have h2 : |(laplaceTransform (fun u => deriv (deriv f) u) s / s ^ 2).re| ≤ M / s.im ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_pow]
    have hsq : s.im ^ 2 ≤ ‖s‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hns
    have hnorm2 : (0 : ℝ) < ‖s‖ ^ 2 := by positivity
    calc ‖laplaceTransform (fun u => deriv (deriv f) u) s‖ / ‖s‖ ^ 2
        ≤ M / ‖s‖ ^ 2 := by
          gcongr
          exact hMbound s hs0
      _ ≤ M / s.im ^ 2 := by gcongr
  calc |(((f 0 : ℝ) : ℂ) / s).re +
        (laplaceTransform (fun u => deriv (deriv f) u) s / s ^ 2).re|
      ≤ |(((f 0 : ℝ) : ℂ) / s).re| +
        |(laplaceTransform (fun u => deriv (deriv f) u) s / s ^ 2).re| := abs_add_le _ _
    _ ≤ |f 0| * max |σ₀| |σ₁| / s.im ^ 2 + M / s.im ^ 2 := add_le_add h1 h2
    _ = (|f 0| * max |σ₀| |σ₁| + M) / s.im ^ 2 := (add_div _ _ _).symm

/-- Norm decay of the pole-subtracted Laplace transform on a right half-plane:
subtracting the `f 0 / s` pole removes the only `1/|Im s|`-order term of
`laplaceTransform_ibp`, so the remainder `F₂(s)/s²` decays like `1/(Im s)^2` in
norm, not just in real part. The full transform does NOT have this decay (its
imaginary part is of order `f 0 / Im s`), which is why the complex sum
`∑ ρ, F(s - ρ)` over the zeta zeros is not absolutely summable for `f 0 ≠ 0`,
while the pole-subtracted sum is. -/
theorem laplaceTransform_sub_pole_norm_decay {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (σ₀ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → s.im ≠ 0 →
      ‖(f 0 : ℂ) / s - laplaceTransform f s‖ ≤ C / s.im ^ 2 := by
  have hdf_C1 : ContDiffOn ℝ 1 (fun y => derivWithin f (Set.Icc 0 d) y) (Set.Icc 0 d) :=
    hf_C2.derivWithin (uniqueDiffOn_Icc hd) (by norm_num)
  have hg_cont : ContinuousOn
      (fun x => derivWithin (fun y => derivWithin f (Set.Icc 0 d) y) (Set.Icc 0 d) x)
      (Set.Icc 0 d) :=
    hdf_C1.continuousOn_derivWithin (uniqueDiffOn_Icc hd) le_rfl
  obtain ⟨K0, hK0⟩ := isCompact_Icc.exists_bound_of_continuousOn hg_cont
  have hK00 : 0 ≤ K0 := (norm_nonneg _).trans (hK0 0 (Set.left_mem_Icc.2 hd.le))
  set B : ℝ := max 0 (-σ₀) with hB
  set M : ℝ := Real.exp (B * d) * K0 * d with hMdef
  have hM0 : 0 ≤ M := mul_nonneg (mul_nonneg (Real.exp_pos _).le hK00) hd.le
  have hMbound : ∀ s : ℂ, σ₀ ≤ s.re →
      ‖laplaceTransform (fun u => deriv (deriv f) u) s‖ ≤ M := by
    intro s hs0
    rw [laplaceTransform_deriv_deriv_eq_interval_of_tsupport_subset_Ico hd hf_supp s]
    have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) d,
        ‖exp (-s * (t : ℂ)) * ((deriv (deriv f) t : ℝ) : ℂ)‖ ≤ Real.exp (B * d) * K0 := by
      intro t ht
      rw [Set.uIoc_of_le hd.le] at ht
      rw [norm_mul, Complex.norm_exp]
      have hre : (-s * (t : ℂ)).re = -(s.re * t) := by simp [Complex.mul_re]
      have hexp_le : Real.exp ((-s * (t : ℂ)).re) ≤ Real.exp (B * d) := by
        rw [hre]
        apply Real.exp_le_exp.2
        have hBge : -s.re ≤ B := le_trans (neg_le_neg hs0) (le_max_right 0 (-σ₀))
        have hB0 : (0 : ℝ) ≤ B := le_max_left 0 (-σ₀)
        calc -(s.re * t) = -s.re * t := (neg_mul _ _).symm
          _ ≤ B * t := mul_le_mul_of_nonneg_right hBge ht.1.le
          _ ≤ B * d := mul_le_mul_of_nonneg_left ht.2 hB0
      have hfpp : ‖((deriv (deriv f) t : ℝ) : ℂ)‖ ≤ K0 := by
        rw [Complex.norm_real]
        by_cases htd : t = d
        · rw [htd, deriv_deriv_eq_zero_of_tsupport_subset_Ico hf_supp le_rfl]
          simpa using hK00
        · have htlt : t < d := lt_of_le_of_ne ht.2 htd
          rw [deriv_deriv_eq_derivWithin_derivWithin_of_mem_Ioo ⟨ht.1, htlt⟩]
          simpa using hK0 t ⟨ht.1.le, ht.2⟩
      exact mul_le_mul hexp_le hfpp (norm_nonneg _) (Real.exp_pos _).le
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hpt) ?_
    rw [sub_zero, abs_of_pos hd]
  refine ⟨M, ?_⟩
  intro s hs0 him0
  have hs : s ≠ 0 := fun h => him0 (by rw [h]; rfl)
  have him2 : (0 : ℝ) < s.im ^ 2 := by positivity
  have hns : s.im ^ 2 ≤ Complex.normSq s := by
    rw [Complex.normSq_apply]
    nlinarith [mul_self_nonneg s.re]
  rw [laplaceTransform_ibp hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hs]
  have hcancel : (f 0 : ℂ) / s -
      ((f 0 : ℂ) / s + laplaceTransform (fun u => deriv (deriv f) u) s / s ^ 2) =
      -(laplaceTransform (fun u => deriv (deriv f) u) s / s ^ 2) := by
    ring
  rw [hcancel, norm_neg, norm_div, norm_pow]
  have hsq : s.im ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hns
  have hnorm2 : (0 : ℝ) < ‖s‖ ^ 2 := by positivity
  calc ‖laplaceTransform (fun u => deriv (deriv f) u) s‖ / ‖s‖ ^ 2
      ≤ M / ‖s‖ ^ 2 := by
        gcongr
        exact hMbound s hs0
    _ ≤ M / s.im ^ 2 := by gcongr

/-- Unconditional summability over the non-trivial zeros of the pole-subtracted
Laplace transform. The un-subtracted complex sum `∑ ρ, F(s - ρ)` is not
absolutely summable when `f 0 ≠ 0` (terms of norm `~ |f 0| / |Im ρ|`); in
equation (16) the groups `f 0 * ∑ ρ, 1/(s - ρ)` and `-∑ ρ, F(s - ρ)` combine
into exactly this summand, which is `O(1/(Im ρ)^2)` and summable against the
crude counting majorant. -/
theorem summable_lap_sub_pole_at_zeros {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (s : ℂ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)) := by
  obtain ⟨C, hC⟩ := laplaceTransform_sub_pole_norm_decay hd hf_C2 hf_supp hf_d
    hf_deriv_0 hf_deriv_d (s.re - 1)
  have htail : Summable (fun ρ : NontrivialZeros ↦
      C * (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ))) :=
    (summable_zeroImagSquareTail_shifted_unconditional s).mul_left C
  refine Summable.of_norm_bounded_eventually htail ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (nontrivialZeros_shifted_abs_im_lt_one_finite s)
  intro ρ hbad
  rw [Set.mem_setOf_eq] at hbad ⊢
  by_contra hsmall
  have him : 1 ≤ |(s - (ρ : ℂ)).im| := le_of_not_gt hsmall
  have him0 : (s - (ρ : ℂ)).im ≠ 0 := by
    intro h
    rw [h] at him
    norm_num at him
  have hre : (ρ : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := ρ.property.1
  have hre_lo : s.re - 1 ≤ (s - (ρ : ℂ)).re := by
    rw [Complex.sub_re]
    linarith [hre.2]
  have hdecay := hC (s - (ρ : ℂ)) hre_lo him0
  apply hbad
  calc ‖(f 0 : ℂ) / (s - (ρ : ℂ)) - laplaceTransform f (s - (ρ : ℂ))‖
      ≤ C / (s - (ρ : ℂ)).im ^ 2 := hdecay
    _ = C * (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) := by
        rw [inv_pow, sq_abs, div_eq_mul_inv]

/-- Unconditional summability of the real parts of the zero residues:
`Re (1/(s - ρ)) = Re (s - ρ) / |s - ρ|²` decays like `1/(Im ρ)^2` on the strip,
while the complex sum `∑ ρ, 1/(s - ρ)` is only conditionally convergent. This is
the summability needed to move `Re` inside the residue sum of equation (16). -/
theorem summable_re_one_div_at_zeros (s : ℂ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (1 / (s - ρ.val)).re) := by
  have htail : Summable (fun ρ : NontrivialZeros ↦
      (|s.re| + 1) * (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ))) :=
    (summable_zeroImagSquareTail_shifted_unconditional s).mul_left _
  refine Summable.of_norm_bounded_eventually htail ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (nontrivialZeros_shifted_abs_im_lt_one_finite s)
  intro ρ hbad
  rw [Set.mem_setOf_eq] at hbad ⊢
  by_contra hsmall
  have him : 1 ≤ |(s - (ρ : ℂ)).im| := le_of_not_gt hsmall
  have him0 : (s - (ρ : ℂ)).im ≠ 0 := by
    intro h
    rw [h] at him
    norm_num at him
  have hw0 : s - (ρ : ℂ) ≠ 0 := by
    intro h
    apply him0
    rw [h]
    rfl
  have hre : (ρ : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := ρ.property.1
  have hre_bound : |(s - (ρ : ℂ)).re| ≤ |s.re| + 1 := by
    rw [Complex.sub_re]
    calc |s.re - (ρ : ℂ).re| ≤ |s.re| + |(ρ : ℂ).re| := abs_sub _ _
      _ ≤ |s.re| + 1 := by
          rw [abs_of_pos hre.1]
          linarith [hre.2]
  have hdiv_re : (1 / (s - (ρ : ℂ))).re =
      (s - (ρ : ℂ)).re / Complex.normSq (s - (ρ : ℂ)) := by
    rw [Complex.div_re]
    simp
  have hns : (s - (ρ : ℂ)).im ^ 2 ≤ Complex.normSq (s - (ρ : ℂ)) := by
    rw [Complex.normSq_apply]
    nlinarith [mul_self_nonneg (s - (ρ : ℂ)).re]
  have him2 : (0 : ℝ) < (s - (ρ : ℂ)).im ^ 2 := by positivity
  have hnpos : (0 : ℝ) < Complex.normSq (s - (ρ : ℂ)) := Complex.normSq_pos.2 hw0
  apply hbad
  rw [Real.norm_eq_abs, hdiv_re, abs_div, abs_of_nonneg (Complex.normSq_nonneg _)]
  calc |(s - (ρ : ℂ)).re| / Complex.normSq (s - (ρ : ℂ))
      ≤ (|s.re| + 1) / Complex.normSq (s - (ρ : ℂ)) := by gcongr
    _ ≤ (|s.re| + 1) / (s - (ρ : ℂ)).im ^ 2 := by
        gcongr
    _ = (|s.re| + 1) * (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) := by
        rw [inv_pow, sq_abs, div_eq_mul_inv]


/-- Summability of the genus-one zero packets `1/ρ + 1/(s - ρ)`: away from finitely
many zeros the packet equals `s/(ρ(s - ρ))`, of norm at most
`‖s‖/2 · (1/(Im ρ)² + 1/(Im (s - ρ))²)` by AM-GM, and both square tails are summable
by the crude counting majorant. This is the convergence input that makes the paired
form of the residue sums legitimate. -/
theorem summable_one_div_add_one_div_at_zeros (s : ℂ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (1 / (ρ.val : ℂ) + 1 / (s - ρ.val))) := by
  have htail0 : Summable (fun ρ : NontrivialZeros ↦ |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) := by
    have h := zeroImagSquareTailSummable_of_crude_majorant
    unfold zeroImagSquareTailSummable zeroImagSquareTail at h
    exact h
  have htails : Summable (fun ρ : NontrivialZeros ↦
      ‖s‖ / 2 * (|(ρ : ℂ).im|⁻¹ ^ (2 : ℕ) + |(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ))) :=
    (htail0.add (summable_zeroImagSquareTail_shifted_unconditional s)).mul_left _
  refine Summable.of_norm_bounded_eventually htails ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset
    (nontrivialZeros_abs_im_lt_one_finite.union
      (nontrivialZeros_shifted_abs_im_lt_one_finite s))
  intro ρ hbad
  rw [Set.mem_setOf_eq] at hbad
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
  by_contra hsmall
  rw [not_or] at hsmall
  obtain ⟨h1, h2⟩ := hsmall
  have him1 : 1 ≤ |(ρ : ℂ).im| := not_lt.mp h1
  have him2 : 1 ≤ |(s - (ρ : ℂ)).im| := not_lt.mp h2
  apply hbad
  have hρ0 : ((ρ : ℂ)) ≠ 0 := nontrivialZero_ne_zero ρ
  have him2ne : (s - (ρ : ℂ)).im ≠ 0 := by
    intro h
    rw [h] at him2
    norm_num at him2
  have hsρ : s - (ρ : ℂ) ≠ 0 := by
    intro h
    apply him2ne
    rw [h]
    rfl
  have hnρ : (0 : ℝ) < ‖(ρ : ℂ)‖ := norm_pos_iff.mpr hρ0
  have hnsρ : (0 : ℝ) < ‖s - (ρ : ℂ)‖ := norm_pos_iff.mpr hsρ
  have him1pos : (0 : ℝ) < |(ρ : ℂ).im| := lt_of_lt_of_le one_pos him1
  have him2pos : (0 : ℝ) < |(s - (ρ : ℂ)).im| := lt_of_lt_of_le one_pos him2
  have hpacket : 1 / ((ρ : ℂ)) + 1 / (s - (ρ : ℂ)) =
      s / (((ρ : ℂ)) * (s - (ρ : ℂ))) := by
    field_simp
    ring
  rw [hpacket, norm_div, norm_mul]
  have hstep1 : ‖s‖ / (‖(ρ : ℂ)‖ * ‖s - (ρ : ℂ)‖) ≤
      ‖s‖ * (|(ρ : ℂ).im|⁻¹ * |(s - (ρ : ℂ)).im|⁻¹) := by
    rw [div_eq_mul_inv, mul_inv]
    have ha : ‖(ρ : ℂ)‖⁻¹ ≤ |(ρ : ℂ).im|⁻¹ :=
      inv_anti₀ him1pos (Complex.abs_im_le_norm _)
    have hb : ‖s - (ρ : ℂ)‖⁻¹ ≤ |(s - (ρ : ℂ)).im|⁻¹ :=
      inv_anti₀ him2pos (Complex.abs_im_le_norm _)
    have hb0 : (0 : ℝ) ≤ ‖s - (ρ : ℂ)‖⁻¹ := by positivity
    have ha0 : (0 : ℝ) ≤ |(ρ : ℂ).im|⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
    exact mul_le_mul ha hb hb0 ha0
  have hstep2 : |(ρ : ℂ).im|⁻¹ * |(s - (ρ : ℂ)).im|⁻¹ ≤
      (|(ρ : ℂ).im|⁻¹ ^ (2 : ℕ) + |(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) / 2 := by
    nlinarith [two_mul_le_add_sq (|(ρ : ℂ).im|⁻¹) (|(s - (ρ : ℂ)).im|⁻¹)]
  calc ‖s‖ / (‖(ρ : ℂ)‖ * ‖s - (ρ : ℂ)‖)
      ≤ ‖s‖ * (|(ρ : ℂ).im|⁻¹ * |(s - (ρ : ℂ)).im|⁻¹) := hstep1
    _ ≤ ‖s‖ * ((|(ρ : ℂ).im|⁻¹ ^ (2 : ℕ) + |(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) / 2) :=
        mul_le_mul_of_nonneg_left hstep2 (norm_nonneg s)
    _ = ‖s‖ / 2 * (|(ρ : ℂ).im|⁻¹ ^ (2 : ℕ) + |(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) := by
        ring

/-- The reciprocal real-part sum, the `s`-free half of the packet. -/
theorem summable_re_inv_at_zeros :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (1 / (ρ.val : ℂ)).re) := by
  refine (summable_re_one_div_at_zeros 0).neg.congr fun ρ ↦ ?_
  rw [zero_sub, one_div, inv_neg, Complex.neg_re, neg_neg, one_div]

/-- Distributing `Re` over the packet sum: the paired complex sum splits into the two
absolutely summable real-part sums. -/
theorem re_tsum_paired_eq_re_inv_add_re_shifted (s : ℂ) :
    (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (s - ρ.val))).re =
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ)).re) +
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (s - ρ.val)).re := by
  have h1 : (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
      (1 / (ρ.val : ℂ) + 1 / (s - ρ.val))).re =
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (s - ρ.val)).re := by
    simpa using ContinuousLinearMap.map_tsum Complex.reCLM
      (summable_one_div_add_one_div_at_zeros s)
  rw [h1, tsum_congr (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
    Complex.add_re (1 / (ρ.val : ℂ)) (1 / (s - ρ.val)))]
  exact summable_re_inv_at_zeros.tsum_add (summable_re_one_div_at_zeros s)

/-- BRIDGE between the two repaired shapes of the residue sums: the Re-inside form
equals the paired form minus the reciprocal correction. Either side can serve as the
zero term of the real-part identities; this lemma converts between them for free. -/
theorem re_shifted_sum_eq_paired_sub_re_inv (s : ℂ) :
    (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (s - ρ.val)).re) =
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (s - ρ.val))).re -
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ)).re := by
  rw [re_tsum_paired_eq_re_inv_add_re_shifted s]
  ring


/-- The explicit formula's weighted zero-sum hypothesis holds at the Kadiri test
function: each integral is the pole-subtracted packet `f 0/(s-ρ) - F(s-ρ)`, of
norm `O(1/(Im (s-ρ))²)`, and the order weight is carried by the unconditional
weighted square tail. This discharges `hΦ_sum` of `identity_16_complex_weighted`. -/
theorem summable_kadiriTestFn_weighted_at_zeros {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (∫ y, kadiriTestFn f s y * exp (ρ.val * (y : ℂ)) ∂volume) *
        (riemannZeta.order ρ.val : ℂ)) := by
  have hpt : ∀ ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
      (∫ y, kadiriTestFn f s y * exp (ρ.val * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val) := by
    intro ρ
    have hre : (0 : ℝ) < (s + -ρ.val).re := by
      have hlt : (ρ.val).re < 1 := ρ.property.1.2
      simp only [Complex.add_re, Complex.neg_re]
      linarith
    have h := kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s (-ρ.val) hre
    simp only [neg_neg] at h
    rw [h, show s + -ρ.val = s - ρ.val by ring]
  have hmain : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)) *
        (riemannZeta.order ρ.val : ℂ)) := by
    obtain ⟨C, hC⟩ := laplaceTransform_sub_pole_norm_decay hd hf_C2 hf_supp hf_d
      hf_deriv_0 hf_deriv_d (s.re - 1)
    have htail := (weighted_zeroImagSquareTail_shifted_summable s).mul_left C
    refine Summable.of_norm_bounded_eventually htail ?_
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (nontrivialZeros_shifted_abs_im_lt_one_finite s)
    intro ρ hbad
    rw [Set.mem_setOf_eq] at hbad ⊢
    by_contra hsmall
    have him : 1 ≤ |(s - (ρ : ℂ)).im| := le_of_not_gt hsmall
    have him0 : (s - (ρ : ℂ)).im ≠ 0 := by
      intro h
      rw [h] at him
      norm_num at him
    have hre_lo : s.re - 1 ≤ (s - (ρ : ℂ)).re := by
      rw [Complex.sub_re]
      linarith [ρ.property.1.2]
    have hdecay := hC (s - (ρ : ℂ)) hre_lo him0
    apply hbad
    have hordZ : (0 : ℤ) ≤ riemannZeta.order (ρ : ℂ) :=
      riemannZeta_order_nonneg (nontrivialZero_ne_one ρ)
    have hord : (0 : ℝ) ≤ ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
      exact_mod_cast hordZ
    rw [norm_mul]
    have hnormord : ‖((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ)‖ =
        ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
      rw [Complex.norm_intCast]
      exact_mod_cast abs_of_nonneg hordZ
    rw [hnormord]
    calc ‖(f 0 : ℂ) / (s - (ρ : ℂ)) - laplaceTransform f (s - (ρ : ℂ))‖ *
          ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ)
        ≤ (C / (s - (ρ : ℂ)).im ^ 2) * ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) :=
          mul_le_mul_of_nonneg_right hdecay hord
      _ = C * (((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) *
            (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ))) := by
          rw [inv_pow, sq_abs, div_eq_mul_inv]
          ring
  exact hmain.congr fun ρ ↦ by rw [hpt ρ]

/-- The weighted complex form of equation (16) with the zero-sum hypothesis
discharged: only the contour integrability and `kadiri_thm_3_1_q1` itself remain. -/
theorem identity_16_complex_weighted_of_integrable {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re)
    (hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, kadiriTestFn f s y *
          exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)) =
      (f 0 : ℂ) * ((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1))
      + riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
          (fun ρ ↦ (f 0 : ℂ) / (s - ρ) - laplaceTransform f (s - ρ))
      + laplaceTransform f (s - 1)
      + ((1 / (2 * (Real.pi : ℂ))) *
          (∫ t : ℝ,
            ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
              laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I))
              / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
          + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2) :=
  identity_16_complex_weighted hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hs
    (summable_kadiriTestFn_weighted_at_zeros hd hf_C2 hf_supp hf_d hf_deriv_0
      hf_deriv_d hs) hΓ_int

@[blueprint
  "kadiri-summable-lap-at-zeros"
  (title := "Summability of $\\sum_\\rho \\Re F(s - \\rho)$")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}, the sum
  $\sum_{\rho \in Z(\zeta)} \Re F(s - \rho)$ over the non-trivial zeros of $\zeta$ is
  convergent (Lean: `Summable`). -/)
  (proof := /-- Combine \ref{kadiri-laplace-re-decay} (giving $|\Re F(s-\rho)| \leq
  C/|\Im(s-\rho)|^2 = C/(\Im s - \gamma)^2$ for $|\gamma|$ large, since the real part
  $\Re(s-\rho) = \Re s - \beta$ stays in the bounded strip $[\Re s - 1, \Re s]$) with
  the unconditional crude counting bound $N(T) = O(T^{3/2})$ proved in
  the Backlund zero-count module: over the dyadic shells
  $|\gamma| \in [2^k, 2^{k+1})$ the shell count is $O(3^k)$ while each term is at
  most $4^{-k}$, so $\sum_{|\gamma| \geq 1} 1/|\gamma|^2 < \infty$. The finitely many
  small-$|\gamma|$ terms are absorbed by cofiniteness. The sharper
  \ref{kadiri-backlund-bound} route ($N(T) \ll T \log T$) is not needed here and
  remains the path to the explicit numerics. -/)
  (latexEnv := "lemma")
  (discussion := 1477)]
theorem summable_lap_re_at_zeros {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (hf_deriv2_d : derivWithin (fun x => derivWithin f (Set.Icc 0 d) x) (Set.Icc 0 d) d = 0)
    (s : ℂ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
                (laplaceTransform f (s - ρ.val)).re) := by
  obtain ⟨C, hC⟩ := laplaceTransform_re_decay hd hf_nonneg hf_C2 hf_supp hf_d
    hf_deriv_0 hf_deriv_d hf_deriv2_d (s.re - 1) s.re
  have htail : Summable (fun ρ : NontrivialZeros ↦
      C * (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ))) :=
    (summable_zeroImagSquareTail_shifted_unconditional s).mul_left C
  refine Summable.of_norm_bounded_eventually htail ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (nontrivialZeros_shifted_abs_im_lt_one_finite s)
  intro ρ hbad
  rw [Set.mem_setOf_eq] at hbad ⊢
  by_contra hsmall
  have him : 1 ≤ |(s - (ρ : ℂ)).im| := le_of_not_gt hsmall
  have hre : (ρ : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := ρ.property.1
  have hre_lo : s.re - 1 ≤ (s - (ρ : ℂ)).re := by
    rw [Complex.sub_re]
    linarith [hre.2]
  have hre_hi : (s - (ρ : ℂ)).re ≤ s.re := by
    rw [Complex.sub_re]
    linarith [hre.1]
  have hdecay := hC (s - (ρ : ℂ)) hre_lo hre_hi him
  apply hbad
  rw [Real.norm_eq_abs]
  calc |(laplaceTransform f (s - (ρ : ℂ))).re|
      ≤ C / (s - (ρ : ℂ)).im ^ 2 := hdecay
    _ = C * (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) := by
        rw [inv_pow, sq_abs, div_eq_mul_inv]

@[blueprint
  "kadiri-identity-16-complex"
  (title := "Complex form of equation (16)")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}: for every
  $s \in \mathbb{C}$ with $\Re s > 1$,
  $$ \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n)
   = f(0) \Bigl( \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} - \frac{1}{s - 1} \Bigr)
   + \sum_{\rho \in Z(\zeta)} \Bigl( \frac{f(0)}{s - \rho} - F(s - \rho) \Bigr)
   + F(s - 1)
   + \Bigl( \frac{1}{2\pi i} \int_{1/2 - i\infty}^{1/2 + i\infty}
       \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{z}{2}\right) \frac{F_2(s - z)}{(s - z)^2}\, dz
       + \frac{F_2(s)}{s^2} \Bigr). $$
  The zero sum is grouped: each summand is $\Phi(-\rho)$, the Laplace transform of the
  test function $\varphi(y) = (f(0) - f(y)) e^{-y s}$ at $-\rho$, equal to
  $-F_2(s-\rho)/(s-\rho)^2$ and hence of size $O(1/|\Im \rho|^2)$; the split sums
  $\sum_\rho 1/(s-\rho)$ and $\sum_\rho F(s-\rho)$ are individually divergent.
-/)
  (proof := /-- Apply \ref{kadiri-thm-3-1-q1} to the Kadiri test function
  $\varphi$; its hypotheses
  are discharged by \ref{kadiri-test-fn-contDiff} ($\varphi$ is $C^1$) and
  \ref{kadiri-test-fn-decay} (decay (B) with any $0 < b < \Re s - 1$, requiring
  $\Re s > 1$). The Laplace transform of $\varphi$ is computed by
  \ref{kadiri-test-fn-laplace}: $\Phi(z;\, s) = f(0)/(s+z) - F(s+z)$. In particular
  $\Phi(-1) = f(0)/(s-1) - F(s-1)$, $\Phi(-\rho) = f(0)/(s-\rho) - F(s-\rho)$,
  $\Phi(0) = f(0)/s - F(s)$, and $\Phi(-z) = f(0)/(s-z) - F(s-z)$ at $z = 1/2 + it$.
  Rewriting $F(s) = f(0)/s + F_2(s)/s^2$ via \ref{kadiri-laplace-ibp} (and likewise at
  $w = s - z$) collapses $\Phi(0) = -F_2(s)/s^2$ and $\Phi(-z) = -F_2(s-z)/(s-z)^2$ used
  inside the contour integral. Three terms of \ref{kadiri-thm-3-1-q1}'s conclusion vanish
  for this $\varphi$: $\varphi(0;\, s) = 0$ kills the
  $\varphi(0) \log \pi$ term, and $\varphi(-\log n;\, s) = 0$ for every $n \geq 1$
   kills the reflected discrete sum. Unfolding
  $\varphi(\log n;\, s) = (f(0) - f(\log n))/n^s$ gives
  $\sum_n \Lambda(n) \varphi(\log n;\, s) = f(0) \sum_n \Lambda(n)/n^s
   - \sum_n \Lambda(n) f(\log n)/n^s$; solving for $\sum_n \Lambda(n) f(\log n)/n^s$ and
  substituting the $\Phi$ values yields the right-hand side.  -/)
  (latexEnv := "sublemma")
  (discussion := 1494)]
theorem identity_16_complex {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (hf_deriv2_d : derivWithin (fun x => derivWithin f (Set.Icc 0 d) x) (Set.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)) =
      (f 0 : ℂ) * ((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1))
      + ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val))
      + laplaceTransform f (s - 1)
      + ((1 / (2 * (Real.pi : ℂ))) *
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
   = f(0) \Bigl( \Re \Bigl( \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} - \frac{1}{s - 1}
                  + \sum_{\rho \in Z(\zeta)} \Bigl( \frac{1}{\rho} + \frac{1}{s - \rho} \Bigr) \Bigr)
                  - \sum_{\rho \in Z(\zeta)} \Re \frac{1}{\rho} \Bigr)
   + \Re F(s - 1) - \sum_{\rho \in Z(\zeta)} \Re F(s - \rho)
   + \Re \Bigl( \frac{1}{2\pi i} \int_{1/2 - i\infty}^{1/2 + i\infty}
       \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{z}{2}\right) \frac{F_2(s - z)}{(s - z)^2}\, dz
       + \frac{F_2(s)}{s^2} \Bigr). $$
  This is the real-part form of \ref{kadiri-identity-16-complex}; the substantive
  derivation from \ref{kadiri-thm-3-1-q1} via the Kadiri test function
  $\varphi(y) = (f(0) - f(y)) e^{-y s} \mathbf{1}_{y \geq 0}$ lives in that sublemma.
  The zero contribution in the $f(0)$-coefficient uses the absolutely convergent
  Hadamard-paired block $\sum_\rho (1/\rho + 1/(s - \rho))$ together with the absolutely
  convergent real correction $\sum_\rho \Re(1/\rho)$, matching
  \ref{kadiri-hadamard-identity}; the standalone $\sum_\rho 1/(s - \rho)$ does not
  converge unconditionally. The restriction $\Re s > 1$ is where the Dirichlet series for
  $-\zeta'/\zeta(s)$ converges absolutely; this is also the range used in Kadiri's
  downstream zero-free region argument, so we do not extend further. -/)
  (proof := /-- Apply \ref{kadiri-identity-16-complex} to obtain the $\mathbb{C}$-valued
  equation, then take real parts of both sides. The grouped zero sum is absolutely
  summable (each summand is $-F_2(s-\rho)/(s-\rho)^2$ by \ref{kadiri-laplace-ibp}), so
  $\Re$ passes through it; each term splits as $f(0) \Re(1/(s-\rho)) - \Re F(s-\rho)$,
  and both real families are absolutely summable. Regrouping
  $\sum_\rho \Re(1/(s-\rho))$ into the paired block minus the $\Re(1/\rho)$ correction
  is legitimate by the paired-family summability. -/)
  (latexEnv := "lemma")
  (discussion := 1488)]
theorem identity_16 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (hf_deriv2_d : derivWithin (fun x => derivWithin f (Set.Icc 0 d) x) (Set.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)).re =
      f 0 * (((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1) +
                ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
                  (1 / (ρ.val : ℂ) + 1 / (s - ρ.val))).re -
              ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
                (1 / (ρ.val : ℂ)).re)
        + (laplaceTransform f (s - 1)).re
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
            (laplaceTransform f (s - ρ.val)).re
        + ((1 / (2 * (Real.pi : ℂ))) *
            (∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                laplaceTransform (fun u ↦ deriv (deriv f) u)
                  (s - (1 / 2 + (t : ℂ) * I))
                / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
            + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2).re := by
  have hcomplex := identity_16_complex hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d
    hf_deriv2_d hs
  have hsub := summable_lap_sub_pole_at_zeros hd hf_C2 hf_supp hf_d hf_deriv_0
    hf_deriv_d s
  have hre1 := summable_re_one_div_at_zeros s
  have hreF := summable_lap_re_at_zeros hd hf_nonneg hf_C2 hf_supp hf_d hf_deriv_0
    hf_deriv_d hf_deriv2_d s
  -- `Re` commutes with the grouped zero sum, which is genuinely summable
  have htsum_re :
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val))).re =
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)).re := by
    simpa using ContinuousLinearMap.map_tsum Complex.reCLM hsub
  -- pointwise real part of the grouped summand
  have hpt : ∀ ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
      ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)).re =
        f 0 * (1 / (s - ρ.val)).re - (laplaceTransform f (s - ρ.val)).re := by
    intro ρ
    have hmul : ((f 0 : ℝ) : ℂ) / (s - ρ.val) =
        ((f 0 : ℝ) : ℂ) * (1 / (s - ρ.val)) := div_eq_mul_one_div _ _
    rw [Complex.sub_re, hmul, Complex.re_ofReal_mul]
  -- split the real tsum of differences
  have hsplit :
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (f 0 * (1 / (s - ρ.val)).re - (laplaceTransform f (s - ρ.val)).re)) =
      f 0 * (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (1 / (s - ρ.val)).re) -
        ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (laplaceTransform f (s - ρ.val)).re := by
    rw [Summable.tsum_sub (hre1.mul_left (f 0)) hreF, tsum_mul_left]
  rw [hcomplex]
  simp only [Complex.add_re, Complex.sub_re]
  rw [htsum_re, tsum_congr hpt, hsplit, Complex.re_ofReal_mul, Complex.sub_re,
    re_shifted_sum_eq_paired_sub_re_inv s]
  ring


/-- The raw von Mangoldt Dirichlet sum is `-ζ'/ζ` on `1 < Re s` (the tsum form of
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`). -/
lemma tsum_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) = -deriv riemannZeta s / riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]

@[blueprint
  "kadiri-re-inner-eq"
  (title := "Inner real-part identity: collapsing to $T_1$")
  (statement := /-- For every $s \in \mathbb{C}$ with $\Re s > 1$,
  $$ \Re \Bigl( \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} - \frac{1}{s - 1}
                + \sum_{\rho \in Z(\zeta)} \Bigl( \frac{1}{\rho} + \frac{1}{s - \rho} \Bigr) \Bigr)
     - \sum_{\rho \in Z(\zeta)} \Re \frac{1}{\rho}
   = -\tfrac{1}{2} \log \pi
     + \tfrac{1}{2} \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{s}{2}+1\right). $$
  The zero block is the absolutely convergent Hadamard pairing of
  \ref{kadiri-hadamard-identity}, and the $\Re(1/\rho)$ correction is absolutely
  convergent; the standalone $\sum_\rho 1/(s - \rho)$ does not converge
  unconditionally. This is the identity that turns the $f(0)$-coefficient of
  equation (16) into the $T_1$ form of \ref{kadiri-prop-2-1}. -/)
  (proof := /-- For $\Re s > 1$ the Dirichlet series gives
  $\sum \Lambda(n)/n^s = -\zeta'/\zeta(s)$; substitute \ref{kadiri-hadamard-identity}
  (treating the equation as one in $\mathbb{C}$, not yet taking $\Re$). The $1/(s-1)$
  terms and the paired zero blocks cancel exactly, leaving
  $-B - \tfrac{1}{2}\log\pi + \tfrac{1}{2}\Gamma'/\Gamma(s/2+1)$. Taking real parts and
  applying \ref{kadiri-re-hadamardB-eq} cancels $\Re B$ against the
  $\sum_\rho \Re(1/\rho)$ correction, leaving the claim. -/)
  (latexEnv := "lemma")
  (discussion := 1478)]
theorem re_inner_eq {s : ℂ} (hs : 1 < s.re) :
    ((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1) +
       ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
         (1 / (ρ.val : ℂ) + 1 / (s - ρ.val))).re -
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ)).re =
    -(1 / 2 : ℝ) * Real.log Real.pi +
      (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re := by
  have hs1 : s ≠ 1 := by
    intro hs_eq
    rw [hs_eq] at hs
    norm_num at hs
  have hsZ : s ∉ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) := by
    intro hz
    exact (not_lt_of_gt hs) hz.1.2
  rw [tsum_vonMangoldt_eq hs, hadamard_identity s hs1 hsZ]
  ring_nf
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [re_hadamardB_eq]
  norm_num
  ring_nf

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
  (latexEnv := "proposition")]
theorem prop_2_1 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (hf_deriv2_d : derivWithin (fun x => derivWithin f (Set.Icc 0 d) x) (Set.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
                (laplaceTransform f (s - ρ.val)).re) ∧
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)).re =
      f 0 * (-(1 / 2 : ℝ) * Real.log Real.pi
              + (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re)
        + (laplaceTransform f (s - 1)).re
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
            (laplaceTransform f (s - ρ.val)).re
        + ((1 / (2 * (Real.pi : ℂ))) *
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
  ((1 / (2 * (Real.pi : ℂ))) *
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
  (latexEnv := "lemma")]
theorem eq_5 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ} (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d)) (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0) (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0) (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (hf_deriv2_d : derivWithin (fun x => derivWithin f (Set.Icc 0 d) x) (Set.Icc 0 d) d = 0) (κ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
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
  have hT1s : -(1 / 2 : ℝ) * Real.log Real.pi +
      (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re = T1 s := rfl
  have hT1sd : -(1 / 2 : ℝ) * Real.log Real.pi +
      (1 / 2 : ℝ) * (digamma ((s + (δ : ℂ)) / 2 + 1)).re = T1 (s + (δ : ℂ)) := rfl
  have hT2s : ((1 / (2 * (Real.pi : ℂ))) *
      (∫ t : ℝ,
        ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
          laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I))
          / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
      + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2).re = T2 f s := rfl
  have hT2sd : ((1 / (2 * (Real.pi : ℂ))) *
      (∫ t : ℝ,
        ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
          laplaceTransform (fun u ↦ deriv (deriv f) u) (s + (δ : ℂ) - (1 / 2 + (t : ℂ) * I))
          / (s + (δ : ℂ) - (1 / 2 + (t : ℂ) * I)) ^ 2)
      + laplaceTransform (fun u ↦ deriv (deriv f) u) (s + (δ : ℂ)) / (s + (δ : ℂ)) ^ 2).re =
      T2 f (s + (δ : ℂ)) := rfl
  rw [hLHS, h1.2, h2.2, hZeros, hT1s, hT1sd, hT2s, hT2sd]
  simp only [Δ1, Δ2, D]
  ring_nf

end Kadiri
