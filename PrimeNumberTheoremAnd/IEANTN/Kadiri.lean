import Architect
import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
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
  \ref{kadiri-prop-2-1}. -/)
  (latexEnv := "definition")
  (discussion := 1474)]
noncomputable def hadamardB : ℂ := sorry

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
private lemma laplaceKernel_hasDerivAt (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => exp (-w * (y : ℂ)))
      (-w * exp (-w * (x : ℂ))) x := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id x).ofReal_comp.const_mul (-w)).cexp

private lemma laplaceKernel_antideriv_hasDerivAt {w : ℂ} (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -exp (-w * (y : ℂ)) / w)
      (exp (-w * (x : ℂ))) x := by
  have h := (laplaceKernel_hasDerivAt w x).neg.div_const w
  convert h using 1
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
      simpa [I, Set.uIcc_of_le hd.le] using continuous_ofReal.comp_continuousOn hreal
    exact hdf_cont.intervalIntegrable
  have hd2f_int : IntervalIntegrable (fun t => (d2f t : ℂ)) volume 0 d := by
    have hd2f_cont : ContinuousOn (fun t => (d2f t : ℂ)) (Set.uIcc (0 : ℝ) d) := by
      have hreal : ContinuousOn d2f I := by
        simpa [d2f] using hdf_C1.continuousOn_derivWithin (uniqueDiffOn_Icc hd) (by norm_num)
      simpa [I, Set.uIcc_of_le hd.le] using continuous_ofReal.comp_continuousOn hreal
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
  simpa [kadiriTestFnRightTail] using hexp.const_mul (f 0 : ℂ)

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
        simpa [kadiriTestFnRightTail] using
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
    (∫ y in (.Ioi (0 : ℝ)), kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s + z) - laplaceTransform f (s + z) := by
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
      simpa [Complex.norm_exp, neg_mul] using h
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

@[blueprint
  "kadiri-identity-16-complex"
  (title := "Complex form of equation (16)")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}: for every
  $s \in \mathbb{C}$ with $\Re s > 1$,
  $$ \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n)
   = f(0) \Bigl( \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} - \frac{1}{s - 1}
                  + \sum_{\rho \in Z(\zeta)} \frac{1}{s - \rho} \Bigr)
   + F(s - 1) - \sum_{\rho \in Z(\zeta)} F(s - \rho)
   + \Bigl( \frac{1}{2\pi i} \int_{1/2 - i\infty}^{1/2 + i\infty}
       \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{z}{2}\right) \frac{F_2(s - z)}{(s - z)^2}\, dz
       + \frac{F_2(s)}{s^2} \Bigr). $$
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
  This is the real-part form of \ref{kadiri-identity-16-complex}; the substantive
  derivation from \ref{kadiri-thm-3-1-q1} via the Kadiri test function
  $\varphi(y) = (f(0) - f(y)) e^{-y s} \mathbf{1}_{y \geq 0}$ lives in that sublemma.
  The restriction $\Re s > 1$ is where the Dirichlet series for $-\zeta'/\zeta(s)$
  converges absolutely and the $\sum_\rho 1/(s - \rho)$ regularization makes sense; this
  is also the range used in Kadiri's downstream zero-free region argument, so we do not
  extend further. -/)
  (proof := /-- Apply \ref{kadiri-identity-16-complex} to obtain the $\mathbb{C}$-valued
  equation, then take real parts of both sides. The $f(0)$ factor extracts via
  $\Re((f(0) : \mathbb{C}) \cdot X) = f(0) \cdot \Re X$ (since $f(0) \in \mathbb{R}$), and
  the $\rho$-tsum commutes with $\Re$ via the continuous linear map
  $\Re \colon \mathbb{C} \to \mathbb{R}$ (`ContinuousLinearMap.map\_tsum`), modulo complex
  summability of $\sum_\rho F(s - \rho)$ — derivable from
  \ref{kadiri-summable-lap-at-zeros} together with the analogous Im-summability (would need
  a `laplaceTransform\_im\_decay` lemma paralleling \ref{kadiri-laplace-re-decay}). To be
  formalised. -/)
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
  rw [hLHS, h1.2, h2.2, hZeros]
  simp only [Δ1, Δ2, D, T1, T2]
  ring_nf

end Kadiri
