import Architect
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Fourier.FourierTransform
import PrimeNumberTheoremAnd.ZetaDefinitions

blueprint_comment /--
\section{Approximating the Riemann zeta function}
-/

blueprint_comment /--
We want a good explicit estimate on
$$\sum_{n\leq a} \frac{1}{n^s} - \int_0^{a} \frac{du}{u^s},$$
for $a$ a half-integer. As it turns out, this is the same problem as that of approximating
$\zeta(s)$ by a sum $\sum_{n\leq a} n^{-s}$. This is one of the two\footnote{The other one is
the approximate functional equation.} main, standard ways of approximating $\zeta(s)$.

The non-explicit version of the result was first proved in
\cite[Lemmas 1 and 2]{zbMATH02601353}. The proof there uses first-order Euler-Maclaurin
combined with a decomposition of $\lfloor x\rfloor - x +1/2$ that turns out to be equivalent
to Poisson summation.
The exposition in \cite[\S 4.7--4.11]{MR882550} uses first-order Euler-Maclaurin and
van de Corput's Process B; the main idea of the latter is Poisson summation.

There are already several explicit versions of the result in the literature.
In \cite{MR1687658}, \cite{MR3105334} and \cite{MR4114203}, what we have is successively
sharper explicit versions of Hardy and Littlewood's original proof.
The proof in \cite[Lemma 2.10]{zbMATH07557592} proceeds simply by a careful estimation of
the terms in high-order Euler-Maclaurin; it does not use Poisson summation. Finally,
\cite{delaReyna} is an explicit version of \cite[\S 4.7--4.11]{MR882550}; it
gives a weaker bound than \cite{MR4114203} or \cite{zbMATH07557592}. The strongest of these
results is \cite{MR4114203}.

We will give another version here, in part because we wish to relax conditions -- we will
work with $\left|\Im s\right| < 2\pi a$ rather than $\left|\Im s\right| \leq a$ -- and in
part to show that one can prove an asymptotically optimal result easily and concisely.
We will use first-order Euler-Maclaurin and Poisson summation. We assume that $a$ is a
half-integer; if one inserts the same assumption into \cite[Lemma 2.10]{zbMATH07557592},
one can improve the result there, yielding an error term closer to the one here.

For additional context, see
\url{https://leanprover.zulipchat.com/\#narrow/channel/423402-PrimeNumberTheorem.2B/topic/Let.20us.20formalize.20an.20appendix}
-/

namespace ZetaAppendix

open Real Complex

-- may want to move this to a more globally accessible location

@[blueprint
  "e-def"
  (title := "e")
  (statement := /-- We recall that $e(\alpha) = e^{2\pi i \alpha}$. -/)]
noncomputable def e (α : ℝ) : ℂ := exp (2 * π * I * α)

blueprint_comment /--
\subsection{The decay of a Fourier transform}
Our first objective will be to estimate the Fourier transform of
$t^{-s} \mathbb{1}_{[a,b]}$. In particular, we will show that, if $a$ and $b$ are
half-integers, the Fourier cosine transform has quadratic decay {\em when evaluated at
integers}. In general, for real arguments, the Fourier transform of a discontinuous
function such as $t^{-s} \mathbb{1}_{[a,b]}$ does not have quadratic decay.
-/

@[blueprint
  "lem:aachIBP"
  (title := "Fourier transform of a truncated power law")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.
Let $\nu\in \mathbb{R}\setminus \{0\}$, $b>a>\frac{|\tau|}{2\pi |\nu|}$.
Then
\begin{equation}\label{eq:aachquno}\int_a^b t^{-s} e(\nu t) dt =
 \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b
 + \sigma \int_a^b \frac{t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} e(\varphi_\nu(t)) dt
 + \int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt,
\end{equation}
where $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$.
-/)
  (proof := /--
We write $t^{-s} e(\nu t) = t^{-\sigma} e(\varphi_\nu(t))$ and integrate by parts with
$u = t^{-\sigma}/(2\pi i \varphi_\nu'(t))$, $v = e(\varphi_\nu(t))$.
Here $\varphi_\nu'(t) = \nu - \tau/(2\pi t)\ne 0$ for $t\in [a,b]$ because
$t\geq a > |\tau|/(2\pi |\nu|)$ implies $|\nu|>|\tau|/(2\pi t)$.
Clearly
\[u dv = \frac{ t^{-\sigma}}{2\pi i \varphi_\nu'(t)} \cdot 2\pi i \varphi_\nu'(t)
  e(\varphi_\nu(t)) dt = t^{-\sigma} e(\varphi_\nu(t)) dt,\]
while
\[du = \left(\frac{-\sigma t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)}
  - \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}\right) dt.\]
-/)
  (latexEnv := "lemma")
  (discussion := 546)]
theorem lemma_aachIBP (s : ℂ) (hsigma : 0 ≤ s.re) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
    let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℂ := fun t ↦ (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
      s.re * ∫ t in Set.Icc a b, (t ^ (-s.re - 1) : ℝ) / (2 * π * I * (deriv φ t)) * e (φ t) +
      ∫ t in Set.Icc a b, (t ^ (-s.re) : ℝ) * (deriv (deriv φ) t) /
        (2 * π * I * (deriv φ t) ^ 2) * e (φ t) := by
  sorry

@[blueprint
  "lem:aachra"
  (title := "Total variation of a function with monotone absolute value")
  (statement := /--
Let $g:[a,b]\to \mathbb{R}$ be continuous, with $|g(t)|$ non-increasing. Then
$g$ is monotone, and $\|g\|_{\mathrm{TV}} = |g(a)|-|g(b)|$.
-/)
  (proof := /--
Suppose $g$ changed sign: $g(a')>0>g(b')$ or $g(a') <0 < g(b')$ for some
$a\leq a'< b'\leq b$. By IVT, there would be an $r\in [a',b']$ such that $g(r)=0$.
Since $|g|$ is non-increasing, $g(b')=0$; contradiction. So, $g$ does not change sign:
either $g\leq 0$ or $g\geq 0$.

Thus, there is an $\varepsilon\in \{-1,1\}$ such that $g(t) = \varepsilon |g(t)|$ for all
$t\in [a,b]$. Hence, $g$ is monotone. Then $\|g\|_{\mathrm{TV}} = |g(a)-g(b)|$.
Since $|g(a)|\geq |g(b)|$ and $g(a)$, $g(b)$ are either both non-positive or non-negative,
$|g(a)-g(b)| = |g(a)|-|g(b)|$.
-/)
  (latexEnv := "lemma")
  (discussion := 547)]
theorem lemma_aachra {a b : ℝ} (ha : a < b) (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    BoundedVariationOn g (Set.Icc a b) ∧
    (eVariationOn g (Set.Icc a b)).toReal = |g a| - |g b| := by
  sorry

@[blueprint
  "lem:aachmonophase"
  (title := "Non-stationary phase estimate")
  (statement := /--
Let $\varphi:[a,b]\to \mathbb{R}$ be $C^1$ with $\varphi'(t)\ne 0$ for all $t\in [a,b]$.
Let $h:[a,b]\to \mathbb{R}$ be such that $g(t) = h(t)/\varphi'(t)$ is continuous and
$|g(t)|$ is non-increasing. Then
\[\left|\int_a^b h(t) e(\varphi(t)) dt\right|\leq \frac{|g(a)|}{\pi}.\]
-/)
  (proof := /--
Since $\varphi$ is $C^1$, $e(\varphi(t))$ is $C^1$, and
$h(t) e(\varphi(t)) = \frac{h(t)}{2\pi i \varphi'(t)} \frac{d}{dt} e(\varphi(t))$ everywhere.
By Lemma \ref{lem:aachra}, $g$ is of bounded variation. Hence, we can integrate by parts:
\[\int_a^b h(t) e(\varphi(t)) dt =
  \left. \frac{h(t) e(\varphi(t))}{2\pi i \varphi'(t)}\right|_a^b -
  \int_a^b e(\varphi(t))\, d\left(\frac{h(t)}{2\pi i \varphi'(t)}\right).
\]
The first term on the right has absolute value $\leq \frac{|g(a)|+|g(b)|}{2\pi}$.
Again by Lemma \ref{lem:aachra},
\[\left|
\int_a^b e(\varphi(t))\, d\left(\frac{h(t)}{2\pi i \varphi'(t)}\right)
\right|\leq \frac{1}{2\pi} \|g\|_{\mathrm{TV}} = \frac{|g(a)|-|g(b)|}{2\pi}.
\]
We are done by
$\frac{|g(a)|+|g(b)|}{2\pi} + \frac{|g(a)|-|g(b)|}{2\pi} = \frac{|g(a)|}{\pi}$.
-/)
  (latexEnv := "lemma")
  (discussion := 548)]
theorem lemma_aachmonophase {a b : ℝ} (ha : a < b) (φ : ℝ → ℝ)
    (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b)) (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0)
    (h g : ℝ → ℝ) (hg : ∀ t, g t = h t / deriv φ t) (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    ‖∫ t in Set.Icc a b, h t * e (φ t)‖ ≤ |g a| / π := by
  sorry

@[blueprint
  "lem:aachdecre"
  (title := "A decreasing function")
  (statement := /--
Let $\sigma\geq 0$, $\tau\in \mathbb{R}$, $\nu \in \mathbb{R}\setminus \{0\}$.
Let $b>a>\frac{|\tau|}{2\pi |\nu|}$. Then, for any $k\geq 1$,
$f(t) = t^{-\sigma-k} |2\pi \nu-\tau/t|^{-k-1}$ is decreasing on $[a,b]$.
-/)
  (proof := /--
Let $a\leq t\leq b$. Since $\left|\frac{\tau}{t \nu}\right| < 2\pi$, we see that
$2\pi-\frac{\tau}{\nu t} >0$, and so
$|2\pi \nu-\tau/t|^{-k-1} = |\nu|^{-k-1} \left(2\pi - \frac{\tau}{t \nu}\right)^{-k-1}$.
Now we take logarithmic derivatives:
\[t (\log f(t))' = - (\sigma+k) - (k+1) \frac{\tau/t}{2\pi \nu - \tau/t}
= -\sigma - \frac{2\pi k + \frac{\tau}{t \nu}}{2\pi - \frac{\tau}{t \nu}} < -\sigma \leq 0,\]
since, again by $\frac{|\tau|}{t |\nu|} < 2\pi$ and $k\geq 1$, we have
$2\pi k + \frac{\tau}{t \nu}>0$, and, as we said, $2\pi - \frac{\tau}{t \nu}>0$.
-/)
  (latexEnv := "lemma")
  (discussion := 549)]
theorem lemma_aachdecre (σ : ℝ) (hσ : 0 ≤ σ) (τ : ℝ) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |τ| / (2 * π * |ν|)) (hb : b > a) (k : ℕ) (hk : 1 ≤ k) :
    let f : ℝ → ℝ := fun t ↦ t ^ (-σ - k) * |2 * π * ν - τ / t| ^ (-(k : ℝ) - 1)
    AntitoneOn f (Set.Icc a b) := by
  sorry

@[blueprint
  "lem:aachfour"
  (title := "Estimating an integral")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.
Let $\nu \in \mathbb{R}\setminus \{0\}$, $b>a>\frac{|\tau|}{2\pi |\nu|}$.
Then
\[\int_a^b t^{-s} e(\nu t) dt =
 \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b +
\frac{a^{-\sigma-1}}{2\pi^2} O^*\left(\frac{\sigma}{(\nu-\vartheta)^2} +
\frac{|\vartheta|}{|\nu-\vartheta|^3}\right),
\]
where $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$ and
$\vartheta = \frac{\tau}{2\pi a}$.
-/)
  (proof := /--
Apply Lemma~\ref{lem:aachIBP}. Since $\varphi_\nu'(t) = \nu - \tau/(2\pi t)$, we know by
Lemma \ref{lem:aachdecre} (with $k=1$) that
$g_1(t) = \frac{t^{-\sigma-1}}{(\varphi_\nu'(t))^2}$ is decreasing on $[a,b]$.
We know that $\varphi_\nu'(t)\ne 0$ for $t\geq a$ by $a>\frac{|\tau|}{2\pi |\nu|}$, and so
we also know that $g_1(t)$ is continuous for $t\geq a$.
Hence, by Lemma \ref{lem:aachmonophase},
\[\left|\int_a^b \frac{t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} e(\varphi_\nu(t)) dt \right|
  \leq \frac{1}{2\pi} \cdot \frac{|g_1(a)|}{\pi}
  = \frac{1}{2\pi^2} \frac{a^{-\sigma-1}}{\left|\nu - \vartheta\right|^2},\]
since $\varphi_\nu'(a) = \nu - \vartheta$. We remember to include the factor of $\sigma$
in front of an integral in \eqref{eq:aachquno}.

Since $\varphi_\nu'(t)$ is as above and $\varphi_\nu''(t) = \tau/(2\pi t^2)$, we know
by Lemma \ref{lem:aachdecre} (with $k=2$) that
$g_2(t) = \frac{t^{-\sigma} |\varphi_\nu''(t)|}{|\varphi_\nu'(t)|^3} =
\frac{|\tau|}{2\pi} \frac{t^{-\sigma-2}}{|\varphi_\nu'(t)|^3}$ is decreasing on $[a,b]$;
we also know, as before, that $g_2(t)$ is continuous.
Hence, again by Lemma \ref{lem:aachmonophase},
\[\left|\int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt\right|\leq \frac{1}{2\pi} \frac{|g_2(a)|}{\pi} = \frac{1}{2\pi^2}
 \frac{a^{-\sigma-1} |\vartheta|}{\left|\nu - \vartheta\right|^3}.
\]
-/)
  (latexEnv := "lemma")
  (discussion := 550)]
theorem lemma_aachfour (s : ℂ) (hsigma : 0 ≤ s.re) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
    let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℂ := fun t ↦ (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    let ϑ : ℝ := s.im / (2 * π * a)
    ∃ E, ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
      ((a ^ (-s.re - 1) : ℝ) / (2 * π ^ 2)) * E ∧
      ‖E‖ ≤ s.re / (|ν - ϑ| ^ 2) + |ϑ| / (|ν - ϑ| ^ 3) := by
  sorry

def _root_.Real.IsHalfInteger (x : ℝ) : Prop := ∃ k : ℤ, x = k + 1 / 2

@[blueprint
  "lem:aachcanc"
  (title := "Estimating an sum")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma,\tau \in \mathbb{R}$.
Let $n\in \mathbb{Z}_{>0}$. Let $a,b\in \mathbb{Z} + \frac{1}{2}$,
$b>a>\frac{|\tau|}{2\pi n}$.
Write $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$.
Then
\[\frac{1}{2} \sum_{\nu = \pm n}
  \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b =
  \left. \frac{(-1)^n t^{-s} \cdot \frac{\tau}{2\pi t}}
  {2\pi i \left(n^2 - \left(\frac{\tau}{2\pi t}\right)^2\right)}\right|_a^b.
\]
-/)
  (proof := /--
Since $e(\varphi_\nu(t)) = e(\nu t) t^{-i \tau} = (-1)^{\nu} t^{-i \tau}$ for any
half-integer $t$ and any integer $\nu$,
\[\left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b =
\left. \frac{(-1)^{\nu} t^{-s}}{2\pi i \varphi_\nu'(t)}\right|_a^b
\]
for $\nu = \pm n$. Clearly $(-1)^{\nu} = (-1)^n$.
Since $\varphi_\nu'(t) = \nu - \alpha$ for $\alpha = \frac{\tau}{2\pi t}$,
\[\frac{1}{2} \sum_{\nu = \pm n} \frac{1}{\varphi_\nu'(t)} = \frac{1/2}{n - \alpha} +
\frac{1/2}{- n - \alpha} = \frac{-\alpha}{\alpha^2-n^2} = \frac{\alpha}{n^2-\alpha^2}.
\]
-/)
  (latexEnv := "lemma")
  (discussion := 551)]
theorem lemma_aachcanc (s : ℂ) {n : ℤ} (hn : 0 < n) {a b : ℝ}
    (ha : a > |s.im| / (2 * π * n)) (hb : b > a)
    (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) :
    let ϕ : ℝ → ℝ → ℝ := fun ν t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℝ → ℂ := fun ν t ↦
      (t ^ (-s.re) : ℝ) * e (ϕ ν t) / (2 * π * I * (deriv (ϕ ν) t))
    let Ψ : ℝ → ℂ := fun t ↦ (-1) ^ n * (t ^ (-s) : ℂ) * (s.im / (2 * π * t)) /
      (2 * π * I * (n ^ 2 - (s.im / (2 * π * t)) ^ 2))
    (1 / 2) * (Φ n b - Φ n a + Φ (-n) b - Φ (-n) a) = Ψ b - Ψ a := by
  sorry

blueprint_comment /--
It is this easy step that gives us quadratic decay on $n$. It is just as
in the proof of van der Corput's Process B in, say, \cite[I.6.3, Thm.~4]{zbMATH06471876}.
-/

@[blueprint
  "prop:applem"
  (title := "Estimating a Fourier cosine integral")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.
Let $a,b\in \mathbb{Z} + \frac{1}{2}$, $b>a>\frac{|\tau|}{2\pi}$.
Write $\vartheta = \frac{\tau}{2\pi a}$. Then, for any integer $n\geq 1$,
$$\begin{aligned}\int_a^b t^{-s} \cos 2\pi n t\, dt &=
\left. \left(\frac{(-1)^n t^{-s}}{2\pi i} \cdot
  \frac{\frac{\tau}{2\pi t}}{n^2 - \left(\frac{\tau}{2\pi t}\right)^2}\right)\right|_a^b \\
&\quad+ \frac{a^{-\sigma-1}}{4\pi^2}\, O^*\left(\frac{\sigma}{(n-\vartheta)^2}
  + \frac{\sigma}{(n+\vartheta)^2}
  + \frac{|\vartheta|}{|n-\vartheta|^3}
  + \frac{|\vartheta|}{|n+\vartheta|^3}\right).\end{aligned}$$
-/)
  (proof := /--
Write $\cos 2\pi n t = \frac{1}{2} (e(n t) + e(-n t))$. Since $n\geq 1$ and
$a>\frac{|\tau|}{2\pi}$, we know that $a>\frac{|\tau|}{2 \pi n}$, and so we can apply
Lemma \ref{lem:aachfour} with $\nu = \pm n$.
We then apply Lemma~\ref{lem:aachcanc} to combine the boundary contributions
$\left. \right|_a^b$ for $\nu=\pm n$.
-/)
  (latexEnv := "proposition")
  (discussion := 552)]
theorem proposition_applem (s : ℂ) (hsigma : 0 ≤ s.re) {a b : ℝ} (ha : a > |s.im| / (2 * π))
    (hb : b > a) (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) {n : ℕ} (hn : 1 ≤ n) :
    let ϑ : ℝ := s.im / (2 * π * a)
    ∃ E, ∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * Real.cos (2 * π * (n : ℝ) * t) =
      ((-1) ^ n * (b ^ (-s) : ℂ) * (s.im / (2 * π * b)) /
        (2 * π * I * ((n : ℝ) ^ 2 - (s.im / (2 * π * b)) ^ 2)) -
       (-1) ^ n * (a ^ (-s) : ℂ) * (s.im / (2 * π * a)) /
        (2 * π * I * ((n : ℝ) ^ 2 - (s.im / (2 * π * a)) ^ 2))) +
      ((a ^ (-s.re - 1) : ℝ) / (4 * π ^ 2)) * E ∧
      ‖E‖ ≤ s.re / ((n - ϑ) ^ 2) + s.re / ((n + ϑ) ^ 2) +
        |ϑ| / (|n - ϑ| ^ 3) + |ϑ| / (|n + ϑ| ^ 3) := by
  sorry


blueprint_comment /--
\subsection{Approximating zeta(s)}
We start with an application of Euler-Maclaurin.
-/

@[blueprint
  "lem:abadeulmac"
  (title := "Identity for a partial sum of zeta(s)")
  (statement := /--
Let $b>0$, $b\in \mathbb{Z} + \frac{1}{2}$.
Then, for all $s\in \mathbb{C}\setminus \{1\}$ with $\Re s > 0$,
\begin{equation}\label{eq:abak1}
  \sum_{n\leq b} \frac{1}{n^s} = \zeta(s) + \frac{b^{1-s}}{1-s}
  + s \int_b^\infty \left(\{y\}-\frac{1}{2}\right) \frac{dy}{y^{s+1}}.
\end{equation}
-/)
  (proof := /--
Assume first that $\Re s > 1$. By first-order Euler-Maclaurin and
$b\in \mathbb{Z}+\frac{1}{2}$,
\[\sum_{n>b}\frac{1}{n^s} = \int_b^\infty \frac{dy}{y^s} + \int_b^\infty
 \left(\{y\}-\frac{1}{2}\right) d\left(\frac{1}{y^s}\right).
\]
Here $\int_b^\infty \frac{dy}{y^s} = -\frac{b^{1-s}}{1-s}$ and
$d\left(\frac{1}{y^s}\right) = - \frac{s}{y^{s+1}} dy$.
Hence, by $\sum_{n\leq b} \frac{1}{n^s} = \zeta(s) - \sum_{n>b} \frac{1}{n^s}$
for $\Re s > 1$,
$$\sum_{n\leq b} \frac{1}{n^s} = \zeta(s) + \frac{b^{1-s}}{1-s} +
\int_b^\infty \left(\{y\}-\frac{1}{2}\right) \frac{s}{y^{s+1}} dy.$$
Since the integral converges absolutely for $\Re s > 0$, both sides extend holomorphically
to $\{s\in \mathbb{C}: \Re s>0, s\ne 1\}$; thus, the equation holds throughout that region.
-/)
  (latexEnv := "lemma")
  (discussion := 566)]
theorem lemma_abadeulmac {b : ℝ} (hb : 0 < b) (hb' : b.IsHalfInteger) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, (n : ℂ) ^ (-s) =
      riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) +
      s * ∫ y in Set.Ioi b, (Int.fract y - 1 / 2) * (y ^ (-(s.re + 1)) : ℝ) := by
  sorry

@[blueprint
  "lem:abadtoabsum"
  (title := "Estimate for a partial sum of $\\zeta(s)$")
  (statement := /--
Let $b>a>0$, $b\in \mathbb{Z} + \frac{1}{2}$.
Then, for all $s\in \mathbb{C}\setminus \{1\}$ with $\sigma = \Re s > 0$,
$$\sum_{n\leq a} \frac{1}{n^s} = -\sum_{a < n\leq b} \frac{1}{n^s} + \zeta(s)
  + \frac{b^{1-s}}{1-s} + O^*\left(\frac{|s|}{2 \sigma b^\sigma}\right).$$
-/)
  (proof := /--
By Lemma \ref{lem:abadeulmac}, $\sum_{n\leq a} = \sum_{n\leq b} - \sum_{a < n\leq b}$,
$\left|\{y\}-\frac{1}{2}\right| \leq \frac{1}{2}$ and
$\int_b^\infty \frac{dy}{|y^{s+1}|} = \frac{1}{\sigma b^\sigma}$.
-/)
  (latexEnv := "lemma")
  (discussion := 567)]
theorem lemma_abadtoabsum {a b : ℝ} (hb : 0 < a) (hb' : b.IsHalfInteger) (hab : b > a) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∃ E, ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
      -∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) +
      riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) + E ∧
      ‖E‖ ≤ ‖s‖ / (2 * s.re * (b ^ s.re : ℝ)) := by
  sorry

@[blueprint
  "lem:abadusepoisson"
  (title := "Poisson summation for a partial sum of $\\zeta(s)$")
  (statement := /--
Let $a,b\in \mathbb{R}\setminus \mathbb{Z}$, $b>a>0$. Let $s\in \mathbb{C}\setminus \{1\}$.
Define $f:\mathbb{R}\to\mathbb{C}$ by $f(y) = 1_{[a,b]}(y)/y^s$. Then
$$\sum_{a < n\leq b} \frac{1}{n^s} = \frac{b^{1-s} - a^{1-s}}{1-s}
  + \lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n)).$$
-/)
  (proof := /--
Since $a\notin \mathbb{Z}$, $\sum_{a < n\leq b} \frac{1}{n^s} = \sum_{n\in \mathbb{Z}} f(n)$.
By Poisson summation (as in \cite[Thm.~D.3]{MR2378655})
$$\sum_{n\in \mathbb{Z}} f(n) = \lim_{N\to \infty} \sum_{n=-N}^N \widehat{f}(n) =
\widehat{f}(0) + \lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n)),$$
where we use the facts that $f$ is in $L^1$, of bounded variation, and
(by $a,b\not\in \mathbb{Z}$) continuous at every integer. Now
$$\widehat{f}(0) = \int_{\mathbb{R}} f(y) dy
  = \int_a^b \frac{dy}{y^s} = \frac{b^{1-s}-a^{1-s}}{1-s}.$$
-/)
  (latexEnv := "lemma")
  (discussion := 568)]
theorem lemma_abadusepoisson {a b : ℝ} (ha : ¬∃ n : ℤ, a = n) (hb : ¬∃ n : ℤ, b = n)
    (hab : b > a) (ha' : 0 < a) {s : ℂ} (hs1 : s ≠ 1) :
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    ∃ L : ℂ, Filter.atTop.Tendsto
      (fun (N : ℕ) ↦ ∑ n ∈ Finset.Ioc 1 N,
        (FourierTransform.fourier f n + FourierTransform.fourier f (-n))) (nhds L) ∧
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) =
        ((b ^ (1 - s) : ℂ) - (a ^ (1 - s) : ℂ)) / (1 - s) + L := by
  sorry

blueprint_comment /--
We could prove these equations starting from Euler's product for $\sin \pi z$.
-/

@[blueprint
  "lem:abadeuleulmit1"
  (title := "Euler/Mittag-Leffler expansion for cosec")
  (statement := /--
Let $z\in \mathbb{C}$, $z\notin \mathbb{Z}$. Then
\[ \frac{\pi}{\sin \pi z} = \frac{1}{z} +
 \sum_n (-1)^n\left(\frac{1}{z - n} + \frac{1}{z + n}\right).
\]
-/)
  (proof := /--
Let us start from the Mittag-Leffler expansion
$\pi \cot \pi s = \frac{1}{s} + \sum_n \left(\frac{1}{s-n} + \frac{1}{s+n}\right)$.

Applying the trigonometric identity
$\cot u - \cot \left(u + \frac{\pi}{2}\right) = \cot u + \tan u = \frac{2}{\sin 2 u}$
with $u=\pi z/2$, and letting $s = z/2$, $s = (z+1)/2$, we see that
\[\begin{aligned}\frac{\pi}{\sin \pi z}
  &= \frac{\pi}{2} \cot \frac{\pi z}{2} - \frac{\pi}{2} \cot \frac{\pi (z+1)}{2} \\
  &= \frac{1/2}{z/2} +
    \sum_n \left(\frac{1/2}{\frac{z}{2} -n} + \frac{1/2}{\frac{z}{2} +n}\right)
    -\frac{1/2}{(z+1)/2}
    - \sum_n \left(\frac{1/2}{\frac{z+1}{2} -n} + \frac{1/2}{\frac{z+1}{2} +n}\right)\\
  &= \frac{1}{z} + \sum_n \left(\frac{1}{z - 2 n} + \frac{1}{z + 2 n}\right) -
    \sum_n \left(\frac{1}{z - (2 n - 1)} + \frac{1}{z + (2 n - 1)}\right)
\end{aligned}\]
after reindexing the second sum. Regrouping terms again, we obtain our equation.
-/)
  (latexEnv := "lemma")
  (discussion := 569)]
theorem lemma_abadeuleulmit1 {z : ℂ} (hz : ¬∃ n : ℤ, z = n) :
    (π / Complex.sin (π * z) : ℂ) =
      (1 / z : ℂ) + ∑' n : ℤ, (-1) ^ n * ((1 / (z - n) : ℂ) + (1 / (z + n) : ℂ)) := by
  sorry

@[blueprint
  "lem:abadeulmit2"
  (title := "Euler/Mittag-Leffler expansion for cosec squared")
  (statement := /--
Let $z\in \mathbb{C}$, $z\notin \mathbb{Z}$. Then
\[\frac{\pi^2}{\sin^2 \pi z} = \sum_{n=-\infty}^\infty \frac{1}{(z-n)^2}.\]
-/)
  (proof := /--
Differentiate the expansion of $\pi \cot \pi z$ term-by-term because it converges
uniformly on compact subsets of $\mathbb{C}\setminus \mathbb{Z}$.
By $\left(\pi \cot \pi z\right)' = - \frac{\pi^2}{\sin^2 \pi z}$ and
$\left(\frac{1}{z\pm n}\right)' = -\frac{1}{(z\pm n)^2}$, we are done.
-/)
  (latexEnv := "lemma")
  (discussion := 570)]
theorem lemma_abadeulmit2 {z : ℂ} (hz : ¬∃ n : ℤ, z = n) :
    (π ^ 2 / (Complex.sin (π * z) ^ 2 : ℂ)) = ∑' n : ℤ, (1 / ((z - n) ^ 2 : ℂ)) := by
  sorry

@[blueprint
  "lem:abadimpseri"
  (title := "Estimate for an inverse cubic series")
  (statement := /--
For $\vartheta\in \mathbb{R}$ with $0\leq |\vartheta|< 1$,
\[\sum_n\left(\frac{1}{(n-\vartheta)^3} + \frac{1}{(n+\vartheta)^3}\right)
\leq \frac{1}{(1-|\vartheta|)^3} + 2\zeta(3)-1.\]
-/)
  (proof := /--
Since $\frac{1}{(n-\vartheta)^3} + \frac{1}{(n+\vartheta)^3}$ is even,
we may replace $\vartheta$ by $|\vartheta|$. Then we rearrange the sum:
\[\sum_{n=1}^\infty \left(\frac{1}{(n-|\vartheta|)^3} + \frac{1}{(n+|\vartheta|)^3}\right)
  = \frac{1}{(1-|\vartheta|)^3}
  + \sum_{n=1}^\infty \left(\frac{1}{\left(n+1-|\vartheta|\right)^3}
  + \frac{1}{\left(n+|\vartheta|\right)^3}\right).\]
We may write $(n+1-|\vartheta|)^3$, $(n+|\vartheta|)^3$
as $(n+\frac{1}{2}-t)^3$, $(n+\frac{1}{2} + t)^3$ for $t = |\vartheta|-1/2$.
Since $1/u^3$ is convex, $\frac{1}{(n+1/2-t)^3} + \frac{1}{(n+1/2+t)^3}$ reaches its
maximum on $[-1/2,1/2]$ at the endpoints. Hence
\[\sum_{n=1}^\infty \left(\frac{1}{\left(n+1-|\vartheta|\right)^3}
  + \frac{1}{\left(n+|\vartheta|\right)^3}\right)
  \leq \sum_{n=1}^\infty \left(\frac{1}{n^3} + \frac{1}{(n+1)^3}\right) = 2 \zeta(3)-1.
\]
-/)
  (latexEnv := "lemma")
  (discussion := 571)]
theorem lemma_abadimpseri {ϑ : ℝ} (hϑ : 0 ≤ |ϑ| ∧ |ϑ| < 1) :
    ∑' n : ℤ, (1 / ((n - ϑ) ^ 3 : ℝ) + 1 / ((n + ϑ) ^ 3 : ℝ)) ≤
      (1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1 := by
  sorry

@[blueprint
  "lem:abadsumas"
  (title := "Estimate for a Fourier sum")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau \in \mathbb{R}$, with $s\ne 1$.
Let $b>a>0$, $a, b\in \mathbb{Z} + \frac{1}{2}$, with $a>\frac{|\tau|}{2\pi}$.
Define $f:\mathbb{R}\to\mathbb{C}$ by $f(y) = 1_{[a,b]}(y)/y^s$.
Write $\vartheta = \frac{\tau}{2\pi a}$, $\vartheta_- = \frac{\tau}{2\pi b}$. Then
$$\begin{aligned} \sum_n (\widehat{f}(n) + \widehat{f}(-n))
  &= \frac{a^{-s} g(\vartheta)}{2 i} - \frac{b^{-s} g(\vartheta_-)}{2 i}
  + O^*\left(\frac{C_{\sigma,\vartheta}}{a^{\sigma+1}}\right)\end{aligned}$$
with absolute convergence,
where $g(t) = \frac{1}{\sin \pi t} - \frac{1}{\pi t}$ for $t\ne 0$, $g(0)=0$, and
\begin{equation}\label{eq:defcsigth}C_{\sigma,\vartheta}= \begin{cases}
  \frac{\sigma}{2} \left(\frac{1}{\sin^2\pi \vartheta} - \frac{1}{(\pi \vartheta)^2}\right)
  + \frac{|\vartheta|}{2\pi^2} \left(\frac{1}{(1-|\vartheta|)^3} + 2\zeta(3)-1\right)
  & \text{for $\vartheta\ne 0$,}\\
  \sigma/6 & \text{for $\vartheta = 0$.}\end{cases}\end{equation}
-/)
  (proof := /--
By Proposition~\ref{prop:applem}, multiplying by $2$
(since $e(-n t)+e(n t) = 2 \cos 2\pi n t$),
\begin{align}\widehat{f}(n) + \widehat{f}(-n) &= \notag
  \frac{a^{-s}}{2\pi i} \frac{(-1)^{n+1} 2\vartheta}{n^2 - \vartheta^2} -
  \frac{b^{-s}}{2\pi i} \frac{(-1)^{n+1} 2\vartheta_-}{n^2 - \vartheta_-^2}
  \\
  &+ \frac{a^{-\sigma-1}}{2\pi^2} O^*\left(\frac{\sigma}{(n-\vartheta)^2}
    + \frac{\sigma}{(n+\vartheta)^2} + \frac{|\vartheta|}{(n-\vartheta)^3}
    + \frac{|\vartheta|}{(n+\vartheta)^3}\right),\label{eq:abaderrcontrib}\end{align}
where $\vartheta_- = \tau/(2\pi b)$. Note $|\vartheta_-|\leq |\vartheta|<1$.
By the Lemma \ref{lem:abadeulmit1},
\[\sum_n \frac{(-1)^{n+1} 2 z}{n^2 - z^2} = \frac{\pi}{\sin \pi z} - \frac{1}{z}
\] for $z\ne 0$, while $\sum_n \frac{(-1)^{n+1} 2 z}{n^2 - z^2} = \sum_n 0 = 0$ for $z=0$.
Moreover, by Lemmas \ref{lem:abadeulmit2} and \ref{lem:abadimpseri}, for $\vartheta\ne 0$,
\[\sum_n \left(\frac{\sigma}{(n-\vartheta)^2} + \frac{\sigma}{(n+\vartheta)^2}\right)\leq
\sigma\cdot \left(\frac{\pi^2}{\sin^2 \pi \vartheta} - \frac{1}{\vartheta^2}\right),\]
\[\sum_n \left(\frac{|\vartheta|}{(n-\vartheta)^3} + \frac{|\vartheta|}{(n+\vartheta)^3}\right)
\leq |\vartheta|\cdot \left( \frac{1}{(1-|\vartheta|)^3} + 2\zeta(3)-1\right).
\]
If $\vartheta=0$, then
$\sum_n \left(\frac{\sigma}{(n-\vartheta)^2} + \frac{\sigma}{(n+\vartheta)^2}\right)
= 2 \sigma \sum_{n=1}^\infty \frac{1}{n^2} = \sigma \frac{\pi^2}{3}$.
-/)
  (latexEnv := "lemma")
  (discussion := 572)]
theorem lemma_abadsumas {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 ≤ s.re) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    let ϑ_minus : ℝ := s.im / (2 * π * b)
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    let g : ℝ → ℂ := fun t ↦
      if t ≠ 0 then (1 / Complex.sin (π * t) : ℂ) - (1 / (π * t : ℂ)) else 0
    let C : ℝ :=
      if ϑ ≠ 0 then
        s.re / 2 * ((1 / (Complex.sin (π * ϑ) ^ 2 : ℂ)).re - (1 / ((π * ϑ) ^ 2 : ℂ)).re) +
          |ϑ| / (2 * π ^ 2) * ((1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1)
      else
        s.re / 6
    ∃ E : ℂ, ∑' n : ℤ, (FourierTransform.fourier f n + FourierTransform.fourier f (-n)) =
      ((a ^ (-s) : ℂ) * g ϑ) / (2 * I) - ((b ^ (-s) : ℂ) * g ϑ_minus) / (2 * I) + E ∧
      ‖E‖ ≤ C := by
  sorry

@[blueprint
  "prop:dadaro"
  (title := "Approximation of zeta(s) by a partial sum")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$, with $s\ne 1$.
Let $a\in \mathbb{Z} + \frac{1}{2}$ with $a>\frac{|\tau|}{2\pi}$. Then
\begin{equation}\label{eq:abadlondie}
  \zeta(s) = \sum_{n\leq a} \frac{1}{n^s} - \frac{a^{1-s}}{1-s} + c_\vartheta a^{-s}
  + O^*\left(\frac{C_{\sigma,\vartheta}}{a^{\sigma+1}}\right),
\end{equation}
where $\vartheta = \frac{\tau}{2\pi a}$,
$c_\vartheta = \frac{i}{2} \left(\frac{1}{\sin \pi \vartheta} - \frac{1}{\pi \vartheta}\right)$
for $\vartheta\ne 0$, $c_0 =0$, and $C_{\sigma,\vartheta}$ is as in \eqref{eq:defcsigth}.
-/)
  (proof := /--
Assume first that $\sigma>0$. Let $b\in \mathbb{Z}+\frac{1}{2}$ with $b>a$, and define
$f(y) = \frac{1_{[a,b]}(y)}{y^s}$.
By Lemma~\ref{lem:abadtoabsum} and Lemma~\ref{lem:abadusepoisson},
$$\sum_{n\leq a} \frac{1}{n^s} = \zeta(s) + \frac{a^{1-s}}{1-s}
  - \lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n))
  + O^*\left(\frac{2 |s|}{\sigma b^\sigma}\right).$$
We apply Lemma~\ref{lem:abadsumas} to estimate
$\lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n))$. We obtain
\[\sum_{n\leq a} \frac{1}{n^s} = \zeta(s) + \frac{a^{1-s}}{1-s} -
\frac{a^{-s} g(\vartheta)}{2 i} + O^*\left(\frac{C_{\sigma,\vartheta}}{a^{\sigma+1}}\right)
+ \frac{b^{-s} g(\vartheta_-)}{2 i} + O^*\left(\frac{2 |s|}{\sigma b^\sigma}\right),
\]
where $\vartheta_- = \frac{\tau}{2\pi b}$ and $g(t)$ is as in Lemma~\ref{lem:abadsumas},
and so $-\frac{g(\vartheta)}{2 i} = c_\vartheta$.
We let $b\to \infty$ through the half-integers, and obtain \eqref{eq:abadlondie},
since $b^{-\sigma}\to 0$, $\vartheta_-\to 0$ and $g(\vartheta_-)\to g(0) = 0$
as $b\to \infty$.

Finally, the case $\sigma=0$ follows since all terms in \eqref{eq:abadlondie} extend
continuously to $\sigma=0$.
-/)
  (latexEnv := "proposition")
  (discussion := 573)]
theorem proposition_dadaro {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 ≤ s.re) {a : ℝ} (ha : 0 < a)
    (ha' : a.IsHalfInteger) (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    let C : ℝ :=
      if ϑ ≠ 0 then
        s.re / 2 * ((1 / (Complex.sin (π * ϑ) ^ 2 : ℂ)).re - (1 / ((π * ϑ) ^ 2 : ℂ)).re) +
          |ϑ| / (2 * π ^ 2) * ((1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1)
      else
        s.re / 6
    let c : ℂ :=
      if ϑ ≠ 0 then
        I / 2 * ((1 / Complex.sin (π * ϑ) : ℂ) - (1 / (π * ϑ : ℂ)))
      else
        0
    ∃ E : ℂ, riemannZeta s =
      ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
      (a ^ (1 - s) : ℂ) / (1 - s) + c * (a ^ (-s) : ℂ) + E ∧
      ‖E‖ ≤ C / (a ^ (s.re + 1 : ℝ)) := by
  sorry

blueprint_comment /--
\begin{remark}
The term $c_\vartheta a^{-s}$ in \eqref{eq:abadlondie} does not seem to have been worked
out before in the literature; the factor of $i$ in $c_\vartheta$ was a surprise.
For the sake of comparison, let us note that, if $a\geq x$, then $|\vartheta|\leq 1/2\pi$,
and so $|c_\vartheta|\leq |c_{\pm 1/2\pi}| = 0.04291\dotsc$ and
$|C_{\sigma,\vartheta}|\leq |C_{\sigma,\pm 1/2\pi}|\leq 0.176\sigma +0.246$.
While $c_\vartheta$ is optimal, $C_{\sigma,\vartheta}$ need not be --
but then that is irrelevant for most applications.
\end{remark}
-/

end ZetaAppendix
