import Architect
import PrimeNumberTheoremAnd.ZetaDefinitions
import Mathlib.Topology.EMetricSpace.BoundedVariation

blueprint_comment /--
\section{Approximating the Riemann zeta function}
-/

blueprint_comment /--
We want a good explicit estimate on
$$\sum_{n\leq a} \frac{1}{n^s} - \int_0^{a} \frac{du}{u^s},$$
for $a$ a half-integer. As it turns out, this is the same problem as that of approximating
$\zeta(s)$ by a sum $\sum_{n\leq a} n^{-s}$. This is one of the two\footnote{The other one is the approximate functional equation.} main, standard ways of approximating $\zeta(s)$.

The non-explicit version of the result was first proved in \cite[Lemmas 1 and 2]{zbMATH02601353}. The proof there uses first-order Euler-Maclaurin combined with a decomposition of $\lfloor x\rfloor - x +1/2$ that turns out to be equivalent to Poisson summation.
The exposition in \cite[\S 4.7--4.11]{MR882550} uses first-order Euler-Maclaurin and
van de Corput's Process B; the main idea of the latter is Poisson summation.


There are already several explicit versions of the result in the literature. In \cite{MR1687658}, \cite{MR3105334} and \cite{MR4114203}, what we have is successively sharper
explicit versions of Hardy and Littlewood's original proof. The proof in \cite[Lemma 2.10]{zbMATH07557592} proceeds simply by a careful estimation of the terms in
high-order Euler-Maclaurin; it does not use Poisson summation. Finally,
\cite{delaReyna} is an explicit version of \cite[\S 4.7--4.11]{MR882550}; it
gives a weaker bound than \cite{MR4114203} or \cite{zbMATH07557592}. The strongest of these results is \cite{MR4114203}.

We will give another version here, in part because we wish to relax conditions -- we will work with $\left|\Im s\right| < 2\pi a$ rather than $\left|\Im s\right| \leq a$ -- and in part to show that one can prove an asymptotically optimal result easily and concisely. We will use first-order Euler-Maclaurin and Poisson summation. We assume that $a$ is a half-integer; if one inserts the same assumption into
\cite[Lemma 2.10]{zbMATH07557592}, one can improve the result there, yielding an error term closer to the one here.

For additional context, see \url{https://leanprover.zulipchat.com/\#narrow/channel/423402-PrimeNumberTheorem.2B/topic/Let.20us.20formalize.20an.20appendix}
-/

namespace ZetaAppendix

open Real Complex

-- may want to move this to a more globally accessible location

@[blueprint
  "e-def"
  (title := "e")
   (statement := /-- We recall that $e(\alpha) = e^{2\pi i \alpha}$ -/)]
noncomputable def e (α : ℝ) : ℂ := exp (2 * π * I * α)

blueprint_comment /--
\subsection{The decay of a Fourier transform}
Our first objective will be to estimate the Fourier transform of $t^{-s} \mathds{1}_{[a,b]}$. In particular, we will show that, if $a$ and $b$ are half-integers, the Fourier cosine transform has quadratic decay {\em when evaluated at integers}. In general, for real arguments, the Fourier transform of a discontinuous function such as $t^{-s} \mathds{1}_{[a,b]}$ does not have quadratic decay. -/

@[blueprint
  "lem:aachIBP"
  (title := "Fourier transform of a truncated power law")
   (statement := /--  Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$. Let $\nu\in \mathbb{R}\setminus \{0\}$,
 $b>a>\frac{|\tau|}{2\pi |\nu|}$.
 Then
\begin{equation}\label{eq:aachquno}\int_a^b t^{-s} e(\nu t) dt =
 \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b
 + \sigma \int_a^b \frac{t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} e(\varphi_\nu(t)) dt + \int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt,
\end{equation}
 where $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$.
 -/)
 (proof := /-- We write $t^{-s} e(\nu t) = t^{-\sigma} e(\varphi_\nu(t))$ and integrate by parts with
$u = t^{-\sigma}/(2\pi i \varphi_\nu'(t))$, $v = e(\varphi_\nu(t))$.
Here $\varphi_\nu'(t) = \nu - \tau/(2\pi t)\ne 0$ for $t\in [a,b]$ because
$t\geq a > |\tau|/(2\pi |\nu|)$ implies $|\nu|>|\tau|/(2\pi t)$.
Clearly
\[u dv = \frac{ t^{-\sigma}}{2\pi i \varphi_\nu'(t)} \cdot 2\pi i \varphi_\nu'(t) e(\varphi_\nu(t)) dt =
t^{-\sigma} e(\varphi_\nu(t)) dt,\]
while
\[du = \left(\frac{-\sigma t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} - \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}\right) dt.\]
 -/)
 (latexEnv := "lemma")]
theorem lemma_aachIBP (s : ℂ) (hsigma : 0 ≤ s.re) (ν : ℝ) (hν : ν ≠ 0)
  (a b : ℝ) (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
  let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
  let Φ : ℝ → ℂ := fun t ↦ (t ^ (-s.re):ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
  ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
    s.re * ∫ t in Set.Icc a b, (t ^ (-s.re - 1):ℝ) / (2 * π * I * (deriv φ t)) * e (φ t) +
    ∫ t in Set.Icc a b, (t ^ (-s.re):ℝ) * (deriv (deriv φ) t) / (2 * π * I * (deriv φ t) ^ 2) * e (φ t)
  := by
  sorry

@[blueprint
  "lem:aachra"
  (title := "Total variation of a function with monotone absolute value")
   (statement := /--
Let $g:[a,b]\to \mathbb{R}$ be continuous, with $|g(t)|$ non-increasing. Then
$g$ is monotone, and $\|g\|_{\TV} = |g(a)|-|g(b)|$.
 -/)
 (proof := /-- Suppose $g$ changed sign: $g(a')>0>g(b')$ or $g(a') <0 < g(b')$ for some $a\leq a'< b'\leq b$. By IVT, there would be an $r\in [a',b']$ such that $g(r)=0$. Since $|g|$ is non-increasing, $g(b')=0$; contradiction. So, $g$ does not change sign: either $g\leq 0$ or $g\geq 0$.

Thus, there is an $\varepsilon\in \{-1,1\}$ such that  $g(t) = \varepsilon |g(t)|$ for all $t\in [a,b]$. Hence, $g$ is monotone. Then $\|g\|_{\TV} = |g(a)-g(b)|$. Since $|g(a)|\geq |g(b)|$ and $g(a)$, $g(b)$
are either both non-positive or non-negative, $|g(a)-g(b)| = |g(a)|-|g(b)|$.
 -/)
 (latexEnv := "lemma")]
theorem lemma_aachra {a b : ℝ} (ha : a < b) (g : ℝ → ℝ)
  (hg_cont : ContinuousOn g (Set.Icc a b))
  (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
  BoundedVariationOn g (Set.Icc a b) ∧
  (eVariationOn g (Set.Icc a b)).toReal = |g a| - |g b| := by
  sorry

@[blueprint
  "lem:aachmonophase"
  (title := "Non-stationary phase estimate")
   (statement := /--
Let $\varphi:[a,b]\to \mathbb{R}$ be $C^1$ with $\varphi'(t)\ne 0$ for
all $t\in [a,b]$. Let $h:[a,b]\to \mathbb{R}$ be such that $g(t) = h(t)/\varphi'(t)$
is continuous and $|g(t)|$ is non-increasing. Then
\[\left|\int_a^b h(t) e(\varphi(t)) dt\right|\leq \frac{|g(a)|}{\pi}.\]
  -/)
  (proof := /--
Since $\varphi$ is $C^1$, $e(\varphi(t))$ is $C^1$, and
$h(t) e(\varphi(t)) = \frac{h(t)}{2\pi i \varphi'(t)} \frac{d}{dt} e(\varphi(t))$ everywhere.
By Lemma \ref{lem:aachra}, $g$ is of bounded variation. Hence, we can integrate by parts:
%Since $h(t)/\varphi'(t)$ is continuous and its absolute value $g(t)$ is non-increasing, it is of constant %sign, and also monotone, and thus of bounded variation.
\[\int_a^b h(t) e(\varphi(t)) dt = \left. \frac{h(t) e(\varphi(t))}{2\pi i \varphi'(t)}\right|_a^b -
\int_a^b e(\varphi(t))\, d\left(\frac{h(t)}{2\pi i \varphi'(t)}\right).
\]
The first term on the right has absolute value $\leq \frac{|g(a)|+|g(b)|}{2\pi}$.
Again by Lemma \ref{lem:aachra},
\[\left|
\int_a^b e(\varphi(t))\, d\left(\frac{h(t)}{2\pi i \varphi'(t)}\right)
\right|\leq \frac{1}{2\pi} \|g\|_{\TV} = \frac{|g(a)|-|g(b)|}{2\pi}.
\]
We are done by $\frac{|g(a)|+|g(b)|}{2\pi} + \frac{|g(a)|-|g(b)|}{2\pi} = \frac{|g(a)|}{\pi}$.
  -/)
   (latexEnv := "lemma")]
theorem lemma_aachmonophase {a b : ℝ} (ha : a < b) (φ : ℝ → ℝ)
  (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b))
  (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0)
  (h g : ℝ → ℝ)
  (hg : ∀ t, g t = h t / deriv φ t)
  (hg_cont : ContinuousOn g (Set.Icc a b))
  (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
  ‖∫ t in Set.Icc a b, h t * e (φ t)‖ ≤ |g a| / π
   := by sorry

@[blueprint
  "lem:aachdecre"
  (title := "A decreasing function")
   (statement := /-- Let $\sigma\geq 0$, $\tau\in \mathbb{R}$, $\nu \in \mathbb{R}\setminus \{0\}$. Let $b>a>\frac{|\tau|}{2\pi |\nu|}$. Then, for any $k\geq 1$, $f(t) = t^{-\sigma-k} |2\pi \nu-\tau/t|^{-k-1}$ is decreasing on $[a,b]$.-/)
  (proof := /-- Let $a\leq t\leq b$. Since $\left|\frac{\tau}{t \nu}\right| < 2\pi$, we see that $2\pi-\frac{\tau}{\nu t} >0$, and so
$|2\pi \nu-\tau/t|^{-k-1} = |\nu|^{-k-1} \left(2\pi - \frac{\tau}{t \nu}\right)^{-k-1}$. Now
we take logarithmic derivatives:
\[t (\log f(t))' = - (\sigma+k) - (k+1) \frac{\tau/t}{2\pi \nu - \tau/t}
= -\sigma - \frac{2\pi k + \frac{\tau}{t \nu}}{2\pi - \frac{\tau}{t \nu}} < -\sigma \leq 0,\]
since, again by $\frac{|\tau|}{t |\nu|} < 2\pi$ and $k\geq 1$, we have
$2\pi k + \frac{\tau}{t \nu}>0$, and, as we said, $2\pi - \frac{\tau}{t \nu}>0$.
  -/)
   (latexEnv := "lemma")]
theorem lemma_aachdecre (σ : ℝ) (hσ : 0 ≤ σ) (τ : ℝ) (ν : ℝ) (hν : ν ≠ 0)
  (a b : ℝ) (ha : a > |τ| / (2 * π * |ν|)) (hb : b > a)
  (k : ℕ) (hk : 1 ≤ k) :
  let f : ℝ → ℝ := fun t ↦ t ^ (-σ - k) * |2 * π * ν - τ / t| ^ (-(k:ℝ) - 1)
  AntitoneOn f (Set.Icc a b) := by
  sorry

@[blueprint
  "lem:aachfour"
  (title := "Estimating an integral")
    (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.  Let
 $\nu \in \mathbb{R}\setminus \{0\}$, $b>a>\frac{|\tau|}{2\pi |\nu|}$.
 Then
\[\int_a^b t^{-s} e(\nu t) dt =
 \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b +
\frac{a^{-\sigma-1}}{2\pi^2} O^*\left(\frac{\sigma}{(\nu-\vartheta)^2} +
\frac{|\vartheta|}{|\nu-\vartheta|^3}\right),
\]
 where $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$ and $\vartheta = \frac{\tau}{2\pi a}$.-/)
  (proof := /--
Apply Lemma~\ref{lem:aachIBP}. Since $\varphi_\nu'(t) = \nu - \tau/(2\pi t)$, we know by
Lemma \ref{lem:aachdecre} (with $k=1$) that $g_1(t) = \frac{t^{-\sigma-1}}{(\varphi_\nu'(t))^2}$ is decreasing on
$[a,b]$. We know that $\varphi_\nu'(t)\ne 0$ for $t\geq a$ by $a>\frac{|\tau|}{2\pi |\nu|}$, and so
we also know that $g_1(t)$ is continuous for $t\geq a$. Hence, by Lemma \ref{lem:aachmonophase},
\[\left|\int_a^b \frac{t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} e(\varphi_\nu(t)) dt \right|\leq
\frac{1}{2\pi} \cdot \frac{|g_1(a)|}{\pi} = \frac{1}{2\pi^2} \frac{a^{-\sigma-1}}{\left|\nu - \vartheta\right|^2},\]
since $\varphi_\nu'(a) = \nu - \vartheta$. We remember to include the factor of $\sigma$
in front of an integral in \eqref{eq:aachquno}.

Since $\varphi_\nu'(t)$ is as above and $\varphi_\nu''(t) = \tau/(2\pi t^2)$,
we know
by Lemma \ref{lem:aachdecre} (with $k=2$) that
$g_2(t) = \frac{t^{-\sigma} |\varphi_\nu''(t)|}{|\varphi_\nu'(t)|^3} =
\frac{|\tau|}{2\pi}  \frac{t^{-\sigma-2}}{|\varphi_\nu'(t)|^3} $ is decreasing on $[a,b]$; we also know, as before,
that $g_2(t)$ is continuous. Hence, again by Lemma \ref{lem:aachmonophase},
\[\left|\int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt\right|\leq \frac{1}{2\pi} \frac{|g_2(a)|}{\pi} = \frac{1}{2\pi^2}
 \frac{a^{-\sigma-1} |\vartheta|}{\left|\nu - \vartheta\right|^3}.
 \]
  -/)
   (latexEnv := "lemma")]
theorem lemma_aachfour (s : ℂ) (hsigma : 0 ≤ s.re) (ν : ℝ) (hν : ν ≠ 0)
  (a b : ℝ) (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
  let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
  let Φ : ℝ → ℂ := fun t ↦ (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
  let ϑ : ℝ := s.im / (2 * π * a)
  ∃ E, ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
    ((a ^ (-s.re - 1) : ℝ) / (2 * π ^ 2)) * E
  ∧ ‖E‖ ≤ (s.re) / (|ν - ϑ| ^ 2) + |ϑ| / (|ν - ϑ| ^ 3) := by
  sorry

def _root_.Real.IsHalfInteger (x : ℝ) : Prop := ∃ k : ℤ, x = k + 1 / 2

@[blueprint
  "lem:aachcanc"
  (title := "Estimating an sum")
    (statement := /-- \begin{lemma}\label{lem:aachcanc}
Let $s = \sigma + i \tau$, $\sigma,\tau \in \mathbb{R}$.
Let $n\in \mathbb{Z}_{>0}$. Let $a,b\in \mathbb{Z} + \frac{1}{2}$, $b>a>\frac{|\tau|}{2\pi n}$. Write $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$.
Then
\[\frac{1}{2} \sum_{\nu = \pm n}\left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b =
\left. \frac{(-1)^n t^{-s} \cdot \frac{\tau}{2\pi t}}{2\pi i \left(n^2 - \left(\frac{\tau}{2\pi t}\right)^2\right)}\right|_a^b .
\] -/)
  (proof := /--
Since $e(\varphi_\nu(t)) = e(\nu t) t^{-i \tau} = (-1)^{\nu} t^{-i \tau}$ for any half-integer $t$ and any integer $\nu$,
\[\left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b =
\left. \frac{(-1)^{\nu} t^{-s}}{2\pi i \varphi_\nu'(t)}\right|_a^b
\]
for $\nu = \pm n$. Clearly $(-1)^{\nu} = (-1)^n$. Since $\varphi_\nu'(t) = \nu - \alpha$ for $\alpha = \frac{\tau}{2\pi t}$,
\[\frac{1}{2} \sum_{\nu = \pm n} \frac{1}{\varphi_\nu'(t)} = \frac{1/2}{n - \alpha} +
\frac{1/2}{- n - \alpha} = \frac{-\alpha}{\alpha^2-n^2} = \frac{\alpha}{n^2-\alpha^2}.
\]
  -/)
   (latexEnv := "lemma")]
theorem lemma_aachcanc (s : ℂ) {n : ℤ} (hn : 0 < n)
  {a b : ℝ} (ha : a > |s.im| / (2 * π * n)) (hb : b > a)
  (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) :
  let ϕ : ℝ → ℝ → ℝ := fun ν t ↦ ν * t - (s.im / (2 * π)) * Real.log t
  let Φ : ℝ → ℝ → ℂ := fun ν t ↦ (t ^ (-s.re) : ℝ) * e (ϕ ν t) / (2 * π * I * (deriv (ϕ ν) t))
  let Ψ : ℝ → ℂ := fun t ↦ (-1) ^ n * (t ^ (-s) : ℂ) * (s.im / (2 * π * t)) /
    (2 * π * I * (n ^ 2 - (s.im / (2 * π * t)) ^ 2))
  (1 / 2) * (Φ n b - Φ n a + Φ (-n) b - Φ (-n) a) = Ψ b - Ψ a
   := by
  sorry

@[blueprint
  "prop:applem"
  (title := "Estimating a Fourier cosine integral")
    (statement := /-- Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.
 Let $a,b\in \mathbb{Z} + \frac{1}{2}$, $b>a>\frac{|\tau|}{2\pi}$. Write $\vartheta = \frac{\tau}{2\pi a}$.  Then, for any integer $n\geq 1$,
$$\begin{aligned}\int_a^b t^{-s} \cos 2\pi n t\, dt &=
\left. \left(\frac{(-1)^n t^{-s}}{2\pi i} \cdot\frac{\frac{\tau}{2\pi t}}{n^2 - \left(\frac{\tau}{2\pi t}\right)^2}\right)\right|_a^b \\ &\quad+ \frac{a^{-\sigma-1}}{4\pi^2}\, O^*\left(\frac{\sigma}{(n-\vartheta)^2} + \frac{\sigma}{(n+\vartheta)^2} + \frac{|\vartheta|}{|n-\vartheta|^3} + \frac{|\vartheta|}{|n+\vartheta|^3}\right).\end{aligned}$$
    -/)
  (proof := /--
Write $\cos 2\pi n t = \frac{1}{2} (e(n t) + e(-n t))$. Since $n\geq 1$ and $a>\frac{|\tau|}{2\pi}$, we know that $a>\frac{|\tau|}{2 \pi n}$, and so we can apply
Lemma \ref{lem:aachfour} with $\nu = \pm n$.
We then apply Lemma~\ref{lem:aachcanc} to combine the boundary contributions $\left.  \right|_a^b$
for $\nu=\pm n$.
  -/)
   (latexEnv := "proposition")]
theorem proposition_applem (s : ℂ) (hsigma : 0 ≤ s.re) {a b : ℝ}
  (ha: a > |s.im| / (2 * π)) (hb : b > a) (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) {n : ℕ} (hn : 1 ≤ n) :
  let ϑ : ℝ := s.im / (2 * π * a)
  ∃ E, ∫ t in Set.Icc a b, (t:ℂ) ^ (-s) * Real.cos (2 * π * (n:ℝ) * t) =
    ((-1) ^ n * (b ^ (-s) : ℂ) * (s.im / (2 * π * b)) /
      (2 * π * I * ((n:ℝ) ^ 2 - (s.im / (2 * π * b)) ^ 2)) -
     (-1) ^ n * (a ^ (-s) : ℂ) * (s.im / (2 * π * a)) /
      (2 * π * I * ((n:ℝ) ^ 2 - (s.im / (2 * π * a)) ^ 2))) +
    ((a ^ (-s.re - 1) : ℝ) / (4 * π ^ 2)) * E
  ∧ ‖E‖ ≤ (s.re) / ((n - ϑ) ^ 2) + (s.re) / ((n + ϑ) ^ 2) +
    |ϑ| / (|n - ϑ| ^ 3) + |ϑ| / (|n + ϑ| ^ 3) := by sorry



end ZetaAppendix
