import Architect
import PrimeNumberTheoremAnd.ZetaDefinitions

blueprint_comment /--
\section{Approximating the Riemann zeta function}
-/

blueprint_comment /--
We want a good explicit estimate on
$$\sum_{n\leq a} \frac{1}{n^s} - \int_0^{a} \frac{du}{u^s},$$
for $a$ a half-integer. As it turns out, this is the same problem as that of approximating
$\zeta(s)$ by a sum $\sum_{n\leq a} n^{-s}$. This is one of the two main, standard ways of approximating $\zeta(s)$; the other one is the approximate functional equation.

For additional context, see \url{https://leanprover.zulipchat.com/\#narrow/channel/423402-PrimeNumberTheorem.2B/topic/Let.20us.20formalize.20an.20appendix}
-/

namespace ZetaAppendix

open Real

@[blueprint
  "lemma:applem"
  (title := "Appendix Lemma 1")
  (statement := /-- Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$. Let $b>a>\frac{|\tau|}{2\pi}$; write $\rho = \frac{\tau}{2\pi a}$. Assume $a,b\in \mathbb{Z}+\frac{1}{2}$. Then, for any integer $n\geq 1$,
$$\begin{aligned}\int_a^b t^{-s} \cos 2\pi n t\, dt &=
\left. \frac{(-1)^n t^{-s} \cdot \frac{\tau}{2\pi t}}{2\pi i \left(n^2 - \left(\frac{\tau}{2\pi t}\right)^2\right)}\right|_a^b \\ &+ \frac{a^{-\sigma-1}}{4\pi^2} O^*\left(\frac{\sigma}{(n-\rho)^2} + \frac{\sigma}{(n+\rho)^2} + \frac{|\rho|}{|n-\rho|^3} + \frac{|\rho|}{|n+\rho|^3}\right).\end{aligned}$$
.-/)
  (proof := /-- Write $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$ for $\nu\in \mathbb{Z}\setminus \{0\}$. Define $I_\nu = \int_a^b t^{-s} e(\nu t) dt = \int_a^b t^{-\sigma} e(\varphi_\nu(t)) dt$; we want to estimate $\frac{1}{2} (I_n + I_{-n})$. By integration by parts,
 \begin{align}I_\nu &= \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b - \int_a^b \left(\frac{t^{-\sigma}}{2\pi i \varphi_\nu'(t)}\right)' e(\varphi_\nu(t)) dt \notag\\
&=
\left. \frac{(-1)^\nu t^{-s}}{2\pi i \varphi_\nu'(t)}\right|_a^b
+ \sigma \int_a^b \frac{t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} e(\varphi_\nu(t)) dt + \int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt, \label{eq:firstcro}
\end{align}
since $e(\varphi_\nu(t)) = (-1)^\nu t^{-i \tau}$ for any half-integer $t$. Clearly $\varphi_\nu'(t) = \nu - \frac{\tau}{2\pi t}$, $\varphi_\nu''(t) = \frac{\tau}{2\pi t^2}$. Thus, $\frac{1}{\varphi_n'(t)} + \frac{1}{\varphi_{-n}'(t)} = \frac{2\cdot \frac{\tau}{2\pi t}}{n^2 - \left(\frac{\tau}{2\pi t}\right)^2}$; this is enough to get the first term of $\frac{1}{2} (I_n + I_{-n})$ from \eqref{eq:firstcro}

To estimate the integrals in \eqref{eq:firstcro}, we integrate by parts a second time:
\begin{equation}\label{eq:docro}\int_a^b \frac{t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} e(\varphi_\nu(t)) dt =
\left. \frac{(-1)^\nu t^{-s-1}}{(2\pi i \varphi_\nu'(t))^2}\right|_a^b
- \int_a^b \left(\frac{t^{-\sigma-1}}{(2\pi i \varphi_\nu'(t))^2}\right)' e(\varphi_\nu(t))dt,\end{equation}
\begin{equation}\label{eq:tricro}\int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt = \left.\frac{(-1)^\nu t^{-s} \frac{\tau}{t^2}}{- (2\pi \varphi_\nu'(t))^3}\right|_a^b-\int_a^b \left(\frac{t^{-\sigma} \frac{\tau}{t^2}}{- (2\pi  \varphi_\nu'(t))^3}\right)' e(\varphi_\nu(t)) dt.\end{equation}
We will work on \eqref{eq:docro} first. Let $f(t) = t^{-\sigma-1} (2\pi \nu -\tau/t)^{-2}$. We take logarithmic derivatives:
$$t (\log f(t))' = -(\sigma+1) -2 \frac{\tau/t}{2\pi \nu - \tau/t} =
-\sigma - \frac{2\pi + \frac{\tau}{t\nu}}{2\pi - \frac{\tau}{t\nu}} < -\sigma \leq 0,$$
 for $t\geq a$,
since $\left|\frac{\tau}{t \nu}\right|\leq \frac{|\tau|}{a} < 2\pi$. Hence, $f$ is decreasing, and so $\left|\int_a^b f'(t) e(\varphi_\nu(t)) dt\right| \leq \int_a^b |f'(t)| dt = f(a) - f(b)$. Hence, the right side of \eqref{eq:docro} is
$\leq f(a) + f(b) + f(a) - f(b) = 2 f(a)$.

We work on \eqref{eq:tricro} in the same way: let $g(t) = |\tau| t^{-\sigma-2} |2\pi \nu - \tau/t|^{-3}$. For $t\geq a$,
$$t (\log g(t))' = - (\sigma+2) - 3 \frac{\tau/t}{2\pi \nu -\tau/t}
= - \sigma - \frac{4\pi + \frac{\tau}{t\nu}}{2\pi - \frac{\tau}{t \nu}} < - \sigma \leq 0.$$
Hence, $g(t)$ is decreasing, and so the right side of \eqref{eq:tricro} is $\leq 2 g(a)$.
  -/)]
theorem lemma_1 {s : ℂ} (hs : 0 ≤ s.re) {a b : ℝ} (hab : a < b)
  (ha : a > |s.im| / (2 * π)) (ha_half : ∃ k : ℤ, a = k + 0.5)
  (hb_half : ∃ k : ℤ, b = k + 0.5) (n : ℕ) (hn : n ≥ 1) : ∃ E,
  ∫ t in a..b, (t : ℂ) ^ (-s) * Complex.cos (2 * π * n * t) =
    ((-1) ^ n * b ^ (-s) * (s.im / (2 * π * b))) /
      (2 * π * Complex.I * (n ^ 2 - (s.im / (2 * π * b)) ^ 2)) -
    ((-1) ^ n * a ^ (-s) * (s.im / (2 * π * a))) /
      (2 * π * Complex.I * (n ^ 2 - (s.im / (2 * π * a)) ^ 2)) +
    (a ^ (-s.re - 1) : ℝ) / (4 * π ^ 2) * E
  ∧ ‖E‖ ≤ (s.re / ((n - s.im / (2 * π * a)) ^ 2) +
          s.re / ((n + s.im / (2 * π * a)) ^ 2) +
          |s.im / (2 * π * a)| / |n - s.im / (2 * π * a)| ^ 3 +
          |s.im / (2 * π * a)| / |n + s.im / (2 * π * a)| ^ 3) := by sorry



@[blueprint
  "prop:dadaro"
  (title := "Appendix Proposition 2")
   (statement := /--
 Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.
  Let $a\in \mathbb{Z} + \frac{1}{2}$ with $a>\frac{|\tau|}{2\pi}$. Then
 \begin{equation}\label{eq:londie}\zeta(s) = \sum_{n\leq a} \frac{1}{n^s} - \frac{a^{1-s}}{1-s} + c_\rho a^{-s} + O^*\left(\frac{C_{\sigma,\rho}}{a^{\sigma+1}}\right),\end{equation}
 where $\rho = \frac{\tau}{2\pi a}$,
 $c_\rho = \frac{i}{2}  \left(\frac{1}{\sin \pi \rho} - \frac{1}{\pi \rho}\right)$
 and $C_{\sigma,\rho}= \frac{\sigma}{2} \left(\frac{1}{\sin^2\pi \rho} - \frac{1}{(\pi \rho)^2}\right) + \frac{|\rho|}{2\pi^2} \left(\frac{1}{(1-|\rho|)^3} + 2\zeta(3)-1\right)$.
 .-/)
   (proof := /-- We can assume $\sigma>0$, in that we can then address the case $\sigma=0$ by letting $\sigma\to 0^+$.

 Let $b>a$, $b\in \mathbb{Z} + \frac{1}{2}$. Clearly $\sum_{n\leq b} 1/n^s = \zeta(s) - \sum_{n>b} 1/n^s$ for $\Re s > 1$, and so, by Euler-Maclaurin and $\int_b^\infty \frac{dy}{y^s} = -\frac{b^{1-s}}{1-s}$,
 $$\sum_{n\leq b} \frac{1}{n^s} = \zeta(s) + \frac{b^{1-s}}{1-s} + s \int_b^\infty \left(\{y\}-\frac{1}{2}\right) \frac{dy}{y^{s+1}};$$
 by analytic continuation, this equation actually holds for $\Re s>0$. Hence, for our $s$,
 $$\sum_{n\leq a} \frac{1}{n^s} = -\sum_{a < n\leq b} \frac{1}{n^s} + \zeta(s) + \frac{b^{1-s}}{1-s} + O\left(\frac{|s|}{\sigma b^\sigma}\right).$$
 Let $f(y) = 1_{[a,b]}(y)/y^s$. Then, by Poisson summation,
 $$\sum_{a < n\leq b} \frac{1}{n^s} = \sum_{n\in \mathbb{Z}} f(n) = \lim_{N\to \infty} \sum_{n=-N}^N \widehat{f}(n).$$
 (See, e.g., Thm.~D.3 of MR2378655; notice $f$ is continuous at every integer.) Clearly
 $$\widehat{f}(0) = \int_{\mathbb{R}} f(y) dy = \int_a^b \frac{dy}{y^s} = \frac{b^{1-s}-a^{1-s}}{1-s},$$
 and so
 $$\sum_{n\leq a} \frac{1}{n^s} = \zeta(s) + \frac{a^{1-s}}{1-s} - \lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n)) + O\left(\frac{|s|}{\sigma b^\sigma}\right).$$
 Applying Lemma \ref{lem:applem} and multiplying by $2$ (since $e(-n t)+e(n t) = 2 \cos 2\pi n t$), we see that
 $$\begin{aligned}\widehat{f}(n) + \widehat{f}(-n) &=
  \frac{(-1)^{n+1} (a^{-s} +O^*\left(\frac{a}{b^{\sigma+1}}\right))}{2\pi i} \frac{2\rho}{n^2 - \rho^2} \\
  &+ \frac{a^{-\sigma-1}}{2\pi^2} O^*\left(\frac{\sigma}{(n-\rho)^2} + \frac{\sigma}{(n+\rho)^2} + \frac{|\rho|}{(n-\rho)^3} + \frac{|\rho|}{(n+\rho)^3}\right).\end{aligned}$$
 (The term involving $b$ really gets divided by $n^2-\left(\frac{\tau}{2\pi b}\right)^2$, but that is larger than $n^2 - \rho^2$.) We have Euler's identities $\sum_{n=1}^\infty \frac{(-1)^{n+1} \cdot 2\rho}{n^2-\rho^2} = \frac{\pi}{\sin \pi \rho} - \frac{1}{\rho}$ and $\sum_{n=-\infty}^\infty \frac{1}{(n-\rho)^2} = \frac{\pi^2}{\sin^2 \pi \rho}$. Moreover, $$\begin{aligned}\sum_{n=1}^\infty \left(\frac{1}{(n-\rho)^3} + \frac{1}{(n+\rho)^3}\right) &=\frac{1}{(1-|\rho|)^3} + \sum_{n=1}^\infty \left(\frac{1}{(n+1-|\rho|)^3} + \frac{1}{(n+|\rho|)^3}\right)\\ &\leq \frac{1}{(1-|\rho|)^3} + 2\zeta(3)-1,\end{aligned}$$
 since $\frac{1}{(n+1-t)^3} + \frac{1}{(n+t)^3}$ reaches its maximum on $[0,1]$ at $t=0,1$. Thus, since $|\rho|<1$,
 $$\begin{aligned}\lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n)) &= \frac{a^{-s}+O(b^{-\sigma-1})}{2 i} \left(\frac{1}{\sin \pi \rho} - \frac{1}{\pi \rho}\right) + O^*\left(\frac{C_{\sigma,\rho}}{a^{\sigma+1}}\right),\end{aligned}$$
 where $C_{\sigma,\rho}= \frac{\sigma}{2} \left(\frac{1}{\sin^2\pi \rho} - \frac{1}{(\pi \rho)^2}\right) + \frac{|\rho|}{2\pi^2} \left(\frac{1}{(1-|\rho|)^3} + 2\zeta(3)-1\right)$. We let $b\to \infty$ and are done.
   -/)]
theorem prop_2 {s : ℂ} (hs : 0 ≤ s.re) (a : ℝ)
  (ha : a > |s.im| / (2 * π)) (ha_half : ∃ k : ℤ, a = k + 0.5) :
  let ρ : ℝ := s.im / (2 * π * a)
  let cρ : ℂ := (Complex.I / 2) * (1 / sin (π * ρ) - 1 / (π * ρ))
  let Cσρ : ℝ :=
    (s.re / 2) * (1 / (sin (π * ρ)) ^ 2 - (1 / (π * ρ)) ^ 2) +
      (|ρ| / (2 * π ^ 2)) *
        (1 / (1 - |ρ|) ^ 3 + 2 * (riemannZeta 3).re - 1)
  ∃ E,
    riemannZeta s =
      ∑ n ∈ Finset.Ioc 0 (⌊a⌋₊ + 1), (n : ℂ) ^ (-s) -
        a ^ (1 - s) / (1 - s) + cρ * a ^ (-s) +
        (a ^ (-s.re - 1) : ℝ) * E
    ∧ ‖E‖ ≤ Cσρ / a^(s.re + 1) := by sorry

blueprint_comment /--
  We have not seen the term $c_\rho a^{-s}$ worked out before in the literature; the factor of $i$ in $c_\rho$ was a surprise. If $\rho=0$ (i.e., $s$ is real), then we read $\frac{1}{\sin \pi \rho} - \frac{1}{\pi \rho} = 0$, $\frac{1}{\sin^2\pi \rho} - \frac{1}{(\pi \rho)^2} = \frac{1}{3}$, by continuity; thus, $c_0=0$ and $C_{\sigma,0} = \frac{\sigma}{6}$.  If $a\geq x$, then $|\rho|\leq 1/2\pi$, and so $|c_\rho|\leq |c_{\pm 1/2\pi}| = 0.04291\dotsc$ and
 $|C_{\sigma,\rho}|\leq |C_{\sigma,\pm 1/2\pi}|\leq 0.176\sigma +0.246$. While $c_\rho$ is optimal, $C_{\sigma,\rho}$ need not be -- but then that is irrelevant for most applications.

 Thus, the fact that $c_\rho$ is imaginary gives us no contradiction. -/





end ZetaAppendix
