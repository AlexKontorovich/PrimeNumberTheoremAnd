import Mathlib.Analysis.Complex.CauchyIntegral

/-%%
The approach here is completely standard. We follow the use of $\mathcal{M}(\widetilde{1_{\epsilon}})$ as in Kontorovich 2015.
%%-/

/-%%
It has already been established that zeta doesn't vanish on the 1 line, and has a pole at $s=1$ of order 1.
We also have that
$$
-\frac{\zeta'(s)}{\zeta(s)} = \sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}.
$$

The main object of study is the following inverse Mellin-type transform, which will turn out to be a smoothed Chebyshev function.
\begin{definition}\label{SmoothedChebyshev}
Fix $\epsilon>0$, and a bumpfunction $\psi$ supported in $[1/2,2]$. Then we define the smoothed Chebyshev function $\psi_{\epsilon}$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ by
$$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(2)}\frac{-\zeta'(s)}{\zeta(s)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds.$$
\end{definition}
%%-/

/-%%
Inserting the Dirichlet series expansion of the log derivative of zeta, we get the following.
\begin{theorem}\label{SmoothedChebyshevDirichlet}
We have that
$$\psi_{\epsilon}(X) = \sum_{n=1}^\infty \Lambda(n)\widetilde{1_{\epsilon}}(n/X).$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{SmoothedChebyshev, MellinInversion}
We have that
$$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(2)}\sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds.$$
We have enough decay (thanks to quadratic decay of $\mathcal{M}(\widetilde{1_{\epsilon}})$) to justify the interchange of summation and integration. We then get
$$\psi_{\epsilon}(X) =
\sum_{n=1}^\infty \Lambda(n)\frac{1}{2\pi i}\int_{(2)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
(n/X)^{-s}
ds
$$
and apply the Mellin inversion formula (Theorem \ref{MellinInversion}).
\end{proof}
%%-/

/-%%
The smoothed Chebyshev function is close to the actual Chebyshev function.
\begin{theorem}[SmoothedChebyshevClose]\label{SmoothedChebyshevClose}
We have that
$$\psi_{\epsilon}(X) = \psi(X) + O(\epsilon X).$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{SmoothedChebyshevDirichlet, Smooth1Properties_above, Smooth1Properties_below, ChebyshevPsi}
Take the difference. By Lemma \ref{Smooth1Properties_above} and \ref{Smooth1Properties_below}, the sums agree except when $1-c \epsilon \leq n/X \leq 1+c \epsilon$. This is an interval of length $\ll \epsilon X$, and the summands are bounded by $\Lambda(n) \ll \log X$.

This is not enough, as it loses a log! (Which is fine if our target is the strong PNT, with exp-root-log savings, but not here with the ``softer'' approach.) So we will need something like the Selberg sieve (already in Mathlib? Or close?) to conclude that the number of primes in this interval is $\ll \epsilon X / \log X + 1$.
(The number of prime powers is $\ll X^{1/2}$.)
And multiplying that by $\Lambda (n) \ll \log X$ gives the desired bound.
\end{proof}
%%-/

/-%%
Returning to the definition of $\psi_{\epsilon}$, fix a large $T$ to be chosen later, and pull contours (via rectangles!) to go
from $2$ up to $2+iT$, then over to $1+iT$, and up from there to $1+i\infty$ (and symmetrically in the lower half plane).  The
rectangles involved are all where the integrand is holomorphic, so there is no change.
\begin{theorem}\label{SmoothedChebyshevPull1}
\uses{SmoothedChebyshev, RectangleIntegral}
We have that
$$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{\text{curve}}\frac{-\zeta'(s)}{\zeta(s)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds.$$
\end{theorem}
%%-/

/-%%
\begin{theorem}\label{ZetaNoZerosOn1Line}
The zeta function does not vanish on the 1-line.
\end{theorem}
This fact is already proved in Stoll's work.
%%-/

/-%%
General theorem:
\begin{theorem}\label{NoZerosInBoxOfNoneOnBoundary}
\lean{NoZerosInBoxOfNoneOnBoundary}
You have a set $S$ of points in $\C$ with no accumulation point.
Suppose that none of these points line on a given line $L$.
Then for any desired interval $I \subset L $, there is a box $B$ having $I$ as its right boundary with no points of $S$ in $B$.
\end{theorem}
%%-/
theorem NoZerosInBoxOfNoneOnBoundary
  {S : Set ℂ}
  --{hS : } -- S has no accumulation point
  {x₀ : ℝ} -- that's the x-coordinate of the line L
  (hL : ∀ z : ℂ, z ∈ S → z.re ≠ x₀) -- none of the points of S lie on L
  {y₀ y₁ : ℝ} -- determine the y-coordinates of the interval I
  :
  ∃ (δ : ℝ) (hδ : 0 < δ), -- width of the box
  ∀ z : ℂ, x₀ - δ ≤ z.re → z.re ≤ x₀ → y₀ ≤ z.im → z.im ≤ y₁ → z ∉ S := by
/-%%
\begin{proof}
We argue by contraposition.
%%-/
    contrapose! hL -- not quite, want to contrapose `hS`
/-%%
If for every $\delta>0$, the box $[x_0-\delta,x_0] \times_{ℂ} [y_0,y_1]$ contains a point of $S$, then we can find an
accumulation point
 of $S$, a contradiction.
\end{proof}
%%-/
    sorry



/-%%
Then, since $\zeta$ doesn't vanish on the 1-line, there is a $\delta$ (depending on $T$), so that the box $[1-\delta,1] \times_{ℂ} [-T,T]$ is free of zeros of $\zeta$.
\begin{theorem}\label{ZetaNoZerosInBox}
For any $T>0$, there is a $\delta>0$ so that $[1-\delta,1] \times_{ℂ} [-T,T]$ is free of zeros of $\zeta$.
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{NoZerosInBoxOfNoneOnBoundary, ZetaNoZerosOn1Line}
We have that zeta doesn't vanish on the 1 line and is holomorphic inside the box (except for the pole at $s=1$). If for a height $T>0$, there was no such $\delta$, then there would be a sequence of zeros of $\zeta$ approaching the 1 line, and by compactness, we could find a subsequence of zeros converging to a point on the 1 line. But then $\zeta$ would vanish at that point, a contradiction. (Worse yet, zeta would then be entirely zero...)
\end{proof}
%%-/

/-%%
The rectangle with opposite corners $1-\delta - i T$ and $2+iT$ contains a single pole of $-\zeta'/\zeta$ at $s=1$, and the residue is $1$ (from Theorem \ref{ResidueOfLogDerivative}).
\begin{theorem}\label{ZeroFreeBox}
$-\zeta'/\zeta$ is holomorphic on the box $[1-\delta,2] \times_{ℂ} [-T,T]$, except a simple pole with residue $1$ at $s$=1.
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{ZetaNoZerosInBox, ResidueOfLogDerivative}
The proof is as described.
\end{proof}
%%-/

/-%%
We insert this information in $\psi_{\epsilon}$. We add and subtract the integral over the box $[1-\delta,2] \times_{ℂ} [-T,T]$, which we evaluate as follows
\begin{theorem}\label{ZetaBoxEval}
The rectangle integral over $[1-\delta,2] \times_{ℂ} [-T,T]$ of the integrand in $\psi_{\epsilon}$ is
$$\frac{1}{2\pi i}\int_{\partial([1-\delta,2] \times_{ℂ} [-T,T])}\frac{-\zeta'(s)}{\zeta(s)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds = \frac{X^{1}}{1}\mathcal{M}(\widetilde{1_{\epsilon}})(1)
= X\left(\mathcal{M}(\psi)\left(\epsilon\right)\right)
= X(1+O(\epsilon))
.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{ZeroFreeBox, Rectangle, RectangleBorder, RectangleIntegral, ResidueOfLogDerivative, MellinOfSmooth1a, MellinOfSmooth1b, MellinOfSmooth1c, MellinOfDeltaSpikeAt1, SmoothedChebyshevPull1}
Residue calculus / the argument principle.
\end{proof}
%%-/

/-%%
It remains to estimate the contributions from the integrals over the curve $\gamma = \gamma_1 +
\gamma_2 + \gamma_3 + \gamma_4
+\gamma_5,
$
where:
\begin{itemize}
\item $\gamma_1$ is the vertical segment from $1-i\infty$ to $1-iT$,
\item $\gamma_2$ is the horizontal segment from $1-iT$ to $1-\delta-iT$,
\item $\gamma_3$ is the vertical segment from $1-\delta-iT$ to $1-\delta+iT$,
\item $\gamma_4$ is the horizontal segment from $1-\delta+iT$ to $1+iT$, and
\item $\gamma_5$ is the vertical segment from $1+iT$ to $1+i\infty$.
\end{itemize}

%%-/
/-%%
\section{Weak PNT proof 2}

\begin{theorem}[Weak PNT2]\label{WeakPNT2}  We have
$$ \sum_{n \leq x} \Lambda(n) = x + o(x).$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{ChebyshevPsi, SmoothedChebyshevClose, ZetaBoxEval}
  Evaluate the integrals.
\end{proof}
%%-/
