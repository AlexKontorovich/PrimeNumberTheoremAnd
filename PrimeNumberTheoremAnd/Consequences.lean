import PrimeNumberTheoremAnd.Wiener
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open BigOperators Filter Real Classical Asymptotics MeasureTheory
open ArithmeticFunction hiding log

/-%%
\begin{lemma}\label{range-eq-range}\lean{finsum_range_eq_sum_range, finsum_range_eq_sum_range'}\leanok For any arithmetic function $f$ and real number $x$, one has
$$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
and
$$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
\end{lemma}
%%-/
lemma finsum_range_eq_sum_range {R: Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n in Finset.range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [Finset.mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R: Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n ≤ x), f n = ∑ n in Finset.Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [Finset.mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero

/-%%
\begin{proof}\leanok Straightforward. \end{proof}
%%-/

/-%%
\begin{theorem}\label{chebyshev-asymptotic}\lean{chebyshev_asymptotic}\leanok  One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$
\end{theorem}
%%-/
theorem chebyshev_asymptotic :
    (fun x ↦ ∑ p in (Finset.filter Nat.Prime (Finset.range ⌈x⌉₊)), log p) ~[atTop] (fun x ↦ x) := by
  sorry

theorem chebyshev_asymptotic_finsum :
    (fun x ↦ ∑ᶠ (p:ℕ) (_: p ≤ x) (_: Nat.Prime p), log p) ~[atTop] (fun x ↦ x) := by
  sorry

-- one could also consider adding a version with p < x instead of p \leq x

/-%%
\begin{proof}
\uses{WeakPNT, range-eq-range}
From the prime number theorem we already have
$$ \sum_{n \leq x} \Lambda(n) = x + o(x)$$
so it suffices to show that
$$ \sum_{j \geq 2} \sum_{p^j \leq x} \log p = o(x).$$
Only the terms with $j \leq \log x / \log 2$ contribute, and each $j$ contributes at most $\sqrt{x} \log x$ to the sum, so the left-hand side is $O( \sqrt{x} \log^2 x ) = o(x)$ as required.
\end{proof}
%%-/

/-%%
\begin{corollary}[Bounds on primorial]  \label{primorial-bounds}\lean{primorial_bounds}\leanok
We have
  $$ \prod_{p \leq x} p = \exp( x + o(x) )$$
\end{corollary}
%%-/
theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
    ∀ x : ℝ, ∏ p in (Finset.filter Nat.Prime (Finset.range ⌊x⌋₊)), p = exp ( x + E x ) := by
  sorry

theorem primorial_bounds_finprod :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
    ∀ x : ℝ, ∏ᶠ (p:ℕ) (_:p ≤ x) (_:Nat.Prime p), p = exp ( x + E x ) := by
  sorry

/-%%
\begin{proof}
\uses{chebyshev-asymptotic}
  Exponentiate Theorem \ref{chebyshev-asymptotic}.
\end{proof}
%%-/

/-%%
Let $\pi(x)$ denote the number of primes up to $x$.

\begin{theorem}\label{pi-asymp}\lean{pi_asymp}\leanok  One has
  $$ \pi(x) = (1+o(1)) \int_2^x \frac{dt}{\log t}$$
as $x \to \infty$.
\end{theorem}
%%-/
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in Set.Icc 2 x, 1 / (log t) ∂ volume := by
  sorry

/-%%
\begin{proof}
\uses{chebyshev-asymptotic}
We have the identity
$$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
+ \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
as can be proven by interchanging the sum and integral and using the fundamental theorem of calculus.  For any $\eps$, we know from Theorem \ref{chebyshev-asymptotic} that there is $x_\eps$ such that
$\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
$$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
+ \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate this after an integration by parts as
$$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
$$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
for $x$ large enough, giving the claim.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{pi-alt}\lean{pi_alt}\leanok  One has
$$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
as $x \to \infty$.
\end{corollary}
%%-/
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  sorry

/-%%
\begin{proof}
\uses{pi-asymp}
An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} + \int_2^x \frac{dt}{\log^2 t}.$$
We have the crude bounds
$$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
and
$$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
and combining all this we obtain
$$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
$$ = (1+o(1)) \frac{x}{\log x}$$
and the claim then follows from Theorem \ref{pi-asymp}.
\end{proof}
%%-/

/-%%
Let $p_n$ denote the $n^{th}$ prime.

\begin{proposition}\label{pn-asymptotic}\lean{pn_asymptotic}\leanok
 One has
  $$ p_n = (1+o(1)) n \log n$$
as $n \to \infty$.
\end{proposition}
%%-/
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime n = (1 + c n) * n * log n := by
  sorry

/-%%
\begin{proof}
\uses{pi-alt}
Use Corollary \ref{pi-alt} to show that for any $\eps>0$, and for $x$ sufficiently large, the number of primes up to $(1-\eps) n \log n$ is less than $n$, and the number of primes up to $(1+\eps) n \log n$ is greater than $n$.
\end{proof}
%%-/

/-%%
\begin{corollary} \label{pn-pnPlus1}\lean{pn_pn_plus_one}\leanok
We have $p_{n+1} - p_n = o(p_n)$
  as $n \to \infty$.
\end{corollary}
%%-/

theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n = (c n) * Nat.nth Nat.Prime n := by
  sorry

/-%%
\begin{proof}
\uses{pn-asymptotic}
  Easy consequence of preceding proposition.
\end{proof}
%%-/

/-%%
\begin{corollary}  \label{prime-between}\lean{prime_between}\leanok
For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for all sufficiently large $x$.
\end{corollary}
%%-/

theorem prime_between {ε:ℝ} (hε: 0 < ε): ∀ᶠ x:ℝ in atTop, ∃ p:ℕ, Nat.Prime p ∧
    x < p ∧ p < (1+ε)* x := by
  sorry


/-%%
\begin{proof}
\uses{pi-alt}
Use Corollary \ref{pi-alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity as $x \to \infty$.
\end{proof}
%%-/

/-%%
\begin{proposition}\label{mun}\lean{sum_mobius_div_self_le}\leanok  We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \ll 1$.
\end{proposition}
%%-/

theorem sum_mobius_div_self_le : ∃ C : ℝ, ∀ N:ℕ, |∑ n in Finset.range N, μ n / n| ≤ C := by sorry

/-%%
\begin{proof}
From M\"obius inversion $1_{n=1} = \sum_{d|n} \mu(d)$ and summing we have
  $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
  for any $x \geq 1$.  Since $\lfloor \frac{x}{d} \rfloor = \frac{x}{d} + O(1)$, we conclude that
  $$ 1 = x \sum_{d \leq x} \frac{\mu(d)}{d} + O(x)$$
  and the claim follows.
\end{proof}
%%-/

/-%%
\begin{proposition}\label{mu-pnt}\lean{mu_pnt}\leanok  We have $\sum_{n \leq x} \mu(n) = o(x)$.
\end{proposition}
%%-/

theorem mu_pnt : (fun x:ℝ ↦ ∑ n in Finset.range ⌊ x ⌋₊, μ n) =o[atTop] (fun x ↦ x) := by sorry

/-%%
\begin{proof}
\uses{mun, WeakPNT}
From the Dirichlet convolution identity
  $$ \mu(n) \log n = - \sum_{d|n} \mu(d) \Lambda(n/d)$$
and summing we obtain
$$ \sum_{n \leq x} \mu(n) \log n = - \sum_{d \leq x} \mu(d) \sum_{m \leq x/d} \Lambda(m).$$
For any $\eps>0$, we have from the prime number theorem that
$$ \sum_{m \leq x/d} \Lambda(m) = x/d + O(\eps x/d) + O_\eps(1)$$
(divide into cases depending on whether $x/d$ is large or small compared to $\eps$).
We conclude that
$$ \sum_{n \leq x} \mu(n) \log n = - x \sum_{d \leq x} \frac{\mu(d)}{d} + O(\eps x \log x) + O_\eps(x).$$
Applying \eqref{mun} we conclude that
$$ \sum_{n \leq x} \mu(n) \log n = O(\eps x \log x) + O_\eps(x).$$
and hence
$$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x) + O( \sum_{n \leq x} (\log x - \log n) ).$$
From Stirling's formula one has
$$  \sum_{n \leq x} (\log x - \log n) = O(x)$$
thus
$$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x)$$
and thus
$$ \sum_{n \leq x} \mu(n) = O(\eps x) + O_\eps(\frac{x}{\log x}).$$
Sending $\eps \to 0$ we obtain the claim.
\end{proof}
%%-/


/-%%
\begin{proposition}\label{lambda-pnt}\lean{lambda_pnt}\leanok
We have $\sum_{n \leq x} \lambda(n) = o(x)$.
\end{proposition}
%%-/

theorem lambda_pnt : (fun x:ℝ ↦ ∑ n in Finset.range ⌊ x ⌋₊, (-1)^(Ω n)) =o[atTop] (fun x ↦ x) := by
  sorry


/-%%
\begin{proof}
\uses{mu-pnt}
From the identity
  $$ \lambda(n) = \sum_{d^2|n} \mu(n/d^2)$$
and summing, we have
$$ \sum_{n \leq x} \lambda(n) = \sum_{d \leq \sqrt{x}} \sum_{n \leq x/d^2} \mu(n).$$
For any $\eps>0$, we have from Proposition \ref{mu-pnt} that
$$ \sum_{n \leq x/d^2} \mu(n) = O(\eps x/d^2) + O_\eps(1)$$
and hence on summing in $d$
$$ \sum_{n \leq x} \lambda(n) = O(\eps x) + O_\eps(x^{1/2}).$$
Sending $\eps \to 0$ we obtain the claim.
\end{proof}

%%-/
