import PrimeNumberTheoremAnd.SecondarySummary

namespace Lcm

open ArithmeticFunction hiding log
open Real

/-%%
\section{The least common multiple sequence is not highly abundant for large \(n\)}
%%-/

/-%%
\subsection{Problem statement and notation}
%%-/

/-%%
\begin{definition}\label{sigma-def}\lean{σ}\leanok $\sigma(n)$ is the sum of the divisors of $n$.
\end{definition}
%%-/

def σ : ArithmeticFunction ℕ := sigma 1

noncomputable abbrev σnorm (n : ℕ) : ℝ := (σ n : ℝ) / (n : ℝ)

/-%%
\begin{definition}\label{highlyabundant-def}\lean{HighlyAbundant}\leanok\uses{sigma-def}
A positive integer \(N\) is called \emph{highly abundant} (HA) if
\[
  \sigma(N) > \sigma(m)
\]
for all positive integers \(m < N\), where \(\sigma(n)\) denotes the sum of the positive divisors of \(n\).
\end{definition}
%%-/

def HighlyAbundant (N : ℕ) : Prop :=
  ∀ m : ℕ, m < N → σ m < σ N

/-%%
\begin{definition}\label{Ln-def}\lean{L}\leanok
For each integer \(n \ge 1\), define
\[
  L_n := \mathrm{lcm}(1,2,\dots,n).
\]
We call \((L_n)_{n \ge 1}\) the \emph{least common multiple sequence}.
\end{definition}
%%-/

def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm _root_.id

/-%%
\textbf{Original MathOverflow question.}
Is it true that every value in the sequence \(L_n = \mathrm{lcm}(1,2,\dots,n)\) is highly abundant?  Equivalently,
\[
  \{L_n : n \ge 1\} \subseteq HA?
\]

In this note we record the structure of an argument showing that, for all sufficiently large \(n\), the integer \(L_n\) is \emph{not} highly abundant.  This argument was taken from \href{https://mathoverflow.net/questions/501066/is-the-least-common-multiple-sequence-textlcm1-2-dots-n-a-subset-of-t?noredirect=1#comment1313839_501066}{this MathOverflow answer}.

\subsection{A general criterion using three medium primes and three large primes}
%%-/

/-%%
In this subsection we assume that $n \geq 1$ and that \(p_1,p_2,p_3,q_1,q_2,q_3\) are primes satisfiying
\[
  \sqrt{n} < p_1 < p_2 < p_3 < q_1 < q_2 < q_3 < n
\]
and the key criterion
\begin{equation}\label{eq:main-ineq}
  \prod_{i=1}^3\Bigl(1+\frac{1}{q_i}\Bigr)
  \le
  \Biggl( \prod_{i=1}^3 \Bigl(1+\frac{1}{p_i(p_i+1)}\Bigr) \Biggr)
  \Bigl(1 + \frac{3}{8n}\Bigr)
  \Biggl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Biggr).
\end{equation}
%%-/



structure Criterion where
  n : ℕ
  hn : n ≥ 1
  p : Fin 3 → ℕ
  hp : ∀ i, Nat.Prime (p i)
  hp_mono : StrictMono p
  q : Fin 3 → ℕ
  hq : ∀ i, Nat.Prime (q i)
  hq_mono : StrictMono q
  h_ord_1 : √(n : ℝ) < p 0
  h_ord_2 : p 2 < q 0
  h_ord_3 : q 2 < n
  h_crit : ∏ i, (1 + ((1:ℝ)/q i)) ≤ (∏ i, (1 + (1:ℝ)/(p i * (p i + 1)))) * (1 + (3:ℝ)/(8 * n)) * (1 - 4 * ∏ i, (p i : ℝ) / ∏ i, (q i : ℝ))


/-%%
\begin{lemma}\label{lem:4p3q3} % \lean{Criterion.prod_p_le_prod_q}\leanok  % problematic, flagged as line 55
We have $4 p_1 p_2 p_3 < q_1 q_2 q_3$.
\end{lemma}
%%-/


theorem Criterion.prod_p_le_prod_q (c : Criterion) : 4 * ∏ i, (c.p i) < ∏ i, (c.q i) := by sorry


/-%%

\begin{proof} Obvious from the non-negativity of the left-hand side of \eqref{eq:main-ineq}.
\end{proof}
%%-/

/-%%

\subsection{Factorisation of \(L_n\) and construction of a competitor}
%%-/

/-%%

\begin{lemma}[Factorisation of \(L_n\)]\label{lem:Lprime-def}\lean{Criterion.ln_eq, Criterion.q_not_dvd_L'}\leanok
There exists a positive integer \(L'\) such that
\[
  L_n = q_1 q_2 q_3 \, L'
\]
and each prime \(q_i\) divides \(L_n\) exactly once and does not divide \(L'\).
\end{lemma}
%%-/

noncomputable def Criterion.L' (c : Criterion) : ℕ := L c.n / ∏ i, c.q i

theorem Criterion.ln_eq (c : Criterion) : L c.n = (c.q 0) * (c.q 1) * (c.q 2) * c.L' := by sorry

theorem Criterion.q_not_dvd_L' (c : Criterion) : ∀ i, ¬(c.q i ∣ c.L') := by sorry

/-%%

\begin{proof}
Since \(q_i < n\), the prime \(q_i\) divides \(L_n\) exactly once (as \(q_i^2 > n\)).  Hence we may write \(L_n = q_1 q_2 q_3 L'\) where \(L'\) is the quotient obtained by removing these prime factors.  By construction, \(q_i \nmid L'\) for each \(i\).
\end{proof}
%%-/

/-%%

\begin{lemma}[Normalised divisor sum for \(L_n\)]\label{lem:sigmaLn}\lean{Criterion.σnorm_ln_eq}\leanok
Let \(L'\) be as in Lemma~\ref{lem:Lprime-def}. Then
\begin{equation}\label{eq:sigmaLn}
  \frac{\sigma(L_n)}{L_n}
  \;=\;
  \frac{\sigma(L')}{L'} \prod_{i=1}^3 \Bigl(1 + \frac{1}{q_i}\Bigr).
\end{equation}
\end{lemma}
%%-/

theorem Criterion.σnorm_ln_eq (c : Criterion) : σnorm (L c.n) = σnorm (c.L') * ∏ i, (1 + 1/(c.q i)) := by sorry

/-%%

\begin{proof}\uses{lem:Lprime-def}
Use the multiplicativity of \(\sigma(\cdot)\) and the fact that each \(q_i\) occurs to the first power in \(L_n\).  Then
\[
  \sigma(L_n)
  = \sigma(L') \prod_{i=1}^3 \sigma(q_i)
  = \sigma(L') \prod_{i=1}^3 (1+q_i).
\]
Dividing by \(L_n = L' \prod_{i=1}^3 q_i\) gives
\[
  \frac{\sigma(L_n)}{L_n}
  = \frac{\sigma(L')}{L'} \prod_{i=1}^3 \frac{1+q_i}{q_i}
  = \frac{\sigma(L')}{L'} \prod_{i=1}^3 \Bigl(1 + \frac{1}{q_i}\Bigr).
\]
\end{proof}
%%-/

/-%%

\begin{lemma}\label{div-remainder}\lean{Criterion.r_ge, Criterion.r_le, Criterion.prod_q_eq}\leanok
There exist integers \(m \ge 0\) and \(r\) satisfying \(0 < r < 4 p_1 p_2 p_3\) and
\[
  q_1 q_2 q_3 = 4 p_1 p_2 p_3 m + r
\]
\end{lemma}
%%-/

def Criterion.m (c : Criterion) : ℕ := (∏ i, c.q i) / (4 * ∏ i, c.p i)

def Criterion.r (c : Criterion) : ℕ := (∏ i, c.q i) % (4 * ∏ i, c.p i)

theorem Criterion.r_ge (c : Criterion) : 0 < c.r := by sorry

theorem Criterion.r_le (c : Criterion) : c.r < 4 * ∏ i, c.p i := by sorry

theorem Criterion.prod_q_eq (c : Criterion) : ∏ i, c.q i = 4 * ∏ i, c.p i * c.m + c.r := by sorry


/-%%

\begin{proof} This is division with remainder.
\end{proof}
%%-/

/-%%

\begin{definition}\label{M-def}\lean{Criterion.M}\leanok\uses{div-remainder}
With $m,r$ as above, define the competitor
\[
  M := 4 p_1 p_2 p_3 m L'.
\]
\end{definition}
%%-/

noncomputable def Criterion.M (c : Criterion) : ℕ := 4 * ∏ i, c.p i * c.m * c.L'

/-%%

\begin{lemma}[Basic properties of \(M\)]\label{lem:M-basic} % \lean{Criterion.M_lt, Criterion.Ln_div_M_gt, Criterion.Ln_div_M_lt}\leanok\uses{M-def}
With notation as above, we have:
\begin{enumerate}
  \item \(M < L_n\).
  \item
  \[
    1 < \frac{L_n}{M} = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
      < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
  \]
\end{enumerate}
\end{lemma}
%%-/

theorem Criterion.M_lt (c : Criterion) : c.M < L c.n := by sorry

theorem Criterion.Ln_div_M_gt (c : Criterion) : 1 < (L c.n) / (c.M) := by sorry

theorem Criterion.Ln_div_M_lt (c : Criterion) : (L c.n) / (c.M) < (1 - ((4:ℝ) * ∏ i, c.p i) / (∏ i, c.q i))⁻¹ := by sorry


/-%%

\begin{proof}
The first item is by construction of the division algorithm.
For the second, note that
\[
  L_n = q_1 q_2 q_3 L' = (4 p_1 p_2 p_3 m + r) L' > 4 p_1 p_2 p_3 m L' = M,
\]
since \(r>0\). For the third,
\[
  \frac{L_n}{M} = \frac{4 p_1 p_2 p_3 m + r}{4 p_1 p_2 p_3 m}
              = 1 + \frac{r}{4 p_1 p_2 p_3 m}
              = \Bigl(1 - \frac{r}{4 p_1 p_2 p_3 m + r}\Bigr)^{-1}
              = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}.
\]
Since \(0 < r < 4p_1p_2p_3\) and \(4p_1p_2p_3 < q_1q_2q_3\), we have
\[
  0<\frac{r}{q_1 q_2 q_3}<\frac{4p_1p_2p_3}{q_1 q_2 q_3},
\]
so
\[
  \Bigl(1-\frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
  < \Bigl(1-\frac{4p_1p_2p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
\]
\end{proof}
%%-/

/-%%

\subsection{A sufficient condition}

We give a sufficient condition for $\sigma(M) \geq \sigma(L_n)$.
%%-/

/-%%

\begin{lemma}[A sufficient inequality]\label{lem:criterion-sufficient} % \lean{Criterion.not_highlyAbundant_1}\leanok\uses{M-def}
Suppose
\[
  \frac{\sigma(M)}{M}
  \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)
  \;\ge\; \frac{\sigma(L_n)}{L_n}.
\]
Then \(\sigma(M) \ge \sigma(L_n)\), and so \(L_n\) is not highly abundant.
\end{lemma}
%%-/

theorem Criterion.not_highlyAbundant_1 (c : Criterion) (h : (σnorm (c.M)) * (1 - (4 : ℝ) * ∏ i, c.p i / ∏ i, c.q i) ≥ σnorm (L c.n)) : ¬ HighlyAbundant (L c.n) := by sorry


/-%%
\begin{proof}\uses{lem:M-basic}
By Lemma~\ref{lem:M-basic},
\[
  \frac{L_n}{M} < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
\]
Hence
\[
  \frac{\sigma(M)}{M} \ge \frac{\sigma(L_n)}{L_n}
  \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}
  > \frac{\sigma(L_n)}{L_n} \cdot \frac{M}{L_n}.
\]
Multiplying both sides by \(M\) gives
\[
  \sigma(M) > \sigma(L_n) \cdot \frac{M}{L_n}
\]
and hence
\[
  \sigma(M) \ge \sigma(L_n),
\]
since \(M/L_n<1\) and both sides are integers.
\end{proof}
%%-/

/-%%

Combining Lemma \ref{lem:criterion-sufficient} with Lemma \ref{lem:sigmaLn}, we see that it suffices to bound \(\sigma(M)/M\) from below in terms of \(\sigma(L')/L'\):

\begin{lemma}[Reduction to a lower bound for \(\sigma(M)/M\)]\label{lem:criterion-reduced} % \lean{Criterion.not_highlyAbundant_2}\leanok % Problematic, flagged as line 220
If
\begin{equation}\label{eq:sigmaM-lower}
  \frac{\sigma(M)}{M}
  \;\ge\;
  \frac{\sigma(L')}{L'}
  \Biggl( \prod_{i=1}^3 \Bigl(1+\frac{1}{p_i(p_i+1)}\Bigr) \Biggr)
  \Bigl(1 + \frac{3}{8n}\Bigr),
\end{equation}
then $L_n$ is not highly abundant.
\end{lemma}
%%-/

theorem Criterion.not_highlyAbundant_2 (c : Criterion) (h : (σnorm c.M) ≥ (σnorm c.L') * ∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ))) * (1 + (3 : ℝ) / (8 * c.n))) : ¬ HighlyAbundant (L c.n) := by sorry


/-%%

\begin{proof}\uses{lem:sigmaLn, lem:criterion-sufficient}
Insert \eqref{eq:sigmaM-lower} and \eqref{eq:sigmaLn} into the desired inequality and compare with the assumed bound \eqref{eq:main-ineq}; this is a straightforward rearrangement.
\end{proof}
%%-/

/-%%



\subsection{Conclusion of the criterion}

\begin{lemma}[Lower bound for \(\sigma(M)/M\)]\label{lem:sigmaM-lower-final}\lean{Criterion.σnorm_M_ge_σnorm_L'_mul}\leanok
With notation as above,
\[
  \frac{\sigma(M)}{M}
  \ge
  \frac{\sigma(L')}{L'}
  \Biggl( \prod_{i=1}^3 \Bigl(1 + \frac{1}{p_i(p_i+1)}\Bigr) \Biggr)
  \Bigl(1 + \frac{3}{8n}\Bigr).
\]
\end{lemma}
%%-/

theorem Criterion.σnorm_M_ge_σnorm_L'_mul (c : Criterion) : (σnorm c.M) ≥ (σnorm c.L') * ∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ))) * (1 + (3:ℝ) / (8 * c.n)) := by sorry


/-%%
\begin{proof}  By multiplicativity, we have
$$
  \frac{\sigma(M)}{M}
  \ge
  \frac{\sigma(L')}{L'}
  \prod_p \frac{1+p^{-1}+\dots+p^{-\nu_p(M)}}{1+p^{-1}+\dots+p^{-\nu_p(L')}.
$$
The contribution of $p=p_i$ is
\[
  \frac{(1+p_i+p_i^2)/p_i^2}{(1+p_i)/p_i}
  = 1 + \frac{1}{p_i(p_i+1)}.
\]
The contribution of $p=2$ is
\[
  \frac{(1+2+\dots+2^{k+2})/2^{k+2}}{(1+2+\dots+2^k)/2^k},
\]
where \(k\) is the largest integer such that \(2^k \le n\)
A direct calculation yields
\[
  \frac{1+2+\dots+2^{k+2}}{1+2+\dots+2^k}
  = \frac{2^{k+3}-1}{2^{k+1}-1}
  = 1 + \frac{3(2^k-1)}{2^{k+1}-1}
  \ge 1 + \frac{3}{2^{k+3}-4},
\]
Finally, since \(2^k \le n < 2^{k+1}\), we have \(2^{k+3} < 8n\), so
\[
  \frac{3}{2^{k+3}-4} \ge \frac{3}{8n},
\]
So the contribution from the prime \(2\) is at least \(1 + 3/(8n)\).

Finally, the contribution of all other primes is at least \(1\).
\end{proof}
%%-/


/-%%

\begin{theorem}\label{thm:criterion} % \lean{Criterion.not_highlyAbundant}\leanok
Let $n \geq 1$.
Suppose that primes \(p_1,p_2,p_3,q_1,q_2,q_3\) satisfy
\[
  \sqrt{n} < p_1 < p_2 < p_3 < q_1 < q_2 < q_3 < n
\]
and the key criterion \eqref{eq:main-ineq}.
Then \(L_n\) is not highly abundant.
\end{theorem}
%%-/

theorem Criterion.not_highlyAbundant (c : Criterion) : ¬ HighlyAbundant (L c.n) := c.not_highlyAbundant_2 c.σnorm_M_ge_σnorm_L'_mul

/-%%

\begin{proof}\leanok\uses{leam:sigmaM-lower-final, lem:criterion-reduced, lem:criterion-sufficient}
By Lemma~\ref{lem:sigmaM-lower-final}, the condition \eqref{eq:sigmaM-lower} holds.  By Lemma~\ref{lem:criterion-reduced} this implies
\[
  \frac{\sigma(M)}{M}
  \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)
  \ge \frac{\sigma(L_n)}{L_n}.
\]
Applying Lemma~\ref{lem:criterion-sufficient}, we obtain \(\sigma(M) \ge \sigma(L_n)\) with \(M < L_n\), so \(L_n\) cannot be highly abundant.
\end{proof}
%%-/

/-%%

\begin{remark}
Analogous arguments allow other pairs \((c,\alpha)\) in place of \((4,3/8)\), such as \((2,1/4)\), \((6,17/36)\), \((30,0.632\dots)\); or even \((1,0)\) provided more primes are used on the \(p\)-side than the \(q\)-side to restore an asymptotic advantage.
\end{remark}
%%-/


abbrev X₀ := 89693

/-%%

\subsection{Choice of six primes \(p_i,q_i\) for large \(n\)}

\begin{lemma}[Choice of medium primes \(p_i\)]\label{lem:choose-pi} % \lean{exists_p_primes}\leanok
Let \(n \ge X_0^2\). Set \(x := \sqrt{n}\). Then there exist primes \(p_1,p_2,p_3\) with
\[
  p_i \le x \Bigl(1 + \frac{1}{\log^3 x}\Bigr)^i
\]
and \(p_1 < p_2 < p_3\).
Moreover, \(\sqrt{n} < p_1\)
\end{lemma}
%%-/

theorem exists_p_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) : ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧ (∀ i, p i ≤ √(n : ℝ) * (1 + 1 / (log (√(n : ℝ))) ^ 3) ^ (i+1:ℝ)) ∧ (√(n : ℝ) < p 0) := by sorry

/-%%

\begin{proof}\uses{thm:Dusart}
Apply Theorem~\ref{thm:Dusart} successively with \(x, x(1+1/\log^3 x), x(1+1/\log^3 x)^2\), keeping track of the resulting primes and bounds.  For \(n\) large and \(x = \sqrt{n}\), we have \(\sqrt{n} < p_1\) as soon as the first interval lies strictly above \(\sqrt{n}\); this can be enforced by taking \(n\) large enough.
\end{proof}
%%-/

/-%%

\begin{lemma}[Choice of large primes \(q_i\)]\label{lem:choose-qi} % \lean{exists_q_primes}\leanok
Let \(n \ge X_0^2\). Then there exist primes \(q_1 < q_2 < q_3\) with
\[
  q_{4-i} \ge n \Bigl(1 + \frac{1}{\log^3 \sqrt{n}}\Bigr)^{-i}
\]
for \(i = 1,2,3\), and \(q_1 < q_2 < q_3 < n\).
\end{lemma}
%%-/

theorem exists_q_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) : ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧ (∀ i:Fin 3, n * (1 + 1 / (log (√(n : ℝ))) ^ 3) ^ (3-(i:ℕ)) ≤ q i) ∧ (q 2 < n) := by sorry


/-%%

\begin{proof}\uses{thm:Dusart}
Apply Theorem~\ref{thm:Dusart} with suitable values of \(x\) slightly below \(n\), e.g.\ \(x = n(1+1/\log^3\sqrt{n})^{-i}\), again keeping track of the intervals.  For \(n\) large enough, these intervals lie in \((\sqrt{n},n)\) and contain primes \(q_i\) with the desired ordering.
\end{proof}
%%-/

/-%%

\subsection{Bounding the factors in \eqref{eq:main-ineq}}

\begin{lemma}[Bounds for the \(q_i\)-product]\label{lem:qi-product} % \lean{prod_q_ge}\leanok
With \(p_i,q_i\) as in Lemmas~\ref{lem:choose-pi} and \ref{lem:choose-qi}, we have
\begin{equation}\label{eq:qi-upper}
  \prod_{i=1}^3 \Bigl(1 + \frac{1}{q_i}\Bigr)
  \le
  \prod_{i=1}^3 \Bigl(1 + \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^i}{n} \Bigr).
\end{equation}
\end{lemma}
%%-/

theorem prod_q_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : ∏ i, (1 + (1:ℝ) / ((exists_q_primes hn).choose i)) ≤ ∏ i:Fin 3, (1 + (1 + 1 / (log (√(n : ℝ))) ^ 3) ^ ((i:ℕ)+1:ℝ) / n) := by sorry


/-%%

\begin{proof}\uses{lem:choose-qi}
By Lemma~\ref{lem:choose-qi}, each \(q_i\) is at least
\[
  n\Bigl(1 + \frac{1}{\log^3 \sqrt{n}}\Bigr)^{-j}
\]
for suitable indices \(j\), so \(1/q_i\) is bounded above by
\[
  \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^i}{n}
\]
after reindexing. Multiplying the three inequalities gives \eqref{eq:qi-upper}.
\end{proof}
%%-/

/-%%

\begin{lemma}[Bounds for the \(p_i\)-product]\label{lem:pi-product} % \lean{prod_p_ge}\leanok
With \(p_i\) as in Lemma~\ref{lem:choose-pi}, we have for large \(n\)
\begin{equation}\label{eq:pi-lower}
  \prod_{i=1}^3 \Bigl(1 + \frac{1}{p_i(p_i+1)}\Bigr)
  \ge
  \prod_{i=1}^3
  \Bigl(
    1 + \frac{1}{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{2i} (n + \sqrt{n})}
  \Bigr).
\end{equation}
\end{lemma}
%%-/

theorem prod_p_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : ∏ i, (1 + (1:ℝ) / ((exists_p_primes hn).choose i)*((exists_p_primes hn).choose i + 1)) ≥ ∏ i:Fin 3, (1 + (1 + 1 / (log (√(n : ℝ))) ^ 3) ^ (2*(i:ℕ)+2:ℝ) * (n + √n)) := by sorry


/-%%

\begin{proof}
By Lemma~\ref{lem:choose-pi}, \(p_i \le \sqrt{n} (1+1/\log^3\sqrt{n})^i\).  Hence
\[
  p_i^2 \le n\bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{2i}
\quad\text{and}\quad
  p_i+1 \le p_i(1 + 1/\sqrt{n}) \le (1+1/\sqrt{n}) p_i.
\]
From these one gets
\[
  p_i(p_i+1) \le \bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{2i} (n + \sqrt{n}),
\]
and hence
\[
  \frac{1}{p_i(p_i+1)} \ge
  \frac{1}{\bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{2i} (n + \sqrt{n})}.
\]
Taking \(1+\cdot\) and multiplying over \(i=1,2,3\) gives \eqref{eq:pi-lower}.
\end{proof}
%%-/

/-%%

\begin{lemma}[Lower bound for the product ratio \(p_i/q_i\)]\label{lem:pq-ratio} % \lean{pq_ratio_ge}\leanok
With \(p_i,q_i\) as in Lemmas~\ref{lem:choose-pi} and \ref{lem:choose-qi}, we have
\begin{equation}\label{eq:pq-ratio}
  1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}
  \ge
  1 - \frac{4 \bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{12}}{n^{3/2}}.
\end{equation}
\end{lemma}
%%-/

theorem pq_ratio_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : 1 - (4 : ℝ) * ∏ i, (exists_p_primes hn).choose i / ∏ i, (exists_q_primes hn).choose i ≥ 1 - (4 * (1 + 1 / (log (√(n : ℝ))) ^ 3) ^ 12) / (n ^ (3 / 2)) := by sorry

/-%%

\begin{proof}
We have \(p_i \le \sqrt{n} (1+1/\log^3 \sqrt{n})^i\), so
\[
  p_1 p_2 p_3 \le n^{3/2} \bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{6}.
\]
Similarly, \(q_i \ge n(1+1/\log^3 \sqrt{n})^{-i}\), so
\[
  q_1 q_2 q_3 \ge n^3 \bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{-6}.
\]
Combining,
\[
  \frac{p_1 p_2 p_3}{q_1 q_2 q_3} \le
  \frac{n^{3/2} \bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{6}}{n^3 \bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{-6}}
  = \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{12}}{n^{3/2}}.
\]
This implies \eqref{eq:pq-ratio}.
\end{proof}
%%-/

/-%%

\subsection{Reduction to a small epsilon-inequality}

\begin{lemma}[Uniform bounds for large \(n\)]\label{lem:eps-bounds} % \lean{inv_cube_log_sqrt_le, inv_n_pow_3_div_2_le}\leanok
For all \(n \ge X_0^2 = 89693^2\) we have
\[
  \frac{1}{\log^3 \sqrt{n}}
  \le 0.000675,
  \qquad
  \frac{1}{n^{3/2}} \le \frac{1}{89693}\cdot\frac{1}{n}.
\]
\end{lemma}

%%-/

theorem inv_cube_log_sqrt_le (n : ℕ) (hn : n ≥ X₀ ^ 2) : 1 / (log (√(n : ℝ))) ^ 3 ≤ 0.000675 := by sorry

theorem inv_n_pow_3_div_2_le (n : ℕ) (hn : n ≥ X₀ ^ 2) : 1 / (n ^ (3 / 2)) ≤ (1 / (89693 : ℝ)) * (1 / (n : ℝ)) := by sorry

/-%%
\begin{proof}
This is a straightforward calculus and monotonicity check: the left-hand sides are decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at \(n=X_0^2\).  One can verify numerically or symbolically.
\end{proof}
%%-/


/-%%

\begin{lemma}[Polynomial approximation of the inequality]\label{lem:poly-ineq} % \lean{prod_epsilon_le, prod_epsilon_ge}\leanok
For \(0 \le \varepsilon \le 1/89693^2\), we have
\[
  \prod_{i=1}^3 (1 + 1.000675^i \varepsilon)
  \le
  \Bigl(1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3\Bigr),
\]
and
\[
  \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i}}\Bigr)
  \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
  \Bigl(1 - \frac{4 \times 1.000675^{12}}{89693}\varepsilon\Bigr)
  \ge
  1 + 3.37\varepsilon - 0.01\varepsilon^2.
\]
\end{lemma}
%%-/

theorem prod_epsilon_le (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) : ∏ i:Fin 3, (1 + (1.000675 : ℝ) ^ ((i:ℕ)+1:ℝ) * ε) ≤ 1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by sorry

theorem prod_epsilon_ge (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) : (∏ i:Fin 3, (1 + ε / (1.000675 : ℝ) ^ (2*((i:ℕ)+1:ℝ)))) * (1 + (3 : ℝ) / 8 * ε) * (1 - (4 * (1.000675 : ℝ) ^ 12) / 89693 * ε) ≥ 1 + 3.37 * ε - 0.01 * ε ^ 2 := by sorry

/-%%

\begin{proof}
Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using the bounds in Lemma~\ref{lem:eps-bounds}, and bound the tails by simple inequalities such as
\[
  (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
\]
for small \(\varepsilon\).
All coefficients can be bounded numerically in a rigorous way; this step is a finite computation that can be checked mechanically.
\end{proof}
%%-/

/-%%

\begin{lemma}[Final polynomial comparison]\label{lem:final-comparison} % \lean{final_comparison}\leanok
For \(0 \le \varepsilon \le 1/89693^2\), we have
\[
  1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
  \le 1 + 3.37\varepsilon - 0.01\varepsilon^2.
\]
\end{lemma}
%%-/

theorem final_comparison (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) : 1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.37 * ε - 0.01 * ε ^ 2 := by sorry

/-%%
\begin{proof}
This is equivalent to
\[
  3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
  \le 3.37\varepsilon - 0.01\varepsilon^2,
\]
or
\[
  0 \le (3.37 - 3.01)\varepsilon - (3.01+0.01)\varepsilon^2 - 1.01\varepsilon^3.
\]
Factor out \(\varepsilon\) and use that \(0<\varepsilon \le 1/89693^2\) to check that the resulting quadratic in \(\varepsilon\) is nonnegative on this interval.  Again, this is a finite computation that can be verified mechanically.
\end{proof}
%%-/

/-%%

\begin{proposition}[Verification of \eqref{eq:main-ineq} for large \(n\)]\label{prop:ineq-holds-large-n}\lean{Criterion.mk'}\leanok
For every integer \(n \ge X_0^2 = 89693^2 \approx 8.04\times 10^9\), the primes \(p_i,q_i\) constructed in Lemmas~\ref{lem:choose-pi} and \ref{lem:choose-qi} satisfy the inequality \eqref{eq:main-ineq}.
\end{proposition}
%%-/

noncomputable def Criterion.mk' {n : ℕ} (hn : n ≥ X₀ ^ 2) : Criterion := {
  n := n
  p := (exists_p_primes hn).choose
  q := (exists_q_primes hn).choose
  hn := sorry
  hp := sorry
  hp_mono := sorry
  hq := sorry
  hq_mono := sorry
  h_ord_1 := sorry
  h_ord_2 := sorry
  h_ord_3 := sorry
  h_crit  := sorry
}

/-%%

\begin{proof}\uses{lem:qi-product, lem:pi-product, lem:pq-ratio, lem:eps-bounds, lem:poly-ineq, lem:final-comparison}
Combine Lemma~\ref{lem:qi-product}, Lemma~\ref{lem:pi-product}, and Lemma~\ref{lem:pq-ratio}.  Then apply Lemma~\ref{lem:eps-bounds} and set \(\varepsilon = 1/n\).  The products are bounded by the expressions in Lemma~\ref{lem:poly-ineq}, and the inequality in Lemma~\ref{lem:final-comparison} then ensures that \eqref{eq:main-ineq} holds.
\end{proof}
%%-/

/-%%

\subsection{Conclusion for large \(n\)}

\begin{theorem}[Non-highly abundant for large \(n\)]\label{thm:large-n-final} % \lean{L_not_HA_of_ge}\leanok
For every integer \(n \ge 89693^2\), the integer \(L_n\) is not highly abundant.
\end{theorem}
%%-/

theorem L_not_HA_of_ge (n : ℕ) (hn : n ≥ 89693 ^ 2) : ¬ HighlyAbundant (L n) := sorry


/-%%

\begin{proof}\uses{prop:ineq-holds-large-n, thm:criterion}
By Proposition~\ref{prop:ineq-holds-large-n}, there exist primes \(p_1,p_2,p_3,q_1,q_2,q_3\) satisfying the hypotheses of Theorem~\ref{thm:criterion}.  Hence \(L_n\) is not highly abundant.
\end{proof}


%%-/

end Lcm
