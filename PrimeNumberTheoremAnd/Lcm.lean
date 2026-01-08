import Architect
import PrimeNumberTheoremAnd.SecondarySummary

namespace Lcm

open ArithmeticFunction hiding log
open Finset Nat Real

blueprint_comment /--
\section{The least common multiple sequence is not highly abundant for large \(n\)}
-/

blueprint_comment /--
\subsection{Problem statement and notation}
-/

@[blueprint
  "sigma-def"
  (statement := /-- $\sigma(n)$ is the sum of the divisors of $n$. -/)]
def σ : ArithmeticFunction ℕ := sigma 1

noncomputable abbrev σnorm (n : ℕ) : ℝ := (σ n : ℝ) / (n : ℝ)

@[blueprint
  "highlyabundant-def"
  (statement := /--
  A positive integer \(N\) is called \emph{highly abundant} (HA) if
  \[
    \sigma(N) > \sigma(m)
  \]
  for all positive integers \(m < N\), where \(\sigma(n)\) denotes the sum of the positive divisors
  of \(n\).
  -/)]
def HighlyAbundant (N : ℕ) : Prop :=
  ∀ m : ℕ, m < N → σ m < σ N

@[blueprint
  "Ln-def"
  (statement := /--
  For each integer \(n \ge 1\), define
  \[
    L_n := \mathrm{lcm}(1,2,\dots,n).
  \]
  We call \((L_n)_{n \ge 1}\) the \emph{least common multiple sequence}.
  -/)]
def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm _root_.id

blueprint_comment /--
\begin{quote}
\textbf{Original MathOverflow question.}
Is it true that every value in the sequence \(L_n = \mathrm{lcm}(1,2,\dots,n)\) is highly abundant?
Equivalently,
\[
  \{L_n : n \ge 1\} \subseteq HA?
\]
\end{quote}

In this note we record the structure of an argument showing that, for all sufficiently large \(n\),
the integer \(L_n\) is \emph{not} highly abundant.  This argument was taken from
\href{https://mathoverflow.net/questions/501066/is-the-least-common-multiple-sequence-textlcm1-2-dots-n-a-subset-of-t?noredirect=1\#comment1313839_501066}{this MathOverflow answer}.

It has previously been verified in Lean that \(L_n\) is highly aboundant for $n \leq 70$, $81 \leq n \leq 96$, $125 \leq n \leq 148$, $169 \leq n \leq 172$, and not highly aboundant for all other $n ≤ 10^{10}$.  The arguments here establish the non-highly-abundance of \(L_n\) for all $n \geq 89683^2$ sufficiently large \(n\), thus completing the determination in Lean of all $n$ for which \(L_n\) is highly abundant.

\subsection{A general criterion using three medium primes and three large primes}
-/

blueprint_comment /--
In this subsection we assume that $n \geq 1$ and that \(p_1,p_2,p_3,q_1,q_2,q_3\) are primes
satisfiying
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

NOTE: In the Lean formalization of this argument, we index the primes from 0 to 2 rather than from 1 to 3.
-/

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
  h_crit : ∏ i, (1 + (1 : ℝ) / q i) ≤
    (∏ i, (1 + (1 : ℝ) / (p i * (p i + 1)))) * (1 + (3 : ℝ) / (8 * n)) *
      (1 - 4 * (∏ i, (p i : ℝ)) / ∏ i, (q i : ℝ))

@[blueprint
  "lem:4p3q3"
  (statement := /-- We have $4 p_1 p_2 p_3 < q_1 q_2 q_3$. -/)
  (proof := /-- Obvious from the non-negativity of the left-hand side of \eqref{eq:main-ineq}. -/)
  (latexEnv := "lemma")]
theorem Criterion.prod_p_le_prod_q (c : Criterion) : 4 * ∏ i, c.p i < ∏ i, c.q i := by
  have hBC_pos : 0 < (∏ i, (1 + (1 : ℝ) / (c.p i * (c.p i + 1)))) * (1 + 3 / (8 * c.n)) := by positivity
  have hR_pos : 0 < 1 - 4 * (∏ i, (c.p i : ℝ)) / ∏ i, (c.q i : ℝ) := by
    by_contra h
    exact absurd (c.h_crit.trans (mul_nonpos_of_nonneg_of_nonpos hBC_pos.le (not_lt.mp h)))
      (not_le.mpr <| prod_pos fun i _ ↦ by positivity)
  rw [sub_pos, div_lt_one <| prod_pos fun i _ ↦ cast_pos.mpr (c.hq i).pos] at hR_pos
  exact_mod_cast hR_pos

blueprint_comment /--
\subsection{Factorisation of \(L_n\) and construction of a competitor}
-/

noncomputable def Criterion.L' (c : Criterion) : ℕ := L c.n / ∏ i, c.q i

lemma Criterion.prod_q_dvd_L (c : Criterion) : ∏ i, c.q i ∣ L c.n :=
  Fintype.prod_dvd_of_isRelPrime (fun i j h ↦ coprime_iff_isRelPrime.mp <|
    (coprime_primes (c.hq i) (c.hq j)).mpr (c.hq_mono.injective.ne h)) fun i ↦ dvd_lcm <|
      mem_Icc.mpr ⟨(c.hq i).one_le, (c.hq_mono.monotone (Fin.le_last i)).trans c.h_ord_3.le⟩

lemma Criterion.L_pos (c : Criterion) : 0 < L c.n :=
  lt_of_lt_of_le Nat.zero_lt_one <| one_le_iff_ne_zero.mpr fun h ↦ by simp_all [L]

lemma Criterion.L'_pos (c : Criterion) : 0 < c.L' :=
  div_pos (le_of_dvd c.L_pos c.prod_q_dvd_L) (prod_pos fun i _ ↦ (c.hq i).pos)

lemma Criterion.L_eq_prod_q_mul_L' (c : Criterion) : L c.n = (∏ i, c.q i) * c.L' := by
  rw [L', Nat.mul_div_cancel' c.prod_q_dvd_L]

@[blueprint
  "lem:Lprime-def"
  (title := "Factorisation of \\(L_n\\)")
  (statement := /--
  There exists a positive integer \(L'\) such that
  \[
    L_n = q_1 q_2 q_3 \, L'
  \]
  and each prime \(q_i\) divides \(L_n\) exactly once and does not divide \(L'\).
  -/)
  (proof := /-- Since \(q_i < n\), the prime \(q_i\) divides \(L_n\) exactly once (as \(q_i^2 > n\)).
  Hence we may write \(L_n = q_1 q_2 q_3 L'\) where \(L'\) is the quotient obtained by removing
  these prime factors.  By construction, \(q_i \nmid L'\) for each \(i\). -/)
  (latexEnv := "lemma")]
theorem Criterion.ln_eq (c : Criterion) : L c.n = c.q 0 * c.q 1 * c.q 2 * c.L' := by
  rw [L', ← Fin.prod_univ_three, Nat.mul_div_cancel' <| Fintype.prod_dvd_of_isRelPrime ?_ ?_]
  · refine fun i j h ↦ Nat.coprime_iff_isRelPrime.mp ?_
    exact Nat.coprime_primes (c.hq i) (c.hq j) |>.mpr <| c.hq_mono.injective.ne h
  refine fun i ↦ Finset.dvd_lcm <| Finset.mem_Icc.mpr ⟨c.hq i |>.one_le, le_trans ?_ c.h_ord_3.le⟩
  exact c.hq_mono.monotone <| Fin.le_last i

@[blueprint
  "lem:Lprime-def"
  (title := "Factorisation of \\(L_n\\)")
  (statement := /--
  There exists a positive integer \(L'\) such that
  \[
    L_n = q_1 q_2 q_3 \, L'
  \]
  and each prime \(q_i\) divides \(L_n\) exactly once and does not divide \(L'\).
  -/)
  (proof := /-- Since \(q_i < n\), the prime \(q_i\) divides \(L_n\) exactly once (as \(q_i^2 > n\)).
  Hence we may write \(L_n = q_1 q_2 q_3 L'\) where \(L'\) is the quotient obtained by removing these
  prime factors.  By construction, \(q_i \nmid L'\) for each \(i\). -/)
  (latexEnv := "lemma")]
theorem Criterion.q_not_dvd_L' (c : Criterion) : ∀ i, ¬(c.q i ∣ c.L') := by sorry

@[blueprint
  "lem:sigmaLn"
  (title := "Normalised divisor sum for \\(L_n\\)")
  (statement := /--
  Let \(L'\) be as in Lemma~\ref{lem:Lprime-def}. Then
  \begin{equation}\label{eq:sigmaLn}
    \frac{\sigma(L_n)}{L_n}
    \;=\;
    \frac{\sigma(L')}{L'} \prod_{i=1}^3 \Bigl(1 + \frac{1}{q_i}\Bigr).
  \end{equation}
  -/)
  (proof := /--
  Use the multiplicativity of \(\sigma(\cdot)\) and the fact that each \(q_i\) occurs to the first
  power in \(L_n\).  Then
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
  -/)
  (proofUses := ["lem:Lprime-def"])
  (latexEnv := "lemma")]
theorem Criterion.σnorm_ln_eq (c : Criterion) :
    σnorm (L c.n) = σnorm c.L' * ∏ i, (1 + (1 : ℝ) / c.q i) := by
  have hcop : ∀ i j, i ≠ j → (c.q i).Coprime (c.q j) := fun i j h ↦
    (coprime_primes (c.hq i) (c.hq j)).mpr (c.hq_mono.injective.ne h)
  have hcopL' : ∀ i, (c.q i).Coprime c.L' := fun i ↦
    (c.hq i).coprime_iff_not_dvd.mpr (c.q_not_dvd_L' i)
  have hσ_prime : ∀ i, sigma 1 (c.q i) = 1 + c.q i := fun i ↦ by
    rw [← pow_one (c.q i), sigma_one_apply_prime_pow (c.hq i), sum_range_succ, range_one,
      sum_singleton, pow_zero, pow_one]
  simp only [σnorm, σ, c.L_eq_prod_q_mul_L', Fin.prod_univ_three]
  rw [show c.q 0 * c.q 1 * c.q 2 * c.L' = (c.q 0 * c.q 1 * c.q 2) * c.L' by ring,
      isMultiplicative_sigma.map_mul_of_coprime (coprime_mul_iff_left.mpr
        ⟨coprime_mul_iff_left.mpr ⟨hcopL' 0, hcopL' 1⟩, hcopL' 2⟩),
      show c.q 0 * c.q 1 * c.q 2 = c.q 0 * (c.q 1 * c.q 2) by ring,
      isMultiplicative_sigma.map_mul_of_coprime (coprime_mul_iff_right.mpr
        ⟨hcop 0 1 Fin.zero_ne_one, hcop 0 2 <| not_eq_of_beq_eq_false rfl⟩),
      isMultiplicative_sigma.map_mul_of_coprime (hcop 1 2 <| not_eq_of_beq_eq_false rfl),
      hσ_prime, hσ_prime, hσ_prime]
  have hq_ne : ∀ i, (c.q i : ℝ) ≠ 0 := fun i ↦ (cast_pos.mpr (c.hq i).pos).ne'
  field_simp [hq_ne, (cast_pos.mpr c.L'_pos).ne']
  grind

def Criterion.m (c : Criterion) : ℕ := (∏ i, c.q i) / (4 * ∏ i, c.p i)

def Criterion.r (c : Criterion) : ℕ := (∏ i, c.q i) % (4 * ∏ i, c.p i)

@[blueprint
  "div-remainder"
  (statement := /--
   There exist integers \(m \ge 0\) and \(r\) satisfying \(0 < r < 4 p_1 p_2 p_3\) and
   \[q_1 q_2 q_3 = 4 p_1 p_2 p_3 m + r \]
  -/)
  (proof := /-- This is division with remainder. -/)
  (latexEnv := "lemma")]
theorem Criterion.r_ge (c : Criterion) : 0 < c.r := by
  simp only [r, Nat.pos_iff_ne_zero, ne_eq]
  intro h
  have h_dvd : c.p 2 ∣ ∏ i, c.q i :=
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ 2)).trans <|
      (Nat.dvd_mul_left _ 4).trans (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨i, _, hi⟩ := (c.hp 2).prime.exists_mem_finset_dvd h_dvd
  have : c.p 2 = c.q i := ((c.hq i).dvd_iff_eq (c.hp 2).ne_one).mp hi |>.symm
  exact absurd this (c.h_ord_2.trans_le (c.hq_mono.monotone (zero_le i))).ne

@[blueprint
  "div-remainder"
  (statement := /--
   There exist integers \(m \ge 0\) and \(r\) satisfying \(0 < r < 4 p_1 p_2 p_3\) and
  \[
    q_1 q_2 q_3 = 4 p_1 p_2 p_3 m + r
  \]
  -/)
  (proof := /-- This is division with remainder. -/)
  (latexEnv := "lemma")]
theorem Criterion.r_le (c : Criterion) : c.r < 4 * ∏ i, c.p i :=
  mod_lt _ <| mul_pos (zero_lt_succ 3) <| Finset.prod_pos <| fun i _ ↦ Prime.pos (c.hp i)

@[blueprint
  "div-remainder"
  (statement := /--
   There exist integers \(m \ge 0\) and \(r\) satisfying \(0 < r < 4 p_1 p_2 p_3\) and
  \[
    q_1 q_2 q_3 = 4 p_1 p_2 p_3 m + r
  \]
  -/)
  (proof := /-- This is division with remainder. -/)
  (latexEnv := "lemma")]
theorem Criterion.prod_q_eq (c : Criterion) : ∏ i, c.q i = (4 * ∏ i, c.p i) * c.m + c.r := by
  simp only [m, r, Nat.div_add_mod]

@[blueprint
  "M-def"
  (statement := /--
    With $m,r$ as above, define the competitor
  \[
    M := 4 p_1 p_2 p_3 m L'.
  \]
  -/)]
noncomputable def Criterion.M (c : Criterion) : ℕ := (4 * ∏ i, c.p i) * c.m * c.L'

lemma Criterion.m_pos (c : Criterion) : 0 < c.m :=
  Nat.div_pos c.prod_p_le_prod_q.le (mul_pos (zero_lt_succ 3) (prod_pos fun i _ ↦ (c.hp i).pos))

lemma Criterion.M_pos (c : Criterion) : 0 < c.M :=
  mul_pos (mul_pos (mul_pos (zero_lt_succ 3) (prod_pos fun i _ ↦ (c.hp i).pos)) c.m_pos) c.L'_pos

@[blueprint
  "lem:M-basic"
  (title := "Basic properties of \\(M\\)")
  (statement := /--
  With notation as above, we have:
  \begin{enumerate}
    \item \(M < L_n\).
    \item
    \[
      1 < \frac{L_n}{M} = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
        < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
    \]
  \end{enumerate}
  -/)
  (proof := /--
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
  -/)
  (latexEnv := "lemma")]
theorem Criterion.M_lt (c : Criterion) : c.M < L c.n := by
  calc c.M < ((4 * ∏ i, c.p i) * c.m + c.r) * c.L' :=
        mul_lt_mul_of_pos_right (Nat.lt_add_of_pos_right c.r_ge) c.L'_pos
    _ = (∏ i, c.q i) * c.L' := by rw [← c.prod_q_eq]
    _ = L c.n := c.L_eq_prod_q_mul_L'.symm

@[blueprint
  "lem:M-basic"
  (title := "Basic properties of \\(M\\)")
  (statement := /--
  With notation as above, we have:
  \begin{enumerate}
    \item \(M < L_n\).
    \item
    \[
      1 < \frac{L_n}{M} = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
        < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
    \]
  \end{enumerate}
  -/)
  (proof := /--
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
  -/)
  (latexEnv := "lemma")]
theorem Criterion.Ln_div_M_gt (c : Criterion) : (1 : ℝ) < L c.n / c.M := by
  rw [one_lt_div (cast_pos.mpr c.M_pos)]
  exact_mod_cast c.M_lt

@[blueprint
  "lem:M-basic"
  (title := "Basic properties of \\(M\\)")
  (statement := /--
  With notation as above, we have:
  \begin{enumerate}
    \item \(M < L_n\).
    \item
    \[
      1 < \frac{L_n}{M} = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
        < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
    \]
  \end{enumerate}
  -/)
  (proof := /--
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
  -/)
  (latexEnv := "lemma")]
theorem Criterion.Ln_div_M_lt (c : Criterion) :
    L c.n / c.M < (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i))⁻¹ := by
  have hprod_q_pos_R : (0 : ℝ) < (∏ i, c.q i) := cast_pos.mpr <| prod_pos fun i _ ↦ (c.hq i).pos
  have hLM_eq : (L c.n : ℝ) / c.M = ((∏ i, c.q i) : ℝ) / (((4 * ∏ i, c.p i) * c.m) : ℕ) := by
    simp only [c.L_eq_prod_q_mul_L', M, cast_mul]
    have hL'_ne : (c.L' : ℝ) ≠ 0 := cast_ne_zero.mpr c.L'_pos.ne'
    field_simp
    congr 1
    exact prod_natCast univ c.q
  have hLM_eq' : (L c.n : ℝ) / c.M = (1 - (c.r : ℝ) / (∏ i, c.q i))⁻¹ := by
    have hprod_q_eq_R : ((∏ i, c.q i) : ℝ) = ((4 * ∏ i, c.p i) * c.m : ℕ) + c.r := by
      exact_mod_cast c.prod_q_eq
    have h4pm_pos : 0 < (4 * ∏ i, c.p i) * c.m := mul_pos
      (mul_pos (by norm_num) <| prod_pos fun i _ ↦ (c.hp i).pos) c.m_pos
    rw [hLM_eq, hprod_q_eq_R]
    have hne : (((4 * ∏ i, c.p i) * c.m : ℕ) : ℝ) ≠ 0 := cast_ne_zero.mpr h4pm_pos.ne'
    have hsum_pos : (0 : ℝ) < ((4 * ∏ i, c.p i) * c.m : ℕ) + c.r := by positivity
    field_simp
    simp_all
  have h1_sub_pos : (0 : ℝ) < 1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i) := by
    rw [sub_pos, div_lt_one hprod_q_pos_R]; exact_mod_cast c.prod_p_le_prod_q
  have hsub_lt : 1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i) <
      1 - (c.r : ℝ) / (∏ i, c.q i) := by gcongr; exact_mod_cast c.r_le
  rw [hLM_eq']
  have hinv := one_div_lt_one_div_of_lt h1_sub_pos hsub_lt
  simp only [one_div] at hinv
  convert hinv using 2

blueprint_comment /--
\subsection{A sufficient condition}

We give a sufficient condition for $\sigma(M) \geq \sigma(L_n)$.
-/

@[blueprint
  "lem:criterion-sufficient"
  (title := "A sufficient inequality")
  (statement := /--
  Suppose
  \[
    \frac{\sigma(M)}{M}
    \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)
    \;\ge\; \frac{\sigma(L_n)}{L_n}.
  \]
  Then \(\sigma(M) \ge \sigma(L_n)\), and so \(L_n\) is not highly abundant.
  -/)
  (proof := /--
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
  -/)
  (proofUses := ["lem:M-basic"])
  (latexEnv := "lemma")]
theorem Criterion.not_highlyAbundant_1 (c : Criterion)
    (h : σnorm c.M * (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) ≥ σnorm (L c.n)) :
    ¬HighlyAbundant (L c.n) := by
  intro hHA
  have hM_pos : (0 : ℝ) < c.M := cast_pos.mpr c.M_pos
  have hLn_pos : (0 : ℝ) < L c.n := cast_pos.mpr c.L_pos
  have hσnorm_Ln_pos : 0 < σnorm (L c.n) := by
    rw [σnorm]; exact div_pos (cast_pos.mpr <| by rw [σ, sigma_pos_iff]; exact c.L_pos) hLn_pos
  have hprod_q_pos : (0 : ℝ) < (∏ i, c.q i) := cast_pos.mpr (prod_pos fun i _ ↦ (c.hq i).pos)
  have h1_sub_pos : (0 : ℝ) < 1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i) := by
    rw [sub_pos, div_lt_one hprod_q_pos]; exact_mod_cast c.prod_p_le_prod_q
  have h1_sub_lt : 1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i) < c.M / L c.n := by
    have hinv_lt := c.Ln_div_M_lt
    rw [lt_inv_comm₀ (div_pos hLn_pos hM_pos) h1_sub_pos, inv_div] at hinv_lt
    exact hinv_lt
  have hσM_gt : (σ c.M : ℝ) > σ (L c.n) := by
    have hσnorm_gt : σnorm c.M > σnorm (L c.n) * (L c.n / c.M) :=
      calc σnorm c.M ≥ σnorm (L c.n) / (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) := by
            rw [ge_iff_le, div_le_iff₀ h1_sub_pos]; exact h
        _ > σnorm (L c.n) / (c.M / L c.n) := by gcongr
        _ = σnorm (L c.n) * (L c.n / c.M) := by rw [div_div_eq_mul_div, mul_div_assoc]
    calc (σ c.M : ℝ) = σnorm c.M * c.M := by field_simp [σnorm]
      _ > σnorm (L c.n) * (L c.n / c.M) * c.M := by nlinarith
      _ = σ (L c.n) := by field_simp [σnorm, c.M_pos.ne']
  exact not_lt.mpr (cast_lt.mp hσM_gt).le (hHA c.M c.M_lt)

blueprint_comment /--
Combining Lemma \ref{lem:criterion-sufficient} with Lemma \ref{lem:sigmaLn}, we see that it suffices to bound \(\sigma(M)/M\) from below in terms of \(\sigma(L')/L'\):
-/

@[blueprint
  "lem:criterion-reduced"
  (title := "Reduction to a lower bound for \\(\\sigma(M)/M\\)")
  (statement := /--
  If
  \begin{equation}\label{eq:sigmaM-lower}
    \frac{\sigma(M)}{M}
    \;\ge\;
    \frac{\sigma(L')}{L'}
    \Biggl( \prod_{i=1}^3 \Bigl(1+\frac{1}{p_i(p_i+1)}\Bigr) \Biggr)
    \Bigl(1 + \frac{3}{8n}\Bigr),
  \end{equation}
  then $L_n$ is not highly abundant.
  -/)
  (proof := /-- Insert \eqref{eq:sigmaM-lower} and \eqref{eq:sigmaLn} into the desired inequality and compare with the assumed bound \eqref{eq:main-ineq}; this is a straightforward rearrangement. -/)
  (proofUses := ["lem:sigmaLn", "lem:criterion-sufficient"])
  (latexEnv := "lemma")]
theorem Criterion.not_highlyAbundant_2 (c : Criterion)
    (h : σnorm c.M ≥ σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) *
    (1 + (3 : ℝ) / (8 * c.n))) : ¬HighlyAbundant (L c.n) := by
  refine c.not_highlyAbundant_1 ?_
  have hL'_pos : 0 < σnorm c.L' := by
    rw [σnorm]; exact div_pos (cast_pos.mpr <| by rw [σ, sigma_pos_iff]; exact c.L'_pos)
      (cast_pos.mpr c.L'_pos)
  have hR_pos : (0 : ℝ) < 1 - 4 * (∏ i, c.p i) / (∏ i, c.q i) := by
    rw [sub_pos, div_lt_one (cast_pos.mpr <| prod_pos fun i _ ↦ (c.hq i).pos)]
    exact_mod_cast c.prod_p_le_prod_q
  have hcrit : (∏ i, (1 + (1 : ℝ) / c.q i)) ≤ (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) *
      (1 + 3 / (8 * c.n)) * (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) := by
    convert c.h_crit using 3; simp only [prod_natCast]
  rw [c.σnorm_ln_eq]
  calc σnorm c.L' * ∏ i, (1 + (1 : ℝ) / c.q i)
    ≤ σnorm c.L' * ((∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) *
        (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i))) :=
          mul_le_mul_of_nonneg_left hcrit hL'_pos.le
  _ = σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) *
    (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) := by ring
  _ ≤ σnorm c.M * (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) :=
    mul_le_mul_of_nonneg_right h hR_pos.le

blueprint_comment /--
\subsection{Conclusion of the criterion}
-/

@[blueprint "lem:sigmaM-lower-final"
  (title := "Lower bound for \\(\\sigma(M)/M\\)")
  (statement := /--
  With notation as above,
  \[
    \frac{\sigma(M)}{M}
    \ge
    \frac{\sigma(L')}{L'}
    \Biggl( \prod_{i=1}^3 \Bigl(1 + \frac{1}{p_i(p_i+1)}\Bigr) \Biggr)
    \Bigl(1 + \frac{3}{8n}\Bigr).
  \]
  -/)
  (proof := /--
    By multiplicativity, we have
  $$
    \frac{\sigma(M)}{M}
    = \frac{\sigma(L')}{L'}
    \prod_p \frac{1+p^{-1}+\dots+p^{-\nu_p(M)}}{1+p^{-1}+\dots+p^{-\nu_p(L')}}.
  $$
  The contribution of $p=p_i$ is
  \[
    \frac{(1+p_i^{-1}+p_i^{-2})}{1+p^{-1}_i}
    = 1 + \frac{1}{p_i(p_i+1)}.
  \]
  The contribution of $p=2$ is
  \[
    \frac{1+2^{-1}+\dots+2^{-k-2}}{1+2^{-1}+\dots+2^{-k}},
  \]
  where \(k\) is the largest integer such that \(2^k \le n\).
  A direct calculation yields
  \[
    \frac{(1+2^{-1}+\dots+2^{-k-2})}{1+2^{-1}+\dots+2^{-k}}
    = \frac{2^{k+3}-1}{2^{k+3}-4}
    = 1 + \frac{3}{2^{k+3}-4},
  \]
  Finally, since \(2^k \le n < 2^{k+1}\), we have \(2^{k+3} < 8n\), so
  \[
    \frac{3}{2^{k+3}-4} \ge \frac{3}{8n},
  \]
  So the contribution from the prime \(2\) is at least \(1 + 3/(8n)\).

  Finally, the contribution of all other primes is at least \(1\).
  -/)
  (latexEnv := "lemma")]
theorem Criterion.σnorm_M_ge_σnorm_L'_mul (c : Criterion) :
    σnorm c.M ≥ σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) := by
  sorry





@[blueprint
  "thm:criterion"
  (statement := /--
    Let $n \geq 1$.
  Suppose that primes \(p_1,p_2,p_3,q_1,q_2,q_3\) satisfy
  \[
    \sqrt{n} < p_1 < p_2 < p_3 < q_1 < q_2 < q_3 < n
  \]
  and the key criterion \eqref{eq:main-ineq}.
  Then \(L_n\) is not highly abundant.
  -/)
  (proof := /--
  By Lemma~\ref{lem:sigmaM-lower-final}, the condition \eqref{eq:sigmaM-lower} holds.  By Lemma~\ref{lem:criterion-reduced} this implies
  \[
    \frac{\sigma(M)}{M}
    \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)
    \ge \frac{\sigma(L_n)}{L_n}.
  \]
  Applying Lemma~\ref{lem:criterion-sufficient}, we obtain \(\sigma(M) \ge \sigma(L_n)\) with \(M < L_n\), so \(L_n\) cannot be highly abundant.
  -/)]
theorem Criterion.not_highlyAbundant (c : Criterion) : ¬HighlyAbundant (L c.n) :=
  c.not_highlyAbundant_2 c.σnorm_M_ge_σnorm_L'_mul

blueprint_comment /--
\begin{remark}
Analogous arguments allow other pairs \((c,\alpha)\) in place of \((4,3/8)\),
such as \((2,1/4)\), \((6,17/36)\), \((30,0.632\dots)\); or even \((1,0)\) provided more primes are
used on the \(p\)-side than the \(q\)-side to restore an asymptotic advantage.
\end{remark}
-/

abbrev X₀ := 89693

blueprint_comment /--
\subsection{Choice of six primes \(p_i,q_i\) for large \(n\)}
-/

@[blueprint
  "lem:choose-pi"
  (title := "Choice of medium primes \\(p_i\\)")
  (statement := /--
  Let \(n \ge X_0^2\). Set \(x := \sqrt{n}\). Then there exist primes \(p_1,p_2,p_3\) with
  \[
    p_i \le x \Bigl(1 + \frac{1}{\log^3 x}\Bigr)^i
  \]
  and \(p_1 < p_2 < p_3\).
  Moreover, \(\sqrt{n} < p_1\)
  -/)
  (proof := /-- Apply Theorem~\ref{thm:Dusart} successively with
  \(x, x(1+1/\log^3 x), x(1+1/\log^3 x)^2\), keeping track of the resulting primes and bounds.
  For \(n\) large and \(x = \sqrt{n}\), we have \(\sqrt{n} < p_1\) as soon as the first interval
  lies strictly above \(\sqrt{n}\); this can be enforced by taking \(n\) large enough. -/)
  (proofUses := ["thm:Dusart"])
  (latexEnv := "lemma")]
theorem exists_p_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i, p i ≤ √(n : ℝ) * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (i + 1 : ℝ)) ∧ √(n : ℝ) < p 0 := by
  let x := √(n : ℝ)
  have hx_ge : x ≥ X₀ := by simpa using sqrt_le_sqrt (by exact_mod_cast hn : (X₀ : ℝ) ^ 2 ≤ n)
  have hx_pos : 0 < x := (by grind : (0 : ℝ) < X₀).trans_le hx_ge
  have hlog_pos : 0 < log x := log_pos ((by grind : (1 : ℝ) < X₀).trans_le hx_ge)
  set ε := 1 / (log x) ^ 3 with hε_def
  have upper {y : ℝ} (hy : 0 < y) (hlog_ge : log y ≥ log x) {p : ℕ}
      (hp : (p : ℝ) ≤ y + y / (log y) ^ (3 : ℝ)) : (p : ℝ) ≤ y * (1 + ε) := by
    have h : y / (log y) ^ (3 : ℝ) ≤ y / (log x) ^ (3 : ℝ) :=
      div_le_div_of_nonneg_left hy.le (rpow_pos_of_pos hlog_pos 3)
        (rpow_le_rpow hlog_pos.le hlog_ge (by grind))
    calc (p : ℝ) ≤ y + y / (log y) ^ (3 : ℝ) := hp
      _ ≤ y + y / (log x) ^ (3 : ℝ) := add_le_add_right h y
      _ = y * (1 + ε) := by simp only [hε_def, ← rpow_natCast]; grind
  have hε_pos : 0 < ε := by positivity
  have hx1_ge : x * (1 + ε) ≥ X₀ := hx_ge.trans (le_mul_of_one_le_right hx_pos.le (by grind))
  have hx2_ge : x * (1 + ε) ^ 2 ≥ X₀ := hx_ge.trans (le_mul_of_one_le_right hx_pos.le
    (by nlinarith [sq_nonneg ε]))
  obtain ⟨p₀, hp₀_prime, hp₀_lb, hp₀_ub⟩ := Dusart.proposition_5_4 x hx_ge
  obtain ⟨p₁, hp₁_prime, hp₁_lb, hp₁_ub⟩ := Dusart.proposition_5_4 _ hx1_ge
  obtain ⟨p₂, hp₂_prime, hp₂_lb, hp₂_ub⟩ := Dusart.proposition_5_4 _ hx2_ge
  have hp₀_ub' : (p₀ : ℝ) ≤ x * (1 + ε) := upper hx_pos le_rfl hp₀_ub
  have hp₁_ub' : (p₁ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    linarith [sq (1 + ε), upper (by grind) (log_le_log hx_pos (by grind)) hp₁_ub]
  have hp₂_ub' : (p₂ : ℝ) ≤ x * (1 + ε) ^ 3 := by
    linarith [pow_succ (1 + ε) 2, upper (by grind) (log_le_log hx_pos (by grind)) hp₂_ub]
  refine ⟨![p₀, p₁, p₂], fun i ↦ by fin_cases i <;> assumption, Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
    fin_cases i
    · exact cast_lt.mp (hp₀_ub'.trans_lt hp₁_lb)
    · exact cast_lt.mp (hp₁_ub'.trans_lt hp₂_lb), fun i ↦ ?_, hp₀_lb⟩
  fin_cases i <;> norm_num
  · convert hp₀_ub' using 2
  · convert hp₁_ub' using 2
  · convert hp₂_ub' using 2



@[blueprint "lem:choose-qi"
  (title := "Choice of large primes \\(q_i\\)")
  (statement := /--
  Let \(n \ge X_0^2\). Then there exist primes \(q_1 < q_2 < q_3\) with
  \[
    q_{4-i} \ge n \Bigl(1 + \frac{1}{\log^3 \sqrt{n}}\Bigr)^{-i}
  \]
  for \(i = 1,2,3\), and \(q_1 < q_2 < q_3 < n\).
  -/)
  (proof := /-- Apply Theorem~\ref{thm:Dusart} with suitable values of \(x\) slightly below \(n\),
  e.g.\ \(x = n(1+1/\log^3\sqrt{n})^{-i}\), again keeping track of the intervals.  For \(n\) large
  enough, these intervals lie in \((\sqrt{n},n)\) and contain primes \(q_i\) with the desired
  ordering. -/)
  (proofUses := ["thm:Dusart"])
  (latexEnv := "lemma")]
theorem exists_q_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3, n * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (-((3 : ℝ) - (i : ℕ))) ≤ q i) ∧ q 2 < n := by
  sorry

blueprint_comment /--
\subsection{Bounding the factors in \eqref{eq:main-ineq}}
-/

@[blueprint
  "lem:qi-product"
  (title := "Bounds for the \\(q_i\\)-product")
  (statement := /--
  With \(p_i,q_i\) as in Lemmas~\ref{lem:choose-pi} and \ref{lem:choose-qi}, we have
  \begin{equation}\label{eq:qi-upper}
    \prod_{i=1}^3 \Bigl(1 + \frac{1}{q_i}\Bigr)
    \le
    \prod_{i=1}^3 \Bigl(1 + \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^i}{n} \Bigr).
  \end{equation}
  -/)
  (proof := /--
  By Lemma~\ref{lem:choose-qi}, each \(q_i\) is at least
  \[
    n\Bigl(1 + \frac{1}{\log^3 \sqrt{n}}\Bigr)^{-j}
  \]
  for suitable indices \(j\), so \(1/q_i\) is bounded above by
  \[
    \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^i}{n}
  \]
  after reindexing. Multiplying the three inequalities gives \eqref{eq:qi-upper}.
  -/)
  (proofUses := ["lem:choose-qi"])
  (latexEnv := "lemma")]
theorem prod_q_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) / (exists_q_primes hn).choose i) ≤
      ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((i : ℕ) + 1 : ℝ) / n) := by
  rw [show ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((i : ℕ) + 1 : ℝ) / n) = ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n) by
    rw [Fin.prod_univ_three, Fin.prod_univ_three]
    conv =>
      enter [1, 1, 1, 2, 1, 2]
      equals 1 => simp
    conv =>
      enter [1, 1, 2, 2, 1, 2]
      equals 2 => norm_cast
    conv =>
      enter [2, 1, 1, 2, 1, 2]
      equals 3 => norm_cast
    conv =>
      enter [1, 2, 2, 1, 2]
      equals 3 => norm_cast
    conv =>
      enter [2, 2, 2, 1, 2]
      equals 1 => norm_cast
    conv =>
      enter [2, 1, 2, 2, 1, 2]
      equals 2 => norm_cast
    ring]
  apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
  intro i _
  suffices h : (1 : ℝ) / (exists_q_primes hn).choose i ≤ (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n from (by linarith)
  have := (exists_q_primes hn).choose_spec.2.2.1 i
  rw [show (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n = 1 / (n / (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) ) by field_simp]
  have nbd : (10 : ℝ) < n := by norm_cast; linarith
  have f0 : (0 : ℝ) < (log √(n : ℝ)) ^ 3 := by
    apply pow_pos
    apply Real.log_pos
    rw [show (1 : ℝ) = √1 by norm_num]
    apply Real.sqrt_lt_sqrt <;> linarith
  have f : (0 : ℝ) < (1 + 1 / (log √(n : ℝ)) ^ 3) := by positivity
  have f' : (0 : ℝ) < (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) := by positivity
  apply one_div_le_one_div_of_le
  · positivity
  · convert this using 1
    field_simp
    rw [← rpow_add f]
    simp

@[blueprint
  "lem:pi-product"
  (title := "Bounds for the \\(p_i\\)-product")
  (statement := /--
  With \(p_i\) as in Lemma~\ref{lem:choose-pi}, we have for large \(n\)
  \begin{equation}\label{eq:pi-lower}
    \prod_{i=1}^3 \Bigl(1 + \frac{1}{p_i(p_i+1)}\Bigr)
    \ge
    \prod_{i=1}^3
    \Bigl(
      1 + \frac{1}{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{2i} (n + \sqrt{n})}
    \Bigr).
  \end{equation}
  -/)
  (proof := /--
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
  -/)
  (latexEnv := "lemma")]
theorem prod_p_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) / ((exists_p_primes hn).choose i * ((exists_p_primes hn).choose i + 1))) ≥
      ∏ i : Fin 3, (1 + 1 / ((1 + 1 / (log √(n : ℝ)) ^ 3) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))) := by
  sorry

@[blueprint
  "lem:pq-ratio"
  (title := "Lower bound for the product ratio \\(p_i/q_i\\)")
  (statement := /--
  With \(p_i,q_i\) as in Lemmas~\ref{lem:choose-pi} and \ref{lem:choose-qi}, we have
  \begin{equation}\label{eq:pq-ratio}
    1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}
    \ge
    1 - \frac{4 \bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{12}}{n^{3/2}}.
  \end{equation}
  -/)
  (proof := /--
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
    \frac{n^{3/2} \bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{6}}{n^3
    \bigl(1 + \frac{1}{\log^3\sqrt{n}}\bigr)^{-6}}
    = \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{12}}{n^{3/2}}.
  \]
  This implies \eqref{eq:pq-ratio}.
  -/)
  (latexEnv := "lemma")]
theorem pq_ratio_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 - (4 : ℝ) * ∏ i, (exists_p_primes hn).choose i / ∏ i, (exists_q_primes hn).choose i ≥
      1 - 4 * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ 12 / n ^ (3 / 2) := by
  sorry

blueprint_comment /--
\subsection{Reduction to a small epsilon-inequality}
-/

@[blueprint
  "lem:eps-bounds"
  (title := "Uniform bounds for large \\(n\\)")
  (statement := /--
  For all \(n \ge X_0^2 = 89693^2\) we have
  \[
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{89693}\cdot\frac{1}{n}.
  \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")]
theorem inv_cube_log_sqrt_le (n : ℕ) (hn : n ≥ X₀ ^ 2) :
    1 / (log √(n : ℝ)) ^ 3 ≤ 0.000675 := by
  sorry

@[blueprint
  "lem:eps-bounds"
  (title := "Uniform bounds for large \\(n\\)")
  (statement := /--
  For all \(n \ge X_0^2 = 89693^2\) we have
  \[
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{89693}\cdot\frac{1}{n}.
  \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")]
theorem inv_n_pow_3_div_2_le (n : ℕ) (hn : n ≥ X₀ ^ 2) :
    1 / ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (89693 : ℝ)) * (1 / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := cast_pos.mpr (lt_of_lt_of_le (by grind) hn)
  rw [one_div_mul_one_div, one_div_le_one_div (rpow_pos_of_pos hn_pos _)
    (mul_pos (by norm_num) hn_pos), show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      rpow_add hn_pos, rpow_one, mul_comm, ← sqrt_eq_rpow]
  refine mul_le_mul_of_nonneg_left ?_ hn_pos.le
  have := Real.sqrt_le_sqrt (cast_le.mpr hn)
  simp_all

@[blueprint
  "lem:poly-ineq"
  (title := "Polynomial approximation of the inequality")
  (statement := /--
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
  -/)
  (proof := /--
  Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using
  the bounds in Lemma~\ref{lem:eps-bounds}, and bound the tails by simple inequalities such as
  \[
    (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
  \]
  for small \(\varepsilon\).
  All coefficients can be bounded numerically in a rigorous way; this step is a finite computation
  that can be checked mechanically.
  -/)
  (latexEnv := "lemma")]
theorem prod_epsilon_le (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith

@[blueprint
  "lem:poly-ineq"
  (title := "Polynomial approximation of the inequality")
  (statement := /--
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
    1 + 3.36687\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using
  the bounds in Lemma~\ref{lem:eps-bounds}, and bound the tails by simple inequalities such as
  \[
    (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
  \]
  for small \(\varepsilon\).
  All coefficients can be bounded numerically in a rigorous way; this step is a finite computation
  that can be checked mechanically.
  -/)
  (latexEnv := "lemma")]
theorem prod_epsilon_ge (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
    (∏ i : Fin 3, (1 + ε / (1.000675 : ℝ) ^ (2 * ((i : ℕ) + 1 : ℝ)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * (1.000675 : ℝ) ^ 12 / 89693 * ε) ≥
      1 + 3.36687 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4]

@[blueprint
  "lem:final-comparison"
  (title := "Final polynomial comparison")
  (statement := /--
  For \(0 \le \varepsilon \le 1/89693^2\), we have
  \[
    1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 1 + 3.36687\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  This is equivalent to
  \[
    3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 3.36687\varepsilon - 0.01\varepsilon^2,
  \]
  or
  \[
    0 \le (3.36687 - 3.01)\varepsilon - (3.01+0.01)\varepsilon^2 - 1.01\varepsilon^3.
  \]
  Factor out \(\varepsilon\) and use that \(0<\varepsilon \le 1/89693^2\) to check that the
  resulting quadratic in \(\varepsilon\) is nonnegative on this interval.  Again, this is a
  finite computation that can be verified mechanically.
  -/)
  (latexEnv := "lemma")]
theorem final_comparison (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36687 * ε - 0.01 * ε ^ 2 := by
  nlinarith

@[blueprint
  "prop:ineq-holds-large-n"
  (title := "Verification of \\eqref{eq:main-ineq} for large \\(n\\)")
  (statement := /-- For every integer \(n \ge X_0^2 = 89693^2 \approx 8.04\times 10^9\), the
  primes \(p_i,q_i\) constructed in Lemmas~\ref{lem:choose-pi} and \ref{lem:choose-qi} satisfy the
  inequality \eqref{eq:main-ineq}. -/)
  (proof := /-- Combine Lemma~\ref{lem:qi-product}, Lemma~\ref{lem:pi-product}, and
  Lemma~\ref{lem:pq-ratio}.  Then apply Lemma~\ref{lem:eps-bounds} and set \(\varepsilon = 1/n\).
  The products are bounded by the expressions in Lemma~\ref{lem:poly-ineq}, and the inequality in
  Lemma~\ref{lem:final-comparison} then ensures that \eqref{eq:main-ineq} holds. -/)
  (proofUses := ["lem:eps-bounds", "lem:qi-product", "lem:final-comparison", "lem:poly-ineq",
  "lem:pq-ratio", "lem:pi-product"])
  (latexEnv := "proposition")]
noncomputable def Criterion.mk' {n : ℕ} (hn : n ≥ X₀ ^ 2) : Criterion where
  n := n
  p := (exists_p_primes hn).choose
  q := (exists_q_primes hn).choose
  hn := le_trans (by decide : 1 ≤ 89693 ^ 2) hn
  hp := (exists_p_primes hn).choose_spec.1
  hp_mono := (exists_p_primes hn).choose_spec.2.1
  hq := (exists_q_primes hn).choose_spec.1
  hq_mono := (exists_q_primes hn).choose_spec.2.1
  h_ord_1 := (exists_p_primes hn).choose_spec.2.2.2
  h_ord_2 := by
    have hn_pos : (0 : ℝ) < n := by positivity
    have hsqrt_ge : √(n : ℝ) ≥ 89693 := by
      simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ 89693 ^ 2)
    have hε_pos : 0 < 1 + 1 / (log √(n : ℝ)) ^ 3 := by
      have : log √(n : ℝ) > 0 := log_pos (by grind)
      positivity
    have hp' : ((exists_p_primes hn).choose 2 : ℝ) ≤ √n * (1 + 1 / (log √n) ^ 3) ^ 3 := by
      convert (exists_p_primes hn).choose_spec.2.2.1 2 using 2; norm_cast
    have hq' : n * (1 + 1 / (log √n) ^ 3) ^ (-3:ℝ) ≤ (exists_q_primes hn).choose 0 := by
      convert (exists_q_primes hn).choose_spec.2.2.1 0 using 2
      norm_num
    have hmid : √n * (1 + 1 / (log √n) ^ 3) ^ 3 < n * (1 + 1 / (log √n) ^ 3) ^ (-3 : ℝ) := by
      norm_cast
      norm_num [rpow_neg_one] at *
      rw [← div_eq_mul_inv, lt_div_iff₀ <| pow_pos hε_pos 3]
      have hlog : log √n > 11 := by
        rw [gt_iff_lt, lt_log_iff_exp_lt (by positivity)]
        calc exp 11 = exp 1 ^ 11 := by norm_num [← exp_nat_mul]
          _ < 89693 := by
            have := exp_one_lt_d9.le
            calc exp 1 ^ 11 ≤ 2.7182818286 ^ 11 := by gcongr
              _ < 89693 := by norm_num
          _ ≤ √n := hsqrt_ge
      have : (1 + ((log √n) ^ 3)⁻¹) ^ 6 < 2 :=
        calc (1 + ((log √n) ^ 3)⁻¹) ^ 6 < (1 + (11 ^ 3 : ℝ)⁻¹) ^ 6 := by gcongr
          _ ≤ 2 := by norm_num
      nlinarith [mul_self_sqrt (Nat.cast_nonneg n)]
    exact_mod_cast hp'.trans_lt <| hmid.trans_le hq'
  h_ord_3 := (exists_q_primes hn).choose_spec.2.2.2
  h_crit := sorry

blueprint_comment /--
\subsection{Conclusion for large \(n\)}
-/

@[blueprint
  "thm:large-n-final"
  (title := "Non-highly abundant for large \\(n\\)")
  (statement := /-- For every integer \(n \ge 89693^2\), the integer \(L_n\) is not highly
  abundant. -/)
  (proof := /-- By Proposition~\ref{prop:ineq-holds-large-n}, there exist primes
  \(p_1,p_2,p_3,q_1,q_2,q_3\) satisfying the hypotheses of Theorem~\ref{thm:criterion}.
  Hence \(L_n\) is not highly abundant. -/)
  (proofUses := ["prop:ineq-holds-large-n", "thm:criterion"])]
theorem L_not_HA_of_ge (n : ℕ) (hn : n ≥ 89693 ^ 2) : ¬HighlyAbundant (L n) :=
  (Criterion.mk' hn).not_highlyAbundant

end Lcm
