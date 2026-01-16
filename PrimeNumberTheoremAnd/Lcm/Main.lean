import Architect
import PrimeNumberTheoremAnd.Lcm.Cert

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

blueprint_comment /--
Informally, a highly abundant number has an unusually large sum of divisors.
-/

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
Clearly $L_n$ has a lot of divisors, and numerical experiments for small $n$ suggests that $L_n$
is often highly abundant.  This leads to the following question:
-/


blueprint_comment /--
\begin{quote}
\textbf{Original MathOverflow question.}
Is it true that every value in the sequence \(L_n = \mathrm{lcm}(1,2,\dots,n)\) is highly abundant?
Equivalently,
\[
  \{L_n : n \ge 1\} \subseteq HA?
\]
\end{quote}

Somewhat surprisingly, the answer is \emph{no}: not every \(L_n\) is highly abundant.

It has previously been verified in Lean that \(L_n\) is highly aboundant for $n \leq 70$,
$81 \leq n \leq 96$, $125 \leq n \leq 148$, $169 \leq n \leq 172$, and not highly abondant for all
other $n ≤ 10^{10}$.  The arguments here establish the non-highly-abundance of \(L_n\) for all
$n \geq 89683^2$ sufficiently large \(n\), thus completing the determination in Lean of all $n$ for
which \(L_n\) is highly abundant. This argument was taken from
\href{https://mathoverflow.net/questions/501066/is-the-least-common-multiple-sequence-textlcm1-2-dots-n-a-subset-of-t?noredirect=1\#comment1313839_501066}{this
MathOverflow answer}.

\subsection{A general criterion using three medium primes and three large primes}
-/

blueprint_comment /--
The key step in the proof is to show that, if one can find six primes $p_1,p_2,p_3,q_1,q_2,q_3$
obeying a certain inequality, then one can find a competitor $M < L_n$ to $L_n$ with
$\sigma(M) > \sigma(L_n)$, which will demonstrate that $L_n$ is not highly abundant.
More precisely:
-/

@[blueprint
  "lcm-criterion"
  (statement := /--
  In the next few subsections we assume that $n \geq 1$ and that \(p_1,p_2,p_3,q_1,q_2,q_3\) are
  primes satisfiying
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

  NOTE: In the Lean formalization of this argument, we index the primes from 0 to 2 rather than
  from 1 to 3.
  -/)]
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
  have hBC_pos : 0 < (∏ i, (1 + (1 : ℝ) / (c.p i * (c.p i + 1)))) * (1 + 3 / (8 * c.n)) := by
    positivity
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
  (proof := /--
  Since \(q_i < n\), the prime \(q_i\) divides \(L_n\) exactly once (as \(q_i^2 > n\)).
  Hence we may write \(L_n = q_1 q_2 q_3 L'\) where \(L'\) is the quotient obtained by removing
  these prime factors.  By construction, \(q_i \nmid L'\) for each \(i\).
  -/)
  (latexEnv := "lemma")]
theorem Criterion.ln_eq (c : Criterion) : L c.n = c.q 0 * c.q 1 * c.q 2 * c.L' := by
  rw [L', ← Fin.prod_univ_three, Nat.mul_div_cancel' <| Fintype.prod_dvd_of_isRelPrime ?_ ?_]
  · refine fun i j h ↦ Nat.coprime_iff_isRelPrime.mp ?_
    exact Nat.coprime_primes (c.hq i) (c.hq j) |>.mpr <| c.hq_mono.injective.ne h
  refine fun i ↦
    Finset.dvd_lcm <| Finset.mem_Icc.mpr ⟨c.hq i |>.one_le, le_trans ?_ c.h_ord_3.le⟩
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
  (proof := /--
  Since \(q_i < n\), the prime \(q_i\) divides \(L_n\) exactly once (as \(q_i^2 > n\)).
  Hence we may write \(L_n = q_1 q_2 q_3 L'\) where \(L'\) is the quotient obtained by removing
  these prime factors.  By construction, \(q_i \nmid L'\) for each \(i\).
  -/)
  (latexEnv := "lemma")]
theorem Criterion.q_not_dvd_L' (c : Criterion) : ∀ i, ¬(c.q i ∣ c.L') := by
  intro i hqi
  have hn_lt_q_sq := Real.lt_sq_of_sqrt_lt <| c.h_ord_1.trans_le <| cast_le.mpr <|
    show c.p 0 ≤ c.q i by
      grw [c.hp_mono.monotone <| Fin.zero_le 2, c.h_ord_2, c.hq_mono.monotone <| Fin.zero_le i]
  norm_cast at hn_lt_q_sq
  suffices ¬(c.q i) ^ 2 ∣ L c.n from this <| Nat.pow_two _ ▸ by
    refine mul_dvd_mul_right (Finset.dvd_prod_of_mem c.q <| Finset.mem_univ i) _ |>.trans ?_
    exact Fin.prod_univ_three c.q ▸ c.ln_eq ▸ mul_dvd_mul_left _ hqi

  set p : ℕ := c.q i
  have hp : Nat.Prime p := c.hq i

  -- 1) prime power divides binary lcm iff divides one side
  have pow_dvd_lcm_iff (a b k : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      p ^ k ∣ Nat.lcm a b ↔ (p ^ k ∣ a ∨ p ^ k ∣ b) := by
    refine ⟨?_, by grind [dvd_trans, Nat.dvd_lcm_left, Nat.dvd_lcm_right]⟩
    grind [Prime.pow_dvd_iff_le_factorization, lcm_ne_zero, factorization_lcm, Finsupp.sup_apply]

  -- 2) prime power divides finset-lcm -> appears in some member
  have exists_mem_of_pow_dvd_finset_lcm (s : Finset ℕ) (hs_nz : ∀ x ∈ s, x ≠ 0) (k)
      (hk : 0 < k) (h : p ^ k ∣ s.lcm _root_.id) : ∃ m ∈ s, p ^ k ∣ m := by
    induction s using Finset.induction with
    | empty =>
      have := one_lt_pow hk.ne' hp.one_lt |>.trans_le <| le_of_dvd zero_lt_one h
      contradiction
    | insert a s ha ih =>
      have ha0 := hs_nz _ <| mem_insert_self a s
      have hs_nz' := (hs_nz · <| mem_insert_of_mem ·)
      have hs0 := lcm_ne_zero_iff.mpr hs_nz'
      have := (pow_dvd_lcm_iff _ _ k ha0 hs0).1 <| by simpa using h
      rcases this with hpa | hps
      · exact ⟨a, mem_insert_self a s, hpa⟩
      · have ⟨m, hmS, hpm⟩ := ih hs_nz' hps
        exact ⟨m, mem_insert_of_mem hmS, hpm⟩

  intro hq2
  have ⟨m, hmIcc, hpm⟩ := exists_mem_of_pow_dvd_finset_lcm _ (by grind) 2 zero_lt_two hq2
  refine not_lt_of_ge ?_ hn_lt_q_sq
  refine le_trans (le_of_dvd ?_ hpm) (Finset.mem_Icc.mp hmIcc).2
  exact succ_le_iff.mp (Finset.mem_Icc.mp hmIcc).1

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
  "lcm-M-def"
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
  have hprod_q_pos_R : (0 : ℝ) < (∏ i, c.q i) :=
    cast_pos.mpr <| prod_pos fun i _ ↦ (c.hq i).pos
  have hLM_eq :
      (L c.n : ℝ) / c.M = ((∏ i, c.q i) : ℝ) / (((4 * ∏ i, c.p i) * c.m) : ℕ) := by
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
Combining Lemma \ref{lem:criterion-sufficient} with Lemma \ref{lem:sigmaLn}, we see that it
suffices to bound \(\sigma(M)/M\) from below in terms of \(\sigma(L')/L'\):
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
  (proof := /--
  Insert \eqref{eq:sigmaM-lower} and \eqref{eq:sigmaLn} into the desired inequality and compare
  with the assumed bound \eqref{eq:main-ineq}; this is a straightforward rearrangement.
  -/)
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
    σnorm c.M ≥
      σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) := by
  sorry



blueprint_comment /--
We have thus completed the key step of demonstrating a sufficient criterion to establish that
$L_n$ is not highly abundant:
-/

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
  By Lemma~\ref{lem:sigmaM-lower-final}, the condition \eqref{eq:sigmaM-lower} holds.
  By Lemma~\ref{lem:criterion-reduced} this implies
  \[
    \frac{\sigma(M)}{M}
    \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)
    \ge \frac{\sigma(L_n)}{L_n}.
  \]
  Applying Lemma~\ref{lem:criterion-sufficient}, we obtain \(\sigma(M) \ge \sigma(L_n)\) with
  \(M < L_n\), so \(L_n\) cannot be highly abundant.
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

blueprint_comment /--
\subsection{Choice of six primes \(p_i,q_i\) for large \(n\)}
-/

blueprint_comment /--
To finish the proof we need to locate six primes $p_1,p_2,p_3,q_1,q_2,q_3$ obeying the required
inequality.  Here we will rely on the prime number theorem of Dusart \cite{Dusart2018}.
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
      (∀ i, p i ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0 := by
  -- define the “base point”
  let x : ℝ := √(n : ℝ)
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [x] using sqrt_ge_X₀ (n := n) hn
  -- define ε once (this is where `hε` comes from if you use `set`)
  let ε : ℝ := gap.δ x

  -- (1) first prime at x
  obtain ⟨p₀, hp₀_prime, hp₀_lb, hp₀_ub⟩ :=
    gap.prime_in_Icc (x := x) hxX
  have hp₀_ub' : (p₀ : ℝ) ≤ x * (1 + ε) := by
    simpa [ε] using hp₀_ub

  -- (2) second prime at x*(1+ε)
  have hx1X : (X₀ : ℝ) ≤ x * (1 + ε) := by
    -- Cert lemma C4, rewritten to use `x`/`ε`
    -- (since x = √n and ε = δ x)
    simpa [x, ε] using step1_ge_X₀ (n := n) hn

  obtain ⟨p₁, hp₁_prime, hp₁_lb, hp₁_ub⟩ :=
    gap.prime_in_Icc (x := x * (1 + ε)) hx1X

  have hp₁_ub' : (p₁ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    -- provider gives `p₁ ≤ (x*(1+ε)) * (1 + δ(x*(1+ε)))`
    -- Cert lemma C6 turns that into `≤ x*(1+ε)^2`
    refine le_trans (by simpa [ε] using hp₁_ub) ?_
    simpa [x, ε] using step1_upper (n := n) hn

  -- (3) third prime at x*(1+ε)^2
  have hx2X : (X₀ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    simpa [x, ε] using step2_ge_X₀ (n := n) hn

  obtain ⟨p₂, hp₂_prime, hp₂_lb, hp₂_ub⟩ :=
    gap.prime_in_Icc (x := x * (1 + ε) ^ 2) hx2X

  have hp₂_ub' : (p₂ : ℝ) ≤ x * (1 + ε) ^ 3 := by
    refine le_trans (by simpa [ε] using hp₂_ub) ?_
    simpa [x, ε] using step2_upper (n := n) hn

  -- package the primes
  refine ⟨![p₀, p₁, p₂], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · -- StrictMono via "prev upper < next lower"
    refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i
    fin_cases i
    · -- p0 < p1
      exact cast_lt.mp (hp₀_ub'.trans_lt hp₁_lb)
    · -- p1 < p2
      exact cast_lt.mp (hp₁_ub'.trans_lt hp₂_lb)
  · -- upper bounds by cases
    intro i
    fin_cases i <;> norm_num
    · -- i = 0 : exponent is 1
      simpa [x, ε] using hp₀_ub'
    · -- i = 1 : exponent is 2
      simpa [x, ε] using hp₁_ub'
    · -- i = 2 : exponent is 3
      simpa [x, ε] using hp₂_ub'
  · -- √n < p0
    simpa [x] using hp₀_lb





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
      (∀ i : Fin 3, n * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (-((3 : ℝ) - (i : ℕ))) ≤ q i) ∧
      q 2 < n := by
  let x := √(n : ℝ)
  have hx₀_pos : (0 : ℝ) < X₀ := by
    unfold X₀; norm_num
  have hx_pos : 0 < x := hx₀_pos.trans_le (hsqrt_ge hn)
  have hlog_pos : 0 < log x := by positivity [hlog hn]
  set ε := 1 / (log x) ^ 3 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h1ε_pos : 0 < 1 + ε := by linarith
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℝ) < (X₀ : ℝ) ^ (2:ℕ) := by
      exact pow_pos hx₀_pos 2
    -- cast hn : n ≥ X₀^2 to reals and conclude
    have hn' : (X₀ : ℝ) ^ (2:ℕ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact this.trans_le hn'
  have hn_eq_x2 : (n : ℝ) = x ^ 2 := (sq_sqrt hn_pos.le).symm
  -- Show that ε is small (ε ≤ 1/11.4³)
  have hε_small : ε ≤ 1 / 11.4 ^ 3 := by
    simp only [hε_def]
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    · apply pow_pos; linarith [log_X₀_gt]
    · apply pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 11.4) (hlog hn)
  have h1ε3_pos : 0 < (1 + ε) ^ 3 := by positivity
  have h1ε2_pos : 0 < (1 + ε) ^ 2 := by positivity
  have h1ε3_le_2 : (1 + ε) ^ 3 ≤ 2 := by
    have h1 : (1 + ε) ^ 3 ≤ (1 + 1 / 11.4 ^ 3) ^ 3 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    calc (1 + ε) ^ 3 ≤ (1 + 1 / 11.4 ^ 3) ^ 3 := h1
      _ ≤ 2 := by norm_num
  -- Define y_i = n / (1 + ε)^(3-i), and show y_i ≥ X₀
  have hy₀_ge : n / (1 + ε) ^ 3 ≥ X₀ := by
    calc n / (1 + ε) ^ 3 = x ^ 2 / (1 + ε) ^ 3 := by rw [hn_eq_x2]
      _ ≥ x ^ 2 / 2 := div_le_div_of_nonneg_left (sq_nonneg x) (by grind) h1ε3_le_2
      _ ≥ X₀ ^ 2 / 2 := by
        apply div_le_div_of_nonneg_right (sq_le_sq' (by linarith) (hsqrt_ge hn))
        norm_num
      _ ≥ X₀ := by norm_num
  have h1ε2_le_1ε3 : (1 + ε) ^ 2 ≤ (1 + ε) ^ 3 := by nlinarith [sq_nonneg ε]
  have h1ε_le_1ε2 : 1 + ε ≤ (1 + ε) ^ 2 := by nlinarith [sq_nonneg ε]
  have hy₁_ge : n / (1 + ε) ^ 2 ≥ X₀ := le_trans hy₀_ge
    (div_le_div_of_nonneg_left hn_pos.le h1ε2_pos h1ε2_le_1ε3)
  have hy₂_ge : n / (1 + ε) ≥ X₀ := le_trans hy₁_ge
    (div_le_div_of_nonneg_left hn_pos.le h1ε_pos h1ε_le_1ε2)
  -- Apply Dusart to get primes
  obtain ⟨q₀, hq₀_prime, hq₀_lb, hq₀_ub⟩ :=
    proposition_5_4 (n / (1 + ε) ^ 3) hy₀_ge
  obtain ⟨q₁, hq₁_prime, hq₁_lb, hq₁_ub⟩ :=
    proposition_5_4 (n / (1 + ε) ^ 2) hy₁_ge
  obtain ⟨q₂, hq₂_prime, hq₂_lb, hq₂_ub⟩ :=
    proposition_5_4 (n / (1 + ε)) hy₂_ge
  -- Show y_i ≥ x (needed for upper bound helper)
  have hx₀_ge_2 : (2 : ℝ) ≤ X₀ := by
    unfold X₀; norm_num
  have hx_ge_2 : x ≥ 2 := by linarith [hsqrt_ge hn, hx₀_ge_2]
  have hy₀_ge_x : n / (1 + ε) ^ 3 ≥ x := by
    calc n / (1 + ε) ^ 3 = x ^ 2 / (1 + ε) ^ 3 := by rw [hn_eq_x2]
      _ ≥ x ^ 2 / 2 := div_le_div_of_nonneg_left (sq_nonneg x) (by grind) h1ε3_le_2
      _ ≥ x := by rw [ge_iff_le, le_div_iff₀' (by norm_num : (0 : ℝ) < 2)]; nlinarith
  have hy₁_ge_x : n / (1 + ε) ^ 2 ≥ x := le_trans hy₀_ge_x
    (div_le_div_of_nonneg_left hn_pos.le h1ε2_pos h1ε2_le_1ε3)
  have hy₂_ge_x : n / (1 + ε) ≥ x := le_trans hy₁_ge_x
    (div_le_div_of_nonneg_left hn_pos.le h1ε_pos h1ε_le_1ε2)
  -- Upper bound helper: show q_i upper bound implies q_i ≤ next threshold
  have upper {y : ℝ} (hy_pos : 0 < y) (hy_ge : y ≥ x) {q : ℕ}
      (hq : (q : ℝ) ≤ y + y / (log y) ^ (3 : ℝ)) : (q : ℝ) ≤ y * (1 + ε) := by
    have hlog_ge : log y ≥ log x := log_le_log hx_pos hy_ge
    have h : y / (log y) ^ (3 : ℝ) ≤ y / (log x) ^ (3 : ℝ) :=
      div_le_div_of_nonneg_left hy_pos.le (rpow_pos_of_pos hlog_pos 3)
        (rpow_le_rpow hlog_pos.le hlog_ge (by grind))
    calc (q : ℝ) ≤ y + y / (log y) ^ (3 : ℝ) := hq
      _ ≤ y + y / (log x) ^ (3 : ℝ) := add_le_add_right h y
      _ = y * (1 + ε) := by simp only [hε_def, ← rpow_natCast]; field_simp; ring_nf
  -- Get upper bounds
  have hq₀_ub' : (q₀ : ℝ) ≤ n / (1 + ε) ^ 2 := by
    have := upper (by positivity) hy₀_ge_x hq₀_ub
    calc (q₀ : ℝ) ≤ (n / (1 + ε) ^ 3) * (1 + ε) := this
      _ = n / (1 + ε) ^ 2 := by field_simp
  have hq₁_ub' : (q₁ : ℝ) ≤ n / (1 + ε) := by
    have := upper (by positivity) hy₁_ge_x hq₁_ub
    calc (q₁ : ℝ) ≤ (n / (1 + ε) ^ 2) * (1 + ε) := this
      _ = n / (1 + ε) := by field_simp
  have hq₂_ub' : (q₂ : ℝ) ≤ n := by
    have := upper (by positivity) hy₂_ge_x hq₂_ub
    calc (q₂ : ℝ) ≤ (n / (1 + ε)) * (1 + ε) := this
      _ = n := by field_simp
  -- StrictMono: q₀ < q₁ < q₂
  have hq₀_lt_q₁ : q₀ < q₁ := Nat.cast_lt.mp (hq₀_ub'.trans_lt hq₁_lb)
  have hq₁_lt_q₂ : q₁ < q₂ := Nat.cast_lt.mp (hq₁_ub'.trans_lt hq₂_lb)
  -- q₂ < n: the Dusart interval has upper bound y₂ * (1 + 1/(log y₂)³) < y₂ * (1 + ε) = n
  have hq₂_lt_n : q₂ < n := by
    have hy₂_pos : 0 < (n : ℝ) / (1 + ε) := by positivity
    have hy₂_lt_n : n / (1 + ε) < n := div_lt_self hn_pos (by linarith)
    have hlog_y₂_pos : 0 < log (n / (1 + ε)) := log_pos (by linarith : 1 < (n : ℝ) / (1 + ε))
    have hx_lt_y₂ : x < n / (1 + ε) := by
      have h1ε_lt_1ε3 : (1 + ε) < (1 + ε) ^ 3 := by nlinarith [sq_nonneg ε, sq_nonneg (1 + ε)]
      have h1 : n / (1 + ε) ^ 3 < n / (1 + ε) :=
        div_lt_div_of_pos_left hn_pos h1ε_pos h1ε_lt_1ε3
      calc x ≤ n / (1 + ε) ^ 3 := hy₀_ge_x
        _ < n / (1 + ε) := h1
    have hlog_y₂_gt : log (n / (1 + ε)) > log x := log_lt_log hx_pos hx_lt_y₂
    have hq₂_strict : (q₂ : ℝ) < n := by
      calc (q₂ : ℝ) ≤ n / (1 + ε) + (n / (1 + ε)) / (log (n / (1 + ε))) ^ 3 := hq₂_ub
        _ = (n / (1 + ε)) * (1 + 1 / (log (n / (1 + ε))) ^ 3) := by
            have hpos : (0 : ℝ) < log (n / (1 + ε)) := hlog_y₂_pos
            field_simp [hpos.ne']
            rw [mul_comm]
            norm_cast
        _ < (n / (1 + ε)) * (1 + 1 / (log x) ^ 3) := by
          apply mul_lt_mul_of_pos_left _ hy₂_pos
          gcongr
        _ = (n / (1 + ε)) * (1 + ε) := by simp only [hε_def]
        _ = n := by field_simp
    exact Nat.cast_lt.mp hq₂_strict
  refine ⟨![q₀, q₁, q₂], fun i ↦ by fin_cases i <;> assumption,
    Fin.strictMono_iff_lt_succ.mpr fun i ↦ by fin_cases i <;> assumption,
    fun i ↦ ?_, hq₂_lt_n⟩
  fin_cases i <;> simp only [hε_def]
  · -- Case i = 0: n * (1 + ε)^(-3) ≤ q₀
    simp only [CharP.cast_eq_zero, sub_zero]
    have heq : (n : ℝ) * (1 + 1 / (log x) ^ 3) ^ (-(3 : ℝ)) = n / (1 + ε) ^ 3 := by
      rw [rpow_neg h1ε_pos.le, div_eq_mul_inv]
      norm_cast
    rw [heq]
    exact hq₀_lb.le
  · -- Case i = 1: show n * (1 + ε)^(-2) ≤ q₁
    simp only [Nat.cast_one]
    have heq : (n : ℝ) * (1 + 1 / (log x) ^ 3) ^ (-(3 - 1 : ℝ)) = n / (1 + ε) ^ 2 := by
      have h1 : -(3 - 1 : ℝ) = -2 := by ring
      rw [h1, rpow_neg h1ε_pos.le, div_eq_mul_inv]
      norm_cast
    rw [heq]
    exact hq₁_lb.le
  · -- Case i = 2: show n * (1 + ε)^(-1) ≤ q₂
    simp only [Nat.cast_ofNat]
    have heq : (n : ℝ) * (1 + 1 / (log x) ^ 3) ^ (-(3 - 2 : ℝ)) = n / (1 + ε) := by
      have h1 : -(3 - 2 : ℝ) = -1 := by ring
      rw [h1, rpow_neg h1ε_pos.le, rpow_one, div_eq_mul_inv]
    rw [heq]
    exact hq₂_lb.le


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
  set b : ℝ := (1 + 1 / (log √(n : ℝ)) ^ 3)
  have hb_pos : 0 < b := by
    have : 0 < (log √(n : ℝ)) ^ 3 := by positivity [hlog hn]
    have : 0 < 1 / (log √(n : ℝ)) ^ 3 := by exact one_div_pos.mpr this
    linarith
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hn_pos : (0 : ℝ) < n := by
    have hx0sq_pos : (0 : ℝ) < (X₀ : ℝ) ^ (2 : ℕ) := by
      dsimp [X₀]
      norm_num
    have hx0sq_le_n : (X₀ : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact hx0sq_pos.trans_le hx0sq_le_n
  rw [show ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((i : ℕ) + 1 : ℝ) / n) =
      ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n) by
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
  suffices h : (1 : ℝ) / (exists_q_primes hn).choose i ≤
      b ^ ((3 : ℝ) - (i : ℕ)) / n from (by linarith)
  set t : ℝ := (3 : ℝ) - (i : ℕ)
  have hqi : (n : ℝ) * b ^ (-t) ≤ (exists_q_primes hn).choose i := by
    simpa [b, t] using (exists_q_primes hn).choose_spec.2.2.1 i
  have hpos : (0 : ℝ) < (n : ℝ) * b ^ (-t) := by
    exact mul_pos hn_pos (Real.rpow_pos_of_pos hb_pos _)
  have h1 : (1 : ℝ) / (exists_q_primes hn).choose i ≤
      1 / ((n : ℝ) * b ^ (-t)) :=
    one_div_le_one_div_of_le hpos hqi
  calc
    (1 : ℝ) / (exists_q_primes hn).choose i ≤ 1 / ((n : ℝ) * b ^ (-t)) := h1
    _ = b ^ t / n := by
      have hbpow_pos : 0 < b ^ t := Real.rpow_pos_of_pos hb_pos _
      have hbpow_ne : b ^ t ≠ 0 := ne_of_gt hbpow_pos
      have hneg : b ^ (-t) = (b ^ t)⁻¹ := by
        simpa using (Real.rpow_neg (x := b) (y := t) hb_pos.le)
      calc
        1 / ((n : ℝ) * b ^ (-t)) = 1 / ((n : ℝ) * (b ^ t)⁻¹) := by simp [hneg]
        _ = (1 / n) * b ^ t := by
          field_simp [hn_pos.ne', hbpow_ne, mul_assoc, mul_left_comm, mul_comm]
        _ = b ^ t / n := by
          simp [div_eq_mul_inv, mul_comm]



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
    ∏ i, (1 + (1 : ℝ) /
        ((exists_p_primes hn).choose i * ((exists_p_primes hn).choose i + 1))) ≥
      ∏ i : Fin 3,
        (1 + 1 / ((1 + 1 / (log √(n : ℝ)) ^ 3) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))) := by
  refine Finset.prod_le_prod (fun i _ => by positivity [hlog hn]) fun i _ => ?_
  set p := (exists_p_primes hn).choose
  have h₀ (i) : √n < p i := by
    have : p 0 ≤ p i := by
      apply (exists_p_primes hn).choose_spec.2.1.monotone
      simp
    grw [← this]
    exact (exists_p_primes hn).choose_spec.2.2.2
  gcongr 1 + 1 / ?_
  · have := ((exists_p_primes hn).choose_spec.1 i).pos
    positivity
  have : p i ≤ √n * (1 + 1 / log √n ^ 3) ^ (i + 1 : ℝ) :=
    (exists_p_primes hn).choose_spec.2.2.1 i
  have h₁ : p i ^ 2 ≤ n * (1 + 1 / log √n ^ 3) ^ (2 * i + 2 : ℝ) := by
    grw [this, mul_pow, sq_sqrt (by simp)]
    norm_cast
    rw [← pow_mul]
    grind
  have hn_pos : (0 : ℝ) < n := by
    have hx0sq_pos : (0 : ℝ) < (X₀ : ℝ) ^ (2 : ℕ) := by
      dsimp [X₀]
      norm_num
    have hx0sq_le_n : (X₀ : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact hx0sq_pos.trans_le hx0sq_le_n
  have h₂ : p i + 1 ≤ p i * (1 / n * (n + √n)) := by
    have hsqrt_nonneg : 0 ≤ (√n : ℝ) := by
      exact Real.sqrt_nonneg _
    have hsq : (√(n : ℝ)) ^ 2 = (n : ℝ) := by
      exact sq_sqrt (cast_nonneg n)
    have hsq' : (√(n : ℝ)) * √n = (n : ℝ) := by
      calc
        (√(n : ℝ)) * √n = (√(n : ℝ)) ^ 2 := by ring
        _ = (n : ℝ) := hsq
    have h_n_le : (n : ℝ) ≤ (p i : ℝ) * √n := by
      have h' : (√(n : ℝ)) * √n ≤ (p i : ℝ) * √n := by
        exact mul_le_mul_of_nonneg_right (le_of_lt (h₀ i)) hsqrt_nonneg
      simpa [hsq'] using h'
    have h_div : (1 : ℝ) ≤ (p i : ℝ) * √n / n := by
      have h_div' : (n : ℝ) / n ≤ (p i : ℝ) * √n / n := by
        exact div_le_div_of_nonneg_right h_n_le hn_pos.le
      simpa [hn_pos.ne'] using h_div'
    have h_expand : (p i : ℝ) * (1 / n * (n + √n)) = (p i : ℝ) + (p i : ℝ) * √n / n := by
      field_simp [hn_pos.ne']
    calc
      (p i : ℝ) + 1 ≤ (p i : ℝ) + (p i : ℝ) * √n / n := by
        linarith [h_div]
      _ = (p i : ℝ) * (1 / n * (n + √n)) := by symm; exact h_expand
  grw [h₂, ← mul_assoc, ← sq, h₁]
  field_simp [hn_pos.ne']
  simp



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
  (latexEnv := "lemma")
  (discussion := 534)]
theorem pq_ratio_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 - ((4 : ℝ) * ∏ i, ((exists_p_primes hn).choose i : ℝ))
    / ∏ i, ((exists_q_primes hn).choose i : ℝ) ≥
    1 - 4 * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ 12 / n ^ (3 / 2 : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have hx0sq_pos : (0 : ℝ) < (X₀ : ℝ) ^ (2 : ℕ) := by
      dsimp [X₀]
      norm_num
    have hx0sq_le_n : (X₀ : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact hx0sq_pos.trans_le hx0sq_le_n
  have l1 : ((1 + 1 / Real.log √n ^ 3) ^ 12 / n ^ (3 / 2 : ℝ)) =
    (n ^ (3 / 2 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ 6) /
    (n ^ (3 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ (- 6 : ℝ)) := by
    rw [rpow_neg (hε_pos hn).le, ← div_eq_mul_inv, div_div_eq_mul_div, mul_assoc,
      mul_comm, ← rpow_natCast, ← rpow_natCast (n := 6), ← rpow_add (hε_pos hn),
      ← div_div_eq_mul_div]
    · congr
      · grind
      · have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
        have hpow : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
          convert (Real.rpow_add hn_pos (3 / 2 : ℝ) (3 / 2 : ℝ)) using 1
          · ring_nf
        field_simp [hn_pos.ne']
        simp [pow_two, hpow]
  have l2 : n ^ (3 / 2 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ 6 = ∏ i : Fin 3,
    √n * (1 + 1 / Real.log √n ^ 3) ^ ((i : ℝ) + 1) := by
    rw [← Finset.pow_card_mul_prod, Fin.prod_univ_three, ← rpow_add (hε_pos hn),
      ← rpow_add (hε_pos hn), rpow_div_two_eq_sqrt _ (by linarith)]
    norm_num
  have l3 : n ^ (3 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ (- 6 : ℝ) =
    ∏ i : Fin 3, n * (1 + 1 / Real.log √n ^ 3) ^ (-((3 : ℝ) - i.1))  := by
    rw [← Finset.pow_card_mul_prod, Fin.prod_univ_three, ← rpow_add (hε_pos hn),
      ← rpow_add (hε_pos hn)]
    norm_num
  rw [← mul_div_assoc', ← mul_div_assoc', l1, l2, l3]
  gcongr
  · have := hε_pos hn
    exact Finset.prod_nonneg fun _ _ => by positivity
  · exact Finset.prod_pos fun _ _ => by positivity [hε_pos hn, hn_pos]
  · exact (exists_p_primes hn).choose_spec.2.2.1 _
  · exact fun _ _ => by positivity [hε_pos hn]
  · exact (exists_q_primes hn).choose_spec.2.2.1 _



blueprint_comment /--
\subsection{Reduction to a small epsilon-inequality}
-/

@[blueprint
  "prop:ineq-holds-large-n"
  (title := "Verification of \\eqref{eq:main-ineq} for large \\(n\\)")
  (statement := /-- For every integer \(n \ge X_0^2 \approx 8.04\times 10^9\), the
  primes \(p_i,q_i\) constructed in Lemmas~\ref{lem:choose-pi} and \ref{lem:choose-qi} satisfy the
  inequality \eqref{eq:main-ineq}. -/)
  (proof := /-- Combine Lemma~\ref{lem:qi-product}, Lemma~\ref{lem:pi-product}, and
  Lemma~\ref{lem:pq-ratio}.  Then apply Lemma~\ref{lem:eps-bounds} and set \(\varepsilon = 1/n\).
  The products are bounded by the expressions in Lemma~\ref{lem:poly-ineq}, and the inequality in
  Lemma~\ref{lem:final-comparison} then ensures that \eqref{eq:main-ineq} holds. -/)
  (proofUses := ["lem:eps-bounds", "lem:qi-product", "lem:final-comparison", "lem:poly-ineq",
  "lem:pq-ratio", "lem:pi-product"])
  (latexEnv := "proposition")
  (discussion := 512)]
noncomputable def Criterion.mk' {n : ℕ} (hn : n ≥ X₀ ^ 2) : Criterion where
  n := n
  p := (exists_p_primes hn).choose
  q := (exists_q_primes hn).choose
  hn := le_trans (by decide : 1 ≤ X₀ ^ 2) hn
  hp := (exists_p_primes hn).choose_spec.1
  hp_mono := (exists_p_primes hn).choose_spec.2.1
  hq := (exists_q_primes hn).choose_spec.1
  hq_mono := (exists_q_primes hn).choose_spec.2.1
  h_ord_1 := (exists_p_primes hn).choose_spec.2.2.2
  h_ord_2 := by
    have hn_pos : (0 : ℝ) < n := by
      -- from hn : X₀^2 ≤ n, it suffices to show 0 < X₀^2
      have hx0sq_pos : (0 : ℝ) < (X₀ : ℝ) ^ (2 : ℕ) := by
        -- easiest: unfold X₀ to a numeral and finish
        dsimp [X₀]
        -- if needed in your setup: dsimp [Dusart.X₀]
        norm_num
      have hx0sq_le_n : (X₀ : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      exact hx0sq_pos.trans_le hx0sq_le_n
    have hp' : ((exists_p_primes hn).choose 2 : ℝ) ≤ √n * (1 + 1 / (log √n) ^ 3) ^ 3 := by
      convert (exists_p_primes hn).choose_spec.2.2.1 2 using 2; norm_cast
    have hq' : n * (1 + 1 / (log √n) ^ 3) ^ (-3 : ℝ) ≤ (exists_q_primes hn).choose 0 := by
      convert (exists_q_primes hn).choose_spec.2.2.1 0 using 2
      norm_num
    have hε_pos := hε_pos hn
    have hmid :
        √n * (1 + 1 / (log √n) ^ 3) ^ 3 < n * (1 + 1 / (log √n) ^ 3) ^ (-3 : ℝ) := by
      set ε : ℝ := 1 + 1 / (log √n) ^ 3
      have hε_pos' : 0 < ε := by
        simpa [ε] using hε_pos
      have hε3_pos : 0 < ε ^ 3 := by
        positivity [hε_pos']
      have hε6_lt2 : ε ^ 6 < 2 := by
        have hlog : (11.4 : ℝ) ≤ log √n := hlog hn
        have hpow : (11.4 : ℝ) ^ 3 ≤ (log √n) ^ 3 := by
          exact (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 11.4) hlog) 3
        have hdiv : 1 / (log √n) ^ 3 ≤ 1 / (11.4 : ℝ) ^ 3 := by
          have hpos : 0 < (11.4 : ℝ) ^ 3 := by norm_num
          exact one_div_le_one_div_of_le hpos hpow
        have hε_le : ε ≤ 1 + 1 / (11.4 : ℝ) ^ 3 := by linarith [hdiv]
        have hε6_le : ε ^ 6 ≤ (1 + 1 / (11.4 : ℝ) ^ 3) ^ 6 := by
          exact (pow_le_pow_left₀ (by linarith [hε_pos']) hε_le) 6
        have hε6_lt : (1 + 1 / (11.4 : ℝ) ^ 3) ^ 6 < 2 := by
          norm_num
        exact lt_of_le_of_lt hε6_le hε6_lt
      have hsqrt_ge2 : (2 : ℝ) ≤ √n := by
        have hx0_ge2 : (2 : ℝ) ≤ X₀ := by
          dsimp [X₀]
          norm_num
        exact le_trans hx0_ge2 (hsqrt_ge hn)
      have hε6_lt_sqrt : ε ^ 6 < √n := lt_of_lt_of_le hε6_lt2 hsqrt_ge2
      have hsqrt_pos : 0 < (√n : ℝ) := by positivity [hn_pos]
      have h1 : √n * ε ^ 6 < (n : ℝ) := by
        have hmul : √n * ε ^ 6 < √n * √n :=
          mul_lt_mul_of_pos_left hε6_lt_sqrt hsqrt_pos
        exact hmul.trans_eq (by
          simpa [mul_comm] using (mul_self_sqrt (Nat.cast_nonneg n)))
      have hdiv := (div_lt_div_of_pos_right h1 hε3_pos)
      have hdiv' : √n * ε ^ 3 < (n : ℝ) / ε ^ 3 := by
        calc
          √n * ε ^ 3 = (√n * ε ^ 6) / ε ^ 3 := by
            field_simp [hε3_pos.ne', pow_add, mul_assoc, mul_left_comm, mul_comm]
          _ < (n : ℝ) / ε ^ 3 := hdiv
      -- rewrite back to the original form
      have hneg : (n : ℝ) * ε ^ (-3 : ℝ) = (n : ℝ) / ε ^ 3 := by
        rw [rpow_neg hε_pos'.le, div_eq_mul_inv]
        simp [Real.rpow_natCast, mul_comm, mul_left_comm, mul_assoc]
      calc
        √n * ε ^ 3 < (n : ℝ) / ε ^ 3 := hdiv'
        _ = (n : ℝ) * ε ^ (-3 : ℝ) := hneg.symm
    exact_mod_cast hp'.trans_lt <| hmid.trans_le hq'
  h_ord_3 := (exists_q_primes hn).choose_spec.2.2.2
  h_crit := by
    have hn₀ : 0 ≤ Real.log √n := by
      sorry
      -- grw [hn]
      -- simp [log_nonneg]
    have h₁ : 1 - (4 : ℝ) *
        (∏ i, (exists_p_primes hn).choose i : ℝ) / ∏ i, ((exists_q_primes hn).choose i : ℝ) ≥
        1 - 4 * onePlusEps_log ^ 12 * ((1 / X₀) * (1 / n)) := by
      grw [pq_ratio_ge hn, inv_cube_log_sqrt_le hn, ← inv_n_pow_3_div_2_le hn]
      simp [field]
    have : 0 ≤ 1 - 4 * onePlusEps_log ^ 12 * ((1 / X₀) * (1 / n)) := by
      sorry
      -- grw [hn]
      -- norm_num
    have := this.trans h₁
    have hn' : (0 : ℝ) ≤ 1 / ↑n ∧ (1 : ℝ) / ↑n ≤ 1 / X₀ ^ 2 :=
      sorry
      -- ⟨by simp, by grw [hn]; simp⟩
    grw [Lcm.prod_q_ge hn, Lcm.prod_p_ge hn, h₁]
    simp_rw [div_eq_mul_one_div (_ ^ (_ : ℝ) : ℝ) (n : ℝ),
      show 3 / (8 * n : ℝ) = 3 / 8 * (1 / n) by field_simp, ← one_div_mul_one_div]
    grw [inv_cube_log_sqrt_le hn, inv_n_add_sqrt_ge hn]
    set ε : ℝ := 1 / n
    calc
      _ ≤ ∏ i : Fin 3, (1 + onePlusEps_log ^ (i + 1 : ℝ) * ε) := by gcongr
      _ ≤ _ := (prod_epsilon_le (ε := ε) hn')
      _ ≤ _ := final_comparison hn'
      _ ≤ _ := by sorry
        -- grw [← prod_epsilon_ge hn']
        -- apply le_of_eq
        -- simp [field]
        -- ring_nf

blueprint_comment /--
\subsection{Conclusion for large \(n\)}
-/

@[blueprint
  "thm:large-n-final"
  (title := "Non-highly abundant for large \\(n\\)")
  (statement := /-- For every integer \(n \ge X_0^2\), the integer \(L_n\) is not highly
  abundant. -/)
  (proof := /-- By Proposition~\ref{prop:ineq-holds-large-n}, there exist primes
  \(p_1,p_2,p_3,q_1,q_2,q_3\) satisfying the hypotheses of Theorem~\ref{thm:criterion}.
  Hence \(L_n\) is not highly abundant. -/)
  (proofUses := ["prop:ineq-holds-large-n", "thm:criterion"])]
theorem L_not_HA_of_ge (n : ℕ) (hn : n ≥ X₀ ^ 2) : ¬HighlyAbundant (L n) :=
  (Criterion.mk' hn).not_highlyAbundant

end Lcm
