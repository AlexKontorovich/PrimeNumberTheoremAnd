import Architect
import Mathlib.NumberTheory.Chebyshev
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

lemma Criterion.p_gt_two (c : Criterion) (i : Fin 3) : 2 < c.p i := by
  have h_pi_gt_two : ∀ i, 1 < c.p i := fun i ↦ Nat.Prime.one_lt (c.hp i)
  by_contra h_contra
  interval_cases _ : c.p i; iterate 2 grind
  · have := c.h_ord_1; have := c.h_ord_2; have := c.h_ord_3; fin_cases i
    · simp_all only [Fin.isValue, Fin.zero_eta, cast_ofNat]
      rw [Real.sqrt_lt] at * <;> norm_cast at * <;>
      linarith [h_pi_gt_two 0, h_pi_gt_two 1, h_pi_gt_two 2, c.hp_mono (show 0 < 1 by decide),
        c.hp_mono (show 1 < 2 by decide), c.hq_mono (show 0 < 1 by decide),
        c.hq_mono (show 1 < 2 by decide)]
    · grind [c.hp_mono (show 0 < 1 by decide) , c.hp_mono (show 1 < 2 by decide)]
    · grind [h_pi_gt_two 0, h_pi_gt_two 1, h_pi_gt_two 2, c.hp_mono (show 0 < 1 by decide),
        c.hp_mono (show 1 < 2 by decide)]

lemma Criterion.q_gt_two (c : Criterion) (i : Fin 3) : 2 < c.q i := by
  have h_q_gt_two : ∀ i, 2 < c.q i := fun i ↦ by
    have h_q_gt_p : ∀ i, c.p 2 < c.q i := fun i ↦ by
      fin_cases i <;> linarith! [c.hp_mono <| show 0 < 1 by decide, c.hp_mono <|
        show 1 < 2 by decide, c.hq_mono <| show 0 < 1 by decide, c.hq_mono <|
        show 1 < 2 by decide, c.h_ord_2, c.h_ord_3]
    grind [c.p_gt_two 2]
  exact h_q_gt_two i

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

lemma Criterion.val_two_L' (c : Criterion) : (c.L').factorization 2 = Nat.log 2 c.n := by
  have h_lcm : ∀ n : ℕ, n ≥ 1 → Nat.factorization (L n) 2 = Nat.log 2 n := by
    have h_lcm_exp : ∀ n : ℕ, n ≥ 1 → (Nat.factorization (Finset.lcm (Finset.Icc 1 n)
        (fun x ↦ x)) 2) = Finset.sup (Finset.Icc 1 n) (fun x ↦ Nat.factorization x 2) := by
      intros n hn
      have h_lcm_exp : ∀ {S : Finset ℕ}, (∀ x ∈ S, x ≠ 0) → (Nat.factorization (Finset.lcm S
          (fun x ↦ x)) 2) = Finset.sup S (fun x ↦ Nat.factorization x 2) := by
        intro S hS
        induction S using Finset.induction with
        | empty => simp
        | insert x S hxS ih =>
            simp_all only [lcm_insert]
            erw [Nat.factorization_lcm] <;> simp_all
      exact h_lcm_exp fun x hx ↦ by linarith [Finset.mem_Icc.mp hx]
    have h_sup : ∀ n : ℕ, n ≥ 1 → Finset.sup (Finset.Icc 1 n) (fun x ↦ Nat.factorization x 2) =
       Nat.log 2 n := fun n hn ↦ by
      apply le_antisymm
      · exact Finset.sup_le fun x hx ↦ Nat.le_log_of_pow_le (by decide) <|
          Nat.le_trans (Nat.le_of_dvd (by linarith [Finset.mem_Icc.mp hx])
          <| Nat.ordProj_dvd _ _) <| by linarith [Finset.mem_Icc.mp hx]
      · refine le_trans ?_ (Finset.le_sup <| Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ zero_lt_two,
          Nat.pow_log_le_self 2 <| by linarith⟩)
        norm_num [Nat.Prime.factorization_self (prime_two)]
    aesop
  rw [show c.L' = L c.n / (∏ i, c.q i) by rfl, Nat.factorization_div] <;> norm_num [h_lcm, c.hn]
  · rw [Nat.factorization_eq_zero_of_not_dvd] <;> norm_num [Fin.prod_univ_three]
    norm_num [Nat.mul_mod, Nat.mod_mod, Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (c.hq 0)
      (by linarith [c.p_gt_two 0, c.q_gt_two 0])), Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (c.hq 1)
      (by linarith [c.p_gt_two 1, c.q_gt_two 1])), Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (c.hq 2)
      (by linarith [c.p_gt_two 2, c.q_gt_two 2]))]
  · exact prod_q_dvd_L c

lemma Criterion.val_p_L' (c : Criterion) (i : Fin 3) : (c.L').factorization (c.p i) = 1 := by
  have h_pi_factor : Nat.factorization (L c.n) (c.p i) = 1 := by
    have h_prime_factor : ∀ {p : ℕ}, Nat.Prime p → Real.sqrt c.n < p → p < c.n →
        (Nat.factorization (L c.n)) p = 1 := @fun p hp hp_sqrt hp_lt_n ↦ by
      have h_prime_factor : (Nat.factorization (L c.n)) p = 1 := by
        have h_prime_factor_def : (Nat.factorization (L c.n)) p = Finset.sup (Finset.Icc 1 c.n)
            (fun i ↦ Nat.factorization i p) := by
          have h_prime_factor_def : (Nat.factorization (Finset.lcm (Finset.Icc 1 c.n) (fun i ↦ i)))
              p = Finset.sup (Finset.Icc 1 c.n) (fun i ↦ Nat.factorization i p) := by
            have h_lcm_factorization : ∀ {S : Finset ℕ}, (∀ i ∈ S, i ≠ 0) →
                (Nat.factorization (Finset.lcm S (fun i ↦ i))) p =
                Finset.sup S (fun i ↦ Nat.factorization i p) := by
              intros S hS_nonzero
              induction S using Finset.induction with
              | empty => simp [Finset.lcm]
              | insert i S hiS ih =>
                  by_cases hi : i = 0
                  · simp_all
                  simp only [lcm_insert]
                  erw [Nat.factorization_lcm] <;> simp_all
            exact h_lcm_factorization fun i hi ↦ by linarith [Finset.mem_Icc.mp hi]
          exact h_prime_factor_def
        have h_prime_power : ∀ i ∈ Finset.Icc 1 c.n, Nat.factorization i p ≤ 1 := fun i hi ↦ by
          have h_prime_power : p^2 > c.n := by
            rw [Real.sqrt_lt] at hp_sqrt <;> norm_cast at * <;> nlinarith only [hp_sqrt, hp_lt_n]
          exact le_of_not_gt fun h ↦ absurd (Nat.dvd_trans (pow_dvd_pow p h) (Nat.ordProj_dvd i p))
            (Nat.not_dvd_of_pos_of_lt (Finset.mem_Icc.mp hi |>.1)
            (by nlinarith [Finset.mem_Icc.mp hi |>.2]))
        refine h_prime_factor_def.trans (le_antisymm (Finset.sup_le h_prime_power) ?_)
        exact le_trans (by norm_num [hp]) (Finset.le_sup (f := fun i ↦ Nat.factorization i p)
          (Finset.mem_Icc.mpr ⟨hp.pos, hp_lt_n.le⟩))
      exact (Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd ((h_prime_factor.symm))) p)).symm
    apply h_prime_factor (c.hp i) (c.h_ord_1.trans_le (by
      exact_mod_cast c.hp_mono.monotone (Nat.zero_le _))) (by
        have := c.h_ord_2; have := c.h_ord_3; fin_cases i <;> linarith! [c.hp_mono <|
          show 0 < 1 by decide, c.hp_mono <| show 1 < 2 by decide, c.hq_mono <|
          show 0 < 1 by decide, c.hq_mono <| show 1 < 2 by decide])
  have h_pi_factor_L' : Nat.factorization (L c.n) (c.p i) = Nat.factorization (c.L')
      (c.p i) + Nat.factorization (∏ i, c.q i) (c.p i) := by
    have h_pi_factor_L' : Nat.factorization (L c.n) = Nat.factorization (c.L') +
        Nat.factorization (∏ i, c.q i) := by
      rw [← Nat.factorization_mul] <;> norm_num [c.L'_pos.ne']
      · rw [mul_comm, Criterion.L_eq_prod_q_mul_L']
      · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.Prime.ne_zero (c.hq i)
    aesop
  have h_pi_not_div_q : ∀ j, ¬(c.p i ∣ c.q j) := by
    intro j hj; have := c.hq j; have := c.hp i; simp_all only [Nat.prime_dvd_prime_iff_eq]
    have := c.h_ord_2; have := c.h_ord_3; fin_cases i <;> fin_cases j <;> linarith! [c.hp_mono <|
      show 0 < 1 by decide, c.hp_mono <| show 1 < 2 by decide, c.hq_mono <|
      show 0 < 1 by decide, c.hq_mono <| show 1 < 2 by decide]
  simp_all [Fin.prod_univ_three,Nat.factorization_mul,Nat.Prime.ne_zero (c.hq _),
    Nat.factorization_eq_zero_of_not_dvd (h_pi_not_div_q _)]

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
    rw [← pow_one (c.q i), sigma_one_apply_prime_pow (c.hq i)]
    simp [reduceAdd, geom_sum_two, pow_one, add_comm]
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

lemma Criterion.val_two_M_ge_L' (c : Criterion) : (c.M).factorization 2 ≥ (c.L').factorization 2 + 2
    := by
  rw [show c.M = (4 * ∏ i, c.p i) * c.m * c.L' from rfl, Nat.factorization_mul]
  · simp only [Fin.prod_univ_three, ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero,
      Nat.Prime.ne_zero (c.hp _), or_self, not_false_eq_true, Nat.ne_of_gt (Criterion.m_pos c),
      factorization_mul]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow]; norm_num; ring_nf;
      linarith [Nat.Prime.factorization_self (prime_two)]
  · simp only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, prod_eq_zero_iff, mem_univ,
    true_and, false_or, not_or, not_exists]
    exact ⟨fun i ↦ Nat.Prime.ne_zero (c.hp i), Nat.ne_of_gt (c.m_pos)⟩
  · exact Nat.ne_of_gt <| c.L'_pos

lemma Criterion.val_p_M_ge_two (c : Criterion) (i : Fin 3) : (c.M).factorization (c.p i) ≥ 2 := by
  have h_pi_factorization_M : (Nat.factorization (c.M)) (c.p i) =
      (Nat.factorization (4 * ∏ i, c.p i)) (c.p i) + (Nat.factorization (c.m)) (c.p i) +
      (Nat.factorization (c.L')) (c.p i) := by
    rw [show c.M = (4 * ∏ i, c.p i) * c.m * c.L' by
          exact Nat.add_zero (((4 * ∏ i, c.p i) * c.m).mul c.L'), Nat.factorization_mul,
            Nat.factorization_mul]
    iterate 3 simp [Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.Prime.ne_zero (c.hp i),
      Nat.ne_of_gt (Criterion.m_pos c)]
    · simp only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or, not_or]
      exact ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.Prime.ne_zero (c.hp i),
        Nat.ne_of_gt (c.m_pos)⟩
    · exact Nat.ne_of_gt (Criterion.L'_pos c)
  simp_all only [Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ i),
    ge_iff_le, val_p_L' c i, reduceLeDiff]
  rw [Nat.factorization_mul] <;> norm_num
  · rw [Nat.factorization_mul]
    · exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le (Nat.zero_le _)
        (Nat.one_le_iff_ne_zero.mpr <| by simp [c.hp i])) (Nat.zero_le _)
    · simp only [ne_eq, prod_eq_zero_iff, mem_sdiff, mem_univ, mem_singleton, true_and,
      not_exists, not_and]
      exact fun x hx ↦ Nat.Prime.ne_zero (c.hp x)
    · exact Nat.Prime.ne_zero (c.hp i)
  · exact ⟨Finset.prod_ne_zero_iff.mpr fun j hj ↦ Nat.Prime.ne_zero (c.hp j),
      Nat.Prime.ne_zero (c.hp i)⟩

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

private lemma σnorm_ratio_ge_aux {k : ℕ} (n : ℕ) (hk : 2 ^ k ≤ n) :
    (∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i) / (∑ i ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ i) ≥
      1 + 3 / (8 * n) := by
    have h_sums : (∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i) = 2 - (1 / 2) ^ (k + 2) ∧
        (∑ i ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ i) = 2 - (1 / 2) ^ k := by
      norm_num [geom_sum_eq]; ring_nf; norm_num
    field_simp [h_sums]
    rw [h_sums.1,h_sums.2]; ring_nf; norm_num
    have h_inv : (n : ℝ)⁻¹ ≤ (1 / 2 : ℝ) ^ k := by
      simpa using inv_anti₀ (by positivity) (mod_cast hk)
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k, pow_le_pow_of_le_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show k ≥ 0 by norm_num)]

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
  (latexEnv := "lemma")
  (discussion := 664)]
theorem Criterion.σnorm_M_ge_σnorm_L'_mul (c : Criterion) :
    σnorm c.M ≥
      σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) := by
  have h_sigma_norm_M : (σnorm c.M) = (σnorm (c.L' : ℕ)) * (∏ p ∈ Nat.primeFactors c.M,
      ((∑ i ∈ Finset.range (Nat.factorization c.M p + 1), (1 / p : ℝ) ^ i) /
      (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) p + 1), (1 / p : ℝ) ^ i))) := by
    have h_sigma_norm_prod : ∀ {n : ℕ}, n ≠ 0 → (σnorm n : ℝ) = (∏ p ∈ Nat.primeFactors n,
        ((∑ i ∈ Finset.range (Nat.factorization n p + 1), (1 / p : ℝ) ^ i))) := by
      intro n hn_ne_zero
      have h_sigma_def : ((σ n) : ℝ) = (∏ p ∈ Nat.primeFactors n, (∑ i ∈ Finset.range
          (Nat.factorization n p + 1), (p ^ i : ℝ))) := by
        unfold σ
        have h_sigma_def : ∀ {n : ℕ}, n ≠ 0 → (Nat.divisors n).sum (fun d ↦ d) =
            ∏ p ∈ n.primeFactors, (∑ i ∈ Finset.range (Nat.factorization n p + 1), p ^ i) := by
          exact fun {n} a ↦ sum_divisors a
        convert congr_arg (( ↑ ) : ℕ → ℝ) (h_sigma_def hn_ne_zero) using 1 <;>
        norm_num [ArithmeticFunction.sigma]
      have h_sigma_def : (n : ℝ) = (∏ p ∈ Nat.primeFactors n, (p ^ (Nat.factorization n p) : ℝ)) :=
        mod_cast Eq.symm (Nat.factorization_prod_pow_eq_self hn_ne_zero)
      simp_all only [div_eq_mul_inv]
      rw [← div_eq_mul_inv, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp ↦ ?_
      field_simp
      rw [Finset.mul_sum _ _ _, ← Finset.sum_flip]
      exact Finset.sum_congr rfl fun i hi ↦ by
        rw [show ((1:ℝ) / ↑p) ^ i = 1 / ((↑p) ^ i) by simp]
        rw [mul_one_div, eq_div_iff (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <|
          Nat.pos_of_mem_primeFactors hp), ←pow_add, Nat.sub_add_cancel <|
          Finset.mem_range_succ_iff.mp hi]
    by_cases hM : c.M = 0 <;> by_cases hL' : c.L' = 0
    · simp_all
    · exact absurd hM (Nat.ne_of_gt (Criterion.M_pos c))
    · exact absurd hL' (Nat.ne_of_gt (Criterion.L'_pos c))
    · simp_all only [ne_eq, one_div, inv_pow, not_false_eq_true, prod_div_distrib]
      rw [mul_div, eq_div_iff]
      · rw [mul_comm, ← Finset.prod_subset (show c.L'.primeFactors ⊆ c.M.primeFactors from ?_)]
        · intro p hp hpn; rw [Nat.factorization_eq_zero_of_not_dvd] <;> aesop
        · intro p hp; simp_all only [mem_primeFactors, ne_eq, not_false_eq_true, and_true, true_and]
          exact dvd_trans hp.2 (by exact ⟨(4 * ∏ i, c.p i) * c.m, by rw [Criterion.M]; ring⟩)
      · exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ ne_of_gt <| Finset.sum_pos
          (fun _ _ ↦ inv_pos.mpr <| pow_pos (Nat.cast_pos.mpr <| Nat.pos_of_mem_primeFactors hp) _)
          <| by norm_num
  have h_ratio_terms (p : ℕ) (hp : p ∈ Nat.primeFactors c.M) : (∑ i ∈ Finset.range
      (Nat.factorization c.M p + 1), (1 / p : ℝ) ^ i) / (∑ i ∈ Finset.range
      (Nat.factorization (c.L' : ℕ) p + 1), (1 / p : ℝ) ^ i) ≥ if p ∈ Finset.image c.p Finset.univ
      then (1 + 1 / (p * (p + 1) : ℝ)) else if p = 2 then (1 + 3 / (8 * c.n : ℝ)) else 1 := by
    split_ifs
    · obtain ⟨i, hi⟩ : ∃ i : Fin 3, p = c.p i := by grind
      have h_ratio_p_i : (∑ i ∈ Finset.range (Nat.factorization c.M p + 1), (1 / p : ℝ) ^ i) /
          (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) p + 1), (1 / p : ℝ) ^ i) ≥
          (∑ i ∈ Finset.range 3, (1 / p : ℝ) ^ i) / (∑ i ∈ Finset.range 2, (1 / p : ℝ) ^ i) := by
        rw [show Nat.factorization (c.L' : ℕ) p = 1 from hi ▸ c.val_p_L' i]
        exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono
          (by grind [c.val_p_M_ge_two i])) fun _ _ _ ↦ by positivity)
          (Finset.sum_nonneg fun _ _ ↦ by positivity)
      convert h_ratio_p_i using 1; norm_num [Finset.sum_range_succ]; ring_nf; field_simp; grind
    · have h_geo_series : (∑ i ∈ Finset.range (Nat.factorization c.M 2 + 1), (1 / 2 : ℝ) ^ i)
          / (∑ i ∈ Finset.range (Nat.factorization c.L' 2 + 1), (1 / 2 : ℝ) ^ i) ≥
          (1 + 3 / (8 * c.n : ℝ)) := by
        have h_geo_series : (∑ i ∈ Finset.range (Nat.factorization c.M 2 + 1), (1 / 2 : ℝ) ^ i)
            / (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) 2 + 1), (1 / 2 : ℝ) ^ i) ≥
            (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) 2 + 3), (1 / 2 : ℝ) ^ i) /
            (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) 2 + 1), (1 / 2 : ℝ) ^ i) := by
          exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (by linarith [val_two_M_ge_L' c])) fun _ _ _ ↦ by positivity)
            (Finset.sum_nonneg fun _ _ ↦ by positivity)
        refine le_trans ?_ h_geo_series
        convert σnorm_ratio_ge_aux c.n _ using 1
        exact c.val_two_L'.symm ▸ Nat.pow_log_le_self 2 (by linarith [c.hn])
      aesop
    · rw [ge_iff_le, le_div_iff₀] <;> norm_num
      · refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ ?_))
          fun ?_ ?_ ?_ ↦ by positivity
        have h_div : c.L' ∣ c.M := by
          exact dvd_mul_left _ _
        exact (Nat.factorization_le_iff_dvd (by aesop) (by aesop)) |>.2 h_div p
      · exact Finset.sum_pos (fun _ _ ↦ inv_pos.mpr (pow_pos (Nat.cast_pos.mpr
          (Nat.pos_of_mem_primeFactors hp)) _)) (by norm_num)
  have h_prod_ratio_terms : (∏ p ∈ Nat.primeFactors c.M,
      ((∑ i ∈ Finset.range (Nat.factorization c.M p + 1), (1 / p : ℝ) ^ i) /
      (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) p + 1), (1 / p : ℝ) ^ i))) ≥
      (∏ p ∈ Finset.image c.p Finset.univ, (1 + 1/(p * (p + 1) : ℝ)))*(1 + 3 / (8 * c.n : ℝ)) := by
    refine le_trans ?_ (Finset.prod_le_prod ?_ h_ratio_terms)
    · rw [Finset.prod_ite]
      refine mul_le_mul ?_ ?_ (by positivity) (Finset.prod_nonneg fun _ _ ↦ by positivity)
      · rw [Finset.prod_subset]
        · simp only [mem_image, mem_univ, true_and, subset_iff, mem_filter, mem_primeFactors,
            forall_exists_index, forall_apply_eq_imp_iff, exists_apply_eq_apply, and_true]
          intro i; exact ⟨c.hp i, by
            exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
              (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) _) _) _, by
              exact Nat.ne_of_gt (Criterion.M_pos c)⟩
        · aesop
      · rw [Finset.prod_ite]
        by_cases h : 2 ∈ c.M.primeFactors <;> simp_all +decide only
          [mem_primeFactors, true_and, prod_const]
        · simp only [one_pow, mul_one]
          refine le_self_pow₀ (M₀ := ℝ) (by norm_num ; positivity) ?_
          · norm_num; exact ⟨2, Nat.prime_two, h.1, h.2, fun i ↦ by linarith [c.p_gt_two i], rfl⟩
        · contrapose! h
          refine ⟨dvd_mul_of_dvd_left ?_ _, Nat.ne_of_gt (Criterion.M_pos c)⟩
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide) _) _
    · intro p hp; split_ifs <;> positivity
  simp_all
  rw [Finset.prod_image] at h_prod_ratio_terms <;> norm_num [Finset.prod_range_succ] at *
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h_prod_ratio_terms <|
      show 0 ≤ σnorm c.L' by exact div_nonneg (Nat.cast_nonneg _) <| Nat.cast_nonneg _
  · simp [c.hp_mono.injective]



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

abbrev X₀ := 89693

lemma hsqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ 89693 := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ 89693 ^ 2)

lemma log_X₀_gt : Real.log X₀ > 11.4 := by
  rw [gt_iff_lt, show (11.4 : ℝ) = 57 / (5 : ℕ) by norm_num, div_lt_iff₀ (by norm_num),
    mul_comm, ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num

lemma hlog {n : ℕ} (hn : n ≥ X₀ ^ 2) : log √(n : ℝ) ≥ 11.4 := by
  calc log √(n : ℝ) ≥ log (X₀ : ℝ) :=
        log_le_log (by grind : (0 : ℝ) < X₀) (hsqrt_ge hn)
    _ ≥ 11.4 := log_X₀_gt.le

lemma hε_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < 1 + 1 / (log √(n : ℝ)) ^ 3 := by
  positivity [hlog hn]

lemma log_X₀_pos : 0 < Real.log X₀ := by linear_combination log_X₀_gt

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
  (proof := /-- Apply Proposition~\ref{Dusart_prop_5_4} successively with
  \(x, x(1+1/\log^3 x), x(1+1/\log^3 x)^2\), keeping track of the resulting primes and bounds.
  For \(n\) large and \(x = \sqrt{n}\), we have \(\sqrt{n} < p_1\) as soon as the first interval
  lies strictly above \(\sqrt{n}\); this can be enforced by taking \(n\) large enough. -/)
  (latexEnv := "lemma")]
theorem exists_p_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i, p i ≤ √(n : ℝ) * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0 := by
  let x := √(n : ℝ)
  have hx_pos : 0 < x := (by grind : (0 : ℝ) < X₀).trans_le (hsqrt_ge hn)
  have hlog_pos : 0 < log x := by positivity [hlog hn]
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
  have hx1_ge : x * (1 + ε) ≥ X₀ := (hsqrt_ge hn).trans (le_mul_of_one_le_right hx_pos.le
    (by grind))
  have hx2_ge : x * (1 + ε) ^ 2 ≥ X₀ := (hsqrt_ge hn).trans (le_mul_of_one_le_right hx_pos.le
    (by nlinarith [sq_nonneg ε]))
  obtain ⟨p₀, hp₀_prime, hp₀_lb, hp₀_ub⟩ := Dusart.proposition_5_4 x (hsqrt_ge hn)
  obtain ⟨p₁, hp₁_prime, hp₁_lb, hp₁_ub⟩ := Dusart.proposition_5_4 _ hx1_ge
  obtain ⟨p₂, hp₂_prime, hp₂_lb, hp₂_ub⟩ := Dusart.proposition_5_4 _ hx2_ge
  have hp₀_ub' : (p₀ : ℝ) ≤ x * (1 + ε) := upper hx_pos le_rfl hp₀_ub
  have hp₁_ub' : (p₁ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    linarith [sq (1 + ε), upper (by grind) (log_le_log hx_pos (by grind)) hp₁_ub]
  have hp₂_ub' : (p₂ : ℝ) ≤ x * (1 + ε) ^ 3 := by
    linarith [pow_succ (1 + ε) 2, upper (by grind) (log_le_log hx_pos (by grind)) hp₂_ub]
  refine ⟨![p₀, p₁, p₂], fun i ↦ by fin_cases i <;> assumption,
    Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
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
  (proof := /-- Apply Theorem~\ref{Dusart_prop_5_4} with suitable values of \(x\) slightly below \(n\),
  e.g.\ \(x = n(1+1/\log^3\sqrt{n})^{-i}\), again keeping track of the intervals.  For \(n\) large
  enough, these intervals lie in \((\sqrt{n},n)\) and contain primes \(q_i\) with the desired
  ordering. -/)
  (proofUses := ["Dusart_prop_5_4"])
  (latexEnv := "lemma")]
theorem exists_q_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3, n * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (-((3 : ℝ) - (i : ℕ))) ≤ q i) ∧
      q 2 < n := by
  let x := √(n : ℝ)
  have hx_pos : 0 < x := (by grind : (0 : ℝ) < X₀).trans_le (hsqrt_ge hn)
  have hlog_pos : 0 < log x := by positivity [hlog hn]
  set ε := 1 / (log x) ^ 3 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h1ε_pos : 0 < 1 + ε := by linarith
  have hn_pos : (0 : ℝ) < n := by positivity
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
    Dusart.proposition_5_4 (n / (1 + ε) ^ 3) hy₀_ge
  obtain ⟨q₁, hq₁_prime, hq₁_lb, hq₁_ub⟩ :=
    Dusart.proposition_5_4 (n / (1 + ε) ^ 2) hy₁_ge
  obtain ⟨q₂, hq₂_prime, hq₂_lb, hq₂_ub⟩ :=
    Dusart.proposition_5_4 (n / (1 + ε)) hy₂_ge
  -- Show y_i ≥ x (needed for upper bound helper)
  have hx_ge_2 : x ≥ 2 := by linarith [hsqrt_ge hn, (by grind : (2 : ℝ) ≤ X₀)]
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
  rw [show ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((i : ℕ) + 1 : ℝ) / n) =
      ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n) by
    simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]; ring_nf]
  apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
  intro i _
  suffices h : (1 : ℝ) / (exists_q_primes hn).choose i ≤
      (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n from (by linarith)
  have := (exists_q_primes hn).choose_spec.2.2.1 i
  rw [show (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n =
      1 / (n / (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) ) by field_simp]
  have f0 : (0 : ℝ) < (log √(n : ℝ)) ^ 3 := by positivity [hlog hn]
  apply one_div_le_one_div_of_le
  · positivity
  · convert this using 1
    field_simp
    rw [← rpow_add (hε_pos hn)]
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
  have h₂ : p i + 1 ≤ p i * (1 / n * (n + √n)) := by
    field_simp [this]
    linear_combination √n * h₀ i - sq_sqrt (cast_nonneg n)
  grw [h₂, ← mul_assoc, ← sq, h₁]
  field_simp
  rfl

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
  have l1 : ((1 + 1 / Real.log √n ^ 3) ^ 12 / n ^ (3 / 2 : ℝ)) =
    (n ^ (3 / 2 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ 6) /
    (n ^ (3 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ (- 6 : ℝ)) := by
    rw [rpow_neg (hε_pos hn).le, ← div_eq_mul_inv, div_div_eq_mul_div, mul_assoc,
      mul_comm, ← rpow_natCast, ← rpow_natCast (n := 6), ← rpow_add (hε_pos hn),
      ← div_div_eq_mul_div]
    · congr
      · grind
      · rw [← rpow_sub (by norm_cast; linarith)]; grind
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
  · exact Finset.prod_pos fun _ _ => by positivity [hε_pos hn]
  · exact (exists_p_primes hn).choose_spec.2.2.1 _
  · exact fun _ _ => by positivity [hε_pos hn]
  · exact (exists_q_primes hn).choose_spec.2.2.1 _

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
  and
  \[ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/89693}\cdot\frac{1}{n}. \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")]
theorem inv_cube_log_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (log √(n : ℝ)) ^ 3 ≤ 0.000675 := by
  calc
    1 / Real.log √n ^ 3 ≤ 1 / Real.log X₀ ^ 3 := by
      gcongr
      exact Real.le_sqrt_of_sq_le (mod_cast hn)
    _ ≤ _ := by
      grw [← log_X₀_gt.le]
      norm_num

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
  and
  \[ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/89693}\cdot\frac{1}{n}. \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")]
theorem inv_n_pow_3_div_2_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (89693 : ℝ)) * (1 / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := cast_pos.mpr (lt_of_lt_of_le (by grind) hn)
  rw [one_div_mul_one_div, one_div_le_one_div (rpow_pos_of_pos hn_pos _)
    (mul_pos (by norm_num) hn_pos), show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      rpow_add hn_pos, rpow_one, mul_comm, ← sqrt_eq_rpow]
  refine mul_le_mul_of_nonneg_left ?_ hn_pos.le
  have := Real.sqrt_le_sqrt (cast_le.mpr hn)
  simp_all

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
  and
  \[ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/89693}\cdot\frac{1}{n}. \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")
  (discussion := 511)]
theorem inv_n_add_sqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (n + √(n : ℝ)) ≥ (1 / (1 + 1 / (89693 : ℝ))) * (1 / (n : ℝ)) := by
  field_simp
  have : 89693 ≤ √n := by grw [hn]; simp
  linear_combination √n * this + sq_sqrt (cast_nonneg n)

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
    \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i}}\frac{1}{1 + 1/89693}\Bigr)
    \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
    \Bigl(1 - \frac{4 \times 1.000675^{12}}{89693}\varepsilon\Bigr)
    \ge
    1 + 3.36683\varepsilon - 0.01\varepsilon^2.
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
theorem prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
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
    \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i} (1 + \frac{1}{89693})}\Bigr)
    \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
    \Bigl(1 - \frac{4 \times 1.000675^{12}}{89693}\varepsilon\Bigr)
    \ge
    1 + 3.36683\varepsilon - 0.01\varepsilon^2.
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
theorem prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / ((1.000675 : ℝ) ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/89693)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * (1.000675 : ℝ) ^ 12 / 89693 * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]
  nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4]

@[blueprint
  "lem:final-comparison"
  (title := "Final polynomial comparison")
  (statement := /--
  For \(0 \le \varepsilon \le 1/89693^2\), we have
  \[
    1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  This is equivalent to
  \[
    3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 3.36683\varepsilon - 0.01\varepsilon^2,
  \]
  or
  \[
    0 \le (3.36683 - 3.01)\varepsilon - (3.01+0.01)\varepsilon^2 - 1.01\varepsilon^3.
  \]
  Factor out \(\varepsilon\) and use that \(0<\varepsilon \le 1/89693^2\) to check that the
  resulting quadratic in \(\varepsilon\) is nonnegative on this interval.  Again, this is a
  finite computation that can be verified mechanically.
  -/)
  (latexEnv := "lemma")]
theorem final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
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
  (latexEnv := "proposition")
  (discussion := 512)]
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
    have hp' : ((exists_p_primes hn).choose 2 : ℝ) ≤ √n * (1 + 1 / (log √n) ^ 3) ^ 3 := by
      convert (exists_p_primes hn).choose_spec.2.2.1 2 using 2; norm_cast
    have hq' : n * (1 + 1 / (log √n) ^ 3) ^ (-3 : ℝ) ≤ (exists_q_primes hn).choose 0 := by
      convert (exists_q_primes hn).choose_spec.2.2.1 0 using 2
      norm_num
    have hε_pos := hε_pos hn
    have hmid :
        √n * (1 + 1 / (log √n) ^ 3) ^ 3 < n * (1 + 1 / (log √n) ^ 3) ^ (-3 : ℝ) := by
      norm_cast
      norm_num [rpow_neg_one] at *
      rw [← div_eq_mul_inv, lt_div_iff₀ <| pow_pos hε_pos 3]
      have : (1 + ((log √n) ^ 3)⁻¹) ^ 6 < 2 :=
        calc (1 + ((log √n) ^ 3)⁻¹) ^ 6 < (1 + (11 ^ 3 : ℝ)⁻¹) ^ 6 := by gcongr; linarith [hlog hn]
          _ ≤ 2 := by norm_num
      nlinarith [mul_self_sqrt (Nat.cast_nonneg n), hsqrt_ge hn]
    exact_mod_cast hp'.trans_lt <| hmid.trans_le hq'
  h_ord_3 := (exists_q_primes hn).choose_spec.2.2.2
  h_crit := by
    have hn₀ : 0 ≤ Real.log √n := by
      grw [hn]
      simp [log_nonneg]
    have h₁ : 1 - (4 : ℝ) *
        (∏ i, (exists_p_primes hn).choose i : ℝ) / ∏ i, ((exists_q_primes hn).choose i : ℝ) ≥
        1 - 4 * (1 + 0.000675) ^ 12 * ((1 / 89693) * (1 / n)) := by
      grw [pq_ratio_ge hn, inv_cube_log_sqrt_le hn, ← inv_n_pow_3_div_2_le hn]
      simp [field]
    have : 0 ≤ 1 - 4 * (1 + 0.000675 : ℝ) ^ 12 * ((1 / 89693) * (1 / n)) := by
      grw [hn]
      norm_num
    have := this.trans h₁
    have hn' : (0 : ℝ) ≤ 1 / ↑n ∧ (1 : ℝ) / ↑n ≤ 1 / 89693 ^ 2 := ⟨by simp, by grw [hn]; simp⟩
    grw [Lcm.prod_q_ge hn, Lcm.prod_p_ge hn, h₁]
    simp_rw [div_eq_mul_one_div (_ ^ (_ : ℝ) : ℝ) (n : ℝ),
      show 3 / (8 * n : ℝ) = 3 / 8 * (1 / n) by field_simp, ← one_div_mul_one_div]
    grw [inv_cube_log_sqrt_le hn, inv_n_add_sqrt_ge hn]
    set ε : ℝ := 1 / n
    calc
      _ ≤ ∏ i : Fin 3, (1 + (1 + 0.000675 : ℝ) ^ (i + 1 : ℝ) * ε) := by gcongr
      _ = ∏ i : Fin 3, (1 + (1.000675 : ℝ) ^ (i + 1 : ℝ) * ε) := by norm_num [div_eq_mul_inv]
      _ ≤ _ := (prod_epsilon_le (ε := ε) hn')
      _ ≤ _ := final_comparison hn'
      _ ≤ _ := by
        grw [← prod_epsilon_ge hn']
        apply le_of_eq
        simp [field]
        ring_nf

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

blueprint_comment /--
\subsection{Bonus material}

The following result is not needed for this application, but is worth recording nevertheless.
-/

@[blueprint
  "thm:lcm-eq"
  (title := "Formula for log of L equals Chebyshev psi")
  (statement := /-- For every $n$, $\log L_n = \sum_{p \leq n} \lfloor \log n / \log p \rfloor \log p$. -/)
  (proof := /-- Compute the number of times $p$ divides $L_n$ and use the fundamental theorem of arithmetic. -/)
  (latexEnv := "sublemma")]
theorem L_eq_prod (n : ℕ) :
    L n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      p ^ ⌊Real.log n / Real.log p⌋₊ := by
        have h_def : (Finset.Icc 1 n).lcm (fun k => k) = Finset.prod (Finset.filter Nat.Prime (Finset.range (n + 1))) (fun p => p ^ Nat.log p n) := by
          have h_def : (Finset.Icc 1 n).lcm (fun k => k) = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p ^ (Nat.factorization ((Finset.Icc 1 n).lcm (fun k => k))) p := by
            conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( show ( Finset.lcm ( Finset.Icc 1 n ) fun k => k ) ≠ 0 from Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) ] ;
            rw [ Finsupp.prod_of_support_subset ] <;> norm_num [ Finset.subset_iff ];
            exact fun p pp dp => ⟨ pp.dvd_factorial.mp ( dvd_trans dp <| Finset.lcm_dvd fun x hx => Nat.dvd_factorial ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ), pp ⟩;
          have h_vp : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), Nat.factorization ((Finset.Icc 1 n).lcm (fun k => k)) p = Nat.log p n := by
            intro p hp
            have h_vp_eq : Nat.factorization ((Finset.Icc 1 n).lcm (fun k => k)) p = Finset.sup (Finset.Icc 1 n) (fun k => Nat.factorization k p) := by
              have h_vp_eq : ∀ {S : Finset ℕ}, (∀ k ∈ S, k ≠ 0) → Nat.factorization (Finset.lcm S (fun k => k)) p = Finset.sup S (fun k => Nat.factorization k p) := by
                intros S hS_nonzero
                induction' S using Finset.induction with k S hkS ih;
                · simp +decide [ Finset.lcm ];
                · simp_all +decide [ Finset.lcm_insert ];
                  erw [ Nat.factorization_lcm ] <;> simp_all +decide [ GCDMonoid.lcm ];
              exact h_vp_eq fun k hk => by linarith [ Finset.mem_Icc.mp hk ] ;
            refine' le_antisymm _ _ <;> norm_num at *;
            · exact h_vp_eq ▸ Finset.sup_le fun x hx => Nat.le_log_of_pow_le hp.2.one_lt <| by linarith [ Finset.mem_Icc.mp hx, Nat.le_of_dvd ( by linarith [ Finset.mem_Icc.mp hx ] ) ( Nat.ordProj_dvd x p ) ] ;
            · refine' h_vp_eq.symm ▸ le_trans _ ( Finset.le_sup ( f := fun k => k.factorization p ) ( show p ^ Nat.log p n ∈ Finset.Icc 1 n from Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.2.pos, Nat.pow_log_le_self _ <| by linarith [ Nat.Prime.one_lt hp.2 ] ⟩ ) );
              rw [ Nat.factorization_pow ] ; norm_num [ hp.2 ];
          exact h_def.trans ( Finset.prod_congr rfl fun p hp => by rw [ h_vp p hp ] );
        convert h_def using 3;
        rw [ Nat.floor_eq_iff <| by positivity ];
        rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop ), div_lt_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop ) ];
        exact ⟨ by rw [ ← Real.log_pow ] ; exact Real.log_le_log ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) _ ) <| mod_cast Nat.pow_log_le_self _ <| by aesop, by rw [ ← Real.log_rpow ( Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) ] ; exact Real.log_lt_log ( mod_cast Nat.pos_of_ne_zero <| by aesop ) <| mod_cast Nat.lt_pow_succ_log_self ( Nat.Prime.one_lt <| by aesop ) _ ⟩

@[blueprint
  "thm:psi-eq"
  (title := "Formula for Chebyshev psi")
  (statement := /-- For every $n$, $\psi(n) = \sum_{p \leq n} \lfloor \log n / \log p \rfloor \log p$, where $\psi$ is the Chebyshev psi function. -/)
  (proof := /-- Compute the number of times $p$ divides $L_n$ and use the fundamental theorem of arithmetic. -/)
  (latexEnv := "sublemma")]
theorem psi_eq_prod (n : ℕ) :
    Chebyshev.psi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      ⌊Real.log n / Real.log p⌋₊ * Real.log p := by
        unfold Chebyshev.psi;
        have h_vonMangoldt_sum : ∑ m ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), ∑ k ∈ Finset.Icc 1 (Nat.floor (Real.log n / Real.log p)), Real.log p := by
          have h_vonMangoldt_sum : ∑ m ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), Real.log p := by
            have h_sum_vonMangoldt : ∑ m ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt m = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n), ∑ k ∈ Finset.Icc 1 (Nat.log p n), ArithmeticFunction.vonMangoldt (p ^ k) := by
              have h_sum : Finset.filter (fun m => ArithmeticFunction.vonMangoldt m ≠ 0) (Finset.Icc 1 n) = Finset.biUnion (Finset.filter Nat.Prime (Finset.Icc 1 n)) (fun p => Finset.image (fun k => p ^ k) (Finset.Icc 1 (Nat.log p n))) := by
                ext m; simp [ArithmeticFunction.vonMangoldt];
                constructor <;> intro h;
                · rw [ isPrimePow_nat_iff ] at h;
                  rcases h.2.1 with ⟨ p, k, hp, hk, rfl ⟩ ; exact ⟨ p, ⟨ ⟨ hp.pos, by linarith [ Nat.le_of_dvd ( by linarith ) ( dvd_pow_self p hk.ne' ) ] ⟩, hp ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.one_lt ( by linarith ) ⟩, rfl ⟩ ;
                · rcases h with ⟨ p, ⟨ ⟨ hp₁, hp₂ ⟩, hp₃ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩ ; refine' ⟨ ⟨ Nat.one_le_pow _ _ hp₃.pos, _ ⟩, _, _, _, _ ⟩ <;> norm_num [ hp₃.ne_zero, hp₃.ne_one ];
                  · exact Nat.pow_le_of_le_log ( by linarith ) ( by linarith );
                  · exact hp₃.isPrimePow.pow ( by linarith );
                  · exact Nat.ne_of_gt ( Nat.minFac_pos _ );
                  · linarith;
                  · linarith [ show ( p ^ k |> Nat.minFac : ℝ ) ≥ 1 by exact_mod_cast Nat.minFac_pos _ ];
              rw [ ← Finset.sum_subset ( show Finset.filter ( fun m => ArithmeticFunction.vonMangoldt m ≠ 0 ) ( Finset.Icc 1 n ) ⊆ Finset.Icc 1 n from Finset.filter_subset _ _ ) ];
              · rw [ h_sum, Finset.sum_biUnion ];
                · exact Finset.sum_congr rfl fun p hp => by rw [ Finset.sum_image ( by intros a ha b hb hab; exact Nat.pow_right_injective ( Nat.Prime.one_lt ( by aesop ) ) hab ) ] ;
                · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ];
                  intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
              · grind;
            simp_all +decide [ ArithmeticFunction.vonMangoldt ];
            refine' Finset.sum_congr rfl fun p hp => _;
            rw [ Finset.sum_congr rfl fun x hx => if_pos <| ?_ ];
            · rw [ Finset.sum_congr rfl fun x hx => by rw [ Nat.pow_minFac ] ; aesop ] ; aesop;
            · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp hp |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp hx ] );
          convert h_vonMangoldt_sum using 2;
          · ext ( _ | p ) <;> aesop;
          · congr! 2;
            rw [ Nat.floor_eq_iff ( div_nonneg ( Real.log_natCast_nonneg _ ) ( Real.log_natCast_nonneg _ ) ), div_lt_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop ), le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop ) ];
            exact ⟨ by rw [ ← Real.log_pow ] ; exact Real.log_le_log ( pow_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) _ ) <| mod_cast Nat.pow_log_le_self _ <| by aesop, by rw [ ← Real.log_rpow ( Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) ] ; exact Real.log_lt_log ( mod_cast Nat.pos_of_ne_zero <| by aesop ) <| mod_cast Nat.lt_pow_succ_log_self ( Nat.Prime.one_lt <| by aesop ) _ ⟩;
        aesop

@[blueprint
  "thm:lcm-psi"
  (title := "Log of L equals Chebyshev psi")
  (statement := /-- For every $n$, $\log L_n = \psi(n)$, where $\psi$ is the Chebyshev psi function. -/)
  (proof := /-- Combine the previous results. -/)
  (latexEnv := "proposition")]
theorem log_L_eq_psi (n : ℕ) : Real.log (L n) = Chebyshev.psi n := by
  rw [ L_eq_prod ];
  rw [ Nat.cast_prod, Real.log_prod ] <;> norm_num;
  · rw [ psi_eq_prod ];
  · aesop


end Lcm
