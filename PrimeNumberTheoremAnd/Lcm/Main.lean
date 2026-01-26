import Architect
import PrimeNumberTheoremAnd.Lcm.Cert_ChoosePrime_lemmas
import PrimeNumberTheoremAnd.Lcm.ChoosePrime

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
  p := (six_primes.exists_p_primes hn).choose
  q := (six_primes.exists_q_primes hn).choose
  hn := le_trans ChoosePrime_lemmas.one_le_X₀_sq hn
  hp := (six_primes.exists_p_primes hn).choose_spec.1
  hp_mono := (six_primes.exists_p_primes hn).choose_spec.2.1
  hq := (six_primes.exists_q_primes hn).choose_spec.1
  hq_mono := (six_primes.exists_q_primes hn).choose_spec.2.1
  h_ord_1 := (six_primes.exists_p_primes hn).choose_spec.2.2.2
  h_ord_2 := by
    -- Goal: p 2 < q 0
    have hp' : ((six_primes.exists_p_primes hn).choose 2 : ℝ) ≤
        √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ 3 := by
      -- exactly the old `hp'` line, but with δ instead of log^(-3)
      -- (this is the i=2 instance of the choose-p bounds)
      convert (six_primes.exists_p_primes hn).choose_spec.2.2.1 2 using 2
      norm_cast

    have hq' :
        (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ) ≤ (six_primes.exists_q_primes hn).choose 0 := by
      -- i = 0 in the choose-q bounds gives exponent (3 - 0) = 3
      simpa using (six_primes.exists_q_primes hn).choose_spec.2.2.1 (0 : Fin 3)

    have hmid :
        √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ)
          <
        (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ) :=
      ChoosePrime_lemmas.ord2_mid (n := n) hn

    have : ((six_primes.exists_p_primes hn).choose 2 : ℝ) < ((six_primes.exists_q_primes hn).choose 0 : ℝ) :=
      lt_of_le_of_lt hp' (lt_of_lt_of_le hmid hq')

    exact_mod_cast this

  h_ord_3 := (six_primes.exists_q_primes hn).choose_spec.2.2.2

  h_crit := by
    have hratio_nonneg :
        0 ≤
          1 - (4 : ℝ) *
                (∏ i : Fin 3, ((six_primes.exists_p_primes hn).choose i : ℝ))
                / (∏ i : Fin 3, ((six_primes.exists_q_primes hn).choose i : ℝ)) := by
      -- Use pq_ratio_ge (delta-only) + delta_ratio_term_nonneg (Cert)
      have hge :
          1 - (4 : ℝ) *
                (∏ i : Fin 3, ((six_primes.exists_p_primes hn).choose i : ℝ))
                / (∏ i : Fin 3, ((six_primes.exists_q_primes hn).choose i : ℝ))
            ≥
          1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
        -- this is your delta-only pq_ratio_ge
        simpa using (six_primes.pq_ratio_ge (n := n) hn)

      -- convert to ≤ form and chain
      have hle :
          (1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ))
            ≤
          (1 - (4 : ℝ) *
                (∏ i : Fin 3, ((six_primes.exists_p_primes hn).choose i : ℝ))
                / (∏ i : Fin 3, ((six_primes.exists_q_primes hn).choose i : ℝ))) :=
        (show _ ≤ _ from by simpa [ge_iff_le] using hge)

      exact le_trans (ChoosePrime_lemmas.delta_ratio_term_nonneg (n := n) hn) hle
    -- Reduce the prime inequality to the delta-only inequality:
    grw [six_primes.prod_q_ge hn, six_primes.prod_p_ge hn, six_primes.pq_ratio_ge hn]
    -- Now the goal matches the Cert lemma:
    · exact ChoosePrime_lemmas.main_ineq_delta_form (n := n) hn
    · exact ChoosePrime_lemmas.delta_prod_mul_nonneg (n := n) hn

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
