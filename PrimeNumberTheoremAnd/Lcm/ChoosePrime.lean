import Architect
import PrimeNumberTheoremAnd.Lcm.Base
import PrimeNumberTheoremAnd.Lcm.Cert
import PrimeNumberTheoremAnd.Lcm.Cert_ChoosePrime_lemmas

namespace Lcm

open ArithmeticFunction hiding log
open Real Finset Nat
open scoped BigOperators

namespace six_primes

variable [Numerical.PrimeGap_Criterion]

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
  \(x, x(1+gap.δ(x)), x(1+gap.δ(x))^2\), keeping track of the resulting primes and bounds.
  For \(n\) large and \(x = \sqrt{n}\), we have \(\sqrt{n} < p_1\) as soon as the first interval
  lies strictly above \(\sqrt{n}\); this can be enforced by taking \(n\) large enough. -/)
  (latexEnv := "lemma")]
theorem exists_p_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i, p i ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0 := by
  -- define the “base point”
  let x : ℝ := √(n : ℝ)
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [x] using ChoosePrime_lemmas.sqrt_ge_X₀ (n := n) hn
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
    simpa [x, ε] using ChoosePrime_lemmas.step1_ge_X₀ (n := n) hn

  obtain ⟨p₁, hp₁_prime, hp₁_lb, hp₁_ub⟩ :=
    gap.prime_in_Icc (x := x * (1 + ε)) hx1X

  have hp₁_ub' : (p₁ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    -- provider gives `p₁ ≤ (x*(1+ε)) * (1 + δ(x*(1+ε)))`
    -- Cert lemma C6 turns that into `≤ x*(1+ε)^2`
    refine le_trans (by simpa [ε] using hp₁_ub) ?_
    simpa [x, ε] using ChoosePrime_lemmas.step1_upper (n := n) hn

  -- (3) third prime at x*(1+ε)^2
  have hx2X : (X₀ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    simpa [x, ε] using ChoosePrime_lemmas.step2_ge_X₀ (n := n) hn
  obtain ⟨p₂, hp₂_prime, hp₂_lb, hp₂_ub⟩ :=
    gap.prime_in_Icc (x := x * (1 + ε) ^ 2) hx2X

  have hp₂_ub' : (p₂ : ℝ) ≤ x * (1 + ε) ^ 3 := by
    refine le_trans (by simpa [ε] using hp₂_ub) ?_
    simpa [x, ε] using ChoosePrime_lemmas.step2_upper (n := n) hn

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
    q_{4-i} \ge n \Bigl(1 + gap.δ(√{n})\Bigr)^{-i}
  \]
  for \(i = 1,2,3\), and \(q_1 < q_2 < q_3 < n\).
  -/)
  (proof := /-- Apply Theorem~\ref{thm:Dusart} with suitable values of \(x\) slightly below \(n\),
  e.g.\ \(x = n(1+gap.δ(√(n)))^{-i}\), again keeping track of the intervals.  For \(n\) large
  enough, these intervals lie in \((\sqrt{n},n)\) and contain primes \(q_i\) with the desired
  ordering. -/)
  (proofUses := ["thm:Dusart"])
  (latexEnv := "lemma")]
theorem exists_q_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3, (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ ((3 : ℕ) - (i : ℕ)) ≤ q i) ∧
      q 2 < n := by
  let x : ℝ := √(n : ℝ)
  let ε : ℝ := gap.δ x
  let y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3
  let y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2
  let y2 : ℝ := (n : ℝ) / (1 + ε)

  -- apply provider at y0,y1,y2
  have hy0X : (X₀ : ℝ) ≤ y0 := by simpa [x, ε, y0] using Numerical.y0_ge_X₀ (n := n) hn
  have hy1X : (X₀ : ℝ) ≤ y1 := by simpa [x, ε, y1] using Numerical.y1_ge_X₀ (n := n) hn
  have hy2X : (X₀ : ℝ) ≤ y2 := by simpa [x, ε, y2] using Numerical.y2_ge_X₀ (n := n) hn

  obtain ⟨q₀, hq₀_prime, hq₀_lb, hq₀_ub⟩ := gap.prime_in_Icc (x := y0) hy0X
  obtain ⟨q₁, hq₁_prime, hq₁_lb, hq₁_ub⟩ := gap.prime_in_Icc (x := y1) hy1X
  obtain ⟨q₂, hq₂_prime, hq₂_lb, hq₂_ub⟩ := gap.prime_in_Icc (x := y2) hy2X

  -- chain the upper bounds
  have hq₀_ub' : (q₀ : ℝ) ≤ y1 := by
    -- q₀ ≤ y0*(1+δ y0) ≤ y1
    refine le_trans (by simpa [y0] using hq₀_ub) ?_
    simpa [x, ε, y0, y1] using Numerical.y0_mul_one_add_delta_le_y1 (n := n) hn

  have hq₁_ub' : (q₁ : ℝ) ≤ y2 := by
    refine le_trans (by simpa [y1] using hq₁_ub) ?_
    simpa [x, ε, y1, y2] using Numerical.y1_mul_one_add_delta_le_y2 (n := n) hn

  have hq₂_lt_n : q₂ < n := by
    -- q₂ ≤ y2*(1+δ y2) < n
    have hq₂_lt : (q₂ : ℝ) < (n : ℝ) := by
      have : (q₂ : ℝ) ≤ y2 * (1 + gap.δ y2) := by simpa [y2] using hq₂_ub
      exact lt_of_le_of_lt this (by simpa [x, ε, y2] using Numerical.y2_mul_one_add_delta_lt_n (n := n) hn)
    exact Nat.cast_lt.mp hq₂_lt

  -- package as Fin 3 → ℕ and prove StrictMono using lb/ub
  refine ⟨![q₀, q₁, q₂], ?_, ?_, ?_, hq₂_lt_n⟩
  · intro i; fin_cases i <;> assumption
  · refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i; fin_cases i
    · exact Nat.cast_lt.mp (hq₀_ub'.trans_lt hq₁_lb)
    · exact Nat.cast_lt.mp (hq₁_ub'.trans_lt hq₂_lb)
  · intro i
    fin_cases i
    · -- i=0 : y0 ≤ q0
      simpa [y0] using (le_of_lt hq₀_lb)
    · -- i=1 : y1 ≤ q1
      simpa [y1] using (le_of_lt hq₁_lb)
    · -- i=2 : y2 ≤ q2
      simpa [y2] using (le_of_lt hq₂_lb)

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
    \prod_{i=1}^3 \Bigl(1 + \frac{\bigl(1 + gap.δ(√{n})\bigr)^i}{n} \Bigr).
  \end{equation}
  -/)
  (proof := /--
  By Lemma~\ref{lem:choose-qi}, each \(q_i\) is at least
  \[
    n\Bigl(1 + gap.δ(√{n})\Bigr)^{-j}
  \]
  for suitable indices \(j\), so \(1/q_i\) is bounded above by
  \[
    \frac{\bigl(1 + gap.δ(√{n})\bigr)^i}{n}
  \]
  after reindexing. Multiplying the three inequalities gives \eqref{eq:qi-upper}.
  -/)
  (proofUses := ["lem:choose-qi"])
  (latexEnv := "lemma")]
theorem prod_q_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) / (exists_q_primes hn).choose i) ≤
      ∏ i : Fin 3, (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / n) := by
  -- introduce the Cert abbreviation locally (purely for readability)
  -- (this does *not* change the theorem statement)
  have hb : (1 + gap.δ (√(n : ℝ))) = Numerical.b n := by
    simp [Numerical.b]

  -- Reindex RHS to match the `exists_q_primes` exponent pattern `((3 : ℝ) - (i : ℕ))`.
  -- After rewriting, all the bounds line up directly.
  -- First rewrite RHS into the `b n` form:
  -- (we do it as a `simp` rewrite so later `prod_q_rhs_reindex` applies cleanly)
  have :
      (∏ i : Fin 3, (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / n))
        =
      (∏ i : Fin 3, (1 + (Numerical.b n) ^ ((i : ℕ) + 1 : ℝ) / n)) := by
    simp [Numerical.b]
  -- use it
  rw [this]
  -- now reindex via Cert lemma
  rw [Numerical.prod_q_rhs_reindex (n := n)]

  -- pointwise compare factors and multiply
  apply Finset.prod_le_prod (fun _ _ => by positivity)
  intro i _
  -- target: `1 + 1/q_i ≤ 1 + (b n)^((3:ℝ)-(i:ℕ))/n`
  suffices
      (1 : ℝ) / (exists_q_primes hn).choose i ≤ (Numerical.b n) ^ ((3 : ℝ) - (i : ℕ)) / n by
    linarith

  -- Extract the lower bound on `q_i` from `exists_q_primes`
  have hq_lower :
      (n : ℝ) * (Numerical.b n) ^ (-((3 : ℝ) - (i : ℕ))) ≤ ((exists_q_primes hn).choose i : ℝ) := by
    -- `choose_spec.2.2.1` is the lower-bound field of `exists_q_primes`.
    -- We just rewrite `n / (1+δ)^k` as `n * (b n)^(-k)` (for k = 3,2,1).
    classical
    have hb_pos : 0 < Numerical.b n := Numerical.b_pos (n := n) hn
    -- `i : Fin 3`, so `((3 : ℝ) - (i : ℕ))` is one of `3,2,1`.
    fin_cases i
    · have hx : ((0 : ℝ) - 3) = (-3 : ℝ) := by norm_num
      simpa [hx, Numerical.b, div_eq_mul_inv, Real.rpow_neg hb_pos.le, Real.rpow_natCast] using
        (exists_q_primes hn).choose_spec.2.2.1 (i := (0 : Fin 3))
    · have hx : ((1 : ℝ) - 3) = (-2 : ℝ) := by norm_num
      simpa [hx, Numerical.b, div_eq_mul_inv, Real.rpow_neg hb_pos.le, Real.rpow_natCast] using
        (exists_q_primes hn).choose_spec.2.2.1 (i := (1 : Fin 3))
    · have hx : ((2 : ℝ) - 3) = (-1 : ℝ) := by norm_num
      simpa [hx, Numerical.b, div_eq_mul_inv, Real.rpow_neg hb_pos.le, Real.rpow_natCast] using
        (exists_q_primes hn).choose_spec.2.2.1 (i := (2 : Fin 3))

  -- Convert that to a reciprocal upper bound using the Cert lemma
  have hinv :
      (1 : ℝ) / ((exists_q_primes hn).choose i : ℝ) ≤ (Numerical.b n) ^ ((3 : ℝ) - (i : ℕ)) / n := by
    exact Numerical.inv_le_rpow_div_of_lower_bound (hn := hn) (t := (3 : ℝ) - (i : ℕ))
      (q := (exists_q_primes hn).choose i) hq_lower

  -- finish (remove explicit casts)
  simpa using hinv


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
      1 + \frac{1}{\bigl(1 + gap.δ(√{n})\bigr)^{2i} (n + √n)}
    \Bigr).
  \end{equation}
  -/)
  (proof := /--
  By Lemma~\ref{lem:choose-pi}, \(p_i \le \sqrt{n} (1+gap.δ(√{n}))^i\).  Hence
  \[
    p_i^2 \le n\bigl(1 + gap.δ(√{n})\bigr)^{2i}
  \quad\text{and}\quad
    p_i+1 \le p_i(1 + 1/\sqrt{n}) \le (1+1/\sqrt{n}) p_i.
  \]
  From these one gets
  \[
    p_i(p_i+1) \le \bigl(1 + gap.δ(√{n})\bigr)^{2i} (n + \sqrt{n}),
  \]
  and hence
  \[
    \frac{1}{p_i(p_i+1)} \ge
    \frac{1}{\bigl(1 + gap.δ(√{n})\bigr)^{2i} (n + \sqrt{n})}.
  \]
  Taking \(1+\cdot\) and multiplying over \(i=1,2,3\) gives \eqref{eq:pi-lower}.
  -/)
  (latexEnv := "lemma")]
theorem prod_p_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) /
        ((exists_p_primes hn).choose i * ((exists_p_primes hn).choose i + 1))) ≥
      ∏ i : Fin 3,
        (1 + 1 / ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))) := by
  -- goal `LHS ≥ RHS` is definitionaly `RHS ≤ LHS`
  refine Finset.prod_le_prod
    (fun i _ => by
      have hB : 0 < (1 + gap.δ (√(n : ℝ))) := Numerical.one_add_delta_pos (n := n) hn
      positivity [hB])
    (fun i _ => by
      -- i is already in context; no `intro` needed

      -- abbreviate the chosen primes
      let p : Fin 3 → ℕ := (exists_p_primes hn).choose

      -- collect the hypotheses needed by the Cert lemma
      have hp_prime : ∀ j, Nat.Prime (p j) := by
        intro j
        simpa [p] using (exists_p_primes hn).choose_spec.1 j

      have hp_mono : StrictMono p := by
        simpa [p] using (exists_p_primes hn).choose_spec.2.1

      have hp_ub :
          ∀ j, (p j : ℝ) ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (j + 1 : ℝ) := by
        intro j
        simpa [p] using (exists_p_primes hn).choose_spec.2.2.1 j

      have hsqrt_lt_p0 : √(n : ℝ) < p 0 := by
        simpa [p] using (exists_p_primes hn).choose_spec.2.2.2

      -- denominator comparison (this is the “real content”; all plumbing is in Cert)
      have hden :
          ((p i * (p i + 1) : ℕ) : ℝ)
            ≤ (1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n) := by
        simpa [p] using
          Numerical.p_mul_padd1_le_bound (hn := hn)
            (p := p) hp_ub i

      -- turn denominator inequality into the desired factor inequality
      have hpos : 0 < ((p i * (p i + 1) : ℕ) : ℝ) := by
        have hpipos : 0 < (p i) := (hp_prime i).pos
        -- `p i * (p i + 1)` is positive in ℕ, hence in ℝ
        positivity [hpipos]

      have hinv :
          (1 : ℝ) / ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))
            ≤ (1 : ℝ) / ((p i * (p i + 1) : ℕ) : ℝ) := by
        -- if a ≤ b and a>0 then 1/b ≤ 1/a
        exact one_div_le_one_div_of_le hpos hden

      -- add 1 to both sides
      have := add_le_add_left hinv 1
      -- rewrite the RHS denominator back to the form that appears in the goal
      simpa [p, Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm,
        mul_assoc, mul_comm, mul_left_comm] using this
    )

@[blueprint
  "lem:pq-ratio"
  (title := "Lower bound for the product ratio \\(p_i/q_i\\)")
  (statement := /--
  With \(p_i,q_i\) as in Lemmas~\ref{lem:choose-pi} and \ref{lem:choose-qi}, we have
  \begin{equation}\label{eq:pq-ratio}
    1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}
    \ge
    1 - \frac{4 \bigl(1 + gap.δ(√{n})\bigr)^{12}}{n^{3/2}}.
  \end{equation}
  -/)
  (proof := /--
  We have \(p_i \le \sqrt{n} (1+gap.δ(√{n}))^i\), so
  \[
    p_1 p_2 p_3 \le n^{3/2} \bigl(1 + gap.δ(√{n})\bigr)^{6}.
  \]
  Similarly, \(q_i \ge n(1+gap.δ(√{n}))^{-i}\), so
  \[
    q_1 q_2 q_3 \ge n^3 \bigl(1 + gap.δ(√{n})\bigr)^{-6}.
  \]
  Combining,
  \[
    \frac{p_1 p_2 p_3}{q_1 q_2 q_3} \le
    \frac{n^{3/2} \bigl(1 + gap.δ(√{n})\bigr)^{6}}{n^3
    \bigl(1 + gap.δ(√{n})\bigr)^{-6}}
    = \frac{\bigl(1 + gap.δ(√{n})\bigr)^{12}}{n^{3/2}}.
  \]
  This implies \eqref{eq:pq-ratio}.
  -/)
  (latexEnv := "lemma")
  (discussion := 534)]
theorem pq_ratio_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 - ((4 : ℝ) * ∏ i, ((exists_p_primes hn).choose i : ℝ))
        / ∏ i, ((exists_q_primes hn).choose i : ℝ) ≥
    1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  -- Reduce to proving the fraction is bounded above, then use antitonicity of `1 - ·`.
  have hnpos : (0 : ℝ) < (n : ℝ) := Numerical.n_pos (n := n) hn
  have hbpos : 0 < (1 + gap.δ (√(n : ℝ))) := Numerical.one_add_delta_pos (n := n) hn

  have hfrac :
      ((4 : ℝ) * ∏ i, ((exists_p_primes hn).choose i : ℝ))
        / ∏ i, ((exists_q_primes hn).choose i : ℝ)
        ≤
      4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    -- Rewrite the RHS into a product ratio that matches the pointwise `p`/`q` bounds.
    rw [Numerical.pq_ratio_rhs_as_fraction (n := n) hn]
    gcongr <;> try
    (first
      | exact (exists_p_primes hn).choose_spec.2.2.1 _
      | exact (exists_q_primes hn).choose_spec.2.2.1 _
      -- | (refine Finset.prod_nonneg ?_; intro; intro; positivity [hbpos])
      -- | (refine Finset.prod_pos ?_; intro; intro; positivity [hnpos, hbpos])
      -- | (refine Finset.prod_pos ?_; intro; intro; exact_mod_cast ((exists_q_primes hn).choose_spec.1 _).pos)
    )
  -- Convert `A ≤ B` into `1 - A ≥ 1 - B`.
  have hsub :
      1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
        ≤
      1 - ((4 : ℝ) * ∏ i, ((exists_p_primes hn).choose i : ℝ))
            / ∏ i, ((exists_q_primes hn).choose i : ℝ) :=
    sub_le_sub_left hfrac 1

  -- goal is the same inequality but written with `≥`
  simpa [ge_iff_le] using hsub



end six_primes
end Lcm
