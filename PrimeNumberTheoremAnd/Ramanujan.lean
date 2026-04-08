import PrimeNumberTheoremAnd.Defs
import LeanCert.Engine.ChebyshevTheta
import PrimeNumberTheoremAnd.SecondarySummary
import PrimeNumberTheoremAnd.RamanujanCalculations

blueprint_comment /--
\section{Ramanujan's inequality}\label{ramanujan-sec}

Use of prime number theorems to establish Ramanujan's inequality
$$\pi(x)^2 < \frac{e x}{\log x} \pi\Big(\frac{x}{e}\Big)$$
for sufficiently large $x$, following \cite{dudek-platt}.
-/

namespace Ramanujan


open Real Set MeasureTheory intervalIntegral Chebyshev

noncomputable def ε (M x : ℝ) : ℝ := 72 + 2 * M + (2 * M + 132) / log x + (4 * M + 288) / (log x)^2 + (12 * M + 576) / (log x)^3 + (48 * M) / (log x)^4 + (M^2) / (log x)^5

noncomputable def ε' (m x : ℝ) : ℝ := 206 + m + 364 / log x + 381 / (log x)^2 + 238 / (log x)^3 + 97 / (log x)^4 + 30 / (log x)^5 + 8 / (log x)^6

-- noncomputable def x' (m M x : ℝ) : ℝ := exp (ε M x - ε' m x)

@[blueprint
  "ramanujan-criterion-1"
  (title := "Criterion for Ramanujan's inequality, substep 1")
  (statement := /--
Let $M_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$
Then for $x > x_a$ we have
\begin{equation} \label{pipi}
\pi^2(x)  <  x^2 \Big\{ \frac{1}{\log^2 x}+ \frac{2}{\log^3 x}+ \frac{5}{\log^4 x}+ \frac{16}{\log^5 x}+ \frac{64}{\log^6 x} + \frac{\epsilon_{M_a}(x)}{\log^7 x} \Big\}
\end{equation}
%
where
$$\epsilon_{M_a} (x) = 72 + 2 M_a + \frac{2M_a+132}{\log x} + \frac{4M_a+288}{\log^2 x} + \frac{12 M_a+576}{\log^3 x}+\frac{48M_a}{\log^4 x} + \frac{M_a^2}{\log^5 x}.$$
(cf. \cite[Lemma 2.1]{dudek-platt})
-/)
  (proof := /-- Direct calculation -/)
  (latexEnv := "sublemma")
  (discussion := 983)]
theorem sq_pi_lt (M_a x_a : ℝ) (hupper : ∀ x > x_a, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) :
    ∀ x > x_a, pi x ^ 2 < x ^ 2 * (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 64 / log x ^ 6 + ε M_a x / log x ^ 7) := by
  intro x hx
  have sq_algebra (M l : ℝ) : ((Nat.factorial 0 : ℝ) / l ^ 1 + (Nat.factorial 1 : ℝ) / l ^ 2 + (Nat.factorial 2 : ℝ) / l ^ 3 + (Nat.factorial 3 : ℝ) / l ^ 4 + (Nat.factorial 4 : ℝ) / l ^ 5 + M / l ^ 6) ^ 2
    = 1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 64 / l ^ 6 + (72 + 2 * M + (2 * M + 132) / l + (4 * M + 288) / l ^ 2 + (12 * M + 576) / l ^ 3 + (48 * M) / l ^ 4 + M ^ 2 / l ^ 5) / l ^ 7 := by
    norm_num
    ring
  have h_nonneg_pi : 0 ≤ pi x := by
    unfold _root_.pi
    exact_mod_cast Nat.zero_le (⌊x⌋₊.primeCounting)
  have h_pos_rhs : 0 < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) := by
    linarith [h_nonneg_pi, hupper x hx]
  have h_sum_eq : ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) = (Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have h_main1 : ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) ^ 2 = 1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 64 / log x ^ 6 + ε M_a x / log x ^ 7 := by
    simpa [ε] using sq_algebra M_a (log x)
  have h_eq : x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) := by
    rw [h_sum_eq]; ring
  have h1'' : pi x < x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) := by
    simpa only [h_eq] using hupper x hx
  have h_pos1 : 0 < x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) := by
    simpa only [h_eq] using h_pos_rhs
  have h2 : pi x ^ 2 < (x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6)) ^ 2 :=
    sq_lt_sq.mpr (by simpa only [abs_of_nonneg h_nonneg_pi, abs_of_pos h_pos1] using h1'')
  have h4 : (x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6)) ^ 2 = x ^ 2 * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) ^ 2 := by ring
  simpa only [h4, h_main1] using h2

noncomputable def εneg (m xₐ x : ℝ) : ℝ :=
  206 + (1 + 1 / log xₐ)^6 * m
    + 364 / log x
    + 381 / (log x)^2
    + 238 / (log x)^3
    + 97  / (log x)^4
    + 30  / (log x)^5
    + 8   / (log x)^6

noncomputable def εlower (m xₐ x : ℝ) : ℝ :=
  if 0 ≤ m then ε' m x else εneg m xₐ x

private lemma shift_factorial_lower
    (l : ℝ) (hl : 1 < l) :
    1 / l * (
      1 / (l - 1) + 1 / (l - 1)^2 + 2 / (l - 1)^3
      + 6 / (l - 1)^4 + 24 / (l - 1)^5)
    ≥
    1 / l^2 + 2 / l^3 + 5 / l^4 + 16 / l^5 + 65 / l^6
      + (206 + 364 / l + 381 / l^2 + 238 / l^3
          + 97 / l^4 + 30 / l^5 + 8 / l^6) / l^7 := by
  have hl0 : 0 < l := by linarith
  have hlm1 : 0 < l - 1 := by linarith
  have hdiff :
      1 / l *
          (1 / (l - 1) + 1 / (l - 1) ^ 2 + 2 / (l - 1) ^ 3 + 6 / (l - 1) ^ 4 + 24 / (l - 1) ^ 5)
        - (1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 65 / l ^ 6 +
            (206 + 364 / l + 381 / l ^ 2 + 238 / l ^ 3 + 97 / l ^ 4 + 30 / l ^ 5 + 8 / l ^ 6) / l ^ 7)
      =
        (153 * (l - 1) ^ 10 + 1484 * (l - 1) ^ 9 + 6249 * (l - 1) ^ 8 + 14886 * (l - 1) ^ 7 +
          22027 * (l - 1) ^ 6 + 21083 * (l - 1) ^ 5 + 13345 * (l - 1) ^ 4 + 5701 * (l - 1) ^ 3 +
          1658 * (l - 1) ^ 2 + 294 * (l - 1) + 24) / (l ^ 13 * (l - 1) ^ 5) := by
    field_simp [hl0.ne', hlm1.ne']
    ring
  have hnum_nonneg :
      0 ≤
        153 * (l - 1) ^ 10 + 1484 * (l - 1) ^ 9 + 6249 * (l - 1) ^ 8 + 14886 * (l - 1) ^ 7 +
          22027 * (l - 1) ^ 6 + 21083 * (l - 1) ^ 5 + 13345 * (l - 1) ^ 4 + 5701 * (l - 1) ^ 3 +
          1658 * (l - 1) ^ 2 + 294 * (l - 1) + 24 := by
    positivity
  have hden_pos : 0 < l ^ 13 * (l - 1) ^ 5 := by positivity
  have hdelta_nonneg :
      0 ≤
        1 / l *
            (1 / (l - 1) + 1 / (l - 1) ^ 2 + 2 / (l - 1) ^ 3 + 6 / (l - 1) ^ 4 + 24 / (l - 1) ^ 5)
          - (1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 65 / l ^ 6 +
              (206 + 364 / l + 381 / l ^ 2 + 238 / l ^ 3 + 97 / l ^ 4 + 30 / l ^ 5 + 8 / l ^ 6) / l ^ 7) := by
    rw [hdiff]
    exact div_nonneg hnum_nonneg hden_pos.le
  linarith

private lemma shift_m_lower_of_nonpos
    (m xₐ l : ℝ)
    (hm : m ≤ 0)
    (hxₐ : 0 < log xₐ)
    (hl : log xₐ + 1 ≤ l) :
    m / (l * (l - 1)^6) ≥ ((1 + 1 / log xₐ)^6 * m) / l^7 := by
  have hxₐ_nonneg : 0 ≤ log xₐ := by linarith
  have hlm1_pos : 0 < l - 1 := by linarith
  have hl_pos : 0 < l := by linarith
  have hbase :
      l / (l - 1) ≤ 1 + 1 / log xₐ := by
    have hlog_le : log xₐ ≤ l - 1 := by linarith
    have h_inv : 1 / (l - 1) ≤ 1 / log xₐ :=
      one_div_le_one_div_of_le hxₐ hlog_le
    have hsum : 1 + 1 / (l - 1) ≤ 1 + 1 / log xₐ := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left h_inv 1
    have hratio : l / (l - 1) = 1 + 1 / (l - 1) := by
      field_simp [hlm1_pos.ne']
      ring
    simpa [hratio] using hsum
  have hpow :
      (l / (l - 1)) ^ 6 ≤ (1 + 1 / log xₐ) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hbase 6
  have hm_div_nonpos : m / l ^ 7 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hm (pow_nonneg hl_pos.le _)
  have hmul :
      (m / l ^ 7) * (1 + 1 / log xₐ) ^ 6 ≤ (m / l ^ 7) * (l / (l - 1)) ^ 6 :=
    mul_le_mul_of_nonpos_left hpow hm_div_nonpos
  have hleft :
      m / (l * (l - 1) ^ 6) = (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    field_simp [hl_pos.ne', hlm1_pos.ne']
  have hright :
      ((1 + 1 / log xₐ) ^ 6 * m) / l ^ 7 = (m / l ^ 7) * (1 + 1 / log xₐ) ^ 6 := by
    ring
  rw [hleft, hright]
  exact hmul

theorem ex_pi_gt_neg
    (m xₐ : ℝ)
    (hm : m ≤ 0)
    (hxₐ : 1 < xₐ)
    (hlower : ∀ x > xₐ,
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (m * x / log x ^ 6) < pi x) :
    ∀ x > exp 1 * xₐ,
      exp 1 * x / log x * pi (x / exp 1) >
        x ^ 2 * (
          1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5
          + 65 / log x ^ 6 + εneg m xₐ x / log x ^ 7) := by
  intro x hx
  have hxe : exp 1 < x := by
    have h1 : exp 1 ≤ exp 1 * xₐ := by
      nlinarith [hxₐ, exp_pos (1 : ℝ)]
    grind
  have hlog_gt1 : 1 < log x := by
    have hlog := log_lt_log (show 0 < exp 1 by positivity) hxe
    simpa using hlog
  have hlog_pos : 0 < log x := by linarith
  have hx_pos : 0 < x := lt_trans (exp_pos 1) hxe
  have hy_gt : x / exp 1 > xₐ := by
    have hmul : xₐ * exp 1 < x := by simpa [mul_comm] using hx
    exact (lt_div_iff₀ (exp_pos 1)).2 hmul
  have hlow := hlower (x / exp 1) hy_gt
  have hmul_pos : 0 < exp 1 * x / log x :=
    div_pos (mul_pos (exp_pos 1) hx_pos) hlog_pos
  have hmul := mul_lt_mul_of_pos_left hlow hmul_pos
  have hlog_div : log (x / exp 1) = log x - 1 := by
    rw [log_div (show x ≠ 0 by linarith) (show exp 1 ≠ 0 by positivity), log_exp]
  have hfrom0 :
      exp 1 * x / log x *
        ((x / exp 1) * ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
          + (m * (x / exp 1) / (log x - 1) ^ 6))
      < exp 1 * x / log x * pi (x / exp 1) := by
    simpa [hlog_div] using hmul
  let S : ℝ := ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
  have hfrom :
      x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6))
      < exp 1 * x / log x * pi (x / exp 1) := by
    have hleft :
        exp 1 * x / log x * ((x / exp 1) * S + (m * (x / exp 1) / (log x - 1) ^ 6))
        = x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6)) := by
      field_simp [hlog_pos.ne', show (exp 1 : ℝ) ≠ 0 by positivity]
    simpa [S, hleft] using hfrom0
  have hsum :
      S =
        1 / (log x - 1) + 1 / (log x - 1) ^ 2 + 2 / (log x - 1) ^ 3 +
        6 / (log x - 1) ^ 4 + 24 / (log x - 1) ^ 5 := by
    dsimp [S]
    simp [Finset.sum_range_succ, Nat.factorial]
  have hfac :
      (1 / log x) * S
      ≥
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
            30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7 := by
    simpa [hsum] using shift_factorial_lower (log x) hlog_gt1
  have hxₐ_log_pos : 0 < log xₐ := log_pos hxₐ
  have hlogxₐ_le : log xₐ + 1 ≤ log x := by
    have hmul : exp 1 * xₐ < x := by simpa [mul_comm] using hx
    have hlog := log_lt_log (show 0 < exp 1 * xₐ by positivity) hmul
    have hlog_mul : log (exp 1 * xₐ) = log xₐ + 1 := by
      rw [log_mul (by positivity) (by positivity), log_exp]
      ring
    linarith
  have hmterm :
      m / (log x * (log x - 1) ^ 6)
      ≥ ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7 := by
    simpa using shift_m_lower_of_nonpos m xₐ (log x) hm hxₐ_log_pos hlogxₐ_le
  have hcore :
      (1 / log x) * (S + m / (log x - 1) ^ 6)
      ≥
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + εneg m xₐ x / log x ^ 7 := by
    have hsplit :
        (1 / log x) * (S + m / (log x - 1) ^ 6)
        = (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := by
      calc
        (1 / log x) * (S + m / (log x - 1) ^ 6)
            = (1 / log x) * S + (1 / log x) * (m / (log x - 1) ^ 6) := by ring
        _ = (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := by
          field_simp [hlog_pos.ne']
    have hfac' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
        ≤ (1 / log x) * S :=
      hfac
    have hmterm' :
        ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7
        ≤ m / (log x * (log x - 1) ^ 6) :=
      hmterm
    have hsum' := add_le_add hfac' hmterm'
    have hsum'' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7
        ≤ (1 / log x) * (S + m / (log x - 1) ^ 6) := by
      calc
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7
            ≤ (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := hsum'
        _ = (1 / log x) * (S + m / (log x - 1) ^ 6) := by
          symm
          exact hsplit
    have hsum''' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            εneg m xₐ x / log x ^ 7
          ≤ (1 / log x) * (S + m / (log x - 1) ^ 6) := by
      calc
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            εneg m xₐ x / log x ^ 7
            =
              1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
                (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
                  30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
                + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7 := by
                  simp [εneg]
                  ring
        _ ≤ (1 / log x) * (S + m / (log x - 1) ^ 6) := hsum''
    exact hsum'''
  have htarget_le :
      x ^ 2 *
          (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            εneg m xₐ x / log x ^ 7)
      ≤ x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6)) :=
    mul_le_mul_of_nonneg_left hcore (sq_nonneg x)
  grind

private lemma shift_m_lower_of_nonneg
    (m l : ℝ)
    (hm : 0 ≤ m)
    (hl : 1 < l) :
    m / (l * (l - 1) ^ 6) ≥ m / l ^ 7 := by
  have hl0 : 0 < l := by linarith
  have hlm1 : 0 < l - 1 := by linarith
  have hratio_ge1 : 1 ≤ l / (l - 1) := by
    have hratio : l / (l - 1) = 1 + 1 / (l - 1) := by
      field_simp [hlm1.ne']
      ring
    have hnonneg : 0 ≤ 1 / (l - 1) := by positivity
    linarith
  have hpow : 1 ≤ (l / (l - 1)) ^ 6 := one_le_pow₀ hratio_ge1
  have hmdiv_nonneg : 0 ≤ m / l ^ 7 :=
    div_nonneg hm (pow_nonneg hl0.le _)
  have hmul : m / l ^ 7 ≤ (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_left hpow hmdiv_nonneg
  have hrepr : m / (l * (l - 1) ^ 6) = (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    field_simp [hl0.ne', hlm1.ne']
  rw [hrepr]
  exact hmul

theorem ex_pi_gt_nonneg
    (m_a x_a : ℝ)
    (hm : 0 ≤ m_a)
    (hlower : ∀ x > x_a,
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (m_a * x / log x ^ 6) < pi x) :
    ∀ x > exp 1 * x_a,
      exp 1 * x / log x * pi (x / exp 1) >
        x ^ 2 * (
          1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5
          + 65 / log x ^ 6 + ε' m_a x / log x ^ 7) := by
  intro x hx
  have hxa_ge_one : 1 ≤ x_a := by
    by_contra hxa
    have hlt : x_a < 1 := lt_of_not_ge hxa
    have hbad := hlower 1 hlt
    have hpi1 : pi 1 = 0 := by
      unfold _root_.pi
      norm_num
    have hleft0 :
        (1 : ℝ) * ∑ k ∈ Finset.range 5, (k.factorial / log (1 : ℝ) ^ (k + 1))
          + (m_a * (1 : ℝ) / log (1 : ℝ) ^ 6) = 0 := by
      norm_num
    linarith
  have hxe : exp 1 < x := by
    have h1 : exp 1 ≤ exp 1 * x_a := by
      nlinarith [hxa_ge_one, exp_pos (1 : ℝ)]
    grind
  have hlog_gt1 : 1 < log x := by
    have hlog := log_lt_log (show 0 < exp 1 by positivity) hxe
    simpa using hlog
  have hlog_pos : 0 < log x := by linarith
  have hx_pos : 0 < x := lt_trans (exp_pos 1) hxe
  have hy_gt : x / exp 1 > x_a := by
    have hmul : x_a * exp 1 < x := by simpa [mul_comm] using hx
    exact (lt_div_iff₀ (exp_pos 1)).2 hmul
  have hlow := hlower (x / exp 1) hy_gt
  have hmul_pos : 0 < exp 1 * x / log x :=
    div_pos (mul_pos (exp_pos 1) hx_pos) hlog_pos
  have hmul := mul_lt_mul_of_pos_left hlow hmul_pos
  have hlog_div : log (x / exp 1) = log x - 1 := by
    rw [log_div (show x ≠ 0 by linarith) (show exp 1 ≠ 0 by positivity), log_exp]
  have hfrom0 :
      exp 1 * x / log x *
        ((x / exp 1) * ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
          + (m_a * (x / exp 1) / (log x - 1) ^ 6))
      < exp 1 * x / log x * pi (x / exp 1) := by
    simpa [hlog_div] using hmul
  let S : ℝ := ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
  have hfrom :
      x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6))
      < exp 1 * x / log x * pi (x / exp 1) := by
    have hleft :
        exp 1 * x / log x * ((x / exp 1) * S + (m_a * (x / exp 1) / (log x - 1) ^ 6))
        = x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6)) := by
      field_simp [hlog_pos.ne', show (exp 1 : ℝ) ≠ 0 by positivity]
    simpa [S, hleft] using hfrom0
  have hsum :
      S =
        1 / (log x - 1) + 1 / (log x - 1) ^ 2 + 2 / (log x - 1) ^ 3 +
        6 / (log x - 1) ^ 4 + 24 / (log x - 1) ^ 5 := by
    dsimp [S]
    simp [Finset.sum_range_succ, Nat.factorial]
  have hfac :
      (1 / log x) * S
      ≥
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
            30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7 := by
    simpa [hsum] using shift_factorial_lower (log x) hlog_gt1
  have hmterm :
      m_a / (log x * (log x - 1) ^ 6)
      ≥ m_a / log x ^ 7 := by
    simpa using shift_m_lower_of_nonneg m_a (log x) hm hlog_gt1
  have hcore65 :
      (1 / log x) * (S + m_a / (log x - 1) ^ 6)
      ≥
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + ε' m_a x / log x ^ 7 := by
    have hsplit :
        (1 / log x) * (S + m_a / (log x - 1) ^ 6)
        = (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := by
      calc
        (1 / log x) * (S + m_a / (log x - 1) ^ 6)
            = (1 / log x) * S + (1 / log x) * (m_a / (log x - 1) ^ 6) := by ring
        _ = (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := by
          field_simp [hlog_pos.ne']
    have hfac' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
        ≤ (1 / log x) * S :=
      hfac
    have hmterm' :
        m_a / log x ^ 7 ≤ m_a / (log x * (log x - 1) ^ 6) :=
      hmterm
    have hsum' := add_le_add hfac' hmterm'
    have hsum'' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + m_a / log x ^ 7
        ≤ (1 / log x) * (S + m_a / (log x - 1) ^ 6) := by
      calc
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + m_a / log x ^ 7
            ≤ (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := hsum'
        _ = (1 / log x) * (S + m_a / (log x - 1) ^ 6) := by
          symm
          exact hsplit
    have hsum''' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + ε' m_a x / log x ^ 7
        ≤ (1 / log x) * (S + m_a / (log x - 1) ^ 6) := by
      calc
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + ε' m_a x / log x ^ 7
            =
              1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
                + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
                    30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
                + m_a / log x ^ 7 := by
                  simp [ε']
                  ring
        _ ≤ (1 / log x) * (S + m_a / (log x - 1) ^ 6) := hsum''
    exact hsum'''
  have htarget_le :
      x ^ 2 *
          (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            ε' m_a x / log x ^ 7)
      ≤ x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6)) :=
    mul_le_mul_of_nonneg_left hcore65 (sq_nonneg x)
  grind
@[blueprint
  "ramanujan-criterion-2"
  (title := "Criterion for Ramanujan's inequality, substep 2")
  (statement := /--
Let $m_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$\pi(x) > x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{m_a x}{\log^6 x}.$$
Then for $x > e x_a$ we have
$$\frac{ex}{\log x} \pi \Big(\frac{x}{e} \Big) > x^2 \Big\{ \frac{1}{\log^2 x}+ \frac{2}{\log^3 x}+ \frac{5}{\log^4 x}+ \frac{16}{\log^5 x}+ \frac{64}{\log^6 x} + \frac{\epsilon'_{m_a}(x)}{\log^7 x} \Big\},$$
where
$$\epsilon'_{m_a}(x) = 206+m_a+\frac{364}{\log x} + \frac{381}{\log^2 x}+\frac{238}{\log^3 x} + \frac{97}{\log^4 x} + \frac{30}{\log^5 x} + \frac{8}{\log^6 x}.$$
-/)
  (proof := /-- We have
$$\frac{ex}{\log x} \pi \Big(\frac{x}{e} \Big) > \frac{x^2}{\log x} \Big( \sum_{k=0}^{4} \frac{k!}{(\log x - 1)^{k+1}}\Big) + \frac{m_a x}{(\log x-1)^{6}}$$
Substituting
\begin{eqnarray*}
\frac{1}{(\log x - 1)^{k+1}} & = & \frac{1}{\log^{k+1} x} \Big(1+ \frac{1}{\log x} + \frac{1}{\log^2 x} + \frac{1}{\log^3 x} + \cdots \Big)^{k+1} \\ \\
& > & \frac{1}{\log^{k+1} x} \Big(1+ \frac{1}{\log x}+ \cdots + \frac{1}{\log^{5-k} x} \Big)^{k+1}
\end{eqnarray*}
we obtain the claim.
  -/)
  (latexEnv := "sublemma")
  (discussion := 984)]
theorem ex_pi_gt (m_a x_a : ℝ) (hx_a : 1 < x_a)
    (hlower : ∀ x > x_a, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) < pi x) :
    ∀ x > exp 1 * x_a,
      exp 1 * x / log x * pi (x / exp 1) >
        x ^ 2 *
          (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            εlower m_a x_a x / log x ^ 7) := by
  by_cases hm : 0 ≤ m_a
  · intro x hx
    have hpos := ex_pi_gt_nonneg m_a x_a hm hlower x hx
    simpa [εlower, hm] using hpos
  · intro x hx
    have hneg := ex_pi_gt_neg m_a x_a (le_of_not_ge hm) hx_a hlower x hx
    simpa [εlower, hm] using hneg

@[blueprint
  "ramanujan-criterion"
  (title := "Criterion for Ramanujan's inequality")
  (statement := /-- \cite[Lemma 2.1]{dudek-platt}
Let $m_a, M_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$ x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+ \frac{m_a x}{\log^6 x} < \pi(x)$$

and for $x > ex_a$ one has
$$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$
%
Then Ramanujan's inequality is true for $x > x_0$ if

$$x_0 ≥ e x_{a}$$
and
$$ \epsilon_{M_a} (x_0) - \epsilon'_{m_a}(x_0) < \log x.$$
 -/)
  (proof := /-- Combine the previous two sublemmas.
 -/)
  (latexEnv := "proposition")
  (discussion := 985)]
theorem criterion (mₐ Mₐ xₐ x₀ : ℝ)
  (hxₐ : 1 < xₐ)
  (hlower : ∀ x > xₐ, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (mₐ * x / log x ^ 6) < pi x)
  (hupper : ∀ x > exp 1 * xₐ, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (Mₐ * x / log x ^ 6))
  (hx₀xₐ : x₀ ≥ exp 1 * xₐ)
  (hcrit : ∀ ⦃x : ℝ⦄, x > x₀ → ε Mₐ x - εlower mₐ xₐ x < log x) :
    ∀ x > x₀, pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1) := by
  intro x hx
  have hxexₐ : x > exp 1 * xₐ := lt_of_le_of_lt hx₀xₐ hx
  have hsq := sq_pi_lt Mₐ (exp 1 * xₐ) hupper x hxexₐ
  have hlow := ex_pi_gt mₐ xₐ hxₐ hlower x hxexₐ
  let U : ℝ := 1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 64 / log x ^ 6 +
    ε Mₐ x / log x ^ 7
  let L : ℝ := 1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
    εlower mₐ xₐ x / log x ^ 7
  have hsq' : pi x ^ 2 < x ^ 2 * U := by
    simpa [U] using hsq
  have hlow' : x ^ 2 * L < exp 1 * x / log x * pi (x / exp 1) := by
    simpa [L] using hlow
  have hx_gt_e : exp 1 < x := by
    have h1 : exp 1 < exp 1 * xₐ := by
      nlinarith [hxₐ, exp_pos (1 : ℝ)]
    exact lt_of_lt_of_le h1 (le_of_lt hxexₐ)
  have hlog_pos : 0 < log x := by
    have h1 : (1 : ℝ) < exp 1 := (Real.one_lt_exp_iff).2 (by norm_num)
    exact log_pos (lt_trans h1 hx_gt_e)
  have hnum_neg : ε Mₐ x - εlower mₐ xₐ x - log x < 0 := by
    linarith [hcrit hx]
  have hden_pos : 0 < log x ^ 7 := by positivity
  have hlog_ne : log x ≠ 0 := ne_of_gt hlog_pos
  have hUL_eq : U - L = (ε Mₐ x - εlower mₐ xₐ x - log x) / log x ^ 7 := by
    simp [U, L]
    field_simp [hlog_ne]
    ring
  have hUL_neg : U - L < 0 := by
    rw [hUL_eq]
    exact div_neg_of_neg_of_pos hnum_neg hden_pos
  have hU_lt_L : U < L := by linarith
  have hx_pos : 0 < x := lt_trans (by positivity : 0 < exp 1 * xₐ) hxexₐ
  have hmul : x ^ 2 * U < x ^ 2 * L :=
    mul_lt_mul_of_pos_left hU_lt_L (sq_pos_of_pos hx_pos)
  exact lt_trans hsq' (lt_trans hmul hlow')

/-- Integration by parts formula for `Li(x)`. -/
lemma Li_eq_sub_add_integral (x : ℝ) (hx : 2 ≤ x) :
    Li x = x / log x - 2 / log 2 + ∫ t in Icc 2 x, 1 / log t ^ 2 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    Li, intervalIntegral.integral_eq_sub_of_hasDerivAt]
  rotate_right
  · use fun t ↦ t / log t + ∫ u in (2 : ℝ)..t, 1 / log u ^ 2
  · norm_num; ring
  · intro t ht
    have ht' := Set.mem_Icc.mp (by simpa [hx] using ht)
    have h_ftc : HasDerivAt (fun t ↦ ∫ u in (2 : ℝ)..t, 1 / log u ^ 2) (1 / log t ^ 2) t := by
      apply_rules [intervalIntegral.integral_hasDerivAt_right]
      · apply_rules [ContinuousOn.intervalIntegrable]
        exact continuousOn_of_forall_continuousAt fun u hu ↦
          ContinuousAt.div continuousAt_const (ContinuousAt.pow
            (continuousAt_log (by cases Set.mem_uIcc.mp hu <;> linarith [ht'])) _)
              (ne_of_gt (sq_pos_of_pos (log_pos (by cases Set.mem_uIcc.mp hu <;> linarith [ht']))))
      · exact (measurable_const.div (measurable_log.pow_const _)).stronglyMeasurable.stronglyMeasurableAtFilter
      · exact ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (continuousAt_log (by cases Set.mem_uIcc.mp ht <;> linarith)) _)
            (ne_of_gt (sq_pos_of_pos (log_pos (by cases Set.mem_uIcc.mp ht <;> linarith))))
    convert HasDerivAt.add
      (HasDerivAt.div (hasDerivAt_id t) (hasDerivAt_log (show t ≠ 0 by cases Set.mem_uIcc.mp ht <;> linarith))
        (ne_of_gt (log_pos (show t > 1 by cases Set.mem_uIcc.mp ht <;> linarith))))
      h_ftc using 1 ; ring_nf
    by_cases h : t = 0 <;> simp [sq, mul_assoc, h]
    by_cases h' : log t = 0 <;> aesop
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt fun t ht ↦
      ContinuousAt.div continuousAt_const (continuousAt_log
        (by linarith [Set.mem_Icc.mp (by simpa [hx] using ht)]))
          (ne_of_gt (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hx] using ht)]))))

@[blueprint
  "pi-error-identity"
  (title := "Integral identity for pi - Li")
  (statement := /-- If $x \geq 2$, then
$$\pi(x) - \textrm{Li}(x) = \frac{\theta(x) - x}{\log x} + \frac{2}{\log 2} + \int_{2}^{x} \frac{\theta(t) -t}{t \log^{2}t}\, dt.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-417} and the fundamental theorem of calculus. -/)
  (latexEnv := "lemma")
  (discussion := 986)]
theorem pi_error_identity (x : ℝ) (hx : 2 ≤ x) :
    pi x - Li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
  have h_integral : ∫ t in Set.Icc 2 x, (θ t - t) / (t * log t ^ 2) =
      (∫ t in Set.Icc 2 x, θ t / (t * log t ^ 2)) -
      (∫ t in Set.Icc 2 x, 1 / log t ^ 2) := by
    rw [← MeasureTheory.integral_sub]
    · exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht ↦ by
        rw [sub_div, div_eq_mul_inv]; ring_nf
        norm_num [show t ≠ 0 by linarith [ht.1], show log t ≠ 0 from ne_of_gt <| log_pos <| by linarith [ht.1]]
    · have h_bound : ∀ t ∈ Set.Icc 2 x, |θ t / (t * log t ^ 2)| ≤ log 4 / log t ^ 2 := by
        intro t ht
        have : θ t ≤ log 4 * t := Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
        rw [abs_of_nonneg (div_nonneg (by exact Finset.sum_nonneg fun _ _ ↦
              log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop)
            (mul_nonneg (by linarith [ht.1]) (sq_nonneg _))), div_le_div_iff₀] <;>
          nlinarith [ht.1, ht.2, log_pos <| show 1 < t by linarith [ht.1],
            log_le_sub_one_of_pos <| show 0 < t by linarith [ht.1],
            show 0 ≤ θ t from Finset.sum_nonneg fun _ _ ↦
              log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop]
      refine MeasureTheory.Integrable.mono' (g := fun t ↦ log 4 / log t ^ 2) ?_ ?_ ?_
      · exact ContinuousOn.integrableOn_Icc (continuousOn_of_forall_continuousAt fun t ht ↦
          ContinuousAt.div continuousAt_const
            (ContinuousAt.pow (continuousAt_log (by linarith [ht.1])) _)
              (ne_of_gt (sq_pos_of_pos (log_pos (by linarith [ht.1])))))
      · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
        · have : Measurable (fun t : ℕ ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 0 t), log p) :=
            measurable_from_nat
          exact this.comp measurable_id'.nat_floor
        · exact Measurable.inv (measurable_id.mul (measurable_log.pow_const 2))
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht using h_bound t ht
    · exact ContinuousOn.integrableOn_Icc (continuousOn_const.div
        (ContinuousOn.pow (continuousOn_log.mono <| by norm_num) _) fun t ht ↦
        ne_of_gt <| sq_pos_of_pos <| log_pos <| by linarith [ht.1])
  have h_pi : pi x = θ x / log x + ∫ t in Icc 2 x, θ t / (t * log t ^ 2) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
    exact primeCounting_eq_theta_div_log_add_integral hx
  rw [h_integral, h_pi, Li_eq_sub_add_integral x hx]; ring

theorem integrable_theta (x : ℝ) :
    IntegrableOn (fun t ↦ (θ t - t) / (t * log t ^ 2)) (Icc 2 x) volume := by
  have l0 : ContinuousOn (fun t ↦ (t * log t ^ 2)⁻¹) (Set.Icc 2 x) := by
    refine ContinuousOn.inv₀ (continuousOn_id.mul (ContinuousOn.pow (ContinuousOn.log
      continuousOn_id fun y hy ↦ ?_) 2)) fun y hy ↦ ?_
    repeat simp_all; grind
  have l1 : IntegrableOn (fun t ↦ θ t / (t * log t ^ 2)) (Icc 2 x) volume :=
    (theta_mono.monotoneOn _).integrableOn_isCompact isCompact_Icc |>.mul_continuousOn l0
    isCompact_Icc
  have l2 : IntegrableOn (fun t ↦ t / (t * log t ^ 2)) (Icc 2 x) volume :=
    monotoneOn_id.integrableOn_isCompact isCompact_Icc |>.mul_continuousOn l0 isCompact_Icc
  simpa [div_sub_div_same] using l1.sub' l2

@[blueprint
  "ramanujan-pi-upper"
  (title := "Upper bound for pi")
  (statement := /-- Suppose that for $x \geq 2$ we have $|\theta(x)-x|\log^{5} x\leq x a(x)$. Then
$$
\pi(x)\leq \frac{x}{\log x} +a(x)\frac{x}{\log^6 x}+\int_2^x\frac{d t}{\log^2 t}+\int_2^x\frac{a(t)}{\log^7 t}\ dt.
$$ (cf. \cite[\S 5]{PT2021})
-/)
  (proof := /-- Follows from Lemma \ref{pi-error-identity} and the triangle inequality. -/)
  (latexEnv := "sublemma")
  (discussion := 987)]
theorem pi_upper (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, |θ x - x| * log x ^ 5 ≤ x * a x) (x : ℝ)
    (ha : IntegrableOn (fun t ↦ a t / log t ^ 7) (Icc 2 x) volume)
    (hx : 2 ≤ x) :
    pi x ≤ x / log x + a x * x / log x ^ 6 + (∫ t in Icc 2 x, 1 / log t ^ 2)
    + ∫ t in Icc 2 x, a t / log t ^ 7 := calc
  _ = pi x - Li x + Li x := by ring
  _ = x / log x + (θ x - x) / log x + (∫ (t : ℝ) in Icc 2 x, 1 / log t ^ 2) +
     ∫ (t : ℝ) in Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
     rw [pi_error_identity x hx, Li_eq_sub_add_integral x hx]; ring
  _ ≤ _ := by
    gcongr ?_ + ?_ + ?_ + ?_
    · calc
      _ = (θ x - x) * log x ^ 5 / log x ^ 6 := by field_simp
      _ ≤ |θ x - x| * log x ^ 5 / log x ^ 6 := by
        gcongr
        · exact pow_nonneg (log_nonneg (by grind)) 5
        · exact le_abs_self _
      _ ≤ _ := by grw [htheta x hx, mul_comm]
    · refine setIntegral_mono_on (integrable_theta x) ha measurableSet_Icc (fun t ht => ?_)
      calc
      _ = (θ t - t) * log t ^ 5 / (t * log t ^ 7) := by field_simp
      _ ≤ |θ t - t| * log t ^ 5 / (t * log t ^ 7) := by
        gcongr
        · exact mul_nonneg (by grind) (pow_nonneg (log_nonneg (by grind)) 7)
        · exact pow_nonneg (log_nonneg (by grind)) 5
        · exact le_abs_self _
      _ ≤ _ := by
        grw [htheta t ht.1, mul_comm]
        · field_simp (disch := grind); rfl
        · exact mul_nonneg (by grind) (pow_nonneg (log_nonneg (by grind)) 7)

@[blueprint
  "ramanujan-pi-lower"
  (title := "Lower bound for pi")
  (statement := /-- Suppose that for $x \geq 2$ we have $|\theta(x)-x|\log^{5} x\leq x a(x)$. Then
$$
\pi(x)\geq \frac{x}{\log x} -a(x)\frac{x}{\log^6 x}+\int_2^x\frac{d t}{\log^2 t}-\int_2^x\frac{a(t)}{\log^7 t}\ dt.
$$ (cf. \cite[\S 5]{PT2021})
-/)
  (proof := /-- Follows from Lemma \ref{pi-error-identity} and the triangle inequality. -/)
  (latexEnv := "sublemma")
  (discussion := 989)]
theorem pi_lower (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, |θ x - x| * log x ^ 5 ≤ x * a x) (x : ℝ)
    (ha : IntegrableOn (fun t ↦ a t / log t ^ 7) (Icc 2 x) volume)
    (hx : 2 ≤ x) :
    pi x ≥ x / log x - a x * x / log x ^ 6 + (∫ t in Icc 2 x, 1 / log t ^ 2) - ∫ t in Icc 2 x, a t / log t ^ 7 := by
  have h1 : (θ x - x) / log x ≥ - (x * a x / log x ^ 6) := by
    have hlog_pos : 0 < log x := log_pos (by linarith)
    have h1a : (θ x - x) / log x ≥ - (|θ x - x| / log x) := by
      have h1a1 : - |θ x - x| ≤ (θ x - x) := neg_abs_le (θ x - x)
      have h : (- |θ x - x|) / log x ≤ (θ x - x) / log x := div_le_div_of_nonneg_right h1a1 hlog_pos.le
      have h' : (- |θ x - x|) / log x = - (|θ x - x| / log x) := by field_simp [hlog_pos.ne']
      rw [h'] at h; exact h.ge
    have h1b : |θ x - x| * log x ^ 5 ≤ x * a x := htheta x hx
    have h1c : |θ x - x| / log x ≤ (x * a x) / log x ^ 6 := by
      have h1c1 : |θ x - x| ≤ (x * a x) / log x ^ 5 := by
        have h1c2 : 0 < log x ^ 5 := by positivity
        calc
          |θ x - x| = (|θ x - x| * log x ^ 5) / log x ^ 5 := by field_simp [hlog_pos.ne']
          _ ≤ (x * a x) / log x ^ 5 := by gcongr
      calc
        |θ x - x| / log x ≤ ((x * a x) / log x ^ 5) / log x := by gcongr
        _ = (x * a x) / log x ^ 6 := by field_simp [pow_succ, hlog_pos.ne']
    have h1d : - (|θ x - x| / log x) ≥ - ((x * a x) / log x ^ 6) := by gcongr
    linarith
  have h_int_abs : IntegrableOn (fun t : ℝ ↦ |(θ t - t) / (t * log t ^ 2)|) (Icc 2 x) volume := integrable_theta x |>.abs
  have h_neg_abs_int : IntegrableOn (fun t : ℝ ↦ - |(θ t - t) / (t * log t ^ 2)|) (Icc 2 x) volume := h_int_abs.neg
  have h2a : ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) ≥ - (∫ t in Icc 2 x, |(θ t - t) / (t * log t ^ 2)|) := by
    have h2a1 : ∀ t ∈ Icc 2 x, - |(θ t - t) / (t * log t ^ 2)| ≤ (θ t - t) / (t * log t ^ 2) := fun t _ => neg_abs_le _
    have h2a2 : ∫ t in Icc 2 x, (- |(θ t - t) / (t * log t ^ 2)|) ≤ ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) :=
      MeasureTheory.setIntegral_mono_on h_neg_abs_int (integrable_theta x) measurableSet_Icc h2a1
    have h2a3 : ∫ t in Icc 2 x, (- |(θ t - t) / (t * log t ^ 2)|) = - (∫ t in Icc 2 x, |(θ t - t) / (t * log t ^ 2)|) := by rw [MeasureTheory.integral_neg]
    rw [h2a3] at h2a2; exact h2a2.ge
  have h2b : ∫ t in Icc 2 x, |(θ t - t) / (t * log t ^ 2)| ≤ ∫ t in Icc 2 x, a t / log t ^ 7 :=
    MeasureTheory.setIntegral_mono_on h_int_abs ha measurableSet_Icc (fun t ht => by
      have ht2 : 2 ≤ t := ht.1
      have hlog_t_pos : 0 < log t := log_pos (by linarith)
      have h71 : |θ t - t| * log t ^ 5 ≤ t * a t := htheta t ht2
      have h72 : |θ t - t| ≤ (t * a t) / log t ^ 5 := by
        have h : 0 < log t ^ 5 := by positivity
        calc
          |θ t - t| = (|θ t - t| * log t ^ 5) / log t ^ 5 := by field_simp [hlog_t_pos.ne']
          _ ≤ (t * a t) / log t ^ 5 := by gcongr
      have h73 : |(θ t - t) / (t * log t ^ 2)| = |θ t - t| / (t * log t ^ 2) := by
        have h_t_pos : 0 < t := by linarith
        rw [abs_div, abs_of_pos (show 0 < t * log t ^ 2 from by positivity)]
      rw [h73]
      calc
        |θ t - t| / (t * log t ^ 2) ≤ ((t * a t) / log t ^ 5) / (t * log t ^ 2) := by gcongr
        _ = (t * a t) / (t * log t ^ 7) := by field_simp [pow_succ, hlog_t_pos.ne']
        _ = a t / log t ^ 7 := by
          have h_t_pos : 0 < t := by linarith
          field_simp [h_t_pos.ne'])
  have h2c : - (∫ t in Icc 2 x, |(θ t - t) / (t * log t ^ 2)|) ≥ - (∫ t in Icc 2 x, a t / log t ^ 7) := by gcongr
  have h2 : ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) ≥ - (∫ t in Icc 2 x, a t / log t ^ 7) := by linarith
  calc
    pi x = x / log x + (θ x - x) / log x + (∫ t in Icc 2 x, 1 / log t ^ 2) + ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
      have h_eq1 : pi x - Li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) := pi_error_identity x hx
      have h_eq2 : Li x = x / log x - 2 / log 2 + ∫ t in Icc 2 x, 1 / log t ^ 2 := Li_eq_sub_add_integral x hx
      linarith
    _ ≥ x / log x + (- (x * a x / log x ^ 6)) + (∫ t in Icc 2 x, 1 / log t ^ 2) + (- (∫ t in Icc 2 x, a t / log t ^ 7)) := by
      gcongr
    _ = x / log x - a x * x / log x ^ 6 + (∫ t in Icc 2 x, 1 / log t ^ 2) - ∫ t in Icc 2 x, a t / log t ^ 7 := by ring

theorem log_7_IBP (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 =
      x / log x ^ 7 - 2 / log 2 ^ 7 +
        7 * ∫ t in Set.Icc 2 x, 1 / log t ^ 8 := by
  suffices h_ibp : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (log t) ^ 7) = (b / (log b) ^ 7) - (a / (log a) ^ 7) +
        7 * ∫ t in a..b, (1 / (log t) ^ 8) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (log t) ^ 7) t =
        1 / (log t) ^ 7 - 7 * (1 / (log t) ^ 8) := by
    intro t ht
    norm_num [differentiableAt_log, ne_of_gt (show 0 < log t from log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]; ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (log t) ^ 7) t =
      (b / (log b) ^ 7) - (a / (log a) ^ 7) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun x hx ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (differentiableAt_log
          (by cases Set.mem_uIcc.mp hx <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| log_pos <|
          by cases Set.mem_uIcc.mp hx <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ (n : ℕ), ∀ y ∈ Set.Icc a b, log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| log_pos <| by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub] <;> norm_num
  · ring_nf
    exact ContinuousOn.intervalIntegrable (
      continuousOn_of_forall_continuousAt fun x hx =>
        ContinuousAt.pow (ContinuousAt.inv₀
          (continuousAt_log (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)]))
          (ne_of_gt (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])))) _) ..
  · apply_rules [ContinuousOn.intervalIntegrable]
    exact ContinuousOn.mul continuousOn_const <|
      ContinuousOn.inv₀ (ContinuousOn.pow
        (continuousOn_log.mono <| by
          intro x hx; cases Set.mem_uIcc.mp hx <;> norm_num <;> linarith) _)
        fun x hx ↦ ne_of_gt <| pow_pos (log_pos <| by
          cases Set.mem_uIcc.mp hx <;> linarith) _

theorem log_8_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 8 <
      sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8 := by
  by_cases h : x < 4
  · refine lt_of_le_of_lt (MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Icc fun t ht =>
      one_div_le_one_div_of_le ?_ <| pow_le_pow_left₀ (log_nonneg <| by linarith [ht.1])
        (log_le_log (by linarith [ht.1]) ht.1) 8) ?_
    · exact ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
        (continuousOn_log.mono <| by norm_num) _) fun t ht ↦ pow_ne_zero _ <| ne_of_gt <|
        log_pos <| by linarith [ht.1])
    · norm_num
    · positivity
    · norm_num [← div_eq_mul_inv]
      exact lt_add_of_le_of_pos (by
        gcongr; cases max_cases (x - 2) 0 <;>
          nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)]) (
        div_pos (by positivity) (pow_pos (log_pos (by linarith)) _))
  · have h_split : ∫ t in Set.Icc 2 x, 1 / log t ^ 8 =
        (∫ t in Set.Icc 2 (sqrt x), 1 / log t ^ 8) +
          (∫ t in Set.Icc (sqrt x) x, 1 / log t ^ 8) := by
      norm_num [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le, sqrt_le_iff, hx]
      rw [← intervalIntegral.integral_of_le (by
            nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)]),
        ← intervalIntegral.integral_of_le (by
          nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)]),
        intervalIntegral.integral_add_adjacent_intervals]
        <;> apply_rules [ContinuousOn.intervalIntegrable]
      · exact continuousOn_of_forall_continuousAt fun y hy =>
          ContinuousAt.inv₀ (ContinuousAt.pow (continuousAt_log (by
            cases Set.mem_uIcc.mp hy <;>
              nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])) _)
            (pow_ne_zero _ <| ne_of_gt <| log_pos <| by
              cases Set.mem_uIcc.mp hy <;>
                nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])
      · exact continuousOn_of_forall_continuousAt fun y hy =>
          ContinuousAt.inv₀ (ContinuousAt.pow (continuousAt_log (by
            cases Set.mem_uIcc.mp hy <;>
              nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])) _)
            (pow_ne_zero _ <| ne_of_gt <| log_pos <| by
              cases Set.mem_uIcc.mp hy <;>
                nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])
    have h_first : ∫ t in Set.Icc 2 (sqrt x), 1 / log t ^ 8 ≤
        sqrt x / (log 2) ^ 8 := by
      have h_mono : ∫ t in Set.Icc 2 (sqrt x), 1 / log t ^ 8 ≤
          ∫ t in Set.Icc 2 (sqrt x), 1 / log 2 ^ 8 := by
        refine MeasureTheory.setIntegral_mono_on ?_ ?_ ?_ ?_ <;> norm_num
        · exact ContinuousOn.integrableOn_Icc (continuousOn_of_forall_continuousAt fun t ht =>
            ContinuousAt.inv₀
              ((Real.continuousAt_log (show t ≠ 0 from ne_of_gt (by linarith [ht.1]))).pow _)
              (ne_of_gt (pow_pos (log_pos (show 1 < t by linarith [ht.1])) _)))
        · exact fun t ht₁ ht₂ ↦ inv_anti₀ (pow_pos (log_pos (by linarith)) _)
            (pow_le_pow_left₀ (log_nonneg (by linarith)) (log_le_log (by linarith) (by linarith)) _)
      refine le_trans h_mono ?_; norm_num
      rw [max_eq_left (sub_nonneg.mpr <| le_sqrt_of_sq_le <| by linarith)]
      ring_nf; norm_num; positivity
    have h_second : ∫ t in Set.Icc (sqrt x) x, 1 / log t ^ 8 ≤
        (x - sqrt x) * (2 ^ 8 / (log x) ^ 8) := by
      have hbd : ∀ t ∈ Set.Icc (sqrt x) x,
          1 / log t ^ 8 ≤ 2 ^ 8 / (log x) ^ 8 := by
        intro t ht
        have hlog_half : log t ≥ log (sqrt x) := log_le_log (by positivity) ht.1
        rw [log_sqrt (by positivity)] at hlog_half
        rw [div_le_div_iff₀] <;>
          nlinarith [pow_pos (log_pos (by linarith : 1 < x)) 8,
            pow_le_pow_left₀ (by linarith [log_pos (by linarith : 1 < x)]) hlog_half 8]
      convert MeasureTheory.setIntegral_mono_on _ _ _ hbd <;> norm_num
      · exact Or.inl <| sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
      · exact ContinuousOn.integrableOn_Icc (continuousOn_of_forall_continuousAt fun t ht =>
          ContinuousAt.inv₀ (ContinuousAt.pow (continuousAt_log (by
            nlinarith [ht.1, sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])) _)
            (pow_ne_zero _ <| ne_of_gt <| log_pos <| by
              nlinarith [ht.1, sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)]))
    refine h_split.symm ▸ lt_of_le_of_lt (add_le_add h_first h_second) ?_
    ring_nf
    nlinarith [show 0 < sqrt x * (log x)⁻¹ ^ 8 from
      mul_pos (sqrt_pos.mpr (by linarith))
        (pow_pos (inv_pos.mpr (log_pos (by linarith))) _)]

@[blueprint
  "log-7-int-bound"
  (title := "Bound for integral of an inverse power of log")
  (statement := /-- For $x \geq 2$ we have
$$\int_2^x \frac{dt}{\log^7 t} < \frac{x}{\log^7 x} + 7 \Big( \frac{\sqrt{x}}{\log^8 2} + \frac{2^8 x}{\log^8 x} \Big).$$
(cf. \cite[Section 2.3]{dudek-platt})-/)
  (proof := /-- Integrate by parts to write the left-hand side as $\frac{x}{\log^7 x} - \frac{2}{\log^7 2} + 7 \int_2^x \frac{t}{\log^8 t} dt$.  Discard the middle term.  For the final term, split between $\int_2^{\sqrt{x}}$ and $\int_{\sqrt{x}}^x$.  For the first, use the bound $\int_2^{\sqrt{x}} \frac{t}{\log^8 t} dt < \int_2^{\sqrt{x}} \frac{t}{\log^8 2} dt$, and for the second, use the bound $\int_{\sqrt{x}}^x \frac{t}{\log^8 t} dt < \int_{\sqrt{x}}^x \frac{t}{\log^8 x} dt$.-/)
  (latexEnv := "lemma")
  (discussion := 988)]
theorem log_7_int_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 < x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8) := by
  rw [log_7_IBP x hx]; linarith [log_8_bound x hx, show 0 ≤ 2 / log 2 ^ 7 by positivity]

-- Native-decide lemma for the computational [3, 599) range
set_option linter.style.nativeDecide false in
open LeanCert.Engine.ChebyshevTheta in
private theorem allThetaChecks_3_599 :
    checkAllThetaRelErrorReal 3 599 (768 / 1000) 20 = true := by native_decide

set_option linter.style.nativeDecide false in
open LeanCert.Engine.ChebyshevTheta in
private theorem thetaCheck599 :
    checkThetaRelErrorReal 599 (65 / 1000) 20 = true := by native_decide

@[blueprint
  "ramanujan-pibound-1"
  (title := "Error estimate for theta, range 1 ")
  (statement := /-- For $2 \leq x < 599$ we have
$$E_\theta(x) \leq 1 - \frac{\log 2}{3}.$$
(cf. \cite[(18)]{PT2021})-/)
  (proof := /-- For $x \in [2, 3)$ we have $\theta(x) = \log 2$, so
$E_\theta(x) = 1 - \log 2 / x < 1 - \log 2 / 3$ since $x < 3$.
For $x \in [3, 599)$ we use the LeanCert ChebyshevTheta engine:
\texttt{checkAllThetaRelErrorReal 3 599 (768/1000) 20} via \texttt{native\_decide}
gives $|\theta(x) - x| \leq 0.768 x$, hence $E_\theta(x) \leq 0.768 \leq 1 - \log 2 / 3$. -/)
  (latexEnv := "sublemma")
  (discussion := 990)]
theorem pi_bound_1 (x : ℝ) (hx : x ∈ Set.Ico 2 599) :
    Eθ x ≤ 1 - log 2 / 3 := by
  obtain ⟨hx2, hx599⟩ := hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hnn : (0 : ℝ) ≤ x := by linarith
  unfold Eθ
  rw [div_le_iff₀ hxpos]
  -- Goal: |θ x - x| ≤ (1 - log 2 / 3) * x
  by_cases hx3 : x < 3
  · -- Case x ∈ [2, 3): ⌊x⌋₊ = 2, θ(2) = log 2
    rw [Chebyshev.theta_eq_theta_coe_floor x]
    have hfloor : ⌊x⌋₊ = 2 := by
      apply (Nat.floor_eq_iff hnn).mpr
      exact ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [hfloor]
    -- Now goal involves θ ↑2, need to compute it
    have htheta_two : θ (↑(2 : ℕ) : ℝ) = log 2 := by
      simp [Chebyshev.theta, Finset.sum_filter, Finset.sum_Ioc_succ_top, Nat.prime_two]
    rw [htheta_two]
    -- Goal: |log 2 - x| ≤ (1 - log 2 / 3) * x
    have hlog2_lt_x : log 2 < x := by linarith [log_two_lt_d9]
    rw [abs_of_nonpos (by linarith), neg_sub]
    -- Goal: x - log 2 ≤ (1 - log 2 / 3) * x
    nlinarith [log_two_gt_d9]
  · -- Case x ∈ [3, 599): use computational checker
    push_neg at hx3
    have hfloor_pos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith : 1 ≤ x)
    have hfloor_ge3 : 3 ≤ ⌊x⌋₊ := Nat.le_floor hx3
    have hfloor_lt : ⌊x⌋₊ < 599 := (Nat.floor_lt hnn).mpr (by exact_mod_cast hx599)
    have hfloor_le : ⌊x⌋₊ ≤ 599 := le_of_lt hfloor_lt
    -- Extract pointwise check from the bulk checker
    have hpointwise :=
      LeanCert.Engine.ChebyshevTheta.checkAllThetaRelErrorReal_implies 3 599 (768 / 1000) 20
        allThetaChecks_3_599 ⌊x⌋₊ hfloor_pos hfloor_ge3 hfloor_le
    rw [if_pos hfloor_lt] at hpointwise
    -- Bridge to real-valued bound
    have hxlo : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hnn
    have hxhi : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have habs :=
      LeanCert.Engine.ChebyshevTheta.abs_theta_sub_le_mul_of_checkThetaRelErrorReal
        ⌊x⌋₊ 20 (768 / 1000) (by norm_num) (by norm_num) hpointwise x hxlo hxhi
    -- Chain: |θ x - x| ≤ 0.768 * x ≤ (1 - log 2 / 3) * x
    calc |θ x - x| ≤ ((768 / 1000 : ℚ) : ℝ) * x := habs
      _ ≤ (1 - log 2 / 3) * x := by
          gcongr
          have : (((768 : ℚ) / 1000 : ℚ) : ℝ) = 768 / 1000 := by push_cast; ring
          rw [this]
          linarith [log_two_lt_d9]

@[blueprint
  "ramanujan-pibound-2"
  (title := "Error estimate for theta, range 2 ")
  (statement := /-- For $599 < x \leq \exp(58)$ we have
$$E_\theta(x) \leq \frac{\log^2 x}{8\pi\sqrt{x}}.$$
(cf. \cite[(18)]{PT2021})-/)
  (proof := /-- This is \cite[Lemma 6]{PT2021}. -/)
  (latexEnv := "sublemma")]
theorem pi_bound_2 (x : ℝ) (hx : x ∈ Set.Ico 599 (exp 58)) :
    Eθ x ≤ log x ^ 2 / (8 * π * sqrt x) := by
  obtain ⟨hx_lo, hx_hi⟩ := hx
  have hx_pos : (0 : ℝ) < x := by linarith
  by_cases hx_gt : x > 599
  · have hlog_pos : (0 : ℝ) < log x := log_pos (by linarith : (1 : ℝ) < x)
    have hlog_ge1 : (1 : ℝ) ≤ log x := by
      rw [show (1 : ℝ) = log (exp 1) from by rw [log_exp]]
      exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_d9.le])
    have hlog_x_ge : 6 < log x := by
      have hexp6_lt : exp (6 : ℝ) < x := by
        have : exp (6 : ℝ) = exp (1 : ℝ) ^ (6 : ℕ) := by rw [← exp_nat_mul]; ring_nf
        rw [this]
        calc (exp 1 : ℝ) ^ 6 < (2.7182818286 : ℝ) ^ 6 := by gcongr; exact exp_one_lt_d9
          _ < 599 := by norm_num
          _ < x := hx_gt
      exact (Real.lt_log_iff_exp_lt hx_pos).mpr hexp6_lt
    have hrh : 4.92 * sqrt (x / log x) ≤ 3e12 := by
      suffices h : 4.92 ^ 2 * x ≤ (3e12) ^ 2 * log x by
        have h1 : 4.92 ^ 2 * (x / log x) ≤ (3e12) ^ 2 := by
          rw [show 4.92 ^ 2 * (x / log x) = 4.92 ^ 2 * x / log x from by ring]
          exact div_le_of_le_mul₀ hlog_pos.le (by positivity) h
        have h2 := sqrt_le_sqrt h1
        rw [sqrt_sq (by positivity : (0 : ℝ) ≤ 3e12)] at h2
        calc 4.92 * sqrt (x / log x) = sqrt (4.92 ^ 2 * (x / log x)) := by
              rw [sqrt_mul (by positivity : (0 : ℝ) ≤ 4.92 ^ 2), sqrt_sq (by positivity : (0 : ℝ) ≤ 4.92)]
          _ ≤ 3e12 := h2
      by_cases hx45 : x ≤ exp 45
      · have hexp45 : exp (45 : ℝ) < 2 * 10^20 := by
          have : exp (45 : ℝ) = exp (1 : ℝ) ^ (45 : ℕ) := by rw [← exp_nat_mul]; ring_nf
          rw [this]
          calc (exp 1 : ℝ) ^ 45 < (2.7182818286 : ℝ) ^ 45 := by gcongr; exact exp_one_lt_d9
            _ < 2 * 10^20 := by norm_num
        have : 4.92 ^ 2 * x ≤ 4.92 ^ 2 * exp 45 := by gcongr
        have : 4.92 ^ 2 * exp 45 < 4.92 ^ 2 * (2 * 10^20) := by gcongr
        have : 4.92 ^ 2 * (2 * (10 : ℝ) ^ 20) ≤ (3e12) ^ 2 * 6 := by norm_num
        have : (3e12) ^ 2 * 6 < (3e12 : ℝ) ^ 2 * log x := by gcongr
        linarith
      · push_neg at hx45
        have hlog45 : 45 < log x := by
          rwa [show (45 : ℝ) = log (exp 45) from by rw [log_exp],
               log_lt_log_iff (exp_pos 45) hx_pos]
        have hexp58 : exp (58 : ℝ) < 16 * 10^24 := by
          have h29 : exp (29 : ℝ) < 4 * 10^12 := by
            have : exp (29 : ℝ) = exp (1 : ℝ) ^ (29 : ℕ) := by rw [← exp_nat_mul]; ring_nf
            rw [this]
            calc (exp 1 : ℝ) ^ 29 < (2.7182818286 : ℝ) ^ 29 := by gcongr; exact exp_one_lt_d9
              _ < 4 * 10^12 := by norm_num
          have : exp (58 : ℝ) = exp (29 : ℝ) * exp (29 : ℝ) := by rw [← exp_add]; norm_num
          rw [this]
          nlinarith [exp_pos (29 : ℝ)]
        have : 4.92 ^ 2 * x < 4.92 ^ 2 * exp 58 := by gcongr
        have : 4.92 ^ 2 * exp 58 < 4.92 ^ 2 * (16 * 10^24) := by gcongr
        have : 4.92 ^ 2 * (16 * (10 : ℝ) ^ 24) ≤ (3e12) ^ 2 * 45 := by norm_num
        have : (3e12) ^ 2 * 45 < (3e12 : ℝ) ^ 2 * log x := by gcongr
        linarith
    have hbuthe := Buthe2.theorem_2b x (3e12) PT_theorem_1 hrh hx_gt
    unfold Eθ
    have hsqrt_pos : (0 : ℝ) < sqrt x := sqrt_pos.mpr hx_pos
    have hsqx : sqrt x * sqrt x = x := Real.mul_self_sqrt hx_pos.le
    rw [div_le_div_iff₀ hx_pos (by positivity : (0 : ℝ) < 8 * π * sqrt x)]
    have h1 :
        |θ x - x| * (8 * π * sqrt x) ≤
          sqrt x * (log x) ^ 2 / (8 * π) * (8 * π * sqrt x) :=
      mul_le_mul_of_nonneg_right hbuthe (by positivity)
    have h2 : sqrt x * (log x) ^ 2 / (8 * π) * (8 * π * sqrt x) = log x ^ 2 * x := by
      field_simp
      nlinarith
    linarith
  · push_neg at hx_gt
    have hx_eq : x = 599 := le_antisymm hx_gt hx_lo
    subst hx_eq
    unfold Eθ
    have habs :=
      LeanCert.Engine.ChebyshevTheta.abs_theta_sub_le_mul_of_checkThetaRelErrorReal
        599 20 (65 / 1000) (by norm_num) (by norm_num) thetaCheck599 (599 : ℝ) (by norm_num)
        (by push_cast; norm_num)
    have hEθ : |θ (599 : ℝ) - 599| / 599 ≤ 65 / 1000 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 599)]
      push_cast at habs
      exact habs
    suffices h_bound : (65 : ℝ) / 1000 ≤ log (599 : ℝ) ^ 2 / (8 * π * sqrt 599) by
      linarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * π * sqrt 599)]
    have hpi : π < 3.1416 := pi_lt_d4
    have hsqrt : sqrt (599 : ℝ) < 24.5 := by
      rw [show (24.5 : ℝ) = sqrt (24.5 ^ 2) from by rw [sqrt_sq (by norm_num : (0 : ℝ) ≤ 24.5)]]
      exact sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hlog : (6.39 : ℝ) < log 599 := by
      rw [show (6.39 : ℝ) = log (exp 6.39) from by rw [log_exp]]
      exact log_lt_log (exp_pos 6.39) (by
        have h1 : exp (6.39 : ℝ) = exp 6 * exp (39 / 100 : ℝ) := by rw [← exp_add]; norm_num
        rw [h1]
        have h2 : exp (6 : ℝ) < 403.5 := by
          have : exp (6 : ℝ) = exp (1 : ℝ) ^ (6 : ℕ) := by rw [← exp_nat_mul]; ring_nf
          rw [this]
          calc (exp 1 : ℝ) ^ 6 < (2.7182818286 : ℝ) ^ 6 := by gcongr; exact exp_one_lt_d9
            _ < 403.5 := by norm_num
        have h3 : exp (39 / 100 : ℝ) < 1.48 := by
          have hx : |((39 : ℝ) / 100)| ≤ 1 := by norm_num
          have hbound := exp_bound hx (n := 5) (by norm_num)
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hbound
          push_cast at hbound
          rw [abs_le] at hbound
          linarith [hbound.2]
        nlinarith [exp_pos (6 : ℝ), exp_pos (39 / 100 : ℝ)])
    nlinarith [Real.pi_pos, sqrt_nonneg (599 : ℝ), sq_nonneg (log (599 : ℝ) - 6.39)]

@[blueprint
  "ramanujan-pibound-3"
  (title := "Error estimate for theta, range 3")
  (statement := /-- For $\exp(58) < x < \exp(1169)$ we have
$$E_\theta(x) \leq \sqrt\frac{8}{17\pi}\left(\frac{\log x}{6.455}\right)^{\frac{1}{4}}\exp\left(-\sqrt{\frac{\log x}{6.455}}\right).$$
(cf. \cite[(18)]{PT2021})-/)
  (proof := /-- This follows from Theorem \ref{trudgian:theorem 1-theta}. -/)
  (latexEnv := "sublemma")
  (discussion := 991)]
theorem pi_bound_3 (x : ℝ) (hx : x ∈ Set.Ico (exp 58) (exp 1169)) :
    Eθ x ≤ sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log x / 6.455)) := by
  have htab : (2, (0.001 : ℝ), (908994923 : ℝ)) ∈ Dusart.Table_4_2 := by
    simp [Dusart.Table_4_2]
  have h908 : (908994923 : ℝ) ≤ exp 58 := by
    interval_decide
  have hx_large : (908994923 : ℝ) ≤ x :=
    le_trans h908 hx.1
  have hE : Eθ x ≤ (0.001 : ℝ) / (log x) ^ 2 :=
    Dusart.theorem_4_2 htab hx_large

  have hlog_ge_58 : (58 : ℝ) ≤ log x := by
    have h := log_le_log (show 0 < exp 58 by positivity) hx.1
    simpa using h
  have hlog_le_1169 : log x ≤ (1169 : ℝ) := by
    have h := log_le_log (show 0 < x by linarith [hx.1, exp_pos 58]) hx.2.le
    simpa using h

  have hleft_const : (0.001 : ℝ) / (log x) ^ 2 ≤ (0.001 : ℝ) / (58 : ℝ) ^ 2 := by
    have hpow : (58 : ℝ) ^ 2 ≤ (log x) ^ 2 := by
      nlinarith
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 0.001)
      (by positivity : 0 < (58 : ℝ) ^ 2) hpow

  have hpi : π ≤ (3.15 : ℝ) := by
    interval_decide
  have hfrac : (8 / (17 * (3.15 : ℝ)) : ℝ) ≤ 8 / (17 * π) := by
    gcongr
  have hsqrt_frac : sqrt (8 / (17 * (3.15 : ℝ)) : ℝ) ≤ sqrt (8 / (17 * π)) :=
    sqrt_le_sqrt hfrac
  have h038 : (0.38 : ℝ) ≤ sqrt (8 / (17 * (3.15 : ℝ)) : ℝ) := by
    refine (Real.le_sqrt (by norm_num) (by positivity)).2 ?_
    norm_num
  have hA_lb : (0.38 : ℝ) ≤ sqrt (8 / (17 * π)) := le_trans h038 hsqrt_frac

  have hexp13_5 : (1 / (900000 : ℝ)) ≤ exp (-(13.5 : ℝ)) := by
    interval_decide
  have hsqrt_lt13_5 : sqrt (1169 / 6.455 : ℝ) < 13.5 :=
    (sqrt_lt (by positivity) (by positivity)).2 (by norm_num)
  have hexp_const : (1 / (900000 : ℝ)) ≤ exp (-sqrt (1169 / 6.455 : ℝ)) := by
    have hmono : exp (-(13.5 : ℝ)) ≤ exp (-sqrt (1169 / 6.455 : ℝ)) :=
      exp_le_exp.mpr (by linarith)
    grind

  have hratio_le : log x / 6.455 ≤ (1169 / 6.455 : ℝ) := by
    gcongr
  have hsqrt_le : sqrt (log x / 6.455 : ℝ) ≤ sqrt (1169 / 6.455 : ℝ) :=
    sqrt_le_sqrt hratio_le
  have hexp_var : exp (-sqrt (1169 / 6.455 : ℝ)) ≤ exp (-sqrt (log x / 6.455 : ℝ)) :=
    exp_le_exp.mpr (by linarith)
  have hexp_lb : (1 / (900000 : ℝ)) ≤ exp (-sqrt (log x / 6.455 : ℝ)) :=
    le_trans hexp_const hexp_var

  have hprod2 : (0.38 : ℝ) * (1 / (900000 : ℝ)) ≤
      sqrt (8 / (17 * π)) * exp (-sqrt (log x / 6.455 : ℝ)) :=
    mul_le_mul hA_lb hexp_lb (by positivity) (by positivity)
  have hpow_ge_one : (1 : ℝ) ≤ (log x / 6.455) ^ (1 / 4 : ℝ) := by
    have hbase_ge_one : (1 : ℝ) ≤ log x / 6.455 := by
      have hdiv58 : (58 / 6.455 : ℝ) ≤ log x / 6.455 := by
        gcongr
      have h58_ge_one : (1 : ℝ) ≤ (58 / 6.455 : ℝ) := by
        norm_num
      grind
    exact one_le_rpow hbase_ge_one (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ))
  have hmul_factor :
      sqrt (8 / (17 * π)) * exp (-sqrt (log x / 6.455 : ℝ)) ≤
        sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log x / 6.455 : ℝ)) := by
    calc
      sqrt (8 / (17 * π)) * exp (-sqrt (log x / 6.455 : ℝ))
          = sqrt (8 / (17 * π)) * (1 : ℝ) * exp (-sqrt (log x / 6.455 : ℝ)) := by ring
      _ ≤ sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log x / 6.455 : ℝ)) := by
        gcongr
  have hprod3 : (0.38 : ℝ) * (1 / (900000 : ℝ)) ≤
      sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log x / 6.455 : ℝ)) := by
    grind

  have hconst_cmp : (0.001 : ℝ) / (58 : ℝ) ^ 2 ≤ (0.38 : ℝ) * (1 / (900000 : ℝ)) := by
    norm_num

  exact le_trans (le_trans (le_trans hE hleft_const) hconst_cmp) (by
    simpa using hprod3)

@[blueprint
  "ramanujan-pibound-4"
  (title := "Error estimate for theta, range 4")
  (statement := /-- For $\exp(1169) \leq x < \exp(2000)$ we have
$$E_\theta(x) \leq 462.0\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$
(cf. \cite[(18)]{PT2021})-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")
  (discussion := 992)]
theorem pi_bound_4 (x : ℝ) (hx : x ∈ Set.Ico (exp 1169) (exp 2000)) :
    Eθ x ≤ 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
  have h3 : exp 1000 ≤ x := by
    have h5 : exp 1000 ≤ exp 1169 := by
      apply exp_le_exp.mpr
      norm_num
    have h6 : exp 1169 ≤ x := hx.1
    linarith
  have h7 : Eθ x ≤ admissible_bound (461.9 + 0.1) (1.52 : ℝ) (1.89 : ℝ) (5.573412 : ℝ) x :=
    PT.corollary_1 1000 0.98 461.9 1.52 1.89 1.20e-5 (by simp [PT.Table_1]) x h3
  have h8 : 461.9 + 0.1 = (462.0 : ℝ) := by norm_num
  simpa [h8, admissible_bound, sqrt_eq_rpow] using h7

@[blueprint
  "ramanujan-pibound-5"
  (title := "Error estimate for theta, range 5 ")
  (statement := /-- For $\exp(2000) \leq x < \exp(3000)$ we have
$$E_\theta(x) \leq 411.5\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$
(cf. \cite[(18)]{PT2021})-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")
  (discussion := 993)]
theorem pi_bound_5 (x : ℝ) (hx : x ∈ Set.Ico (exp 2000) (exp 3000)) :
    Eθ x ≤ 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
  have h7 : Eθ x ≤ admissible_bound (411.4 + 0.1) (1.52 : ℝ) (1.89 : ℝ) (5.573412 : ℝ) x :=
    PT.corollary_1 2000 0.98 411.4 1.52 1.89 8.35e-10 (by simp [PT.Table_1]) x hx.1
  have h8 : 411.4 + 0.1 = (411.5 : ℝ) := by norm_num
  simpa [h8, admissible_bound, sqrt_eq_rpow] using h7

@[blueprint
  "ramanujan-pibound-6"
  (title := "Error estimate for theta, range 6 ")
  (statement := /-- For $x > \exp(3000)$ we have
$$E_\theta(x) \leq 379.7\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$
(cf. \cite[(18)]{PT2021})-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")
  (discussion := 1094)]
theorem pi_bound_6 (x : ℝ) (hx : exp 3000 ≤ x) :
    Eθ x ≤ 379.7 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
  have h7 : Eθ x ≤ admissible_bound (379.6 + 0.1) (1.52 : ℝ) (1.89 : ℝ) (5.573412 : ℝ) x :=
    PT.corollary_1 3000 0.98 379.6 1.52 1.89 4.51e-13 (by simp [PT.Table_1]) x hx
  have h8 : 379.6 + 0.1 = (379.7 : ℝ) := by norm_num
  simpa [h8, admissible_bound, sqrt_eq_rpow] using h7


noncomputable def a (x : ℝ) : ℝ := (log x)^5 * (
  if x ∈ Set.Ico 2 599 then 1 - log 2 / 3
  else if x ∈ Set.Ico 599 (exp 58) then log x ^ 2 / (8 * π * sqrt x)
  else if x ∈ Set.Ico (exp 58) (exp 1169) then sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log x / 6.455))
  else if x ∈ Set.Ico (exp 1169) (exp 2000) then 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  else if x ∈ Set.Ico (exp 2000) (exp 3000) then 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  else 379.7 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)))

@[blueprint
  "pt_eq_18"
  (title := "Equation (18) of Platt-Trudgian")
  (statement := /-- For $x \geq 2$ we have
$$E_\theta(x) (\log x)^5 \leq a(x).$$-/)
  (proof := /-- This follows from the previous five sublemmas. -/)
  (latexEnv := "proposition")
  (discussion := 994)]
theorem pi_bound (x : ℝ) (hx : 2 ≤ x) :
    Eθ x * ( log x)^5 ≤ a x := by
  set b : ℝ :=
    if x ∈ Set.Ico 2 599 then 1 - log 2 / 3
    else if x ∈ Set.Ico 599 (exp 58) then log x ^ 2 / (8 * π * sqrt x)
    else if x ∈ Set.Ico (exp 58) (exp 1169) then sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log x / 6.455))
    else if x ∈ Set.Ico (exp 1169) (exp 2000) then 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
    else if x ∈ Set.Ico (exp 2000) (exp 3000) then 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
    else 379.7 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  have ha : a x = (log x) ^ 5 * b := by
    simp [a, b]
  have hb : Eθ x ≤ b := by
    by_cases h1 : x ∈ Set.Ico 2 599
    · simpa [b, h1] using pi_bound_1 x h1
    · have hx599 : (599 : ℝ) ≤ x := by
        by_contra hx599
        exact h1 ⟨hx, lt_of_not_ge hx599⟩
      by_cases h2 : x ∈ Set.Ico 599 (exp 58)
      · simpa [b, h1, h2] using pi_bound_2 x h2
      · have hx58 : exp 58 ≤ x := by
          by_contra hx58
          exact h2 ⟨hx599, lt_of_not_ge hx58⟩
        by_cases h3 : x ∈ Set.Ico (exp 58) (exp 1169)
        · simpa [b, h1, h2, h3] using pi_bound_3 x h3
        · have hx1169 : exp 1169 ≤ x := by
            by_contra hx1169
            exact h3 ⟨hx58, lt_of_not_ge hx1169⟩
          by_cases h4 : x ∈ Set.Ico (exp 1169) (exp 2000)
          · simpa [b, h1, h2, h3, h4] using pi_bound_4 x h4
          · have hx2000 : exp 2000 ≤ x := by
              by_contra hx2000
              exact h4 ⟨hx1169, lt_of_not_ge hx2000⟩
            by_cases h5 : x ∈ Set.Ico (exp 2000) (exp 3000)
            · simpa [b, h1, h2, h3, h4, h5] using pi_bound_5 x h5
            · have hx3000 : exp 3000 ≤ x := by
                by_contra hx3000
                exact h5 ⟨hx2000, lt_of_not_ge hx3000⟩
              simpa [b, h1, h2, h3, h4, h5] using pi_bound_6 x hx3000
  have hlog5_nonneg : 0 ≤ log x ^ 5 :=
    pow_nonneg (log_nonneg (by linarith : 1 ≤ x)) 5
  have hmul : Eθ x * log x ^ 5 ≤ b * log x ^ 5 :=
    mul_le_mul_of_nonneg_right hb hlog5_nonneg
  simpa [ha, mul_assoc, mul_left_comm, mul_comm] using hmul

private lemma pi_bound_abs_mul (x : ℝ) (hx : 2 ≤ x) :
    |θ x - x| * log x ^ 5 ≤ x * a x := by
  have hpb : Eθ x * log x ^ 5 ≤ a x := pi_bound x hx
  have hxpos : 0 < x := by linarith
  have hpb' : (|θ x - x| / x) * log x ^ 5 ≤ a x := by
    simpa [Eθ] using hpb
  have hmul : ((|θ x - x| / x) * log x ^ 5) * x ≤ a x * x :=
    mul_le_mul_of_nonneg_right hpb' hxpos.le
  have hleft : ((|θ x - x| / x) * log x ^ 5) * x = |θ x - x| * log x ^ 5 := by
    field_simp [hxpos.ne']
  have hright : a x * x = x * a x := by ring
  simpa [hleft, hright] using hmul

noncomputable def xₐ : ℝ := exp 3914

@[blueprint
  "a-mono"
  (title := "Monotonicity of a(x)")
  (statement := /-- The function $a(x)$ is nonincreasing for $x \geq x_a$. -/)
  (proof := /-- Follows from Lemma \ref{admissible-bound-monotone}. -/)
  (latexEnv := "lemma")
  (discussion := 995)]
theorem a_mono : AntitoneOn a (Set.Ici xₐ) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hxa3 : xₐ ≥ exp 3000 := by
    unfold xₐ
    exact exp_le_exp.mpr (by norm_num)
  have hx3 := le_trans hxa3 hx; have hy3 := le_trans hxa3 hy
  have neg : ∀ z ≥ exp 3000, ∀ lo hi : ℝ, hi ≤ exp 3000 → ¬(z ∈ Set.Ico lo hi) :=
    fun z hz _ _ hhi h ↦ absurd (Set.mem_Ico.mp h).2 (not_lt.mpr (le_trans hhi hz))
  have h599 : (599 : ℝ) ≤ exp 3000 := by linarith [add_one_le_exp (3000 : ℝ)]
  have h58 := exp_le_exp.mpr (show (58 : ℝ) ≤ 3000 by norm_num)
  have h1169 := exp_le_exp.mpr (show (1169 : ℝ) ≤ 3000 by norm_num)
  have h2000 := exp_le_exp.mpr (show (2000 : ℝ) ≤ 3000 by norm_num)
  have ha_eq : ∀ z ≥ exp 3000, a z = admissible_bound (379.7 * 5.573412 ^ 5) 6.52 1.89 5.573412 z := by
    intro z hz
    have hlog : 0 < log z := log_pos (by linarith [add_one_le_exp (3000 : ℝ)])
    have hdiv : 0 < log z / 5.573412 := by positivity
    unfold a admissible_bound
    simp only [neg z hz _ _ h599, neg z hz _ _ h58, neg z hz _ _ h1169,
      neg z hz _ _ h2000, neg z hz _ _ le_rfl, ite_false, sqrt_eq_rpow]
    have h_pow : (log z) ^ (5 : ℕ) = 5.573412 ^ (5 : ℕ) * (log z / 5.573412) ^ (5 : ℕ) := by
      rw [show log z = 5.573412 * (log z / 5.573412) from by field_simp]; ring
    have h_rpow : (log z / 5.573412) ^ (5 : ℕ) * (log z / 5.573412) ^ (1.52 : ℝ) =
        (log z / 5.573412) ^ (6.52 : ℝ) := by
      rw [← rpow_natCast (log z / 5.573412) 5, ← rpow_add hdiv]; push_cast; norm_num
    rw [h_pow]
    conv_lhs =>
      rw [show ∀ (a b c d e : ℝ), a * b * (c * d * e) = c * a * (b * d) * e from by intros; ring]
    rw [h_rpow]
  change a y ≤ a x
  rw [ha_eq x hx3, ha_eq y hy3]
  exact admissible_bound.mono _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (Set.mem_Ici.mpr (le_trans (show exp (5.573412 * (2 * 6.52 / 1.89) ^ 2) ≤ xₐ from by
      unfold xₐ; exact exp_le_exp.mpr (by norm_num)) hx))
    (Set.mem_Ici.mpr (le_trans (show exp (5.573412 * (2 * 6.52 / 1.89) ^ 2) ≤ xₐ from by
      unfold xₐ; exact exp_le_exp.mpr (by norm_num)) hy)) hxy

noncomputable def C₁ : ℝ := log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7

noncomputable def C₂ : ℝ := log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 - a t) / log t ^ 7

noncomputable def C₃ : ℝ := 2 * log xₐ ^ 6 / xₐ * ∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)

private noncomputable def B : ℝ :=
  1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2 + 7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8)

noncomputable def Mₐ (x : ℝ) : ℝ := 120 + a x + C₁ + (720 + a xₐ) * B

noncomputable def mₐ (x : ℝ) : ℝ := 120 - a x - (C₂ + C₃) - a xₐ * B

noncomputable def exₐ : ℝ := exp 1 * xₐ

private theorem log_xₐ_val : log xₐ = (3914 : ℝ) := by
  unfold xₐ
  rw [log_exp]

private lemma xₐ_pos : 0 < xₐ := by
  unfold xₐ
  positivity

private lemma one_lt_xₐ : 1 < xₐ := by
  unfold xₐ
  exact (Real.one_lt_exp_iff).2 (by norm_num)

private lemma two_le_xₐ : 2 ≤ xₐ := by
  unfold xₐ
  linarith [add_one_le_exp (3914 : ℝ)]

private lemma log_xₐ_pos : 0 < log xₐ :=
  log_pos one_lt_xₐ

private lemma exp3000_le_xₐ : exp 3000 ≤ xₐ := by
  unfold xₐ
  exact exp_le_exp.mpr (by norm_num)

private lemma xₐ_le_exₐ : xₐ ≤ exₐ := by
  unfold exₐ
  have h1 : (1 : ℝ) ≤ exp 1 := by
    linarith [add_one_le_exp (1 : ℝ)]
  nlinarith [h1, xₐ_pos.le]

private lemma two_le_exₐ : 2 ≤ exₐ :=
  le_trans two_le_xₐ xₐ_le_exₐ

private theorem exₐ_eq : exₐ = exp (3915 : ℝ) := by
  unfold exₐ xₐ
  rw [← exp_add]
  norm_num

private lemma exₐ_pos : 0 < exₐ := by
  rw [exₐ_eq]
  positivity

private lemma integrable_a_over_log7_piecewise (x : ℝ) (_hx2 : 2 ≤ x) :
    IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 x) volume := by
  let I : Set ℝ := Set.Icc 2 x
  let A1 : Set ℝ := Set.Ico 2 599
  let A2 : Set ℝ := Set.Ico 599 (exp 58)
  let A3 : Set ℝ := Set.Ico (exp 58) (exp 1169)
  let A4 : Set ℝ := Set.Ico (exp 1169) (exp 2000)
  let A5 : Set ℝ := Set.Ico (exp 2000) (exp 3000)

  let S1 : Set ℝ := I ∩ A1
  let S2 : Set ℝ := I ∩ A1ᶜ ∩ A2
  let S3 : Set ℝ := I ∩ A1ᶜ ∩ A2ᶜ ∩ A3
  let S4 : Set ℝ := I ∩ A1ᶜ ∩ A2ᶜ ∩ A3ᶜ ∩ A4
  let S5 : Set ℝ := I ∩ A1ᶜ ∩ A2ᶜ ∩ A3ᶜ ∩ A4ᶜ ∩ A5
  let S6 : Set ℝ := I ∩ A1ᶜ ∩ A2ᶜ ∩ A3ᶜ ∩ A4ᶜ ∩ A5ᶜ

  let f : ℝ → ℝ := fun t ↦ a t / log t ^ 7

  let g1 : ℝ → ℝ := fun t ↦ (log t) ^ 5 * (1 - log 2 / 3) / log t ^ 7
  let g2 : ℝ → ℝ := fun t ↦ (log t) ^ 5 * (log t ^ 2 / (8 * π * sqrt t)) / log t ^ 7
  let g3 : ℝ → ℝ := fun t ↦ (log t) ^ 5 *
    (sqrt (8 / (17 * π)) * (log t / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log t / 6.455))) / log t ^ 7
  let g4 : ℝ → ℝ := fun t ↦ (log t) ^ 5 *
    (462.0 * (log t / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log t / 5.573412))) / log t ^ 7
  let g5 : ℝ → ℝ := fun t ↦ (log t) ^ 5 *
    (411.5 * (log t / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log t / 5.573412))) / log t ^ 7
  let g6 : ℝ → ℝ := fun t ↦ (log t) ^ 5 *
    (379.7 * (log t / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log t / 5.573412))) / log t ^ 7

  have hI_log_cont : ContinuousOn (fun t ↦ log t ^ 7) I := by
    dsimp [I]
    exact (continuousOn_log.mono (by intro t ht; exact ne_of_gt (by linarith [ht.1]))).pow 7
  have hI_log_ne : ∀ t ∈ I, log t ^ 7 ≠ 0 := by
    intro t ht
    exact pow_ne_zero _ (ne_of_gt (log_pos (by linarith [ht.1])))

  have hg1_cont : ContinuousOn g1 I := by
    dsimp [g1]
    refine (ContinuousOn.mul ((continuousOn_log.mono (by intro t ht; exact ne_of_gt (by linarith [ht.1]))).pow 5) continuousOn_const).div hI_log_cont ?_
    intro t ht
    exact hI_log_ne t ht

  have hg2_cont : ContinuousOn g2 I := by
    refine continuousOn_of_forall_continuousAt ?_
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hlog : ContinuousAt (fun t => log t) t := continuousAt_log ht0
    have hsqrt : ContinuousAt (fun t => sqrt t) t := (Real.continuous_sqrt.continuousAt)
    have hden : ContinuousAt (fun t => (8 * π) * sqrt t) t := continuousAt_const.mul hsqrt
    have hden_ne : (8 * π) * sqrt t ≠ 0 := by
      have hsqrt_pos : 0 < sqrt t := sqrt_pos.mpr (by linarith [ht.1])
      positivity
    have hfrac : ContinuousAt (fun t => log t ^ 2 / ((8 * π) * sqrt t)) t :=
      (hlog.pow 2).div hden hden_ne
    have hfrac' : ContinuousAt (fun t => log t ^ 2 / (8 * π * sqrt t)) t := by
      simpa [mul_assoc] using hfrac
    have hnum : ContinuousAt (fun t => (log t) ^ 5 * (log t ^ 2 / (8 * π * sqrt t))) t :=
      (hlog.pow 5).mul hfrac'
    have hden2 : ContinuousAt (fun t => log t ^ 7) t := (hlog.pow 7)
    exact hnum.div hden2 (hI_log_ne t ht)

  have hg3_cont : ContinuousOn g3 I := by
    refine continuousOn_of_forall_continuousAt ?_
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hlog : ContinuousAt (fun t => log t) t := continuousAt_log ht0
    have hbase : ContinuousAt (fun t => log t / 6.455) t := hlog.div_const _
    have hrpow : ContinuousAt (fun t => (log t / 6.455) ^ (1 / 4 : ℝ)) t :=
      hbase.rpow_const (Or.inr (by positivity : 0 ≤ (1 / 4 : ℝ)))
    have hsqrt : ContinuousAt (fun t => sqrt (log t / 6.455)) t := (Real.continuous_sqrt.continuousAt).comp hbase
    have hexp : ContinuousAt (fun t => exp (-sqrt (log t / 6.455))) t :=
      (Real.continuous_exp.continuousAt).comp hsqrt.neg
    have hmul2 : ContinuousAt (fun t =>
        sqrt (8 / (17 * π)) * (log t / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log t / 6.455))) t := by
      simpa using (continuousAt_const.mul hrpow).mul hexp
    have hnum : ContinuousAt (fun t => (log t) ^ 5 *
        (sqrt (8 / (17 * π)) * (log t / 6.455) ^ (1 / 4 : ℝ) * exp (-sqrt (log t / 6.455)))) t :=
      (hlog.pow 5).mul hmul2
    have hden2 : ContinuousAt (fun t => log t ^ 7) t := (hlog.pow 7)
    exact hnum.div hden2 (hI_log_ne t ht)

  have hcont46 : ∀ c : ℝ, ContinuousOn (fun t ↦ (log t) ^ 5 *
      (c * (log t / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log t / 5.573412))) / log t ^ 7) I := by
    intro c
    refine continuousOn_of_forall_continuousAt ?_
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hlog : ContinuousAt (fun t => log t) t := continuousAt_log ht0
    have hbase : ContinuousAt (fun t => log t / 5.573412) t := hlog.div_const _
    have hrpow : ContinuousAt (fun t => (log t / 5.573412) ^ (1.52 : ℝ)) t :=
      hbase.rpow_const (Or.inr (by positivity : 0 ≤ (1.52 : ℝ)))
    have hsqrt : ContinuousAt (fun t => sqrt (log t / 5.573412)) t :=
      (Real.continuous_sqrt.continuousAt).comp hbase
    have hexp : ContinuousAt (fun t => exp (-1.89 * sqrt (log t / 5.573412))) t :=
      (Real.continuous_exp.continuousAt).comp (continuousAt_const.mul hsqrt)
    have hmul2 : ContinuousAt (fun t => c * (log t / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log t / 5.573412))) t :=
      (continuousAt_const.mul hrpow).mul hexp
    have hnum : ContinuousAt (fun t => (log t) ^ 5 * (c * (log t / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log t / 5.573412)))) t :=
      (hlog.pow 5).mul hmul2
    have hden2 : ContinuousAt (fun t => log t ^ 7) t := (hlog.pow 7)
    exact hnum.div hden2 (hI_log_ne t ht)

  have hg4_cont : ContinuousOn g4 I := by
    simpa [g4] using hcont46 462.0
  have hg5_cont : ContinuousOn g5 I := by
    simpa [g5] using hcont46 411.5
  have hg6_cont : ContinuousOn g6 I := by
    simpa [g6] using hcont46 379.7

  have hg1_int_I : IntegrableOn g1 I volume := ContinuousOn.integrableOn_Icc hg1_cont
  have hg2_int_I : IntegrableOn g2 I volume := ContinuousOn.integrableOn_Icc hg2_cont
  have hg3_int_I : IntegrableOn g3 I volume := ContinuousOn.integrableOn_Icc hg3_cont
  have hg4_int_I : IntegrableOn g4 I volume := ContinuousOn.integrableOn_Icc hg4_cont
  have hg5_int_I : IntegrableOn g5 I volume := ContinuousOn.integrableOn_Icc hg5_cont
  have hg6_int_I : IntegrableOn g6 I volume := ContinuousOn.integrableOn_Icc hg6_cont

  have hS1_meas : MeasurableSet S1 := by
    dsimp [S1, I, A1]
    exact measurableSet_Icc.inter measurableSet_Ico
  have hS2_meas : MeasurableSet S2 := by
    dsimp [S2, I, A1, A2]
    exact (measurableSet_Icc.inter measurableSet_Ico.compl).inter measurableSet_Ico
  have hS3_meas : MeasurableSet S3 := by
    dsimp [S3, I, A1, A2, A3]
    exact ((measurableSet_Icc.inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico
  have hS4_meas : MeasurableSet S4 := by
    dsimp [S4, I, A1, A2, A3, A4]
    exact (((measurableSet_Icc.inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico
  have hS5_meas : MeasurableSet S5 := by
    dsimp [S5, I, A1, A2, A3, A4, A5]
    exact ((((measurableSet_Icc.inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico
  have hS6_meas : MeasurableSet S6 := by
    dsimp [S6, I, A1, A2, A3, A4, A5]
    exact ((((measurableSet_Icc.inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico.compl).inter measurableSet_Ico.compl

  have hg1_int_S1 : IntegrableOn g1 S1 volume := hg1_int_I.mono_set (by intro t ht; exact ht.1)
  have hg2_int_S2 : IntegrableOn g2 S2 volume := hg2_int_I.mono_set (by intro t ht; exact ht.1.1)
  have hg3_int_S3 : IntegrableOn g3 S3 volume := hg3_int_I.mono_set (by intro t ht; exact ht.1.1.1)
  have hg4_int_S4 : IntegrableOn g4 S4 volume := hg4_int_I.mono_set (by intro t ht; exact ht.1.1.1.1)
  have hg5_int_S5 : IntegrableOn g5 S5 volume := hg5_int_I.mono_set (by intro t ht; exact ht.1.1.1.1.1)
  have hg6_int_S6 : IntegrableOn g6 S6 volume := hg6_int_I.mono_set (by intro t ht; exact ht.1.1.1.1.1)

  have hEq1 : EqOn f g1 S1 := by
    intro t ht
    have h1 : t ∈ Set.Ico 2 599 := by simpa [A1] using ht.2
    dsimp [f, g1]
    unfold a
    simp [h1]

  have hEq2 : EqOn f g2 S2 := by
    intro t ht
    have h1 : t ∉ Set.Ico 2 599 := by simpa [A1] using ht.1.2
    have h2 : t ∈ Set.Ico 599 (exp 58) := by simpa [A2] using ht.2
    dsimp [f, g2]
    unfold a
    simp [h1, h2]

  have hEq3 : EqOn f g3 S3 := by
    intro t ht
    have h1 : t ∉ Set.Ico 2 599 := by simpa [A1] using ht.1.1.2
    have h2 : t ∉ Set.Ico 599 (exp 58) := by simpa [A2] using ht.1.2
    have h3 : t ∈ Set.Ico (exp 58) (exp 1169) := by simpa [A3] using ht.2
    dsimp [f, g3]
    unfold a
    simp [h1, h2, h3]

  have hEq4 : EqOn f g4 S4 := by
    intro t ht
    have h1 : t ∉ Set.Ico 2 599 := by simpa [A1] using ht.1.1.1.2
    have h2 : t ∉ Set.Ico 599 (exp 58) := by simpa [A2] using ht.1.1.2
    have h3 : t ∉ Set.Ico (exp 58) (exp 1169) := by simpa [A3] using ht.1.2
    have h4 : t ∈ Set.Ico (exp 1169) (exp 2000) := by simpa [A4] using ht.2
    dsimp [f, g4]
    unfold a
    simp [h1, h2, h3, h4]

  have hEq5 : EqOn f g5 S5 := by
    intro t ht
    have h1 : t ∉ Set.Ico 2 599 := by simpa [A1] using ht.1.1.1.1.2
    have h2 : t ∉ Set.Ico 599 (exp 58) := by simpa [A2] using ht.1.1.1.2
    have h3 : t ∉ Set.Ico (exp 58) (exp 1169) := by simpa [A3] using ht.1.1.2
    have h4 : t ∉ Set.Ico (exp 1169) (exp 2000) := by simpa [A4] using ht.1.2
    have h5 : t ∈ Set.Ico (exp 2000) (exp 3000) := by simpa [A5] using ht.2
    dsimp [f, g5]
    unfold a
    simp [h1, h2, h3, h4, h5]

  have hEq6 : EqOn f g6 S6 := by
    intro t ht
    have h1 : t ∉ Set.Ico 2 599 := by simpa [A1] using ht.1.1.1.1.2
    have h2 : t ∉ Set.Ico 599 (exp 58) := by simpa [A2] using ht.1.1.1.2
    have h3 : t ∉ Set.Ico (exp 58) (exp 1169) := by simpa [A3] using ht.1.1.2
    have h4 : t ∉ Set.Ico (exp 1169) (exp 2000) := by simpa [A4] using ht.1.2
    have h5 : t ∉ Set.Ico (exp 2000) (exp 3000) := by simpa [A5] using ht.2
    dsimp [f, g6]
    unfold a
    simp [h1, h2, h3, h4, h5]

  have hf_int_S1 : IntegrableOn f S1 volume := (integrableOn_congr_fun hEq1 hS1_meas).2 hg1_int_S1
  have hf_int_S2 : IntegrableOn f S2 volume := (integrableOn_congr_fun hEq2 hS2_meas).2 hg2_int_S2
  have hf_int_S3 : IntegrableOn f S3 volume := (integrableOn_congr_fun hEq3 hS3_meas).2 hg3_int_S3
  have hf_int_S4 : IntegrableOn f S4 volume := (integrableOn_congr_fun hEq4 hS4_meas).2 hg4_int_S4
  have hf_int_S5 : IntegrableOn f S5 volume := (integrableOn_congr_fun hEq5 hS5_meas).2 hg5_int_S5
  have hf_int_S6 : IntegrableOn f S6 volume := (integrableOn_congr_fun hEq6 hS6_meas).2 hg6_int_S6

  let U : Set ℝ := S1 ∪ (S2 ∪ (S3 ∪ (S4 ∪ (S5 ∪ S6))))

  have hU_int : IntegrableOn f U volume := by
    dsimp [U]
    exact hf_int_S1.union (hf_int_S2.union (hf_int_S3.union (hf_int_S4.union (hf_int_S5.union hf_int_S6))))

  have hU_eq_I : U = I := by
    ext t
    constructor
    · intro ht
      dsimp [U, S1, S2, S3, S4, S5, S6] at ht
      rcases ht with hS1 | hrest
      · exact hS1.1
      · rcases hrest with hS2 | hrest
        · exact hS2.1.1
        · rcases hrest with hS3 | hrest
          · exact hS3.1.1.1
          · rcases hrest with hS4 | hrest
            · exact hS4.1.1.1.1
            · rcases hrest with hS5 | hS6
              · exact hS5.1.1.1.1.1
              · exact hS6.1.1.1.1.1
    · intro ht
      by_cases h1 : t ∈ A1
      · exact Or.inl ⟨ht, h1⟩
      · by_cases h2 : t ∈ A2
        · exact Or.inr (Or.inl ⟨⟨ht, h1⟩, h2⟩)
        · by_cases h3 : t ∈ A3
          · exact Or.inr (Or.inr (Or.inl ⟨⟨⟨ht, h1⟩, h2⟩, h3⟩))
          · by_cases h4 : t ∈ A4
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨⟨⟨ht, h1⟩, h2⟩, h3⟩, h4⟩)))
            · by_cases h5 : t ∈ A5
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨⟨⟨⟨ht, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨⟨⟨⟨ht, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩))))

  have hI_int : IntegrableOn f I volume := by
    simpa [hU_eq_I] using hU_int
  simpa [f, I] using hI_int

lemma log_6_IBP_t (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 6 =
      x / log x ^ 6 - 2 / log 2 ^ 6 +
        6 * ∫ t in Set.Icc 2 x, 1 / log t ^ 7 := by
  suffices h_ibp : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (log t) ^ 6) = (b / (log b) ^ 6) - (a / (log a) ^ 6) +
        6 * ∫ t in a..b, (1 / (log t) ^ 7) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (log t) ^ 6) t =
        1 / (log t) ^ 6 - 6 * (1 / (log t) ^ 7) := by
    intro t ht
    norm_num [differentiableAt_log, ne_of_gt (show 0 < log t from log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (log t) ^ 6) t =
      (b / (log b) ^ 6) - (a / (log a) ^ 6) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun x hx ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (differentiableAt_log
          (by cases Set.mem_uIcc.mp hx <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| log_pos <|
          by cases Set.mem_uIcc.mp hx <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ (n : ℕ), ∀ y ∈ Set.Icc a b, log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| log_pos <| by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt fun x hx ↦
      ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
        (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))
  · exact ContinuousOn.intervalIntegrable ((continuousOn_const.mul
      (continuousOn_of_forall_continuousAt fun x hx ↦
        ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
          (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))))

lemma log_5_IBP_t (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 5 =
      x / log x ^ 5 - 2 / log 2 ^ 5 +
        5 * ∫ t in Set.Icc 2 x, 1 / log t ^ 6 := by
  suffices h_ibp : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (log t) ^ 5) = (b / (log b) ^ 5) - (a / (log a) ^ 5) +
        5 * ∫ t in a..b, (1 / (log t) ^ 6) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (log t) ^ 5) t =
        1 / (log t) ^ 5 - 5 * (1 / (log t) ^ 6) := by
    intro t ht
    norm_num [differentiableAt_log, ne_of_gt (show 0 < log t from log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (log t) ^ 5) t =
      (b / (log b) ^ 5) - (a / (log a) ^ 5) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun x hx ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (differentiableAt_log
          (by cases Set.mem_uIcc.mp hx <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| log_pos <|
          by cases Set.mem_uIcc.mp hx <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ (n : ℕ), ∀ y ∈ Set.Icc a b, log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| log_pos <| by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt fun x hx ↦
      ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
        (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))
  · exact ContinuousOn.intervalIntegrable ((continuousOn_const.mul
      (continuousOn_of_forall_continuousAt fun x hx ↦
        ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
          (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))))

lemma log_4_IBP_t (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 4 =
      x / log x ^ 4 - 2 / log 2 ^ 4 +
        4 * ∫ t in Set.Icc 2 x, 1 / log t ^ 5 := by
  suffices h_ibp : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (log t) ^ 4) = (b / (log b) ^ 4) - (a / (log a) ^ 4) +
        4 * ∫ t in a..b, (1 / (log t) ^ 5) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (log t) ^ 4) t =
        1 / (log t) ^ 4 - 4 * (1 / (log t) ^ 5) := by
    intro t ht
    norm_num [differentiableAt_log, ne_of_gt (show 0 < log t from log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (log t) ^ 4) t =
      (b / (log b) ^ 4) - (a / (log a) ^ 4) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun x hx ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (differentiableAt_log
          (by cases Set.mem_uIcc.mp hx <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| log_pos <|
          by cases Set.mem_uIcc.mp hx <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ (n : ℕ), ∀ y ∈ Set.Icc a b, log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| log_pos <| by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt fun x hx ↦
      ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
        (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))
  · exact ContinuousOn.intervalIntegrable ((continuousOn_const.mul
      (continuousOn_of_forall_continuousAt fun x hx ↦
        ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
          (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))))

lemma log_3_IBP_t (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 3 =
      x / log x ^ 3 - 2 / log 2 ^ 3 +
        3 * ∫ t in Set.Icc 2 x, 1 / log t ^ 4 := by
  suffices h_ibp : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (log t) ^ 3) = (b / (log b) ^ 3) - (a / (log a) ^ 3) +
        3 * ∫ t in a..b, (1 / (log t) ^ 4) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (log t) ^ 3) t =
        1 / (log t) ^ 3 - 3 * (1 / (log t) ^ 4) := by
    intro t ht
    norm_num [differentiableAt_log, ne_of_gt (show 0 < log t from log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (log t) ^ 3) t =
      (b / (log b) ^ 3) - (a / (log a) ^ 3) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun x hx ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (differentiableAt_log
          (by cases Set.mem_uIcc.mp hx <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| log_pos <|
          by cases Set.mem_uIcc.mp hx <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ (n : ℕ), ∀ y ∈ Set.Icc a b, log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| log_pos <| by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt fun x hx ↦
      ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
        (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))
  · exact ContinuousOn.intervalIntegrable ((continuousOn_const.mul
      (continuousOn_of_forall_continuousAt fun x hx ↦
        ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
          (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))))

lemma log_2_IBP_t (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 2 =
      x / log x ^ 2 - 2 / log 2 ^ 2 +
        2 * ∫ t in Set.Icc 2 x, 1 / log t ^ 3 := by
  suffices h_ibp : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (log t) ^ 2) = (b / (log b) ^ 2) - (a / (log a) ^ 2) +
        2 * ∫ t in a..b, (1 / (log t) ^ 3) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (log t) ^ 2) t =
        1 / (log t) ^ 2 - 2 * (1 / (log t) ^ 3) := by
    intro t ht
    norm_num [differentiableAt_log, ne_of_gt (show 0 < log t from log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (log t) ^ 2) t =
      (b / (log b) ^ 2) - (a / (log a) ^ 2) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun x hx ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (differentiableAt_log
          (by cases Set.mem_uIcc.mp hx <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| log_pos <|
          by cases Set.mem_uIcc.mp hx <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ (n : ℕ), ∀ y ∈ Set.Icc a b, log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| log_pos <| by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt fun x hx ↦
      ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
        (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))
  · exact ContinuousOn.intervalIntegrable ((continuousOn_const.mul
      (continuousOn_of_forall_continuousAt fun x hx ↦
        ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)
          (ne_of_gt (pow_pos (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])) _)))))

lemma log_2_expansion_t (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 2 =
      x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5 + 120 * x / log x ^ 6
      - 2 * (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)) + 720 * ∫ t in Set.Icc 2 x, 1 / log t ^ 7 := by
  rw [log_2_IBP_t x hx, log_3_IBP_t x hx, log_4_IBP_t x hx, log_5_IBP_t x hx, log_6_IBP_t x hx]
  have hsum :
      (∑ k ∈ Finset.Icc 1 5, (k.factorial : ℝ) / log 2 ^ (k + 1)) =
        (log 2)⁻¹ ^ 2 + (log 2)⁻¹ ^ 3 * 2 + (log 2)⁻¹ ^ 4 * 6 + (log 2)⁻¹ ^ 5 * 24 + (log 2)⁻¹ ^ 6 * 120 := by
    norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
    ring_nf
  rw [hsum]
  ring_nf

private lemma integral_Icc_split_at_xa (f : ℝ → ℝ) (x : ℝ) (h2xa : 2 ≤ xₐ) (hxax : xₐ ≤ x)
    (hInt : IntegrableOn f (Set.Icc 2 x) volume) :
    ∫ t in Set.Icc 2 x, f t = (∫ t in Set.Icc 2 xₐ, f t) + (∫ t in Set.Icc xₐ x, f t) := by
  have hx2 : 2 ≤ x := le_trans h2xa hxax
  have h_int_left : IntegrableOn f (Set.Icc 2 xₐ) volume :=
    hInt.mono_set (by intro t ht; exact ⟨ht.1, le_trans ht.2 hxax⟩)
  have h_int_right : IntegrableOn f (Set.Icc xₐ x) volume :=
    hInt.mono_set (by intro t ht; exact ⟨by linarith [h2xa, ht.1], ht.2⟩)
  have h_int_left_u : IntegrableOn f (Set.uIcc 2 xₐ) volume := by
    simpa [Set.uIcc_of_le h2xa] using h_int_left
  have h_int_right_u : IntegrableOn f (Set.uIcc xₐ x) volume := by
    simpa [Set.uIcc_of_le hxax] using h_int_right
  have h_split_interval :
      ∫ t in (2 : ℝ)..x, f t =
        (∫ t in (2 : ℝ)..xₐ, f t) + (∫ t in xₐ..x, f t) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (MeasureTheory.IntegrableOn.intervalIntegrable h_int_left_u)
      (MeasureTheory.IntegrableOn.intervalIntegrable h_int_right_u)).symm
  simpa [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx2,
      intervalIntegral.integral_of_le h2xa,
      intervalIntegral.integral_of_le hxax] using h_split_interval

private lemma h_monotone_aux : MonotoneOn (fun y : ℝ => y - 12 * log y) (Set.Ici 12) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 12) ?_ ?_ ?_
  · exact continuousOn_id.sub (continuousOn_const.mul
      (continuousOn_log.mono (by intro y hy; exact ne_of_gt (lt_of_lt_of_le (by norm_num) (Set.mem_Ici.mp hy)))))
  · intro y hy
    rw [interior_Ici] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((hasDerivAt_id y).sub
      ((Real.hasDerivAt_log (show y ≠ 0 by linarith [Set.mem_Ioi.mp hy])).const_mul 12)).differentiableAt
  · intro y hy
    rw [interior_Ici] at hy
    have hypos : 0 < y := by linarith [Set.mem_Ioi.mp hy]
    have hderiv : deriv (fun y : ℝ => y - 12 * log y) y = 1 - 12 * y⁻¹ :=
      ((hasDerivAt_id y).sub
        ((Real.hasDerivAt_log (show y ≠ 0 by linarith [hypos])).const_mul 12)).deriv
    rw [hderiv]
    have hyge12 : 12 ≤ y := le_of_lt (Set.mem_Ioi.mp hy)
    have hyinv : 12 * y⁻¹ ≤ 1 := by
      have hdiv : 12 / y ≤ 1 := (div_le_iff₀ hypos).2 (by simpa using hyge12)
      simpa [div_eq_mul_inv] using hdiv
    nlinarith

private lemma ratio_bound_xa (x : ℝ) (hxax : xₐ ≤ x) : xₐ / log xₐ ^ 12 ≤ x / log x ^ 12 := by
  have h2xa : 2 ≤ xₐ := two_le_xₐ
  have hxapos : 0 < xₐ := xₐ_pos
  have hxpos : 0 < x := lt_of_lt_of_le hxapos hxax
  have h1xa : 1 < xₐ := one_lt_xₐ
  have h1x : 1 < x := lt_of_lt_of_le h1xa hxax
  have hlogapos : 0 < log xₐ := log_xₐ_pos
  have hlogpos : 0 < log x := log_pos h1x
  have hlogxa_le : log xₐ ≤ log x := log_le_log hxapos hxax
  have hlogxa_ge12 : 12 ≤ log xₐ := by
    rw [log_xₐ_val]
    norm_num
  have hlogx_ge12 : 12 ≤ log x := le_trans hlogxa_ge12 hlogxa_le
  have hh : log xₐ - 12 * log (log xₐ) ≤ log x - 12 * log (log x) :=
    h_monotone_aux (Set.mem_Ici.mpr hlogxa_ge12) (Set.mem_Ici.mpr hlogx_ge12) hlogxa_le
  rw [← log_le_log_iff (by positivity) (by positivity)]
  have hleft : log (xₐ / log xₐ ^ 12) = log xₐ - 12 * log (log xₐ) := by
    rw [log_div hxapos.ne' (pow_ne_zero _ hlogapos.ne'), log_pow]
    ring
  have hright : log (x / log x ^ 12) = log x - 12 * log (log x) := by
    rw [log_div hxpos.ne' (pow_ne_zero _ hlogpos.ne'), log_pow]
    ring
  linarith

private lemma ratio6_bound_xa (x : ℝ) (hxax : xₐ ≤ x) : xₐ / log xₐ ^ 6 ≤ x / log x ^ 6 := by
  have h2xa : 2 ≤ xₐ := two_le_xₐ
  have hxapos : 0 < xₐ := xₐ_pos
  have hxpos : 0 < x := lt_of_lt_of_le hxapos hxax
  have h1xa : 1 < xₐ := one_lt_xₐ
  have h1x : 1 < x := lt_of_lt_of_le h1xa hxax
  have hlogapos : 0 < log xₐ := log_xₐ_pos
  have hlogpos : 0 < log x := log_pos h1x
  have hlogxa_le : log xₐ ≤ log x := log_le_log hxapos hxax
  have hlogxa_ge12 : 12 ≤ log xₐ := by
    rw [log_xₐ_val]
    norm_num
  have hlogx_ge12 : 12 ≤ log x := le_trans hlogxa_ge12 hlogxa_le
  have hh : log xₐ - 6 * log (log xₐ) ≤ log x - 6 * log (log x) := by
    have hmono6 : MonotoneOn (fun y : ℝ => y - 6 * log y) (Set.Ici 6) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 6) ?_ ?_ ?_
      · exact continuousOn_id.sub (continuousOn_const.mul
          (continuousOn_log.mono (by intro y hy; exact ne_of_gt (lt_of_lt_of_le (by norm_num) (Set.mem_Ici.mp hy)))))
      · intro y hy
        rw [interior_Ici] at hy
        refine DifferentiableAt.differentiableWithinAt ?_
        exact ((hasDerivAt_id y).sub
          ((Real.hasDerivAt_log (show y ≠ 0 by linarith [Set.mem_Ioi.mp hy])).const_mul 6)).differentiableAt
      · intro y hy
        rw [interior_Ici] at hy
        have hypos : 0 < y := by linarith [Set.mem_Ioi.mp hy]
        have hderiv : deriv (fun y : ℝ => y - 6 * log y) y = 1 - 6 * y⁻¹ :=
          ((hasDerivAt_id y).sub
            ((Real.hasDerivAt_log (show y ≠ 0 by linarith [hypos])).const_mul 6)).deriv
        rw [hderiv]
        have hyge6 : 6 ≤ y := le_of_lt (Set.mem_Ioi.mp hy)
        have hyinv : 6 * y⁻¹ ≤ 1 := by
          have hdiv : 6 / y ≤ 1 := (div_le_iff₀ hypos).2 (by simpa using hyge6)
          simpa [div_eq_mul_inv] using hdiv
        nlinarith
    have hlogxa_ge6 : 6 ≤ log xₐ := le_trans (by norm_num) hlogxa_ge12
    have hlogx_ge6 : 6 ≤ log x := le_trans (by norm_num) hlogx_ge12
    exact hmono6 (Set.mem_Ici.mpr hlogxa_ge6) (Set.mem_Ici.mpr hlogx_ge6) hlogxa_le
  rw [← log_le_log_iff (by positivity) (by positivity)]
  have hleft : log (xₐ / log xₐ ^ 6) = log xₐ - 6 * log (log xₐ) := by
    rw [log_div hxapos.ne' (pow_ne_zero _ hlogapos.ne'), log_pow]
    ring
  have hright : log (x / log x ^ 6) = log x - 6 * log (log x) := by
    rw [log_div hxpos.ne' (pow_ne_zero _ hlogpos.ne'), log_pow]
    ring
  linarith

private lemma sqrt_bound_xa (x : ℝ) (hxax : xₐ ≤ x) :
    sqrt x ≤ x / log x ^ 6 * log xₐ ^ 6 / sqrt xₐ := by
  have hxapos : 0 < xₐ := xₐ_pos
  have hxpos : 0 < x := lt_of_lt_of_le hxapos hxax
  have h1x : 1 < x :=
    lt_of_lt_of_le one_lt_xₐ hxax
  have hlogpos : 0 < log x := log_pos h1x
  have hlogapos : 0 < log xₐ := log_xₐ_pos
  have hr : xₐ / log xₐ ^ 12 ≤ x / log x ^ 12 := ratio_bound_xa x hxax
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 : xₐ ≤ x * log xₐ ^ 12 / log x ^ 12 := by
    have hloga12_pos : 0 < log xₐ ^ 12 := by positivity
    have := (div_le_iff₀ hloga12_pos).mp hr
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hr' : x * xₐ ≤ x ^ 2 * log xₐ ^ 12 / log x ^ 12 := by
    have hm : x * xₐ ≤ x * (x * log xₐ ^ 12 / log x ^ 12) :=
      mul_le_mul_of_nonneg_left h1 hxpos.le
    have hmul : x * (x * log xₐ ^ 12 / log x ^ 12) = x ^ 2 * log xₐ ^ 12 / log x ^ 12 := by
      ring
    simpa [hmul] using hm
  have hsqrtxa_ne : sqrt xₐ ≠ 0 := ne_of_gt (sqrt_pos.mpr hxapos)
  have hsq' : (sqrt xₐ) ^ 2 = xₐ := by simpa [pow_two] using (sq_sqrt hxapos.le)
  have hcalc1 : (x / log x ^ 6 * log xₐ ^ 6 / sqrt xₐ) ^ 2 =
      x ^ 2 * log xₐ ^ 12 / (log x ^ 12 * (sqrt xₐ) ^ 2) := by
    field_simp [hlogpos.ne', hlogapos.ne', hsqrtxa_ne]
  rw [hcalc1, hsq']
  have : x * (log x ^ 12 * xₐ) ≤ x ^ 2 * log xₐ ^ 12 := by
    have hmul : x * xₐ * log x ^ 12 ≤ (x ^ 2 * log xₐ ^ 12 / log x ^ 12) * log x ^ 12 :=
      mul_le_mul_of_nonneg_right hr' (by positivity)
    have hlog12_ne : log x ^ 12 ≠ 0 := pow_ne_zero _ hlogpos.ne'
    have htmp : (x ^ 2 * log xₐ ^ 12 / log x ^ 12) * log x ^ 12 = x ^ 2 * log xₐ ^ 12 := by
      field_simp [hlog12_ne]
    nlinarith
  have hden_pos : 0 < log x ^ 12 * xₐ := by positivity
  exact (le_div_iff₀ hden_pos).2 <| by simpa [mul_assoc, mul_left_comm, mul_comm] using this

private lemma sqrt_term_bound_xa (x : ℝ) (hxax : xₐ ≤ x) :
    sqrt x / log 2 ^ 8 ≤ x / log x ^ 6 * (log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8)) := by
  have hsqrt := sqrt_bound_xa x hxax
  have := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ (log 2 ^ 8)⁻¹ by positivity)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

private lemma pi_upper_specific_h720Ia
    (x : ℝ)
    (ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 x) volume) :
    (720 : ℝ) * (∫ t in Set.Icc 2 x, 1 / log t ^ 7) + (∫ t in Set.Icc 2 x, a t / log t ^ 7)
      = ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7 := by
  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / log t ^ 7) (Set.Icc 2 x) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
      (continuousOn_log.mono <| by intro t ht; exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) fun t ht ↦
      pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1])
  have h720_int_mul : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ 7)) (Set.Icc 2 x) volume :=
    hJ_int.const_mul 720
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add h720_int_mul ha_int]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro t ht
  ring

private lemma pi_upper_specific_main_le
    (x : ℝ)
    (hx2 : 2 ≤ x)
    (hpi0 :
      pi x ≤ x / log x + a x * x / log x ^ 6 + (∫ t in Set.Icc 2 x, 1 / log t ^ 2)
        + ∫ t in Set.Icc 2 x, a t / log t ^ 7)
    (hI2 :
      ∫ t in Set.Icc 2 x, 1 / log t ^ 2 =
        x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5 + 120 * x / log x ^ 6
        - 2 * (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)) + 720 * ∫ t in Set.Icc 2 x, 1 / log t ^ 7)
    (hsumx :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) =
        x / log x + x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5)
    (hS_nonneg : 0 ≤ (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)))
    (hax_le : a x ≤ a exₐ)
    (h720Ia :
      (720 : ℝ) * (∫ t in Set.Icc 2 x, 1 / log t ^ 7) + (∫ t in Set.Icc 2 x, a t / log t ^ 7)
        = ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7) :
    pi x ≤ x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
      + ((120 + a exₐ) * x / log x ^ 6)
      + (∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7) := by
  let S : ℝ := ∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)
  let J : ℝ := ∫ t in Set.Icc 2 x, 1 / log t ^ 7
  let IA : ℝ := ∫ t in Set.Icc 2 x, a t / log t ^ 7
  let Q : ℝ := x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5 + 120 * x / log x ^ 6
  let P : ℝ := x / log x + x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5
  have hS_nonneg' : 0 ≤ S := by simpa [S] using hS_nonneg
  have htmp :
      pi x ≤ x / log x + a x * x / log x ^ 6
        + (x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5 + 120 * x / log x ^ 6
        - 2 * S + 720 * J)
        + IA := by
    have htmp0 := hpi0
    rw [hI2] at htmp0
    simpa [S, J, IA] using htmp0
  have htmp2 :
      pi x ≤ P + (120 + a exₐ) * x / log x ^ 6 + (720 * J + IA) := by
    have haxterm : a x * x / log x ^ 6 ≤ a exₐ * x / log x ^ 6 := by
      have hxlog6_nonneg : 0 ≤ x / log x ^ 6 :=
        div_nonneg (by linarith) (pow_nonneg (log_nonneg (by linarith)) 6)
      have hmul : a x * (x / log x ^ 6) ≤ a exₐ * (x / log x ^ 6) :=
        mul_le_mul_of_nonneg_right hax_le hxlog6_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
    have hdropS :
        Q - 2 * S + 720 * J ≤ Q + 720 * J := by
      linarith
    have htmpJ :
        pi x ≤ x / log x + a x * x / log x ^ 6 + (Q - 2 * S + 720 * J) + IA := by
      unfold Q
      simpa [J, IA] using htmp
    have hmidJ :
        x / log x + a x * x / log x ^ 6 + (Q - 2 * S + 720 * J) + IA
        ≤ x / log x + a exₐ * x / log x ^ 6 + (Q + 720 * J) + IA := by
      have h1 : x / log x + a x * x / log x ^ 6 ≤ x / log x + a exₐ * x / log x ^ 6 :=
        add_le_add_right haxterm (x / log x)
      have h2 : (Q - 2 * S + 720 * J) + IA ≤ (Q + 720 * J) + IA :=
        add_le_add_left hdropS IA
      have hsum := add_le_add h1 h2
      simpa [add_assoc] using hsum
    have htmp2raw :
        pi x ≤ x / log x + a exₐ * x / log x ^ 6 + (Q + 720 * J) + IA := le_trans htmpJ hmidJ
    have hEq :
        x / log x + a exₐ * x / log x ^ 6 + (Q + 720 * J) + IA
        = P + (120 + a exₐ) * x / log x ^ 6 + (720 * J + IA) := by
      unfold P Q
      ring
    simpa [hEq] using htmp2raw
  let G : ℝ := ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7
  have htmp3 :
      pi x ≤ P + (120 + a exₐ) * x / log x ^ 6 + G := by
    have h720IaJ : (720 : ℝ) * J + IA = G := by
      unfold G J IA
      simpa using h720Ia
    calc
      pi x ≤ P + (120 + a exₐ) * x / log x ^ 6 + (720 * J + IA) := htmp2
      _ = P + (120 + a exₐ) * x / log x ^ 6 + G := by
        rw [h720IaJ]
  have hsum_form :
      P = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) := by
    unfold P
    exact hsumx.symm
  calc
    pi x ≤ P + (120 + a exₐ) * x / log x ^ 6 + G := htmp3
    _ = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
          + (120 + a exₐ) * x / log x ^ 6 + G := by
      rw [hsum_form]
    _ = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
          + (120 + a exₐ) * x / log x ^ 6
          + (∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7) := by
      simp [G, add_assoc]
@[blueprint
  "pi-upper-specific"
  (title := "Specific upper bound on pi")
  (statement := /-- For $x > ex_a$, $$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$. -/)
  (proof := /-- This follows from the previous lemmas and calculations, including Lemma \ref{log-7-int-bound}. -/)
  (latexEnv := "lemma")
  (discussion := 996)]
theorem pi_upper_specific : ∀ x > exₐ, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + ((Mₐ exₐ) * x / log x ^ 6) := by
  intro x hx
  have h2xa : 2 ≤ xₐ := two_le_xₐ
  have hxa_exa : xₐ ≤ exₐ := xₐ_le_exₐ
  have hxax : xₐ ≤ x := le_trans hxa_exa (le_of_lt hx)
  have hx2 : 2 ≤ x := by linarith
  have hxapos : 0 < xₐ := xₐ_pos
  have hxpos : 0 < x := by linarith
  have hexax : exₐ ≤ x := le_of_lt hx

  have htheta : ∀ t ≥ 2, |θ t - t| * log t ^ 5 ≤ t * a t := by
    intro t ht
    exact pi_bound_abs_mul t ht

  have ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 x) volume :=
    integrable_a_over_log7_piecewise x hx2

  have hpi0 :
      pi x ≤ x / log x + a x * x / log x ^ 6 + (∫ t in Set.Icc 2 x, 1 / log t ^ 2)
        + ∫ t in Set.Icc 2 x, a t / log t ^ 7 :=
    pi_upper a htheta x ha_int hx2

  have hI2 :
      ∫ t in Set.Icc 2 x, 1 / log t ^ 2 =
        x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5 + 120 * x / log x ^ 6
        - 2 * (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)) + 720 * ∫ t in Set.Icc 2 x, 1 / log t ^ 7 :=
    log_2_expansion_t x hx2

  have hsumx :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) =
        x / log x + x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring

  have hS_nonneg : 0 ≤ (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)) := by
    refine Finset.sum_nonneg ?_
    intro k hk
    exact div_nonneg (by positivity) (pow_nonneg (log_nonneg (by norm_num)) _)

  have ha_nonneg : ∀ t ≥ 2, 0 ≤ a t := by
    intro t ht
    have hpb : |θ t - t| * log t ^ 5 ≤ t * a t := htheta t ht
    have hL_nonneg : 0 ≤ |θ t - t| * log t ^ 5 :=
      mul_nonneg (abs_nonneg _) (pow_nonneg (log_nonneg (by linarith : (1 : ℝ) ≤ t)) 5)
    have hR_nonneg : 0 ≤ t * a t := le_trans hL_nonneg hpb
    nlinarith

  have hax_le : a x ≤ a exₐ :=
    a_mono (Set.mem_Ici.mpr hxa_exa) (Set.mem_Ici.mpr hxax) hexax

  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / log t ^ 7) (Set.Icc 2 x) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
      (continuousOn_log.mono <| by intro t ht; exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) fun t ht ↦
      pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1])

  have h720_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7) (Set.Icc 2 x) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ 7)) (Set.Icc 2 x) volume :=
      hJ_int.const_mul 720
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring

  have h_add_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7 + a t / log t ^ 7) (Set.Icc 2 x) volume :=
    h720_int.add ha_int

  have hG_int : IntegrableOn (fun t : ℝ ↦ (720 + a t) / log t ^ 7) (Set.Icc 2 x) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 h_add_int
    intro t ht
    ring

  have h720Ia :
      (720 : ℝ) * (∫ t in Set.Icc 2 x, 1 / log t ^ 7) + (∫ t in Set.Icc 2 x, a t / log t ^ 7)
        = ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7 :=
    pi_upper_specific_h720Ia x ha_int

  have hsplitG :
      ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7 =
        (∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7) +
        (∫ t in Set.Icc xₐ x, (720 + a t) / log t ^ 7) :=
    integral_Icc_split_at_xa (fun t ↦ (720 + a t) / log t ^ 7) x h2xa hxax hG_int

  have htail_le :
      ∫ t in Set.Icc xₐ x, (720 + a t) / log t ^ 7 ≤
        (720 + a xₐ) * ∫ t in Set.Icc xₐ x, 1 / log t ^ 7 := by
    have htail_int : IntegrableOn (fun t : ℝ ↦ (720 + a t) / log t ^ 7) (Set.Icc xₐ x) volume :=
      hG_int.mono_set (by intro t ht; exact ⟨by linarith [h2xa, ht.1], ht.2⟩)
    have hconst_int : IntegrableOn (fun t : ℝ ↦ (720 + a xₐ) / log t ^ 7) (Set.Icc xₐ x) volume :=
      (ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
        (continuousOn_log.mono <| by intro t ht; exact ne_of_gt (lt_of_lt_of_le (by linarith [h2xa]) ht.1)) _)
        fun t ht ↦ pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [h2xa, ht.1]))
    have hpt : ∀ t ∈ Set.Icc xₐ x, (720 + a t) / log t ^ 7 ≤ (720 + a xₐ) / log t ^ 7 := by
      intro t ht
      have hat : a t ≤ a xₐ :=
        a_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.1) ht.1
      have hden_nonneg : 0 ≤ log t ^ 7 :=
        pow_nonneg (log_nonneg (by linarith [h2xa, ht.1])) 7
      have hnum : 720 + a t ≤ 720 + a xₐ := by linarith
      exact div_le_div_of_nonneg_right hnum hden_nonneg
    have := MeasureTheory.setIntegral_mono_on htail_int hconst_int measurableSet_Icc hpt
    have hconst_factor :
        ∫ t in Set.Icc xₐ x, (720 + a xₐ) / log t ^ 7 =
          (720 + a xₐ) * ∫ t in Set.Icc xₐ x, 1 / log t ^ 7 := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
      intro t ht
      ring
    simpa [hconst_factor] using this

  have hJtail_le :
      ∫ t in Set.Icc xₐ x, 1 / log t ^ 7 ≤ ∫ t in Set.Icc 2 x, 1 / log t ^ 7 := by
    refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
    · exact hJ_int
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      exact one_div_nonneg.mpr (pow_nonneg (log_nonneg (by linarith [ht.1])) _)
    · exact MeasureTheory.ae_of_all _ (fun t ht ↦ ⟨by linarith [ht.1, h2xa], ht.2⟩)

  have haxa_nonneg : 0 ≤ a xₐ := ha_nonneg xₐ h2xa
  have h720axa_nonneg : 0 ≤ 720 + a xₐ := by linarith
  have h720axa_pos : 0 < 720 + a xₐ := by linarith

  have hJfull_lt :
      ∫ t in Set.Icc 2 x, 1 / log t ^ 7 <
        x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8) :=
    log_7_int_bound x hx2

  have htail_lt :
      ∫ t in Set.Icc xₐ x, (720 + a t) / log t ^ 7 <
        (720 + a xₐ) * (x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8)) := by
    have hJtail_lt : ∫ t in Set.Icc xₐ x, 1 / log t ^ 7 <
        x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8) :=
      lt_of_le_of_lt hJtail_le hJfull_lt
    have hm := mul_lt_mul_of_pos_left hJtail_lt h720axa_pos
    grind

  have hI0_eq :
      ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 = C₁ * xₐ / log xₐ ^ 6 := by
    have hlogxapos0 : 0 < log xₐ := log_xₐ_pos
    have htmp : C₁ = log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 := rfl
    have htmp2 : C₁ * xₐ / log xₐ ^ 6 = ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 := by
      rw [htmp]
      field_simp [hxapos.ne', hlogxapos0.ne']
    exact htmp2.symm

  have hlogxapos : 0 < log xₐ := log_xₐ_pos
  have hlogxpos : 0 < log x := log_pos (by linarith)
  have hlog_le : log xₐ ≤ log x := log_le_log hxapos hxax
  have hinv_log : (log x)⁻¹ ≤ (log xₐ)⁻¹ := inv_anti₀ hlogxapos hlog_le

  have hterm1 : x / log x ^ 7 ≤ x / log x ^ 6 * (1 / log xₐ) := by
    have : (1 / log x) ≤ (1 / log xₐ) := by simpa [one_div] using hinv_log
    calc
      x / log x ^ 7 = (x / log x ^ 6) * (1 / log x) := by
        field_simp [hlogxpos.ne']
      _ ≤ (x / log x ^ 6) * (1 / log xₐ) := by gcongr

  have hterm2 : 2 ^ 8 * x / log x ^ 8 ≤ x / log x ^ 6 * (2 ^ 8 / log xₐ ^ 2) := by
    have hpow2 : (log x)⁻¹ ^ 2 ≤ (log xₐ)⁻¹ ^ 2 := by
      gcongr
    have : 2 ^ 8 / log x ^ 2 ≤ 2 ^ 8 / log xₐ ^ 2 := by
      simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hpow2 (by positivity : 0 ≤ (2 ^ 8 : ℝ)))
    calc
      2 ^ 8 * x / log x ^ 8 = (x / log x ^ 6) * (2 ^ 8 / log x ^ 2) := by
        field_simp [hlogxpos.ne']
      _ ≤ (x / log x ^ 6) * (2 ^ 8 / log xₐ ^ 2) := by gcongr

  have hterm3 :
      sqrt x / log 2 ^ 8 ≤ x / log x ^ 6 * (log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8)) :=
    sqrt_term_bound_xa x hxax

  have hB :
      x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8)
        ≤ x / log x ^ 6 * B := by
    have hterm2' : 7 * 2 ^ 8 * x / log x ^ 8 ≤ x / log x ^ 6 * (7 * 2 ^ 8 / log xₐ ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hterm2 (by positivity : 0 ≤ (7 : ℝ))
      ring_nf at hmul ⊢
      exact hmul
    have hsum12 : x / log x ^ 7 + 7 * 2 ^ 8 * x / log x ^ 8 ≤
        x / log x ^ 6 * (1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2) := by
      nlinarith
    have hsum_all :
        x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8)
          ≤ x / log x ^ 7 + 7 * (x / log x ^ 6 * (log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8)) + 2 ^ 8 * x / log x ^ 8) := by
      gcongr
    calc
      x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8)
          ≤ x / log x ^ 7 + 7 * (x / log x ^ 6 * (log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8)) + 2 ^ 8 * x / log x ^ 8) := hsum_all
      _ = (x / log x ^ 7 + 7 * 2 ^ 8 * x / log x ^ 8) + x / log x ^ 6 * (7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8)) := by
        ring
      _ ≤ x / log x ^ 6 * (1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2) + x / log x ^ 6 * (7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8)) := by
        gcongr
      _ = x / log x ^ 6 * B := by
        unfold B
        ring

  have hC1_nonneg : 0 ≤ C₁ := by
    unfold C₁
    refine mul_nonneg ?_ ?_
    · positivity
    · apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      have ha_t : 0 ≤ a t := ha_nonneg t ht.1
      have hnum : 0 ≤ 720 + a t := by linarith
      have hden : 0 ≤ log t ^ 7 :=
        pow_nonneg (log_nonneg (by linarith [ht.1])) 7
      exact div_nonneg hnum hden

  have hratio6 : xₐ / log xₐ ^ 6 ≤ x / log x ^ 6 :=
    ratio6_bound_xa x hxax

  have hI0_le :
      ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 ≤ C₁ * x / log x ^ 6 := by
    rw [hI0_eq]
    have hm0 : C₁ * (xₐ / log xₐ ^ 6) ≤ C₁ * (x / log x ^ 6) :=
      mul_le_mul_of_nonneg_left hratio6 hC1_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hm0

  have htail_B_lt :
      ∫ t in Set.Icc xₐ x, (720 + a t) / log t ^ 7 <
        (720 + a xₐ) * (x / log x ^ 6 * B) := by
    have htmp :
        (720 + a xₐ) * (x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8))
          ≤ (720 + a xₐ) * (x / log x ^ 6 * B) :=
      mul_le_mul_of_nonneg_left hB h720axa_nonneg
    grind

  have hG_lt :
      ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7 <
        C₁ * x / log x ^ 6 +
        (720 + a xₐ) * (x / log x ^ 6 * B) := by
    rw [hsplitG]
    exact add_lt_add_of_le_of_lt hI0_le htail_B_lt

  have hmain_le :
      pi x ≤ x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + ((120 + a exₐ) * x / log x ^ 6)
        + (∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7) :=
    pi_upper_specific_main_le x hx2 hpi0 hI2 hsumx hS_nonneg hax_le h720Ia

  have hfinal_lt :
      pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (120 + a exₐ) * x / log x ^ 6
        + (C₁ * x / log x ^ 6
        + (720 + a xₐ) * (x / log x ^ 6 * B)) := by
    have hmain_lt :
        x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
          + ((120 + a exₐ) * x / log x ^ 6)
          + (∫ t in Set.Icc 2 x, (720 + a t) / log t ^ 7)
        < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
          + ((120 + a exₐ) * x / log x ^ 6)
          + (C₁ * x / log x ^ 6 + (720 + a xₐ) * (x / log x ^ 6 * B)) := by
      gcongr
    grind

  have hMa_eq :
      (120 + a exₐ) * x / log x ^ 6
        + (C₁ * x / log x ^ 6 + (720 + a xₐ) * (x / log x ^ 6 * B))
      = Mₐ exₐ * x / log x ^ 6 := by
    unfold Mₐ
    ring

  calc
    pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
      + ((120 + a exₐ) * x / log x ^ 6
      + (C₁ * x / log x ^ 6 + (720 + a xₐ) * (x / log x ^ 6 * B))) := by
      linarith
    _ = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + ((Mₐ exₐ) * x / log x ^ 6) := by
      rw [hMa_eq]

private theorem a_eq_admissible_ge_3000 {z : ℝ} (hz : z ≥ exp 3000) :
    a z = admissible_bound (379.7 * 5.573412 ^ 5) 6.52 1.89 5.573412 z := by
  have h599 : (599 : ℝ) ≤ exp 3000 := by linarith [add_one_le_exp (3000 : ℝ)]
  have h58 : exp 58 ≤ exp 3000 := exp_le_exp.mpr (by norm_num)
  have h1169 : exp 1169 ≤ exp 3000 := exp_le_exp.mpr (by norm_num)
  have h2000 : exp 2000 ≤ exp 3000 := exp_le_exp.mpr (by norm_num)
  unfold a admissible_bound
  simp only [not_mem_Ico_of_ge_exp3000 hz h599, not_mem_Ico_of_ge_exp3000 hz h58,
    not_mem_Ico_of_ge_exp3000 hz h1169, not_mem_Ico_of_ge_exp3000 hz h2000,
    not_mem_Ico_of_ge_exp3000 hz le_rfl, ite_false, sqrt_eq_rpow]
  have hlogz : 0 < log z := by
    have hz1 : (1 : ℝ) < z := by
      have h1 : (1 : ℝ) < exp 3000 :=
        Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 3000)
      linarith
    exact log_pos hz1
  have hdiv : 0 < log z / 5.573412 := by positivity
  have hpow : (log z) ^ (5 : ℕ) = 5.573412 ^ (5 : ℕ) * (log z / 5.573412) ^ (5 : ℕ) := by
    rw [show log z = 5.573412 * (log z / 5.573412) by field_simp]
    ring
  rw [hpow]
  conv_lhs =>
    rw [show ∀ (u v w r s : ℝ), u * v * (w * r * s) = w * u * (v * r) * s from by
      intro u v w r s; ring]
  rw [← rpow_652_split hdiv]

private theorem a_exp_upper {L C : ℝ}
    (hL : 3000 ≤ L)
    (hpow5 : (5.573412 : ℝ) ^ (5 : ℕ) * ((L / 5.573412) ^ (5 : ℕ)) = L ^ (5 : ℕ))
    (haux : ∀ y ∈ Set.Icc L L, styleVal y ≤ C) :
    a (exp L) ≤ C := by
  exact
    Calculations.a_exp_upper_of (a := a)
      (ha_eq_admissible_ge_3000 := by
        intro z hz
        exact a_eq_admissible_ge_3000 hz)
      hL hpow5 haux

private theorem a_xa_upper : a xₐ ≤ (1311 : ℝ) := by
  simpa [xₐ] using
    (a_exp_upper (L := (3914 : ℝ)) (C := (1311 : ℝ)) (by norm_num) (by norm_num)
      styleVal_bound_3914_1311)

private theorem a_3870_upper : a (exp 3870) ≤ (1800 : ℝ) := by
  simpa using
    (a_exp_upper (L := (3870 : ℝ)) (C := (1800 : ℝ)) (by norm_num) (by norm_num)
      styleVal_bound_3870_1800)

private theorem B_nonneg : 0 ≤ B := by
  unfold B
  rw [log_xₐ_val]
  positivity

private theorem B_le_small : B ≤ (3 : ℝ) / 8000 :=
  Calculations.B_le_small_of (xₐ := xₐ) rfl log_xₐ_val

private theorem a_nonneg {z : ℝ} (hz : 2 ≤ z) : 0 ≤ a z := by
  unfold a
  have hzlog : 0 ≤ log z := log_nonneg (by linarith [hz])
  by_cases h1 : z ∈ Set.Ico 2 599
  · simp only [h1, ↓reduceIte]
    have hconst : 0 ≤ (1 - log 2 / 3 : ℝ) := by linarith [log_two_lt_d9]
    exact mul_nonneg (pow_nonneg hzlog 5) hconst
  · by_cases h2 : z ∈ Set.Ico 599 (exp 58)
    · simp only [h1, ↓reduceIte, h2]
      positivity
    · by_cases h3 : z ∈ Set.Ico (exp 58) (exp 1169)
      · simp only [h1, ↓reduceIte, h2, h3, Nat.ofNat_nonneg, sqrt_div, sqrt_mul, one_div]
        positivity
      · by_cases h4 : z ∈ Set.Ico (exp 1169) (exp 2000)
        · simp only [h1, ↓reduceIte, h2, h3, h4, neg_mul]
          positivity
        · by_cases h5 : z ∈ Set.Ico (exp 2000) (exp 3000) <;>
          simp only [h1, ↓reduceIte, h2, h3, h4, h5, neg_mul] <;> positivity

private theorem a_mono_3000 : AntitoneOn a (Set.Ici (exp 3000)) := by
  intro x hx y hy hxy
  change a y ≤ a x
  rw [a_eq_admissible_ge_3000 hy, a_eq_admissible_ge_3000 hx]
  exact admissible_bound.mono _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (Set.mem_Ici.mpr (le_trans
      (exp_le_exp.mpr (by norm_num) : exp (5.573412 * (2 * 6.52 / 1.89) ^ 2) ≤ exp 3000)
      hx))
    (Set.mem_Ici.mpr (le_trans
      (exp_le_exp.mpr (by norm_num) : exp (5.573412 * (2 * 6.52 / 1.89) ^ 2) ≤ exp 3000)
      hy))
    hxy

private theorem C₁_nonneg : 0 ≤ C₁ := by
  unfold C₁
  have hlogx : 0 ≤ log xₐ := by
    rw [log_xₐ_val]
    norm_num
  have hcoef_nonneg : 0 ≤ log xₐ ^ 6 / xₐ := by
    have hxan : 0 ≤ xₐ := by
      unfold xₐ
      positivity
    exact div_nonneg (pow_nonneg hlogx 6) hxan
  refine mul_nonneg hcoef_nonneg ?_
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  have h2 : 2 ≤ t := ht.1
  have ha : 0 ≤ a t := a_nonneg h2
  have hlog : 0 ≤ log t := log_nonneg (by linarith)
  exact div_nonneg (by linarith) (pow_nonneg hlog 7)

private theorem C₂_abs_le_C₁ : |C₂| ≤ C₁ := by
  unfold C₁ C₂
  have h2xa : 2 ≤ xₐ := by
    unfold xₐ
    have h2e : (2 : ℝ) < exp 1 := by
      nlinarith [exp_one_gt_d9]
    have h1 : exp 1 ≤ exp 3914 :=
      exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 3914)
    grind
  have hcoef_nonneg : 0 ≤ log xₐ ^ 6 / xₐ := by
    have hlogx : 0 ≤ log xₐ := by
      rw [log_xₐ_val]
      norm_num
    exact div_nonneg (pow_nonneg hlogx 6) (by positivity)
  have ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    integrable_a_over_log7_piecewise xₐ h2xa
  have hconst_int : IntegrableOn (fun t ↦ (720 : ℝ) / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    refine ContinuousOn.integrableOn_Icc (continuousOn_const.div ?_ ?_)
    · exact (continuousOn_log.mono (by
        intro t ht
        exact ne_of_gt (by linarith [ht.1]))).pow 7
    · intro t ht
      exact pow_ne_zero _ (ne_of_gt (log_pos (by linarith [ht.1])))
  have hminus_int : IntegrableOn (fun t ↦ (720 - a t) / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have hEq :
        (fun t ↦ (720 - a t) / log t ^ 7)
          = (fun t ↦ 720 / log t ^ 7 - a t / log t ^ 7) := by
      funext; ring
    rw [hEq]
    exact hconst_int.sub ha_int
  have hplus_int : IntegrableOn (fun t ↦ (720 + a t) / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have hEq :
        (fun t ↦ (720 + a t) / log t ^ 7)
          = (fun t ↦ 720 / log t ^ 7 + a t / log t ^ 7) := by
      funext; ring
    rw [hEq]
    exact hconst_int.add ha_int
  rw [abs_mul]
  have habs_int :
      |∫ t in Set.Icc 2 xₐ, (720 - a t) / log t ^ 7|
        ≤ ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 := by
    have h0 :
        |∫ t in Set.Icc 2 xₐ, (720 - a t) / log t ^ 7|
          ≤ ∫ t in Set.Icc 2 xₐ, |(720 - a t) / log t ^ 7| := by
      simpa using
        (MeasureTheory.abs_integral_le_integral_abs
          (f := fun t ↦ (720 - a t) / log t ^ 7)
          (μ := volume.restrict (Set.Icc 2 xₐ)))
    refine le_trans h0 ?_
    · refine MeasureTheory.setIntegral_mono_on hminus_int.norm hplus_int measurableSet_Icc ?_
      intro t ht
      have := ht.1
      have ha : 0 ≤ a t := a_nonneg ht.1
      have hlog : 0 < log t := log_pos (by linarith)
      rw [abs_div, abs_of_pos (pow_pos hlog 7)]
      exact div_le_div_of_nonneg_right (by grind) (pow_nonneg hlog.le 7)
  have hmul :
      |log xₐ ^ 6 / xₐ| * |∫ t in Set.Icc 2 xₐ, (720 - a t) / log t ^ 7|
        ≤ (log xₐ ^ 6 / xₐ) * (∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7) := by
    have hleftabs : |log xₐ ^ 6 / xₐ| = log xₐ ^ 6 / xₐ := abs_of_nonneg hcoef_nonneg
    rw [hleftabs]
    exact mul_le_mul_of_nonneg_left habs_int hcoef_nonneg
  simpa using hmul

private theorem C₃_nonneg : 0 ≤ C₃ := by
  unfold C₃
  rw [log_xₐ_val]
  unfold xₐ
  positivity

private theorem C₃_le_one : C₃ ≤ (1 : ℝ) := by
  simpa [C₃] using
    (Calculations.C3_le_one_of (xₐ := xₐ) rfl log_xₐ_val)

private theorem a_le_low_huge {t : ℝ} (ht : t ∈ Set.Icc 2 (exp 3870)) :
    a t ≤ (100000000000000000000 : ℝ) := by
  have hte : t ≤ exp 3870 := ht.2
  have h2 : 2 ≤ t := ht.1
  unfold a
  have hlog_nonneg : 0 ≤ log t := log_nonneg (by linarith)
  by_cases h1 : t ∈ Set.Ico 2 599
  · simp only [h1, ↓reduceIte, ge_iff_le]
    have hlog_le : log t ≤ (599 : ℝ) := by
      have hlog_le_t : log t ≤ t := by
        have htpos : 0 < t := by linarith
        nlinarith [log_le_sub_one_of_pos htpos]
      linarith [hlog_le_t, le_of_lt h1.2]
    have hconst_nonneg : 0 ≤ (1 - log 2 / 3 : ℝ) := by
      linarith [log_two_lt_d9]
    have hconst_le : (1 - log 2 / 3 : ℝ) ≤ 1 := by
      linarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have : (log t) ^ 5 ≤ (599 : ℝ) ^ 5 :=
      pow_le_pow_left₀ hlog_nonneg hlog_le 5
    have :
        (log t) ^ 5 * (1 - log 2 / 3) ≤ (599 : ℝ) ^ 5 * 1 := by
      gcongr
    grind
  · by_cases h2b : t ∈ Set.Ico 599 (exp 58)
    · simp only [h1, ↓reduceIte, h2b, ge_iff_le]
      have hlog_le : log t ≤ (58 : ℝ) :=
        (log_le_iff_le_exp (by linarith)).2 (le_of_lt h2b.2)
      have : 0 < sqrt t := sqrt_pos.mpr (by linarith [h2b.1])
      have : (1 : ℝ) ≤ sqrt t := one_le_sqrt.2 (by linarith [h2])
      have hdiv_le : (log t) ^ 2 / (8 * Real.pi * sqrt t) ≤ (log t) ^ 2 / 1 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith [pi_gt_three])
      calc
        (log t) ^ 5 * ((log t) ^ 2 / (8 * Real.pi * sqrt t))
            ≤ (log t) ^ 5 * (log t) ^ 2 := by
            simpa using mul_le_mul_of_nonneg_left hdiv_le (pow_nonneg hlog_nonneg 5)
        _ = (log t) ^ 7 := by ring
        _ ≤ (58 : ℝ) ^ 7 := pow_le_pow_left₀ hlog_nonneg hlog_le 7
        _ ≤ (100000000000000000000 : ℝ) := by norm_num
    · by_cases h3 : t ∈ Set.Ico (exp 58) (exp 1169)
      · simpa [h1, h2b, h3] using branch3_aux (t := t) h3
      · by_cases h4 : t ∈ Set.Ico (exp 1169) (exp 2000)
        · have ht4 : t ∈ Set.Icc (exp 1169) (exp 3870) := ⟨h4.1, hte⟩
          simpa [h1, h2b, h3, h4] using
            (high_branch_aux (t := t) (c := (462.0 : ℝ)) ht4 (by norm_num))
        · by_cases h5 : t ∈ Set.Ico (exp 2000) (exp 3000)
          · have ht5 : t ∈ Set.Icc (exp 1169) (exp 3870) :=
              ⟨le_trans (exp_le_exp.mpr (by norm_num : (1169 : ℝ) ≤ 2000)) h5.1, hte⟩
            simpa [h1, h2b, h3, h4, h5] using
              (high_branch_aux (t := t) (c := (411.5 : ℝ)) ht5 (by norm_num))
          · simpa [h1, h2b, h3, h4, h5] using
              (high_branch_aux (t := t) (c := (379.7 : ℝ)) (by grind) (by norm_num))

private theorem C₁_le_one : C₁ ≤ (1 : ℝ) := by
  have h2xa : 2 ≤ xₐ := by
    unfold xₐ
    linarith [add_one_le_exp (3914 : ℝ)]
  have h3870le : exp 3870 ≤ xₐ := by
    unfold xₐ
    exact exp_le_exp.mpr (by norm_num)
  have ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    integrable_a_over_log7_piecewise xₐ h2xa
  have hJ3870 :
      ∫ t in Set.Icc 2 (exp 3870), 1 / log t ^ 7
        ≤ exp 3870 / log (exp 3870) ^ 7
          + 7 * (sqrt (exp 3870) / log 2 ^ 8 + 2 ^ 8 * exp 3870 / log (exp 3870) ^ 8) :=
    le_of_lt (log_7_int_bound (exp 3870) (by linarith [add_one_le_exp (3870 : ℝ)]))
  simpa [C₁] using
    (Calculations.C1_le_one_of (a := a) (xₐ := xₐ) rfl h2xa h3870le ha_int
      (fun _ ↦ a_le_low_huge)
      a_mono_3000 a_3870_upper hJ3870)

private theorem a_exa_upper_tight : a exₐ ≤ (13042 / 10 : ℝ) := by
  rw [exₐ_eq]
  exact
    a_exp_upper (L := (3915 : ℝ)) (C := (13042 / 10 : ℝ)) (by norm_num) (by norm_num)
      styleVal_bound_3915_13042_div_10

private theorem mₐ_xₐ_le_121 : mₐ xₐ ≤ (121 : ℝ) := by
  have : 0 ≤ a xₐ := a_nonneg two_le_xₐ
  grind [Calculations.m_upper_from_bounds, mₐ, C₃_nonneg, B_nonneg, C₂_abs_le_C₁, C₁_le_one]

private theorem Mₐ_exₐ_nonneg : 0 ≤ Mₐ exₐ := by
  have : 0 ≤ a xₐ := a_nonneg two_le_xₐ
  have : 0 ≤ a exₐ := a_nonneg two_le_exₐ
  grind [Calculations.M_nonneg_from_bounds, Mₐ, C₁_nonneg, B_nonneg]

private theorem Mₐ_exₐ_le_1426 : Mₐ exₐ ≤ (1426 : ℝ) := by
  have : 0 ≤ a xₐ := a_nonneg two_le_xₐ
  grind [Calculations.M_upper_from_bounds, Mₐ, C₁_le_one, a_xa_upper, a_exa_upper_tight, B_le_small]

private theorem mₐ_xₐ_ge_neg1194 : (-1194 : ℝ) ≤ mₐ xₐ := by
  have : 0 ≤ a xₐ := a_nonneg two_le_xₐ
  grind [Calculations.m_lower_from_bounds, mₐ, a_xa_upper, C₁_le_one, C₂_abs_le_C₁, C₃_le_one, B_le_small]


@[blueprint
  "pi-lower-specific"
  (title := "Specific lower bound on pi")
  (statement := /-- For $x > x_a$, $$ \pi(x) > x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{m_a x}{\log^6 x}.$$. -/)
  (proof := /-- This follows from the previous lemmas and calculations, including Lemma \ref{log-7-int-bound}. -/)
  (latexEnv := "lemma")
  (discussion := 997)]
theorem pi_lower_specific : ∀ x > xₐ, pi x > x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + ((mₐ xₐ) * x / log x ^ 6) := by
  intro x hx
  have hlogx_gt : (3914 : ℝ) < log x := by
    have hlog := log_lt_log xₐ_pos hx
    simpa [xₐ, log_exp] using hlog
  have hlogx_pos : 0 < log x := by linarith
  have h4e9_le_xa : (4000000000 : ℝ) ≤ xₐ := by
    unfold xₐ
    have hexp23 : exp (23 : ℝ) < exp (3914 : ℝ) :=
      exp_lt_exp.mpr (by norm_num)
    grind [exp_23_gt_4e9]
  have hx_ge_4e9 : x ≥ 4e9 := by grind
  rcases Dusart.theorem_5_1 hx_ge_4e9 with ⟨E, hEeq, hEabs⟩

  have hsumx :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        = x / log x + x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring

  have hmul : (mₐ xₐ) * x ≤ (121 : ℝ) * x := mul_le_mul_of_nonneg_right mₐ_xₐ_le_121 (by grind)
  have hmterm :
      (mₐ xₐ) * x / log x ^ 6 ≤ (121 : ℝ) * x / log x ^ 6 :=
    div_le_div_of_nonneg_right hmul (pow_nonneg hlogx_pos.le 6)

  have htarget_le_121 :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + ((mₐ xₐ) * x / log x ^ 6)
        ≤ x / log x * (1 + 1 / log x + 2 / log x ^ 2 + 6 / log x ^ 3 + 24 / log x ^ 4 + 121 / log x ^ 5) := by
    rw [hsumx]
    have halg :
        x / log x + x / log x ^ 2 + 2 * x / log x ^ 3 + 6 * x / log x ^ 4 + 24 * x / log x ^ 5 +
            (121 : ℝ) * x / log x ^ 6
          = x / log x * (1 + 1 / log x + 2 / log x ^ 2 + 6 / log x ^ 3 + 24 / log x ^ 4 + 121 / log x ^ 5) := by
      field_simp [hlogx_pos.ne']
    linarith

  have hloglog_gt8 : (8 : ℝ) < log (log x) :=
    (Real.lt_log_iff_exp_lt hlogx_pos).2 (lt_trans exp_8_lt_3914 hlogx_gt)

  have hpoly_pos :
      0 < 2 * (log (log x) - 1) * log x ^ 3 - 13.32 * log x ^ 2 - 24 * log x - 121 := by
    have hcoef : (14 : ℝ) ≤ 2 * (log (log x) - 1) := by nlinarith
    have hmain_lb : (14 : ℝ) * log x ^ 3 ≤ 2 * (log (log x) - 1) * log x ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg hlogx_pos.le 3)
    nlinarith

  have hinside121 :
      1 + 1 / log x + 2 / log x ^ 2 + 6 / log x ^ 3 + 24 / log x ^ 4 + 121 / log x ^ 5
        < 1 + 1 / log x + 2 * log (log x) / log x ^ 2 - 7.32 / log x ^ 3 := by
    have hdiff :
        (1 + 1 / log x + 2 * log (log x) / log x ^ 2 - 7.32 / log x ^ 3)
            - (1 + 1 / log x + 2 / log x ^ 2 + 6 / log x ^ 3 + 24 / log x ^ 4 + 121 / log x ^ 5)
          = (2 * (log (log x) - 1) * log x ^ 3 - 13.32 * log x ^ 2 - 24 * log x - 121) / log x ^ 5 := by
      field_simp [hlogx_pos.ne']
      ring
    have hdiff_pos :
        0 <
          (1 + 1 / log x + 2 * log (log x) / log x ^ 2 - 7.32 / log x ^ 3)
            - (1 + 1 / log x + 2 / log x ^ 2 + 6 / log x ^ 3 + 24 / log x ^ 4 + 121 / log x ^ 5) := by
      convert div_pos hpoly_pos (pow_pos hlogx_pos 5)
    nlinarith

  have htarget_lt_dusart :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + ((mₐ xₐ) * x / log x ^ 6)
        < x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ 2 - 7.32 / log x ^ 3) := by
    have :
        x / log x * (1 + 1 / log x + 2 / log x ^ 2 + 6 / log x ^ 3 + 24 / log x ^ 4 + 121 / log x ^ 5)
          < x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ 2 - 7.32 / log x ^ 3) :=
      mul_lt_mul_of_pos_left hinside121 (by positivity)
    grind

  have hEge : -(7.32 / log x ^ 3) ≤ E := (abs_le.mp hEabs).1
  have hdusart_lower :
      x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ 2 - 7.32 / log x ^ 3)
        ≤ pi x := by
    have :
        x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ 2 - 7.32 / log x ^ 3)
          ≤ x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ 2 + E) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have : x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ 2 + E) = pi x := by
      simpa using hEeq.symm
    grind

  have htarget_lt_pi :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + ((mₐ xₐ) * x / log x ^ 6) < pi x :=
    lt_of_lt_of_le htarget_lt_dusart hdusart_lower
  simpa [gt_iff_lt] using htarget_lt_pi


@[blueprint
  "epsilon-bound"
  (title := "Bound for εMₐ - εmₐ")
  (statement := /-- We have $\epsilon_{M_a} - \epsilon'_{m_a} < \log (e x_a )$. -/)
  (proof := /-- This is a direct calculation. An AI verification can be found at https://chatgpt.com/share/69a64f96-b1cc-800e-8f85-850168d23094
  -/)
  (latexEnv := "lemma")
  (discussion := 998)]
theorem epsilon_bound :
  ∀ x > exₐ, ε (Mₐ exₐ) x - εlower (mₐ xₐ) xₐ x < log x := by
  intro x hx
  have log_gt_3915 : (3915 : ℝ) < log x := by
    have hlog : log exₐ < log x := log_lt_log exₐ_pos hx
    have hexa_eq : exₐ = exp (3915 : ℝ) := exₐ_eq
    simpa [hexa_eq, log_exp] using hlog
  have := Mₐ_exₐ_nonneg
  have := Mₐ_exₐ_le_1426
  have : (2 * Mₐ exₐ + 132) / log x ≤ (2 * (1426 : ℝ) + 132) / (3915 : ℝ) := by
    have : (2 * Mₐ exₐ + 132) / log x ≤ (2 * Mₐ exₐ + 132) / (3915 : ℝ) :=
      div_le_div_of_nonneg_left (by nlinarith) (by positivity) (le_of_lt log_gt_3915)
    have : (2 * Mₐ exₐ + 132) / (3915 : ℝ) ≤ (2 * (1426 : ℝ) + 132) / (3915 : ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    grind
  have : (4 * Mₐ exₐ + 288) / (log x) ^ 2 ≤ (4 * (1426 : ℝ) + 288) / (3915 : ℝ) ^ 2 := by
    have : (4 * Mₐ exₐ + 288) / (log x) ^ 2 ≤ (4 * Mₐ exₐ + 288) / (3915 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by grind [pow_le_pow_left₀])
    have : (4 * Mₐ exₐ + 288) / (3915 : ℝ) ^ 2 ≤ (4 * (1426 : ℝ) + 288) / (3915 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    grind
  have : (12 * Mₐ exₐ + 576) / (log x) ^ 3 ≤ (12 * (1426 : ℝ) + 576) / (3915 : ℝ) ^ 3 := by
    have : (12 * Mₐ exₐ + 576) / (log x) ^ 3 ≤ (12 * Mₐ exₐ + 576) / (3915 : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by grind [pow_le_pow_left₀])
    have : (12 * Mₐ exₐ + 576) / (3915 : ℝ) ^ 3 ≤ (12 * (1426 : ℝ) + 576) / (3915 : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    grind
  have : (48 * Mₐ exₐ) / (log x) ^ 4 ≤ (48 * (1426 : ℝ)) / (3915 : ℝ) ^ 4 := by
    have : (48 * Mₐ exₐ) / (log x) ^ 4 ≤ (48 * Mₐ exₐ) / (3915 : ℝ) ^ 4 :=
      div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by grind [pow_le_pow_left₀])
    have : (48 * Mₐ exₐ) / (3915 : ℝ) ^ 4 ≤ (48 * (1426 : ℝ)) / (3915 : ℝ) ^ 4 :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    grind
  have : (Mₐ exₐ ^ 2) / (log x) ^ 5 ≤ ((1426 : ℝ) ^ 2) / (3915 : ℝ) ^ 5 := by
    have hcoef_nonneg : 0 ≤ Mₐ exₐ ^ 2 := sq_nonneg (Mₐ exₐ)
    have : (Mₐ exₐ ^ 2) / (log x) ^ 5 ≤ (Mₐ exₐ ^ 2) / (3915 : ℝ) ^ 5 :=
      div_le_div_of_nonneg_left hcoef_nonneg (by positivity) (by grind [pow_le_pow_left₀])
    have : (Mₐ exₐ ^ 2) / (3915 : ℝ) ^ 5 ≤ ((1426 : ℝ) ^ 2) / (3915 : ℝ) ^ 5 :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    grind
  have : 0 ≤ 364 / log x := by positivity
  have : 0 ≤ 381 / (log x) ^ 2 := by positivity
  have : 0 ≤ 238 / (log x) ^ 3 := by positivity
  have : 0 ≤ 97 / (log x) ^ 4 := by positivity
  have : 0 ≤ 30 / (log x) ^ 5 := by positivity
  have : 0 ≤ 8 / (log x) ^ 6 := by positivity
  by_cases hm : 0 ≤ mₐ xₐ
  · rw [εlower, if_pos hm]
    unfold ε ε'
    linarith
  · rw [εlower, if_neg hm]
    have := mₐ_xₐ_ge_neg1194
    have halpha_tight :
        (1 + 1 / log xₐ) ^ 6 ≤ (10016 : ℝ) / 10000 := by
      rw [log_xₐ_val]
      norm_num
    have :
        ((10016 : ℝ) / 10000) * (mₐ xₐ)
          ≤ (1 + 1 / log xₐ) ^ 6 * (mₐ xₐ) :=
      mul_le_mul_of_nonpos_right halpha_tight (by linarith)
    unfold ε εneg
    nlinarith

@[blueprint
  "ramanujan-final"
  (title := "Ramanujan's inequality")
  (statement := /-- For $x \geq e x_a$ we have $\pi(x)^2 < \frac{e x}{\log x} \pi\Big(\frac{x}{e}\Big)$. -/)
  (proof := /-- \cite[Theorem 2]{PT2021} This follows from the previous lemmas and calculations, including the criterion for Ramanujan's inequality. -/)
  (latexEnv := "theorem")
  (discussion := 999)]
theorem ramanujan_final : ∀ x > exₐ, pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1) :=
  criterion (mₐ xₐ) (Mₐ exₐ) xₐ exₐ
    one_lt_xₐ
    pi_lower_specific
    pi_upper_specific
    (le_refl _)
    epsilon_bound


end Ramanujan
