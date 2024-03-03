import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.ZetaFunction
import EulerProducts.PNT

open BigOperators

lemma sum_eq_int_deriv_aux2 {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ}
    (φDiff : ContDiffOn ℝ 1 φ (Set.Icc a b)) :
    ∫ (x : ℝ) in a..b, (k + 1 / 2 - x) * deriv φ x =
      (k + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a + ∫ (x : ℝ) in a..b, φ x := by
  set v' := deriv φ
  set v := φ
  set u := fun (x : ℝ) ↦ (k + 1 / 2 - x : ℂ)
  set u' := fun (x : ℝ) ↦ (-1 : ℂ)
  have hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x := by
    intros x hx
    -- convert HasDerivAt.add (f := fun (x : ℝ) ↦ (k + 1 / 2 : ℂ)) (g := fun (x : ℝ) ↦ (-x : ℂ))
    --   (f' := (0 : ℂ)) (g' := (-1 : ℂ)) ?_ ?_
    sorry
  have hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x := by
    intros x hx
    sorry
  have hu' : IntervalIntegrable u' MeasureTheory.volume a b := sorry
  have hv' : IntervalIntegrable v' MeasureTheory.volume a b := sorry
--  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hu' hv hv'
  sorry

lemma sum_eq_int_deriv_aux_eq {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ}
    (b_eq_kpOne : b = k + 1) (φDiff : ContDiffOn ℝ 1 φ (Set.Icc a b)) :
    ∑ n in Finset.Icc (k + 1) ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  have flb_eq_k : ⌊b⌋ = k + 1 := Int.floor_eq_iff.mpr ⟨by exact_mod_cast b_eq_kpOne.symm.le,
    by rw [b_eq_kpOne]; simp⟩
  simp_rw [flb_eq_k]
  simp only [Finset.Icc_self, Finset.sum_singleton, Int.cast_add, Int.cast_one]
  rw [sum_eq_int_deriv_aux2 φDiff]
  ring_nf
  rw [b_eq_kpOne]
  congr! 1
  ring_nf

lemma sum_eq_int_deriv_aux_lt {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (k_le_a : k ≤ a) (a_lt_b : a < b)
    (b_lt_kpOne : b < k + 1) (φDiff : ContDiffOn ℝ 1 φ (Set.Icc a b)) :
    ∑ n in Finset.Icc (k + 1) ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  have flb_eq_k : ⌊b⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  simp_rw [flb_eq_k]
  simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, Finset.Icc_eq_empty_of_lt,
    Finset.sum_empty]
  rw [sum_eq_int_deriv_aux2 φDiff]
  ring_nf

lemma sum_eq_int_deriv_aux1 {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (k_le_a : k ≤ a) (a_lt_b : a < b)
    (b_le_kpOne : b ≤ k + 1) (φDiff : ContDiffOn ℝ 1 φ (Set.Icc a b)) :
    ∑ n in Finset.Icc (k + 1) ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  by_cases h : b = k + 1
  · exact sum_eq_int_deriv_aux_eq h φDiff
  · have : b < k + 1 := Ne.lt_of_le h b_le_kpOne
    exact sum_eq_int_deriv_aux_lt k_le_a a_lt_b this φDiff

/-%%
\begin{lemma}[sum_eq_int_deriv_aux]\label{sum_eq_int_deriv_aux}\lean{sum_eq_int_deriv_aux}\leanok
  Let $k \le a < b\le k+1$, with $k$ an integer, and let $\phi$ be continuously differentiable on
  $[a, b]$.
  Then
  \[
  \sum_{a < n \le b} \phi(n) = \int_a^b \phi(x) \, dx + \left(\lfloor b \rfloor + \frac{1}{2} - b\right) \phi(b) - \left(\lfloor a \rfloor + \frac{1}{2} - a\right) \phi(a) - \int_a^b \left(\lfloor x \rfloor + \frac{1}{2} - x\right) \phi'(x) \, dx.
  \]
\end{lemma}
%%-/
/-- Note: Need to finish proof of `sum_eq_int_deriv_aux2` -/
lemma sum_eq_int_deriv_aux {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (k_le_a : k ≤ a) (a_lt_b : a < b)
    (b_le_kpOne : b ≤ k + 1) (φDiff : ContDiffOn ℝ 1 φ (Set.Icc a b)) :
    ∑ n in Finset.Icc (⌊a⌋ + 1) ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (⌊a⌋ + 1 / 2 - a) * φ a
      - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  have fl_a_eq_k : ⌊a⌋ = k := Int.floor_eq_iff.mpr ⟨k_le_a, by linarith⟩
  convert sum_eq_int_deriv_aux1 k_le_a a_lt_b b_le_kpOne φDiff using 2
  · congr
  · congr
  apply intervalIntegral.integral_congr_ae
  have :  ∀ᵐ (x : ℝ) ∂MeasureTheory.volume, x ≠ b := by
    convert Set.Countable.ae_not_mem (s := {b}) (by simp) (μ := MeasureTheory.volume) using 1
  filter_upwards [this]
  intro x x_ne_b hx
  congr
  rw [Set.uIoc_of_le a_lt_b.le, Set.mem_Ioc] at hx
  refine Int.floor_eq_iff.mpr ⟨by linarith, ?_⟩
  have : x < b := Ne.lt_of_le x_ne_b hx.2
  linarith
/-%%
\begin{proof}\leanok
Partial integration.
\end{proof}
%%-/

/-%%
\begin{lemma}[sum_eq_int_deriv]\label{sum_eq_int_deriv}\lean{sum_eq_int_deriv}\leanok
  Let $a < b$, and let $\phi$ be continuously differentiable on $[a, b]$.
  Then
  \[
  \sum_{a < n \le b} \phi(n) = \int_a^b \phi(x) \, dx + \left(\lfloor b \rfloor + \frac{1}{2} - b\right) \phi(b) - \left(\lfloor a \rfloor + \frac{1}{2} - a\right) \phi(a) - \int_a^b \left(\lfloor x \rfloor + \frac{1}{2} - x\right) \phi'(x) \, dx.
  \]
\end{lemma}
%%-/
/-- ** Partial summation ** (TODO : Add to Mathlib) -/
theorem sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (a_lt_b : a < b)
    (φDiff : ContDiffOn ℝ 1 φ (Set.Icc a b)) :
    ∑ n in Finset.Icc (⌊a⌋ + 1) ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (⌊a⌋ + 1 / 2 - a) * φ a
      - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  sorry
/-%%
\begin{proof}\uses{sum_eq_int_deriv_aux}
  Apply Lemma \ref{sum_eq_int_deriv_aux} in blocks of length $\le 1$.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaSum_aux1]\label{ZetaSum_aux1}\lean{ZetaSum_aux1}\leanok
  Let $a < b$ be natural numbers and $s\in \C$ with $s \ne 1$.
  Then
  \[
  \sum_{a < n \le b} \frac{1}{n^s} =  \frac{b^{1-s} - a^{1-s}}{1-s} + \frac{b^{-s}-a^{-s}}{2} + s \int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx.
  \]
\end{lemma}
%%-/
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (a_lt_b : a < b) :
    ∑ n in Finset.Icc (a + 1) b, 1 / (n : ℂ)^s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + (b ^ (-s) - a ^ (-s)) / 2
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1) := by
  let φ := fun (x : ℝ) ↦ (x : ℂ) ^ (-s)
  let φ' := fun (x : ℝ) ↦ -s / (x : ℂ)^(s + 1)
  have φDiff : ContDiffOn ℝ 1 φ (Set.Icc a b) := sorry
  convert sum_eq_int_deriv (by exact_mod_cast a_lt_b) φDiff using 1
  · sorry
  sorry
/-%%
\begin{proof}\uses{sum_eq_int_deriv}
  Apply Lemma \ref{sum_eq_int_deriv} to the function $x \mapsto x^{-s}$.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaSum_aux1a]\label{ZetaSum_aux1a}\lean{ZetaSum_aux1a}\leanok
For any $0 < a < b$ and  $s \in \C$ with $\sigma=\Re(s)>0$,
$$
\left|\int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx\right|
\le \frac{a^{-\sigma}-b^{-\sigma}}/{\sigma}.
$$
\end{lemma}
%%-/
lemma ZetaSum_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    Complex.abs (∫ x in a..b, (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1)) ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  sorry
/-%%
\begin{proof}
Apply the triangle inequality
$$
\left|\int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx\right|
\le \int_a^b \frac{1}{x^{\sigma+1}} \, dx,
$$
and evaluate the integral.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaSum_aux2]\label{ZetaSum_aux2}\lean{ZetaSum_aux2}\leanok
  Let $N$ be a natural number and $s\in \C$, $\Re(s)>1$.
  Then
  \[
  \sum_{N < n} \frac{1}{n^s} =  \frac{- N^{1-s}}{1-s} + \frac{-N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx.
  \]
\end{lemma}
%%-/
lemma ZetaSum_aux2 {N : ℕ} {s : ℂ} (s_re_pos : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Set.Ici (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1) := by
  sorry
/-%%
\begin{proof}\uses{ZetaSum_aux1, ZetaSum_aux1a}
  Apply Lemma \ref{ZetaSum_aux1} with $a=N$ and $b\to \infty$.
\end{proof}
%%-/

/-%%
\begin{definition}[RiemannZeta0]\label{RiemannZeta0}\lean{RiemannZeta0}\leanok
\uses{ZetaSum_aux2}
For any natural $N\ge1$, we define
$$
\zeta_0(N,s) :=
\sum_{1\le n < N} \frac1{n^s}
+
\frac{- N^{1-s}}{1-s} + \frac{-N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
$$
\end{definition}
%%-/
noncomputable def RiemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n in Finset.Icc 1 (N - 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Set.Ici (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ)^(s + 1)

/-%%
\begin{lemma}[Zeta0EqZeta]\label{Zeta0EqZeta}\lean{Zeta0EqZeta}\leanok
If $\Re(s)>0$, then for any $N$,
$$
\zeta_0(N,s) = \zeta(s).
$$
[** What about junk values at $s=1$? Maybe add $s\ne1$. **]
\end{lemma}
%%-/
/-- ** Add `s ≠ 1`? -/
lemma Zeta0EqZeta (N : ℕ) (s : ℂ) (reS_pos : 0 < s.re) :
    RiemannZeta0 N s = riemannZeta s := by
  sorry
/-%%
\begin{proof}
\uses{ZetaSum_aux2, RiemannZeta0}
Use Lemma \ref{ZetaSum_aux2} and the Definition \ref{RiemannZeta0}.
\end{proof}
%%-/
