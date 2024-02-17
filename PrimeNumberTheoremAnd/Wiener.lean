import EulerProducts.PNT
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.Support
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.FunProp.Measurable

open Nat Real BigOperators ArithmeticFunction MeasureTheory
open Complex hiding log
-- note: the opening of ArithmeticFunction introduces a notation σ that seems impossible to hide, and hence parameters that are traditionally called σ will have to be called σ' instead in this file.

set_option autoImplicit false

-- This version makes the support of Ψ explicit, and this is easier for some later proofs
lemma smooth_urysohn_support_Ioo {a b c d:ℝ} (h1: a < b) (h2: b<c) (h3: c < d) : ∃ Ψ:ℝ → ℝ, (∀ n, ContDiff ℝ n Ψ) ∧ (HasCompactSupport Ψ) ∧ Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧ (Function.support Ψ = Set.Ioo a d) := by

  have := exists_msmooth_zero_iff_one_iff_of_isClosed
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici)
    (isClosed_Icc)
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc,
        Set.mem_empty_iff_false, and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)

  rcases this with ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩

  simp only [Set.EqOn, Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici,
    ContMDiffMap.coeFn_mk, Pi.zero_apply, Set.mem_Icc, Pi.one_apply, and_imp] at *
  use Ψ
  constructor
  · rw [contDiff_all_iff_nat, ←contDiff_top]
    exact ContMDiff.contDiff hΨSmooth
  · constructor
    · rw [hasCompactSupport_def]
      apply IsCompact.closure_of_subset (K := Set.Icc a d) isCompact_Icc
      simp_rw [Function.support_subset_iff, ne_eq, <-hΨ0]
      intro x hx
      contrapose! hx
      simp only [Set.mem_Icc, not_and_or] at hx
      by_contra! h'
      cases' hx <;> linarith
    · constructor
      · intro x
        rw [Set.indicator_apply]
        split_ifs with h
        · simp only [Set.mem_Icc, Pi.one_apply] at *
          simp_rw [hΨ1 x] at h
          exact Eq.le (_root_.id h.symm)
        · have : Ψ x ∈ Set.range Ψ := by simp only [Set.mem_range, exists_apply_eq_apply]
          have : Ψ x ∈ Set.Icc 0 1 := by exact hΨrange this
          simp at this
          exact this.left
      · constructor
        ·
          intro x
          rw [Set.indicator_apply]
          split_ifs with h
          · have : Ψ x ∈ Set.range Ψ := by simp only [Set.mem_range, exists_apply_eq_apply]
            have : Ψ x ∈ Set.Icc 0 1 := by exact hΨrange this
            simp at this
            simp
            exact this.right
          · simp only [Set.mem_Ioo, Pi.one_apply] at *
            simp only [not_and_or, not_lt] at h
            simp_rw [hΨ0 x] at h
            exact Eq.le h
        · simp_rw [Function.support, ne_eq, ←hΨ0]
          simp [Set.ext_iff]
          intro x
          push_neg
          tauto
  done


/-%%
The Fourier transform of an absolutely integrable function $\psi: \R \to \C$ is defined by the formula
$$ \hat \psi(u) := \int_\R e(-tu) \psi(t)\ dt$$
where $e(\theta) := e^{2\pi i \theta}$.

Let $f: \N \to \C$ be an arithmetic function such that $\sum_{n=1}^\infty \frac{|f(n)|}{n^\sigma} < \infty$ for all $\sigma>1$.  Then the Dirichlet series
$$ F(s) := \sum_{n=1}^\infty \frac{f(n)}{n^s}$$
is absolutely convergent for $\sigma>1$.
%%-/

variable {f: ArithmeticFunction ℝ} (hf: ∀ (σ':ℝ), 1 < σ' → Summable (fun n ↦ |f n| / n^σ'))

/-%%
\begin{lemma}[First Fourier identity]\label{first-fourier}\lean{first_fourier}\leanok  If $\psi: \R \to \C$ is continuous and compactly supported and $x > 0$, then for any $\sigma>1$
  $$ \sum_{n=1}^\infty \frac{f(n)}{n^\sigma} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) = \int_\R F(\sigma + it) \psi(t) x^{it}\ dt.$$
\end{lemma}
%%-/

-- set_option trace.Meta.Tactic.fun_prop true
lemma first_fourier {ψ:ℝ → ℂ} (hcont: Continuous ψ) (hsupp: HasCompactSupport ψ)
    {x σ':ℝ} (hx: 0 < x) (hσ: 1 < σ') :
    ∑' n : ℕ, f n / (n^σ':ℝ) * (fourierIntegral ψ (1 / (2 * π) * log (n / x))) =
    ∫ t:ℝ, ArithmeticFunction.LSeries f (σ' + t * I) * ψ t * x^(t * I) ∂ volume := by
/-%%
\begin{proof}  By the definition of the Fourier transform, the left-hand side expands as
$$ \sum_{n=1}^\infty \int_\R \frac{f(n)}{n^\sigma} \psi(t) e( - \frac{1}{2\pi} t \log \frac{n}{x})\ dt$$
while the right-hand side expands as
$$ \int_\R \sum_{n=1}^\infty \frac{f(n)}{n^{\sigma+it}} \psi(t) x^{it}\ dt.$$
Since
$$\frac{f(n)}{n^\sigma} \psi(t) e( - \frac{1}{2\pi} t \log \frac{n}{x}) = \frac{f(n)}{n^{\sigma+it}} \psi(t) x^{it}$$
the claim then follows from Fubini's theorem.
\end{proof}
%%-/
  calc
    _ = ∑' (n : ℕ), (f n : ℂ) / ↑((n : ℝ) ^ σ') *
        ∫ (v : ℝ), fourierChar (-(v * ((1 : ℝ) / ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      rfl
    _ = ∑' (n : ℕ), ∫ (v : ℝ), (f n : ℂ) / ↑((n : ℝ) ^ σ') *
        fourierChar (-(v * ((1 : ℝ) / ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      congr 1; ext : 1; exact (integral_mul_left _ _).symm
    _ = ∫ (v : ℝ), ∑' (n : ℕ), (f n : ℂ) / ↑((n : ℝ) ^ σ') *
        fourierChar (-(v * ((1 : ℝ) / ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ Measurable.aestronglyMeasurable ?_
        refine Measurable.mul (by fun_prop) ((Measurable.comp ?_ (by fun_prop)).smul (by fun_prop))
        exact Continuous.measurable Real.continuous_fourierChar
      · simp_rw [nnnorm_mul]
        push_cast
        have (n : ℕ) : Measurable fun (u : ℝ) =>
            (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖₊ : ENNReal) := by
          refine Measurable.comp ?_ (by fun_prop) |>.smul (by fun_prop)
            |>.nnnorm |>.coe_nnreal_ennreal
          exact Continuous.measurable Real.continuous_fourierChar
        simp_rw [lintegral_const_mul _ (this _), ← lt_top_iff_ne_top]
        calc
          _ ≤ ∑' (i : ℕ), (∑' (j : ℕ), (‖(f j : ℂ) / ↑((j : ℝ) ^ σ')‖₊ : ENNReal)) *
              ∫⁻ (a : ℝ), ‖fourierChar (-(a * ((1 : ℝ) / ((2 : ℝ) * π) * Real.log (i / x)))) • ψ a‖₊
              ∂volume := by
            refine tsum_mono ENNReal.summable ENNReal.summable fun i ↦ ?_
            gcongr
            exact ENNReal.le_tsum i
          _ < ⊤ := by
            rw [ENNReal.tsum_mul_left]
            apply ENNReal.mul_lt_top
            · norm_cast
              sorry -- NNReal.tsum_eq_toNNReal_tsum
            · sorry -- Fourier.norm_fourierIntegral_le_integral_norm
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (L _ _), ← smul_eq_mul (a := (L _ _)), ArithmeticFunction.LSeries]
      rw [← tsum_smul_const]
      · congr 1; ext n
        show _ * ((fourierChar <| Multiplicative.ofAdd (_) : ℂ) • ψ y) = ((f n : ℂ) / _) • _
        rw [fourierChar_apply]
        show _ / _ * cexp (↑(_ * -(y * _)) * I) • ψ y = _
        calc
          _ = ((f n : ℂ) *
              (cexp (↑((2 : ℝ) * π * -(y * ((1 : ℝ) / ((2 : ℝ) * π) * Real.log (n / x)))) * I) /
              ↑((n : ℝ) ^ σ'))) • ψ y := by
            simp_rw [smul_eq_mul]; group
          _ = ((f n : ℂ) * (↑x ^ (↑y * I) / ↑n ^ (↑σ' + ↑y * I))) • ψ y := by
            congr 2
            cases n with
            | zero =>
              have : σ' = 0 → ¬y = 0 := fun _ ↦ False.elim (by linarith)
              simp [Real.zero_rpow (by linarith : σ' ≠ 0),
                Complex.zero_cpow (by simpa [Complex.ext_iff] using this : σ' + ↑y * I ≠ 0)]
            | succ n =>
              rw [Real.rpow_def_of_pos (cast_pos.mpr (Nat.zero_lt_succ n)),
                Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)),
                Complex.cpow_def_of_ne_zero (NeZero.natCast_ne (succ n) ℂ)]
              push_cast
              simp_rw [← Complex.exp_sub]
              congr 1
              have : (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n + 1) / x))) =
                  -(y * Real.log ((n + 1) / x)) := calc
                _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n + 1) / x))) := by ring
                _ = _ := by rw [div_self (by norm_num; exact pi_ne_zero), one_mul]
              rw [this, Real.log_div (cast_add_one_ne_zero n) (ne_of_gt hx)]
              push_cast
              rw [Complex.ofReal_log (by linarith), Complex.ofReal_log hx.le]
              push_cast
              ring
          _ = _ := by simp_rw [smul_eq_mul]; group
      · apply Summable.of_norm
        convert hf σ' hσ with n
        cases n <;> simp [-cast_succ, Complex.abs_cpow_of_ne_zero (NeZero.natCast_ne _ ℂ)]

/-%%
\begin{lemma}[Second Fourier identity]\label{second-fourier}\lean{second_fourier}\leanok If $\psi: \R \to \C$ is continuous and compactly supported and $x > 0$, then for any $\sigma>1$
$$ \int_{-\log x}^\infty e^{-u(\sigma-1)} \hat \psi(\frac{u}{2\pi})\ du = x^{\sigma - 1} \int_\R \frac{1}{\sigma+it-1} \psi(t) x^{it}\ dt.$$
\end{lemma}
%%-/

lemma second_fourier {ψ:ℝ → ℂ} (hcont: Continuous ψ) (hsupp: HasCompactSupport ψ) {x σ':ℝ} (hx: 0 < x) (hσ: 1 < σ') : ∫ u in Set.Ici (-log x), Real.exp (-u * (σ' - 1)) * fourierIntegral ψ (u / (2 * π)) = (x^(σ' - 1):ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume :=
  sorry

/-%%
\begin{proof}
\uses{first-fourier}
  The left-hand side expands as
  $$ \int_{-\log x}^\infty \int_\R e^{-u(\sigma-1)} \psi(t) e(-\frac{tu}{2\pi})\ dt du = x^{\sigma - 1} \int_\R \frac{1}{\sigma+it-1} \psi(t) x^{it}\ dt$$
  so by Fubini's theorem it suffices to verify the identity
$$ \int_{-\log x}^\infty \int_\R e^{-u(\sigma-1)} e(-\frac{tu}{2\pi})\ du = x^{\sigma - 1} \frac{1}{\sigma+it-1} x^{it}$$
which is a routine calculation.
\end{proof}
%%-/

/-%%
Now let $A \in \C$, and suppose that there is a continuous function $G(s)$ defined on $\mathrm{Re} s \geq 1$ such that $G(s) = F(s) - \frac{A}{s-1}$ whenever $\mathrm{Re} s > 1$.  We also make the Chebyshev-type hypothesis
\begin{equation}\label{cheby}
\sum_{n \leq x} |f(n)| \ll x
\end{equation}
for all $x \geq 1$ (this hypothesis is not strictly necessary, but simplifies the arguments and can be obtained fairly easily in applications).
%%-/

variable {A:ℝ} {G:ℂ → ℂ} (hG: ContinuousOn G {s | 1 ≤ s.re}) (hG' : Set.EqOn G (fun s ↦ ArithmeticFunction.LSeries f s - A / (s - 1)) {s | 1 < s.re})

variable (hcheby: ∃ C:ℝ, ∀ x:ℕ, ∑ n in Finset.Iic x, |f n| ≤ C * x)

/-%%
\begin{lemma}[Decay bounds]\label{decay}\lean{decay_bounds}\leanok  If $\psi:\R \to \C$ is $C^2$ and obeys the bounds
  $$ |\psi(t)|, |\psi''(t)| \leq A / (1 + |t|^2)$$
  for all $t \in \R$, then
$$ |\hat \psi(u)| \leq C A / (1+|u|^2)$$
for all $u \in \R$, where $C$ is an absolute constant.
\end{lemma}
%%-/

lemma decay_bounds : ∃ C:ℝ, ∀ (ψ:ℝ → ℂ) (hψ: ContDiff ℝ 2 ψ) (hsupp: HasCompactSupport ψ) (A:ℝ) (hA: ∀ t, ‖ψ t‖ ≤ A / (1 + t^2)) (hA': ∀ t, ‖deriv^[2] ψ t‖  ≤ A / (1 + t^2)) (u:ℝ), ‖fourierIntegral ψ u‖ ≤ C * A / (1 + u^2) := by
  sorry

/-%%
\begin{proof} This follows from a standard integration by parts argument.
\end{proof}
%%-/

/-%%
\begin{lemma}[Limiting Fourier identity]\label{limiting}\lean{limiting_fourier}\leanok  If $\psi: \R \to \C$ is $C^2$ and compactly supported and $x \geq 1$, then
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) - A \int_{-\log x}^\infty \hat \psi(\frac{u}{2\pi})\ du =  \int_\R G(1+it) \psi(t) x^{it}\ dt.$$
\end{lemma}
%%-/


lemma limiting_fourier {ψ:ℝ → ℂ} (hψ: ContDiff ℝ 2 ψ) (hsupp: HasCompactSupport ψ) {x:ℝ} (hx: 1 ≤ x) : ∑' n, f n / n * fourierIntegral ψ (1/(2*π) * log (n/x)) - A * ∫ u in Set.Ici (-log x), fourierIntegral ψ (u / (2*π)) ∂ volume = ∫ (t : ℝ), (G (1 + I*t)) * (ψ t) * x^(I * t) ∂ volume := by
  sorry

/-%%
\begin{proof}
\uses{first-fourier,second-fourier,decay}
 By the preceding two lemmas, we know that for any $\sigma>1$, we have
  $$ \sum_{n=1}^\infty \frac{f(n)}{n^\sigma} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) - A x^{1-\sigma} \int_{-\log x}^\infty e^{-u(\sigma-1)} \hat \psi(\frac{u}{2\pi})\ du =  \int_\R G(\sigma+it) \psi(t) x^{it}\ dt.$$
  Now take limits as $\sigma \to 1$ using dominated convergence together with \eqref{cheby} and Lemma \ref{decay} to obtain the result.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{limiting-cor}\lean{limiting_cor}\leanok  With the hypotheses as above, we have
  $$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) = A \int_{-\infty}^\infty \hat \psi(\frac{u}{2\pi})\ du + o(1)$$
  as $x \to \infty$.
\end{corollary}
%%-/

open Filter

lemma limiting_cor {ψ:ℝ → ℂ} (hψ: ContDiff ℝ 2 ψ) (hsupp: HasCompactSupport ψ) : Tendsto (fun x : ℝ ↦ ∑' n, f n / n * fourierIntegral ψ (1/(2*π) * log (n/x)) - A * ∫ u in Set.Ici (-log x), fourierIntegral ψ (u / (2*π)) ∂ volume) atTop (nhds 0) := by sorry

/-%%
\begin{proof}
\uses{limiting}
 Immediate from the Riemann-Lebesgue lemma, and also noting that $\int_{-\infty}^{-\log x} \hat \psi(\frac{u}{2\pi})\ du = o(1)$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{schwarz-id}\lean{limiting_cor_schwartz}\leanok  The previous corollary also holds for functions $\psi$ that are assumed to be in the Schwartz class, as opposed to being $C^2$ and compactly supported.
\end{lemma}
%%-/

lemma limiting_cor_schwartz {ψ: SchwartzMap ℝ ℂ} : Tendsto (fun x : ℝ ↦ ∑' n, f n / n * fourierIntegral ψ (1/(2*π) * log (n/x)) - A * ∫ u in Set.Ici (-log x), fourierIntegral ψ (u / (2*π)) ∂ volume) atTop (nhds 0) := by sorry

/-%%
\begin{proof}
\uses{limiting-cor}
For any $R>1$, one can use a smooth cutoff function to write $\psi = \psi_{\leq R} + \psi_{>R}$, where $\psi_{\leq R}$ is $C^2$ (in fact smooth) and compactly supported (on $[-R,R]$), and $\psi_{>R}$ obeys bounds of the form
$$ |\psi_{>R}(t)|, |\psi''_{>R}(t)| \ll R^{-1} / (1 + |t|^2) $$
where the implied constants depend on $\psi$.  By Lemma \ref{decay} we then have
$$ \hat \psi_{>R}(u) \ll R^{-1} / (1+|u|^2).$$
Using this and \eqref{cheby} one can show that
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi_{>R}( \frac{1}{2\pi} \log \frac{n}{x} ), A \int_{-\infty}^\infty \hat \psi_{>R} (\frac{u}{2\pi})\ du \ll R^{-1} $$
(with implied constants also depending on $A$), while from Lemma \ref{limiting-cor} one has
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi_{\leq R}( \frac{1}{2\pi} \log \frac{n}{x} ) = A \int_{-\infty}^\infty \hat \psi_{\leq R} (\frac{u}{2\pi})\ du + o(1).$$
Combining the two estimates and letting $R$ be large, we obtain the claim.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{bij}\lean{fourier_surjection_on_schwartz}\leanok  The Fourier transform is a bijection on the Schwartz class.
\end{lemma}
%%-/

-- just the surjectivity is stated here, as this is all that is needed for the current application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : SchwartzMap ℝ ℂ) : ∃ g : SchwartzMap ℝ ℂ, fourierIntegral g = f := by sorry

/-%%
\begin{proof}
\uses{MellinInversion}
 This is a standard result in Fourier analysis.
It can be proved here by appealing to Mellin inversion, Theorem \ref{MellinInversion}.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{WienerIkeharaSmooth}\lean{wiener_ikehara_smooth}\leanok
  If $\Psi: (0,\infty) \to \C$ is smooth and compactly supported away from the origin, then, then
$$ \sum_{n=1}^\infty f(n) \Psi( \frac{n}{x} ) = A x \int_0^\infty \Psi(y)\ dy + o(x)$$
as $u \to \infty$.
\end{corollary}
%%-/

lemma wiener_ikehara_smooth {Ψ: ℝ → ℂ} (hsmooth: ∀ n, ContDiff ℝ n Ψ) (hsupp: HasCompactSupport Ψ) (hplus: closure (Function.support Ψ) ⊆ Set.Ioi (0:ℝ)): Tendsto (fun x : ℝ ↦ (∑' n, f n / n * Ψ (n/x))/x - A * ∫ y in Set.Ioi 0, Ψ y ∂ volume) atTop (nhds 0) := by sorry

/-%%
\begin{proof}
\uses{bij,schwarz-id}
 By Lemma \ref{bij}, we can write
$$ y \Psi(y) = \hat \psi( \frac{1}{2\pi} \log y )$$
for all $y>0$ and some Schwartz function $\psi$.  Making this substitution, the claim is then equivalent after standard manipulations to
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) = A \int_{-\infty}^\infty \hat \psi(\frac{u}{2\pi})\ du + o(1)$$
and the claim follows from Lemma \ref{schwarz-id}.
\end{proof}
%%-/

/-%%
\begin{lemma}[Smooth Urysohn lemma]\label{smooth-ury}\lean{smooth_urysohn}\leanok  If $I$ is a closed interval contained in an open interval $J$, then there exists a smooth function $\Psi: \R \to \R$ with $1_I \leq \Psi \leq 1_J$.
\end{lemma}
%%-/

lemma smooth_urysohn {a b c d:ℝ} (h1: a < b) (h2: b<c) (h3: c < d) : ∃ Ψ:ℝ → ℝ, (∀ n, ContDiff ℝ n Ψ) ∧ (HasCompactSupport Ψ) ∧ Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by
  have := exists_smooth_zero_one_of_isClosed (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici)
    (isClosed_Icc)
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc,
        Set.mem_empty_iff_false, and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  rcases this with ⟨⟨Ψ, hΨcontMDiff⟩, hΨ0, hΨ1, hΨ01⟩
  simp only [Set.EqOn, Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici,
    ContMDiffMap.coeFn_mk, Pi.zero_apply, Set.mem_Icc, Pi.one_apply, and_imp] at *
  use Ψ
  constructor
  · rw [contDiff_all_iff_nat, ←contDiff_top]
    exact ContMDiff.contDiff hΨcontMDiff
  · constructor
    · rw [hasCompactSupport_def]
      apply IsCompact.closure_of_subset (K := Set.Icc a d) isCompact_Icc
      rw [Function.support_subset_iff]
      intro x hx
      contrapose! hx
      simp only [Set.mem_Icc, not_and_or] at hx
      apply hΨ0
      by_contra! h'
      cases' hx <;> linarith
    · constructor
      · intro x
        rw [Set.indicator_apply]
        split_ifs with h
        simp only [Set.mem_Icc, Pi.one_apply] at *
        rw [hΨ1 h.left h.right]
        exact (hΨ01 x).left
      · intro x
        rw [Set.indicator_apply]
        split_ifs with h
        simp at *
        exact (hΨ01 x).right
        rw [hΨ0]
        simp only [Set.mem_Ioo, not_and_or] at h
        by_contra! h'
        cases' h <;> linarith
  done


/-%%
\begin{proof}  \leanok
A standard analysis lemma, which can be proven by convolving $1_K$ with a smooth approximation to the identity for some interval $K$ between $I$ and $J$. Note that we have ``SmoothBumpFunction''s on smooth manifolds in Mathlib, so this shouldn't be too hard...
\end{proof}
%%-/

/-%%
Now we add the hypothesis that $f(n) \geq 0$ for all $n$.

\begin{proposition}
\label{WienerIkeharaInterval}\lean{WienerIkeharaInterval}\leanok
  For any closed interval $I \subset (0,+\infty)$, we have
  $$ \sum_{n=1}^\infty f(n) 1_I( \frac{n}{x} ) = A x |I|  + o(x).$$
\end{proposition}
%%-/

variable (hpos: ∀ n, 0 ≤ f n)

lemma WienerIkeharaInterval (a b:ℝ) (ha: 0 < a) (hb: a < b) : Tendsto (fun x : ℝ ↦ ∑' n, f n / n * (Set.indicator (Set.Icc a b) 1 (n/x))/x - A * (b-a)) atTop (nhds 0) := by
  sorry

/-%%
\begin{proof}
\uses{smooth-ury, WienerIkeharaSmooth}
  Use Lemma \ref{smooth-ury} to bound $1_I$ above and below by smooth compactly supported functions whose integral is close to the measure of $|I|$, and use the non-negativity of $f$.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{WienerIkehara}\lean{WienerIkeharaTheorem'}\leanok
  We have
$$ \sum_{n\leq x} f(n) = A x |I|  + o(x).$$
\end{corollary}
%%-/
open Filter Nat ArithmeticFunction in
/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/
theorem WienerIkeharaTheorem' {f : ArithmeticFunction ℝ} {A : ℝ} {F : ℂ → ℂ} (hf : ∀ n, 0 ≤ f n)
    (hF : Set.EqOn F (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hF' : ContinuousOn F {s | 1 ≤ s.re}) :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum f) / N) atTop (nhds A) := by
  sorry
/-%%
\begin{proof}
\uses{WienerIkeharaInterval}
  Apply the preceding proposition with $I = [\varepsilon,1]$ and then send $\varepsilon$ to zero (using \eqref{cheby} to control the error).
\end{proof}
%%-/

/-%%
\section{Weak PNT}

\begin{theorem}[Weak PNT]\label{WeakPNT}\lean{WeakPNT}\leanok  We have
$$ \sum_{n \leq x} \Lambda(n) = x + o(x).$$
\end{theorem}
%%-/
theorem WeakPNT :
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum Λ) / N) atTop (nhds 1) := by
  sorry
/-%%
\begin{proof}
\uses{WienerIkehara, ChebyshevPsi}
  Already done by Stoll, assuming Wiener-Ikehara.
\end{proof}
%%-/
