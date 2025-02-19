import PrimeNumberTheoremAnd.ZetaBounds
import Mathlib.Algebra.Group.Support

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

local notation (name := mellintransform2) "𝓜" => MellinTransform
open scoped ArithmeticFunction


/-%%
The approach here is completely standard. We follow the use of
$\mathcal{M}(\widetilde{1_{\epsilon}})$ as in Kontorovich 2015.
%%-/

/-%%
It has already been established that zeta doesn't vanish on the 1 line, and has a pole at $s=1$
of order 1.
We also have the following.
\begin{theorem}[LogDerivativeDirichlet]\label{LogDerivativeDirichlet}\lean{LogDerivativeDirichlet}\leanok
We have that, for $\Re(s)>1$,
$$
-\frac{\zeta'(s)}{\zeta(s)} = \sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}.
$$
\end{theorem}
%%-/
theorem LogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = ∑' n, Λ n / (n : ℂ) ^ s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp
  · have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    dsimp [LSeriesSummable] at this
    convert this; rename ℕ => n
    by_cases h : n = 0 <;> simp [LSeries.term, h]
/-%%
\begin{proof}\leanok
Already in Mathlib.
\end{proof}


The main object of study is the following inverse Mellin-type transform, which will turn out to
be a smoothed Chebyshev function.
\begin{definition}[SmoothedChebyshev]\label{SmoothedChebyshev}\lean{SmoothedChebyshev}\leanok
Fix $\epsilon>0$, and a bumpfunction supported in $[1/2,2]$. Then we define the smoothed
Chebyshev function $\psi_{\epsilon}$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ by
$$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(2)}\frac{-\zeta'(s)}{\zeta(s)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds.$$
\end{definition}
%%-/
noncomputable abbrev SmoothedChebyshevIntegrand (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 ((Smooth1 SmoothingF ε) ·) s * (X : ℂ) ^ s

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) 2


open MeasureTheory


/-%%
\begin{lemma}[SmoothedChebyshevDirichlet_aux_integrable]\label{SmoothedChebyshevDirichlet_aux_integrable}\lean{SmoothedChebyshevDirichlet_aux_integrable}\leanok
Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in $[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$, the function
$$
x \mapsto
\int_{(0,\infty)} t^{1+ix} \widetilde{1_{\epsilon}}(t) dt
$$
is integrable on $\mathbb{R}$. ** Conditions are overkill; can remove some assumptions... **
\end{lemma}
%%-/
lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ε : ℝ) (εpos : 0 < ε) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ ∫ (t : ℝ) in Ioi 0, (t : ℂ) ^ (1 + y * I) * (Smooth1 SmoothingF ε t : ℂ)) := by
  sorry
/-%%
\begin{proof}
\uses{MellinOfSmooth1b}
By Lemma \ref{MellinOfSmooth1b} the integrand is $O(1/t^2)$ as $t\rightarrow \infty$ and hence the function is integrable.
\end{proof}
%%-/

/-%%
\begin{lemma}[SmoothedChebyshevDirichlet_aux_contAt]\label{SmoothedChebyshevDirichlet_aux_contAt}\lean{SmoothedChebyshevDirichlet_aux_contAt}\leanok
Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in $[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$, the function
$x \mapsto \int_{(0,\infty)} x^{1+it} \widetilde{1_{\epsilon}}(x) dx$ is continuous at any $y>0$.
** Conditions are overkill; can remove some assumptions... **
\end{lemma}
%%-/
lemma SmoothedChebyshevDirichlet_aux_contAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  apply Continuous.continuousAt
  unfold Smooth1 DeltaSpike MellinConvolution
  simp only [one_div, ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
  sorry
/-%%
\begin{proof}
\uses{Smooth1Properties_above}
The function is a sum of continuous functions, and hence continuous.
\end{proof}
%%-/

/-%%
\begin{lemma}[SmoothedChebyshevDirichlet_aux_tsum_integral]\label{SmoothedChebyshevDirichlet_aux_tsum_integral}\lean{SmoothedChebyshevDirichlet_aux_tsum_integral}\leanok
Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in $[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$, the function
$x \mapsto \sum_{n=1}^\infty \frac{\Lambda(n)}{n^{2+it}} \mathcal{M}(\widetilde{1_{\epsilon}})(2+it) x^{2+it}$ is equal to
$\sum_{n=1}^\infty \int_{(0,\infty)} \frac{\Lambda(n)}{n^{2+it}} \mathcal{M}(\widetilde{1_{\epsilon}})(2+it) x^{2+it}$.
** Conditions are overkill; can remove some assumptions... Is there really no ``tsum_integral_swap''?**
\end{lemma}
%%-/
lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) (X : ℝ)
    (X_pos : 0 < X) (ε : ℝ) (εpos : 0 < ε)
    (ε_lt_one : ε < 1) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (Λ n) / (n : ℂ) ^ (2 + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (2 + t * I) * (X : ℂ) ^ (2 + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (Λ n) / (n : ℂ) ^ (2 + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (2 + ↑t * I) * (X : ℂ) ^ (2 + t * I) := by
  sorry
/-%%
\begin{proof}
\uses{Smooth1Properties_above, SmoothedChebyshevDirichlet_aux_integrable}
Interchange of summation and integration.
\end{proof}
%%-/

/-%%
Inserting the Dirichlet series expansion of the log derivative of zeta, we get the following.
\begin{theorem}[SmoothedChebyshevDirichlet]\label{SmoothedChebyshevDirichlet}
\lean{SmoothedChebyshevDirichlet}\leanok
We have that
$$\psi_{\epsilon}(X) = \sum_{n=1}^\infty \Lambda(n)\widetilde{1_{\epsilon}}(n/X).$$
\end{theorem}
%%-/
theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (mass_one: ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    (X : ℝ) (X_pos : 0 < X) (ε : ℝ) (εpos: 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X = ∑' n, Λ n * Smooth1 SmoothingF ε (n / X) := by
  dsimp [SmoothedChebyshev, SmoothedChebyshevIntegrand, VerticalIntegral', VerticalIntegral]
  rw [MellinTransform_eq]
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, Λ n / (n : ℂ) ^ (2 + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (2 + ↑t * I) * X ^ (2 + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), Λ n / (n : ℂ) ^ (2 + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (2 + ↑t * I) * X ^ (2 + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (2 + ↑t * I) * (X / (n : ℂ)) ^ (2 + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (2 + ↑t * I) * (X / (n : ℂ)) ^ (2 + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (2 + ↑t * I) * (X / (n : ℂ)) ^ (2 + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (2 + ↑t * I) * ((n : ℂ) / X) ^ (-(2 + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LogDerivativeDirichlet (s := 2 + t * I) (by simp)]
    rw [← tsum_mul_right, ← tsum_mul_right]
  · congr
    rw [← MellinTransform_eq]
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one X X_pos ε εpos ε_lt_one
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_mul_left ]; congr; ext t
    by_cases n_ne_zero : n = 0; simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := 2 + t * I) ?_ ?_
    push_cast at this ⊢
    rw [← this, div_mul_cancel₀]
    · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
    · apply div_nonneg X_pos.le; simp
    · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, not_and, not_not]
      intro hn; exfalso; exact n_ne_zero hn
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(2 + t * I) = (-1) * (2 + t * I) := by simp
    have hn (n : ℂ): (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ): (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) X_pos.le]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (2 + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (2 + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; rhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · push_cast
    congr
    ext n
    by_cases n_zero : n = 0; simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    rw [(by rw [div_mul]; simp : 1 / (2 * π) = 1 / (2 * π * I) * I), mul_assoc]
    conv => lhs; rhs; rhs; rhs; intro t; rw [mul_comm]; norm_cast
    have := MellinInversion 2 (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      (by simp [n_pos, X_pos]) ?_ ?_ ?_
    · beta_reduce at this
      dsimp [MellinInverseTransform, VerticalIntegral] at this
      rw [← MellinTransform_eq, this]
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one
      simp
    · dsimp [VerticalIntegrable, mellin]
      ring_nf
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one ε εpos
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact SmoothedChebyshevDirichlet_aux_contAt diffSmoothingF SmoothingFpos suppSmoothingF
        mass_one εpos (by positivity)
/-%%
\begin{proof}\leanok
\uses{SmoothedChebyshev, MellinInversion, LogDerivativeDirichlet, Smooth1LeOne, MellinOfSmooth1b,
SmoothedChebyshevDirichlet_aux_integrable,
SmoothedChebyshevDirichlet_aux_contAt, SmoothedChebyshevDirichlet_aux_tsum_integral}
We have that
$$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(2)}\sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds.$$
We have enough decay (thanks to quadratic decay of $\mathcal{M}(\widetilde{1_{\epsilon}})$) to
justify the interchange of summation and integration. We then get
$$\psi_{\epsilon}(X) =
\sum_{n=1}^\infty \Lambda(n)\frac{1}{2\pi i}\int_{(2)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
(n/X)^{-s}
ds
$$
and apply the Mellin inversion formula (Theorem \ref{MellinInversion}).
\end{proof}
%%-/

/-%%
\begin{definition}\label{ChebyshevPsi}\lean{ChebyshevPsi}\leanok
The Chebyshev Psi function is defined as
$$
\psi(x) := \sum_{n \le x} \Lambda(n),
$$
where $\Lambda(n)$ is the von Mangoldt function.
\end{definition}
%%-/
noncomputable def ChebyshevPsi (x : ℝ) : ℝ := (Finset.range (Nat.floor x)).sum Λ

/-%%
The smoothed Chebyshev function is close to the actual Chebyshev function.
\begin{theorem}[SmoothedChebyshevClose]\label{SmoothedChebyshevClose}\lean{SmoothedChebyshevClose}\leanok
We have that
$$\psi_{\epsilon}(X) = \psi(X) + O(\epsilon X \log X).$$
\end{theorem}
%%-/
lemma SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) (X : ℝ) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : C < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖SmoothedChebyshev SmoothingF ε X - ChebyshevPsi X‖ ≤ C * ε * X * Real.log X := by
  let C : ℝ := sorry
  have Cpos : 0 < C := sorry
  refine ⟨C, Cpos, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩
  unfold ChebyshevPsi
  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF mass_one
    X (by linarith) _ εpos ε_lt_one]




  sorry
-- #exit
-- lemma SmoothedChebyshevClose {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
--     (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
--     (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) (X : ℝ) :
--     (fun X ↦ ‖SmoothedChebyshev SmoothingF ε X - ChebyshevPsi X‖) =O[atTop]
--       (fun X ↦ ε * X * Real.log X) := by
--   sorry
/-%%
\begin{proof}
\uses{SmoothedChebyshevDirichlet, Smooth1Properties_above,
Smooth1Properties_below,
Smooth1Nonneg,
Smooth1LeOne,
ChebyshevPsi}
Take the difference. By Lemma \ref{Smooth1Properties_above} and \ref{Smooth1Properties_below},
the sums agree except when $1-c \epsilon \leq n/X \leq 1+c \epsilon$. This is an interval of
length $\ll \epsilon X$, and the summands are bounded by $\Lambda(n) \ll \log X$.

%[No longer relevant, as we will do better than any power of log savings...: This is not enough,
%as it loses a log! (Which is fine if our target is the strong PNT, with
%exp-root-log savings, but not here with the ``softer'' approach.) So we will need something like
%the Selberg sieve (already in Mathlib? Or close?) to conclude that the number of primes in this
%interval is $\ll \epsilon X / \log X + 1$.
%(The number of prime powers is $\ll X^{1/2}$.)
%And multiplying that by $\Lambda (n) \ll \log X$ gives the desired bound.]
\end{proof}
%%-/

/-%%
Returning to the definition of $\psi_{\epsilon}$, fix a large $T$ to be chosen later, and pull
contours (via rectangles!) to go
from $2$ up to $2+iT$, then over to $1+iT$, and up from there to $1+i\infty$ (and symmetrically
in the lower half plane).  The
rectangles involved are all where the integrand is holomorphic, so there is no change.
\begin{theorem}[SmoothedChebyshevPull1]\label{SmoothedChebyshevPull1}\lean{SmoothedChebyshevPull1}\leanok
We have that
$$\psi_{\epsilon}(X) =
\mathcal{M}(\widetilde{1_{\epsilon}})(1)
X^{1} +
 \frac{1}{2\pi i}\int_{\text{curve}}\frac{-\zeta'(s)}{\zeta(s)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds.$$
\end{theorem}
%%-/
theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε) (X : ℝ) {T : ℝ} (T_pos : 0 < T) {σ₀ : ℝ}
    (σ₀_pos : 0 < σ₀)
    (holoOn : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X) ((Icc σ₀ 2)×ℂ (univ : Set ℝ) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    SmoothedChebyshev SmoothingF ε X =
    𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X +
    (1 / (2 * π * I)) * (∫ t : ℝ in Iic (-T), SmoothedChebyshevIntegrand SmoothingF ε X (2 + t * I)) -
    (1 / (2 * π * I)) * (∫ s : ℝ in Icc σ₀ 2, SmoothedChebyshevIntegrand SmoothingF ε X (s - T * I)) +
    (1 / (2 * π * I)) * (∫ t : ℝ in Icc (-T) T, SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + t * I)) +
    (1 / (2 * π * I)) * (∫ s : ℝ in Icc σ₀ 2, SmoothedChebyshevIntegrand SmoothingF ε X (s + T * I)) +
    (1 / (2 * π * I)) * (∫ t : ℝ in Ici T, SmoothedChebyshevIntegrand SmoothingF ε X (2 + t * I)) := by
    --VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) 2
  sorry
/-%%
\begin{proof}
\uses{SmoothedChebyshev, RectangleIntegral}
Pull rectangle contours and evaluate the pole at $s=1$.
\end{proof}
%%-/

/-%
\begin{theorem}[ZetaNoZerosOn1Line]\label{ZetaNoZerosOn1Line}
The zeta function does not vanish on the 1-line.
\end{theorem}
This fact is already proved in Stoll's work.
%-/

/-%
Then, since $\zeta$ doesn't vanish on the 1-line, there is a $\delta$ (depending on $T$), so that
the box $[1-\delta,1] \times_{ℂ} [-T,T]$ is free of zeros of $\zeta$.
\begin{theorem}\label{ZetaNoZerosInBox}
For any $T>0$, there is a $\delta>0$ so that $[1-\delta,1] \times_{ℂ} [-T,T]$ is free of zeros of
$\zeta$.
\end{theorem}
%-/

/-%
\begin{proof}
\uses{ZetaNoZerosOn1Line}
We have that zeta doesn't vanish on the 1 line and is holomorphic inside the box (except for the
pole at $s=1$). If for a height $T>0$, there was no such $\delta$, then there would be a sequence
of zeros of $\zeta$ approaching the 1 line, and by compactness, we could find a subsequence of
zeros converging to a point on the 1 line. But then $\zeta$ would vanish at that point, a
contradiction. (Worse yet, zeta would then be entirely zero...)
\end{proof}
%-/

/-%
The rectangle with opposite corners $1-\delta - i T$ and $2+iT$ contains a single pole of
$-\zeta'/\zeta$ at $s=1$, and the residue is $1$ (from Theorem \ref{ResidueOfLogDerivative}).
\begin{theorem}\label{ZeroFreeBox}
$-\zeta'/\zeta$ is holomorphic on the box $[1-\delta,2] \times_{ℂ} [-T,T]$, except a simple pole
with residue $1$ at $s$=1.
\end{theorem}
%-/

/-%
\begin{proof}
\uses{ZetaNoZerosInBox, ResidueOfLogDerivative}
The proof is as described.
\end{proof}
%-/

/-%%
We insert this information in $\psi_{\epsilon}$. We add and subtract the integral over the box
$[1-\delta,2] \times_{ℂ} [-T,T]$, which we evaluate as follows
\begin{theorem}[ZetaBoxEval]\label{ZetaBoxEval}
The rectangle integral over $[1-\delta,2] \times_{ℂ} [-T,T]$ of the integrand in
$\psi_{\epsilon}$ is
$$\frac{1}{2\pi i}\int_{\partial([1-\delta,2] \times_{ℂ} [-T,T])}\frac{-\zeta'(s)}{\zeta(s)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds = \frac{X^{1}}{1}\mathcal{M}(\widetilde{1_{\epsilon}})(1)
= X\left(\mathcal{M}(\psi)\left(\epsilon\right)\right)
= X(1+O(\epsilon))
.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{RectangleBorder, RectangleIntegral,
MellinOfSmooth1a, MellinOfSmooth1b, MellinOfSmooth1c, MellinOfDeltaSpikeAt1,
SmoothedChebyshevPull1}
Residue calculus / the argument principle.
\end{proof}
%%-/

/-%%
It remains to estimate the contributions from the integrals over the curve $\gamma = \gamma_1 +
\gamma_2 + \gamma_3 + \gamma_4
+\gamma_5,
$
where:
\begin{itemize}
\item $\gamma_1$ is the vertical segment from $1-i\infty$ to $1-iT$,
\item $\gamma_2$ is the horizontal segment from $1-iT$ to $1-\delta-iT$,
\item $\gamma_3$ is the vertical segment from $1-\delta-iT$ to $1-\delta+iT$,
\item $\gamma_4$ is the horizontal segment from $1-\delta+iT$ to $1+iT$, and
\item $\gamma_5$ is the vertical segment from $1+iT$ to $1+i\infty$.
\end{itemize}

%%-/

/-%%
\section{MediumPNT}

\begin{theorem}[MediumPNT]\label{MediumPNT}  We have
$$ \sum_{n \leq x} \Lambda(n) = x + O(x \exp(-c(\log x)^{1/18})).$$
\end{theorem}
%%-/
/-- *** Prime Number Theorem (Medium Strength) *** The `ChebyshevPsi` function is asymptotic to `x`. -/
theorem MediumPNT : ∃ (c : ℝ) (_ : 0 < c),
    (ChebyshevPsi - id) =O[atTop] (fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
  let c : ℝ := sorry
  have cpos : 0 < c := sorry
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := sorry
  refine ⟨C, ?_⟩
  rw [Filter.eventually_atTop]
  let X₀ : ℝ := sorry
  refine ⟨X₀, ?_⟩
  intro X X_ge_X₀

  sorry
/-%%
\begin{proof}
\uses{ChebyshevPsi, SmoothedChebyshevClose, LogDerivZetaBndAlt, ZetaBoxEval}
  Evaluate the integrals.
\end{proof}
%%-/
