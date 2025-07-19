import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.ZetaConj
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Real.Pi.Bounds

set_option lang.lemmaCmd true
set_option maxHeartbeats 400000

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)

/-%%
The approach here is completely standard. We follow the use of
$\mathcal{M}(\widetilde{1_{\epsilon}})$ as in [Kontorovich 2015].
%%-/

local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

/-%%
\begin{definition}\label{ChebyshevPsi}\lean{ChebyshevPsi}\leanok
The (second) Chebyshev Psi function is defined as
$$
\psi(x) := \sum_{n \le x} \Lambda(n),
$$
where $\Lambda(n)$ is the von Mangoldt function.
\end{definition}
%%-/
noncomputable def ChebyshevPsi (x : ℝ) : ℝ :=
  (Finset.range ⌊x + 1⌋₊).sum Λ

local notation "ψ" => ChebyshevPsi

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
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
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
$$\psi_{\epsilon}(X) = \frac{1}{2\pi i}\int_{(\sigma)}\frac{-\zeta'(s)}{\zeta(s)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds,$$
where we'll take $\sigma = 1 + 1 / \log X$.
\end{definition}
%%-/
noncomputable abbrev SmoothedChebyshevIntegrand (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 ((Smooth1 SmoothingF ε) ·) s * (X : ℂ) ^ s

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate

/-%%
\begin{lemma}[SmoothedChebyshevIntegrand_conj]\label{SmoothedChebyshevIntegrand_conj}\lean{SmoothedChebyshevIntegrand_conj}\leanok
The smoothed Chebyshev integrand satisfies the conjugation symmetry
$$
\psi_{\epsilon}(X)(\overline{s}) = \overline{\psi_{\epsilon}(X)(s)}
$$
for all $s \in \mathbb{C}$, $X > 0$, and $\epsilon > 0$.
\end{lemma}
%%-/
lemma smoothedChebyshevIntegrand_conj {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    SmoothedChebyshevIntegrand SmoothingF ε X (conj s) = conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
  unfold SmoothedChebyshevIntegrand
  simp only [map_mul, map_div₀, map_neg]
  congr
  · exact deriv_riemannZeta_conj s
  · exact riemannZeta_conj s
  · unfold MellinTransform
    rw[← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x xpos
    simp only [map_mul, Complex.conj_ofReal]
    congr
    nth_rw 1 [← map_one conj]
    rw[← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg xpos.le]
    exact Real.pi_ne_zero.symm
  · rw[Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm
/-%%
\begin{proof}\uses{deriv_riemannZeta_conj, riemannZeta_conj}\leanok
We expand the definition of the smoothed Chebyshev integrand and compute, using the corresponding
conjugation symmetries of the Riemann zeta function and its derivative.
\end{proof}
%%-/

open MeasureTheory

/-%%
\begin{lemma}[SmoothedChebyshevDirichlet_aux_integrable]\label{SmoothedChebyshevDirichlet_aux_integrable}\lean{SmoothedChebyshevDirichlet_aux_integrable}\leanok
Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in $[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$, and $\sigma\in (1, 2]$, the function
$$
x \mapsto\mathcal{M}(\widetilde{1_{\epsilon}})(\sigma + ix)
$$
is integrable on $\mathbb{R}$.
\end{lemma}
%%-/
lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
  obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  apply Integrable.mono' (g := (fun t ↦ c / ε * 1 / (1 + t ^ 2)))
  · apply Integrable.const_mul integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
      SmoothingFpos mass_one (s := σ + x * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith) |>.continuousAt
    fun_prop
  · filter_upwards [] with t
    calc
      _≤ c / ε * 1 / (σ^2 + t^2) := by
        convert hc (σ / 2) (by linarith) (σ + t * I) (by simp only [add_re, ofReal_re, mul_re,
          I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, half_le_self_iff]; linarith)
          (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero]; linarith) ε εpos  ε_lt_one using 1
        simp only [mul_one, Complex.sq_norm, normSq_apply, add_re, ofReal_re, mul_re, I_re,
          mul_zero, ofReal_im, I_im, sub_self, add_zero, add_im, mul_im, zero_add, mul_inv_rev]
        ring_nf
      _ ≤ _ := by
        gcongr; nlinarith

/-%%
\begin{proof}\leanok
\uses{MellinOfSmooth1b}
By Lemma \ref{MellinOfSmooth1b} the integrand is $O(1/t^2)$ as $t\rightarrow \infty$ and hence the function is integrable.
\end{proof}
%%-/

/-%%
\begin{lemma}[SmoothedChebyshevDirichlet_aux_tsum_integral]\label{SmoothedChebyshevDirichlet_aux_tsum_integral}
\lean{SmoothedChebyshevDirichlet_aux_tsum_integral}\leanok
Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in
$[1/2,2]$, and total mass one, $\int_{(0,\infty)} F(x)/x dx = 1$. Then for any $\epsilon>0$ and $\sigma\in(1,2]$, the
function
$x \mapsto \sum_{n=1}^\infty \frac{\Lambda(n)}{n^{\sigma+it}}
\mathcal{M}(\widetilde{1_{\epsilon}})(\sigma+it) x^{\sigma+it}$ is equal to
$\sum_{n=1}^\infty \int_{(0,\infty)} \frac{\Lambda(n)}{n^{\sigma+it}}
\mathcal{M}(\widetilde{1_{\epsilon}})(\sigma+it) x^{\sigma+it}$.
\end{lemma}
%%-/

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by

  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑a * I) := by
    rw [continuous_iff_continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    . refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one hz).continuousAt
    . fun_prop
    . simp only [mapsTo_univ_iff, mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith

  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    -- norm_cast
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, rpow_two, Real.toNNReal_of_nonneg <| rpow_nonneg (y:= σ) (x:= i) (by linarith)]
    norm_cast

  rw [MeasureTheory.integral_tsum]
  have x_neq_zero : X ≠ 0 := by linarith
  . intro i
    by_cases i_eq_zero : i = 0
    . simpa [i_eq_zero] using aestronglyMeasurable_const
    . apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  . rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal, Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnnorm_real, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, rpow_two]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp), ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top

    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    . rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
        (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp[h]
    . simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

/-%%
\begin{proof}\leanok
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
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one: ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos: 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
  dsimp [SmoothedChebyshev, SmoothedChebyshevIntegrand, VerticalIntegral', VerticalIntegral]
  rw [MellinTransform_eq]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt (by linarith : 0 < X)]
    linarith [Real.exp_one_lt_d9]
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by
      simp only [inv_pos]
      linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LogDerivativeDirichlet]
    · rw [← tsum_mul_right, ← tsum_mul_right]
    · simp [σ_gt]
  · congr
    rw [← MellinTransform_eq]
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0; simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + t * I) ?_ ?_
    push_cast at this ⊢
    rw [← this, div_mul_cancel₀]
    · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
    · apply div_nonneg (by linarith : 0 ≤ X); simp
    · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, not_and, not_not]
      intro hn; exfalso; exact n_ne_zero hn
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
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
    have := MellinInversion σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [MellinInverseTransform, VerticalIntegral] at this
      rw [← MellinTransform_eq, this]
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩ SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      rw [← MellinTransform_eq]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
        εpos (by positivity)
/-%%
\begin{proof}\leanok
\uses{SmoothedChebyshev, MellinInversion, LogDerivativeDirichlet, Smooth1LeOne, MellinOfSmooth1b,
SmoothedChebyshevDirichlet_aux_integrable,
Smooth1ContinuousAt, SmoothedChebyshevDirichlet_aux_tsum_integral}
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
The smoothed Chebyshev function is close to the actual Chebyshev function.
\begin{theorem}[SmoothedChebyshevClose]\label{SmoothedChebyshevClose}\lean{SmoothedChebyshevClose}\leanok
We have that
$$\psi_{\epsilon}(X) = \psi(X) + O(\epsilon X \log X).$$
\end{theorem}
%%-/

--open scoped ArithmeticFunction in
theorem SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2) (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X) (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) → Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
  ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
        ↑((Finset.range ⌊X + 1⌋₊).sum ⇑ArithmeticFunction.vonMangoldt)‖ ≤
    C * ε * X * Real.log X := by
  norm_cast

  let F := Smooth1 SmoothingF ε

  let n₀ := ⌈X * (1 - c₁ * ε)⌉₊

  have n₀_pos : 0 < n₀ := by
    simp only [Nat.ceil_pos, n₀]
    subst C_eq
    simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos, n₀]
    exact mul_lt_one_of_nonneg_of_lt_one_left c₁_pos.le c₁_lt ε_lt_one.le

  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    apply sub_le_self
    positivity

  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    apply le_of_lt
    exact Nat.ceil_lt_add_one (by bound)

  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))

  have sumΛ : Summable (fun (n : ℕ) ↦ Λ n * F (n / X)) := by
    exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    (hc₂ _ _ (by trivial) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
    (s ∘ Finset.mem_range.2))))))

  have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ Λ (n + n₀) * F ((n + n₀) / X)) := by exact_mod_cast sumΛ.comp_injective fun Q=>by valid

  rw[← Summable.sum_add_tsum_nat_add' (k := n₀) (mod_cast sumΛn₀ n₀)]

  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊

  have n₁_pos : 0 < n₁ := by
      dsimp only [n₁]
      apply Nat.le_floor
      rw[Nat.succ_eq_add_one, zero_add]
      norm_cast
      apply one_le_mul_of_one_le_of_one_le (by linarith)
      apply le_add_of_nonneg_right
      positivity

  have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))

  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)

  have n₁_ge_n₀ : n₀ ≤ n₁ := by
    exact_mod_cast le_implies_le_of_le_of_le n₀_le n₁_ge (by linarith)

  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
    calc
      (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                        exact sub_le_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
       _            = X * ε * (c₂ + c₁) := by ring

  have : (∑' (n : ℕ), Λ (n + n₀ : ) * F ((n + n₀ : ) / X)) =
    (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((n + n₀) / X)) +
    (∑' (n : ℕ), Λ (n + n₁ : ) * F ((n + n₁ : ) / X)) := by
    rw[← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)]
    congr! 5
    · simp only [Nat.cast_add]
    · omega
    · congr! 1
      norm_cast
      omega
    · convert sumΛn₀ ((n₁ - n₀) + n₀) using 4
      · omega
      · congr! 1
        norm_cast
        omega

  rw [this]
  clear this

  have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) := by
    have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) + (∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X)) := by
      let fTemp := fun n ↦ Λ (n + n₁) * F ((↑n + ↑n₁) / X)
      have sum_fTemp : Summable fTemp := by exact sumΛn₀ n₁
      have hTemp (n : ℕ): fTemp n = Λ (n + n₁) * F (↑(n + n₁) / X) := by rw[Nat.cast_add]
      have : ∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X) = ∑' (n : ℕ), fTemp n := by exact Eq.symm (tsum_congr hTemp)
      rw[this]
      have (n : ℕ): fTemp (n + 1) = Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X) := by exact hTemp (n + 1)
      have : ∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X) = ∑' (n : ℕ), fTemp (n + 1) := by exact Eq.symm (tsum_congr this)
      rw[this]
      have : Λ n₁ * F (↑n₁ / X) = fTemp 0 := by
        dsimp only [fTemp]
        rw[← Nat.cast_add, zero_add]
      rw[this]
      exact Summable.tsum_eq_zero_add (sumΛn₀ n₁)
    rw[this]
    apply add_eq_left.mpr
    convert tsum_zero with n
    have : n₁ ≤ n + (n₁) := by exact Nat.le_add_left (n₁) n
    convert mul_zero _
    convert smoothIs0 (n + 1 + n₁) ?_
    rw[← mul_le_mul_right X_pos]
    have : ↑(n + 1 + n₁) / X * X = ↑(n + 1 + n₁) := by field_simp
    rw[this]
    have : (1 + c₂ * ε) * X = 1 + (X * (1 + c₂ * ε) - 1) := by ring
    rw[this, Nat.cast_add, Nat.cast_add]
    exact add_le_add (by bound) n₁_ge

  rw [this]
  clear this

  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one, Nat.cast_add, Nat.cast_one]
    have temp : X ≤ ↑⌈X⌉₊ := by exact Nat.le_ceil X
    have : (⌈X⌉₊ : ℝ) ≤ ↑⌊X⌋₊ + 1 := by exact_mod_cast Nat.ceil_le_floor_add_one X
    exact Preorder.le_trans X (↑⌈X⌉₊) (↑⌊X⌋₊ + 1) temp this
    positivity

  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := by exact Nat.floor_le (by positivity)

  have : ∑ x ∈ Finset.range ⌊X + 1⌋₊, Λ x =
      (∑ x ∈ Finset.range n₀, Λ x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + ↑n₀) := by
    field_simp only [add_comm _ n₀,n₀_le.trans,le_of_lt,n₀.le_floor,Finset.sum_range_add]
    rw [← Finset.sum_range_add, Nat.add_sub_of_le]
    dsimp only [n₀]
    refine Nat.ceil_le.mpr ?_
    exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X X_le_floor_add_one
  rw [this]
  clear this

  have : ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, Λ n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases n_zero : n = 0
    · rw [n_zero]
      simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert mul_one _
      convert smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      have : (n < ⌈X * (1 - c₁ * ε)⌉₊) → (n ≤ ⌊X * (1 - c₁ * ε)⌋₊) := by
        intro n_lt
        by_contra hcontra

        rw[not_le] at hcontra

        have temp1: (⌊X * (1 - c₁ * ε)⌋₊).succ.succ ≤ n.succ := by
          apply Nat.succ_le_succ
          exact Nat.succ_le_of_lt hcontra
        have : n.succ ≤ ⌈X * (1 - c₁ * ε)⌉₊ := by exact Nat.succ_le_of_lt hn
        have temp2: ⌊X * (1 - c₁ * ε)⌋₊ + 2 = (⌊X * (1 - c₁ * ε)⌋₊ + 1) + 1 := by ring
        have : ⌊X * (1 - c₁ * ε)⌋₊ + 2 ≤ ⌈X * (1 - c₁ * ε)⌉₊ := by
          rw[temp2, ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one]
          exact Nat.le_trans temp1 hn
        rw[← and_not_self_iff (⌊X * (1 - c₁ * ε)⌋₊ + 2 ≤ ⌈X * (1 - c₁ * ε)⌉₊), not_le]
        apply And.intro
        exact this
        rw[temp2, ← Nat.succ_eq_add_one, Nat.lt_succ_iff]
        exact Nat.ceil_le_floor_add_one (X * (1 - c₁ * ε))
      exact (Nat.le_floor_iff' n_zero).mp (this hn)

  rw [this, sub_eq_add_neg, add_assoc, add_assoc]
  nth_rewrite 3 [add_comm]
  nth_rewrite 2 [← add_assoc]
  rw [← add_assoc, ← add_assoc, ← sub_eq_add_neg]
  clear this

  have :
    ∑ n ∈ Finset.range n₀, Λ n + (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X)) -
      (∑ x ∈ Finset.range n₀, Λ x + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀))
      =
      (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X)) -
      (∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀)) := by
    ring
  rw [this]
  clear this

  have :
    ‖∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X) - ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀) + Λ n₁ * F (↑n₁ / X)‖
    ≤
    (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
      ‖Λ n₁‖ * ‖F (↑n₁ / X)‖:= by
    apply norm_add_le_of_le
    apply norm_sub_le_of_le
    apply norm_sum_le_of_le
    intro b hb
    exact norm_mul_le_of_le (by rfl) (by rfl)
    apply norm_sum_le_of_le
    intro b hb
    rfl
    exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)

  refine this.trans ?_

  clear this

  have vonBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    intro n hn
    have n_add_n0_le_n1: (n : ℝ) + n₀ ≤ n₁ := by
      apply le_of_lt
      rw[Finset.mem_range] at hn
      rw[← add_lt_add_iff_right (-↑n₀), add_neg_cancel_right, add_comm, ← sub_eq_neg_add]
      exact_mod_cast hn
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
      apply ArithmeticFunction.vonMangoldt_nonneg
    have inter2: Real.log (↑n + ↑n₀) ≤ Real.log (↑n₁) := by exact_mod_cast Real.log_le_log (by positivity) n_add_n0_le_n1
    have inter3: Real.log (↑n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by exact Real.log_le_log (by bound) (by linarith)
    exact le_implies_le_of_le_of_le inter1 inter3 inter2

  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖
    ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by
    have : (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) = (∑ n ∈ Finset.range (n₁ - n₀), Real.log (X * (1 + c₂ * ε))) := by
      rw[← Nat.cast_sub]
      nth_rewrite 1 [← Finset.card_range (n₁ - n₀)]
      rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
      exact Eq.symm (Finset.sum_const (Real.log (X * (1 + c₂ * ε))))
      exact n₁_ge_n₀
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul (vonBnd1 _ hn) _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddAbove
    bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound

  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤ (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by
    have : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) = (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), Real.log (X + 1)) := by
      rw[← Nat.cast_sub]
      nth_rewrite 1 [← Finset.card_range (⌊X + 1⌋₊ - n₀)]
      rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
      exact Eq.symm (Finset.sum_const (Real.log (X + 1)))
      simp only [Nat.ceil_le, n₀, F]
      exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X X_le_floor_add_one
    rw[this]
    apply Finset.sum_le_sum
    intro n hn
    have n_add_n0_le_X_add_one: (n : ℝ) + n₀ ≤ X + 1 := by
      rw[Finset.mem_range] at hn
      rw[← add_le_add_iff_right (-↑n₀), add_assoc, ← sub_eq_add_neg, sub_self, add_zero, ← sub_eq_add_neg]
      have temp: (n : ℝ) < ⌊X + 1⌋₊ - n₀ := by
        rw[← Nat.cast_sub, Nat.cast_lt]
        exact hn
        simp only [Nat.ceil_le, n₀, F]
        exact le_trans n₀_inside_le_X X_le_floor_add_one
      have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
        apply sub_le_sub_right floor_X_add_one_le_self
      exact le_of_lt (lt_of_le_of_lt' this temp)
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
      apply ArithmeticFunction.vonMangoldt_nonneg
    apply le_trans inter1
    exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)

  have largeSumBound := add_le_add bnd1 bnd2

  clear vonBnd1 bnd1 bnd2

  have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
    apply Real.log_le_log (by positivity)
    have const_le_2: 1 + c₂ * ε ≤ 3 := by
      have : (3 : ℝ) = 1 + 2 := by ring
      rw[this]
      apply add_le_add_left
      rw[← mul_one 2]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw[mul_comm]
    exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)

  have inter2 : (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
    apply mul_le_mul n₁_sub_n₀ _ (log_nonneg (by linarith)) (by positivity)
    rw[← Real.log_mul (by positivity) (by positivity)]
    nth_rewrite 3 [mul_comm]
    exact inter1

  have inter3 : (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) ≤ 2 * (X * ε * (c₂ + c₁)) * (Real.log (X)) := by
    nth_rewrite 3 [mul_assoc]
    rw[two_mul, mul_add]
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by linarith)

  have inter4 : (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) ≤ 2 * (X * ε * (c₁ + c₂)) * (Real.log (X)) := by
    nth_rewrite 2 [add_comm]
    exact le_trans inter2 inter3

  clear inter2 inter3

  have inter6 : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
    apply mul_le_mul _ _ (log_nonneg (by linarith)) (by positivity)
    have : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)) := by ring
    rw[this]
    apply sub_le_sub
    have : X + 1 ≤ X * (1 + ε * c₁) := by
      ring_nf
      rw[add_comm, add_le_add_iff_left]
      exact X_bound_1
    exact le_trans floor_X_add_one_le_self this
    nth_rewrite 2 [mul_comm]
    exact n₀_gt
    rw[← Real.log_mul (by positivity) (by norm_num), mul_comm]
    exact Real.log_le_log (by positivity) (by linarith)

  have inter7: 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) ≤ 4 * (X * ε * c₁) * Real.log (X) := by
    have : (4 : ℝ) = 2 + 2 := by ring
    rw[this, mul_add]
    nth_rewrite 5 [mul_assoc]
    rw[add_mul]
    apply add_le_add
    nth_rewrite 1 [mul_assoc]
    rfl
    nth_rewrite 1 [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left <| Real.log_le_log (by positivity) (by linarith)
    positivity

  have inter9: (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) + (↑⌊X + 1⌋₊ - ↑n₀) * Real.log (X + 1) ≤
    2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by
    have : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁) := by ring
    rw[this, add_mul]
    exact add_le_add inter4 <| le_trans inter6 inter7

  have largeSumBound2 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤
    2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by
    exact le_trans largeSumBound inter9

  clear largeSumBound inter4 inter9

  have inter10 : ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    rw[← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul _ _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact le_trans ArithmeticFunction.vonMangoldt_le_log <| Real.log_le_log (mod_cast n₁_pos) n₁_le
    rw[Real.norm_of_nonneg]
    apply smooth1BddAbove _ n₁_pos
    apply smooth1BddBelow _ n₁_pos

  have largeSumBound3 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by exact add_le_add largeSumBound2 (le_trans inter10 inter1)
  clear inter1 inter10 largeSumBound2

  have largeSumBound4 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (2 * Real.log X + Real.log (3)) := by
    nth_rewrite 2 [two_mul, add_assoc]
    rw [← Real.log_mul (by positivity) (by positivity), mul_comm X 3]
    apply le_trans largeSumBound3
    nth_rewrite 2 [mul_add]
    apply add_le_add_left
    nth_rewrite 1 [← one_mul (Real.log (3 * X))]
    apply mul_le_mul_of_nonneg_right _ (log_nonneg (by linarith))
    linarith

  clear largeSumBound3

  have largeSumBoundFinal : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ (6 * (X * ε * (3 * c₁ + c₂))) * Real.log (X) := by
    apply le_trans largeSumBound4
    rw[mul_add]
    have : (6 : ℝ) = 4 + 2 := by ring
    rw[this, add_mul, add_mul]
    apply add_le_add
    ring_nf
    rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by linarith)

  clear largeSumBound4

  rw[C_eq]
  linear_combination largeSumBoundFinal

theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ChebyshevPsi X‖ ≤ C * ε * X * Real.log X := by
  have vonManBnd (n : ℕ) : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log

  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one

  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF

  have c₁_lt : c₁ < 1 := by
    rw[c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)

  have c₂_lt : c₂ < 2 := by
    rw[c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    rfl
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    exact Real.log_nonneg (by norm_num)
    positivity

  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl

  clear_value C

  have Cpos : 0 < C := by
    rw [C_eq]
    positivity

  refine ⟨C, Cpos, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩
  unfold ChebyshevPsi

  have X_gt_zero : (0 : ℝ) < X := by linarith

  have X_ne_zero : X ≠ 0 := by linarith

  have n_on_X_pos {n : ℕ} (npos : 0 < n) :
      0 < n / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity

  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)

  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos

  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : n ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le

  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ n / X) :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le

  have ε_pos: ε > 0 := by linarith
  have X_pos: X > 0 := by linarith
  have X_gt_three : 3 < X := by linarith

  intro X_bound

  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw[c₁_eq, ← div_le_iff₀]
    have : 1 / Real.log 2 < 2 := by
      nth_rewrite 2 [← one_div_one_div 2]
      rw[one_div_lt_one_div]
      exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
      exact Real.log_pos (by norm_num)
      norm_num
    apply le_of_lt
    exact gt_trans X_bound this
    exact Real.log_pos (by norm_num)

  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw[c₂_eq, ← div_le_iff₀]
    have : 1 / (2 * Real.log 2) < 2 := by
      nth_rewrite 3 [← one_div_one_div 2]
      rw[one_div_lt_one_div, ← one_mul (1 / 2)]
      apply mul_lt_mul
      norm_num
      apply le_of_lt
      exact lt_trans (by norm_num) (Real.log_two_gt_d9)
      repeat norm_num
      exact Real.log_pos (by norm_num)
      norm_num
    apply le_of_lt
    exact gt_trans X_bound this
    norm_num
    exact Real.log_pos (by norm_num)

  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF
    mass_one (by linarith) εpos ε_lt_one]

  convert SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε ε_pos ε_lt_one
    X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow smoothIs1 smoothIs0

/-%%
\begin{proof}\leanok
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
Returning to the definition of $\psi_{\epsilon}$, fix a large $T$ to be chosen later, and set
$\sigma_0 = 1 + 1 / log X$,
$\sigma_1 = 1- A/ \log T^9$, and
$\sigma_2<\sigma_1$ a constant.
Pull
contours (via rectangles!) to go
from $\sigma_0-i\infty$ up to $\sigma_0-iT$, then over to $\sigma_1-iT$,
up to $\sigma_1-3i$, over to $\sigma_2-3i$, up to $\sigma_2+3i$, back over to $\sigma_1+3i$, up to $\sigma_1+iT$, over to $\sigma_0+iT$, and finally up to $\sigma_0+i\infty$.

\begin{verbatim}
                    |
                    | I₉
              +-----+
              |  I₈
              |
           I₇ |
              |
              |
  +-----------+
  |       I₆
I₅|
--σ₂----------σ₁--1-σ₀----
  |
  |       I₄
  +-----------+
              |
              |
            I₃|
              |
              |  I₂
              +-----+
                    | I₁
                    |
\end{verbatim}

In the process, we will pick up the residue at $s=1$.
We will do this in several stages. Here the interval integrals are defined as follows:
%%-/

/-%%
\begin{definition}[I₁]\label{I1}\lean{I₁}\leanok
$$
I_1(\nu, \epsilon, X, T) := \frac{1}{2\pi i} \int_{-\infty}^{-T}
\left(
\frac{-\zeta'}\zeta(\sigma_0 + t i)
\right)
 \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
X^{\sigma_0 + t i}
\ i \ dt
$$
\end{definition}
%%-/
noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

/-%%
\begin{definition}[I₂]\label{I2}\lean{I₂}\leanok
$$
I_2(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
\left(
\frac{-\zeta'}\zeta(\sigma - i T)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma - i T)
X^{\sigma - i T} \ d\sigma
$$
\end{definition}
%%-/
noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

/-%%
\begin{definition}[I₃₇]\label{I37}\lean{I₃₇}\leanok
$$
I_{37}(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{-T}^{T}
\left(
\frac{-\zeta'}\zeta(\sigma_1 + t i)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
X^{\sigma_1 + t i} \ i \ dt
$$
\end{definition}
%%-/
noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

/-%%
\begin{definition}[I₈]\label{I8}\lean{I₈}\leanok
$$
I_8(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
\left(
\frac{-\zeta'}\zeta(\sigma + T i)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma + T i)
X^{\sigma + T i} \ d\sigma
$$
\end{definition}
%%-/
noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

/-%%
\begin{definition}[I₉]\label{I9}\lean{I₉}\leanok
$$
I_9(\nu, \epsilon, X, T) := \frac{1}{2\pi i} \int_{T}^{\infty}
\left(
\frac{-\zeta'}\zeta(\sigma_0 + t i)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
X^{\sigma_0 + t i} \ i \ dt
$$
\end{definition}
%%-/
noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

/-%%
\begin{definition}[I₃]\label{I3}\lean{I₃}\leanok
$$
I_3(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{-T}^{-3}
\left(
\frac{-\zeta'}\zeta(\sigma_1 + t i)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
X^{\sigma_1 + t i} \ i \ dt
$$
\end{definition}
%%-/
noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))


/-%%\begin{definition}[I₇]\label{I7}\lean{I₇}\leanok
$$
I_7(\nu, \epsilon, X, T, \sigma_1) := \frac{1}{2\pi i} \int_{3}^{T}
\left(
\frac{-\zeta'}\zeta(\sigma_1 + t i)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
X^{\sigma_1 + t i} \ i \ dt
$$
\end{definition}
%%-/
noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))


/-%%
\begin{definition}[I₄]\label{I4}\lean{I₄}\leanok
$$
I_4(\nu, \epsilon, X, \sigma_1, \sigma_2) := \frac{1}{2\pi i} \int_{\sigma_2}^{\sigma_1}
\left(
\frac{-\zeta'}\zeta(\sigma - 3 i)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma - 3 i)
X^{\sigma - 3 i} \ d\sigma
$$
\end{definition}
%%-/
noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

/-%%
\begin{definition}[I₆]\label{I6}\lean{I₆}\leanok
$$
I_6(\nu, \epsilon, X, \sigma_1, \sigma_2) := \frac{1}{2\pi i} \int_{\sigma_2}^{\sigma_1}
\left(
\frac{-\zeta'}\zeta(\sigma + 3 i)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma + 3 i)
X^{\sigma + 3 i} \ d\sigma
$$
\end{definition}
%%-/
noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

/-%%
\begin{definition}[I₅]\label{I5}\lean{I₅}\leanok
$$
I_5(\nu, \epsilon, X, \sigma_2) := \frac{1}{2\pi i} \int_{-3}^{3}
\left(
\frac{-\zeta'}\zeta(\sigma_2 + t i)
\right)
  \mathcal M(\widetilde 1_\epsilon)(\sigma_2 + t i)
X^{\sigma_2 + t i} \ i \ dt
$$
\end{definition}
%%-/
noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-3)..3,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

theorem realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  apply ContinuousAt.comp _ (by fun_prop)
  convert hf.continuousAt
  simp

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED
theorem riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (t : ℝ) :
  ∃ c > 0, ‖ζ (σ₀ + t * I)‖ ≤ c :=
  by
    let s := σ₀ + t * I
    let s_re : ℂ  := σ₀

    have H : s.re = σ₀ := by
          rw [add_re, ofReal_re, mul_re, ofReal_re, I_re, I_im]
          simp

    have non_neg : σ₀ ≠ 0 := by
      by_contra h
      rw [h] at σ₀_gt
      norm_cast at σ₀_gt

    have pos : s.re > 1 := by exact lt_of_lt_of_eq σ₀_gt (id (Eq.symm H))
    have pos_triv : s_re.re > 1 := by exact σ₀_gt

    have series := LSeries_one_eq_riemannZeta pos
    rw [← series]

    have identity : ∀(n : ℕ), ‖LSeries.term 1 s n‖ = 1 / n^σ₀ := by
      unfold LSeries.term
      intro n
      by_cases h0 : n = 0
      · simp [*]
      · simp [*]
        push_neg at h0
        have C : n > 0 := by exact Nat.zero_lt_of_ne_zero h0
        have T :=  Complex.norm_natCast_cpow_of_pos C s
        rw [H] at T
        exact T

    have summable : Summable (fun (n : ℕ) ↦  ‖LSeries.term 1 s n‖) := by
      simp [identity]
      exact σ₀_gt

    have B := calc
      ‖∑' (n : ℕ), LSeries.term 1 s n‖ ≤ ∑' (n : ℕ), ‖LSeries.term 1 s n‖ := norm_tsum_le_tsum_norm summable
      _                                ≤ ∑' (n : ℕ), (1 / ↑n^σ₀) := by simp [← identity]
      _                                ≤ norm (∑' (n : ℕ), (1 / ↑n^σ₀) : ℝ ) := by exact le_norm_self (∑' (n : ℕ), 1 / ↑n ^ σ₀)
      _                                ≤ 1 + norm (∑' (n : ℕ), (1 / ↑n^σ₀) : ℝ ) := by linarith

    let c : ℝ := 1 + norm (∑' (n : ℕ), (1 / ↑n^σ₀) : ℝ )

    have c_is_pos : c > 0 := by positivity
    use (1 + norm (∑' (n : ℕ), (1 / ↑n^σ₀) : ℝ ))
    exact ⟨c_is_pos, B⟩


theorem summable_real_iff_summable_coe_complex (f : ℕ → ℝ) :
    Summable f ↔ Summable (fun n => (f n : ℂ)) := by
  constructor

  · intro ⟨s, hs⟩
    use (s : ℂ)
    exact hasSum_ofReal.mpr hs

  · intro ⟨s, hs⟩
    use s.re
    have h_re : HasSum (fun n => ((f n : ℂ)).re) s.re :=
      by exact hasSum_re hs
    convert h_re using 1

theorem cast_pow_eq (n : ℕ) (σ₀ : ℝ):
  (↑((↑n : ℝ) ^ σ₀) : ℂ )  = (↑n : ℂ) ^ (↑σ₀ : ℂ) := by
    have U : (↑n : ℝ) ≥ 0 := by exact Nat.cast_nonneg' n
    have endit := Complex.ofReal_cpow U σ₀
    exact endit

theorem summable_complex_then_summable_real_part (f : ℕ → ℂ) :
  Summable f → Summable (fun n ↦ (f n).re) := by
    intro ⟨s, hs⟩
    use s.re
    have h_re : HasSum (fun n => ((f n : ℂ)).re) s.re :=
      by exact hasSum_re hs
    convert h_re using 1

theorem dlog_riemannZeta_bdd_on_vertical_lines_generalized :
  ∀(σ₀ σ₁ : ℝ), ∀(t : ℝ), 1 < σ₀ → σ₀ ≤ σ₁ →
    ‖(- ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
  intro σ₀
  intro σ₁
  intro t
  intro σ₀_gt_one
  intro σ₀_lt_σ₁

  let s₁ := σ₁ + t * I
  have s₁_re_eq_sigma : s₁.re = σ₁ := by
    rw [Complex.add_re (σ₁) (t * I)]
    rw [Complex.ofReal_re σ₁]
    rw [Complex.mul_I_re]
    simp [*]

  have s₀_re_eq_sigma : (↑σ₀ : ℂ).re = σ₀ := by
    rw [Complex.ofReal_re σ₀]

  let s₀ := σ₀

  have σ₁_gt_one : 1 < σ₁ := by exact lt_of_le_of_lt' σ₀_lt_σ₁ σ₀_gt_one
  have s₀_gt_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt_one

  have s₁_re_geq_one : 1 < s₁.re := by exact lt_of_lt_of_eq σ₁_gt_one (id (Eq.symm s₁_re_eq_sigma))
  have s₁_re_coerce_geq_one : 1 < (↑s₁.re : ℂ).re := by exact s₁_re_geq_one
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₁_re_geq_one)]
  unfold LSeries

  have summable_von_mangoldt : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) s₁.re i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₁_re_geq_one

  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt σ₀_gt_one

  have summable_re_von_mangoldt : Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) s₁.re i).re) := by
    exact summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) s₁.re) summable_von_mangoldt

  have summable_re_von_mangoldt_at_σ₀ : Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i).re) := by
    exact summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) σ₀) summable_von_mangoldt_at_σ₀

  have positivity : ∀(n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ = (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by
    intro n
    calc
      ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ = Λ n / ‖(↑n : ℂ)^(s₁ : ℂ)‖ := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · push_neg at h
          simp [*]
          have pos : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
          rw [abs_of_nonneg pos]

      _ = Λ n / (↑n)^s₁.re := by
        by_cases h : n = 0
        · simp [*]
        · rw [Complex.norm_natCast_cpow_of_pos]
          push_neg at h
          exact Nat.zero_lt_of_ne_zero h

      _ = (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · simp [*]
          push_neg at h
          ring_nf
          rw [Complex.re_ofReal_mul (Λ n)]
          ring_nf
          rw [Complex.inv_re]
          rw [Complex.cpow_ofReal_re]
          simp [*]
          left
          have N : (0 : ℝ) ≤ ↑n := by exact Nat.cast_nonneg' n
          have T2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).re = (↑n : ℝ)^σ₁ := by exact rfl
          have T1 : ((↑n : ℂ ) ^ (↑σ₁ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [T2]
            simp [*]
            exact Real.rpow_nonneg N σ₁


          simp [Complex.normSq_apply]
          simp [T1, T2]


  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ i‖) := by
    rw [summable_congr positivity]
    exact summable_re_von_mangoldt

  have triangle_ineq : ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), ↑‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖ :=
    norm_tsum_le_tsum_norm summable_abs_value

  have bounded_by_sum_of_re : ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n).re :=
    by
      simp [positivity] at triangle_ineq
      exact triangle_ineq

  have sum_of_re_commutes : ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n).re = (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)).re :=
    (Complex.re_tsum (summable_von_mangoldt)).symm

  have re_of_sum_bdd_by_norm : (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)).re  ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n)‖ :=
    Complex.re_le_norm (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s₁.re) n))

  have ineq_s₁_s₀ : ∀(n : ℕ),
    (LSeries.term (fun n ↦ Λ n) s₁.re n).re ≤ (LSeries.term (fun n ↦ Λ n) σ₀ n).re :=
  by
    intro n
    unfold LSeries.term
    by_cases h : n = 0
    · simp [*]
    · push_neg at h
      simp [*]
      have H : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      ring_nf
      rw [Complex.re_ofReal_mul (Λ n) ((↑n : ℂ) ^ (↑σ₁ : ℂ))⁻¹]
      rw [Complex.re_ofReal_mul (Λ n) ((↑n : ℂ) ^ (↑σ₀ : ℂ))⁻¹]
      refine mul_le_mul_of_nonneg_left ?_ H
      · simp [Complex.inv_re]
        have R1 : ((↑n : ℂ) ^ (↑σ₀ : ℂ)).re = (↑n : ℝ) ^ σ₀ := rfl
        have R2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).re = (↑n : ℝ) ^ σ₁ := rfl
        have geq : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
        have geq_zero : 0 ≤ n := Nat.zero_le n
        have n_geq_one : (1 : ℝ) ≤ ↑n := by
          norm_cast
        have n_geq_pos : (0 : ℝ) ≤ ↑n := by
          norm_cast
        have n_gt_pos : (0 : ℝ) < (↑n) := by
          norm_cast

        have I1 : ((↑n : ℂ) ^ (↑σ₀ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [R1]
            simp [*]
            exact Real.rpow_nonneg n_geq_pos σ₀

        have I2 : ((↑n : ℂ) ^ (↑σ₁ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [R2]
            simp [*]
            exact Real.rpow_nonneg n_geq_pos σ₁

        simp [Complex.normSq_apply, R1, R2, I1, I2]
        have P1 : 0 < (↑n : ℝ)^σ₁ := Real.rpow_pos_of_pos n_gt_pos σ₁
        have P2 : 0 < (↑n : ℝ)^σ₀ := Real.rpow_pos_of_pos n_gt_pos σ₀

        have N : (↑n : ℝ)^σ₀ ≤ (↑n : ℝ)^σ₁ :=
          Real.rpow_le_rpow_of_exponent_le n_geq_one σ₀_lt_σ₁
        apply inv_anti₀
        · exact P2
        · exact N

  have Z :=
    by
      calc
        ‖LSeries (fun n ↦ ↑(Λ n)) s₁‖ ≤ ∑' (n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ n‖
            := norm_tsum_le_tsum_norm summable_abs_value
      _ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s₁.re n).re := by simp [←positivity]
      _ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n).re := by
          refine Summable.tsum_mono ?_ ?_ ineq_s₁_s₀
          · exact summable_re_von_mangoldt
          · exact summable_re_von_mangoldt_at_σ₀
      _ = (∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n)).re := (Complex.re_tsum (summable_von_mangoldt_at_σ₀)).symm
      _ ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) σ₀ n)‖ := re_le_norm (∑' (n : ℕ), LSeries.term (fun n ↦ ↑(Λ n)) σ₀ n)
      _ = ‖- ζ' (σ₀) / ζ (σ₀)‖ := by
          simp only [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₀_gt_one)]
          unfold LSeries
          rfl
      _ = ‖ζ' σ₀ / ζ σ₀‖ := by
        rw [← s₀_re_eq_sigma]
        simp [*]

  exact Z


theorem triv_bound_zeta :
  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ → ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C
  := by

      let ⟨U, ⟨U_in_nhds, zeta_residue_on_U⟩⟩ := riemannZetaLogDerivResidue

      let ⟨open_in_U, ⟨open_in_U_subs_U, open_in_U_is_open, one_in_open_U⟩⟩ := mem_nhds_iff.mp U_in_nhds

      let ⟨ε₀, ⟨ε_pos, metric_ball_around_1_is_in_U'⟩⟩ := EMetric.isOpen_iff.mp open_in_U_is_open (1 : ℂ) one_in_open_U

      let ε := if ε₀ = ⊤ then ENNReal.ofReal 1 else ε₀
      have O1 : ε ≠ ⊤ := by
        by_cases h : ε₀ = ⊤
        · unfold ε
          simp [*]
        · unfold ε
          simp [*]

      have metric_ball_around_1_is_in_U :
        EMetric.ball (1 : ℂ) ε ⊆ U := by
          by_cases h : ε₀ = ⊤
          · unfold ε
            simp [*]
            have T : EMetric.ball (1 : ℂ) 1 ⊆ EMetric.ball 1 ε₀ := by
              simp [*]
            exact subset_trans (subset_trans T metric_ball_around_1_is_in_U') open_in_U_subs_U

          · unfold ε
            simp [h] at ε
            simp [h]
            exact subset_trans metric_ball_around_1_is_in_U' open_in_U_subs_U

      have O2 : ε ≠ 0 := by
        by_cases h : ε₀ = ⊤
        · unfold ε
          simp [*]
        · unfold ε
          simp [*]
          exact pos_iff_ne_zero.mp ε_pos

      let metric_ball_around_1 := EMetric.ball (1 : ℂ) ε
      let ε_div_two := ε / 2
      let boundary := ENNReal.toReal (1 + ε_div_two)

      let ⟨bound, ⟨bound_pos, bound_prop⟩⟩ :=
          BddAbove.exists_ge zeta_residue_on_U 0

      have boundary_geq_one : 1 < boundary := by
          unfold boundary
          have Z : (1 : ENNReal).toReal = 1 := by rfl
          rw [←Z]
          have U : ε_div_two ≠ ⊤ := by
            refine ENNReal.div_ne_top O1 ?_
            simp
          simp [ENNReal.toReal_lt_toReal O1 U]
          simp [ENNReal.toReal_add _ U]
          refine ENNReal.toReal_pos ?_ ?_
          · unfold ε_div_two
            simp [*]
          · exact U

      let const : ℝ := bound
      let final_const : ℝ := (boundary - 1)⁻¹ + const
      have boundary_inv_pos : 0 < (boundary - 1)⁻¹ := by
        ring_nf
        apply inv_pos_of_pos
        simp [*]

      have final_const_pos : final_const ≥ 0 := by
        unfold final_const
        simp [*]
        have Z :=
          by
            calc
              0 ≤ (boundary - 1)⁻¹ := by simp [boundary_inv_pos]; linarith
              _ ≤ (boundary - 1)⁻¹ + const := by unfold const; simp [bound_pos]

        exact Z

      have const_le_final_const : const ≤ final_const := by
        calc
          const ≤ (boundary - 1)⁻¹ + const := by simp [boundary_inv_pos]; linarith
          _ = final_const := by rfl

      /- final const is actually the constant that we will use -/

      have const_pos : const ≥ 0 := by
        linarith

      use final_const
      use final_const_pos
      intro σ₀
      intro t
      intro σ₀_gt

      -- Pick a neighborhood, if in neighborhood then we are good
      -- If outside of the neighborhood then use that ζ' / ζ is monotonic
      -- and take the bound to be the edge but this will require some more work

      by_cases h : σ₀ ≤ boundary
      · have σ₀_in_ball : (↑σ₀ : ℂ) ∈ metric_ball_around_1 := by
          unfold metric_ball_around_1
          unfold EMetric.ball
          simp [*]
          have Z := edist_dist (↑σ₀) (↑1 : ℂ)
          rw [Z]
          have U := dist_eq_norm (↑σ₀) (↑1 : ℂ)
          rw [U]
          norm_cast
          have U : 0 ≤ σ₀ - 1 := by linarith
          have U1 : ‖σ₀ - 1‖ = σ₀ - 1 := by exact norm_of_nonneg U
          have U2 : ε ≠ ⊤ := by exact O1
          have U3 : 0 ≤ ε := by exact zero_le ε
          simp [Real.norm_of_nonneg U]
          simp [ENNReal.ofReal_lt_iff_lt_toReal U U2]
          have U4 : ENNReal.ofReal 1 ≠ ⊤ := by exact ENNReal.ofReal_ne_top
          have Z0 : ε_div_two.toReal < ε.toReal := by
            have T1 : ε ≠ ⊤ := by exact U2
            have T2 : ε ≠ 0 := by exact O2
            have T3 : ε_div_two < ε := by
              refine ENNReal.half_lt_self ?_ U2
              exact T2

            exact ENNReal.toReal_strict_mono T1 T3

          have Z := by
            calc
              σ₀ - 1 ≤ boundary - 1 := by linarith
              _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
              _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp [ENNReal.toReal_ofReal]
              _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
              _ = ENNReal.toReal (ε_div_two) := by simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
              _ < ε.toReal := Z0

          exact Z

        have σ₀_in_U : (↑σ₀ : ℂ) ∈ (U \ {1}) := by
          refine mem_diff_singleton.mpr ?_
          constructor
          · unfold metric_ball_around_1 at σ₀_in_ball
            exact metric_ball_around_1_is_in_U σ₀_in_ball
          · by_contra a
            have U : σ₀ = 1 := by exact ofReal_eq_one.mp a
            rw [U] at σ₀_gt
            linarith

        have bdd := Set.forall_mem_image.mp bound_prop (σ₀_in_U)
        simp [*] at bdd
        have Z :=
          calc
            ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
               have U := dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ₀ t (σ₀_gt) (by simp)
               exact U
            _ = ‖- ζ' σ₀ / ζ σ₀‖ := by simp only [Complex.norm_div, norm_neg]
            _ = ‖(- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹) + (σ₀ - 1)⁻¹‖ := by simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
            _ ≤ ‖(- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹)‖ + ‖(σ₀ - 1)⁻¹‖ := by
              have Z := norm_add_le (- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹) ((σ₀ - 1)⁻¹)
              norm_cast at Z
            _ ≤ const + ‖(σ₀ - 1)⁻¹‖ := by
              have U := add_le_add_right bdd ‖(σ₀ - 1)⁻¹‖
              ring_nf at U
              ring_nf
              norm_cast at U
              norm_cast
            _ ≤ const + (σ₀ - 1)⁻¹ := by
              simp [norm_inv]
              have pos : 0 ≤ σ₀ - 1 := by
                linarith
              simp [abs_of_nonneg pos]
            _ = (σ₀ - 1)⁻¹ + const := by
              rw [add_comm]
            _ ≤ (σ₀ - 1)⁻¹ + final_const := by
              simp [const_le_final_const]

        exact Z

      · push_neg at h

        have boundary_geq_one : 1 < boundary := by
          unfold boundary
          have Z : (1 : ENNReal).toReal = 1 := by rfl
          rw [←Z]
          have U : ε_div_two ≠ ⊤ := by
            refine ENNReal.div_ne_top O1 ?_
            simp
          simp [ENNReal.toReal_lt_toReal O1 U]
          simp [ENNReal.toReal_add _ U]
          refine ENNReal.toReal_pos ?_ ?_
          · unfold ε_div_two
            simp [*]
          · exact U

        have boundary_in_ball : (↑boundary : ℂ) ∈ metric_ball_around_1 := by
          unfold metric_ball_around_1
          unfold EMetric.ball
          simp [*]
          have Z := edist_dist (↑boundary) (↑1 : ℂ)
          rw [Z]
          have U := dist_eq_norm (↑boundary) (↑1 : ℂ)
          rw [U]
          norm_cast
          have U : 0 ≤ boundary - 1 := by linarith
          have U1 : ‖boundary - 1‖ = boundary - 1 := by exact norm_of_nonneg U
          have U2 : ε ≠ ⊤ := by exact O1
          have U3 : 0 ≤ ε := by exact zero_le ε
          simp [Real.norm_of_nonneg U]
          simp [ENNReal.ofReal_lt_iff_lt_toReal U U2]
          have U4 : ENNReal.ofReal 1 ≠ ⊤ := by exact ENNReal.ofReal_ne_top
          have Z0 : ε_div_two.toReal < ε.toReal := by
            have T1 : ε ≠ ⊤ := by exact U2
            have T2 : ε ≠ 0 := by exact O2
            have T3 : ε_div_two < ε := by
              refine ENNReal.half_lt_self ?_ U2
              exact T2

            exact ENNReal.toReal_strict_mono T1 T3

          have Z := by
            calc
              boundary - 1 ≤ boundary - 1 := by linarith
              _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
              _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp [ENNReal.toReal_ofReal]
              _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
              _ = ENNReal.toReal (ε_div_two) := by simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
              _ < ε.toReal := Z0

          exact Z

        have boundary_in_U : (↑boundary : ℂ) ∈ U \ {1} := by
          refine mem_diff_singleton.mpr ?_
          constructor
          · unfold metric_ball_around_1 at boundary_in_ball
            exact metric_ball_around_1_is_in_U boundary_in_ball
          · by_contra a
            norm_cast at a
            norm_cast at boundary_geq_one
            simp [←a] at boundary_geq_one

        have bdd := Set.forall_mem_image.mp bound_prop (boundary_in_U)

        have Z :=
          calc
            ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ ‖ζ' boundary / ζ boundary‖ := by
               have U := dlog_riemannZeta_bdd_on_vertical_lines_generalized boundary σ₀ t (boundary_geq_one) (by linarith)
               exact U
            _ = ‖- ζ' boundary / ζ boundary‖ := by simp only [Complex.norm_div, norm_neg]
            _ = ‖(- ζ' boundary / ζ boundary - (boundary - 1)⁻¹) + (boundary - 1)⁻¹‖ := by simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
            _ ≤ ‖(- ζ' boundary / ζ boundary - (boundary - 1)⁻¹)‖ + ‖(boundary - 1)⁻¹‖ := by
              have Z := norm_add_le (- ζ' boundary / ζ boundary - (boundary - 1)⁻¹) ((boundary - 1)⁻¹)
              norm_cast at Z
            _ ≤ const + ‖(boundary - 1)⁻¹‖ := by
              have U9 := add_le_add_right bdd ‖(boundary - 1)⁻¹‖
              ring_nf at U9
              ring_nf
              norm_cast at U9
              norm_cast
              simp [*] at U9
              simp [*]
              exact U9

            _ ≤ const + (boundary - 1)⁻¹ := by
              simp [norm_inv]
              have pos : 0 ≤ boundary - 1 := by
                linarith
              simp [abs_of_nonneg pos]
            _ = (boundary - 1)⁻¹ + const := by
              rw [add_comm]
            _ = final_const := by rfl
            _ ≤ (σ₀ - 1)⁻¹ + final_const := by
              have H : 0 ≤ (σ₀ - 1)⁻¹ := by
                simp [inv_pos_of_pos]
                linarith

              simp [H]

        exact Z

lemma LogDerivZetaBndUnif :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9 := by
      let ⟨A, pf_A, C, C_pos, ζbd_in⟩ := LogDerivZetaBnd'
      let ⟨C_triv, ⟨pf_C_triv, ζbd_out⟩⟩ := triv_bound_zeta

      have T0 : A > 0 := by
        simp only [one_div, mem_Ioc] at pf_A
        exact (pf_A).1

      have ha : 1 ≤ A⁻¹ := by
        simp only [one_div, mem_Ioc, true_and, T0] at pf_A
        have U := (inv_le_inv₀ (by positivity) (by positivity)).mpr pf_A
        simp only [inv_inv] at U
        linarith

      use A
      use pf_A
      use ((1 + C + C_triv) * A⁻¹)
      use (by positivity)

      intro σ t hyp_t hyp_σ

      have logt_gt : (1 : ℝ) < Real.log |t| := by
        refine (Real.lt_log_iff_exp_lt (by linarith)).mpr (lt_trans ?_ hyp_t)
        exact lt_trans Real.exp_one_lt_d9 (by norm_num)

      have logt_gt' : (1 : ℝ) < Real.log |t| ^ 9 := by
        calc
          1 < Real.log |t| := logt_gt
          _ ≤ (Real.log |t|) ^ 9 := by exact ZetaInvBnd_aux logt_gt

      have logt_gt'' : (1 : ℝ) < 1 + A / Real.log |t| ^ 9 := by
        simp only [lt_add_iff_pos_right, div_pos_iff_of_pos_left, T0]
        positivity

      have T1 : ∀⦃σ : ℝ⦄, 1 + A / Real.log |t| ^ 9 ≤ σ → 1 < σ := by
        intro σ'
        intro hyp_σ'
        calc
          1 < 1 + A / Real.log |t| ^ 9 := logt_gt''
          _ ≤ σ' := hyp_σ'

      have T2 : ∀⦃σ : ℝ⦄, 1 + A / Real.log |t| ^ 9 ≤ σ → A / Real.log |t| ^ 9 ≤ σ - 1 := by
        intro σ'
        intro hyp_σ'
        calc
          A / Real.log |t| ^ 9 = (1 + A / Real.log |t| ^ 9) - 1 := by ring_nf
          _ ≤ σ' - 1 := by gcongr


      by_cases h : σ ∈ Ico (1 - A / Real.log |t| ^ 9) (1 + A / Real.log |t| ^ 9)
      · calc
          ‖ζ' (↑σ + ↑t * I) / ζ (↑σ + ↑t * I)‖ ≤ C * Real.log |t| ^ 9 := ζbd_in σ t hyp_t h
          _ ≤ ((1 + C + C_triv) * A⁻¹) * Real.log |t| ^ 9 := by
              gcongr
              · calc
                  C ≤ 1 + C := by simp only [le_add_iff_nonneg_left, zero_le_one]
                  _ ≤ (1 + C + C_triv) * 1 := by simp only [mul_one, le_add_iff_nonneg_right]; positivity
                  _ ≤ (1 + C + C_triv) * A⁻¹ := by gcongr

      · simp only [mem_Ico, tsub_le_iff_right, not_and, not_lt, mem_Ici] at h hyp_σ
        replace h := h hyp_σ
        calc
          ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by simp only [Complex.norm_div,
            norm_neg]

          _ ≤ (σ - 1)⁻¹ + C_triv := ζbd_out σ t (by exact T1 h)

          _ ≤ (A / Real.log |t| ^ 9)⁻¹ + C_triv := by
              gcongr
              · exact T2 h

          _ ≤ (A / Real.log |t| ^ 9)⁻¹ + C_triv * A⁻¹ := by
              gcongr
              · have hb : 0 ≤ C_triv := by linarith
                exact le_mul_of_one_le_right hb ha

          _ ≤ (1 + C_triv) * A⁻¹ * Real.log |t| ^ 9 := by
              simp only [inv_div]
              ring_nf
              gcongr
              · simp only [inv_pos, le_mul_iff_one_le_left, T0]
                linarith

          _ ≤ (1 + C + C_triv) * A⁻¹ * Real.log |t| ^ 9 := by gcongr; simp only [le_add_iff_nonneg_right]; positivity

def LogDerivZetaHasBound (A C : ℝ) : Prop :=∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9

theorem dlog_riemannZeta_bdd_on_vertical_lines_explicit {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∀(t : ℝ), ‖(-ζ' (σ₀ + t * I) / ζ (σ₀ + t * I))‖ ≤ ‖(ζ' σ₀ / ζ σ₀)‖ := by

  intro t
  let s := σ₀ + t * I
  have s_re_eq_sigma : s.re = σ₀ := by
    rw [Complex.add_re (σ₀) (t * I)]
    rw [Complex.ofReal_re σ₀]
    rw [Complex.mul_I_re]
    simp [*]

  have s₀_geq_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt
  have s_re_geq_one : 1 < s.re := by exact lt_of_lt_of_eq σ₀_gt (id (Eq.symm s_re_eq_sigma))
  have s_re_coerce_geq_one : 1 < (↑s.re : ℂ).re := by exact s_re_geq_one
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s_re_geq_one)]
  unfold LSeries

  have summable_von_mangoldt : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) s.re i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s_re_geq_one

  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₀_geq_one

  have summable_re_von_mangoldt : Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) s.re i).re) := by
    exact summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) s.re) summable_von_mangoldt

  have positivity : ∀(n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s n‖ = (LSeries.term (fun n ↦ Λ n) s.re n).re := by
    intro n
    calc
      ‖LSeries.term (fun n ↦ ↑(Λ n)) s n‖ = Λ n / ‖(↑n : ℂ)^(s : ℂ)‖ := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · push_neg at h
          simp [*]
          have pos : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
          rw [abs_of_nonneg pos]

      _ = Λ n / (↑n)^s.re := by
        by_cases h : n = 0
        · simp [*]
        · rw [Complex.norm_natCast_cpow_of_pos]
          push_neg at h
          exact Nat.zero_lt_of_ne_zero h

      _ = (LSeries.term (fun n ↦ Λ n) s.re n).re := by
        unfold LSeries.term
        by_cases h : n = 0
        · simp [*]
        · simp [*]
          push_neg at h
          ring_nf
          rw [Complex.re_ofReal_mul (Λ n)]
          ring_nf
          rw [Complex.inv_re]
          rw [Complex.cpow_ofReal_re]
          simp [*]
          left
          have N : (0 : ℝ) ≤ ↑n := by exact Nat.cast_nonneg' n
          have T2 : ((↑n : ℂ) ^ (↑σ₀ : ℂ)).re = (↑n : ℝ)^σ₀ := by exact rfl
          have T1 : ((↑n : ℂ ) ^ (↑σ₀ : ℂ)).im = 0 := by
            refine abs_re_eq_norm.mp ?_
            rw [T2]
            simp [*]
            exact Real.rpow_nonneg N σ₀


          simp [Complex.normSq_apply]
          simp [T1, T2]


  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(Λ n)) s i‖) := by
    rw [summable_congr positivity]
    exact summable_re_von_mangoldt

  have triangle_ineq : ‖LSeries (fun n ↦ ↑(Λ n)) s‖ ≤ ∑' (n : ℕ), ↑‖LSeries.term (fun n ↦ ↑(Λ n)) s n‖ :=
    norm_tsum_le_tsum_norm summable_abs_value

  have bounded_by_sum_of_re : ‖LSeries (fun n ↦ ↑(Λ n)) s‖ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n).re :=
    by
      simp [positivity] at triangle_ineq
      exact triangle_ineq

  have sum_of_re_commutes : ∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n).re = (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n)).re :=
    (Complex.re_tsum (summable_von_mangoldt)).symm

  have re_of_sum_bdd_by_norm : (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n)).re  ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n)‖ :=
    Complex.re_le_norm (∑' (n : ℕ), (LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n))

  have Z :=
    by
      calc
        ‖LSeries (fun n ↦ ↑(Λ n)) s‖ ≤ ∑' (n : ℕ), ‖LSeries.term (fun n ↦ ↑(Λ n)) s n‖
            := norm_tsum_le_tsum_norm summable_abs_value
      _ ≤ ∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s.re n).re := by simp [←positivity]
      _ = (∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s.re n)).re := (Complex.re_tsum (summable_von_mangoldt)).symm
      _ ≤ ‖∑' (n : ℕ), (LSeries.term (fun n ↦ Λ n) s.re n)‖ := re_le_norm (∑' (n : ℕ), LSeries.term (fun n ↦ ↑(Λ n)) (↑s.re) n)
      _ = ‖- ζ' (↑s.re) / ζ (↑s.re)‖ := by
          simp only [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s_re_coerce_geq_one)]
          unfold LSeries
          rfl
      _ = ‖ζ' σ₀ / ζ σ₀‖ := by
        rw [← s_re_eq_sigma]
        simp [*]

--          unfold LSeries
--      _ = ‖ζ' σ₀ / ζ σ₀‖ := by rw [←s_re_eq_sigma]
  exact Z


-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED
theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀)  :
  ∃ c > 0, ∀(t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ c := by

    let s_re : ℂ  := σ₀

    let new_const : ℝ := 1 + (↑(Norm.norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) (↑ s_re : ℂ ) n‖)) : ℝ )
    have new_const_is_pos : new_const > 0 := by positivity

    use new_const
    use new_const_is_pos
    intro t

    let s := σ₀ + t * I

    have DD : (↑ s.re : ℂ)  = s_re := by
      refine ofReal_inj.mpr ?_
      rw [add_re, ofReal_re, mul_re, ofReal_re, I_re, I_im]
      simp


    have L : s_re = σ₀ := by rfl

    have H : s.re = σ₀ := by
          rw [add_re, ofReal_re, mul_re, ofReal_re, I_re, I_im]
          simp

    have non_neg : σ₀ ≠ 0 := by
      by_contra h
      rw [h] at σ₀_gt
      norm_cast at σ₀_gt

    have pos : s.re > 1 := by exact lt_of_lt_of_eq σ₀_gt (id (Eq.symm H))
    have pos_triv : s_re.re > 1 := by exact σ₀_gt

    rw [← norm_neg, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div pos]

    have identity0 : ∀(n : ℕ), ‖LSeries.term 1 s n‖ = 1 / n^σ₀ := by
      unfold LSeries.term
      intro n
      by_cases h0 : n = 0
      · simp [*]
      · simp [*]
        push_neg at h0
        have C : n > 0 := by exact Nat.zero_lt_of_ne_zero h0
        have T :=  Complex.norm_natCast_cpow_of_pos C s
        rw [H] at T
        exact T

    have O : ∀(s : ℂ), ∀(n : ℕ), s.re = σ₀ → (↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ) : ℂ) = LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ ) n := by
      intro s
      intro n
      intro cond
--      have L : s_re = σ₀ := by rfl
      by_cases h1 : (n = 0)
      · simp [h1]
      · push_neg at h1
        unfold LSeries.term
        simp [*]
        have U : |Λ n| = Λ n := abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
        have R : n > 0 := by exact Nat.zero_lt_of_ne_zero h1
        rw [U]
        have Z := Complex.norm_natCast_cpow_of_pos R s
        rw [Z]
        rw [← L]
        --push_cast
        by_cases h : (Λ n = 0)
        · simp [h]
        · norm_cast
          apply_fun (fun (w : ℂ) ↦ w * (↑ n : ℂ)^s_re  / (Λ n))
          · simp [*]
            ring_nf
            rw [mul_comm]
            nth_rewrite 1 [mul_assoc]
            simp [*]
            have := cast_pow_eq n σ₀
            rw [this]
            simp [*]

          · have G : (↑ n : ℂ)^s_re  / (Λ n) ≠ 0 := by
              have T : (↑ n : ℂ)^s_re ≠ 0 := by
                have T : n > 0 := by exact R
                have M : ∃(m : ℕ), n = m + 1 := by exact Nat.exists_eq_succ_of_ne_zero h1
                let ⟨m, pf⟩ := M
                have U := Complex.natCast_add_one_cpow_ne_zero m s_re
                rw [pf]
                push_cast
                exact U
              refine div_ne_zero T ?_
              push_neg at h
              norm_cast
            have U := by exact mul_left_injective₀ G
            have T : (fun (x : ℂ) ↦ x * (↑ n : ℂ)^s_re  / (Λ n)) = (fun (x : ℂ) ↦ x * ((↑ n : ℂ)^s_re  / (Λ n))) := by funext x; exact mul_div_assoc x (↑n ^ s_re) ↑(Λ n)
            simp [←T] at U
            exact U

    have K : (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ)) = (fun (n : ℕ) ↦ (LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ )  n )) := by
      funext n
      rw [O s n H]

    have K1 : (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) (↑ s.re : ℂ) n‖ : ℝ)) = (fun (n : ℕ) ↦ (LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ )  n )) := by
      funext n
      rw [O (↑ s.re : ℂ) n H]
      simp [*]

    have D2 :  (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) s n‖ : ℝ)) = (fun (n : ℕ) ↦ ↑(‖LSeries.term (fun x ↦ (Λ x)) (↑ s.re : ℂ)  n‖ : ℝ)) := by
      simp [← K]

    have S : Summable (fun n ↦ (↑(‖LSeries.term (fun x ↦ Λ x) s n‖ : ℝ) : ℝ  )) := by
      apply (summable_real_iff_summable_coe_complex (fun n ↦ (↑(‖LSeries.term (fun x ↦ Λ x) s n‖ : ℝ) : ℝ  ))).mpr
      rw [K]
      have T := ArithmeticFunction.LSeriesSummable_vonMangoldt (pos_triv)
      have U : s_re = s.re := by exact congrFun (congrArg Complex.mk (id (Eq.symm H))) 0
      simp [← U]
      exact T

    have C := calc
      ‖∑' (n : ℕ), (LSeries.term (fun x ↦ Λ x) s n)‖ ≤ ∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) s n‖ := norm_tsum_le_tsum_norm S
--      _                                              = ∑' (n : ℕ), LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ )  n) := by simp [K]
      _                                              ≤ norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) s n‖) := by exact le_norm_self (∑' (n : ℕ), ‖LSeries.term (fun x ↦ ↑(Λ x)) s n‖)
      _                                              = norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) (↑ s.re : ℂ) n‖) := by simp [D2]
      _                                              ≤ 1 + norm (∑' (n : ℕ), ‖LSeries.term (fun x ↦ Λ x) ( ↑ s.re : ℂ) n‖ ) := by linarith
      _                                              = new_const := by rw [DD]

    exact C

/-%%
\begin{lemma}[dlog_riemannZeta_bdd_on_vertical_lines']\label{dlog_riemannZeta_bdd_on_vertical_lines'}\lean{dlog_riemannZeta_bdd_on_vertical_lines'}\leanok
For $\sigma_0 > 1$, there exists a constant $C > 0$ such that
$$
\forall t \in \R, \quad
\left\| \frac{\zeta'(\sigma_0 + t i)}{\zeta(\sigma_0 + t i)} \right\| \leq C.
$$
\end{lemma}
%%-/
theorem dlog_riemannZeta_bdd_on_vertical_lines' {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∃ C > 0, ∀ (t : ℝ), ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ C :=
  dlog_riemannZeta_bdd_on_vertical_lines σ₀_gt
/-%%
\begin{proof}\uses{LogDerivativeDirichlet}\leanok
Write as Dirichlet series and estimate trivially using Theorem \ref{LogDerivativeDirichlet}.
\end{proof}
%%-/

/-%%
\begin{lemma}[SmoothedChebyshevPull1_aux_integrable]\label{SmoothedChebyshevPull1_aux_integrable}\lean{SmoothedChebyshevPull1_aux_integrable}\leanok
The integrand $$\zeta'(s)/\zeta(s)\mathcal{M}(\widetilde{1_{\epsilon}})(s)X^{s}$$
is integrable on the contour $\sigma_0 + t i$ for $t \in \R$ and $\sigma_0 > 1$.
\end{lemma}
%%-/
theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines' σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
    intro t
    simp only [Complex.norm_mul, norm_neg, c]
    gcongr
    · convert hC t using 1
      simp
    · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
      · simp
      · linarith
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, ne_eq, c]
        linarith
  convert (SmoothedChebyshevDirichlet_aux_integrable ContDiffSmoothingF SmoothingFnonneg
    suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul ?_ ⟨c, this⟩ using 2
  · unfold SmoothedChebyshevIntegrand
    ring
  · apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousOn_univ]
    intro t _
    let s := σ₀ + (t : ℂ) * I
    have s_ne_one : s ≠ 1 := by
      intro h
      -- If σ₀ + t * I = 1, then taking real parts gives σ₀ = 1
      have : σ₀ = 1 := by
        have := congr_arg Complex.re h
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, one_re, s] at this
        exact this
      -- But this contradicts 1 < σ₀
      linarith [σ₀_gt]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have diffζ := differentiableAt_riemannZeta s_ne_one
      apply ContinuousAt.div
      · apply ContinuousAt.neg
        have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
          differentiableAt_deriv_riemannZeta s_ne_one
        convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) this <;> simp
      · convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp [σ₀_gt]
    · apply ContinuousAt.comp _ (by fun_prop)
      apply continuousAt_const_cpow
      norm_cast
      linarith

/-%%
\begin{proof}\uses{MellinOfSmooth1b, SmoothedChebyshevDirichlet_aux_integrable}\leanok
The $\zeta'(s)/\zeta(s)$ term is bounded, as is $X^s$, and the smoothing function
$\mathcal{M}(\widetilde{1_{\epsilon}})(s)$
decays like $1/|s|^2$ by Theorem \ref{MellinOfSmooth1b}.
Actually, we already know that
$\mathcal{M}(\widetilde{1_{\epsilon}})(s)$
is integrable from Theorem \ref{SmoothedChebyshevDirichlet_aux_integrable},
so we should just need to bound the rest.
\end{proof}
%%-/

/-%%
\begin{lemma}[BddAboveOnRect]\label{BddAboveOnRect}\lean{BddAboveOnRect}\leanok
Let $g : \C \to \C$ be a holomorphic function on a rectangle, then $g$ is bounded above on the rectangle.
\end{lemma}
%%-/
lemma BddAboveOnRect {g : ℂ → ℂ} {z w : ℂ} (holoOn : HolomorphicOn g (z.Rectangle w)) :
    BddAbove (norm ∘ g '' (z.Rectangle w)) := by
  have compact_rect : IsCompact (z.Rectangle w) := by
    apply IsCompact.reProdIm <;> apply isCompact_uIcc
  refine IsCompact.bddAbove_image compact_rect ?_
  apply holoOn.continuousOn.norm

/-%%
\begin{proof}\leanok
Use the compactness of the rectangle and the fact that holomorphic functions are continuous.
\end{proof}
%%-/


/-%%
\begin{theorem}[SmoothedChebyshevPull1]\label{SmoothedChebyshevPull1}\lean{SmoothedChebyshevPull1}\leanok
We have that
$$\psi_{\epsilon}(X) =
\mathcal{M}(\widetilde{1_{\epsilon}})(1)
X^{1} +
I_1 - I_2 +I_{37} + I_8 + I_9
.
$$
\end{theorem}
%%-/

theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X := by
  unfold SmoothedChebyshev
  unfold VerticalIntegral'
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    refine add_lt_add_of_le_of_lt ?_ ?_
    rfl
    rw[inv_pos, ← Real.log_one]
    apply Real.log_lt_log
    norm_num
    linarith
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw[← one_add_one_eq_two]
    refine (Real.add_lt_add_iff_left 1).mpr ?_
    refine inv_lt_one_of_one_lt₀ ?_
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    positivity
    have : rexp 1 < 3 := by exact lt_trans (Real.exp_one_lt_d9) (by norm_num)
    linarith
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  ·
    exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
      X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
  ·
    have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by field_simp
    repeat rw[smul_eq_mul]
    unfold I₁
    rw[temp, mul_add, mul_add, add_assoc, sub_eq_add_neg]
    nth_rewrite 4 [add_assoc]
    nth_rewrite 3 [add_assoc]
    nth_rewrite 2 [add_assoc]
    rw[add_assoc, add_left_cancel_iff, add_assoc]
    nth_rewrite 7 [add_comm]
    rw[← add_assoc]
    unfold I₉
    rw[add_right_cancel_iff, ← add_right_inj (1 / (2 * ↑π * I) *
      -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
      ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
    unfold VIntegral I₂ I₃₇ I₈
    rw[smul_eq_mul, temp, ← add_assoc, ← add_assoc]
    nth_rewrite 2 [div_mul_comm]
    rw[mul_one, ← neg_div, ← mul_neg]
    nth_rewrite 2 [← one_div_mul_eq_div]
    repeat rw[← mul_add]
    let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
      SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
    let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
    have : ∫ (y : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
      ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
      unfold fTempRR
      rw[temp]
    rw[this]
    have : ∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I) =
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
      unfold fTempRR
      rw[Complex.ofReal_neg, neg_mul]
      rfl
    rw[this]
    have : ∫ (t : ℝ) in -T..T, SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
      ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := by rfl
    rw[this]
    have : ∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ + ↑T * I) =
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := by rfl
    rw[this]
    repeat rw[← add_assoc]
    have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
      -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
      I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
        -1 * RectangleIntegral fTempC ((1 : ℝ) + (Real.log X)⁻¹ + T * I) (σ₁ - T * I) := by
      unfold RectangleIntegral
      rw[HIntegral_symm, VIntegral_symm]
      nth_rewrite 2 [HIntegral_symm, VIntegral_symm]
      unfold HIntegral VIntegral
      repeat rw[smul_eq_mul]
      repeat rw[add_re]
      repeat rw[add_im]
      repeat rw[sub_re]
      repeat rw[sub_im]
      repeat rw[mul_re]
      repeat rw[mul_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      rw[I_re, I_im, mul_zero, zero_mul, mul_one]
      ring_nf
      unfold fTempC
      have : ∫ (y : ℝ) in -T..T, fTempRR (I * ↑y + ↑σ₁).re (I * ↑y + ↑σ₁).im =
        ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := by simp
      rw[this]
      have : ∫ (y : ℝ) in -T..T,
          fTempRR (I * ↑y + ↑(1 + (Real.log X)⁻¹)).re (I * ↑y + ↑(1 + (Real.log X)⁻¹)).im =
        ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by simp
      rw[this]
      have : ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR (I * ↑T + ↑x).re (I * ↑T + ↑x).im =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := by simp
      rw[this]
      have : ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR (I * ↑(-T) + ↑x).re (I * ↑(-T) + ↑x).im =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by simp
      rw[this]
      ring_nf
    rw[this, neg_one_mul, div_mul_comm, mul_one,
        ← add_right_inj
        (RectangleIntegral fTempC (1 + ↑(Real.log X)⁻¹ + ↑T * I) (↑σ₁ - ↑T * I) / (2 * ↑π * I)),
        ← add_assoc]
    field_simp
    rw[rectangleIntegral_symm]
    have : RectangleIntegral fTempC (↑σ₁ - ↑T * I) (1 + 1 / ↑(Real.log X) + ↑T * I) / (2 * ↑π * I) =
      RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
      unfold RectangleIntegral'
      rw[smul_eq_mul]
      field_simp
    rw[this]

    let holoMatch : ℂ → ℂ := fun z ↦
      (fTempC z - (𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) 1 * ↑X) / (z - 1))
    have inv_log_X_pos: 0 < (Real.log X)⁻¹ := by
      rw[inv_pos, ← Real.log_one]
      apply Real.log_lt_log (by positivity) (by linarith)
    have pInRectangleInterior :
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
      refine rectangle_mem_nhds_iff.mpr ?_
      refine mem_reProdIm.mpr ?_
      have : re 1 = 1 := by rfl
      rw[this]
      have : im 1 = 0 := by rfl
      rw[this]
      repeat rw[sub_re]
      repeat rw[sub_im]
      repeat rw[add_re]
      repeat rw[add_im]
      rw[mul_re, mul_im, I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have temp : 1 ∈ uIoo σ₁ (re 1 + (Real.log X)⁻¹) := by
        have : re 1 = 1 := by rfl
        rw[this]
        unfold uIoo
        have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
        rw[this]
        have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by exact max_eq_right (by linarith)
        rw[this]
        refine mem_Ioo.mpr ?_
        exact ⟨σ₁_lt_one, (by linarith)⟩
      have : 0 ∈ uIoo (-T) (T + im 1) := by
        have : im 1 = 0 := by rfl
        rw[this, add_zero]
        unfold uIoo
        have : min (-T) T = -T := by exact min_eq_left (by linarith)
        rw[this]
        have : max (-T) T = T := by exact max_eq_right (by linarith)
        rw[this]
        refine mem_Ioo.mpr ?_
        exact ⟨(by linarith), (by linarith)⟩
      exact ⟨temp, this⟩
    --TODO:
    have holoMatchHoloOn : HolomorphicOn holoMatch
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) \ {1}) := by
      unfold HolomorphicOn holoMatch
      refine DifferentiableOn.sub ?_ ?_
      · unfold fTempC fTempRR
        have : (fun z ↦ SmoothedChebyshevIntegrand SmoothingF ε X (↑z.re + ↑z.im * I)) =
          (fun z ↦ SmoothedChebyshevIntegrand SmoothingF ε X z) := by
          apply funext
          intro z
          have : (↑z.re + ↑z.im * I) = z := by exact re_add_im z
          rw[this]
        rw[this]
        refine DifferentiableOn.mul ?_ ?_
        · refine DifferentiableOn.mul ?_ ?_
          · have : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)) := by
              refine funext ?_
              intro x
              exact neg_div (ζ x) (ζ' x)
            rw[this]
            refine DifferentiableOn.neg ?_
            unfold DifferentiableOn
            intro x x_location
            unfold Rectangle at x_location
            rw[Set.mem_diff, Complex.mem_reProdIm, sub_re, add_re, sub_im, add_im, mul_re, mul_im,
              I_re, I_im, add_re, add_im] at x_location
            simp only [ofReal_re, mul_zero, ofReal_im, mul_one, sub_self, sub_zero, one_re,
              ofReal_inv, inv_re, normSq_ofReal, div_self_mul_self', add_zero, zero_sub, one_im,
              inv_im, neg_zero, zero_div, zero_add, mem_singleton_iff] at x_location

            -- repeat rw[ofReal_re] at x_location
            -- repeat rw[ofReal_im] at x_location
            obtain ⟨⟨xReIn, xImIn⟩, xOut⟩ := x_location
            unfold uIcc at xReIn xImIn
            have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
            rw[this] at xReIn
            have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by exact max_eq_right (by linarith)
            rw[this] at xReIn
            have : min (-T) T = (-T) := by exact min_eq_left (by linarith)
            rw[this] at xImIn
            have : max (-T) T = T := by exact max_eq_right (by linarith)
            rw[this] at xImIn
            unfold HolomorphicOn DifferentiableOn at holoOn
            have temp : DifferentiableWithinAt ℂ (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) x := by
              have : x ∈ Icc σ₁ 2 ×ℂ Icc (-T) T \ {1} := by
                rw [Set.mem_diff, Complex.mem_reProdIm]
                have xReTemp : x.re ∈ Icc σ₁ 2 := by
                  have xReLb : σ₁ ≤ x.re := by exact xReIn.1
                  have xReUb : x.re ≤ 2 := by exact (lt_of_le_of_lt xReIn.2 X_eq_lt_two).le
                  exact ⟨xReLb, xReUb⟩
                have xImTemp : x.im ∈ Icc (-T) T := by exact ⟨xImIn.1, xImIn.2⟩
                exact ⟨⟨xReTemp, xImTemp⟩, xOut⟩
              exact holoOn x this


            have : ((↑σ₁ - ↑T * I).Rectangle (1 + ↑(Real.log X)⁻¹ + ↑T * I) \ {1}) ⊆
              (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) := by
              intro a a_location
              rw[Set.mem_diff, Complex.mem_reProdIm]
              rw[Set.mem_diff] at a_location
              obtain ⟨aIn, aOut⟩ := a_location
              unfold Rectangle uIcc at aIn
              rw[sub_re, add_re, add_re, sub_im, add_im, add_im, mul_re, mul_im, ofReal_re, ofReal_re, ofReal_re, ofReal_im, ofReal_im, ofReal_im, I_re, I_im] at aIn
              have : re 1 = 1 := by rfl
              rw[this] at aIn
              have : im 1 = 0 := by rfl
              rw[this] at aIn
              ring_nf at aIn
              have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by linarith
              rw[this] at aIn
              have : max σ₁ (1 + (Real.log X)⁻¹) = 1 + (Real.log X)⁻¹ := by linarith
              rw[this] at aIn
              have : min (-T) T = (-T) := by linarith
              rw[this] at aIn
              have : max (-T) T = T := by linarith
              rw[this] at aIn
              rw[Complex.mem_reProdIm] at aIn
              obtain ⟨aReIn, aImIn⟩ := aIn
              have aReInRedo : a.re ∈ Icc σ₁ 2 := by
                have : a.re ≤ 2 := by exact (lt_of_le_of_lt aReIn.2 X_eq_lt_two).le
                exact ⟨aReIn.1, this⟩
              exact ⟨⟨aReInRedo, aImIn⟩, aOut⟩
            exact DifferentiableWithinAt.mono temp this
          · unfold DifferentiableOn
            intro x x_location
            refine DifferentiableAt.differentiableWithinAt ?_
            have hε : ε ∈ Ioo 0 1 := by exact ⟨ε_pos, ε_lt_one⟩
            have xRePos : 0 < x.re := by
              unfold Rectangle at x_location
              rw[Set.mem_diff, Complex.mem_reProdIm] at x_location
              obtain ⟨⟨xReIn, _⟩, _⟩ := x_location
              unfold uIcc at xReIn
              rw[sub_re, add_re, add_re, mul_re, I_re, I_im] at xReIn
              repeat rw[ofReal_re] at xReIn
              repeat rw[ofReal_im] at xReIn
              ring_nf at xReIn
              have : re 1 = 1 := by rfl
              rw[this] at xReIn
              have : min σ₁ (1 + (Real.log X)⁻¹) = σ₁ := by exact min_eq_left (by linarith)
              rw[this] at xReIn
              have : σ₁ ≤ x.re := by exact xReIn.1
              linarith
            exact Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF hε SmoothingFnonneg mass_one xRePos
        · unfold DifferentiableOn
          intro x x_location
          apply DifferentiableAt.differentiableWithinAt
          unfold HPow.hPow instHPow
          simp only
          apply DifferentiableAt.const_cpow
          · exact differentiableAt_fun_id
          · left
            refine ne_zero_of_re_pos ?_
            simp only [ofReal_re]
            linarith
      · refine DifferentiableOn.mul ?_ ?_
        ·
          unfold DifferentiableOn
          intro x x_location
          rw[Set.mem_diff] at x_location
          obtain ⟨xInRect, xOut⟩ := x_location
          apply DifferentiableAt.differentiableWithinAt
          apply differentiableAt_const
        · unfold DifferentiableOn
          intro x x_location
          apply DifferentiableAt.differentiableWithinAt
          apply DifferentiableAt.inv
          · fun_prop
          · intro h
            rw [sub_eq_zero] at h
            have := x_location.2
            simp only [mem_singleton_iff] at this
            exact this h

    have holoMatchBddAbove : BddAbove
        (norm ∘ holoMatch '' (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) \ {1})) := by
      let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
      let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
      let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
      have bigO_holoMatch : holoMatch =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
        unfold holoMatch fTempC fTempRR SmoothedChebyshevIntegrand
        simp only [re_add_im]
        have : (fun z ↦
            (-ζ' z / ζ z * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z -
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) 1 * ↑X / (z - 1))) =
            (fun z ↦ (f z * g z - 1 * g 1 / (z - 1))) := by
          apply funext
          intro x
          simp[f, g]
          rw[mul_assoc]
        rw[this]
        have g_holc : HolomorphicOn g U := by
          unfold HolomorphicOn DifferentiableOn
          intro u uInU
          refine DifferentiableAt.differentiableWithinAt ?_
          simp[g]
          refine DifferentiableAt.mul ?_ ?_
          have hε : ε ∈ Set.Ioo 0 1 := by exact ⟨ε_pos, ε_lt_one⟩
          have hu : 0 < u.re := by
            simp[U] at uInU
            unfold Rectangle uIcc at uInU
            rw[Complex.mem_reProdIm] at uInU
            obtain ⟨uReIn, uImIn⟩ := uInU
            have : min (↑σ₁ - ↑T * I).re (1 + (↑(Real.log X))⁻¹ + ↑T * I).re = σ₁ := by
              rw[sub_re, add_re, add_re, mul_re, I_re, I_im]
              repeat rw[ofReal_re]
              repeat rw[ofReal_im]
              simp
              linarith
            rw[this] at uReIn
            have : σ₁ ≤ u.re := by exact uReIn.1
            linarith
          exact Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF hε SmoothingFnonneg mass_one hu
          unfold HPow.hPow instHPow
          simp
          apply DifferentiableAt.const_cpow
          exact differentiableAt_fun_id
          refine Or.inl ?_
          refine ne_zero_of_re_pos ?_
          rw[ofReal_re]
          positivity
        have U_in_nhds : U ∈ nhds 1 := by
          simp only [U]
          exact pInRectangleInterior
        have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
          simp[f]
          have : ((fun z ↦ -ζ' z / ζ z) - fun z ↦ (z - 1)⁻¹) =
            (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
            apply funext
            intro z
            simp
          rw[this]
          exact riemannZetaLogDerivResidueBigO
        exact ResidueMult g_holc U_in_nhds f_near_p
      have : ∃ V ∈ nhds 1, BddAbove (norm ∘ holoMatch '' (V \ {1})) := by exact IsBigO_to_BddAbove bigO_holoMatch
      obtain ⟨V, VInNhds_one, BddAboveV⟩ := this
      have : ∃ W ⊆ V, 1 ∈ W ∧ IsOpen W ∧ BddAbove (norm ∘ holoMatch '' (W \ {1})) := by
        rw[mem_nhds_iff] at VInNhds_one
        obtain ⟨W, WSubset, WOpen, one_in_W⟩ := VInNhds_one
        use W
        have : BddAbove (Norm.norm ∘ holoMatch '' (W \ {1})) := by
          have : Norm.norm ∘ holoMatch '' (W \ {1}) ⊆
            Norm.norm ∘ holoMatch '' (V \ {1}) := by
            exact image_mono (by exact diff_subset_diff_left WSubset)
          exact BddAbove.mono this BddAboveV
        exact ⟨WSubset, ⟨one_in_W, WOpen, this⟩⟩
      obtain ⟨W, WSubset, one_in_W, OpenW, BddAboveW⟩ := this
      have : (↑σ₁ - ↑T * I).Rectangle (1 + ↑(Real.log X)⁻¹ + ↑T * I) = U := by rfl
      rw[this] at holoMatchHoloOn ⊢
      have one_in_U : 1 ∈ U := by
        have U_in_nhds : U ∈ nhds 1 := by
          simp only [U]
          exact pInRectangleInterior
        exact mem_of_mem_nhds U_in_nhds
      have (h1 : 1 ∈ U) (h2 : 1 ∈ W) : U \ {1} = (U \ W) ∪ ((U ∩ W) \ {1}) := by
        ext x
        simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff]
        constructor
        intro ⟨hxU, hx1⟩
        by_cases hw : x ∈ W
        · right
          exact ⟨⟨hxU, hw⟩, hx1⟩
        · left
          exact ⟨hxU, hw⟩
        · intro h
          cases' h with h_left h_right
          have : x ≠ 1 := by
            intro x_eq_1
            rw[x_eq_1] at h_left
            exact h_left.2 h2
          · exact ⟨h_left.1, this⟩
          · exact ⟨h_right.1.1, h_right.2⟩
      rw[this one_in_U one_in_W]
      have : Norm.norm ∘ holoMatch '' (U \ W ∪ (U ∩ W) \ {1}) =
        Norm.norm ∘ holoMatch '' (U \ W) ∪ Norm.norm ∘ holoMatch '' ((U ∩ W) \ {1}) := by
        exact image_union (Norm.norm ∘ holoMatch) (U \ W) ((U ∩ W) \ {1})
      rw[this]
      refine BddAbove.union ?_ ?_
      refine IsCompact.bddAbove_image ?_ ?_
      refine IsCompact.diff ?_ ?_
      unfold U Rectangle
      apply IsCompact.reProdIm
      unfold uIcc
      exact isCompact_Icc
      unfold uIcc
      exact isCompact_Icc
      exact OpenW
      refine Continuous.comp_continuousOn ?_ ?_
      exact continuous_norm
      have : HolomorphicOn holoMatch (U \ W) := by
        have : U \ W ⊆ U \ {1} := by
          intro x x_location
          obtain ⟨xInU, xOutW⟩ := x_location
          rw[Set.mem_diff]
          apply And.intro
          exact xInU
          rw[Set.mem_singleton_iff]
          intro x_eq_1
          rw[x_eq_1] at xOutW
          exact xOutW one_in_W
        exact DifferentiableOn.mono holoMatchHoloOn this
      unfold HolomorphicOn at this
      exact DifferentiableOn.continuousOn this
      have : Norm.norm ∘ holoMatch '' ((U ∩ W) \ {1}) ⊆
        Norm.norm ∘ holoMatch '' (W \ {1}) := by
        have : (U ∩ W) \ {1} ⊆ W \ {1} := by
          intro x x_location
          rw[Set.mem_diff] at x_location
          obtain ⟨⟨xInU, xInW⟩, xOut⟩ := x_location
          exact ⟨xInW, xOut⟩
        exact image_mono this
      exact BddAbove.mono this BddAboveW

    obtain ⟨g, gHolo_Eq⟩ := existsDifferentiableOn_of_bddAbove
      pInRectangleInterior holoMatchHoloOn holoMatchBddAbove
    obtain ⟨gHolo, gEq⟩ := gHolo_Eq

    have zRe_le_wRe : (σ₁ - ↑T * I).re ≤ (1 + (Real.log X)⁻¹ + T * I).re := by
      repeat rw[sub_re]
      repeat rw[add_re]
      repeat rw[mul_re]
      rw[I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have : re 1 = 1 := by rfl
      rw[this]
      linarith
    have zIm_le_wIm : (σ₁ - ↑T * I).im ≤ (1 + (Real.log X)⁻¹ + T * I).im := by
      repeat rw[sub_im]
      repeat rw[add_im]
      repeat rw[mul_im]
      rw[I_re, I_im]
      repeat rw[ofReal_re]
      repeat rw[ofReal_im]
      ring_nf
      have : im 1 = 0 := by rfl
      rw[this]
      linarith
    exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm
      pInRectangleInterior gHolo gEq

/-%%
\begin{proof}\leanok
\uses{SmoothedChebyshev, RectangleIntegral, ResidueMult, riemannZetaLogDerivResidue,
SmoothedChebyshevPull1_aux_integrable, BddAboveOnRect, BddAbove_to_IsBigO,
I1, I2, I37, I8, I9}
Pull rectangle contours and evaluate the pole at $s=1$.
\end{proof}
%%-/

lemma interval_membership (r : ℝ)(a b: ℝ)(h1 : r ∈ Set.Icc (min a b) (max a b)) (h2 : a < b) :
  a ≤ r ∧ r ≤ b := by
  -- Since a < b, we have min(a,b) = a and max(a,b) = b
  have min_eq : min a b = a := min_eq_left (le_of_lt h2)
  have max_eq : max a b = b := max_eq_right (le_of_lt h2)
  rw [min_eq, max_eq] at h1
  rw [← @mem_Icc]
  exact h1

lemma verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    VIntegral f σ s e =
    VIntegral f σ s a +
    VIntegral f σ a b +
    VIntegral f σ b e := by
  dsimp [VIntegral]
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
  rw[← intervalIntegral.integral_add_adjacent_intervals (b := a), ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
  · ring
  all_goals apply IntervalIntegrable.mono_set hf; apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith

lemma verticalIntegral_split_three_finite' {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s e) =
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) := by
  have : (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) = (1 : ℂ) / (2 * π * I) * ((VIntegral f σ s a) +
    (VIntegral f σ a b) +
    (VIntegral f σ b e)) := by ring
  rw [this]
  clear this
  rw [← verticalIntegral_split_three_finite hf hab]

theorem SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
  (holoOn : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
  ContinuousOn (fun (t : ℝ) ↦ -ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)) (Icc (-T) T) := by
  rw [show (fun (t : ℝ) ↦ -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) = -(ζ' / ζ) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
  apply ContinuousOn.neg
  apply holoOn.continuousOn.comp (by fun_prop)
  intro t ht
  simp
  constructor
  · apply mem_reProdIm.mpr
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
    linarith
  · intro h
    replace h := congr_arg re h
    simp at h
    linarith

/-%%
Next pull contours to another box.
\begin{lemma}[SmoothedChebyshevPull2]\label{SmoothedChebyshevPull2}\lean{SmoothedChebyshevPull2}\leanok
We have that
$$
I_{37} =
I_3 - I_4 + I_5 + I_6 + I_7
.
$$
\end{lemma}
%%-/

theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith
  -- Step (1)
  -- Show that the Rectangle is in a given subset of holomorphicity
  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
    -- for every point x in the Rectangle
    intro x hx
    constructor
    . -- x is in the locus of holomorphicity
      simp only [Rectangle, uIcc] at hx
      rw [Complex.mem_reProdIm] at hx ⊢
      obtain ⟨hx_re, hx_im⟩ := hx
      -- the real part of x is in the correct interval
      have hzw_re : z.re < w.re := by
        dsimp [z, w]
        linarith
      have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
        exact interval_membership x.re z.re w.re hx_re hzw_re
      have x_re_in_Icc : x.re ∈ Icc σ₂ 2 := by
        have ⟨h_left, h_right⟩ := x_re_bounds
        have h_left' : σ₂ ≤ x.re := by
          dsimp [z] at h_left
          linarith
        have h_right' : x.re ≤ 2 := by
          apply le_trans h_right
          dsimp [w]
          linarith
        exact ⟨h_left', h_right'⟩
      -- the imaginary part of x is in the correct interval
      have hzw_im : z.im < w.im := by
        dsimp [z, w]
        linarith
      have x_im_bounds : z.im ≤ x.im ∧ x.im ≤ w.im := by
        exact interval_membership x.im z.im w.im hx_im hzw_im
      have x_im_in_Icc : x.im ∈ Icc (-3) 3 := by
        have ⟨h_left, h_right⟩ := x_im_bounds
        have h_left' : -3 ≤ x.im := by
          dsimp [z] at h_left
          linarith
        have h_right' : x.im ≤ 3 := by
          dsimp [w] at h_right
          linarith
        exact ⟨h_left', h_right'⟩
      exact ⟨x_re_in_Icc, x_im_in_Icc⟩
    -- x is not in {1} by contradiction
    . simp only [mem_singleton_iff]
      -- x has real part less than 1
      have x_re_upper: x.re ≤ σ₁ := by
        simp only [Rectangle, uIcc] at hx
        rw [Complex.mem_reProdIm] at hx
        obtain ⟨hx_re, _⟩ := hx
        -- the real part of x is in the interval
        have hzw_re : z.re < w.re := by
          dsimp [z, w]
          linarith
        have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
          exact interval_membership x.re z.re w.re hx_re hzw_re
        have x_re_upper' : x.re ≤ w.re := by exact x_re_bounds.2
        dsimp [w] at x_re_upper'
        linarith
      -- by contracdiction
      have h_x_ne_one : x ≠ 1 := by
        intro h_eq
        have h_re : x.re = 1 := by rw [h_eq, Complex.one_re]
        have h1 : 1 ≤ σ₁ := by
          rw [← h_re]
          exact x_re_upper
        linarith
      exact h_x_ne_one
  have zero_over_box := HolomorphicOn.vanishesOnRectangle holoOn2 sub
  have splitting : I₃₇ SmoothingF ε T X σ₁ =
    I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    unfold I₃₇ I₃ I₅ I₇
    apply verticalIntegral_split_three_finite'
    · apply ContinuousOn.integrableOn_Icc
      unfold SmoothedChebyshevIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t t_mem
          have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF  ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
          simpa using realDiff_of_complexDiff _ this
      · apply continuousOn_of_forall_continuousAt
        intro t t_mem
        apply ContinuousAt.comp
        · refine continuousAt_const_cpow' ?_
          intro h
          have : σ₁ = 0 := by
            have h_real : (↑σ₁ + ↑t * I).re = (0 : ℂ).re := by
              rw [h]
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, zero_re, z, w] at h_real
            exact h_real
          linarith
        · -- continuity -- failed
          apply ContinuousAt.add
          · exact continuousAt_const
          · apply ContinuousAt.mul
            · apply continuous_ofReal.continuousAt
            · exact continuousAt_const
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc I₃₇ SmoothingF ε T X σ₁ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
    - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by simp [RectangleIntegral]
    _ = I₃₇ SmoothingF ε T X σ₁ - ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
        neg_add_cancel_right, sub_right_inj, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
    --- starting from now, we split the integral `I₃₇` into `I₃ σ₂ + I₅ σ₁ + I₇ σ₁` using `verticalIntegral_split_three_finite`
    _ = I₃ SmoothingF ε T X σ₁
    + I₅ SmoothingF ε X σ₁
    + I₇ SmoothingF ε T X σ₁
    - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      rw [splitting]
    _ = I₃ SmoothingF ε T X σ₁
    - I₄ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₂
    + I₆ SmoothingF ε X σ₁ σ₂
    + I₇ SmoothingF ε T X σ₁ := by
      ring

/-%%
\begin{proof}\uses{HolomorphicOn.vanishesOnRectangle, I3, I4, I5, I6, I7, I37}\leanok
Mimic the proof of Lemma \ref{SmoothedChebyshevPull1}.
\end{proof}
%%-/

/-%%
We insert this information in $\psi_{\epsilon}$. We add and subtract the integral over the box
$[1-\delta,2] \times_{ℂ} [-T,T]$, which we evaluate as follows
\begin{theorem}[ZetaBoxEval]\label{ZetaBoxEval}\lean{ZetaBoxEval}\leanok
For all $\epsilon > 0$ sufficiently close to $0$, the rectangle integral over $[1-\delta,2] \times_{ℂ} [-T,T]$ of the integrand in
$\psi_{\epsilon}$ is
$$
\frac{X^{1}}{1}\mathcal{M}(\widetilde{1_{\epsilon}})(1)
= X(1+O(\epsilon))
,$$
where the implicit constant is independent of $X$.
\end{theorem}
%%-/
theorem ZetaBoxEval {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C, ∀ᶠ ε in (nhdsWithin 0 (Ioi 0)), ∀ X : ℝ, 0 ≤ X →
    ‖𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X - X‖ ≤ C * ε * X := by
  have := MellinOfSmooth1c ContDiffSmoothingF suppSmoothingF mass_one
  clear suppSmoothingF mass_one ContDiffSmoothingF
  rw[Asymptotics.isBigO_iff] at this
  obtain ⟨C, hC⟩ := this
  use C
  have εpos : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), ε > 0 :=
    eventually_mem_of_tendsto_nhdsWithin fun ⦃U⦄ hU ↦ hU
  filter_upwards [hC, εpos] with ε hC εpos
  rw[id_eq, norm_of_nonneg (le_of_lt εpos)] at hC
  intro X Xnne
  nth_rw 2 [← one_mul (X : ℂ)]
  rw[← sub_mul, norm_mul, norm_real, norm_of_nonneg Xnne]
  exact mul_le_mul_of_nonneg_right hC Xnne

--set_option maxHeartbeats 4000000


theorem norm_reciprocal_inequality_1 (x : ℝ) (x₁ : ℝ) (hx₁ : x₁ ≥ 1) :
  ‖x^2 + x₁^2‖₊⁻¹ ≤ (‖x₁‖₊^2)⁻¹ := by
  -- First, establish that x₁² ≥ 1 since x₁ ≤ -1
  have h1 : x₁^2 ≥ 1 := by
    have h_abs : |x₁| ≥ 1 := by
      rw [abs_of_pos]
      linarith
      positivity
    simp only [ge_iff_le, one_le_sq_iff_one_le_abs, h_abs]

  -- Show that x² + x₁² ≥ x₁²
  have h2 : x^2 + x₁^2 ≥ x₁^2 := by
    linarith [sq_nonneg x]

  -- Show that x₁² > 0
  have h3 : x₁^2 > 0 := by
    apply sq_pos_of_ne_zero
    linarith

  have h33 : 2 * x₁^2 > 0 := by
    simp [*]

  -- Show that x² + x₁² > 0
  have h4 : x^2 + x₁^2 > 0 := by
    linarith [sq_nonneg x, h3]

  -- Since both x² + x₁² and x₁² are positive, we can use the fact that
  -- a ≥ b > 0 implies b⁻¹ ≥ a⁻¹
  have h5 : x₁^2 ≤ x^2 + x₁^2 := h2

  -- Convert to norms
  have h6 : ‖x₁^2‖₊ = ‖x₁‖₊^2 := by
    rw [nnnorm_pow]

  have h7 : ‖x^2 + x₁^2‖₊ = x^2 + x₁^2 := by
    rw [Real.nnnorm_of_nonneg (le_of_lt h4)]
    norm_cast

  rw [← NNReal.coe_le_coe]
  push_cast
  simp [*]
  simp_all
  rw [abs_of_nonneg]
  · have U := inv_le_inv₀ h4 h3
    rw [U]
    simp [*]

  · positivity

theorem norm_reciprocal_inequality (x : ℝ) (x₁ : ℝ) (hx₁ : x₁ ≤ -1) :
  ‖x^2 + x₁^2‖₊⁻¹ ≤ (‖x₁‖₊^2)⁻¹ := by
  -- First, establish that x₁² ≥ 1 since x₁ ≤ -1
  have h1 : x₁^2 ≥ 1 := by
    have h_abs : |x₁| ≥ 1 := by
      rw [abs_of_nonpos (le_of_lt (lt_of_le_of_lt hx₁ (by norm_num : (-1 : ℝ) < 0)))]
      linarith
    simp only [ge_iff_le, one_le_sq_iff_one_le_abs, h_abs]

  -- Show that x² + x₁² ≥ x₁²
  have h2 : x^2 + x₁^2 ≥ x₁^2 := by
    linarith [sq_nonneg x]

  -- Show that x₁² > 0
  have h3 : x₁^2 > 0 := by
    apply sq_pos_of_ne_zero
    linarith

  have h33 : 2 * x₁^2 > 0 := by
    simp [*]

  -- Show that x² + x₁² > 0
  have h4 : x^2 + x₁^2 > 0 := by
    linarith [sq_nonneg x, h3]

  -- Since both x² + x₁² and x₁² are positive, we can use the fact that
  -- a ≥ b > 0 implies b⁻¹ ≥ a⁻¹
  have h5 : x₁^2 ≤ x^2 + x₁^2 := h2

  -- Convert to norms
  have h6 : ‖x₁^2‖₊ = ‖x₁‖₊^2 := by
    rw [nnnorm_pow]

  have h7 : ‖x^2 + x₁^2‖₊ = x^2 + x₁^2 := by
    rw [Real.nnnorm_of_nonneg (le_of_lt h4)]
    norm_cast

  rw [← NNReal.coe_le_coe]
  push_cast
  simp [*]
  simp_all
  rw [abs_of_nonneg]
  · have U := inv_le_inv₀ h4 h3
    rw [U]
    simp [*]

  · positivity

theorem poisson_kernel_integrable (x : ℝ) (hx : x ≠ 0) :
  MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
  -- First, simplify the complex norm
  have h1 : ∀ t : ℝ, ‖x + t * I‖^2 = x^2 + t^2 := by
    intro t
    rw [Complex.norm_add_mul_I, Real.sq_sqrt]
    positivity
  -- Rewrite the integrand using this simplification
  have h2 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) = (fun (t : ℝ) ↦ (x^2 + t^2)⁻¹) := by
    ext t
    rw [h1]
  rw [h2]
  -- Show that x^2 + t^2 > 0 for all t when x ≠ 0
  have h3 : ∀ t : ℝ, x^2 + t^2 > 0 := by
    intro t
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_ne_zero hx
    · exact sq_nonneg t
  -- The function is continuous everywhere
  have h4 : Continuous (fun t : ℝ ↦ (x^2 + t^2)⁻¹) := by
    apply Continuous.inv₀
    · exact continuous_const.add (continuous_pow 2)
    · intro t
      exact ne_of_gt (h3 t)
  -- Split the integral into bounded and unbounded parts
  -- The function is integrable on any bounded interval by continuity
  have integrable_on_bounded : ∀ R > 0, MeasureTheory.IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Icc (-R) R) := by
    intro R hR
    refine ContinuousOn.integrableOn_Icc ?_
    · exact Continuous.continuousOn h4
  -- For integrability at infinity, we use that (x^2 + t^2)⁻¹ ~ t⁻² as |t| → ∞
  -- Since ∫ t⁻² dt converges at infinity, our function is integrable
  -- Key estimate: for |t| ≥ 2|x|, we have x^2 + t^2 ≥ t^2/2
  have decay_bound : ∀ t : ℝ, 0 < |t| → (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro t
    intro hyp_t
    rw [←inv_le_inv₀]
    simp_all only [ne_eq, gt_iff_lt, abs_pos, inv_inv, le_add_iff_nonneg_left]
    · positivity
    · simp_all only [ne_eq, gt_iff_lt, abs_pos, inv_pos]
      positivity
    · positivity

  have decay_bound_1 : ∀ x_1 ≤ -1, ‖x ^ 2 + x_1 ^ 2‖₊⁻¹ ≤ (‖x_1‖₊ ^ 2)⁻¹ := by
    exact norm_reciprocal_inequality x

  have decay_bound_2 : ∀ (x_1 : ℝ), 1 ≤ x_1 → ‖x ^ 2 + x_1 ^ 2‖₊⁻¹ ≤ (‖x_1‖₊ ^ 2)⁻¹ := by
    exact norm_reciprocal_inequality_1 x

  -- Show integrability on (-∞, -1]
  have f_int_1 : IntegrableOn (fun (t : ℝ) ↦ (t^2)⁻¹) (Set.Iic (-1)) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff,
      Nat.one_lt_ofNat]
    have D2 : 0 < (1 : ℝ) := by simp only [zero_lt_one]
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, involutiveNeg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat,
            zero_lt_one, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton,
            EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat, zero_lt_one,
      rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow, Int.reduceNegSucc, Int.cast_neg, Int.cast_one]
    exact D4

  -- Show integrability on [1, ∞)
  have f_int_2 : IntegrableOn (fun (t : ℝ) ↦ (t^2)⁻¹) (Set.Ici 1) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff,
      Nat.one_lt_ofNat]
    have D2 : 0 < (1 : ℝ) := by simp only [zero_lt_one]
    have D3 := integrableOn_Ioi_rpow_of_lt D1 D2
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg] at D3
    have D4 :=
      (integrableOn_Ici_iff_integrableOn_Ioi'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat,
            zero_lt_one, measure_singleton, EReal.coe_ennreal_zero, EReal.coe_ennreal_top,
            EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, gt_iff_lt, abs_pos, neg_lt_neg_iff, Nat.one_lt_ofNat, zero_lt_one]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4

  have int_neg : IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Iic (-1)) volume := by
    have h_le : ∀ t ∈ Set.Iic (-1), (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
      intro t ht
      simp only [Set.mem_Iic] at ht
      -- Fix: Use the fact that t ≤ -1 implies t < 0
      have t_neg : t < 0 := lt_of_le_of_lt ht (by norm_num : (-1 : ℝ) < 0)
      exact decay_bound t (abs_pos.mpr (ne_of_lt t_neg))
    have h_meas : AEStronglyMeasurable (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Set.Iic (-1))) := by
      exact Continuous.aestronglyMeasurable h4

    unfold IntegrableOn
    unfold Integrable
    constructor
    · exact h_meas
    · have Z : HasFiniteIntegral (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Iic (-1))) := by
        refine MeasureTheory.HasFiniteIntegral.mono'_enorm f_int_1.2 ?_
        · unfold Filter.Eventually
          simp only [measurableSet_Iic, ae_restrict_eq, nnnorm_inv, nnnorm_pow, enorm_le_coe]
          refine mem_inf_of_right ?_
          · refine mem_principal.mpr ?_
            · rw [Set.subset_def]
              simp only [mem_Iic, mem_setOf_eq]
              exact decay_bound_1

      exact Z

--    have U := IntegrableOn.mono_fun f_int_1 h_meas h_le
--    _
  have int_pos : IntegrableOn (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (Set.Ici 1) volume := by
    have h_le : ∀ t ∈ Set.Ici 1, (x^2 + t^2)⁻¹ ≤ (t^2)⁻¹ := by
      intro t ht
      simp only [Set.mem_Ici] at ht
      -- Fix: Use the fact that t ≥ 1 implies t > 0
      have t_pos : t > 0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht
      exact decay_bound t (abs_pos.mpr (ne_of_gt t_pos))
    have h_meas : AEStronglyMeasurable (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Set.Ici 1)) := by
      exact Continuous.aestronglyMeasurable h4

    unfold IntegrableOn
    unfold Integrable
    constructor
    · exact h_meas
    · have Z : HasFiniteIntegral (fun t : ℝ ↦ (x^2 + t^2)⁻¹) (volume.restrict (Ici (1))) := by
        refine MeasureTheory.HasFiniteIntegral.mono'_enorm f_int_2.2 ?_
        · unfold Filter.Eventually
          simp only [measurableSet_Ici, ae_restrict_eq, nnnorm_inv, nnnorm_pow, enorm_le_coe]
          refine mem_inf_of_right ?_
          · refine mem_principal.mpr ?_
            · rw [Set.subset_def]
              simp only [mem_Ici, mem_setOf_eq]
              exact decay_bound_2
--              simp [*]
--              exact decay_bound_2

      exact Z

  -- Combine all pieces
  have split : Set.univ = Set.Iic (-1) ∪ Set.Icc (-1) 1 ∪ Set.Ici 1 := by
    ext t
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici, true_iff]
    by_cases h : t ≤ -1
    · left; left; exact h
    · by_cases h' : t ≥ 1
      · right; exact h'
      · left; right; constructor <;> linarith

  have Z :=
    MeasureTheory.IntegrableOn.union
      (MeasureTheory.IntegrableOn.union
          (int_neg)
          (integrable_on_bounded 1 zero_lt_one))
      (int_pos)

  simp_all only [ne_eq, gt_iff_lt, abs_pos, Int.reduceNeg, neg_le_self_iff, zero_le_one, Iic_union_Icc_eq_Iic,
  Iic_union_Ici, integrableOn_univ]

theorem ae_volume_of_contains_compl_singleton_zero --{α : Type*} --[MeasurableSpace α] --[MeasurableSpace.CountablyGenerated α]
  (s : Set ℝ)
  (h : (univ : Set ℝ) \ {0} ⊆ s) :
  s ∈ (MeasureTheory.ae volume) := by
  -- The key insight is that {0} has measure zero in ℝ
  have h_zero_null : volume ({0} : Set ℝ) = 0 := by
    exact volume_singleton
    -- A singleton set has measure zero in Euclidean space
    -- exact measure_singleton

  -- Since s contains univ \ {0} = ℝ \ {0}, its complement is contained in {0}
  have h_compl_subset : sᶜ ⊆ {0} := by
    intro x hx
    -- If x ∉ s, then x ∉ ℝ \ {0} (since ℝ \ {0} ⊆ s)
    -- This means x = 0
    by_contra h_not_zero
    have : x ∈ univ \ {0} := ⟨trivial, h_not_zero⟩
    exact hx (h this)

  -- Therefore, volume(sᶜ) ≤ volume({0}) = 0
  have h_compl_measure : volume sᶜ ≤ volume ({0} : Set ℝ) :=
    measure_mono h_compl_subset

  -- So volume(sᶜ) = 0
  have h_compl_zero : volume sᶜ = 0 := by
    rw [h_zero_null] at h_compl_measure
    exact le_antisymm h_compl_measure (zero_le _)

  -- A set is in ae.sets iff its complement has measure zero
  rwa [mem_ae_iff]

theorem integral_evaluation (x : ℝ) (T : ℝ)
  : (3 < T) → ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by

  intro T_large

  have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
    intro x
    intro t
    rw [Complex.norm_add_mul_I x t]
    ring_nf
    rw [Real.sq_sqrt _]
    simp only [le_add_iff_nonneg_right]; positivity
    positivity

  have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro x
    intro t
    intro hyp
    have U0 : 0 < t^2 := by positivity
    have U1 : 0 < ‖x + t * I‖^2 := by
      rw [Complex.norm_add_mul_I x t]
      rw [Real.sq_sqrt _]
      positivity
      positivity
    rw [inv_le_inv₀ U1 U0]
    exact (T00 x t)

  have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    refine mem_inf_of_left ?_
    · refine Filter.mem_sets.mp ?_
      · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
          rw [Set.setOf_subset_setOf]
          intro t
          intro hyp_t
          exact T0 x t hyp_t
        have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
          apply Set.ext
          intro x
          simp_all only [ne_eq, setOf_subset_setOf, not_false_eq_true, implies_true, mem_setOf_eq, mem_diff, mem_univ,
  mem_singleton_iff, true_and]

        rw [U1] at U
        have Z := ae_volume_of_contains_compl_singleton_zero
          ({x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹} : Set ℝ) U
        exact Z

  have T2 : 0 ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, Pi.zero_apply, inv_nonneg, norm_nonneg, pow_nonneg,
  setOf_true, univ_mem]

  have T4 : deriv (fun (t : ℝ) ↦ t⁻¹) = (fun t ↦ (- (t^2)⁻¹)) := by
    exact deriv_inv'

  have hcont : ContinuousWithinAt (fun t ↦ t⁻¹) (Set.Iic (-T)) (-T) := by
    refine ContinuousWithinAt.inv₀ ?_ ?_
    · exact ContinuousAt.continuousWithinAt fun ⦃U⦄ a ↦ a
    · by_contra h
      simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', neg_eq_zero]
      --norm_cast
      norm_num

      have : (0 : ℝ) < 3 := by norm_num
      have D := calc
        0 < 3 := this
        _ < 0 := T_large

      have Dnot :=  lt_irrefl 0
      norm_cast at D

  have hderiv : ∀ x ∈ Set.Iio (-T), HasDerivAt (fun t ↦ t⁻¹) ((fun t ↦ - (t^2)⁻¹) x) x := by
   --   ∀ x ∈ Set.Iio (-T), HasDerivAt (fun t ↦ t⁻¹) ((fun t ↦ - (t^2)⁻¹) x) x := by
    intro x hx
  -- x ∈ Set.Iio (-T) means x < -T, so x ≠ 0
    have hx_ne_zero : x ≠ 0 := by
      intro h
      rw [h] at hx
      simp [Set.Iio] at hx
      linarith
  -- Use the standard derivative of inverse function
    convert hasDerivAt_inv hx_ne_zero
  -- Simplify: -(x^2)⁻¹ = -x⁻² = -(x^2)⁻¹
    --simp [pow_two]

  have f'int : IntegrableOn (fun t ↦ - (t^2)⁻¹) (Set.Iic (-T)) volume := by
    have D1 : (-2) < (-1 : ℝ) := by simp only [neg_lt_neg_iff, Nat.one_lt_ofNat]
    have D2 : 0 < T := by positivity
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
    --simp_all
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp [*] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, neg_lt_neg_iff,
  Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton, EReal.coe_ennreal_zero,
  EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, neg_lt_neg_iff,
  Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
--    unfold Integrable
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]

    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow]
    have D6 := MeasureTheory.integrable_neg_iff.mpr D4
    have eq_fun : (-fun x ↦ (x^2)⁻¹) = (fun (x : ℝ) ↦ - (x^2)⁻¹) := by
      funext x
      simp only [Pi.neg_apply]
    rw [eq_fun] at D6
    exact D6


  have hf : Filter.Tendsto (fun (t : ℝ) ↦ t⁻¹) Filter.atBot (nhds 0) := by exact
    tendsto_inv_atBot_zero

  have T5 : ∫ (t : ℝ) in Iic (-T), - (t^2)⁻¹ = (-T)⁻¹ - 0 := by
    exact MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto hcont hderiv f'int hf

  have T6 : ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹ = T⁻¹ := by
    simp only [inv_neg, sub_zero] at T5
    have D6 : - ∫ (t : ℝ) in Iic (-T), - (t^2)⁻¹ =  ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹ := by
      simp only [integral_neg fun a ↦ (a ^ 2)⁻¹, neg_neg]

    rw [←D6]
    rw [T5]
    simp only [neg_neg]

  have T3 : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Iic (-T))) := by
    --simp_all
    have D1 : (-2) < (-1 : ℝ) := by simp only [neg_lt_neg_iff, Nat.one_lt_ofNat]
    have D2 : 0 < T := by positivity
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
    --simp_all
    have D3 := MeasureTheory.IntegrableOn.comp_neg D
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, involutiveNeg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          · simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, inv_neg, sub_zero,
  neg_lt_neg_iff, Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, measure_singleton, EReal.coe_ennreal_zero,
  EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', mem_Iio, inv_neg, sub_zero,
  neg_lt_neg_iff, Nat.one_lt_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg]
--    unfold Integrable
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow]

  have Z :=
    by
      calc
        ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹  := by
          exact MeasureTheory.integral_mono_of_nonneg T2 T3 T1

        _ = T⁻¹ := by exact T6

  exact Z


theorem integral_evaluation' (x : ℝ) (T : ℝ)
  : (3 < T) → ∫ (t : ℝ) in Ici (T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
  intro T_large

  have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
    intro x
    intro t
    rw [Complex.norm_add_mul_I x t]
    ring_nf
    rw [Real.sq_sqrt _]
    simp only [le_add_iff_nonneg_right]; positivity
    positivity

  have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro x
    intro t
    intro hyp
    have U0 : 0 < t^2 := by positivity
    have U1 : 0 < ‖x + t * I‖^2 := by
      rw [Complex.norm_add_mul_I x t]
      rw [Real.sq_sqrt _]
      positivity
      positivity
    rw [inv_le_inv₀ U1 U0]
    exact (T00 x t)

  have T2 : 0 ≤ᶠ[ae (volume.restrict (Ioi T))] (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, Pi.zero_apply, inv_nonneg, norm_nonneg, pow_nonneg,
  setOf_true, univ_mem]

  have T3 : Integrable (fun (t : ℝ) ↦ - (t^2)⁻¹) (volume.restrict (Ioi T)) := by
    have D1 : (-2) < (-1 : ℝ) := by simp only [neg_lt_neg_iff, Nat.one_lt_ofNat]
    have D2 : 0 < T := by positivity
    have D := integrableOn_Ioi_rpow_of_lt D1 D2
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg] at D
    exact MeasureTheory.Integrable.neg' D
--    exact D
--    simp [*] at D
--    have hb : volume {T} ≠ ⊤ := by
--      rw [Real.volume_singleton]
--      simp
--    exact ((integrableOn_Ici_iff_integrableOn_Ioi' hb).mpr D)


  have T3' : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Ioi T)) := by
    have D := MeasureTheory.Integrable.neg' T3
    simp_all only [ne_eq, measurableSet_Ioi, ae_restrict_eq, neg_neg]

  have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Ioi T))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Ioi, ae_restrict_eq]
    refine mem_inf_of_left ?_
    · refine Filter.mem_sets.mp ?_
      · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
          rw [Set.setOf_subset_setOf]
          intro t
          intro hyp_t
          exact T0 x t hyp_t
        have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
          apply Set.ext
          intro x
          simp_all only [ne_eq, setOf_subset_setOf, not_false_eq_true, implies_true, mem_setOf_eq, mem_diff, mem_univ,
  mem_singleton_iff, true_and]

        rw [U1] at U
        have Z := ae_volume_of_contains_compl_singleton_zero
          ({x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹} : Set ℝ) U
        exact Z


  have hcont : ContinuousWithinAt (fun t ↦ t⁻¹) (Set.Ici T) T := by
    refine ContinuousWithinAt.inv₀ ?_ ?_
    · exact ContinuousAt.continuousWithinAt fun ⦃U⦄ a ↦ a
    · by_contra h
      simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, deriv_inv', neg_eq_zero]
      --norm_cast
      norm_num

      have : (0 : ℝ) < 3 := by norm_num
      have D := calc
        0 < 3 := this
        _ < 0 := T_large

      have Dnot :=  lt_irrefl 0
      norm_cast at D

  have hderiv : ∀ x ∈ Set.Ioi T, HasDerivAt (fun t ↦ t⁻¹) ((fun t ↦ - (t^2)⁻¹) x) x := by
   --   ∀ x ∈ Set.Iio (-T), HasDerivAt (fun t ↦ t⁻¹) ((fun t ↦ - (t^2)⁻¹) x) x := by
    intro x hx
  -- x ∈ Set.Iio (-T) means x < -T, so x ≠ 0
    have hx_ne_zero : x ≠ 0 := by
      intro h
      rw [h] at hx
      simp [Set.Iio] at hx
      linarith
  -- Use the standard derivative of inverse function
    convert hasDerivAt_inv hx_ne_zero
  -- Simplify: -(x^2)⁻¹ = -x⁻² = -(x^2)⁻¹
    --simp [pow_two]

  have hf : Filter.Tendsto (fun (t : ℝ) ↦ t⁻¹) Filter.atTop (nhds 0) := by exact
    tendsto_inv_atTop_zero

  have T5 : ∫ (t : ℝ) in Ioi T, (t^2)⁻¹ = (T)⁻¹ - 0 := by
    have U := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv T3 hf
    simp [*] at U
    rw [MeasureTheory.integral_neg] at U
    simp_all only [ne_eq, measurableSet_Ici, ae_restrict_eq, mem_Ioi, neg_inj, sub_zero]

  have T6 : ∫ (t : ℝ) in Ioi T, (t^2)⁻¹ = T⁻¹ := by
    simp only [inv_neg, sub_zero] at T5
    have D6 : - ∫ (t : ℝ) in Ioi T, - (t^2)⁻¹ =  ∫ (t : ℝ) in Ioi T, (t^2)⁻¹ := by
      simp only [integral_neg fun a ↦ (a ^ 2)⁻¹, neg_neg]

    rw [←D6]
    rw [←T5]
    exact D6

  have Z :=
    by
      calc
        ∫ (t : ℝ) in Ioi T, (‖x + t * I‖ ^ 2)⁻¹ ≤ ∫ (t : ℝ) in Ioi T, (t^2)⁻¹  := by
          exact MeasureTheory.integral_mono_of_nonneg T2 T3' T1

        _ = T⁻¹ := by exact T6

  rw [←MeasureTheory.integral_Ici_eq_integral_Ioi] at Z

  exact Z




/-%%
\begin{proof}\leanok
\uses{MellinOfSmooth1c}
Unfold the definitions and apply Lemma \ref{MellinOfSmooth1c}.
\end{proof}
%%-/

/-%%
It remains to estimate all of the integrals.
%%-/

/-%%
This auxiliary lemma is useful for what follows.
\begin{lemma}[IBound_aux1]\label{IBound_aux1}\lean{IBound_aux1}\leanok
Given a natural number $k$ and a real number $X_0 > 0$, there exists $C \geq 1$ so that for all $X \geq X_0$,
$$
\log^k X \le C \cdot X.
$$
\end{lemma}
%%-/
lemma IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) (k : ℕ) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
  -- When X is large, the ratio goes to 0.
  have ⟨M, hM⟩ := Filter.eventually_atTop.mp (isLittleO_log_rpow_rpow_atTop k zero_lt_one).eventuallyLE
  -- When X is small, use the extreme value theorem.
  let f := fun X ↦ Real.log X ^ k / X
  let I := Icc X₀ M
  have : 0 ∉ I := notMem_Icc_of_lt X₀pos
  have f_cont : ContinuousOn f (Icc X₀ M) :=
    ((continuousOn_log.pow k).mono (subset_compl_singleton_iff.mpr this)).div
    continuous_id.continuousOn (fun x hx ↦ ne_of_mem_of_not_mem hx this)
  have ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn f_cont
  use max C₁ 1, le_max_right C₁ 1
  intro X hX
  have Xpos : X > 0 := lt_of_lt_of_le X₀pos hX
  by_cases hXM : X ≤ M
  · rw[← div_le_iff₀ Xpos]
    calc
      f X ≤ ‖f X‖ := le_norm_self _
      _ ≤ C₁ := hC₁ X ⟨hX, hXM⟩
      _ ≤ max C₁ 1 := le_max_left C₁ 1
  · calc
      Real.log X ^ k ≤ ‖Real.log X ^ k‖ := le_norm_self _
      _ ≤ ‖X ^ 1‖ := by exact_mod_cast hM X (by linarith[hXM])
      _ = 1 * X := by
        rw[pow_one, one_mul]
        apply norm_of_nonneg
        exact Xpos.le
      _ ≤ max C₁ 1 * X := by
        rw[mul_le_mul_right Xpos]
        exact le_max_right C₁ 1

/-%%
\begin{proof}
\uses{isLittleO_log_rpow_rpow_atTop}\leanok
We use the fact that $\log^k X / X$ goes to $0$ as $X \to \infty$.
Then we use the extreme value theorem to find a constant $C$ that works for all $X \geq X_0$.
\end{proof}
%%-/

/-%%
\begin{lemma}[I1Bound]\label{I1Bound}\lean{I1Bound}\leanok
We have that
$$
\left|I_{1}(\nu, \epsilon, X, T)\
\right| \ll \frac{X}{\epsilon T}
.
$$
Same with $I_9$.
\end{lemma}
%%-/

theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by


  obtain ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  have G0 : ∃K > 0, ∀(t σ : ℝ), 1 < σ → σ < 2 → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    let ⟨K', ⟨K'_pos, K'_bounds_zeta⟩⟩ := triv_bound_zeta
    use (2 * (K' + 1))
    use (by positivity)
    intro t
    intro σ
    intro cond
    intro cond2

    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
  norm_neg, tsub_le_iff_right, inv_one, U1]

    have T : (K' + 1) * 1 ≤ (K' + 1) * (σ - 1)⁻¹ :=
      by
        exact (mul_le_mul_left T0).mpr T1
    have T2 : (K' + 1) ≤ (K' + 1) * (σ - 1)⁻¹ := by
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
  norm_neg, mul_one, le_mul_iff_one_le_right]

    have U := calc
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by
        rw [← norm_neg _, mul_comm, neg_div' _ _]
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds_zeta σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by linarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by
        ring_nf

    exact U

  obtain ⟨K, ⟨K_is_pos, K_bounds_zeta_at_any_t'⟩⟩ := G0

--  let (C_final : ℝ) := K * M
  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity

  use (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M))
  use C_final_pos

  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)


  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := by
    intro t
    unfold pts
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]

  have pts_re_ge_one : 1 < pts_re := by
    unfold pts_re
    simp only [lt_add_iff_pos_right, inv_pos]
    have U : 1 < X := by linarith
    exact Real.log_pos U

  have pts_re_le_one : pts_re < 2 := by
    unfold pts_re
    have Z0 : 3 ∈ {x : ℝ | 1 ≤ x} := by
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt, Complex.norm_div,
  mem_setOf_eq, Nat.one_le_ofNat]
    have Z1 : X ∈ {x : ℝ | 1 ≤ x} := by
      simp only [mem_setOf_eq]
      linarith
    have Z : Real.log 3 < Real.log X :=
      by
        refine log_lt_log ?_ X_large
        simp only [Nat.ofNat_pos]

    have Z01 : 1 < Real.log 3  :=
      by
        have Z001 : 1 = Real.log (rexp 1) := by exact Eq.symm (Real.log_exp 1)
        rw [Z001]
        have Z002 : (0 : ℝ) < rexp 1 := by positivity
        have Z003 : (0 : ℝ) < 3 := by positivity
        have Z004 : rexp 1 < 3 := by
          calc
            rexp 1 < (↑ 2.7182818286 : ℚ) := Real.exp_one_lt_d9
            _ < (↑ 3 : ℚ) := by linarith

        exact (Real.log_lt_log_iff Z002 Z003).mpr Z004

    have Zpos0 : 0 < Real.log 3 := by positivity
    have Zpos1 : 0 < Real.log X := by calc
      0 < Real.log 3 := Zpos0
      _ < Real.log X := Z

    have Z1 : (Real.log X)⁻¹ < (Real.log 3)⁻¹ :=
      by
        exact (inv_lt_inv₀ Zpos1 Zpos0).mpr Z

    have Z02 : (Real.log 3)⁻¹ < 1 := by
      have T01 := (inv_lt_inv₀ ?_ ?_).mpr Z01
      simp only [inv_one] at T01
      exact T01
      exact Zpos0
      simp only [zero_lt_one]

    have Z2 : 1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := by
      exact (Real.add_lt_add_iff_left 1).mpr Z1

    have Z3 : 1 + (Real.log 3)⁻¹ < 2 := by
      calc
        1 + (Real.log 3)⁻¹ < 1 + 1 := by linarith
        _ = 2 := by ring_nf

    calc
      1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := Z2
      _ < 2 := Z3

  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    unfold pts_re
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, add_sub_cancel_left, inv_inv]

  have K_bounds_zeta_at_any_t : ∀(t : ℝ), ‖ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
    intro t
    rw [←inve]
    exact K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by
    unfold pts_re
    positivity

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := by
    intro t
    unfold pts_re
    exact Eq.ge (pts_re_triv t)

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 := by
    intro t
    unfold pts
    refine EReal.coe_le_coe_iff.mp ?_
    · simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, le_refl, implies_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, EReal.coe_le_coe_iff]
      exact le_of_lt pts_re_le_one

  have pts_re_ge_1 : pts_re > 1 := by
    unfold pts_re
    exact pts_re_ge_one

  have X_pos_triv : 0 < X := by positivity

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  /- Main pointwise bound -/

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by

    intro t

    let M_bounds_mellin_easy := fun (t : ℝ) ↦ M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t) (triv_pts_up_bound t) eps eps_pos eps_less_one

    let zeta_part := (fun (t : ℝ) ↦ -ζ' (pts t) / ζ (pts t))
    let mellin_part := (fun (t : ℝ) ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF eps x)) (pts t))
    let X_part := (fun (t : ℝ) ↦ (↑X : ℂ) ^ (pts t))

    let g := fun (t : ℝ) ↦ (zeta_part t) * (mellin_part t) * (X_part t)

    have X_part_eq : ∀(t : ℝ), ‖X_part t‖ = X^pts_re := by
      intro t
      have U := Complex.norm_cpow_eq_rpow_re_of_pos (X_pos_triv) (pts t)
      rw [pts_re_triv t] at U
      exact U

    have X_part_bound : ∀(t : ℝ), ‖X_part t‖ ≤ X^pts_re := by
      intro t
      rw [←X_part_eq]

    have mellin_bound : ∀(t : ℝ), ‖mellin_part t‖ ≤ M * (eps * ‖pts t‖ ^ 2)⁻¹ := by
      intro t
      exact M_bounds_mellin_easy t

    have X_part_and_mellin_bound : ∀(t : ℝ),‖mellin_part t * X_part t‖ ≤ M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
      intro t
      exact norm_mul_le_of_le (mellin_bound t) (X_part_bound t)

    have T2 : ∀(t : ℝ), ‖zeta_part t‖ = ‖ζ' (pts t) / ζ (pts t)‖ := by
      intro t
      unfold zeta_part
      simp only [Complex.norm_div, norm_neg]

    have zeta_bound : ∀(t : ℝ), ‖zeta_part t‖ ≤ K * Real.log X := by
      intro t
      unfold zeta_part
      rw [T2]
      exact K_bounds_zeta_at_any_t t

    have g_bound : ∀(t : ℝ), ‖zeta_part t * (mellin_part t * X_part t)‖ ≤ (K * Real.log X) * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      intro t
      exact norm_mul_le_of_le (zeta_bound t) (X_part_and_mellin_bound t)

    have T1 : f = g := by rfl

    have final_bound_pointwise : ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      rw [T1]
      unfold g
      rw [mul_assoc]
      exact g_bound t

    have trivialize : K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) = (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
            ring_nf

    rw [trivialize] at final_bound_pointwise
    exact final_bound_pointwise


  have σ₀_gt : 1 < pts_re := by exact pts_re_ge_1
  have σ₀_le_2 : pts_re ≤ 2 := by
    unfold pts_re
    -- LOL!
    exact
      Preorder.le_trans (1 + (Real.log X)⁻¹) (pts (SmoothingF (SmoothingF M))).re 2
        (triv_pts_lo_bound (SmoothingF (SmoothingF M))) (triv_pts_up_bound (SmoothingF (SmoothingF M)))

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large σ₀_gt σ₀_le_2 suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    unfold pts_re

    calc
      X ^ (1 + (Real.log X)⁻¹) = X * X ^ ((Real.log X)⁻¹) := by
        refine rpow_one_add' ?_ ?_
        · positivity
        · exact Ne.symm (ne_of_lt pts_re_pos)
      _ = X * rexp 1 := by
        refine (mul_right_inj' ?_).mpr ?_
        · exact Ne.symm (ne_of_lt X_pos_triv)
        · refine rpow_inv_log X_pos_triv ?_
          · by_contra h
            simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
              Complex.norm_div, Nat.not_ofNat_lt_one]
      _ = rexp 1 * X := by ring_nf


  have pts_re_neq_zero : pts_re ≠ 0 := by
    by_contra h
    rw [h] at pts_re_ge_1
    simp only [gt_iff_lt] at pts_re_ge_1
    norm_cast at pts_re_ge_1

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Iic (-T), f t‖ ≤ ∫ (t : ℝ) in Iic (-T), ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Iic (-T), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono ?_ ?_ (fun t ↦ G t)
            · refine Integrable.norm ?_
              · unfold f
                exact MeasureTheory.Integrable.restrict f_integrable
            · have equ : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹ := by
                   intro t; ring_nf
              have fun_equ : (fun (t : ℝ) ↦ ((K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re)) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹)) := by
                   funext t
                   exact equ t

              rw [fun_equ]
              have nonzero := ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              have simple_int : MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
                := by
                   unfold pts
                   exact poisson_kernel_integrable pts_re (pts_re_neq_zero)

              have U := MeasureTheory.Integrable.const_mul simple_int ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              refine MeasureTheory.Integrable.restrict ?_
              exact U
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * ∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹ := by
              have simpli : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹ :=
                by intro t; ring_nf
              have simpli_fun : (fun (t : ℝ) ↦ (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re ) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹)) :=
                by funext t; ring_nf
              rw [simpli_fun]
              exact MeasureTheory.integral_const_mul ((K * M) * Real.log X * X ^ pts_re * eps⁻¹) (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ := by
              have U := integral_evaluation (pts_re) T (T_large)
              unfold pts
              simp only [ge_iff_le]
              have U2 : 0 ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ := by
                simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
                  Complex.norm_div, le_refl, implies_true, inv_pos, mul_nonneg_iff_of_pos_right]
                refine Left.mul_nonneg ?_ ?_
                · refine Left.mul_nonneg ?_ ?_
                  · exact Left.mul_nonneg (by positivity) (by positivity)
                  · refine log_nonneg ?_
                    · linarith
                · refine Left.mul_nonneg ?_ ?_
                  · exact exp_nonneg 1
                  · exact le_of_lt X_pos_triv
              have U1 := IsOrderedRing.mul_le_mul_of_nonneg_left
                (∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹)
                (T⁻¹)
                ((K * M) * Real.log X * X ^ pts_re * eps⁻¹)
                U
                U2
              exact U1
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf


  unfold I₁
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 :=
    IsOrderedRing.mul_le_mul_of_nonneg_left _ _ _ Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4



theorem I9Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
/-
  intros SmoothingF suppSmoothingF ContDiffSmoothingF
  let ⟨C, ⟨C_pos, hC⟩⟩  := I1Bound suppSmoothingF ContDiffSmoothingF
  use C
  use C_pos
  intros ε ε_pos ε_lt_one X X_gt T T_gt σ₁ SmoothingFnonneg mass_one ContDiffSmoothingF
  have := hC ε ε_pos ε_lt_one X X_gt T_gt SmoothingFnonneg mass_one
  unfold I₉
  unfold I₁ at this
  have U := by
    rw [integral_comp_neg_Iic] at this
  _
-/


  obtain ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  have G0 : ∃K > 0, ∀(t σ : ℝ), 1 < σ → σ < 2 → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    let ⟨K', ⟨K'_pos, K'_bounds_zeta⟩⟩ := triv_bound_zeta
    use (2 * (K' + 1))
    use (by positivity)
    intro t
    intro σ
    intro cond
    intro cond2

    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
  norm_neg, tsub_le_iff_right, inv_one, U1]

    have T : (K' + 1) * 1 ≤ (K' + 1) * (σ - 1)⁻¹ :=
      by
        exact (mul_le_mul_left T0).mpr T1
    have T2 : (K' + 1) ≤ (K' + 1) * (σ - 1)⁻¹ := by
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
  norm_neg, mul_one, le_mul_iff_one_le_right]

    have U := calc
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by
        rw [← norm_neg _, mul_comm, neg_div' _ _]
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds_zeta σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by linarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by
        ring_nf

    exact U

  obtain ⟨K, ⟨K_is_pos, K_bounds_zeta_at_any_t'⟩⟩ := G0

--  let (C_final : ℝ) := K * M
  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity

  use (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M))
  use C_final_pos

  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)


  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := by
    intro t
    unfold pts
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]

  have pts_re_ge_one : 1 < pts_re := by
    unfold pts_re
    simp only [lt_add_iff_pos_right, inv_pos]
    have U : 1 < X := by linarith
    exact Real.log_pos U

  have pts_re_le_one : pts_re < 2 := by
    unfold pts_re
    have Z0 : 3 ∈ {x : ℝ | 1 ≤ x} := by
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt, Complex.norm_div,
  mem_setOf_eq, Nat.one_le_ofNat]
    have Z1 : X ∈ {x : ℝ | 1 ≤ x} := by
      simp only [mem_setOf_eq]
      linarith
    have Z : Real.log 3 < Real.log X :=
      by
        refine log_lt_log ?_ X_large
        simp only [Nat.ofNat_pos]

    have Z01 : 1 < Real.log 3  :=
      by
        have Z001 : 1 = Real.log (rexp 1) := by exact Eq.symm (Real.log_exp 1)
        rw [Z001]
        have Z002 : (0 : ℝ) < rexp 1 := by positivity
        have Z003 : (0 : ℝ) < 3 := by positivity
        have Z004 : rexp 1 < 3 := by
          calc
            rexp 1 < (↑ 2.7182818286 : ℚ) := Real.exp_one_lt_d9
            _ < (↑ 3 : ℚ) := by linarith

        exact (Real.log_lt_log_iff Z002 Z003).mpr Z004

    have Zpos0 : 0 < Real.log 3 := by positivity
    have Zpos1 : 0 < Real.log X := by calc
      0 < Real.log 3 := Zpos0
      _ < Real.log X := Z

    have Z1 : (Real.log X)⁻¹ < (Real.log 3)⁻¹ :=
      by
        exact (inv_lt_inv₀ Zpos1 Zpos0).mpr Z

    have Z02 : (Real.log 3)⁻¹ < 1 := by
      have T01 := (inv_lt_inv₀ ?_ ?_).mpr Z01
      simp only [inv_one] at T01
      exact T01
      exact Zpos0
      simp only [zero_lt_one]

    have Z2 : 1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := by
      exact (Real.add_lt_add_iff_left 1).mpr Z1

    have Z3 : 1 + (Real.log 3)⁻¹ < 2 := by
      calc
        1 + (Real.log 3)⁻¹ < 1 + 1 := by linarith
        _ = 2 := by ring_nf

    calc
      1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := Z2
      _ < 2 := Z3

  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    unfold pts_re
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, add_sub_cancel_left, inv_inv]

  have K_bounds_zeta_at_any_t : ∀(t : ℝ), ‖ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
    intro t
    rw [←inve]
    exact K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by
    unfold pts_re
    positivity

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := by
    intro t
    unfold pts_re
    exact Eq.ge (pts_re_triv t)

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 := by
    intro t
    unfold pts
    refine EReal.coe_le_coe_iff.mp ?_
    · simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, le_refl, implies_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, EReal.coe_le_coe_iff]
      exact le_of_lt pts_re_le_one

  have pts_re_ge_1 : pts_re > 1 := by
    unfold pts_re
    exact pts_re_ge_one

  have X_pos_triv : 0 < X := by positivity

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  /- Main pointwise bound -/

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by

    intro t

    let M_bounds_mellin_easy := fun (t : ℝ) ↦ M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t) (triv_pts_up_bound t) eps eps_pos eps_less_one

    let zeta_part := (fun (t : ℝ) ↦ -ζ' (pts t) / ζ (pts t))
    let mellin_part := (fun (t : ℝ) ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF eps x)) (pts t))
    let X_part := (fun (t : ℝ) ↦ (↑X : ℂ) ^ (pts t))

    let g := fun (t : ℝ) ↦ (zeta_part t) * (mellin_part t) * (X_part t)

    have X_part_eq : ∀(t : ℝ), ‖X_part t‖ = X^pts_re := by
      intro t
      have U := Complex.norm_cpow_eq_rpow_re_of_pos (X_pos_triv) (pts t)
      rw [pts_re_triv t] at U
      exact U

    have X_part_bound : ∀(t : ℝ), ‖X_part t‖ ≤ X^pts_re := by
      intro t
      rw [←X_part_eq]

    have mellin_bound : ∀(t : ℝ), ‖mellin_part t‖ ≤ M * (eps * ‖pts t‖ ^ 2)⁻¹ := by
      intro t
      exact M_bounds_mellin_easy t

    have X_part_and_mellin_bound : ∀(t : ℝ),‖mellin_part t * X_part t‖ ≤ M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
      intro t
      exact norm_mul_le_of_le (mellin_bound t) (X_part_bound t)

    have T2 : ∀(t : ℝ), ‖zeta_part t‖ = ‖ζ' (pts t) / ζ (pts t)‖ := by
      intro t
      unfold zeta_part
      simp only [Complex.norm_div, norm_neg]

    have zeta_bound: ∀(t : ℝ), ‖zeta_part t‖ ≤ K * Real.log X := by
      intro t
      unfold zeta_part
      rw [T2]
      exact K_bounds_zeta_at_any_t t

    have g_bound : ∀(t : ℝ), ‖zeta_part t * (mellin_part t * X_part t)‖ ≤ (K * Real.log X) * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      intro t
      exact norm_mul_le_of_le (zeta_bound t) (X_part_and_mellin_bound t)

    have T1 : f = g := by rfl

    have final_bound_pointwise : ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      rw [T1]
      unfold g
      rw [mul_assoc]
      exact g_bound t

    have trivialize : K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) = (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
            ring_nf

    rw [trivialize] at final_bound_pointwise
    exact final_bound_pointwise


  have σ₀_gt : 1 < pts_re := by exact pts_re_ge_1
  have σ₀_le_2 : pts_re ≤ 2 := by
    unfold pts_re
    -- LOL!
    exact
      Preorder.le_trans (1 + (Real.log X)⁻¹) (pts (SmoothingF (SmoothingF M))).re 2
        (triv_pts_lo_bound (SmoothingF (SmoothingF M))) (triv_pts_up_bound (SmoothingF (SmoothingF M)))

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large σ₀_gt σ₀_le_2 suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    unfold pts_re

    calc
      X ^ (1 + (Real.log X)⁻¹) = X * X ^ ((Real.log X)⁻¹) := by
        refine rpow_one_add' ?_ ?_
        · positivity
        · exact Ne.symm (ne_of_lt pts_re_pos)
      _ = X * rexp 1 := by
        refine (mul_right_inj' ?_).mpr ?_
        · exact Ne.symm (ne_of_lt X_pos_triv)
        · refine rpow_inv_log X_pos_triv ?_
          · by_contra h
            simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
              Complex.norm_div, Nat.not_ofNat_lt_one]
      _ = rexp 1 * X := by ring_nf


  have pts_re_neq_zero : pts_re ≠ 0 := by
    by_contra h
    rw [h] at pts_re_ge_1
    simp only [gt_iff_lt] at pts_re_ge_1
    norm_cast at pts_re_ge_1

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Ici T, f t‖ ≤ ∫ (t : ℝ) in Ici T, ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Ici T, (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono ?_ ?_ (fun t ↦ G t)
            · refine Integrable.norm ?_
              · unfold f
                exact MeasureTheory.Integrable.restrict f_integrable
            · have equ : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹ := by
                   intro t; ring_nf
              have fun_equ : (fun (t : ℝ) ↦ ((K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re)) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹)) := by
                   funext t
                   exact equ t

              rw [fun_equ]
              have nonzero := ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              have simple_int : MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
                := by
                   unfold pts
                   exact poisson_kernel_integrable pts_re (pts_re_neq_zero)

              have U := MeasureTheory.Integrable.const_mul simple_int ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              refine MeasureTheory.Integrable.restrict ?_
              exact U
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * ∫ (t : ℝ) in Ici T, (‖pts t‖ ^ 2)⁻¹ := by
              have simpli : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹ :=
                by intro t; ring_nf
              have simpli_fun : (fun (t : ℝ) ↦ (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re ) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹)) :=
                by funext t; ring_nf
              rw [simpli_fun]
              exact MeasureTheory.integral_const_mul ((K * M) * Real.log X * X ^ pts_re * eps⁻¹) (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ := by
              have U := integral_evaluation' (pts_re) T (T_large)
              unfold pts
              simp only [ge_iff_le]
              have U2 : 0 ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ := by
                simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
                  Complex.norm_div, le_refl, implies_true, inv_pos, mul_nonneg_iff_of_pos_right]
                refine Left.mul_nonneg ?_ ?_
                · refine Left.mul_nonneg ?_ ?_
                  · exact Left.mul_nonneg (by positivity) (by positivity)
                  · refine log_nonneg ?_
                    · linarith
                · refine Left.mul_nonneg ?_ ?_
                  · exact exp_nonneg 1
                  · exact le_of_lt X_pos_triv
              have U1 := IsOrderedRing.mul_le_mul_of_nonneg_left
                (∫ (t : ℝ) in Ici T, (‖pts t‖ ^ 2)⁻¹)
                (T⁻¹)
                ((K * M) * Real.log X * X ^ pts_re * eps⁻¹)
                U
                U2
              exact U1
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf


  unfold I₉
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 :=
    IsOrderedRing.mul_le_mul_of_nonneg_left _ _ _ Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4



/-%%
\begin{proof}\uses{MellinOfSmooth1b, dlog_riemannZeta_bdd_on_vertical_lines', I1, I9,
  IBound_aux1}\leanok
  Unfold the definitions and apply the triangle inequality.
$$
\left|I_{1}(\nu, \epsilon, X, T)\right| =
\left|
\frac{1}{2\pi i} \int_{-\infty}^{-T}
\left(
\frac{-\zeta'}\zeta(\sigma_0 + t i)
\right)
 \mathcal M(\widetilde 1_\epsilon)(\sigma_0 + t i)
X^{\sigma_0 + t i}
\ i \ dt
\right|
$$
By Theorem \ref{dlog_riemannZeta_bdd_on_vertical_lines'} (once fixed!!),
$\zeta'/\zeta (\sigma_0 + t i)$ is bounded by $\zeta'/\zeta(\sigma_0)$, and
Theorem \ref{riemannZetaLogDerivResidue} gives $\ll 1/(\sigma_0-1)$ for the latter. This gives:
$$
\leq
\frac{1}{2\pi}
\left|
 \int_{-\infty}^{-T}
C \log X\cdot
 \frac{C'}{\epsilon|\sigma_0 + t i|^2}
X^{\sigma_0}
\ dt
\right|
,
$$
where we used Theorem \ref{MellinOfSmooth1b}.
Continuing the calculation, we have
$$
\leq
\log X \cdot
C'' \frac{X^{\sigma_0}}{\epsilon}
\int_{-\infty}^{-T}
\frac{1}{t^2}
\ dt
\ \leq \
C''' \frac{X\log X}{\epsilon T}
,
$$
where we used that $\sigma_0=1+1/\log X$, and $X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
\end{proof}
%%-/

lemma one_add_inv_log {X : ℝ} (X_ge : 3 ≤ X): (1 + (Real.log X)⁻¹) < 2 := by
  rw[← one_add_one_eq_two]
  refine (Real.add_lt_add_iff_left 1).mpr ?_
  refine inv_lt_one_of_one_lt₀ ?_
  refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> linarith[Real.exp_one_lt_d9]


/-%%
\begin{lemma}[I2Bound]\label{I2Bound}\lean{I2Bound}\leanok
We have that
$$
\left|I_{2}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon T}
.
$$
\end{lemma}
%%-/
lemma I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
--    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) 
    {A C₂ : ℝ} (has_bound: LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) 9)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]

  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
--  clear suppSmoothingF mass_one ContDiffSmoothingF
  have Xpos : 0 < X := lt_trans (by norm_num) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    dsimp[σ₁]
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_left
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      exact A_in.1.le
      apply pow_nonneg
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have σ₁pos : 0 < σ₁ := by
    rw[sub_pos]
    calc
      A / Real.log T ^ 9 ≤ 1 / 2 / Real.log T ^ 9 := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply pow_nonneg
        rw[log_nonneg_iff Tpos]
        exact le_trans (by norm_num) (le_of_lt T_gt)
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        apply one_le_pow₀
        apply le_of_lt
        refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> linarith[Real.exp_one_lt_d9]
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹), ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        convert this using 3
        apply uIoc_of_le
        exact interval_length_nonneg
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
        calc
          1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
          _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
  -- Now bound the integrand
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ 9 := has_bound σ (-T) (by simp; rw [abs_of_pos Tpos]; exact T_gt) (by unfold σ₁ at hσ; simp at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ 9 := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  -- Then estimate the remaining factors.
  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith[one_add_inv_log X_gt.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, σ₁]
          rw[← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
          exact hσ.2
          · refine (log_pos ?_).ne.symm
            linarith
          · apply log_pos
            linarith
          · linarith
          · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_left]
          exact this
          exact ε_pos
          positivity
          apply mul_pos ε_pos
          exact lt_of_lt_of_le (pow_pos Tpos 2) this
          positivity
        _ = C' * X / (ε * T) := by
          field_simp
          ring

/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBndUniform, I2, I8}\leanok
Unfold the definitions and apply the triangle inequality.
$$
\left|I_{2}(\nu, \epsilon, X, T, \sigma_1)\right| =
\left|\frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
\left(\frac{-\zeta'}\zeta(\sigma - T i) \right) \cdot
\mathcal M(\widetilde 1_\epsilon)(\sigma - T i) \cdot
X^{\sigma - T i}
 \ d\sigma
\right|
$$
$$\leq
\frac{1}{2\pi}
\int_{\sigma_1}^{\sigma_0}
C \cdot \log T ^ 9
\frac{C'}{\epsilon|\sigma - T i|^2}
X^{\sigma_0}
 \ d\sigma
 \leq
C'' \cdot \frac{X\log T^9}{\epsilon T^2}
,
$$
where we used Theorems \ref{MellinOfSmooth1b} and \ref{LogDerivZetaBndUniform}, and the fact that
$X^\sigma \le X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
Since $T>3$, we have $\log T^9 \leq C''' T$.
\end{proof}
%%-/

/-%%
\begin{lemma}[I8I2]\label{I8I2}\lean{I8I2}\leanok
Symmetry between $I_2$ and $I_8$:
$$
I_8(\nu, \epsilon, X, T) = -\overline{I_2(\nu, \epsilon, X, T)}
.
$$
\end{lemma}
%%-/
lemma I8I2 {SmoothingF : ℝ → ℝ}
    {X ε T σ₁ : ℝ} (T_gt : 3 < T) :
    I₈ SmoothingF ε X T σ₁ = -conj (I₂ SmoothingF ε X T σ₁) := by
  unfold I₂ I₈
  rw[map_mul, ← neg_mul]
  congr
  · simp[conj_ofNat]
  · rw[← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw[← smoothedChebyshevIntegrand_conj]
    simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    exact lt_trans (by norm_num) T_gt
/-%%
\begin{proof}\uses{I2, I8, SmoothedChebyshevIntegrand_conj}\leanok
  This is a direct consequence of the definitions of $I_2$ and $I_8$.
\end{proof}
%%-/


/-%%
\begin{lemma}[I8Bound]\label{I8Bound}\lean{I8Bound}\leanok
We have that
$$
\left|I_{8}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon T}
.
$$
\end{lemma}
%%-/
lemma I8Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) 
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
--    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by

  obtain ⟨C, hC, i2Bound⟩ := I2Bound suppSmoothingF ContDiffSmoothingF has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
  exact i2Bound
/-%%
\begin{proof}\uses{I8I2, I2Bound}\leanok
  We deduce this from the corresponding bound for $I_2$, using the symmetry between $I_2$ and $I_8$.
\end{proof}
%%-/


/-%%
\begin{lemma}[IntegralofLogx^n/x^2Bounded]\label{IntegralofLogx^n/x^2Bounded}\lean{log_pow_over_xsq_integral_bounded}\leanok
For every $n$ there is some absolute constant $C>0$ such that
$$
\int_3^T \frac{(\log x)^9}{x^2}dx < C
$$
\end{lemma}
%%-/

lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ T >3, ∫ x in Ioo 3 T, (Real.log x)^n / x^2 < C := by
  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]
  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3
  intro n
  induction n with
  | zero =>
    use 1
    constructor
    · norm_num
    · intro T hT
      have Tgt3 : (3 : ℝ) < T := hT
      simp only [pow_zero]
      have h1 :(0 ≤ (-2) ∨ (-2) ≠ (-1) ∧ 0 ∉ Set.uIcc 3 T) := by
        right
        constructor
        · linarith
        · refine notMem_uIcc_of_lt ?_ ?_
          · exact three_pos
          · linarith
      have integral := integral_zpow h1
      ring_nf at integral

      have swap_int_kind : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), 1 / x ^ 2 = ∫ (x : ℝ) in Ioo 3 T, 1 / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      rw [← swap_int_kind]
      have change_int_power : ∫ (x : ℝ) in (3 : ℝ)..T, (1 : ℝ) / x ^ (↑ 2)
                            = ∫ (x : ℝ) in (3 : ℝ).. T, x ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp
        rfl
      rw [change_int_power, integral]
      have : T ^ (-1 : ℤ) > 0 := by
        refine zpow_pos ?_ (-1)
        linarith
      linarith
  | succ d ih =>
    obtain ⟨Cd, Cdpos, IH⟩ := ih
    use ((Real.log 3)^(d+1) / 3) + (d+1) * Cd
    constructor
    · have logpowpos : (Real.log 3) ^ (d + 1) > 0 := by
        refine pow_pos ?_ (d + 1)
        linarith
      have :  0 < (Real.log 3) ^ (d + 1) / 3 := by
        exact div_pos logpowpos (by norm_num)
      have dbound : d + 1 ≥ 1 := by
        exact Nat.le_add_left 1 d
      have : Real.log 3 ^ (d + 1) / 3 + (↑d + 1) * Cd > 0 / 3 + 0 := by
        have term1_pos : 0 < Real.log 3 ^ (d + 1) / 3 := this
        have term2_pos : 0 < (↑d + 1) * Cd := by
          refine (mul_pos_iff_of_pos_right Cdpos).mpr ?_
          exact Nat.cast_add_one_pos d
        refine add_lt_add ?_ term2_pos
        refine div_lt_div₀ logpowpos ?_ ?_ ?_
        linarith
        linarith
        linarith
      ring_nf at this
      ring_nf
      exact this
    · intro T Tgt3
      let u := fun x : ℝ ↦ (Real.log x) ^ (d + 1)
      let v := fun x : ℝ ↦ -1 / x
      let u' := fun x : ℝ ↦ (d + 1 : ℝ) * (Real.log x)^d / x
      let v' := fun x : ℝ ↦ 1 / x^2


      have swap_int_type : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2
                          = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ (d + 1) / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw [← swap_int_type]

      have uIcc_is_Icc : Set.uIcc 3 T = Set.Icc 3 T := by
        exact uIcc_of_lt Tgt3

      have cont_u : ContinuousOn u (Set.uIcc 3 T) := by
        unfold u
        rw[uIcc_is_Icc]
        refine ContinuousOn.pow ?_ (d + 1)
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        refine continuousAt_log ?_
        linarith [hx.1]

      have cont_v : ContinuousOn v (Set.uIcc 3 T) := by
        unfold v
        rw[uIcc_is_Icc]
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        have cont1 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) x := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have cont2 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) (-x) := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have fun1 : (fun (x : ℝ) ↦ -1 / x) = (fun (x : ℝ) ↦ 1 / (-x)) := by
          ext x
          ring_nf
        rw [fun1]
        exact ContinuousAt.comp cont2 (HasDerivAt.neg (hasDerivAt_id x)).continuousAt

      have deriv_u : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt u (u' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        unfold u u'
        have xne0 : x ≠ 0 := by linarith [hx.1]
        have deriv1 := Real.deriv_log x
        have deriv2 := (Real.hasDerivAt_log xne0).pow (d + 1)
        have fun1 : (fun x ↦ (↑d + 1) * Real.log x ^ d / x) = (fun x ↦ (↑d + 1) * Real.log x ^ d * x⁻¹) := by
          exact rfl
        have fun2 : (↑d + 1) * Real.log x ^ d / x =  (↑d + 1) * Real.log x ^ d * x⁻¹:= by
          exact rfl
        rw [fun2]
        convert deriv2 using 1
        rw [Nat.add_sub_cancel]
        rw [Nat.cast_add, Nat.cast_one]

      have deriv_v : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt v (v' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        have xne0 : x ≠ 0 := by linarith [hx.1]
        unfold v v'
        have deriv1 := hasDerivAt_inv xne0
        have fun1 : (fun (x : ℝ) ↦ x⁻¹) = (fun (x : ℝ) ↦ 1 / x) := by
          ext x
          exact inv_eq_one_div x
        rw [fun1] at deriv1
        have fun2 : -(x ^ 2)⁻¹ = - 1 / x ^ 2 := by
          field_simp
        rw [fun2] at deriv1
        convert HasDerivAt.neg deriv1 using 1
        · ext x
          rw [neg_eq_neg_one_mul]
          field_simp
        · field_simp

      have cont_u' : ContinuousOn u' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold u'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · refine ContinuousOn.mul ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.pow ?_ d
            refine continuousOn_of_forall_continuousAt ?_
            intro x hx
            refine continuousAt_log ?_
            linarith [hx.1]
        · exact continuousOn_id' (Icc 3 T)
        · intro x hx
          linarith [hx.1]

      have cont_v' : ContinuousOn v' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold v'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · exact continuousOn_const
        · exact continuousOn_pow 2
        · intro x hx
          refine pow_ne_zero 2 ?_
          linarith [hx.1]

      have int_u': IntervalIntegrable u' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_u'

      have int_v': IntervalIntegrable v' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_v'

      have IBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt cont_u cont_v deriv_u deriv_v int_u' int_v'

      unfold u u' v v' at IBP

      have int1 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) * (1 / x ^ 2)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2 := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          field_simp

      rw[int1] at IBP
      rw[IBP]


      have int2 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = -(↑d + 1) * ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2 := by
        have : ∀ x, (↑d + 1) * Real.log x ^ d / x * (-1 / x)
         = -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          intro x
          field_simp
          ring
        have : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          exact intervalIntegral.integral_congr fun ⦃x⦄ a ↦ this x
        rw [this]
        rw [←intervalIntegral.integral_const_mul]
        ring_nf

      rw[int2]

      have int3 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2
                = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw[int3]

      have IHbound : ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := by
        exact IH T Tgt3

      ring_nf
      have bound2 : (Real.log T * Real.log T ^ d * T⁻¹) ≥ 0 := by
        have logTpos : Real.log T ≥ 0 := by
          refine log_nonneg ?_
          linarith
        apply mul_nonneg
        · apply mul_nonneg
          · exact logTpos
          · exact pow_nonneg logTpos d
        · field_simp
          apply one_div_nonneg.mpr
          linarith
      have bound3 : -(Real.log T * Real.log T ^ d * T⁻¹) ≤ 0 := by
        exact Right.neg_nonpos_iff.mpr bound2
      let S := Real.log T * Real.log T ^ d * T⁻¹
      have Spos : S ≥ 0 := by
        unfold S
        exact bound2

      have : (-(Real.log T * Real.log T ^ d * T⁻¹) + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 = (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        unfold S
        rfl
      rw [this]

      have GetRidOfS : (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2
                      ≤ ( Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        linarith [Spos]
      apply lt_of_le_of_lt GetRidOfS
      rw [add_assoc]

      have bound4 : ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := IHbound

      have bound5 : ↑d * ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 ≤ ↑d * Cd := by
        apply (mul_le_mul_of_nonneg_left bound4.le)
        exact Nat.cast_nonneg d

      have bound_sum : ↑d * (∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2)
                       + ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < ↑d * Cd + Cd := by
        linarith [bound4, bound5]
      rw[add_assoc]
      apply add_lt_add_left
      field_simp
      linarith [bound_sum]

/-%%
\begin{proof}\leanok
Induct on n and just integrate by parts.
\end{proof}
%%-/


/-%%
\begin{lemma}[I3Bound]\label{I3Bound}\lean{I3Bound}\leanok
We have that
$$
\left|I_{3}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon}\, X^{-\frac{A}{(\log T)^9}}
.
$$
Same with $I_7$.
\end{lemma}
%%-/

theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioc 0 (1/2)),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        --(SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
        --(mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1),
        let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
--  intro SmoothingF suppSmoothingF ContDiffSmoothingF
  choose A hA Cζ Cζpos hCζ using LogDerivZetaBnd
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded 9
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  use A
  use hA
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁ -- SmoothingFnonneg mass_one
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3

  have logXgt1 : Real.log X > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logTgt1 : Real.log T > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logX9gt1 : Real.log X ^ 9 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logXgt1
    linarith
    linarith

  have logT9gt1 : Real.log T ^ 9 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logTgt1
    linarith
    linarith

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      linarith[h2]
    have abs_tgt3 : 3 < |t| := by
      rw[this]
      linarith[h2]
    have abs_tltX : |t| < T := by
      rw[this]
      linarith[h1]
    exact ⟨abs_tgt3, abs_tltX⟩

  have logtgt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| > 1 := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine logt_gt_one ?_
    exact h1

  have logt9gt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 > 1 := by
    intro t ht
    refine one_lt_pow₀ (logtgt1_bounds t ht) ?_
    linarith

  have logtltlogT_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| < Real.log T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine log_lt_log ?_ ?_
    linarith
    linarith

  have logt9ltlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 < Real.log T ^ 9 := by
    intro t ht
    obtain h1 := logtltlogT_bounds t ht
    obtain h2 := logtgt1_bounds t ht
    have h3: 0 ≤ Real.log |t| := by linarith
    refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr h1
    linarith
    linarith
    linarith

  have Aoverlogt9gtAoverlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ 9 > A / Real.log T ^ 9 := by
    intro t ht
    have h1 := logt9ltlogT9_bounds t ht
    have h2 :=logt9gt1_bounds t ht
    refine div_lt_div_of_pos_left ?_ ?_ h1
    linarith [hA.1]
    linarith

  have AoverlogT9in0half: A / Real.log T ^ 9 ∈ Ioo 0 (1/2) := by
    constructor
    · refine div_pos ?_ ?_
      refine EReal.coe_pos.mp ?_
      exact EReal.coe_lt_coe hA.1
      linarith
    · refine (div_lt_comm₀ ?_ ?_).mpr ?_
      linarith
      linarith
      refine (div_lt_iff₀' ?_).mpr ?_
      linarith
      have hA_lt : A ≤ 1 / 2 := hA.2
      have hbound : 1 / 2 < (1 / 2) * Real.log T ^ 9 := by
        linarith
      exact lt_of_le_of_lt hA_lt hbound

  have σ₁lt2 : (σ₁ : ℝ) < 2 := by
    unfold σ₁
    linarith[AoverlogT9in0half.1]

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    linarith[AoverlogT9in0half.1]

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    linarith[AoverlogT9in0half.2]

  have quotient_bound : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ 9 / t ^ 2  := by
    intro t ht
    have loght := logt9gt1_bounds t ht
    have logpos : Real.log |t| ^ 9 > 0 := by linarith
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    have denom_pos : 0 < t ^ 2 := by
      have : t ^ 2 = |t| ^ 2 := by
        exact Eq.symm (sq_abs t)
      rw [this]
      have h1 := ht.1
      have abspos : |t| > 0 := by linarith
      exact sq_pos_of_pos abspos
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have boundthing : ∀ t, 3 < |t| ∧ |t| < T → σ₁ ∈ Ico (1 - A / Real.log |t| ^ 9) 1 := by
    intro t ht
    have h1 := Aoverlogt9gtAoverlogT9_bounds t ht
    constructor
    · unfold σ₁
      linarith
    · exact σ₁lt1

  have : ∫ (t : ℝ) in -T..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) = ∫ (t : ℝ) in Ioo (-T : ℝ) (-3 : ℝ),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.integral_Ioc_eq_integral_Ioo
  rw[this]

  have MellinBound : ∀ (t : ℝ) , ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    apply CMhyp σ₁
    exact σ₁pos
    dsimp
    ring_nf
    rfl
    dsimp
    ring_nf
    linarith
    exact εgt0
    exact εlt1

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ 9 := by
    intro t tbounds
    obtain ⟨tgt3, tltT⟩ := tbounds
    apply hCζ
    · exact tgt3
    · apply boundthing
      constructor
      · exact tgt3
      · exact tltT

  have Mellin_bd : ∀ t, 3 < |t| ∧ |t| < T →
  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖σ₁ + t * I‖ ^ 2)⁻¹ := by
    intro t ht
    apply MellinBound

  have logzeta_bd : ∀ t, 3 < |t| ∧ |t| < T →
    ‖ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)‖ ≤ Cζ * Real.log |t| ^ 9 := by
    intro t t_bounds
    obtain ⟨abs_tgt3,abs_tltX⟩ := t_bounds
    apply logzetabnd
    constructor
    · exact abs_tgt3
    · exact abs_tltX
  have : ‖1 / (2 * ↑π * I) *
        (I * ∫ (t : ℝ) in -X..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑T ^ (↑σ₁ + ↑t * I))‖
    =
    (1 / (2 * π)) * ‖∫ (t : ℝ) in -X..-3,
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑T ^ (↑σ₁ + ↑t * I)‖ := by
    simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
    rw[Complex.norm_I]
    simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
    have : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by
      dsimp
      ring_nf
      simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
      rw[inv_I]
      have : ‖-I‖ = ‖-1 * I‖ := by
        simp
      rw[this]
      have : ‖-1 * I‖ = ‖-1‖ * ‖I‖ := by
        simp
      rw[this, Complex.norm_I]
      ring_nf
      simp
      exact pi_nonneg
    rw[this]

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have norm_X_sigma1: ∀ (t : ℝ), ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
    intro t
    have Xpos : 0 < X := by linarith
    have : ((↑σ₁ + ↑t * I).re) = σ₁ := by
      dsimp
      ring_nf
    nth_rw 2[← this]
    apply Complex.norm_cpow_eq_rpow_re_of_pos Xpos

  have bound_integral : ∀ (t : ℝ), 3  < |t| ∧ |t| < T → ‖f t‖ ≤ g t := by
    intro t
    rintro ⟨ht_gt3, ht_ltT⟩
    have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := norm_X_sigma1 t
    have logtgt1 : 1 < Real.log |t| := by
        exact logt_gt_one ht_gt3
    have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
    have h𝓜 := MellinBound t
    have : ‖f ↑t‖ = ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ := by
      rfl
    rw[this]
    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ 9) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      rw[Xσ_bound]
      gcongr
    have : (Cζ * Real.log |t| ^ 9) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f: ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I))‖ = ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          f t)‖ := by
      unfold f
      simp
  rw[int_with_f]
  apply (norm_mul_le _ _).trans
  have int_mulbyI_is_int : ‖I * ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ = ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    rw [Complex.norm_mul, Complex.norm_I]
    ring
  rw[int_mulbyI_is_int]

  have norm_1over2pii_le1: ‖1 / (2 * ↑π * I)‖ ≤ 1 := by
    simp
    have pi_gt_3 : Real.pi > 3 := by
      exact pi_gt_three
    have pi_pos : 0 < π := by linarith [pi_gt_3]
    have abs_pi_inv_le : |π|⁻¹ ≤ (1 : ℝ) := by
      rw [abs_of_pos pi_pos]
      have h : 1 = π * π⁻¹ := by
        field_simp
      rw[h]
      nth_rw 1 [← one_mul π⁻¹]
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact inv_nonneg.mpr (le_of_lt pi_pos)
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_half_le_one : (2 : ℝ)⁻¹ ≤ 1 := by norm_num
    linarith

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · exact norm_1over2pii_le1
  apply le_trans this
  have : ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑ t‖ := by
    apply norm_integral_le_integral_norm
  apply le_trans this

  have norm_f_nonneg: ∀ t, ‖f t‖ ≥ 0 := by
    exact fun t ↦ norm_nonneg (f t)

  have g_cont : ContinuousOn g (Icc (-T) (-3)) := by
    unfold g
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_const
    · exact continuousOn_const
    · refine ContinuousOn.pow ?_ 9
      refine ContinuousOn.log ?_ ?_
      · refine Continuous.continuousOn ?_
        exact _root_.continuous_abs
      · intro t ht
        have h1 := ht.1
        have h2 := ht.2
        by_contra!
        have : t = 0 := by
          exact abs_eq_zero.mp this
        rw[this] at h2
        absurd
        h2
        linarith
    · refine ContinuousOn.inv₀ ?_ ?_
      · refine ContinuousOn.mul ?_ ?_
        · exact continuousOn_const
        · refine ContinuousOn.pow ?_ 2
          refine ContinuousOn.norm ?_
          refine ContinuousOn.add ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.mul ?_ ?_
            · refine continuousOn_of_forall_continuousAt ?_
              intro x hx
              exact continuous_ofReal.continuousAt
            · exact continuousOn_const
      · intro x hx
        have norm_sq_pos : ‖(σ₁ : ℂ) + x * Complex.I‖ ^ 2 = σ₁ ^ 2 + x ^ 2 := by
          rw [Complex.sq_norm]
          exact normSq_add_mul_I σ₁ x
        have : 0 < σ₁ ^ 2 + x ^ 2 := by
          apply add_pos_of_pos_of_nonneg
          · exact sq_pos_of_pos σ₁pos
          · exact sq_nonneg x
        apply mul_ne_zero
        · linarith
        · rw [norm_sq_pos]
          exact ne_of_gt this
    · exact continuousOn_const

  have g_integrable_Icc : IntegrableOn g (Icc (-T) (-3)) volume := by
    exact ContinuousOn.integrableOn_Icc g_cont

  have g_integrable_Ioo : IntegrableOn g (Ioo (-T) (-3)) volume := by
    apply MeasureTheory.IntegrableOn.mono_set g_integrable_Icc
    exact Ioo_subset_Icc_self

  have int_normf_le_int_g: ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in Ioo (-T) (-3), g ↑t := by

    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · have f_int : IntegrableOn (fun (t : ℝ) ↦ ‖f t‖) (Ioo (-T : ℝ) (-3 : ℝ)) volume := by
        have hle : -T ≤ -3 := by linarith
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp h_int
      apply MeasureTheory.setIntegral_mono_on
      exact f_int
      exact g_integrable_Ioo
      exact measurableSet_Ioo
      intro t ht
      apply bound_integral
      have : |t| = -t := by
        refine abs_of_neg ?_
        linarith [ht.2]
      have abs_tgt3 : 3 < |t| := by
        rw[this]
        linarith[ht.2]
      have abs_tltX : |t| < T := by
        rw[this]
        linarith[ht.1]
      constructor
      · linarith
      · linarith
    · have : ∫ (t : ℝ) in -T..-3, ‖f ↑ t‖ = ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖  := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      have : ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖ = 0 := by
        rw [← this]
        exact intervalIntegral.integral_undef h_int
      rw [this]
      apply MeasureTheory.setIntegral_nonneg
      · exact measurableSet_Ioo
      · intro t ht
        have abst_negt : |t| = -t := by
          refine abs_of_neg ?_
          linarith [ht.2]
        have tbounds1 : 3 < |t| ∧ |t| < T := by
          rw[abst_negt]
          constructor
          · linarith [ht.2]
          · linarith [ht.1]
        unfold g
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        · linarith
        · linarith
        · linarith [logt9gt1_bounds t tbounds1]
        · field_simp
          apply div_nonneg
          · linarith
          · apply mul_nonneg
            · linarith
            · rw [Complex.sq_norm]
              exact normSq_nonneg (↑σ₁ + ↑t * I)
        · apply Real.rpow_nonneg
          linarith

  apply le_trans int_normf_le_int_g
  unfold g

  have : X ^ σ₁ = X ^ (1 - A / Real.log T ^ 9) := by
    rfl
  rw[this]

  have : X ^ (1 - A / Real.log T ^ 9) = X * X ^ (- A / Real.log T ^ 9) := by
    have hX : X > 0 := by linarith
    simp only [Real.rpow_sub hX, Real.rpow_one]
    have h₁ : X ^ (-A / Real.log T ^ 9) * X ^ (A / Real.log T ^ 9) = 1 := by
      rw [← Real.rpow_add hX]
      ring_nf
      exact rpow_zero X
    field_simp
    rw[mul_assoc, h₁]
    ring

  rw[this]


  have Bound_of_log_int: ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]
    have normsquared : ∀ (t : ℝ), ‖↑σ₁ + ↑t * I‖ ^ 2 = σ₁ ^ 2 + t ^ 2 := by
      intro t
      simp only [Complex.sq_norm]
      exact normSq_add_mul_I σ₁ t

    have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2
          = ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) := by
      simp_rw [normsquared]

    have bound : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      rw [this]
      have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 /  t ^ 2 := by
        refine setIntegral_mono_on ?_ ?_ ?_ ?_
        ·
          have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have h2 : t ≠ 0 := by linarith
              have h3 : 0 < t ^ 2 := pow_two_pos_of_ne_zero h2
              have h4 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              linarith [h3, h4]
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have tne0 : t ≠ 0 := by linarith
              exact pow_ne_zero 2 tne0
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · exact measurableSet_Ioo
        · intro x hx
          have xneg : x < 0 := by linarith[hx.2]
          have absx : |x| = -x := abs_of_neg xneg
          have h1 : 3 < |x| ∧ |x| < T := by
            rw[absx]
            constructor
            · linarith [hx.2]
            · linarith [hx.1]
          exact quotient_bound x (t_bounds x hx)
      apply le_trans this
      have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
            = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
        have eq_integrand : ∀ (t : ℝ), t ∈ Ioo (-T) (-3) → (Real.log |t|) ^ 9 / t ^ 2 = (Real.log (-t)) ^ 9 / (-t) ^ 2 := by
          intro t ht
          have tneg : t < 0 := by linarith[ht.2]
          have : |t| = -t := abs_of_neg tneg
          rw [this, neg_sq]

        have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
              = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo eq_integrand

        rw [this]

        have interval_to_Ioo1 : ∫ (t : ℝ) in -T..-3, Real.log (-t) ^ 9 / (-t) ^ 2
                        = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        have interval_to_Ioo2 : ∫ (t : ℝ) in (3)..(T), Real.log t ^ 9 / t ^ 2
                    = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        rw [← interval_to_Ioo1, ← interval_to_Ioo2]
        rw [intervalIntegral.integral_comp_neg (fun (t : ℝ) ↦ Real.log (t) ^ 9 / (t) ^ 2)]
        simp
      rw [this]
      have : ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 < Cint := by
        exact Cinthyp T Tgt3
      linarith
    rw [ mul_comm]
    rw [← mul_div_assoc, mul_one]
    exact (div_le_div_iff_of_pos_right εgt0).mpr bound


  have factor_out_constants :
  ∫ (t : ℝ) in Ioo (-T) (-3), Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ^ 9))
  = Cζ * CM * (X * X ^ (-A / Real.log T ^ 9)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     rw [← integral_const_mul]
     apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
     intro t ht
     ring
  rw[factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T ^ 9)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T ^ 9)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · have hpos : 0 < X * X ^ (-A / Real.log T ^ 9) := by
        apply mul_pos
        · linarith
        · apply Real.rpow_pos_of_pos
          linarith
      apply mul_nonneg
      · apply mul_nonneg
        · linarith
        · linarith
      · linarith [hpos]

  apply le_trans this
  ring_nf
  field_simp

lemma I7Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    --(SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    --(mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioc 0 (1/2)),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  choose A hA Cζ Cζpos hCζ using LogDerivZetaBnd
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded 9
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  use A
  use hA
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁
  unfold I₇
  unfold SmoothedChebyshevIntegrand

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3

  have logXgt1 : Real.log X > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logTgt1 : Real.log T > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logX9gt1 : Real.log X ^ 9 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logXgt1
    linarith
    linarith

  have logT9gt1 : Real.log T ^ 9 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logTgt1
    linarith
    linarith

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      linarith[h2]
    have abs_tgt3 : 3 < |t| := by
      rw[this]
      linarith[h2]
    have abs_tltX : |t| < T := by
      rw[this]
      linarith[h1]
    exact ⟨abs_tgt3, abs_tltX⟩

  have logtgt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| > 1 := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine logt_gt_one ?_
    exact h1

  have logt9gt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 > 1 := by
    intro t ht
    refine one_lt_pow₀ (logtgt1_bounds t ht) ?_
    linarith

  have logtltlogT_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| < Real.log T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine log_lt_log ?_ ?_
    linarith
    linarith

  have logt9ltlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 < Real.log T ^ 9 := by
    intro t ht
    obtain h1 := logtltlogT_bounds t ht
    obtain h2 := logtgt1_bounds t ht
    have h3: 0 ≤ Real.log |t| := by linarith
    refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr h1
    linarith
    linarith
    linarith

  have Aoverlogt9gtAoverlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ 9 > A / Real.log T ^ 9 := by
    intro t ht
    have h1 := logt9ltlogT9_bounds t ht
    have h2 :=logt9gt1_bounds t ht
    refine div_lt_div_of_pos_left ?_ ?_ h1
    linarith [hA.1]
    linarith

  have AoverlogT9in0half: A / Real.log T ^ 9 ∈ Ioo 0 (1/2) := by
    constructor
    · refine div_pos ?_ ?_
      refine EReal.coe_pos.mp ?_
      exact EReal.coe_lt_coe hA.1
      linarith
    · refine (div_lt_comm₀ ?_ ?_).mpr ?_
      linarith
      linarith
      refine (div_lt_iff₀' ?_).mpr ?_
      linarith
      have hA_lt : A ≤ 1 / 2 := hA.2
      have hbound : 1 / 2 < (1 / 2) * Real.log T ^ 9 := by
        linarith
      exact lt_of_le_of_lt hA_lt hbound

  have σ₁lt2 : (σ₁ : ℝ) < 2 := by
    unfold σ₁
    linarith[AoverlogT9in0half.1]

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    linarith[AoverlogT9in0half.1]

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    linarith[AoverlogT9in0half.2]

  have quotient_bound : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ 9 / t ^ 2  := by
    intro t ht
    have loght := logt9gt1_bounds t ht
    have logpos : Real.log |t| ^ 9 > 0 := by linarith
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    have denom_pos : 0 < t ^ 2 := by
      have : t ^ 2 = |t| ^ 2 := by
        exact Eq.symm (sq_abs t)
      rw [this]
      have h1 := ht.1
      have abspos : |t| > 0 := by linarith
      exact sq_pos_of_pos abspos
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have boundthing : ∀ t, 3 < |t| ∧ |t| < T → σ₁ ∈ Ico (1 - A / Real.log |t| ^ 9) 1 := by
    intro t ht
    have h1 := Aoverlogt9gtAoverlogT9_bounds t ht
    constructor
    · unfold σ₁
      linarith
    · exact σ₁lt1

  have : ∫ (t : ℝ) in (↑3)..T,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) = ∫ (t : ℝ) in Ioo (3 : ℝ) (T : ℝ),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.integral_Ioc_eq_integral_Ioo

  rw[this]

  have MellinBound : ∀ (t : ℝ) , ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    apply CMhyp σ₁
    exact σ₁pos
    dsimp
    ring_nf
    rfl
    dsimp
    ring_nf
    linarith
    exact εgt0
    exact εlt1

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ 9 := by
    intro t tbounds
    obtain ⟨tgt3, tltT⟩ := tbounds
    apply hCζ
    · exact tgt3
    · apply boundthing
      constructor
      · exact tgt3
      · exact tltT

  have Mellin_bd : ∀ t, 3 < |t| ∧ |t| < T →
  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖σ₁ + t * I‖ ^ 2)⁻¹ := by
    intro t ht
    apply MellinBound

  have logzeta_bd : ∀ t, 3 < |t| ∧ |t| < T →
    ‖ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)‖ ≤ Cζ * Real.log |t| ^ 9 := by
    intro t t_bounds
    obtain ⟨abs_tgt3,abs_tltX⟩ := t_bounds
    apply logzetabnd
    constructor
    · exact abs_tgt3
    · exact abs_tltX
  have : ‖1 / (2 * ↑π * I) *
        (I * ∫ (t : ℝ) in -X..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑T ^ (↑σ₁ + ↑t * I))‖
    =
    (1 / (2 * π)) * ‖∫ (t : ℝ) in -X..-3,
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑T ^ (↑σ₁ + ↑t * I)‖ := by
    simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
    rw[Complex.norm_I]
    simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
    have : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by
      dsimp
      ring_nf
      simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
      rw[inv_I]
      have : ‖-I‖ = ‖-1 * I‖ := by
        simp
      rw[this]
      have : ‖-1 * I‖ = ‖-1‖ * ‖I‖ := by
        simp
      rw[this, Complex.norm_I]
      ring_nf
      simp
      exact pi_nonneg
    rw[this]

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have norm_X_sigma1: ∀ (t : ℝ), ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
    intro t
    have Xpos : 0 < X := by linarith
    have : ((↑σ₁ + ↑t * I).re) = σ₁ := by
      dsimp
      ring_nf
    nth_rw 2[← this]
    apply Complex.norm_cpow_eq_rpow_re_of_pos Xpos

  have bound_integral : ∀ (t : ℝ), 3  < |t| ∧ |t| < T → ‖f t‖ ≤ g t := by
    intro t
    rintro ⟨ht_gt3, ht_ltT⟩
    have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := norm_X_sigma1 t
    have logtgt1 : 1 < Real.log |t| := by
        exact logt_gt_one ht_gt3
    have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
    have h𝓜 := MellinBound t
    have : ‖f ↑t‖ = ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ := by
      rfl
    rw[this]
    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ 9) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      rw[Xσ_bound]
      gcongr
    have : (Cζ * Real.log |t| ^ 9) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f: ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (3) (T),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I))‖ = ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (3) (T),
          f t)‖ := by
      unfold f
      simp
  rw[int_with_f]
  apply (norm_mul_le _ _).trans
  have int_mulbyI_is_int : ‖I * ∫ (t : ℝ) in Ioo (3) (T), f ↑t‖ = ‖ ∫ (t : ℝ) in Ioo (3) (T), f ↑t‖ := by
    rw [Complex.norm_mul, Complex.norm_I]
    ring
  rw[int_mulbyI_is_int]

  have norm_1over2pii_le1: ‖1 / (2 * ↑π * I)‖ ≤ 1 := by
    simp
    have pi_gt_3 : Real.pi > 3 := by
      exact Real.pi_gt_three
    have pi_pos : 0 < π := by linarith [pi_gt_3]
    have abs_pi_inv_le : |π|⁻¹ ≤ (1 : ℝ) := by
      rw [abs_of_pos pi_pos]
      have h : 1 = π * π⁻¹ := by
        field_simp
      rw[h]
      nth_rw 1 [← one_mul π⁻¹]
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact inv_nonneg.mpr (le_of_lt pi_pos)
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_half_le_one : (2 : ℝ)⁻¹ ≤ 1 := by norm_num
    linarith

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in Ioo (3) (T), f ↑t‖ ≤  ‖∫ (t : ℝ) in Ioo (3) (T), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · exact norm_1over2pii_le1
  apply le_trans this
  have : ‖ ∫ (t : ℝ) in Ioo (3) (T), f ↑t‖ ≤  ∫ (t : ℝ) in Ioo (3) (T), ‖f ↑ t‖ := by
    apply norm_integral_le_integral_norm
  apply le_trans this

  have norm_f_nonneg: ∀ t, ‖f t‖ ≥ 0 := by
    exact fun t ↦ norm_nonneg (f t)

  have g_cont : ContinuousOn g (Icc (3) (T)) := by
    unfold g
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_const
    · exact continuousOn_const
    · refine ContinuousOn.pow ?_ 9
      refine ContinuousOn.log ?_ ?_
      · refine Continuous.continuousOn ?_
        exact _root_.continuous_abs
      · intro t ht
        have h1 := ht.1
        have h2 := ht.2
        by_contra!
        have : t = 0 := by
          exact abs_eq_zero.mp this
        rw[this] at h2
        absurd
        h2
        linarith
    · refine ContinuousOn.inv₀ ?_ ?_
      · refine ContinuousOn.mul ?_ ?_
        · exact continuousOn_const
        · refine ContinuousOn.pow ?_ 2
          refine ContinuousOn.norm ?_
          refine ContinuousOn.add ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.mul ?_ ?_
            · refine continuousOn_of_forall_continuousAt ?_
              intro x hx
              exact continuous_ofReal.continuousAt
            · exact continuousOn_const
      · intro x hx
        have norm_sq_pos : ‖(σ₁ : ℂ) + x * Complex.I‖ ^ 2 = σ₁ ^ 2 + x ^ 2 := by
          rw [Complex.sq_norm]
          exact normSq_add_mul_I σ₁ x
        have : 0 < σ₁ ^ 2 + x ^ 2 := by
          apply add_pos_of_pos_of_nonneg
          · exact sq_pos_of_pos σ₁pos
          · exact sq_nonneg x
        apply mul_ne_zero
        · linarith
        · rw [norm_sq_pos]
          exact ne_of_gt this
    · exact continuousOn_const

  have g_integrable_Icc : IntegrableOn g (Icc (3) (T)) volume := by
    exact ContinuousOn.integrableOn_Icc g_cont

  have g_integrable_Ioo : IntegrableOn g (Ioo (3) (T)) volume := by
    apply MeasureTheory.IntegrableOn.mono_set g_integrable_Icc
    exact Ioo_subset_Icc_self

  have int_normf_le_int_g: ∫ (t : ℝ) in Ioo (3) (T), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in Ioo (3) (T), g ↑t := by

    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (3) (T)
    · have f_int : IntegrableOn (fun (t : ℝ) ↦ ‖f t‖) (Ioo (3 : ℝ) (T : ℝ)) volume := by
        have hle : 3 ≤ T := by linarith
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp h_int
      apply MeasureTheory.setIntegral_mono_on
      exact f_int
      exact g_integrable_Ioo
      exact measurableSet_Ioo
      intro t ht
      apply bound_integral
      have : |t| = t := by
        refine abs_of_pos ?_
        linarith [ht.1]
      have abs_tgt3 : 3 < |t| := by
        rw[this]
        linarith[ht.1]
      have abs_tltX : |t| < T := by
        rw[this]
        linarith[ht.2]
      constructor
      · linarith
      · linarith
    · have : ∫ (t : ℝ) in (3 : ℝ)..(T : ℝ), ‖f ↑ t‖ = ∫ (t : ℝ) in Ioo (3) (T), ‖f ↑t‖  := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      have : ∫ (t : ℝ) in Ioo (3) (T), ‖f ↑t‖ = 0 := by
        rw [← this]
        exact intervalIntegral.integral_undef h_int
      rw [this]
      apply MeasureTheory.setIntegral_nonneg
      · exact measurableSet_Ioo
      · intro t ht
        have abst_negt : |t| = t := by
          refine abs_of_pos ?_
          linarith [ht.1]
        have tbounds1 : 3 < |t| ∧ |t| < T := by
          rw[abst_negt]
          constructor
          · linarith [ht.1]
          · linarith [ht.2]
        unfold g
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        · linarith
        · linarith
        · linarith [logt9gt1_bounds t tbounds1]
        · field_simp
          apply div_nonneg
          · linarith
          · apply mul_nonneg
            · linarith
            · rw [Complex.sq_norm]
              exact normSq_nonneg (↑σ₁ + ↑t * I)
        · apply Real.rpow_nonneg
          linarith

  apply le_trans int_normf_le_int_g
  unfold g

  have : X ^ σ₁ = X ^ (1 - A / Real.log T ^ 9) := by
    rfl
  rw[this]

  have : X ^ (1 - A / Real.log T ^ 9) = X * X ^ (- A / Real.log T ^ 9) := by
    have hX : X > 0 := by linarith
    simp only [Real.rpow_sub hX, Real.rpow_one]
    have h₁ : X ^ (-A / Real.log T ^ 9) * X ^ (A / Real.log T ^ 9) = 1 := by
      rw [← Real.rpow_add hX]
      ring_nf
      exact rpow_zero X
    field_simp
    rw[mul_assoc, h₁]
    ring

  rw[this]


  have Bound_of_log_int: ∫ (t : ℝ) in Ioo (3) (T), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in Ioo (3) (T), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in Ioo (3) (T), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]
    have normsquared : ∀ (t : ℝ), ‖↑σ₁ + ↑t * I‖ ^ 2 = σ₁ ^ 2 + t ^ 2 := by
      intro t
      simp only [Complex.sq_norm]
      exact normSq_add_mul_I σ₁ t

    have : ∫ t in Ioo (3) (T), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2
          = ∫ t in Ioo (3) (T), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) := by
      simp_rw [normsquared]

    have bound : ∫ t in Ioo (3) (T), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      rw [this]
      have : ∫ t in Ioo (3) (T), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in Ioo (3) (T), Real.log |t| ^ 9 /  t ^ 2 := by
        refine setIntegral_mono_on ?_ ?_ ?_ ?_
        ·
          have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Set.Icc (3) (T)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : 3 ≤ x := hx.1
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' (Icc (3) (T))
            · intro t ht
              have h1 : 3 ≤ t := ht.1
              have h2 : t ≠ 0 := by linarith
              have h3 : 0 < t ^ 2 := pow_two_pos_of_ne_zero h2
              have h4 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              linarith [h3, h4]
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Icc (3) (T)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Ioo (3) (T)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Set.Icc (3) (T)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : 3 ≤ x := hx.1
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' (Icc (3) (T))
            · intro t ht
              have h1 : 3 ≤ t := ht.1
              have tne0 : t ≠ 0 := by linarith
              exact pow_ne_zero 2 tne0
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Icc (3) (T)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Ioo (3) (T)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · exact measurableSet_Ioo
        · intro x hx
          have xneg : 0 < x := by linarith[hx.1]
          have absx : |x| = x := abs_of_pos xneg
          have h1 : 3 < |x| ∧ |x| < T := by
            rw[absx]
            constructor
            · linarith [hx.1]
            · linarith [hx.2]
          exact quotient_bound x h1
      apply le_trans this

      have : ∫ (t : ℝ) in Ioo (3) (T), Real.log |t| ^ 9 / t ^ 2
            = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
        have eq_integrand : ∀ (t : ℝ), t ∈ Ioo (3) (T) → (Real.log |t|) ^ 9 / t ^ 2 = (Real.log t) ^ 9 / t ^ 2 := by
          intro t ht
          have tpos : 0 < t := by linarith[ht.1]
          have : |t| = t := abs_of_pos tpos
          rw [this]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo eq_integrand

      rw [this]
      have : ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 < Cint := by
        exact Cinthyp T Tgt3
      linarith
    rw [ mul_comm]
    rw [← mul_div_assoc, mul_one]
    exact (div_le_div_iff_of_pos_right εgt0).mpr bound


  have factor_out_constants :
  ∫ (t : ℝ) in Ioo (3) (T), Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ^ 9))
  = Cζ * CM * (X * X ^ (-A / Real.log T ^ 9)) * ∫ (t : ℝ) in Ioo (3) (T), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     rw [← integral_const_mul]
     apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
     intro t ht
     ring
  rw[factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T ^ 9)) * ∫ (t : ℝ) in Ioo (3) (T), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T ^ 9)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · have hpos : 0 < X * X ^ (-A / Real.log T ^ 9) := by
        apply mul_pos
        · linarith
        · apply Real.rpow_pos_of_pos
          linarith
      apply mul_nonneg
      · apply mul_nonneg
        · linarith
        · linarith
      · linarith [hpos]

  apply le_trans this
  ring_nf
  field_simp
/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBnd, IntegralofLogx^n/x^2Bounded, I3, I7}\leanok
Unfold the definitions and apply the triangle inequality.
$$
\left|I_{3}(\nu, \epsilon, X, T, \sigma_1)\right| =
\left|\frac{1}{2\pi i} \int_{-T}^3
\left(\frac{-\zeta'}\zeta(\sigma_1 + t i) \right)
\mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
X^{\sigma_1 + t i}
\ i \ dt
\right|
$$
$$\leq
\frac{1}{2\pi}
\int_{-T}^3
C \cdot \log t ^ 9
\frac{C'}{\epsilon|\sigma_1 + t i|^2}
X^{\sigma_1}
 \ dt
,
$$
where we used Theorems \ref{MellinOfSmooth1b} and \ref{LogDerivZetaBnd}.
Now we estimate $X^{\sigma_1} = X \cdot X^{-A/ \log T^9}$, and the integral is absolutely bounded.
\end{proof}
%%-/



/-%%
\begin{lemma}[I4Bound]\label{I4Bound}\lean{I4Bound}\leanok
We have that
$$
\left|I_{4}(\nu, \epsilon, X, \sigma_1, \sigma_2)\right| \ll \frac{X}{\epsilon}\,
 X^{-\frac{A}{(\log T)^9}}
.
$$
Same with $I_6$.
\end{lemma}
%%-/
lemma I4Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioo 0 (1/2)) (σ₂ : ℝ) (_ : σ₂ ∈ Ioo 0 1),
    ∀ (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    {T : ℝ} (T_gt : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log X) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  sorry

lemma I6Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioo 0 (1/2)) (σ₂ : ℝ) (_ : σ₂ ∈ Ioo 0 1),
    ∀ (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    {T : ℝ} (T_gt : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log X) ^ 9
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  sorry
/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBndAlt, I4, I6}
The analysis of $I_4$ is similar to that of $I_2$, (in Lemma \ref{I2Bound}) but even easier.
Let $C$ be the sup of $-\zeta'/\zeta$ on the curve $\sigma_2 + 3 i$ to $1+ 3i$ (this curve is compact, and away from the pole at $s=1$).
Apply Theorem \ref{MellinOfSmooth1b} to get the bound $1/(\epsilon |s|^2)$, which is bounded by $C'/\epsilon$.
And $X^s$ is bounded by $X^{\sigma_1} = X \cdot X^{-A/ \log T^9}$.
Putting these together gives the result.
\end{proof}
%%-/


/-%%
\begin{lemma}[I5Bound]\label{I5Bound}\lean{I5Bound}\leanok
We have that
$$
\left|I_{5}(\nu, \epsilon, X, \sigma_2)\right| \ll \frac{X^{\sigma_2}}{\epsilon}.
$$
\end{lemma}
%%-/

lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    : ∃ (C : ℝ) (_ : 0 < C) (σ₂ : ℝ) (_ : σ₂ ∈ Ioo 0 1),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by

  let ⟨σ₂, ⟨σ₂_le_one, h_logDeriv_holo⟩⟩ := LogDerivZetaHolcSmallT
  -- IsCompact.exists_bound_of_continuousOn'
  unfold HolomorphicOn at h_logDeriv_holo
  let zeta'_zeta_on_line := fun (t : ℝ) ↦ ζ' (σ₂ + t * I) / ζ (σ₂ + t * I)


  let our_σ₂ : ℝ := max σ₂ (1/2 : ℝ)

  have T : our_σ₂ < 1 := by
    unfold our_σ₂
    by_cases h : σ₂ > (1/2 : ℝ)
    · simp only [one_div, sup_lt_iff, true_and, σ₂_le_one]
      linarith
    · simp only [one_div, sup_lt_iff, true_and, σ₂_le_one]
      linarith

  have P : our_σ₂ > 0 := by
    unfold our_σ₂
    simp only [one_div, gt_iff_lt, lt_sup_iff, inv_pos, Nat.ofNat_pos, or_true]

  have subst : {our_σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
    simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, neg_le_self_iff,
      Nat.ofNat_nonneg, uIcc_of_le]
    intro z
    intro hyp_z
    simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
    simp only [mem_diff, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · constructor
      · rw [hyp_z.1]
        refine mem_uIcc_of_le ?_ ?_
        · exact le_max_left σ₂ (1 / 2)
        · linarith
      · exact hyp_z.2
    · push_neg
      by_contra h
      rw [h] at hyp_z
      simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
      rw [hyp_z] at σ₂_le_one
      simp_all only [lt_self_iff_false]

  have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn


  have is_compact' : IsCompact ({our_σ₂} ×ℂ uIcc (-3) 3) := by
    refine IsCompact.reProdIm ?_ ?_
    · exact isCompact_singleton
    · exact isCompact_uIcc

  let ⟨zeta_bound, zeta_prop⟩ :=
    IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

  let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

  let our_σ₂ : ℝ := max σ₂ (1/2 : ℝ)


  unfold I₅
  unfold SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑our_σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard our_σ₂ (by positivity) (our_σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith))

  simp only [mul_inv_rev] at mellin_prop

  let Const := 1 + (our_σ₂^2)⁻¹ * (abs zeta_bound) * M

  let C := |π|⁻¹ * 2⁻¹ * 6 * Const
  use C
  have C_pos : 0 < C := by positivity
  use C_pos
  use our_σ₂

  have U : our_σ₂ ∈ Ioo 0 1 := by
    refine mem_Ioo.mpr ?_
    · constructor
      · exact P
      · exact T

  use U

  clear U  T  σ₂_le_one C_pos

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < our_σ₂^2 := by
    unfold our_σ₂
    exact sq_pos_of_pos P


  have easy_bound : ∀(t : ℝ), (‖↑our_σ₂ + ↑t * I‖^2)⁻¹ ≤ (our_σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      rw [Complex.sq_norm]; rw [Complex.normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]; ring_nf; simp only [le_add_iff_nonneg_right]; exact zpow_two_nonneg t
      rw [Complex.sq_norm, Complex.normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]; ring_nf; positivity
      positivity


  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑our_σ₂ + ↑t * I) / ζ (↑our_σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ our_σ₂ := by
    intro t
    intro hyp_t
    have Z := by
      calc
        ‖(-ζ' (↑our_σ₂ + ↑t * I) / ζ (↑our_σ₂ + ↑t * I)) * (𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖ = ‖-ζ' (↑our_σ₂ + ↑t * I) / ζ (↑our_σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑our_σ₂ + ↑t * I) / ζ (↑our_σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑our_σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · rfl
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑our_σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑our_σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (our_σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖  := by
          have T : 0 ≤ abs zeta_bound * M := by positivity
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑our_σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (our_σ₂^2)⁻¹ * ε⁻¹ * X ^ (our_σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ our_σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z


  -- Now want to apply the triangle inequality
  -- and bound everything trivially

  -- intervalIntegral.norm_integral_le_of_norm_le_const

  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ our_σ₂ * |3 + 3|) = C * X ^ our_σ₂ / ε :=
    by
      unfold C
      ring_nf
      simp only [Nat.abs_ofNat, one_div]
      have T :  6 * (2 : ℝ)⁻¹ = 3 := by
        refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
        · exact Ne.symm (NeZero.ne' 2)
        · norm_cast
      rw [←T]
      ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)


/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaHolcSmallT, I5}\leanok
Here $\zeta'/\zeta$ is absolutely bounded on the compact interval $\sigma_2 + i [-3,3]$, and
$X^s$ is bounded by $X^{\sigma_2}$. Using Theorem \ref{MellinOfSmooth1b} gives the bound $1/(\epsilon |s|^2)$, which is bounded by $C'/\epsilon$.
Putting these together gives the result.
\end{proof}
%%-/

/-%%
\section{MediumPNT}

\begin{theorem}[MediumPNT]\label{MediumPNT}  We have
$$ \sum_{n \leq x} \Lambda(n) = x + O(x \exp(-c(\log x)^{1/10})).$$
\end{theorem}
%%-/
/-- *** Prime Number Theorem (Medium Strength) *** The `ChebyshevPsi` function is asymptotic to `x`. -/
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
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
  have X_gt_3 : 3 < X := by sorry
  let ε : ℝ := sorry
  have ε_pos : 0 < ε := sorry
  have ε_lt_one : ε < 1 := sorry
  have ε_X : 2 < X * ε := sorry
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by
    exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by
    rwa [← integral_Ici_eq_integral_Ioi]
  let ψ_ε_of_X := SmoothedChebyshev ν ε X
  have : ∃ C > 0, ‖ψ X - ψ_ε_of_X‖ ≤ C * X * ε * Real.log X := by
    obtain ⟨C, Cpos, hC⟩ := SmoothedChebyshevClose ContDiff1ν
      ν_supp ν_nonneg ν_massOne
    refine ⟨C, Cpos, ?_⟩
    convert hC X X_gt_3 ε ε_pos ε_lt_one ε_X using 1
    · rw [← norm_neg]
      congr
      ring
    · ring
  obtain ⟨C_unsmoothing, C_unsmoothing_pos, ψ_ψ_ε_diff⟩ := this

  let T : ℝ := sorry
  have T_gt_3 : 3 < T := sorry
  obtain ⟨A, A_in_Ioc, holo1⟩ := LogDerivZetaHolcLargeT
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
  have σ₁pos : 0 < σ₁ := by sorry
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by sorry
  have σ₂_lt_one : σ₂ < 1 := by sorry
  have holo2 : HolomorphicOn (fun s ↦ ζ' s / ζ s) (uIcc σ₂ 2 ×ℂ uIcc (-3) 3 \ {1}) := by sorry
  have σ₂_lt_σ₁ : σ₂ < σ₁ := by sorry
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith[mem_reProdIm.mp hs.1 |>.1.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 ((Smooth1 ν ε) ·) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith) σ₁pos σ₁_lt_one holo1 ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith) σ₂_pos σ₁_lt_one σ₂_lt_σ₁ holo1 holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    apply le_trans (by apply norm_add_le)
    rw [(by ring : ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ = (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖) + (‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖))]
    gcongr <;> apply le_trans (by apply norm_sub_le) <;> rfl
  have : ∃ C_main > 0, ‖𝓜 ((Smooth1 ν ε) ·) 1 * X - X‖ ≤ C_main * ε * X := by sorry

  obtain ⟨C_main, C_main_pos, main_diff⟩ := this

  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  have I₁bnd := hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3

  obtain ⟨c₂, c₂pos, A₂, hA₂, hc₂⟩ := I2Bound ν_supp ContDiff1ν
  -- argh `I2bound` introduces its own `A` which is not the same as the one we have;
  -- need to refactor `I2Bound` to take `A` as an argument, via holomorphy and bounds for
  -- `ζ'/ζ`

  have := (
    calc
      ‖ψ X - X‖ = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
      _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
      _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X)
                    + (𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X)‖ := by ring_nf
      _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X‖
                    + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖ := by
                      rw [add_assoc]
                      gcongr
                      apply norm_add_le
      _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖
                    + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X‖ := by ring
      _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖
                    + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                    + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                    + ‖I₉ ν ε X T‖) := by gcongr

      _         = sorry := by sorry
  )

  sorry
/-%%
\begin{proof}
\uses{ChebyshevPsi, SmoothedChebyshevClose, LogDerivZetaBndAlt, ZetaBoxEval, LogDerivZetaBndUniform, LogDerivZetaHolcSmallT, LogDerivZetaHolcLargeT,
SmoothedChebyshevPull1, SmoothedChebyshevPull2, I1Bound, I2Bound, I3Bound, I4Bound, I5Bound}
  Evaluate the integrals.
\end{proof}
%%-/

-- #check MediumPNT
