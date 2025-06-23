import PrimeNumberTheoremAnd.ZetaBounds
import Mathlib.Algebra.Group.Support

set_option lang.lemmaCmd true

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
    bound
    rw[← mul_one 1]
    apply mul_lt_mul
    exact c₁_lt
    exact le_of_lt ε_lt_one
    exact ε_pos
    linarith

  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg
    rfl
    nth_rewrite 2 [← sub_zero 1]
    apply sub_le_sub
    rfl
    repeat positivity

  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    apply le_of_lt
    exact Nat.ceil_lt_add_one (by bound)

  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))

  have sumΛ : Summable (fun (n : ℕ) ↦ Λ n * F (n / X)) := by sorry
    -- := by
    -- exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    -- (hc₂ _ _ (by trivial) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
    -- (s ∘ Finset.mem_range.2))))))

  have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ Λ (n + n₀) * F ((n + n₀) / X)) := by exact_mod_cast sumΛ.comp_injective fun Q=>by valid

  have : ∑' (n : ℕ), Λ n * F (n / X) =
    (∑ n ∈ Finset.range (n₀), Λ n * F (n / X)) +
    (∑' (n : ℕ), Λ (n + n₀ : ) * F ((n + n₀ : ) / X)) := by
    rw[← Summable.sum_add_tsum_nat_add' (k := n₀)]
    norm_num[‹_›]

  rw [this]
  clear this

  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊

  have n₁_pos : 0 < n₁ := by
      dsimp only [n₁]
      apply Nat.le_floor
      rw[Nat.succ_eq_add_one, zero_add, ← one_mul 1, Nat.cast_mul]
      apply le_of_lt
      apply mul_lt_mul
      norm_cast
      linarith
      rw[← add_zero 1, Nat.cast_add]
      apply add_le_add
      rw[Nat.cast_le_one]
      rw[← mul_zero 0, Nat.cast_mul]
      apply mul_le_mul
      apply le_of_lt
      exact_mod_cast c₂_pos
      exact_mod_cast le_of_lt ε_pos
      exact Nat.cast_nonneg' 0
      exact_mod_cast le_of_lt c₂_pos
      rw[Nat.cast_pos]
      repeat positivity

  have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))

  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)

  have n₁_ge_n₀ : n₀ ≤ n₁ := by
    have : X * (1 - c₁ * ε) + 1 ≤ X * (1 + c₂ * ε) - 1 := by
      nth_rewrite 2 [sub_eq_add_neg]
      rw[← add_le_add_iff_right 1]
      ring_nf
      rw[← add_le_add_iff_right (X * ε * c₁)]
      ring_nf
      rw[add_comm, add_assoc, add_le_add_iff_left]
      have : (2 : ℝ) = 1 + 1 := by ring
      rw[this]
      apply add_le_add
      rw[mul_assoc]
      nth_rewrite 2 [mul_comm]
      rw[← mul_assoc]
      exact X_bound_1
      exact X_bound_2
    exact_mod_cast le_implies_le_of_le_of_le n₀_le n₁_ge this

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
    have : (∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X)) = 0 := by
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
    rw[this, add_zero]

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
    apply mul_le_mul
    apply vonBnd1
    exact hn
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddAbove
    bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound
    rw[← Real.log_one]
    exact Real.log_le_log (by positivity) (by bound)

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
        exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X X_le_floor_add_one
      have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
        apply sub_le_sub
        exact floor_X_add_one_le_self
        rfl
      exact le_of_lt (gt_of_ge_of_gt this temp)
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
      apply ArithmeticFunction.vonMangoldt_nonneg
    have inter2: Real.log (↑n + ↑n₀) ≤ Real.log (X + 1) := by exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)
    exact Preorder.le_trans ‖Λ (n + n₀)‖ (Real.log (↑n + ↑n₀)) (Real.log (X + 1)) inter1 inter2

  have largeSumBound:= add_le_add bnd1 bnd2

  clear vonBnd1 bnd1 bnd2

  have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
    apply Real.log_le_log
    positivity
    have const_le_2: 1 + c₂ * ε ≤ 3 := by
      have : (3 : ℝ) = 1 + 2 := by ring
      rw[this]
      apply add_le_add
      rfl
      rw[← mul_one 2]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw[mul_comm]
    exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)

  have inter2 : (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
    apply mul_le_mul
    exact n₁_sub_n₀
    rw[← Real.log_mul]
    nth_rewrite 3 [mul_comm]
    exact inter1
    repeat positivity
    rw[← Real.log_one]
    exact Real.log_le_log (by positivity) (by bound)
    positivity

  have inter3 : (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) ≤ 2 * (X * ε * (c₂ + c₁)) * (Real.log (X)) := by
    nth_rewrite 3 [mul_assoc]
    rw[two_mul, mul_add]
    apply add_le_add
    rfl
    apply mul_le_mul
    rfl
    exact Real.log_le_log (by positivity) (by linarith)
    rw[← Real.log_one]
    exact Real.log_le_log (by positivity) (by linarith)
    positivity

  have inter4 : (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) ≤ 2 * (X * ε * (c₁ + c₂)) * (Real.log (X)) := by
    nth_rewrite 2 [add_comm]
    exact
      Preorder.le_trans ((↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)))
        (X * ε * (c₂ + c₁) * (Real.log X + Real.log 3)) (2 * (X * ε * (c₂ + c₁)) * Real.log X)
        inter2 inter3

  clear inter2 inter3

  have inter5: Real.log (X + 1) ≤ Real.log (3 * X) := by exact Real.log_le_log (by positivity) (by linarith)

  have inter6 : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
    apply mul_le_mul
    have : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)) := by ring
    rw[this]
    apply sub_le_sub
    have : X + 1 ≤ X * (1 + ε * c₁) := by
      ring_nf
      rw[add_comm, add_le_add_iff_left]
      exact X_bound_1
    exact Preorder.le_trans (↑⌊X + 1⌋₊) (X + 1) (X * (1 + ε * c₁)) floor_X_add_one_le_self this
    nth_rewrite 2 [mul_comm]
    exact n₀_gt
    rw[← Real.log_mul, mul_comm]
    exact inter5
    repeat positivity
    rw[← Real.log_one]
    exact Real.log_le_log (by positivity) (by linarith)
    positivity

  have inter7: 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) ≤ 4 * (X * ε * c₁) * Real.log (X) := by
    have : (4 : ℝ) = 2 + 2 := by ring
    rw[this, mul_add]
    nth_rewrite 5 [mul_assoc]
    rw[add_mul]
    apply add_le_add
    nth_rewrite 1 [mul_assoc]
    rfl
    nth_rewrite 1 [mul_assoc]
    apply mul_le_mul
    rfl
    apply mul_le_mul
    rfl
    exact Real.log_le_log (by positivity) (by linarith)
    rw[← Real.log_one]
    exact Real.log_le_log (by positivity) (by linarith)
    repeat positivity

  have inter8: (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) ≤ 4 * (X * ε * c₁) * Real.log (X) := by
    exact
      Preorder.le_trans ((↑⌊X + 1⌋₊ - ↑n₀) * Real.log (X + 1))
        (2 * (X * ε * c₁) * (Real.log X + Real.log 3)) (4 * (X * ε * c₁) * Real.log X) inter6 inter7

  clear inter5 inter6 inter7

  have inter9: (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) + (↑⌊X + 1⌋₊ - ↑n₀) * Real.log (X + 1) ≤
    2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by
    have : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁) := by ring
    rw[this, add_mul]
    exact add_le_add inter4 inter8

  have largeSumBound2 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤
    2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by
    exact
      Preorder.le_trans (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖)
        ((↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) + (↑⌊X + 1⌋₊ - ↑n₀) * Real.log (X + 1))
        (2 * (X * ε * (3 * c₁ + c₂)) * Real.log X) largeSumBound inter9

  clear largeSumBound inter4 inter8 inter9

  have inter10 : ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    rw[← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul
    rw[Real.norm_of_nonneg]
    have temp : Λ n₁ ≤ Real.log (n₁) := by exact ArithmeticFunction.vonMangoldt_le_log
    have : Real.log (n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by
      apply Real.log_le_log
      exact_mod_cast n₁_pos
      exact n₁_le
    exact Preorder.le_trans (Λ n₁) (Real.log ↑n₁) (Real.log (X * (1 + c₂ * ε))) temp this
    exact ArithmeticFunction.vonMangoldt_nonneg
    rw[Real.norm_of_nonneg]
    apply smooth1BddAbove
    exact n₁_pos
    apply smooth1BddBelow
    exact n₁_pos
    rw[Real.norm_of_nonneg]
    apply smooth1BddBelow
    exact n₁_pos
    apply smooth1BddBelow
    exact n₁_pos
    rw[← Real.log_one]
    exact Real.log_le_log (by positivity) (by bound)

  have inter11 : ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ Real.log (3 * X) := by
    exact
      Preorder.le_trans (‖Λ n₁‖ * ‖F (↑n₁ / X)‖) (Real.log (X * (1 + c₂ * ε))) (Real.log (3 * X))
        inter10 inter1

  clear inter1 inter10

  have largeSumBound3 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by exact add_le_add largeSumBound2 inter11

  clear largeSumBound2 inter11

  have largeSumBound4 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (2 * Real.log X + Real.log (3)) := by
    have : 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) ≤
      2 * (X * ε * (3 * c₁ + c₂)) * (Real.log X + Real.log (3 * X)) := by
      nth_rewrite 2 [mul_add]
      apply add_le_add
      rfl
      nth_rewrite 1 [← one_mul (Real.log (3 * X))]
      apply mul_le_mul
      ring_nf
      rw[← zero_add 1]
      exact add_le_add (by positivity) (by bound)
      rfl
      rw[← Real.log_one]
      exact Real.log_le_log (by positivity) (by linarith)
      positivity
    nth_rewrite 2 [two_mul, add_assoc]
    rw [← Real.log_mul, mul_comm X 3]

    exact
      Preorder.le_trans
        (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ +
            ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
          ‖Λ n₁‖ * ‖F (↑n₁ / X)‖)
        (2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X))
        (2 * (X * ε * (3 * c₁ + c₂)) * (Real.log X + Real.log (3 * X))) largeSumBound3 this
    repeat positivity

  clear largeSumBound3

  have largeSumBoundFinal : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ (6 * (X * ε * (3 * c₁ + c₂))) * Real.log (X) := by
    have : 2 * (X * ε * (3 * c₁ + c₂)) * (2 * Real.log X + Real.log (3)) <= (6 * (X * ε * (3 * c₁ + c₂))) * Real.log (X) := by
      rw[mul_add]
      have : (6 : ℝ) = 4 + 2 := by ring
      rw[this, add_mul, add_mul]
      apply add_le_add
      ring_nf
      rfl
      apply mul_le_mul
      rfl
      exact Real.log_le_log (by positivity) (by linarith)
      rw[← Real.log_one]
      exact Real.log_le_log (by positivity) (by linarith)
      positivity
    exact
      Preorder.le_trans
        (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ +
            ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
          ‖Λ n₁‖ * ‖F (↑n₁ / X)‖)
        (2 * (X * ε * (3 * c₁ + c₂)) * (2 * Real.log X + Real.log 3))
        (6 * (X * ε * (3 * c₁ + c₂)) * Real.log X) largeSumBound4 this

  clear largeSumBound4

  rw[C_eq]
  linear_combination largeSumBoundFinal

theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ (C : ℝ), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
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

  refine ⟨C, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩
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
  ------------+
  |       I₆
I₅|
--σ₂----------σ₁----σ₀----
  |
  |       I₄
  +-----+-----+
              |
              |
            I₃|
              |
              |  I₂
              +----
                  |
                  | I₁
                  |
\end{verbatim}

In the process, we will pick up the residue at $s=1$.
We will do this in several stages.
%%-/

noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-3)..3,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (X : ℝ)
    {σ₀ : ℝ} (σ₀_pos : 0 < σ₀)
    (holoOn : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X) (Icc σ₀ 2 ×ℂ univ \ {1}))
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  sorry

/-%%
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
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₀ 2)×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₀ +
      I₃₇ SmoothingF ε T X σ₀ +
      I₈ SmoothingF ε T X σ₀ +
      I₉ SmoothingF ε X T
      + 𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X := by
  unfold SmoothedChebyshev
  unfold VerticalIntegral'
  rw [verticalIntegral_split_three (a := -T) (b := T)]

  swap
  sorry
  --exact SmoothedChebyshevPull1_aux_integrable ε_pos X σ₀_pos holoOn suppSmoothingF SmoothingFnonneg mass_one



    --VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) 2
  sorry
/-%%
\begin{proof}
\uses{SmoothedChebyshev, RectangleIntegral, ResidueMult, riemannZetaLogDerivResidue}
Pull rectangle contours and evaluate the pole at $s=1$.
\end{proof}
%%-/


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
It remains to estimate all of the integrals...
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

  sorry
/-%%
\begin{proof}
\uses{ChebyshevPsi, SmoothedChebyshevClose, LogDerivZetaBndAlt, ZetaBoxEval, LogDerivZetaBndUniform, LogDerivZetaHolcSmallT, LogDerivZetaHolcLargeT}
  Evaluate the integrals.
\end{proof}
%%-/

-- #check MediumPNT
