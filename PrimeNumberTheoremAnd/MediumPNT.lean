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
    subst C_eq
    simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos, n₀]
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

  have sumΛ : Summable (fun (n : ℕ) ↦ Λ n * F (n / X)) := by
    exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    (hc₂ _ _ (by trivial) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
    (s ∘ Finset.mem_range.2))))))

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
              +---+
                  |
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






theorem realDiff_of_complexDIff {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  -- First, get continuity of f at s from differentiability
  have hf_cont : ContinuousAt f s := DifferentiableAt.continuousAt hf

  -- The function x ↦ s.re + x * I is continuous
  have h_param : ContinuousAt (fun x : ℝ ↦ (s.re + x * I : ℂ)) s.im := by
    apply ContinuousAt.add
    · exact continuousAt_const
    · apply ContinuousAt.mul
      · refine Continuous.continuousAt ?_
        exact continuous_ofReal
      · exact continuousAt_const

  -- Need to show that s.re + s.im * I = s
  have h_eq : (s.re : ℂ) + (s.im : ℂ) * I = s := by
    rw [← Complex.re_add_im s]
    simp

  -- Use the equation to transform the continuity
  rw [← h_eq] at hf_cont
  -- The composition of continuous functions is continuous
  exact ContinuousAt.comp hf_cont h_param

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


theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  have : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta s_ne_one
  have exclude := eventually_ne_nhds s_ne_one
  unfold Filter.Eventually at exclude
  have : AnalyticAt ℂ riemannZeta s := by
      refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
      unfold Filter.Eventually
      have T : {x | (fun x ↦ x ≠ 1) x} ⊆ {x | (fun z ↦ DifferentiableAt ℂ ζ z) x} := by
        intro x
        simp [*]
        push_neg
        intro hyp_x
        exact differentiableAt_riemannZeta hyp_x
      apply mem_nhds_iff.mpr
      use {x | (fun x ↦ x ≠ 1) x}
      constructor
      · exact T
      · constructor
        · exact isOpen_ne
        · exact s_ne_one

  exact this

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


theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
      have U := (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt
      exact U

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
--    (holoOn : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X) (Icc σ₀ 2 ×ℂ univ \ {1}))
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines' σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have : ∀ᵐ t ∂volume, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
    apply Filter.Eventually.of_forall
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
    suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul' (c := c) ?_ this using 2
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
        convert realDiff_of_complexDIff (s := σ₀ + (t : ℂ) * I) this <;> simp
      · convert realDiff_of_complexDIff (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp [σ₀_gt]
    · -- The function x ↦ σ₀ + x * I is continuous
      have h_param : ContinuousAt (fun x : ℝ ↦ (↑σ₀ + ↑x * I : ℂ)) t := by
        apply ContinuousAt.add
        · exact continuousAt_const
        · apply ContinuousAt.mul
          · exact continuous_ofReal.continuousAt
          · exact continuousAt_const

      -- The complex power function z ↦ X^z is continuous (assuming X > 0)
      have h_pow : ContinuousAt (fun z : ℂ ↦ (↑X : ℂ) ^ z) (↑σ₀ + ↑t * I) := by
        apply continuousAt_const_cpow
        simp only [ne_eq, ofReal_eq_zero, s]
        linarith

      -- Composition of continuous functions
      exact ContinuousAt.comp h_pow h_param

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
  sorry
/-%%
\begin{proof}
Use the compactness of the rectangle and the fact that holomorphic functions are continuous.
\end{proof}
%%-/


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
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    refine add_lt_add_of_le_of_lt ?_ ?_
    rfl
    rw[inv_pos, ← Real.log_one]
    apply Real.log_lt_log
    norm_num
    linarith
  have holoIntegrand : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Ico (1 + (Real.log X)⁻¹) 2 ×ℂ univ \ {1}) := by
    unfold SmoothedChebyshevIntegrand HolomorphicOn
    refine DifferentiableOn.mul ?_ ?_
    refine DifferentiableOn.mul ?_ ?_
    have : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)) := by
      refine funext ?_
      intro x
      exact neg_div (ζ x) (ζ' x)
    rw[this]
    refine DifferentiableOn.neg ?_
    unfold DifferentiableOn
    intro s s_location
    rw[Set.mem_diff, Complex.mem_reProdIm] at s_location
    obtain ⟨⟨sReIn, sImIn⟩, sOut⟩ := s_location
    obtain ⟨A, A_inter, Tlb, Tlb_inter, holoOnTemp⟩ := LogDerivZetaHolcLargeT
    have : ∃ (T : ℝ), Tlb < T ∧ |s.im| < T := by
      let T : ℝ := 1 + max Tlb |s.im|
      use T
      have temp : Tlb < T := by
        dsimp[T]
        nth_rewrite 1 [← zero_add Tlb]
        refine add_lt_add_of_lt_of_le ?_ ?_
        norm_num
        exact le_max_left Tlb |s.im|
      have : |s.im| < T := by
        dsimp[T]
        nth_rewrite 1 [← zero_add |s.im|]
        refine add_lt_add_of_lt_of_le ?_ ?_
        norm_num
        exact le_max_right Tlb |s.im|
      exact ⟨temp, this⟩
    obtain ⟨T, Tbounds⟩ := this
    have holoOnTemp : HolomorphicOn (fun s ↦ ζ' s / ζ s) (Ioo (1 - A / Real.log T ^ 9) 2 ×ℂ Ioo (-T) T \ {1}) := by exact holoOnTemp T Tbounds.1
    unfold HolomorphicOn at holoOnTemp
    unfold DifferentiableOn at holoOnTemp
    have sInBiggerBox : s ∈ Ioo (1 - A / Real.log T ^ 9) 2 ×ℂ Ioo (-T) T \ {1} := by
      rw[Set.mem_diff, Complex.mem_reProdIm]
      have temp : s.re ∈ Ioo (1 - A / Real.log T ^ 9) 2 := by
        have : 1 - A / Real.log T ^ 9 < s.re := by
          have : 1 - A / Real.log T ^ 9 < 1 + (Real.log X)⁻¹ := by
            have : 0 < A / Real.log T ^ 9 := by
              refine div_pos ?_ ?_
              exact A_inter.1
              apply pow_pos
              rw[← Real.log_one]
              apply Real.log_lt_log
              positivity
              linarith
            have : 0 < (Real.log X)⁻¹ := by
              rw[inv_pos, ← Real.log_one]
              apply Real.log_lt_log
              positivity
              linarith
            linarith
          exact gt_of_ge_of_gt sReIn.1 this
        exact ⟨this, sReIn.2⟩
      have : s.im ∈ Ioo (-T) T := by
        obtain ⟨_, abs_sIm_bound⟩ := Tbounds
        exact ⟨by exact neg_lt_of_abs_lt abs_sIm_bound, by exact lt_of_abs_lt abs_sIm_bound⟩
      exact ⟨⟨temp, this⟩, sOut⟩
    have : DifferentiableWithinAt ℂ (fun s ↦ ζ' s / ζ s) (Ioo (1 - A / Real.log T ^ 9) 2 ×ℂ Ioo (-T) T \ {1}) s := by exact holoOnTemp s sInBiggerBox
    refine DifferentiableAt.differentiableWithinAt ?_
    have h_open : IsOpen (Ioo (1 - A / Real.log T ^ 9) 2 ×ℂ Ioo (-T) T \ {1}) := by
      apply IsOpen.sdiff
      refine IsOpen.reProdIm (by exact isOpen_Ioo) (by exact isOpen_Ioo)
      exact isClosed_singleton
    have h_mem : s ∈ Ioo (1 - A / Real.log T ^ 9) 2 ×ℂ Ioo (-T) T \ {1} := sInBiggerBox
    exact this.differentiableAt (h_open.mem_nhds h_mem)
    unfold DifferentiableOn
    intro s s_location
    rw[Set.mem_diff, Complex.mem_reProdIm] at s_location
    obtain ⟨⟨sReIn, sImIn⟩, sOut⟩ := s_location
    refine DifferentiableAt.differentiableWithinAt ?_
    have εInter : ε ∈ Ioo 0 1 := by exact ⟨ε_pos, ε_lt_one⟩
    have hs : 0 < s.re := by
      have : 1 + (Real.log X)⁻¹ ≤ s.re := by exact sReIn.1
      linarith
    exact Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF εInter SmoothingFnonneg
      mass_one hs
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    cases' hs with h_in h_not_one
    unfold HPow.hPow instHPow
    simp
    apply DifferentiableAt.const_cpow
    exact differentiableAt_id'
    refine Or.inl ?_
    refine ne_zero_of_re_pos ?_
    rw[ofReal_re]
    positivity
    -- apply add_pos (by positivity)
    -- rw[inv_pos, ← Real.log_one]
    -- apply Real.log_lt_log (by positivity) (by linarith)
  have logX_gt : 1 + (Real.log X)⁻¹ ≤ 2 := by
    sorry
    -- apply add_lt_add_left
    -- apply inv_lt_one_of_pos
    -- rw[Real.log_one]
    -- exact Real.log_pos (by positivity)
    -- exact X_gt

  exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one logX_gt
    suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF


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
  rw[add_right_cancel_iff, ← add_right_inj (1 / (2 * ↑π * I) * -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T), ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
  unfold VIntegral I₂ I₃₇ I₈
  rw[smul_eq_mul, temp, ← add_assoc, ← add_assoc]
  nth_rewrite 2 [div_mul_comm]
  rw[mul_one, ← neg_div, ← mul_neg]
  nth_rewrite 2 [← one_div_mul_eq_div]
  repeat rw[← mul_add]
  let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦ SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
  let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
  have : ∫ (y : ℝ) in -T..T, SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
    ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
    unfold fTempRR
    rw[temp]
  rw[this]
  have : ∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹, SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I) =
    ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
    unfold fTempRR
    rw[Complex.ofReal_neg, neg_mul]
    rfl
  rw[this]
  have : ∫ (t : ℝ) in -T..T, SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
    ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := by rfl
  rw[this]
  have : ∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹, SmoothedChebyshevIntegrand SmoothingF ε X (↑σ + ↑T * I) =
    ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := by rfl
  rw[this]
  repeat rw[← add_assoc]
  have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
    -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
    I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
    ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T = -1 * RectangleIntegral fTempC ((1 : ℝ) + (Real.log X)⁻¹ + T * I) (σ₁ - T * I) := by
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
    have : ∫ (y : ℝ) in -T..T, fTempRR (I * ↑y + ↑(1 + (Real.log X)⁻¹)).re (I * ↑y + ↑(1 + (Real.log X)⁻¹)).im =
      ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by simp
    rw[this]
    have : ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR (I * ↑T + ↑x).re (I * ↑T + ↑x).im =
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := by simp
    rw[this]
    have : ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR (I * ↑(-T) + ↑x).re (I * ↑(-T) + ↑x).im =
      ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by simp
    rw[this]
    ring_nf
  rw[this, neg_one_mul, div_mul_comm, mul_one, ← add_right_inj (RectangleIntegral fTempC (1 + ↑(Real.log X)⁻¹ + ↑T * I) (↑σ₁ - ↑T * I) / (2 * ↑π * I)), ← add_assoc]
  field_simp
  rw[rectangleIntegral_symm]
  have : RectangleIntegral fTempC (↑σ₁ - ↑T * I) (1 + 1 / ↑(Real.log X) + ↑T * I) / (2 * ↑π * I) =
    RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
    unfold RectangleIntegral'
    rw[smul_eq_mul]
    field_simp
  rw[this]

  let holoMatch : ℂ → ℂ := fun z ↦ (fTempC z - (𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) 1 * ↑X) / (z - 1))
  have inv_log_X_pos: 0 < (Real.log X)⁻¹ := by
    rw[inv_pos, ← Real.log_one]
    apply Real.log_lt_log (by positivity) (by linarith)
  have pInRectangleInterior : (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
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
  have holoMatchHoloOn : HolomorphicOn holoMatch (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) \ {1}) := by
    unfold HolomorphicOn holoMatch
    refine DifferentiableOn.sub ?_ ?_
    sorry
    refine DifferentiableOn.mul ?_ ?_
    unfold DifferentiableOn
    intro x x_location
    rw[Set.mem_diff] at x_location
    obtain ⟨xInRect, xOut⟩ := x_location
    sorry
    sorry
  --TODO:
  have holoMatchBddAbove : BddAbove (norm ∘ holoMatch '' (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) \ {1})) := by sorry --should be able to do with lemmas from workshop
  obtain ⟨g, gHolo_Eq⟩ := existsDifferentiableOn_of_bddAbove pInRectangleInterior holoMatchHoloOn holoMatchBddAbove
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
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectangleInterior gHolo gEq


lemma interval_membership (r : ℝ)(a b: ℝ)(h1 : r ∈ Set.Icc (min a b) (max a b)) (h2 : a < b) :
  a ≤ r ∧ r ≤ b := by
  -- Since a < b, we have min(a,b) = a and max(a,b) = b
  have min_eq : min a b = a := min_eq_left (le_of_lt h2)
  have max_eq : max a b = b := max_eq_right (le_of_lt h2)
  rw [min_eq, max_eq] at h1
  rw [← @mem_Icc]
  exact h1

/-%%
\begin{proof}
\uses{SmoothedChebyshev, RectangleIntegral, ResidueMult, riemannZetaLogDerivResidue,
SmoothedChebyshevPull1_aux_integrable, BddAboveOnRect,
I₁, I₂, I₃₇, I₈, I₉}
Pull rectangle contours and evaluate the pole at $s=1$.
\end{proof}
%%-/

/-%%
Next pull contours to another box.
\begin{lemma}[SmoothedChebyshevPull2]\label{SmoothedChebyshevPull2}\lean{SmoothedChebyshevPull2}\leanok
We have that
$$\psi_{\epsilon}(X) =
\mathcal{M}(\widetilde{1_{\epsilon}})(1)
X^{1} +
  \frac{1}{2\pi i}\int_{\text{curve}_2}\frac{-\zeta'(s)}{\zeta(s)}
\mathcal{M}(\widetilde{1_{\epsilon}})(s)
X^{s}ds
$$
\end{lemma}
%%-/

-- use intervalIntegral.integral_add_adjacent_intervals
lemma verticalIntegral_split_three_finite (s a b e σ: ℝ) (f : ℂ → ℝ)(hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ = VIntegral f σ s a + VIntegral f σ a b + VIntegral f σ b e := by sorry

theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by

  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I

  -- the leftmost rectangle is in the locus of holomorphicity
  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
    intro x hx

    constructor
    . -- x in box
      simp only [Rectangle, uIcc] at hx
      rw [Complex.mem_reProdIm] at hx ⊢
      obtain ⟨hx_re, hx_im⟩ := hx
      -- the real part of x is in the interval
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

      -- the imaginary part of x is in the interval
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
    -- x not in {1}
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

  -- split the vertial integral along the vertical line at `x = σ₁` into 3 segments at `a = -3` and `b = 3`
  -- the integral on `(-∞, -3)` is `I_3`
  -- the integral on `(3, ∞)` is `I_7`
  -- the integral on `[-3, 3]` is equal to `-I₅ SmoothingF ε T X σ₁`.
  have splitting : I₃₇ SmoothingF ε T X σ₁ = I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    have := verticalIntegral_split_three_finite (a := -3) (b := 3)
    -- rw [verticalIntegral_split_three (a := -3) (b := 3)]





  -- computing the contour integral from I_3 to I_7 by adding and subtracting the
  -- integral leftmost box
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


  sorry

    -- := by ring
    -- _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    -- - I₆ SmoothingF ε X σ₁ σ₂
    -- + I₅ SmoothingF ε X σ₂
    -- - I₅ SmoothingF ε X σ₂) := by
    --   simp only [I₄, I₅, I₆]
    --   ring_nf
    --   simp
      -- dsimp [RectangleIntegral]

/-%%
\begin{proof}\uses{HolomorphicOn.vanishesOnRectangle, I₃, I₄, I₅, I₆, I₇, I₃₇}
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

/-%%
\begin{proof}
\uses{MellinOfSmooth1c}
Unfold the definitions and apply Lemma \ref{MellinOfSmooth1c}.
\end{proof}
%%-/

/-%%
It remains to estimate all of the integrals.
%%-/

/-%%
This auxiliary lemme is useful for what follows.
\begin{lemma}[IBound_aux1]\label{IBound_aux1}\lean{IBound_aux1}\leanok
Given $k>0$, there exists $C>0$ so that for all $T>3$,
$$
\log T ^ k \le C \cdot T.
$$
\end{lemma}
%%-/
lemma IBound_aux1 {k : ℝ} (k_pos : 0 < k) : ∃ C > 0,
    ∀ {T : ℝ} (T_gt : 3 < T), Real.log T ^ k ≤ C * T := by
    sorry
/-%%
\begin{proof}
Elementary. Use `isLittleO_log_rpow_rpow_atTop` in Mathlib.
\end{proof}
%%-/

/-%%
\begin{lemma}[I1Bound]\label{I1Bound}\lean{I1Bound}\leanok
We have that
$$
\left|I_{1}(\nu, \epsilon, X, T)\
\right| \ll {X \over \epsilon T}
.
$$
Same with $I_9$.
\end{lemma}
%%-/
theorem I1Bound :
    ∃ C > 0, ∀ {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_gt : 3 < T) {σ₁ : ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) ,
    ‖I₁ SmoothingF ε X T‖ ≤ C * X / (ε * T) := by
  sorry

theorem I9Bound :
    ∃ C > 0, ∀ {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_gt : 3 < T) {σ₁ : ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) ,
    ‖I₉ SmoothingF ε X T‖ ≤ C * X / (ε * T) := by
  sorry

/-%%
\begin{proof}\uses{MellinOfSmooth1b, dlog_riemannZeta_bdd_on_vertical_lines', I₁}
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
$$
\leq
\frac{1}{2\pi}
\left|
 \int_{-\infty}^{-T}
C
 \frac{C'}{\epsilon|\sigma_0 + t i|^2}
X^{\sigma_0}
\ dt
\right|
$$
where we used Theorems \ref{MellinOfSmooth1b} and
\ref{dlog_riemannZeta_bdd_on_vertical_lines'}. Continuing the calculation, we have
$$
\leq
C'' {X^{\sigma_0}\over \epsilon}
\int_{-\infty}^{-T}
\frac{1}{t^2}
\ dt
$$
$$
\leq
C'''  {X\over \epsilon T}
,
$$
where we used that $\sigma_0=1+1/\log X$, and $X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
\end{proof}
%%-/

/-%%
\begin{lemma}[I2Bound]\label{I2Bound}\lean{I2Bound}\leanok
We have that
$$
\left|I_{2}(\nu, \epsilon, X, T)\right| \ll {X\over \epsilon T}
.
$$
Same with $I_8$.
\end{lemma}
%%-/
lemma I2Bound : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioo 0 (1/2)), ∀ {SmoothingF : ℝ → ℝ}
    (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    {T : ℝ} (T_gt : 3 < T)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF),
    let σ₁ : ℝ := 1 - A / (Real.log X) ^ 9
    ‖I₂ SmoothingF ε X T σ₁‖ ≤ C * X / (ε * T) := by
  sorry

lemma I8Bound : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioo 0 (1/2)), ∀ {SmoothingF : ℝ → ℝ}
    (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    {T : ℝ} (T_gt : 3 < T)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF),
    let σ₁ : ℝ := 1 - A / (Real.log X) ^ 9
    ‖I₈ SmoothingF ε X T σ₁‖ ≤ C * X / (ε * T) := by
  sorry
/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBndUniform, I₂}
Unfold the definitions and apply the triangle inequality.
$$
\left|I_{2}(\nu, \epsilon, X, T, \sigma_1)\right| =
\left|\frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
\left(\frac{-\zeta'}\zeta(\sigma - T i) \right)
\mathcal M(\widetilde 1_\epsilon)(\sigma - T i)
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
C'' \cdot {X\log T^9 \over \epsilon T^2}
,
$$
where we used Theorems \ref{MellinOfSmooth1b} and \ref{LogDerivZetaBndUniform}, and the fact that
$X^\sigma \le X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
Since $T>3$, we have $\log T^9 \leq C''' T$.
\end{proof}
%%-/

/-%%
\begin{lemma}[I3Bound]\label{I3Bound}\lean{I3Bound}\leanok
We have that
$$
\left|I_{3}(\nu, \epsilon, X, T)\right| \ll {X\over \epsilon}\, X^{-\frac{A}{(\log T)^9}}
.
$$
Same with $I_7$.
\end{lemma}
%%-/
lemma I3Bound : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioo 0 (1/2)), ∀ {SmoothingF : ℝ → ℝ}
    (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    {T : ℝ} (T_gt : 3 < T)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF),
    let σ₁ : ℝ := 1 - A / (Real.log X) ^ 9
    ‖I₃ SmoothingF ε X T σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε  := by
  sorry

lemma I7Bound : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioo 0 (1/2)), ∀ {SmoothingF : ℝ → ℝ}
    (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    {T : ℝ} (T_gt : 3 < T)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF),
    let σ₁ : ℝ := 1 - A / (Real.log X) ^ 9
    ‖I₇ SmoothingF ε X T σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε  := by
  sorry
/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBnd, I₃}
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
\left|I_{4}(\nu, \epsilon, X, \sigma_1, \sigma_2)\right| \ll {X\over \epsilon}\,
 X^{-\frac{A}{(\log T)^9}}
.
$$
Same with $I_6$.
\end{lemma}
%%-/
lemma I4Bound : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioo 0 (1/2)) (σ₂ : ℝ) (_ : σ₂ ∈ Ioo 0 1),
    ∀ {SmoothingF : ℝ → ℝ}
    (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    {T : ℝ} (T_gt : 3 < T)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF),
    let σ₁ : ℝ := 1 - A / (Real.log X) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  sorry

lemma I6Bound : ∃ (C : ℝ) (_ : 0 < C) (A : ℝ) (_ : A ∈ Ioo 0 (1/2)) (σ₂ : ℝ) (_ : σ₂ ∈ Ioo 0 1),
    ∀ {SmoothingF : ℝ → ℝ}
    (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    {T : ℝ} (T_gt : 3 < T)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF),
    let σ₁ : ℝ := 1 - A / (Real.log X) ^ 9
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  sorry
/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBndAlt, I₄}
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
\left|I_{5}(\nu, \epsilon, X, \sigma_2)\right| \ll {X^{\sigma_2} \over \epsilon}.
$$
\end{lemma}
%%-/
lemma I5Bound : ∃ (C : ℝ) (_ : 0 < C) (σ₂ : ℝ) (_ : σ₂ ∈ Ioo 0 1), ∀ {SmoothingF : ℝ → ℝ}
    (X : ℝ) (X_gt : 3 < X) {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by
  sorry
/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaHolcSmallT, I₅}
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

  sorry
/-%%
\begin{proof}
\uses{ChebyshevPsi, SmoothedChebyshevClose, LogDerivZetaBndAlt, ZetaBoxEval, LogDerivZetaBndUniform, LogDerivZetaHolcSmallT, LogDerivZetaHolcLargeT,
SmoothedChebyshevPull1, SmoothedChebyshevPull2}
  Evaluate the integrals.
\end{proof}
%%-/

-- #check MediumPNT
