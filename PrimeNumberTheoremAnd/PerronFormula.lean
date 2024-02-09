import Mathlib.Analysis.Calculus.ContDiff.Basic
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Uniformly
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.Asymptotics
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.Wiener

open Asymptotics Complex ComplexConjugate Topology Filter Real MeasureTheory Set

/-%%
In this section, we prove the Perron formula, which plays a key role in our proof of Mellin inversion.
%%-/

/-%%
The following is preparatory material used in the proof of the Perron formula, see Lemma \ref{formulaLtOne}.
%%-/

/-%%
TODO: move to general section.
\begin{lemma}[zeroTendstoDiff]\label{zeroTendstoDiff}\lean{zeroTendstoDiff}\leanok
If the limit of $0$ is $L₁ - L₂$, then $L₁ = L₂$.
\end{lemma}
%%-/
lemma zeroTendstoDiff (L₁ L₂ : ℂ) (f : ℝ → ℂ) (h : ∀ᶠ T in atTop,  f T = 0)
    (h' : Tendsto f atTop (𝓝 (L₂ - L₁))) : L₁ = L₂ := by
  rw [← zero_add L₁, ← @eq_sub_iff_add_eq]
  apply tendsto_nhds_unique (EventuallyEq.tendsto h) h'
/-%%
\begin{proof}\leanok
Obvious.
\end{proof}
%%-/

/-%%
TODO: Move this to general section.
\begin{lemma}[RectangleIntegral_tendsTo_VerticalIntegral]\label{RectangleIntegral_tendsTo_VerticalIntegral}\lean{RectangleIntegral_tendsTo_VerticalIntegral}\leanok
\uses{RectangleIntegral}
Let $\sigma,\sigma' ∈ \mathbb{R}$, and $f : \mathbb{C} \to \mathbb{C}$ such that
the vertical integrals $\int_{(\sigma)}f(s)ds$ and $\int_{(\sigma')}f(s)ds$ exist and
the horizontal integral $\int_{(\sigma)}^{\sigma'}f(x + yi)dx$ vanishes as $y \to \pm \infty$.
Then the limit of rectangle integrals
$$\lim_{T\to\infty}\int_{\sigma-iT}^{\sigma'+iT}f(s)ds =
\int_{(\sigma')}f(s)ds - \int_{(\sigma)}f(s)ds.$$
\end{lemma}
%%-/
lemma RectangleIntegral_tendsTo_VerticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) => ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) => ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ - I * T) (σ' + I * T)) atTop
      (𝓝 (VerticalIntegral f σ' - VerticalIntegral f σ)) := by
/-%%
\begin{proof}\leanok
Almost by definition.
%%-/
  have h_lower (x : ℝ) : (σ - I * x).im = -x := by simp
  have h_upper (x : ℝ) : (σ' + I * x).im = x := by simp
  have h_left (x : ℝ) : (σ - I * x).re = σ := by simp
  have h_right (x : ℝ) : (σ' + I * x).re = σ' := by simp
  simp_rw [RectangleIntegral, h_left, h_right, h_lower, h_upper]
  apply Tendsto.sub
  · rewrite [← zero_add (VerticalIntegral _ _), ← zero_sub_zero]
    apply Tendsto.add <| Tendsto.sub (hbot.comp tendsto_neg_atTop_atBot) htop
    exact (intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id).const_smul I
  · exact (intervalIntegral_tendsto_integral hleft tendsto_neg_atTop_atBot tendsto_id).const_smul I
--%%\end{proof}

/-%%
\begin{lemma}[RectangleIntegral_tendsTo_UpperU]\label{RectangleIntegral_tendsTo_UpperU}\lean{RectangleIntegral_tendsTo_UpperU}\leanok
Let $\sigma,\sigma' ∈ \mathbb{R}$, and $f : \mathbb{C} \to \mathbb{C}$ such that
the vertical integrals $\int_{(\sigma)}f(s)ds$ and $\int_{(\sigma')}f(s)ds$ exist and
the horizontal integral $\int_{(\sigma)}^{\sigma'}f(x + yi)dx$ vanishes as $y \to \pm \infty$.
Then the limit of rectangle integrals
$$\int_{\sigma+iT}^{\sigma'+iU}f(s)ds$$
as $U\to\infty$ is the ``UpperUIntegral'' of $f$.
\end{lemma}
%%-/
lemma RectangleIntegral_tendsTo_UpperU {σ σ' T : ℝ} {f : ℂ → ℂ}
    (htop : Tendsto (fun (y : ℝ) => ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ + I * T) (σ' + I * U)) atTop
      (𝓝 (UpperUIntegral f σ σ' T)) := by
  sorry
/-%%
\begin{proof}
\uses{RectangleIntegral, UpperUIntegral}
Almost by definition.
\end{proof}
%%-/

/-%%
\begin{lemma}[RectangleIntegral_tendsTo_LowerU]\label{RectangleIntegral_tendsTo_LowerU}\lean{RectangleIntegral_tendsTo_LowerU}\leanok
Let $\sigma,\sigma' ∈ \mathbb{R}$, and $f : \mathbb{C} \to \mathbb{C}$ such that
the vertical integrals $\int_{(\sigma)}f(s)ds$ and $\int_{(\sigma')}f(s)ds$ exist and
the horizontal integral $\int_{(\sigma)}^{\sigma'}f(x + yi)dx$ vanishes as $y \to -\infty$.
Then the limit of rectangle integrals
$$\int_{\sigma-iU}^{\sigma'-iT}f(s)ds$$
as $U\to\infty$ is the ``LowerUIntegral'' of $f$.
\end{lemma}
%%-/
lemma RectangleIntegral_tendsTo_LowerU {σ σ' T : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) => ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ - I * U) (σ' - I * T)) atTop
      (𝓝 (LowerUIntegral f σ σ' T)) := by
  sorry
/-%%
\begin{proof}
\uses{RectangleIntegral, LowerUIntegral}
Almost by definition.
\end{proof}
%%-/


/-%%
TODO : Move to general section
\begin{lemma}[limitOfConstant]\label{limitOfConstant}\lean{limitOfConstant}\leanok
Let $a:\R\to\C$ be a function, and let $\sigma>0$ be a real number. Suppose that, for all
$\sigma, \sigma'>0$, we have $a(\sigma')=a(\sigma)$, and that
$\lim_{\sigma\to\infty}a(\sigma)=0$. Then $a(\sigma)=0$.
\end{lemma}
%%-/
lemma limitOfConstant {a : ℝ → ℂ} {σ : ℝ} (σpos : 0 < σ)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : 0 < σ') (_ : 0 < σ''), a σ' = a σ'')
    (ha' : Tendsto a atTop (𝓝 0)) : a σ = 0 := by
/-%%
\begin{proof}\leanok\begin{align*}
\lim_{\sigma'\to\infty}a(\sigma) &= \lim_{\sigma'\to\infty}a(\sigma') \\
%%-/
  have := eventuallyEq_of_mem (mem_atTop σ) fun σ' h ↦ ha σ' σ (σpos.trans_le h) σpos
--%% &= 0
  exact tendsto_const_nhds_iff.mp (ha'.congr' this)
--%%\end{align*}\end{proof}

/-%%
\begin{lemma}[limitOfConstantLeft]\label{limitOfConstantLeft}\lean{limitOfConstantLeft}\leanok
Let $a:\R\to\C$ be a function, and let $\sigma<-3/2$ be a real number. Suppose that, for all
$\sigma, \sigma'>0$, we have $a(\sigma')=a(\sigma)$, and that
$\lim_{\sigma\to-\infty}a(\sigma)=0$. Then $a(\sigma)=0$.
\end{lemma}
%%-/
lemma limitOfConstantLeft {a : ℝ → ℂ} {σ : ℝ} (σlt : σ ≤ -3/2)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : σ' ≤ -3/2) (_ : σ'' ≤ -3/2), a σ' = a σ'')
    (ha' : Tendsto a atBot (𝓝 0)) : a σ = 0 := by
/-%%
\begin{proof}\leanok
\begin{align*}
\lim_{\sigma'\to-\infty}a(\sigma) &= \lim_{\sigma'\to-\infty}a(\sigma') \\
%%-/
  have := eventuallyEq_of_mem (mem_atBot (-3/2)) fun σ' h ↦ ha σ' σ h σlt
--%% &= 0
  exact tendsto_const_nhds_iff.mp (ha'.congr' this)
--%%\end{align*}\end{proof}

/-%%
\begin{lemma}[tendsto_rpow_atTop_nhds_zero_of_norm_lt_one]\label{tendsto_rpow_atTop_nhds_zero_of_norm_lt_one}\lean{tendsto_rpow_atTop_nhds_zero_of_norm_lt_one}\leanok
Let $x>0$ and $x<1$. Then
$$\lim_{\sigma\to\infty}x^\sigma=0.$$
\end{lemma}
%%-/
lemma tendsto_rpow_atTop_nhds_zero_of_norm_lt_one {x : ℝ}  (xpos : 0 < x) (x_lt_one : x < 1) (C : ℝ) :
    Tendsto (fun (σ : ℝ) => x ^ σ * C) atTop (𝓝 0) := by
/-%%
\begin{proof}\leanok
Standard.
%%-/
  have := Tendsto.mul_const C (tendsto_rpow_atTop_of_base_lt_one x (by linarith) x_lt_one)
  simpa only [rpow_eq_pow, zero_mul] using this
--%%\end{proof}

/-%%
\begin{lemma}[tendsto_rpow_atTop_nhds_zero_of_norm_gt_one]\label{tendsto_rpow_atTop_nhds_zero_of_norm_gt_one}\lean{tendsto_rpow_atTop_nhds_zero_of_norm_gt_one}\leanok
Let $x>1$. Then
$$\lim_{\sigma\to-\infty}x^\sigma=0.$$
\end{lemma}
%%-/
lemma tendsto_rpow_atTop_nhds_zero_of_norm_gt_one {x : ℝ} (x_gt_one : 1 < x) (C : ℝ) :
    Tendsto (fun (σ : ℝ) => x ^ σ * C) atBot (𝓝 0) := by
  have := (zero_lt_one.trans x_gt_one)
  have h := tendsto_rpow_atTop_nhds_zero_of_norm_lt_one (inv_pos.mpr this) (inv_lt_one x_gt_one) C
  convert (h.comp tendsto_neg_atBot_atTop) using 1
  ext; simp only [this.le, inv_rpow, Function.comp_apply, rpow_neg, inv_inv]

/-%%
\begin{proof}
Standard.
\end{proof}
%%-/

-- From PR #9598
/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

-- From PR #9598
/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  rw [← @preimage_equivRealProd_prod s t, ← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

-- From PR #9598
/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert prod_subset_prod_iff
  exact reProdIm_subset_iff

-- Exists in Mathlib; need to update version
/-- The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
noncomputable def equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (Real.sqrt 2) equivRealProd_apply_le' fun p =>
    abs_le_sqrt_two_mul_max (equivRealProd.symm p)

namespace Perron

variable {x σ σ' σ'' T : ℝ}

noncomputable abbrev f (x : ℝ) := fun (s : ℂ) => x ^ s / (s * (s + 1))

/-%%
TODO: Change this to the statement of `isHolomorphicOn2` and refactor.
\begin{lemma}[isHolomorphicOn]\label{isHolomorphicOn}\lean{Perron.isHolomorphicOn}\leanok
Let $x>0$. Then the function $f(s) = x^s/(s(s+1))$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
\end{lemma}
%%-/
lemma isHolomorphicOn (xpos : 0 < x) : HolomorphicOn (f x) {0, -1}ᶜ := by
/-%%
\begin{proof}\leanok
Composition of differentiabilities.
%%-/
  unfold f
  simp_rw [Complex.cpow_def_of_ne_zero <| ofReal_ne_zero.mpr <| ne_of_gt xpos]
  apply DifferentiableOn.div <| DifferentiableOn.cexp <| DifferentiableOn.const_mul differentiableOn_id _
  · exact DifferentiableOn.mul differentiableOn_id <| DifferentiableOn.add_const differentiableOn_id 1
  · intro x hx
    obtain ⟨h0, h1⟩ := not_or.mp hx
    exact mul_ne_zero h0 <| add_ne_add_left 1 |>.mpr h1 |>.trans_eq (add_left_neg 1)
--%%\end{proof}

/-%%
\begin{lemma}[integralPosAux]\label{integralPosAux}\lean{Perron.integralPosAux}\leanok
The integral
$$\int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt$$
is positive (and hence convergent - since a divergent integral is zero in Lean, by definition).
\end{lemma}
%%-/
lemma integralPosAux : 0 < ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| := by
/-%%
\begin{proof}\leanok
This integral is between $\frac{1}{2}$ and $1$ of the integral of $\frac{1}{1+t^2}$, which is $\pi$.
%%-/
  simp_rw [fun (t : ℝ) ↦ abs_of_pos (show sqrt (1 + t^2) * sqrt (2 + t^2) > 0 by positivity)]
  apply (half_pos <| pi_pos.trans_eq integral_volume_one_div_one_add_sq.symm).trans_le
  rewrite [← integral_div]

  have h_int1 : Integrable fun (t : ℝ) ↦ 1 / (1 + t^2) := Classical.byContradiction fun hc ↦
    (integral_volume_one_div_one_add_sq.trans_ne pi_ne_zero) (integral_undef hc)
  have h_int2 : Integrable fun (t : ℝ) ↦ 1 / (1 + t^2) / 2 := Integrable.div_const h_int1 2

  have h_mono1 (t : ℝ): 1 / (1 + t^2) / 2 ≤ 1 / (sqrt (1 + t^2) * sqrt (2 + t^2)) := by
    apply (div_div _ _ _).trans_le
    gcongr 1 / ?_
    calc
      _ ≤ sqrt (2 + t^2) * sqrt (2 + t^2) := by gcongr; apply Real.sqrt_le_sqrt; nlinarith
      _ = 2 + t^2 := by rw [← Real.sqrt_mul, sqrt_mul_self] <;> positivity
      _ ≤ _ := by nlinarith
  have h_mono2 (t : ℝ) : 1 / (sqrt (1 + t^2) * sqrt (2 + t^2)) ≤ 1 / (1 + t^2) := by
    gcongr 1 / ?_
    calc
      _ = sqrt (1 + t^2) * sqrt (1 + t^2) := by rw [← Real.sqrt_mul, sqrt_mul_self] <;> positivity
      _ ≤ _ := by gcongr; apply Real.sqrt_le_sqrt; nlinarith

  refine integral_mono h_int2 (Integrable.mono h_int1 ?_ ?_) h_mono1
  · refine (measurable_const.div <| Measurable.mul ?_ ?_).aestronglyMeasurable
    all_goals exact (measurable_const.add <| measurable_id'.pow_const 2).sqrt
  · refine ae_of_all _ (fun x ↦ ?_)
    repeat rewrite [norm_of_nonneg (by positivity)]
    exact h_mono2 x
--%%\end{proof}

/-%%
\begin{lemma}[vertIntBound]\label{vertIntBound}\lean{Perron.vertIntBound}\leanok
Let $x>0$ and $\sigma>1$. Then
$$\left|
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt.$$
\end{lemma}
%%-/

lemma vertIntBound (xpos : 0 < x) (σ_gt_one : 1 < σ) :
    Complex.abs (VerticalIntegral (f x) σ)
      ≤ x ^ σ * ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| := by
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (Complex.abs (σ + t * I) * Complex.abs (σ + t * I + 1)) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| :=
        mul_le_mul_of_nonneg_left ?_ (rpow_nonneg xpos.le _)
  · simp only [VerticalIntegral, smul_eq_mul, map_mul, abs_I, one_mul, Complex.norm_eq_abs]
  · congr with t
    rw [norm_div, Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos xpos, add_re, ofReal_re,
      re_ofReal_mul, I_re, mul_zero, add_zero]
  · simp_rw [div_eq_mul_inv, integral_mul_left, one_mul, Complex.norm_eq_abs, map_mul]
  clear! x
  -- Note: I didn't try to prove this because the result is trivial if it isn't true.
  by_cases hint : Integrable fun (a : ℝ) => 1 / (Complex.abs (σ + ↑a * I) * Complex.abs (↑σ + ↑a * I + 1))
  swap
  · rw [integral_undef hint]
    apply integral_nonneg
    rw [Pi.le_def]
    intro t
    simp only [Pi.zero_apply, one_div, inv_nonneg, abs_nonneg]
  apply integral_mono hint
  · have := integralPosAux
    contrapose! this
    have := integral_undef this
    simp_rw [this, le_rfl]
  rw [Pi.le_def]
  intro t
  rw [abs_eq_self.mpr (by positivity)]
  simp only [Complex.abs_apply]
  gcongr
  · apply sqrt_le_sqrt
    rw [normSq_add_mul_I, add_le_add_iff_right]
    exact one_le_pow_of_one_le σ_gt_one.le _
  · apply sqrt_le_sqrt
    rw [add_right_comm, ← ofReal_one, ← ofReal_add, normSq_add_mul_I, add_le_add_iff_right]
    nlinarith

/-%%
\begin{proof}\leanok
\uses{VerticalIntegral}
Triangle inequality and pointwise estimate.
\end{proof}
%%-/

/-%%
\begin{lemma}[vertIntBoundLeft]\label{vertIntBoundLeft}\lean{Perron.vertIntBoundLeft}\leanok
Let $x>1$ and $\sigma<-3/2$. Then
$$\left|
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt.$$
\end{lemma}
%%-/

lemma vertIntBoundLeft (x_gt_zero : 0 < x) :
    ∃ C > 0, ∀ (σ : ℝ) (_ : σ < -3 / 2), Complex.abs (VerticalIntegral' (f x) σ) ≤ x ^ σ * C := by
  sorry
/-%%
\begin{proof}
\uses{VerticalIntegral}
Triangle inequality and pointwise estimate.
\end{proof}
%%-/


/-%%
TODO : Remove this lemma if it's not needed
\begin{lemma}[vertIntBound2]\label{vertIntBound2}\lean{Perron.vertIntBound2}\leanok
Let $x>0$ and $\sigma\in \R$, $\sigma \ne 0, -1$. Then
$$\left|
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \ll_\sigma x^\sigma.$$
Note that the implied constant here does depend on $\sigma$. (So it's not as useful a lemma.)
\end{lemma}
%%-/
lemma vertIntBound2 (xpos : 0 < x) (σ_ne_zero : σ ≠ 0) (σ_ne_neg_one : σ ≠ -1) :
    ∃ C > 0, Complex.abs (VerticalIntegral (f x) σ) ≤ x ^ σ * C := by
  sorry
/-%%
\begin{proof}
\uses{vertIntBound}
Similar to ``vertIntBound''.
\end{proof}
%%-/

lemma map_conj (hx : 0 ≤ x) (s : ℂ) : f x (conj s) = conj (f x s) := by
  simp? [f] says simp only [f, map_div₀, map_mul, map_add, map_one]
  congr
  rw [cpow_conj, Complex.conj_ofReal]
  · rewrite [Complex.arg_ofReal_of_nonneg hx]
    exact pi_ne_zero.symm

theorem isTheta_uniformlyOn_uIcc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 (uIcc σ' σ'') ×ˢ (atBot ⊔ atTop)]
    ((fun y ↦ 1 / y^2) ∘ Prod.snd) := by
  have hx : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt xpos)
  refine IsTheta.div ?_ ?_
  · simp_rw [cpow_add _ _ hx]
    conv => { rhs; ext; rw [show (1 : ℝ) = 1 * 1 by norm_num] }
    refine IsTheta.mul ?_ ?_
    · have hcont : ContinuousOn (fun (σ : ℝ) ↦ (x : ℂ) ^ (σ : ℂ)) (uIcc σ' σ'') :=
        continuousOn_const.cpow continuous_ofReal.continuousOn fun _ _ ↦ Or.inl xpos
      refine hcont.const_isThetaUniformlyOn_isCompact isCompact_uIcc (by norm_num) (fun i _ ↦ ?_) _
      rewrite [← Complex.ofReal_cpow (le_of_lt xpos), ofReal_ne_zero]
      exact ne_of_gt (rpow_pos_of_pos xpos _)
    · -- in mathlib this `simp` closes the goal, but here it's nonterminal as `norm_one` fails to apply
      simp? [← isTheta_norm_left, Complex.abs_cpow_of_ne_zero hx, arg_ofReal_of_nonneg xpos.le] says
        simp only [← isTheta_norm_left, Complex.norm_eq_abs,
          Complex.abs_cpow_of_ne_zero hx, abs_ofReal, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, rpow_zero, arg_ofReal_of_nonneg xpos.le, mul_im, add_zero,
          zero_mul, Real.exp_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, norm_one]
      conv => { lhs; ext; rw [norm_one] }
  · set l := 𝓟 (uIcc σ' σ'') ×ˢ (atBot ⊔ atTop : Filter ℝ) with hl
    have h_yI : (fun ((_σ, y) : ℝ × ℝ) ↦ y * I) =Θ[l] Prod.snd :=
      isTheta_of_norm_eventuallyEq <| eventuallyEq_of_mem univ_mem fun _ _ ↦ by simp
    have h_c {c : ℂ} : (fun (_ : ℝ × ℝ) => c) =o[l] Prod.snd := by
      rewrite [hl, Filter.prod_sup, isLittleO_sup]
      exact ⟨isLittleO_const_snd_atBot c _, isLittleO_const_snd_atTop c _⟩
    have h_fst : (fun (σy : ℝ × ℝ) ↦ (σy.1 : ℂ)) =o[l]
        fun (_σ, y) => y * I :=
      continuous_ofReal.continuousOn.const_isBigOUniformlyOn_isCompact isCompact_uIcc
        (by norm_num : ‖(1 : ℂ)‖ ≠ 0) _ |>.trans_isLittleO (h_c.trans_isTheta h_yI.symm)
    have h_σ_yI : (fun (σy : ℝ × ℝ) ↦ σy.1 + σy.2 * I) =Θ[l] fun ((_σ, y) : ℝ × ℝ) => y * I := by
      conv => { lhs; ext; rewrite [add_comm] }
      exact IsTheta.add_isLittleO h_fst
    simp_rw [sq]
    refine (h_σ_yI.trans h_yI).mul ?_
    calc
      _ =Θ[l] (fun (σy : ℝ × ℝ) ↦ σy.1 + σy.2 * I) := by
        refine IsTheta.add_isLittleO <| (h_c (c := (1 : ℂ))).trans_isTheta <| h_yI.symm.trans ?_
        conv => { rhs; ext; rw [add_comm] }
        refine (IsTheta.add_isLittleO h_fst).symm
      _ =Θ[l] _ := h_σ_yI.trans h_yI

theorem isTheta_uniformlyOn_uIoc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 (uIoc σ' σ'') ×ˢ (atBot ⊔ atTop)]
    fun (σ, y) ↦ 1 / y^2 := by
  refine (𝓟 (uIoc σ' σ'')).eq_or_neBot.casesOn (fun hbot ↦ by simp [hbot]) (fun _ ↦ ?_)
  haveI : NeBot (atBot (α := ℝ) ⊔ atTop) := sup_neBot.mpr (Or.inl atBot_neBot)
  exact (isTheta_uniformlyOn_uIcc xpos σ' σ'').mono (by simpa using Ioc_subset_Icc_self)

lemma isTheta (xpos : 0 < x) :
    ((fun (y : ℝ) ↦ f x (σ + y * I)) =Θ[atBot] fun (y : ℝ) ↦ 1 / y^2) ∧
    (fun (y : ℝ) ↦ f x (σ + y * I)) =Θ[atTop] fun (y : ℝ) ↦ 1 / y^2 :=
  isTheta_sup.mp <| isTheta_of_isThetaUniformly (isTheta_uniformlyOn_uIcc xpos σ σ) left_mem_uIcc

/-%%
\begin{lemma}[isIntegrable]\label{isIntegrable}\lean{Perron.isIntegrable}\leanok
Let $x>0$ and $\sigma\in\R$. Then
$$\int_{\R}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}d\sigma$$
is integrable.
\end{lemma}
%%-/
lemma isIntegrable (xpos : 0 < x) (σ_ne_zero : σ ≠ 0) (σ_ne_neg_one : σ ≠ -1) :
    Integrable fun (t : ℝ) ↦ f x (σ + t * I) := by
/-%%
\begin{proof}\uses{isHolomorphicOn}\leanok
By \ref{isHolomorphicOn}, $f$ is continuous, so it is integrable on any interval.
%%-/
  have : Continuous (fun (y : ℝ) ↦ f x (σ + y * I)) := by
    refine (isHolomorphicOn xpos).continuousOn.comp_continuous (by continuity) fun x ↦ not_or.mpr ?_
    simp [Complex.ext_iff, σ_ne_zero, σ_ne_neg_one]
--%% Also, $|f(x)| = \Theta(x^{-2})$ as $x\to\infty$,
  refine this.locallyIntegrable.integrable_of_isBigO_atTop_of_norm_eq_norm_neg
    ?_ (isTheta xpos).2.isBigO ?_
--%% and $|f(-x)| = \Theta(x^{-2})$ as $x\to\infty$.
  · refine univ_mem' fun y ↦ ?_
    show ‖f x (↑σ + ↑y * I)‖ = ‖f x (↑σ + ↑(-y) * I)‖
    have : (↑σ + ↑(-y) * I) = conj (↑σ + ↑y * I) := Complex.ext (by simp) (by simp)
    simp_rw [this, map_conj xpos.le, Complex.norm_eq_abs, abs_conj]
--%% Since $g(x) = x^{-2}$ is integrable on $[a,\infty)$ for any $a>0$, we conclude.
  · refine ⟨Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num)
      (show (0 : ℝ) < 1 by norm_num) |>.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi⟩
    beta_reduce
    rw [rpow_neg (show (0 : ℝ) < 1 by norm_num |>.trans hy |>.le), inv_eq_one_div, rpow_two]
--%%\end{proof}

theorem horizontal_integral_isBigO
    {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    (fun (y : ℝ) => ∫ (σ : ℝ) in σ'..σ'', f x (σ + y * I) ∂μ) =O[atBot ⊔ atTop]
    fun y ↦ 1 / y^2 := by
  let g := fun ((σ, y) : ℝ × ℝ) ↦ f x (σ + y * I)
  calc
    _ =Θ[atBot ⊔ atTop] fun (y : ℝ) => ∫ (σ : ℝ) in uIoc σ' σ'', g (σ, y) ∂μ :=
        isTheta_of_norm_eventuallyEq <| eventuallyEq_of_mem univ_mem fun _ _ ↦
          intervalIntegral.norm_intervalIntegral_eq _ _ _ _
    _ =O[atBot ⊔ atTop] _ :=
      (isTheta_uniformlyOn_uIoc xpos σ' σ'').isBigO.set_integral_isBigO
        measurableSet_uIoc measure_Ioc_lt_top

/-%%
\begin{lemma}[tendsto_zero_Lower]\label{tendsto_zero_Lower}\lean{Perron.tendsto_zero_Lower}\leanok
Let $x>0$ and $\sigma',\sigma''\in\R$. Then
$$\int_{\sigma'}^{\sigma''}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}d\sigma$$
goes to $0$ as $t\to-\infty$.
\end{lemma}
%%-/
lemma tendsto_zero_Lower (xpos : 0 < x) (σ' σ'' : ℝ) :
    Tendsto (fun (t : ℝ) => ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atBot (𝓝 0) := by
/-%%
\begin{proof}\leanok
The numerator is bounded and the denominator tends to infinity.
\end{proof}
%%-/
  have hcast : (fun (y : ℝ) ↦ 1 / y ^ 2) =ᶠ[atBot] fun y ↦ (-y) ^ (-2 : ℝ) := by
    filter_upwards [Iic_mem_atBot 0]
    intro y hy
    rw [rpow_neg (neg_nonneg.mpr hy), inv_eq_one_div, rpow_two, neg_sq]
  exact isBigO_sup.mp (horizontal_integral_isBigO xpos σ' σ'' volume)
    |>.1.trans_eventuallyEq hcast |>.trans_tendsto
    <| tendsto_rpow_neg_atTop (by norm_num) |>.comp tendsto_neg_atBot_atTop

/-%%
\begin{lemma}[tendsto_zero_Upper]\label{tendsto_zero_Upper}\lean{Perron.tendsto_zero_Upper}\leanok
Let $x>0$ and $\sigma',\sigma''\in\R$. Then
$$\int_{\sigma'}^{\sigma''}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}d\sigma$$
goes to $0$ as $t\to\infty$.
\end{lemma}
%%-/
lemma tendsto_zero_Upper (xpos : 0 < x) (σ' σ'' : ℝ) :
    Tendsto (fun (t : ℝ) => ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atTop (𝓝 0) := by
/-%%
\begin{proof}\leanok
The numerator is bounded and the denominator tends to infinity.
\end{proof}
%%-/
  have hcast : (fun (y : ℝ) ↦ 1 / y ^ 2) =ᶠ[atTop] fun y ↦ y ^ (-2 : ℝ) := by
    filter_upwards [Ici_mem_atTop 0]
    intro y hy
    rw [rpow_neg hy, inv_eq_one_div, rpow_two]
  refine isBigO_sup.mp (horizontal_integral_isBigO xpos σ' σ'' volume)
    |>.2.trans_eventuallyEq hcast |>.trans_tendsto <| tendsto_rpow_neg_atTop (by norm_num)

/-%%
We are ready for the first case of the Perron formula, namely when $x<1$:
\begin{lemma}[formulaLtOne]\label{formulaLtOne}\lean{Perron.formulaLtOne}\leanok
For $x>0$, $\sigma>0$, and $x<1$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =0.
$$
\end{lemma}
%%-/

lemma formulaLtOne (xpos : 0 < x) (x_lt_one : x < 1) (σ_pos : 0 < σ)
    : VerticalIntegral (f x) σ = 0 := by
/-%%
\begin{proof}\leanok
\uses{isHolomorphicOn, HolomorphicOn.vanishesOnRectangle, integralPosAux,
vertIntBound, limitOfConstant, RectangleIntegral_tendsTo_VerticalIntegral, zeroTendstoDiff,
tendsto_rpow_atTop_nhds_zero_of_norm_lt_one,
tendsto_zero_Lower, tendsto_zero_Upper, isIntegrable}
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
%%-/
  let f := f x
  have fHolo : HolomorphicOn f {0, -1}ᶜ := isHolomorphicOn xpos
--%% The rectangle integral of $f$ with corners $\sigma-iT$ and $\sigma+iT$ is zero.
  have rectInt (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') (T : ℝ) :
      RectangleIntegral f (σ' - I * T) (σ'' + I * T) = 0
  · refine fHolo.vanishesOnRectangle fun z h_rect ↦ not_or.mpr (?_ : ¬z = 0 ∧ ¬z = -1)
    simp_rw [Complex.ext_iff, ← not_or, Complex.zero_re, show (-1 : ℂ).re = -1 from rfl]
    have : σ' ≤ z.re ∨ σ'' ≤ z.re := by simpa using h_rect.1.1
    intro hc; cases hc <;> cases this <;> linarith [σ'pos, σ''pos]
--%% The limit of this rectangle integral as $T\to\infty$ is $\int_{(\sigma')}-\int_{(\sigma)}$.
  have rectIntLimit (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') :
      Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ' - I * T) (σ'' + I * T))
      atTop (𝓝 (VerticalIntegral f σ'' - VerticalIntegral f σ')) := by
    apply RectangleIntegral_tendsTo_VerticalIntegral
    · exact tendsto_zero_Lower xpos σ' σ''
    · exact tendsto_zero_Upper xpos σ' σ''
    · exact isIntegrable xpos (by linarith) (by linarith)
    · exact isIntegrable xpos (by linarith) (by linarith)
--%% Therefore, $\int_{(\sigma')}=\int_{(\sigma)}$.
  have contourPull (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') :
    VerticalIntegral f σ' = VerticalIntegral f σ''
  · apply zeroTendstoDiff
    · filter_upwards
      exact rectInt σ' σ'' σ'pos σ''pos
    · exact rectIntLimit σ' σ'' σ'pos σ''pos
--%% But we also have the bound $\int_{(\sigma')} \leq x^{\sigma'} * C$, where
--%% $C=\int_\R\frac{1}{|(1+t)(1+t+1)|}dt$.
  have VertIntBound : ∃ C > 0, ∀ σ' > 1, Complex.abs (VerticalIntegral f σ') ≤ x^σ' * C
  · let C := ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)|
    exact ⟨C, integralPosAux, fun _ ↦ vertIntBound xpos⟩
--%% Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$.
  have AbsVertIntTendsto : Tendsto (Complex.abs ∘ (VerticalIntegral f)) atTop (𝓝 0)
  · obtain ⟨C, _, hC⟩ := VertIntBound
    have := tendsto_rpow_atTop_nhds_zero_of_norm_lt_one xpos x_lt_one C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    · filter_upwards; exact fun _ ↦ Complex.abs.nonneg' _
    · filter_upwards [eventually_gt_atTop 1]; exact hC
  have VertIntTendsto : Tendsto (VerticalIntegral f) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr AbsVertIntTendsto
  --%% So pulling contours gives $\int_{(\sigma)}=0$.
  exact limitOfConstant σ_pos contourPull VertIntTendsto
--%%\end{proof}


/-%%
The second case is when $x>1$.
Here are some auxiliary lemmata for the second case.
%%-/


/-%%
\begin{lemma}[sigmaNegOneHalfPull]\label{sigmaNegOneHalfPull}
\lean{Perron.sigmaNegOneHalfPull}\leanok
Let $x>0$ and $\sigma, \sigma'\in\R$. Then for all $T>0$, we have that
$$
\frac1{2\pi i}
\int_{(\sigma')}\frac{x^s}{s(s+1)}ds -
\frac 1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =
\int_{-1/2-iT}^{\sigma +iT}\frac{x^s}{s(s+1)}ds,
$$
that is, a rectangle with corners $-1/2-iT$ and $\sigma+iT$.
\end{lemma}
%%-/
lemma sigmaNegOneHalfPull (xpos : 0 < x) (Tpos : 0 < T):
    VerticalIntegral (fun s => x ^ s / (s * (s + 1))) σ
    - VerticalIntegral (fun s => x ^ s / (s * (s + 1))) (-1 / 2)
    = RectangleIntegral (fun s => x ^ s / (s * (s + 1))) (-1 / 2 - I * T) (σ + I * T) := by
  sorry
/-%%
\begin{proof}\uses{HolomorphicOn.vanishesOnRectangle, UpperUIntegral,
RectangleIntegral_tendsTo_VerticalIntegral, LowerUIntegral, RectangleIntegral_tendsTo_LowerU,
RectangleIntegral_tendsTo_UpperU, tendsto_zero_Upper, tendsto_zero_Lower,
isIntegrable}
The integral on $(\sigma)$ minus that on $(-1/2)$, minus the integral on the rectangle, is
the integral over an UpperU and a LowerU.
The integrals over the U's are limits of integrals over rectangles with corners at $-1/2+iT$
and $\sigma+iU$ (for UpperU); this uses Lemma \ref{RectangleIntegral_tendsTo_UpperU}. The
integrals over the rectangles vanish by Lemmas \ref{tendsto_zero_Upper} and
\end{proof}
%%-/

/-%%
\begin{lemma}[keyIdentity]\label{keyIdentity}\lean{Perron.keyIdentity}\leanok
Let $x\in \R$ and $s \ne 0, -1$. Then
$$
\frac{x^\sigma}{s(1+s)} = \frac{x^\sigma}{s} - \frac{x^\sigma}{1+s}
$$
\end{lemma}
%%-/
lemma keyIdentity {s : ℂ} (s_ne_zero : s ≠ 0) (s_ne_neg_one : s ≠ -1) :
    (x : ℂ) ^ s / (s * (1 + s))
      = (x : ℂ) ^ s / s - (x : ℂ) ^ s / (1 + s) := by
  have : 1 + s ≠ 0 := by
    intro h
    have : s = -1 := by rw [neg_eq_of_add_eq_zero_right h]
    exact s_ne_neg_one this
  have : s * (1 + s) ≠ 0 := mul_ne_zero s_ne_zero this
  field_simp
  ring
/-%%
\begin{proof}\leanok
By ring.
\end{proof}
%%-/

/-%%
\begin{lemma}[diffBddAtZero]\label{diffBddAtZero}\lean{Perron.diffBddAtZero}\leanok
Let $x>0$. Then for $0 < c < 1 /2$, we have that the function
$$
s ↦ \frac{x^s}{s(s+1)} - \frac1s
$$
is bounded above on the rectangle with corners at $-c-i*c$ and $c+i*c$ (except at $s=0$).
\end{lemma}
%%-/
lemma diffBddAtZero (x : ℝ) {c : ℝ} (cpos : 0 < c) (c_lt : c < 1/2) :
    BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - 1 / s)) ''
      (Rectangle (-c - I * c) (c + I * c) \ {0})) := by
  sorry
/-%%
\begin{proof}\uses{keyIdentity}
Applying Lemma \ref{keyIdentity}, the
 function $s ↦ x^s/s(s+1) - 1/s = x^s/s - x^0/s - x^s/(1+s)$. The last term is bounded for $s$
 away from $-1$. The first two terms are the difference quotient of the function $s ↦ x^s$ at
 $0$; since it's differentiable, the difference remains bounded as $s\to 0$.
\end{proof}
%%-/


/-%%
\begin{lemma}[diffBddAtNegOne]\label{diffBddAtNegOne}\lean{Perron.diffBddAtNegOne}\leanok
Let $x>0$. Then for $0 < c < 1 /2$, we have that the function
$$
s ↦ \frac{x^s}{s(s+1)} - \frac{-x^{-1}}{s+1}
$$
is bounded above on the rectangle with corners at $-1-c-i*c$ and $-1+c+i*c$ (except at $s=-1$).
\end{lemma}
%%-/
lemma diffBddAtNegOne (x : ℝ) {c : ℝ} (cpos : 0 < c) (c_lt : c < 1/2) :
    BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - (-x⁻¹) / (s+1))) ''
      (Rectangle (-1 - c - I * c) (-1 + c + I * c) \ {-1})) := by
  sorry
/-%%
\begin{proof}\uses{keyIdentity}
Applying Lemma \ref{keyIdentity}, the
 function $s ↦ x^s/s(s+1) - x^{-1}/(s+1) = x^s/s - x^s/(s+1) - (-x^{-1})/(s+1)$. The first term is bounded for $s$
 away from $0$. The last two terms are the difference quotient of the function $s ↦ x^s$ at
 $-1$; since it's differentiable, the difference remains bounded as $s\to -1$.
\end{proof}
%%-/

/-%%
\begin{lemma}[residueAtZero]\label{residueAtZero}\lean{Perron.residueAtZero}\leanok
Let $x>0$. Then for all sufficiently small $c>0$, we have that
$$
\frac1{2\pi i}
\int_{-c-i*c}^{c+ i*c}\frac{x^s}{s(s+1)}ds = 1.
$$
\end{lemma}
%%-/
lemma residueAtZero (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (fun (s : ℂ) ↦ x ^ s / (s * (s + 1))) (-c - I * c) (c + I * c) = 1 := by
/-%%
\begin{proof}\leanok
\uses{diffBddAtZero, ResidueTheoremOnRectangleWithSimplePole,
existsDifferentiableOn_of_bddAbove}
For $c>0$ sufficiently small, say $c<1/2$,
%%-/
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (by linarith : (0 : ℝ) < 1 / 2)]
  intro c hc
  set f : ℂ → ℂ := (fun (s : ℂ) ↦ x ^ s / (s * (s + 1)))
  set Rect := Rectangle (-c - I * c) (c + I * c)
  have RectSub : Rect \ {0} ⊆ {0, -1}ᶜ := sorry
  have fHolo : HolomorphicOn f (Rect \ {0}) :=
    (isHolomorphicOn xpos).mono RectSub
  set f1 : ℂ → ℂ := f - (fun (s : ℂ) ↦ 1 / s)
  have f1Holo : HolomorphicOn f1 (Rect \ {0}) := sorry
  simp only [mem_Ioo] at hc
  have uIccIcc : uIcc (-c) c = Icc (-c) c := by apply uIcc_of_le; linarith
  have RectMemNhds : Rect ∈ 𝓝 0
  · rw [mem_nhds_iff]
    refine ⟨(Ioo (-c / 2) (c / 2)) ×ℂ (Ioo (-c / 2) (c / 2)), ?_, ?_⟩
    dsimp [Rectangle]
    simp only [zero_mul, mul_zero, sub_self, sub_zero, add_zero, neg_zero, one_mul, zero_add,
      zero_sub]
    simp_rw [uIccIcc]
    apply reProdIm_subset_iff'.mpr
    · left
      constructor
      · intro u
        simp only [mem_Ioo, mem_Icc, and_imp]
        intro hu1 hu2
        refine ⟨by linarith, by linarith⟩
      · intro u
        simp only [mem_Ioo, mem_Icc, and_imp]
        intro hu1 hu2
        refine ⟨by linarith, by linarith⟩
    · constructor
      · rw [← preimage_equivRealProd_prod]
        apply (isOpen_Ioo.prod isOpen_Ioo).preimage
        exact _root_.equivRealProdCLM.continuous
      · rw [mem_reProdIm]
        simp only [zero_re, mem_Ioo, zero_im, and_self]
        refine ⟨by linarith, by linarith⟩
/-%% $x^s/(s(s+1))$ is equal to $1/s$ plus a function, $g$, say,
holomorphic in the whole rectangle (by Lemma \ref{diffBddAtZero}).
%%-/
  have bddAbove := diffBddAtZero x hc.1 hc.2
  obtain ⟨g, gHolo, g_eq_fDiff⟩ := existsDifferentiableOn_of_bddAbove RectMemNhds f1Holo bddAbove
--%% Now apply Lemma \ref{ResidueTheoremOnRectangleWithSimplePole}.
  apply ResidueTheoremOnRectangleWithSimplePole (pInRectInterior := RectMemNhds) (fHolo := fHolo) (g := g) (A := 1) (gHolo := gHolo)
  convert g_eq_fDiff using 1
  simp
--%%\end{proof}

/-%%
\begin{lemma}[residuePull1]\label{residuePull1}\lean{Perron.residuePull1}\leanok
For $x>1$ (of course $x>0$ would suffice) and $\sigma>0$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =1
+
\frac 1{2\pi i}
\int_{(-1/2)}\frac{x^s}{s(s+1)}ds.
$$
\end{lemma}
%%-/
lemma residuePull1 (x_gt_one : 1 < x) (σ_pos : 0 < σ) :
    VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) σ =
    1 + VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) (-1 / 2) := by
  sorry
/-%%
\begin{proof}
\uses{sigmaNegOneHalfPull, residueAtZero}
By Lemma \ref{sigmaNegOneHalfPull}, the difference of the two vertical integrals is equal
to the integral over a rectangle with corners at $-1/2-iT$ and $\sigma+iT$ (for any $T>0$). By
Lemma \ref{RectanglePullToNhdOfPole}, for $c>0$ sufficiently small, the integral over
this rectangle is equal to the integral over a square with corners at $-c-i*c$ and $c+i*c$ for $c>0$
sufficiently small.
By Lemma \ref{residueAtZero}, the integral over this square is equal to $1$.
\end{proof}
%%-/

/-%%
\begin{lemma}[residuePull2]\label{residuePull2}\lean{Perron.residuePull2}\leanok
For $x>1$, we have
$$
\frac1{2\pi i}
\int_{(-1/2)}\frac{x^s}{s(s+1)}ds = -1/x +
\frac 1{2\pi i}
\int_{(-3/2)}\frac{x^s}{s(s+1)}ds.
$$
\end{lemma}
%%-/
lemma residuePull2 (x_gt_one : 1 < x) :
    VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) (-1 / 2)
    = -1 / x + VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) (-3 / 2) := by
  sorry
/-%%
\begin{proof}
\uses{diffBddAtNegOne}
Pull contour from $(-1/2)$ to $(-3/2)$.
\end{proof}
%%-/

/-%%
\begin{lemma}[contourPull3]\label{contourPull3}\lean{Perron.contourPull3}\leanok
For $x>1$ and $\sigma<-3/2$, we have
$$
\frac1{2\pi i}
\int_{(-3/2)}\frac{x^s}{s(s+1)}ds = \frac 1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds.
$$
\end{lemma}
%%-/
lemma contourPull3 (x_gt_one : 1 < x) (σ'le : σ' ≤ -3/2) (σ''le : σ'' ≤ -3/2) :
    VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) σ' = VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) σ'' := by
  sorry
/-%%
\begin{proof}
Pull contour from $(-3/2)$ to $(\sigma)$.
\end{proof}
%%-/

/-%%
\begin{lemma}[formulaGtOne]\label{formulaGtOne}\lean{Perron.formulaGtOne}\leanok
For $x>1$ and $\sigma>0$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =1-1/x.
$$
\end{lemma}
%%-/
lemma formulaGtOne (x_gt_one : 1 < x) (σ_pos : 0 < σ) :
    VerticalIntegral' (fun s ↦ x^s / (s * (s + 1))) σ = 1 - 1 / x := by
/-%%
\begin{proof}\leanok
\uses{isHolomorphicOn2, residuePull1,
residuePull2, contourPull3, integralPosAux, vertIntBoundLeft,
tendsto_rpow_atTop_nhds_zero_of_norm_gt_one, limitOfConstantLeft}
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on $\C \setminus {0,1}$.
%%-/
  set f : ℂ → ℂ := (fun s ↦ x^s / (s * (s + 1)))
  have : HolomorphicOn f {0, -1}ᶜ := isHolomorphicOn (by linarith : 0 < x)
--%% First pull the contour from $(\sigma)$ to $(-1/2)$, picking up a residue $1$ at $s=0$.
  have contourPull₁ : VerticalIntegral' f σ = 1 + VerticalIntegral' f (-1 / 2) := residuePull1 x_gt_one σ_pos
  rw [contourPull₁]
--%% Next pull the contour from $(-1/2)$ to $(-3/2)$, picking up a residue $-1/x$ at $s=-1$.
  have contourPull₂ : VerticalIntegral' f (-1 / 2) = -1 / x + VerticalIntegral' f (-3 / 2) := residuePull2 x_gt_one
  rw [contourPull₂]
--%% Then pull the contour all the way to $(\sigma')$ with $\sigma'<-3/2$.
  have contourPull₃ : ∀ σ' σ'' (_ : σ' ≤ -3/2) (_ : σ'' ≤ -3/2), VerticalIntegral' f σ' = VerticalIntegral' f σ'' := fun σ' σ'' σ'le σ''le ↦ contourPull3 x_gt_one σ'le σ''le
--%% For $\sigma' < -3/2$, the integral is bounded by $x^{\sigma'}\int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt$.
  have VertIntBound : ∃ C > 0, ∀ σ' < -3/2, Complex.abs (VerticalIntegral' f σ') ≤ x^σ' * C :=
    vertIntBoundLeft (by linarith : 0 < x)
--%% Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$.
  have AbsVertIntTendsto : Tendsto (Complex.abs ∘ (VerticalIntegral' f)) atBot (𝓝 0)
  · obtain ⟨C, _, hC⟩ := VertIntBound
    have := tendsto_rpow_atTop_nhds_zero_of_norm_gt_one x_gt_one C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    · filter_upwards; exact fun _ ↦ Complex.abs.nonneg' _
    · filter_upwards [eventually_lt_atBot (-3/2)]; exact hC
  have VertIntTendsto : Tendsto (VerticalIntegral' f) atBot (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr AbsVertIntTendsto
  --%% So pulling contours gives $\int_{(-3/2)}=0$.
  have VertIntEqZero: VerticalIntegral' f (-3 / 2) = 0 :=
    limitOfConstantLeft (σ := -3/2) (Eq.le rfl) contourPull₃ VertIntTendsto
  rw [VertIntEqZero]
  simp only [add_zero, one_div]
  ring
/-%%
\end{proof}
%%-/


/-%%
The two together give the Perron formula. (Which doesn't need to be a separate lemma.)

For $x>0$ and $\sigma>0$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds = \begin{cases}
1-\frac1x & \text{ if }x>1\\
0 & \text{ if } x<1
\end{cases}.
$$
%%-/
