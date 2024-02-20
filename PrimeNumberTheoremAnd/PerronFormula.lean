import Mathlib.Analysis.Calculus.ContDiff.Basic
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Uniformly
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
/-%%
\begin{proof}
\uses{RectangleIntegral, UpperUIntegral}
Almost by definition.
%%-/
  have h_re  (s : ℝ) (t : ℝ) : (s  + I * t).re = s  := by simp
  have h_im  (s : ℝ) (t : ℝ) : (s  + I * t).im = t  := by simp
  have hbot : Tendsto (fun (_ : ℝ) => ∫ (x : ℝ) in σ..σ', f (x + T * I)) atTop (𝓝 <| ∫ (x : ℝ) in σ..σ', f (x + T * I)) := by
    exact tendsto_const_nhds
  have hvert (s : ℝ) (int : Integrable (fun (y : ℝ) ↦ f (s + y * I))) :
      Tendsto (fun (U : ℝ) => I * ∫ (y : ℝ) in T..U, f (s + y * I)) atTop (𝓝 <| I * ∫ (y : ℝ) in Ioi T, f (s + y * I)) := by
    exact (intervalIntegral_tendsto_integral_Ioi T int.restrict tendsto_id).const_smul I
  have := ((hbot.sub htop).add (hvert σ' hright)).sub (hvert σ hleft)
  simpa only [RectangleIntegral, UpperUIntegral, h_re, h_im, sub_zero, ←integral_Ici_eq_integral_Ioi]
--%%\end{proof}

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
      (𝓝 (- LowerUIntegral f σ σ' T)) := by
/-%%
\begin{proof}
\uses{RectangleIntegral, LowerUIntegral}
Almost by definition.
%%-/
  have h_re  (s : ℝ) (t : ℝ) : (s  - I * t).re = s  := by simp
  have h_im  (s : ℝ) (t : ℝ) : (s  - I * t).im = -t  := by simp
  have hbot' : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x - y * I)) atTop (𝓝 0) := by
    convert (hbot.comp tendsto_neg_atTop_atBot) using 1
    ext; simp only [Function.comp_apply, ofReal_neg, neg_mul]; rfl
  have htop : Tendsto (fun (_ : ℝ) => ∫ (x : ℝ) in σ..σ', f (x - T * I)) atTop (𝓝 <| ∫ (x : ℝ) in σ..σ', f (x - T * I)) := by
    exact tendsto_const_nhds
  have hvert (s : ℝ) (int : Integrable (fun (y : ℝ) ↦ f (s + y * I))) :
      Tendsto (fun (U : ℝ) => I * ∫ (y : ℝ) in -U..-T, f (s + y * I)) atTop (𝓝 <| I * ∫ (y : ℝ) in Iic (-T), f (s + y * I)) := by
    have := (intervalIntegral_tendsto_integral_Iic (-T) int.restrict tendsto_id).const_smul I
    convert (this.comp tendsto_neg_atTop_atBot) using 1
  have := ((hbot'.sub htop).add (hvert σ' hright)).sub (hvert σ hleft)
  have final : (((-∫ (x : ℝ) in σ..σ', f (↑x - ↑T * I)) + I * ∫ (y : ℝ) in Iic (-T), f (↑σ' + ↑y * I)) -
      I * ∫ (y : ℝ) in Iic (-T), f (↑σ + ↑y * I)) = (-(I * ∫ (y : ℝ) in Iic (-T), f (↑σ + ↑y * I)) +
      ((I * ∫ (y : ℝ) in Iic (-T), f (↑σ' + ↑y * I)) - ∫ (x : ℝ) in σ..σ', f (↑x - ↑T * I))) := by
    ring_nf
  rw [zero_sub] at this
  simp_rw [RectangleIntegral, LowerUIntegral, h_re, h_im, ofReal_neg, neg_mul, neg_add_rev, neg_sub]
  exact final ▸ this
--%%\end{proof}

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
\begin{proof}\leanok
Standard.
\end{proof}
%%-/

namespace Perron

variable {x σ σ' σ'' T : ℝ}

noncomputable abbrev f (x : ℝ) := fun (s : ℂ) => x ^ s / (s * (s + 1))

/-%%
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

lemma integral_one_div_const_add_sq_pos (c : ℝ) (hc : 0 < c) : 0 < ∫ (t : ℝ), 1 / (c + t^2) := by
  have hfun_eq (t : ℝ) : 1 / (c + t^2) = c⁻¹ * (1 + ((Real.sqrt c)⁻¹ * t)^2)⁻¹ := by
    field_simp [hc.ne.symm]
  simp_rw [hfun_eq]
  rw [MeasureTheory.integral_mul_left, Measure.integral_comp_mul_left (fun t ↦ (1+t^2)⁻¹) (a:=(Real.sqrt c)⁻¹)]
  simp only [inv_inv, abs_eq_self.mpr <| Real.sqrt_nonneg c, smul_eq_mul, gt_iff_lt, inv_pos, hc,
    mul_pos_iff_of_pos_left, sqrt_pos, integral_univ_inv_one_add_sq]
  positivity

lemma Integrable.one_div_const_add_sq (c : ℝ) (hc : 0 < c) : Integrable fun (t : ℝ) ↦ 1 / (c + t^2) :=
  .of_integral_ne_zero (integral_one_div_const_add_sq_pos c hc).ne'

lemma integralPosAux'_of_le (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (hle : c₁ ≤ c₂) : 0 < ∫ (t : ℝ), 1 / |Real.sqrt (c₁ + t^2) * Real.sqrt (c₂ + t^2)| := by
  have c₂_pos : 0 < c₂ := by linarith
  simp_rw [fun (t : ℝ) ↦ abs_of_pos (show sqrt (c₁ + t^2) * sqrt (c₂ + t^2) > 0 by positivity)]

  have hlower (t : ℝ) : 1 / (c₂ + t^2) ≤ 1 / (Real.sqrt (c₁ + t^2) * Real.sqrt (c₂ + t^2)) := by
    gcongr
    calc
      _ ≤ Real.sqrt (c₂ + t^2) * Real.sqrt (c₂ + t^2) := ?_
      _ ≤ c₂ + t^2 := ?_
    · gcongr
      apply Real.sqrt_le_sqrt
      gcongr
    · rw[←Real.sqrt_mul, sqrt_mul_self] <;> positivity

  have hupper (t : ℝ) : 1 / (Real.sqrt (c₁ + t^2) * Real.sqrt (c₂ + t^2)) ≤ 1 / (c₁ + t^2)  := by
    gcongr
    calc
      _ ≥ Real.sqrt (c₁ + t^2) * Real.sqrt (c₁ + t^2) := ?_
      _ ≥ c₁ + t^2 := ?_
    · gcongr
      apply Real.sqrt_le_sqrt
      gcongr
    · rw[←Real.sqrt_mul, sqrt_mul_self] <;> positivity

  calc 0 < ∫ t, 1 / (c₂ + t^2) := integral_one_div_const_add_sq_pos c₂ c₂_pos
       _ ≤ ∫ t, 1 / (Real.sqrt (c₁ + t^2) * Real.sqrt (c₂ + t^2)) := ?_

  apply integral_mono
  · apply Integrable.one_div_const_add_sq c₂ c₂_pos
  · apply MeasureTheory.Integrable.mono (g := fun t:ℝ ↦ 1/(c₁ + t^2))
    · apply Integrable.one_div_const_add_sq c₁ c₁_pos
    · refine (measurable_const.div <| Measurable.mul ?_ ?_).aestronglyMeasurable <;>
        exact (measurable_const.add <| measurable_id'.pow_const 2).sqrt
    refine ae_of_all _ (fun x ↦ ?_)
    repeat rewrite [norm_of_nonneg (by positivity)]
    exact hupper x
  apply hlower


lemma integralPosAux' (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (c₂_pos : 0 < c₂) : 0 < ∫ (t : ℝ), 1 / |Real.sqrt (c₁ + t^2) * Real.sqrt (c₂ + t^2)| := by
  by_cases hc : c₁ ≤ c₂
  · apply integralPosAux'_of_le c₁ c₂ c₁_pos hc
  · convert integralPosAux'_of_le c₂ c₁ c₂_pos (by linarith) using 4
    rw [mul_comm]

lemma integralPosAux : 0 < ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| := by
/-%%
\begin{proof}\leanok
This integral is between $\frac{1}{2}$ and $1$ of the integral of $\frac{1}{1+t^2}$, which is $\pi$.
%%-/
  apply integralPosAux' <;> norm_num
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
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1/4+t^2)(2+t^2)|^{1/2}}dt.$$
\end{lemma}
%%-/

lemma vertIntBoundLeft (xpos : 0 < x) :
    ∃ C, ∀ (σ : ℝ) (_ : σ < -3 / 2), Complex.abs (VerticalIntegral' (f x) σ) ≤ x ^ σ * C := by
/-%%
\begin{proof}\leanok
\uses{VerticalIntegral}
%%-/
  /- This proof is adapted from `vertIntBound` -/
  use (1/(2*π)) *  ∫ (t : ℝ), 1 / |Real.sqrt (4⁻¹ + t^2) * Real.sqrt (2 + t^2)|
  intro σ hσ
  suffices h : Complex.abs (VerticalIntegral (f x) σ) ≤ x^σ * ∫ (t : ℝ), 1 / |Real.sqrt (4⁻¹ + t^2) * Real.sqrt (2 + t^2)| by
    rw [VerticalIntegral']
    simp only [one_div, mul_inv_rev, inv_I, neg_mul, map_neg_eq_map, map_mul, abs_I, map_inv₀,
      abs_ofReal, abs_ofNat, one_mul, ge_iff_le, abs_of_pos Real.pi_pos] at h ⊢
    convert_to π⁻¹ * 2⁻¹ * Complex.abs (VerticalIntegral (f x) σ) ≤ π⁻¹ * 2⁻¹ * (x ^ σ * ∫ (t : ℝ), |sqrt (4⁻¹ + t ^ 2) * sqrt (2 + t ^ 2)|⁻¹)
    · ring
    · gcongr
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (Complex.abs (σ + t * I) * Complex.abs (σ + t * I + 1)) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / |Real.sqrt (4⁻¹ + t^2) * Real.sqrt (2 + t^2)| := ?_
  · simp [VerticalIntegral', VerticalIntegral, show 0 ≤ π from le_of_lt Real.pi_pos]
  · congr with t
    rw [norm_div, Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos xpos, add_re, ofReal_re,
      re_ofReal_mul, I_re, mul_zero, add_zero]
  · simp_rw [div_eq_mul_inv, integral_mul_left, one_mul, Complex.norm_eq_abs, map_mul]
  gcongr
  by_cases hint : Integrable fun (a : ℝ) => 1 / (Complex.abs (σ + ↑a * I) * Complex.abs (↑σ + ↑a * I + 1))
  swap
  · rw [integral_undef hint]
    apply integral_nonneg
    rw [Pi.le_def]
    intro t
    simp only [Pi.zero_apply, one_div, inv_nonneg, abs_nonneg]
  apply integral_mono hint
  · have := integralPosAux' (4⁻¹) 2 (by norm_num) (by norm_num)
    contrapose! this
    have := integral_undef this
    simp_rw [this, le_rfl]
  rw [Pi.le_def]
  intro t
  rw [abs_eq_self.mpr (by positivity)]
  simp only [Complex.abs_apply]
  rw[mul_comm]
  gcongr
  swap
  · apply sqrt_le_sqrt
    rw [normSq_add_mul_I, add_le_add_iff_right]
    nlinarith only [hσ]
  · apply sqrt_le_sqrt
    rw [add_right_comm, ← ofReal_one, ← ofReal_add, normSq_add_mul_I, add_le_add_iff_right]
    ring_nf
    nlinarith
/-%%
Triangle inequality and pointwise estimate.
\end{proof}
%%-/


/-% -- this is purposefully the wrong delimiter, so it doesn't get scraped into blueprint
TODO : Remove this lemma if it's not needed
\begin{lemma}[vertIntBound2]%\label{vertIntBound2}\lean{Perron.vertIntBound2}\leanok
Let $x>0$ and $\sigma\in \R$, $\sigma \ne 0, -1$. Then
$$\left|
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \ll_\sigma x^\sigma.$$
Note that the implied constant here does depend on $\sigma$. (So it's not as useful a lemma.)
\end{lemma}
%-/
lemma vertIntBound2 (xpos : 0 < x) (σ_ne_zero : σ ≠ 0) (σ_ne_neg_one : σ ≠ -1) :
    ∃ C > 0, Complex.abs (VerticalIntegral (f x) σ) ≤ x ^ σ * C := by
  sorry
/-%
\begin{proof}
\uses{vertIntBound}
Similar to ``vertIntBound''.
\end{proof}
%-/

lemma map_conj (hx : 0 ≤ x) (s : ℂ) : f x (conj s) = conj (f x s) := by
  simp? [f] says simp only [f, map_div₀, map_mul, map_add, map_one]
  congr
  rw [cpow_conj, Complex.conj_ofReal]
  · rewrite [Complex.arg_ofReal_of_nonneg hx]
    exact pi_ne_zero.symm

theorem isTheta_uniformlyOn_uIcc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 (uIcc σ' σ'') ×ˢ (atBot ⊔ atTop)]
    ((fun y ↦ 1 / y^2) ∘ Prod.snd) := by
  set l := 𝓟 (uIcc σ' σ'') ×ˢ (atBot ⊔ atTop : Filter ℝ) with hl
  refine IsTheta.div (isTheta_norm_left.mp ?_) ?_
  · suffices (fun (σ, _y) => |x| ^ σ) =Θ[l] fun _ => (1 : ℝ) by
      simpa [Complex.abs_cpow_of_ne_zero <| ofReal_ne_zero.mpr (ne_of_gt xpos),
        arg_ofReal_of_nonneg xpos.le] using this
    exact (continuousOn_const.rpow continuousOn_id fun _ _ ↦ Or.inl <| ne_of_gt (abs_pos_of_pos xpos))
      |>.const_isThetaUniformlyOn_isCompact isCompact_uIcc (by norm_num)
      (fun i _ ↦ ne_of_gt <| rpow_pos_of_pos (abs_pos_of_pos xpos) _) _
  · have h_c {c : ℂ} : (fun (_ : ℝ × ℝ) => c) =o[l] Prod.snd := by
      rewrite [hl, Filter.prod_sup, isLittleO_sup]
      exact ⟨isLittleO_const_snd_atBot c _, isLittleO_const_snd_atTop c _⟩
    have h_yI : (fun ((_σ, y) : ℝ × ℝ) ↦ y * I) =Θ[l] Prod.snd :=
      isTheta_of_norm_eventuallyEq (by simp; rfl)
    have h_σ_yI : (fun (σy : ℝ × ℝ) ↦ σy.1 + σy.2 * I) =Θ[l] Prod.snd := by
      refine IsLittleO.add_isTheta ?_ h_yI
      exact continuous_ofReal.continuousOn.const_isBigOUniformlyOn_isCompact isCompact_uIcc
        (by norm_num : ‖(1 : ℂ)‖ ≠ 0) _ |>.trans_isLittleO h_c
    simp_rw [sq]
    exact h_σ_yI.mul (h_σ_yI.add_isLittleO h_c)

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
    (univ_mem' fun y ↦ ?_) (isTheta xpos).2.isBigO ⟨Ioi 1, Ioi_mem_atTop 1, ?_⟩
--%% and $|f(-x)| = \Theta(x^{-2})$ as $x\to\infty$.
  · show ‖f x (↑σ + ↑y * I)‖ = ‖f x (↑σ + ↑(-y) * I)‖
    have : (↑σ + ↑(-y) * I) = conj (↑σ + ↑y * I) := Complex.ext (by simp) (by simp)
    simp_rw [this, map_conj xpos.le, Complex.norm_eq_abs, abs_conj]
--%% Since $g(x) = x^{-2}$ is integrable on $[a,\infty)$ for any $a>0$, we conclude.
  · refine integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num)
      (show (0 : ℝ) < 1 by norm_num) |>.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
    rw [rpow_neg (show (0 : ℝ) < 1 by norm_num |>.trans hy |>.le), inv_eq_one_div, rpow_two]
--%%\end{proof}

theorem horizontal_integral_isBigO
    {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    (fun (y : ℝ) => ∫ (σ : ℝ) in σ'..σ'', f x (σ + y * I) ∂μ) =O[atBot ⊔ atTop]
    fun y ↦ 1 / y^2 := by
  let g := fun ((σ, y) : ℝ × ℝ) ↦ f x (σ + y * I)
  calc
    _ =Θ[atBot ⊔ atTop] fun (y : ℝ) => ∫ (σ : ℝ) in uIoc σ' σ'', g (σ, y) ∂μ :=
        isTheta_of_norm_eventuallyEq <| univ_mem'
          fun _ ↦ intervalIntegral.norm_intervalIntegral_eq _ _ _ _
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

lemma contourPull {σ' σ'' : ℝ} (xpos : 0 < x) (hσ0 : 0 ∉ uIcc σ' σ'') (hσ1 : -1 ∉ uIcc σ' σ'') :
    VerticalIntegral (f x) σ' = VerticalIntegral (f x) σ'' := by
  have fHolo : HolomorphicOn (f x) {0, -1}ᶜ := isHolomorphicOn xpos
  have hσ'0 : σ' ≠ 0 := fun h ↦ hσ0 (h ▸ left_mem_uIcc)
  have hσ'1 : σ' ≠ -1 := fun h ↦ hσ1 (h ▸ left_mem_uIcc)
  have hσ''0 : σ'' ≠ 0 := fun h ↦ hσ0 (h ▸ right_mem_uIcc)
  have hσ''1 : σ'' ≠ -1 := fun h ↦ hσ1 (h ▸ right_mem_uIcc)
  have rectInt (T : ℝ) : RectangleIntegral (f x) (σ' - I * T) (σ'' + I * T) = 0 := by
    apply integral_boundary_rect_eq_zero_of_differentiableOn (f x) _ _ (fHolo.mono fun z hrect ↦ ?_)
    have : z ∈ uIcc σ' σ'' ×ℂ uIcc (-T) T := by simpa using hrect
    have h_re : z.re ≠ 0 := fun h ↦ hσ0 (h ▸ this.1)
    have h_im : z.re ≠ -1 := fun h ↦ hσ1 (h ▸ this.1)
    simp_all [Complex.ext_iff]
  exact zeroTendstoDiff _ _ _ (univ_mem' rectInt) <| RectangleIntegral_tendsTo_VerticalIntegral
    (tendsto_zero_Lower xpos σ' σ'') (tendsto_zero_Upper xpos σ' σ'')
    (isIntegrable xpos hσ'0 hσ'1) (isIntegrable xpos hσ''0 hσ''1)

lemma formulaLtOne (xpos : 0 < x) (x_lt_one : x < 1) (σ_pos : 0 < σ)
    : VerticalIntegral (f x) σ = 0 := by
/-%%
\begin{proof}\leanok
\uses{isHolomorphicOn, HolomorphicOn.vanishesOnRectangle, integralPosAux,
vertIntBound, limitOfConstant, RectangleIntegral_tendsTo_VerticalIntegral, zeroTendstoDiff,
tendsto_rpow_atTop_nhds_zero_of_norm_lt_one,
tendsto_zero_Lower, tendsto_zero_Upper, isIntegrable}
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
  The rectangle integral of $f$ with corners $\sigma-iT$ and $\sigma+iT$ is zero.
  The limit of this rectangle integral as $T\to\infty$ is $\int_{(\sigma')}-\int_{(\sigma)}$.
  Therefore, $\int_{(\sigma')}=\int_{(\sigma)}$.
%%-/
  have h_contourPull (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') :
      VerticalIntegral (f x) σ' = VerticalIntegral (f x) σ'' :=
    contourPull xpos (not_mem_uIcc_of_lt σ'pos σ''pos)
      (not_mem_uIcc_of_lt (by linarith) (by linarith))
--%% But we also have the bound $\int_{(\sigma')} \leq x^{\sigma'} * C$, where
--%% $C=\int_\R\frac{1}{|(1+t)(1+t+1)|}dt$.
  have VertIntBound : ∃ C > 0, ∀ σ' > 1, Complex.abs (VerticalIntegral (f x) σ') ≤ x^σ' * C
  · let C := ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)|
    exact ⟨C, integralPosAux, fun _ ↦ vertIntBound xpos⟩
--%% Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$.
  have AbsVertIntTendsto : Tendsto (Complex.abs ∘ (VerticalIntegral (f x))) atTop (𝓝 0)
  · obtain ⟨C, _, hC⟩ := VertIntBound
    have := tendsto_rpow_atTop_nhds_zero_of_norm_lt_one xpos x_lt_one C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    · filter_upwards; exact fun _ ↦ Complex.abs.nonneg' _
    · filter_upwards [eventually_gt_atTop 1]; exact hC
  have VertIntTendsto : Tendsto (VerticalIntegral (f x)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr AbsVertIntTendsto
  --%% So pulling contours gives $\int_{(\sigma)}=0$.
  exact limitOfConstant σ_pos h_contourPull VertIntTendsto
--%%\end{proof}

/-%%
The second case is when $x>1$.
Here are some auxiliary lemmata for the second case.
TODO: Move to more general section
%%-/

theorem HolomorphicOn.upperUIntegral_eq_zero {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ T ≤ z.im})
    (htop : Tendsto (fun y : ℝ => ∫ (x : ℝ) in σ..σ', f (↑x + ↑y * I)) atTop (𝓝 0))
    (hleft : Integrable fun y : ℝ => f (↑σ + ↑y * I))
    (hright : Integrable fun y : ℝ => f (↑σ' + ↑y * I)) :
    UpperUIntegral f σ σ' T = 0 := by
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_UpperU htop hleft hright)
  apply EventuallyEq.tendsto
  filter_upwards [eventually_ge_atTop T]
  refine fun _ hTU ↦ hf.vanishesOnRectangle fun _ ↦ ?_
  rw [mem_Rect (by simp [hσ]) (by simp [hTU])]
  simpa using by tauto

theorem HolomorphicOn.lowerUIntegral_eq_zero {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ z.im ≤ -T})
    (hbot : Tendsto (fun (y : ℝ) => ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : Integrable fun y : ℝ => f (↑σ + ↑y * I))
    (hright : Integrable fun y : ℝ => f (↑σ' + ↑y * I)) :
    LowerUIntegral f σ σ' T = 0 := by
  suffices h : - LowerUIntegral f σ σ' T = 0 by exact neg_eq_zero.mp h
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_LowerU hbot hleft hright)
  apply EventuallyEq.tendsto
  filter_upwards [eventually_ge_atTop T]
  refine fun _ hTU ↦ hf.vanishesOnRectangle fun _ ↦ ?_
  rw [mem_Rect (by simp [hσ]) (by simp [hTU])]
  simpa using by tauto

/-%%
\begin{lemma}[sigmaNegOneHalfPull]\label{sigmaNegOneHalfPull}
\lean{Perron.sigmaNegOneHalfPull}\leanok
Let $x>0$ and $\sigma > 0$. Then for all $T>0$, we have that
$$
\frac1{2\pi i}
\int_{(-1/2)}\frac{x^s}{s(s+1)}ds -
\frac 1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =
\int_{-1/2-iT}^{\sigma +iT}\frac{x^s}{s(s+1)}ds,
$$
that is, a rectangle with corners $-1/2-iT$ and $\sigma+iT$.
\end{lemma}
%%-/
lemma sigmaNegOneHalfPull_aux {f : ℂ → ℂ} (hf1 : Integrable (fun t : ℝ ↦ f ((-1/2:ℝ) + t * I)))
  (hf2 : Integrable (fun t : ℝ ↦ f (σ + t * I)))
  (hftop : Tendsto (fun y : ℝ => ∫ (x : ℝ) in (-1/2:ℝ)..σ, f (↑x + ↑y * I)) atTop (𝓝 0))
  (hfbot : Tendsto (fun y : ℝ => ∫ (x : ℝ) in (-1/2:ℝ)..σ, f (x + y * I)) atBot (𝓝 0))
  (hf_holo : HolomorphicOn f {0, -1}ᶜ) (σpos : 0 < σ) (Tpos : 0 < T):
    VerticalIntegral f σ
    - VerticalIntegral f (-1 / 2)
    = RectangleIntegral f (-1 / 2 - I * T) (σ + I * T) := by

/-%%
\begin{proof}\uses{HolomorphicOn.vanishesOnRectangle, UpperUIntegral,
RectangleIntegral_tendsTo_VerticalIntegral, LowerUIntegral, RectangleIntegral_tendsTo_LowerU,
RectangleIntegral_tendsTo_UpperU, tendsto_zero_Upper, tendsto_zero_Lower,
isIntegrable}\leanok
%%-/
  suffices : VerticalIntegral f σ
    - VerticalIntegral f (-1 / 2)
    - RectangleIntegral f (-1 / 2 - I * T) (σ + I * T) = 0
  · linear_combination this
  calc
    _ = UpperUIntegral f (-1/2) σ T
        - LowerUIntegral f (-1/2) σ T := ?_
    _ = 0 := ?_
/-%%
The integral on $(\sigma)$ minus that on $(-1/2)$, minus the integral on the rectangle, is
the integral over an UpperU and a LowerU.
%%-/
  · convert DiffVertRect_eq_UpperLowerUs hf1 hf2
    norm_num
/-%%
The integrals over the U's are limits of integrals over rectangles with corners at $-1/2+iT$
and $\sigma+iU$ (for UpperU); this uses Lemma \ref{RectangleIntegral_tendsTo_UpperU}. The
integrals over the rectangles vanish by Lemmas \ref{tendsto_zero_Upper} and
\end{proof}
%%-/
  · rw[HolomorphicOn.upperUIntegral_eq_zero (by linarith) _ hftop hf1 hf2,
      HolomorphicOn.lowerUIntegral_eq_zero (by linarith) _ hfbot hf1 hf2]
    · ring
    all_goals
    · apply hf_holo.mono
      intro z
      simp only [mem_setOf_eq, mem_compl_iff, mem_insert_iff, mem_singleton_iff, and_imp]
      push_neg
      intro _ _ _
      constructor <;> apply_fun Complex.im <;> norm_num <;> linarith

lemma sigmaNegOneHalfPull (xpos : 0 < x) (σpos : 0 < σ) (Tpos : 0 < T):
    VerticalIntegral (f x) σ - VerticalIntegral (f x) (-1 / 2)
    = RectangleIntegral (f x) (-1 / 2 - I * T) (σ + I * T) :=
  sigmaNegOneHalfPull_aux (isIntegrable xpos (by norm_num) (by norm_num))
    (isIntegrable xpos σpos.ne.symm (by linarith)) (tendsto_zero_Upper xpos ..)
    (tendsto_zero_Lower xpos ..) (isHolomorphicOn xpos) σpos Tpos

lemma sPlusOneNeZero {s : ℂ} (s_ne_neg_one : s ≠ -1) : s + 1 ≠ 0 := by
  intro h
  have : s = -1 := add_eq_zero_iff_eq_neg.mp h
  exact s_ne_neg_one this

/-%%
\begin{lemma}[keyIdentity]\label{keyIdentity}\lean{Perron.keyIdentity}\leanok
Let $x\in \R$ and $s \ne 0, -1$. Then
$$
\frac{x^\sigma}{s(1+s)} = \frac{x^\sigma}{s} - \frac{x^\sigma}{1+s}
$$
\end{lemma}
%%-/
lemma keyIdentity (x : ℝ) {s : ℂ} (s_ne_zero : s ≠ 0) (s_ne_neg_one : s ≠ -1) :
    (x : ℂ) ^ s / (s * (s + 1))
      = (x : ℂ) ^ s / s - (x : ℂ) ^ s / (s + 1) := by
  have : s + 1 ≠ 0 := sPlusOneNeZero s_ne_neg_one
  have : s * (s + 1) ≠ 0 := mul_ne_zero s_ne_zero this
  field_simp
  ring
/-%%
\begin{proof}\leanok
By ring.
\end{proof}
%%-/

lemma diffBddAtZero_aux_ge {x : ℝ} (xpos : 0 < x) (xge : 1 ≤ x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, ∀ s ∈ Square 0 c,
    Complex.abs ((x : ℂ) ^ s / s - s⁻¹) ≤ x ^ (2 : ℝ) * 2 := sorry

lemma diffBddAtZero_aux_lt {x : ℝ} (xpos : 0 < x) (xlt : x < 1) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, ∀ s ∈ Square 0 c,
    Complex.abs ((x : ℂ) ^ s / s - s⁻¹) ≤ x ^ (-(2 : ℝ)) * 2 := sorry

lemma diffBddAtZero_aux {x : ℝ} (xpos : 0 < x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, ∀ s ∈ Square 0 c,
    Complex.abs ((x : ℂ) ^ s / s - s⁻¹) ≤ if h : 1 ≤ x then x ^ (2 : ℝ) * 2 else x ^ (-(2 : ℝ)) * 2 := by
  by_cases h : 1 ≤ x
  · filter_upwards [diffBddAtZero_aux_ge xpos h]
    intro c sRectBnd sRect
    simpa [h, ↓reduceDite, rpow_two, ge_iff_le] using (sRectBnd sRect)
  · filter_upwards [diffBddAtZero_aux_lt xpos (by linarith : x < 1)]
    intro c sRectBnd sRect
    simpa [h, ↓reduceDite, rpow_two, ge_iff_le] using (sRectBnd sRect)

/-%%
\begin{lemma}[diffBddAtZero]\label{diffBddAtZero}\lean{Perron.diffBddAtZero}\leanok
Let $x>0$. Then for $0 < c < 1 /2$, we have that the function
$$
s ↦ \frac{x^s}{s(s+1)} - \frac1s
$$
is bounded above on the rectangle with corners at $-c-i*c$ and $c+i*c$ (except at $s=0$).
\end{lemma}
%%-/
lemma diffBddAtZero {x : ℝ} (xpos : 0 < x) :
     ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - 1 / s)) ''
      (Square 0 c \ {0})) := by
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (by linarith : (0 : ℝ) < 1 / 2), diffBddAtZero_aux xpos]
  intro c hc sRectBnd
  simp only [mem_Ioo] at hc
  have cpos : 0 < c := hc.1
  have c_lt : c < 1 / 2 := hc.2
  rw [bddAbove_def]
  let bnd := if h : 1 ≤ x then x ^ (2 : ℝ) * 4 else x ^ (-(2 : ℝ)) * 4
  use bnd
  intro y hy
  simp only [one_div, Function.comp_apply, Complex.norm_eq_abs, mem_image, mem_diff,
    mem_singleton_iff] at hy
  obtain ⟨s, ⟨s_memRect, s_nonzero⟩, rfl⟩ := hy
  change s ≠ 0 at s_nonzero
  have s_ne_neg_one : s ≠ -1 := by
    intro h
    rw [h] at s_memRect
    rw [Square, mem_Rect (by simp; linarith) (by simp; linarith)] at s_memRect
    simp only [sub_re, neg_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_self, sub_zero, one_re, neg_le_neg_iff, add_re, add_zero, sub_im, neg_im, neg_zero,
      mul_im, one_mul, zero_add, zero_sub, one_im, Left.neg_nonpos_iff, add_im, and_self] at s_memRect
    linarith
  rw [keyIdentity x s_nonzero s_ne_neg_one]

  calc
    _ = Complex.abs ((x : ℂ) ^ s / s - s⁻¹ + -(x : ℂ) ^ s / (s + 1)) := by congr; ring
    _ ≤ Complex.abs ((x : ℂ) ^ s / s - s⁻¹) + Complex.abs (-(x : ℂ) ^ s / (s + 1)) := AbsoluteValue.add_le Complex.abs _ _
    _ ≤ Complex.abs ((x : ℂ) ^ s / s - s⁻¹) +  bnd / 2 := ?_
    _ ≤ bnd / 2 + bnd / 2 := by
      gcongr
      convert sRectBnd s s_memRect
      by_cases one_le_x : 1 ≤ x <;> simp only [dite_eq_ite, one_le_x, ↓reduceIte, ↓reduceDite] <;> field_simp <;> ring
    _ = bnd := by ring

  gcongr
  rw [← Complex.abs_neg]
  simp only [map_neg_eq_map, map_div₀]
  rw [Square, mem_Rect] at s_memRect
  · simp only [sub_re, neg_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_self, sub_zero, add_re, add_zero, sub_im, neg_im, neg_zero, mul_im, one_mul, zero_add,
      zero_sub, add_im] at s_memRect
    have bnd2 : (Complex.abs (s + 1))⁻¹ ≤ 2
    · rw [inv_le (by simp [sPlusOneNeZero s_ne_neg_one]) (by linarith)]
      calc
        2⁻¹ ≤ (s + 1).re := by
          simp only [add_re, one_re]
          have aux1 : -(1 : ℝ) / 2 ≤ s.re := by linarith [s_memRect.1]
          have aux2 : -(1 : ℝ) / 2 = -1 + 2⁻¹ := by norm_num
          rw [aux2] at aux1
          linarith
        _ ≤ Complex.abs (s + 1) := Complex.re_le_abs _
    by_cases one_le_x : 1 ≤ x
    · simp only [one_le_x, ↓reduceDite, mul_div_assoc]
      rw [(by norm_num : (4 : ℝ) / 2 = 2)]
      have bnd1 : Complex.abs ((x : ℂ) ^ s) ≤ x ^ (2 : ℝ) := by
        rw [Complex.abs_cpow_eq_rpow_re_of_pos xpos]
        have : s.re ≤ 2 := by linarith [s_memRect.2.1]
        exact Real.rpow_le_rpow_of_exponent_le one_le_x this
      change Complex.abs ((x : ℂ) ^ s) * (Complex.abs (s + 1))⁻¹ ≤ _
      refine mul_le_mul bnd1 bnd2 (inv_nonneg_of_nonneg (AbsoluteValue.nonneg Complex.abs _)) ?_
      convert sq_nonneg x
      exact rpow_two x
    · simp only [one_le_x, ↓reduceDite, one_div]
      simp only [not_le] at one_le_x
      rw [mul_div_assoc, (by norm_num : (4 : ℝ) / 2 = 2)]
      set t := x⁻¹
      have tpos : 0 < t := inv_pos_of_pos xpos
      have tGeOne : 1 ≤ t := one_le_inv xpos one_le_x.le
      have bnd1 : Complex.abs ((x : ℂ) ^ s) ≤ x ^ (-(2 : ℝ)) := by
        rw [Complex.abs_cpow_eq_rpow_re_of_pos xpos]
        rw [(by field_simp : x = t⁻¹), Real.inv_rpow tpos.le, inv_le (Real.rpow_pos_of_pos tpos _) (by simp [Real.rpow_pos_of_pos xpos _])]
        have : (t⁻¹ ^ (-(2 : ℝ)))⁻¹ = t ^ (-(2 : ℝ))
        · simp only [inv_inv]
          rw [Real.rpow_neg xpos.le, inv_inv, Real.rpow_neg tpos.le, Real.inv_rpow xpos.le, inv_inv]
        rw [this]
        apply Real.rpow_le_rpow_of_exponent_le tGeOne -- (Real.rpow_pos_of_pos tpos s.re)
        linarith [s_memRect.1]
      change Complex.abs ((x : ℂ) ^ s) * (Complex.abs (s + 1))⁻¹ ≤ _
      refine mul_le_mul bnd1 bnd2 (inv_nonneg_of_nonneg (AbsoluteValue.nonneg Complex.abs _)) ?_
      convert sq_nonneg t
      rw [← rpow_two t, Real.rpow_neg]
      simp only [rpow_two, inv_pow]
      exact xpos.le
  · simp only [sub_re, neg_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
      sub_zero, add_re, add_zero, neg_le_self_iff]
    linarith
  · simp only [sub_im, neg_im, ofReal_im, neg_zero, mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul,
      zero_add, zero_sub, add_im, neg_le_self_iff]
    linarith

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
      (Square (-1) c \ {-1})) := by
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
    RectangleIntegral' (f x) (-c - c * I) (c + c * I) = 1 := by
/-%%
\begin{proof}\leanok
\uses{diffBddAtZero, ResidueTheoremOnRectangleWithSimplePole,
existsDifferentiableOn_of_bddAbove}
For $c>0$ sufficiently small,
%%-/
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (by linarith : (0 : ℝ) < 1 / 2), diffBddAtZero xpos]
  intro c hc bddAbove
  obtain ⟨cpos, _⟩ := hc
  have RectSub : Square 0 c \ {0} ⊆ {0, -1}ᶜ := by
    refine fun s ⟨hs, hs0⟩ ↦ not_or.mpr ⟨hs0, ?_⟩
    rw [Square, mem_Rect (by simpa using by linarith) (by simp [cpos.le])] at hs
    replace hs : -c ≤ s.re ∧ s.re ≤ c ∧ -c ≤ s.im ∧ s.im ≤ c := by simpa using hs
    simpa [Complex.ext_iff] using fun h ↦ by linarith
  have fHolo : HolomorphicOn (f x) (Square 0 c \ {0}) := (isHolomorphicOn xpos).mono RectSub
  have f1Holo : HolomorphicOn ((f x) - (fun (s : ℂ) ↦ 1 / s)) (Square 0 c \ {0}) :=
    fHolo.sub (by simpa using differentiableOn_inv.mono fun s hs ↦ hs.2)

  have RectMemNhds : Square 0 c ∈ 𝓝 0 := square_mem_nhds 0 (ne_of_gt cpos)
/-%% $x^s/(s(s+1))$ is equal to $1/s$ plus a function, $g$, say,
holomorphic in the whole rectangle (by Lemma \ref{diffBddAtZero}).
%%-/
  obtain ⟨g, gHolo, g_eq_fDiff⟩ := existsDifferentiableOn_of_bddAbove RectMemNhds f1Holo bddAbove
  simp_rw [Square, add_zero] at fHolo gHolo RectMemNhds

--%% Now apply Lemma \ref{ResidueTheoremOnRectangleWithSimplePole}.
  refine ResidueTheoremOnRectangleWithSimplePole ?_ ?_ RectMemNhds gHolo ?_
  · simpa using cpos.le
  · simpa using cpos.le
  · convert g_eq_fDiff using 3 <;> simp [Square]
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
    VerticalIntegral' (f x) σ = 1 + VerticalIntegral' (f x) (-1 / 2) := by
/-%%
\begin{proof}\leanok
\uses{sigmaNegOneHalfPull, residueAtZero}
By Lemma \ref{sigmaNegOneHalfPull}, the difference of the two vertical integrals is equal
to the integral over a rectangle with corners at $-1/2-iT$ and $\sigma+iT$ (for any $T>0$). By
Lemma \ref{RectanglePullToNhdOfPole}, for $c>0$ sufficiently small, the integral over
this rectangle is equal to the integral over a square with corners at $-c-i*c$ and $c+i*c$ for $c>0$
sufficiently small.
By Lemma \ref{residueAtZero}, the integral over this square is equal to $1$.
\end{proof}
%%-/
  apply eq_add_of_sub_eq
  have xpos : 0 < x := zero_lt_one.trans x_gt_one
  rw [VerticalIntegral', ← mul_sub, sigmaNegOneHalfPull xpos σ_pos (by norm_num : (0 : ℝ) < 1)]
  have h_nhds : Rectangle (-1 / 2 - I * ↑1) (↑σ + I * ↑1) ∈ 𝓝 0 := by
    rw [rectangle_mem_nhds_iff]
    suffices 0 ∈ Ioo (-1 / 2) σ ×ℂ Ioo (-1) 1 by simpa [(by linarith : -1/2 ≤ σ)] using this
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num
    exact σ_pos
  have fHolo : HolomorphicOn (f x) (Rectangle (-1 / 2 - I * ↑1) (↑σ + I * ↑1) \ {0}) := by
    apply (isHolomorphicOn xpos).mono
    refine fun s ⟨hs, hs0⟩ ↦ not_or.mpr ⟨hs0, ?_⟩
    rw [mem_Rect (by simpa using by linarith) (by simp)] at hs
    replace hs : -1 / 2 ≤ s.re ∧ s.re ≤ σ ∧ -1 ≤ s.im ∧ s.im ≤ 1 := by simpa using hs
    simpa [Complex.ext_iff] using fun h ↦ by linarith
  have := RectanglePullToNhdOfPole (by simpa using by linarith) (by simp) h_nhds fHolo
  obtain ⟨c, hcf, hc⟩ := ((residueAtZero xpos).and this).exists_mem
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhdsWithin_iff.mp hcf
  replace hεc : ε/2 ∈ c := hεc ⟨mem_ball_iff_norm.mpr (by simp [abs_of_pos hε, hε]), half_pos hε⟩
  obtain ⟨h1, h2⟩ := hc (ε/2) hεc
  unfold RectangleIntegral' at h1
  replace : (2 * π * I) ≠ 0 := by norm_num; exact pi_ne_zero
  replace h1 :
      RectangleIntegral (f x) (-↑(ε / 2) - ↑(ε / 2) * I) (↑(ε / 2) + ↑(ε / 2) * I) = 2 * ↑π * I
  · field_simp at h1 ⊢
    exact h1
  push_cast at *
  simp_rw [h2, add_zero, mul_comm I, h1, one_div_mul_cancel this]

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
/-%%
\begin{proof}\leanok
Pull contour from $(-3/2)$ to $(\sigma)$.
\end{proof}
%%-/
  unfold VerticalIntegral'
  congr 1
  exact contourPull (by linarith) (not_mem_uIcc_of_gt (by linarith) (by linarith))
    (not_mem_uIcc_of_gt (by linarith) (by linarith))

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
\uses{isHolomorphicOn, residuePull1,
residuePull2, contourPull3, integralPosAux, vertIntBoundLeft,
tendsto_rpow_atTop_nhds_zero_of_norm_gt_one, limitOfConstantLeft}
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on $\C \setminus {0,1}$.
%%-/
  set f : ℂ → ℂ := (fun s ↦ x^s / (s * (s + 1)))
  have : HolomorphicOn f {0, -1}ᶜ := isHolomorphicOn (by linarith : 0 < x)
--%% First pull the contour from $(\sigma)$ to $(-1/2)$, picking up a residue $1$ at $s=0$.
  have contourPull₁ : VerticalIntegral' f σ = 1 + VerticalIntegral' f (-1 / 2) :=
    residuePull1 x_gt_one σ_pos
  rw [contourPull₁]
--%% Next pull the contour from $(-1/2)$ to $(-3/2)$, picking up a residue $-1/x$ at $s=-1$.
  have contourPull₂ : VerticalIntegral' f (-1 / 2) = -1 / x + VerticalIntegral' f (-3 / 2) :=
    residuePull2 x_gt_one
  rw [contourPull₂]
--%% Then pull the contour all the way to $(\sigma')$ with $\sigma'<-3/2$.
  have contourPull₃ (σ' σ'' : ℝ) (hσ' : σ' ≤ -3/2) (hσ'' : σ'' ≤ -3/2) :
      VerticalIntegral' f σ' = VerticalIntegral' f σ'' :=
    contourPull3 x_gt_one hσ' hσ''
--%% For $\sigma' < -3/2$, the integral is bounded by $x^{\sigma'}\int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt$.
  have VertIntBound : ∃ C, ∀ σ' < -3/2,
      Complex.abs (VerticalIntegral' f σ') ≤ x^σ' * C :=
    vertIntBoundLeft (by linarith : 0 < x)
--%% Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$.
  have AbsVertIntTendsto : Tendsto (Complex.abs ∘ (VerticalIntegral' f)) atBot (𝓝 0)
  · obtain ⟨C, hC⟩ := VertIntBound
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
