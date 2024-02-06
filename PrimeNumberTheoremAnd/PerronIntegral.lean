import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.Wiener
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Complex Topology Filter Real MeasureTheory Set

/-%%
In this section, we prove the Perron formula, which plays a key role in our proof of Mellin inversion.
%%-/

/-%%
It is very convenient to define integrals along vertical lines in the complex plane, as follows.
\begin{definition}\label{VerticalIntegral}\leanok
Let $f$ be a function from $\mathbb{C}$ to $\mathbb{C}$, and let $\sigma$ be a real number. Then we define
$$\int_{(\sigma)}f(s)ds = \int_{\sigma-i\infty}^{\sigma+i\infty}f(s)ds.$$
\end{definition}
%%-/

noncomputable def VerticalIntegral (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  I • ∫ t : ℝ, f (σ + t * I)

--%% We also have a version with a factor of $1/(2\pi i)$.
noncomputable abbrev VerticalIntegral' (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * VerticalIntegral f σ

/-%%
The following is preparatory material used in the proof of the Perron formula, see Lemma \ref{PerronFormulaLtOne}.
%%-/

/-%%
TODO: move to general section.
\begin{lemma}\label{zeroTendstoDiff}\lean{zeroTendstoDiff}\leanok
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
TODO: Change this to the statement of `HolomorphicOn_of_Perron_function2` and refactor.
\begin{lemma}\label{HolomorphicOn_of_Perron_function}\lean{HolomorphicOn_of_Perron_function}\leanok
Let $x>0$. Then the function $f(s) = x^s/(s(s+1))$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
\end{lemma}
%%-/
lemma HolomorphicOn_of_Perron_function {x : ℝ} (xpos : 0 < x) :
    HolomorphicOn (fun s => x ^ s / (s * (s + 1))) {s | 0 < s.re} := by
/-%%
\begin{proof}\leanok
Composition of differentiabilities.
%%-/
  simp_rw [Complex.cpow_def_of_ne_zero <| ofReal_ne_zero.mpr <| ne_of_gt xpos]
  apply DifferentiableOn.div <| DifferentiableOn.cexp <| DifferentiableOn.const_mul differentiableOn_id _
  · exact DifferentiableOn.mul differentiableOn_id <| DifferentiableOn.add_const differentiableOn_id 1
  · exact fun _ hx ↦ mul_ne_zero (ne_of_apply_ne re <| ne_of_gt hx)
      <| ne_of_apply_ne re <| ne_of_gt <| (lt_add_one 0).trans <| add_lt_add_right (by exact hx) 1
--%%\end{proof}

/-%%
TODO: Move this to general section.
\begin{lemma}\label{RectangleIntegral_tendsTo_VerticalIntegral}\lean{RectangleIntegral_tendsTo_VerticalIntegral}\leanok
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
\begin{lemma}\label{RectangleIntegral_tendsTo_UpperU}\lean{RectangleIntegral_tendsTo_UpperU}\leanok
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
\begin{lemma}\label{RectangleIntegral_tendsTo_LowerU}\lean{RectangleIntegral_tendsTo_LowerU}\leanok
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

-- TODO: upstream to mathlib Arctan.lean
lemma arctan_atTop : Tendsto arctan atTop (𝓝 (π / 2)) :=
  tendsto_nhds_of_tendsto_nhdsWithin (tendsto_Ioo_atTop.mp tanOrderIso.symm.tendsto_atTop)

lemma arctan_atBot : Tendsto arctan atBot (𝓝 (-(π / 2))) :=
  tendsto_nhds_of_tendsto_nhdsWithin (tendsto_Ioo_atBot.mp tanOrderIso.symm.tendsto_atBot)

lemma arctan_ne_zero {x : ℝ} (hx : x ≠ 0) : arctan x ≠ 0 :=
  fun h ↦ hx <| (show arctan.Injective from StrictMono.injective tanOrderIso.symm.strictMono)
    (h.trans arctan_zero.symm)

-- TODO: upstream to mathlib ImproperIntegral.lean
private lemma intervalIntegral_one_div_one_add_sq_tendsto :
    Tendsto (fun i => ∫ (x : ℝ) in -i..i, 1 / (1 + x ^ 2)) atTop (𝓝 π) := by
  convert Tendsto.add arctan_atTop arctan_atTop <;> simp

open MeasureTheory in
lemma integrable_one_div_one_add_sq : Integrable fun (x : ℝ) ↦ 1 / (1 + x ^ 2) := by
  have (x : ℝ) : ‖1 / (1 + x ^ 2)‖ = 1 / (1 + x ^ 2) := norm_of_nonneg (by positivity)
  refine integrable_of_intervalIntegral_norm_tendsto π (fun i ↦ ?_) tendsto_neg_atTop_atBot
    tendsto_id (by simpa only [this] using intervalIntegral_one_div_one_add_sq_tendsto)
  by_cases hi : i = 0
  · rewrite [hi, Set.Ioc_eq_empty (by norm_num)]; exact integrableOn_empty
  · refine (intervalIntegral.intervalIntegrable_of_integral_ne_zero ?_).1
    simp [← two_mul, arctan_ne_zero hi]

open MeasureTheory in
lemma integral_Iic_one_div_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Iic i, 1 / (1 + x ^ 2) = arctan i + (π / 2) :=
  integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan x)
    integrable_one_div_one_add_sq.integrableOn arctan_atBot |>.trans (sub_neg_eq_add _ _)

open MeasureTheory in
lemma integral_Ioi_one_div_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Ioi i, 1 / (1 + x ^ 2) = (π / 2) - arctan i :=
  integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan x)
    integrable_one_div_one_add_sq.integrableOn arctan_atTop

open MeasureTheory in
lemma integral_volume_one_div_one_add_sq : ∫ (x : ℝ), 1 / (1 + x ^ 2) = π :=
  tendsto_nhds_unique (intervalIntegral_tendsto_integral integrable_one_div_one_add_sq
    tendsto_neg_atTop_atBot tendsto_id) intervalIntegral_one_div_one_add_sq_tendsto

/-%%
\begin{lemma}\label{PerronIntegralPosAux}\lean{PerronIntegralPosAux}\leanok
The integral
$$\int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt$$
is positive (and hence convergent - since a divergent integral is zero in Lean, by definition).
\end{lemma}
%%-/
open MeasureTheory in
lemma PerronIntegralPosAux : 0 < ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| := by
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
\begin{lemma}\label{VertIntPerronBound}\lean{VertIntPerronBound}\leanok
\uses{VerticalIntegral}
Let $x>0$, $\sigma>1$, and $x<1$. Then
$$\left|
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt.$$
\end{lemma}
%%-/

lemma VertIntPerronBound {x : ℝ} (xpos : 0 < x) {σ : ℝ} (σ_gt_one : 1 < σ) :
    Complex.abs (VerticalIntegral (fun s ↦ x^s / (s * (s + 1))) σ)
      ≤ x ^ σ * ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| := by
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (Complex.abs (σ + t * I) * Complex.abs (σ + t * I + 1)) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| :=
        mul_le_mul_of_nonneg_left ?_ (rpow_nonneg xpos.le _)
  · simp only [VerticalIntegral, smul_eq_mul, map_mul, abs_I, one_mul, Complex.norm_eq_abs]
  · congr with t
    rw [norm_div, Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos xpos, add_re, ofReal_re,
      re_ofReal_mul, I_re, mul_zero, add_zero]
  · simp_rw [div_eq_mul_inv, MeasureTheory.integral_mul_left, one_mul, Complex.norm_eq_abs, map_mul]
  clear! x
  -- Note: I didn't try to prove this because the result is trivial if it isn't true.
  by_cases hint : MeasureTheory.Integrable fun (a : ℝ) => 1 / (Complex.abs (σ + ↑a * I) * Complex.abs (↑σ + ↑a * I + 1))
  swap
  · rw [MeasureTheory.integral_undef hint]
    apply MeasureTheory.integral_nonneg
    rw [Pi.le_def]
    intro t
    simp only [Pi.zero_apply, one_div, inv_nonneg, abs_nonneg]
  apply MeasureTheory.integral_mono hint
  · have := PerronIntegralPosAux
    contrapose! this
    have := MeasureTheory.integral_undef this
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
Triangle inequality and pointwise estimate.
\end{proof}
%%-/


/-%%
\begin{lemma}\label{PerronFun_integrable}\lean{PerronFun_integrable}\leanok
Let $x>0$ and $\sigma\in\R$. Then
$$\int_{\R}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}d\sigma$$
is integrable.
\end{lemma}
%%-/
lemma PerronFun_integrable {x : ℝ} (xpos : 0 < x) (σ : ℝ) :
    let f := fun (s : ℂ) ↦ x ^ s / (s * (s + 1));
    Integrable fun (t : ℝ) ↦ f (σ + t * I) := by
  sorry
/-%%
\begin{proof}\uses{VertIntPerronBound}
Apply Lemma \ref{VertIntPerronBound}.
\end{proof}
%%-/

/-%%
TODO : Move to general section
\begin{lemma}\label{limitOfConstant}\lean{limitOfConstant}\leanok
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
\begin{lemma}\label{tendsto_rpow_atTop_nhds_zero_of_norm_lt_one}\lean{tendsto_rpow_atTop_nhds_zero_of_norm_lt_one}\leanok
Let $x>0$ and $x<1$. Then
$$\lim_{\sigma\to\infty}x^\sigma=0.$$
\end{lemma}
%%-/
lemma tendsto_rpow_atTop_nhds_zero_of_norm_lt_one {x : ℝ}  (xpos : 0 < x) (x_lt_one : x < 1) (C : ℝ) :
  Tendsto (fun (σ : ℝ) => x ^ σ * C) atTop (𝓝 0) := by
  have := Tendsto.mul_const C (tendsto_rpow_atTop_of_base_lt_one x (by linarith) x_lt_one)
  simp only [rpow_eq_pow, zero_mul] at this
  exact this

/-%%
\begin{proof}\leanok
Standard.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{PerronFun_tendsto_zero_Lower}\lean{PerronFun_tendsto_zero_Lower}\leanok
Let $x>0$ and $\sigma',\sigma''\in\R$. Then
$$\int_{\sigma'}^{\sigma''}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}d\sigma$$
goes to $0$ as $t\to-\infty$.
\end{lemma}
%%-/
lemma PerronFun_tendsto_zero_Lower {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    let f := fun (s : ℂ) ↦ x ^ s / (s * (s + 1));
    Tendsto (fun (t : ℝ) => ∫ (σ : ℝ) in σ'..σ'', f (σ + t * I)) atBot (𝓝 0) := by
  intro f
  dsimp [f]
  sorry
/-%%
\begin{proof}\leanok
The numerator is bounded and the denominator tends to infinity.
\end{proof}
%%-/


/-%%
\begin{lemma}\label{PerronFun_tendsto_zero_Upper}\lean{PerronFun_tendsto_zero_Upper}\leanok
Let $x>0$ and $\sigma',\sigma''\in\R$. Then
$$\int_{\sigma'}^{\sigma''}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}d\sigma$$
goes to $0$ as $t\to\infty$.
\end{lemma}
%%-/
lemma PerronFun_tendsto_zero_Upper {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    let f := fun (s : ℂ) ↦ x ^ s / (s * (s + 1));
    Tendsto (fun (t : ℝ) => ∫ (σ : ℝ) in σ'..σ'', f (σ + t * I)) atTop (𝓝 0) := by
  intro f
  dsimp [f]
  sorry
/-%%
\begin{proof}\leanok
The numerator is bounded and the denominator tends to infinity.
\end{proof}
%%-/

/-%%
We are ready for the first case of the Perron formula, namely when $x<1$:
\begin{lemma}\label{PerronFormulaLtOne}\lean{PerronFormulaLtOne}\leanok
For $x>0$, $\sigma>0$, and $x<1$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =0.
$$
\end{lemma}
%%-/

lemma PerronFormulaLtOne {x : ℝ}  (xpos : 0 < x) (x_lt_one : x < 1)
    {σ : ℝ} (σ_pos : 0 < σ) : VerticalIntegral (fun s ↦ x^s / (s * (s + 1))) σ = 0 := by
/-%%
\begin{proof}\leanok
\uses{HolomorphicOn_of_Perron_function, HolomorphicOn.vanishesOnRectangle, PerronIntegralPosAux,
VertIntPerronBound, limitOfConstant, RectangleIntegral_tendsTo_VerticalIntegral, zeroTendstoDiff,
tendsto_rpow_atTop_nhds_zero_of_norm_lt_one,
PerronFun_tendsto_zero_Lower, PerronFun_tendsto_zero_Upper, PerronFun_integrable}
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
%%-/
  set f : ℂ → ℂ := (fun s ↦ x^s / (s * (s + 1)))
  have fHolo : HolomorphicOn f {s : ℂ | 0 < s.re} := HolomorphicOn_of_Perron_function xpos
--%% The rectangle integral of $f$ with corners $\sigma-iT$ and $\sigma+iT$ is zero.
  have rectInt (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') (T : ℝ) :
      RectangleIntegral f (σ' - I * T) (σ'' + I * T) = 0
  -- TODO: This can be golfed to one line
  · apply fHolo.vanishesOnRectangle --(fun _ h_rect ↦ LT.lt.trans_le (by simp_all) h_rect.1.1)
    intro z h_rect
    simp only [mem_setOf_eq]
    have := h_rect.1.1
    simp only [sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
      sub_zero, add_re, add_zero, inf_le_iff] at this
    cases this <;> linarith [σ'pos, σ''pos]
--%% The limit of this rectangle integral as $T\to\infty$ is $\int_{(\sigma')}-\int_{(\sigma)}$.
  have rectIntLimit (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') :
      Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ' - I * T) (σ'' + I * T))
      atTop (𝓝 (VerticalIntegral f σ'' - VerticalIntegral f σ')) := by
    apply RectangleIntegral_tendsTo_VerticalIntegral
    · exact PerronFun_tendsto_zero_Lower xpos σ' σ''
    · exact PerronFun_tendsto_zero_Upper xpos σ' σ''
    · exact PerronFun_integrable xpos σ'
    · exact PerronFun_integrable xpos σ''
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
    exact ⟨C, PerronIntegralPosAux, fun _ ↦ VertIntPerronBound xpos⟩
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
%-/

/-%%
\begin{lemma}\label{HolomorphicOn_of_Perron_function2}\lean{HolomorphicOn_of_Perron_function2}\leanok
Let $x>1$. Then the function $f(s) = x^s/(s(s+1))$ is holomorphic on $\C\setminus\{0,1\}$.
\end{lemma}
%%-/
lemma HolomorphicOn_of_Perron_function2 {x : ℝ} (x_gt_one : 1 < x) :
    HolomorphicOn (fun s ↦ x^s / (s * (s + 1))) {0, -1}ᶜ := by
  sorry
/-%%
\begin{proof}
Composition of differentiabilities.
\end{proof}
%%-/

/-%%
\begin{lemma}[PerronSigmaNegOneHalfPull]\label{PerronSigmaNegOneHalfPull}
\lean{PerronSigmaNegOneHalfPull}\leanok
Let $x>0$ and $\sigma>0$. Then for all $T>0$, we have that
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds -
\frac 1{2\pi i}
\int_{(-1/2)}\frac{x^s}{s(s+1)}ds =
\int_{-1/2-iT}^{\sigma +iT}\frac{x^s}{s(s+1)}ds,
$$
that is, a rectangle with corners $-1/2-iT$ and $\sigma+iT$.
\end{lemma}
%%-/
lemma PerronSigmaNegOneHalfPull {x : ℝ} (xpos : 0 < x) {σ T : ℝ} (σ_pos : 0 < σ) (Tpos : 0 < T):
    VerticalIntegral (fun s => x ^ s / (s * (s + 1))) σ
    - VerticalIntegral (fun s => x ^ s / (s * (s + 1))) (-1 / 2)
    = RectangleIntegral (fun s => x ^ s / (s * (s + 1))) (-1 / 2 - I * T) (σ + I * T) := by
  sorry
/-%%
\begin{proof}\uses{HolomorphicOn.vanishesOnRectangle}
The integral on $(\sigma)$ minus that on $(-1/2)$, minus the integral on the rectangle, is
the integral over two regions, one in the upper half plane and one in the lower half plane.
In the upper half plane, the shape looks like $|\_|$, with corners at $-1/2+iT$ and $\sigma+iT$.
The integral over that shape is the limit of integrals over rectangles with corners at $-1/2+iT$
and $\sigma+iU$, for $U\to \infty$; each of those rectangles has integral zero.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{PerronResidueAtZero}\lean{PerronResidueAtZero}\leanok
Let $x>0$. Then for all sufficiently small $c>0$, we have that
$$
\frac1{2\pi i}
\int_{-c-i*c}^{c+ i*c}\frac{x^s}{s(s+1)}ds = 1.
$$
\end{lemma}
%%-/
lemma PerronResidueAtZero {x : ℝ} (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (fun (s : ℂ) ↦ x ^ s / (s * (s + 1))) (-c - I * c) (c + I * c) = 1 := by
  sorry

/-%%
\begin{proof}
For $c>0$ sufficiently small, $x^s/(s(s+1))$ is equal to $1/s$ plus a function, $g$, say,
holomorphic in the whole rectangle. The rectangle integral of $g$ is zero. It suffices to
compute the rectangle integral of $1/s$. This is done as described in the proof
of Lemma \ref{ResidueTheoremOnRectangle}. But perhaps it's easier to do it directly
than prove a general theorem.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{PerronResiduePull1}\lean{PerronResiduePull1}\leanok
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
lemma PerronResiduePull1 {x : ℝ} (x_gt_one : 1 < x) {σ : ℝ} (σ_pos : 0 < σ) :
    VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) σ =
    1 + VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) (-1 / 2) := by
  sorry
/-%%
\begin{proof}
\uses{PerronSigmaNegOneHalfPull, PerronResidueAtZero}
By Lemma \ref{PerronSigmaNegOneHalfPull}, the difference of the two vertical integrals is equal
to the integral over a rectangle with corners at $-1/2-iT$ and $\sigma+iT$ (for any $T>0$). By
Lemma \ref{RectanglePullToNhdOfPole}, for $c>0$ sufficiently small, the integral over
this rectangle is equal to the integral over a square with corners at $-c-i*c$ and $c+i*c$ for $c>0$
sufficiently small.
By Lemma \ref{PerronResidueAtZero}, the integral over this square is equal to $1$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{PerronResiduePull2}\lean{PerronResiduePull2}\leanok
For $x>1$, we have
$$
\frac1{2\pi i}
\int_{(-1/2)}\frac{x^s}{s(s+1)}ds = -1/x +
\frac 1{2\pi i}
\int_{(-3/2)}\frac{x^s}{s(s+1)}ds.
$$
\end{lemma}
%%-/
lemma PerronResiduePull2 {x : ℝ} (x_gt_one : 1 < x) :
    VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) (-1 / 2)
    = -1 / x + VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) (-3 / 2) := by
  sorry
/-%%
\begin{proof}
Pull contour from $(-1/2)$ to $(-3/2)$.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{PerronContourPull3}\lean{PerronContourPull3}\leanok
For $x>1$ and $\sigma<-3/2$, we have
$$
\frac1{2\pi i}
\int_{(-3/2)}\frac{x^s}{s(s+1)}ds = \frac 1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds.
$$
\end{lemma}
%%-/
lemma PerronContourPull3 {x : ℝ} (x_gt_one : 1 < x) {σ' σ'' : ℝ} (σ'le : σ' ≤ -3/2) (σ''le : σ'' ≤ -3/2) :
    VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) σ' = VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) σ'' := by
  sorry
/-%%
\begin{proof}
Pull contour from $(-3/2)$ to $(\sigma)$.
\end{proof}
%%-/


/-%%
\begin{lemma}\label{VertIntPerronBoundLeft}\lean{VertIntPerronBoundLeft}\leanok
\uses{VerticalIntegral}
Let $x>1$ and $\sigma<-3/2$. Then
$$\left|
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt.$$
\end{lemma}
%%-/

lemma VertIntPerronBoundLeft {x : ℝ} (x_gt_one : 1 < x) {σ : ℝ} (σle : σ < -3 / 2) :
    Complex.abs (VerticalIntegral' (fun s ↦ x^s / (s * (s + 1))) σ)
      ≤ x ^ σ *
        ((∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)|) / (2 * π)) := by
  sorry
/-%%
\begin{proof}
Triangle inequality and pointwise estimate. Use
\end{proof}
%%-/


/-%%
\begin{lemma}\label{tendsto_rpow_atTop_nhds_zero_of_norm_gt_one}\lean{tendsto_rpow_atTop_nhds_zero_of_norm_gt_one}\leanok
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


/-%%
\begin{lemma}\label{limitOfConstantLeft}\lean{limitOfConstantLeft}\leanok
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
\begin{lemma}\label{PerronFormulaGtOne}\lean{PerronFormulaGtOne}\leanok
For $x>1$ and $\sigma>0$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =1-1/x.
$$
\end{lemma}
%%-/
lemma PerronFormulaGtOne {x : ℝ} (x_gt_one : 1 < x) {σ : ℝ} (σ_pos : 0 < σ) :
    VerticalIntegral' (fun s ↦ x^s / (s * (s + 1))) σ = 1 - 1 / x := by
/-%%
\begin{proof}\leanok
\uses{HolomorphicOn_of_Perron_function2, PerronResiduePull1,
PerronResiduePull2, PerronContourPull3, PerronIntegralPosAux, VertIntPerronBoundLeft,
tendsto_rpow_atTop_nhds_zero_of_norm_gt_one, limitOfConstantLeft}
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on $\C \setminus {0,1}$.
%%-/
  set f : ℂ → ℂ := (fun s ↦ x^s / (s * (s + 1)))
  have : HolomorphicOn f {0, -1}ᶜ := HolomorphicOn_of_Perron_function2 x_gt_one
--%% First pull the contour from $(\sigma)$ to $(-1/2)$, picking up a residue $1$ at $s=0$.
  have contourPull₁ : VerticalIntegral' f σ = 1 + VerticalIntegral' f (-1 / 2) := PerronResiduePull1 x_gt_one σ_pos
  rw [contourPull₁]
--%% Next pull the contour from $(-1/2)$ to $(-3/2)$, picking up a residue $-1/x$ at $s=-1$.
  have contourPull₂ : VerticalIntegral' f (-1 / 2) = -1 / x + VerticalIntegral' f (-3 / 2) := PerronResiduePull2 x_gt_one
  rw [contourPull₂]
--%% Then pull the contour all the way to $(\sigma')$ with $\sigma'<-3/2$.
  have contourPull₃ : ∀ σ' σ'' (_ : σ' ≤ -3/2) (_ : σ'' ≤ -3/2), VerticalIntegral' f σ' = VerticalIntegral' f σ'' := fun σ' σ'' σ'le σ''le ↦ PerronContourPull3 x_gt_one σ'le σ''le
--%% For $\sigma' < -3/2$, the integral is bounded by $x^{\sigma'}\int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt$.
  have VertIntBound : ∃ C > 0, ∀ σ' < -3/2, Complex.abs (VerticalIntegral' f σ') ≤ x^σ' * C
  · let C := ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)|
    have : 0 < C / (2 * π) := div_pos PerronIntegralPosAux (by norm_num [pi_pos])
    exact ⟨C / (2 * π), this, fun _ ↦ VertIntPerronBoundLeft x_gt_one⟩
--%% Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$.
  have AbsVertIntTendsto : Tendsto (Complex.abs ∘ (VerticalIntegral' f)) atBot (𝓝 0)
  · obtain ⟨C, Cpos, hC⟩ := VertIntBound
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
