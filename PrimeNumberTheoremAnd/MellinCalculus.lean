import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.Wiener
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Complex Topology Filter Real

/-%%
In this section, we define the Mellin transform (already in Mathlib, thanks to David Loeffler), prove its inversion formula, and
derive a number of important properties of some special functions and bumpfunctions.

Def: (Already in Mathlib)
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of $f$ to be the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$

[Note: My preferred way to think about this is that we are integrating over the multiplicative group $\mathbb{R}_{>0}$, multiplying by a (not necessarily unitary!) character $|\cdot|^s$, and integrating with respect to the invariant Haar measure $dx/x$. This is very useful in the kinds of calculations carried out below. But may be more difficult to formalize as things now stand. So we
might have clunkier calculations, which ``magically'' turn out just right - of course they're explained by the aforementioned structure...]

%%-/


/-%%
It is very convenient to define integrals along vertical lines in the complex plane, as follows.
\begin{definition}\label{VerticalIntegral}\leanok
Let $f$ be a function from $\mathbb{C}$ to $\mathbb{C}$, and let $\sigma$ be a real number. Then we define
$$\int_{(\sigma)}f(s)ds = \int_{\sigma-i\infty}^{\sigma+i\infty}f(s)ds.$$
\end{definition}

We also have a version with a factor of $1/(2\pi i)$.
%%-/

noncomputable def VerticalIntegral (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  I • ∫ t : ℝ, f (σ + t * I)

noncomputable abbrev VerticalIntegral' (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ∫ t : ℝ, f (σ + t * I)

/-%%
The following is preparatory material used in the proof of the Perron formula, see Lemma \ref{PerronFormulaLtOne}.
%%-/

/-%%
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

theorem HolomorphicOn.vanishesOnRectangle {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (f_holo : HolomorphicOn f U) (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 := by sorry -- mathlib4#9598

/-%%
\begin{lemma}\label{RectangleIntegral_eq_zero}\lean{RectangleIntegral_eq_zero}\leanok
\uses{RectangleIntegral}
Let $\sigma,\sigma',T>0$, and let $f$ be a holomorphic function on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$. Then
the rectangle integral
$$\int_{\sigma-iT}^{\sigma'+iT}f(s)ds = 0.$$
\end{lemma}
%%-/
lemma RectangleIntegral_eq_zero {σ σ' T : ℝ} (σ_pos : 0 < σ) (σ'_pos : 0 < σ')
    {f : ℂ → ℂ} (fHolo : HolomorphicOn f {s | 0 < s.re}) :
    RectangleIntegral f (σ - I * T) (σ' + I * T) = 0 :=
/-%%
\begin{proof}\leanok
Direct application of HolomorphicOn.vanishesOnRectangle (mathlib4#9598).
%%-/
  fHolo.vanishesOnRectangle (fun _ h_rect ↦ LT.lt.trans_le (by simp_all) h_rect.1.1)
--%%\end{proof}


/-%%
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
open MeasureTheory

lemma RectangleIntegral_tendsTo_VerticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) => ∫ (x : ℝ) in σ..σ', f (↑x + ↑(-y) * I)) atTop (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) => ∫ (x : ℝ) in σ..σ', f (↑x + ↑(y) * I)) atTop (𝓝 0))
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
  · rewrite [← zero_add (VerticalIntegral _ _)]
    apply Tendsto.add (by rewrite [← zero_sub_zero]; exact Tendsto.sub hbot htop)
    exact (intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id).const_smul I
  · exact (intervalIntegral_tendsto_integral hleft tendsto_neg_atTop_atBot tendsto_id).const_smul I
--%%\end{proof}

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
Triangle inequality and pointwise estimate. Use
\end{proof}
%%-/

/-%%
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
We are ready for the Perron formula, which breaks into two cases, the first being:
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
\begin{proof}
\uses{HolomorphicOn_of_Perron_function, RectangleIntegral_eq_zero, PerronIntegralPosAux,
VertIntPerronBound, limitOfConstant, RectangleIntegral_tendsTo_VerticalIntegral, zeroTendstoDiff,
tendsto_rpow_atTop_nhds_zero_of_norm_lt_one}
\leanok
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
%%-/
  set f : ℂ → ℂ := (fun s ↦ x^s / (s * (s + 1)))
  have fHolo : HolomorphicOn f {s : ℂ | 0 < s.re} := HolomorphicOn_of_Perron_function xpos
--%% The rectangle integral of $f$ with corners $\sigma-iT$ and $\sigma+iT$ is zero.
  have rectInt (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') (T : ℝ) :
      RectangleIntegral f (σ' - I * T) (σ'' + I * T) = 0 :=
    RectangleIntegral_eq_zero σ'pos σ''pos fHolo
--%% The limit of this rectangle integral as $T\to\infty$ is $\int_{(\sigma')}-\int_{(\sigma)}$.
  have rectIntLimit (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') :
      Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ' - I * T) (σ'' + I * T))
      atTop (𝓝 (VerticalIntegral f σ'' - VerticalIntegral f σ')) :=
    RectangleIntegral_tendsTo_VerticalIntegral σ'pos σ''pos fHolo
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
The second lemma is the case $x>1$.

Here are some auxiliary lemmata for the second case.
%-/

/-%%
\begin{lemma}\label{HolomorphicOn_of_Perron_function2}\lean{HolomorphicOn_of_Perron_function2}\leanok
Let $x>1$. Then the function $f(s) = x^s/(s(s+1))$ is holomorphic on $\C\setminus{0,1}$.
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
\begin{lemma}\label{PerronResiduePull1}\lean{PerronResiduePull1}\leanok
For $x>1$ and $\sigma>0$, we have
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
    VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) σ = 1 + VerticalIntegral' (fun s => x ^ s / (s * (s + 1))) (-1 / 2) := by
  sorry
/-%%
\begin{proof}
Pull contour from $(\sigma)$ to $(-1/2)$.
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

/-%%
\begin{definition}\label{MellinTransform}\lean{MellinTransform}\leanok
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of $f$ to be the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$
\end{definition}
[Note: already exists in Mathlib, with some good API.]
%%-/
noncomputable def MellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi 0, f x * x ^ (s - 1)

/-%%
\begin{theorem}\label{MellinInversion}\lean{MellinInversion}\leanok
Let $f$ be a ``nice'' function from $\mathbb{R}_{>0}$ to $\mathbb{C}$, and let $\sigma$ be sufficiently large. Then
$$f(x) = \frac{1}{2\pi i}\int_{(\sigma)}\mathcal{M}(f)(s)x^{-s}ds.$$
\end{theorem}

[Note: How ``nice''? Schwartz (on $(0,\infty)$) is certainly enough. As we formalize this, we can add whatever conditions are necessary for the proof to go through.]
%%-/
theorem MellinInversion {f : ℝ → ℂ} (σ : ℝ) (hσ : σ > 0) (hf : Continuous f) :
    f = fun (x : ℝ) => VerticalIntegral (fun s ↦ x ^ (-s) * MellinTransform f s) σ  := by
  sorry
/-%%
\begin{proof}
\uses{PerronFormulaLtOne, PerronFormulaGtOne, MellinTransform}
The proof is from [Goldfeld-Kontorovich 2012].
Integrate by parts twice.
$$
\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx = - \int_0^\infty f'(x)x^s\frac{1}{s}dx = \int_0^\infty f''(x)x^{s+1}\frac{1}{s(s+1)}dx.
$$
Assuming $f$ is Schwartz, say, we now have at least quadratic decay in $s$ of the Mellin transform. Inserting this formula into the inversion formula and Fubini-Tonelli (we now have absolute convergence!) gives:
$$
RHS = \frac{1}{2\pi i}\left(\int_{(\sigma)}\int_0^\infty f''(t)t^{s+1}\frac{1}{s(s+1)}dt\right) x^{-s}ds
$$
$$
= \int_0^\infty f''(t) t \left( \frac{1}{2\pi i}\int_{(\sigma)}(t/x)^s\frac{1}{s(s+1)}ds\right) dt.
$$
Apply the Perron formula to the inside:
$$
= \int_x^\infty f''(t) t \left(1-\frac{x}{t}\right)dt
= -\int_x^\infty f'(t) dt
= f(x),
$$
where we integrated by parts (undoing the first partial integration), and finally applied the fundamental theorem of calculus (undoing the second).
\end{proof}
%%-/

/-%%
Finally, we need Mellin Convolutions and properties thereof.
\begin{definition}\label{MellinConvolution}
Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. Then we define the Mellin convolution of $f$ and $g$ to be the function $f\ast g$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$(f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}.$$
\end{definition}
%%-/

/-%%
The Mellin transform of a convolution is the product of the Mellin transforms.
\begin{theorem}\label{MellinConvolutionTransform}
Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. Then
$$\mathcal{M}(f\ast g)(s) = \mathcal{M}(f)(s)\mathcal{M}(g)(s).$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{MellinTransform}
This is a straightforward calculation.
\end{proof}
%%-/

lemma Function.support_id : Function.support (fun x : ℝ => x) = Set.Iio 0 ∪ Set.Ioi 0 := by
  ext x
  simp only [mem_support, ne_eq, Set.Iio_union_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff]

attribute [- simp] one_div

/-%%
Let $\psi$ be a bumpfunction.
\begin{theorem}\label{SmoothExistence}\leanok
There exists a smooth (once differentiable would be enough), nonnegative ``bumpfunction'' $\psi$,
 supported in $[1/2,2]$ with total mass one:
$$
\int_0^\infty \psi(x)\frac{dx}{x} = 1.
$$
\end{theorem}
%%-/

lemma SmoothExistence : ∃ (Ψ : ℝ → ℝ), (∀ n, ContDiff ℝ n Ψ) ∧ (∀ x, 0 ≤ Ψ x) ∧ Ψ.support ⊆ Set.Icc (1 / 2) 2 ∧ ∫ x in Set.Ici 0, Ψ x / x = 1 := by
  suffices h : ∃ (Ψ : ℝ → ℝ), (∀ n, ContDiff ℝ n Ψ) ∧ (∀ x, 0 ≤ Ψ x) ∧ Ψ.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, Ψ x / x
  · rcases h with ⟨Ψ, hΨ, hΨnonneg, hΨsupp, hΨpos⟩
    let c := (∫ x in Set.Ici 0, Ψ x / x)
    use fun y => Ψ y / c
    constructor
    · intro n
      exact ContDiff.div_const (hΨ n) c
    · constructor
      · intro y
        exact div_nonneg (hΨnonneg y) (le_of_lt hΨpos)
      · constructor
        · simp only [Function.support, Set.subset_def, div_ne_zero] at hΨsupp ⊢
          intro y hy
          have := hΨsupp y
          apply this
          simp at hy
          push_neg at hy
          simp [hy.left]
        · simp only [div_right_comm _ c _]
          rw [MeasureTheory.integral_div c]
          apply div_self
          exact ne_of_gt hΨpos

  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3/2) (d := 2) (by linarith) (by linarith) (by linarith)
  rcases this with ⟨Ψ, hΨContDiff, _, hΨ0, hΨ1, hΨSupport⟩
  use Ψ
  use hΨContDiff
  unfold Set.indicator at hΨ0 hΨ1
  simp only [Set.mem_Icc, Pi.one_apply, Pi.le_def, Set.mem_Ioo] at hΨ0 hΨ1
  constructor
  · intro x
    replace hΨ0 := hΨ0 x
    replace hΨ1 := hΨ1 x
    apply le_trans _ hΨ0
    simp [apply_ite]
  constructor
  · simp only [hΨSupport, Set.subset_def, Set.mem_Ioo, Set.mem_Icc, and_imp]
    intro y hy hy'
    exact ⟨by linarith, by linarith⟩
  · rw [MeasureTheory.integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, MeasureTheory.Measure.restrict_apply']
      rw [hΨSupport]
      rw [Function.support_id]
      have : (Set.Ioo (1 / 2 : ℝ) 2 ∩ (Set.Iio 0 ∪ Set.Ioi 0) ∩ Set.Ici 0) = Set.Ioo (1 / 2) 2 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iio, Set.mem_Ioi, Set.mem_union, not_lt, and_true, not_le]
        constructor
        · intros h
          exact h.left.left
        · intros h
          simp [h, and_true, lt_or_lt_iff_ne, ne_eq]
          constructor
          · linarith [h.left]
          · linarith
      simp only [this, Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · rw [Pi.le_def]
      intro y
      simp only [Pi.zero_apply]
      by_cases h : y ∈ Function.support Ψ
      . apply div_nonneg
        · apply le_trans _ (hΨ0 y)
          simp [apply_ite]
        rw [hΨSupport, Set.mem_Ioo] at h
        linarith [h.left]
      . simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x => Ψ x / x) = Set.piecewise (Set.Icc (1 / 2) 2) (fun x => Ψ x / x) 0 := by
        ext x
        simp only [Set.piecewise]
        by_cases hxIcc : x ∈ Set.Icc (1 / 2) 2
        · exact (if_pos hxIcc).symm
        · rw [if_neg hxIcc]
          have hΨx0 : Ψ x = 0 := by
            have hxIoo : x ∉ Set.Ioo (1 / 2) 2 := by
              simp only [Set.mem_Icc, not_and_or, not_le] at hxIcc
              simp [Set.mem_Ioo, Set.mem_Icc]
              intro
              cases hxIcc <;> linarith
            rw [<-hΨSupport] at hxIoo
            simp only [Function.mem_support, ne_eq, not_not] at hxIoo
            exact hxIoo
          simp [hΨx0]
      rw [this]
      apply MeasureTheory.Integrable.piecewise measurableSet_Icc
      · apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.div
        · replace hΨContDiff := hΨContDiff 0
          simp only [contDiff_zero] at hΨContDiff
          exact Continuous.continuousOn hΨContDiff
        · apply continuousOn_id
        · simp only [Set.mem_Icc, ne_eq, and_imp]
          intros
          linarith
      · -- exact? -- fails
        exact MeasureTheory.integrableOn_zero


/-%%
\begin{proof}\leanok
\uses{smooth-ury}
Same idea as Urysohn-type argument.
\end{proof}
%%-/

/-%%
The $\psi$ function has Mellin transform $\mathcal{M}(\psi)(s)$ which is entire and decays (at least) like $1/|s|$.
\begin{theorem}\label{MellinOfPsi}
The Mellin transform of $\psi$ is
$$\mathcal{M}(\psi)(s) =  O\left(\frac{1}{|s|}\right),$$
as $|s|\to\infty$.
\end{theorem}

[Of course it decays faster than any power of $|s|$, but it turns out that we will just need one power.]
%%-/

/-%%
\begin{proof}
\uses{MellinTransform, SmoothExistence}
Integrate by parts once.
\end{proof}
%%-/

/-%%
We can make a delta spike out of this bumpfunction, as follows.
\begin{definition}\label{DeltaSpike}
\uses{SmoothExistence}
Let $\psi$ be a bumpfunction supported in $[1/2,2]$. Then for any $\epsilon>0$, we define the delta spike $\psi_\epsilon$ to be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$\psi_\epsilon(x) = \frac{1}{\epsilon}\psi\left(x^{\frac{1}{\epsilon}}\right).$$
\end{definition}

This spike still has mass one:
\begin{lemma}\label{DeltaSpikeMass}
For any $\epsilon>0$, we have
$$\int_0^\infty \psi_\epsilon(x)\frac{dx}{x} = 1.$$
\end{lemma}
%%-/
/-%%
\begin{proof}
\uses{DeltaSpike}
Substitute $y=x^{1/\epsilon}$, and use the fact that $\psi$ has mass one, and that $dx/x$ is Haar measure.
\end{proof}
%%-/

/-%%
The Mellin transform of the delta spike is easy to compute.
\begin{theorem}\label{MellinOfDeltaSpike}
For any $\epsilon>0$, the Mellin transform of $\psi_\epsilon$ is
$$\mathcal{M}(\psi_\epsilon)(s) = \mathcal{M}(\psi)\left(\epsilon s\right).$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{DeltaSpike, MellinTransform}
Substitute $y=x^{1/\epsilon}$, use Haar measure; direct calculation.
\end{proof}
%%-/

/-%%
In particular, for $s=1$, we have that the Mellin transform of $\psi_\epsilon$ is $1+O(\epsilon)$.
\begin{corollary}\label{MellinOfDeltaSpikeAt1}
For any $\epsilon>0$, we have
$$\mathcal{M}(\psi_\epsilon)(1) =
\mathcal{M}(\psi)(\epsilon)= 1+O(\epsilon).$$
\end{corollary}
%%-/

/-%%
\begin{proof}
\uses{MellinOfDeltaSpike, DeltaSpikeMass}
This is immediate from the above theorem, the fact that $\mathcal{M}(\psi)(0)=1$ (total mass one),
and that $\psi$ is Lipschitz.
\end{proof}
%%-/

/-%%
Let $1_{(0,1]}$ be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$1_{(0,1]}(x) = \begin{cases}
1 & \text{ if }x\leq 1\\
0 & \text{ if }x>1
\end{cases}.$$
This has Mellin transform
\begin{theorem}\label{MellinOf1}
The Mellin transform of $1_{(0,1]}$ is
$$\mathcal{M}(1_{(0,1]})(s) = \frac{1}{s}.$$
\end{theorem}
[Note: this already exists in mathlib]
%%-/

/-%%
What will be essential for us is properties of the smooth version of $1_{(0,1]}$, obtained as the
 Mellin convolution of $1_{(0,1]}$ with $\psi_\epsilon$.
\begin{definition}\label{Smooth1}\uses{MellinOf1, MellinConvolution}
Let $\epsilon>0$. Then we define the smooth function $\widetilde{1_{\epsilon}}$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ by
$$\widetilde{1_{\epsilon}} = 1_{(0,1]}\ast\psi_\epsilon.$$
\end{definition}
%%-/

/-%%
In particular, we have the following
\begin{lemma}\label{Smooth1Properties}
Fix $\epsilon>0$. There is an absolute constant $c>0$ so that:

(1) If $x\leq (1-c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 1.$$

And (2):
if $x\geq (1+c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 0.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{Smooth1, MellinConvolution}
This is a straightforward calculation, using the fact that $\psi_\epsilon$ is supported in $[1/2^\epsilon,2^\epsilon]$.
\end{proof}
%%-/

/-%%
Combining the above, we have the following Main Lemma of this section on the Mellin transform of $\widetilde{1_{\epsilon}}$.
\begin{lemma}\label{MellinOfSmooth1}\uses{Smooth1Properties, MellinConvolutionTransform, MellinOfDeltaSpikeAt1, MellinOfPsi}
Fix  $\epsilon>0$. Then the Mellin transform of $\widetilde{1_{\epsilon}}$ is
$$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = \frac{1}{s}\left(\mathcal{M}(\psi)\left(\epsilon s\right)\right).$$

For any $s$, we have the bound
$$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = O\left(\frac{1}{\epsilon|s|^2}\right).$$

At $s=1$, we have
$$\mathcal{M}(\widetilde{1_{\epsilon}})(1) = (1+O(\epsilon)).$$
\end{lemma}
%%-/
