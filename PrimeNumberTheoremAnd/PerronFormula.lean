import Mathlib.Analysis.Calculus.ContDiff.Basic
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Uniformly
import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.Asymptotics
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.Wiener

open Asymptotics Complex ComplexConjugate Topology Filter Real MeasureTheory Set

open scoped Interval

/-%%
In this section, we prove the Perron formula, which plays a key role in our proof of Mellin inversion.
%%-/

/-%%
The following is preparatory material used in the proof of the Perron formula, see Lemma \ref{formulaLtOne}.
%%-/

/-%
TODO: move to general section.
\begin{lemma}[zeroTendstoDiff]\label{zeroTendstoDiff}\lean{zeroTendstoDiff}\leanok
If the limit of $0$ is $L₁ - L₂$, then $L₁ = L₂$.
\end{lemma}
%-/
lemma zeroTendstoDiff (L₁ L₂ : ℂ) (f : ℝ → ℂ) (h : ∀ᶠ T in atTop,  f T = 0)
    (h' : Tendsto f atTop (𝓝 (L₂ - L₁))) : L₁ = L₂ := by
  rw [← zero_add L₁, ← @eq_sub_iff_add_eq]
  exact tendsto_nhds_unique (EventuallyEq.tendsto h) h'
/-%
\begin{proof}\leanok
Obvious.
\end{proof}
%-/

/-%
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
%-/
lemma RectangleIntegral_tendsTo_VerticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ - I * T) (σ' + I * T)) atTop
      (𝓝 (VerticalIntegral f σ' - VerticalIntegral f σ)) := by
/-%
\begin{proof}\leanok
Almost by definition.
%-/
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
    mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im, one_mul, zero_add, zero_sub,
    add_im]
  apply Tendsto.sub
  · rewrite [← zero_add (VerticalIntegral _ _), ← zero_sub_zero]
    apply Tendsto.add <| Tendsto.sub (hbot.comp tendsto_neg_atTop_atBot) htop
    exact (intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id).const_smul I
  · exact (intervalIntegral_tendsto_integral hleft tendsto_neg_atTop_atBot tendsto_id).const_smul I
--%\end{proof}

lemma verticalIntegral_eq_verticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hf : HolomorphicOn f ([[σ,  σ']] ×ℂ univ))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    VerticalIntegral f σ = VerticalIntegral f σ' := by
  refine zeroTendstoDiff _ _ _ (univ_mem' fun _ ↦ ?_)
    (RectangleIntegral_tendsTo_VerticalIntegral hbot htop hleft hright)
  exact integral_boundary_rect_eq_zero_of_differentiableOn f _ _
    (hf.mono fun z hrect ↦ ⟨by simpa using hrect.1, trivial⟩)

lemma verticalIntegral_sub_verticalIntegral_eq_squareIntegral {σ σ' : ℝ} {f : ℂ → ℂ} {p : ℂ}
    (hσ: σ < p.re ∧ p.re < σ') (hf : HolomorphicOn f (Icc σ  σ' ×ℂ univ \ {p}))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, VerticalIntegral f σ' - VerticalIntegral f σ =
    RectangleIntegral f (-c - c * I + p) (c + c * I + p) := by
  have : Icc σ σ' ×ℂ univ ∈ 𝓝 p := by
    rw [← mem_interior_iff_mem_nhds, Complex.interior_reProdIm, interior_Icc, interior_univ]
    refine ⟨⟨?_, ?_⟩, trivial⟩ <;> linarith
  obtain ⟨c', hc'0, hc'⟩ := ((nhds_hasBasis_square p).1 _).mp this
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' hc'0] with c ⟨hc0, hcc'⟩
  have hsub : Square p c ⊆ Icc σ σ' ×ℂ univ := (square_subset_square hc0 hcc'.le).trans hc'
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_VerticalIntegral hbot htop hleft hright)
  apply Filter.EventuallyEq.tendsto
  filter_upwards [Filter.Ioi_mem_atTop ((c - p.im) ⊔ (c + p.im))] with y hy
  have : c - p.im < y ∧ c + p.im < y := sup_lt_iff.mp hy
  have : c + σ ≤ p.re := by simpa using (hsub ⟨left_mem_uIcc, left_mem_uIcc⟩).1.1
  have : c + p.re ≤ σ' := by simpa using (hsub ⟨right_mem_uIcc, right_mem_uIcc⟩).1.2
  apply RectanglePullToNhdOfPole'
  · simpa using ⟨by linarith, by linarith, by linarith⟩
  · exact square_mem_nhds p (ne_of_gt hc0)
  · apply RectSubRect' <;> simpa using by linarith
  · refine hf.mono (diff_subset_diff ?_ subset_rfl)
    simpa [Rectangle, uIcc_of_lt (hσ.1.trans hσ.2)] using fun x ⟨hx, _⟩ ↦ ⟨hx, trivial⟩

/-% ** Wrong delimiter on purpose **
\begin{lemma}[RectangleIntegral_tendsTo_UpperU]\label{RectangleIntegral_tendsTo_UpperU}\lean{RectangleIntegral_tendsTo_UpperU}\leanok
Let $\sigma,\sigma' ∈ \mathbb{R}$, and $f : \mathbb{C} \to \mathbb{C}$ such that
the vertical integrals $\int_{(\sigma)}f(s)ds$ and $\int_{(\sigma')}f(s)ds$ exist and
the horizontal integral $\int_{(\sigma)}^{\sigma'}f(x + yi)dx$ vanishes as $y \to \pm \infty$.
Then the limit of rectangle integrals
$$\int_{\sigma+iT}^{\sigma'+iU}f(s)ds$$
as $U\to\infty$ is the ``UpperUIntegral'' of $f$.
\end{lemma}
%-/
lemma RectangleIntegral_tendsTo_UpperU {σ σ' T : ℝ} {f : ℂ → ℂ}
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ + I * T) (σ' + I * U)) atTop
      (𝓝 (UpperUIntegral f σ σ' T)) := by
/-%
\begin{proof}\leanok
\uses{RectangleIntegral, UpperUIntegral}
Almost by definition.
%-/
  have h_re  (s : ℝ) (t : ℝ) : (s  + I * t).re = s  := by simp
  have h_im  (s : ℝ) (t : ℝ) : (s  + I * t).im = t  := by simp
  have hbot : Tendsto (fun (_ : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + T * I)) atTop (𝓝 <| ∫ (x : ℝ) in σ..σ', f (x + T * I)) := by
    exact tendsto_const_nhds
  have hvert (s : ℝ) (int : Integrable (fun (y : ℝ) ↦ f (s + y * I))) :
      Tendsto (fun (U : ℝ) ↦ I * ∫ (y : ℝ) in T..U, f (s + y * I)) atTop (𝓝 <| I * ∫ (y : ℝ) in Ioi T, f (s + y * I)) := by
    exact (intervalIntegral_tendsto_integral_Ioi T int.restrict tendsto_id).const_smul I
  have := ((hbot.sub htop).add (hvert σ' hright)).sub (hvert σ hleft)
  simpa only [RectangleIntegral, UpperUIntegral, h_re, h_im, sub_zero, ←integral_Ici_eq_integral_Ioi]
--%\end{proof}

/-% ** Wrong delimiter on purpose **
\begin{lemma}[RectangleIntegral_tendsTo_LowerU]\label{RectangleIntegral_tendsTo_LowerU}\lean{RectangleIntegral_tendsTo_LowerU}\leanok
Let $\sigma,\sigma' ∈ \mathbb{R}$, and $f : \mathbb{C} \to \mathbb{C}$ such that
the vertical integrals $\int_{(\sigma)}f(s)ds$ and $\int_{(\sigma')}f(s)ds$ exist and
the horizontal integral $\int_{(\sigma)}^{\sigma'}f(x + yi)dx$ vanishes as $y \to -\infty$.
Then the limit of rectangle integrals
$$\int_{\sigma-iU}^{\sigma'-iT}f(s)ds$$
as $U\to\infty$ is the ``LowerUIntegral'' of $f$.
\end{lemma}
%-/
lemma RectangleIntegral_tendsTo_LowerU {σ σ' T : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ - I * U) (σ' - I * T)) atTop
      (𝓝 (- LowerUIntegral f σ σ' T)) := by
/-%
\begin{proof}\leanok
\uses{RectangleIntegral, LowerUIntegral}
Almost by definition.
%-/
  have h_re  (s : ℝ) (t : ℝ) : (s  - I * t).re = s  := by simp
  have h_im  (s : ℝ) (t : ℝ) : (s  - I * t).im = -t  := by simp
  have hbot' : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x - y * I)) atTop (𝓝 0) := by
    convert (hbot.comp tendsto_neg_atTop_atBot) using 1
    ext; simp only [Function.comp_apply, ofReal_neg, neg_mul]; rfl
  have htop : Tendsto (fun (_ : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x - T * I)) atTop (𝓝 <| ∫ (x : ℝ) in σ..σ', f (x - T * I)) :=
    tendsto_const_nhds
  have hvert (s : ℝ) (int : Integrable (fun (y : ℝ) ↦ f (s + y * I))) :
      Tendsto (fun (U : ℝ) ↦ I * ∫ (y : ℝ) in -U..-T, f (s + y * I)) atTop (𝓝 <| I * ∫ (y : ℝ) in Iic (-T), f (s + y * I)) := by
    have := (intervalIntegral_tendsto_integral_Iic (-T) int.restrict tendsto_id).const_smul I
    convert (this.comp tendsto_neg_atTop_atBot) using 1
  have := ((hbot'.sub htop).add (hvert σ' hright)).sub (hvert σ hleft)
  rw [zero_sub] at this
  simp_rw [RectangleIntegral, LowerUIntegral, HIntegral, VIntegral, h_re, h_im, ofReal_neg, neg_mul, neg_add_rev, neg_sub]
  have final : (((-∫ (x : ℝ) in σ..σ', f (↑x - ↑T * I)) + I * ∫ (y : ℝ) in Iic (-T), f (↑σ' + ↑y * I)) -
      I * ∫ (y : ℝ) in Iic (-T), f (↑σ + ↑y * I)) = (-(I * ∫ (y : ℝ) in Iic (-T), f (↑σ + ↑y * I)) +
      ((I * ∫ (y : ℝ) in Iic (-T), f (↑σ' + ↑y * I)) - ∫ (x : ℝ) in σ..σ', f (↑x - ↑T * I))) := by
    ring_nf
  exact final ▸ this
--%\end{proof}

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
    Tendsto (fun (σ : ℝ) ↦ x ^ σ * C) atTop (𝓝 0) := by
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
    Tendsto (fun (σ : ℝ) ↦ x ^ σ * C) atBot (𝓝 0) := by
  have := (zero_lt_one.trans x_gt_one)
  have h := tendsto_rpow_atTop_nhds_zero_of_norm_lt_one (inv_pos.mpr this) (inv_lt_one x_gt_one) C
  convert (h.comp tendsto_neg_atBot_atTop) using 1
  ext; simp only [this.le, inv_rpow, Function.comp_apply, rpow_neg, inv_inv]

/-%%
\begin{proof}\leanok
Standard.
\end{proof}
%%-/

-- TODO: move near `Complex.cpow_neg`?
lemma Complex.cpow_inv_ofReal_pos {a : ℝ} (ha : 0 ≤ a) (r : ℂ) :
    ((a : ℂ) ^ r)⁻¹ = (a : ℂ)⁻¹ ^ r := by
  sorry

lemma Complex.cpow_eq_exp_log_ofReal (x : ℝ) (hx : 0 < x) (y : ℂ) :
    (x : ℂ) ^ y = Complex.exp (Real.log x * y) := by
  simp [← Complex.cpow_eq_pow, Complex.cpow, hx.ne.symm, ← Complex.ofReal_log hx.le]

-- TODO: move near `Complex.mul_cpow_ofReal_nonneg`
lemma Complex.cpow_neg_eq_inv_pow_ofReal_pos {a : ℝ} (ha : 0 < a) (r : ℂ) :
    (a : ℂ) ^ (-r) = (a⁻¹ : ℂ) ^ r := by
  rw [cpow_neg, ← Complex.inv_cpow]
  exact slitPlane_arg_ne_pi (Or.inl ha)

namespace Perron

variable {x σ σ' σ'' T : ℝ}

noncomputable abbrev f (x : ℝ) := fun (s : ℂ) ↦ x ^ s / (s * (s + 1))


lemma f_mul_eq_f {x t : ℝ} (tpos : 0 < t) (xpos : 0 < x) (s : ℂ) : f t s * (x : ℂ) ^ (-s) = f (t / x) s := by
  by_cases s_eq_zero : s = 0
  · simp [f, s_eq_zero]
  by_cases s_eq_neg_one : s = -1
  · simp [f, s_eq_neg_one]
  field_simp [f, mul_ne_zero s_eq_zero (fun hs ↦ add_eq_zero_iff_eq_neg.mp hs |> s_eq_neg_one)]
  convert (Complex.mul_cpow_ofReal_nonneg tpos.le (inv_pos.mpr xpos).le s).symm using 2
  · convert Complex.cpow_neg_eq_inv_pow_ofReal_pos xpos s
    exact ofReal_inv x
  · simp only [ofReal_inv]; rfl

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

lemma integral_one_div_const_add_sq_pos (c : ℝ) (hc : 0 < c) : 0 < ∫ (t : ℝ), 1 / (c + t ^ 2) := by
  have hfun_eq (t : ℝ) : 1 / (c + t ^ 2) = c⁻¹ * (1 + (c.sqrt⁻¹ * t) ^ 2)⁻¹ := by
    field_simp [hc.ne.symm]
  simp_rw [hfun_eq, MeasureTheory.integral_mul_left,
    Measure.integral_comp_mul_left (fun t ↦ (1 + t ^ 2)⁻¹) (a:=c.sqrt⁻¹)]
  simp [abs_eq_self.mpr <| Real.sqrt_nonneg c,
    mul_pos (inv_pos.mpr hc) <| mul_pos (sqrt_pos.mpr hc) Real.pi_pos]

lemma Integrable.one_div_const_add_sq (c : ℝ) (hc : 0 < c) : Integrable fun (t : ℝ) ↦ 1 / (c + t ^ 2) :=
  .of_integral_ne_zero (integral_one_div_const_add_sq_pos c hc).ne'

lemma integralPosAux'_of_le (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (hle : c₁ ≤ c₂) :
    0 < ∫ (t : ℝ), 1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) := by
  have c₂_pos : 0 < c₂ := by linarith
  have hlower (t : ℝ) : 1 / (c₂ + t ^ 2) ≤ 1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) := by
    gcongr
    calc
      _ ≤ (c₂ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt := by gcongr
      _ ≤ c₂ + t ^ 2 := by rw [← Real.sqrt_mul, sqrt_mul_self] <;> positivity
  have hupper (t : ℝ) : 1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) ≤ 1 / (c₁ + t ^ 2)  := by
      gcongr
      calc
        _ ≥ (c₁ + t ^ 2).sqrt * (c₁ + t ^ 2).sqrt := by gcongr
        _ ≥ c₁ + t ^ 2 := by rw [← Real.sqrt_mul, sqrt_mul_self] <;> positivity
  calc 0 < ∫ t, 1 / (c₂ + t^2) := integral_one_div_const_add_sq_pos c₂ c₂_pos
       _ ≤ ∫ t, 1 / (Real.sqrt (c₁ + t^2) * Real.sqrt (c₂ + t^2)) := ?_
  refine integral_mono (Integrable.one_div_const_add_sq c₂ c₂_pos) ?_ hlower
  apply MeasureTheory.Integrable.mono (g := fun t:ℝ ↦ 1/(c₁ + t^2)) <| Integrable.one_div_const_add_sq c₁ c₁_pos
  · refine (measurable_const.div <| Measurable.mul ?_ ?_).aestronglyMeasurable <;>
      exact (measurable_const.add <| measurable_id'.pow_const 2).sqrt
  · refine ae_of_all _ (fun x ↦ ?_)
    repeat rewrite [norm_of_nonneg (by positivity)]
    exact hupper x


lemma integralPosAux' (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (c₂_pos : 0 < c₂) :
    0 < ∫ (t : ℝ), 1 / ((c₁ + t^2).sqrt * (c₂ + t^2).sqrt) := by
  by_cases hc : c₁ ≤ c₂
  · exact integralPosAux'_of_le c₁ c₂ c₁_pos hc
  · convert integralPosAux'_of_le c₂ c₁ c₂_pos (by linarith) using 4; rw [mul_comm]

lemma integralPosAux : 0 < ∫ (t : ℝ), 1 / ((1 + t^2).sqrt * (2 + t^2).sqrt) := by
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
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1+t ^ 2)(2+t ^ 2)|^{1/2}}dt.$$
\end{lemma}
%%-/
lemma vertIntBound (xpos : 0 < x) (σ_gt_one : 1 < σ) :
    ‖VerticalIntegral (f x) σ‖ ≤ x ^ σ * ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt) := by
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (‖σ + t * I‖ * ‖σ + t * I + 1‖) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt) :=
        mul_le_mul_of_nonneg_left ?_ (rpow_nonneg xpos.le _)
  · simp [VerticalIntegral]
  · simp [Complex.abs_cpow_eq_rpow_re_of_pos xpos]
  · simp [integral_mul_left, div_eq_mul_inv]
  by_cases hint : Integrable fun (a : ℝ) ↦ 1 / (‖σ + a * I‖ * ‖σ + a * I + 1‖)
  swap; rw [integral_undef hint]; exact integral_nonneg <| fun t ↦ by positivity
  conv => rhs; rhs; intro a; rhs
  apply integral_mono hint
  · have := integralPosAux
    contrapose! this
    simp_rw [integral_undef this, le_rfl]
  rw [Pi.le_def]
  intro t
  gcongr <;> apply sqrt_le_sqrt
  · simp_rw [normSq_add_mul_I, add_le_add_iff_right, one_le_pow_of_one_le σ_gt_one.le _]
  · rw [add_right_comm, ← ofReal_one, ← ofReal_add, normSq_add_mul_I, add_le_add_iff_right]
    nlinarith
  rfl
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
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1/4+t ^ 2)(2+t ^ 2)|^{1/2}}dt.$$
\end{lemma}
%%-/

lemma vertIntBoundLeft (xpos : 0 < x) :
    ∃ C, ∀ (σ : ℝ) (_ : σ < -3 / 2), ‖VerticalIntegral' (f x) σ‖ ≤ C * x ^ σ := by
/-%%
\begin{proof}\leanok
\uses{VerticalIntegral}
%%-/
  /- This proof is adapted from `vertIntBound` -/
  use 1 / (2 * π) *  ‖(∫ (t : ℝ), 1 / ((4⁻¹ + t ^ 2).sqrt * (4⁻¹ + t ^ 2).sqrt : ℂ))‖
  intro σ hσ
  simp only [VerticalIntegral', abs_of_pos Real.pi_pos, smul_eq_mul, norm_mul, f]
  rw [(by simp [pi_nonneg] : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π)), mul_assoc]
  apply (mul_le_mul_left (by simp [pi_pos])).mpr
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (‖σ + t * I‖ * ‖σ + t * I + 1‖) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / ((4⁻¹ + t ^ 2).sqrt * (4⁻¹ + t ^ 2).sqrt) := ?_
    _ ≤ _ := ?_
  · simp [VerticalIntegral, Real.pi_nonneg]
  · congr with t
    rw [norm_div, Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos xpos, add_re, ofReal_re,
      re_ofReal_mul, I_re, mul_zero, add_zero]
  · simp_rw [div_eq_mul_inv, integral_mul_left, one_mul, Complex.norm_eq_abs, map_mul]
  · gcongr
    by_cases hint : Integrable fun (a : ℝ) ↦ 1 / (‖σ + ↑a * I‖ * ‖σ + ↑a * I + 1‖)
    swap
    · rw [integral_undef hint]
      exact integral_nonneg <| fun t ↦ by simp only [Pi.le_def, Pi.zero_apply]; positivity
    apply integral_mono hint
    · have := integralPosAux' (4⁻¹) (4⁻¹) (by norm_num) (by norm_num)
      contrapose! this
      simp_rw [integral_undef this, le_rfl]
    rw [Pi.le_def]
    intro t
    gcongr <;> apply sqrt_le_sqrt
    · rw [normSq_add_mul_I, add_le_add_iff_right]; ring_nf; nlinarith
    · rw [(by push_cast; ring : σ + t * I + 1 = ofReal' (σ + 1) + t * I),
        normSq_add_mul_I, add_le_add_iff_right]; ring_nf; nlinarith
  · rw [mul_comm]
    gcongr
    · have : 0 ≤ ∫ (t : ℝ), 1 / (sqrt (4⁻¹ + t ^ 2) * sqrt (4⁻¹ + t ^ 2)) := by positivity
      rw [← _root_.abs_of_nonneg this, ← Complex.abs_ofReal]
      apply le_of_eq; congr; norm_cast; exact integral_ofReal.symm
/-%%
Triangle inequality and pointwise estimate.
\end{proof}
%%-/

lemma map_conj (hx : 0 ≤ x) (s : ℂ) : f x (conj s) = conj (f x s) := by
  simp only [f, map_div₀, map_mul, map_add, map_one]
  congr
  rw [cpow_conj, Complex.conj_ofReal]; rw [Complex.arg_ofReal_of_nonneg hx]; exact pi_ne_zero.symm

theorem isTheta_uniformlyOn_uIcc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 [[σ', σ'']] ×ˢ (atBot ⊔ atTop)]
    ((fun y ↦ 1 / y^2) ∘ Prod.snd) := by
  set l := 𝓟 [[σ', σ'']] ×ˢ (atBot ⊔ atTop : Filter ℝ) with hl
  refine IsTheta.div (isTheta_norm_left.mp ?_) ?_
  · suffices (fun (σ, _y) ↦ |x| ^ σ) =Θ[l] fun _ ↦ (1 : ℝ) by
      simpa [Complex.abs_cpow_of_ne_zero <| ofReal_ne_zero.mpr (ne_of_gt xpos),
        arg_ofReal_of_nonneg xpos.le] using this
    exact (continuousOn_const.rpow continuousOn_id fun _ _ ↦ Or.inl <| ne_of_gt (abs_pos_of_pos xpos))
      |>.const_isThetaUniformlyOn_isCompact isCompact_uIcc (by norm_num)
      (fun i _ ↦ ne_of_gt <| rpow_pos_of_pos (abs_pos_of_pos xpos) _) _
  · have h_c {c : ℂ} : (fun (_ : ℝ × ℝ) ↦ c) =o[l] Prod.snd := by
      rewrite [hl, Filter.prod_sup, isLittleO_sup]
      exact ⟨isLittleO_const_snd_atBot c _, isLittleO_const_snd_atTop c _⟩
    have h_yI : (fun ((_σ, y) : ℝ × ℝ) ↦ y * I) =Θ[l] Prod.snd :=
      isTheta_of_norm_eventuallyEq (by simp)
    have h_σ_yI : (fun (σy : ℝ × ℝ) ↦ σy.1 + σy.2 * I) =Θ[l] Prod.snd := by
      refine IsLittleO.add_isTheta ?_ h_yI
      exact continuous_ofReal.continuousOn.const_isBigOUniformlyOn_isCompact isCompact_uIcc
        (by norm_num : ‖(1 : ℂ)‖ ≠ 0) _ |>.trans_isLittleO h_c
    simp_rw [sq]; exact h_σ_yI.mul (h_σ_yI.add_isLittleO h_c)

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
    (fun (y : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + y * I) ∂μ) =O[atBot ⊔ atTop]
    fun y ↦ 1 / y^2 := by
  let g := fun ((σ, y) : ℝ × ℝ) ↦ f x (σ + y * I)
  calc
    _ =Θ[atBot ⊔ atTop] fun (y : ℝ) ↦ ∫ (σ : ℝ) in uIoc σ' σ'', g (σ, y) ∂μ :=
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
    Tendsto (fun (t : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atBot (𝓝 0) := by
/-%%
\begin{proof}\leanok
The numerator is bounded and the denominator tends to infinity.
\end{proof}
%%-/
  have hcast : (fun (y : ℝ) ↦ 1 / y ^ 2) =ᶠ[atBot] fun y ↦ (-y) ^ (-2 : ℝ) := by
    filter_upwards [Iic_mem_atBot 0] with y hy using
      by rw [rpow_neg (neg_nonneg.mpr hy), inv_eq_one_div, rpow_two, neg_sq]
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
    Tendsto (fun (t : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atTop (𝓝 0) := by
/-%%
\begin{proof}\leanok
The numerator is bounded and the denominator tends to infinity.
\end{proof}
%%-/
  have hcast : (fun (y : ℝ) ↦ 1 / y ^ 2) =ᶠ[atTop] fun y ↦ y ^ (-2 : ℝ) := by
    filter_upwards [Ici_mem_atTop 0] with y hy using by rw [rpow_neg hy, inv_eq_one_div, rpow_two]
  refine isBigO_sup.mp (horizontal_integral_isBigO xpos σ' σ'' volume)
    |>.2.trans_eventuallyEq hcast |>.trans_tendsto <| tendsto_rpow_neg_atTop (by norm_num)

lemma contourPull {σ' σ'' : ℝ} (xpos : 0 < x) (hσ0 : 0 ∉ [[σ', σ'']]) (hσ1 : -1 ∉ [[σ', σ'']]) :
    VerticalIntegral (f x) σ' = VerticalIntegral (f x) σ'' := by
  refine verticalIntegral_eq_verticalIntegral ((isHolomorphicOn xpos).mono ?_)
    (tendsto_zero_Lower xpos σ' σ'') (tendsto_zero_Upper xpos σ' σ'')
    (isIntegrable xpos (fun h ↦ hσ0 (h ▸ left_mem_uIcc)) (fun h ↦ hσ1 (h ▸ left_mem_uIcc)))
    (isIntegrable xpos (fun h ↦ hσ0 (h ▸ right_mem_uIcc)) (fun h ↦ hσ1 (h ▸ right_mem_uIcc)))
  rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨hc | hc⟩ <;> simp_all [Complex.ext_iff]

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
vertIntBound, limitOfConstant,
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
  have VertIntBound : ∃ C > 0, ∀ σ' > 1, ‖VerticalIntegral (f x) σ'‖ ≤ x^σ' * C := by
    let C := ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt)
    exact ⟨C, integralPosAux, fun _ ↦ vertIntBound xpos⟩
--%% Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$.
  have AbsVertIntTendsto : Tendsto (Complex.abs ∘ (VerticalIntegral (f x))) atTop (𝓝 0) := by
    obtain ⟨C, _, hC⟩ := VertIntBound
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
    (htop : Tendsto (fun y : ℝ ↦ ∫ (x : ℝ) in σ..σ', f (↑x + ↑y * I)) atTop (𝓝 0))
    (hleft : Integrable fun y : ℝ ↦ f (↑σ + ↑y * I))
    (hright : Integrable fun y : ℝ ↦ f (↑σ' + ↑y * I)) :
    UpperUIntegral f σ σ' T = 0 := by
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_UpperU htop hleft hright)
  apply EventuallyEq.tendsto
  filter_upwards [eventually_ge_atTop T]
  refine fun _ hTU ↦ hf.vanishesOnRectangle fun _ ↦ ?_
  rw [mem_Rect (by simp [hσ]) (by simp [hTU])]
  simpa using by tauto

theorem HolomorphicOn.lowerUIntegral_eq_zero {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ z.im ≤ -T})
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : Integrable fun y : ℝ ↦ f (↑σ + ↑y * I))
    (hright : Integrable fun y : ℝ ↦ f (↑σ' + ↑y * I)) :
    LowerUIntegral f σ σ' T = 0 := by
  suffices h : - LowerUIntegral f σ σ' T = 0 by exact neg_eq_zero.mp h
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_LowerU hbot hleft hright)
  apply EventuallyEq.tendsto
  filter_upwards [eventually_ge_atTop T]
  refine fun _ hTU ↦ hf.vanishesOnRectangle fun _ ↦ ?_
  rw [mem_Rect (by simp [hσ]) (by simp [hTU])]
  simpa using by tauto

lemma sPlusOneNeZero {s : ℂ} (s_ne_neg_one : s ≠ -1) : s + 1 ≠ 0 :=
  fun h ↦ s_ne_neg_one (add_eq_zero_iff_eq_neg.mp h)

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
    field_simp [sPlusOneNeZero, mul_ne_zero]; ring_nf
/-%%
\begin{proof}\leanok
By ring.
\end{proof}
%%-/

variable  {α β : Type*} [LinearOrder β] [NoMaxOrder β] [TopologicalSpace β] [ClosedIciTopology β]
  {y : β} {l : Filter α}

lemma _root_.Filter.Tendsto.eventually_bddAbove {f : α → β} (hf : Tendsto f l (𝓝 y)) :
    ∀ᶠ s in l.smallSets, BddAbove (f '' s) := by
  obtain ⟨y', hy'⟩ := exists_gt y
  obtain ⟨s, hsl, hs⟩ := (eventually_le_of_tendsto_lt hy' hf).exists_mem
  simp_rw [Filter.eventually_smallSets, bddAbove_def]
  refine ⟨s, hsl, fun t ht ↦ ⟨y', fun y hy ↦ ?_⟩⟩
  obtain ⟨x, hxt, hxy⟩ := hy
  exact hxy ▸ hs x (ht hxt)

lemma bddAbove_square_of_tendsto {f : ℂ → β} {x : ℂ} (hf : Tendsto f (𝓝[≠] x) (𝓝 y)) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, BddAbove (f '' (Square x c \ {x})) := by
  obtain ⟨t, htf, ht⟩ := eventually_smallSets.mp hf.eventually_bddAbove
  obtain ⟨ε, hε0, hε⟩ := nhdsWithin_hasBasis (nhds_hasBasis_square x) {x}ᶜ |>.1 t |>.mp htf
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' hε0] with ε' ⟨hε'0, hε'⟩
  exact ht _ <| (diff_subset_diff (square_subset_square hε'0 hε'.le) subset_rfl).trans hε

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
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - 1 / s)) ''
    (Square 0 c \ {0})) := by
/-%%
\begin{proof}\uses{keyIdentity}\leanok
Applying Lemma \ref{keyIdentity}, the
 function $s ↦ x^s/s(s+1) - 1/s = x^s/s - x^0/s - x^s/(1+s)$. The last term is bounded for $s$
 away from $-1$. The first two terms are the difference quotient of the function $s ↦ x^s$ at
 $0$; since it's differentiable, the difference remains bounded as $s\to 0$.
\end{proof}
%%-/
  apply bddAbove_square_of_tendsto
  suffices Tendsto (norm ∘ (fun (s : ℂ) ↦ ↑x ^ s / s - ↑x ^ (0 : ℂ) / s - ↑x ^ s / (1 + s)))
      (𝓝[≠] 0) (𝓝 (‖(deriv (fun (s : ℂ) ↦ (x : ℂ) ^ s) 0) - x ^ (0 : ℂ) / (1 + 0)‖)) by
    apply this.congr'
    filter_upwards [diff_mem_nhdsWithin_compl (isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr (by norm_num : (0 : ℂ) ≠ -1))) {0}] with s hs
    rw [Function.comp_apply, Function.comp_apply, keyIdentity _ hs.2 hs.1, cpow_zero]; ring_nf
  have hx0 : (x : ℂ) ≠ 0 := slitPlane_ne_zero (.inl xpos)
  refine (Tendsto.sub ?_ (tendsto_nhdsWithin_of_tendsto_nhds ?_)).norm
  · convert hasDerivAt_iff_tendsto_slope.mp
      (differentiableAt_id'.const_cpow (.inl hx0)).hasDerivAt using 2
    rw [slope_def_field]; ring
  · exact (continuous_id.const_cpow (.inl hx0)).tendsto 0
      |>.div (tendsto_const_nhds.add tendsto_id) (by norm_num)

/-%%
\begin{lemma}[diffBddAtNegOne]\label{diffBddAtNegOne}\lean{Perron.diffBddAtNegOne}\leanok
Let $x>0$. Then for $0 < c < 1 /2$, we have that the function
$$
s ↦ \frac{x^s}{s(s+1)} - \frac{-x^{-1}}{s+1}
$$
is bounded above on the rectangle with corners at $-1-c-i*c$ and $-1+c+i*c$ (except at $s=-1$).
\end{lemma}
%%-/
lemma diffBddAtNegOne {x : ℝ} (xpos : 0 < x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - (-x⁻¹) / (s+1))) ''
      (Square (-1) c \ {-1})) := by
/-%%
\begin{proof}\uses{keyIdentity}\leanok
Applying Lemma \ref{keyIdentity}, the
 function $s ↦ x^s/s(s+1) - x^{-1}/(s+1) = x^s/s - x^s/(s+1) - (-x^{-1})/(s+1)$. The first term is bounded for $s$
 away from $0$. The last two terms are the difference quotient of the function $s ↦ x^s$ at
 $-1$; since it's differentiable, the difference remains bounded as $s\to -1$.
\end{proof}
%%-/
  apply bddAbove_square_of_tendsto
  suffices Tendsto (norm ∘ (fun (s : ℂ) ↦ ↑x ^ s / s - (↑x ^ s / (s + 1) - x⁻¹ / (s + 1))))
      (𝓝[≠] (-1)) (𝓝 (‖x ^ (-1 : ℂ) / -1 - (deriv (fun (s : ℂ) ↦ (x : ℂ) ^ s) (-1))‖)) by
    apply this.congr'
    filter_upwards [diff_mem_nhdsWithin_compl (isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr (by norm_num : (-1 : ℂ) ≠ 0))) {-1}] with s hs
    rw [Function.comp_apply, Function.comp_apply, keyIdentity _ hs.1 hs.2]
    ring_nf
  have hx0 : (x : ℂ) ≠ 0 := slitPlane_ne_zero (.inl xpos)
  refine (Tendsto.sub (tendsto_nhdsWithin_of_tendsto_nhds ?_) ?_).norm
  · exact ((continuous_id.const_cpow (.inl hx0)).tendsto _).div tendsto_id (by norm_num)
  · convert hasDerivAt_iff_tendsto_slope.mp
      (differentiableAt_id'.const_cpow (.inl hx0)).hasDerivAt using 2
    rw [slope_def_field, cpow_neg_one, ofReal_inv]; ring

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
  any_goals simpa using cpos.le
  convert g_eq_fDiff using 3 <;> simp [Square]
--%%\end{proof}

lemma residueAtNegOne (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (f x) (-c - c * I - 1) (c + c * I - 1) = -x⁻¹ := by
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (by linarith : (0 : ℝ) < 1 / 2), diffBddAtNegOne xpos]
  intro c hc bddAbove
  obtain ⟨cpos, _⟩ := hc
  have h_mem {s : ℂ} (hs : s ∈ Square (-1) c) :
      -c ≤ s.re + 1 ∧ s.re + 1 ≤ c ∧ -c ≤ s.im ∧ s.im ≤ c := by
    rw [Square, mem_Rect (by simpa using by linarith) (by simp [cpos.le])] at hs
    simpa using hs
  have RectSub : Square (-1) c \ {-1} ⊆ {0, -1}ᶜ := by
    refine fun s ⟨hs, hs1⟩ ↦ not_or.mpr ⟨?_, hs1⟩
    simpa [Complex.ext_iff] using fun _ _ ↦ by linarith [h_mem hs]
  have fHolo : HolomorphicOn (f x) (Square (-1) c \ {-1}) := (isHolomorphicOn xpos).mono RectSub
  have f1Holo : HolomorphicOn ((f x) - (fun (s : ℂ) ↦ -x⁻¹ / (s + 1))) (Square (-1) c \ {-1}) := by
    refine fHolo.sub <| (differentiableOn_const _).neg.div ?_ fun x hx ↦ sPlusOneNeZero hx.2
    exact differentiableOn_id.add (differentiableOn_const 1)
  have RectMemNhds : Square (-1) c ∈ 𝓝 (-1) := square_mem_nhds (-1) (ne_of_gt cpos)
  obtain ⟨g, gHolo, g_eq_fDiff⟩ := existsDifferentiableOn_of_bddAbove RectMemNhds f1Holo bddAbove
  simp_rw [Square] at fHolo gHolo RectMemNhds
  refine ResidueTheoremOnRectangleWithSimplePole ?_ ?_ RectMemNhds gHolo ?_
  · simpa using cpos.le
  · simpa using cpos.le
  · convert g_eq_fDiff using 3; simp

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
\uses{residueAtZero}
We pull to a square with corners at $-c-i*c$ and $c+i*c$ for $c>0$
sufficiently small.
By Lemma \ref{residueAtZero}, the integral over this square is equal to $1$.
\end{proof}
%%-/
  apply eq_add_of_sub_eq
  have xpos : 0 < x := zero_lt_one.trans x_gt_one
  have hf : HolomorphicOn (f x) (Icc (-1 / 2) σ ×ℂ univ \ {0}) :=
    (isHolomorphicOn xpos).mono fun s ⟨⟨⟨_, _⟩, _⟩, hs0⟩ hc ↦ hc.casesOn
      (fun hc ↦ hs0 hc) (fun hc ↦ by linarith [show s.re = -1 from congrArg _ hc])
  have := (residueAtZero xpos).and <| verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    (by simpa using ⟨by linarith, by linarith⟩) hf
    (tendsto_zero_Lower xpos _ _) (tendsto_zero_Upper xpos _ _)
    (isIntegrable xpos (by norm_num) (by norm_num)) (isIntegrable xpos (by linarith) (by linarith))
  obtain ⟨c, hcf, hc⟩ := this.exists_mem
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhdsWithin_iff.mp hcf
  obtain hε := hc (ε/2) (hεc ⟨mem_ball_iff_norm.mpr (by simp [abs_of_pos hε, hε]), half_pos hε⟩)
  rw [VerticalIntegral', ← smul_sub, hε.2, ← RectangleIntegral', add_zero, add_zero, hε.1]

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
    VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) (-1 / 2)
    = -1 / x + VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) (-3 / 2) := by
  apply eq_add_of_sub_eq
  have xpos : 0 < x := zero_lt_one.trans x_gt_one
  have hf : HolomorphicOn (f x) (Icc (-3 / 2) (-1 / 2) ×ℂ univ \ {-1}) :=
    (isHolomorphicOn xpos).mono fun s ⟨⟨⟨_, _⟩, _⟩, hs1⟩ hc ↦ hc.casesOn
      (fun hc ↦ by linarith [show s.re = 0 from congrArg _ hc]) (fun hc ↦ hs1 hc)
  have := (residueAtNegOne xpos).and <| verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    (by simpa using ⟨by linarith, by linarith⟩) hf
    (tendsto_zero_Lower xpos _ _) (tendsto_zero_Upper xpos _ _)
    (isIntegrable xpos (by norm_num) (by norm_num)) (isIntegrable xpos (by norm_num) (by norm_num))
  obtain ⟨c, hcf, hc⟩ := this.exists_mem
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhdsWithin_iff.mp hcf
  replace hε := hc (ε/2) (hεc ⟨mem_ball_iff_norm.mpr (by simp [abs_of_pos, hε]), half_pos hε⟩)
  rw [VerticalIntegral', ← smul_sub, hε.2, ← RectangleIntegral', neg_div, one_div, ← ofReal_inv]
  exact hε.1
/-%%
\begin{proof}\leanok
\uses{residueAtNegOne}
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
    VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) σ' = VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) σ'' := by
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
--%% First pull the contour from $(\sigma)$ to $(-1/2)$, picking up a residue $1$ at $s=0$.
  rw [residuePull1 x_gt_one σ_pos]
--%% Next pull the contour from $(-1/2)$ to $(-3/2)$, picking up a residue $-1/x$ at $s=-1$.
  rw [residuePull2 x_gt_one]
--%% Then pull the contour all the way to $(\sigma')$ with $\sigma'<-3/2$.
  have contourPull₃ (σ' σ'' : ℝ) (hσ' : σ' ≤ -3/2) (hσ'' : σ'' ≤ -3/2) :
      VerticalIntegral' f σ' = VerticalIntegral' f σ'' :=
    contourPull3 x_gt_one hσ' hσ''
--%% For $\sigma' < -3/2$, the integral is bounded by $x^{\sigma'}\int_\R\frac{1}{|(1+t ^ 2)(2+t ^ 2)|^{1/2}}dt$.
  have VertIntBound : ∃ C, ∀ σ' < -3/2, ‖VerticalIntegral' f σ'‖ ≤ C * x ^ σ' :=
    vertIntBoundLeft (by linarith : 0 < x)
--%% Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$.
  have AbsVertIntTendsto : Tendsto (Complex.abs ∘ (VerticalIntegral' f)) atBot (𝓝 0) := by
    obtain ⟨C, hC⟩ := VertIntBound
    have := tendsto_rpow_atTop_nhds_zero_of_norm_gt_one x_gt_one C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    · filter_upwards using fun _ ↦ Complex.abs.nonneg' _
    · filter_upwards [eventually_lt_atBot (-3/2)]
      (conv at hC => intro σ hσ; rw [mul_comm]); exact fun _ ↦ hC _
  --%% So pulling contours gives $\int_{(-3/2)}=0$.
  rw [limitOfConstantLeft (σ := -3/2) (Eq.le rfl) contourPull₃ ?_]; ring
  exact tendsto_zero_iff_norm_tendsto_zero.mpr AbsVertIntTendsto
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
