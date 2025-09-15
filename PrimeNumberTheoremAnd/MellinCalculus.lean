import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import PrimeNumberTheoremAnd.Auxiliary

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`
theorem MeasureTheory.setIntegral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E] [MeasureTheory.SigmaFinite ν]
    [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ] (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by
  apply integral_integral_swap
  convert hf.integrable
  exact Measure.prod_restrict s t

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

lemma MeasureTheory.integral_comp_mul_right_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_mul_right_Ioi (fun y ↦ f y / y) 0 ha
  simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at this
  rw [← integral_smul] at this
  rw [← this, setIntegral_congr_fun (by simp)]
  intro _ _
  simp only [RCLike.real_smul_eq_coe_mul]
  rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
  exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha

lemma MeasureTheory.integral_comp_mul_right_I0i_haar_real
    (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y :=
  MeasureTheory.integral_comp_mul_right_I0i_haar f ha

lemma MeasureTheory.integral_comp_mul_left_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a * y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  convert integral_comp_mul_right_I0i_haar f ha using 5; ring

-- TODO: generalize to `RCLike`
lemma MeasureTheory.integral_comp_rpow_I0i_haar_real (f : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
    ∫ (y : ℝ) in Ioi 0, |p| * f (y ^ p) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  rw [← integral_comp_rpow_Ioi (fun y ↦ f y / y) hp, setIntegral_congr_fun (by simp)]
  intro y hy
  have ypos : 0 < y := mem_Ioi.mp hy
  simp [field, rpow_sub_one ypos.ne']

lemma MeasureTheory.integral_comp_inv_I0i_haar (f : ℝ → 𝕂) :
    ∫ (y : ℝ) in Ioi 0, f (1 / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_rpow_Ioi (fun y ↦ f y / y) (p := -1) (by simp)
  rw [← this, setIntegral_congr_fun (by simp)]
  intro y hy
  have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
  field_simp [RCLike.real_smul_eq_coe_mul]
  simp [field, RCLike.real_smul_eq_coe_mul, rpow_neg_one]
  ring_nf
  simp [field]

lemma MeasureTheory.integral_comp_div_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  calc
    _ = ∫ (y : ℝ) in Ioi 0, f (a * y) / y := ?_
    _ = _ := integral_comp_mul_left_I0i_haar f ha
  convert (integral_comp_inv_I0i_haar fun y ↦ f (a * (1 / y))).symm using 4
  · rw [mul_one_div]
  · rw [one_div_one_div]

theorem Complex.ofReal_rpow {x : ℝ} (h : x > 0) (y : ℝ) :
    (((x : ℝ) ^ (y : ℝ)) : ℝ) = (x : ℂ) ^ (y : ℂ) := by
  rw [rpow_def_of_pos h, ofReal_exp, ofReal_mul, Complex.ofReal_log h.le,
    Complex.cpow_def_of_ne_zero]
  simp only [ne_eq, ofReal_eq_zero, ne_of_gt h, not_false_eq_true]

@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

lemma Function.support_mul_subset_of_subset {s : Set ℝ} {f g : ℝ → 𝕂} (fSupp : f.support ⊆ s) :
    (f * g).support ⊆ s := by
  simp_rw [support_mul', inter_subset, subset_union_of_subset_right fSupp]

lemma Function.support_of_along_fiber_subset_subset {α β M : Type*} [Zero M]
    {f : α × β → M} {s : Set α} {t : Set β}
    (hx : ∀ (y : β), (fun x ↦ f (x, y)).support ⊆ s)
    (hy : ∀ (x : α), (fun y ↦ f (x, y)).support ⊆ t) :
    f.support ⊆ s ×ˢ t := by
  intro ⟨x, y⟩ hxy
  constructor
  · exact hx y (by simp only [Function.mem_support, ne_eq] at hxy ⊢; exact hxy)
  · exact hy x (by simp only [Function.mem_support, ne_eq] at hxy ⊢; exact hxy)

lemma Function.support_deriv_subset_Icc {a b : ℝ} {f : ℝ → 𝕂}
    (fSupp : f.support ⊆ Set.Icc a b) :
    (deriv f).support ⊆ Set.Icc a b := by
    have := support_deriv_subset (f := fun x ↦ f x)
    dsimp [tsupport] at this
    have := subset_trans this <| closure_mono fSupp
    rwa [closure_Icc] at this

lemma IntervalIntegral.integral_eq_integral_of_support_subset_Icc {a b : ℝ} {μ : Measure ℝ} [NoAtoms μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (h : f.support ⊆ Icc a b) :
    ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ := by
  rcases le_total a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc, indicator_eq_self.2 h]
  · by_cases hab2 : b = a
    · rw [hab2] at h ⊢
      simp only [intervalIntegral.integral_same]
      simp only [Icc_self] at h
      have : ∫ (x : ℝ), f x ∂μ = ∫ (x : ℝ) in {a}, f x ∂μ := by
        rw [ ← integral_indicator (by simp), indicator_eq_self.2 h]
      rw [this, integral_singleton]; simp [Measure.real]
    · rw [Icc_eq_empty_iff.mpr <| by exact fun x ↦ hab2 <| le_antisymm hab x, subset_empty_iff,
          Function.support_eq_empty_iff] at h; simp [h]

lemma SetIntegral.integral_eq_integral_inter_of_support_subset {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set ℝ} {f : ℝ → E} (h : f.support ⊆ t) (ht : MeasurableSet t) :
    ∫ x in s, f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [← setIntegral_indicator ht, indicator_eq_self.2 h]

lemma SetIntegral.integral_eq_integral_inter_of_support_subset_Icc {a b} {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} {f : ℝ → E} (h : f.support ⊆ Icc a b) (hs : Icc a b ⊆ s) :
    ∫ x in s, f x ∂μ = ∫ x in Icc a b, f x ∂μ := by
  rw [SetIntegral.integral_eq_integral_inter_of_support_subset h measurableSet_Icc,
      inter_eq_self_of_subset_right hs]

lemma intervalIntegral.norm_integral_le_of_norm_le_const' {a b C : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hab : a ≤ b) (h : ∀ x ∈ (Icc a b), ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  exact fun x hx ↦ h x <| mem_Icc_of_Ioc <| uIoc_of_le hab ▸ hx

lemma Filter.TendstoAtZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f (𝓝[>]0) (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioo_mem_nhdsGT ha] with c hc; replace hc := (mem_Ioo.mp hc).2
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.TendstoAtTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f atTop (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioi_mem_atTop b] with c hc; rw [mem_Ioi] at hc
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.BigO_zero_atZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[𝓝[>] 0] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < a)] with c hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h, (mem_Ioo.mp hc).2]

lemma Filter.BigO_zero_atTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[atTop] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioi_mem_atTop b] with c hc; replace hc := mem_Ioi.mp hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h]

lemma deriv.ofReal_comp' {f : ℝ → ℝ} :
    deriv (fun x : ℝ ↦ (f x : ℂ)) = (fun x ↦ ((deriv f) x : ℂ)) :=
  funext fun _ ↦ deriv.ofReal_comp

lemma deriv.comp_ofReal' {e : ℂ → ℂ} (hf : Differentiable ℂ e) :
    deriv (fun x : ℝ ↦ e x) = fun (x : ℝ) ↦ deriv e x :=
  funext fun _ ↦ deriv.comp_ofReal (hf.differentiableAt)

/-%%
\begin{lemma}[PartialIntegration]\label{PartialIntegration}\lean{PartialIntegration}\leanok
Let $f, g$ be once differentiable functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$ so that $fg'$
and $f'g$ are both integrable, and $f\cdot g (x)\to 0$ as $x\to 0^+,\infty$.
Then
$$
\int_0^\infty f(x)g'(x) dx = -\int_0^\infty f'(x)g(x)dx.
$$
\end{lemma}
%%-/
/-- *Need differentiability, and decay at `0` and `∞`* -/
lemma PartialIntegration (f g : ℝ → ℂ)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0))
    (gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0))
    (lim_at_zero : Tendsto (f * g) (𝓝[>] 0) (𝓝 0))
    (lim_at_inf : Tendsto (f * g) atTop (𝓝 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx ↦ fDiff.hasDerivAt (Ioi_mem_nhds hx))
    (fun x hx ↦ gDiff.hasDerivAt (Ioi_mem_nhds hx))
    fDerivgInt gDerivfInt lim_at_zero lim_at_inf
/-%%
\begin{proof}\leanok
Partial integration.
\end{proof}
%%-/

lemma PartialIntegration_of_support_in_Icc {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a) (h : a ≤ b)
    (fSupp : f.support ⊆ Set.Icc a b)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fderivCont : ContinuousOn (deriv f) (Ioi 0))
    (gderivCont : ContinuousOn (deriv g) (Ioi 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  have Icc_sub : Icc a b ⊆ Ioi 0 := (Icc_subset_Ioi_iff h).mpr ha
  have fderivSupp := Function.support_deriv_subset_Icc fSupp
  have fgSupp : (f * g).support ⊆ Icc a b := Function.support_mul_subset_of_subset fSupp
  have fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fSupp).mp
    exact fDiff.continuousOn.mono Icc_sub |>.mul (gderivCont.mono Icc_sub) |>.integrableOn_Icc
  have gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fderivSupp).mp
    exact fderivCont.mono Icc_sub |>.mul (gDiff.continuousOn.mono Icc_sub) |>.integrableOn_Icc
  have lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0) := TendstoAtZero_of_support_in_Icc (f * g) ha fgSupp
  have lim_at_inf : Tendsto (f * g) atTop (𝓝 0) := TendstoAtTop_of_support_in_Icc (f * g) fgSupp
  apply PartialIntegration f g fDiff gDiff fDerivgInt gDerivfInt lim_at_zero lim_at_inf

/-%%
In this section, we define the Mellin transform (already in Mathlib, thanks to David Loeffler),
prove its inversion formula, and
derive a number of important properties of some special functions and bumpfunctions.

Def: (Already in Mathlib)
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of
$f$ to be the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$

[Note: My preferred way to think about this is that we are integrating over the multiplicative
group $\mathbb{R}_{>0}$, multiplying by a (not necessarily unitary!) character $|\cdot|^s$, and
integrating with respect to the invariant Haar measure $dx/x$. This is very useful in the kinds
of calculations carried out below. But may be more difficult to formalize as things now stand. So
we might have clunkier calculations, which ``magically'' turn out just right - of course they're
explained by the aforementioned structure...]

%%-/


local notation (name := mellintransform) "𝓜" => mellin


/-%%
Finally, we need Mellin Convolutions and properties thereof.
\begin{definition}[MellinConvolution]\label{MellinConvolution}\lean{MellinConvolution}
\leanok
Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. Then we define the
Mellin convolution of $f$ and $g$ to be the function $f\ast g$ from $\mathbb{R}_{>0}$
to $\mathbb{C}$ defined by
$$(f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}.$$
\end{definition}
%%-/
noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y

/-%%
Let us start with a simple property of the Mellin convolution.
\begin{lemma}[MellinConvolutionSymmetric]\label{MellinConvolutionSymmetric}
\lean{MellinConvolutionSymmetric}\leanok
Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{R}$ or $\mathbb{C}$, for $x\neq0$,
$$
  (f\ast g)(x)=(g\ast f)(x)
  .
$$
\end{lemma}
%%-/
lemma MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
    MellinConvolution f g x = MellinConvolution g f x := by
  unfold MellinConvolution
  calc
    _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
    _ = _ := ?_
  · rw [← integral_comp_mul_right_I0i_haar (fun y ↦ f y * g (x / y)) xpos]
    simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
  · convert (integral_comp_inv_I0i_haar fun y ↦ f (y * x) * g (1 / y)).symm using 3
    rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]
/-%%
\begin{proof}\leanok
  \uses{MellinConvolution}
  By Definition \ref{MellinConvolution},
  $$
    (f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}
  $$
  in which we change variables to $z=x/y$:
  $$
    (f\ast g)(x) = \int_0^\infty f(x/z)g(z)\frac{dz}{z}
    =(g\ast f)(x)
    .
  $$
\end{proof}
%%-/
open Pointwise in
lemma support_MellinConvolution_subsets {f g : ℝ → 𝕂} {A B : Set ℝ} (hf : f.support ⊆ A) (hg : g.support ⊆ B) : (MellinConvolution f g).support ⊆ A * B := by
  rw [Function.support_subset_iff'] at hf hg ⊢
  intro x hx
  unfold MellinConvolution
  simp only [Set.mem_mul, not_exists, not_and] at hx
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (by measurability)]
  intro y hy
  simp only [mem_Ioi] at hy
  simp only [Pi.zero_apply, div_eq_zero_iff, mul_eq_zero, map_eq_zero]
  left
  by_cases hyA : y ∈ A
  · right
    apply hg
    intro hxyB
    apply hx _ hyA _ hxyB
    field_simp
  · left
    apply hf _ hyA

open Pointwise in
lemma support_MellinConvolution (f g : ℝ → 𝕂) : (MellinConvolution f g).support ⊆ f.support * g.support :=
  support_MellinConvolution_subsets subset_rfl subset_rfl

/-%%
The Mellin transform of a convolution is the product of the Mellin transforms.
\begin{theorem}[MellinConvolutionTransform]\label{MellinConvolutionTransform}
\lean{MellinConvolutionTransform}\leanok
Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$ such that
\begin{equation}
  (x,y)\mapsto f(y)\frac{g(x/y)}yx^{s-1}
  \label{eq:assm_integrable_Mconv}
\end{equation}
is absolutely integrable on $[0,\infty)^2$.
Then
$$\mathcal{M}(f\ast g)(s) = \mathcal{M}(f)(s)\mathcal{M}(g)(s).$$
\end{theorem}
%%-/
lemma MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun x y ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
      (Ioi 0 ×ˢ Ioi 0)) :
    𝓜 (MellinConvolution f g) s = 𝓜 f s * 𝓜 g s := by
  dsimp [mellin, MellinConvolution]
  set f₁ : ℝ × ℝ → ℂ := fun ⟨x, y⟩ ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
  calc
    _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioi 0, f₁ (x, y) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f₁ (x, y) := setIntegral_integral_swap _ hf
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * g (x / y) / ↑y * ↑x ^ (s - 1) := rfl
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * g (x * y / y) / ↑y * ↑(x * y) ^ (s - 1) * y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * ↑y ^ (s - 1) * (g x * ↑x ^ (s - 1)) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, f y * ↑y ^ (s - 1) * ∫ (x : ℝ) in Ioi 0, g x * ↑x ^ (s - 1) := ?_
    _ = _ := integral_mul_const _ _
  <;> try (rw [setIntegral_congr_fun (by simp)]; intro y hy; simp only [ofReal_mul])
  · simp only [integral_mul_const, f₁, mul_comm]
  · simp only [integral_mul_const]
    have := integral_comp_mul_right_Ioi (fun x ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)) 0 hy
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := slitPlane_ne_zero (Or.inl hy)
    field_simp at this ⊢
    simp [field] at this ⊢
    rw [← this]
    field_simp
    congr with x
    ring_nf
  · rw [setIntegral_congr_fun (by simp)]
    intro x hx
    have y_ne_zeroℝ : y ≠ 0 := ne_of_gt (mem_Ioi.mp hy)
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := by exact_mod_cast y_ne_zeroℝ
    field_simp
    rw [mul_cpow_ofReal_nonneg hy.le hx.le]
    ring
  · apply integral_const_mul
  · congr <;> ext <;> ring

/-%%
\begin{proof}\leanok
\uses{MellinConvolution}
By Definitions \ref{MellinTransform} and \ref{MellinConvolution}
$$
  \mathcal M(f\ast g)(s)=
  \int_0^\infty \int_0^\infty f(y)g(x/y)x^{s-1}\frac{dy}ydx
$$
By (\ref{eq:assm_integrable_Mconv}) and Fubini's theorem,
$$
  \mathcal M(f\ast g)(s)=
  \int_0^\infty \int_0^\infty f(y)g(x/y)x^{s-1}dx\frac{dy}y
$$
in which we change variables from $x$ to $z=x/y$:
$$
  \mathcal M(f\ast g)(s)=
  \int_0^\infty \int_0^\infty f(y)g(z)y^{s-1}z^{s-1}dzdy
$$
which, by Definition \ref{MellinTransform}, is
$$
  \mathcal M(f\ast g)(s)=
  \mathcal M(f)(s)\mathcal M(g)(s)
  .
$$

\end{proof}
%%-/

lemma mem_within_strip (σ₁ σ₂ : ℝ) :
  {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂} ∈ 𝓟 {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂} := by simp

lemma MellinOfPsi_aux {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    {s : ℂ} (hs : s ≠ 0) :
    ∫ (x : ℝ) in Ioi 0, (ν x) * (x : ℂ) ^ (s - 1) =
    - (1 / s) * ∫ (x : ℝ) in Ioi 0, (deriv ν x) * (x : ℂ) ^ s := by
  let g (s : ℂ) := fun (x : ℝ)  ↦ x ^ s / s
  have gderiv {s : ℂ} (hs : s ≠ 0) {x: ℝ} (hx : x ∈ Ioi 0) :
      deriv (g s) x = x ^ (s - 1) := by
    have := HasDerivAt.cpow_const (c := s) (hasDerivAt_id (x : ℂ)) (Or.inl hx)
    simp_rw [mul_one, id_eq] at this
    rw [deriv_div_const, deriv.comp_ofReal (e := fun x ↦ x ^ s)]
    · rw [this.deriv, mul_div_right_comm, div_self hs, one_mul]
    · apply hasDerivAt_deriv_iff.mp
      simp only [this.deriv, this]
  calc
    _ =  ∫ (x : ℝ) in Ioi 0, ↑(ν x) * deriv (@g s) x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv (fun x ↦ ↑(ν x)) x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * x ^ s / s := by simp only [mul_div, g]
    _ = _ := ?_
  · rw [setIntegral_congr_fun (by simp)]
    intro _ hx
    simp only [gderiv hs hx]
  · apply PartialIntegration_of_support_in_Icc (ν ·) (g s)
      (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
    · simpa only [Function.support_subset_iff, ne_eq, ofReal_eq_zero]
    · exact (Differentiable.ofReal_comp_iff.mpr (diffν.differentiable (by norm_num))).differentiableOn
    · refine DifferentiableOn.div_const ?_ s
      intro a ha
      refine DifferentiableAt.comp_ofReal (e := fun x ↦ x ^ s) ?_ |>.differentiableWithinAt
      apply differentiableAt_fun_id.cpow (differentiableAt_const s) <| by exact Or.inl ha
    · simp only [deriv.ofReal_comp']
      exact continuous_ofReal.comp (diffν.continuous_deriv (by norm_num)) |>.continuousOn
    · apply ContinuousOn.congr (f := fun (x : ℝ) ↦ (x : ℂ) ^ (s - 1)) ?_ fun x hx ↦ gderiv hs hx
      exact Continuous.continuousOn (by continuity) |>.cpow continuousOn_const (by simp)
  · congr; funext; congr
    apply (hasDerivAt_deriv_iff.mpr ?_).ofReal_comp.deriv
    exact diffν.contDiffAt.differentiableAt (by norm_num)
  · simp only [neg_mul, neg_inj]
    conv => lhs; rhs; intro; rw [← mul_one_div, mul_comm]
    rw [integral_const_mul]

/-%%
The $\nu$ function has Mellin transform $\mathcal{M}(\nu)(s)$ which is entire and decays (at
least) like $1/|s|$.
\begin{theorem}[MellinOfPsi]\label{MellinOfPsi}\lean{MellinOfPsi}\leanok
The Mellin transform of $\nu$ is
$$\mathcal{M}(\nu)(s) =  O\left(\frac{1}{|s|}\right),$$
as $|s|\to\infty$ with $\sigma_1 \le \Re(s) \le 2$.
\end{theorem}

[Of course it decays faster than any power of $|s|$, but it turns out that we will just need one
power.]
%%-/

-- filter-free version:
lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (Continuous.comp (by continuity) <| diffν.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  let σ₂ : ℝ := 2
  let C : ℝ := f a * 2 ^ σ₂ * (3 / 2)
  have mainBnd : ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ 2 → ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
    intro σ₁ σ₁pos s hs₁ hs₂
    have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs₁]
    simp only [mellin, f, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, smul_eq_mul, mul_comm]
    gcongr; simp
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ := le_abs_self _
      _ ≤ _ := ?_
    · simp_rw [norm_integral_le_integral_norm]
    · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
      · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
        apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * 2 ^ σ₂)
        (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
        rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
            intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx;
        have f_bound := isMaxOn_iff.mp max x hx
        have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
          have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
          exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
        convert mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]
  have Cnonneg : 0 ≤ C := by
    have hh := mainBnd 1 (by norm_num) ((3 : ℂ) / 2) (by norm_num) (by norm_num)
    have hhh : 0 ≤ ‖𝓜 (fun x ↦ (ν x : ℂ)) ((3 : ℂ) / 2)‖ := by positivity
    have hhhh : 0 < ‖(3 : ℂ) / 2‖⁻¹ := by norm_num
    have := hhh.trans hh
    exact (mul_nonneg_iff_of_pos_right hhhh).mp this
  by_cases CeqZero : C = 0
  · refine ⟨1, by linarith, ?_⟩
    intro ε εpos s hs₁ hs₂
    have := mainBnd ε εpos s hs₁ hs₂
    rw [CeqZero, zero_mul] at this
    have : 0 ≤ 1 * ‖s‖⁻¹ := by positivity
    linarith
  · exact ⟨C, lt_of_le_of_ne Cnonneg fun a ↦ CeqZero (id (Eq.symm a)), mainBnd⟩


-- #exit

-- lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
--     (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
--     (fun s ↦ ‖𝓜 (ν ·) s‖)
--     =O[𝓟 {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂}]
--       fun s ↦ 1 / ‖s‖ := by
--   let f := fun (x : ℝ) ↦ ‖deriv ν x‖
--   have cont : ContinuousOn f (Icc (1 / 2) 2) :=
--     (Continuous.comp (by continuity) <| diffν.continuous_deriv (by norm_num)).continuousOn
--   obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
--   rw [Asymptotics.isBigO_iff]
--   use f a * 2 ^ σ₂ * (3 / 2)
--   filter_upwards [mem_within_strip σ₁ σ₂] with s hs
--   have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs.1]
--   simp only [MellinTransform, f, MellinOfPsi_aux diffν suppν s_ne_zero, norm_norm, norm_mul]
--   conv => rhs; rw [mul_comm]
--   gcongr; simp
--   calc
--     _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
--     _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
--     _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ := le_abs_self _
--     _ ≤ _ := ?_
--   · simp_rw [norm_integral_le_integral_norm]
--   · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
--     · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
--       apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
--     · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
--   · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * 2 ^ σ₂)
--       (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
--     · simp only [Real.norm_eq_abs, Complex.norm_eq_abs, abs_ofReal, map_mul] at this ⊢
--       rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
--           intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
--     · intro x hx;
--       have f_bound := isMaxOn_iff.mp max x hx
--       have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
--         rw [Complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
--         have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
--         have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
--         exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs.2
--       convert mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]

-- -- filter-free version:
-- lemma MellinOfPsi' {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
--     (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
--     {σ₁ σ₂ : ℝ} (σ₁pos : 0 < σ₁) (σ₁_lt_σ₂ : σ₁ < σ₂) :
--     ∃ C > 0, ∀ (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ σ₂),
--     ‖𝓜 (ν ·) s‖ ≤ C * ‖s‖⁻¹ := by
--   have' := MellinOfPsi diffν suppν σ₁pos σ₂
--   rw [Asymptotics.isBigO_iff] at this
--   obtain ⟨C, mainBnd⟩ := this
--   simp only [one_div, norm_inv, norm_norm,
--     eventually_principal, mem_setOf_eq, and_imp] at mainBnd
--   by_cases h : C = 0
--   · refine ⟨1, by positivity, ?_⟩
--     intro s hs₁ hs₂
--     have := mainBnd s hs₁ hs₂
--     rw [h] at this
--     apply le_trans this <| by norm_num
--   · push_neg at h
--     have fnonneg : 0 ≤ C := by
--       have hh := mainBnd ((σ₂ + σ₁) / 2) (by norm_cast; linarith) (by norm_cast; linarith)
--       have : 0 ≤ ‖𝓜 (fun x ↦ ↑(ν x)) ((σ₂ + σ₁) / 2)‖ := by positivity
--       have hhh : 0 ≤ C * ‖(σ₂ + σ₁) / 2‖⁻¹ := by
--         exact_mod_cast this.trans hh
--       have : 0 < ‖(σ₂ + σ₁) / 2‖⁻¹ := by
--         simp only [norm_div, Real.norm_eq_abs, Real.norm_ofNat, inv_div, Nat.ofNat_pos,
--           div_pos_iff_of_pos_left, abs_pos, ne_eq]
--         norm_num
--         linarith
--       exact (mul_nonneg_iff_of_pos_right this).mp hhh
--     have fpos : 0 < C := by
--       exact lt_of_le_of_ne fnonneg h.symm
--     exact ⟨C, fpos, mainBnd⟩

/-%%
\begin{proof}\leanok
\uses{SmoothExistence}
Integrate by parts:
$$
\left|\int_0^\infty \nu(x)x^s\frac{dx}{x}\right| =
\left|-\int_0^\infty \nu'(x)\frac{x^{s}}{s}dx\right|
$$
$$
\le \frac{1}{|s|} \int_{1/2}^2|\nu'(x)|x^{\Re(s)}dx.
$$
Since $\Re(s)$ is bounded, the right-hand side is bounded by a
constant times $1/|s|$.
\end{proof}
%%-/

/-%%
We can make a delta spike out of this bumpfunction, as follows.
\begin{definition}[DeltaSpike]\label{DeltaSpike}\lean{DeltaSpike}\leanok
\uses{SmoothExistence}
Let $\nu$ be a bumpfunction supported in $[1/2,2]$. Then for any $\epsilon>0$, we define the
delta spike $\nu_\epsilon$ to be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$\nu_\epsilon(x) = \frac{1}{\epsilon}\nu\left(x^{\frac{1}{\epsilon}}\right).$$
\end{definition}
%%-/

noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε

/-%%
This spike still has mass one:
\begin{lemma}[DeltaSpikeMass]\label{DeltaSpikeMass}\lean{DeltaSpikeMass}\leanok
For any $\epsilon>0$, we have
$$\int_0^\infty \nu_\epsilon(x)\frac{dx}{x} = 1.$$
\end{lemma}
%%-/

lemma DeltaSpikeMass {ν : ℝ → ℝ} (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (εpos : 0 < ε) : ∫ x in Ioi 0, ((DeltaSpike ν ε) x) / x = 1 :=
  calc
    _ = ∫ (x : ℝ) in Ioi 0, (|1/ε| * x ^ (1 / ε - 1)) •
      ((fun z ↦ (ν z) / z) (x ^ (1 / ε))) := by
      apply setIntegral_congr_ae measurableSet_Ioi
      filter_upwards with x hx
      simp only [smul_eq_mul, abs_of_pos (one_div_pos.mpr εpos)]
      symm; calc
        _ = (ν (x ^ (1 / ε)) / x ^ (1 / ε)) * x ^ (1 / ε - 1) * (1 / ε) := by ring
        _ = _ := by rw [rpow_sub hx, rpow_one]
        _ = (ν (x ^ (1 / ε)) / x ^ (1 / ε) * x ^ (1 / ε) / x) * (1/ ε) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt (rpow_pos_of_pos hx (1/ε)))]
        _ = (ν (x ^ (1 / ε)) / ε / x) := by ring
    _ = 1 := by
      rw [integral_comp_rpow_Ioi (fun z ↦ (ν z) / z), ← mass_one]
      simp only [ne_eq, div_eq_zero_iff, one_ne_zero, εpos.ne', or_self, not_false_eq_true]

/-%%
\begin{proof}\leanok
\uses{DeltaSpike}
Substitute $y=x^{1/\epsilon}$, and use the fact that $\nu$ has mass one, and that $dx/x$ is Haar
measure.
\end{proof}
%%-/

lemma DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  unfold DeltaSpike
  simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
    not_forall, exists_prop, mem_Icc, and_imp]
  intro x hx h; push_neg at h
  have := suppν <| Function.mem_support.mpr h.1
  simp only [one_div, mem_Icc] at this
  have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
  rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
  refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
  linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]

lemma DeltaSpikeSupport' {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
  intro h
  have : (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x) x = DeltaSpike ν ε x := by simp [xnonneg]
  rw [← this] at h
  exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h

lemma DeltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    x ∉ Icc (2 ^ (-ε)) (2 ^ ε) → DeltaSpike ν ε x = 0 := by
  contrapose!; exact DeltaSpikeSupport' εpos xnonneg suppν

@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (diffν : ContDiff ℝ 1 ν) :
    Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le

lemma DeltaSpikeOfRealContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (diffν : ContDiff ℝ 1 ν) :
    Continuous (fun x ↦ (DeltaSpike ν ε x : ℂ)) :=
  continuous_ofReal.comp <| DeltaSpikeContinuous εpos diffν

/-%%
The Mellin transform of the delta spike is easy to compute.
\begin{theorem}[MellinOfDeltaSpike]\label{MellinOfDeltaSpike}\lean{MellinOfDeltaSpike}\leanok
For any $\epsilon>0$, the Mellin transform of $\nu_\epsilon$ is
$$\mathcal{M}(\nu_\epsilon)(s) = \mathcal{M}(\nu)\left(\epsilon s\right).$$
\end{theorem}
%%-/
theorem MellinOfDeltaSpike (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) s = 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  unfold DeltaSpike
  push_cast
  rw [mellin_div_const, mellin_comp_rpow (fun x ↦ (ν x : ℂ)), abs_of_nonneg (by positivity)]
  simp only [one_div, inv_inv, ofReal_inv, div_inv_eq_mul, real_smul]
  rw [mul_div_cancel_left₀ _ (ne_zero_of_re_pos εpos)]
  ring_nf

/-%%
\begin{proof}\leanok
\uses{DeltaSpike}
Substitute $y=x^{1/\epsilon}$, use Haar measure; direct calculation.
\end{proof}
%%-/

/-%%
In particular, for $s=1$, we have that the Mellin transform of $\nu_\epsilon$ is $1+O(\epsilon)$.
\begin{corollary}[MellinOfDeltaSpikeAt1]\label{MellinOfDeltaSpikeAt1}\lean{MellinOfDeltaSpikeAt1}
\leanok
For any $\epsilon>0$, we have
$$\mathcal{M}(\nu_\epsilon)(1) =
\mathcal{M}(\nu)(\epsilon).$$
\end{corollary}
%%-/

lemma MellinOfDeltaSpikeAt1 (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) 1 = 𝓜 (fun x ↦ (ν x : ℂ)) ε := by
  convert MellinOfDeltaSpike ν εpos 1; simp [mul_one]
/-%%
\begin{proof}\leanok
\uses{MellinOfDeltaSpike, DeltaSpikeMass}
This is immediate from the above theorem.
\end{proof}
%%-/

/-%%
\begin{lemma}[MellinOfDeltaSpikeAt1_asymp]\label{MellinOfDeltaSpikeAt1_asymp}
\lean{MellinOfDeltaSpikeAt1_asymp}\leanok
As $\epsilon\to 0$, we have
$$\mathcal{M}(\nu_\epsilon)(1) = 1+O(\epsilon).$$
\end{lemma}
%%-/
lemma MellinOfDeltaSpikeAt1_asymp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    (fun (ε : ℝ) ↦ (𝓜 (fun x ↦ (ν x : ℂ)) ε) - 1) =O[𝓝[>]0] id := by
  have diff : DifferentiableWithinAt ℝ (fun (ε : ℝ) ↦ 𝓜 (fun x ↦ (ν x : ℂ)) ε - 1) (Ioi 0) 0 := by
    apply DifferentiableAt.differentiableWithinAt
    simp only [(differentiableAt_const _).fun_sub_iff_left]
    refine DifferentiableAt.comp_ofReal ?_
    refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1) ?_ ?_ (by simp) ?_ (by simp)
    · apply (Continuous.continuousOn ?_).locallyIntegrableOn (by simp)
      have := diffν.continuous; continuity
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atTop_of_support_in_Icc (a := 1 / 2) (b := 2)
      rwa [ν.support_ofReal]
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atZero_of_support_in_Icc (a := 1 / 2) (b := 2) (ha := (by norm_num))
      rwa [ν.support_ofReal]
  have := ofReal_zero ▸ diff.isBigO_sub
  simp only [sub_sub_sub_cancel_right, sub_zero] at this
  convert this
  simp only [mellin, zero_sub, cpow_neg_one, smul_eq_mul]
  rw [← ofReal_one, ← mass_one]; convert integral_ofReal.symm; field_simp; simp

-- lemma MellinOfDeltaSpikeAt1_asymp' {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
--     (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
--     (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
--     ∃ (c : ℝ) (_ : 0 < c), ∀ (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
--       ‖(𝓜 (ν ·) ε) - 1‖ ≤ c * ε := by
--   have := MellinOfDeltaSpikeAt1_asymp diffν suppν mass_one
--   rw [Asymptotics.isBigO_iff] at this
--   obtain ⟨c, mainBnd⟩ := this
--   sorry
  -- refine ⟨c, ?_, ?_⟩
  -- · sorry
  -- · intro ε εpos εlt1
  --   rw [Filter.eventually_iff, mem_nhdsWithin] at mainBnd
  --   obtain ⟨u, uopen, zeroinu, hu⟩ := mainBnd
  --   have : ∃ ε₁, 0 < ε₁ ∧ ε₁ < ε ∧ ε₁ < 1 ∧ ε₁ ∈ u := by
  --     sorry

  --   sorry

/-%%
\begin{proof}\leanok
\uses{MellinOfDeltaSpikeAt1,SmoothExistence}
By Lemma \ref{MellinOfDeltaSpikeAt1},
$$
  \mathcal M(\nu_\epsilon)(1)=\mathcal M(\nu)(\epsilon)
$$
which by Definition \ref{MellinTransform} is
$$
  \mathcal M(\nu)(\epsilon)=\int_0^\infty\nu(x)x^{\epsilon-1}dx
  .
$$
Since $\nu(x) x^{\epsilon-1}$ is integrable (because $\nu$ is continuous and compactly supported),
$$
  \mathcal M(\nu)(\epsilon)-\int_0^\infty\nu(x)\frac{dx}x=\int_0^\infty\nu(x)(x^{\epsilon-1}-x^{-1})dx
  .
$$
By Taylor's theorem,
$$
  x^{\epsilon-1}-x^{-1}=O(\epsilon)
$$
so, since $\nu$ is absolutely integrable,
$$
  \mathcal M(\nu)(\epsilon)-\int_0^\infty\nu(x)\frac{dx}x=O(\epsilon)
  .
$$
We conclude the proof using Theorem \ref{SmoothExistence}.
\end{proof}
%%-/

/-%%
Let $1_{(0,1]}$ be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$1_{(0,1]}(x) = \begin{cases}
1 & \text{ if }x\leq 1\\
0 & \text{ if }x>1
\end{cases}.$$
This has Mellin transform
\begin{theorem}[MellinOf1]\label{MellinOf1}\lean{MellinOf1}\leanok
The Mellin transform of $1_{(0,1]}$ is
$$\mathcal{M}(1_{(0,1]})(s) = \frac{1}{s}.$$
\end{theorem}
[Note: this already exists in mathlib]
%%-/
lemma MellinOf1 (s : ℂ) (h : s.re > 0) : 𝓜 ((fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)) s = 1 / s := by
  convert (hasMellin_one_Ioc h).right
  congr

/-%%
\begin{proof}\leanok
This is a straightforward calculation.
\end{proof}
%%-/

/-%%
What will be essential for us is properties of the smooth version of $1_{(0,1]}$, obtained as the
 Mellin convolution of $1_{(0,1]}$ with $\nu_\epsilon$.
\begin{definition}[Smooth1]\label{Smooth1}\lean{Smooth1}
\uses{MellinOf1, MellinConvolution}\leanok
Let $\epsilon>0$. Then we define the smooth function $\widetilde{1_{\epsilon}}$ from
$\mathbb{R}_{>0}$ to $\mathbb{C}$ by
$$\widetilde{1_{\epsilon}} = 1_{(0,1]}\ast\nu_\epsilon.$$
\end{definition}
%%-/
noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

-- This lemma might not be necessary, but the RHS is supported on [0, ∞), which makes results like `support_MellinConvolution_subsets` easier to apply.
lemma Smooth1_def_ite {ν : ℝ → ℝ} {ε x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x = MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x) x := by
  unfold Smooth1
  rw [MellinConvolutionSymmetric _ _ xpos]
  conv => lhs; rw [MellinConvolutionSymmetric _ _ xpos]
  unfold MellinConvolution
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
  simp +contextual
  intro y ypos
  rw [eq_comm, if_neg (by push_neg; positivity)]

/-% ** Wrong delimiters on purpose, no need to include this in blueprint
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%-/

lemma Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
  apply (div_lt_iff₀' εpos).mpr
  have : 1 - 1 / (2 : ℝ) ^ ε = ((2 : ℝ) ^ ε - 1) / (2 : ℝ) ^ ε := by
    rw [sub_div, div_self (by positivity)]
  rw [← Real.log_rpow (by norm_num), rpow_neg (by norm_num), inv_eq_one_div (2 ^ ε), this]
  set c := (2 : ℝ) ^ ε
  have hc : 1 < c := by
    rw [← rpow_zero (2 : ℝ)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
  apply (div_lt_iff₀' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
  let f := (fun x ↦ x * Real.log x - x)
  rw [(by simp [f] : -1 = f 1), (by simp [f] : c * Real.log c - c = f c)]
  have mono: StrictMonoOn f <| Ici 1 := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
      intro x hx; simp only [mem_Ici] at hx; simp only [id_eq, ne_eq]; linarith
    · intro x hx; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
      dsimp only [f]
      rw [deriv_fun_sub, deriv_fun_mul, deriv_log, deriv_id'', one_mul, mul_inv_cancel₀]; simp
      · exact log_pos hx
      · linarith
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_log_iff, ne_eq]; linarith
      · exact differentiableAt_fun_id.mul <| differentiableAt_fun_id.log (by linarith)
      · simp only [differentiableAt_fun_id]
  exact mono (by rw [mem_Ici]) (mem_Ici.mpr <| le_of_lt hc) hc
/-%%
\begin{proof}\leanok
Let $c:=2^\epsilon > 1$, in terms of which we wish to prove
$$
  -1 < c \log c - c .
$$
Letting $f(x):=x\log x - x$, we can rewrite this as $f(1) < f(c)$.
Since
$$
  \frac {d}{dx}f(x) = \log x > 0 ,
$$
$f$ is monotone increasing on [1, \infty), and we are done.
\end{proof}
%%-/


/-%%
In particular, we have the following two properties.
\begin{lemma}[Smooth1Properties_below]\label{Smooth1Properties_below}
\lean{Smooth1Properties_below}\leanok
Fix $\epsilon>0$. There is an absolute constant $c>0$ so that:
If $0 < x \leq (1-c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 1.$$
\end{lemma}
%%-/

lemma Smooth1Properties_below_aux {x ε : ℝ} (hx : x ≤ 1 - Real.log 2 * ε) (εpos : 0 < ε) :
    x < 2 ^ (-ε) := by
  calc
    x ≤ 1 - Real.log 2 * ε := hx
    _ < 2 ^ (-ε) := ?_
  rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
  exact (div_lt_iff₀ εpos).mp <| Smooth1Properties_estimate εpos

lemma Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧ ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1 := by
  set c := Real.log 2; use c
  refine ⟨log_pos (by norm_num), rfl, ?_⟩
  intro ε x εpos xpos hx
  have hx2 := Smooth1Properties_below_aux hx εpos
  rewrite [← DeltaSpikeMass mass_one εpos]
  unfold Smooth1 MellinConvolution
  calc
    _ = ∫ (y : ℝ) in Ioi 0, indicator (Ioc 0 1) (fun y ↦ DeltaSpike ν ε (x / y) / ↑y) y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, DeltaSpike ν ε (x / y) / y := ?_
    _ = _ := integral_comp_div_I0i_haar (fun y ↦ DeltaSpike ν ε y) xpos
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    by_cases h : y ≤ 1 <;> simp [indicator, mem_Ioi.mp hy, h]
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    have : y ≠ 0 := by
      rintro rfl
      simp at hy
    simp only [indicator_apply_eq_self, mem_Ioc, not_and, not_le, div_eq_zero_iff, this, or_false]
    intro hy2; replace hy2 := hy2 <| mem_Ioi.mp hy
    apply DeltaSpikeSupport εpos ?_ suppν
    · simp only [mem_Icc, not_and, not_le]; intro
      linarith [(by apply (div_lt_iff₀ (by linarith)).mpr; nlinarith : x / y < 2 ^ (-ε))]
    · rw [le_div_iff₀ (by linarith), zero_mul]; exact xpos.le

/-%%
\begin{proof}\leanok
\uses{Smooth1, MellinConvolution,DeltaSpikeMass}
Opening the definition, we have that the Mellin convolution of $1_{(0,1]}$ with $\nu_\epsilon$ is
$$
\int_0^\infty 1_{(0,1]}(y)\nu_\epsilon(x/y)\frac{dy}{y}
=
\int_0^1 \nu_\epsilon(x/y)\frac{dy}{y}.
$$
The support of $\nu_\epsilon$ is contained in $[1/2^\epsilon,2^\epsilon]$, so it suffices to consider
$y \in [1/2^\epsilon x,2^\epsilon x]$ for nonzero contributions. If $x < 2^{-\epsilon}$, then the integral is the same as that over $(0,\infty)$:
$$
\int_0^1 \nu_\epsilon(x/y)\frac{dy}{y}
=
\int_0^\infty \nu_\epsilon(x/y)\frac{dy}{y},
$$
in which we change variables to $z=x/y$ (using $x>0$):
$$
\int_0^\infty \nu_\epsilon(x/y)\frac{dy}{y}
=
\int_0^\infty \nu_\epsilon(z)\frac{dz}{z},
$$
which is equal to one by Lemma \ref{DeltaSpikeMass}.
We then choose
$$
  c:=\log 2,
$$
which satisfies
$$
  c > \frac{1-2^{-\epsilon}}\epsilon
$$
by Lemma \ref{Smooth1Properties_estimate}, so
$$
  1-c\epsilon < 2^{-\epsilon}.
$$
\end{proof}
%%-/

lemma Smooth1Properties_above_aux {x ε : ℝ} (hx : 1 + (2 * Real.log 2) * ε ≤ x) (hε : ε ∈ Ioo 0 1) :
    2 ^ ε < x := by
  calc
    x ≥ 1 + (2 * Real.log 2) * ε := hx
    _ > 2 ^ ε := ?_
  refine lt_add_of_sub_left_lt <| (div_lt_iff₀ hε.1).mp ?_
  calc
    2 * Real.log 2 > 2 * (1 - 2 ^ (-ε)) / ε := ?_
    _ > 2 ^ ε * (1 - 2 ^ (-ε)) / ε := ?_
    _ = (2 ^ ε - 1) / ε := ?_
  · have := (mul_lt_mul_left (a := 2) (by norm_num)).mpr <| Smooth1Properties_estimate hε.1
    field_simp at this; simp [this]
  · have : (2 : ℝ) ^ ε < 2 := by
      nth_rewrite 1 [← pow_one 2]
      convert rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) hε.2 <;> norm_num
    have pos: 0 < (1 - 2 ^ (-ε)) / ε := by
      refine div_pos ?_ hε.1
      rw [sub_pos]
      convert rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) (neg_lt_zero.mpr hε.1); norm_num
    have := (mul_lt_mul_right pos).mpr this
    ring_nf at this ⊢
    exact this
  · have : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = (2 : ℝ) ^ (ε - ε) := by
      rw [← rpow_add (by norm_num), add_neg_cancel, sub_self]
    conv => lhs; lhs; ring_nf; rhs; simp [this]

lemma Smooth1Properties_above_aux2 {x y ε : ℝ} (hε : ε ∈ Ioo 0 1) (hy : y ∈ Ioc 0 1)
  (hx2 : 2 ^ ε < x) :
    2 < (x / y) ^ (1 / ε) := by
  obtain ⟨εpos, ε1⟩ := hε
  obtain ⟨ypos, y1⟩ := hy
  calc
    _ > (2 ^ ε / y) ^ (1 / ε) := ?_
    _ = 2 / y ^ (1 / ε) := ?_
    _ ≥ 2 / y := ?_
    _ ≥ 2 := ?_
  · rw [gt_iff_lt, div_rpow, div_rpow, lt_div_iff₀, mul_comm_div, div_self, mul_one]
    <;> try positivity
    · exact rpow_lt_rpow (by positivity) hx2 (by positivity)
    · exact LT.lt.le <| lt_trans (by positivity) hx2
  · rw [div_rpow, ← rpow_mul, mul_div_cancel₀ 1 <| ne_of_gt εpos, rpow_one] <;> positivity
  · have : y ^ (1 / ε) ≤ y := by
      nth_rewrite 2 [← rpow_one y]
      exact rpow_le_rpow_of_exponent_ge ypos y1 (by linarith [one_lt_one_div εpos ε1])
    have pos : 0 < y ^ (1 / ε) := rpow_pos_of_pos ypos _
    rw [ge_iff_le, div_le_iff₀, div_mul_eq_mul_div, le_div_iff₀', mul_comm] <;> try linarith
  · rw [ge_iff_le, le_div_iff₀ <| ypos]; exact (mul_le_iff_le_one_right zero_lt_two).mpr y1
/-%%
\begin{lemma}[Smooth1Properties_above]\label{Smooth1Properties_above}
\lean{Smooth1Properties_above}\leanok
Fix $0<\epsilon<1$. There is an absolute constant $c>0$ so that:
if $x\geq (1+c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 0.$$
\end{lemma}
%%-/
lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧ ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by
  set c := 2 * Real.log 2; use c
  constructor
  · simp only [c, zero_lt_two, mul_pos_iff_of_pos_left]; exact log_pos (by norm_num)
  constructor
  · rfl
  intro ε x hε hx
  have hx2 := Smooth1Properties_above_aux hx hε
  unfold Smooth1 MellinConvolution
  simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have ypos := mem_Ioi.mp hy
  by_cases y1 : y ≤ 1
  swap
  · simp [ypos, y1]
  simp only [mem_Ioi.mp hy, y1, and_self, ↓reduceIte, div_eq_zero_iff]; left
  apply DeltaSpikeSupport hε.1 ?_ suppν
  on_goal 1 =>
    simp only [mem_Icc, not_and, not_le]
  on_goal 2 =>
    suffices h : 2 ^ ε < x / y by
      linarith [(by apply rpow_pos_of_pos (by norm_num) : 0 < (2 : ℝ) ^ ε)]
  all_goals
  try intro
  have : x / y = ((x / y) ^ (1 / ε)) ^ ε := by
    rw [← rpow_mul]
    simp only [one_div, inv_mul_cancel₀ (ne_of_gt hε.1), rpow_one]
    apply div_nonneg_iff.mpr; left;
    exact ⟨(le_trans (rpow_pos_of_pos (by norm_num) ε).le) hx2.le, ypos.le⟩
  rw [this]
  refine rpow_lt_rpow (by norm_num) ?_ hε.1
  exact Smooth1Properties_above_aux2 hε ⟨ypos, y1⟩ hx2
/-%%
\begin{proof}\leanok
\uses{Smooth1, MellinConvolution}
Again the Mellin convolution is
$$\int_0^1 \nu_\epsilon(x/y)\frac{dy}{y},$$
but now if $x > 2^\epsilon$, then the support of $\nu_\epsilon$ is disjoint
from the region of integration, and hence the integral is zero.
We choose
$$
  c:=2\log 2
  .
$$
By Lemma \ref{Smooth1Properties_estimate},
$$
  c > 2\frac{1-2^{-\epsilon}}\epsilon > 2^\epsilon\frac{1-2^{-\epsilon}}\epsilon
  =
  \frac{2^\epsilon-1}\epsilon,
$$
so
$$
  1+c\epsilon > 2^\epsilon.
$$
\end{proof}
%%-/

lemma DeltaSpikeNonNeg_of_NonNeg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
     {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
    0 ≤ DeltaSpike ν ε x := by
  dsimp [DeltaSpike]
  have : 0 < x ^ (1 / ε) := by positivity
  have : 0 ≤ ν (x ^ (1 / ε)) := νnonneg _ this
  positivity

lemma MellinConvNonNeg_of_NonNeg {f g : ℝ → ℝ} (f_nonneg : ∀ x > 0, 0 ≤ f x)
    (g_nonneg : ∀ x > 0, 0 ≤ g x) {x : ℝ} (xpos : 0 < x) :
    0 ≤ MellinConvolution f g x := by
  dsimp [MellinConvolution]
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Ioi
  · intro y ypos; simp only [mem_Ioi] at ypos
    have : 0 ≤ f y := f_nonneg _ ypos
    have : 0 < x / y := by positivity
    have : 0 ≤ g (x / y) := g_nonneg _ this
    positivity

/-%%
\begin{lemma}[Smooth1Nonneg]\label{Smooth1Nonneg}\lean{Smooth1Nonneg}\leanok
If $\nu$ is nonnegative, then $\widetilde{1_{\epsilon}}(x)$ is nonnegative.
\end{lemma}
%%-/
lemma Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ} (xpos : 0 < x)
    (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  dsimp [Smooth1]
  apply MellinConvNonNeg_of_NonNeg ?_ ?_ xpos
  · intro y hy; by_cases h : y ≤ 1 <;> simp [h, hy]
  · intro y ypos; exact DeltaSpikeNonNeg_of_NonNeg νnonneg ypos εpos
/-%%
\begin{proof}\uses{Smooth1, MellinConvolution, DeltaSpike}\leanok
By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
$$
  \widetilde{1_\epsilon}(x)=\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
$$
and all the factors in the integrand are nonnegative.
\end{proof}
%%-/

lemma Smooth1LeOne_aux {x ε : ℝ} {ν : ℝ → ℝ} (xpos : 0 < x) (εpos : 0 < ε)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∫ (y : ℝ) in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
    calc
      _ = ∫ (y : ℝ) in Ioi 0, (ν (y ^ (1 / ε)) / ε) / y := ?_
      _ = ∫ (y : ℝ) in Ioi 0, ν y / y := ?_
      _ = 1 := mass_one
    · have := integral_comp_div_I0i_haar (fun y ↦ ν ((x / y) ^ (1 / ε)) / ε) xpos
      convert this.symm using 1
      congr; funext y; congr; field_simp [mul_comm]
    · have := integral_comp_rpow_I0i_haar_real (fun y ↦ ν y) (one_div_ne_zero εpos.ne')
      rw [ ← this, abs_of_pos <| one_div_pos.mpr εpos]
      field_simp

/-%%
\begin{lemma}[Smooth1LeOne]\label{Smooth1LeOne}\lean{Smooth1LeOne}\leanok
If $\nu$ is nonnegative and has mass one, then $\widetilde{1_{\epsilon}}(x)\le 1$, $\forall x>0$.
\end{lemma}
%%-/
lemma Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by
  unfold Smooth1 MellinConvolution DeltaSpike
  have := Smooth1LeOne_aux xpos εpos mass_one
  calc
    _ = ∫ (y : ℝ) in Ioi 0, (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (ν ((x / y) ^ (1 / ε)) / ε / y) := ?_
    _ ≤ ∫ (y : ℝ) in Ioi 0, (ν ((x / y) ^ (1 / ε)) / ε) / y := ?_
    _ = 1 := this
  · rw [setIntegral_congr_fun (by simp)]
    simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
    intro y hy; aesop
  · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one this) (by simp) ?_
    · refine integrable_of_integral_eq_one this |>.bdd_mul ?_ (by use 1; aesop)
      have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) = indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
        aesop
      simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
      exact aestronglyMeasurable_one
    · simp only [ite_mul, one_mul, zero_mul]
      intro y hy
      by_cases h : y ≤ 1
      · aesop
      field_simp
      simp [mem_Ioc, h, and_false, reduceIte]
      apply mul_nonneg
      · apply νnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
      · simp only [mem_Ioi] at hy
        positivity

/-%%
\begin{proof}\uses{Smooth1,MellinConvolution,DeltaSpike,SmoothExistence}\leanok
By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
$$
  \widetilde{1_\epsilon}(x)=\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
$$
and since $1_{(0,1]}(y)\le 1$, and all the factors in the integrand are nonnegative,
$$
  \widetilde{1_\epsilon}(x)\le\int_0^\infty \frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
$$
(because in mathlib the integral of a non-integrable function is $0$, for the inequality above to be true, we must prove that $\nu((x/y)^{\frac1\epsilon})/y$ is integrable; this follows from the computation below).
We then change variables to $z=(x/y)^{\frac1\epsilon}$:
$$
  \widetilde{1_\epsilon}(x)\le\int_0^\infty \nu(z) \frac{dz}z
$$
which by Theorem \ref{SmoothExistence} is 1.
\end{proof}
%%-/

/-%%
Combining the above, we have the following three Main Lemmata of this section on the Mellin
transform of $\widetilde{1_{\epsilon}}$.
\begin{lemma}[MellinOfSmooth1a]\label{MellinOfSmooth1a}\lean{MellinOfSmooth1a}\leanok
Fix  $\epsilon>0$. Then the Mellin transform of $\widetilde{1_{\epsilon}}$ is
$$\mathcal{M}(\widetilde{1_{\epsilon}})(s) =
\frac{1}{s}\left(\mathcal{M}(\nu)\left(\epsilon s\right)\right).$$
\end{lemma}
%%-/
lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s = s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  let f' : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x
  let f : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x / x
  let g : ℝ → ℂ := fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0
  let F : ℝ × ℝ → ℂ := Function.uncurry fun x y ↦ f y * g (x / y) * (x : ℂ) ^ (s - 1)
  let S := {⟨x, y⟩ : ℝ × ℝ | 0 < x  ∧ x ≤ y ∧ 2 ^ (-ε) ≤ y ∧ y ≤ 2 ^ ε}
  let F' : ℝ × ℝ → ℂ := piecewise S (fun ⟨x, y⟩ ↦ f y * (x : ℂ) ^ (s - 1))
     (fun _ ↦ 0)
  let Tx := Ioc 0 ((2 : ℝ) ^ ε)
  let Ty := Icc ((2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ ε)

  have Seq : S = (Tx ×ˢ Ty) ∩ {(x, y) : ℝ × ℝ | x ≤ y} := by
    ext ⟨x, y⟩; constructor
    · exact fun h ↦ ⟨⟨⟨h.1, le_trans h.2.1 h.2.2.2⟩, ⟨h.2.2.1, h.2.2.2⟩⟩, h.2.1⟩
    · exact fun h ↦  ⟨h.1.1.1, ⟨h.2, h.1.2.1, h.1.2.2⟩⟩
  have SsubI : S ⊆ Ioi 0 ×ˢ Ioi 0 :=
    fun z hz ↦ ⟨hz.1, lt_of_lt_of_le (by apply rpow_pos_of_pos; norm_num) hz.2.2.1⟩
  have SsubT: S ⊆ Tx ×ˢ Ty := by simp_rw [Seq, inter_subset_left]
  have Smeas : MeasurableSet S := by
    rw [Seq]; apply MeasurableSet.inter ?_ <| measurableSet_le measurable_fst measurable_snd
    simp [measurableSet_prod, Tx, Ty]

  have int_F: IntegrableOn F (Ioi 0 ×ˢ Ioi 0) := by
    apply IntegrableOn.congr_fun (f := F') ?_ ?_ (by simp [measurableSet_prod]); swap
    · simp only [F, F', f, g, mul_ite, mul_one, mul_zero]
      intro ⟨x, y⟩ hz
      by_cases hS : ⟨x, y⟩ ∈ S <;> simp only [hS, piecewise]
      <;> simp only [mem_prod, mem_Ioi, mem_setOf_eq, not_and, not_le, S] at hz hS
      · simp [div_pos hz.1 hz.2, (div_le_one hz.2).mpr hS.2.1]
      · by_cases hxy : x / y ≤ 1; swap; simp [hxy]
        have hy : y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
          simp only [mem_Icc, not_and, not_le]; exact hS hz.1 <| (div_le_one hz.2).mp hxy
        simp [DeltaSpikeSupport εpos hz.2.le suppν hy]
    · apply Integrable.piecewise Smeas ?_ integrableOn_zero
      simp only [IntegrableOn, Measure.restrict_restrict_of_subset SsubI]
      apply MeasureTheory.Integrable.mono_measure ?_
      apply MeasureTheory.Measure.restrict_mono' (HasSubset.Subset.eventuallyLE SsubT) le_rfl
      have : volume.restrict (Tx ×ˢ Ty) = (volume.restrict Tx).prod (volume.restrict Ty) := by
        rw [Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
      conv => rw [this]; lhs; intro; rw [mul_comm]
      apply MeasureTheory.Integrable.mul_prod (f := fun x ↦ (x : ℂ) ^ (s - 1))
        (μ := Measure.restrict volume Tx)
      · simp only [Tx]
        rw [← IntegrableOn, integrableOn_Ioc_iff_integrableOn_Ioo,
          intervalIntegral.integrableOn_Ioo_cpow_iff]
        · simp [hs]
        · apply rpow_pos_of_pos (by norm_num)
      · apply (ContinuousOn.div ?_ ?_ ?_).integrableOn_compact isCompact_Icc
        · exact (DeltaSpikeOfRealContinuous εpos diffν).continuousOn
        · exact continuous_ofReal.continuousOn
        · intro x hx; simp only [mem_Icc] at hx; simp only [ofReal_ne_zero]
          linarith [(by apply rpow_pos_of_pos (by norm_num) : (0 : ℝ) < 2 ^ (-ε))]

  have : 𝓜 (MellinConvolution g f') s = 𝓜 g s * 𝓜 f' s := by
    rw [mul_comm, ← MellinConvolutionTransform f' g s (by convert int_F using 1; simp [F, f, f']; field_simp)]
    dsimp [mellin]; rw [setIntegral_congr_fun (by simp)]
    intro x hx; simp_rw [MellinConvolutionSymmetric _ _ <| mem_Ioi.mp hx]

  convert this using 1
  · congr; funext x; convert integral_ofReal.symm
    simp only [MellinConvolution, RCLike.ofReal_div, ite_mul, one_mul, zero_mul, @apply_ite ℝ ℂ,
      algebraMap.coe_zero, g]; rfl
  · rw [MellinOf1 s hs, MellinOfDeltaSpike ν εpos s]
    simp
/-%%
\begin{proof}\uses{Smooth1,MellinConvolutionTransform, MellinOfDeltaSpike, MellinOf1, MellinConvolutionSymmetric}\leanok
By Definition \ref{Smooth1},
$$
  \mathcal M(\widetilde{1_\epsilon})(s)
  =\mathcal M(1_{(0,1]}\ast\nu_\epsilon)(s)
  .
$$
We wish to apply Theorem \ref{MellinConvolutionTransform}.
To do so, we must prove that
$$
  (x,y)\mapsto 1_{(0,1]}(y)\nu_\epsilon(x/y)/y
$$
is integrable on $[0,\infty)^2$.
It is actually easier to do this for the convolution: $\nu_\epsilon\ast 1_{(0,1]}$, so we use Lemma \ref{MellinConvolutionSymmetric}: for $x\neq0$,
$$
  1_{(0,1]}\ast\nu_\epsilon(x)=\nu_\epsilon\ast 1_{(0,1]}(x)
  .
$$
Now, for $x=0$, both sides of the equation are 0, so the equation also holds for $x=0$.
Therefore,
$$
  \mathcal M(\widetilde{1_\epsilon})(s)
  =\mathcal M(\nu_\epsilon\ast 1_{(0,1]})(s)
  .
$$
Now,
$$
  (x,y)\mapsto \nu_\epsilon(y)1_{(0,1]}(x/y)\frac{x^{s-1}}y
$$
has compact support that is bounded away from $y=0$ (specifically $y\in[2^{-\epsilon},2^\epsilon]$ and $x\in(0,y]$), so it is integrable.
We can thus apply Theorem \ref{MellinConvolutionTransform} and find
$$
  \mathcal M(\widetilde{1_\epsilon})(s)
  =\mathcal M(\nu_\epsilon)(s)\mathcal M(1_{(0,1]})(s)
  .
$$
By Lemmas \ref{MellinOf1} and \ref{MellinOfDeltaSpike},
$$
  \mathcal M(\widetilde{1_\epsilon})(s)
  =\frac1s\mathcal M(\nu)(\epsilon s)
  .
$$
\end{proof}
%%-/

/-%%
\begin{lemma}[MellinOfSmooth1b]\label{MellinOfSmooth1b}\lean{MellinOfSmooth1b}\leanok
Given $0<\sigma_1\le\sigma_2$, for any $s$ such that $\sigma_1\le\mathcal Re(s)\le\sigma_2$, we have
$$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = O\left(\frac{1}{\epsilon|s|^2}\right).$$
\end{lemma}
%%-/
lemma MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfPsi diffν suppν
  refine ⟨C, Cpos, ?_⟩
  intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
  rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
  have hh1 : ε * σ₁ ≤ (ε * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hh2 : (ε * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  calc
    ‖s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ = ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
    _                        ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
      gcongr
      convert hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
      simp [abs_eq_self.mpr εpos.le]
    _                        = C * (ε * ‖s‖ ^ 2)⁻¹ := by
      simp only [norm_inv, mul_inv_rev]
      ring

--   rw [Asymptotics.isBigO_iff]
--   simp only [prod_principal_principal, eventually_principal, mem_prod, mem_setOf_eq,
--     and_imp, Prod.forall, norm_norm]
-- --  have' := MellinOfSmooth1a diffν suppν

--   sorry
-- #exit
--   have' := MellinOfPsi diffν suppν --(mul_pos εpos σ₁pos) (σ₂ := ε * σ₂)
--   rw [Asymptotics.isBigO_iff] at this ⊢
--   obtain ⟨c, hc⟩ := this
--   use c
--   simp only [norm_norm, norm_div, norm_one, eventually_principal, mem_setOf_eq] at hc ⊢
--   intro s hs
--   rw [MellinOfSmooth1a ν diffν suppν εpos <| gt_of_ge_of_gt hs.1 σ₁pos]
--   have : ‖𝓜 (fun x ↦ ↑(ν x)) (ε * s)‖ ≤ c * (1 / ‖ε * s‖) := by
--     refine hc (ε * s) ?_
--     simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
--     exact ⟨(mul_le_mul_left εpos).mpr hs.1, (mul_le_mul_left εpos).mpr hs.2⟩
--   convert mul_le_mul_of_nonneg_left (a := 1 / ‖s‖) this ?_ using 1
--   · simp
--   · simp only [Complex.norm_eq_abs, norm_mul, Real.norm_eq_abs, norm_pow, Complex.abs_abs, one_div,
--     mul_inv_rev, abs_ofReal]; ring_nf
--   · exact div_nonneg (by norm_num) (norm_nonneg s)

/-%%
\begin{proof}\uses{MellinOfSmooth1a, MellinOfPsi}\leanok
Use Lemma \ref{MellinOfSmooth1a} and the bound in Lemma \ref{MellinOfPsi}.
\end{proof}
%%-/
/-%%
\begin{lemma}[MellinOfSmooth1c]\label{MellinOfSmooth1c}\lean{MellinOfSmooth1c}\leanok
At $s=1$, we have
$$\mathcal{M}(\widetilde{1_{\epsilon}})(1) = 1+O(\epsilon)).$$
\end{lemma}
%%-/

lemma MellinOfSmooth1c {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    (fun ε ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by
  have h := MellinOfDeltaSpikeAt1_asymp diffν suppν mass_one
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc, Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)] with ε hε hε'
  rw [MellinOfSmooth1a diffν suppν hε'.1 (s := 1) (by norm_num)]
  simp only [inv_one, mul_one, one_mul, id_eq, Real.norm_eq_abs]
  exact hε
/-%%
\begin{proof}\uses{MellinOfSmooth1a, MellinOfDeltaSpikeAt1, MellinOfDeltaSpikeAt1_asymp}\leanok
Follows from Lemmas \ref{MellinOfSmooth1a}, \ref{MellinOfDeltaSpikeAt1} and \ref{MellinOfDeltaSpikeAt1_asymp}.
\end{proof}
%%-/

/-%%
\begin{lemma}[Smooth1ContinuousAt]\label{Smooth1ContinuousAt}\lean{Smooth1ContinuousAt}\leanok
Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in $[1/2,2]$. Then for any $\epsilon>0$, the function
$x \mapsto \int_{(0,\infty)} x^{1+it} \widetilde{1_{\epsilon}}(x) dx$ is continuous at any $y>0$.
\end{lemma}
%%-/
lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  apply ContinuousAt.congr (f := (fun x ↦ MellinConvolution (DeltaSpike SmoothingF ε) (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) x)) _
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply MellinConvolutionSymmetric _ _ hx
  apply continuousAt_of_dominated (bound := (fun x ↦ 2 ^ ε * DeltaSpike SmoothingF ε x))
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Measurable.mul
      · exact Continuous.measurable <| DeltaSpikeContinuous εpos diffSmoothingF
      · apply Measurable.ite _ (by fun_prop) (by fun_prop)
        apply MeasurableSet.congr (s := Ici x) (by measurability)
        ext a
        constructor
        · intro ha
          have apos : 0 < a := lt_of_lt_of_le hx ha
          constructor
          · exact div_pos hx apos
          · exact (div_le_one apos).mpr ha
        · intro ha
          have : 0 < a := (div_pos_iff_of_pos_left hx).mp ha.1
          exact (div_le_one this).mp ha.2
    · fun_prop
  · filter_upwards [lt_mem_nhds ypos] with x hx
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp
    by_cases h : DeltaSpike SmoothingF ε t = 0
    · simp [h]
    push_neg at h
    have := DeltaSpikeSupport' εpos ht.le suppSmoothingF h
    have dsnonneg : 0 ≤ DeltaSpike SmoothingF ε t := by apply DeltaSpikeNonNeg_of_NonNeg <;> assumption
    calc
      _ ≤ |DeltaSpike SmoothingF ε t| / |t| := by
        gcongr
        · split_ifs with h
          · apply le_refl
          · exact dsnonneg
      _ ≤ _ := by
        rw [_root_.abs_of_nonneg dsnonneg, mul_comm, div_eq_mul_one_div, _root_.abs_of_pos ht]
        gcongr
        apply (one_div_le ht (by bound)).mpr
        · convert this.1 using 1; field_simp
          rw [← rpow_add (by norm_num), add_neg_cancel, rpow_zero]
  · apply Integrable.const_mul
    apply (integrable_indicator_iff (by measurability)).mp
    apply (integrableOn_iff_integrable_of_support_subset (s := Icc (2 ^ (-ε)) (2 ^ ε)) _).mp
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.congr  (f := DeltaSpike SmoothingF ε)
      · apply Continuous.continuousOn
        apply DeltaSpikeContinuous<;> assumption
      · intro x hx
        have : x ∈ Ioi 0 := by
          apply mem_Ioi.mpr
          apply lt_of_lt_of_le (by bound) hx.1
        rw [indicator, if_pos this]
    · unfold indicator
      simp_rw [mem_Ioi]
      apply Function.support_subset_iff.mpr
      intro x
      simp
      intro hx
      apply DeltaSpikeSupport' εpos hx.le suppSmoothingF
  · have : ∀ᵐ (a : ℝ) ∂volume.restrict (Ioi 0), a ≠ y := by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_mem (by measurability), this] with x hx hx2
    simp at hx
    apply ContinuousAt.div_const
    apply ContinuousAt.mul (by fun_prop)
    have : (fun x_1 ↦ if 0 < x_1 / x ∧ x_1 / x ≤ 1 then 1 else 0) = (Ioc 0 x).indicator (fun _ ↦ (1 : ℝ)) := by
      ext t
      unfold indicator
      congr 1
      simp
      apply and_congr
      · exact div_pos_iff_of_pos_right hx
      · exact div_le_one₀ hx
    rw [this]
    apply ContinuousOn.continuousAt_indicator (by fun_prop)
    rw [frontier_Ioc hx]
    simp
    constructor <;> push_neg
    · exact ypos.ne.symm
    · exact hx2.symm


/-%%
\begin{proof}\leanok
\uses{MellinConvolutionSymmetric}
Use Lemma \ref{MellinconvolutionSymmetric} to write $\widetilde{1_{\epsilon}}(x)$ as an integral over an integral near $1$, in particular avoiding the singularity at $0$.  The integrand may be bounded by $2^{\epsilon}\nu_\epsilon(t)$ which is independent of $x$ and we can use dominated convergence to prove continuity.
\end{proof}
%%-/

lemma Smooth1MellinConvergent {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2)
    (hε : ε ∈ Ioo 0 1) (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x ↦ (Smooth1 Ψ ε x : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp; bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx

lemma Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2)
    (hε : ε ∈ Ioo 0 1) (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp; bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx
