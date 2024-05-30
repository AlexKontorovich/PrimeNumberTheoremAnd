import Mathlib.Analysis.MellinInversion
import PrimeNumberTheoremAnd.PerronFormula
import Mathlib.Algebra.GroupWithZero.Units.Basic

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
  rw [← this, setIntegral_congr (by simp)]
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
  rw [← integral_comp_rpow_Ioi (fun y ↦ f y / y) hp, setIntegral_congr (by simp)]
  intro y hy
  have ypos : 0 < y := mem_Ioi.mp hy
  field_simp [rpow_sub_one]
  ring

lemma MeasureTheory.integral_comp_inv_I0i_haar (f : ℝ → 𝕂) :
    ∫ (y : ℝ) in Ioi 0, f (1 / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_rpow_Ioi (fun y ↦ f y / y) (p := -1) (by simp)
  rw [← this, setIntegral_congr (by simp)]
  intro y hy
  have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
  field_simp [RCLike.real_smul_eq_coe_mul]
  ring_nf
  rw [rpow_neg_one, mul_assoc, rpow_neg <| le_of_lt <| mem_Ioi.mp hy]
  field_simp [pow_two]

lemma MeasureTheory.integral_comp_div_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a):
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
lemma Function.support_abs {α : Type*} (f : α → 𝕂):
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq, mem_setOf_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal'); simp [ofReal_zero]

lemma Function.support_id : Function.support (fun x : ℝ ↦ x) = Iio 0 ∪ Ioi 0 := by
  ext x; simp only [mem_support, ne_eq, Iio_union_Ioi, mem_compl_iff, mem_singleton_iff]

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
      rw [this, integral_singleton]; simp
    · rw [Icc_eq_empty_iff.mpr <| by exact fun x ↦ hab2 <| le_antisymm hab x, subset_empty_iff,
          Function.support_eq_empty_iff] at h; simp [h]

lemma SetIntegral.integral_eq_integral_inter_of_support_subset {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set ℝ} {f : ℝ → E} (h : f.support ⊆ t) (ht : MeasurableSet t):
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

lemma Filter.TendstoAtZero_of_support_in_Icc {a b : ℝ} (f: ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f (𝓝[>]0) (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' ha] with c hc; replace hc := (mem_Ioo.mp hc).2
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.TendstoAtTop_of_support_in_Icc {a b : ℝ} (f: ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f atTop (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioi_mem_atTop b] with c hc; rw [mem_Ioi] at hc
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.BigO_zero_atZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b):
    f =O[𝓝[>] 0] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (by linarith : (0 : ℝ) < a)] with c hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h, (mem_Ioo.mp hc).2]

lemma Filter.BigO_zero_atTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b):
    f =O[atTop] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioi_mem_atTop b] with c hc; replace hc := mem_Ioi.mp hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h]

-- steal coercion lemmas from EulerProducts.Auxiliary because of build issues, and add new ones
namespace Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal' 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma deriv_ofReal (x : ℝ) : deriv ofReal' x = 1 :=
  (hasDerivAt_ofReal x).deriv

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal' x :=
  (hasDerivAt_ofReal x).differentiableAt

lemma differentiable_ofReal : Differentiable ℝ ofReal' :=
  ofRealCLM.differentiable

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma Differentiable.comp_ofReal {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ (fun x : ℝ ↦ e x) :=
  fun _ ↦ h.differentiableAt.comp_ofReal

lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt

lemma Differentiable.ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) :=
  fun _ ↦ hf.differentiableAt.ofReal_comp

open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, smulRight_apply, one_apply, one_smul] at H
  refine ⟨u, rfl, ?_⟩
  convert (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, smulRight_apply, one_apply, one_smul, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt <| hf',
      Complex.ofReal_zero]

lemma deriv.ofReal_comp' {f : ℝ → ℝ} :
    deriv (fun x : ℝ ↦ (f x : ℂ)) = (fun x ↦ ((deriv f) x : ℂ)) :=
  funext fun _ ↦ deriv.ofReal_comp

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

lemma deriv.comp_ofReal' {e : ℂ → ℂ} (hf : Differentiable ℂ e) :
    deriv (fun x : ℝ ↦ e x) = fun (x : ℝ) ↦ deriv e x :=
  funext fun _ ↦ deriv.comp_ofReal (hf.differentiableAt)

/-%%
\begin{lemma}[PartialIntegration]\label{PartialIntegration}\lean{PartialIntegration}\leanok
Let $f, g$ be once differentiable functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$ so that $fg'$
and $f'g$ are both integrable, and $f*g (x)\to 0$ as $x\to 0^+,\infty$.
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
    (lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0))
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


/-%%
\begin{definition}[MellinTransform]\label{MellinTransform}\lean{MellinTransform}\leanok
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of
$f$ to be
the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$
\end{definition}
[Note: already exists in Mathlib, with some good API.]
%%-/
noncomputable def MellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Ioi 0, f x * x ^ (s - 1)

local notation (name := mellintransform) "𝓜" => MellinTransform
/-%%
\begin{definition}[MellinInverseTransform]\label{MellinInverseTransform}
\lean{MellinInverseTransform}\leanok
Let $F$ be a function from $\mathbb{C}$ to $\mathbb{C}$. We define the Mellin inverse transform of
$F$ to be the function $\mathcal{M}^{-1}(F)$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$\mathcal{M}^{-1}(F)(x) = \frac{1}{2\pi i}\int_{(\sigma)}F(s)x^{-s}ds,$$
where $\sigma$ is sufficiently large (say $\sigma>2$).
\end{definition}
%%-/
noncomputable def MellinInverseTransform (F : ℂ → ℂ) (σ : ℝ) (x : ℝ) : ℂ :=
  VerticalIntegral' (fun s ↦ x ^ (-s) * F s) σ

/-%%
\begin{lemma}[PerronInverseMellin_lt]\label{PerronInverseMellin_lt}\lean{PerronInverseMellin_lt}
\leanok
Let $0 < t < x$ and $\sigma>0$. Then the inverse Mellin transform of the Perron function
$$F: s\mapsto t^s/s(s+1)$$ is equal to
$$\frac{1}{2\pi i}\int_{(\sigma)}\frac{t^s}{s(s+1)}x^{-s}ds
= 0.$$
\end{lemma}
%%-/
lemma PerronInverseMellin_lt {t x : ℝ} (tpos : 0 < t) (t_lt_x : t < x) {σ : ℝ} (σpos : 0 < σ) :
    MellinInverseTransform (Perron.f t) σ x = 0 := by
  dsimp [MellinInverseTransform, VerticalIntegral']
  have xpos : 0 < x := lt_trans tpos t_lt_x
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, neg_eq_zero, mul_eq_zero, I_ne_zero,
    inv_eq_zero, ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero, or_self, false_or]
  convert Perron.formulaLtOne (div_pos tpos xpos) ((div_lt_one xpos).mpr t_lt_x) σpos using 2
  ext1 s
  convert Perron.f_mul_eq_f tpos xpos s using 1
  ring
/-%%
\begin{proof}\leanok
\uses{Perron.formulaLtOne}
This is a straightforward calculation.
\end{proof}
%%-/

/-%%
\begin{lemma}[PerronInverseMellin_gt]\label{PerronInverseMellin_gt}\lean{PerronInverseMellin_gt}
\leanok
Let $0 < x < t$ and $\sigma>0$. Then the inverse Mellin transform of the Perron function is equal
to
$$\frac{1}{2\pi i}\int_{(\sigma)}\frac{t^s}{s(s+1)}x^{-s}ds = 1 - x / t.$$
\end{lemma}
%%-/
lemma PerronInverseMellin_gt {t x : ℝ} (xpos : 0 < x) (x_lt_t : x < t) {σ : ℝ} (σpos : 0 < σ) :
    MellinInverseTransform (Perron.f t) σ x = 1 - x / t := by
  dsimp [MellinInverseTransform]
  have tpos : 0 < t := by linarith
  have txinv_gtOne : 1 < t / x := (one_lt_div xpos).mpr x_lt_t
  rw [← smul_eq_mul]
  convert Perron.formulaGtOne txinv_gtOne σpos using 2
  · congr
    ext1 s
    convert Perron.f_mul_eq_f tpos xpos s using 1
    ring
  · field_simp
/-%%
\begin{proof}
\uses{Perron.formulaGtOne}\leanok
This is a straightforward calculation.
\end{proof}
%%-/

/-% ** Wrong delimiters on purpose **
Unnecessary lemma:
%\begin{lemma}[MellinInversion_aux1]\label{MellinInversion_aux1}\lean{MellinInversion_aux1}\leanok
Let $f$ be differentiable on $(0,\infty)$, and assume that $f(x)x^s\to 0$ as $x\to 0$, and that
$f(x)x^s\to 0$.
Then
$$
\int_0^\infty f(x)x^s\frac{dx}{x} = \frac{1}{s}\int_0^\infty f'(x)x^{s} dx.
$$
%\end{lemma}
%-/
lemma MellinInversion_aux1 {f : ℝ → ℂ} {s : ℂ} (s_ne_zero : s ≠ 0)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (hfs : Tendsto (fun x ↦ f x * x ^ s) (𝓝[>]0) (𝓝 0))
    (hfinf : Tendsto (fun x ↦ f x * x ^ s) atTop (𝓝 0)) :
    ∫ x in Ioi 0, f x * x ^ s / x = - ∫ x in Ioi 0, (deriv f x) * x ^ s / s := by
  sorry

/-% ** Wrong delimiters on purpose **
\begin{proof}
\uses{PartialIntegration}
Partial integration.
\end{proof}
%-/

/-% ** Wrong delimiters on purpose **
\begin{lemma}[MellinInversion_aux2]\label{MellinInversion_aux2}\lean{MellinInversion_aux2}\leanok
Let $f$ be twice differentiable on $(0,\infty)$, and assume that $f'(x)x^s\to 0$ as $x\to 0$, and
that $f'(x)x^s\to 0$.
Then
$$
\int_0^\infty f'(x)x^{s} dx = -\int_0^\infty f''(x)x^{s+1}\frac{1}{(s+1)}dx.
$$
\end{lemma}
%-/
lemma MellinInversion_aux2 {f : ℝ → ℂ} (s : ℂ) (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (fDiff2 : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hfs : Tendsto (fun x ↦ deriv f x * x ^ s) (𝓝[>]0) (𝓝 0))
    (hfinf : Tendsto (fun x ↦ deriv f x * x ^ s) atTop (𝓝 0)) :
    ∫ x in Ioi 0, (deriv f x) * x ^ s =
      -∫ x in Ioi 0, (deriv (deriv f) x) * x ^ (s + 1) / (s + 1) := by
  sorry
/-%
\begin{proof}
\uses{PartialIntegration, MellinInversion_aux1}
Partial integration. (Apply Lemma \ref{MellinInversion_aux1} to the function $f'$ and $s+1$.)
\end{proof}
%-/

/-% ** Wrong delimiters on purpose **
\begin{lemma}[MellinInversion_aux3]%\label{MellinInversion_aux3}\lean{MellinInversion_aux3}\leanok
Given $f$ and $\sigma$, assume that $f(x)x^\sigma$ is absolutely integrable on $(0,\infty)$.
Then the map  $(x,s) \mapsto f(x)x^s/(s(s+1))$ is absolutely integrable on
$(0,\infty)\times\{\Re s = \sigma\}$ for any $\sigma>0$.
\end{lemma}
%-/
lemma MellinInversion_aux3 {f : ℝ → ℂ} (σ : ℝ) (σ_ne_zero : σ ≠ 0) (σ_ne_negOne : σ ≠ -1)
    (fInt : IntegrableOn (fun x ↦ f x * (x : ℂ) ^ (σ : ℂ)) (Ioi 0)) :
    IntegrableOn (fun (⟨x, t⟩ : ℝ × ℝ) ↦ f x * x ^ (σ + t * I) / ((σ + t * I) * ((σ + t * I) + 1)))
      ((Ioi 0).prod (univ : Set ℝ)) := by
  sorry
/-%
\begin{proof}
Put absolute values and estimate.
\end{proof}
%-/

/-% ** Wrong delimiters on purpose **
\begin{lemma}[MellinInversion_aux4]%\label{MellinInversion_aux4}\lean{MellinInversion_aux4}\leanok
Given $f$ and $\sigma$, assume that $f(x)x^\sigma$ is absolutely integrable on $(0,\infty)$.
Then we can interchange orders of integration
$$
\int_{(\sigma)}\int_0^\infty f(x)x^{s+1}\frac{1}{s(s+1)}dx ds =
\int_0^\infty
\int_{(\sigma)}f(x)x^{s+1}\frac{1}{s(s+1)}ds dx.
$$
\end{lemma}
%-/
lemma MellinInversion_aux4 {f : ℝ → ℂ} (σ : ℝ) (σ_ne_zero : σ ≠ 0) (σ_ne_negOne : σ ≠ -1)
    (fInt : IntegrableOn (fun x ↦ f x * (x : ℂ) ^ (σ : ℂ)) (Ioi 0)) :
    VerticalIntegral (fun s ↦ ∫ x in Ioi 0, f x * (x : ℂ) ^ (s + 1) / (s * (s + 1))) σ =
      ∫ x in Ioi 0, VerticalIntegral (fun s ↦ f x * (x : ℂ) ^ (s + 1) / (s * (s + 1))) σ := by
  sorry -- `MeasureTheory.integral_prod` and `MeasureTheory.integral_swap` should be useful here
/-%
\begin{proof}
\uses{MellinInversion_aux3}
Fubini-Tonelli.
\end{proof}
%-/

lemma MellinTransform_eq : 𝓜 = mellin := by unfold mellin MellinTransform; simp_rw [smul_eq_mul, mul_comm]

lemma MellinInverseTransform_eq (σ : ℝ) (f : ℂ → ℂ) :
    MellinInverseTransform f σ = mellinInv σ f := by
  unfold mellinInv MellinInverseTransform VerticalIntegral' VerticalIntegral
  beta_reduce; ext x
  rw [← smul_assoc, smul_eq_mul (a' := I), div_mul]; simp

/-%%
\begin{theorem}[MellinInversion]\label{MellinInversion}\lean{MellinInversion}\leanok
Let $f$ be a twice differentiable function from $\mathbb{R}_{>0}$ to $\mathbb{C}$, and
let $\sigma$
be sufficiently large. Then
$$f(x) = \frac{1}{2\pi i}\int_{(\sigma)}\mathcal{M}(f)(s)x^{-s}ds.$$
\end{theorem}

%[Note: How ``nice''? Schwartz (on $(0,\infty)$) is certainly enough. As we formalize
%this, we can add whatever
% conditions are necessary for the proof to go through.]
%%-/
theorem MellinInversion (σ : ℝ) {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) (hfx : ContinuousAt f x) :
    MellinInverseTransform (𝓜 f) σ x = f x := by
  rw [MellinTransform_eq, MellinInverseTransform_eq, mellin_inversion σ f hx hf hFf hfx]
/-%%
\begin{proof}\leanok
\uses{PartialIntegration, formulaLtOne, formulaGtOne, MellinTransform,
MellinInverseTransform, PerronInverseMellin_gt, PerronInverseMellin_lt}
%MellinInversion_aux1, MellinInversion_aux2, MellinInversion_aux3,
%MellinInversion_aux4, }
The proof is from [Goldfeld-Kontorovich 2012].
Integrate by parts twice (assuming $f$ is twice differentiable, and all occurring
integrals converge absolutely, and
boundary terms vanish).
$$
\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx = - \int_0^\infty f'(x)x^s\frac{1}{s}dx
= \int_0^\infty f''(x)x^{s+1}\frac{1}{s(s+1)}dx.
$$
We now have at least quadratic decay in $s$ of the Mellin transform. Inserting this
formula into the inversion formula and Fubini-Tonelli (we now have absolute
convergence!) gives:
$$
RHS = \frac{1}{2\pi i}\left(\int_{(\sigma)}\int_0^\infty
  f''(t)t^{s+1}\frac{1}{s(s+1)}dt\right) x^{-s}ds
$$
$$
= \int_0^\infty f''(t) t \left( \frac{1}{2\pi i}
\int_{(\sigma)}(t/x)^s\frac{1}{s(s+1)}ds\right) dt.
$$
Apply the Perron formula to the inside:
$$
= \int_x^\infty f''(t) t \left(1-\frac{x}{t}\right)dt
= -\int_x^\infty f'(t) dt
= f(x),
$$
where we integrated by parts (undoing the first partial integration), and finally
applied the fundamental theorem of calculus (undoing the second).
\end{proof}
%%-/


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
lemma MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos: 0 < x) :
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
  dsimp [MellinTransform, MellinConvolution]
  set f₁ : ℝ × ℝ → ℂ := fun ⟨x, y⟩ ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
  calc
    _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioi 0, f₁ (x, y) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f₁ (x, y) := setIntegral_integral_swap _ hf
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * g (x / y) / ↑y * ↑x ^ (s - 1) := rfl
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * g (x * y / y) / ↑y * ↑(x * y) ^ (s - 1) * y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * ↑y ^ (s - 1) * (g x * ↑x ^ (s - 1)) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, f y * ↑y ^ (s - 1) * ∫ (x : ℝ) in Ioi 0, g x * ↑x ^ (s - 1) := ?_
    _ = _ := integral_mul_right _ _
  <;> try (rw [setIntegral_congr (by simp)]; intro y hy; simp only [ofReal_mul])
  · simp only [integral_mul_right]; rfl
  · simp only [integral_mul_right]
    have := integral_comp_mul_right_Ioi (fun x ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)) 0 hy
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := slitPlane_ne_zero (Or.inl hy)
    field_simp at this ⊢
    rw [this]
  · rw [setIntegral_congr (by simp)]
    intro x hx
    have y_ne_zeroℝ : y ≠ 0 := ne_of_gt (mem_Ioi.mp hy)
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := by exact_mod_cast y_ne_zeroℝ
    field_simp [mul_cpow_ofReal_nonneg (LT.lt.le hx) (LT.lt.le hy)]
    ring
  · apply integral_mul_left

/-%%
\begin{proof}\leanok
\uses{MellinTransform,MellinConvolution}
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

/-%%
Let $\psi$ be a bumpfunction.
\begin{theorem}[SmoothExistence]\label{SmoothExistence}\lean{SmoothExistence}\leanok
There exists a smooth (once differentiable would be enough), nonnegative ``bumpfunction'' $\psi$,
 supported in $[1/2,2]$ with total mass one:
$$
\int_0^\infty \psi(x)\frac{dx}{x} = 1.
$$
\end{theorem}
%%-/

attribute [- simp] one_div in

lemma SmoothExistence : ∃ (Ψ : ℝ → ℝ), (ContDiff ℝ ⊤ Ψ) ∧ (∀ x, 0 ≤ Ψ x) ∧
    Ψ.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, Ψ x / x = 1 := by
  suffices h : ∃ (Ψ : ℝ → ℝ), (ContDiff ℝ ⊤ Ψ) ∧ (∀ x, 0 ≤ Ψ x) ∧
      Ψ.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, Ψ x / x by
    rcases h with ⟨Ψ, hΨ, hΨnonneg, hΨsupp, hΨpos⟩
    let c := (∫ x in Ici 0, Ψ x / x)
    use fun y ↦ Ψ y / c
    refine ⟨hΨ.div_const c, fun y ↦ div_nonneg (hΨnonneg y) (le_of_lt hΨpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hΨpos).symm, inter_univ]
      convert hΨsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hΨpos]

  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3/2) (d := 2) (by linarith)
    (by linarith)
  rcases this with ⟨Ψ, hΨContDiff, _, hΨ0, hΨ1, hΨSupport⟩
  use Ψ, hΨContDiff
  unfold indicator at hΨ0 hΨ1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hΨ0 hΨ1
  simp only [hΨSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hΨ0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply', hΨSupport, Function.support_id]
      have : (Ioo (1 / 2 : ℝ) 2 ∩ (Iio 0 ∪ Ioi 0) ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ici, mem_Iio, mem_Ioi,
          mem_union, not_lt, and_true, not_le]
        constructor
        · exact fun h ↦ h.left.left
        · intro h
          simp only [h, and_self, lt_or_lt_iff_ne, ne_eq, true_and]
          constructor <;> linarith [h.left]
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support Ψ
      . apply div_nonneg <| le_trans (by simp [apply_ite]) (hΨ0 y)
        rw [hΨSupport, mem_Ioo] at h; linarith [h.left]
      . simp only [Function.mem_support, ne_eq, not_not] at h; simp [h]
    · have : (fun x ↦ Ψ x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hΨSupport]
        apply subset_trans (by apply inter_subset_left) Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hΨContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]; intros;linarith
/-%%
\begin{proof}\leanok
\uses{smooth-ury}
Same idea as Urysohn-type argument.
\end{proof}
%%-/

lemma mem_within_strip (σ₁ σ₂ : ℝ) :
  {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂} ∈ 𝓟 {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂} := by simp

lemma MellinOfPsi_aux {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    {s : ℂ} (hs : s ≠ 0) :
    ∫ (x : ℝ) in Ioi 0, (Ψ x) * (x : ℂ) ^ (s - 1) =
    - (1 / s) * ∫ (x : ℝ) in Ioi 0, (deriv Ψ x) * (x : ℂ) ^ s := by
  let g {s : ℂ} := fun (x : ℝ)  ↦ x ^ s / s
  have gderiv {s : ℂ} (hs : s ≠ 0) {x: ℝ} (hx : x ∈ Ioi 0) :
      deriv g x = x ^ (s - 1) := by
    have := HasDerivAt.cpow_const (c := s) (hasDerivAt_id (x : ℂ)) (Or.inl hx)
    simp_rw [mul_one, id_eq] at this
    rw [deriv_div_const, deriv.comp_ofReal (e := fun x ↦ x ^ s)]
    · rw [this.deriv, mul_div_right_comm, div_self hs, one_mul]
    · apply hasDerivAt_deriv_iff.mp
      simp only [this.deriv, this]
  calc
    _ =  ∫ (x : ℝ) in Ioi 0, ↑(Ψ x) * deriv (@g s) x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv (fun x ↦ ↑(Ψ x)) x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv Ψ x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv Ψ x * x ^ s / s := by simp only [mul_div, g]
    _ = _ := ?_
  · rw [setIntegral_congr (by simp)]
    intro _ hx
    simp only [gderiv hs hx]
  · apply PartialIntegration_of_support_in_Icc (Ψ ·) g
      (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
    · simpa only [Function.support_subset_iff, ne_eq, ofReal_eq_zero]
    · exact (Differentiable.ofReal_comp_iff.mpr (diffΨ.differentiable (by norm_num))).differentiableOn
    · refine DifferentiableOn.div_const ?_ s
      intro a ha
      refine DifferentiableAt.comp_ofReal (e := fun x ↦ x ^ s) ?_ |>.differentiableWithinAt
      apply differentiableAt_id'.cpow (differentiableAt_const s) <| by exact Or.inl ha
    · simp only [deriv.ofReal_comp']
      exact continuous_ofReal.comp (diffΨ.continuous_deriv (by norm_num)) |>.continuousOn
    · apply ContinuousOn.congr (f := fun (x : ℝ) ↦ (x : ℂ) ^ (s - 1)) ?_ fun x hx ↦ gderiv hs hx
      exact Continuous.continuousOn (by continuity) |>.cpow continuousOn_const (by simp)
  · congr; funext; congr
    apply (hasDerivAt_deriv_iff.mpr ?_).ofReal_comp.deriv
    exact diffΨ.contDiffAt.differentiableAt (by norm_num)
  · simp only [neg_mul, neg_inj]
    conv => lhs; rhs; intro; rw [← mul_one_div, mul_comm]
    rw [integral_mul_left]

/-%%
The $\psi$ function has Mellin transform $\mathcal{M}(\psi)(s)$ which is entire and decays (at
least) like $1/|s|$.
\begin{theorem}[MellinOfPsi]\label{MellinOfPsi}\lean{MellinOfPsi}\leanok
The Mellin transform of $\psi$ is
$$\mathcal{M}(\psi)(s) =  O\left(\frac{1}{|s|}\right),$$
as $|s|\to\infty$ with $\sigma_1 \le \Re(s) \le \sigma_2$.
\end{theorem}

[Of course it decays faster than any power of $|s|$, but it turns out that we will just need one
power.]
%%-/
lemma MellinOfPsi {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    {σ₁ σ₂ : ℝ} (σ₁pos : 0 < σ₁) :
    (fun s ↦ ‖𝓜 (Ψ ·) s‖)
    =O[Filter.principal {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂}]
      fun s ↦ 1 / ‖s‖ := by
  let f := fun (x : ℝ) ↦ ‖deriv Ψ x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (Continuous.comp (by continuity) <| diffΨ.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  rw [Asymptotics.isBigO_iff]
  use f a * 2 ^ σ₂ * (3 / 2)
  filter_upwards [mem_within_strip σ₁ σ₂] with s hs
  have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs.1]
  simp only [MellinTransform, f, MellinOfPsi_aux diffΨ suppΨ s_ne_zero, norm_norm, norm_mul]
  conv => rhs; rw [mul_comm]
  gcongr; simp
  calc
    _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv Ψ x * (x : ℂ) ^ s)‖ := ?_
    _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv Ψ x * (x : ℂ) ^ s)‖ := ?_
    _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv Ψ x * (x : ℂ) ^ s)‖‖ := le_abs_self _
    _ ≤ _ := ?_
  · simp_rw [norm_integral_le_integral_norm]
  · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
    · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
      apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppΨ
    · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
  · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * 2 ^ σ₂)
      (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
    · simp only [Real.norm_eq_abs, Complex.norm_eq_abs, abs_ofReal, map_mul] at this ⊢
      rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
          intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
    · intro x hx;
      have f_bound := isMaxOn_iff.mp max x hx
      have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
        rw [Complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
        have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
        have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
        exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs.2
      convert mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]
/-%%
\begin{proof}\leanok
\uses{MellinTransform, SmoothExistence}
Integrate by parts:
$$
\left|\int_0^\infty \psi(x)x^s\frac{dx}{x}\right| =
\left|-\int_0^\infty \psi'(x)\frac{x^{s}}{s}dx\right|
$$
$$
\le \frac{1}{|s|} \int_{1/2}^2|\psi'(x)|x^{\Re(s)}dx.
$$
Since $\Re(s)$ is bounded, the right-hand side is bounded by a
constant times $1/|s|$.
\end{proof}
%%-/

/-%%
We can make a delta spike out of this bumpfunction, as follows.
\begin{definition}[DeltaSpike]\label{DeltaSpike}\lean{DeltaSpike}\leanok
\uses{SmoothExistence}
Let $\psi$ be a bumpfunction supported in $[1/2,2]$. Then for any $\epsilon>0$, we define the
delta spike $\psi_\epsilon$ to be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$\psi_\epsilon(x) = \frac{1}{\epsilon}\psi\left(x^{\frac{1}{\epsilon}}\right).$$
\end{definition}
%%-/

noncomputable def DeltaSpike (Ψ : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ Ψ (x ^ (1 / ε)) / ε

/-%%
This spike still has mass one:
\begin{lemma}[DeltaSpikeMass]\label{DeltaSpikeMass}\lean{DeltaSpikeMass}\leanok
For any $\epsilon>0$, we have
$$\int_0^\infty \psi_\epsilon(x)\frac{dx}{x} = 1.$$
\end{lemma}
%%-/

lemma DeltaSpikeMass {Ψ : ℝ → ℝ} (mass_one: ∫ x in Ioi 0, Ψ x / x = 1) {ε : ℝ}
    (εpos : 0 < ε) : ∫ x in Ioi 0, ((DeltaSpike Ψ ε) x) / x = 1 :=
  calc
    _ = ∫ (x : ℝ) in Ioi 0, (|1/ε| * x ^ (1 / ε - 1)) •
      ((fun z ↦ (Ψ z) / z) (x ^ (1 / ε))) := by
      apply setIntegral_congr_ae measurableSet_Ioi
      filter_upwards with x hx
      simp only [mem_Ioi, smul_eq_mul, abs_of_pos (one_div_pos.mpr εpos)]
      symm; calc
        _ = (Ψ (x ^ (1 / ε)) / x ^ (1 / ε)) * x ^ (1 / ε - 1) * (1 / ε) := by ring
        _ = _ := by rw [rpow_sub hx, rpow_one]
        _ = (Ψ (x ^ (1 / ε)) / x ^ (1 / ε) * x ^ (1 / ε) / x) * (1/ ε) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt (rpow_pos_of_pos hx (1/ε)))]
        _ = (Ψ (x ^ (1 / ε)) / ε / x) := by ring
    _ = 1 := by
      rw [integral_comp_rpow_Ioi (fun z ↦ (Ψ z) / z), ← mass_one]
      simp only [ne_eq, div_eq_zero_iff, one_ne_zero, εpos.ne', or_self, not_false_eq_true]

/-%%
\begin{proof}\leanok
\uses{DeltaSpike}
Substitute $y=x^{1/\epsilon}$, and use the fact that $\psi$ has mass one, and that $dx/x$ is Haar
measure.
\end{proof}
%%-/

lemma DeltaSpikeSupport_aux {Ψ : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2):
    (fun x ↦ if x < 0 then 0 else DeltaSpike Ψ ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  unfold DeltaSpike
  simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
    not_forall, exists_prop, mem_Icc, and_imp]
  intro x hx h; push_neg at h
  have := suppΨ <| Function.mem_support.mpr h.1
  simp only [one_div, mem_Icc] at this
  have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
  rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
  refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
  linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]

lemma DeltaSpikeSupport' {Ψ : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) :
    DeltaSpike Ψ ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
  intro h
  have : (fun x ↦ if x < 0 then 0 else DeltaSpike Ψ ε x) x = DeltaSpike Ψ ε x := by simp [xnonneg]
  rw [← this] at h
  exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppΨ) _ h

lemma DeltaSpikeSupport {Ψ : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) :
    x ∉ Icc (2 ^ (-ε)) (2 ^ ε) → DeltaSpike Ψ ε x = 0 := by
  contrapose!; exact DeltaSpikeSupport' εpos xnonneg suppΨ

lemma DeltaSpikeContinuous {Ψ : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (diffΨ : ContDiff ℝ 1 Ψ) :
    Continuous (fun x ↦ DeltaSpike Ψ ε x) := by
  apply diffΨ.continuous.comp (g := Ψ) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le

lemma DeltaSpikeOfRealContinuous {Ψ : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε) (diffΨ : ContDiff ℝ 1 Ψ) :
    Continuous (fun x ↦ (DeltaSpike Ψ ε x : ℂ)) :=
  continuous_ofReal.comp <| DeltaSpikeContinuous εpos diffΨ

/-%%
The Mellin transform of the delta spike is easy to compute.
\begin{theorem}[MellinOfDeltaSpike]\label{MellinOfDeltaSpike}\lean{MellinOfDeltaSpike}\leanok
For any $\epsilon>0$, the Mellin transform of $\psi_\epsilon$ is
$$\mathcal{M}(\psi_\epsilon)(s) = \mathcal{M}(\psi)\left(\epsilon s\right).$$
\end{theorem}
%%-/
theorem MellinOfDeltaSpike (Ψ : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    𝓜 ((DeltaSpike Ψ ε) ·) s = 𝓜 (Ψ ·) (ε * s) := by
  unfold MellinTransform DeltaSpike
  rw [← integral_comp_rpow_Ioi (fun z ↦ ((Ψ z) : ℂ) * (z : ℂ) ^ ((ε : ℂ) * s - 1))
    (one_div_ne_zero (ne_of_gt εpos))]
  apply setIntegral_congr_ae measurableSet_Ioi
  filter_upwards with x hx

  -- Simple algebra, would be nice if some tactic could handle this
  have log_x_real: (Complex.log (x : ℂ)).im = 0 := by
    rw [← ofReal_log, ofReal_im]
    exact LT.lt.le hx
  rw [div_eq_mul_inv, ofReal_mul, abs_of_pos (one_div_pos.mpr εpos)]
  simp only [real_smul, ofReal_mul, ofReal_div, ofReal_one, Complex.ofReal_rpow hx]
  rw [← Complex.cpow_mul _ ?_ ?_, mul_sub]
  · simp only [← mul_assoc, ofReal_sub, ofReal_div, ofReal_one, mul_one, ofReal_inv]
    symm
    · rw [one_div_mul_cancel (by exact slitPlane_ne_zero (Or.inl εpos)), mul_comm (1 / (ε:ℂ)),
          mul_comm, ← mul_assoc, ← mul_assoc]
      rw [← Complex.cpow_add _ _ (by exact slitPlane_ne_zero (Or.inl hx))]; ring_nf
  · simp [im_mul_ofReal, log_x_real, zero_mul, pi_pos]
  · simp [im_mul_ofReal, log_x_real, zero_mul, pi_nonneg]
/-%%
\begin{proof}\leanok
\uses{DeltaSpike, MellinTransform}
Substitute $y=x^{1/\epsilon}$, use Haar measure; direct calculation.
\end{proof}
%%-/

/-%%
In particular, for $s=1$, we have that the Mellin transform of $\psi_\epsilon$ is $1+O(\epsilon)$.
\begin{corollary}[MellinOfDeltaSpikeAt1]\label{MellinOfDeltaSpikeAt1}\lean{MellinOfDeltaSpikeAt1}
\leanok
For any $\epsilon>0$, we have
$$\mathcal{M}(\psi_\epsilon)(1) =
\mathcal{M}(\psi)(\epsilon).$$
\end{corollary}
%%-/

lemma MellinOfDeltaSpikeAt1 (Ψ : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) :
    𝓜 ((DeltaSpike Ψ ε) ·) 1 = 𝓜 (Ψ ·) ε := by
  convert MellinOfDeltaSpike Ψ εpos 1; simp [mul_one]
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
$$\mathcal{M}(\psi_\epsilon)(1) = 1+O(\epsilon).$$
\end{lemma}
%%-/
lemma MellinOfDeltaSpikeAt1_asymp {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi 0, Ψ x / x = 1) :
    (fun (ε : ℝ) ↦ (𝓜 (Ψ ·) ε) - 1) =O[𝓝[>]0] id := by
  have diff : DifferentiableWithinAt ℝ (fun (ε : ℝ) ↦ 𝓜 (Ψ ·) ε - 1) (Ioi 0) 0 := by
    apply DifferentiableAt.differentiableWithinAt
    simp only [differentiableAt_sub_const_iff, MellinTransform_eq]
    refine DifferentiableAt.comp_ofReal ?_
    refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1) ?_ ?_ (by simp) ?_ (by simp)
    · apply (Continuous.continuousOn ?_).locallyIntegrableOn (by simp)
      have := diffΨ.continuous; continuity
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atTop_of_support_in_Icc (a := 1 / 2) (b := 2)
      rwa [Ψ.support_ofReal]
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atZero_of_support_in_Icc (a := 1 / 2) (b := 2) (ha := (by norm_num))
      rwa [Ψ.support_ofReal]
  have := ofReal_zero ▸ diff.isBigO_sub
  simp only [sub_sub_sub_cancel_right, sub_zero] at this
  convert this
  simp only [MellinTransform, zero_sub, sub_right_inj, cpow_neg_one, ← div_eq_mul_inv, ← ofReal_div]
  rw [← ofReal_one, ← mass_one]; convert integral_ofReal.symm
/-%%
\begin{proof}\leanok
\uses{MellinTransform,MellinOfDeltaSpikeAt1,SmoothExistence}
By Lemma \ref{MellinOfDeltaSpikeAt1},
$$
  \mathcal M(\psi_\epsilon)(1)=\mathcal M(\psi)(\epsilon)
$$
which by Definition \ref{MellinTransform} is
$$
  \mathcal M(\psi)(\epsilon)=\int_0^\infty\psi(x)x^{\epsilon-1}dx
  .
$$
Since $\psi(x) x^{\epsilon-1}$ is integrable (because $\psi$ is continuous and compactly supported),
$$
  \mathcal M(\psi)(\epsilon)-\int_0^\infty\psi(x)\frac{dx}x=\int_0^\infty\psi(x)(x^{\epsilon-1}-x^{-1})dx
  .
$$
By Taylor's theorem,
$$
  x^{\epsilon-1}-x^{-1}=O(\epsilon)
$$
so, since $\psi$ is absolutely integrable,
$$
  \mathcal M(\psi)(\epsilon)-\int_0^\infty\psi(x)\frac{dx}x=O(\epsilon)
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
  convert (hasMellin_one_Ioc h).right using 1
  apply setIntegral_congr_ae measurableSet_Ioi
  filter_upwards with _ _; rw [smul_eq_mul, mul_comm]; congr

/-%%
\begin{proof}\leanok
\uses{MellinTransform}
This is a straightforward calculation.
\end{proof}
%%-/

/-%%
What will be essential for us is properties of the smooth version of $1_{(0,1]}$, obtained as the
 Mellin convolution of $1_{(0,1]}$ with $\psi_\epsilon$.
\begin{definition}[Smooth1]\label{Smooth1}\lean{Smooth1}
\uses{MellinOf1, MellinConvolution}\leanok
Let $\epsilon>0$. Then we define the smooth function $\widetilde{1_{\epsilon}}$ from
$\mathbb{R}_{>0}$ to $\mathbb{C}$ by
$$\widetilde{1_{\epsilon}} = 1_{(0,1]}\ast\psi_\epsilon.$$
\end{definition}
%%-/
noncomputable def Smooth1 (Ψ : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike Ψ ε)

/-%%
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%%-/

lemma Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
  apply (div_lt_iff' εpos).mpr
  have : 1 - 1 / (2 : ℝ) ^ ε = ((2 : ℝ) ^ ε - 1) / (2 : ℝ) ^ ε := by
    rw [sub_div, div_self (by positivity)]
  rw [← Real.log_rpow (by norm_num), rpow_neg (by norm_num), inv_eq_one_div (2 ^ ε), this]
  set c := (2 : ℝ) ^ ε
  have hc : 1 < c := by
    rw [← rpow_zero (2 : ℝ)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
  apply (div_lt_iff' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
  let f := (fun x ↦ x * Real.log x - x)
  rw [(by simp [f] : -1 = f 1), (by simp : c * Real.log c - c = f c)]
  have mono: StrictMonoOn f <| Ici 1 := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
      intro x hx; simp only [mem_Ici] at hx; simp only [id_eq, ne_eq]; linarith
    · intro x hx; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
      funext; dsimp only [f]
      rw [deriv_sub, deriv_mul, deriv_log, deriv_id'', one_mul, mul_inv_cancel]; simp
      · exact log_pos hx
      · linarith
      · simp only [differentiableAt_id']
      · simp only [differentiableAt_log_iff, ne_eq]; linarith
      · exact differentiableAt_id'.mul <| differentiableAt_id'.log (by linarith)
      · simp only [differentiableAt_id']
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

lemma Smooth1Properties_below_aux {x ε : ℝ} (hx : x ≤ 1 - Real.log 2 * ε) (εpos: 0 < ε) :
    x < 2 ^ (-ε) := by
  calc
    x ≤ 1 - Real.log 2 * ε := hx
    _ < 2 ^ (-ε) := ?_
  rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
  exact (div_lt_iff εpos).mp <| Smooth1Properties_estimate εpos

lemma Smooth1Properties_below {Ψ : ℝ → ℝ} (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2)
    (ε : ℝ) (εpos: 0 < ε) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ ∀ (x : ℝ), 0 < x → x ≤ 1 - c * ε → Smooth1 Ψ ε x = 1 := by
  set c := Real.log 2; use c
  constructor; exact log_pos (by norm_num)
  intro x xpos hx
  have hx2 := Smooth1Properties_below_aux hx εpos
  rewrite [← DeltaSpikeMass mass_one εpos]
  unfold Smooth1 MellinConvolution
  calc
    _ = ∫ (y : ℝ) in Ioi 0, indicator (Ioc 0 1) (fun y ↦ DeltaSpike Ψ ε (x / y) / ↑y) y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, DeltaSpike Ψ ε (x / y) / y := ?_
    _ = _ := integral_comp_div_I0i_haar (fun y ↦ DeltaSpike Ψ ε y) xpos
  · rw [setIntegral_congr (by simp)]
    intro y hy
    by_cases h : y ≤ 1 <;> simp [indicator, mem_Ioi.mp hy, h]
  · rw [setIntegral_congr (by simp)]
    intro y hy
    simp only [indicator_apply_eq_self, mem_Ioc, not_and, not_le, div_eq_zero_iff]
    intro hy2; replace hy2 := hy2 <| mem_Ioi.mp hy
    by_cases h : y = 0; right; exact h; left
    apply DeltaSpikeSupport εpos ?_ suppΨ
    · simp only [mem_Icc, not_and, not_le]; intro
      linarith [(by apply (div_lt_iff (by linarith)).mpr; nlinarith : x / y < 2 ^ (-ε))]
    · rw [le_div_iff (by linarith), zero_mul]; exact xpos.le
/-%%
\begin{proof}\leanok
\uses{Smooth1, MellinConvolution,DeltaSpikeMass, Smooth1Properties_estimate}
Opening the definition, we have that the Mellin convolution of $1_{(0,1]}$ with $\psi_\epsilon$ is
$$
\int_0^\infty 1_{(0,1]}(y)\psi_\epsilon(x/y)\frac{dy}{y}
=
\int_0^1 \psi_\epsilon(x/y)\frac{dy}{y}.
$$
The support of $\psi_\epsilon$ is contained in $[1/2^\epsilon,2^\epsilon]$, so it suffices to consider
$y \in [1/2^\epsilon x,2^\epsilon x]$ for nonzero contributions. If $x < 2^{-\epsilon}$, then the integral is the same as that over $(0,\infty)$:
$$
\int_0^1 \psi_\epsilon(x/y)\frac{dy}{y}
=
\int_0^\infty \psi_\epsilon(x/y)\frac{dy}{y},
$$
in which we change variables to $z=x/y$ (using $x>0$):
$$
\int_0^\infty \psi_\epsilon(x/y)\frac{dy}{y}
=
\int_0^\infty \psi_\epsilon(z)\frac{dz}{z},
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
  refine lt_add_of_sub_left_lt <| (div_lt_iff hε.1).mp ?_
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
      rw [sub_pos, ← pow_zero 2]
      convert rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) (neg_lt_zero.mpr hε.1); norm_num
    have := (mul_lt_mul_right pos).mpr this
    ring_nf at this ⊢
    exact this
  · have : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = (2 : ℝ) ^ (ε - ε) := by
      rw [← rpow_add (by norm_num), add_neg_self, sub_self]
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
  · rw [gt_iff_lt, div_rpow, div_rpow, lt_div_iff, mul_comm_div, div_self, mul_one]
    <;> try positivity
    · exact rpow_lt_rpow (by positivity) hx2 (by positivity)
    · exact LT.lt.le <| lt_trans (by positivity) hx2
  · rw [div_rpow, ← rpow_mul, mul_div_cancel₀ 1 <| ne_of_gt εpos, rpow_one] <;> positivity
  · have : y ^ (1 / ε) ≤ y := by
      nth_rewrite 2 [← rpow_one y]
      exact rpow_le_rpow_of_exponent_ge ypos y1 (by linarith [one_lt_one_div εpos ε1])
    have pos : 0 < y ^ (1 / ε) := rpow_pos_of_pos ypos _
    rw [ge_iff_le, div_le_iff, div_mul_eq_mul_div, le_div_iff', mul_comm] <;> try linarith
  · rw [ge_iff_le, le_div_iff <| ypos]; exact (mul_le_iff_le_one_right zero_lt_two).mpr y1
/-%%
\begin{lemma}[Smooth1Properties_above]\label{Smooth1Properties_above}
\lean{Smooth1Properties_above}\leanok
Fix $0<\epsilon<1$. There is an absolute constant $c>0$ so that:
if $x\geq (1+c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 0.$$
\end{lemma}
%%-/
lemma Smooth1Properties_above {Ψ : ℝ → ℝ} (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (hε : ε ∈ Ioo 0 1) :
    ∃ (c : ℝ), 0 < c ∧ ∀ (x : ℝ), 1 + c * ε ≤ x → Smooth1 Ψ ε x = 0 := by
  set c := 2 * Real.log 2; use c
  constructor
  · simp only [c, zero_lt_two, mul_pos_iff_of_pos_left]; exact log_pos (by norm_num)
  intro x hx
  have hx2 := Smooth1Properties_above_aux hx hε
  unfold Smooth1 MellinConvolution
  simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have ypos := mem_Ioi.mp hy
  by_cases y1 : y ≤ 1; swap; simp [ypos, y1]
  simp only [mem_Ioi.mp hy, y1, and_self, ↓reduceIte, div_eq_zero_iff]; left
  apply DeltaSpikeSupport hε.1 ?_ suppΨ
  simp only [mem_Icc, not_and, not_le]
  swap; suffices h : 2 ^ ε < x / y by
    linarith [(by apply rpow_pos_of_pos (by norm_num) : 0 < (2 : ℝ) ^ ε)]
  all_goals
  try intro
  have : x / y = ((x / y) ^ (1 / ε)) ^ ε := by
    rw [← rpow_mul]
    simp only [one_div, inv_mul_cancel (ne_of_gt hε.1), rpow_one]
    apply div_nonneg_iff.mpr; left;
    exact ⟨(le_trans (rpow_pos_of_pos (by norm_num) ε).le) hx2.le, ypos.le⟩
  rw [this]
  refine rpow_lt_rpow (by norm_num) ?_ hε.1
  exact Smooth1Properties_above_aux2 hε ⟨ypos, y1⟩ hx2
/-%%
\begin{proof}\leanok
\uses{Smooth1, MellinConvolution, Smooth1Properties_estimate}
Again the Mellin convolution is
$$\int_0^1 \psi_\epsilon(x/y)\frac{dy}{y},$$
but now if $x > 2^\epsilon$, then the support of $\psi_\epsilon$ is disjoint
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

lemma DeltaSpikeNonNeg_of_NonNeg {Ψ : ℝ → ℝ} (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x)
     {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
    0 ≤ DeltaSpike Ψ ε x := by
  dsimp [DeltaSpike]
  have : 0 < x ^ (1 / ε) := by positivity
  have : 0 ≤ Ψ (x ^ (1 / ε)) := Ψnonneg _ this
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
If $\psi$ is nonnegative, then $\widetilde{1_{\epsilon}}(x)$ is nonnegative.
\end{lemma}
%%-/
lemma Smooth1Nonneg {Ψ : ℝ → ℝ} (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) {ε x : ℝ} (xpos : 0 < x)
    (εpos : 0 < ε) : 0 ≤ Smooth1 Ψ ε x := by
  dsimp [Smooth1]
  apply MellinConvNonNeg_of_NonNeg ?_ ?_ xpos
  · intro y hy; by_cases h : y ≤ 1 <;> simp [h, hy]
  · intro y ypos; exact DeltaSpikeNonNeg_of_NonNeg Ψnonneg ypos εpos
/-%%
\begin{proof}\uses{Smooth1, MellinConvolution, DeltaSpike}\leanok
By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
$$
  \widetilde{1_\epsilon}(x)=\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\psi((x/y)^{\frac1\epsilon}) \frac{dy}y
$$
and all the factors in the integrand are nonnegative.
\end{proof}
%%-/

lemma Smooth1LeOne_aux {x ε : ℝ} {Ψ : ℝ → ℝ} (xpos : 0 < x) (εpos : 0 < ε)
    (mass_one : ∫ x in Ioi 0, Ψ x / x = 1) :
    ∫ (y : ℝ) in Ioi 0, Ψ ((x / y) ^ (1 / ε)) / ε / y = 1 := by
    calc
      _ = ∫ (y : ℝ) in Ioi 0, (Ψ (y ^ (1 / ε)) / ε) / y := ?_
      _ = ∫ (y : ℝ) in Ioi 0, Ψ y / y := ?_
      _ = 1 := mass_one
    · have := integral_comp_div_I0i_haar (fun y ↦ Ψ ((x / y) ^ (1 / ε)) / ε) xpos
      convert this.symm using 1
      congr; funext y; congr; field_simp [mul_comm]
    · have := integral_comp_rpow_I0i_haar_real (fun y ↦ Ψ y) (one_div_ne_zero εpos.ne')
      field_simp [ ← this, abs_of_pos <| one_div_pos.mpr εpos]

/-%%
\begin{lemma}[Smooth1LeOne]\label{Smooth1LeOne}\lean{Smooth1LeOne}\leanok
If $\psi$ is nonnegative and has mass one, then $\widetilde{1_{\epsilon}}(x)\le 1$, $\forall x>0$.
\end{lemma}
%%-/
lemma Smooth1LeOne {Ψ : ℝ → ℝ} (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (mass_one : ∫ x in Ioi 0, Ψ x / x = 1) {ε : ℝ} (εpos : 0 < ε) :
    ∀ (x : ℝ), 0 < x → Smooth1 Ψ ε x ≤ 1 := by
  unfold Smooth1 MellinConvolution DeltaSpike
  intro x xpos
  have := Smooth1LeOne_aux xpos εpos mass_one
  calc
    _ = ∫ (y : ℝ) in Ioi 0, (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (Ψ ((x / y) ^ (1 / ε)) / ε / y) := ?_
    _ ≤ ∫ (y : ℝ) in Ioi 0, (Ψ ((x / y) ^ (1 / ε)) / ε) / y := ?_
    _ = 1 := this
  · rw [setIntegral_congr (by simp)]
    simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
    intro y hy; aesop
  · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one this) (by simp) ?_
    · refine integrable_of_integral_eq_one this |>.bdd_mul ?_ (by use 1; aesop)
      have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) = indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
        aesop
      simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
      exact aestronglyMeasurable_one
    · simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
      intro y hy
      by_cases h : y ≤ 1; aesop
      field_simp [mem_Ioc, h, and_false, reduceIte]
      apply mul_nonneg
      · apply Ψnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
      · apply inv_nonneg.mpr <| mul_nonneg εpos.le (mem_Ioi.mp hy).le
/-%%
\begin{proof}\uses{Smooth1,MellinConvolution,DeltaSpike,SmoothExistence}\leanok
By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
$$
  \widetilde{1_\epsilon}(x)=\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\psi((x/y)^{\frac1\epsilon}) \frac{dy}y
$$
and since $1_{(0,1]}(y)\le 1$, and all the factors in the integrand are nonnegative,
$$
  \widetilde{1_\epsilon}(x)\le\int_0^\infty \frac1\epsilon\psi((x/y)^{\frac1\epsilon}) \frac{dy}y
$$
(because in mathlib the integral of a non-integrable function is $0$, for the inequality above to be true, we must prove that $\psi((x/y)^{\frac1\epsilon})/y$ is integrable; this follows from the computation below).
We then change variables to $z=(x/y)^{\frac1\epsilon}$:
$$
  \widetilde{1_\epsilon}(x)\le\int_0^\infty \psi(z) \frac{dz}z
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
\frac{1}{s}\left(\mathcal{M}(\psi)\left(\epsilon s\right)\right).$$
\end{lemma}
%%-/
lemma MellinOfSmooth1a (Ψ : ℝ → ℝ) (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) : 𝓜 ((Smooth1 Ψ ε) ·) s = 1 / s * 𝓜 (Ψ ·) (ε * s) := by
  let f' : ℝ → ℂ := fun x ↦ DeltaSpike Ψ ε x
  let f : ℝ → ℂ := fun x ↦ DeltaSpike Ψ ε x / x
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
    · simp only [F, F', f, g, mul_ite, mul_one, mul_zero, Function.uncurry_apply_pair]
      intro ⟨x, y⟩ hz
      by_cases hS : ⟨x, y⟩ ∈ S <;> simp only [hS, piecewise, hz]
      <;> simp only [mem_prod, mem_Ioi, mem_setOf_eq, not_and, not_le, S] at hz hS
      · simp [hS, div_pos hz.1 hz.2, (div_le_one hz.2).mpr hS.2.1]
      · by_cases hxy : x / y ≤ 1; swap; simp [hxy]
        have hy : y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
          simp only [mem_Icc, not_and, not_le]; exact hS hz.1 <| (div_le_one hz.2).mp hxy
        simp [DeltaSpikeSupport εpos hz.2.le suppΨ hy]
    · apply Integrable.piecewise Smeas ?_ integrableOn_zero
      simp only [IntegrableOn, Measure.restrict_restrict_of_subset SsubI]
      apply MeasureTheory.Integrable.mono_measure ?_
      apply MeasureTheory.Measure.restrict_mono' (HasSubset.Subset.eventuallyLE SsubT) le_rfl
      have : volume.restrict (Tx ×ˢ Ty) = (volume.restrict Tx).prod (volume.restrict Ty) := by
        rw [Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
      conv => rw [this]; lhs; intro; rw [mul_comm]
      apply MeasureTheory.Integrable.prod_mul (f := fun x ↦ (x : ℂ) ^ (s - 1))
        (μ := Measure.restrict volume Tx)
      · apply integrableOn_Ioc_iff_integrableOn_Ioo.mpr ?_
        apply (intervalIntegral.integrableOn_Ioo_cpow_iff (s := s - 1) (t := (2 : ℝ) ^ ε) ?_).mpr
        · simp [hs]
        · apply rpow_pos_of_pos (by norm_num)
      · apply (ContinuousOn.div ?_ ?_ ?_).integrableOn_compact isCompact_Icc
        · exact (DeltaSpikeOfRealContinuous εpos diffΨ).continuousOn
        · exact continuous_ofReal.continuousOn
        · intro x hx; simp only [mem_Icc] at hx; simp only [ofReal_ne_zero]
          linarith [(by apply rpow_pos_of_pos (by norm_num) : (0 : ℝ) < 2 ^ (-ε))]

  have : 𝓜 (MellinConvolution g f') s = 𝓜 g s * 𝓜 f' s := by
    rw [mul_comm, ← MellinConvolutionTransform f' g s (by convert int_F using 1; field_simp [F, f, f'])]
    dsimp [MellinTransform]; rw [setIntegral_congr (by simp)]
    intro x hx; simp_rw [MellinConvolutionSymmetric _ _ <| mem_Ioi.mp hx]

  convert this using 1
  · congr; funext x; convert integral_ofReal.symm
    simp only [MellinConvolution, RCLike.ofReal_div, ite_mul, one_mul, zero_mul, @apply_ite ℝ ℂ,
      algebraMap.coe_zero, f, g]; rfl
  · rw [MellinOf1 s hs, MellinOfDeltaSpike Ψ εpos s]
/-%%
\begin{proof}\uses{Smooth1,MellinConvolutionTransform, MellinOfDeltaSpike, MellinOf1, MellinConvolutionSymmetric}\leanok
By Definition \ref{Smooth1},
$$
  \mathcal M(\widetilde{1_\epsilon})(s)
  =\mathcal M(1_{(0,1]}\ast\psi_\epsilon)(s)
  .
$$
We wish to apply Theorem \ref{MellinConvolutionTransform}.
To do so, we must prove that
$$
  (x,y)\mapsto 1_{(0,1]}(y)\psi_\epsilon(x/y)/y
$$
is integrable on $[0,\infty)^2$.
It is actually easier to do this for the convolution: $\psi_\epsilon\ast 1_{(0,1]}$, so we use Lemma \ref{MellinConvolutionSymmetric}: for $x\neq0$,
$$
  1_{(0,1]}\ast\psi_\epsilon(x)=\psi_\epsilon\ast 1_{(0,1]}(x)
  .
$$
Now, for $x=0$, both sides of the equation are 0, so the equation also holds for $x=0$.
Therefore,
$$
  \mathcal M(\widetilde{1_\epsilon})(s)
  =\mathcal M(\psi_\epsilon\ast 1_{(0,1]})(s)
  .
$$
Now,
$$
  (x,y)\mapsto \psi_\epsilon(y)1_{(0,1]}(x/y)\frac{x^{s-1}}y
$$
has compact support that is bounded away from $y=0$ (specifically $y\in[2^{-\epsilon},2^\epsilon]$ and $x\in(0,y]$), so it is integrable.
We can thus apply Theorem \ref{MellinConvolutionTransform} and find
$$
  \mathcal M(\widetilde{1_\epsilon})(s)
  =\mathcal M(\psi_\epsilon)(s)\mathcal M(1_{(0,1]})(s)
  .
$$
By Lemmas \ref{MellinOf1} and \ref{MellinOfDeltaSpike},
$$
  \mathcal M(\widetilde{1_\epsilon})(s)
  =\frac1s\mathcal M(\psi)(\epsilon s)
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
lemma MellinOfSmooth1b {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    {σ₁ σ₂ : ℝ} (σ₁pos : 0 < σ₁) (ε : ℝ) (εpos : 0 < ε) :
    (fun (s : ℂ) ↦ ‖𝓜 ((Smooth1 Ψ ε) ·) s‖)
      =O[Filter.principal {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂}]
      fun s ↦ 1 / (ε * ‖s‖ ^ 2) := by
  have := MellinOfPsi diffΨ suppΨ (mul_pos εpos σ₁pos) (σ₂ := ε * σ₂)
  rw [Asymptotics.isBigO_iff] at this ⊢
  obtain ⟨c, hc⟩ := this
  use c
  simp only [norm_norm, norm_div, norm_one, eventually_principal, mem_setOf_eq] at hc ⊢
  intro s hs
  rw [MellinOfSmooth1a Ψ diffΨ suppΨ εpos <| gt_of_ge_of_gt hs.1 σ₁pos]
  have : ‖𝓜 (fun x ↦ ↑(Ψ x)) (ε * s)‖ ≤ c * (1 / ‖ε * s‖) := by
    refine hc (ε * s) ?_
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact ⟨(mul_le_mul_left εpos).mpr hs.1, (mul_le_mul_left εpos).mpr hs.2⟩
  convert mul_le_mul_of_nonneg_left (a := 1 / ‖s‖) this ?_ using 1
  · simp
  · simp only [Complex.norm_eq_abs, norm_mul, Real.norm_eq_abs, norm_pow, Complex.abs_abs, one_div,
    mul_inv_rev, abs_ofReal]; ring_nf
  · exact div_nonneg (by norm_num) (norm_nonneg s)
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

lemma MellinOfSmooth1c {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, Ψ x / x = 1) :
    (fun ε ↦ 𝓜 ((Smooth1 Ψ ε) ·) 1 - 1) =O[𝓝[>]0] id := by
  have h := MellinOfDeltaSpikeAt1_asymp diffΨ suppΨ mass_one
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc, Ioo_mem_nhdsWithin_Ioi' (by linarith : (0 : ℝ) < 1)] with ε hε hε'
  simp_rw [MellinOfSmooth1a Ψ diffΨ suppΨ hε'.1 (s := 1) (by norm_num), mul_one]
  simpa using hε
/-%%
\begin{proof}\uses{MellinOfSmooth1a, MellinOfDeltaSpikeAt1, MellinOfDeltaSpikeAt1_asymp}\leanok
Follows from Lemmas \ref{MellinOfSmooth1a}, \ref{MellinOfDeltaSpikeAt1} and \ref{MellinOfDeltaSpikeAt1_asymp}.
\end{proof}
%%-/
