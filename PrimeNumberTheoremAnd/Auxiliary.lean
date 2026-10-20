/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Architect
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
### Auxiliary lemmas
-/

namespace Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma deriv_ofReal (x : ℝ) : deriv ofReal x = 1 :=
  (hasDerivAt_ofReal x).deriv

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

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
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]

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
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]


section ConstantLimits

open Filter Topology

@[blueprint
  (title := "zeroTendstoDiff")
  (statement := /--
  If the limit of $0$ is $L_1 - L_2$, then $L_1 = L_2$.
  -/)
  (proof := /-- Obvious. -/)
  (latexEnv := "lemma")]
lemma zeroTendstoDiff {α E : Type*} [AddGroup E] [TopologicalSpace E] [T2Space E]
    {l : Filter α} [l.NeBot] (L₁ L₂ : E) (f : α → E) (h : ∀ᶠ T in l, f T = 0)
    (h' : Tendsto f l (𝓝 (L₂ - L₁))) : L₁ = L₂ := by
  rw [← zero_add L₁, ← @eq_sub_iff_add_eq]
  exact tendsto_nhds_unique (EventuallyEq.tendsto h) h'


@[blueprint
  (title := "limitOfConstant")
  (statement := /--
  Let $a:\R\to E$ be a function, and let $\sigma>0$ be a real number. Suppose that, for all
  $\sigma, \sigma'>0$, we have $a(\sigma')=a(\sigma)$, and that
  $\lim_{\sigma\to\infty}a(\sigma)=0$. Then $a(\sigma)=0$.
  -/)
  (latexEnv := "lemma")]
lemma limitOfConstant {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    {a : ℝ → E} {σ : ℝ} (σpos : 0 < σ)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : 0 < σ') (_ : 0 < σ''), a σ' = a σ'')
    (ha' : Tendsto a atTop (𝓝 0)) : a σ = 0 := by
  /--
  \begin{align*}
  \lim_{\sigma'\to\infty}a(\sigma) &= \lim_{\sigma'\to\infty}a(\sigma') \\
  &= 0
  \end{align*}
  -/
  have := eventuallyEq_of_mem (mem_atTop σ) fun σ' h ↦ ha σ' σ (σpos.trans_le h) σpos
  exact tendsto_const_nhds_iff.mp (ha'.congr' this)



@[blueprint
  (title := "limitOfConstantLeft")
  (statement := /--
  Let $a:\R\to E$ be a function, and let $\sigma\le -3/2$ be a real number. Suppose that, for all
  $\sigma, \sigma'\le -3/2$, we have $a(\sigma')=a(\sigma)$, and that
  $\lim_{\sigma\to-\infty}a(\sigma)=0$. Then $a(\sigma)=0$.
  -/)
  (latexEnv := "lemma")]
lemma limitOfConstantLeft {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    {a : ℝ → E} {σ : ℝ} (σlt : σ ≤ -3 / 2)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : σ' ≤ -3 / 2) (_ : σ'' ≤ -3 / 2), a σ' = a σ'')
    (ha' : Tendsto a atBot (𝓝 0)) : a σ = 0 := by
  /--
  \begin{align*}
    \lim_{\sigma'\to-\infty}a(\sigma) &= \lim_{\sigma'\to-\infty}a(\sigma') \\
    &= 0
  \end{align*}
  -/
  have := eventuallyEq_of_mem (mem_atBot (-3/2)) fun σ' h ↦ ha σ' σ h σlt
  exact tendsto_const_nhds_iff.mp (ha'.congr' this)




end ConstantLimits
