import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntegralEqImproper
import PrimeNumberTheoremAnd.PerronFormula

-- TODO: move near `MeasureTheory.set_integral_prod`
theorem MeasureTheory.set_integral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E] [MeasureTheory.SigmaFinite ν]
    [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ] (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by
  apply integral_integral_swap
  convert hf.integrable
  exact Measure.prod_restrict s t

-- How do deal with this coersion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

section from_PR10944

open Real Complex Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def VerticalIntegrable (f : ℂ → E) (σ : ℝ) (μ : Measure ℝ := by volume_tac) : Prop :=
  Integrable (fun (y : ℝ) ↦ f (σ + y * I)) μ

end from_PR10944

open Complex Topology Filter Real MeasureTheory Set


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
  ∫ x in Set.Ioi 0, f x * x ^ (s - 1)

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
lemma PerronInverseMellin_lt {t x : ℝ} (t_pos : 0 < t) (t_lt_x : t < x) {σ : ℝ} (σ_pos : 0 < σ) :
    MellinInverseTransform (Perron.f t) σ x = 0 := by
  dsimp [MellinInverseTransform, VerticalIntegral']
  have xpos : 0 < x := by linarith
  have txinvpos : 0 < t / x := div_pos t_pos xpos
  have txinv_ltOne : t / x < 1 := (div_lt_one xpos).mpr t_lt_x
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, neg_eq_zero, mul_eq_zero, I_ne_zero,
    inv_eq_zero, ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero, or_self, false_or]
  convert Perron.formulaLtOne txinvpos txinv_ltOne σ_pos using 2
  ext1 s
  convert Perron.f_mul_eq_f t_pos xpos s using 1
  ring
/-%%
\begin{proof}
\uses{Perron.formulaLtOne}
\leanok
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
lemma PerronInverseMellin_gt {t x : ℝ} (x_pos : 0 < x) (x_lt_t : x < t) {σ : ℝ} (σ_pos : 0 < σ) :
    MellinInverseTransform (Perron.f t) σ x = 1 - x / t := by
  dsimp [MellinInverseTransform]
  have tpos : 0 < t := by linarith
  have txinv_gtOne : 1 < t / x := (one_lt_div x_pos).mpr x_lt_t
  rw [← smul_eq_mul]
  convert Perron.formulaGtOne txinv_gtOne σ_pos using 2
  · congr
    ext1 s
    convert Perron.f_mul_eq_f tpos x_pos s using 1
    ring
  · field_simp
/-%%
\begin{proof}
\uses{Perron.formulaGtOne}\leanok
This is a straightforward calculation.
\end{proof}
%%-/

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
lemma PartialIntegration (f g : ℝ → ℂ) (fDiff : DifferentiableOn ℝ f (Set.Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Set.Ioi 0))
    (fDerivgInt : IntegrableOn (f * deriv g) (Set.Ioi 0))
    (gDerivfInt : IntegrableOn (deriv f * g) (Set.Ioi 0))
    (lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0))
    (lim_at_inf : Tendsto (f * g) atTop (𝓝 0)) :
    ∫ x in Set.Ioi 0, f x * deriv g x = -∫ x in Set.Ioi 0, deriv f x * g x := by
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx ↦ fDiff.hasDerivAt (Ioi_mem_nhds hx))
    (fun x hx ↦ gDiff.hasDerivAt (Ioi_mem_nhds hx))
    fDerivgInt gDerivfInt lim_at_zero lim_at_inf
/-%%
\begin{proof}\leanok
Partial integration.
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
    (fDiff : DifferentiableOn ℝ f (Set.Ioi 0))
    (hfs : Tendsto (fun x ↦ f x * x ^ s) (𝓝[>]0) (𝓝 0))
    (hfinf : Tendsto (fun x ↦ f x * x ^ s) atTop (𝓝 0)) :
    ∫ x in Set.Ioi 0, f x * x ^ s / x = - ∫ x in Set.Ioi 0, (deriv f x) * x ^ s / s := by
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
lemma MellinInversion_aux2 {f : ℝ → ℂ} (s : ℂ) (fDiff : DifferentiableOn ℝ f (Set.Ioi 0))
    (fDiff2 : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfs : Tendsto (fun x ↦ deriv f x * x ^ s) (𝓝[>]0) (𝓝 0))
    (hfinf : Tendsto (fun x ↦ deriv f x * x ^ s) atTop (𝓝 0)) :
    ∫ x in Set.Ioi 0, (deriv f x) * x ^ s =
      -∫ x in Set.Ioi 0, (deriv (deriv f) x) * x ^ (s + 1) / (s + 1) := by
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
    (fInt : IntegrableOn (fun x ↦ f x * (x : ℂ) ^ (σ : ℂ)) (Set.Ioi 0)) :
    IntegrableOn (fun (⟨x, t⟩ : ℝ × ℝ) =>
      f x * x ^ (σ + t * I) / ((σ + t * I) * ((σ + t * I) + 1)))
      ((Set.Ioi 0).prod (univ : Set ℝ)) := by
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
    (fInt : IntegrableOn (fun x ↦ f x * (x : ℂ) ^ (σ : ℂ)) (Set.Ioi 0)) :
    VerticalIntegral (fun s ↦ ∫ x in Set.Ioi 0, f x * (x : ℂ) ^ (s + 1) / (s * (s + 1))) σ =
      ∫ x in Set.Ioi 0, VerticalIntegral (fun s ↦ f x * (x : ℂ) ^ (s + 1) / (s * (s + 1))) σ := by
  sorry -- `MeasureTheory.integral_prod` and `MeasureTheory.integral_swap` should be useful here
/-%
\begin{proof}
\uses{MellinInversion_aux3}
Fubini-Tonelli.
\end{proof}
%-/

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
    MellinInverseTransform (MellinTransform f) σ x = f x := by
  -- Done in PR#10944
  sorry
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

variable {𝕂 : Type*} [IsROrC 𝕂]

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
  ∫ y in Set.Ioi 0, f y * g (x / y) / y

/-%%
Let us start with a simple property of the Mellin convolution.
\begin{lemma}[MellinConvolutionSymmetric]\label{MellinConvolutionSymmetric}
\lean{MellinConvolutionSymmetric}\leanok
Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$, for $x\neq0$,
$$
  (f\ast g)(x)=(g\ast f)(x)
  .
$$
\end{lemma}
%%-/
lemma MellinConvolutionSymmetric (f g : ℝ → ℂ) {x : ℝ} (xpos: 0<x) :
    MellinConvolution f g x = MellinConvolution g f x :=
  sorry

/-%%
\begin{proof}
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
    MellinTransform (MellinConvolution f g) s = MellinTransform f s * MellinTransform g s := by
  dsimp [MellinTransform, MellinConvolution]
  set f₁ : ℝ × ℝ → ℂ := fun ⟨x, y⟩ ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
  calc
    _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioi 0, f₁ (x, y) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f₁ (x, y) := set_integral_integral_swap _ hf
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * g (x / y) / ↑y * ↑x ^ (s - 1) := rfl
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * g (x * y / y) / ↑y * ↑(x * y) ^ (s - 1) * y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f y * ↑y ^ (s - 1) * (g x * ↑x ^ (s - 1)) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, f y * ↑y ^ (s - 1) * ∫ (x : ℝ) in Ioi 0, g x * ↑x ^ (s - 1) := ?_
    _ = _ := integral_mul_right _ _
  <;> try (rw [set_integral_congr (by simp)]; intro y hy)
  · simp only [integral_mul_right]; rfl
  · simp only [integral_mul_right]
    rw [mul_comm]
    have abs : |y⁻¹| = y⁻¹ := abs_of_pos <| inv_pos.mpr hy
    let fx : ℝ → ℂ := fun x ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
    have := abs ▸ MeasureTheory.integral_comp_mul_right_Ioi fx 0 hy
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := slitPlane_ne_zero (Or.inl hy)
    simp [fx] at this
    simp only [ofReal_mul, this, ← mul_assoc, mul_inv_cancel y_ne_zeroℂ, one_mul]
  · simp only [ofReal_mul]
    rw [set_integral_congr (by simp)]
    intro x hx
    have y_ne_zeroℝ : y ≠ 0 := ne_of_gt (mem_Ioi.mp hy)
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := by exact_mod_cast y_ne_zeroℝ
    field_simp [mul_cpow_ofReal_nonneg (LT.lt.le hx) (LT.lt.le hy)]
    ring
  · exact integral_mul_left _ _

/-%%
\begin{proof}
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

lemma Function.support_id : Function.support (fun x : ℝ => x) = Set.Iio 0 ∪ Set.Ioi 0 := by
  ext x
  simp only [mem_support, ne_eq, Set.Iio_union_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff]

attribute [- simp] one_div

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

lemma SmoothExistence : ∃ (Ψ : ℝ → ℝ), (∀ n, ContDiff ℝ n Ψ) ∧ (∀ x, 0 ≤ Ψ x) ∧
    Ψ.support ⊆ Set.Icc (1 / 2) 2 ∧ ∫ x in Set.Ici 0, Ψ x / x = 1 := by
  suffices h : ∃ (Ψ : ℝ → ℝ), (∀ n, ContDiff ℝ n Ψ) ∧ (∀ x, 0 ≤ Ψ x) ∧
      Ψ.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, Ψ x / x by
    rcases h with ⟨Ψ, hΨ, hΨnonneg, hΨsupp, hΨpos⟩
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

  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3/2) (d := 2) (by linarith)
    (by linarith)
  rcases this with ⟨Ψ, hΨContDiff, _, hΨ0, hΨ1, hΨSupport⟩
  use Ψ
  use hΨContDiff
  unfold Set.indicator at hΨ0 hΨ1
  simp only [Set.mem_Icc, Pi.one_apply, Pi.le_def, Set.mem_Ioo] at hΨ0 hΨ1
  constructor
  · intro x
    apply le_trans _ (hΨ0 x)
    simp [apply_ite]
  constructor
  · simp only [hΨSupport, Set.subset_def, Set.mem_Ioo, Set.mem_Icc, and_imp]
    intro y hy hy'
    exact ⟨by linarith, by linarith⟩
  · rw [MeasureTheory.integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, MeasureTheory.Measure.restrict_apply']
      rw [hΨSupport]
      rw [Function.support_id]
      have : (Set.Ioo (1 / 2 : ℝ) 2 ∩ (Set.Iio 0 ∪ Set.Ioi 0) ∩ Set.Ici 0) =
        Set.Ioo (1 / 2) 2 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iio, Set.mem_Ioi,
          Set.mem_union, not_lt, and_true, not_le]
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
/-- Need to intersect `cocompact` filter `within` `s.re` bounded -/
lemma MellinOfPsi {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2) :
    (fun s ↦ Complex.abs (MellinTransform (Ψ ·) s)) =O[cocompact ℂ]
      fun s ↦ 1 / Complex.abs s := by
  sorry
/-%%
\begin{proof}
\uses{MellinTransform, SmoothExistence}
Integrate by parts:
$$
\left|\int_0^\infty \psi(x)x^s\frac{dx}{x}\right| =
\left|-\int_0^\infty \psi'(x)\frac{x^{s}}sdx\right|
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
  fun x => Ψ (x ^ (1 / ε)) / ε

/-%%
This spike still has mass one:
\begin{lemma}[DeltaSpikeMass]\label{DeltaSpikeMass}\lean{DeltaSpikeMass}\leanok
For any $\epsilon>0$, we have
$$\int_0^\infty \psi_\epsilon(x)\frac{dx}{x} = 1.$$
\end{lemma}
%%-/

lemma DeltaSpikeMass {Ψ : ℝ → ℝ} (mass_one: ∫ x in Set.Ioi 0, Ψ x / x = 1) {ε : ℝ}
    (εpos : 0 < ε) : ∫ x in Set.Ioi 0, ((DeltaSpike Ψ ε) x) / x = 1 :=
  calc
    _ = ∫ (x : ℝ) in Set.Ioi 0, (|1/ε| * x ^ (1 / ε - 1)) •
      ((fun z => (Ψ z) / z) (x ^ (1 / ε))) := by
      apply MeasureTheory.set_integral_congr_ae measurableSet_Ioi
      filter_upwards with x hx
      simp only [Set.mem_Ioi, smul_eq_mul, abs_of_pos (one_div_pos.mpr εpos)]
      symm ; calc
        _ = (Ψ (x ^ (1 / ε)) / x ^ (1 / ε)) * x ^ (1 / ε - 1) * (1 / ε) := by ring
        _ = _ := by rw [rpow_sub hx, rpow_one]
        _ = (Ψ (x ^ (1 / ε)) / x ^ (1 / ε) * x ^ (1 / ε) / x) * (1/ ε) := by ring
        _ = _ := by rw [div_mul_cancel _ (ne_of_gt (Real.rpow_pos_of_pos hx (1/ε)))]
        _ = (Ψ (x ^ (1 / ε)) / ε / x) := by ring
    _ = 1 := by
      rw [MeasureTheory.integral_comp_rpow_Ioi (fun z => (Ψ z) / z), ← mass_one]
      simp only [ne_eq, div_eq_zero_iff, one_ne_zero, εpos.ne', or_self, not_false_eq_true]

/-%%
\begin{proof}\leanok
\uses{DeltaSpike}
Substitute $y=x^{1/\epsilon}$, and use the fact that $\psi$ has mass one, and that $dx/x$ is Haar
measure.
\end{proof}
%%-/


theorem Complex.ofReal_rpow {x : ℝ} (h:x>0) (y: ℝ) : (((x:ℝ) ^ (y:ℝ)):ℝ) = (x:ℂ) ^ (y:ℂ) := by
  rw [Real.rpow_def_of_pos h, ofReal_exp, ofReal_mul, Complex.ofReal_log h.le,
    Complex.cpow_def_of_ne_zero]
  simp only [ne_eq, ofReal_eq_zero, ne_of_gt h, not_false_eq_true]

/-%%
The Mellin transform of the delta spike is easy to compute.
\begin{theorem}[MellinOfDeltaSpike]\label{MellinOfDeltaSpike}\lean{MellinOfDeltaSpike}\leanok
For any $\epsilon>0$, the Mellin transform of $\psi_\epsilon$ is
$$\mathcal{M}(\psi_\epsilon)(s) = \mathcal{M}(\psi)\left(\epsilon s\right).$$
\end{theorem}
%%-/
theorem MellinOfDeltaSpike (Ψ : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    MellinTransform ((DeltaSpike Ψ ε) ·) s = MellinTransform (Ψ ·) (ε * s) := by
  unfold MellinTransform DeltaSpike
  rw [← MeasureTheory.integral_comp_rpow_Ioi (fun z => ((Ψ z): ℂ) * (z:ℂ)^((ε : ℂ)*s-1))
    (one_div_ne_zero (ne_of_gt εpos))]
  apply MeasureTheory.set_integral_congr_ae measurableSet_Ioi
  filter_upwards with x hx

  -- Simple algebra, would be nice if some tactic could handle this
  have log_x_real: (Complex.log (x:ℂ)).im=0 := by
    rw [← ofReal_log, ofReal_im]
    exact LT.lt.le hx
  rw [div_eq_mul_inv, ofReal_mul]
  symm
  rw [abs_of_pos (one_div_pos.mpr εpos)]
  simp only [real_smul, ofReal_mul, ofReal_div, ofReal_one]
  simp only [Complex.ofReal_rpow hx]
  rw [← Complex.cpow_mul, mul_sub]
  simp only [← mul_assoc, ofReal_sub, ofReal_div, ofReal_one, mul_one, ofReal_inv]
  rw [one_div_mul_cancel, mul_comm (1 / (ε:ℂ)) _, mul_comm, ← mul_assoc, ← mul_assoc,
    ← Complex.cpow_add]
  ring_nf
  exact slitPlane_ne_zero (Or.inl hx)
  exact slitPlane_ne_zero (Or.inl εpos)
  simp only [im_mul_ofReal, log_x_real, zero_mul, Left.neg_neg_iff, pi_pos]
  simp only [im_mul_ofReal, log_x_real, zero_mul, pi_nonneg]

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
    MellinTransform ((DeltaSpike Ψ ε) ·) 1 = MellinTransform (Ψ ·) ε := by
  convert MellinOfDeltaSpike Ψ εpos 1
  simp only [mul_one]
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
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) :
    (fun (ε : ℝ) ↦ (MellinTransform (Ψ ·) ε) - 1) =O[𝓝[>]0] id := by
  sorry -- use `mellin_differentiableAt_of_isBigO_rpow` for differentiability at 0
/-%%
\begin{proof}
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
lemma MellinOf1 (s : ℂ) (h : s.re > 0) :
    MellinTransform ((fun x => if x ≤ 1 then 1 else 0)) s = 1 / s := by
  convert (hasMellin_one_Ioc h).right using 1
  apply MeasureTheory.set_integral_congr_ae measurableSet_Ioi
  filter_upwards with x hx
  rw [smul_eq_mul, mul_comm]
  congr
  simp only [mem_Ioc, eq_iff_iff, iff_and_self]
  apply fun _ => hx

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
  MellinConvolution (fun x => if x ≤ 1 then 1 else 0) (DeltaSpike Ψ ε)

/-%%
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%%-/

lemma Smooth1Properties_estimate {ε : ℝ}
    {eps_pos : 0<ε} :
    (1-2^(-ε))/ε < Real.log 2 :=
  sorry

/-%%
\begin{proof}
Let $\alpha:=2^\epsilon>1$, in terms of which we wish to prove
$$
  1\geqslant\frac{1-1/\alpha}{\log \alpha}
  .
$$
In addition,
$$
  \frac d{d\alpha}\left(1-\frac1\alpha-\log \alpha\right)=\frac1{\alpha^2}(1-\alpha)<0
$$
so $1-1/\alpha-\log\alpha$ is monotone decreasing so it is smaller than its value at $\alpha=1$:
$$
  1-\frac1\alpha-\log\alpha<0
  .
$$
We conclude the proof using $\log\alpha>0$.
\end{proof}
%%-/


/-%%
In particular, we have the following two properties.
\begin{lemma}[Smooth1Properties_below]\label{Smooth1Properties_below}
\lean{Smooth1Properties_below}\leanok
Fix $\epsilon>0$. There is an absolute constant $c>0$ so that:
If $0<x\leq (1-c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 1.$$
\end{lemma}
%%-/
lemma Smooth1Properties_below {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2) (ε : ℝ)
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ ∀ (x : ℝ), 0 < x → x ≤ 1 - c * ε → Smooth1 Ψ ε x = 1 := by
  sorry
/-%%
\begin{proof}
\uses{Smooth1, MellinConvolution,DeltaSpikeMass, Smooth1Properties_estimate}
Opening the definition, we have that the Mellin convolution of $1_{(0,1]}$ with $\psi_\epsilon$ is
$$
\int_0^\infty 1_{(0,1]}(y)\psi_\epsilon(x/y)\frac{dy}{y}
=
\int_0^1 \psi_\epsilon(x/y)\frac{dy}{y}.
$$
The support of $\psi_\epsilon$ is contained in $[1/2^\epsilon,2^\epsilon]$, so
$y \in [1/2^\epsilon x,2^\epsilon x]$. If $x \le 2^{-\epsilon}$, then the integral is the same as that over $(0,\infty)$:
$$
\int_0^\infty 1_{(0,1]}(y)\psi_\epsilon(x/y)\frac{dy}{y}
=
\int_0^\infty \psi_\epsilon(x/y)\frac{dy}{y}.
$$
in which we change variables to $z=x/y$ (using $x>0$):
$$
\int_0^\infty 1_{(0,1]}(y)\psi_\epsilon(x/y)\frac{dy}{y}
=
\int_0^\infty \psi_\epsilon(z)\frac{dz}{z}.
$$
which is equal to one by Lemma \ref{DeltaSpikeMass}.
We then choose
$$
  c:=\log 2
$$
which satisfies
$$
  c\geqslant\frac{1-2^{-\epsilon}}\epsilon
$$
by Lemma \ref{Smooth1Properties_estimate}, so
$$
  1-c\epsilon\leqslant 2^{-\epsilon}
  .
$$
\end{proof}
%%-/

/-%%
\begin{lemma}[Smooth1Properties_above]\label{Smooth1Properties_above}
\lean{Smooth1Properties_above}\leanok
Fix $0<\epsilon<1$. There is an absolute constant $c>0$ so that:
if $x\geq (1+c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 0.$$
\end{lemma}
%%-/
lemma Smooth1Properties_above {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2) (ε : ℝ)
    (eps_pos: 0 < ε) (eps_lt1: ε < 1)
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ ∀ (x : ℝ), x ≥ 1 + c * ε → Smooth1 Ψ ε x = 0 := by
  sorry
/-%%
\begin{proof}
\uses{Smooth1, MellinConvolution, Smooth1Properties_estimate}
Again the Mellin convolution is
$$\int_0^1 \psi_\epsilon(x/y)\frac{dy}{y},$$
but now if $x \ge 2^\epsilon$, then the support of $\psi_\epsilon$ is disjoint
from the region of integration, and hence the integral is zero.
We choose
$$
  c:=2\log 2
  .
$$
By Lemma \ref{Smooth1Properties_estimate},
$$
  c\geqslant 2\frac{1-2^{-\epsilon}}\epsilon\geqslant 2^\epsilon\frac{1-2^{-\epsilon}}\epsilon
  =
  \frac{2^\epsilon-1}\epsilon
$$
so
$$
  1+c\epsilon\geqslant 2^\epsilon
  .
$$
\end{proof}
%%-/

/-%%
\begin{lemma}[Smooth1Nonneg]\label{Smooth1Nonneg}\lean{Smooth1Nonneg}\leanok
If $\psi$ is nonnegative, then $\widetilde{1_{\epsilon}}(x)$ is nonnegative.
\end{lemma}
%%-/
lemma Smooth1Nonneg {Ψ : ℝ → ℝ} (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (ε : ℝ) :
    ∀ (x : ℝ), 0 ≤ Smooth1 Ψ ε x := by
  sorry
/-%%
\begin{proof}\uses{Smooth1,MellinConvolution,DeltaSpike}
By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
$$
  \widetilde{1_\epsilon}(x)=\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\psi((x/y)^{\frac1\epsilon}) \frac{dy}y
$$
and all the factors in the integrand are nonnegative.
\end{proof}
%%-/

/-%%
\begin{lemma}[Smooth1LeOne]\label{Smooth1LeOne}\lean{Smooth1LeOne}\leanok
If $\psi$ is nonnegative and has mass one, then $\widetilde{1_{\epsilon}}(x)\le 1$, $\forall x>0$.
\end{lemma}
%%-/
lemma Smooth1LeOne {Ψ : ℝ → ℝ}
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x)
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) (ε : ℝ) :
    ∀ (x : ℝ), 0<x → Smooth1 Ψ ε x ≤ 1 := by
  sorry
/-%%
\begin{proof}\uses{Smooth1,MellinConvolution,DeltaSpike,SmoothExistence}
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
lemma MellinOfSmooth1a (Ψ : ℝ → ℝ)
    -- (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    -- (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    MellinTransform ((Smooth1 Ψ ε) ·) s = 1 / s * MellinTransform (Ψ ·) (ε * s) := by
  dsimp [Smooth1]
--  rw [MellinConvolutionTransform, MellinOf1 _ hs, MellinOfDeltaSpike Ψ (εpos) s]
  sorry
/-%%
\begin{proof}\uses{Smooth1,MellinConvolutionTransform, MellinOfDeltaSpike, MellinOf1, MellinConvolutionSymmetric}
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
-- ** Statement needs `cocompact` filter *within* `0<σ₁ ≤ ℜ s≤ σ₂` **
lemma MellinOfSmooth1b {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) (ε : ℝ) (εpos : 0 < ε) :
    (fun (s : ℂ) ↦ Complex.abs (MellinTransform ((Smooth1 Ψ ε) ·) s)) =O[cocompact ℂ]
      fun s ↦ 1 / (ε * Complex.abs s) ^ 2 := by
  --have := MellinOfSmooth1a Ψ εpos hs
  --obtain ⟨C, hC⟩  := MellinOfPsi diffΨ suppΨ
  --have := hC s
  sorry
/-%%
\begin{proof}\uses{MellinOfSmooth1a, MellinOfPsi}
Use Lemma \ref{MellinOfSmooth1a} and the bound in Lemma \ref{MellinOfPsi}.
\end{proof}
%%-/
/-%%
\begin{lemma}[MellinOfSmooth1c]\label{MellinOfSmooth1c}\lean{MellinOfSmooth1c}\leanok
At $s=1$, we have
$$\mathcal{M}(\widetilde{1_{\epsilon}})(1) = (1+O(\epsilon)).$$
\end{lemma}
%%-/
lemma MellinOfSmooth1c {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) {ε : ℝ} (εpos : 0 < ε) :
    (fun ε ↦ MellinTransform ((Smooth1 Ψ ε) ·) 1 - 1) =O[𝓝[>]0] id := by
  sorry
/-%%
\begin{proof}\uses{MellinOfSmooth1a, MellinOfDeltaSpikeAt1, MellinOfDeltaSpikeAt1_asymp}
Follows from Lemmas \ref{MellinOfSmooth1a}, \ref{MellinOfDeltaSpikeAt1} and \ref{MellinOfDeltaSpikeAt1_asymp}.
\end{proof}
%%-/
