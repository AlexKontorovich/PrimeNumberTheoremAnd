import PrimeNumberTheoremAnd.PerronFormula

open Complex Topology Filter Real MeasureTheory Set

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
\begin{definition}[MellinTransform]\label{MellinTransform}\lean{MellinTransform}\leanok
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of $f$ to be the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$
\end{definition}
[Note: already exists in Mathlib, with some good API.]
%%-/
noncomputable def MellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi 0, f x * x ^ (s - 1)

/-%%
\begin{theorem}[MellinInversion]\label{MellinInversion}\lean{MellinInversion}\leanok
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
\uses{formulaLtOne, formulaGtOne, MellinTransform}
The proof is from [Goldfeld-Kontorovich 2012].
Integrate by parts twice (assuming $f$ is twice differentiable, and all occurring integrals converge absolutely).
$$
\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx = - \int_0^\infty f'(x)x^s\frac{1}{s}dx = \int_0^\infty f''(x)x^{s+1}\frac{1}{s(s+1)}dx.
$$
We now have at least quadratic decay in $s$ of the Mellin transform. Inserting this formula into the inversion formula and Fubini-Tonelli (we now have absolute convergence!) gives:
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
\begin{definition}[MellinConvolution]\label{MellinConvolution}\lean{MellinConvolution}\leanok
Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. Then we define the Mellin convolution of $f$ and $g$ to be the function $f\ast g$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$(f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}.$$
\end{definition}
%%-/
noncomputable def MellinConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Set.Ioi 0, f y * g (x / y) / y
/-%%
The Mellin transform of a convolution is the product of the Mellin transforms.
\begin{theorem}[MellinConvolutionTransform]\label{MellinConvolutionTransform}\lean{MellinConvolutionTransform}\leanok
Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. Then
$$\mathcal{M}(f\ast g)(s) = \mathcal{M}(f)(s)\mathcal{M}(g)(s).$$
** Needs conditions so that the integrals converge absolutely.**
\end{theorem}
%%-/
lemma MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ) : MellinTransform (MellinConvolution f g) s = MellinTransform f s * MellinTransform g s := by
  sorry
/-%%
\begin{proof}
\uses{MellinTransform}
This is a straightforward calculation; open the two integrals.
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

  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3/2) (d := 2) (by linarith) (by linarith)
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
\begin{theorem}[MellinOfPsi]\label{MellinOfPsi}\lean{MellinOfPsi}
The Mellin transform of $\psi$ is
$$\mathcal{M}(\psi)(s) =  O\left(\frac{1}{|s|}\right),$$
as $|s|\to\infty$.
\end{theorem}

[Of course it decays faster than any power of $|s|$, but it turns out that we will just need one power.]
%%-/
-- Better way to spell this? Using BigO and cocompact filter?
lemma MellinOfPsi {Ψ : ℝ → ℂ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ), ∀ (s : ℂ), C ≤ Complex.abs s → Complex.abs (MellinTransform Ψ s) ≤ C / Complex.abs s := by
  sorry
/-%%
\begin{proof}
\uses{MellinTransform, SmoothExistence}
Integrate by parts once.
\end{proof}
%%-/

/-%%
We can make a delta spike out of this bumpfunction, as follows.
\begin{definition}[DeltaSpike]\label{DeltaSpike}\lean{DeltaSpike}\leanok
\uses{SmoothExistence}
Let $\psi$ be a bumpfunction supported in $[1/2,2]$. Then for any $\epsilon>0$, we define the delta spike $\psi_\epsilon$ to be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
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

lemma DeltaSpikeMass {Ψ : ℝ → ℝ} (mass_one: ∫ x in Set.Ioi 0, Ψ x / x = 1) (ε : ℝ) (εpos : 0 < ε) :
    ∫ x in Set.Ioi 0, ((DeltaSpike Ψ ε) x) / x = 1 :=
  calc
    _ = ∫ (x : ℝ) in Set.Ioi 0, (|1/ε| * x ^ (1 / ε - 1)) • ((fun z => (Ψ z) / z) (x ^ (1 / ε))) := by
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
Substitute $y=x^{1/\epsilon}$, and use the fact that $\psi$ has mass one, and that $dx/x$ is Haar measure.
\end{proof}
%%-/

-- How do deal with this coersion?...
noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ (f x : ℂ)

/-%%
The Mellin transform of the delta spike is easy to compute.
\begin{theorem}[MellinOfDeltaSpike]\label{MellinOfDeltaSpike}\lean{MellinOfDeltaSpike}\leanok
For any $\epsilon>0$, the Mellin transform of $\psi_\epsilon$ is
$$\mathcal{M}(\psi_\epsilon)(s) = \mathcal{M}(\psi)\left(\epsilon s\right).$$
\end{theorem}
%%-/
theorem MellinOfDeltaSpike {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    (ε : ℝ) (s : ℂ) :
    MellinTransform (funCoe (DeltaSpike Ψ ε)) s = MellinTransform (funCoe Ψ) (ε * s) := by
  sorry
/-%%
\begin{proof}
\uses{DeltaSpike, MellinTransform}
Substitute $y=x^{1/\epsilon}$, use Haar measure; direct calculation.
\end{proof}
%%-/

/-%%
In particular, for $s=1$, we have that the Mellin transform of $\psi_\epsilon$ is $1+O(\epsilon)$.
\begin{corollary}[MellinOfDeltaSpikeAt1]\label{MellinOfDeltaSpikeAt1}\lean{MellinOfDeltaSpikeAt1}\leanok
For any $\epsilon>0$, we have
$$\mathcal{M}(\psi_\epsilon)(1) =
\mathcal{M}(\psi)(\epsilon).$$
\end{corollary}
%%-/

lemma MellinOfDeltaSpikeAt1 {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2) (ε : ℝ) :
    MellinTransform (funCoe (DeltaSpike Ψ ε)) 1 = MellinTransform (funCoe Ψ) ε := by
  sorry
/-%%
\begin{proof}
\uses{MellinOfDeltaSpike, DeltaSpikeMass}
This is immediate from the above theorem.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{MellinOfDeltaSpikeAt1_asymp}\lean{MellinOfDeltaSpikeAt1_asymp}\leanok
As $\epsilon\to 0$, we have
$$\mathcal{M}(\psi_\epsilon)(1) = 1+O(\epsilon).$$
\end{lemma}
%%-/
lemma MellinOfDeltaSpikeAt1_asymp {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) :
    (fun (ε : ℝ) ↦ (MellinTransform (funCoe Ψ) ε) - 1) =O[𝓝[>]0] id := by
  sorry
/-%%
\begin{proof}
\uses{MellinOfDeltaSpike, DeltaSpikeMass}
This follows from the fact that $\mathcal{M}(\psi)(0)=1$ (total mass one), and the differentiability of $\psi$.
\end{proof}
%%-/

/-%%
Let $1_{(0,1]}$ be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$1_{(0,1]}(x) = \begin{cases}
1 & \text{ if }x\leq 1\\
0 & \text{ if }x>1
\end{cases}.$$
This has Mellin transform
\begin{theorem}[MellinOf1]\label{MellinOf1}\lean[MellinOf1]\leanok
The Mellin transform of $1_{(0,1]}$ is
$$\mathcal{M}(1_{(0,1]})(s) = \frac{1}{s}.$$
\end{theorem}
[Note: this already exists in mathlib]
%%-/
lemma MellinOf1 (s : ℂ) : MellinTransform (funCoe (fun x => if x ≤ 1 then 1 else 0)) s = 1 / s := by
  sorry -- hasMellin_one_Ioc

/-%%
\begin{proof}
\uses{MellinTransform}
This is a straightforward calculation.
\end{proof}
%%-/

/-%%
What will be essential for us is properties of the smooth version of $1_{(0,1]}$, obtained as the
 Mellin convolution of $1_{(0,1]}$ with $\psi_\epsilon$.
\begin{definition}[Smooth1]\label{Smooth1}\uses{MellinOf1, MellinConvolution}\leanok
Let $\epsilon>0$. Then we define the smooth function $\widetilde{1_{\epsilon}}$ from $\mathbb{R}_{>0}$ to $\mathbb{C}$ by
$$\widetilde{1_{\epsilon}} = 1_{(0,1]}\ast\psi_\epsilon.$$
\end{definition}
%%-/
noncomputable def Smooth1 (Ψ : ℝ → ℝ) (ε : ℝ) : ℝ → ℂ :=
  MellinConvolution (fun x => if x ≤ 1 then 1 else 0) (funCoe (DeltaSpike Ψ ε))


/-%%
In particular, we have the following two properties.
\begin{lemma}[Smooth1Properties_below]\label{Smooth1Properties_below}\lean{Smooth1Properties_below}\leanok
Fix $\epsilon>0$. There is an absolute constant $c>0$ so that:
If $x\leq (1-c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 1.$$
\end{lemma}
%%-/
lemma Smooth1Properties_below {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2) (ε : ℝ)
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) : ∃ (c : ℝ), 0 < c ∧ ∀ (x : ℝ), x ≤ 1 - c * ε →
      Smooth1 Ψ ε x = 1 := by
  sorry
/-%%
\begin{proof}
\uses{Smooth1, MellinConvolution}
This is a straightforward calculation, using the fact that $\psi_\epsilon$ is supported in $[1/2^\epsilon,2^\epsilon]$.
\end{proof}
%%-/

/-%%
\begin{lemma}[Smooth1Properties_above]\label{Smooth1Properties_above}\lean{Smooth1Properties_above}\leanok
Fix $\epsilon>0$. There is an absolute constant $c>0$ so that:
if $x\geq (1+c\epsilon)$, then
$$\widetilde{1_{\epsilon}}(x) = 0.$$
\end{lemma}
%%-/
lemma Smooth1Properties_above {Ψ : ℝ → ℝ} (diffΨ : ContDiff ℝ 1 Ψ) (suppΨ : Ψ.support ⊆ Set.Icc (1 / 2) 2) (ε : ℝ)
    (mass_one : ∫ x in Set.Ici 0, Ψ x / x = 1) : ∃ (c : ℝ), 0 < c ∧ ∀ (x : ℝ), x ≥ 1 + c * ε →
      Smooth1 Ψ ε x = 0 := by
  sorry
/-%%
\begin{proof}
\uses{Smooth1, MellinConvolution}
This is a straightforward calculation, using the fact that $\psi_\epsilon$ is supported in $[1/2^\epsilon,2^\epsilon]$.
\end{proof}
%%-/

/-%%
Combining the above, we have the following Main Lemma of this section on the Mellin transform of $\widetilde{1_{\epsilon}}$.
\begin{lemma}\label{MellinOfSmooth1}\uses{Smooth1Properties_below, Smooth1Properties_above, MellinConvolutionTransform, MellinOfDeltaSpikeAt1, MellinOfPsi}
Fix  $\epsilon>0$. Then the Mellin transform of $\widetilde{1_{\epsilon}}$ is
$$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = \frac{1}{s}\left(\mathcal{M}(\psi)\left(\epsilon s\right)\right).$$

For any $s$, we have the bound
$$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = O\left(\frac{1}{\epsilon|s|^2}\right).$$

At $s=1$, we have
$$\mathcal{M}(\widetilde{1_{\epsilon}})(1) = (1+O(\epsilon)).$$
\end{lemma}
%%-/
