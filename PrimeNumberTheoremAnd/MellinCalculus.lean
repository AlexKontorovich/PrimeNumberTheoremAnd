import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

open Complex Topology Filter

/-%%
In this section, we define the Mellin transform (already in Mathlib, thanks to David Loeffler), prove its inversion formula, and
derive a number of important properties of some special functions and bumpfunctions.

\begin{definition}\label{MellinTransform}
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of $f$ to be the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$
\end{definition}

[Note: My preferred way to think about this is that we are integrating over the multiplicative group $\mathbb{R}_{>0}$, multiplying by a (not necessarily unitary!) character $|\cdot|^s$, and integrating with respect to the invariant Haar measure $dx/x$. This is very useful in the kinds of calculations carried out below. But may be more difficult to formalize as things now stand. So we
might have clunkier calculations, which ``magically'' turn out just right - of course they're explained by the aforementioned structure...]

%%-/

/-%%
It is very convenient to define integrals along vertical lines in the complex plane, as follows.
\begin{definition}\label{VerticalIntegral}\leanok
Let $f$ be a function from $\mathbb{C}$ to $\mathbb{C}$, and let $\sigma$ be a real number. Then we define
$$\int_{(\sigma)}f(s)ds = \int_{\sigma-i\infty}^{\sigma+i\infty}f(s)ds.$$
\end{definition}
[Note: Better to define $\int_{(\sigma)}$ as $\frac1{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}$??
There's a factor of $2\pi i$ in such contour integrals...]
%%-/
noncomputable def VerticalIntegral (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  I • ∫ t : ℝ, f (σ + t * I)

/-%%
We first prove the following ``Perron-type'' formula, see Lemma \ref{PerronFormula} below.
This requires some preparatory material.
%%-/

/-%%
\begin{lemma}\label{HolomorphicOn_of_Perron_function}\lean{HolomorphicOn_of_Perron_function}
Let $x>0$. Then the function $f(s) = x^s/(s(s+1))$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
\end{lemma}
%%-/
lemma HolomorphicOn_of_Perron_function {x : ℝ} (xpos : 0 < x) :
    HolomorphicOn (fun s => x ^ s / (s * (s + 1))) {s | 0 < s.re} := by
  sorry

/-%%
\begin{lemma}\label{RectangleIntegral_eq_zero}\lean{RectangleIntegral_eq_zero}
\uses{RectangleIntegral}
Let $\sigma,\sigma',T>0$, and let $f$ be a holomorphic function on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$. Then
the rectanglet integral
$$\int_{\sigma-iT}^{\sigma'+iT}f(s)ds = 0.$$
\end{lemma}
%%-/
lemma RectangleIntegral_eq_zero {σ σ' T : ℝ} (σ_pos : 0 < σ) (σ'_pos : 0 < σ') (T_pos : 0 < T)
    {f : ℂ → ℂ} (fHolo : HolomorphicOn f {s | 0 < s.re}) :
    RectangleIntegral f (σ - I * T) (σ' + I * T) = 0 := by
  sorry -- apply HolomorphicOn.vanishesOnRectangle in PR #9598

/-%%
\begin{lemma}\label{RectangleIntegral_tendsTo_VerticalIntegral}\lean{RectangleIntegral_tendsTo_VerticalIntegral}
\uses{RectangleIntegral}
Let $\sigma,\sigma'>0$, and let $f$ be a holomorphic function on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$. Then
the limit of rectangle integrals
$$\lim_{T\to\infty}\int_{\sigma-iT}^{\sigma'+iT}f(s)ds = \int_{(\sigma')}f(s)ds - \int_{(\sigma)}f(s)ds
.$$
*** Needs more conditions on $f$ ***
\end{lemma}
%%-/
lemma RectangleIntegral_tendsTo_VerticalIntegral {σ σ' : ℝ} (σ_pos : 0 < σ) (σ'_pos : 0 < σ')
    {f : ℂ → ℂ} (fHolo : HolomorphicOn f {s | 0 < s.re}) :
    -- needs more hypotheses
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ - I * T) (σ' + I * T)) atTop
      (𝓝 (VerticalIntegral f σ' - VerticalIntegral f σ)) := by
  sorry

/-%%
\begin{lemma}\label{PerronIntegralPosAux}\lean{PerronIntegralPosAux}
The integral
$$\int_\R\frac{1}{|(1+t)(1+t+1)|}dt$$
is positive (and hence convergent - since a divergent integral is zero in Lean, by definition).
\end{lemma}
%%-/
lemma PerronIntegralPosAux : 0 < ∫ (t : ℝ), 1 / |(1 + t) * (1 + t + 1)| := by
  sorry

/-%%
\begin{lemma}\label{VertIntPerronBound}\lean{VertIntPerronBound}
\uses{VerticalIntegral}
Let $x>0$, $\sigma>1$, and $x<1$. Then
$$\left|
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1+t)(1+t+1)|}dt.$$
\end{lemma}
%%-/
lemma VertIntPerronBound {x : ℝ} (xpos : 0 < x) (x_le_one : x < 1) {σ : ℝ} (σ_gt_one : 1 < σ) :
    Complex.abs (VerticalIntegral f σ) ≤ x ^ σ * ∫ (t : ℝ), 1 / |(1 + t) * (1 + t + 1)| := by
  sorry

/-%%
\begin{lemma}\label{limitOfConstant}\lean{limitOfConstant}
Let $a:\R\to\C$ be a function, and let $\sigma>0$ be a real number. Suppose that, for all
$\sigma, \sigma'>0$, we have $a(\sigma')=a(\sigma)$, and that
$\lim_{\sigma\to\infty}a(\sigma)=0$. Then $a(\sigma)=0$.
\end{lemma}
%%-/
lemma limitOfConstant {a : ℝ → ℂ} {σ : ℝ} (σpos : 0 < σ) (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (σ'pos : 0 < σ')
    (σ''pos : 0 < σ''), a σ' = a σ'') (ha' : Tendsto (fun σ' => a σ') atTop (𝓝 0)) : a σ = 0 := by
  sorry
/-%%
We are ready for the Perron formula, which breaks into two cases, the first being:
\begin{lemma}\label{PerronFormulaLtOne}\lean{VerticalIntegral_Perron_lt_one}
For $x>0$, $\sigma>0$, and $x<1$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =0.
$$
\end{lemma}
%%-/
lemma VerticalIntegral_Perron_lt_one {x : ℝ} (xpos : 0 < x) (x_lt_one : x < 1)
    {σ : ℝ} (σ_pos : 0 < σ) : VerticalIntegral (fun s ↦ x^s / (s * (s + 1))) σ = 0 := by
/-%%
\begin{proof}
\uses{HolomorphicOn_of_Perron_function, RectangleIntegral_eq_zero, PerronIntegralPosAux, VertIntPerronBound, limitOfConstant, RectangleIntegral_tendsTo_VerticalIntegral}
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
%%-/
  set f : ℂ → ℂ := (fun s ↦ x^s / (s * (s + 1)))
  have fHolo : HolomorphicOn f {s : ℂ | 0 < s.re} := HolomorphicOn_of_Perron_function xpos
--%% The rectangle integral of $f$ with corners $\sigma-iT$ and $\sigma+iT$ is zero.
  have rectInt : ∀ (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') (T : ℝ) (Tpos : 0 < T),
    RectangleIntegral f (σ' - I * T) (σ'' + I * T) = 0 :=
    fun σ' σ'' σ'pos σ''pos T Tpos ↦ RectangleIntegral_eq_zero σ'pos σ''pos Tpos fHolo
--%% The limit of this rectangle integral as $T\to\infty$ is $\int_{(\sigma')}-\int_{(\sigma)}$.
  have rectIntLimit : ∀ (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ''),
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ' - I * T) (σ'' + I * T))
      atTop (𝓝 (VerticalIntegral f σ'' - VerticalIntegral f σ')) := fun σ' σ'' σ'pos σ''pos ↦
      RectangleIntegral_tendsTo_VerticalIntegral σ'pos σ''pos fHolo
--%% Therefore, $\int_{(\sigma')}=\int_{(\sigma)}$.
  have contourPull : ∀ (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ''),
    VerticalIntegral f σ' = VerticalIntegral f σ''
  · intro σ' σ'' σ'pos σ''pos
    have := rectIntLimit σ' σ'' σ'pos σ''pos
    sorry
--%% But we also have the bound $\int_{(\sigma')} \leq x^{\sigma'} * C$, where
--%% $C=\int_\R\frac{1}{|(1+t)(1+t+1)|}dt$.
  have VertIntBound : ∃ C > 0, ∀ σ' > 1, Complex.abs (VerticalIntegral f σ') ≤ x^σ' * C
  · let C := ∫ (t : ℝ), 1 / |(1 + t) * (1 + t + 1)|
    exact ⟨C, PerronIntegralPosAux, fun σ' σ'_gt_one ↦ VertIntPerronBound xpos x_lt_one σ'_gt_one⟩
--%% Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$.
  have VertIntTendsto : Tendsto (fun (σ' : ℝ) ↦ VerticalIntegral f σ') atTop (𝓝 0)
  · have : ‖x‖ < 1 := sorry
    have := tendsto_pow_atTop_nhds_0_of_norm_lt_1 this
    sorry
--%% So pulling contours gives $\int_{(\sigma)}=0$.
  exact limitOfConstant (a := fun σ' ↦ VerticalIntegral f σ') σ_pos contourPull VertIntTendsto
--%%\end{proof}


/-%%
The second lemma is the case $x>1$.
\begin{lemma}\label{PerronFormulaGtOne}\lean{VerticalIntegral_Perron_gt_one}
For $x>1$ and $\sigma>0$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =1-1/x.
$$
\end{lemma}
%%-/
lemma VerticalIntegral_Perron_gt_one {x : ℝ} (x_gt_one : 1 < x) {σ : ℝ} (σ_pos : 0 < σ) :
    VerticalIntegral (fun s ↦ x^s / (s * (s + 1))) σ = 1 - 1 / x := by
  sorry


/-%%
The two together give the Perron formula.
\begin{lemma}\label{PerronFormula}
\uses{PerronFormulaLtOne, PerronFormulaGtOne}
For $x>0$ and $\sigma>0$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds = \begin{cases}
1-\frac1x & \text{ if }x>1\\
0 & \text{ if } x<1
\end{cases}.
$$
\end{lemma}
%%-/

/-%%
\begin{theorem}\label{MellinInversion}
Let $f$ be a nice function from $\mathbb{R}_{>0}$ to $\mathbb{C}$, and let $\sigma$ be sufficiently large. Then
$$f(x) = \frac{1}{2\pi i}\int_{(\sigma)}\mathcal{M}(f)(s)x^{-s}ds.$$
\end{theorem}

[Note: How ``nice''? Schwartz (on $(0,\infty)$) is certainly enough. As we formalize this, we can add whatever conditions are necessary for the proof to go through.]
%%-/
/-%%
\begin{proof}
\uses{PerronFormula}
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

/-%%
Let $\psi$ be a bumpfunction.
\begin{theorem}\label{SmoothExistence}
There exists a smooth (once differentiable would be enough), nonnegative ``bumpfunction'' $\psi$,
 supported in $[1/2,2]$ with total mass one:
$$
\int_0^\infty \psi(x)\frac{dx}{x} = 1.
$$
\end{theorem}
\begin{proof}
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
\begin{lemma}\label{MellinOfSmooth1}\uses{Smooth1Properties, MellinConvolutionTransform, MellinOfDeltaSpikeAt1}
Fix  $\epsilon>0$. Then the Mellin transform of $\widetilde{1_{\epsilon}}$ is
$$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = \frac{1}{s}\left(\mathcal{M}(\psi)\left(\epsilon s\right)\right).$$

For any $s$, we have the bound
$$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = O\left(\frac{1}{\epsilon|s|^2}\right).$$

At $s=1$, we have
$$\mathcal{M}(\widetilde{1_{\epsilon}})(1) = (1+O(\epsilon)).$$
\end{lemma}
%%-/
