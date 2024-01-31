import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Topology Filter

open scoped Interval


/-%%
\begin{definition}\label{Rectangle}\lean{Rectangle}\leanok
A Rectangle has corners $z$ and $w \in \C$.
\end{definition}
%%-/
/-- A `Rectangle` has corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-%%
\begin{definition}\label{RectangleIntegral}\lean{RectangleIntegral}\leanok
A RectangleIntegral of a function $f$ is one over a rectangle determined by $z$ and $w$ in $\C$.
\end{definition}
%%-/
/-- A `RectangleIntegral` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

/-- A function is `HolomorphicOn` a set if it is complex differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → ℂ) (s : Set ℂ) : Prop := DifferentiableOn ℂ f s

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
The following is preparatory material used in the proof of the Perron formula, see Lemma \ref{PerronFormula}.
%%-/

/-%%
\begin{lemma}\label{HolomorphicOn_of_Perron_function}\lean{HolomorphicOn_of_Perron_function}\leanok
Let $x>0$. Then the function $f(s) = x^s/(s(s+1))$ is holomorphic on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$.
\end{lemma}
%%-/
lemma HolomorphicOn_of_Perron_function {x : ℝ} (xpos : 0 < x) :
    HolomorphicOn (fun s => x ^ s / (s * (s + 1))) {s | 0 < s.re} := by
  sorry
/-%%
\begin{proof}
Chain differentiabilities.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{RectangleIntegral_eq_zero}\lean{RectangleIntegral_eq_zero}\leanok
\uses{RectangleIntegral}
Let $\sigma,\sigma',T>0$, and let $f$ be a holomorphic function on the half-plane $\{s\in\mathbb{C}:\Re(s)>0\}$. Then
the rectangle integral
$$\int_{\sigma-iT}^{\sigma'+iT}f(s)ds = 0.$$
\end{lemma}
%%-/

lemma RectangleIntegral_eq_zero {σ σ' T : ℝ} (σ_pos : 0 < σ) (σ'_pos : 0 < σ') (T_pos : 0 < T)
    {f : ℂ → ℂ} (fHolo : HolomorphicOn f {s | 0 < s.re}) :
    RectangleIntegral f (σ - I * T) (σ' + I * T) = 0 := by
  sorry -- apply HolomorphicOn.vanishesOnRectangle in PR #9598

/-%%
\begin{lemma}\label{RectangleIntegral_tendsTo_VerticalIntegral}\lean{RectangleIntegral_tendsTo_VerticalIntegral}\leanok
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
\begin{lemma}\label{PerronIntegralPosAux}\lean{PerronIntegralPosAux}\leanok
The integral
$$\int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt$$
is positive (and hence convergent - since a divergent integral is zero in Lean, by definition).
\end{lemma}
%%-/
lemma PerronIntegralPosAux : 0 < ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| := by
  sorry
/-%%
\begin{proof}
Standard estimate.
\end{proof}
%%-/

/-%%
\begin{lemma}\label{VertIntPerronBound}\lean{VertIntPerronBound}\leanok
\uses{VerticalIntegral}
Let $x>0$, $\sigma>1$, and $x<1$. Then
$$\left|
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq x^\sigma \int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt.$$
\end{lemma}
%%-/

lemma VertIntPerronBound {x : ℝ} (xpos : 0 < x) (x_le_one : x < 1) {σ : ℝ} (σ_gt_one : 1 < σ) :
    Complex.abs (VerticalIntegral (fun s ↦ x^s / (s * (s + 1))) σ)
      ≤ x ^ σ * ∫ (t : ℝ), 1 / |Real.sqrt (1 + t^2) * Real.sqrt (2 + t^2)| := by
  sorry

/-%%
\begin{lemma}\label{limitOfConstant}\lean{limitOfConstant}\leanok
Let $a:\R\to\C$ be a function, and let $\sigma>0$ be a real number. Suppose that, for all
$\sigma, \sigma'>0$, we have $a(\sigma')=a(\sigma)$, and that
$\lim_{\sigma\to\infty}a(\sigma)=0$. Then $a(\sigma)=0$.
\end{lemma}
%%-/
lemma limitOfConstant {a : ℝ → ℂ} {σ : ℝ} (σpos : 0 < σ) (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (σ'pos : 0 < σ')
    (σ''pos : 0 < σ''), a σ' = a σ'') (ha' : Tendsto (fun σ' => a σ') atTop (𝓝 0)) : a σ = 0 := by
  sorry
/-%%
\begin{proof}
To show that $a(\sigma)=0$, we show that $a(\sigma)< \epsilon$ for all $\epsilon>0$. Let $\epsilon>0$.
The fact that $\lim_{\sigma\to\infty}a(\sigma)=0$ means that there exists $\sigma_0>0$ such that
$|a(\sigma)|<\epsilon$ for all $\sigma>\sigma_0$. Now let $\sigma>0$. Then $a(\sigma)=a(\sigma_0)$, and
so $|a(\sigma)|=|a(\sigma_0)|<\epsilon$, as required.
\end{proof}
%%-/
