import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Meromorphic
import EulerProducts.LSeries


open Complex BigOperators Finset Nat Classical Real Topology Filter Set MeasureTheory

open scoped Interval

/-%%

In this section, we develop residue calculus on rectangles for \emph{simple} poles.

\begin{definition}\label{Rectangle}\lean{Rectangle}\leanok
A Rectangle has corners $z$ and $w \in \C$.
\end{definition}
%%-/
/-- A `Rectangle` has corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

lemma Rectangle.symm {z w : ℂ} : Rectangle z w = Rectangle w z := by
  dsimp [Rectangle]
  rw [Set.uIcc_comm z.re w.re, Set.uIcc_comm z.im w.im]

/-%%
\begin{definition}[RectangleIntegral]\label{RectangleIntegral}\lean{RectangleIntegral}\leanok
A RectangleIntegral of a function $f$ is one over a rectangle determined by $z$ and $w$ in $\C$.
We will sometimes denote it by $\int_{z}^{w} f$. (There is also a primed version, which is $1/(2\pi i)$ times the original.)
\end{definition}
%%-/
/-- A `RectangleIntegral` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

noncomputable abbrev RectangleIntegral' (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    (1/(2 * π * I)) * RectangleIntegral f z w

/-%%
The border of a rectangle is the union of its four sides.
\begin{definition}[RectangleBorder]\label{RectangleBorder}\lean{RectangleBorder}\leanok
A Rectangle's border, given corners $z$ and $w$ is the union of the four sides.
\end{definition}
%%-/
/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

/-%%
An UpperUIntegral is the integral of a function over a |\_| shape.
\begin{definition}\label{UpperUIntegral}\lean{UpperUIntegral}\leanok
An UpperUIntegral of a function $f$ comes from $\sigma+i\infty$ down to $\sigma+iT$, over to $\sigma'+iT$, and back up to $\sigma'+i\infty$.
\end{definition}
%%-/
noncomputable def UpperUIntegral (f : ℂ → ℂ) (σ σ' T : ℝ) : ℂ :=
    ((∫ x : ℝ in σ..σ', f (x + T * I))
     + I • (∫ y : ℝ in Ici T, f (σ' + y * I)) - I • ∫ y : ℝ in Ici T, f (σ + y * I))

/-%%
A LowerUIntegral is the integral of a function over a |-| shape.
\begin{definition}[LowerUIntegral]\label{LowerUIntegral}\lean{LowerUIntegral}\leanok
A LowerUIntegral of a function $f$ comes from $\sigma-i\infty$ up to $\sigma-iT$, over to $\sigma'-iT$, and back down to $\sigma'-i\infty$.
\end{definition}
%%-/
noncomputable def LowerUIntegral (f : ℂ → ℂ) (σ σ' T : ℝ) : ℂ :=
    ((∫ x : ℝ in σ..σ', f (x - T * I))
     - I • (∫ y : ℝ in Iic (-T), f (σ' - y * I)) + I • ∫ y : ℝ in Iic (-T), f (σ - y * I))


/-%%
It is very convenient to define integrals along vertical lines in the complex plane, as follows.
\begin{definition}[VerticalIntegral]\label{VerticalIntegral}\leanok
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
\begin{lemma}[DiffVertRect_eq_UpperLowerUs]\label{DiffVertRect_eq_UpperLowerUs}\lean{DiffVertRect_eq_UpperLowerUs}\leanok
The difference of two vertical integrals and a rectangle is the difference of an upper and a lower U integrals.
\end{lemma}
%%-/
lemma DiffVertRect_eq_UpperLowerUs {f : ℂ → ℂ} {σ σ' T : ℝ}
    (f_int_σ : Integrable (fun (t : ℝ) ↦ f (σ + t * I)))
    (f_int_σ' : Integrable (fun (t : ℝ) ↦ f (σ' + t * I))) :
  (VerticalIntegral f σ') - (VerticalIntegral f σ) - (RectangleIntegral f (σ - I * T) (σ' + I * T)) = (UpperUIntegral f σ σ' T) - (LowerUIntegral f σ σ' T) := by
  sorry
/-%%
\begin{proof}\uses{UpperUIntegral, LowerUIntegral}
Follows directly from the definitions.
\end{proof}
%%-/

/-- A function is `HolomorphicOn` a set if it is complex differentiable on that set. -/
abbrev HolomorphicOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (s : Set ℂ) :
    Prop := DifferentiableOn ℂ f s


/-%%
\begin{theorem}[existsDifferentiableOn_of_bddAbove]\label{existsDifferentiableOn_of_bddAbove}\lean{existsDifferentiableOn_of_bddAbove}\leanok
If $f$ is differentiable on a set $s$ except at $c\in s$, and $f$ is bounded above on $s\setminus\{c\}$, then there exists a differentiable function $g$ on $s$ such that $f$ and $g$ agree on $s\setminus\{c\}$.
\end{theorem}
%%-/
theorem existsDifferentiableOn_of_bddAbove {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E), HolomorphicOn g s ∧ (Set.EqOn f g (s \ {c})) := by
  refine ⟨(Function.update f c (limUnder (nhdsWithin c {c}ᶜ) f)),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb, ?_⟩
  intro z hz
  by_cases h : z = c
  · exfalso
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hz
    exact hz.2 h
  · simp [h]
/-%%
\begin{proof}\leanok
This is the Reimann Removable Singularity Theorem, slightly rephrased from what's in Mathlib. (We don't care what the function $g$ is, just that it's holomorphic.)
\end{proof}
%%-/

/-%%
\begin{theorem}[HolomorphicOn.vanishesOnRectangle]\label{HolomorphicOn.vanishesOnRectangle}\lean{HolomorphicOn.vanishesOnRectangle}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$, then the integral of $f$ over the rectangle with corners $z$ and $w$ is $0$.
\end{theorem}
%%-/
theorem HolomorphicOn.vanishesOnRectangle {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (f_holo : HolomorphicOn f U) (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 := by sorry -- mathlib4\#9598
/-%%
\begin{proof}\leanok
This is in a Mathlib PR.
\end{proof}
%%-/

/--
Given `x₀ a x₁ : ℝ`, `x₀ < a < x₁` and `y₀ y₁ : ℝ` and a function `f : ℂ → ℂ` so that
both `(t : ℝ) ↦ f(t + y₀ * I)` and `(t : ℝ) ↦ f(t + y₁ * I)` are integrable over both
`t ∈ Icc x₀ a` and `t ∈ Icc a x₁`, we have that
`RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I)` is the sum of
`RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I)` and
`RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I)`.
-/
lemma RectangleIntegralHSplit {f : ℂ → ℂ} {x₀ a x₁ y₀ y₁ : ℝ}
    (x₀_lt_a : x₀ < a) (a_lt_x₁ : a < x₁)
    (f_int_x₀_a : IntegrableOn (fun (t : ℝ) ↦ f (t + y₀ * I)) (Icc x₀ a))
    (f_int_a_x₁ : IntegrableOn (fun (t : ℝ) ↦ f (t + y₁ * I)) (Icc a x₁)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  sorry

/--
A rectangle integral with corners `a` and `d` can be subdivided into nine smaller rectangles.
-/
lemma RectangleSubdivide {a b c d : ℂ} (aRe_lt_bRe : a.re < b.re) (bRe_lt_cRe : b.re < c.re)
    (cRe_lt_dRe : c.re < d.re) (aIm_lt_bIm : a.im < b.im) (bIm_lt_cIm : b.im < c.im)
    (cIm_lt_dIm : c.im < d.im) (f : ℂ → ℂ) (fcont : ContinuousOn f (Rectangle a d)) :
    RectangleIntegral f a d =
      RectangleIntegral f a b +
      RectangleIntegral f (b.re + I * a.im) (c.re + I * b.im) +
      RectangleIntegral f (c.re + I * a.im) (d.re + I * b.im) +
      RectangleIntegral f (a.re + I * b.im) (b.re + I * c.im) +
      RectangleIntegral f b c +
      RectangleIntegral f (c.re + I * b.im) (d.re + I * c.im) +
      RectangleIntegral f (a.re + I * c.im) (b.re + I * d.im) +
      RectangleIntegral f (b.re + I * c.im) (c.re + I * d.im) +
      RectangleIntegral f c d := by
  dsimp [RectangleIntegral]

  sorry

/-%%
The next lemma allows to zoom a big rectangle down to a small square, centered at a pole.

\begin{lemma}[RectanglePullToNhdOfPole]\label{RectanglePullToNhdOfPole}\lean{RectanglePullToNhdOfPole}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$ except at a point $p$, then the integral of $f$
over the rectangle with corners $z$ and $w$ is the same as the integral of $f$ over a small square
centered at $p$.
\end{lemma}
%%-/
lemma RectanglePullToNhdOfPole {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    (zIm_lt_wIm : z.im < w.im) (pInRectInterior : Rectangle z w ∈ nhds p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, RectangleIntegral f z w =
      RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
--%% \begin{proof}\uses{HolomorphicOn.vanishesOnRectangle}
  rw [mem_nhds_iff] at pInRectInterior
  obtain ⟨nhdP, nhdSubRect, nhdOpen, pInNhd⟩ := pInRectInterior
  have : ∃ c₁ > 0, Metric.ball p c₁ ⊆ nhdP := by
    simp_all
    refine Metric.mem_nhds_iff.mp ?_
    exact IsOpen.mem_nhds nhdOpen pInNhd
--%% Let $c_1$ be small enough that a ball of radius $c_1$ about $p$ is contained in the rectangle.
  obtain ⟨c₁, c₁Pos, c₁SubNhd⟩ := this
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (half_pos c₁Pos)]
  set c₀ := c₁ / 2
--%% Let $c < c_1/2$.
  intro c cPos
  simp_all only [gt_iff_lt, Set.mem_Ioo]
--%% Let $R_1$ be the rectangle with corners $z$ and $-c-i c + p$.
  let R1 := Rectangle z (-c - I * c + p)
  let RI1 := RectangleIntegral f z (-c - I * c + p)
  have fHolo1 : HolomorphicOn f R1 := by
    sorry
--%% Let $R_2$ be the rectangle with corners $-c + \Re p + i \Im z$ and $c - i c + p$.
  let R2 := Rectangle (-c + p.re + I * z.im) (c - I * c + p)
  let RI2 := RectangleIntegral f (-c + p.re + I * z.im) (c - I * c + p)
  have fHolo2 : HolomorphicOn f R2 := by
    sorry
--%% Let $R_3$ be the rectangle with corners $c + \Re p + i \Im z$ and $\Re w + \Im p - i c$.
  sorry
/-%%
Chop the big rectangle with two vertical cuts and two horizontal cuts into nine smaller rectangles,
the middle one being the desired square. The integral over each of the eight outer rectangles
vanishes, since $f$ is holomorphic there. (The constant $c$ being ``small enough'' here just means
that the inner square is strictly contained in the big rectangle.)
\end{proof}
%%-/


/-%%
\begin{lemma}[ResidueTheoremAtOrigin]\label{ResidueTheoremAtOrigin}
\lean{ResidueTheoremAtOrigin}\leanok
The rectangle (square) integral of $f(s) = 1/s$ with corners $-1-i$ and $1+i$ is equal to $2\pi i$.
\end{lemma}
%%-/
lemma ResidueTheoremAtOrigin :
    RectangleIntegral' (fun s ↦ 1 / s) (-1 - I) (1 + I) = 1 := by
  sorry
/-%%
\begin{proof}
The bottom is:
$$
\frac1{2\pi i}
\int_{-1-i}^{1-i} \frac1z dz
=
\frac1{2\pi i}
\int_{-1}^1 \frac1{x-i} dx,
$$
and the top is the negative of:
$$
\frac1{2\pi i}
\int_{-1+i}^{1+i} \frac1z dz
=
\frac1{2\pi i}
\int_{-1}^1 \frac1{x+i} dx.
$$
The two together add up to:
$$
\frac1{2\pi i}
\int_{-1}^1
\left(\frac1{x-i}-\frac1{x+i} \right)dx
=
\frac1{\pi}
\int_{-1}^1
\frac{1}{x^2+1}dx,
$$
which is the arctan at $1$ (namely $\pi/4$) minus that at $-1$. In total, this contributes $1/2$ to the integral.

The vertical sides are:
$$
\frac1{2\pi i}
\int_{1-i}^{1+i} \frac1z dz
=
\frac1{2\pi}
\int_{-1}^1 \frac1{1+iy} dy
$$
and the negative of
$$
\frac1{2\pi i}
\int_{-1-i}^{-1+i} \frac1z dz
=
\frac1{2\pi}
\int_{-1}^1 \frac1{-1+iy} dy.
$$
This difference comes out to:
$$
\frac1{2\pi}
\int_{-1}^1 \left(\frac1{1+iy}-\frac1{-1+iy}\right) dy
=
\frac1{2\pi}
\int_{-1}^1 \left(\frac{-2}{-1-y^2}\right) dy,
$$
which contributes another factor of $1/2$. (Fun! Each of the vertical/horizontal sides contributes half of the winding.)
\end{proof}
%%-/

/-%%
\begin{lemma}[ResidueTheoremOnRectangleWithSimplePole]\label{ResidueTheoremOnRectangleWithSimplePole}
\lean{ResidueTheoremOnRectangleWithSimplePole}\leanok
Suppose that $f$ is a holomorphic function on a rectangle, except for a simple pole
at $p$. By the latter, we mean that there is a function $g$ holomorphic on the rectangle such that, $f = g + A/(s-p)$ for some $A\in\C$. Then the integral of $f$ over the
rectangle is $A$.
\end{lemma}
%%-/
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (pInRectInterior : Rectangle z w ∈ nhds p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) (g)
      (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  sorry
/-%%
\begin{proof}\uses{ResidueTheoremAtOrigin, RectanglePullToNhdOfPole, HolomorphicOn.vanishesOnRectangle}
Replace $f$ with $g + A/(s-p)$ in the integral.
The integral of $g$ vanishes by Lemma \ref{HolomorphicOn.vanishesOnRectangle}.
 To evaluate the integral of $1/(s-p)$,
pull everything to a square about the origin using Lemma \ref{RectanglePullToNhdOfPole},
and rescale by $c$;
what remains is handled by Lemma \ref{ResidueTheoremAtOrigin}.
\end{proof}
%%-/
