import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.Analytic.Meromorphic
import PrimeNumberTheoremAnd.EulerProducts.LSeries


open Complex BigOperators Finset Nat Classical Real

open scoped ArithmeticFunction Interval

/-%%

In this file, we develop residue calculus on rectangles.

\begin{definition}\label{Rectangle}\lean{Rectangle}\leanok
A Rectangle has corners $z$ and $w \in \C$.
\end{definition}
%%-/
/-- A `Rectangle` has corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-%%
\begin{definition}\label{RectangleIntegral}\lean{RectangleIntegral}\leanok
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

/-- A function is `HolomorphicOn` a set if it is complex differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → ℂ) (s : Set ℂ) : Prop := DifferentiableOn ℂ f s

/-%%
The border of a rectangle is the union of its four sides.
\begin{definition}\label{RectangleBorder}\lean{RectangleBorder}\leanok
A Rectangle's border, given corners $z$ and $w$ is the union of the four sides.
\end{definition}
%%-/
/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]


/-%%
\begin{definition}\label{MeromorphicOnRectangle}\lean{MeromorphicOnRectangle}\leanok
\uses{Rectangle, RectangleBorder, RectangleIntegral}
A function $f$ is Meromorphic on a rectangle with corners $z$ and $w$ if it is holomorphic off a
(finite) set of poles, none of which are on the boundary of the rectangle.
[Note: Might be overkill, can just work explicitly with the functions that arise. Of course would be nice to have the general theory as well...]
\end{definition}
%%-/
/-- A function is `MeromorphicOnRectangle` if it's holomorphic off of a finite set of `poles`,
  none of which is on the boundary of the rectangle (so the function is continuous there). -/
class MeromorphicOnRectangle (f : ℂ → ℂ) (poles : Finset ℂ) (z w : ℂ) : Prop where
  holomorphicOn : HolomorphicOn f ((Rectangle z w) ∩ polesᶜ)
  hasPoleAt : ∀ p ∈ poles, MeromorphicAt f p
  continuousOn : ContinuousOn f (RectangleBorder z w)

/-%%
\begin{theorem}\label{RectangleIntegralEqSumOfRectangles}%\lean{RectangleIntegralEqSumOfRectangles}
If $f$ is meromorphic on a rectangle with corners $z$ and $w$, then the rectangle integral of $f$
is equal to the sum of sufficiently small rectangle integrals around each pole.
\end{theorem}
%%-/
--theorem RectangleIntegralEqSumOfRectangles (f : ℂ → ℂ) (poles : Finset ℂ) (z w : ℂ) [MeromorphicOnRectangle f poles z w] :
    -- ∀ᶠ c in 𝓝[>](0:ℝ),
    -- RectangleIntegral f z w = ∑ p in poles, RectangleIntegral f (p-(c+c*I)) (p+c+c*I) := sorry

/-%%
\begin{proof}
\uses{MeromorphicOnRectangle, RectangleIntegral}
Rectangles tile rectangles, zoom in.
\end{proof}
%%-/
/-%%
A meromorphic function has a pole of finite order.
\begin{definition}\label{PoleOrder}
If $f$ has a pole at $z_0$, then there is an integer $n$ such that
$$
\lim_{z\to z_0} (z-z_0)^n f(z) = c \neq 0.
$$
\end{definition}

[Note: There is a recent PR by David Loeffler dealing with orders of poles.]
%%-/


/-%%
If a meromorphic function $f$ has a pole at $z_0$, then the residue of $f$ at $z_0$ is the coefficient of $1/(z-z_0)$ in the Laurent series of $f$ around $z_0$.
\begin{definition}\label{Residue}
If $f$ has a pole of order $n$ at $z_0$, then
$$
Res_{z_0} f = \lim_{z\to z_0}\frac1{(n-1)!}(\partial/\partial z)^{n-1}[(z-z_0)^{n-1}f(z)].
$$
\end{definition}
%%-/

/-%%
We can evaluate a small integral around a pole by taking the residue.
\begin{theorem}\label{ResidueTheoremOnRectangle}\lean{ResidueTheoremOnRectangle}
If $f$ has a pole at $z_0$, then every small enough rectangle integral around $z_0$ is equal to $2\pi i Res_{z_0} f$.
\end{theorem}
%%-/
-- theorem ResidueTheoremOnRectangle (f : ℂ → ℂ) (z₀ : ℂ) (h : MeromorphicAt f z₀) :
--     ∀ᶠ c in 𝓝[>](0:ℝ),
--     RectangleIntegral f (z-(c+c*I)) (z+c+c*I) = 2*π*I* Res f z₀ := sorry

/-%%
\begin{proof}
\uses{PoleOrder, Residue, RectangleIntegral, RectangleIntegralEqSumOfRectangles}
Near $z_0$, $f$ looks like $(z-z_0)^{-n} g(z)$, where $g$ is holomorphic and $g(z_0) \neq 0$.
Expand $g$ in a power series around $z_0$, so that
$$
f(z) = a_{-n}(z-z_0)^{-n} + \cdots + a_{-1}(z-z_0)^{-1} + \cdots.
$$
We can integrate term by term.

The key is being able to integrate $1/z$ around a rectangle with corners, say, $-1-i$ and $1+i$. The bottom is:
$$
\int_{-1-i}^{1-i} \frac1z dz
=
\int_{-1}^1 \frac1{x-i} dx,
$$
and the top is the negative of:
$$
\int_{-1+i}^{1+i} \frac1z dz
=
\int_{-1}^1 \frac1{x+i} dx.
$$
The two together add up to:
$$
\int_{-1}^1
\left(\frac1{x-i}-\frac1{x+i} \right)dx
=
2i\int_{-1}^1
\frac{1}{x^2+1}dx,
$$
which is the arctan at $1$ (namely $\pi/4$) minus that at $-1$. In total, this contributes $\pi i$ to the integral.

The vertical sides are:
$$
\int_{1-i}^{1+i} \frac1z dz
=
i\int_{-1}^1 \frac1{1+iy} dy
$$
and the negative of
$$
\int_{-1-i}^{-1+i} \frac1z dz
=
i\int_{-1}^1 \frac1{-1+iy} dy.
$$
This difference comes out to:
$$
i\int_{-1}^1 \left(\frac1{1+iy}-\frac1{-1+iy}\right) dy
=
i\int_{-1}^1 \left(\frac{-2}{-1-y^2}\right) dy,
$$
which contributes another factor of $\pi i$. (Fun! Each of the vertical/horizontal sides contributes half of the winding.)
\end{proof}

[Note: Of course the standard thing is to do this with circles, where the integral comes out directly from the parametrization. But discs don't tile
discs! Thus the standard approach is with annoying keyhole contours, etc; this is a total mess to formalize! Instead, we observe that rectangles do tile rectangles, so we can just do the
whole theory with rectangles. The cost is the extra difficulty of this little calculation.]

[Note: We only ever need simple poles for PNT, so would be enough to develop those...]
%%-/

/-%%
If a function $f$ is meromorphic at $z_0$ with a pole of order $n$, then
the residue at $z_0$ of the logarithmic derivative is $-n$ exactly.
\begin{theorem}\label{ResidueOfLogDerivative}\lean{ResidueOfLogDerivative}
If $f$ has a pole of order $n$ at $z_0$, then
$$
Res_{z_0} \frac{f'}f = -n.
$$
\end{theorem}
%%-/
-- theorem ResidueOfLogDerivative (f : ℂ → ℂ) (z₀ : ℂ) (h : MeromorphicAt f z₀) :
--     Res (f'/f) z₀ = -orderOfPole f z₀ := sorry

/-%%
\begin{proof}
\uses{Residue, PoleOrder}
We can write $f(z) = (z-z_0)^{-n} g(z)$, where $g$ is holomorphic and $g(z_0) \neq 0$.
Then $f'(z) = -n(z-z_0)^{-n-1} g(z) + (z-z_0)^{-n} g'(z)$, so
$$
\frac{f'(z)}{f(z)} = \frac{-n}{z-z_0} + \frac{g'(z)}{g(z)}.
$$
The residue of the first term is $-n$, and the residue of the second term is $0$.
\end{proof}
%%-/
