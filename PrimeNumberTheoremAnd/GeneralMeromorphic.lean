import Architect
import Mathlib.Analysis.Meromorphic.Basic
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

open Complex BigOperators

open scoped Interval

/-- A function is `MeromorphicOnRectangle` if it's holomorphic off of a
  finite set of `poles`, none of which is on the boundary of the rectangle
  (so the function is continuous there). -/
@[blueprint (statement := /--
  A function $f$ is Meromorphic on a rectangle with corners $z$ and $w$
  if it is holomorphic off a (finite) set of poles, none of which are on
  the boundary of the rectangle.
  -/)]
class MeromorphicOnRectangle (f : ℂ → ℂ) (poles : Finset ℂ) (z w : ℂ) : Prop where
  holomorphicOn : HolomorphicOn f ((Rectangle z w) ∩ polesᶜ)
  hasPoleAt : ∀ p ∈ poles, MeromorphicAt f p
  continuousOn : ContinuousOn f (RectangleBorder z w)

-- @[blueprint
--   (title := "Theorem about RectangleIntegralEqSumOfRectangles")
--   (statement := /--
--   If $f$ is meromorphic on a rectangle with corners $z$ and $w$,
--   then the rectangle integral of $f$ is equal to the sum of
--   sufficiently small rectangle integrals around each pole.
--   -/)]
-- theorem RectangleIntegralEqSumOfRectangles
--     (f : ℂ → ℂ) (poles : Finset ℂ) (z w : ℂ) [MeromorphicOnRectangle f poles z w] :
--     ∀ᶠ c in 𝓝[>](0:ℝ), RectangleIntegral f z w =
--       ∑ p in poles, RectangleIntegral f (p-(c+c*I)) (p+c+c*I) := by
--   sorry_using [MeromorphicOnRectangle, RectangleIntegral]

blueprint_comment /--
A meromorphic function has a pole of finite order.
\begin{definition}\label{PoleOrder}
If $f$ has a pole at $z_0$, then there is an integer $n$ such that
$$
\lim_{z\to z_0} (z-z_0)^n f(z) = c \neq 0.
$$
\end{definition}
-/

blueprint_comment /--
If a meromorphic function $f$ has a pole at $z_0$, then the residue of
$f$ at $z_0$ is the coefficient of $1/(z-z_0)$ in the Laurent series of
$f$ around $z_0$.
\begin{definition}\label{Residue}
If $f$ has a pole of order $n$ at $z_0$, then
$$
Res_{z_0} f =
  \lim_{z\to z_0}\frac1{(n-1)!}
    (\partial/\partial z)^{n-1}[(z-z_0)^{n-1}f(z)].
$$
\end{definition}
-/

blueprint_comment /--
We can evaluate a small integral around a pole by taking the residue.
-/
-- @[blueprint
--   (statement := /--
--     If $f$ has a pole at $z_0$, then every small enough rectangle
--     integral around $z_0$ is equal to $2\pi i Res_{z_0} f$.
--   -/)]]
-- theorem ResidueTheoremOnRectangle
--     (f : ℂ → ℂ) (z₀ : ℂ) (h : MeromorphicAt f z₀) :
--     ∀ᶠ c in 𝓝[>](0:ℝ),
--     RectangleIntegral f (z-(c+c*I)) (z+c+c*I) = 2*π*I* Res f z₀ := by
--   /--
--   The key is being able to integrate $1/z$ around a rectangle
--   with corners, say, $-1-i$ and $1+i$. The bottom is:
--   $$
--   \int_{-1-i}^{1-i} \frac1z dz
--   =
--   \int_{-1}^1 \frac1{x-i} dx,
--   $$
--   and the top is the negative of:
--   $$
--   \int_{-1+i}^{1+i} \frac1z dz
--   =
--   \int_{-1}^1 \frac1{x+i} dx.
--   $$
--   The two together add up to:
--   $$
--   \int_{-1}^1
--   \left(\frac1{x-i}-\frac1{x+i} \right)dx
--   =
--   2i\int_{-1}^1
--   \frac{1}{x^2+1}dx,
--   $$
--   which is the arctan at $1$ (namely $\pi/4$) minus that at $-1$.
--   In total, this contributes $\pi i$ to the integral.
--
--   The vertical sides are:
--   $$
--   \int_{1-i}^{1+i} \frac1z dz
--   =
--   i\int_{-1}^1 \frac1{1+iy} dy
--   $$
--   and the negative of
--   $$
--   \int_{-1-i}^{-1+i} \frac1z dz
--   =
--   i\int_{-1}^1 \frac1{-1+iy} dy.
--   $$
--   This difference comes out to:
--   $$
--   i\int_{-1}^1 \left(
--     \frac1{1+iy}-\frac1{-1+iy}\right) dy
--   =
--   i\int_{-1}^1 \left(\frac{-2}{-1-y^2}\right) dy,
--   $$
--   which contributes another factor of $\pi i$.
--   (Each of the vertical/horizontal sides contributes
--   half of the winding.)
--   -/
--   sorry_using [PoleOrder, Residue, RectangleIntegral, RectangleIntegralEqSumOfRectangles]

blueprint_comment /--
If a function $f$ is meromorphic at $z_0$ with a pole of order $n$, then
the residue at $z_0$ of the logarithmic derivative is $-n$ exactly.
-/
-- @[blueprint
--   (statement := /--
--   If $f$ has a pole of order $n$ at $z_0$, then
--   $$
--   Res_{z_0} \frac{f'}f = -n.
--   -/)]
-- theorem ResidueOfLogDerivative (f : ℂ → ℂ) (z₀ : ℂ) (h : MeromorphicAt f z₀) :
--     Res (f'/f) z₀ = -orderOfPole f z₀ := by
--   /--
--   We can write $f(z) = (z-z_0)^{-n} g(z)$, where $g$ is
--   holomorphic and $g(z_0) \neq 0$.
--   Then $f'(z) = -n(z-z_0)^{-n-1} g(z) +
--     (z-z_0)^{-n} g'(z)$, so
--   $$
--   \frac{f'(z)}{f(z)} =
--     \frac{-n}{z-z_0} + \frac{g'(z)}{g(z)}.
--   $$
--   The residue of the first term is $-n$, and the residue of
--   the second term is $0$.
--   -/
--   sorry_using [Residue, PoleOrder]
