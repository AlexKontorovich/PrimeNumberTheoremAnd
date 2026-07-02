import Architect
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log

noncomputable section

@[blueprint
  "kadiri-thm-3-1-q1-I"
  (title := "Truncated contour integral $I(T)$ on $\\sigma = 1 + a$")
  (statement := /-- Kadiri's $I(T)$ from \cite[p.~12]{Kadiri2005}: the truncated contour
  integral
  $$ I(T) \;:=\; \frac{1}{2\pi i} \int_{1+a-iT}^{1+a+iT}
              \!\!\!\! \left(-\frac{\zeta'}{\zeta}\right)\!(s)\, \Phi(-s)\, ds, $$
  where $\Phi(s) := \int_0^\infty \varphi(y) e^{-sy}\, dy$ is the Laplace transform of
  $\varphi$. The $T \to \infty$ limit of $I(T)$ is the Mellin-contour identity of
  \ref{kadiri-thm-3-1-q1-eq-11}, and its rectangle decomposition is equation~(12) of
  \cite{Kadiri2005} (\ref{kadiri-thm-3-1-q1-eq-12}). -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
          riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
        Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I))

end

end Kadiri
