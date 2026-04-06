import PrimeNumberTheoremAnd.SecondaryDefinitions

blueprint_comment /--
\section{The estimates of Buthe}\label{buthe-sec}

In this section we collect some results from Buthe's paper
\cite{Buthe}, which provides explicit estimates on $\psi(x)$,
$\theta(x)$, and $\pi(x)$.

TODO: Add more results and proofs here, and reorganize the blueprint
-/

namespace Buthe

open MeasureTheory Real Chebyshev

@[blueprint
  "buthe-eq-1-4"
  (title := "Buthe Equation (1.4)")
  (statement := /--
    $\pi^*(x) = \sum_{k \geq 1} \pi(x^{1/k}) / k$. -/)]
noncomputable def pi_star (x : ℝ) : ℝ := ∑' (k : ℕ), pi (x ^ (1 / (k : ℝ))) / (k : ℝ)

@[blueprint
  "buthe-theorem-2a"
  (title := "Buthe Theorem 2(a)")
  (statement := /--
    If $11 < x \leq 10^{19}$, then
    $|x - \psi(x)| \leq 0.94\sqrt{x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_2a {x : ℝ} (hx1 : 11 < x) (hx2 : x ≤ 10 ^ 19) :
    Eψ x ≤ 0.94 / sqrt x := by sorry

@[blueprint
  "buthe-theorem-2b"
  (title := "Buthe Theorem 2(b)")
  (statement := /--
    If $1423 \leq x \leq 10^{19}$, then
    $x - \vartheta(x) \leq 1.95\sqrt{x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_2b {x : ℝ} (hx1 : 1423 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    x - θ x ≤ 1.95 * sqrt x := by sorry

@[blueprint
  "buthe-theorem-2c"
  (title := "Buthe Theorem 2(c)")
  (statement := /--
    If $1 \leq x \leq 10^{19}$, then
    $x - \vartheta(x) > 0.05\sqrt{x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_2c {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    x - θ x ≥ 0.05 * sqrt x := by sorry

@[blueprint
  "buthe-theorem-2d"
  (title := "Buthe Theorem 2(d)")
  (statement := /--
    If $2 \leq x \leq 10^{19}$, then
    $|\li(x) - \pi^*(x)| < \frac{\sqrt{x}}{\log x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_2d {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    abs (li x - pi_star x) < sqrt x / log x := by sorry

@[blueprint
  "buthe-theorem-2e"
  (title := "Buthe Theorem 2(e)")
  (statement := /--
    If $2 \leq x \leq 10^{19}$, then
    $\li(x) - \pi(x) \leq \frac{\sqrt{x}}{\log(x)}
    \left(1.95 + \frac{3.9}{\log x}
    + \frac{19.5}{\log(x)^2}\right)$. -/)
  (latexEnv := "theorem")]
theorem theorem_2e {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    li x - pi x ≤ (sqrt x / log x) * (1.95 + 3.9 / log x + 19.5 / (log x) ^ 2) := by sorry

@[blueprint
  "buthe-theorem-2f"
  (title := "Buthe Theorem 2(f)")
  (statement := /--
    If $2 \leq x \leq 10^{19}$, then
    $\mathrm{li}(x) - \pi(x) > 0$. -/)
  (latexEnv := "theorem")]
theorem theorem_2f {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) : li x - pi x > 0 := by sorry

/- Table1.UpperandlowerboundsM± ψ(x)for t−ψ(t) √t in[x,2x] x M− ψ(x) M+ ψ(x) x M− ψ(x) M+ ψ(x) 1010 −.77 .85 1012 −.80 .81 2×1010 −.75 .64 2×1012 −.79 .76 4×1010 −.73 .80 4×1012 −.73 .73 8×1010 −.80 .86 8×1012 −.80 .76 16×1010 −.88 .68 16×1012 −.80 .68 32×1010 −.88 .78 32×1012 −.67 .93 64×1010 −.66 .74 64×1012 −.78 .77 x M− ψ(x) M+ ψ(x) x M− ψ(x) M+ ψ(x) 1014 −.79 .72 1016 −.88 .74 2×1014 −.60 .76 2×1016 −.87 .70 4×1014 −.65 .73 4×1016 −.65 .73 8×1014 −.81 .88 8×1016 −.82 .77 16×1014 −.66 .86 16×1016 −.71 .92 32×1014 −.74 .86 32×1016 −.78 .71 64×1014 −.73 .66 64×1016 −.94 .82 128×1016 −.94 .75 256×1016 −.82 .86 512×1016 −.83 .94 -/

def table_1 : List (ℝ × ℝ × ℝ) := [
  (10 ^ 10, -0.77, 0.85),
  (2 * 10 ^ 10, -0.75, 0.64),
  (4 * 10 ^ 10, -0.73, 0.80),
  (8 * 10 ^ 10, -0.80, 0.86),
  (16 * 10 ^ 10, -0.88, 0.68),
  (32 * 10 ^ 10, -0.88, 0.78),
  (64 * 10 ^ 10, -0.66, 0.74),
  (10 ^ 12, -0.80, 0.81),
  (2 * 10 ^ 12, -0.79, 0.76),
  (4 * 10 ^ 12, -0.73, 0.73),
  (8 * 10 ^ 12, -0.80, 0.76),
  (16 * 10 ^ 12, -0.80, 0.68),
  (32 * 10 ^ 12, -0.67, 0.93),
  (64 * 10 ^ 12, -0.78, 0.77),
  (10 ^ 14, -0.79, 0.72),
  (2 * 10 ^ 14, -0.60, 0.76),
  (4 * 10 ^ 14, -0.65, 0.73),
  (8 * 10 ^ 14, -0.81, 0.88),
  (16 * 10 ^ 14, -0.66, 0.86),
  (32 * 10 ^ 14, -0.74, 0.86),
  (64 * 10 ^ 14, -0.73, 0.66),
  (10 ^ 16, -0.88, 0.74),
  (2 * 10 ^ 16, -0.87, 0.70),
  (4 * 10 ^ 16, -0.65, 0.73),
  (8 * 10 ^ 16, -0.82, 0.77),
  (16 * 10 ^ 16, -0.71, 0.92),
  (32 * 10 ^ 16, -0.78, 0.71),
  (64 * 10 ^ 16, -0.94, 0.82),
  (128 * 10 ^ 16, -0.94, 0.75),
  (256 * 10 ^ 16, -0.82, 0.86),
  (512 * 10 ^ 16, -0.83, 0.94)
]

@[blueprint
  "buthe-eq-6-2"
  (title := "Buthe Equation (6.2)")
  (statement := /-- If $x, M_\psi^-, M_\psi^+$ are as in Table 1 of Buthe, then $\frac{t - \psi(t)}{\sqrt{t}} \in [M_\psi^-, M_\psi^+]$ for $t \in [x, 2x]$. -/)
  (latexEnv := "lemma")]
theorem eq_6_2 (x Mψ_minus Mψ_plus : ℝ) (h : (x, Mψ_minus, Mψ_plus) ∈ table_1) :
    ∀ t ∈ Set.Icc x (2 * x), Mψ_minus ≤ (t - ψ t) / sqrt t ∧ (t - ψ t) / sqrt t ≤ Mψ_plus := by
    sorry

end Buthe
