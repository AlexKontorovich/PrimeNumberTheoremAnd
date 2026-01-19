import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.FioriKadiriSwidinsky
import PrimeNumberTheoremAnd.BKLNW
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime

blueprint_comment /--
\section{The implications of FKS2}

In this file we record the implications in the paper \cite{FKS2} that allow one to convert primary bounds on $E_\psi$ into secondary bounds on $E_\pi$, $E_\theta$.
-/

open Real

namespace FKS2

@[blueprint
  "fks2-rem"
  (title := "Remark in FKS2 Section 1.1")
  (statement := /-- $\li(x) - \Li(x) = \li(2)$. -/)
  (proof := /-- This follows directly from the definitions of $\li$ and $\Li$. -/)
  (latexEnv := "remark")
  (discussion := 608)]
theorem sec_1_1_remark : ∀ x > 2, li x - Li x = li 2 := sorry

@[blueprint
  "fks2-eq-16"
  (title := "g function, FKS2 (16)")
  (statement := /--
  For any $a,b,c,x \in \mathbb{R}$ we define
  $g(a,b,c,x) := x^{-a} (\log x)^b \exp( c (\log x)^{1/2} )$. -/)]
noncomputable def g_bound (a b c x : ℝ) : ℝ := x^(-a) * (log x)^b * exp (c * sqrt (log x))

@[blueprint
  "fks2-eq-17"
  (title := "FKS2 equation (17)")
  (statement := /--
  For any $2 \leq x_0 < x$ one has
  $$ (\pi(x) - \Li(x)) - (\pi(x_0) - \Li(x_0)) = \frac{\theta(x) - x}{\log x}
    - \frac{\theta(x_0) - x_0}{\log x_0} + \int_{x_0}^x \frac{\theta(t) - t}{t \log^2 t} dt.$$ -/)
  (proof := /-- This follows from Sublemma \ref{rs-417}. -/)
  (latexEnv := "sublemma")
  (discussion := 609)]
theorem eq_17 {x₀ x : ℝ} (hx₀ : x₀ ≥ 2) (hx : x > x₀) :
  (pi x - Li x) - (pi x₀ - Li x₀) =
    (θ x - x) / log x - (θ x₀ - x₀) / log x₀ +
    ∫ t in x₀..x, (θ t - t) / (t * log t ^ 2) :=
  sorry

@[blueprint
  "fks2-lemma-10-substep"
  (title := "FKS2 Sublemma 10-1")
  (statement := /-- We have
$$ \frac{d}{dx} g(a, b, c, x) = \left( -a \log(x) + b + \frac{c}{2}\sqrt{\log(x)} \right) x^{-a-1} (\log(x))^{b-1} \exp(c\sqrt{\log(x)}).$$
  -/)
  (proof := /-- This follows from straightforward differentiation. -/)
  (latexEnv := "sublemma")
  (discussion := 610)]
theorem lemma_10_substep {a b c x : ℝ} (hx : x > 1) :
  deriv (g_bound a b c) x =
    (-a * log x + b + (c / 2) * sqrt (log x)) * x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) := by
      have h_prod_rule : deriv (fun x => x ^ (-a) * (log x) ^ b * exp (c * sqrt (log x))) x =
        (deriv (fun x => x ^ (-a)) x) * (log x) ^ b * exp (c * sqrt (log x)) +
        x ^ (-a) * (deriv (fun x => (log x) ^ b) x) * exp (c * sqrt (log x)) +
        x ^ (-a) * (log x) ^ b * (deriv (fun x => exp (c * sqrt (log x))) x) := by
          norm_num [ DifferentiableAt.mul, DifferentiableAt.rpow, DifferentiableAt.sqrt, show x ≠ 0 by linarith, show log x ≠ 0 by exact ne_of_gt <| log_pos hx ] ; ring
      unfold g_bound
      rw [h_prod_rule]
      norm_num [ show x ≠ 0 by linarith, show log x ≠ 0 by exact ne_of_gt ( log_pos hx ), sqrt_eq_rpow, rpow_sub_one, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ; ring_nf
      norm_num [ ne_of_gt ( log_pos hx ) ]
      rw [ show ( - ( 1 / 2 : ℝ ) ) = ( 1 / 2 : ℝ ) - 1 by norm_num, rpow_sub ( log_pos hx ) ] ; norm_num ; ring

@[blueprint
  "fks2-lemma-10-substep-2"
  (title := "FKS2 Sublemma 10-2")
  (statement := /-- $\frac{d}{dx} g(a, b, c, x) $ is negative when $-au^2 + \frac{c}{2}u + b < 0$, where $u = \sqrt{\log(x)}$.
  -/)
  (proof := /-- Clear from previous sublemma. -/)
  (latexEnv := "sublemma")
  (discussion := 611)]
theorem lemma_10_substep_2 {a b c x : ℝ} (hx : x > 1) :
  deriv (g_bound a b c) x < 0 ↔
    -a * (sqrt (log x)) ^ 2 + (c / 2) * sqrt (log x) + b < 0 := by
  have hlogx := log_pos hx
  rw [lemma_10_substep hx, sq_sqrt hlogx.le]
  have hpos : 0 < x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) := by positivity
  rw [show ∀ y, y * x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) =
      y * (x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x))) from fun _ => by ring]
  rw [mul_neg_iff]
  constructor <;> intro h
  · rcases h with ⟨-, hc⟩ | ⟨h, -⟩ <;> linarith
  · exact Or.inr ⟨by linarith, hpos⟩

@[blueprint
  "fks2-lemma-10a"
  (title := "FKS2 Lemma 10a")
  (statement := /-- If $a>0$, $c>0$ and $b < -c^2/16a$, then $g(a,b,c,x)$ decreases with $x$. -/)
  (proof := /-- We apply Lemma \ref{fks2-lemma-10-substep-2}. There are no roots when $b < -\frac{c^2}{16a}$, and the derivative is always negative in this case.
 -/)
  (latexEnv := "lemma")
  (discussion := 612)]
theorem lemma_10a {a b c : ℝ} (ha : a > 0) (hc : c > 0) (hb : b < -c ^ 2 / (16 * a)) :
  StrictAnti (g_bound a b c) :=
  sorry

@[blueprint
  "fks2-lemma-10b"
  (title := "FKS2 Lemma 10b")
  (statement := /--
  For any $a>0$, $c>0$ and $b \geq -c^2/16a$, $g(a,b,c,x)$ decreases with $x$ for
  $x > \exp((\frac{c}{4a} + \frac{1}{2a} \sqrt{\frac{c^2}{4} + 4ab})^2)$. -/)
  (proof := /-- We apply Lemma \ref{fks2-lemma-10-substep-2}. If $a > 0$, there are two real roots only if $\frac{c^2}{4} + 4ab \geq 0$ or equivalently $b \geq -\frac{c^2}{16a}$, and the derivative is negative for $u > \frac{\frac{c}{2} + \sqrt{\frac{c^2}{4} + 4ab}}{2a}$.
 -/)
  (latexEnv := "lemma")
  (discussion := 613)]
theorem lemma_10b {a b c : ℝ} (ha : a > 0) (hc : c > 0) (hb : b ≥ -c ^ 2 / (16 * a)) :
    StrictAntiOn (g_bound a b c)
      (Set.Ioi (exp ((c / (4 * a) + (1 / (2 * a)) * sqrt (c ^ 2 / 4 + 4 * a * b)) ^ 2))) :=
  sorry

@[blueprint
  "fks2-lemma-10c"
  (title := "FKS2 Lemma 10c")
  (statement := /--
  If $c>0$, $g(0,b,c,x)$ decreases with $x$ for $\sqrt{\log x} < -2b/c$. -/)
  (proof := /-- We apply Lemma \ref{fks2-lemma-10-substep-2}. If $a = 0$, it is negative when $u < \frac{-2b}{c}$.
  Note: this lemma is mistyped as $\sqrt{\log x} > -2b/c$ in \cite{FKS2}.
 -/)
  (latexEnv := "lemma")
  (discussion := 614)]
theorem lemma_10c {b c : ℝ} (hb : b < 0) :
    StrictAntiOn (g_bound 0 b c) (Set.Ioo 1 (exp ((-2 * b / c) ^ 2))) := by
    intro x hx y hy hxy
    simp only [g_bound, neg_zero, rpow_zero, one_mul, Nat.reduceDiv, pow_zero, mul_one]
    refine mul_lt_mul_of_pos_right ?_ (by simpa [exp] using Real.exp_pos c)
    rw [Real.rpow_lt_rpow_iff_of_neg (Real.log_pos (Set.mem_Ioo.mp hy).1) (Real.log_pos (Set.mem_Ioo.mp hx).1) hb]
    exact Real.log_lt_log (by linarith [(Set.mem_Ioo.mp hx).1]) hxy

@[blueprint
  "fks2-corollary-11"
  (title := "FKS2 Corollary 11")
  (statement := /--
  If $B \geq 1 + C^2 / 16R$ then $g(1,1-B,C/\sqrt{R},x)$ is decreasing in $x$. -/)
  (proof := /-- This follows from Lemma \ref{fks2-lemma-10a} applied with $a=1$, $b=1-B$ and $c=C/\sqrt{R}$. -/)
  (latexEnv := "corollary")
  (discussion := 615)]
theorem corollary_11 {B C R : ℝ} (hR : R > 0) (hB : B > 1 + C ^ 2 / (16 * R)) (hC : C > 0) :
    StrictAnti (g_bound 1 (1 - B) (C / sqrt R)) := by
  apply lemma_10a one_pos (div_pos hC (sqrt_pos.mpr hR))
  rw [div_pow, sq_sqrt hR.le, mul_one]
  linarith [show C ^ 2 / R / 16 = C ^ 2 / (16 * R) by ring]

@[blueprint
  "fks2-eq-19"
  (title := "Dawson function, FKS2 (19)")
  (statement := /--
  The Dawson function $D_+ : \mathbb{R} \to \mathbb{R}$ is defined by the formula
  $D_+(x) := e^{-x^2} \int_0^x e^{t^2}\ dt$. -/)]
noncomputable def dawson (x : ℝ) : ℝ := exp (-x ^ 2) * ∫ t in 0..x, exp (t ^ 2)


@[blueprint
  "fks2-remark-after-corollary-11"
  (title := "FKS2 remark after Corollary 11")
  (statement := /--
  The Dawson function has a single maximum at $x \approx 0.942$, after which the function is
  decreasing. -/)
  (proof := /-- The Dawson function satisfies the differential equation $F'(x) + 2xF(x) = 1$ from which it follows that the second derivative satisfies $F''(x) = −2F(x) − 2x(−2xF(x) + 1)$, so that at every critical point (where we have $F(x) = \frac{1}{2x}$) we have $F''(x) = −\frac{1}{x}$.  It follows that every positive critical value gives a local maximum, hence there is a unique such critical value and the function decreases after it. Numerically one may verify this is near 0.9241 see https://oeis.org/ A133841. -/)
  (latexEnv := "remark")
  (discussion := 616)]
theorem remark_after_corollary_11 :
    ∃ x₀ : ℝ, x₀ ∈ Set.Icc 0.924 0.925 ∧ (∀ x, dawson x ≤ dawson x₀) ∧
      StrictAntiOn dawson (Set.Ioi x₀) := sorry

@[blueprint
  "fks2-lemma-12"
  (title := "FKS2 Lemma 12")
  (statement := /--
  Suppose that $E_\theta$ satisfies an admissible classical bound with parameters $A,B,C,R,x_0$.
  Then, for all $x \geq x_0$,
  $$ \int_{x_0}^x |\frac{E_\theta(t)}{\log^2 t} dt| \leq \frac{2A}{R^B} x m(x_0,x)
    \exp(-C \sqrt{\frac{\log x}{R}}) D_+( \sqrt{\log x} - \frac{C}{2\sqrt{R}} )$$
  where
  $$ m(x_0,x) = \max ( (\log x_0)^{(2B-3)/2}, (\log x)^{(2B-3)/2} ). $$
  -/)
  (proof := /-- Since $\varepsilon_{\theta,\mathrm{asymp}}(t)$ provides an admissible bound on $\theta(t)$ for all $t \geq x_0$, we have
\[
\int_{x_0}^{x} \left| \frac{\theta(t) - t}{t(\log(t))^2} \right| dt \leq \int_{x_0}^{x} \frac{\varepsilon_{\theta,\mathrm{asymp}}(t)}{(\log(t))^2} = \frac{A_\theta}{R^B} \int_{x_0}^{x} (\log(t))^{B-2} \exp\left( -C\sqrt{\frac{\log(t)}{R}} \right) dt.
\]
We perform the substitution $u = \sqrt{\log(t)}$ and note that $u^{2B-3} \leq m(x_0, x)$ as defined in (21). Thus the above is bounded above by
\[
\frac{2A_\theta m(x_0, x)}{R^B} \int_{\sqrt{\log(x_0)}}^{\sqrt{\log(x)}} \exp\left( u^2 - \frac{Cu}{\sqrt{R}} \right) du.
\]
Then, by completing the square $u^2 - \frac{Cu}{\sqrt{R}} = \left( u - \frac{C}{2\sqrt{R}} \right)^2 - \frac{C^2}{4R}$ and doing the substitution $v = u - \frac{C}{2\sqrt{R}}$, the above becomes
\[
\frac{2A_\theta m(x_0, x)}{R^B} \exp\left( -\frac{C^2}{4R} \right) \int_{\sqrt{\log(x_0)} - \frac{C}{2\sqrt{R}}}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv.
\]
Now we have
\begin{align*}
\int_{\sqrt{\log(x_0)} - \frac{C}{2\sqrt{R}}}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv &\leq \int_{0}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv \\
&= x \exp\left( \frac{C^2}{4R} \right) \exp\left( -C\sqrt{\frac{\log(x)}{R}} \right) D_+\left( \sqrt{\log(x)} - \frac{C}{2\sqrt{R}} \right).
\end{align*}
Combining the above completes the proof. -/)
  (latexEnv := "lemma")
  (discussion := 617)]
theorem lemma_12 {A B C R x₀ x : ℝ} (hEθ : Eθ.classicalBound A B C R x₀) (hx : x ≥ x₀) :
  ∫ t in x₀..x, |Eθ t| / log t ^ 2 ≤
    (2 * A) / (R ^ B) * x * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) *
    exp (-C * sqrt (log x / R)) * dawson (sqrt (log x) - C / (2 * sqrt R)) :=
  sorry

noncomputable def ν_asymp (Aψ B C R x₀ : ℝ) : ℝ :=
  (1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
    (BKLNW.a₁ (log x₀) * (log x₀) * x₀ ^ (-(1:ℝ)/2) +
      BKLNW.a₂ (log x₀) * (log x₀) * x₀ ^ (-(2:ℝ)/3))

@[blueprint
  "fks2-proposition-13"
  (title := "FKS2 Proposition 13")
  (statement := /--
  Suppose that $A_\psi,B,C,R,x_0$ give an admissible bound for $E_\psi$.  If $B > C^2/8R$, then
  $A_\theta, B, C, R, x_0$ give an admissible bound for $E_\theta$, where
  $$ A_\theta = A_\psi (1 + \nu_{asymp}(x_0))$$
  with
  $$ \nu_{asymp}(x_0) = \frac{1}{A_\psi} (\frac{R}{\log x_0})^B
    \exp(C \sqrt{\frac{\log x_0}{R}}) (a_1 (\log x_0) x_0^{-1/2} + a_2 (\log x_0) x_0^{-2/3}).$$
  -/)
  (proof := /-- The proof of \cite[Corollary 14.1]{BKLNW} essentially proves the proposition, but requires that $x_0 \geq e^{1000}$ to conclude that the function
  $$ 1 + \frac{a_1 \exp(C \sqrt{\frac{\log x}{R}})}{A_\psi \sqrt{x} (\log x/R)^{B}} + \frac{a_2 \exp(C \sqrt{\frac{\log x}{R}})}{A_\psi x^{2/3} (\log x/R)^{B}} = 1 + \frac{a_1}{A_\psi} g(1/2, -B, C/\sqrt{R}, x) + \frac{a_2}{A_\psi} g(2/3, -B, C/\sqrt{R}, x)$$
  is decreasing. By Lemma \ref{fks2-lemma-10a}, since $B > C^2/8R$, the function is actually decreasing for all $x$. -/)
  (latexEnv := "proposition")
  (discussion := 671)]
theorem proposition_13
  (Aψ B C R x₀ : ℝ)
  (h_bound : Eψ.classicalBound Aψ B C R x₀)
  (hB : B > C ^ 2 / (8 * R)) :
  Eθ.classicalBound (Aψ * (1 + ν_asymp Aψ B C R x₀)) B C R x₀ := by sorry

@[blueprint
  "fks2-corollary-14"
  (title := "FKS2 Corollary 14")
  (statement := /--
  We have an admissible bound for $E_\theta$ with $A = 121.0961$, $B=3/2$, $C=2$,
  $R = 5.5666305$, $x_0=2$.
  -/)
  (proof := /-- By \cite[Corollary 1.3]{FKS}, with $R = 5.5666305$, and using the admissible asymptotic bound for $E_\psi(x)$ with $A_\psi = 121.096$, $B = 3/2$, $C = 2$, for all $x \geq x_0 = e^{30}$, we can obtain $\nu_{asymp}(x_0) \leq 6.3376 \cdot 10^{-7}$, from which one can conclude an admissible asymptotic bound for $E_\theta(x)$ with $A_\theta = 121.0961$, $B = 3/2$, $C = 2$, for all $x \geq x_0 = e^{30}$. Additionally, the minimum value of $\varepsilon_{\theta,asymp}(x)$ for $2 \leq x \leq e^{30}$ is roughly $2.6271\ldots$ at $x=2$. The results found in \cite[Table 13 and 14]{BKLNW} give $E_\theta(x) \leq 1 < \varepsilon_{\theta,asymp}(2) \leq \varepsilon_{\theta,asymp}(x)$ for all $2 \leq x \leq e^{30}$. -/)
  (latexEnv := "corollary")
  (discussion := 672)]
theorem corollary_14 : Eθ.classicalBound 121.0961 (3/2) 2 5.5666305 2 := sorry


@[blueprint
  "fks2-eq-9"
  (title := "mu asymptotic function, FKS2 (9)")
  (statement := /--
  For $x_0,x_1 > 0$, we define
  $$ \mu_{asymp}(x_0,x_1) := \frac{x_0 \log(x_1)}{\epsilon_{\theta,asymp}(x_1) x_1 \log(x_0)}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| +
    \frac{2D_+(\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}}}{\sqrt{\log x_1}}$$.
  -/)]
noncomputable def μ_asymp (A B C R x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / ((admissible_bound A B C R x₁) * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| +
    2 * (dawson (sqrt (log x₁) - C / (2 * sqrt R))) / (sqrt (log x₁))

@[blueprint
  "fks2-def-5"
  (title := "FKS2 Definition 5")
  (statement := /--
  Let $x_0 > 2$. We say a (step) function $ε_{\diamond,num}(x_0)$ gives an admissible numerical
  bound for $E_\diamond(x)$ if $E_\diamond(x) \leq ε_{\diamond,num}(x_0)$ for all $x \geq x_0$. -/)]
def _root_.Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ (ε x₀)

def _root_.Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ (ε x₀)

noncomputable def μ_num_1 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    (log x₂) / x₂ * (Li x₂ - x₂ / log x₂ - Li x₁ + x₁ / log x₁)

noncomputable def μ_num_2 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    1 / (log x₁ + log (log x₁) - 1)

noncomputable def μ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) (x₂ : EReal) : ℝ :=
  if x₂ ≤ x₁ * log x₁ then
    μ_num_1 b εθ_num x₀ x₁ x₂.toReal
  else
    μ_num_2 b εθ_num x₀ x₁

noncomputable def επ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ)
    (x₂ : EReal) : ℝ :=
  εθ_num x₁ * (1 + μ_num b εθ_num x₀ x₁ x₂)

noncomputable def default_b (x₀ x₁ : ℝ) : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then log x₀ else log x₁

@[blueprint
  "fks2-remark-7"
  (title := "FKS2 Remark 7")
  (statement := /--
  If
  $$ \frac{d}{dx} \frac{\log x}{x}
    \left( \Li(x) - \frac{x}{\log x} - \Li(x_1) + \frac{x_1}{\log x_1} \right)|_{x_2} \geq 0 $$
  then $\mu_{num,1}(x_0,x_1,x_2) < \mu_{num,2}(x_0,x_1)$.
  -/)
  (proof := /-- This follows from the definitions of $\mu_{num,1}$ and $\mu_{num,2}$. -/)
  (latexEnv := "remark")
  (discussion := 673)]
theorem remark_7 {x₀ x₁ : ℝ} (x₂ : ℝ) (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂)
  (hderiv : deriv (fun x ↦ (log x) / x * (Li x - x / log x - Li x₁ + x₁ / log x₁)) x₂ ≥ 0) :
    μ_num_1 b εθ_num x₀ x₁ x₂ < μ_num_2 b εθ_num x₀ x₁ := by sorry

@[blueprint
  "fks2-remark-15"
  (title := "FKS2 Remark 15")
  (statement := /--
  If $\log x_0 \geq 1000$ then we have an admissible bound for $E_\theta$ with the indicated
  choice of $A(x_0)$, $B = 3/2$, $C = 2$, and $R = 5.5666305$.
  -/)
  (latexEnv := "remark")
  (discussion := 674)]
theorem remark_15 (x₀ : ℝ) (h : log x₀ ≥ 1000) :
    Eθ.classicalBound (FKS.A x₀) (3/2) 2 5.5666305 x₀ := by sorry

@[blueprint
  "fks2-theorem-3"
  (title := "FKS2 Theorem 3")
  (statement := /--
  If $B \geq \max(3/2, 1 + C^2/16 R)$, $x_0 > 0$, and one has an admissible asymptotic bound
  with parameters $A,B,C,x_0$ for $E_\theta$, and
  $$ x_1 \geq \max( x_0, \exp( (1 + \frac{C}{2\sqrt{R}}))^2),$$
  then
  $$ E_\pi(x) \leq \epsilon_{\theta,asymp}(x_1) ( 1 + \mu_{asymp}(x_0,x_1) ) $$
  for all $x \geq x_1$.  In other words, we have an admissible bound with parameters
  $(1+\mu_{asymp}(x_0,x_1))A, B, C, x_1$ for $E_\pi$.
  -/)
  (proof := /-- We assume that $(\pi(x_0) - \Li(x_0))$ can be numerically calculated. Thus we use (17) to rewrite $(\pi(x) - \Li(x)) - (\pi(x_0) - \Li(x_0))$, so that
  $$ |\pi(x) - \Li(x)| = \frac{\theta(x) - x}{\log(x)} - \frac{\theta(x_0) - x_0}{\log(x_0)} + \int_{x_0}^{x} \frac{\theta(t) - t}{t (\log(t))^2} dt + \pi(x_0) - \Li(x_0) $$
  $$ \leq |\pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)}| + \frac{\theta(x) - x}{\log(x)} + \int_{x_0}^{x} \frac{\theta(t) - t}{t (\log(t))^2} dt.$$
  We use the assumption ($\varepsilon_{\theta,\mathrm{asymp}}(x)$ provides an admissible bound on $\theta(x)$ for all $x \geq x_0$) to bound $\frac{\theta(x) - x}{\log(x)}$ and Lemma \ref{fks2-lemma-12} to bound $\int_{x_0}^{x} \frac{\theta(t) - t}{t (\log(t))^2} dt$.  We obtain
  $$ |\pi(x) - \Li(x)| \leq |\pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)}| + \frac{x \varepsilon_{\theta,\mathrm{asymp}}(x)}{\log(x)} + \frac{2 A_\theta}{R^B} x m(x_0,x) \exp(-C \sqrt{\frac{\log x}{R}}) D_+\left( \sqrt{\log x} - \frac{C}{2\sqrt{R}} \right).$$
  We recall that $x \geq x_1 \geq x_0$.  Note that, by Corollary \ref{fks2-corollary-11},
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} = \frac{1}{A_\theta} g(1, 1 - B, \frac{C}{\sqrt{R}}, x) $$
  is decreasing for all $x$.  Thus,
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} \leq \frac{\log(x_1)}{x_1 \varepsilon_{\theta,\mathrm{asymp}}(x_1)}. $$
  In addition, we have the simplification
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} \frac{2 A_\theta}{R^B} x m(x_0,x) e^{-C \sqrt{\frac{\log x}{R}}} = 2 m(x_0,x) (\log(x))^{1 - B} = 2 (\log(x))^{1 - B} \leq 2 (\log(x_1))^{1 - B}, $$
  by definition (6) of $\varepsilon_{\theta,\mathrm{asymp}}(x)$ and by $m(x_0,x) = (\log(x))^{(2B - 3)/2}$, since $B \geq 3/2$.  Finally, since $\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}} > 1$, the Dawson function decreases for all $x \geq x_1$:
  $$ D_+\left( \sqrt{\log x} - \frac{C}{2\sqrt{R}} \right) \leq D_+\left( \sqrt{\log x_1} - \frac{C}{2\sqrt{R}} \right). $$
  We conclude by combining the above:
  $$ \frac{|\pi(x) - \Li(x)|}{\frac{x \varepsilon_{\theta,\mathrm{asymp}}(x)}{\log(x)}} \leq \frac{\log(x_1)}{x_1 \varepsilon_{\theta,\mathrm{asymp}}(x_1)} |\pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)}| + 1 + \frac{2 D_+\left( \sqrt{\log x_1} - \frac{C}{2\sqrt{R}} \right)}{\sqrt{\log(x_1)}}, $$
  from which we deduce the announced bound. -/)
  (latexEnv := "theorem")
  (discussion := 675)
  ]
theorem theorem_3 (A B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hx0 : x₀ > 0)
  (hE_theta : Eθ.classicalBound A B C R x₀)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2))) :
  Eπ.classicalBound (A * (1 + μ_asymp A B C R x₀ x₁)) B C R x₁ :=
  sorry

noncomputable def εθ_from_εψ (εψ : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  εψ x₀ + 1.00000002 * (x₀ ^ (-(1:ℝ)/2) + x₀ ^ (-(2:ℝ)/3) + x₀ ^ (-(4:ℝ)/5)) +
    0.94 * (x₀ ^ (-(3:ℝ)/4) + x₀ ^ (-(5:ℝ)/6) + x₀ ^ (-(9:ℝ)/10))

@[blueprint
  "fks2-proposition-17"
  (title := "FKS2 Proposition 17")
  (statement := /--
  Let $x > x_0 > 2$.  If $E_\psi(x) \leq \varepsilon_{\psi,num}(x_0)$, then
  $$ - \varepsilon_{\theta,num}(x_0) \leq \frac{\theta(x)-x}{x}
    \leq \varepsilon_{\psi,num}(x_0) \leq \varepsilon_{\theta,num}(x_0)$$
  where
  $$ \varepsilon_{\theta,num}(x_0) = \varepsilon_{\psi,num}(x_0) +
    1.00000002(x_0^{-1/2}+x_0^{-2/3}+x_0^{-4/5}) +
    0.94 (x_0^{-3/4} + x_0^{-5/6} + x_0^{-9/10})$$ -/)
  (proof := /-- The upper bound is immediate since $\theta(x) \leq \psi(x)$ for all $x$. For the lower bound, we have
  $$\frac{\theta(x) - x}{x} = \frac{\psi(x) - x}{x} + \frac{\theta(x) - \psi(x)}{x}.$$
  By Theorem \ref{costa-pereira-theorem-1a}, we have
  $$\psi(x) - \theta(x) \leq \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}).$$
  We use [4, Theorem 2], that for $0 < x < 11$, $\psi(x) < x$, and that $\varepsilon_{\psi,num}(10^{19}) < 2 \cdot 10^{-8}$. In particular when $2 < x < 10^{38}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq x^{1/2} + x^{1/3} + x^{1/5} + 0.94(x^{1/4} + x^{1/6} + x^{1/10}),$$
  when $10^{38} \leq x < 10^{54}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002x^{1/2} + x^{1/3} + x^{1/5} + 0.94(x^{1/6} + x^{1/10}),$$
  when $10^{54} \leq x < 10^{95}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002(x^{1/2} + x^{1/3}) + x^{1/5} + 0.94x^{1/10},$$
  and finally when $x \geq 10^{95}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002(x^{1/2} + x^{1/3} + x^{1/5}).$$
  The result follows by combining the worst coefficients from all cases and dividing by $x$. -/)
  (latexEnv := "proposition")]
theorem proposition_17 {x x₀ : ℝ} (hx : x > x₀) (hx₀ : x₀ > 2) (εψ : ℝ → ℝ)
    (hEψ : Eψ x ≤ εψ x₀) :
    -εθ_from_εψ εψ x₀ ≤ (θ x - x) / x ∧ (θ x - x) / x ≤ εψ x₀ ∧
      εψ x₀ ≤ εθ_from_εψ εψ x₀ := by sorry

@[blueprint
  "fks2-lemma-19"
  (title := "FKS2 Lemma 19")
  (statement := /--
  Let $x_1 > x_0 \geq 2$, $N \in \N$, and let $(b_i)_{i=1}^N$ be a finite partition of
  $[x_0,x_1]$.  Then
  $$ |\int_{x_0}^{x_1} \frac{\theta(t)-t}{t \log^2 t}\ dt|
    \leq \sum_{i=1}^{N-1} \eps_{\theta,num}(e^{b_i})
    ( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}).$$ -/)
  (latexEnv := "lemma")]
theorem lemma_19 {x₀ x₁ : ℝ} (hx₁ : x₁ > x₀) (hx₀ : x₀ ≥ 2)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) :
  |∫ t in x₀..x₁, (θ t - t) / (t * log t ^ 2)| ≤
    ∑ i ∈ Finset.Iio (Fin.last N),
      εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) :=
  sorry

@[blueprint
  "fks2-lemma-20"]
theorem lemma_20_a : StrictAntiOn (fun x ↦ Li x - x / log x) (Set.Ioi 6.58) := sorry

@[blueprint
  "fks2-lemma-20"
  (title := "FKS2 Lemma 20")
  (statement := /--
  Assume $x \geq 6.58$. Then $\Li(x) - \frac{x}{\log x}$ is strictly increasing and
  $\Li(x) - \frac{x}{\log x} > \frac{x-6.58}{\log^2 x} > 0$.
  -/)
  (latexEnv := "lemma")]
theorem lemma_20_b {x : ℝ} (hx : x ≥ 6.58) :
  Li x - x / log x > (x - 6.58) / (log x) ^ 2 ∧
  (x - 6.58) / (log x) ^ 2 > 0 :=
  sorry



@[blueprint
  "fks2-theorem-6"
  (title := "FKS2 Theorem 6")
  (latexEnv := "theorem")]
theorem theorem_6 {x₀ x₁ : ℝ} (x₂ : EReal) (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x.toEReal ≤ x₂) :
  Eπ x ≤ επ_num b εθ_num x₀ x₁ x₂ :=
  sorry

@[blueprint
  "fks2-theorem-6"
  (title := "FKS2 Theorem 6")
  (statement := /--
  Let $x_0 > 0$ be chosen such that $\pi(x_0)$ and $\theta(x_0)$ are computable, and let
  $x_1 \geq \max(x_0, 14)$. Let $\{b_i\}_{i=1}^N$ be a finite partition of
  $[\log x_0, \log x_1]$, with $b_1 = \log x_0$ and $b_N = \log x_1$, and suppose that
  $\varepsilon_{\theta,\mathrm{num}}$ gives computable admissible numerical bounds for
  $x = \exp(b_i)$, for each $i=1,\dots,N$.  For $x_1 \leq x_2 \leq x_1 \log x_1$, we define
  $$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_0) x_1 \log x_0}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$
  $$ + \frac{\log x_1}{\varepsilon_{theta,num}(x_1) x_1} \sum_{i=1}^{N-1}
    \varepsilon_{\theta,num}(\exp(b_i))
    \left( Li(e^{b_{i+1}}) - Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}\right)$$
  $$ + \frac{\log x_2}{x_2}
    \left( Li(x_2) - \frac{x_2}{\log x_2} - Li(x_1) + \frac{x_1}{\log x_1} \right)$$
  and for $x_2 > x_1 \log x_1$, including the case $x_2 = \infty$, we define
  $$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_1) x_1 \log x_0}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$
  $$ + \frac{\log x_1}{\varepsilon_{\theta,num}(x_1) x_1} \sum_{i=1}^{N-1}
    \varepsilon_{\theta,num}(\exp(b_i))
    \left( Li(e^{b_{i+1}}) - Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}\right)$$
  $$ + \frac{1}{\log x_1 + \log\log x_1 - 1}.$$
  Then, for all $x_1 \leq x \leq x_2$ we have
  $$ E_\pi(x) \leq \varepsilon_{\pi,num}(x_1,x_2) :=
    \varepsilon_{\theta,num}(x_1)(1 + \mu_{num}(x_0,x_1,x_2)).$$ -/)]
theorem theorem_6_alt {x₀ x₁ : ℝ} (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) :
  Eπ x ≤ εθ_num x₁ * (1 + μ_num_2 b εθ_num x₀ x₁) :=
  sorry


@[blueprint
  "fks2-corollary-8"
  (title := "FKS2 Corollary 8")
  (statement := /--
  Let $\{b'_i\}_{i=1}^M$ be a set of finite subdivisions of $[\log(x_1),\infty)$, with
  $b'_1 = \log(x_1)$ and $b'_M = \infty$. Define
  $$ \varepsilon_{\pi, num}(x_1) :=
    \max_{1 \leq i \leq M-1}\varepsilon_{\pi, num}(\exp(b'_i), \exp(b'_{i+1})).$$
  Then $E_\pi(x) \leq \varepsilon_{\pi,num}(x_1)$ for all $x \geq x_1$.
  -/)
  (latexEnv := "corollary")]
theorem corollary_8 {x₁ : ℝ} (hx₁ : x₁ ≥ 14)
    {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (h_b_start : b' 0 = log x₁)
    (h_b_end : b' (Fin.last M) = ⊤)
    (εθ_num : ℝ → ℝ)
    (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx : x ≥ x₁) :
    Eπ x ≤ iSup (fun i : Finset.Iio (Fin.last M) ↦
      επ_num (fun j : Fin (i.val.val+1) ↦ (b' ⟨ j.val, by grind ⟩).toReal)
        εθ_num x₁ (exp (b' i.val).toReal)
        (if (i+1) = Fin.last M then ⊤ else exp (b' (i+1)).toReal)) :=
  sorry

@[blueprint
  "fks2-corollary-21"
  (title := "FKS2 Corollary 21")
  (statement := /--
  Let $B \geq \max(\frac{3}{2}, 1 + \frac{C^2}{16R})$.  Let $x_0, x_1 > 0$ with
  $x_1 \geq \max(x_0, \exp( (1 + \frac{C}{2\sqrt{R}})^2))$. If $E_\psi$ satisfies an admissible
  classical bound with parameters $A_\psi,B,C,R,x_0$, then $E_\pi$ satisfies an admissible
  classical bound with $A_\pi, B, C, R, x_1$, where
  $$ A_\pi = (1 + \nu_{asymp}(x_0)) (1 + \mu_{asymp}(x_0, x_1)) A_\psi$$
  for all $x \geq x_0$, where
  $$ |E_\theta(x)| \leq \varepsilon_{\theta,asymp}(x) :=
    A (1 + \mu_{asymp}(x_0,x)) \exp(-C \sqrt{\frac{\log x}{R}})$$
  where
  $$ \nu_{asymp}(x_0) = \frac{1}{A_\psi} (\frac{R}{\log x_0})^B
    \exp(C \sqrt{\frac{\log x_0}{R}}) (a_1 (\log x_0) x_0^{-1/2} + a_2 (\log x_0) x_0^{-2/3})$$
  and
  $$ \mu_{asymp}(x_0,x_1) = \frac{x_0 \log x_1}{\eps_{\theta,asymp}(x_1)x_1 \log x_0}
    |E_\pi(x_0) - E_\theta(x_0)| + \frac{2 D_+(\sqrt{\log x} - \frac{C}{2\sqrt{R}})}
    {\sqrt{\log x_1}}.$$
  -/)
  (latexEnv := "corollary")]
theorem corollary_21
  (Aψ B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hx0 : x₀ > 0)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)))
  (hEψ : Eψ.classicalBound Aψ B C R x₀) :
  let Aθ := Aψ * (1 + ν_asymp Aψ B C R x₀)
  Eπ.classicalBound (Aθ * (1 + (μ_asymp Aθ B C R x₀ x₁))) B C R x₁ :=
  sorry


@[blueprint
  "fks2-corollary-22"
  (title := "FKS2 Corollary 22")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 9.2211 x \sqrt{\log x} \exp(-0.8476 \sqrt{\log x})
  \]
  for all $x \geq 2$.
  -/)
  (latexEnv := "corollary")]
theorem corollary_22 : Eπ.classicalBound 9.2211 1.5 0.8476 1 2 := sorry

def table6 : List (List ℝ) := [[0.000120, 0.25, 1.00, 22.955],
                                 [0.826, 0.25, 1.00, 1.000],
                                 [1.41, 0.50, 1.50, 2.000],
                                 [1.76, 1.00, 1.50, 3.000],
                                 [2.22, 1.50, 1.50, 3.000],
                                 [12.4, 1.50, 1.90, 1.000],
                                 [38.8, 1.50, 1.95, 1.000],
                                 [121.107, 1.50, 2.00, 1.000],
                                 [6.60, 2.00, 2.00, 3.000]]

@[blueprint
  "fks2-corollary-23"
  (title := "FKS2 Corollary 23")
  (statement := /--
  $A_\pi, B, C, x_0$ as in Table 6 give an admissible asymptotic bound for $E_\pi$ with
  $R = 5.5666305$.
  -/)
  (latexEnv := "corollary")]
theorem corollary_23 (Aπ B C x₀ : ℝ) (h : [Aπ, B, C, x₀] ∈ table6) :
    Eπ.classicalBound Aπ B C 5.5666305 x₀ := sorry

noncomputable def table7 : List ((ℝ → ℝ) × Set ℝ) :=
  [ (fun x ↦ 2 * log x * x^(-(1:ℝ)/2), Set.Icc 1 57),
    (fun x ↦ (log x)^(3/2) * x^(-(1:ℝ)/2), Set.Icc 1 65.65),
    (fun x ↦ 8 * π * (log x)^2 * x^(-(1:ℝ)/2), Set.Icc 8 60.8),
    (fun x ↦ (log x)^2 * x^(-(1:ℝ)/2), Set.Icc 1 70.6),
    (fun x ↦ (log x)^3 * x^(-(1:ℝ)/2), Set.Icc 1 80),
    (fun x ↦ x^(-(1:ℝ)/3), Set.Icc 1 80.55),
    (fun x ↦ x^(-(1:ℝ)/4), Set.Icc 1 107.6),
    (fun x ↦ x^(-(1:ℝ)/5), Set.Icc 1 134.8),
    (fun x ↦ x^(-(1:ℝ)/10), Set.Icc 1 270.8),
    (fun x ↦ x^(-(1:ℝ)/50), Set.Icc 1 1358.6),
    (fun x ↦ x^(-(1:ℝ)/100), Set.Icc 1 3757.6)
  ]

@[blueprint
  "fks2-corollary-24"
  (title := "FKS2 Corollary 24")
  (statement := /--
  We have the bounds $E_\pi(x) \leq B(x)$, where
  $B(x)$ is given by Table 7.
  -/)
  (latexEnv := "corollary")]
theorem corollary_24 (B : ℝ → ℝ) (I : Set ℝ) (h : (B, I) ∈ table7) :
    ∀ x, log x ∈ I → Eπ x ≤ B x := sorry

@[blueprint
  "fks2-corollary-26"
  (title := "FKS2 Corollary 26")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 0.4298 \frac{x}{\log x}
  \]
  for all $x \geq 2$.
  -/)
  (latexEnv := "corollary")]
theorem corollary_26 : Eπ.bound 0.4298 2 := sorry

end FKS2
