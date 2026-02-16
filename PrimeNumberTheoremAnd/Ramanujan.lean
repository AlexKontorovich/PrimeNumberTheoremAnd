import PrimeNumberTheoremAnd.Defs


blueprint_comment /--
\section{Ramanujan's inequality}\label{ramanujan-sec}

Use of prime number theorems to establish Ramanujan's inequality
$$\pi(x)^2 < \frac{e x}{\log x} \pi\Big(\frac{x}{e}\Big)$$
for sufficiently large $x$, following \cite{dudek-platt}.
-/

namespace Ramanujan


open Real Set MeasureTheory intervalIntegral Chebyshev

noncomputable def ε (M x : ℝ) : ℝ := 72 + 2 * M + (2 * M + 132) / log x + (4 * M + 288) / (log x)^2 + (12 * M + 576) / (log x)^3 + (48 * M) / (log x)^4 + (M^2) / (log x)^5

noncomputable def ε' (m x : ℝ) : ℝ := 206 + m + 364 / log x + 381 / (log x)^2 + 238 / (log x)^3 + 97 / (log x)^4 + 30 / (log x)^5 + 8 / (log x)^6

noncomputable def x' (m M x : ℝ) : ℝ := exp (ε M x - ε' m x)

@[blueprint
  "ramanujan-criterion-1"
  (title := "Criterion for Ramanujan's inequality, substep 1")
  (statement := /--
Let $M_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$
Then for $x > x_a$ we have
\begin{equation} \label{pipi}
\pi^2(x)  <  x^2 \Big\{ \frac{1}{\log^2 x}+ \frac{2}{\log^3 x}+ \frac{5}{\log^4 x}+ \frac{16}{\log^5 x}+ \frac{64}{\log^6 x} + \frac{\epsilon_{M_a}(x)}{\log^7 x} \Big\}
\end{equation}
%
where
$$\epsilon_{M_a} (x) = 72 + 2 M_a + \frac{2M_a+132}{\log x} + \frac{4M_a+288}{\log^2 x} + \frac{12 M_a+576}{\log^3 x}+\frac{48M_a}{\log^4 x} + \frac{M_a^2}{\log^5 x}.$$
-/)
  (proof := /-- Direct calculation -/)
  (latexEnv := "sublemma")
  (discussion := 983)]
theorem sq_pi_lt (M_a x_a : ℝ) (hupper : ∀ x > x_a, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) (hM_a : M_a > 0) :
    ∀ x > x_a, pi x ^ 2 < x ^ 2 * (∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) + ε M_a x / log x ^ 7) := by
    sorry

@[blueprint
  "ramanujan-criterion-2"
  (title := "Criterion for Ramanujan's inequality, substep 2")
  (statement := /--
Let $m_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$\pi(x) > x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{m_a x}{\log^6 x}.$$
Then for $x > e x_a$ we have
$$\frac{ex}{\log x} \pi \Big(\frac{x}{e} \Big) > x^2 \Big\{ \frac{1}{\log^2 x}+ \frac{2}{\log^3 x}+ \frac{5}{\log^4 x}+ \frac{16}{\log^5 x}+ \frac{64}{\log^6 x} + \frac{\epsilon'_{m_a}(x)}{\log^7 x} \Big\},$$
where
$$\epsilon'_{m_a}(x) = 206+m_a+\frac{364}{\log x} + \frac{381}{\log^2 x}+\frac{238}{\log^3 x} + \frac{97}{\log^4 x} + \frac{30}{\log^5 x} + \frac{8}{\log^6 x}.$$
-/)
  (proof := /-- We have
$$\frac{ex}{\log x} \pi \Big(\frac{x}{e} \Big) > \frac{x^2}{\log x} \Big( \sum_{k=0}^{4} \frac{k!}{(\log x - 1)^{k+1}}\Big) + \frac{m_a x}{(\log x-1)^{6}}$$
Substituting
\begin{eqnarray*}
\frac{1}{(\log x - 1)^{k+1}} & = & \frac{1}{\log^{k+1} x} \Big(1+ \frac{1}{\log x} + \frac{1}{\log^2 x} + \frac{1}{\log^3 x} + \cdots \Big)^{k+1} \\ \\
& > & \frac{1}{\log^{k+1} x} \Big(1+ \frac{1}{\log x}+ \cdots + \frac{1}{\log^{5-k} x} \Big)^{k+1}
\end{eqnarray*}
we obtain the claim.
  -/)
  (latexEnv := "sublemma")
  (discussion := 984)]
theorem ex_pi_gt (m_a x_a : ℝ) (hlower : ∀ x > x_a, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) < pi x) :
    ∀ x > exp 1 * x_a, exp 1 * x / log x * pi (x / exp 1) > x ^ 2 * (∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) + ε' m_a x / log x ^ 7) := by
    sorry

@[blueprint
  "ramanujan-criterion"
  (title := "Criterion for Ramanujan's inequality")
  (statement := /-- \cite[Lemma 2.1]{dudek-platt}
Let $m_a, M_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have

$$ x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+ \frac{m_a x}{\log^6 x} < \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$
%
Then Ramanujan's inequality is true if

$$x > \max( e x_{a},x_{a}' )$$
where $x'_a := \exp( \epsilon_{M_a} (x_{a}) - \epsilon'_{m_a} (x_{a}) )$.
 -/)
  (proof := /-- Combine the previous two sublemmas.
 -/)
  (latexEnv := "proposition")
  (discussion := 985)]
theorem criterion (m_a M_a x_a : ℝ)
  (hlower : ∀ x > x_a, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) < pi x)
  (hupper : ∀ x > x_a, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) :
    ∀ x > max (exp 1 * x_a) (x' m_a M_a x_a), pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1) := by
  sorry

/-- Integration by parts formula for `Li(x)`. -/
lemma Li_eq_sub_add_integral (x : ℝ) (hx : 2 ≤ x) :
    Li x = x / log x - 2 / log 2 + ∫ t in Icc 2 x, 1 / log t ^ 2 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    Li, intervalIntegral.integral_eq_sub_of_hasDerivAt]
  rotate_right
  · use fun t ↦ t / log t + ∫ u in (2 : ℝ)..t, 1 / log u ^ 2
  · norm_num; ring
  · intro t ht
    have ht' := Set.mem_Icc.mp (by simpa [hx] using ht)
    have h_ftc : HasDerivAt (fun t ↦ ∫ u in (2 : ℝ)..t, 1 / log u ^ 2) (1 / log t ^ 2) t := by
      apply_rules [intervalIntegral.integral_hasDerivAt_right]
      · apply_rules [ContinuousOn.intervalIntegrable]
        exact continuousOn_of_forall_continuousAt fun u hu ↦
          ContinuousAt.div continuousAt_const (ContinuousAt.pow
            (continuousAt_log (by cases Set.mem_uIcc.mp hu <;> linarith [ht'])) _)
              (ne_of_gt (sq_pos_of_pos (log_pos (by cases Set.mem_uIcc.mp hu <;> linarith [ht']))))
      · exact (measurable_const.div (measurable_log.pow_const _)).stronglyMeasurable.stronglyMeasurableAtFilter
      · exact ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (continuousAt_log (by cases Set.mem_uIcc.mp ht <;> linarith)) _)
            (ne_of_gt (sq_pos_of_pos (log_pos (by cases Set.mem_uIcc.mp ht <;> linarith))))
    convert HasDerivAt.add
      (HasDerivAt.div (hasDerivAt_id t) (hasDerivAt_log (show t ≠ 0 by cases Set.mem_uIcc.mp ht <;> linarith))
        (ne_of_gt (log_pos (show t > 1 by cases Set.mem_uIcc.mp ht <;> linarith))))
      h_ftc using 1 ; ring_nf
    by_cases h : t = 0 <;> simp [sq, mul_assoc, h]
    by_cases h' : log t = 0 <;> aesop
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt fun t ht ↦
      ContinuousAt.div continuousAt_const (continuousAt_log
        (by linarith [Set.mem_Icc.mp (by simpa [hx] using ht)]))
          (ne_of_gt (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hx] using ht)]))))

@[blueprint
  "pi-error-identity"
  (title := "Integral identity for pi - Li")
  (statement := /-- If $x \geq 2$, then
$$\pi(x) - \textrm{Li}(x) = \frac{\theta(x) - x}{\log x} + \frac{2}{\log 2} + \int_{2}^{x} \frac{\theta(t) -t}{t \log^{2}t}\, dt.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-417} and the fundamental theorem of calculus. -/)
  (latexEnv := "lemma")
  (discussion := 986)]
theorem pi_error_identity (x : ℝ) (hx : 2 ≤ x) :
    pi x - Li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
  have h_integral : ∫ t in Set.Icc 2 x, (θ t - t) / (t * log t ^ 2) =
      (∫ t in Set.Icc 2 x, θ t / (t * log t ^ 2)) -
      (∫ t in Set.Icc 2 x, 1 / log t ^ 2) := by
    rw [← MeasureTheory.integral_sub]
    · exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht ↦ by
        rw [sub_div, div_eq_mul_inv]; ring_nf
        norm_num [show t ≠ 0 by linarith [ht.1], show log t ≠ 0 from ne_of_gt <| log_pos <| by linarith [ht.1]]
    · have h_bound : ∀ t ∈ Set.Icc 2 x, |θ t / (t * log t ^ 2)| ≤ log 4 / log t ^ 2 := by
        intro t ht
        have : θ t ≤ log 4 * t := Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
        rw [abs_of_nonneg (div_nonneg (by exact Finset.sum_nonneg fun _ _ ↦
              log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop)
            (mul_nonneg (by linarith [ht.1]) (sq_nonneg _))), div_le_div_iff₀] <;>
          nlinarith [ht.1, ht.2, log_pos <| show 1 < t by linarith [ht.1],
            log_le_sub_one_of_pos <| show 0 < t by linarith [ht.1],
            show 0 ≤ θ t from Finset.sum_nonneg fun _ _ ↦
              log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop]
      refine MeasureTheory.Integrable.mono' (g := fun t ↦ log 4 / log t ^ 2) ?_ ?_ ?_
      · exact ContinuousOn.integrableOn_Icc (continuousOn_of_forall_continuousAt fun t ht ↦
          ContinuousAt.div continuousAt_const
            (ContinuousAt.pow (continuousAt_log (by linarith [ht.1])) _)
              (ne_of_gt (sq_pos_of_pos (log_pos (by linarith [ht.1])))))
      · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
        · have : Measurable (fun t : ℕ ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 0 t), log p) :=
            measurable_from_nat
          exact this.comp measurable_id'.nat_floor
        · exact Measurable.inv (measurable_id.mul (measurable_log.pow_const 2))
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht using h_bound t ht
    · exact ContinuousOn.integrableOn_Icc (continuousOn_const.div
        (ContinuousOn.pow (continuousOn_log.mono <| by norm_num) _) fun t ht ↦
        ne_of_gt <| sq_pos_of_pos <| log_pos <| by linarith [ht.1])
  have h_pi : pi x = θ x / log x + ∫ t in Icc 2 x, θ t / (t * log t ^ 2) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
    exact primeCounting_eq_theta_div_log_add_integral hx
  rw [h_integral, h_pi, Li_eq_sub_add_integral x hx]; ring

@[blueprint
  "ramanujan-pi-upper"
  (title := "Upper bound for pi")
  (statement := /-- Suppose that for $x \geq 2$ we have $|\theta(x)-x|\log^{5} x\leq x a(x)$. Then
$$
\pi(x)\leq \frac{x}{\log x} +a(x)\frac{x}{\log^6 x}+\int_2^x\frac{d t}{\log^2 t}+\int_2^x\frac{a(t)}{\log^7 t}\ dt.
$$ (cf. \cite[\S 5]{PT2021})
-/)
  (proof := /-- Follows from Lemma \ref{pi-error-identity} and the triangle inequality. -/)
  (latexEnv := "sublemma")
  (discussion := 987)]
theorem pi_upper (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, abs (θ x - x) * log x ^ 5 ≤ x * a x) (x : ℝ) (hx : 2 ≤ x) :
    pi x ≤ x / log x + a x * x / log x ^ 6 + ∫ t in Set.Icc 2 x, 1 / log t ^ 2 + ∫ t in Set.Icc 2 x, a t / log t ^ 7 := by
    sorry

@[blueprint
  "ramanujan-pi-lower"
  (title := "Lower bound for pi")
  (statement := /-- Suppose that for $x \geq 2$ we have $|\theta(x)-x|\log^{5} x\leq x a(x)$. Then
$$
\pi(x)\geq \frac{x}{\log x} -a(x)\frac{x}{\log^6 x}+\int_2^x\frac{d t}{\log^2 t}-\int_2^x\frac{a(t)}{\log^7 t}\ dt.
$$ (cf. \cite[\S 5]{PT2021})
-/)
  (proof := /-- Follows from Lemma \ref{pi-error-identity} and the triangle inequality. -/)
  (latexEnv := "sublemma")
  (discussion := 989)]
theorem pi_lower (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, abs (θ x - x) * log x ^ 5 ≤ x * a x) (x : ℝ) (hx : 2 ≤ x) :
    pi x ≥ x / log x - a x * x / log x ^ 6 + ∫ t in Set.Icc 2 x, 1 / log t ^ 2 - ∫ t in Set.Icc 2 x, a t / log t ^ 7 := by
    sorry

@[blueprint
  "log-7-int-bound"
  (title := "Bound for integral of an inverse power of log")
  (statement := /-- For $x \geq 2$ we have
$$\int_2^x \frac{dt}{\log^7 t} < \frac{x}{\log^7 x} + 7 \Big( \frac{\sqrt{x}}{\log^8 2} + \frac{2^8 x}{\log^8 x} \Big).$$-/)
  (proof := /-- Integrate by parts to write the left-hand side as $\frac{x}{\log^7 x} - \frac{2}{\log^7 2} + 7 \int_2^x \frac{t}{\log^8 t} dt$.  Discard the middle term.  For the final term, split between $\int_2^{\sqrt{x}}$ and $\int_{\sqrt{x}}^x$.  For the first, use the bound $\int_2^{\sqrt{x}} \frac{t}{\log^8 t} dt < \int_2^{\sqrt{x}} \frac{t}{\log^8 2} dt$, and for the second, use the bound $\int_{\sqrt{x}}^x \frac{t}{\log^8 t} dt < \int_{\sqrt{x}}^x \frac{t}{\log^8 x} dt$.-/)
  (latexEnv := "lemma")
  (discussion := 988)]
theorem log_7_int_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 < x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8) := by
    sorry

@[blueprint
  "ramanujan-pibound-1"
  (title := "Error estimate for theta, range 1")
  (statement := /-- For $2 < x \leq 599$ we have
$$E_\theta(x) \leq 1 - \frac{\log 3}{3}.$$-/)
  (proof := /-- This can be verified by direct computation, perhaps breaking $x$ up into intervals.  In \cite{PT2021} the bound of $(2 - \log 2)/2$ is claimed, but this is actually false for $2 < x < 3$. -/)
  (latexEnv := "sublemma")
  (discussion := 990)]
theorem pi_bound_1 (x : ℝ) (hx : x ∈ Set.Ico 2 599) :
    Eθ x ≤ 1 - log 3 / 3 := by
    sorry

@[blueprint
  "ramanujan-pibound-2"
  (title := "Error estimate for theta, range 2")
  (statement := /-- For $599 < x \leq \exp(58)$ we have
$$E_\theta(x) \leq \frac{\log^2 x}{8\pi\sqrt{x}}.$$-/)
  (proof := /-- This is \cite[Lemma 6]{PT2021}. -/)
  (latexEnv := "sublemma")]
theorem pi_bound_2 (x : ℝ) (hx : x ∈ Set.Ico 599 (exp 58)) :
    Eθ x ≤ log x ^ 2 / (8 * π * sqrt x) := by
    sorry

@[blueprint
  "ramanujan-pibound-3"
  (title := "Error estimate for theta, range 3")
  (statement := /-- For $\exp(58) < x < \exp(1169)$ we have
$$E_\theta(x) \leq \sqrt\frac{8}{17\pi}\left(\frac{\log x}{6.455}\right)^{\frac{1}{4}}\exp\left(-\sqrt{\frac{\log x}{6.455}}\right).$$-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")
  (discussion := 991)]
theorem pi_bound_3 (x : ℝ) (hx : x ∈ Set.Ico (exp 58) (exp 1169)) :
    Eθ x ≤ sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4) * exp (-sqrt (log x / 6.455)) := by
    sorry

@[blueprint
  "ramanujan-pibound-4"
  (title := "Error estimate for theta, range 4")
  (statement := /-- For $\exp(1169) \leq x < \exp(2000)$ we have
$$E_\theta(x) \leq 462.0\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")
  (discussion := 992)]
theorem pi_bound_4 (x : ℝ) (hx : x ∈ Set.Ico (exp 1169) (exp 2000)) :
    Eθ x ≤ 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
    sorry

@[blueprint
  "ramanujan-pibound-5"
  (title := "Error estimate for theta, range 5")
  (statement := /-- For $\exp(2000) \leq x < \exp(3000)$ we have
$$E_\theta(x) \leq 411.5\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")
  (discussion := 993)]
theorem pi_bound_5 (x : ℝ) (hx : x ∈ Set.Ico (exp 2000) (exp 3000)) :
    Eθ x ≤ 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
    sorry

noncomputable def a (x : ℝ) : ℝ := (log x)^5 * (
  if x ∈ Set.Ico 2 599 then 1 - log 2 / 3
  else if x ∈ Set.Ico 599 (exp 58) then log x ^ 2 / (8 * π * sqrt x)
  else if x ∈ Set.Ico (exp 58) (exp 1169) then sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4) * exp (-sqrt (log x / 6.455))
  else if x ∈ Set.Ico (exp 1169) (exp 2000) then 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  else if x ∈ Set.Ico (exp 2000) (exp 3000) then 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  else 379.7 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)))

@[blueprint
  "pt_eq_18"
  (title := "Equation (18) of Platt-Trudgian")
  (statement := /-- For $x \geq 2$ we have
$$E_\theta(x) \leq a(x).$$-/)
  (proof := /-- This follows from the previous five sublemmas. -/)
  (latexEnv := "proposition")
  (discussion := 994)]
theorem pi_bound (x : ℝ) (hx : 2 ≤ x) :
    Eθ x ≤ a x := by
    sorry

noncomputable def xₐ : ℝ := exp 3914

@[blueprint
  "a-mono"
  (title := "Monotonicity of a(x)")
  (statement := /-- The function $a(x)$ is nonincreasing for $x \geq x_a$. -/)
  (proof := /-- Follows from Lemma \ref{admissible-bound-monotone}. -/)
  (latexEnv := "lemma")
  (discussion := 995)]
theorem a_mono : AntitoneOn a (Set.Ici xₐ) := by
    sorry

noncomputable def C₁ : ℝ := log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7

noncomputable def C₂ : ℝ := log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 - a t) / log t ^ 7

noncomputable def C₃ : ℝ := 2 * log xₐ ^ 6 / xₐ * ∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)

noncomputable def Mₐ : ℝ := 120 + a xₐ + C₁ + (720 + a xₐ) * (1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2 + 7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8))

noncomputable def mₐ : ℝ := 120 - a xₐ - (C₂ + C₃) - a xₐ * (1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2 + 7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8))

noncomputable def εMₐ : ℝ := 72 + 2 * Mₐ + (2 * Mₐ + 132) / log xₐ + (4 * Mₐ + 288) / log xₐ ^ 2 + (12 * Mₐ + 576) / log xₐ ^ 3 + (48 * Mₐ) / log xₐ ^ 4 + (Mₐ ^ 2) / log xₐ ^ 5

noncomputable def εmₐ : ℝ := 206 + mₐ + 364 / log xₐ + 381 / log xₐ ^ 2 + 238 / log xₐ ^ 3 + 97 / log xₐ ^ 4 + 30 / log xₐ ^ 5 + 8 / log xₐ ^ 6

@[blueprint
  "pi-upper-specific"
  (title := "Specific upper bound on pi")
  (statement := /-- For $x \geq x_a$, $$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$. -/)
  (proof := /-- This follows from the previous lemmas and calculations, including Lemma \ref{log-7-int-bound}. -/)
  (latexEnv := "lemma")
  (discussion := 996)]
theorem pi_upper_specific : ∀ x > xₐ, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (Mₐ * x / log x ^ 6) := by
    sorry

@[blueprint
  "pi-lower-specific"
  (title := "Specific lower bound on pi")
  (statement := /-- For $x \geq x_a$, $$ \pi(x) > x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{m_a x}{\log^6 x}.$$. -/)
  (proof := /-- This follows from the previous lemmas and calculations, including Lemma \ref{log-7-int-bound}. -/)
  (latexEnv := "lemma")
  (discussion := 997)]
theorem pi_lower_specific : ∀ x > xₐ, pi x > x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (mₐ * x / log x ^ 6) := by
    sorry

@[blueprint
  "epsilon-bound"
  (title := "Bound for εMₐ - εmₐ")
  (statement := /-- We have $\epsilon_{M_a} - \epsilon'_{m_a} < 0$. -/)
  (proof := /-- This is a direct calculation. -/)
  (latexEnv := "lemma")
  (discussion := 998)]
theorem epsilon_bound : εMₐ - εmₐ < 0 := by
    sorry

@[blueprint
  "ramanujan-final"
  (title := "Ramanujan's inequality")
  (statement := /-- For $x \geq e x_a$ we have $\pi(x)^2 < \frac{e x}{\log x} \pi\Big(\frac{x}{e}\Big)$. -/)
  (proof := /-- \cite[Theorem 2]{PT2021} This follows from the previous lemmas and calculations, including the criterion for Ramanujan's inequality. -/)
  (latexEnv := "theorem")
  (discussion := 999)]
theorem ramanujan_final : ∀ x > exp 1 * xₐ, pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1) := by
    sorry



end Ramanujan
