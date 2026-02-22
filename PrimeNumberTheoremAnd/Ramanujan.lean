import PrimeNumberTheoremAnd.Defs
import LeanCert.Engine.ChebyshevTheta

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

theorem integrable_theta (x : ℝ) :
    IntegrableOn (fun t ↦ (θ t - t) / (t * log t ^ 2)) (Icc 2 x) volume := by
  have l0 : ContinuousOn (fun t ↦ (t * log t ^ 2)⁻¹) (Set.Icc 2 x) := by
    refine ContinuousOn.inv₀ (continuousOn_id.mul (ContinuousOn.pow (ContinuousOn.log
      continuousOn_id fun y hy ↦ ?_) 2)) fun y hy ↦ ?_
    repeat simp_all; grind
  have l1 : IntegrableOn (fun t ↦ θ t / (t * log t ^ 2)) (Icc 2 x) volume :=
    (theta_mono.monotoneOn _).integrableOn_isCompact isCompact_Icc |>.mul_continuousOn l0
    isCompact_Icc
  have l2 : IntegrableOn (fun t ↦ t / (t * log t ^ 2)) (Icc 2 x) volume :=
    monotoneOn_id.integrableOn_isCompact isCompact_Icc |>.mul_continuousOn l0 isCompact_Icc
  simpa [div_sub_div_same] using l1.sub' l2

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
theorem pi_upper (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, |θ x - x| * log x ^ 5 ≤ x * a x) (x : ℝ)
    (ha : IntegrableOn (fun t ↦ a t / log t ^ 7) (Icc 2 x) volume)
    (hx : 2 ≤ x) :
    pi x ≤ x / log x + a x * x / log x ^ 6 + (∫ t in Icc 2 x, 1 / log t ^ 2)
    + ∫ t in Icc 2 x, a t / log t ^ 7 := calc
  _ = pi x - Li x + Li x := by ring
  _ = x / log x + (θ x - x) / log x + (∫ (t : ℝ) in Icc 2 x, 1 / log t ^ 2) +
     ∫ (t : ℝ) in Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
     rw [pi_error_identity x hx, Li_eq_sub_add_integral x hx]; ring
  _ ≤ _ := by
    gcongr ?_ + ?_ + ?_ + ?_
    · calc
      _ = (θ x - x) * log x ^ 5 / log x ^ 6 := by field_simp
      _ ≤ |θ x - x| * log x ^ 5 / log x ^ 6 := by
        gcongr
        · exact pow_nonneg (log_nonneg (by grind)) 5
        · exact le_abs_self _
      _ ≤ _ := by grw [htheta x hx, mul_comm]
    · refine setIntegral_mono_on (integrable_theta x) ha measurableSet_Icc (fun t ht => ?_)
      calc
      _ = (θ t - t) * log t ^ 5 / (t * log t ^ 7) := by field_simp
      _ ≤ |θ t - t| * log t ^ 5 / (t * log t ^ 7) := by
        gcongr
        · exact mul_nonneg (by grind) (pow_nonneg (log_nonneg (by grind)) 7)
        · exact pow_nonneg (log_nonneg (by grind)) 5
        · exact le_abs_self _
      _ ≤ _ := by
        grw [htheta t ht.1, mul_comm]
        · field_simp (disch := grind); rfl
        · exact mul_nonneg (by grind) (pow_nonneg (log_nonneg (by grind)) 7)

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
theorem pi_lower (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, |θ x - x| * log x ^ 5 ≤ x * a x) (x : ℝ)
    (ha : IntegrableOn (fun t ↦ a t / log t ^ 7) (Icc 2 x) volume)
    (hx : 2 ≤ x) :
    pi x ≥ x / log x - a x * x / log x ^ 6 + (∫ t in Icc 2 x, 1 / log t ^ 2) - ∫ t in Icc 2 x, a t / log t ^ 7 := by
  have h1 : (θ x - x) / log x ≥ - (x * a x / log x ^ 6) := by
    have hlog_pos : 0 < log x := log_pos (by linarith)
    have h1a : (θ x - x) / log x ≥ - (|θ x - x| / log x) := by
      have h1a1 : - |θ x - x| ≤ (θ x - x) := neg_abs_le (θ x - x)
      have h : (- |θ x - x|) / log x ≤ (θ x - x) / log x := div_le_div_of_nonneg_right h1a1 hlog_pos.le
      have h' : (- |θ x - x|) / log x = - (|θ x - x| / log x) := by field_simp [hlog_pos.ne']
      rw [h'] at h; exact h.ge
    have h1b : |θ x - x| * log x ^ 5 ≤ x * a x := htheta x hx
    have h1c : |θ x - x| / log x ≤ (x * a x) / log x ^ 6 := by
      have h1c1 : |θ x - x| ≤ (x * a x) / log x ^ 5 := by
        have h1c2 : 0 < log x ^ 5 := by positivity
        calc
          |θ x - x| = (|θ x - x| * log x ^ 5) / log x ^ 5 := by field_simp [hlog_pos.ne']
          _ ≤ (x * a x) / log x ^ 5 := by gcongr
      calc
        |θ x - x| / log x ≤ ((x * a x) / log x ^ 5) / log x := by gcongr
        _ = (x * a x) / log x ^ 6 := by field_simp [pow_succ, hlog_pos.ne']
    have h1d : - (|θ x - x| / log x) ≥ - ((x * a x) / log x ^ 6) := by gcongr
    linarith
  have h_int_abs : IntegrableOn (fun t : ℝ ↦ |(θ t - t) / (t * log t ^ 2)|) (Icc 2 x) volume := integrable_theta x |>.abs
  have h_neg_abs_int : IntegrableOn (fun t : ℝ ↦ - |(θ t - t) / (t * log t ^ 2)|) (Icc 2 x) volume := h_int_abs.neg
  have h2a : ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) ≥ - (∫ t in Icc 2 x, |(θ t - t) / (t * log t ^ 2)|) := by
    have h2a1 : ∀ t ∈ Icc 2 x, - |(θ t - t) / (t * log t ^ 2)| ≤ (θ t - t) / (t * log t ^ 2) := fun t _ => neg_abs_le _
    have h2a2 : ∫ t in Icc 2 x, (- |(θ t - t) / (t * log t ^ 2)|) ≤ ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) :=
      MeasureTheory.setIntegral_mono_on h_neg_abs_int (integrable_theta x) measurableSet_Icc h2a1
    have h2a3 : ∫ t in Icc 2 x, (- |(θ t - t) / (t * log t ^ 2)|) = - (∫ t in Icc 2 x, |(θ t - t) / (t * log t ^ 2)|) := by rw [MeasureTheory.integral_neg]
    rw [h2a3] at h2a2; exact h2a2.ge
  have h2b : ∫ t in Icc 2 x, |(θ t - t) / (t * log t ^ 2)| ≤ ∫ t in Icc 2 x, a t / log t ^ 7 :=
    MeasureTheory.setIntegral_mono_on h_int_abs ha measurableSet_Icc (fun t ht => by
      have ht2 : 2 ≤ t := ht.1
      have hlog_t_pos : 0 < log t := log_pos (by linarith)
      have h71 : |θ t - t| * log t ^ 5 ≤ t * a t := htheta t ht2
      have h72 : |θ t - t| ≤ (t * a t) / log t ^ 5 := by
        have h : 0 < log t ^ 5 := by positivity
        calc
          |θ t - t| = (|θ t - t| * log t ^ 5) / log t ^ 5 := by field_simp [hlog_t_pos.ne']
          _ ≤ (t * a t) / log t ^ 5 := by gcongr
      have h73 : |(θ t - t) / (t * log t ^ 2)| = |θ t - t| / (t * log t ^ 2) := by
        have h_t_pos : 0 < t := by linarith
        rw [abs_div, abs_of_pos (show 0 < t * log t ^ 2 from by positivity)]
      rw [h73]
      calc
        |θ t - t| / (t * log t ^ 2) ≤ ((t * a t) / log t ^ 5) / (t * log t ^ 2) := by gcongr
        _ = (t * a t) / (t * log t ^ 7) := by field_simp [pow_succ, hlog_t_pos.ne']
        _ = a t / log t ^ 7 := by
          have h_t_pos : 0 < t := by linarith
          field_simp [h_t_pos.ne'])
  have h2c : - (∫ t in Icc 2 x, |(θ t - t) / (t * log t ^ 2)|) ≥ - (∫ t in Icc 2 x, a t / log t ^ 7) := by gcongr
  have h2 : ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) ≥ - (∫ t in Icc 2 x, a t / log t ^ 7) := by linarith [h2a, h2c]
  calc
    pi x = x / log x + (θ x - x) / log x + (∫ t in Icc 2 x, 1 / log t ^ 2) + ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
      have h_eq1 : pi x - Li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) := pi_error_identity x hx
      have h_eq2 : Li x = x / log x - 2 / log 2 + ∫ t in Icc 2 x, 1 / log t ^ 2 := Li_eq_sub_add_integral x hx
      linarith
    _ ≥ x / log x + (- (x * a x / log x ^ 6)) + (∫ t in Icc 2 x, 1 / log t ^ 2) + (- (∫ t in Icc 2 x, a t / log t ^ 7)) := by
      gcongr
    _ = x / log x - a x * x / log x ^ 6 + (∫ t in Icc 2 x, 1 / log t ^ 2) - ∫ t in Icc 2 x, a t / log t ^ 7 := by ring

theorem log_7_IBP (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 =
      x / log x ^ 7 - 2 / log 2 ^ 7 +
        7 * ∫ t in Set.Icc 2 x, 1 / log t ^ 8 := by
  suffices h_ibp : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (log t) ^ 7) = (b / (log b) ^ 7) - (a / (log a) ^ 7) +
        7 * ∫ t in a..b, (1 / (log t) ^ 8) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (log t) ^ 7) t =
        1 / (log t) ^ 7 - 7 * (1 / (log t) ^ 8) := by
    intro t ht
    norm_num [differentiableAt_log, ne_of_gt (show 0 < log t from log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]; ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (log t) ^ 7) t =
      (b / (log b) ^ 7) - (a / (log a) ^ 7) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun x hx ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (differentiableAt_log
          (by cases Set.mem_uIcc.mp hx <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| log_pos <|
          by cases Set.mem_uIcc.mp hx <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ (n : ℕ), ∀ y ∈ Set.Icc a b, log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| log_pos <| by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub] <;> norm_num; ring
  · exact ContinuousOn.intervalIntegrable (by
      exact continuousOn_of_forall_continuousAt fun x hx =>
        ContinuousAt.pow (ContinuousAt.inv₀
          (continuousAt_log (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)]))
          (ne_of_gt (log_pos (by linarith [Set.mem_Icc.mp (by simpa [hab] using hx)])))) _) ..
  · apply_rules [ContinuousOn.intervalIntegrable]
    exact ContinuousOn.mul continuousOn_const <|
      ContinuousOn.inv₀ (ContinuousOn.pow
        (continuousOn_log.mono <| by
          intro x hx; cases Set.mem_uIcc.mp hx <;> norm_num <;> linarith) _)
        fun x hx ↦ ne_of_gt <| pow_pos (log_pos <| by
          cases Set.mem_uIcc.mp hx <;> linarith) _

theorem log_8_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 8 <
      sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8 := by
  by_cases h : x < 4
  · refine lt_of_le_of_lt (MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Icc fun t ht =>
      one_div_le_one_div_of_le ?_ <| pow_le_pow_left₀ (log_nonneg <| by linarith [ht.1])
        (log_le_log (by linarith [ht.1]) ht.1) 8) ?_
    · exact ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
        (continuousOn_log.mono <| by norm_num) _) fun t ht ↦ pow_ne_zero _ <| ne_of_gt <|
        log_pos <| by linarith [ht.1])
    · norm_num
    · positivity
    · norm_num [← div_eq_mul_inv]
      exact lt_add_of_le_of_pos (by
        gcongr; cases max_cases (x - 2) 0 <;>
          nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)]) (by
        exact div_pos (by positivity) (pow_pos (log_pos (by linarith)) _))
  · have h_split : ∫ t in Set.Icc 2 x, 1 / log t ^ 8 =
        (∫ t in Set.Icc 2 (sqrt x), 1 / log t ^ 8) +
          (∫ t in Set.Icc (sqrt x) x, 1 / log t ^ 8) := by
      norm_num [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le, sqrt_le_iff, hx]
      rw [← intervalIntegral.integral_of_le (by
            nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)]),
        ← intervalIntegral.integral_of_le (by
          nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)]),
        intervalIntegral.integral_add_adjacent_intervals]
        <;> apply_rules [ContinuousOn.intervalIntegrable]
      · exact continuousOn_of_forall_continuousAt fun y hy =>
          ContinuousAt.inv₀ (ContinuousAt.pow (continuousAt_log (by
            cases Set.mem_uIcc.mp hy <;>
              nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])) _)
            (pow_ne_zero _ <| ne_of_gt <| log_pos <| by
              cases Set.mem_uIcc.mp hy <;>
                nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])
      · exact continuousOn_of_forall_continuousAt fun y hy =>
          ContinuousAt.inv₀ (ContinuousAt.pow (continuousAt_log (by
            cases Set.mem_uIcc.mp hy <;>
              nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])) _)
            (pow_ne_zero _ <| ne_of_gt <| log_pos <| by
              cases Set.mem_uIcc.mp hy <;>
                nlinarith [sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])
    have h_first : ∫ t in Set.Icc 2 (sqrt x), 1 / log t ^ 8 ≤
        sqrt x / (log 2) ^ 8 := by
      have h_mono : ∫ t in Set.Icc 2 (sqrt x), 1 / log t ^ 8 ≤
          ∫ t in Set.Icc 2 (sqrt x), 1 / log 2 ^ 8 := by
        refine MeasureTheory.setIntegral_mono_on ?_ ?_ ?_ ?_ <;> norm_num
        · exact ContinuousOn.integrableOn_Icc (continuousOn_of_forall_continuousAt fun t ht =>
            ContinuousAt.inv₀
              ((Real.continuousAt_log (show t ≠ 0 from ne_of_gt (by linarith [ht.1]))).pow _)
              (ne_of_gt (pow_pos (Real.log_pos (show 1 < t by linarith [ht.1])) _)))
        · exact fun t ht₁ ht₂ ↦ inv_anti₀ (pow_pos (log_pos (by linarith)) _)
            (pow_le_pow_left₀ (log_nonneg (by linarith)) (log_le_log (by linarith) (by linarith)) _)
      refine le_trans h_mono ?_; norm_num
      rw [max_eq_left (sub_nonneg.mpr <| le_sqrt_of_sq_le <| by linarith)]
      ring_nf; norm_num; positivity
    have h_second : ∫ t in Set.Icc (sqrt x) x, 1 / log t ^ 8 ≤
        (x - sqrt x) * (2 ^ 8 / (log x) ^ 8) := by
      have hbd : ∀ t ∈ Set.Icc (sqrt x) x,
          1 / log t ^ 8 ≤ 2 ^ 8 / (log x) ^ 8 := by
        intro t ht
        have hlog_half : log t ≥ log (sqrt x) := log_le_log (by positivity) ht.1
        rw [log_sqrt (by positivity)] at hlog_half
        rw [div_le_div_iff₀] <;>
          nlinarith [pow_pos (log_pos (by linarith : 1 < x)) 8,
            pow_le_pow_left₀ (by linarith [log_pos (by linarith : 1 < x)]) hlog_half 8]
      convert MeasureTheory.setIntegral_mono_on _ _ _ hbd <;> norm_num
      · exact Or.inl <| sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
      · exact ContinuousOn.integrableOn_Icc (continuousOn_of_forall_continuousAt fun t ht =>
          ContinuousAt.inv₀ (ContinuousAt.pow (continuousAt_log (by
            nlinarith [ht.1, sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)])) _)
            (pow_ne_zero _ <| ne_of_gt <| log_pos <| by
              nlinarith [ht.1, sqrt_nonneg x, sq_sqrt (show 0 ≤ x by linarith)]))
    refine h_split.symm ▸ lt_of_le_of_lt (add_le_add h_first h_second) ?_
    ring_nf
    nlinarith [show 0 < sqrt x * (log x)⁻¹ ^ 8 by
      exact mul_pos (sqrt_pos.mpr (by linarith))
        (pow_pos (inv_pos.mpr (log_pos (by linarith))) _)]

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
  rw [log_7_IBP x hx]; linarith [log_8_bound x hx, show 0 ≤ 2 / Real.log 2 ^ 7 by positivity]

-- Native-decide lemma for the computational [3, 599) range
set_option linter.style.nativeDecide false in
open LeanCert.Engine.ChebyshevTheta in
private theorem allThetaChecks_3_599 :
    checkAllThetaRelErrorReal 3 599 (768 / 1000) 20 = true := by native_decide

@[blueprint
  "ramanujan-pibound-1"
  (title := "Error estimate for theta, range 1")
  (statement := /-- For $2 \leq x < 599$ we have
$$E_\theta(x) \leq 1 - \frac{\log 2}{3}.$$-/)
  (proof := /-- For $x \in [2, 3)$ we have $\theta(x) = \log 2$, so
$E_\theta(x) = 1 - \log 2 / x < 1 - \log 2 / 3$ since $x < 3$.
For $x \in [3, 599)$ we use the LeanCert ChebyshevTheta engine:
\texttt{checkAllThetaRelErrorReal 3 599 (768/1000) 20} via \texttt{native\_decide}
gives $|\theta(x) - x| \leq 0.768 x$, hence $E_\theta(x) \leq 0.768 \leq 1 - \log 2 / 3$. -/)
  (latexEnv := "sublemma")
  (discussion := 990)]
theorem pi_bound_1 (x : ℝ) (hx : x ∈ Set.Ico 2 599) :
    Eθ x ≤ 1 - log 2 / 3 := by
  obtain ⟨hx2, hx599⟩ := hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hnn : (0 : ℝ) ≤ x := by linarith
  unfold Eθ
  rw [div_le_iff₀ hxpos]
  -- Goal: |θ x - x| ≤ (1 - log 2 / 3) * x
  by_cases hx3 : x < 3
  · -- Case x ∈ [2, 3): ⌊x⌋₊ = 2, θ(2) = log 2
    rw [Chebyshev.theta_eq_theta_coe_floor x]
    have hfloor : ⌊x⌋₊ = 2 := by
      apply (Nat.floor_eq_iff hnn).mpr
      exact ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [hfloor]
    -- Now goal involves θ ↑2, need to compute it
    have htheta_two : θ (↑(2 : ℕ) : ℝ) = log 2 := by
      simp [Chebyshev.theta, Finset.sum_filter, Finset.sum_Ioc_succ_top, Nat.prime_two]
    rw [htheta_two]
    -- Goal: |log 2 - x| ≤ (1 - log 2 / 3) * x
    have hlog2_lt_x : log 2 < x := by linarith [log_two_lt_d9]
    rw [abs_of_nonpos (by linarith), neg_sub]
    -- Goal: x - log 2 ≤ (1 - log 2 / 3) * x
    nlinarith [log_two_gt_d9]
  · -- Case x ∈ [3, 599): use computational checker
    push_neg at hx3
    have hfloor_pos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith : 1 ≤ x)
    have hfloor_ge3 : 3 ≤ ⌊x⌋₊ := Nat.le_floor hx3
    have hfloor_lt : ⌊x⌋₊ < 599 := (Nat.floor_lt hnn).mpr (by exact_mod_cast hx599)
    have hfloor_le : ⌊x⌋₊ ≤ 599 := le_of_lt hfloor_lt
    -- Extract pointwise check from the bulk checker
    have hpointwise :=
      LeanCert.Engine.ChebyshevTheta.checkAllThetaRelErrorReal_implies 3 599 (768 / 1000) 20
        allThetaChecks_3_599 ⌊x⌋₊ hfloor_pos hfloor_ge3 hfloor_le
    rw [if_pos hfloor_lt] at hpointwise
    -- Bridge to real-valued bound
    have hxlo : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hnn
    have hxhi : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have habs :=
      LeanCert.Engine.ChebyshevTheta.abs_theta_sub_le_mul_of_checkThetaRelErrorReal
        ⌊x⌋₊ 20 (768 / 1000) (by norm_num) (by norm_num) hpointwise x hxlo hxhi
    -- Chain: |θ x - x| ≤ 0.768 * x ≤ (1 - log 2 / 3) * x
    calc |θ x - x| ≤ ((768 / 1000 : ℚ) : ℝ) * x := habs
      _ ≤ (1 - log 2 / 3) * x := by
          gcongr
          have : (((768 : ℚ) / 1000 : ℚ) : ℝ) = 768 / 1000 := by push_cast; ring
          rw [this]
          linarith [log_two_lt_d9]

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
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hxa3 : xₐ ≥ exp 3000 := by unfold xₐ; exact exp_le_exp.mpr (by norm_num)
  have hx3 := le_trans hxa3 hx; have hy3 := le_trans hxa3 hy
  have neg : ∀ z ≥ exp 3000, ∀ lo hi : ℝ, hi ≤ exp 3000 → ¬(z ∈ Set.Ico lo hi) :=
    fun z hz _ _ hhi h ↦ absurd (Set.mem_Ico.mp h).2 (not_lt.mpr (le_trans hhi hz))
  have h599 : (599 : ℝ) ≤ exp 3000 := by linarith [add_one_le_exp (3000 : ℝ)]
  have h58 := exp_le_exp.mpr (show (58 : ℝ) ≤ 3000 by norm_num)
  have h1169 := exp_le_exp.mpr (show (1169 : ℝ) ≤ 3000 by norm_num)
  have h2000 := exp_le_exp.mpr (show (2000 : ℝ) ≤ 3000 by norm_num)
  have ha_eq : ∀ z ≥ exp 3000, a z = admissible_bound (379.7 * 5.573412 ^ 5) 6.52 1.89 5.573412 z := by
    intro z hz
    have hlog : 0 < log z := log_pos (by linarith [add_one_le_exp (3000 : ℝ)])
    have hdiv : 0 < log z / 5.573412 := by positivity
    unfold a admissible_bound
    simp only [neg z hz _ _ h599, neg z hz _ _ h58, neg z hz _ _ h1169,
      neg z hz _ _ h2000, neg z hz _ _ le_rfl, ite_false, sqrt_eq_rpow]
    have h_pow : (log z) ^ (5 : ℕ) = 5.573412 ^ (5 : ℕ) * (log z / 5.573412) ^ (5 : ℕ) := by
      rw [show log z = 5.573412 * (log z / 5.573412) from by field_simp]; ring
    have h_rpow : (log z / 5.573412) ^ (5 : ℕ) * (log z / 5.573412) ^ (1.52 : ℝ) =
        (log z / 5.573412) ^ (6.52 : ℝ) := by
      rw [← rpow_natCast (log z / 5.573412) 5, ← rpow_add hdiv]; push_cast; norm_num
    rw [h_pow]
    conv_lhs =>
      rw [show ∀ (a b c d e : ℝ), a * b * (c * d * e) = c * a * (b * d) * e from by intros; ring]
    rw [h_rpow]
  change a y ≤ a x
  rw [ha_eq x hx3, ha_eq y hy3]
  exact admissible_bound.mono _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (Set.mem_Ici.mpr (le_trans (show exp (5.573412 * (2 * 6.52 / 1.89) ^ 2) ≤ xₐ from by
      unfold xₐ; exact exp_le_exp.mpr (by norm_num)) hx))
    (Set.mem_Ici.mpr (le_trans (show exp (5.573412 * (2 * 6.52 / 1.89) ^ 2) ≤ xₐ from by
      unfold xₐ; exact exp_le_exp.mpr (by norm_num)) hy)) hxy

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
