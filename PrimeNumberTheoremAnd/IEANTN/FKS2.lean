import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Rat.Cast.OfScientific
import PrimeNumberTheoremAnd.IEANTN.SecondaryDefinitions
import PrimeNumberTheoremAnd.IEANTN.FioriKadiriSwidinsky.FioriKadiriSwidinsky
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime
import PrimeNumberTheoremAnd.IEANTN.LogTables
import PrimeNumberTheoremAnd.IEANTN.Ramanujan.RamanujanCalculations

blueprint_comment /--
\section{The implications of FKS2}\label{fks2-sec}

In this file we record the implications in the paper \cite{FKS2}.  Roughly speaking, this paper has two components: a "$\psi$ to $\theta$ pipeline" that converts estimates on the error $E_\psi(x) = |\psi(x)-x|/x$ in the prime number theorem for the first Chebyshev function $\psi$ to estimates on the error $E_\theta(x) = |\theta(x)-x|/x$ in the prime number theorem for the second Chebyshev function $\theta$; and a "$\theta$ to $\pi$ pipeline" that converts estimates $E_\theta$ to estimates on the error $E_\pi(x) = |\pi(x) - \Li(x)|/(x/\log x)$ in the prime number theorem for the prime counting function $\pi$.  Each pipeline converts "admissible classical bounds" (Definitions \ref{classical-bound-psi} \ref{classical-bound-theta}, \ref{classical-bound-pi}) of one error to admissible classical bounds of the next error in the pipeline.

There are two types of bounds considered here.  The first are asymptotic bounds of the form
$$ E_\psi(x), E_\theta(x), E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right) $$
for various $A,B,C,R$ and all $x \geq x_0$.  The second are numerical bounds of the form
$$ E_\psi(x), E_\theta(x), E_\pi(x) \leq \varepsilon_{num}(x_0) $$
for all $x \geq x_0$ and certain specific numerical choices of $x_0$ and $\varepsilon_{num}(x_0)$.  One needs to merge these bounds together to obtain the best final results.

-/

open Real MeasureTheory Chebyshev

namespace FKS2

blueprint_comment /--
\subsection{Basic estimates on the error bound g}

Our asymptotic bounds can be described using a certain function $g$.  Here we define $g$ and record its basic properties.

-/


@[blueprint
  "fks2-eq-16"
  (title := "g function, FKS2 (16)")
  (statement := /--
  For any $a,b,c,x \in \mathbb{R}$ we define
  $g(a,b,c,x) := x^{-a} (\log x)^b \exp( c (\log x)^{1/2} )$. -/)]
noncomputable def g_bound (a b c x : ℝ) : ℝ := x^(-a) * (log x)^b * exp (c * sqrt (log x))

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
      have : log x ≠ 0 := by simp; grind
      have h_prod_rule : deriv (fun x ↦ x ^ (-a) * (log x) ^ b * exp (c * sqrt (log x))) x =
        (deriv (fun x ↦ x ^ (-a)) x) * (log x) ^ b * exp (c * sqrt (log x)) +
        x ^ (-a) * (deriv (fun x ↦ (log x) ^ b) x) * exp (c * sqrt (log x)) +
        x ^ (-a) * (log x) ^ b * (deriv (fun x ↦ exp (c * sqrt (log x))) x) := by
          rw [deriv_fun_mul, deriv_fun_mul]
          · ring
          all_goals fun_prop (disch := grind)
      unfold g_bound
      rw [h_prod_rule]
      norm_num [ show x ≠ 0 by linarith, show log x ≠ 0 by exact ne_of_gt ( log_pos hx ), sqrt_eq_rpow, rpow_sub_one, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ; ring_nf
      norm_num [ ne_of_gt ( log_pos hx ) ]
      rw [_root_.deriv_exp (by fun_prop (disch := grind))]
      simp only [deriv_const_mul_field']
      rw [_root_.deriv_rpow_const (by fun_prop (disch := grind)) (by grind), deriv_log]
      ring_nf
      rw [ show ( -1 / 2 : ℝ  ) = ( 1 / 2 : ℝ ) - 1 by norm_num, rpow_sub ( log_pos hx ) ] ; norm_num ; ring

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
      y * (x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x))) from fun _ ↦ by ring]
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
theorem lemma_10a {a b c : ℝ} (ha : a > 0) (hb : b < -c ^ 2 / (16 * a)) :
    StrictAntiOn (g_bound a b c) (Set.Ioi 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 1) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have : 0 < x := by linarith [hx.out]
    exact (((continuousAt_id.rpow continuousAt_const (Or.inl this.ne')).mul
      ((continuousAt_log this.ne').rpow continuousAt_const (Or.inl (log_pos hx.out).ne'))).mul
      (continuous_exp.continuousAt.comp (continuousAt_const.mul
      (continuous_sqrt.continuousAt.comp (continuousAt_log this.ne'))))).continuousWithinAt
  · rw [interior_Ioi] at hx; rw [lemma_10_substep_2 hx]
    let t := sqrt (log x)
    have : -a * t^2 + c/2 * t + b = -a * (t - c/(4*a))^2 + (b + c^2/(16*a)) := by grind
    have : b + c^2/(16*a) < 0 := by grind
    linarith [mul_nonneg (le_of_lt ha) (sq_nonneg (t - c/(4*a)))]

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
    StrictAntiOn (g_bound a b c) (Set.Ioi (exp ((c / (4 * a) + (1 / (2 * a)) * sqrt (c ^ 2 / 4 + 4 * a * b)) ^ 2))) := by
  have h_deriv_neg : ∀ x > exp ((c / (4 * a) + 1 / (2 * a) * sqrt (c ^ 2 / 4 + 4 * a * b)) ^ 2),
      deriv (g_bound a b c) x < 0 := by
    intro x hx
    have h_sqrt : sqrt (log x) > c / (4 * a) + 1 / (2 * a) * sqrt (c ^ 2 / 4 + 4 * a * b) :=
      lt_sqrt_of_sq_lt (by simpa using log_lt_log (by positivity) hx)
    have h_quadratic : -a * (sqrt (log x)) ^ 2 + (c / 2) * sqrt (log x) + b < 0 := by
      field_simp at *
      nlinarith [sqrt_nonneg ((c ^ 2 + a * b * 4 ^ 2) / 4),
        mul_self_sqrt (show 0 ≤ (c ^ 2 + a * b * 4 ^ 2) / 4 by nlinarith), sqrt_nonneg (log x),
        mul_self_sqrt (show 0 ≤ log x by
          exact le_of_not_gt fun h ↦ by
            rw [sqrt_eq_zero'.mpr h.le] at *; nlinarith [sqrt_nonneg ((c ^ 2 + a * b * 4 ^ 2) / 4),
              mul_self_sqrt (show 0 ≤ (c ^ 2 + a * b * 4 ^ 2) / 4 by nlinarith)])]
    convert (lemma_10_substep_2 (show x > 1 from lt_trans (by norm_num; positivity) hx)).2 h_quadratic using 1
  intro x hx y hy hxy
  obtain ⟨z, hz⟩ : ∃ z ∈ Set.Ioo x y, deriv (g_bound a b c) z = (g_bound a b c y - g_bound a b c x) / (y - x) := by
    apply_rules [exists_deriv_eq_slope]
    · exact continuousOn_of_forall_continuousAt fun z hz ↦ DifferentiableAt.continuousAt
        (differentiableAt_of_deriv_ne_zero (ne_of_lt (h_deriv_neg z (lt_of_lt_of_le hx hz.1))))
    · exact fun u hu ↦ DifferentiableAt.differentiableWithinAt
        (differentiableAt_of_deriv_ne_zero (ne_of_lt (h_deriv_neg u (lt_trans hx hu.1))))
  have := h_deriv_neg z <| hx.out.trans hz.1.1
  rw [hz.2, div_lt_iff₀] at this <;> linarith

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
theorem lemma_10c {b c : ℝ} (hb : b < 0) (hc : c > 0) :
    StrictAntiOn (g_bound 0 b c) (Set.Ioo 1 (exp ((-2 * b / c) ^ 2))) := by
  intro x hx y hy hxy
  simp only [g_bound, neg_zero, rpow_zero, one_mul]
  rw [rpow_def_of_pos <| log_pos hy.1, rpow_def_of_pos <| log_pos hx.1, ← exp_add, ← exp_add, exp_lt_exp]
  have huy_bound : sqrt (log y) < -2 * b / c := by
    rw [← sqrt_sq (div_pos (by linarith) hc).le]
    exact sqrt_lt_sqrt (log_pos hy.1).le <| (log_exp _).symm.trans_gt (log_lt_log (by linarith [hy.1]) hy.2)
  rw [show log (log x) = 2 * log (sqrt (log x)) from by rw [log_sqrt (log_pos hx.1).le]; ring,
    show log (log y) = 2 * log (sqrt (log y)) from by rw [log_sqrt (log_pos hy.1).le]; ring]
  have hderiv_neg : 2 * b / sqrt (log y) + c < 0 := by
    have : c * sqrt (log y) < -2 * b := by
      calc c * sqrt (log y) < c * (-2 * b / c) := mul_lt_mul_of_pos_left huy_bound hc
        _ = -2 * b := by field_simp
    have h2 : 2 * b / sqrt (log y) < -c := by rw [div_lt_iff₀ <| sqrt_pos.mpr <| log_pos hy.1]; linarith
    linarith
  have hconcave : log (sqrt (log y)) - log (sqrt (log x)) ≥ (sqrt (log y) - sqrt (log x)) / sqrt (log y) := by
    have := one_sub_inv_le_log_of_pos <| div_pos (sqrt_pos.mpr <| log_pos hy.1) <| sqrt_pos.mpr <| log_pos hx.1
    simp only [inv_div] at this
    calc log (sqrt (log y)) - log (sqrt (log x)) = log (sqrt (log y) / sqrt (log x)) := by
          rw [log_div (sqrt_pos.mpr <| log_pos hy.1).ne' (sqrt_pos.mpr <| log_pos hx.1).ne']
      _ ≥ 1 - sqrt (log x) / sqrt (log y) := this
      _ = (sqrt (log y) - sqrt (log x)) / sqrt (log y) := by rw [sub_div, div_self (sqrt_pos.mpr <| log_pos hy.1).ne']
  calc 2 * log (sqrt (log y)) * b + c * sqrt (log y)
      _ ≤ 2 * b * (log (sqrt (log x)) + (sqrt (log y) - sqrt (log x)) / sqrt (log y)) + c * sqrt (log y) := by nlinarith [hconcave]
      _ = 2 * b * log (sqrt (log x)) + (sqrt (log y) - sqrt (log x)) * (2 * b / sqrt (log y) + c) + c * sqrt (log x) := by field_simp; ring
      _ < 2 * log (sqrt (log x)) * b + c * sqrt (log x) := by nlinarith [hderiv_neg, sqrt_lt_sqrt (log_pos hx.1).le <| log_lt_log (by linarith [hx.1]) hxy]

@[blueprint
  "fks2-corollary-11"
  (title := "FKS2 Corollary 11")
  (statement := /--
  If $B \geq 1 + C^2 / 16R$ then $g(1,1-B,C/\sqrt{R},x)$ is decreasing in $x$. -/)
  (proof := /-- This follows from Lemma \ref{fks2-lemma-10a} applied with $a=1$, $b=1-B$ and $c=C/\sqrt{R}$. -/)
  (latexEnv := "corollary")
  (discussion := 615)]
theorem corollary_11 {B C R : ℝ} (hR : R > 0) (hB : B > 1 + C ^ 2 / (16 * R)) :
    StrictAntiOn (g_bound 1 (1 - B) (C / sqrt R)) (Set.Ioi 1) := by
  apply lemma_10a one_pos
  rw [div_pow, sq_sqrt hR.le, mul_one]
  linarith [show C ^ 2 / R / 16 = C ^ 2 / (16 * R) by ring]

blueprint_comment /--
When integrating expressions involving $g$, the Dawson function naturally appears; and we need to record some basic properties about it.
-/

@[blueprint
  "fks2-eq-19"
  (title := "Dawson function, FKS2 (19)")
  (statement := /--
  The Dawson function $D_+ : \mathbb{R} \to \mathbb{R}$ is defined by the formula
  $D_+(x) := e^{-x^2} \int_0^x e^{t^2}\ dt$. -/)]
noncomputable def dawson (x : ℝ) : ℝ := exp (-x ^ 2) * ∫ t in 0..x, exp (t ^ 2)

lemma deriv_dawson : ∀ x, deriv dawson x = 1 - 2 * x * dawson x := by
  intro x
  unfold dawson
  have h_exp_cont : Continuous (fun t : ℝ ↦ exp (t ^ 2)) := by fun_prop
  rw [deriv_fun_mul (by fun_prop) ((intervalIntegral.differentiable_integral_of_continuous h_exp_cont) x),
    deriv_exp (by fun_prop), Continuous.deriv_integral _ h_exp_cont 0 x,
    show deriv (fun y ↦ -y ^ 2) x = -2 * x by rw [deriv.fun_neg, deriv_pow_field 2]; norm_num,
    ← exp_add, neg_add_cancel, exp_zero]
  ring

lemma differentiable_dawson : Differentiable ℝ dawson := by
  intro x
  unfold dawson
  have h_exp_cont : Continuous (fun t : ℝ ↦ exp (t ^ 2)) := by fun_prop
  exact DifferentiableAt.mul (by fun_prop) ((intervalIntegral.differentiable_integral_of_continuous h_exp_cont) x)

lemma continuous_dawson : Continuous dawson :=
  differentiable_dawson.continuous

/-
dawson is non-negative
-/
lemma dawson_nonneg {x : ℝ} (hx : x ≥ 0) : dawson x ≥ 0 := by
  exact mul_nonneg ( Real.exp_nonneg _ ) ( intervalIntegral.integral_nonneg ( by positivity ) fun t ht => Real.exp_nonneg _ )

lemma dawson_one_pos : dawson 1 > 0 := by
  unfold dawson
  exact mul_pos (exp_pos _) (intervalIntegral.integral_pos (by norm_num) (continuous_exp.comp (continuous_pow 2)).continuousOn
    (fun _ _ ↦ (exp_pos _).le) ⟨0, by norm_num, exp_pos _⟩)

lemma filter_tendsto_dawson_at_top_zero : Filter.Tendsto dawson Filter.atTop (nhds 0) := by
  have h_dawson_le : ∀ x > 0, dawson x ≤ 1 / x := by
    intro x hx
    have h_deriv : ∀ t, HasDerivAt (fun t ↦ exp (x * t) / x) (exp (x * t)) t := by
      intro t
      have h := ((hasDerivAt_id t).const_mul x).exp.div_const x
      rwa [mul_one, mul_div_cancel_right₀ _ (ne_of_gt hx)] at h
    have hc : Continuous (fun t ↦ exp (x * t)) := by fun_prop
    have h_int_val : ∫ t in 0..x, exp (x * t) = exp (x * x) / x - exp (x * 0) / x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ h_deriv t) (hc.intervalIntegrable 0 x)
    have h_int_le_exp : ∫ t in 0..x, exp (x * t) ≤ exp (x ^ 2) / x := by
      rw [h_int_val, mul_zero, exp_zero, ← sq]
      have : 0 ≤ 1 / x := one_div_nonneg.mpr hx.le
      linarith
    have hc1 : Continuous (fun t : ℝ ↦ exp (t ^ 2)) := continuous_exp.comp (continuous_pow 2)
    have h_mono : ∫ t in 0..x, exp (t ^ 2) ≤ ∫ t in 0..x, exp (x * t) := by
      refine intervalIntegral.integral_mono_on hx.le (hc1.intervalIntegrable 0 x)
        (hc.intervalIntegrable 0 x) (fun t ht ↦ exp_le_exp.mpr ?_)
      rw [Set.mem_Icc] at ht
      rw [sq, mul_comm x]
      exact mul_le_mul_of_nonneg_left ht.2 ht.1
    unfold dawson
    calc exp (-x ^ 2) * ∫ t in 0..x, exp (t ^ 2)
      _ ≤ exp (-x ^ 2) * (exp (x ^ 2) / x) := mul_le_mul_of_nonneg_left (le_trans h_mono h_int_le_exp) (exp_pos _).le
      _ = 1 / x := by
        rw [show exp (-x ^ 2) * (exp (x ^ 2) / x) = (exp (-x ^ 2) * exp (x ^ 2)) / x by ring]
        rw [← exp_add, neg_add_cancel, exp_zero]
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    exact dawson_nonneg hx.le
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    exact h_dawson_le x hx
  · simpa only [inv_eq_one_div] using tendsto_inv_atTop_zero

lemma dawson_exists_M : ∃ M : ℝ, M > 1 ∧ ∀ x ≥ M, dawson x < dawson 1 := by
  have h_dawson_1_pos : dawson 1 > 0 := dawson_one_pos
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.mp filter_tendsto_dawson_at_top_zero (dawson 1) h_dawson_1_pos
  refine ⟨max R 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right R 2), fun x hx ↦ ?_⟩
  have h_dist := hR x (le_trans (le_max_left R 2) hx)
  rw [Real.dist_eq, sub_zero] at h_dist
  exact lt_of_le_of_lt (le_abs_self _) h_dist

lemma dawson_exists_max_Icc (M : ℝ) (hM : M > 1) :
    ∃ x₀ ∈ Set.Icc 0 M, ∀ x ∈ Set.Icc 0 M, dawson x ≤ dawson x₀ := by
  refine IsCompact.exists_isMaxOn isCompact_Icc ⟨0, ?_⟩ continuous_dawson.continuousOn
  rw [Set.mem_Icc]
  exact ⟨le_rfl, by linarith⟩

lemma dawson_pos {x : ℝ} (hx : x > 0) : dawson x > 0 := by
  unfold dawson
  exact mul_pos (exp_pos _)
    (intervalIntegral.integral_pos hx (by fun_prop)
      (fun t _ ↦ (exp_pos _).le) ⟨0, Set.mem_Icc.mpr ⟨le_rfl, hx.le⟩, exp_pos _⟩)

/-- Substituted form: `dawson z = ∫₀^z exp (u² − 2zu) du`. -/
lemma dawson_eq_integral (z : ℝ) :
    dawson z = ∫ u in (0:ℝ)..z, exp (u ^ 2 - 2 * z * u) := by
  unfold dawson
  have hsub : (∫ t in (0:ℝ)..z, exp (t ^ 2)) =
      ∫ u in (0:ℝ)..z, exp ((z - u) ^ 2) := by
    have := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := z)
      (fun t => exp (t ^ 2)) z
    simpa using this.symm
  rw [hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  change exp (-z ^ 2) * exp ((z - u) ^ 2) = exp (u ^ 2 - 2 * z * u)
  rw [← Real.exp_add]
  congr 1
  ring

/-- `∫₀^w e^{−2zu} du ≤ 1/(2z)`. -/
private lemma integral_exp_neg_mul_le {z w : ℝ} (hz : 0 < z) :
    (∫ u in (0:ℝ)..w, exp (-(2 * z) * u)) ≤ 1 / (2 * z) := by
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) w,
      HasDerivAt (fun u => -(exp (-(2 * z) * u) / (2 * z))) (exp (-(2 * z) * u)) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => -(2 * z) * u) (-(2 * z)) u := by
      simpa using (hasDerivAt_id u).const_mul (-(2 * z))
    have h2 : HasDerivAt (fun u : ℝ => exp (-(2 * z) * u))
        (exp (-(2 * z) * u) * (-(2 * z))) u := (Real.hasDerivAt_exp _).comp u h1
    have h3 := (h2.div_const (2 * z)).neg
    convert! h3 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; continuity)]
  have hE : 0 ≤ exp (-(2 * z) * w) / (2 * z) :=
    div_nonneg (exp_nonneg _) (by positivity)
  have h0 : exp (-(2 * z) * 0) = 1 := by norm_num
  rw [h0]
  linarith

/-- `∫₀^w u² e^{−2zu} du ≤ 1/(4z³)` via the explicit antiderivative. -/
private lemma integral_sq_mul_exp_le {z w : ℝ} (hz : 0 < z) (hw : 0 ≤ w) :
    (∫ u in (0:ℝ)..w, u ^ 2 * exp (-(2 * z) * u)) ≤ 1 / (4 * z ^ 3) := by
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) w,
      HasDerivAt
        (fun u => -(exp (-(2 * z) * u) * (u ^ 2 / (2 * z) + u / (2 * z ^ 2) + 1 / (4 * z ^ 3))))
        (u ^ 2 * exp (-(2 * z) * u)) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => -(2 * z) * u) (-(2 * z)) u := by
      simpa using (hasDerivAt_id u).const_mul (-(2 * z))
    have h2 : HasDerivAt (fun u : ℝ => exp (-(2 * z) * u))
        (exp (-(2 * z) * u) * (-(2 * z))) u := (Real.hasDerivAt_exp _).comp u h1
    have hp2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h3 : HasDerivAt
        (fun u : ℝ => u ^ 2 / (2 * z) + u / (2 * z ^ 2) + 1 / (4 * z ^ 3))
        (2 * u / (2 * z) + 1 / (2 * z ^ 2)) u :=
      ((hp2.div_const (2 * z)).add ((hasDerivAt_id u).div_const (2 * z ^ 2))).add_const
        (1 / (4 * z ^ 3))
    have hprod := (h2.mul h3).neg
    convert! hprod using 1
    have hz' : z ≠ 0 := hz.ne'
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; continuity)]
  have hPw : 0 ≤ exp (-(2 * z) * w) * (w ^ 2 / (2 * z) + w / (2 * z ^ 2) + 1 / (4 * z ^ 3)) := by
    apply mul_nonneg (exp_nonneg _)
    have t1 : (0:ℝ) ≤ w ^ 2 / (2 * z) := div_nonneg (sq_nonneg w) (by positivity)
    have t2 : (0:ℝ) ≤ w / (2 * z ^ 2) := div_nonneg hw (by positivity)
    have t3 : (0:ℝ) ≤ 1 / (4 * z ^ 3) := by positivity
    linarith
  have h0 : exp (-(2 * z) * 0) * ((0:ℝ) ^ 2 / (2 * z) + 0 / (2 * z ^ 2) + 1 / (4 * z ^ 3)) =
      1 / (4 * z ^ 3) := by
    norm_num
  rw [h0]
  linarith

/-- `e^x ≤ 1 + x e^c` for `0 ≤ x ≤ c` (from `1 − x ≤ e^{−x}`). -/
private lemma exp_le_one_add_mul_exp {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) :
    exp x ≤ 1 + x * exp c := by
  have h1 : 1 - x ≤ exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h2 : exp x * (1 - x) ≤ 1 := by
    calc exp x * (1 - x) ≤ exp x * exp (-x) :=
          mul_le_mul_of_nonneg_left h1 (exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  have h3 : exp x ≤ exp c := Real.exp_le_exp.mpr hxc
  nlinarith [exp_nonneg x, mul_nonneg hx (exp_nonneg x)]

/-- Sharp Dawson upper bound: for `0 ≤ w ≤ z`,
`dawson z ≤ 1/(2z) + e^{w²}/(4z³) + (z−w)·e^{−w(2z−w)}`.

Refines `dawson x ≤ 1/x` to the true leading term `1/(2z)` with explicitly
controlled corrections; a moderate `w` makes the last two terms negligible
for large `z`. This is the estimate behind the numerical bound on
`μ_asymp` in Corollary 22. -/
theorem dawson_le_sharp {z w : ℝ} (hw0 : 0 ≤ w) (hwz : w ≤ z) (hz : 0 < z) :
    dawson z ≤ 1 / (2 * z) + exp (w ^ 2) / (4 * z ^ 3) +
      (z - w) * exp (-(w * (2 * z - w))) := by
  rw [dawson_eq_integral]
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (fun u => exp (u ^ 2 - 2 * z * u)) volume a b := by
    intro a b
    apply Continuous.intervalIntegrable
    continuity
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := (0:ℝ)) (b := w) (c := z)
    (hint 0 w) (hint w z)]
  have head : (∫ u in (0:ℝ)..w, exp (u ^ 2 - 2 * z * u)) ≤
      1 / (2 * z) + exp (w ^ 2) / (4 * z ^ 3) := by
    have hptw : ∀ u ∈ Set.Icc (0:ℝ) w,
        exp (u ^ 2 - 2 * z * u) ≤
          exp (-(2 * z) * u) + exp (w ^ 2) * (u ^ 2 * exp (-(2 * z) * u)) := by
      intro u hu
      have hsplit : exp (u ^ 2 - 2 * z * u) = exp (u ^ 2) * exp (-(2 * z) * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      have hb := exp_le_one_add_mul_exp (sq_nonneg u)
        (by nlinarith [hu.1, hu.2] : u ^ 2 ≤ w ^ 2)
      have hepos : (0:ℝ) ≤ exp (-(2 * z) * u) := exp_nonneg _
      nlinarith [hb, hepos]
    have hmono := intervalIntegral.integral_mono_on hw0 (hint 0 w)
      (by apply Continuous.intervalIntegrable; continuity) hptw
    have hlin : (∫ u in (0:ℝ)..w,
          (exp (-(2 * z) * u) + exp (w ^ 2) * (u ^ 2 * exp (-(2 * z) * u)))) =
        (∫ u in (0:ℝ)..w, exp (-(2 * z) * u)) +
          exp (w ^ 2) * (∫ u in (0:ℝ)..w, u ^ 2 * exp (-(2 * z) * u)) := by
      rw [intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; continuity)
        (by apply Continuous.intervalIntegrable; continuity),
        intervalIntegral.integral_const_mul]
    have hgeom := integral_exp_neg_mul_le (w := w) hz
    have hsq := integral_sq_mul_exp_le (w := w) hz hw0
    have hew : (0:ℝ) ≤ exp (w ^ 2) := exp_nonneg _
    calc (∫ u in (0:ℝ)..w, exp (u ^ 2 - 2 * z * u))
        ≤ _ := hmono
      _ = _ := hlin
      _ ≤ 1 / (2 * z) + exp (w ^ 2) * (1 / (4 * z ^ 3)) := by
          have := mul_le_mul_of_nonneg_left hsq hew
          linarith
      _ = 1 / (2 * z) + exp (w ^ 2) / (4 * z ^ 3) := by ring
  have tail : (∫ u in w..z, exp (u ^ 2 - 2 * z * u)) ≤
      (z - w) * exp (-(w * (2 * z - w))) := by
    have hptw : ∀ u ∈ Set.Icc w z,
        exp (u ^ 2 - 2 * z * u) ≤ exp (-(w * (2 * z - w))) := by
      intro u hu
      apply Real.exp_le_exp.mpr
      nlinarith [hu.1, hu.2]
    calc (∫ u in w..z, exp (u ^ 2 - 2 * z * u))
        ≤ ∫ _u in w..z, exp (-(w * (2 * z - w))) :=
          intervalIntegral.integral_mono_on hwz (hint w z)
            _root_.intervalIntegrable_const hptw
      _ = (z - w) * exp (-(w * (2 * z - w))) := by
          rw [intervalIntegral.integral_const]
          ring
  linarith [head, tail]

private lemma hasDerivAt_exp_sq (x : ℝ) : HasDerivAt (fun t ↦ exp (t^2)) (2 * x * exp (x^2)) x := by
  have h : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * x) x := by
    have h := hasDerivAt_pow 2 x; rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
    exact h.congr_deriv (by push_cast; ring)
  exact h.exp.congr_deriv (by ring)

lemma F_strictAnti : StrictAntiOn (fun t ↦ exp (t^2) * ((1 : ℝ) - (2 : ℝ) * t * dawson t)) (Set.Ioi (0 : ℝ)) := by
  have h_diff : Differentiable ℝ (fun t ↦ exp (t^2) * ((1 : ℝ) - (2 : ℝ) * t * dawson t)) := by
    apply Differentiable.mul (by fun_prop)
    exact (differentiable_const _).sub (differentiable_id.const_mul (2 : ℝ) |>.mul differentiable_dawson)
  refine strictAntiOn_of_deriv_neg (convex_Ioi _) h_diff.continuous.continuousOn (fun x hx ↦ ?_)
  rw [interior_Ioi] at hx
  have h_deriv_eq : deriv (fun t ↦ exp (t^2) * ((1 : ℝ) - (2 : ℝ) * t * dawson t)) x = -2 * exp (x^2) * dawson x := by
    have h_dawson : HasDerivAt dawson (1 - 2 * x * dawson x) x :=
      differentiable_dawson.differentiableAt.hasDerivAt.congr_deriv (deriv_dawson x)
    exact ((hasDerivAt_exp_sq x).mul
      ((hasDerivAt_const x 1).sub
        (((hasDerivAt_id x).const_mul 2).mul h_dawson))).deriv.trans (by dsimp; ring)
  rw [h_deriv_eq]
  nlinarith [exp_pos (x^2), dawson_pos hx]

private lemma pos_of_deriv_pos_of_zero {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hg0 : g 0 = 0) (hg_deriv : ∀ y > 0, deriv g y > 0) {x : ℝ} (hx : x > 0) : g x > 0 := by
  obtain ⟨c, hc, h_eq⟩ := exists_deriv_eq_slope g hx hg.continuous.continuousOn hg.differentiableOn
  rw [eq_div_iff (by linarith : x - 0 ≠ 0), hg0, sub_zero] at h_eq
  linarith [mul_pos (hg_deriv c hc.1) (sub_pos.mpr hx), h_eq.symm, sub_zero (g x)]

/-- The Taylor polynomial approximation of degree 13 for the Dawson function. -/
noncomputable def S6 (x : ℝ) : ℝ :=
  x - 2/3 * x^3 + 4/15 * x^5 - 8/105 * x^7 + 16/945 * x^9 - 32/10395 * x^11 + 64/135135 * x^13

/-- The Taylor polynomial approximation of degree 11 for the Dawson function. -/
noncomputable def S5 (x : ℝ) : ℝ :=
  x - 2/3 * x^3 + 4/15 * x^5 - 8/105 * x^7 + 16/945 * x^9 - 32/10395 * x^11

private lemma hasDerivAt_S5 (y : ℝ) : HasDerivAt S5
    (1 - 2 * y^2 + 4/3 * y^4 - 8/15 * y^6 + 16/105 * y^8 - 32/945 * y^10) y := by
  unfold S5
  have d1 : HasDerivAt (fun x ↦ x) 1 y := hasDerivAt_id y
  have d2 : HasDerivAt (fun x ↦ 2/3 * x^3) (2 * y^2) y :=
    ((hasDerivAt_pow 3 y).const_mul (2/3)).congr_deriv (by norm_cast; ring)
  have d3 : HasDerivAt (fun x ↦ 4/15 * x^5) (4/3 * y^4) y :=
    ((hasDerivAt_pow 5 y).const_mul (4/15)).congr_deriv (by norm_cast; ring)
  have d4 : HasDerivAt (fun x ↦ 8/105 * x^7) (8/15 * y^6) y :=
    ((hasDerivAt_pow 7 y).const_mul (8/105)).congr_deriv (by norm_cast; ring)
  have d5 : HasDerivAt (fun x ↦ 16/945 * x^9) (16/105 * y^8) y :=
    ((hasDerivAt_pow 9 y).const_mul (16/945)).congr_deriv (by norm_cast; ring)
  have d6 : HasDerivAt (fun x ↦ 32/10395 * x^11) (32/945 * y^10) y :=
    ((hasDerivAt_pow 11 y).const_mul (32/10395)).congr_deriv (by norm_cast; ring)
  exact ((((d1.sub d2).add d3).sub d4).add d5).sub d6

private lemma hasDerivAt_S6 (y : ℝ) : HasDerivAt S6
    (1 - 2 * y^2 + 4/3 * y^4 - 8/15 * y^6 + 16/105 * y^8 - 32/945 * y^10 + 64/10395 * y^12) y := by
  have hd7 : HasDerivAt (fun x ↦ 64/135135 * x^13) (64/10395 * y^12) y :=
    ((hasDerivAt_pow 13 y).const_mul (64/135135)).congr_deriv (by norm_cast; ring)
  have heq : S6 = fun x => S5 x + 64/135135 * x^13 := by funext x; simp [S6, S5]
  rw [heq]; exact ((hasDerivAt_S5 y).add hd7).congr_deriv (by ring)

lemma dawson_lt_S6 (x : ℝ) (hx : x > 0) : dawson x < S6 x := by
  have hf0 : exp (0^2) * (S6 0 - dawson 0) = 0 := by
    unfold S6 dawson
    simp
  have h_deriv_f : ∀ y > 0, deriv (fun t ↦ exp (t^2) * (S6 t - dawson t)) y =
      exp (y^2) * (128 / 135135) * y^14 := by
    intro y hy
    have h_dawson : HasDerivAt dawson (1 - 2 * y * dawson y) y :=
      differentiable_dawson.differentiableAt.hasDerivAt.congr_deriv (deriv_dawson y)
    have h_exp := hasDerivAt_exp_sq y
    have h_comb := h_exp.mul ((hasDerivAt_S6 y).sub h_dawson)
    change deriv ((fun t ↦ exp (t^2)) * (S6 - dawson)) y = exp (y^2) * (128 / 135135) * y^14
    rw [h_comb.deriv]
    change 2 * y * exp (y^2) * (S6 y - dawson y) +
      exp (y^2) *
        (1 - 2 * y^2 + 4/3 * y^4 - 8/15 * y^6 + 16/105 * y^8 - 32/945 * y^10 + 64/10395 * y^12 -
          (1 - 2 * y * dawson y)) =
      exp (y^2) * (128 / 135135) * y^14
    unfold S6
    ring
  have h_deriv_pos : ∀ y > 0, deriv (fun t ↦ exp (t^2) * (S6 t - dawson t)) y > 0 := fun y hy => by
    rw [h_deriv_f y hy]
    exact mul_pos (mul_pos (exp_pos _) (by norm_num)) (pow_pos hy 14)
  have h_diff : Differentiable ℝ (fun t ↦ exp (t^2) * (S6 t - dawson t)) := by
    apply Differentiable.mul (by fun_prop)
    apply Differentiable.sub
    · unfold S6; fun_prop
    · exact differentiable_dawson
  have hf_pos : exp (x^2) * (S6 x - dawson x) > 0 :=
    pos_of_deriv_pos_of_zero h_diff hf0 h_deriv_pos hx
  exact lt_of_sub_pos (pos_of_mul_pos_right hf_pos (exp_pos _).le)

lemma S6_0924_bound : S6 0.924 < 1 / (2 * 0.924) := by
  unfold S6
  norm_num

theorem dawson_0924_bound : dawson 0.924 < 1 / (2 * 0.924) :=
  lt_trans (dawson_lt_S6 _ (by norm_num)) S6_0924_bound

lemma S5_lt_dawson (x : ℝ) (hx : x > 0) : S5 x < dawson x := by
  have hf0 : exp (0^2) * (dawson 0 - S5 0) = 0 := by
    unfold S5 dawson
    simp
  have h_deriv_f : ∀ y > 0, deriv (fun t ↦ exp (t^2) * (dawson t - S5 t)) y =
      exp (y^2) * (64 / 10395) * y^12 := by
    intro y hy
    have h_dawson : HasDerivAt dawson (1 - 2 * y * dawson y) y :=
      differentiable_dawson.differentiableAt.hasDerivAt.congr_deriv (deriv_dawson y)
    have h_exp := hasDerivAt_exp_sq y
    have h_comb := h_exp.mul (h_dawson.sub (hasDerivAt_S5 y))
    change deriv ((fun t ↦ exp (t^2)) * (dawson - S5)) y = exp (y^2) * (64 / 10395) * y^12
    rw [h_comb.deriv]
    change 2 * y * exp (y^2) * (dawson y - S5 y) +
      exp (y^2) *
        (1 - 2 * y * dawson y - (1 - 2 * y^2 + 4/3 * y^4 - 8/15 * y^6 + 16/105 * y^8 - 32/945 * y^10)) =
      exp (y^2) * (64 / 10395) * y^12
    unfold S5
    ring
  have h_deriv_pos : ∀ y > 0, deriv (fun t ↦ exp (t^2) * (dawson t - S5 t)) y > 0 := fun y hy => by
    rw [h_deriv_f y hy]
    exact mul_pos (mul_pos (exp_pos _) (by norm_num)) (pow_pos hy 12)
  have h_diff : Differentiable ℝ (fun t ↦ exp (t^2) * (dawson t - S5 t)) := by
    apply Differentiable.mul (by fun_prop)
    apply Differentiable.sub
    · exact differentiable_dawson
    · unfold S5; fun_prop
  have hf_pos : exp (x^2) * (dawson x - S5 x) > 0 :=
    pos_of_deriv_pos_of_zero h_diff hf0 h_deriv_pos hx
  exact lt_of_sub_pos (pos_of_mul_pos_right hf_pos (exp_pos _).le)

lemma S5_0925_bound : 1 / (2 * 0.925) < S5 0.925 := by
  unfold S5
  norm_num

theorem dawson_0925_bound : 1 / (2 * 0.925) < dawson 0.925 :=
  lt_trans S5_0925_bound (S5_lt_dawson _ (by norm_num))

private lemma crit_ge_of_F_pos (x₀ a : ℝ) (hx₀_pos : x₀ > 0) (ha_pos : a > 0)
    (h_crit_eq : 1 - 2 * x₀ * dawson x₀ = 0)
    (ha_bound : 1 - 2 * a * dawson a > 0) : a ≤ x₀ := by
  by_contra h_lt
  have hF_lt := F_strictAnti hx₀_pos ha_pos (lt_of_not_ge h_lt)
  dsimp at hF_lt
  rw [h_crit_eq, mul_zero] at hF_lt
  nlinarith [exp_pos (a ^ 2), ha_bound]

private lemma crit_le_of_F_neg (x₀ b : ℝ) (hx₀_pos : x₀ > 0) (hb_pos : b > 0)
    (h_crit_eq : 1 - 2 * x₀ * dawson x₀ = 0)
    (hb_bound : 1 - 2 * b * dawson b < 0) : x₀ ≤ b := by
  by_contra h_gt
  have hF_lt := F_strictAnti hb_pos hx₀_pos (lt_of_not_ge h_gt)
  dsimp at hF_lt
  rw [h_crit_eq, mul_zero] at hF_lt
  nlinarith [exp_pos (b ^ 2), hb_bound]

private lemma dawson_exists_critical_global_max :
    ∃ x₀ : ℝ, x₀ > 0 ∧ (∀ x, dawson x ≤ dawson x₀) ∧ deriv dawson x₀ = 0 := by
  have h_dawson_1_pos : dawson 1 > 0 := dawson_one_pos
  rcases dawson_exists_M with ⟨M, hM1, hM⟩
  rcases dawson_exists_max_Icc M hM1 with ⟨x₀, hx₀_mem, hx₀_max⟩
  have hx₀_pos : x₀ > 0 := by
    have hdawson_x₀_pos : dawson x₀ > 0 :=
      lt_of_lt_of_le h_dawson_1_pos
        (hx₀_max 1 (Set.mem_Icc.mpr ⟨by norm_num, hM1.le⟩))
    exact lt_of_le_of_ne hx₀_mem.1 fun heq => by
      subst heq
      simp [dawson] at hdawson_x₀_pos
  have h_max_nonneg : ∀ x ≥ 0, dawson x ≤ dawson x₀ := by
    intro x hx
    rcases le_or_gt x M with hle | hgt
    · exact hx₀_max x ⟨hx, hle⟩
    · have h1_mem : (1 : ℝ) ∈ Set.Icc 0 M := Set.mem_Icc.mpr ⟨by norm_num, hM1.le⟩
      exact le_trans (hM x hgt.le).le (hx₀_max 1 h1_mem)
  have h_max_neg : ∀ x < 0, dawson x < dawson x₀ := by
    intro x hx
    have hdawson_x₀_pos : dawson x₀ > 0 :=
      lt_of_lt_of_le h_dawson_1_pos
        (hx₀_max 1 (Set.mem_Icc.mpr ⟨by norm_num, hM1.le⟩))
    have h_dawson_neg : dawson x ≤ 0 := by
      unfold dawson
      rw [intervalIntegral.integral_symm x 0, mul_neg]
      exact neg_nonpos_of_nonneg (mul_nonneg (exp_pos _).le
        (intervalIntegral.integral_nonneg (le_of_lt hx) (fun t _ => (exp_pos _).le)))
    exact lt_of_le_of_lt h_dawson_neg hdawson_x₀_pos
  have h_max_global : ∀ x, dawson x ≤ dawson x₀ := fun x => by
    rcases le_or_gt 0 x with hge | hlt
    · exact h_max_nonneg x hge
    · exact (h_max_neg x hlt).le
  exact ⟨x₀, hx₀_pos, h_max_global,
    IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall h_max_global)⟩

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
      StrictAntiOn dawson (Set.Ioi x₀) := by
  obtain ⟨x₀, hx₀_pos, h_glob_max, h_crit⟩ := dawson_exists_critical_global_max
  have h_crit_eq : 1 - 2 * x₀ * dawson x₀ = 0 := (deriv_dawson x₀).symm.trans h_crit
  have h_deriv_pos_0924 : 1 - 2 * 0.924 * dawson 0.924 > 0 := by linarith [dawson_0924_bound]
  have h_deriv_neg_0925 : 1 - 2 * 0.925 * dawson 0.925 < 0 := by linarith [dawson_0925_bound]
  have h_ge_0924 : 0.924 ≤ x₀ :=
    crit_ge_of_F_pos x₀ 0.924 hx₀_pos (by norm_num) h_crit_eq h_deriv_pos_0924
  have h_le_0925 : x₀ ≤ 0.925 :=
    crit_le_of_F_neg x₀ 0.925 hx₀_pos (by norm_num) h_crit_eq h_deriv_neg_0925
  have h_deriv_neg : ∀ x ∈ Set.Ioi x₀, 1 - 2 * x * dawson x < 0 := by
    intro x hx
    have hF_lt := F_strictAnti hx₀_pos (lt_trans hx₀_pos hx) hx
    dsimp at hF_lt
    rw [h_crit_eq, mul_zero] at hF_lt
    nlinarith [exp_pos (x ^ 2)]
  refine ⟨x₀, ⟨h_ge_0924, h_le_0925⟩, h_glob_max,
    strictAntiOn_of_deriv_neg (convex_Ioi x₀) continuous_dawson.continuousOn (fun x hx ↦ ?_)⟩
  rw [interior_Ioi] at hx
  rw [deriv_dawson]
  exact h_deriv_neg x hx


blueprint_comment /--
\subsection{From asymptotic estimates on psi to asymptotic estimates on theta}

To get from asymptotic estimates on $E_\psi$ to asymptotic estimates on $E_\theta$, the paper cites results and arguments from the previous paper \cite{BKLNW}, which is treated elsewhere in this blueprint.
-/

noncomputable def ν_asymp (Aψ B C R x₀ : ℝ) : ℝ :=
  (1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
    (BKLNW.a₁ (log x₀) * (log x₀) * x₀ ^ (-(1:ℝ)/2) +
      BKLNW.a₂ (log x₀) * (log x₀) * x₀ ^ (-(2:ℝ)/3))


/-- The explicit slack used in `remark_15_margin`. -/
abbrev remark_15_margin : ℝ := 1e-5

/--
Key inequality behind the exponential decay:
for `t ≥ 1000` we have `2 * sqrt (t/R) ≤ t/4` with `R = 5.5666305`.
-/
lemma two_mul_sqrt_div_le_quarter (t : ℝ) (ht : t ≥ 1000) :
    2 * Real.sqrt (t / 5.5666305) ≤ t / 4 := by
  -- Suggested proof:
  -- 1) note `t > 0` and `0 < (5.5666305:ℝ)`.
  -- 2) square both sides using `Real.mul_self_le_mul_self_iff` (or `sq_le_sq`),
  --    reducing to `4*(t/5.5666305) ≤ (t/4)^2`.
  -- 3) simplify to `t ≥ 64/5.5666305`, then use `ht` and `norm_num`.
  have ht0 : 0 ≤ t := by linarith
  have hdiv_nonneg : 0 ≤ t / 5.5666305 := by positivity
  have hright_nonneg : 0 ≤ t / 4 := by positivity
  have h64 : (64 / 5.5666305 : ℝ) ≤ t := by
    have hnum : (64 / 5.5666305 : ℝ) < 1000 := by norm_num
    linarith
  have hmain : 4 * (t / 5.5666305) ≤ (t / 4) ^ 2 := by
    have hmul : (64 / 5.5666305 : ℝ) * t ≤ t * t := by
      exact mul_le_mul_of_nonneg_right h64 ht0
    have hdiv16 : ((64 / 5.5666305 : ℝ) * t) / 16 ≤ (t * t) / 16 :=
      div_le_div_of_nonneg_right hmul (by norm_num)
    norm_num [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] at hdiv16 ⊢
    exact hdiv16
  have hsq : (2 * Real.sqrt (t / 5.5666305)) * (2 * Real.sqrt (t / 5.5666305)) ≤ (t / 4) * (t / 4) := by
    have hsqrt_sq : (Real.sqrt (t / 5.5666305)) ^ 2 = t / 5.5666305 := Real.sq_sqrt hdiv_nonneg
    calc
      (2 * Real.sqrt (t / 5.5666305)) * (2 * Real.sqrt (t / 5.5666305))
          = 4 * (Real.sqrt (t / 5.5666305)) ^ 2 := by ring
      _ = 4 * (t / 5.5666305) := by rw [hsqrt_sq]
      _ ≤ (t / 4) ^ 2 := hmain
      _ = (t / 4) * (t / 4) := by ring
  have hnonneg_left : 0 ≤ 2 * Real.sqrt (t / 5.5666305) := by positivity
  exact (mul_self_le_mul_self_iff hnonneg_left hright_nonneg).2 hsq

/--
A very crude upper bound on `BKLNW.a₁` at large `t`.
You can make this as weak as you like; `≤ 2` is plenty.
-/
lemma BKLNW_a1_le_two_of_ge_1000 (t : ℝ) (ht : t ≥ 1000) :
    BKLNW.a₁ t ≤ 2 := by
  -- Sketch:
  -- unfold `BKLNW.a₁` -> `Inputs.default.a₁`.
  -- split on `t ≤ 2*log x₁`; in either branch it is `1 + ε(...)` with ε tiny.
  -- For the branch `1 + table_8_ε (t/2)`, use:
  --   `BKLNW_app.table_8_ε_le_of_row (b₀ := 20) (ε := 4.2676e-5) ...`
  -- because `20 ≤ t/2` when `t ≥ 1000`.
  -- conclude by `linarith` / `nlinarith`.
  have h_exp20 : exp (20 : ℝ) ≤ (1e19 : ℝ) := by
    grw [← exp_one_rpow 20, Real.exp_one_lt_d9]
    norm_num only
  have h20_log : (20 : ℝ) ≤ log (1e19 : ℝ) := by
    have := log_le_log (exp_pos (20 : ℝ)) h_exp20
    simpa [log_exp] using this
  have hmain :
      (if t ≤ 2 * log (1e19 : ℝ) then 1 + BKLNW_app.table_8_ε (log (1e19 : ℝ))
       else 1 + BKLNW_app.table_8_ε (t / 2)) ≤ 2 := by
    by_cases hif : t ≤ 2 * log (1e19 : ℝ)
    · have h_eps : BKLNW_app.table_8_ε (log (1e19 : ℝ)) ≤ 4.2676e-5 := by
        exact BKLNW_app.table_8_ε_le_of_row
          (b₀ := 20) (ε := 4.2676e-5) BKLNW_app.table_8_mem_20 h20_log
      simp [hif]
      linarith
    · have h20 : (20 : ℝ) ≤ t / 2 := by linarith [ht]
      have h_eps : BKLNW_app.table_8_ε (t / 2) ≤ 4.2676e-5 := by
        exact BKLNW_app.table_8_ε_le_of_row
          (b₀ := 20) (ε := 4.2676e-5) BKLNW_app.table_8_mem_20 h20
      simp [hif]
      linarith
  simpa [BKLNW.a₁, BKLNW.Inputs.a₁, BKLNW.Inputs.default, BKLNW.Pre_inputs.default] using hmain

/--
A crude linear bound on `BKLNW.a₂` at large `t`.
Any linear bound is enough; `≤ 5*t` is extremely safe for `t ≥ 1000`.
-/
lemma BKLNW_a2_le_five_mul_of_ge_1000 (t : ℝ) (ht : t ≥ 1000) :
    BKLNW.a₂ t ≤ 5 * t := by
  -- Sketch:
  -- unfold `BKLNW.a₂` -> `Inputs.default.a₂`:
  --   `(1+α) * max (f (exp t)) (f (2^(⌊t/log 2⌋₊ + 1)))`.
  -- Bound `f x` by the number of terms:
  --   for `x ≥ 1`, each summand `x^(1/k - 1/3) ≤ 1`,
  --   hence `f x ≤ (⌊log x / log 2⌋₊ + 1)` (cast to ℝ).
  -- Use this for both `exp t` and the dyadic point; conclude
  --   `a₂ t ≤ 2 * (t / log 2 + 3)` and then `≤ 5*t` from `ht` + `norm_num`.
  have ht_nonneg : 0 ≤ t := by linarith
  have hlog2_pos : 0 < log 2 := log_pos one_lt_two
  set n : ℕ := ⌊t / log 2⌋₊

  have hf_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ BKLNW.f x := by
    unfold BKLNW.f
    exact Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg hx _)

  have hf_le_floor_plus_one (x : ℝ) (hx : 1 ≤ x) :
      BKLNW.f x ≤ (⌊(log x) / (log 2)⌋₊ + 1 : ℝ) := by
    have hterm :
        ∀ k ∈ Finset.Icc 3 ⌊(log x) / (log 2)⌋₊, x ^ (1 / (k : ℝ) - 1 / (3 : ℝ) : ℝ) ≤ (1 : ℝ) := by
      intro k hk
      have hk3 : (3 : ℕ) ≤ k := (Finset.mem_Icc.mp hk).1
      have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      have hpow_le_zero : (1 / (k : ℝ) - 1 / (3 : ℝ) : ℝ) ≤ 0 := by
        have : (1 / (k : ℝ) : ℝ) ≤ 1 / (3 : ℝ) := by
          exact one_div_le_one_div_of_le (by norm_num) hk3'
        linarith
      have hxpow : x ^ (1 / (k : ℝ) - 1 / (3 : ℝ) : ℝ) ≤ x ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx hpow_le_zero
      simpa using hxpow
    have hcard :
        Finset.card (Finset.Icc 3 ⌊(log x) / (log 2)⌋₊) ≤ ⌊(log x) / (log 2)⌋₊ + 1 := by
      calc
        Finset.card (Finset.Icc 3 ⌊(log x) / (log 2)⌋₊) ≤
            Finset.card (Finset.Icc 0 ⌊(log x) / (log 2)⌋₊) := by
              apply Finset.card_le_card
              intro m hm
              exact Finset.mem_Icc.mpr ⟨Nat.zero_le m, (Finset.mem_Icc.mp hm).2⟩
        _ = ⌊(log x) / (log 2)⌋₊ + 1 := by simp
    calc
      BKLNW.f x ≤ ∑ k ∈ Finset.Icc 3 ⌊(log x) / (log 2)⌋₊, (1 : ℝ) := by
        unfold BKLNW.f
        exact Finset.sum_le_sum hterm
      _ = (Finset.card (Finset.Icc 3 ⌊(log x) / (log 2)⌋₊) : ℝ) := by
        simp
      _ ≤ (⌊(log x) / (log 2)⌋₊ + 1 : ℝ) := by exact_mod_cast hcard

  have hexp_ge_one : (1 : ℝ) ≤ exp t := by
    have : exp (0 : ℝ) ≤ exp t := exp_le_exp_of_le ht_nonneg
    simpa using this
  have hf_exp : BKLNW.f (exp t) ≤ t / log 2 + 2 := by
    calc
      BKLNW.f (exp t) ≤ (⌊(log (exp t)) / (log 2)⌋₊ + 1 : ℝ) :=
        hf_le_floor_plus_one (exp t) hexp_ge_one
      _ = (⌊t / log 2⌋₊ + 1 : ℝ) := by simp
      _ ≤ t / log 2 + 1 := by
        nlinarith [Nat.floor_le (div_nonneg ht_nonneg hlog2_pos.le)]
      _ ≤ t / log 2 + 2 := by linarith

  have hpow_ge_one : (1 : ℝ) ≤ 2 ^ (n + 1 : ℕ) := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hf_pow : BKLNW.f (2 ^ (n + 1 : ℕ)) ≤ t / log 2 + 2 := by
    have hfloor_pow : ⌊(log ((2 : ℝ) ^ (n + 1))) / (log 2)⌋₊ = n + 1 := by
      have hlog2_ne : (log 2 : ℝ) ≠ 0 := hlog2_pos.ne'
      rw [log_pow, show (((n + 1 : ℕ) : ℝ) * log 2 / log 2) = ((n + 1 : ℕ) : ℝ) by
        field_simp [hlog2_ne]]
      simpa using (Nat.floor_natCast (n + 1))
    calc
      BKLNW.f (2 ^ (n + 1 : ℕ)) ≤ (⌊(log ((2 : ℝ) ^ (n + 1))) / (log 2)⌋₊ + 1 : ℝ) :=
        hf_le_floor_plus_one ((2 : ℝ) ^ (n + 1 : ℕ)) hpow_ge_one
      _ = (n : ℝ) + 2 := by
        rw [hfloor_pow, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ t / log 2 + 2 := by
        nlinarith [Nat.floor_le (div_nonneg ht_nonneg hlog2_pos.le)]

  have hmax :
      max (BKLNW.f (exp t)) (BKLNW.f (2 ^ (⌊t / log 2⌋₊ + 1))) ≤ t / log 2 + 2 := by
    refine max_le hf_exp ?_
    simpa [n] using hf_pow

  have hfac : (1 + BKLNW.Inputs.default.α : ℝ) ≤ 2 := by
    change 1 + 1.93378e-8 * BKLNW_app.table_8_margin ≤ 2
    norm_num [BKLNW_app.table_8_margin]
  have hmax_nonneg :
      0 ≤ max (BKLNW.f (exp t)) (BKLNW.f (2 ^ (⌊t / log 2⌋₊ + 1))) := by
    exact le_trans (hf_nonneg (exp t) (by positivity)) (le_max_left _ _)

  have ha2_le : BKLNW.a₂ t ≤ 2 * (t / log 2 + 2) := by
    unfold BKLNW.a₂ BKLNW.Inputs.a₂
    calc
      (1 + BKLNW.Inputs.default.α) *
          max (BKLNW.f (exp t)) (BKLNW.f (2 ^ (⌊t / log 2⌋₊ + 1)))
          ≤ 2 * max (BKLNW.f (exp t)) (BKLNW.f (2 ^ (⌊t / log 2⌋₊ + 1))) := by
            exact mul_le_mul_of_nonneg_right hfac hmax_nonneg
      _ ≤ 2 * (t / log 2 + 2) := by gcongr

  have hcoef : (2 / log 2 : ℝ) < 3 := by
    have hlog : (2 / 3 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
    refine (div_lt_iff₀ hlog2_pos).2 ?_
    nlinarith [hlog]
  have hlin : 2 * (t / log 2 + 2) ≤ 5 * t := by
    calc
      2 * (t / log 2 + 2) = (2 / log 2) * t + 4 := by ring
      _ ≤ 3 * t + 4 := by nlinarith [le_of_lt hcoef, ht_nonneg]
      _ ≤ 5 * t := by linarith [ht]

  exact ha2_le.trans hlin

/--
Purely numerical tail bound used at the end:
`60000 * exp (-230) ≤ 1e-5`.
This can be discharged by `interval_decide`.
-/
lemma sixty_thousand_mul_exp_neg_230_le :
    (60000 : ℝ) * Real.exp (-230) ≤ (1e-5 : ℝ) := by
  have h_exp : Real.exp (-230) ≤ BKLNW.exp_neg_one_ub ^ (100 : ℕ) := by
    simpa using (BKLNW.exp_neg_le_pow (n := 100) (x := 230) (by norm_num))
  have h_mul :
      (60000 : ℝ) * Real.exp (-230) ≤ 60000 * BKLNW.exp_neg_one_ub ^ (100 : ℕ) := by
    exact mul_le_mul_of_nonneg_left h_exp (by norm_num)
  have h_num : 60000 * BKLNW.exp_neg_one_ub ^ (100 : ℕ) ≤ (1e-5 : ℝ) := by
    norm_num [BKLNW.exp_neg_one_ub]
  exact h_mul.trans h_num

lemma t_mul_exp_neg_one_thousandth_le_five_hundred
    (t : ℝ) (_ht : t ≥ 1000) :
    t * exp (-(1 / 1000 : ℝ) * t) ≤ 500 := by
  have htwo : 2 * (t / 1000) ≤ exp (t / 1000) := Real.two_mul_le_exp
  have ht_le : t ≤ 500 * exp (t / 1000) := by
    have hmul := mul_le_mul_of_nonneg_left htwo (by norm_num : (0 : ℝ) ≤ 500)
    have hmul' : 500 * (2 * (t / 1000)) ≤ 500 * exp (t / 1000) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      t = 500 * (2 * (t / 1000)) := by
        ring_nf
      _ ≤ 500 * exp (t / 1000) := hmul'
  have hdiv : t / exp (t / 1000) ≤ 500 := (div_le_iff₀ (Real.exp_pos _)).2 ht_le
  have hdiv' : t * (exp (t / 1000))⁻¹ ≤ 500 := by
    simpa [div_eq_mul_inv] using hdiv
  have hexp_inv : exp (-(1 / 1000 : ℝ) * t) = (exp (t / 1000))⁻¹ := by
    rw [show (-(1 / 1000 : ℝ) * t) = -(t / 1000) by ring_nf, Real.exp_neg]
  calc
    t * exp (-(1 / 1000 : ℝ) * t) = t * (exp (t / 1000))⁻¹ := by
      rw [hexp_inv]
    _ ≤ 500 := hdiv'

lemma exp_neg_five_twelfths_mul_le
    (t : ℝ) (ht : t ≥ 1000) :
    exp (-(5 / 12 : ℝ) * t) ≤ exp (-(230 : ℝ)) * exp (-(1 / 1000 : ℝ) * t) := by
  rw [← Real.exp_add]
  refine (Real.exp_le_exp).2 ?_
  have hcoef_nonneg : 0 ≤ ((5 / 12 : ℝ) - 1 / 1000) := by norm_num
  have hmul :
      ((5 / 12 : ℝ) - 1 / 1000) * 1000 ≤ ((5 / 12 : ℝ) - 1 / 1000) * t :=
    mul_le_mul_of_nonneg_left ht hcoef_nonneg
  have h230 : (230 : ℝ) ≤ ((5 / 12 : ℝ) - 1 / 1000) * t := by
    have hnum : (230 : ℝ) ≤ ((5 / 12 : ℝ) - 1 / 1000) * 1000 := by norm_num
    exact hnum.trans hmul
  have hneg : -(((5 / 12 : ℝ) - 1 / 1000) * t) ≤ (-230 : ℝ) := by
    exact neg_le_neg h230
  calc
    (-(5 / 12 : ℝ)) * t
        = -(((5 / 12 : ℝ) - 1 / 1000) * t) + (-(1 / 1000 : ℝ) * t) := by
          ring_nf
    _ ≤ (-230 : ℝ) + (-(1 / 1000 : ℝ) * t) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right hneg (-(1 / 1000 : ℝ) * t))

lemma part1_decay_bound
    (t powfac expfac : ℝ)
    (ht : t ≥ 1000)
    (hpow_le_div : powfac ≤ (5.5666305 : ℝ) / t)
    (hexpfac_nonneg : 0 ≤ expfac)
    (h_exp_half :
      expfac * exp (-(1 / 2 : ℝ) * t) ≤ exp (-(1 / 4 : ℝ) * t)) :
    powfac * expfac * ((2 * t) * exp (-(1 / 2 : ℝ) * t))
      ≤ (2 * (5.5666305 : ℝ)) * exp (-(230 : ℝ)) := by
  have ht_pos : 0 < t := by linarith [ht]
  have hpow_t : powfac * (2 * t) ≤ 2 * (5.5666305 : ℝ) := by
    have hmul : powfac * (2 * t) ≤ ((5.5666305 : ℝ) / t) * (2 * t) :=
      mul_le_mul_of_nonneg_right hpow_le_div (by positivity)
    have ht_eq : ((5.5666305 : ℝ) / t) * (2 * t) = 2 * (5.5666305 : ℝ) := by
      field_simp [ht_pos.ne']
    calc
      powfac * (2 * t) ≤ ((5.5666305 : ℝ) / t) * (2 * t) := hmul
      _ = 2 * (5.5666305 : ℝ) := ht_eq
  have hexp230 :
      exp (-(1 / 4 : ℝ) * t) ≤ exp (-(230 : ℝ)) := by
    refine (Real.exp_le_exp).2 ?_
    linarith [ht]
  calc
    powfac * expfac * ((2 * t) * exp (-(1 / 2 : ℝ) * t))
        = (powfac * (2 * t)) * (expfac * exp (-(1 / 2 : ℝ) * t)) := by ring_nf
    _ ≤ (2 * (5.5666305 : ℝ)) * exp (-(1 / 4 : ℝ) * t) := by
      exact mul_le_mul hpow_t h_exp_half
        (mul_nonneg hexpfac_nonneg (Real.exp_nonneg _)) (by positivity)
    _ ≤ (2 * (5.5666305 : ℝ)) * exp (-(230 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hexp230 (by positivity)

lemma part2_decay_bound
    (t powfac expfac : ℝ)
    (ht : t ≥ 1000)
    (hpow_le_div : powfac ≤ (5.5666305 : ℝ) / t)
    (hexpfac_nonneg : 0 ≤ expfac)
    (h_exp_third :
      expfac * exp (-(2 / 3 : ℝ) * t) ≤ exp (-(5 / 12 : ℝ) * t)) :
    powfac * expfac * ((5 * t * t) * exp (-(2 / 3 : ℝ) * t))
      ≤ (2500 * (5.5666305 : ℝ)) * exp (-(230 : ℝ)) := by
  have ht_pos : 0 < t := by linarith [ht]
  have hpow_t2 : powfac * (5 * t * t) ≤ 5 * (5.5666305 : ℝ) * t := by
    have hmul : powfac * (5 * t * t) ≤ ((5.5666305 : ℝ) / t) * (5 * t * t) :=
      mul_le_mul_of_nonneg_right hpow_le_div (by positivity)
    have ht_eq : ((5.5666305 : ℝ) / t) * (5 * t * t) = 5 * (5.5666305 : ℝ) * t := by
      field_simp [ht_pos.ne']
    calc
      powfac * (5 * t * t) ≤ ((5.5666305 : ℝ) / t) * (5 * t * t) := hmul
      _ = 5 * (5.5666305 : ℝ) * t := ht_eq
  have h_t_exp :
      t * exp (-(1 / 1000 : ℝ) * t) ≤ 500 :=
    t_mul_exp_neg_one_thousandth_le_five_hundred t ht
  have hexp_big :
      exp (-(5 / 12 : ℝ) * t) ≤ exp (-(230 : ℝ)) * exp (-(1 / 1000 : ℝ) * t) :=
    exp_neg_five_twelfths_mul_le t ht
  have hmix :
      exp (-(5 / 12 : ℝ) * t) * t ≤ exp (-(230 : ℝ)) * 500 := by
    have hstep1 :
        exp (-(5 / 12 : ℝ) * t) * t ≤
          (exp (-(230 : ℝ)) * exp (-(1 / 1000 : ℝ) * t)) * t :=
      mul_le_mul_of_nonneg_right hexp_big (by positivity)
    have h_t_exp' : exp (-(1 / 1000 : ℝ) * t) * t ≤ 500 := by
      calc
        exp (-(1 / 1000 : ℝ) * t) * t = t * exp (-(1 / 1000 : ℝ) * t) := by ac_rfl
        _ ≤ 500 := h_t_exp
    have hstep2 :
        (exp (-(230 : ℝ)) * exp (-(1 / 1000 : ℝ) * t)) * t ≤ exp (-(230 : ℝ)) * 500 := by
      have hmul := mul_le_mul_of_nonneg_left h_t_exp' (Real.exp_nonneg (-(230 : ℝ)))
      calc
        (exp (-(230 : ℝ)) * exp (-(1 / 1000 : ℝ) * t)) * t
            = exp (-(230 : ℝ)) * (exp (-(1 / 1000 : ℝ) * t) * t) := by simp [mul_assoc]
        _ ≤ exp (-(230 : ℝ)) * 500 := hmul
    exact hstep1.trans hstep2
  calc
    powfac * expfac * ((5 * t * t) * exp (-(2 / 3 : ℝ) * t))
        = (powfac * (5 * t * t)) * (expfac * exp (-(2 / 3 : ℝ) * t)) := by ac_rfl
    _ ≤ (5 * (5.5666305 : ℝ) * t) * exp (-(5 / 12 : ℝ) * t) := by
      exact mul_le_mul hpow_t2 h_exp_third
        (mul_nonneg hexpfac_nonneg (Real.exp_nonneg _)) (by positivity)
    _ = (5 * (5.5666305 : ℝ)) * (exp (-(5 / 12 : ℝ) * t) * t) := by ac_rfl
    _ ≤ (5 * (5.5666305 : ℝ)) * (exp (-(230 : ℝ)) * 500) := by
      gcongr
    _ = (2500 * (5.5666305 : ℝ)) * exp (-(230 : ℝ)) := by ring_nf

/--
**The missing lemma** Codex complained about:
for `log x₀ ≥ 1000` the correction `ν_asymp` is far below `1e-5`.
This is enough to go from the “exact” Remark 15 statement with `(1+ν_asymp)`
to the relaxed statement with `(1+remark_15_margin)`.
-/
theorem FKS_A_one_le (x₀ : ℝ) (h : Real.log x₀ ≥ 1000) : (1 : ℝ) ≤ FKS.A x₀ := by
  grind (splits := 30) [FKS.A]

private lemma BKLNW_a1_nonneg (t : ℝ) (ht : t ≥ 1000) : 0 ≤ BKLNW.a₁ t := by
  unfold BKLNW.a₁ BKLNW.Inputs.a₁ BKLNW.Inputs.default BKLNW.Pre_inputs.default
  by_cases hif : t ≤ 2 * Real.log (1e19 : ℝ)
  · simp [hif]
    have hx1_nonneg : 0 ≤ Real.log (1e19 : ℝ) := Real.log_nonneg (by norm_num)
    have hε : 0 ≤ BKLNW_app.table_8_ε (Real.log (1e19 : ℝ)) :=
      BKLNW.Pre_inputs.epsilon_nonneg BKLNW.Pre_inputs.default hx1_nonneg
    linarith
  · simp [hif]
    have hhalf_nonneg : 0 ≤ t / 2 := by linarith
    have hε : 0 ≤ BKLNW_app.table_8_ε (t / 2) :=
      BKLNW.Pre_inputs.epsilon_nonneg BKLNW.Pre_inputs.default hhalf_nonneg
    linarith

private lemma BKLNW_a2_nonneg (t : ℝ) : 0 ≤ BKLNW.a₂ t := by
  unfold BKLNW.a₂ BKLNW.Inputs.a₂
  have hfac : 0 ≤ (1 + BKLNW.Inputs.default.α : ℝ) := by
    change 0 ≤ 1 + 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hmax_nonneg : 0 ≤ max (BKLNW.f (Real.exp t)) (BKLNW.f (2 ^ (⌊t / Real.log 2⌋₊ + 1))) := by
    have hf_exp_nonneg : 0 ≤ BKLNW.f (Real.exp t) := by
      unfold BKLNW.f
      exact Finset.sum_nonneg (fun _ _ ↦ by positivity)
    exact le_trans hf_exp_nonneg (le_max_left _ _)
  exact mul_nonneg hfac hmax_nonneg

private lemma term_inside_bound {a t x₀ c A : ℝ} (ht_nonneg : 0 ≤ t)
    (ha_nonneg : 0 ≤ a) (ha_le : a ≤ A)
    (hx_abs : |x₀ ^ c| ≤ Real.exp (c * t)) :
    a * t * x₀ ^ c ≤ A * t * Real.exp (c * t) := by
  have hx_le : x₀ ^ c ≤ Real.exp (c * t) := le_trans (le_abs_self _) hx_abs
  have hat_nonneg : 0 ≤ a * t := mul_nonneg ha_nonneg ht_nonneg
  have h1 : a * t * x₀ ^ c ≤ a * t * Real.exp (c * t) :=
    mul_le_mul_of_nonneg_left hx_le hat_nonneg
  have h2 : a * t * Real.exp (c * t) ≤ A * t * Real.exp (c * t) := by
    have hat_le : a * t ≤ A * t := mul_le_mul_of_nonneg_right ha_le ht_nonneg
    exact mul_le_mul_of_nonneg_right hat_le (Real.exp_nonneg _)
  exact h1.trans h2

theorem nu_asymp_le_remark_15_margin (x₀ : ℝ) (h : Real.log x₀ ≥ 1000) :
    ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ ≤ remark_15_margin := by
  set t : ℝ := Real.log x₀
  have ht : t ≥ 1000 := by simpa [t] using h
  have ht_pos : 0 < t := by linarith [ht]

  have hA_pos : 0 < FKS.A x₀ := by linarith [FKS_A_one_le x₀ h]
  have h_invA_le_one : 1 / FKS.A x₀ ≤ 1 :=
    (div_le_iff₀ hA_pos).2 (by simpa using FKS_A_one_le x₀ h)

  have hxhalf_abs : |x₀ ^ (-(1 / 2 : ℝ))| ≤ exp (-(1 / 2 : ℝ) * t) := by
    simpa [t, mul_assoc, mul_left_comm, mul_comm] using Real.abs_rpow_le_exp_log_mul x₀ (-(1 / 2 : ℝ))
  have hxthird_abs : |x₀ ^ (-(2 / 3 : ℝ))| ≤ exp (-(2 / 3 : ℝ) * t) := by
    simpa [t, mul_assoc, mul_left_comm, mul_comm] using Real.abs_rpow_le_exp_log_mul x₀ (-(2 / 3 : ℝ))

  have hpow_le_div : ((5.5666305 : ℝ) / t) ^ (3 / 2 : ℝ) ≤ (5.5666305 : ℝ) / t := by
    simpa using Real.rpow_le_rpow_of_exponent_ge (by positivity)
      ((div_le_iff₀ (by linarith)).2 (by linarith)) (by norm_num : (1 : ℝ) ≤ 3 / 2)

  have h_exp_half :
      exp (2 * Real.sqrt (t / 5.5666305)) * exp (-(1 / 2 : ℝ) * t) ≤ exp (-(1 / 4 : ℝ) * t) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [two_mul_sqrt_div_le_quarter t ht])
  have h_exp_third :
      exp (2 * Real.sqrt (t / 5.5666305)) * exp (-(2 / 3 : ℝ) * t) ≤ exp (-(5 / 12 : ℝ) * t) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [two_mul_sqrt_div_le_quarter t ht])

  have h_inside :
      BKLNW.a₁ t * t * x₀ ^ (-(1 / 2 : ℝ)) + BKLNW.a₂ t * t * x₀ ^ (-(2 / 3 : ℝ))
        ≤ (2 * t) * exp (-(1 / 2 : ℝ) * t) + (5 * t * t) * exp (-(2 / 3 : ℝ) * t) := by
    linarith [term_inside_bound ht_pos.le (BKLNW_a1_nonneg t ht) (BKLNW_a1_le_two_of_ge_1000 t ht) hxhalf_abs,
      term_inside_bound ht_pos.le (BKLNW_a2_nonneg t) (BKLNW_a2_le_five_mul_of_ge_1000 t ht) hxthird_abs]
  have hhalf_rewrite : ((-1 : ℝ) / 2) = -(1 / 2 : ℝ) := by norm_num
  have hthird_rewrite : ((-2 : ℝ) / 3) = -(2 / 3 : ℝ) := by norm_num

  let powfac : ℝ := ((5.5666305 : ℝ) / t) ^ (3 / 2 : ℝ)
  let expfac : ℝ := exp (2 * Real.sqrt (t / 5.5666305))
  have hpowfac_nonneg : 0 ≤ powfac := by unfold powfac; positivity
  have hexpfac_nonneg : 0 ≤ expfac := by unfold expfac; positivity

  have h_main0 :
      ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀
        ≤ (1 / FKS.A x₀) * powfac * expfac *
            ((2 * t) * exp (-(1 / 2 : ℝ) * t) + (5 * t * t) * exp (-(2 / 3 : ℝ) * t)) := by
    simpa [hhalf_rewrite, hthird_rewrite, ν_asymp, t, powfac, expfac, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left h_inside (by positivity : 0 ≤ (1 / FKS.A x₀) * powfac * expfac)

  have h_main1 : ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀
      ≤ powfac * expfac * ((2 * t) * exp (-(1 / 2 : ℝ) * t) + (5 * t * t) * exp (-(2 / 3 : ℝ) * t)) :=
    h_main0.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_right h_invA_le_one (by positivity))

  have h_split :
      powfac * expfac * ((2 * t) * exp (-(1 / 2 : ℝ) * t) + (5 * t * t) * exp (-(2 / 3 : ℝ) * t))
        ≤ (2 * (5.5666305 : ℝ)) * exp (-(230 : ℝ)) + (2500 * (5.5666305 : ℝ)) * exp (-(230 : ℝ)) := by
    rw [mul_add]
    exact add_le_add
      (part1_decay_bound t powfac expfac ht hpow_le_div hexpfac_nonneg h_exp_half)
      (part2_decay_bound t powfac expfac ht hpow_le_div hexpfac_nonneg h_exp_third)

  have h_main2 : ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ ≤ (60000 : ℝ) * exp (-(230 : ℝ)) :=
    h_main1.trans (h_split.trans (by
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)))

  simpa [remark_15_margin] using h_main2.trans sixty_thousand_mul_exp_neg_230_le

/-- A rewritten form of `nu_asymp_le_remark_15_margin`. -/
theorem nu_asymp_le_remark_15_margin_sub_one (x₀ : ℝ) (h : Real.log x₀ ≥ 1000) :
    ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ ≤ (1 + remark_15_margin) - 1 := by
  -- this is just rewriting
  simpa [remark_15_margin] using (nu_asymp_le_remark_15_margin x₀ h)

private lemma g_bound_strictAntiOn (α : ℝ) (hα : 0 < α) (B C R : ℝ) (hR : R > 0)
    (hcond : B > C ^ 2 / (16 * α * R)) :
    StrictAntiOn (g_bound α (-B) (C / Real.sqrt R)) (Set.Ioi 1) := by
  apply lemma_10a hα
  rw [show -(C / Real.sqrt R) ^ 2 / (16 * α) = -C ^ 2 / (16 * α * R) by
        rw [div_pow, Real.sq_sqrt hR.le]; ring, neg_div]
  linarith

private lemma g_bound_le_of_anti {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 1))
    {x₀ x : ℝ} (hx₀_pos : 0 < x₀) (hx₀ : 7 ≤ Real.log x₀) (hx : x₀ ≤ x) :
    f x ≤ f x₀ := by
  rcases eq_or_lt_of_le hx with rfl | hx_lt
  · exact le_rfl
  · have h_gt1 : 1 < x₀ := by rw [← Real.log_pos_iff hx₀_pos.le]; linarith
    exact (hanti h_gt1 (h_gt1.trans hx_lt) hx_lt).le

private lemma mul_rpow_sub_div_le_admissible_bound_mul (α a Aψ B C R x x₀ : ℝ)
    (ha_nonneg : 0 ≤ a) (hAψ : Aψ > 0) (hR : R > 0)
    (hx_pos : 0 < x) (hx₀_pos : 0 < x₀)
    (hlog_pos : 0 < Real.log x) (hlog_x₀_pos : 0 < Real.log x₀)
    (hx₀ : 7 ≤ Real.log x₀)
    (hg_le : g_bound α (-B) (C / Real.sqrt R) x ≤ g_bound α (-B) (C / Real.sqrt R) x₀) :
    a * x ^ (1 - α) / x ≤
      admissible_bound Aψ B C R x * ((1 / Aψ) * (R / Real.log x₀) ^ B *
        Real.exp (C * Real.sqrt (Real.log x₀ / R)) * (a * Real.log x₀ * x₀ ^ (-α))) := by
  have h_exp_cancel : Real.exp (-C * Real.sqrt (Real.log x / R)) * Real.exp (C / Real.sqrt R * Real.sqrt (Real.log x)) = 1 := by
    rw [← Real.exp_add, show -C * Real.sqrt (Real.log x / R) + C / Real.sqrt R * Real.sqrt (Real.log x) = 0 by
      rw [show Real.log x / R = Real.log x * R⁻¹ from div_eq_mul_inv _ _, Real.sqrt_mul hlog_pos.le, Real.sqrt_inv]; ring, Real.exp_zero]
  have h_log_cancel : (Real.log x) ^ B * (Real.log x) ^ (-B) = 1 := by
    rw [← Real.rpow_add hlog_pos, add_neg_cancel, Real.rpow_zero]
  have h_div_pow1 : (Real.log x / R) ^ B = (Real.log x) ^ B * R ^ (-B) := by
    rw [div_eq_mul_inv, Real.mul_rpow hlog_pos.le (inv_pos.mpr hR).le, Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]
  have h_div_pow2 : (R / Real.log x₀) ^ B = R ^ B * (Real.log x₀) ^ (-B) := by
    rw [div_eq_mul_inv, Real.mul_rpow hR.le (inv_pos.mpr hlog_x₀_pos).le, Real.inv_rpow hlog_x₀_pos.le, ← Real.rpow_neg hlog_x₀_pos.le]
  have h_R_cancel : R ^ (-B) * R ^ B = 1 := by
    rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  have h_exp_eq₀ : C / Real.sqrt R * Real.sqrt (Real.log x₀) = C * Real.sqrt (Real.log x₀ / R) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, Real.sqrt_mul hlog_x₀_pos.le, Real.sqrt_inv]; ring
  have hg_nonneg : 0 ≤ g_bound α (-B) (C / Real.sqrt R) x₀ := by unfold g_bound; positivity
  have h_g_scaled : g_bound α (-B) (C / Real.sqrt R) x ≤ g_bound α (-B) (C / Real.sqrt R) x₀ * Real.log x₀ :=
    le_trans hg_le (by simpa using mul_le_mul_of_nonneg_left (by linarith : 1 ≤ Real.log x₀) hg_nonneg)
  calc a * x ^ (1 - α) / x
      _ = a * x ^ (-α) := by
          rw [mul_div_assoc, show x ^ (1 - α) / x = x ^ (-α) by
            field_simp; rw [show 1 - α = 1 + -α by ring, Real.rpow_add hx_pos, Real.rpow_one]]
      _ = a * (Real.log x) ^ B * Real.exp (-C * Real.sqrt (Real.log x / R)) *
            g_bound α (-B) (C / Real.sqrt R) x := by
          unfold g_bound
          rw [show a * (Real.log x) ^ B * Real.exp (-C * Real.sqrt (Real.log x / R)) *
              (x ^ (-α) * (Real.log x) ^ (-B) * Real.exp (C / Real.sqrt R * Real.sqrt (Real.log x))) =
              a * x ^ (-α) * ((Real.log x) ^ B * (Real.log x) ^ (-B)) *
              (Real.exp (-C * Real.sqrt (Real.log x / R)) *
              Real.exp (C / Real.sqrt R * Real.sqrt (Real.log x))) by ring,
              h_log_cancel, h_exp_cancel]
          ring
      _ ≤ a * (Real.log x) ^ B * Real.exp (-C * Real.sqrt (Real.log x / R)) *
            (g_bound α (-B) (C / Real.sqrt R) x₀ * Real.log x₀) :=
          mul_le_mul_of_nonneg_left h_g_scaled (by positivity)
      _ = admissible_bound Aψ B C R x * ((1 / Aψ) * (R / Real.log x₀) ^ B *
            Real.exp (C * Real.sqrt (Real.log x₀ / R)) * (a * Real.log x₀ * x₀ ^ (-α))) := by
          unfold admissible_bound g_bound
          rw [(Real.sqrt_eq_rpow _).symm, h_div_pow1, h_div_pow2, h_exp_eq₀]
          rw [show Aψ * ((Real.log x) ^ B * R ^ (-B)) * Real.exp (-C * Real.sqrt (Real.log x / R)) *
              ((1 / Aψ) * (R ^ B * (Real.log x₀) ^ (-B)) * Real.exp (C * Real.sqrt (Real.log x₀ / R)) *
              (a * Real.log x₀ * x₀ ^ (-α))) =
              (Aψ * (1 / Aψ)) * (R ^ (-B) * R ^ B) * (a * (Real.log x) ^ B *
              Real.exp (-C * Real.sqrt (Real.log x / R)) *
              ((x₀ ^ (-α) * (Real.log x₀) ^ (-B) *
              Real.exp (C * Real.sqrt (Real.log x₀ / R))) * Real.log x₀)) by ring]
          rw [mul_one_div_cancel hAψ.ne', h_R_cancel]
          ring

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
  and $a_1,a_2$ are given by Definitions \ref{bklnw-def-a-1} and \ref{bklnw-def-a-2}.
  -/)
  (proof := /-- The proof of Corollary \ref{bklnw-cor-14-1} essentially proves the proposition, but requires that $x_0 \geq e^{1000}$ to conclude that the function
  $$ 1 + \frac{a_1 \exp(C \sqrt{\frac{\log x}{R}})}{A_\psi \sqrt{x} (\log x/R)^{B}} + \frac{a_2 \exp(C \sqrt{\frac{\log x}{R}})}{A_\psi x^{2/3} (\log x/R)^{B}} = 1 + \frac{a_1}{A_\psi} g(1/2, -B, C/\sqrt{R}, x) + \frac{a_2}{A_\psi} g(2/3, -B, C/\sqrt{R}, x)$$
  is decreasing. By Lemma \ref{fks2-lemma-10a}, since $B > C^2/8R$, the function is actually decreasing for all $x$. -/)
  (latexEnv := "proposition")
  (discussion := 671)]
theorem proposition_13
  (Aψ B C R x₀ : ℝ) (hAψ : Aψ > 0) (hR : R > 0) (hx₀_pos : 0 < x₀) (hx₀ : 7 ≤ Real.log x₀)
  (h_bound : Eψ.classicalBound Aψ B C R x₀)
  (hB : B > C ^ 2 / (8 * R)) :
  Eθ.classicalBound (Aψ * (1 + ν_asymp Aψ B C R x₀)) B C R x₀ := by
  unfold Eθ.classicalBound Eθ
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hx₀_pos hx
  have h_abs_le : |θ x - x| ≤ |ψ x - x| + (ψ x - θ x) := by
    have h1 : |θ x - x| ≤ |ψ x - x| + |θ x - ψ x| := by
      rw [show θ x - x = (ψ x - x) + (θ x - ψ x) by ring]; exact abs_add_le _ _
    have h2 : |θ x - ψ x| = ψ x - θ x := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (theta_le_psi x))]
    linarith
  have hg1_anti : StrictAntiOn (g_bound (1 / 2) (-B) (C / sqrt R)) (Set.Ioi 1) :=
    g_bound_strictAntiOn (1 / 2) (by norm_num) B C R hR
      (by rw [show 16 * (1 / 2 : ℝ) * R = 8 * R by ring]; exact hB)
  have hg2_anti : StrictAntiOn (g_bound (2 / 3) (-B) (C / sqrt R)) (Set.Ioi 1) :=
    g_bound_strictAntiOn (2 / 3) (by norm_num) B C R hR (by
      have : 0 ≤ C ^ 2 / R := by positivity
      rw [show C ^ 2 / (16 * (2 / 3 : ℝ) * R) = (3 / 32) * (C ^ 2 / R) by ring]
      rw [show C ^ 2 / (8 * R) = (1 / 8) * (C ^ 2 / R) by ring] at hB
      linarith)
  have hlog_pos : 0 < log x := log_pos (by
    have : 1 < x₀ := by rw [← log_pos_iff hx₀_pos.le]; linarith
    linarith)
  have ha₁_nonneg : 0 ≤ BKLNW.a₁ (log x₀) := by
    unfold BKLNW.a₁ BKLNW.Inputs.a₁; split_ifs
    · have hx₁_ge_one : 1 ≤ BKLNW.Inputs.default.x₁ := (one_le_exp (by positivity)).trans BKLNW.Inputs.default.hx₁
      have hε := BKLNW.Pre_inputs.epsilon_nonneg BKLNW.Inputs.default.toPre_inputs (Real.log_nonneg hx₁_ge_one)
      linarith
    · have hε := BKLNW.Pre_inputs.epsilon_nonneg BKLNW.Inputs.default.toPre_inputs (by linarith : 0 ≤ log x₀ / 2)
      linarith
  have ha₂_nonneg : 0 ≤ BKLNW.a₂ (log x₀) := by
    unfold BKLNW.a₂ BKLNW.Inputs.a₂
    refine mul_nonneg (by norm_num [BKLNW.Inputs.default, BKLNW_app.table_8_margin]) (le_trans ?_ (le_max_left _ _))
    unfold BKLNW.f; exact Finset.sum_nonneg (fun _ _ ↦ by positivity)
  have h_term1_le : BKLNW.a₁ (log x₀) * x ^ (1 / 2 : ℝ) / x ≤
      admissible_bound Aψ B C R x * ((1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
        (BKLNW.a₁ (log x₀) * log x₀ * x₀ ^ (-(1 / 2 : ℝ)))) := by
    have h := mul_rpow_sub_div_le_admissible_bound_mul (1 / 2) _ Aψ B C R x x₀ ha₁_nonneg hAψ hR hx_pos hx₀_pos
      hlog_pos (by linarith) hx₀ (g_bound_le_of_anti hg1_anti hx₀_pos hx₀ hx)
    rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  have h_term2_le : BKLNW.a₂ (log x₀) * x ^ (1 / 3 : ℝ) / x ≤
      admissible_bound Aψ B C R x * ((1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
        (BKLNW.a₂ (log x₀) * log x₀ * x₀ ^ (-(2 / 3 : ℝ)))) := by
    have h := mul_rpow_sub_div_le_admissible_bound_mul (2 / 3) _ Aψ B C R x x₀ ha₂_nonneg hAψ hR hx_pos hx₀_pos
      hlog_pos (by linarith) hx₀ (g_bound_le_of_anti hg2_anti hx₀_pos hx₀ hx)
    rwa [show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num] at h
  calc |θ x - x| / x
    _ ≤ (|ψ x - x| + (ψ x - θ x)) / x := div_le_div_of_nonneg_right h_abs_le hx_pos.le
    _ ≤ admissible_bound Aψ B C R x + (ψ x - θ x) / x := by rw [add_div]; exact add_le_add_left (h_bound x hx) _
    _ ≤ admissible_bound Aψ B C R x +
        (admissible_bound Aψ B C R x * ((1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
          (BKLNW.a₁ (log x₀) * log x₀ * x₀ ^ (-(1 / 2 : ℝ)))) +
         admissible_bound Aψ B C R x * ((1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
          (BKLNW.a₂ (log x₀) * log x₀ * x₀ ^ (-(2 / 3 : ℝ))))) := by
        have h_div_le : (ψ x - θ x) / x ≤ (BKLNW.a₁ (log x₀) * x ^ (1 / 2 : ℝ) + BKLNW.a₂ (log x₀) * x ^ (1 / 3 : ℝ)) / x :=
          div_le_div_of_nonneg_right (BKLNW.cor_5_1 hx₀ (by rwa [exp_log hx₀_pos])) hx_pos.le
        rw [add_div] at h_div_le
        linarith [h_term1_le, h_term2_le]
    _ = admissible_bound (Aψ * (1 + ν_asymp Aψ B C R x₀)) B C R x := by
        unfold admissible_bound ν_asymp; simp only [neg_div]; ring

-- Helper to bound the summation of a term B ^ (1 / k - 1 / 3) for B ≥ 1.
private lemma rpow_sum_le_card {B : ℝ} (hB : 1 ≤ B) (N : ℕ) :
    ∑ k ∈ Finset.Icc (3 : ℕ) N, B ^ (1 / (k : ℝ) - 1 / 3 : ℝ) ≤ ((Finset.Icc (3 : ℕ) N).card : ℝ) := by
  have hterm : ∀ k ∈ Finset.Icc (3 : ℕ) N, B ^ (1 / (k : ℝ) - 1 / 3 : ℝ) ≤ 1 := by
    intro k hk
    have hk3 : (3 : ℕ) ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (3 : ℕ)) hk3)
    have hexp : (1 / (k : ℝ) - 1 / 3 : ℝ) ≤ 0 := by
      have hk_inv : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 := by
        rw [one_div_le_one_div hkpos (by norm_num : (0 : ℝ) < 3)]
        exact_mod_cast hk3
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hB hexp
  simpa using (Finset.sum_le_card_nsmul (Finset.Icc (3 : ℕ) N)
    (fun k ↦ B ^ (1 / (k : ℝ) - 1 / 3 : ℝ)) 1 hterm)

-- Helper for proving a lower bound on `Real.exp (-b)` via `Real.log` of the inverse base.
private lemma inv_le_exp_neg {a b : ℝ} (ha : 0 < a) (h : b ≤ Real.log a) :
    1 / a ≤ Real.exp (-b) :=
  (Real.log_le_iff_le_exp (by positivity)).1 (by
    rw [one_div, Real.log_inv]
    linarith)

-- Helper for corollary_14_small_adm when u ≤ 16/25.
private lemma corollary_14_small_adm_case1 (u : ℝ) (hu_pos : 0 < u) (hu_ge : (31 / 250 : ℝ) ≤ u) (hu64 : u ≤ (16 / 25 : ℝ)) :
    (1 : ℝ) ≤ 121.0961 * (u * Real.sqrt u) * Real.exp (-2 * Real.sqrt u) := by
  have hsqrt_upper : Real.sqrt u ≤ (4 / 5 : ℝ) :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith⟩
  have hsqrt_lower : (7 / 20 : ℝ) ≤ Real.sqrt u :=
    (Real.le_sqrt (by norm_num) hu_pos.le).2 (by nlinarith [hu_ge])
  have hu_mul : (217 / 5000 : ℝ) ≤ u * Real.sqrt u := by
    nlinarith [hu_ge, hsqrt_lower]
  have h_exp_base : (1 / 5 : ℝ) ≤ Real.exp (- (8 / 5 : ℝ)) :=
    inv_le_exp_neg (by norm_num) (by nlinarith [LogTables.log_5_gt])
  have h_exp_u : Real.exp (- (8 / 5 : ℝ)) ≤ Real.exp (-2 * Real.sqrt u) :=
    Real.exp_le_exp.mpr (by linarith)
  have h_exp : (1 / 5 : ℝ) ≤ Real.exp (-2 * Real.sqrt u) := le_trans h_exp_base h_exp_u
  nlinarith [hu_mul, h_exp]

-- Helper for corollary_14_small_adm when 16/25 < u ≤ 9/4.
private lemma corollary_14_small_adm_case2 (u : ℝ) (hu_pos : 0 < u) (hu64' : (16 / 25 : ℝ) < u) (hu94 : u ≤ (9 / 4 : ℝ)) :
    (1 : ℝ) ≤ 121.0961 * (u * Real.sqrt u) * Real.exp (-2 * Real.sqrt u) := by
  have hsqrt_lower : (4 / 5 : ℝ) ≤ Real.sqrt u :=
    (Real.le_sqrt (by norm_num) hu_pos.le).2 (by nlinarith [hu64'])
  have hu_mul : (64 / 125 : ℝ) ≤ u * Real.sqrt u := by
    nlinarith [hu64', hsqrt_lower]
  have h_exp_base : (1 / 25 : ℝ) ≤ Real.exp (-3 : ℝ) := by
    apply inv_le_exp_neg (by norm_num)
    have hlog25 : (3 : ℝ) ≤ Real.log 25 := by
      rw [show (25 : ℝ) = (5 : ℝ) ^ 2 by norm_num, Real.log_pow]
      exact le_of_lt (by norm_cast; nlinarith [LogTables.log_5_gt])
    linarith
  have h_exp_u : Real.exp (-3 : ℝ) ≤ Real.exp (-2 * Real.sqrt u) := by
    refine Real.exp_le_exp.mpr ?_
    have hsqrt_upper : Real.sqrt u ≤ (3 / 2 : ℝ) :=
      (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hu94]⟩
    linarith
  have h_exp : (1 / 25 : ℝ) ≤ Real.exp (-2 * Real.sqrt u) := le_trans h_exp_base h_exp_u
  nlinarith [hu_mul, h_exp]

-- Helper for corollary_14_small_adm when 9/4 < u ≤ 30 / 5.5666305.
private lemma corollary_14_small_adm_case3 (u : ℝ) (hu_pos : 0 < u) (hu94' : (9 / 4 : ℝ) < u) (hu_le : u ≤ 30 / 5.5666305) :
    (1 : ℝ) ≤ 121.0961 * (u * Real.sqrt u) * Real.exp (-2 * Real.sqrt u) := by
  have hsqrt_lower : (3 / 2 : ℝ) ≤ Real.sqrt u :=
    (Real.le_sqrt (by norm_num) hu_pos.le).2 (by nlinarith [hu94'])
  have hu_mul : (27 / 8 : ℝ) ≤ u * Real.sqrt u := by
    nlinarith [hu94', hsqrt_lower]
  have hsqrt_upper : Real.sqrt u ≤ (47 / 20 : ℝ) :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hu_le]⟩
  have h_exp_base : (1 / 115 : ℝ) ≤ Real.exp (- (47 / 10 : ℝ)) := by
    apply inv_le_exp_neg (by norm_num)
    have hlog115 : (47 / 10 : ℝ) ≤ Real.log 115 := by
      have h115 : (115 : ℝ) = 23 * 5 := by norm_num
      rw [h115, Real.log_mul (by norm_num) (by norm_num)]
      nlinarith [LogTables.log_23_gt, LogTables.log_5_gt]
    linarith
  have h_exp_u : Real.exp (- (47 / 10 : ℝ)) ≤ Real.exp (-2 * Real.sqrt u) :=
    Real.exp_le_exp.mpr (by linarith)
  have h_exp : (1 / 115 : ℝ) ≤ Real.exp (-2 * Real.sqrt u) := le_trans h_exp_base h_exp_u
  nlinarith [hu_mul, h_exp]

lemma corollary_14_small_adm :
    ∀ {x : ℝ}, 2 ≤ x → x ≤ Real.exp 30 →
    (1:ℝ) ≤ admissible_bound 121.0961 (3/2) 2 5.5666305 x := by
  intro x hx hx30
  let u : ℝ := Real.log x / 5.5666305
  have hu_pos : 0 < u := by
    have hlogx : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
    exact div_pos hlogx (by norm_num)
  have hu_ge : (31/250:ℝ) ≤ u := by
    have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h : (31/250:ℝ) * 5.5666305 ≤ Real.log x := by
      nlinarith [hlog2x, LogTables.log_2_gt]
    exact (le_div_iff₀ (by norm_num : (0:ℝ) < 5.5666305)).2 h
  have hu_le : u ≤ 30 / 5.5666305 := by
    have hlog : Real.log x ≤ 30 := by
      have := Real.log_le_log (by positivity : 0 < x) hx30
      simpa [Real.log_exp] using this
    have hdiv : Real.log x / 5.5666305 ≤ 30 / 5.5666305 :=
      div_le_div_of_nonneg_right hlog (by norm_num)
    simpa [u] using hdiv
  change (1:ℝ) ≤ 121.0961 * u ^ (3 / 2 : ℝ) * Real.exp (-2 * u ^ (1 / 2 : ℝ))
  have hu_pow : u ^ (3 / 2 : ℝ) = u * Real.sqrt u := by
    rw [show (3 / 2 : ℝ) = (1:ℝ) + (1 / 2 : ℝ) by norm_num]
    rw [Real.rpow_add hu_pos]
    simp [Real.sqrt_eq_rpow]
  have hu_sqrtpow : u ^ (1 / 2 : ℝ) = Real.sqrt u := by
    simp [Real.sqrt_eq_rpow]
  rw [hu_pow, hu_sqrtpow]
  by_cases hu64 : u ≤ (16/25:ℝ)
  · exact corollary_14_small_adm_case1 u hu_pos hu_ge hu64
  · have hu64' : (16/25:ℝ) < u := lt_of_not_ge hu64
    by_cases hu94 : u ≤ (9/4:ℝ)
    · exact corollary_14_small_adm_case2 u hu_pos hu64' hu94
    · have hu94' : (9/4:ℝ) < u := lt_of_not_ge hu94
      exact corollary_14_small_adm_case3 u hu_pos hu94' hu_le

-- Helper establishing ⌊30 / log 2⌋₊ = 43.
private lemma floor_30_div_log2_eq_43 : ⌊(30 : ℝ) / Real.log 2⌋₊ = 43 := by
  refine (Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ 30 / Real.log 2)).2 ⟨?_, ?_⟩
  · exact le_of_lt ((lt_div_iff₀ (Real.log_pos one_lt_two)).2 (by norm_num; linarith [LogTables.log_2_lt]))
  · exact (div_lt_iff₀ (Real.log_pos one_lt_two)).2 (by norm_num; linarith [LogTables.log_2_gt])

-- Helper bounding BKLNW.a₁ 30.
private lemma bklnw_a1_30_le : BKLNW.a₁ 30 ≤ 1 + 1.9339e-8 := by
  unfold BKLNW.a₁ BKLNW.Inputs.a₁
  have h40 : (40 : ℝ) ≤ Real.log (1e19) := by
    have h1e19 : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
    rw [h1e19, Real.log_pow]
    norm_num
    nlinarith [LogTables.log_10_gt]
  have hif : (30 : ℝ) ≤ 2 * Real.log (1e19) := by linarith [h40]
  have htable : BKLNW_app.table_8_ε (Real.log (1e19)) ≤ 1.9339e-8 :=
    BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_40 h40
  have hgoal : 1 + BKLNW_app.table_8_ε (Real.log (1e19)) ≤ 1 + 1.9339e-8 := by linarith
  simpa [BKLNW.Inputs.default, BKLNW.Pre_inputs.default, if_pos hif] using hgoal

-- Helper bounding BKLNW.f (exp 30).
private lemma bklnw_f_exp30_le : BKLNW.f (Real.exp 30) ≤ 41 := by
  unfold BKLNW.f
  have hfloor : ⌊(Real.log (Real.exp 30)) / Real.log 2⌋₊ = 43 := by
    rw [Real.log_exp]
    exact floor_30_div_log2_eq_43
  rw [hfloor]
  have hsum := rpow_sum_le_card (one_le_exp (by norm_num : (0 : ℝ) ≤ 30)) 43
  have hcard : (Finset.Icc (3 : ℕ) 43).card = 41 := by
    norm_num [Nat.card_Icc]
  exact le_trans hsum (by simp [hcard])

-- Helper bounding BKLNW.f (2^44).
private lemma bklnw_f_pow44_le : BKLNW.f ((2 ^ (44 : ℕ) : ℝ)) ≤ 42 := by
  unfold BKLNW.f
  have hfloor : ⌊(Real.log ((2 ^ (44 : ℕ) : ℝ))) / Real.log 2⌋₊ = 44 := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have hval : (Real.log ((2 ^ (44 : ℕ) : ℝ))) / Real.log 2 = (44 : ℝ) := by
      rw [show ((2 ^ (44 : ℕ) : ℝ)) = (2 : ℝ) ^ (44 : ℝ) by norm_num]
      rw [Real.log_rpow (by positivity), div_eq_iff hlog2]
    rw [hval]
    norm_num
  rw [hfloor]
  have hsum := rpow_sum_le_card (by norm_num : (1 : ℝ) ≤ 2 ^ (44 : ℕ)) 44
  have hcard : (Finset.Icc (3 : ℕ) 44).card = 42 := by
    norm_num [Nat.card_Icc]
  exact le_trans hsum (by simp [hcard])

-- Helper bounding BKLNW.a₂ 30.
private lemma bklnw_a2_30_le : BKLNW.a₂ 30 ≤ 42.42 := by
  have hf_exp30 : BKLNW.f (Real.exp 30) ≤ 41 := bklnw_f_exp30_le
  have hf_pow44 : BKLNW.f ((2 ^ (44 : ℕ) : ℝ)) ≤ 42 := bklnw_f_pow44_le
  have hf_powExpr : BKLNW.f (2 ^ (⌊(30 : ℝ) / Real.log 2⌋₊ + 1)) ≤ 42 := by
    simpa [floor_30_div_log2_eq_43] using hf_pow44
  unfold BKLNW.a₂ BKLNW.Inputs.a₂
  have hmax : max (BKLNW.f (Real.exp 30)) (BKLNW.f (2 ^ (⌊(30 : ℝ) / Real.log 2⌋₊ + 1))) ≤ 42 :=
    max_le (le_trans hf_exp30 (by norm_num)) hf_powExpr
  have halpha_nonneg : (0 : ℝ) ≤ BKLNW.Inputs.default.α := by
    simp [BKLNW.Inputs.default, BKLNW_app.table_8_margin]
    norm_num
  have halpha : BKLNW.Inputs.default.α ≤ (0.01 : ℝ) := by
    simp [BKLNW.Inputs.default, BKLNW_app.table_8_margin]
    norm_num
  have hfac : (1 + BKLNW.Inputs.default.α) ≤ (1.01 : ℝ) := by linarith
  have hmul1 : (1 + BKLNW.Inputs.default.α) *
      max (BKLNW.f (Real.exp 30)) (BKLNW.f (2 ^ (⌊(30 : ℝ) / Real.log 2⌋₊ + 1))) ≤
      (1 + BKLNW.Inputs.default.α) * 42 :=
    mul_le_mul_of_nonneg_left hmax (by linarith)
  have hmul2 : (1 + BKLNW.Inputs.default.α) * 42 ≤ 1.01 * 42 :=
    mul_le_mul_of_nonneg_right hfac (by norm_num)
  linarith

-- Helper bounding the main asymptotic coefficient.
private lemma coeff_bound_30 :
    (1 / (121.096 : ℝ)) * (5.5666305 / 30) ^ (3 / 2 : ℝ) * Real.exp (2 * Real.sqrt (30 / 5.5666305)) ≤ 0.06865 := by
  let r : ℝ := 5.5666305 / 30
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hrpow : r ^ (3 / 2 : ℝ) = r * Real.sqrt r := by
    rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by norm_num]
    rw [Real.rpow_add hr_pos]
    simp [Real.sqrt_eq_rpow]
  have hsqrt_r : Real.sqrt r ≤ (43077 / 100000 : ℝ) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · norm_num
    · dsimp [r]
      norm_num
  have hrpow_bound : r ^ (3 / 2 : ℝ) ≤ r * (43077 / 100000 : ℝ) := by
    rw [hrpow]
    gcongr
  have hsqrt_u : Real.sqrt (30 / 5.5666305) ≤ (23215 / 10000 : ℝ) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · norm_num
    · norm_num
  have hexp104 : Real.exp (2 * Real.sqrt (30 / 5.5666305)) ≤ 104 := by
    have hpow : 2 * Real.sqrt (30 / 5.5666305) ≤ (4.643 : ℝ) := by
      nlinarith [hsqrt_u]
    have hlog104 : (4.643 : ℝ) ≤ Real.log 104 := by
      have h104 : (104 : ℝ) = 13 * 2 ^ (3 : ℕ) := by norm_num
      rw [h104, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
      have h : (4.643 : ℝ) < Real.log 13 + 3 * Real.log 2 := by
        nlinarith [LogTables.log_13_gt, LogTables.log_2_gt]
      linarith
    have : Real.exp (2 * Real.sqrt (30 / 5.5666305)) ≤ Real.exp (Real.log 104) :=
      Real.exp_le_exp.mpr (le_trans hpow hlog104)
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 104)] using this
  have hcoef_step :
      (1 / (121.096 : ℝ)) * r ^ (3 / 2 : ℝ) * Real.exp (2 * Real.sqrt (30 / 5.5666305))
      ≤ (1 / (121.096 : ℝ)) * (r * (43077 / 100000 : ℝ)) * 104 := by
    have hnonneg : 0 ≤ (1 / (121.096 : ℝ)) := by positivity
    have hmul1 : (1 / (121.096 : ℝ)) * r ^ (3 / 2 : ℝ) ≤ (1 / (121.096 : ℝ)) * (r * (43077 / 100000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hrpow_bound hnonneg
    have hmul2 : (1 / (121.096 : ℝ)) * r ^ (3 / 2 : ℝ) * Real.exp (2 * Real.sqrt (30 / 5.5666305))
        ≤ ((1 / (121.096 : ℝ)) * (r * (43077 / 100000 : ℝ))) * 104 :=
      mul_le_mul hmul1 hexp104 (by positivity) (by positivity)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul2
  have hnum : (1 / (121.096 : ℝ)) * (r * (43077 / 100000 : ℝ)) * 104 ≤ (0.06865 : ℝ) := by
    dsimp [r]
    norm_num
  have hmain :
      (1 / (121.096 : ℝ)) * r ^ (3 / 2 : ℝ) * Real.exp (2 * Real.sqrt (30 / 5.5666305)) ≤ (0.06865 : ℝ) :=
    le_trans hcoef_step hnum
  simpa [r] using hmain

-- Helper bounding ν_asymp.
private lemma nu_asymp_bound_30 : ν_asymp 121.096 (3 / 2 : ℝ) 2 5.5666305 (Real.exp 30) ≤ 8.25e-7 := by
  have hcoef :
      (1 / (121.096 : ℝ)) * (5.5666305 / 30) ^ (3 / 2 : ℝ) * Real.exp (2 * Real.sqrt (30 / 5.5666305)) ≤ 0.06865 := coeff_bound_30
  have ha1 : BKLNW.a₁ 30 ≤ 1 + 1.9339e-8 := bklnw_a1_30_le
  have ha2 : BKLNW.a₂ 30 ≤ 42.42 := bklnw_a2_30_le
  have h15 : Real.exp (-15 : ℝ) ≤ (1 / 3250000 : ℝ) :=
    (le_of_lt (LogTables.exp_neg_15_lt.trans_le (by norm_num)))
  have h20 : Real.exp (-20 : ℝ) ≤ (1 / 460000000 : ℝ) :=
    (le_of_lt (LogTables.exp_neg_20_lt.trans_le (by norm_num)))
  let coeff : ℝ := (1 / (121.096 : ℝ)) * (5.5666305 / 30) ^ (3 / 2 : ℝ) * Real.exp (2 * Real.sqrt (30 / 5.5666305))
  let c1 : ℝ := 1 + 1.9339e-8
  let c2 : ℝ := 42.42
  let rhsBracket : ℝ := 30 * (c1 * (1 / 3250000 : ℝ)) + 30 * (c2 * (1 / 460000000 : ℝ))
  have hpow1 : (Real.exp 30) ^ (- (1 : ℝ) / 2) = Real.exp (-15) := by
    calc
      (Real.exp 30) ^ (- (1 : ℝ) / 2) = Real.exp (30 * (- (1 : ℝ) / 2)) := (Real.exp_mul 30 (- (1 : ℝ) / 2)).symm
      _ = Real.exp (-15) := by ring_nf
  have hpow2 : (Real.exp 30) ^ (- (2 : ℝ) / 3) = Real.exp (-20) := by
    calc
      (Real.exp 30) ^ (- (2 : ℝ) / 3) = Real.exp (30 * (- (2 : ℝ) / 3)) := (Real.exp_mul 30 (- (2 : ℝ) / 3)).symm
      _ = Real.exp (-20) := by ring_nf
  have hνeq₀ : ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30)
      = coeff * (BKLNW.a₁ 30 * 30 * Real.exp (-15) + BKLNW.a₂ 30 * 30 * Real.exp (-20)) := by
    simp [ν_asymp, hpow1, hpow2, coeff]
  have hνeq : ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30)
      = coeff * (30 * (BKLNW.a₁ 30 * Real.exp (-15)) + 30 * (BKLNW.a₂ 30 * Real.exp (-20))) := by
    calc
      ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30)
          = coeff * (BKLNW.a₁ 30 * 30 * Real.exp (-15) + BKLNW.a₂ 30 * 30 * Real.exp (-20)) := hνeq₀
      _ = coeff * (30 * (BKLNW.a₁ 30 * Real.exp (-15)) + 30 * (BKLNW.a₂ 30 * Real.exp (-20))) := by
        ring
  rw [hνeq]
  have hbracket :
      30 * (BKLNW.a₁ 30 * Real.exp (-15)) + 30 * (BKLNW.a₂ 30 * Real.exp (-20))
      ≤ rhsBracket := by
    have hc1_nonneg : 0 ≤ c1 := by
      dsimp [c1]
      norm_num
    have hc2_nonneg : 0 ≤ c2 := by
      dsimp [c2]
      norm_num
    have he15_nonneg : 0 ≤ Real.exp (-15) := le_of_lt (Real.exp_pos _)
    have he20_nonneg : 0 ≤ Real.exp (-20) := le_of_lt (Real.exp_pos _)
    have h30_nonneg : (0 : ℝ) ≤ 30 := by norm_num
    have h1 : 30 * (BKLNW.a₁ 30 * Real.exp (-15)) ≤ 30 * (c1 * (1 / 3250000 : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha1 he15_nonneg) h30_nonneg)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h15 hc1_nonneg) h30_nonneg)
    have h2 : 30 * (BKLNW.a₂ 30 * Real.exp (-20)) ≤ 30 * (c2 * (1 / 460000000 : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha2 he20_nonneg) h30_nonneg)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h20 hc2_nonneg) h30_nonneg)
    exact add_le_add h1 h2
  have hcoef' : coeff ≤ 0.06865 := by simpa [coeff] using hcoef
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    have hinv : 0 ≤ (1 / (121.096 : ℝ)) := by norm_num
    have hpow : 0 ≤ (5.5666305 / 30 : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5.5666305 / 30) _
    have hexp : 0 ≤ Real.exp (2 * Real.sqrt (30 / 5.5666305)) := le_of_lt (Real.exp_pos _)
    exact mul_nonneg (mul_nonneg hinv hpow) hexp
  have hrhs_nonneg : 0 ≤ rhsBracket := by
    dsimp [rhsBracket]
    have h1nn : 0 ≤ 30 * (c1 * (1 / 3250000 : ℝ)) := by
      have hc1_nonneg : 0 ≤ c1 := by
        dsimp [c1]
        norm_num
      exact mul_nonneg (by norm_num) (mul_nonneg hc1_nonneg (by norm_num))
    have h2nn : 0 ≤ 30 * (c2 * (1 / 460000000 : ℝ)) := by
      have hc2_nonneg : 0 ≤ c2 := by
        dsimp [c2]
        norm_num
      exact mul_nonneg (by norm_num) (mul_nonneg hc2_nonneg (by norm_num))
    exact add_nonneg h1nn h2nn
  have hmul1 : coeff * (30 * (BKLNW.a₁ 30 * Real.exp (-15)) + 30 * (BKLNW.a₂ 30 * Real.exp (-20))) ≤ coeff * rhsBracket :=
    mul_le_mul_of_nonneg_left hbracket hcoeff_nonneg
  have hmul2 : coeff * rhsBracket ≤ 0.06865 * rhsBracket :=
    mul_le_mul_of_nonneg_right hcoef' hrhs_nonneg
  have hnum : 0.06865 * rhsBracket ≤ 8.25e-7 := by
    dsimp [rhsBracket]
    norm_num
  exact le_trans hmul1 (le_trans hmul2 hnum)

-- Helper establishing the classical bound for Eψ at exp 30.
private lemma epsi_classicalBound_30 : Eψ.classicalBound 121.096 (3 / 2) 2 5.5666305 (Real.exp 30) := by
  intro y hy
  have h2exp30 : (2 : ℝ) ≤ Real.exp 30 :=
    le_trans Real.exp_one_gt_two.le ((Real.exp_le_exp).2 (by norm_num : (1 : ℝ) ≤ 30))
  exact FKS.FKS_corollary_1_3 y (le_trans h2exp30 hy)

@[blueprint
  "fks2-corollary-14"
  (title := "FKS2 Corollary 14")
  (statement := /--
  We have an admissible bound for $E_\theta$ with $A = 121.0961$, $B=3/2$, $C=2$,
  $R = 5.5666305$, $x_0=2$.
  -/)
  (proof := /-- By Corollary \ref{fks_cor_13}, with $R = 5.5666305$, and using the admissible asymptotic bound for $E_\psi(x)$ with $A_\psi = 121.096$, $B = 3/2$, $C = 2$, for all $x \geq x_0 = e^{30}$, we can obtain $\nu_{asymp}(x_0) \leq 6.3376 \cdot 10^{-7}$, from which one can conclude an admissible asymptotic bound for $E_\theta(x)$ with $A_\theta = 121.0961$, $B = 3/2$, $C = 2$, for all $x \geq x_0 = e^{30}$. Additionally, the minimum value of $\varepsilon_{\theta,asymp}(x)$ for $2 \leq x \leq e^{30}$ is roughly $2.6271\ldots$ at $x=2$. The results found in \cite[Table 13 and 14]{BKLNW} give $E_\theta(x) \leq 1 < \varepsilon_{\theta,asymp}(2) \leq \varepsilon_{\theta,asymp}(x)$ for all $2 \leq x \leq e^{30}$. -/)
  (latexEnv := "corollary")
  (discussion := 672)]
theorem corollary_14 : Eθ.classicalBound 121.0961 (3 / 2) 2 5.5666305 2 := by
  have hsmall_adm :
      ∀ {x : ℝ}, 2 ≤ x → x ≤ Real.exp 30 →
      (1 : ℝ) ≤ admissible_bound 121.0961 (3 / 2) 2 5.5666305 x := corollary_14_small_adm

  have hfloor30 : ⌊(30 : ℝ) / Real.log 2⌋₊ = 43 := floor_30_div_log2_eq_43
  have ha1 : BKLNW.a₁ 30 ≤ 1 + 1.9339e-8 := bklnw_a1_30_le
  have ha2 : BKLNW.a₂ 30 ≤ 42.42 := bklnw_a2_30_le
  have hcoef :
      (1 / (121.096 : ℝ)) * (5.5666305 / 30) ^ (3 / 2 : ℝ) * Real.exp (2 * Real.sqrt (30 / 5.5666305)) ≤ 0.06865 := coeff_bound_30
  have hν : ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30) ≤ 8.25e-7 := nu_asymp_bound_30

  have hA : 121.096 * (1 + ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30)) ≤ 121.0961 := by
    nlinarith [hν]

  have hEψ30 : Eψ.classicalBound 121.096 (3 / 2) 2 5.5666305 (Real.exp 30) := epsi_classicalBound_30
  have hB : (3 / 2 : ℝ) > 2 ^ 2 / (8 * 5.5666305) := by norm_num
  have hEθ30 :
      Eθ.classicalBound (121.096 * (1 + ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30)))
        (3 / 2) 2 5.5666305 (Real.exp 30) :=
    proposition_13 121.096 (3 / 2) 2 5.5666305 (Real.exp 30) (by norm_num) (by norm_num) (exp_pos 30) (by rw [Real.log_exp]; norm_num) hEψ30 hB

  rw [Eθ.classicalBound]
  intro x hx
  by_cases hx30 : x ≤ Real.exp 30
  · have hx_pos : 0 < x := by linarith
    have hExp30_le_1e19 : Real.exp 30 ≤ (1e19 : ℝ) := by
      have h30lelog : (30 : ℝ) ≤ Real.log (1e19) := by
        have h1e19 : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
        rw [h1e19, Real.log_pow]
        norm_num
        nlinarith [LogTables.log_10_gt]
      have : Real.exp 30 ≤ Real.exp (Real.log (1e19)) := (Real.exp_le_exp).2 h30lelog
      simpa [Real.exp_log (by norm_num : (0 : ℝ) < 1e19)] using this
    have hx_le_1e19 : x ≤ (1e19 : ℝ) := le_trans hx30 hExp30_le_1e19
    have hθlt : θ x < x := BKLNW.buthe_eq_1_7 x ⟨hx_pos, hx_le_1e19⟩
    have hEθ1 : Eθ x ≤ 1 := by
      unfold Eθ
      have habs : |θ x - x| ≤ x := by
        have hleft : -x ≤ θ x - x := by linarith [theta_nonneg x]
        have hright : θ x - x ≤ x := by linarith [hθlt]
        exact abs_le.mpr ⟨hleft, hright⟩
      exact (div_le_iff₀ hx_pos).mpr (by nlinarith [habs])
    have hAdm1 : (1 : ℝ) ≤ admissible_bound 121.0961 (3 / 2) 2 5.5666305 x := hsmall_adm hx hx30
    exact le_trans hEθ1 hAdm1
  · have hx30' : Real.exp 30 ≤ x := le_of_lt (lt_of_not_ge hx30)
    have hmain : Eθ x ≤ admissible_bound
        (121.096 * (1 + ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30)))
        (3 / 2) 2 5.5666305 x := hEθ30 x hx30'
    have hlog_div_nonneg : 0 ≤ Real.log x / 5.5666305 := by
      have hx_ge1 : (1 : ℝ) ≤ x := by
        have h1exp30 : (1 : ℝ) < Real.exp 30 := (Real.one_lt_exp_iff).2 (by norm_num : (0 : ℝ) < 30)
        exact le_trans h1exp30.le hx30'
      exact div_nonneg (Real.log_nonneg hx_ge1) (by norm_num)
    have hpow_nonneg : 0 ≤ (Real.log x / 5.5666305) ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg hlog_div_nonneg _
    have hexp_nonneg : 0 ≤ Real.exp (-2 * (Real.log x / 5.5666305) ^ ((1 : ℝ) / (2 : ℝ))) := by positivity
    have hAmono : admissible_bound
        (121.096 * (1 + ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30)))
        (3 / 2) 2 5.5666305 x ≤ admissible_bound 121.0961 (3 / 2) 2 5.5666305 x := by
      let t : ℝ := (Real.log x / 5.5666305) ^ (3 / 2 : ℝ)
      let e : ℝ := Real.exp (-2 * (Real.log x / 5.5666305) ^ ((1 : ℝ) / (2 : ℝ)))
      have ht_nonneg : 0 ≤ t := by simpa [t] using hpow_nonneg
      have he_nonneg : 0 ≤ e := by simpa [e] using hexp_nonneg
      have hAt :
          (121.096 * (1 + ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30))) * t ≤ 121.0961 * t :=
        mul_le_mul_of_nonneg_right hA ht_nonneg
      have hAte :
          ((121.096 * (1 + ν_asymp 121.096 (3 / 2) 2 5.5666305 (Real.exp 30))) * t) * e ≤
          (121.0961 * t) * e :=
        mul_le_mul_of_nonneg_right hAt he_nonneg
      unfold admissible_bound
      simpa [t, e, mul_assoc, mul_left_comm, mul_comm] using hAte
    exact le_trans hmain hAmono



theorem remark_15' (x₀ : ℝ) (hx₀_pos : 0 < x₀) (h : log x₀ ≥ 1000) :
    Eθ.classicalBound ((FKS.A x₀) * (1 + remark_15_margin)) (3 / 2) 2 5.5666305 x₀ := by
    have hν : ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ ≤ (1 + remark_15_margin) - 1 := by
      exact nu_asymp_le_remark_15_margin_sub_one x₀ h
    have hEψ : Eψ.classicalBound (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ :=
      FKS.theorem_1_2b x₀ h
    have hB : (3 / 2 : ℝ) > 2 ^ 2 / (8 * (5.5666305 : ℝ)) := by
      have hR : (0 : ℝ) < 5.5666305 := by norm_num
      have hden : (0 : ℝ) < 8 * (5.5666305 : ℝ) := by nlinarith
      have : (2 ^ 2 : ℝ) / (8 * (5.5666305 : ℝ)) < (3 / 2 : ℝ) := by
        refine (div_lt_iff₀ hden).2 ?_
        nlinarith [hR]
      simpa using this
    have hA_pos : FKS.A x₀ > 0 := by linarith [FKS_A_one_le x₀ h]
    have hx₀_ge7 : 7 ≤ Real.log x₀ := by linarith
    have hθ :
        Eθ.classicalBound ((FKS.A x₀) * (1 + ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀))
          (3 / 2) 2 5.5666305 x₀ :=
      proposition_13 (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ hA_pos (by norm_num) hx₀_pos hx₀_ge7 hEψ hB
    have hA_nonneg : 0 ≤ FKS.A x₀ := by
      have hbound₀ : Eψ (exp (log x₀)) ≤ admissible_bound (FKS.A x₀) (3 / 2) 2 5.5666305 (exp (log x₀)) :=
        hEψ (exp (log x₀)) (Real.le_exp_log x₀)
      have hEψ_nonneg : 0 ≤ Eψ (exp (log x₀)) := by
        unfold Eψ
        positivity
      have hlogx₀_pos : 0 < log x₀ := by linarith
      have hR : (0 : ℝ) < 5.5666305 := by norm_num
      have hlogx₀R_pos : 0 < log x₀ / (5.5666305 : ℝ) := div_pos hlogx₀_pos hR
      have hfactor_pos :
          0 <
            (log x₀ / (5.5666305 : ℝ)) ^ (3 / 2 : ℝ) *
              exp (-2 * (log x₀ / (5.5666305 : ℝ)) ^ ((1 : ℝ) / (2 : ℝ))) := by
        exact mul_pos (Real.rpow_pos_of_pos hlogx₀R_pos _) (Real.exp_pos _)
      have hbound₀' :
          Eψ (exp (log x₀)) ≤
            (FKS.A x₀) *
              ((log x₀ / (5.5666305 : ℝ)) ^ (3 / 2 : ℝ) *
                exp (-2 * (log x₀ / (5.5666305 : ℝ)) ^ ((1 : ℝ) / (2 : ℝ)))) := by
        simpa [admissible_bound, Real.log_exp, mul_assoc, mul_left_comm, mul_comm] using hbound₀
      have hmul_nonneg :
          0 ≤
            (FKS.A x₀) *
              ((log x₀ / (5.5666305 : ℝ)) ^ (3 / 2 : ℝ) *
                exp (-2 * (log x₀ / (5.5666305 : ℝ)) ^ ((1 : ℝ) / (2 : ℝ)))) := by
        linarith
      have hmul_nonneg' :
          0 ≤
            ((log x₀ / (5.5666305 : ℝ)) ^ (3 / 2 : ℝ) *
                exp (-2 * (log x₀ / (5.5666305 : ℝ)) ^ ((1 : ℝ) / (2 : ℝ)))) *
              (FKS.A x₀) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_nonneg
      exact nonneg_of_mul_nonneg_right hmul_nonneg' hfactor_pos
    have hA :
        (FKS.A x₀) * (1 + ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀) ≤
          (FKS.A x₀) * (1 + remark_15_margin) := by
      have h1 : 1 + ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ ≤ 1 + remark_15_margin := by
        linarith
      exact mul_le_mul_of_nonneg_left h1 hA_nonneg
    intro x hx
    have hrpow_nonneg : 0 ≤ (log x / (5.5666305 : ℝ)) ^ (3 / 2 : ℝ) := by
      by_cases hbase : 0 ≤ log x / (5.5666305 : ℝ)
      · exact Real.rpow_nonneg hbase _
      · have hbase' : log x / (5.5666305 : ℝ) ≤ 0 := le_of_not_ge hbase
        rw [Real.rpow_def_of_nonpos hbase']
        have hcos : Real.cos ((3 / 2 : ℝ) * π) = 0 := by
          have hsplit : ((3 / 2 : ℝ) * π) = π / 2 + π := by ring
          rw [hsplit, Real.cos_add_pi]
          norm_num [Real.cos_pi_div_two]
        rw [hcos]
        norm_num
    have hθx := hθ x hx
    unfold admissible_bound at hθx ⊢
    have hA' :
        ((FKS.A x₀) * (1 + ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀)) *
            (log x / (5.5666305 : ℝ)) ^ (3 / 2 : ℝ) ≤
          ((FKS.A x₀) * (1 + remark_15_margin)) * (log x / (5.5666305 : ℝ)) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hA hrpow_nonneg
    exact le_trans hθx (mul_le_mul_of_nonneg_right hA' (Real.exp_nonneg _))


@[blueprint
  "fks2-remark-15"
  (title := "FKS2 Remark 15")
  (statement := /--
  If $\log x_0 \geq 1000$ then we have an admissible bound for $E_\theta$ with the indicated
  choice of $A(x_0)$, $B = 3/2$, $C = 2$, and $R = 5.5666305$.
  -/)
  (latexEnv := "remark")
  (proof := /-- From \cite[Table 6]{FKS} we have $\nu_{asymp}(x_0) \leq 10^{-200}$. Thus, one easily verifies that the rounding up involved in forming \cite[Table 6]{FKS} exceeds the rounding up also needed to apply this step. Consequently we may use values from $A_\theta$ taken from \cite[Table 6]{FKS} directly but this does, in contrast to Corollary \ref{fks2-corollary-14}, require the assumption $x > x_0$, as per that table. -/)
  (discussion := 674)]
theorem remark_15 (x₀ : ℝ) (hx₀_pos : 0 < x₀) (h : log x₀ ≥ 1000) :
    Eθ.classicalBound ((FKS.A x₀) * (1 + ν_asymp (FKS.A x₀) (3 / 2) 2 5.5666305 x₀)) (3 / 2) 2 5.5666305 x₀ := by
  have hEψ : Eψ.classicalBound (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ :=
    FKS.theorem_1_2b x₀ h
  have hB : (3 / 2 : ℝ) > 2 ^ 2 / (8 * (5.5666305 : ℝ)) := by
    have hR : (0 : ℝ) < 5.5666305 := by norm_num
    have hden : (0 : ℝ) < 8 * (5.5666305 : ℝ) := by nlinarith
    -- Use (div_lt_iff₀ hden) to clear the denominator.
    have : (2 ^ 2 : ℝ) / (8 * (5.5666305 : ℝ)) < (3 / 2 : ℝ) := by
      refine (div_lt_iff₀ hden).2 ?_
      -- Goal: 2^2 < (3/2) * (8*R), which is immediate numerically.
      nlinarith [hR]
    simpa using this
  have hA_pos : FKS.A x₀ > 0 := by linarith [FKS_A_one_le x₀ h]
  have hx₀_ge7 : 7 ≤ Real.log x₀ := by linarith
  simpa using proposition_13 (FKS.A x₀) (3 / 2) 2 5.5666305 x₀ hA_pos (by norm_num) hx₀_pos hx₀_ge7 hEψ hB

theorem l0 {x y : ℝ} (hx : 2 ≤ x) (hy : x ≤ y) :
    ContinuousOn (fun t ↦ (t * log t ^ 2)⁻¹) (Set.uIcc x y) := by
  refine ContinuousOn.inv₀ (continuousOn_id.mul (ContinuousOn.pow (ContinuousOn.log
    continuousOn_id fun y hy ↦ ?_) 2)) fun y hy ↦ ?_
  repeat simp_all; grind

theorem Li_identity {x} (hx : 2 ≤ x) :
    Li x = x / log x - 2 / log 2 + ∫ t in 2..x, 1 / (log t ^ 2) := by
  have hnt {t} (ht : t ∈ Set.uIcc 2 x) : t ≠ 0 := by simp_all; linarith
  rw [Li, funext fun t ↦ (mul_one (1 / log t)).symm,
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun t ↦ 1 / log t)
    (u' := fun t ↦ -(1 / t) / log t ^ 2) _ (fun t _ ↦ hasDerivAt_id' t) _
    intervalIntegrable_const]
  · suffices ∫ (x : ℝ) in 2..x, - (1 / x) / log x ^ 2 * x
      = ∫ (x : ℝ) in 2..x, - (1 / (log x ^ 2)) from by
      rw [this, intervalIntegral.integral_neg]; ring
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    ring_nf
    rw [mul_inv_cancel₀ (hnt ht), one_mul]
  · intro t ht
    simpa using! HasDerivAt.inv (hasDerivAt_log (hnt ht)) (by simp_all; grind)
  · simp only [neg_div, div_div]
    simpa using! (l0 (refl 2) hx).intervalIntegrable.neg

theorem l1 {x y} (hx : 2 ≤ x) (hy : x ≤ y) :
    IntervalIntegrable (fun t ↦ θ t / (t * log t ^ 2)) volume x y := by
  simpa [div_eq_mul_inv] using theta_mono.intervalIntegrable.mul_continuousOn (l0 hx hy)

theorem l2 {x y} (hx : 2 ≤ x) (hy : x ≤ y) :
    IntervalIntegrable (fun t ↦ t / (t * log t ^ 2)) volume x y := by
  simpa [div_eq_mul_inv] using intervalIntegral.intervalIntegrable_id.mul_continuousOn (l0 hx hy)

theorem he {x} (hx : 2 ≤ x) : pi x - Li x = (θ x - x) / log x + 2 / log 2
  + ∫ t in 2..x, (θ t - t) / (t * log t ^ 2) := by
  simp only [RS_prime.eq_417 hx, Li_identity hx, sub_div,
    intervalIntegral.integral_sub (l1 (refl 2) hx) (l2 (refl 2) hx)]
  rw [intervalIntegral.integral_congr fun t ht ↦ div_mul_cancel_left₀ _ ((log t) ^ 2)]
  · ring_nf
  · simp_all; grind

theorem l3 {x y} (hx : 2 ≤ x) (hy : x ≤ y) :
    IntervalIntegrable (fun t ↦ (θ t - t) / (t * log t ^ 2)) volume x y := by
  simpa [sub_div] using (l1 hx hy).sub (l2 hx hy)

blueprint_comment /--
\subsection{From asymptotic estimates on theta to asymptotic estimates on pi}

To get from asymptotic estimates on $E_\theta$ to asymptotic estimates on $E_\pi$, one first needs a way to express the latter as an integral of the former.
-/
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
theorem eq_17 {x₀ x : ℝ} (hx₀ : 2 ≤ x₀) (hx : x₀ < x) :
    (pi x - Li x) - (pi x₀ - Li x₀) =
    (θ x - x) / log x - (θ x₀ - x₀) / log x₀ +
    ∫ t in x₀..x, (θ t - t) / (t * log t ^ 2) :=
  have px : 2 ≤ x := by linarith
  calc
  _ = (θ x - x) / log x - (θ x₀ - x₀) / log x₀ + ((∫ t in 2..x, (θ t - t) / (t * log t ^ 2)) -
    ∫ t in 2..x₀, (θ t - t) / (t * log t ^ 2)) := by rw [he px, he hx₀]; ring
  _ = (θ x - x) / log x - (θ x₀ - x₀) / log x₀ + ∫ t in x₀..x, (θ t - t) / (t * log t ^ 2) := by
    rw [intervalIntegral.integral_interval_sub_left]
    · simpa [sub_div] using l3 (refl 2) px
    · simpa [sub_div] using l3 (refl 2) hx₀

blueprint_comment /--
The following definition is only implicitly in FKS2, but will be convenient:
-/

@[blueprint
  "fks2-error-def"
  (title := "Defining an error term")
  (statement := /--
  For any $x_0>0$, we define
  $$\delta(x_0) := |\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}|.$$
  -/)]
noncomputable def δ (x₀ : ℝ) : ℝ :=
  |(pi x₀ - Li x₀) / (x₀ / log x₀) - (θ x₀ - x₀) / x₀|

blueprint_comment /--
We can now obtain an upper bound on $E_\pi$ in terms of $E_\theta$:
-/

@[blueprint
  "fks2-eq-30"
  (title := "FKS2 Equation (30)")
  (statement := /--
  For any $x \geq x_0 > 0$,
  $$ |\pi(x) - \Li(x)| \leq \left| \frac{\theta(x) - x}{\log(x)} \right| + \left| \pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)} \right| + \left| \int_{x_0}^{x} \frac{\theta(t) - t}{t(\log(t))^2} \, dt \right|. $$
  -/)
  (proof := /-- This follows from applying the triangle inequality to Sublemma \ref{fks2-eq-17}. -/)
  (latexEnv := "sublemma")
  (discussion := 741)]
theorem eq_30 {x x₀ : ℝ} (hx : x ≥ x₀) (hx₀ : x₀ ≥ 2) :
  Eπ x ≤ Eθ x + (log x / x) * (x₀ / log x₀) * δ x₀ + (log x / x) * ∫ t in x₀..x, Eθ t / log t ^ 2 := by
  -- NOTE: the hypothesis `hx₀` was added to apply `eq_17`.
  -- It is not present in the original source material [FKS2].
  have : (log x / x) * (x₀ / log x₀) * δ x₀ = (log x / x) * |pi x₀ - Li x₀ - (θ x₀ - x₀) / log x₀| := by
    unfold δ
    have : log x₀ > 0 := log_pos (by linarith)
    field_simp
    rw [abs_div, abs_of_nonneg (by linarith : x₀ ≥ 0), abs_div, abs_of_pos this]
    field_simp
  rw [this]; unfold Eπ Eθ
  field_simp [(by linarith : x > 0)]
  calc
    _ = |pi x - Li x - (pi x₀ - Li x₀) + pi x₀ - Li x₀| * log x := by ring_nf
    _ = |(θ x - x) / log x
        + (pi x₀ - Li x₀ - (θ x₀ - x₀) / log x₀)
        + (∫ t in x₀..x, (θ t - t) / (t * log t ^ 2))| * log x := by
      by_cases h : x = x₀
      · rw [h, intervalIntegral.integral_same]; ring_nf
      · congr
        rw [eq_17 hx₀ (lt_of_le_of_ne hx (Ne.symm h))]
        ring
    _ ≤ |(θ x - x) / log x| * log x
        + |pi x₀ - Li x₀ - (θ x₀ - x₀) / log x₀| * log x
        + |∫ t in x₀..x, (θ t - t) / (t * log t ^ 2)| * log x := by
      rw [← distrib_three_right]; gcongr
      · exact log_nonneg (by linarith)
      · exact abs_add_three _ _ _
    _ ≤ |θ x - x|
        + log x * |pi x₀ - Li x₀ - (θ x₀ - x₀) / log x₀|
        + log x * ∫ t in x₀..x, |θ t - t| / (t * log t ^ 2) := by
      have : log x > 0 := log_pos (by linarith)
      rw [abs_div, abs_of_pos this]
      field_simp [this]
      gcongr
      have : ∫ t in x₀..x, |θ t - t| / (t * log t ^ 2) = ∫ t in x₀..x, |(θ t - t) / (t * log t ^ 2)| := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [Set.uIoc_of_le hx, Set.mem_Ioc] at ht
        have : t * log t ^ 2 ≥ 0 := mul_nonneg (by linarith) (pow_two_nonneg (log t))
        rw [abs_div, abs_of_nonneg this]
      simp only [this, intervalIntegral.abs_integral_le_integral_abs hx]

blueprint_comment /--
Next, we bound the integral appearing in Sublemma \ref{fks2-eq-17}.
-/

@[blueprint
  "fks2-lemma-12"
  (title := "FKS2 Lemma 12")
  (statement := /--
  Suppose that $E_\theta$ satisfies an admissible classical bound with parameters $A,B,C,R,x_0$.
  Then, for all $x \geq x_0$,
  $$ \int_{x_0}^x \left|\frac{E_\theta(t)}{\log^2 t} dt\right| \leq \frac{2A}{R^B} x m(x_0,x)
    \exp\left(-C \sqrt{\frac{\log x}{R}}\right) D_+\left( \sqrt{\log x} - \frac{C}{2\sqrt{R}} \right)$$
  where
  $$ m(x_0,x) = \max ( (\log x_0)^{(2B-3)/2}, (\log x)^{(2B-3)/2} ). $$
  -/)
  (proof := /--
NOTE: in order for the proof to work, some lower bounds on $x_0$ were added to make various limits of integration non-negative.

  Since $\varepsilon_{\theta,\mathrm{asymp}}(t)$ provides an admissible bound on $\theta(t)$ for all $t \geq x_0$, we have
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
theorem lemma_12 {A B C R x₀ x : ℝ} (hEθ : Eθ.classicalBound A B C R x₀) (hx : x ≥ x₀)
    (hx₀ : 2 ≤ x₀) (hR : 0 < R) (hA : 0 ≤ A) (h : 0 ≤ √(log x₀) - C / (2 * √R)) :
  ∫ t in x₀..x, |Eθ t| / log t ^ 2 ≤
    (2 * A) / (R ^ B) * x * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) *
    exp (-C * sqrt (log x / R)) * dawson (sqrt (log x) - C / (2 * sqrt R)) := by
  have log_t_ne_zero : ∀ t ∈ Set.uIcc x₀ x, log t ≠ 0 := fun t ht ↦ (by simp; grind [Set.uIcc_of_le hx])
  have t_ne_zero : ∀ t ∈ Set.uIcc x₀ x, t ≠ 0 := fun t ht ↦ (by grind [Set.uIcc_of_le hx])
  have t_pos : ∀ t ∈ Set.uIcc √(log x₀) √(log x), 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le (by gcongr)] at ht
    apply lt_of_lt_of_le _ ht.1
    exact sqrt_pos.mpr (log_pos (by linarith))
  calc
  _ ≤ ∫ t in x₀..x, |admissible_bound A B C R t| / log t ^ 2 := by
    apply intervalIntegral.integral_mono_on hx
    · refine IntervalIntegrable.mul_continuousOn ?_ (by fun_prop (disch := grind))
      unfold Eθ
      apply IntervalIntegrable.abs
      refine IntervalIntegrable.mul_continuousOn ?_ (by fun_prop (disch := grind))
      refine IntervalIntegrable.abs <| IntervalIntegrable.sub ?_ intervalIntegral.intervalIntegrable_id
      apply intervalIntegrable_iff_integrableOn_Icc_of_le hx|>.mpr
      conv => arg 1; ext x; rw [← one_mul (θ x), theta_eq_sum_Icc, Finset.sum_filter]
      apply  integrableOn_mul_sum_Icc _ (by linarith)
      apply ContinuousOn.integrableOn_Icc
      fun_prop
    · apply IntervalIntegrable.mul_continuousOn
      · apply IntervalIntegrable.abs
        apply ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
        unfold admissible_bound
        fun_prop (disch := grind)
      · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
        fun_prop (disch := grind)
    · intro t ht
      specialize hEθ t ht.1
      gcongr
      unfold Eθ
      exact div_nonneg (by positivity) (by grind)
  _ = ∫ (t : ℝ) in x₀..x, A * (log t / R) ^ B * rexp (-C * (log t / R) ^ ((1 : ℝ) / 2)) / log t ^ 2 := by
    unfold admissible_bound
    apply intervalIntegral.integral_congr fun t ht ↦ ?_
    congr
    rw [abs_of_nonneg]
    refine mul_nonneg ?_ (by positivity)
    refine mul_nonneg hA <| rpow_nonneg (div_nonneg ?_ hR.le) _
    exact log_nonneg (by grind [Set.uIcc_of_le hx])
  _ = ∫ (t : ℝ) in x₀..x, A / R ^ B * (log t ^ (B - 2) * rexp (-C * (log t / R) ^ ((1 : ℝ) / 2))) := by
    apply intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [div_rpow (log_nonneg (by grind[Set.uIcc_of_le hx])) hR.le, rpow_sub (log_pos (by grind[Set.uIcc_of_le hx])), rpow_ofNat]
    field
  _ = A / R ^ B * ∫ (t : ℝ) in x₀..x, log t ^ (B - 2) * rexp (-C * (log t / R) ^ ((1 : ℝ) / 2)) := by
    rw [intervalIntegral.integral_const_mul]
  _ =  A / R ^ B * ∫ (t : ℝ) in √(log x₀)..√(log x), (t ^ 2) ^ (B - 2) * rexp (-C * (t ^ 2 / R) ^ ((1 : ℝ) / 2)) * (2 * t * rexp (t ^ 2)) := by
    have subst := intervalIntegral.integral_comp_mul_deriv' (f := (fun t ↦ rexp (t ^ 2))) (g := (fun t ↦ log t ^ (B - 2) * rexp (-C * (log t / R) ^ ((1 : ℝ) / 2)))) (f' := (fun t ↦ 2 * t * rexp (t ^ 2))) (a := x₀.log.sqrt) (b := x.log.sqrt)
    have left : rexp (x₀.log.sqrt ^ 2) = x₀ := by
      rw [sq_sqrt (log_nonneg (by linarith)), exp_log (by linarith)]
    have right : rexp (x.log.sqrt ^ 2) = x := by
      rw [sq_sqrt (log_nonneg (by linarith)), exp_log (by linarith)]
    simp_rw [left, right] at subst
    simp only [Function.comp_apply, log_exp] at subst
    rw [← subst]
    · intro t ht
      have := hasDerivAt_pow 2 t
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
      convert! hasDerivAt_exp (t ^ 2) |>.comp t this using 1
      ring
    · fun_prop
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      simp only [Set.mem_image] at ht
      rcases ht with ⟨y, ⟨hy1, hy2⟩⟩
      rw [Set.uIcc_of_le (by gcongr)] at hy1
      have : log t ≠ 0 := by
        rw [← hy2, log_exp]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
        have : √(log x₀) > 0 := by
          exact sqrt_pos.mpr <| log_pos (by linarith)
        linarith [hy1.1]
      have : t ≠ 0 := by
        rw [← hy2]
        exact exp_ne_zero _
      fun_prop (disch := grind)
  _ = A / R ^ B * ∫ (t : ℝ) in √(log x₀)..√(log x), 2 * t ^ (2 * B - 4) * t * rexp (-C * (t ^ 2 / R) ^ ((1 : ℝ) / 2)) * rexp (t ^ 2) := by
    congr 1
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [← rpow_ofNat, ← rpow_mul (t_pos t ht).le]
    ring_nf
  _ = A / R ^ B * ∫ (t : ℝ) in √(log x₀)..√(log x), 2 * t ^ (2 * B - 3) * rexp (-C * (t ^ 2 / R) ^ ((1 : ℝ) / 2) + t ^ 2) := by
    congr 1
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [exp_add, (by ring : 2 * B - 3 = (2 * B - 4)+ 1), rpow_add <| t_pos t ht, rpow_one]
    ring
  _ = A / R ^ B * ∫ (t : ℝ) in √(log x₀)..√(log x), 2 * (t ^ (2 * B - 3) * rexp (t ^ 2 - C * t / √R)) := by
    congr 1
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [← sqrt_eq_rpow, sqrt_div (by positivity), sqrt_sq (t_pos t ht).le]
    ring_nf
  _ = 2 * A / R ^ B * ∫ (t : ℝ) in √(log x₀)..√(log x), t ^ (2 * B - 3) * rexp (t ^ 2 - C * t / √R) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  _ ≤ 2 * A / R ^ B * ∫ (t : ℝ) in √(log x₀)..√(log x), max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) * rexp (t ^ 2 - C * t / √R) := by
    gcongr
    apply intervalIntegral.integral_mono_on (by gcongr)
    · apply ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      fun_prop (disch := grind)
    · apply ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      fun_prop
    · intro t ht
      gcongr
      by_cases! h : 0 ≤ 2 * B - 3
      · apply le_max_of_le_right
        grw [ht.2, sqrt_eq_rpow, ← rpow_mul]
        · field_simp; rfl
        · apply log_nonneg (by linarith)
        · exact le_trans (sqrt_nonneg _) ht.1
      · apply le_max_of_le_left
        trans (√(log x₀)) ^ (2 * B - 3)
        · apply rpow_le_rpow_of_nonpos _ ht.1 h.le
          exact sqrt_pos.mpr (log_pos (by linarith))
        · rw [sqrt_eq_rpow, ← rpow_mul]
          · field_simp; rfl
          · exact log_nonneg (by linarith)
  _ = 2 * A / R ^ B * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) * ∫ (t : ℝ) in √(log x₀)..√(log x), rexp (t ^ 2 - C * t / √R) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  _ = 2 * A / R ^ B * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) * ∫ (t : ℝ) in √(log x₀)..√(log x), rexp ((t - C / (2 * √R)) ^ 2 + (-C ^ 2 / (4 * R))) := by
    congr 1
    apply intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [sub_sq, div_pow, mul_pow, sq_sqrt hR.le]
    ring_nf
  _ = 2 * A / R ^ B * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) * ∫ (t : ℝ) in √(log x₀)..√(log x), rexp (-C ^ 2 / (4 * R)) * rexp ((t - C / (2 * √R)) ^ 2) := by
    congr 1
    apply intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [exp_add]
    ring
  _ = 2 * A / R ^ B * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) * rexp (-C ^ 2 / (4 * R)) * ∫ (t : ℝ) in √(log x₀)..√(log x), rexp ((t - C / (2 * √R)) ^ 2) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  _ = 2 * A / R ^ B * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) * rexp (-C ^ 2 / (4 * R)) * ∫ (t : ℝ) in (√(log x₀)  - C / (2 * √R))..(√(log x)  - C / (2 * √R)), rexp (t ^ 2) := by
    rw [intervalIntegral.integral_comp_sub_right (f := (fun t ↦ rexp (t ^ 2)))]
  _ ≤ 2 * A / R ^ B * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) * rexp (-C ^ 2 / (4 * R)) * ∫ (t : ℝ) in 0..(√(log x)  - C / (2 * √R)), rexp (t ^ 2) := by
    gcongr
    · bound
    · apply intervalIntegral.integral_mono_interval h (by gcongr) (by rfl)
      · filter_upwards [] with t using exp_nonneg (t ^ 2)
      · apply Continuous.intervalIntegrable
        fun_prop
  _ = _ := by
    unfold dawson
    rw [sub_sq, sq_sqrt (log_nonneg (by linarith)), div_pow, mul_pow, sq_sqrt hR.le, ← mul_assoc]
    congr 1
    ac_change 2 * A / R ^ B * (max (log x₀ ^ ((2 * B - 3) / 2)) (log x ^ ((2 * B - 3) / 2)) * rexp (-C ^ 2 / (4 * R))) =
      2 * A / R ^ B * (max (log x₀ ^ ((2 * B - 3) / 2)) (log x ^ ((2 * B - 3) / 2)) * (x * rexp (-C * √(log x / R)) *
      rexp (-(log x - 2 * √(log x) * (C / (2 * √R)) + C ^ 2 / (2 ^ 2 * R)))))
    congr 2
    have : x = exp (log x) := by rw [exp_log (by linarith)]
    nth_rw 1 [this]
    rw [← exp_add, ← exp_add, sqrt_div (log_nonneg (by linarith))]
    ring_nf

@[blueprint
  "fks2-eq-9"
  (title := "mu asymptotic function, FKS2 (9)")
  (statement := /--
  For $x_0,x_1 > 0$, we define
  $$ \mu_{asymp}(x_0,x_1) := \frac{x_0 \log(x_1)}{\epsilon_{\theta,asymp}(x_1) x_1 \log(x_0)}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| +
    \frac{2D_+\bigl(\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}}\bigr)}{\sqrt{\log x_1}}$.
  -/)]
noncomputable def μ_asymp (A B C R x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / ((admissible_bound A B C R x₁) * x₁ * log x₀) * δ x₀ +
    2 * (dawson (sqrt (log x₁) - C / (2 * sqrt R))) / (sqrt (log x₁))

blueprint_comment /--
We obtain our final bound for converting bounds on $E_\theta$ to bounds on $E_\pi$.
-/

/- The following lemmas are used for theorem_3.
-/


-- Helper: admissible_bound is linear in A
lemma admissible_bound_mul (A K B C R x : ℝ) :
    admissible_bound (A * K) B C R x = K * admissible_bound A B C R x := by
  simp [admissible_bound]; ring

/-
Helper: the ratio log x / (x * admissible_bound A B C R x) equals R^B / A * g_bound 1 (1-B) (C/√R) x
-/
lemma ratio_eq_g {A B C R x : ℝ}
    (hR : R > 0) (hx : x > 0) (hlogx : log x > 0) :
    log x / (x * admissible_bound A B C R x) =
    R ^ B / A * g_bound 1 (1 - B) (C / sqrt R) x := by
  unfold admissible_bound g_bound; ring_nf;
  rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; norm_num [ Real.rpow_sub, Real.rpow_neg, Real.sqrt_mul, hR.le, hx.le, hlogx.le ] ; ring_nf;
  rw [ Real.rpow_sub hlogx, Real.rpow_one ] ; norm_num [ Real.exp_neg ] ; ring_nf;
  next =>
    norm_num
    left
    rw [show (log x * R⁻¹) ^ (1 / 2 : ℝ) = Real.sqrt (log x * R⁻¹) by rw [Real.sqrt_eq_rpow]]
    rw [Real.sqrt_mul, Real.sqrt_inv] <;> linarith





/-
Helper: for x ≥ x₁, the ratio log x / (x * admissible_bound) is at most the value at x₁
-/
lemma ratio_mono {A B C R x₁ x : ℝ} (hB : B ≥ 1 + C ^ 2 / (16 * R)) (hR : R > 0)
    (hx1 : x₁ > 1) (hx : x ≥ x₁) (hA : A > 0) :
    log x / (x * admissible_bound A B C R x) ≤
    log x₁ / (x₁ * admissible_bound A B C R x₁) := by
  have h_ratio_simplified : R ^ B / A * g_bound 1 (1 - B) (C / Real.sqrt R) x ≤ R ^ B / A * g_bound 1 (1 - B) (C / Real.sqrt R) x₁ := by
    have h_decreasing : ∀ x y : ℝ, 1 < x → x ≤ y → g_bound 1 (1 - B) (C / Real.sqrt R) x ≥ g_bound 1 (1 - B) (C / Real.sqrt R) y := by
      intros x y hx hy
      have h_deriv_neg : ∀ x : ℝ, 1 < x → deriv (g_bound 1 (1 - B) (C / Real.sqrt R)) x ≤ 0 := by
        intros x hx
        have h_deriv_neg : deriv (g_bound 1 (1 - B) (C / Real.sqrt R)) x = (-1 * Real.log x + (1 - B) + (C / (2 * Real.sqrt R)) * Real.sqrt (Real.log x)) * x ^ (-2 : ℝ) * (Real.log x) ^ ((1 - B) - 1) * Real.exp ((C / Real.sqrt R) * Real.sqrt (Real.log x)) := by
          field_simp;
          rw [ lemma_10_substep hx ] ; ring_nf ; norm_num [ Real.sqrt_ne_zero'.mpr hR, Real.sqrt_ne_zero'.mpr ( Real.log_pos hx ), Real.rpow_neg_one ] ; ring_nf;
          grind
        generalize_proofs at *; (
        have h_quad_neg : ∀ u : ℝ, u > 0 → -u^2 + (C / (2 * Real.sqrt R)) * u + (1 - B) ≤ 0 := by
          intros u hu
          have h_quad_neg : -u^2 + (C / (2 * Real.sqrt R)) * u + (1 - B) ≤ 0 := by
            have h_discriminant : (C / (2 * Real.sqrt R))^2 - 4 * (-1) * (1 - B) ≤ 0 := by
              field_simp at *; ring_nf at *; nlinarith [ inv_mul_cancel₀ ( ne_of_gt hR ), inv_pos.mpr hR, Real.sqrt_nonneg R, Real.sq_sqrt hR.le, mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr hR ) ), Real.sqrt_nonneg ( R⁻¹ ), Real.sq_sqrt ( inv_nonneg.mpr hR.le ) ] ;
            linarith [ sq_nonneg ( C / ( 2 * Real.sqrt R ) - 2 * u ) ]
          generalize_proofs at *; (exact h_quad_neg)
        generalize_proofs at *; (
        exact h_deriv_neg.symm ▸ mul_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( by have := h_quad_neg ( Real.sqrt ( Real.log x ) ) ( Real.sqrt_pos.mpr ( Real.log_pos hx ) ) ; rw [ Real.sq_sqrt ( Real.log_nonneg hx.le ) ] at this; linarith ) ( by positivity ) ) ( by exact Real.rpow_nonneg ( Real.log_nonneg hx.le ) _ ) ) ( by positivity ) ;))
      generalize_proofs at *; (
      by_contra h_contra;
      have := exists_deriv_eq_slope ( g_bound 1 ( 1 - B ) ( C / Real.sqrt R ) ) ( show x < y from hy.lt_of_ne ( by rintro rfl; linarith ) ) ; norm_num at this;
      exact absurd ( this ( by exact ContinuousOn.mono ( show ContinuousOn ( g_bound 1 ( 1 - B ) ( C / Real.sqrt R ) ) ( Set.Icc x y ) from by exact ContinuousOn.mul ( ContinuousOn.mul ( ContinuousOn.rpow continuousOn_id continuousOn_const <| by intro u hu; exact Or.inl <| by linarith [ hu.1 ] ) <| ContinuousOn.rpow ( Real.continuousOn_log.mono <| by exact fun u hu => ne_of_gt <| by linarith [ hu.1 ] ) continuousOn_const <| by intro u hu; exact Or.inl <| ne_of_gt <| Real.log_pos <| by linarith [ hu.1 ] ) <| ContinuousOn.rexp <| ContinuousOn.mul continuousOn_const <| ContinuousOn.sqrt <| Real.continuousOn_log.mono <| by exact fun u hu => ne_of_gt <| by linarith [ hu.1 ] ) <| Set.Icc_subset_Icc ( by linarith ) le_rfl ) <| by exact fun u hu => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.mul ( DifferentiableAt.mul ( DifferentiableAt.rpow ( differentiableAt_id ) ( differentiableAt_const _ ) <| by linarith [ hu.1 ] ) <| DifferentiableAt.rpow ( Real.differentiableAt_log <| by linarith [ hu.1 ] ) ( differentiableAt_const _ ) <| by exact ne_of_gt <| Real.log_pos <| by linarith [ hu.1 ] ) <| DifferentiableAt.exp <| DifferentiableAt.mul ( differentiableAt_const _ ) <| DifferentiableAt.sqrt ( Real.differentiableAt_log <| by linarith [ hu.1 ] ) <| by exact ne_of_gt <| Real.log_pos <| by linarith [ hu.1 ] ) ( by rintro ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ ; rw [ eq_div_iff ] at hcd <;> nlinarith [ h_deriv_neg c <| by linarith ] ) ;);
    exact mul_le_mul_of_nonneg_left ( h_decreasing _ _ hx1 hx ) ( by positivity );
  convert h_ratio_simplified using 1 <;> norm_num [ ratio_eq_g hR ( by linarith : 0 < x ) ( Real.log_pos ( by linarith ) ), ratio_eq_g hR ( by linarith : 0 < x₁ ) ( Real.log_pos ( by linarith ) ) ]

/-
Helper: for B ≥ 3/2 and x ≥ x₁ ≥ x₀, the m(x₀,x)*(log x)^(1-B) factor simplifies
-/
lemma m_simplify {B x₀ x x₁ : ℝ} (hB : B ≥ 3 / 2) (hx₀ : x₀ > 1) (hx₁ : x₁ > 1)
    (hx₁x₀ : x₁ ≥ x₀) (hx : x ≥ x₁) (hlogx : log x > 0) :
    max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) *
    (log x) ^ (1 - B) ≤ 1 / sqrt (log x₁) := by
  rw [ max_def ];
  split_ifs <;> norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_add hlogx ];
  · rw [ ← Real.rpow_neg ( Real.log_nonneg hx₁.le ) ] ; ring_nf ; norm_num [ hlogx ];
    rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ Real.log_pos hx₁, Real.log_le_log ( by linarith ) hx ];
  · exact False.elim <| ‹¬log x₀ ^ ( ( 2 * B - 3 ) / 2 ) ≤ log x ^ ( ( 2 * B - 3 ) / 2 ) › <| Real.rpow_le_rpow ( Real.log_nonneg <| by linarith ) ( Real.log_le_log ( by linarith ) <| by linarith ) <| by linarith;

/-
Helper: admissible_bound is positive under suitable conditions
-/
lemma admissible_bound_pos {A B C R x : ℝ} (hA : A > 0) (hR : R > 0) (hlogx : log x > 0) :
    admissible_bound A B C R x > 0 := by
  exact mul_pos ( mul_pos hA ( Real.rpow_pos_of_pos ( div_pos hlogx hR ) _ ) ) ( Real.exp_pos _ )

/-
Helper: Eθ is non-negative
-/
lemma Eθ_nonneg (x : ℝ) (hx : x > 0) : Eθ x ≥ 0 := by
  exact div_nonneg ( abs_nonneg _ ) hx.le

/-
Helper: δ is non-negative
-/
lemma delta_nonneg (x₀ : ℝ) : δ x₀ ≥ 0 := by
  exact abs_nonneg _

/-
Helper: from ratio_mono, derive the bound on log x / x in terms of admissible_bound
-/
lemma logx_over_x_bound {A B C R x₁ x : ℝ}
    (hB : B ≥ 1 + C ^ 2 / (16 * R)) (hR : R > 0) (hA : A > 0)
    (hx1_gt1 : x₁ > 1) (hx : x ≥ x₁) :
    log x / x ≤ (log x₁ / (x₁ * admissible_bound A B C R x₁)) * admissible_bound A B C R x := by
  convert! mul_le_mul_of_nonneg_right ( ratio_mono hB hR hx1_gt1 hx hA ) ( admissible_bound_pos hA hR ( Real.log_pos <| show 1 < x by linarith ) |> le_of_lt ) using 1 ; ring_nf;
  norm_num [ ne_of_gt ( admissible_bound_pos hA hR ( Real.log_pos <| show 1 < x by linarith ) ) ]

/-
PROBLEM
Bound the delta term from eq_30.

PROVIDED SOLUTION
Use logx_over_x_bound to get log x / x ≤ (log x₁ / (x₁ * admissible_bound A B C R x₁)) * admissible_bound A B C R x.
Multiply both sides by (x₀ / log x₀) * δ x₀ (which is non-negative since δ is non-negative by delta_nonneg and x₀/log x₀ > 0 from hlogx₀).
The LHS becomes (log x / x) * (x₀ / log x₀) * δ x₀.
The RHS becomes (log x₁ / (x₁ * admissible_bound A B C R x₁)) * (x₀ / log x₀) * δ x₀ * admissible_bound A B C R x
which equals (x₀ * log x₁) / (admissible_bound A B C R x₁ * x₁ * log x₀) * δ x₀ * admissible_bound A B C R x by algebraic rearrangement.
-/
lemma delta_term_bound {A B C R x₀ x₁ x : ℝ}
    (hB : B ≥ 1 + C ^ 2 / (16 * R)) (hR : R > 0) (hA : A > 0)
    (hx1_gt1 : x₁ > 1) (hx : x ≥ x₁) (hx0_pos : x₀ > 0) (hlogx₀ : log x₀ > 0) :
    (log x / x) * (x₀ / log x₀) * δ x₀ ≤
    (x₀ * log x₁) / (admissible_bound A B C R x₁ * x₁ * log x₀) * δ x₀ *
    admissible_bound A B C R x := by
  have h1 := logx_over_x_bound hB hR hA hx1_gt1 hx
  have h2 : x₀ / log x₀ ≥ 0 := div_nonneg hx0_pos.le hlogx₀.le
  have h3 := delta_nonneg x₀
  calc (log x / x) * (x₀ / log x₀) * δ x₀
      ≤ ((log x₁ / (x₁ * admissible_bound A B C R x₁)) * admissible_bound A B C R x) * (x₀ / log x₀) * δ x₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) h3
    _ = (x₀ * log x₁) / (admissible_bound A B C R x₁ * x₁ * log x₀) * δ x₀ * admissible_bound A B C R x := by ring

/-
Helper: Dawson function is monotone decreasing for large arguments (after ~0.924)
We use remark_after_corollary_11 which gives the existence of a maximum around 0.924
-/
lemma dawson_antitoneOn : ∃ x₀ : ℝ, x₀ < 1 ∧ StrictAntiOn dawson (Set.Ioi x₀) := by
  obtain ⟨ x₀, hx₀ ⟩ := remark_after_corollary_11;
  exact ⟨ x₀, by norm_num at hx₀; linarith, hx₀.2.2 ⟩

/-
Helper: Eθ t = |Eθ t| since Eθ is non-negative
-/
lemma Eθ_eq_abs {t : ℝ} (ht : t > 0) : Eθ t = |Eθ t| := by
  rw [ abs_of_nonneg ( Eθ_nonneg t ht ) ]

/-
Algebraic identity: (log x / x) * (2A/R^B) * x * m * exp(-C*√(log x/R)) * D
= 2 * m * (log x)^(1-B) * D * admissible_bound A B C R x
-/
lemma integral_algebra {A B C R x m D : ℝ} (hR : R > 0) (hx : x > 1) :
    (log x / x) * ((2 * A) / R ^ B * x * m * exp (-C * √(log x / R)) * D) =
    2 * m * (log x) ^ (1 - B) * D * admissible_bound A B C R x := by
  unfold admissible_bound; ring_nf;
  rw [ Real.rpow_sub ( by linarith [ Real.log_pos hx ] ), Real.rpow_one ] ; ring_nf;
  rw [ Real.mul_rpow ( by linarith [ Real.log_pos hx ] ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; ring_nf ; norm_num [ ne_of_gt ( zero_lt_one.trans hx ) ] ;
  rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( Real.log_pos hx ) _ ) ) ]
  have heq: Real.exp (-(C * (Real.log x * R⁻¹)^(1/2 : ℝ))) = Real.exp (-(C * Real.sqrt (Real.log x * R⁻¹))) := by congr; rw [Real.sqrt_eq_rpow]
  rw [heq]
  linarith






/-
Dawson monotonicity for arguments ≥ 1
-/
lemma dawson_mono_ge_one {a b : ℝ} (ha : a ≥ 1) (hab : a ≤ b) :
    dawson b ≤ dawson a := by
  obtain ⟨ x₀, hx₀ ⟩ := dawson_antitoneOn;
  exact hx₀.2.le_iff_ge ( show x₀ < b by linarith ) ( show x₀ < a by linarith ) |>.2 ( by linarith )

/-
Derive that √(log x₁) - C/(2√R) ≥ 1 from the hypothesis on x₁
-/
lemma sqrt_log_minus_ge_one {C R x₁ : ℝ}
    (hx1 : x₁ ≥ exp ((1 + C / (2 * sqrt R)) ^ 2)) :
    √(log x₁) - C / (2 * √R) ≥ 1 := by
  -- Taking the natural logarithm of both sides of the inequality $x₁ \geq \exp((1 + C / (2 * \sqrt{R}))^2)$, we get $\log x₁ \geq (1 + C / (2 * \sqrt{R}))^2$.
  have h_log : Real.log x₁ ≥ (1 + C / (2 * Real.sqrt R)) ^ 2 := by
    simpa using Real.log_le_log ( by positivity ) hx1;
  exact le_tsub_of_add_le_right ( Real.le_sqrt_of_sq_le ( by linarith ) )

/-
PROBLEM
Helper: the integral term from eq_30 is bounded by the Dawson component of μ_asymp

Bound the integral term from eq_30.

PROVIDED SOLUTION
Step 1: Since Eθ t ≥ 0, we have ∫ Eθ t / log t^2 ≤ ∫ |Eθ t| / log t^2.
Step 2: Apply lemma_12 to bound the integral.
Step 3: Multiply by log x / x and use integral_algebra to simplify:
  = 2 * m(x₀,x) * (log x)^(1-B) * dawson(√(log x) - C/(2√R)) * admissible_bound.
Step 4: Apply m_simplify to get m * (log x)^(1-B) ≤ 1/√(log x₁).
Step 5: Apply dawson_mono_ge_one (using sqrt_log_minus_ge_one for the ≥ 1 condition)
  to get dawson(√(log x)-C/(2√R)) ≤ dawson(√(log x₁)-C/(2√R)).
Step 6: Combine: ≤ 2/√(log x₁) * dawson(√(log x₁)-C/(2√R)) * admissible_bound.
-/
lemma integral_term_bound {A B C R x₀ x₁ x : ℝ}
  (hB : B ≥ 3 / 2)
  (hR : R > 0) (hA : A > 0)
  (hE_theta : Eθ.classicalBound A B C R x₀)
  (hx1_gt1 : x₁ > 1) (hx₁x₀ : x₁ ≥ x₀) (hx : x ≥ x₁)
  (hx0_ge2 : x₀ ≥ 2)
  (hsqrt_cond : 0 ≤ √(log x₀) - C / (2 * √R))
  (hx1_exp : x₁ ≥ exp ((1 + C / (2 * sqrt R)) ^ 2)) :
  (log x / x) * ∫ t in x₀..x, Eθ t / log t ^ 2 ≤
  2 * dawson (√(log x₁) - C / (2 * √R)) / √(log x₁) *
  admissible_bound A B C R x := by
  -- Apply the integral bound from lemma_12.
  have h_integral_bound : ∫ t in x₀..x, Eθ t / Real.log t ^ 2 ≤
      (2 * A) / R ^ B * x * max ((Real.log x₀) ^ ((2 * B - 3) / 2)) ((Real.log x) ^ ((2 * B - 3) / 2)) *
      Real.exp (-C * Real.sqrt (Real.log x / R)) * dawson (Real.sqrt (Real.log x) - C / (2 * Real.sqrt R)) := by
        convert lemma_12 _ _ _ _ ?_ ?_ using 1;
        any_goals linarith;
        · exact intervalIntegral.integral_congr fun t ht => by rw [ abs_of_nonneg ( Eθ_nonneg t ( by linarith [ Set.mem_Icc.mp ( by simpa [ show x₀ ≤ x by linarith ] using ht ) ] ) ) ] ;
        · assumption;
  -- Multiply by log x / x and use integral_algebra to simplify:
  have h_integral_mul : (log x / x) * ∫ t in x₀..x, Eθ t / Real.log t ^ 2 ≤
      2 * (max ((Real.log x₀) ^ ((2 * B - 3) / 2)) ((Real.log x) ^ ((2 * B - 3) / 2))) * (Real.log x) ^ (1 - B) *
      dawson (Real.sqrt (Real.log x) - C / (2 * Real.sqrt R)) * admissible_bound A B C R x := by
        convert! mul_le_mul_of_nonneg_left h_integral_bound ( show 0 ≤ Real.log x / x from div_nonneg ( Real.log_nonneg <| by linarith ) <| by linarith ) using 1 ; ring_nf;
        unfold admissible_bound; ring_nf;
        rw [ Real.mul_rpow ( by linarith [ Real.log_nonneg ( by linarith : ( 1:ℝ ) ≤ x ) ] ) ( by positivity ), Real.inv_rpow ( by positivity ) ] ; ring_nf;
        by_cases hxtemp : x = 0
        · simp [hxtemp]
          linarith
        · congr 2
          · simp only [mul_comm, mul_left_comm, mul_assoc, mul_eq_mul_left_iff]
            simp only [ne_eq, hxtemp, not_false_eq_true, mul_inv_cancel_left₀, mul_eq_mul_left_iff,
              inv_eq_zero]
            rw [ ← mul_assoc ]
            rw [ ← Real.rpow_add ( Real.log_pos <| by linarith ) ]
            norm_num
          congr
          rw [ Real.sqrt_eq_rpow ]
  -- Apply m_simplify to get m * (log x)^(1-B) ≤ 1/√(log x₁).
  have h_m_simplify : max ((Real.log x₀) ^ ((2 * B - 3) / 2)) ((Real.log x) ^ ((2 * B - 3) / 2)) * (Real.log x) ^ (1 - B) ≤ 1 / Real.sqrt (Real.log x₁) := by
    apply m_simplify hB (by linarith) (by linarith) hx₁x₀ hx (Real.log_pos (by linarith));
  -- Apply dawson_mono_ge_one to get dawson(√(log x)-C/(2√R)) ≤ dawson(√(log x₁)-C/(2√R)).
  have h_dawson_mono : dawson (Real.sqrt (Real.log x) - C / (2 * Real.sqrt R)) ≤ dawson (Real.sqrt (Real.log x₁) - C / (2 * Real.sqrt R)) := by
    apply dawson_mono_ge_one;
    · exact le_trans (sqrt_log_minus_ge_one hx1_exp) (sub_le_sub_right (Real.sqrt_le_sqrt <| Real.log_le_log (by linarith) (by linarith)) _);
    · exact sub_le_sub_right ( Real.sqrt_le_sqrt <| Real.log_le_log ( by linarith ) <| by linarith ) _;
  refine le_trans h_integral_mul ?_;
  convert mul_le_mul_of_nonneg_right ( mul_le_mul ( mul_le_mul_of_nonneg_left h_m_simplify zero_le_two ) h_dawson_mono ( ?_ ) ( ?_ ) ) ( show 0 ≤ admissible_bound A B C R x from ?_ ) using 1 <;> ring_nf;
  · apply_rules [ dawson_nonneg ];
    ring_nf at *; linarith [ Real.sqrt_le_sqrt ( show Real.log x₀ ≤ Real.log x by exact Real.log_le_log ( by linarith ) ( by linarith ) ) ] ;
  · positivity;
  · exact mul_nonneg ( mul_nonneg hA.le ( Real.rpow_nonneg ( div_nonneg ( Real.log_nonneg ( by linarith ) ) hR.le ) _ ) ) ( Real.exp_nonneg _ )

lemma theorem_3_easy_preconditions
    (B C R x₀ x₁ : ℝ)
    (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
    (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2))) :
    x₁ ≥ x₀ ∧ x₁ ≥ exp ((1 + C / (2 * sqrt R)) ^ 2) ∧
    B ≥ 3 / 2 ∧ B ≥ 1 + C ^ 2 / (16 * R) :=
  ⟨le_of_max_le_left hx1, le_of_max_le_right hx1,
   le_of_max_le_left hB, le_of_max_le_right hB⟩

@[blueprint
  "fks2-theorem-3"
  (title := "FKS2 Theorem 3")
  (statement := /--
  If $B \geq \max(3/2, 1 + C^2/16 R)$, $x_0 > 0$, and one has an admissible asymptotic bound
  with parameters $A,B,C,x_0$ for $E_\theta$, and
  $$ x_1 \geq \max( x_0, \exp( (1 + \frac{C}{2\sqrt{R}}))^2),$$
  then
  $$ E_\pi(x) \leq \epsilon_{\theta,asymp}(x) ( 1 + \mu_{asymp}(x_0,x_1) ) $$
  for all $x \geq x_1$.  In other words, we have an admissible bound with parameters
  $(1+\mu_{asymp}(x_0,x_1))A, B, C, x_1$ for $E_\pi$.
  -/)
  (proof := /-- The starting point is Sublemma \ref{fks2-eq-30}.
  The assumption ($\varepsilon_{\theta,\mathrm{asymp}}(x)$ provides an admissible bound on $\theta(x)$ for all $x \geq x_0$) to bound $\frac{\theta(x) - x}{\log(x)}$ and Lemma \ref{fks2-lemma-12} to bound $\int_{x_0}^{x} \frac{\theta(t) - t}{t (\log(t))^2} dt$.  We obtain
  $$ |\pi(x) - \Li(x)| \leq |\pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)}| + \frac{x \varepsilon_{\theta,\mathrm{asymp}}(x)}{\log(x)} + \frac{2 A_\theta}{R^B} x m(x_0,x) \exp(-C \sqrt{\frac{\log x}{R}}) D_+\left( \sqrt{\log x} - \frac{C}{2\sqrt{R}} \right).$$
  We recall that $x \geq x_1 \geq x_0$.  Note that, by Corollary \ref{fks2-corollary-11},
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} = \frac{1}{A_\theta} g(1, 1 - B, \frac{C}{\sqrt{R}}, x) $$
  is decreasing for all $x$.  Thus,
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} \leq \frac{\log(x_1)}{x_1 \varepsilon_{\theta,\mathrm{asymp}}(x_1)}. $$
  In addition, we have the simplification
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} \frac{2 A_\theta}{R^B} x m(x_0,x) e^{-C \sqrt{\frac{\log x}{R}}} = 2 m(x_0,x) (\log(x))^{1 - B} = 2 (\log(x))^{1 - B} \leq 2 (\log(x_1))^{1 - B}, $$
  by Definition \ref{classical-bound-theta} and by $m(x_0,x) = (\log(x))^{(2B - 3)/2}$, since $B \geq 3/2$.  Finally, since $\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}} > 1$, the Dawson function decreases for all $x \geq x_1$:
  $$ D_+\left( \sqrt{\log x} - \frac{C}{2\sqrt{R}} \right) \leq D_+\left( \sqrt{\log x_1} - \frac{C}{2\sqrt{R}} \right). $$
  We conclude by combining the above:
  $$ \frac{|\pi(x) - \Li(x)|}{\frac{x \varepsilon_{\theta,\mathrm{asymp}}(x)}{\log(x)}} \leq \frac{\log(x_1)}{x_1 \varepsilon_{\theta,\mathrm{asymp}}(x_1)} |\pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)}| + 1 + \frac{2 D_+\left( \sqrt{\log x_1} - \frac{C}{2\sqrt{R}} \right)}{\sqrt{\log(x_1)}}, $$
  from which we deduce the announced bound. -/)
  (latexEnv := "theorem")
  (discussion := 675)]
theorem theorem_3 (A B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hx0 : x₀ > 0)
  (hE_theta : Eθ.classicalBound A B C R x₀)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)))
  (hR : R > 0)
  (hA : A > 0)
  (hx0_ge2 : x₀ ≥ 2)
  (hsqrt_cond : 0 ≤ √(log x₀) - C / (2 * √R)) :
  Eπ.classicalBound (A * (1 + μ_asymp A B C R x₀ x₁)) B C R x₁ := by
  /-NOTE: The conditions hx0_ge2 and hsqrt_cond are not present in the source material [FKS2]. They are added to
  facilitate the application of lemma_12, which requires x₀ ≥ 2 and 0 ≤ √(log x₀) - C/(2√R).
  -/
  obtain ⟨hx1x0, hx1_exp, hB1, hB2⟩ := theorem_3_easy_preconditions B C R x₀ x₁ hB hx1
  have hx1_ge1 : x₁ ≥ 1 := le_trans (Real.one_le_exp (sq_nonneg _)) hx1_exp
  have hx1_gt1 : x₁ > 1 := by linarith
  have hlogx0 : log x₀ > 0 := Real.log_pos (by linarith)
  intro x hx
  simp only [admissible_bound_mul]
  have h30 := eq_30 (show x ≥ x₀ by linarith) hx0_ge2
  have hEtheta_x := hE_theta x (show x ≥ x₀ by linarith)
  have hdelta := delta_term_bound hB2 hR hA hx1_gt1 hx hx0 hlogx0
  have hintegral := integral_term_bound hB1 hR hA hE_theta hx1_gt1 hx1x0 hx hx0_ge2 hsqrt_cond hx1_exp
  calc Eπ x ≤ Eθ x + (log x / x) * (x₀ / log x₀) * δ x₀ + (log x / x) * ∫ t in x₀..x, Eθ t / log t ^ 2 := h30
    _ ≤ admissible_bound A B C R x +
          ((x₀ * log x₁) / (admissible_bound A B C R x₁ * x₁ * log x₀) * δ x₀ *
           admissible_bound A B C R x) +
          (2 * dawson (√(log x₁) - C / (2 * √R)) / √(log x₁) *
           admissible_bound A B C R x) := by linarith
    _ = (1 + μ_asymp A B C R x₀ x₁) * admissible_bound A B C R x := by
          unfold μ_asymp; ring


blueprint_comment /--
\subsection{From numerical estimates on psi to numerical estimates on theta}

Here we record a way to convert a numerical bound on $E_\psi$ to a numerical bound on $E_\theta$.
-/

noncomputable def εθ_from_εψ (εψ : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  εψ x₀ + 1.00000002 * (x₀ ^ (-(1:ℝ)/2) + x₀ ^ (-(2:ℝ)/3) + x₀ ^ (-(4:ℝ)/5)) +
    0.94 * (x₀ ^ (-(3:ℝ)/4) + x₀ ^ (-(5:ℝ)/6) + x₀ ^ (-(9:ℝ)/10))

/-- Bound for `ψ(y)` for small `y`. -/
theorem psi_le_bound_small (y : ℝ) (hy1 : 1 < y) (hy2 : y < 100) :
    ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1/2 : ℝ) := by
  have h_ineq : (RS_prime.c₀ - 1.00000002) * y ≤ 0.94 * y ^ (1 / 2 : ℝ) := by
    rw [← sqrt_eq_rpow]
    nlinarith [sq_nonneg (sqrt y - 3), mul_self_sqrt (show 0 ≤ y by positivity),
      sqrt_nonneg y, show RS_prime.c₀ = 1.03883 by rfl]
  grind [RS_prime.theorem_12 (by positivity)]

/-- Bound for `ψ(y)` for medium `y`. -/
theorem psi_le_bound_medium (y : ℝ) (hy1 : 100 ≤ y) (hy2 : y ≤ 1e19) :
    ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1/2 : ℝ) := by
  have h_psi_le : |ψ y - y| ≤ 0.94 * sqrt y := by
    have := BKLNW_app.bklnw_eq_A_26 y hy1 hy2
    rw [le_div_iff₀ (sqrt_pos.mpr (by positivity)), show Eψ y = |ψ y - y| / y by rfl,
        div_mul_eq_mul_div, div_le_iff₀] at this <;>
          nlinarith [sqrt_nonneg y, sq_sqrt (by positivity : 0 ≤ y)]
  rw [← sqrt_eq_rpow]
  grind

/-- Bound for `ψ(y)` for large `y`. -/
theorem psi_le_bound_large (y : ℝ) (hy : 1e19 < y) :
    ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1/2 : ℝ) := by
  have h_b : |ψ y - y| ≤ BKLNW_app.table_8_ε (19 * log 10) * y := by
    apply BKLNW_app.theorem_2 (19 * log 10) (by positivity) y (by
      rw [mul_comm, exp_mul, exp_log (by positivity)]; linarith)
  have h_eps : BKLNW_app.table_8_ε (19 * log 10) ≤ 1.93378e-8 * BKLNW_app.table_8_margin := by
    have h_log_approx : 43 < 19 * log 10 ∧ 19 * log 10 < 44 :=
      ⟨by nlinarith [LogTables.log_10_gt], by nlinarith [LogTables.log_10_lt]⟩
    grw [BKLNW_app.table_8_ε.le_simp (19 * log 10) (by grind)]
    norm_num [BKLNW_app.table_8_ε', h_log_approx]; norm_num at *
    field_simp
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
        if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
        if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
        if_pos (by linarith)]
    norm_num [log_pos] at *
  norm_num [← sqrt_eq_rpow] at *
  nlinarith [abs_le.mp h_b, sqrt_nonneg y, sq_sqrt (show 0 ≤ y by linarith), h_eps]

/-- Bound for `ψ(y)` for all `y > 1`. -/
theorem psi_le_bound (y : ℝ) (hy : 1 < y) : ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1/2 : ℝ) := by
  by_cases hy_large : y ≤ 1e19
  · by_cases hy_small : y < 100
    · exact psi_le_bound_small y hy hy_small
    · exact psi_le_bound_medium y (by grind) (by grind)
  · exact psi_le_bound_large y (by grind)

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
  We use \cite[Theorem 2]{Buthe}, that for $0 < x < 11$, $\psi(x) < x$, and that $\varepsilon_{\psi,num}(10^{19}) < 2 \cdot 10^{-8}$. In particular when $2 < x < 10^{38}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq x^{1/2} + x^{1/3} + x^{1/5} + 0.94(x^{1/4} + x^{1/6} + x^{1/10}),$$
  when $10^{38} \leq x < 10^{54}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002x^{1/2} + x^{1/3} + x^{1/5} + 0.94(x^{1/6} + x^{1/10}),$$
  when $10^{54} \leq x < 10^{95}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002(x^{1/2} + x^{1/3}) + x^{1/5} + 0.94x^{1/10},$$
  and finally when $x \geq 10^{95}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002(x^{1/2} + x^{1/3} + x^{1/5}).$$
  The result follows by combining the worst coefficients from all cases and dividing by $x$. -/)
  (latexEnv := "proposition")
  (discussion := 711)]
theorem proposition_17 {x x₀ : ℝ} (hx : x > x₀) (hx₀ : x₀ > 2) (εψ : ℝ → ℝ) (hEψ : Eψ x ≤ εψ x₀) :
    -εθ_from_εψ εψ x₀ ≤ (θ x - x) / x ∧ (θ x - x) / x ≤ εψ x₀ ∧ εψ x₀ ≤ εθ_from_εψ εψ x₀ := by
  refine ⟨?_, ?_, ?_⟩
  · have hx_pos : 0 < x := by linarith
    have hθ_bound :
        θ x ≥ x - εψ x₀ * x -
          1.00000002 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ)) -
          0.94 * (x ^ (1 / 4 : ℝ) + x ^ (1 / 6 : ℝ) + x ^ (1 / 10 : ℝ)) := by
      have hθ_from_ψ :
          θ x ≥ x - εψ x₀ * x -
            (ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ψ (x ^ (1 / 5 : ℝ))) := by
        have hθ_basic : θ x ≥ x - εψ x₀ * x - (ψ x - θ x) := by
          rw [show Eψ x = |ψ x - x| / x from rfl] at hEψ
          rw [div_le_iff₀] at hEψ <;>
            cases abs_cases (ψ x - x) <;> nlinarith [show 0 < x by linarith]
        exact hθ_basic.trans' <| sub_le_sub_left
          (le_trans (by norm_num)
            (show ψ x - θ x ≤ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ψ (x ^ (1 / 5 : ℝ)) by
              simpa [one_div] using Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x)) _
      have hψ_bounds :
          ψ (x ^ (1 / 2 : ℝ)) ≤ 1.00000002 * x ^ (1 / 2 : ℝ) + 0.94 * x ^ (1 / 4 : ℝ) ∧
          ψ (x ^ (1 / 3 : ℝ)) ≤ 1.00000002 * x ^ (1 / 3 : ℝ) + 0.94 * x ^ (1 / 6 : ℝ) ∧
          ψ (x ^ (1 / 5 : ℝ)) ≤ 1.00000002 * x ^ (1 / 5 : ℝ) + 0.94 * x ^ (1 / 10 : ℝ) := by
        have hψ_le : ∀ y : ℝ, 1 < y → ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1 / 2 : ℝ) :=
          fun y a ↦ psi_le_bound y a
        exact ⟨by
            convert hψ_le (x ^ (1 / 2 : ℝ)) (one_lt_rpow (by linarith) (by norm_num)) using 1
            rw [← rpow_mul (by linarith)]; norm_num, by
            convert hψ_le (x ^ (1 / 3 : ℝ)) (one_lt_rpow (by linarith) (by norm_num)) using 1
            rw [← rpow_mul (by linarith)]; norm_num, by
            convert hψ_le (x ^ (1 / 5 : ℝ)) (one_lt_rpow (by linarith) (by norm_num)) using 1
            rw [← rpow_mul (by linarith)]; norm_num⟩
      linarith [rpow_pos_of_pos hx_pos (1 / 2 : ℝ),
        rpow_pos_of_pos hx_pos (1 / 3 : ℝ), rpow_pos_of_pos hx_pos (1 / 5 : ℝ),
        rpow_pos_of_pos hx_pos (1 / 4 : ℝ), rpow_pos_of_pos hx_pos (1 / 6 : ℝ),
        rpow_pos_of_pos hx_pos (1 / 10 : ℝ)]
    have hfactor :
        1.00000002 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ)) +
          0.94 * (x ^ (1 / 4 : ℝ) + x ^ (1 / 6 : ℝ) + x ^ (1 / 10 : ℝ)) ≤
        x * (1.00000002 * (x₀ ^ (-(1 / 2 : ℝ)) + x₀ ^ (-(2 / 3 : ℝ)) + x₀ ^ (-(4 / 5 : ℝ))) +
          0.94 * (x₀ ^ (-(3 / 4 : ℝ)) + x₀ ^ (-(5 / 6 : ℝ)) + x₀ ^ (-(9 / 10 : ℝ)))) := by
      have hpowers :
          x ^ (1 / 2 : ℝ) ≤ x * x₀ ^ (-(1 / 2 : ℝ)) ∧
          x ^ (1 / 3 : ℝ) ≤ x * x₀ ^ (-(2 / 3 : ℝ)) ∧
          x ^ (1 / 5 : ℝ) ≤ x * x₀ ^ (-(4 / 5 : ℝ)) ∧
          x ^ (1 / 4 : ℝ) ≤ x * x₀ ^ (-(3 / 4 : ℝ)) ∧
          x ^ (1 / 6 : ℝ) ≤ x * x₀ ^ (-(5 / 6 : ℝ)) ∧
          x ^ (1 / 10 : ℝ) ≤ x * x₀ ^ (-(9 / 10 : ℝ)) := by
        have hpower_bound : ∀ k : ℝ, 0 < k → k < 1 → x ^ k ≤ x * x₀ ^ (k - 1) := by
          intro k hk hk'
          rw [← log_le_log_iff (rpow_pos_of_pos (by linarith) _) (mul_pos (by linarith)
            (rpow_pos_of_pos (by linarith) _)), log_rpow (by linarith),
              log_mul (by linarith) (ne_of_gt (rpow_pos_of_pos (by linarith) _)), log_rpow (by linarith)]
          ring_nf
          nlinarith [log_lt_log (by linarith) hx]
        exact ⟨by convert hpower_bound (1 / 2) (by norm_num) (by norm_num) using 1; ring_nf,
          by convert hpower_bound (1 / 3) (by norm_num) (by norm_num) using 1; ring_nf,
          by convert hpower_bound (1 / 5) (by norm_num) (by norm_num) using 1; ring_nf,
          by convert hpower_bound (1 / 4) (by norm_num) (by norm_num) using 1; ring_nf,
          by convert hpower_bound (1 / 6) (by norm_num) (by norm_num) using 1; ring_nf,
          by convert hpower_bound (1 / 10) (by norm_num) (by norm_num) using 1; ring_nf⟩
      linarith [rpow_pos_of_pos hx_pos (1 / 2 : ℝ),
        rpow_pos_of_pos hx_pos (1 / 3 : ℝ), rpow_pos_of_pos hx_pos (1 / 5 : ℝ),
        rpow_pos_of_pos hx_pos (1 / 4 : ℝ), rpow_pos_of_pos hx_pos (1 / 6 : ℝ),
        rpow_pos_of_pos hx_pos (1 / 10 : ℝ)]
    rw [le_div_iff₀ hx_pos, εθ_from_εψ]
    grind
  · have h_le_psi : (θ x - x) / x ≤ (ψ x - x) / x := by
      gcongr
      · linarith
      · exact theta_le_psi x
    exact h_le_psi.trans <| hEψ.trans' (div_le_div_of_nonneg_right (le_abs_self _) (by linarith))
  · exact le_add_of_le_of_nonneg (le_add_of_nonneg_right <| by positivity) <| by positivity

blueprint_comment /--
\subsection{From numerical estimates on theta to numerical estimates on pi}

Here we record a way to convert a numerical bound on $E_\theta$ to a numerical bound on $E_\pi$.  We first need some preliminary lemmas.
-/

theorem Li_identity' {a b : ℝ} (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, 1 / log t ^ 2 = Li b - Li a - b / log b + a / log a :=
  have {x} (hx : 2 ≤ x) : IntervalIntegrable (fun t ↦ 1 / log t ^ 2) volume 2 x := by
    simp only [one_div]
    refine ((((continuousOn_id' _).log ?_).pow 2).inv₀ (fun t ht => ?_)).intervalIntegrable
    · rw [Set.uIcc_of_le hx]; grind
    · rw [Set.uIcc_of_le hx] at ht
      positivity [log_pos (by grind : 1 < t)]
  calc
  _ = (∫ t in 2..b, 1 / log t ^ 2) - ∫ t in 2..a, 1 / log t ^ 2 :=
    (intervalIntegral.integral_interval_sub_left (this (ha.trans hb)) (this ha)).symm
  _ = b / log b - 2 / log 2 + (∫ t in 2..b, 1 / (log t ^ 2)) - b / log b -
    (a / log a - 2 / log 2 + (∫ t in 2..a, 1 / (log t ^ 2)) - a / log a) := by ring
  _ = _ := by rw [Li_identity ha, Li_identity (ha.trans hb)]; ring

@[blueprint
  "fks2-lemma-19"
  (title := "FKS2 Lemma 19")
  (statement := /--
  Let $x_1 > x_0 \geq 2$, $N \in \N$, and let $(b_i)_{i=1}^N$ be a finite partition of
  $[\log x_0, \log x_1]$.  Then
  $$ |\int_{x_0}^{x_1} \frac{\theta(t)-t}{t \log^2 t}\ dt|
    \leq \sum_{i=1}^{N-1} \eps_{\theta,num}(e^{b_i})
    ( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}).$$ -/)
  (proof := /-- We split the integral at each $e^{b_i}$ and apply the bound
  $$ |\frac{\theta(t)-t}{t}| \leq \eps_{\theta,num}(e^{b_i}), \text{ for every } e^{b_i} \leq t < e^{b_{i+1}}. $$
  Thus,
  $$ |\int_{x_0}^{x_1} \frac{\theta(t)-t}{t \log^2 t}\ dt|
    \leq \sum_{i=1}^{N-1} \int_{e^{b_i}}^{e^{b_{i+1}}}
      |\frac{\theta(t)-t}{t \log^2 t}|\ dt
    \leq \sum_{i=1}^{N-1} \eps_{\theta,num}(e^{b_i})
      \int_{e^{b_i}}^{e^{b_{i+1}}} \frac{dt}{(\log t)^2}. $$
  We conclude by using the identity: for all $2 \leq a < b$,
  $$ \int_a^b \frac{dt}{(\log t)^2}
    = \Li(b) - \frac{b}{\log b} - (\Li(a) - \frac{a}{\log a}). $$ -/)
  (latexEnv := "lemma")
  (discussion := 712)]
theorem lemma_19 {x₀ x₁ : ℝ} (hx₁ : x₀ < x₁) (hx₀ : x₀ ≥ 2)
  {N : ℕ} (b : ℕ → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀) (hN : 0 ≤ N)
  (h_b_end : b N = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : ∀ i ∈ Finset.Ico 0 N, Eθ.numericalBound (exp (b i)) εθ_num) :
  |∫ t in x₀..x₁, (θ t - t) / (t * log t ^ 2)| ≤
    ∑ i ∈ Finset.Ico 0 N,
      εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) :=
  have h1 {i} : 2 ≤ exp (b i) := by
    trans exp (b 0)
    · rw [h_b_start, exp_log (by grind)]; exact hx₀
    · exact exp_monotone (hmono (by linarith))
  have h2 {i} : exp (b i) ≤ exp (b (i + 1)) := exp_monotone (hmono (by linarith))
  have h3 {i} : IntervalIntegrable (fun t ↦ |θ t - t| / t / log t ^ 2) volume
    (exp (b i)) (exp (b (i + 1))) := by
    refine (intervalIntegrable_congr fun t ht => ?_).2 (l3 h1 h2).abs
    simp [abs_div, div_div, abs_of_nonneg (by grind : 0 ≤ t)]
  calc
  _ ≤ ∫ t in x₀..x₁, |(θ t - t) / (t * log t ^ 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hx₁.le
  _ = ∫ t in x₀..x₁, |θ t - t| / t / log t ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx₁.le] at ht
    simp [abs_div, div_div, abs_of_nonneg (by grind : 0 ≤ t)]
  _ = ∑ i ∈ Finset.Ico 0 N, ∫ (t : ℝ) in (exp (b i))..exp (b (i + 1)),
    |θ t - t| / t / log t ^ 2 := by
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico hN]
    · rw [← exp_log (by grind : 0 < x₀), ← exp_log (by grind : 0 < x₁), h_b_end, h_b_start]
    · exact fun i hi => h3
  _ ≤ ∑ i ∈ Finset.Ico 0 N, ∫ (t : ℝ) in (exp (b i))..exp (b (i + 1)),
    εθ_num (exp (b i)) / log t ^ 2 := by
    gcongr with i hi
    refine intervalIntegral.integral_mono_on h2 h3 ?_ fun t ht => ?_
    · simp only [div_eq_mul_inv]
      refine IntervalIntegrable.const_mul ((ContinuousOn.pow ?_ 2).inv₀ ?_).intervalIntegrable _
      · refine (continuousOn_id' _).log fun t ht => ?_
        rw [Set.uIcc_of_le h2] at ht
        grind
      · intro t ht
        rw [Set.uIcc_of_le h2] at ht
        positivity [log_pos (by grind : 1 < t)]
    · gcongr
      exact h_εθ_num i hi t ht.1
  _ = ∑ i ∈ Finset.Ico 0 N, εθ_num (exp (b i)) *
    ∫ (t : ℝ) in (exp (b i))..exp (b (i + 1)), 1 / log t ^ 2 := by
    congr with i
    simp [← intervalIntegral.integral_const_mul, div_eq_mul_inv]
  _ = _ := by
    congr with i
    rw [Li_identity' h1 h2, log_exp, log_exp]
    ring

lemma hasDerivAt_Li {x : ℝ} (hx : x ∈ Set.Ioi 6.58) : HasDerivAt Li (1 / log x) x := by
  have hf (x) (hx : x ∈ Set.Ioi 6.58) : ContinuousAt (fun x ↦ 1 / log x) x := by
    have := log_pos (by linarith [Set.mem_Ioi.mp hx]) |>.ne'
    fun_prop (disch := simp_all)
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ (hf x hx)
  · have := Set.uIcc_of_le (show 2 ≤ x by linarith [Set.mem_Ioi.mp hx])
    apply intervalIntegral.intervalIntegrable_one_div (by grind [log_eq_zero])
    fun_prop (disch := grind)
  · grind [ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hf]

@[blueprint
  "fks2-lemma-20a"
  (title := "FKS2 Lemma 20a")
  (statement := /--
  The function $\Li(x) - \frac{x}{\log x}$ is strictly increasing for $x > 6.58$.
  -/)
  (proof := /-- Differentiate
  \[
  \frac{d}{dx} \left( \Li(x) - \frac{x}{\log(x)} \right) = \frac{1}{\log(x)} + \frac{1 - \log(x)}{(\log(x))^2} = \frac{1}{(\log(x))^2}
  \]
  to see that the difference is strictly increasing. Evaluating at $x = 6.58$ and applying the mean value theorem gives the announced result.
  -/)
  (latexEnv := "lemma")
  (discussion := 713)]
theorem lemma_20_a : StrictMonoOn (fun x ↦ Li x - x / log x) (Set.Ioi 6.58) := by
  have hpos (x : ℝ) (hx : x ∈ Set.Ioi 6.58) := log_pos (by linarith [Set.mem_Ioi.mp hx]) |>.ne'
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · apply HasDerivAt.continuousOn (by apply hasDerivAt_Li) |>.sub
    fun_prop (disch := simp_all)
  · intro x hx
    rw [interior_Ioi, Set.mem_Ioi] at hx
    rw [deriv_fun_sub (hasDerivAt_Li hx).differentiableAt (by fun_prop (disch := simp_all)),
      deriv_fun_div differentiableAt_fun_id (differentiableAt_log (by linarith)) (hpos x hx)]
    simp [(hasDerivAt_Li hx).deriv, field, pow_two_pos_of_ne_zero, (hpos x hx), - sub_pos]

private lemma Li_ibp {x : ℝ} (hx : x > 2) :
    Li x - x / log x = -2 / log 2 + ∫ t in (2:ℝ)..x, 1 / (log t) ^ 2 := by
  have h_parts : ∀ a b : ℝ, 2 ≤ a → a < b →
      ∫ t in a..b, (1 : ℝ) / Real.log t =
        (b / Real.log b) - (a / Real.log a) + ∫ t in a..b, (1 : ℝ) / Real.log t ^ 2 := by
    intro a b _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
    rotate_right
    next => use fun x => x / Real.log x + ∫ t in a..x, 1 / Real.log t ^ 2
    · norm_num; ring
    · intro x hx
      exact Ramanujan.hasDerivAt_li_antideriv (by linarith)
        (by cases Set.mem_uIcc.mp hx <;> linarith)
    · apply_rules [ContinuousOn.intervalIntegrable]
      exact continuousOn_of_forall_continuousAt fun t ht =>
        ContinuousAt.div continuousAt_const
          (Real.continuousAt_log (by cases Set.mem_uIcc.mp ht <;> linarith))
          (ne_of_gt (Real.log_pos (by cases Set.mem_uIcc.mp ht <;> linarith)))
  convert! congr_arg (fun y => y - x / Real.log x) (h_parts 2 x (by norm_num) hx) using 1
  ring!


/-The following lemmas are used for the proof of lemma_20_b. The first lemma was originally used for
the proof of theorem_6_3, but was moved up here to be used for lemma_20_b as well.
-/


lemma hasDerivAt_Li_sub_div_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => Li t - t / log t) (1 / (log t) ^ 2) t := by
  have h_deriv_Li : HasDerivAt Li (1 / Real.log t) t := by
    apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) );
    · exact Measurable.stronglyMeasurable ( by exact Measurable.div measurable_const ( Real.measurable_log ) ) |> fun h => h.stronglyMeasurableAtFilter;
    · exact ContinuousAt.div continuousAt_const ( Real.continuousAt_log ( by positivity ) ) ( ne_of_gt ( Real.log_pos ht ) )
  generalize_proofs at *; (
  convert! HasDerivAt.sub h_deriv_Li ( HasDerivAt.div ( hasDerivAt_id t ) ( Real.hasDerivAt_log ( by positivity ) ) ( ne_of_gt ( Real.log_pos ht ) ) ) using 1 ; ring_nf! ; norm_num [ ne_of_gt, Real.log_pos ht ] ; ring_nf!;
  grind)

private lemma summable_li_series_658 :
    Summable fun n : ℕ =>
      (Real.log 6.58) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
  refine .of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_nat_add_iff 1 |>.2 <| Real.summable_pow_div_factorial <| Real.log 6.58)
  · exact div_nonneg (pow_nonneg (Real.log_nonneg (by norm_num)) _)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mod_cast Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

private lemma li_series_658_lower : (3.32710 : ℝ) ≤
    ∑' n : ℕ, (Real.log 6.58) ^ (n + 1) /
      ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
  have h_sum_le_tsum :
      (∑ n ∈ Finset.range 10, (Real.log 6.58) ^ (n + 1) /
        ((↑(n + 1) : ℝ) * ↑(n + 1).factorial)) ≤
        ∑' n : ℕ, (Real.log 6.58) ^ (n + 1) /
          ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) :=
    Summable.sum_le_tsum _ (fun _ _ => div_nonneg (by positivity) (by positivity))
      summable_li_series_658
  have h_partial : (3.32710 : ℝ) ≤
      ∑ n ∈ Finset.range 10, (Real.log 6.58) ^ (n + 1) /
        ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
    have hlog : (1.884034 : ℝ) ≤ Real.log 6.58 := by linarith [LogTables.log_6_58_gt]
    have h_const : (3.32710 : ℝ) ≤
        ∑ n ∈ Finset.range 10, (1.884034 : ℝ) ^ (n + 1) /
          ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    have h_const_le_partial :
        (∑ n ∈ Finset.range 10, (1.884034 : ℝ) ^ (n + 1) /
          ((↑(n + 1) : ℝ) * ↑(n + 1).factorial)) ≤
        ∑ n ∈ Finset.range 10, (Real.log 6.58) ^ (n + 1) /
          ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
      gcongr with n hn
    exact le_trans h_const h_const_le_partial
  exact le_trans h_partial h_sum_le_tsum

theorem Li_diff_pos_at_6_58 : Li 6.58 - 6.58 / log 6.58 > 0 := by
  have hli2 : li 2 ≤ (1.0452 : ℝ) := (li.two_approx).2
  have hll : (0.633415 : ℝ) ≤ Real.log (Real.log 6.58) := by linarith [LogTables.log_log_6_58_gt]
  have hdiv : 6.58 / Real.log 6.58 ≤ (3.492506 : ℝ) := by
    have hlog : (1.884034 : ℝ) ≤ Real.log 6.58 := by linarith [LogTables.log_6_58_gt]
    have hlogpos : 0 < Real.log 6.58 := by linarith
    rw [div_le_iff₀ hlogpos]
    nlinarith
  have hli : (4.537729 : ℝ) < li 6.58 := by
    rw [li_eq_eulerMascheroni_add_log_log_add_tsum (show (1 : ℝ) < 6.58 by norm_num)]
    linarith [hγ_lo, hll, li_series_658_lower]
  have hLi : Li 6.58 = li 6.58 - li 2 := by
    linarith [li.sub_Li 6.58 (show (2 : ℝ) ≤ 6.58 by norm_num)]
  rw [hLi]
  linarith

/- [FIX]: This fixes a typo in the original paper https://arxiv.org/pdf/2206.12557. -/
@[blueprint
  "fks2-lemma-20b"
  (title := "FKS2 Lemma 20b")
  (statement := /--
  Assume $x > 6.58$. Then
  $\Li(x) - \frac{x}{\log x} > \frac{x-6.58}{\log^2 x} > 0$.
  -/)
  (proof := /-- This follows from Lemma \ref{fks2-lemma-20a} and the mean value theorem. -/)
  (latexEnv := "lemma")
  (discussion := 714)]
theorem lemma_20_b {x : ℝ} (hx : x > 6.58) :
    Li x - x / log x > (x - 6.58) / (log x) ^ 2 ∧ (x - 6.58) / (log x) ^ 2 > 0 :=
by
  let f : ℝ → ℝ := fun t ↦ Li t - t / log t
  obtain ⟨c, hc, h_slope⟩ : ∃ c ∈ Set.Ioo (6.58 : ℝ) x,
      deriv f c = (f x - f 6.58) / (x - 6.58) := by
    refine exists_deriv_eq_slope f hx ?_ ?_
    · intro y hy
      exact (hasDerivAt_Li_sub_div_log
        (by rcases Set.mem_Icc.mp hy with ⟨hy₁, hy₂⟩; linarith)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_Li_sub_div_log
        (by rcases Set.mem_Ioo.mp hy with ⟨hy₁, hy₂⟩; linarith)).differentiableAt.differentiableWithinAt
  have hc_gt_one : 1 < c := by linarith [hc.1]
  have h_deriv_c : deriv f c = 1 / (log c) ^ 2 :=
    (hasDerivAt_Li_sub_div_log hc_gt_one).deriv
  have hx_sub_pos : 0 < x - 6.58 := by linarith
  have hf_diff : f x - f 6.58 = (x - 6.58) / (log c) ^ 2 := by
    have hq : (f x - f 6.58) / (x - 6.58) = 1 / (log c) ^ 2 := by
      linarith
    rw [div_eq_iff hx_sub_pos.ne'] at hq
    rw [hq]
    ring
  have hlogc_pos : 0 < log c := Real.log_pos hc_gt_one
  have hlogx_pos : 0 < log x := Real.log_pos (by linarith)
  have hlog_lt : log c < log x := Real.log_lt_log (by positivity) hc.2
  have hsq_lt : (log c) ^ 2 < (log x) ^ 2 := by
    nlinarith
  have hinv_lt : 1 / (log x) ^ 2 < 1 / (log c) ^ 2 := by
    exact one_div_lt_one_div_of_lt (sq_pos_of_pos hlogc_pos) hsq_lt
  have hmain : (x - 6.58) / (log x) ^ 2 < f x := by
    rw [← sub_pos]
    have hbase : 0 < f 6.58 := by
      simpa [f] using Li_diff_pos_at_6_58
    have hmul : (x - 6.58) / (log x) ^ 2 <
        (x - 6.58) / (log c) ^ 2 := by
      gcongr
    have hfx : f x = f 6.58 + (x - 6.58) / (log c) ^ 2 := by
      linarith
    rw [hfx]
    linarith
  have hpos : 0 < (x - 6.58) / (log x) ^ 2 := by
    positivity
  exact ⟨by simpa [f] using hmain, by simpa using hpos⟩

-- Integrability of Eθ t / log t ^ 2
private lemma Eθ_integrable {x y : ℝ} (hx : 2 ≤ x) (hy : x ≤ y) :
    IntervalIntegrable (fun t ↦ Eθ t / log t ^ 2) volume x y := by
  unfold Eθ
  refine (intervalIntegrable_congr fun t ht => ?_).2 (l3 hx hy).abs
  rw [Set.uIoc_of_le hy, Set.mem_Ioc] at ht
  have ht_gt_1 : 1 < t := by linarith [hx]
  have hlog : 0 < log t := Real.log_pos ht_gt_1
  have hden : 0 < t * log t ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden]
  have ht_pos : 0 < t := by positivity
  field_simp [ht_pos.ne', hlog.ne']

-- Bound on Eθ t / log t ^ 2 on the interval [x₁, x]
private lemma Eθ_bound_integral_last {x₁ x : ℝ} (hx₁ : 2 ≤ x₁) (hx : x₁ ≤ x)
    (εθ_num : ℝ → ℝ) (h_εθ_num_last : Eθ.numericalBound x₁ εθ_num) :
    (∫ t in x₁..x, Eθ t / log t ^ 2) ≤ εθ_num x₁ * ∫ t in x₁..x, 1 / (log t) ^ 2 := by
  have h_int : IntervalIntegrable (fun t ↦ Eθ t / log t ^ 2) volume x₁ x := Eθ_integrable hx₁ hx
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hx h_int ?_ ?_
  · apply_rules [ContinuousOn.intervalIntegrable]
    exact continuousOn_of_forall_continuousAt fun u hu =>
      ContinuousAt.mul continuousAt_const <|
      ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log (by rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)) _)
        (ne_of_gt <| sq_pos_of_pos <| Real.log_pos (by rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith))
  · intro t ht; rw [mul_one_div]; gcongr
    exact h_εθ_num_last t ht.1

-- Bound on the partition sum from x₀ to x₁
private lemma bound_x0_x1 {x₀ x₁ : ℝ} (hx₀ : x₀ ≥ 2) (hx₀_le_x₁ : x₀ ≤ x₁)
    {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
    (h_b_start : b 0 = log x₀)
    (h_b_end : b (Fin.last N) = log x₁)
    (εθ_num : ℝ → ℝ)
    (h_εθ_num : ∀ i : Fin (N+1), Eθ.numericalBound (exp (b i)) εθ_num) :
    (∫ t in x₀..x₁, Eθ t / log t ^ 2) ≤
      ∑ i ∈ Finset.Iio (Fin.last N),
        εθ_num (exp (b i)) *
        (Li (exp (b (i + 1))) - Li (exp (b i)) +
        exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) := by
  have h_int_x₀_x₁ := Eθ_integrable hx₀ hx₀_le_x₁
  have h_exp_ge_2 (i : Fin (N + 1)) : 2 ≤ exp (b i) := by
    have : b 0 ≤ b i := hmono (Nat.zero_le i)
    rw [← exp_log (by positivity : 0 < x₀)] at hx₀
    exact hx₀.trans (exp_le_exp.mpr (h_b_start ▸ this))
  have h_x₀ : x₀ = exp (b 0) := by rw [h_b_start, exp_log (by positivity)]
  have h_x₁ : x₁ = exp (b (Fin.last N)) := by rw [h_b_end, exp_log (by linarith)]
  have h_int_b : IntervalIntegrable (fun t => Eθ t / (log t) ^ 2) volume (exp (b 0)) (exp (b (Fin.last N))) := by
    rwa [← h_x₀, ← h_x₁]
  have h_ind : ∀ n : Fin (N + 1), ∫ t in (exp (b 0))..(exp (b n)), Eθ t / (log t) ^ 2 = ∑ i ∈ Finset.Iio n, ∫ t in (exp (b i))..(exp (b (i + 1))), Eθ t / (log t) ^ 2 := by
    intro n
    induction n using Fin.induction with
    | zero => simp [show (Finset.Iio 0 : Finset (Fin (N + 1))) = ∅ by ext i; simp]
    | succ n ih =>
      have h_RHS : Set.uIcc (exp (b 0)) (exp (b (Fin.last N))) = Set.Icc (exp (b 0)) (exp (b (Fin.last N))) :=
        Set.uIcc_of_le (exp_le_exp.mpr (hmono (Fin.le_last _)))
      have h_succ : n.castSucc + 1 = Fin.succ n := by
        ext; simp
      rw [show (Finset.Iio (Fin.succ n) : Finset (Fin (N + 1))) = Finset.Iio (Fin.castSucc n) ∪ {Fin.castSucc n} by ext i; simp [Fin.lt_def, Fin.le_def],
        Finset.sum_union (by simp [Finset.disjoint_singleton_right]), Finset.sum_singleton, h_succ, ← ih, intervalIntegral.integral_add_adjacent_intervals]
      · refine h_int_b.mono_set ?_
        rw [h_RHS, Set.uIcc_of_le (exp_le_exp.mpr (hmono (Nat.zero_le n)))]
        exact Set.Icc_subset_Icc_right (exp_le_exp.mpr (hmono (Fin.le_last _)))
      · refine h_int_b.mono_set ?_
        rw [h_RHS, Set.uIcc_of_le (exp_le_exp.mpr (hmono (Nat.le_succ _)))]
        exact Set.Icc_subset_Icc (exp_le_exp.mpr (hmono (Nat.zero_le _))) (exp_le_exp.mpr (hmono (Fin.le_last _)))
  have h_bound_x₀_x₁ : ∫ t in x₀..x₁, Eθ t / (log t) ^ 2 ≤ ∑ i ∈ Finset.Iio (Fin.last N), ∫ t in (exp (b i))..(exp (b (i + 1))), Eθ t / (log t) ^ 2 := by
    rw [h_x₀, h_x₁]
    rw [h_ind (Fin.last N)]
  refine le_trans h_bound_x₀_x₁ <| Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_Iio, Fin.lt_def] at hi
  have h_le : b i ≤ b (i + 1) := hmono (by
    rw [Fin.le_iff_val_le_val, Fin.val_add]
    have h_one : (1 : Fin (N + 1)).val = 1 % (N + 1) := rfl
    rw [h_one]
    have h1 : 1 < N + 1 := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : i.val + 1 < N + 1 := by omega
    rw [Nat.mod_eq_of_lt h2]
    omega)
  have h_exp_le : exp (b i) ≤ exp (b (i + 1)) := exp_le_exp.mpr h_le
  have h_bound_x₀_x₁ : ∫ t in (exp (b i))..(exp (b (i + 1))), Eθ t / (log t) ^ 2 ≤ εθ_num (exp (b i)) * ∫ t in (exp (b i))..(exp (b (i + 1))), 1 / (log t) ^ 2 := by
    rw [intervalIntegral.integral_of_le h_exp_le, intervalIntegral.integral_of_le h_exp_le]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_mono_on
    · refine h_int_x₀_x₁.1.mono_set ?_
      refine Set.Ioc_subset_Ioc ?_ ?_
      · rw [← exp_log (by linarith : 0 < x₀), ← h_b_start]
        exact exp_le_exp.mpr (hmono (Nat.zero_le i))
      · rw [← exp_log (by linarith : 0 < x₁), ← h_b_end]
        exact exp_le_exp.mpr (hmono (by
          rw [Fin.le_iff_val_le_val, Fin.val_add]
          have h_one : (1 : Fin (N + 1)).val = 1 % (N + 1) := rfl
          rw [h_one]
          have h1 : 1 < N + 1 := by omega
          rw [Nat.mod_eq_of_lt h1]
          have h2 : i.val + 1 < N + 1 := by omega
          rw [Nat.mod_eq_of_lt h2]
          omega))
    · have h_ge_2 : 2 ≤ exp (b i) := h_exp_ge_2 i
      refine ContinuousOn.integrableOn_Icc ?_ |> fun h => h.mono_set Set.Ioc_subset_Icc_self
      have h_log : ∀ x ∈ Set.Icc (exp (b i)) (exp (b (i + 1))), log x ≠ 0 := by
        intro x hx
        have : x > 1 := by linarith [h_ge_2.trans hx.1]
        exact (Real.log_pos this).ne'
      refine ContinuousOn.const_mul ?_ _
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · refine continuousOn_of_forall_continuousAt fun x hx => ?_
        refine ContinuousAt.pow (Real.continuousAt_log ?_) 2
        linarith [h_ge_2.trans hx.1]
      · intro x hx
        exact pow_ne_zero 2 (h_log x hx)
    · exact measurableSet_Ioc
    · intro t ht₁
      rw [mul_one_div]; gcongr
      exact h_εθ_num i t ht₁.1.le
  have h_int_eq : (∫ t in (exp (b i))..(exp (b (i + 1))), 1 / (log t) ^ 2) =
      Li (exp (b (i + 1))) - Li (exp (b i)) + exp (b i) / b i - exp (b (i + 1)) / b (i + 1) := by
    rw [Li_identity' (h_exp_ge_2 i) h_exp_le, log_exp, log_exp]
    ring
  rw [h_int_eq] at h_bound_x₀_x₁
  exact h_bound_x₀_x₁

blueprint_comment /--
Now we can start estimating $E_\pi$.  We make the following running hypotheses. Let $x_0 > 0$ be chosen such that $\pi(x_0)$ and $\theta(x_0)$ are computable, and let   $x_1 \geq \max(x_0, 14)$. Let $\{b_i\}_{i=1}^N$ be a finite partition of   $[\log x_0, \log x_1]$, with $b_1 = \log x_0$ and $b_N = \log x_1$, and suppose that   $\varepsilon_{\theta,\mathrm{num}}$ gives numerical bounds for $x = \exp(b_i)$, for each $i=1,\dots,N$.
-/



@[blueprint
  "fks2-theorem-6-1"
  (title := "FKS2 Theorem 6, substep 1")
  (statement := /-- With the above hypotheses, for all $x \geq x_1$ we have
  $$ E_\pi(x) \leq \varepsilon_{\theta,num}(x_1) + \frac{\log x}{x} \frac{x_0}{\log x_0} (E_\pi(x_0) + E_\theta(x_0))$$
  $$ + \frac{\log x}{x} \sum_{i=1}^{N-1} \varepsilon_{\theta,num}(e^{b_i}) \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}} \right) $$
  $$ + \varepsilon_{\theta,num}(x_1) \frac{\log x}{x} \int_{x_1}^{x} \frac{1}{(\log t)^2} \, dt. $$ -/)
  (proof := /-- This is obtained by combining Sublemma \ref{fks2-eq-30} with the admissibility of $\varepsilon_{\theta,num}$ and Lemma \ref{fks2-lemma-19}.
  -/)
  (latexEnv := "sublemma")
  (discussion := 715)]
theorem theorem_6_1 {x₀ x₁ : ℝ} (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : ∀ i : Fin (N+1), Eθ.numericalBound (exp (b i)) εθ_num) (x : ℝ) (hx : x ≥ x₁) (hx₀ : x₀ ≥ 2) :
  Eπ x ≤ εθ_num x₁ + (log x / x) * (x₀ / log x₀) * (Eπ x₀ + Eθ x₀) +
    (log x / x) * ∑ i ∈ Finset.Iio (Fin.last N),
      εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) +
    εθ_num x₁ * (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2 := by
  have hx₀_le_x₁ : x₀ ≤ x₁ := le_trans (le_max_left _ _) h
  have hx₀_le_x : x₀ ≤ x := le_trans hx₀_le_x₁ hx
  have h30 := eq_30 hx₀_le_x hx₀
  have hEθ_x_le : Eθ x ≤ εθ_num x₁ := by
    have := h_εθ_num (Fin.last N)
    rw [h_b_end, exp_log (by linarith [h])] at this
    exact this x hx
  have hδ_le : δ x₀ ≤ Eπ x₀ + Eθ x₀ := by
    rw [δ, Eπ, Eθ]
    refine (abs_sub_le _ 0 _).trans ?_
    have hx₀_pos : 0 < x₀ := by positivity
    have hlogx₀_pos : 0 < log x₀ := Real.log_pos (by linarith)
    simp [abs_div, abs_of_pos hx₀_pos, abs_of_pos (by positivity : 0 < x₀ / log x₀)]
  have hx₁_ge2 : x₁ ≥ 2 := by linarith [h]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (Eθ_integrable hx₀ hx₀_le_x₁) (Eθ_integrable hx₁_ge2 hx)
  have hlogx_x_nonneg : 0 ≤ log x / x :=
    div_nonneg (Real.log_nonneg (by linarith [hx, h])) (by linarith [hx, h])
  have h_coeff_nonneg : 0 ≤ (log x / x) * (x₀ / log x₀) := by
    apply mul_nonneg hlogx_x_nonneg
    have : 0 < log x₀ := Real.log_pos (by linarith)
    exact div_nonneg (by linarith) this.le
  calc
    Eπ x ≤
        Eθ x
        + (log x / x) * (x₀ / log x₀) * δ x₀
        + (log x / x) * ∫ t in x₀..x, Eθ t / log t ^ 2 :=
      h30
    _ ≤ εθ_num x₁
        + (log x / x) * (x₀ / log x₀) * (Eπ x₀ + Eθ x₀)
        + (log x / x) * ∫ t in x₀..x, Eθ t / log t ^ 2 := by
      gcongr
    _ ≤ εθ_num x₁
        + (log x / x) * (x₀ / log x₀) * (Eπ x₀ + Eθ x₀)
        + (log x / x) *
          ((∫ t in x₀..x₁, Eθ t / log t ^ 2)
          + ∫ t in x₁..x, Eθ t / log t ^ 2) := by
      rw [hsplit]
    _ ≤ εθ_num x₁ + (log x / x) * (x₀ / log x₀) * (Eπ x₀ + Eθ x₀) +
      (log x / x) * ∑ i ∈ Finset.Iio (Fin.last N),
        εθ_num (exp (b i)) *
          (Li (exp (b (i + 1))) - Li (exp (b i)) +
          exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) +
      εθ_num x₁ * (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2 := by
      have h_bound_x1_x : ∫ t in x₁..x, Eθ t / log t ^ 2 ≤
          εθ_num x₁ * ∫ t in x₁..x, 1 / (log t) ^ 2 := by
        have := h_εθ_num (Fin.last N)
        rw [h_b_end, exp_log (by linarith [h])] at this
        exact Eθ_bound_integral_last hx₁_ge2 hx εθ_num this
      have h_bound_x0_x1 := bound_x0_x1 hx₀ hx₀_le_x₁ b hmono h_b_start h_b_end εθ_num h_εθ_num
      nlinarith [h_bound_x0_x1, h_bound_x1_x, hlogx_x_nonneg]



/- The following 2 lemmas are used for theorem_6_3.
-/


lemma integral_one_div_log_sq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / (log t) ^ 2 = (Li b - b / log b) - (Li a - a / log a) := by
  rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
  · exact fun x hx => hasDerivAt_Li_sub_div_log ( by cases Set.mem_uIcc.mp hx <;> linarith );
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) )

-- Proves $\int_{x₁}^s \frac{1}{\log^2 u} du \le \frac{s - x₁}{\log^2 x₁}$ for $1 < x₁ \le s$.
private lemma integral_one_div_log_sq_le_const {x₁ s : ℝ} (hx₁ : 1 < x₁) (h : x₁ ≤ s) :
    ∫ u in x₁..s, 1 / (Real.log u) ^ 2 ≤ (s - x₁) / (Real.log x₁) ^ 2 := by
  have h_bound : ∫ u in x₁..s, 1 / (Real.log u) ^ 2 ≤ ∫ u in x₁..s, 1 / (Real.log x₁) ^ 2 := by
    apply_rules [ intervalIntegral.integral_mono_on ];
    · apply ContinuousOn.intervalIntegrable
      -- Goal: ContinuousOn (fun u ↦ 1 / log u ^ 2) (uIcc x₁ s)
      apply ContinuousOn.div continuousOn_const
      · -- Continuity of (log ·)^2 on the interval
        apply ContinuousOn.pow
        apply Real.continuousOn_log.mono
        -- Need: ∀ u ∈ uIcc x₁ s, u ≠ 0
        intro u hu
        rw [Set.uIcc_of_le h] at hu
        -- u ≥ x₁ > 1 > 0, so u ≠ 0
        exact ne_of_gt (by linarith [hu.1])
      · -- Non-vanishing: (log u)^2 ≠ 0 on the interval
        intro u hu
        rw [Set.uIcc_of_le h] at hu
        have hlog : 0 < Real.log u :=
          Real.log_pos (hx₁.trans_le hu.1)
        exact pow_ne_zero _ hlog.ne'
    · apply_rules [ ContinuousOn.intervalIntegrable ]; exact continuousOn_const
    · intro x hx
      have hx₁' : 0 < Real.log x₁ := Real.log_pos hx₁
      have hlog : Real.log x₁ ≤ Real.log x :=
        Real.log_le_log (by linarith) hx.1
      have hlogx : 0 < Real.log x := hx₁'.trans_le hlog
      rw [div_le_div_iff₀ (pow_pos hlogx 2) (pow_pos hx₁' 2)]
      simp only [one_mul]
      nlinarith [sq_nonneg (Real.log x - Real.log x₁)]
  aesop

private lemma log_gt_two_of_ge_14 {x₁ : ℝ} (h : 14 ≤ x₁) : 2 < Real.log x₁ := by
  have : (2 : ℝ) < Real.log 14 := by
    rw [LogTables.log_14]; linarith [LogTables.log_2_gt, LogTables.log_7_gt]
  exact this.trans_le (Real.log_le_log (by norm_num) h)

lemma hasDerivAt_id_div_log_sq {s : ℝ} (hs : 1 < s) :
    HasDerivAt (fun s ↦ s / (Real.log s) ^ 2) (1 / (Real.log s) ^ 2 - 2 / (Real.log s) ^ 3) s := by
  have hlog : Real.log s ≠ 0 := ne_of_gt (Real.log_pos hs)
  have h_deriv := HasDerivAt.div (hasDerivAt_id s)
      (HasDerivAt.pow (Real.hasDerivAt_log (by linarith)) 2) (pow_ne_zero 2 hlog)
  convert! h_deriv using 1; field_simp [hlog]; simp; ring

lemma integral_one_div_log_sq_le_of_ge {x₁ : ℝ} (hx₁ : 14 ≤ x₁) {y : ℝ} (hy : x₁ ≤ y) :
    ∫ s in x₁..y, 1 / (Real.log s) ^ 2 ≤ (Real.log x₁ / (Real.log x₁ - 2)) * (y / (Real.log y) ^ 2) := by
  have hx₁_gt : 1 < x₁ := by linarith
  have hlogx₁ : 0 < Real.log x₁ := Real.log_pos hx₁_gt
  have hlogx₁_gt : 2 < Real.log x₁ := log_gt_two_of_ge_14 hx₁
  have hc : 0 < 1 - 2 / Real.log x₁ := by
    have : 2 / Real.log x₁ < 1 := (div_lt_iff₀ hlogx₁).mpr (by linarith)
    linarith
  have hs_gt_of_mem : ∀ s ∈ Set.uIcc x₁ y, 1 < s := fun s hs => by
    cases Set.mem_uIcc.mp hs <;> linarith
  have h_intble1 : IntervalIntegrable (fun s ↦ (1 - 2 / Real.log x₁) * (1 / (Real.log s) ^ 2)) volume x₁ y :=
    ContinuousOn.intervalIntegrable <| continuousOn_of_forall_continuousAt fun s hs ↦ by
      have hne : Real.log s ≠ 0 := ne_of_gt (Real.log_pos (hs_gt_of_mem s hs))
      exact ContinuousAt.mul continuousAt_const
        (ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log (by linarith [hs_gt_of_mem s hs])) 2)
          (pow_ne_zero 2 hne))
  have h_intble2 : IntervalIntegrable (fun s ↦ 1 / (Real.log s) ^ 2 - 2 / (Real.log s) ^ 3) volume x₁ y :=
    ContinuousOn.intervalIntegrable <| continuousOn_of_forall_continuousAt fun s hs ↦ by
      have hne : Real.log s ≠ 0 := ne_of_gt (Real.log_pos (hs_gt_of_mem s hs))
      have hs0 : s ≠ 0 := by linarith [hs_gt_of_mem s hs]
      exact (ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log hs0) 2) (pow_ne_zero 2 hne)).sub
        (ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log hs0) 3) (pow_ne_zero 3 hne))
  have h_mono : ∫ s in x₁..y, (1 - 2 / Real.log x₁) * (1 / (Real.log s) ^ 2) ≤
      ∫ s in x₁..y, (1 / (Real.log s) ^ 2 - 2 / (Real.log s) ^ 3) := by
    apply intervalIntegral.integral_mono_on hy h_intble1 h_intble2
    intro s hs
    have hs_gt : 1 < s := hx₁_gt.trans_le hs.1
    have hlogs : 0 < Real.log s := Real.log_pos hs_gt
    have hlog_le : Real.log x₁ ≤ Real.log s := Real.log_le_log (by linarith) hs.1
    have h_frac : 2 / Real.log s ≤ 2 / Real.log x₁ :=
      div_le_div_of_nonneg_left (by norm_num) hlogx₁ hlog_le
    rw [show (1 - 2 / Real.log x₁) * (1 / (Real.log s) ^ 2) = (1 - 2 / Real.log x₁) / (Real.log s) ^ 2 by ring,
        show 1 / (Real.log s) ^ 2 - 2 / (Real.log s) ^ 3 = (1 - 2 / Real.log s) / (Real.log s) ^ 2 by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h_int_eq : ∫ s in x₁..y, (1 / (Real.log s) ^ 2 - 2 / (Real.log s) ^ 3) =
      y / (Real.log y) ^ 2 - x₁ / (Real.log x₁) ^ 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hasDerivAt_id_div_log_sq (hx₁_gt.trans_le (Set.uIcc_of_le hy ▸ hs).1))
      h_intble2
  rw [intervalIntegral.integral_const_mul] at h_mono
  have h_bound : (1 - 2 / Real.log x₁) * ∫ s in x₁..y, 1 / (Real.log s) ^ 2 ≤ y / (Real.log y) ^ 2 :=
    calc (1 - 2 / Real.log x₁) * ∫ s in x₁..y, 1 / (Real.log s) ^ 2
        ≤ ∫ s in x₁..y, (1 / (Real.log s) ^ 2 - 2 / (Real.log s) ^ 3) := h_mono
      _ = y / (Real.log y) ^ 2 - x₁ / (Real.log x₁) ^ 2 := h_int_eq
      _ ≤ y / (Real.log y) ^ 2 := by linarith [div_nonneg (by linarith : 0 ≤ x₁) (by positivity : (0 : ℝ) ≤ (Real.log x₁) ^ 2)]
  have h_bound' : ∫ s in x₁..y, 1 / (Real.log s) ^ 2 ≤ (y / (Real.log y) ^ 2) / (1 - 2 / Real.log x₁) := by
    rwa [le_div_iff₀ hc, mul_comm]
  convert h_bound' using 1
  field_simp

lemma log_div_self_mul_integral_le_of_ge {x₁ : ℝ} (hx₁ : 14 ≤ x₁) {y : ℝ} (hy : x₁ ≤ y) :
    (Real.log y / y) * ∫ s in x₁..y, 1 / (Real.log s) ^ 2 ≤ (Real.log x₁ / (Real.log x₁ - 2)) / Real.log y := by
  have hlogy_pos : 0 < Real.log y := Real.log_pos ((by linarith : 1 < x₁).trans_le hy)
  refine (mul_le_mul_of_nonneg_left (integral_one_div_log_sq_le_of_ge hx₁ hy)
      (div_nonneg hlogy_pos.le (by linarith))).trans_eq ?_
  have hlogx₁_gt : 2 < Real.log x₁ := log_gt_two_of_ge_14 hx₁
  field_simp [show Real.log x₁ - 2 ≠ 0 by linarith, hlogy_pos.ne', show y ≠ 0 by linarith]

private lemma log_gt_one_of_ge_14 {x₁ : ℝ} (h : 14 ≤ x₁) : 1 < Real.log x₁ := by
  have hexp : Real.exp 1 < x₁ := by linarith [Real.exp_one_lt_d9, show (2.7182818286:ℝ) < 14 by norm_num]
  rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  exact Real.log_lt_log (Real.exp_pos 1) hexp

lemma x1_le_x1_log_x1 {x₁ : ℝ} (h : 14 ≤ x₁) : x₁ ≤ x₁ * Real.log x₁ :=
  le_mul_of_one_le_right (by linarith) (log_gt_one_of_ge_14 h).le

lemma x1_lt_x1_log_x1 {x₁ : ℝ} (h : 14 ≤ x₁) : x₁ < x₁ * Real.log x₁ :=
  lt_mul_of_one_lt_right (by linarith) (log_gt_one_of_ge_14 h)

lemma log_div_self_mul_integral_nonneg {x₁ : ℝ} (hx₁ : 14 ≤ x₁) {y : ℝ} (hy : x₁ ≤ y) :
    0 ≤ (Real.log y / y) * ∫ s in x₁..y, 1 / (Real.log s) ^ 2 := by
  have hx₁_gt : 1 < x₁ := by linarith
  have hlogy_pos : 0 < Real.log y := Real.log_pos (hx₁_gt.trans_le hy)
  exact mul_nonneg (div_nonneg hlogy_pos.le (by linarith))
    (intervalIntegral.integral_nonneg hy fun s hs ↦ by
      have : s > 1 := hx₁_gt.trans_le hs.1; positivity)

lemma tendsto_log_div_self_mul_integral_atTop_zero {x₁ : ℝ} (hx₁ : 14 ≤ x₁) :
    Filter.Tendsto (fun y ↦ (Real.log y / y) * ∫ s in x₁..y, 1 / (Real.log s) ^ 2) Filter.atTop (nhds 0) := by
  have h_lim : Filter.Tendsto (fun y ↦ Real.log x₁ / (Real.log x₁ - 2) / Real.log y) Filter.atTop (nhds 0) := by
    have h_inv : Filter.Tendsto (fun y ↦ (Real.log y)⁻¹) Filter.atTop (nhds 0) :=
      Filter.Tendsto.comp tendsto_inv_atTop_zero Real.tendsto_log_atTop
    have := tendsto_const_nhds (x := Real.log x₁ / (Real.log x₁ - 2)) |>.mul h_inv
    simp only [mul_zero] at this
    rwa [show (fun x ↦ Real.log x₁ / (Real.log x₁ - 2) * (Real.log x)⁻¹) =
        (fun y ↦ Real.log x₁ / (Real.log x₁ - 2) / Real.log y) by ext y; ring] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop x₁] with y hy
    exact log_div_self_mul_integral_nonneg hx₁ hy
  · filter_upwards [Filter.eventually_ge_atTop x₁] with y hy
    exact log_div_self_mul_integral_le_of_ge hx₁ hy

private lemma integral_sub_div_self {x₁ t : ℝ} (hx₁ : 0 < x₁) (ht : x₁ ≤ t) :
    ∫ s in x₁..t, (s - x₁) / s = (t - x₁) - x₁ * Real.log (t / x₁) := by
  rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
  rotate_right;
  next => use fun x => x - x₁ * Real.log x;
  · rw [ Real.log_div ] <;> linarith
  · intro x hx; convert! HasDerivAt.sub ( hasDerivAt_id x ) ( HasDerivAt.const_mul x₁ ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) using 1 ; ring_nf;
    rw [ mul_inv_cancel₀ ( by cases Set.mem_uIcc.mp hx <;> linarith ) ];
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact continuousOn_of_forall_continuousAt fun s hs => ContinuousAt.div ( continuousAt_id.sub continuousAt_const ) continuousAt_id ( by cases Set.mem_uIcc.mp hs <;> linarith );

private lemma integral_I_div_self_le {x₁ t : ℝ} (hx₁ : 14 ≤ x₁) (ht : t ∈ Set.Icc x₁ (x₁ * Real.log x₁)) :
    ∫ s in x₁..t, (∫ u in x₁..s, 1 / (Real.log u) ^ 2) / s ≤
      (1 / (Real.log x₁) ^ 2) * ∫ s in x₁..t, (s - x₁) / s := by
  have hx₁_gt_1 : 1 < x₁ := by linarith
  have h_bound : ∀ s ∈ Set.Icc x₁ t, (∫ u in x₁..s, 1 / (Real.log u) ^ 2) ≤ (s - x₁) / (Real.log x₁) ^ 2 := by
    intros s hs
    exact integral_one_div_log_sq_le_const hx₁_gt_1 hs.1
  rw [ ← intervalIntegral.integral_const_mul ];
  refine intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_ <;> norm_num;
  · linarith [ ht.1 ];
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    apply ContinuousOn.div
    · intro u hu; apply_rules [ intervalIntegral.continuousWithinAt_primitive ]
      · aesop
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        simp +zetaDelta only [Set.mem_Icc, one_div, and_imp, inf_le_left, inf_of_le_right, le_sup_left, sup_of_le_right, le_sup_iff, inf_le_right, or_self, Set.uIcc_of_le] at *;
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases min_cases x₁ t <;> cases max_cases x₁ t <;> linarith [ hx.1, hx.2 ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases min_cases x₁ t <;> cases max_cases x₁ t <;> linarith [ hx.1, hx.2 ] ) ) ) );
    · exact continuousOn_id
    · intro s hs; cases Set.mem_uIcc.mp hs <;> linarith [ ht.1, ht.2 ];
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul continuousAt_const <| ContinuousAt.div ( continuousAt_id.sub continuousAt_const ) continuousAt_id <| by cases Set.mem_uIcc.mp hx <;> linarith [ ht.1, ht.2 ] ;
  · intro s hs₁ hs₂
    convert! mul_le_mul_of_nonneg_right ( h_bound s ⟨ hs₁, hs₂ ⟩ ) ( inv_nonneg.mpr ( by linarith : 0 ≤ s ) ) using 1
    · ring_nf
    · field_simp

private lemma u_eq_sub_integral {x₁ t : ℝ} (hx₁ : 14 ≤ x₁) (ht : t ∈ Set.Icc x₁ (x₁ * Real.log x₁)) :
    t / Real.log t - (Real.log t - 1) * (∫ s in x₁..t, 1 / (Real.log s) ^ 2) =
      x₁ / Real.log x₁ - ∫ s in x₁..t, (∫ u in x₁..s, 1 / (Real.log u) ^ 2) / s := by
  set I : ℝ → ℝ := fun t => ∫ s in x₁..t, 1 / (Real.log s) ^ 2;
  have h_integral : ∫ s in x₁..t, (I s) / s = ((Real.log t - 1) * I t - t / Real.log t) - ((Real.log x₁ - 1) * I x₁ - x₁ / Real.log x₁) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      have hI_deriv : HasDerivAt I (1 / (Real.log x) ^ 2) x := by
        apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun y hy => ContinuousAt.div continuousAt_const ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hy <;> linarith [ Set.mem_Icc.mp ( show x ∈ Set.Icc x₁ ( x₁ * Real.log x₁ ) from by cases Set.mem_uIcc.mp hx <;> constructor <;> linarith [ ht.1, ht.2 ] ) ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hy <;> linarith [ Set.mem_Icc.mp ( show x ∈ Set.Icc x₁ ( x₁ * Real.log x₁ ) from by cases Set.mem_uIcc.mp hx <;> constructor <;> linarith [ ht.1, ht.2 ] ) ] ) ) ) );
        · exact Measurable.stronglyMeasurable ( by exact Measurable.div measurable_const ( by exact Measurable.pow_const ( Real.measurable_log ) _ ) ) |> fun h => h.stronglyMeasurableAtFilter;
        · exact ContinuousAt.div continuousAt_const ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ ht.1, ht.2 ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ ht.1, ht.2 ] ) ) ) );
      convert! HasDerivAt.sub ( HasDerivAt.mul ( HasDerivAt.sub ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith [ ht.1, ht.2 ] ) ) ( hasDerivAt_const _ _ ) ) hI_deriv ) ( HasDerivAt.div ( hasDerivAt_id x ) ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith [ ht.1, ht.2 ] ) ) ( ne_of_gt ( Real.log_pos ( show x > 1 by cases Set.mem_uIcc.mp hx <;> linarith [ ht.1, ht.2 ] ) ) ) ) using 1 ; ring_nf;
      by_cases h : x = 0
      · simp [h]
      simp +decide [h, sq, mul_comm]; ring;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      apply ContinuousOn.div
      · intro u hu; apply_rules [ intervalIntegral.continuousWithinAt_primitive ]
        · aesop
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          simp +zetaDelta only [Set.mem_Icc, one_div, inf_le_left, inf_of_le_right, le_sup_left,
            sup_of_le_right, le_sup_iff, inf_le_right, or_self, Set.uIcc_of_le] at *;
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases min_cases x₁ t <;> cases max_cases x₁ t <;> linarith [ hx.1, hx.2 ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases min_cases x₁ t <;> cases max_cases x₁ t <;> linarith [ hx.1, hx.2 ] ) ) ) );
      · exact continuousOn_id
      · intro s hs; cases Set.mem_uIcc.mp hs <;> linarith [ ht.1, ht.2 ];
  have h_I_x₁ : I x₁ = 0 := intervalIntegral.integral_same
  change t / Real.log t - (Real.log t - 1) * I t = x₁ / Real.log x₁ - ∫ s in x₁..t, (I s) / s
  rw [ h_integral, h_I_x₁ ]
  ring

private lemma hu_simplify {x₁ t : ℝ} (hx₁ : 14 ≤ x₁) (ht : t ∈ Set.Icc x₁ (x₁ * Real.log x₁)) :
    x₁ / Real.log x₁ - (1 / (Real.log x₁) ^ 2) * (t - x₁ - x₁ * Real.log (t / x₁)) ≥ 0 := by
  field_simp;
  rw [ le_div_iff₀ ( sq_pos_of_pos <| Real.log_pos <| by linarith ) ];
  nlinarith [ ht.1, ht.2, Real.log_nonneg ( show 1 ≤ x₁ by linarith ), Real.log_le_log ( by linarith ) ht.1, Real.log_le_log ( by linarith [ ht.1 ] ) ht.2, Real.log_div ( show t ≠ 0 by linarith [ ht.1 ] ) ( show x₁ ≠ 0 by linarith ) ];

private lemma continuousOn_one_div_log_sq_Ioi :
    ContinuousOn (fun s : ℝ ↦ 1 / (Real.log s) ^ 2) (Set.Ioi 1) := by
  intro y hy
  have hlog_pos : 0 < Real.log y := Real.log_pos hy
  have hy0 : y ≠ 0 := by
    have : 1 < y := Set.mem_Ioi.mp hy
    linarith
  exact (ContinuousAt.div continuousAt_const
    (ContinuousAt.pow (Real.continuousAt_log hy0) 2)
    (pow_ne_zero 2 hlog_pos.ne')).continuousWithinAt

private lemma hasDerivAt_integral_one_div_log_sq {x₁ t : ℝ} (hx₁ : 1 < x₁) (ht : x₁ ≤ t) :
    HasDerivAt (fun u ↦ ∫ s in x₁..u, 1 / (Real.log s) ^ 2) (1 / (Real.log t) ^ 2) t := by
  have ht_gt : 1 < t := hx₁.trans_le ht
  apply intervalIntegral.integral_hasDerivAt_right
  · exact ContinuousOn.intervalIntegrable
      (continuousOn_one_div_log_sq_Ioi.mono fun s hs =>
        Set.mem_Ioi.mpr (by rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ <;> linarith))
  · exact continuousOn_one_div_log_sq_Ioi.stronglyMeasurableAtFilter
      isOpen_Ioi t (Set.mem_Ioi.mpr ht_gt)
  · exact continuousOn_one_div_log_sq_Ioi.continuousAt
      (isOpen_Ioi.mem_nhds ht_gt)

lemma hasDerivAt_log_div_self_mul_integral {x₁ : ℝ} (hx₁ : 1 < x₁) {t : ℝ} (ht : x₁ < t) :
    HasDerivAt (fun t => (Real.log t / t) * ∫ s in x₁..t, 1 / (Real.log s) ^ 2)
      ((t / Real.log t - (Real.log t - 1) * ∫ s in x₁..t, 1 / (Real.log s) ^ 2) / t^2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlogt0 : Real.log t ≠ 0 := ne_of_gt ( Real.log_pos (by linarith : 1 < t) )
  have ht20 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have hlogt20 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlogt0
  have h_deriv_I := hasDerivAt_integral_one_div_log_sq hx₁ ht.le
  convert! HasDerivAt.mul ( HasDerivAt.div ( Real.hasDerivAt_log ht0 ) ( hasDerivAt_id t ) ht0 ) h_deriv_I using 1
  dsimp; field_simp [ht0, hlogt0, ht20, hlogt20]; ring_nf

-- Proves the derivative of $(log t / t) * I t$.
private lemma h_deriv_at {x₁ t : ℝ} (hx₁ : 14 ≤ x₁) (ht : t ∈ Set.Ioo x₁ (x₁ * Real.log x₁)) :
    HasDerivAt (fun t => (Real.log t / t) * ∫ s in x₁..t, 1 / (Real.log s) ^ 2)
      ((t / Real.log t - (Real.log t - 1) * ∫ s in x₁..t, 1 / (Real.log s) ^ 2) / t^2) t :=
  hasDerivAt_log_div_self_mul_integral (by linarith : 1 < x₁) ht.1

lemma h_monotoneOn {x₁ : ℝ} (hx₁ : x₁ ≥ 14) :
    MonotoneOn (fun t => (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2)
      (Set.Icc x₁ (x₁ * log x₁)) := by
  -- Let $I(t) = \int_{x₁}^t 1 / (\log s)^2 \, ds$.
  set I : ℝ → ℝ := fun t => ∫ s in x₁..t, 1 / (Real.log s) ^ 2;
  -- We need to show that $u(t) = \frac{t}{\log t} - (\log t - 1)I(t)$ is non-negative on $[x₁, x₁ \log x₁]$.
  have hu_nonneg : ∀ t ∈ Set.Icc x₁ (x₁ * Real.log x₁), t / Real.log t - (Real.log t - 1) * I t ≥ 0 := by
    intros t ht
    have h_u_eq := u_eq_sub_integral hx₁ ht
    have h_I_bound := integral_I_div_self_le hx₁ ht
    rw [integral_sub_div_self (by linarith : 0 < x₁) ht.1] at h_I_bound
    dsimp only [I]
    linarith [hu_simplify hx₁ ht]
  have h_deriv : ∀ t ∈ Set.Ioo x₁ (x₁ * Real.log x₁), HasDerivAt (fun t => (Real.log t / t) * I t) ((t / Real.log t - (Real.log t - 1) * I t) / t^2) t :=
    fun t ht => h_deriv_at hx₁ ht
  intro a ha b hb hab; rcases eq_or_lt_of_le hab with rfl | hab' <;> norm_num at *;
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo a b, deriv (fun t => (Real.log t / t) * I t) c = ((fun t => (Real.log t / t) * I t) b - (fun t => (Real.log t / t) * I t) a) / (b - a) := by
    apply_rules [ exists_deriv_eq_slope ];
    · refine ContinuousOn.mul ( ContinuousOn.div ( Real.continuousOn_log.mono <| by intro t ht; exact ne_of_gt <| by linarith [ ht.1 ] ) continuousOn_id <| by intro t ht; linarith [ ht.1 ] ) ?_;
      intro t ht; apply_rules [ intervalIntegral.continuousWithinAt_primitive ]
      · aesop
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> cases min_cases x₁ a <;> cases max_cases x₁ b <;> linarith [ ht.1, ht.2 ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> cases min_cases x₁ a <;> cases max_cases x₁ b <;> linarith [ ht.1, ht.2 ] ) ) ) );
    · exact fun t ht => ( h_deriv t ( by linarith [ ht.1 ] ) ( by linarith [ ht.2 ] ) |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt );
  simp +zetaDelta only [one_div, Set.mem_Ioo] at *
  have hd := (h_deriv c (by linarith) (by linarith)).deriv
  rw [eq_div_iff] at * <;> nlinarith [hu_nonneg c (by linarith) (by linarith), show 0 < c ^ 2 by nlinarith]

theorem hasDerivAt_log_div_self_mul_integral_one_div_log_sq {x₁ : ℝ} (h : x₁ ≥ 14) :
    HasDerivAt (fun t ↦ (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2)
      (deriv (fun t ↦ (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2) (x₁ * log x₁))
      (x₁ * log x₁) := by
  have h_logx₁_gt : 1 < Real.log x₁ := log_gt_one_of_ge_14 h
  have hD := hasDerivAt_log_div_self_mul_integral (by linarith : 1 < x₁) (by nlinarith : x₁ < x₁ * Real.log x₁)
  rwa [hD.deriv]

lemma deriv_log_div_self_mul_integral_one_div_log_sq_pos {x₁ : ℝ} (h : x₁ ≥ 14) :
    deriv (fun t ↦ (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2) (x₁ * log x₁) > 0 := by
  have h_logx₁_gt : 1 < Real.log x₁ := log_gt_one_of_ge_14 h
  have ht₀_pos : 0 < x₁ * log x₁ := mul_pos (by linarith) (by linarith)
  have hx₁_le_x₀ : x₁ ≤ x₁ * Real.log x₁ := x1_le_x1_log_x1 h
  have h_deriv_t₀ := hasDerivAt_log_div_self_mul_integral (by linarith : 1 < x₁) (by nlinarith : x₁ < x₁ * log x₁)
  rw [h_deriv_t₀.deriv]
  have ht₀_sq_pos : 0 < (x₁ * log x₁) ^ 2 := pow_pos ht₀_pos 2
  refine div_pos ?_ ht₀_sq_pos
  have ht₀_mem : x₁ * log x₁ ∈ Set.Icc x₁ (x₁ * log x₁) := ⟨hx₁_le_x₀, le_refl _⟩
  have h_sub_div_t₀ : ∫ s in x₁..x₁ * log x₁, (s - x₁) / s = x₁ * log x₁ - x₁ - x₁ * log (log x₁) := by
    have h_sub := integral_sub_div_self (by linarith : 0 < x₁) hx₁_le_x₀
    rw [mul_div_cancel_left₀ _ (by linarith : x₁ ≠ 0)] at h_sub
    linarith
  have h_I_bound_t₀ : ∫ s in x₁..x₁ * log x₁, (∫ u in x₁..s, 1 / (log u) ^ 2) / s ≤
      (1 / (log x₁) ^ 2) * (x₁ * log x₁ - x₁ - x₁ * log (log x₁)) :=
    h_sub_div_t₀ ▸ integral_I_div_self_le (by linarith) ht₀_mem
  have h_u_eq_t₀ := u_eq_sub_integral (by linarith) ht₀_mem
  have h_pos_bound : x₁ / log x₁ - (1 / (log x₁) ^ 2) * (x₁ * log x₁ - x₁ - x₁ * log (log x₁)) > 0 := by
    have h_logx₁_pos : 0 < log x₁ := Real.log_pos (by linarith)
    have h_loglogx₁_pos : 0 < log (log x₁) := Real.log_pos h_logx₁_gt
    have h_eq : x₁ / log x₁ - (1 / (log x₁) ^ 2) * (x₁ * log x₁ - x₁ - x₁ * log (log x₁)) =
        x₁ * (1 + log (log x₁)) / (log x₁) ^ 2 := by
      field_simp
      ring
    rw [h_eq]
    positivity
  linarith [h_u_eq_t₀, h_I_bound_t₀, h_pos_bound]

lemma exists_larger_than_boundary_val {x₁ : ℝ} (h : x₁ ≥ 14) :
    ∃ t > x₁ * log x₁, (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2 >
      (log (x₁ * log x₁) / (x₁ * log x₁)) * ∫ s in x₁..(x₁ * log x₁), 1 / (log s) ^ 2 := by
  have h_deriv : deriv (fun t ↦ (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2) (x₁ * log x₁) > 0 :=
    deriv_log_div_self_mul_integral_one_div_log_sq_pos h
  have h_tendsto := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_log_div_self_mul_integral_one_div_log_sq h)
  have h_slope_pos : ∀ᶠ t in nhdsWithin (x₁ * log x₁) (Set.Ioi (x₁ * log x₁)), slope (fun t ↦ (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2) (x₁ * log x₁) t > 0 :=
    Filter.Eventually.filter_mono (nhdsWithin_mono (x₁ * log x₁) (fun _ h ↦ ne_of_gt h))
      (Filter.Tendsto.eventually_const_lt h_deriv h_tendsto)
  have h_exists : ∃ t > x₁ * log x₁, slope (fun t ↦ (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2) (x₁ * log x₁) t > 0 := by
    haveI : Filter.NeBot (nhdsWithin (x₁ * log x₁) {x | (fun x ↦ x > x₁ * log x₁) x}) := nhdsWithin_Ioi_neBot le_rfl
    exact Filter.Eventually.exists (Filter.Eventually.and self_mem_nhdsWithin h_slope_pos)
  obtain ⟨t, ht_gt, ht_slope⟩ := h_exists
  have h_val : (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2 >
    (log (x₁ * log x₁) / (x₁ * log x₁)) * ∫ s in x₁..(x₁ * log x₁), 1 / (log s) ^ 2 :=
    (slope_pos_iff_of_le ht_gt.le).mp ht_slope
  exact ⟨t, ht_gt, h_val⟩

lemma exists_isMaxOn_Ici_log_div_self_mul_integral_one_div_log_sq {x₁ : ℝ} (h : x₁ ≥ 14) : ∃ xm > x₁, xm > x₁ * log x₁ ∧
  ∀ y ≥ x₁, (log y / y) * ∫ t in x₁..y, 1 / (log t) ^ 2 ≤ 1 / (log xm - 1) := by
  obtain ⟨t₁, ht₁_gt, ht₁_val⟩ := exists_larger_than_boundary_val h
  have ht₁_ge : x₁ ≤ t₁ := (x1_le_x1_log_x1 h).trans ht₁_gt.le
  have h_exists_max : ∃ xm ≥ x₁, ∀ y ≥ x₁,
    (log y / y) * ∫ t in x₁..y, 1 / (log t) ^ 2 ≤ (log xm / xm) * ∫ t in x₁..xm, 1 / (log t) ^ 2 := by
    have hc_pos : 0 < (log t₁ / t₁) * ∫ s in x₁..t₁, 1 / (log s) ^ 2 :=
      (log_div_self_mul_integral_nonneg h (x1_le_x1_log_x1 h)).trans_lt ht₁_val
    have h_eventually : ∀ᶠ y in Filter.atTop,
        (log y / y) * ∫ s in x₁..y, 1 / (log s) ^ 2 <
        (log t₁ / t₁) * ∫ s in x₁..t₁, 1 / (log s) ^ 2 := by
      filter_upwards [tendsto_log_div_self_mul_integral_atTop_zero h
          (Metric.ball_mem_nhds 0 hc_pos),
        Filter.eventually_ge_atTop x₁] with y hy hy_ge
      rwa [Set.mem_preimage, Metric.mem_ball, Real.dist_0_eq_abs,
           abs_of_nonneg (log_div_self_mul_integral_nonneg h hy_ge)] at hy
    obtain ⟨M, hM_prop⟩ := Filter.eventually_atTop.mp h_eventually
    set M' := max (max M t₁) x₁
    have hM'_ge_x₁ : x₁ ≤ M' := le_max_right (max M t₁) x₁
    have hM'_ge_t₁ : t₁ ≤ M' := (le_max_right M t₁).trans (le_max_left (max M t₁) x₁)
    have hM'_ge_M  : M ≤ M'  := (le_max_left M t₁).trans (le_max_left (max M t₁) x₁)
    have h_int_M' : IntervalIntegrable (fun s ↦ 1 / (Real.log s) ^ 2) volume x₁ M' := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hM'_ge_x₁]
      intro s hs
      have hs0 : s ≠ 0 := ne_of_gt (by linarith [hs.1] : 0 < s)
      have hlog_ne : Real.log s ≠ 0 :=
        ne_of_gt (Real.log_pos (by linarith [hs.1] : 1 < s))
      exact (ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log hs0) 2)
        (pow_ne_zero 2 hlog_ne)).continuousWithinAt
    have h_cont_f : ContinuousOn
        (fun y ↦ (Real.log y / y) * ∫ t in x₁..y, 1 / (Real.log t) ^ 2) (Set.Icc x₁ M') := by
      apply ContinuousOn.mul
      · intro y hy
        exact (ContinuousAt.div (Real.continuousAt_log (ne_of_gt (by linarith [hy.1] : 0 < y)))
          continuousAt_id (by simp; linarith [hy.1])).continuousWithinAt
      · rw [← Set.uIcc_of_le hM'_ge_x₁]
        exact intervalIntegral.continuousOn_primitive_interval' h_int_M' Set.left_mem_uIcc
    obtain ⟨xm, hxm_mem, hxm_max⟩ :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hM'_ge_x₁) h_cont_f
    exact ⟨xm, hxm_mem.1, fun y hy_ge ↦ by
      by_cases hy_le : y ≤ M'
      · exact hxm_max ⟨hy_ge, hy_le⟩
      · have hy_ge_M : M ≤ y := by linarith [hM'_ge_M, not_le.mp hy_le]
        exact ((hM_prop y hy_ge_M).trans_le (hxm_max ⟨ht₁_ge, hM'_ge_t₁⟩)).le⟩
  obtain ⟨xm, hxm_ge, hxm_max⟩ := h_exists_max
  have h_xm_gt : xm > x₁ * log x₁ := by
    by_contra hle
    push Not at hle
    linarith [h_monotoneOn h ⟨hxm_ge, hle⟩ ⟨x1_le_x1_log_x1 h, le_refl _⟩ hle,
              hxm_max t₁ ((x1_lt_x1_log_x1 h).trans ht₁_gt |>.le)]
  have h_max_val : (log xm / xm) * ∫ t in x₁..xm, 1 / (log t) ^ 2 = 1 / (log xm - 1) := by
    have hxm_gt : x₁ < xm := (x1_lt_x1_log_x1 h).trans h_xm_gt
    have h_local_max : IsLocalMax (fun t ↦ (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2) xm := by
      filter_upwards [eventually_ge_nhds hxm_gt] with y hy using hxm_max y hy
    have h_deriv_xm : HasDerivAt (fun t ↦ (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2)
        ((xm / log xm - (log xm - 1) * ∫ s in x₁..xm, 1 / (log s) ^ 2) / xm ^ 2) xm :=
      hasDerivAt_log_div_self_mul_integral (by linarith : 1 < x₁) hxm_gt
    have h_num_eq_zero : xm / log xm - (log xm - 1) * ∫ s in x₁..xm, 1 / (log s) ^ 2 = 0 :=
      div_eq_zero_iff.mp (h_deriv_xm.deriv ▸ h_local_max.deriv_eq_zero)
        |>.resolve_right (pow_ne_zero 2 (by linarith : xm ≠ 0))
    have h_logxm_gt : log xm > 1 := by
      have h1 : log x₁ > 1 := log_gt_one_of_ge_14 h
      linarith [Real.log_le_log (by positivity) h_xm_gt.le, Real.log_pos h1,
                Real.log_mul (by linarith : x₁ ≠ 0) (by linarith : log x₁ ≠ 0)]
    have h_logxm_sub_ne : log xm - 1 ≠ 0 := by linarith
    have h_logxm_ne : log xm ≠ 0 := by linarith
    have h_xm_ne : xm ≠ 0 := by linarith
    rw [show (log xm / xm) * ∫ s in x₁..xm, 1 / (log s) ^ 2 =
        ((log xm - 1) * ∫ s in x₁..xm, 1 / (log s) ^ 2) * (log xm / (xm * (log xm - 1)))
        from by field_simp,
      show (log xm - 1) * ∫ s in x₁..xm, 1 / (log s) ^ 2 = xm / log xm
        from by linarith [h_num_eq_zero]]
    field_simp [h_logxm_sub_ne, h_logxm_ne, h_xm_ne]
  exact ⟨xm, (x1_lt_x1_log_x1 h).trans h_xm_gt, h_xm_gt,
    fun y hy ↦ (hxm_max y hy).trans h_max_val.le⟩

@[blueprint
  "fks2-theorem-6-2"
  (title := "FKS2 Theorem 6, substep 2")
  (statement := /-- With the above hypotheses, for all $x \geq x_1$ we have
  $$ \frac{\log x}{x} \int_{x_1}^x \frac{dt}{\log^2 t} < \frac{1}{\log x_1 + \log \log x_1 - 1}. $$ -/)
  (proof := /-- Call the left-hand side $f(x)$. We have
  $$ f(x) = \frac{\log x}{x} \left( \mathrm{Li}(x) - \frac{x}{\log x} - \mathrm{Li}(x_1) + \frac{x_1}{\log x_1} \right). $$
  Using integration by parts, its derivative can be written as
  $$ f'(x) = -\frac{1}{x \log^2 x} + \frac{2}{x \log^3 x} + \frac{\log x - 1}{x^2} \left( \frac{x_1}{\log^2 x_1} + \frac{2 x_1}{\log^3 x_1} - \int_{x_1}^x \frac{6}{\log^4 t} dt \right). $$
  From which we see that $f'(x_1) = \frac{1}{\log x_1} > 0$, and that $f'(x)$ is eventually negative. Thus there exists a critical point for $f(x)$ to the right of $x_1$. Moreover, by bounding $\int_{x_1}^x \frac{6}{\log^4 t} dt < 6 \frac{x - x_1}{\log^4 x_1}$, one finds that $f'(x_1 \log x_1) > 0$ if $x_1 > e$.
  Now we write $f'(x) = \frac{f_1(x)}{x^2}$ with
  $$ f_1(x) = \frac{x}{\log x} - (\log x - 1) \int_{x_1}^x \frac{1}{\log^2 t} dt. $$
  Its derivative is $f_1'(x) = -\frac{1}{x} \int_{x_1}^x \frac{1}{\log^2 t} dt$, which is negative for $x > x_1$. Thus $f_1(x)$ decreases and vanishes at most once, giving $f(x)$ at most one critical point, $x_m > x_1$, which is then the maximum of $f(x)$. In other words, $x_m$ satisfies $f_1(x_m) = 0$, i.e.\ $\mathrm{Li}(x_m) - \mathrm{Li}(x_1) + \frac{x_1}{\log x_1} = -\frac{x_m}{1 - \log x_m}$, which shows that $f(x)$ attains its maximum at $x = x_m$, where
  $$ f(x_m) = \frac{\log x_m}{x_m} \left( -\frac{x_m}{\log x_m} - \frac{x_m}{1 - \log x_m} \right) = \frac{1}{\log x_m - 1}. $$
  Now, because $x_m > x_1 \log x_1$ we obtain the bound
  $$ f(x) < \frac{1}{\log x_1 + \log(\log x_1) - 1}, $$
  which gives the announced result.
  -/)
  (latexEnv := "sublemma")
  (discussion := 716)]
theorem theorem_6_2 {x₁ : ℝ} (h : x₁ ≥ 14) (x : ℝ) (hx : x ≥ x₁) :
  (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2 < 1 / (log x₁ + log (log x₁) - 1) := by
  have h_denom_pos : 0 < log x₁ + log (log x₁) - 1 := by
    have hlog14 : log 14 ≤ log x₁ := Real.log_le_log (by norm_num) h
    have hlog14_pos : 0 < log 14 := Real.log_pos (by norm_num)
    linarith [Real.log_le_log hlog14_pos hlog14,
              show (0 : ℝ) < log 14 + log (log 14) - 1 from by interval_decide]
  rcases exists_isMaxOn_Ici_log_div_self_mul_integral_one_div_log_sq h with ⟨xm, hxm_gt, hxm_bound, h_max⟩
  have h_log_sub_lt : log x₁ + log (log x₁) - 1 < log xm - 1 := by
    have h1 : log x₁ > 1 := log_gt_one_of_ge_14 h
    have h_log_mul : log (x₁ * log x₁) = log x₁ + log (log x₁) :=
      Real.log_mul (by linarith : x₁ ≠ 0) (by linarith : log x₁ ≠ 0)
    linarith [Real.log_lt_log (mul_pos (by linarith : 0 < x₁) (by linarith : 0 < log x₁)) hxm_bound,
              h_log_mul]
  calc (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2
      ≤ 1 / (log xm - 1)                        := h_max x hx
    _ < 1 / (log x₁ + log (log x₁) - 1)         := one_div_lt_one_div_of_lt h_denom_pos h_log_sub_lt


@[blueprint
  "fks2-theorem-6-3"
  (title := "FKS2 Theorem 6, substep 3")
  (statement := /-- With the above hypotheses, for all $x \geq x_1$ we have
  $$ \frac{\log x}{x} \int_{x_1}^x \frac{dt}{\log^2 t} \leq \frac{\log x_2}{x_2} \left( \Li(x_2) - \frac{x_2}{\log x_2} - \Li(x_1) + \frac{x_1}{\log x_1} \right ). $$ -/)
  (proof := /-- Let $f(x)$ be as in the previous sublemma.  Notice that by assumption $x_1 \leq x \leq x_2 \leq x_1 \log x_1 < x_m$, so that
  $$ f(x) \leq f(x_2) = \frac{\log x_2}{x_2} \left( \Li(x_2) - \frac{x_2}{\log x_2} - \Li(x_1) + \frac{x_1}{\log x_1} \right). $$ -/)
  (latexEnv := "sublemma")
  (discussion := 717)]
theorem theorem_6_3 {x₁ : ℝ} (h : x₁ ≥ 14) (x₂ : ℝ) (hx₂ : x₂ ≥ x₁) (x : ℝ) (hx : x ≥ x₁) (hx' : x ≤ x₂) (hx₂' : x₂ ≤ x₁ * log x₁) :
  (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2 ≤
    (log x₂ / x₂) * (Li x₂ - x₂ / log x₂ - Li x₁ + x₁ / log x₁) := by
    have h_integral_le_integral : (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2 ≤ (log x / x) * (Li x - x / log x - Li x₁ + x₁ / log x₁) := by
      rw [ integral_one_div_log_sq ] <;> try linarith;
    have h_monotone : MonotoneOn (fun t => (log t / t) * (Li t - t / log t - Li x₁ + x₁ / log x₁)) (Set.Icc x₁ (x₁ * log x₁)) := by
      have h_monotone : MonotoneOn (fun t => (log t / t) * ∫ s in x₁..t, 1 / (log s) ^ 2) (Set.Icc x₁ (x₁ * log x₁)) := by
        apply_rules [ h_monotoneOn ];
    -- Using the fact that the integral of 1/(log t)^2 from x₁ to t is equal to Li t - t / log t - Li x₁ + x₁ / log x₁, we can rewrite the function.
      have h_integral_eq : ∀ t ∈ Set.Icc x₁ (x₁ * log x₁), ∫ s in x₁..t, 1 / (log s) ^ 2 = Li t - t / log t - Li x₁ + x₁ / log x₁ := by
        intros t ht; rw [ integral_one_div_log_sq ]
        · ring
        · linarith
        · linarith [ ht.1 ]
      exact fun t ht u hu htu => by simpa only [ h_integral_eq t ht, h_integral_eq u hu ] using h_monotone ht hu htu;
    exact h_integral_le_integral.trans ( h_monotone ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ hx' )

blueprint_comment /--
We can merge these sublemmas together after making some definitions. -/

@[blueprint
  "fks2-eq-11"
  (title := "FKS2 equation (11)")
  (statement := /--
  For $x_1 \leq x_2 \leq x_1 \log x_1$, we define
  $$ \mu_{num,1}(x_0,x_1,x_2) := \frac{x_0 \log(x_1)}{\epsilon_{\theta,num}(x_1) x_1 \log(x_0)}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| +
    \frac{\log(x_1)}{\epsilon_{\theta,num}(x_1) x_1}
    \sum_{i=0}^{N-1} \epsilon_{\theta,num}(e^{b_i})
    \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}} \right) +
    \frac{\log(x_2)}{x_2} \left( \Li(x_2) - \frac{x_2}{\log x_2} - \Li(x_1) + \frac{x_1}{\log x_1} \right).$$
   -/)]
noncomputable def μ_num_1 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * δ x₀ +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    (log x₂) / x₂ * (Li x₂ - x₂ / log x₂ - Li x₁ + x₁ / log x₁)

@[blueprint
  "fks2-eq-12"
  (title := "FKS2 equation (12)")
  (statement := /--
  For $x_2 \geq x_1 \log x_1$, we define
  $$ \mu_{num,2}(x_0,x_1) := \frac{x_0 \log(x_1)}{\epsilon_{\theta,num}(x_1) x_1 \log(x_0)}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| +
    \frac{\log(x_1)}{\epsilon_{\theta,num}(x_1) x_1}
    \sum_{i=0}^{N-1} \epsilon_{\theta,num}(e^{b_i})
    \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}} \right) +
    \frac{1}{\log x_1 + \log(\log x_1) - 1}.$$
   -/)]
noncomputable def μ_num_2 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * δ x₀ +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    1 / (log x₁ + log (log x₁) - 1)

@[blueprint
  "fks2-mu-def"
  (title := "Definition of mu")
  (statement := /-- We define $\mu_{num}(x_0, x_1, x_2)$ to equal $\mu_{num,1}(x_0,x_1,x_2)$ when $x_2 \leq x_1 \log x_1$ and $\mu_{num,2}(x_0,x_1)$ otherwise. -/)]
noncomputable def μ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) (x₂ : EReal) : ℝ :=
  if x₂ ≤ x₁ * log x₁ then
    μ_num_1 b εθ_num x₀ x₁ x₂.toReal
  else
    μ_num_2 b εθ_num x₀ x₁

@[blueprint
  "fks2-eq-13"
  (title := "FKS2 equation (13)")
  (statement := /--
  For $x_1 \leq x_2$, we define $\epsilon_{\pi,num}(x_0,x_1,x_2) := \epsilon_{\theta,num}(x_1)
    (1 + \mu_{num}(x_0,x_1,x_2))$.
   -/)]
noncomputable def επ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ)
    (x₂ : EReal) : ℝ :=
  εθ_num x₁ * (1 + μ_num b εθ_num x₀ x₁ x₂)

noncomputable def default_b (x₀ x₁ : ℝ) : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then log x₀ else log x₁

/- [NOTE]: The original FKS2 paper states the derivative condition
`deriv (fun x ↦ (log x) / x * (Li x - x / log x - Li x₁ + x₁ / log x₁)) x₂ ≥ 0`
as a hypothesis for this remark. However, Aristotle's proof shows it is not required. -/
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
    {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂) :
    μ_num_1 b εθ_num x₀ x₁ x₂ < μ_num_2 b εθ_num x₀ x₁ := by
  simp only [μ_num_2, μ_num_1, sup_le_iff, add_lt_add_iff_left] at *
  convert theorem_6_2 (by linarith : x₁ ≥ 14) x₂ (by linarith) using 1
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]; rotate_right
    · exact fun x ↦ Li x - x / log x
    · ring_nf
    · intro x hx
      convert! HasDerivAt.sub (hasDerivAt_Li _) (HasDerivAt.div (hasDerivAt_id x)
        (hasDerivAt_log _) _) using 1 <;>
        ring_nf <;> norm_num [show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith,
          show log x ≠ 0 by exact ne_of_gt <| log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith]
      · by_cases h : log x = 0 <;> simp [sq, h]
      · cases Set.mem_uIcc.mp hx <;> linarith
    · apply_rules [ContinuousOn.intervalIntegrable]
      exact continuousOn_of_forall_continuousAt fun t ht ↦ ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (continuousAt_log (by cases Set.mem_uIcc.mp ht <;> linarith)) _)
          (ne_of_gt (sq_pos_of_pos (log_pos (by cases Set.mem_uIcc.mp ht <;> linarith))))

private lemma exists_Eθ_pos {x₁ : ℝ} : ∃ x, x₁ ≤ x ∧ Eθ x > 0 := by
  set N := Nat.floor x₁ + 1
  set a := (N : ℝ)
  set b := (N : ℝ) + 1 / 2;
  have hθ_eq : theta a = theta b := by
    unfold theta;
    rw [ show ⌊a⌋₊ = N from ?_, show ⌊b⌋₊ = N from ?_ ];
    · rw [ Nat.floor_eq_iff ]
      · grind;
      · positivity;
    · exact Nat.floor_natCast _;
  by_cases ha : theta a = a;
  · refine ⟨ b, ?_, ?_ ⟩;
    · simp +zetaDelta at *;
      linarith [ Nat.lt_floor_add_one x₁ ];
    · refine div_pos ( abs_pos.mpr ?_ ) ( by positivity );
      grind +qlia;
  · refine ⟨ a, ?_, ?_ ⟩ <;> norm_num [ Eθ ];
    · exact le_of_lt ( Nat.lt_of_floor_lt ( Nat.lt_succ_self _ ) );
    · exact div_pos ( abs_pos.mpr ( sub_ne_zero.mpr ha ) ) ( Nat.cast_pos.mpr ( Nat.succ_pos _ ) )

blueprint_comment /--
This gives us the final result to obtain numerical bounds for $E_\pi$ from numerical bounds on $E_\theta$. -/

@[blueprint
  "fks2-theorem-6"
  (title := "FKS2 Theorem 6")
  (latexEnv := "theorem")
  (discussion := 718)]
theorem theorem_6 {x₀ x₁ : ℝ} (x₂ : EReal) (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : ∀ i : Fin (N+1), Eθ.numericalBound (exp (b i)) εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x.toEReal ≤ x₂) (hx₀ : x₀ ≥ 2) :
  Eπ x ≤ επ_num b εθ_num x₀ x₁ x₂ := by
  -- NOTE: the hypothesis `hx₀ : x₀ ≥ 2` is not present in the original source material
  have h_key : Eπ x ≤ εθ_num x₁ + (x₀ * log x₁) / (x₁ * log x₀) * δ x₀ + (log x₁ / x₁) * (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) * (Li (exp (b (i + 1))) - Li (exp (b i)) + exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) + εθ_num x₁ * ((log x / x) * ∫ t in x₁..x, 1 / (Real.log t) ^ 2) := by
    have h_key : Eπ x ≤ Eθ x + (log x / x) * (x₀ / log x₀) * δ x₀ + (log x / x) * (∫ t in x₀..x₁, Eθ t / log t ^ 2) + (log x / x) * (∫ t in x₁..x, Eθ t / log t ^ 2) := by
      have h_split : ∫ t in x₀..x, Eθ t / log t ^ 2 = (∫ t in x₀..x₁, Eθ t / log t ^ 2) + (∫ t in x₁..x, Eθ t / log t ^ 2) := by
        rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Eθ_integrable ] <;> linarith [ le_max_left x₀ 14, le_max_right x₀ 14 ];
      convert eq_30 ( show x ≥ x₀ by linarith [ le_max_left x₀ 14 ] ) ( show x₀ ≥ 2 by linarith ) using 1 ; rw [ h_split ] ; ring;
    have h_bound : Eθ x ≤ εθ_num x₁ := by
      have := h_εθ_num ( Fin.last N ) ; simp_all +decide [ Eθ.numericalBound ] ;
      simpa [ Real.exp_log ( by linarith : 0 < x₁ ) ] using this x ( by rw [ Real.exp_log ( by linarith ) ] ; linarith )
    have h_bound_integral : ∫ t in x₀..x₁, Eθ t / log t ^ 2 ≤ ∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) * (Li (exp (b (i + 1))) - Li (exp (b i)) + exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) := by
      apply_rules [ bound_x0_x1 ];
      linarith [ le_max_left x₀ 14, le_max_right x₀ 14 ]
    have h_bound_integral_last : ∫ t in x₁..x, Eθ t / log t ^ 2 ≤ εθ_num x₁ * ∫ t in x₁..x, 1 / log t ^ 2 := by
      apply_rules [ Eθ_bound_integral_last ];
      · linarith [ le_max_left x₀ 14, le_max_right x₀ 14 ];
      · convert h_εθ_num ( Fin.last N ) using 1 ; norm_num [ h_b_end, Real.exp_log ( show 0 < x₁ by linarith [ le_max_right x₀ 14 ] ) ];
    have h_log_div_self_antitone : Real.log x / x ≤ Real.log x₁ / x₁ := by
      apply Real.log_div_self_antitoneOn;
      · exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith [ le_max_right x₀ 14 ] );
      · exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith [ le_max_right x₀ 14 ] );
      · linarith;
    refine le_trans h_key ?_;
    refine add_le_add ( add_le_add ( add_le_add h_bound ?_ ) ?_ ) ?_;
    · convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right h_log_div_self_antitone ( show 0 ≤ x₀ / log x₀ by exact div_nonneg ( by linarith ) ( Real.log_nonneg ( by linarith ) ) ) ) ( show 0 ≤ δ x₀ by exact delta_nonneg x₀ ) using 1 ; ring;
    · gcongr;
      · refine intervalIntegral.integral_nonneg ?_ ?_ <;> norm_num;
        · linarith [ le_max_left x₀ 14, le_max_right x₀ 14 ];
        · exact fun u hu₁ hu₂ => div_nonneg ( Eθ_nonneg u ( by linarith ) ) ( sq_nonneg _ );
      · exact div_nonneg ( Real.log_nonneg ( by linarith [ le_max_right x₀ 14 ] ) ) ( by linarith [ le_max_right x₀ 14 ] );
    · convert mul_le_mul_of_nonneg_left h_bound_integral_last ( show 0 ≤ log x / x by exact div_nonneg ( Real.log_nonneg ( by linarith [ le_max_left x₀ 14, le_max_right x₀ 14 ] ) ) ( by linarith [ le_max_left x₀ 14, le_max_right x₀ 14 ] ) ) using 1 ; ring;
  by_cases hc : x₂ ≤ Real.toEReal ( x₁ * Real.log x₁ )
  · simp_all +decide only [ge_iff_le, sup_le_iff, Fin.Iio_last_eq_map, Finset.sum_map,
    Fin.coe_castSuccEmb, Fin.coeSucc_eq_succ, one_div, EReal.coe_mul, επ_num, μ_num, ↓reduceIte]
    have h63 := theorem_6_3 ( by linarith : 14 ≤ x₁ ) x₂.toReal ( by
      cases x₂ <;> norm_num at *;
      · linarith;
      · exact absurd hc ( by exact ne_of_lt ( EReal.coe_lt_top _ ) ) ) x hx₁ ( by
      cases x₂ <;> norm_num at *;
      · linarith;
      · exact absurd hc ( by exact ne_of_lt ( EReal.coe_lt_top _ ) ) ) ( by
      cases x₂ <;> norm_num at *;
      · exact_mod_cast hc;
      · exact mul_nonneg ( by linarith ) ( Real.log_nonneg ( by linarith ) ) );
    unfold μ_num_1; ring_nf at *;
    by_cases h : εθ_num x₁ = 0
    · simp_all +decide only [mul_comm, inv_pow, mul_assoc, mul_left_comm, zero_mul, mul_zero,
      add_zero, zero_add, Finset.sum_sub_distrib, inv_zero, Fin.Iio_last_eq_map, Finset.sum_map,
      Fin.coe_castSuccEmb, Fin.coeSucc_eq_succ, sub_self, ge_iff_le];
      have := exists_Eθ_pos ( x₁ := x₁ ) ; obtain ⟨ y, hy₁, hy₂ ⟩ := this; have := h_εθ_num ( Fin.last N ) ;
      simp_all +decide only [gt_iff_lt, Real.exp_log (by linarith : 0 < x₁), ge_iff_le] ;
      exact absurd ( this y hy₁ ) ( by norm_num [ h ] ; linarith );
    · simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]
      nlinarith [ show 0 < εθ_num x₁ from lt_of_le_of_ne ( by
                    have := h_εθ_num ( Fin.last N );
                    rw [ h_b_end, Real.exp_log ( by linarith ) ] at this; exact le_trans ( Eθ_nonneg _ ( by linarith ) ) ( this _ le_rfl ) ; ) ( Ne.symm h ) ];
  · simp_all +decide only [ge_iff_le, sup_le_iff, Fin.Iio_last_eq_map, Finset.sum_map,
    Fin.coe_castSuccEmb, Fin.coeSucc_eq_succ, one_div, EReal.coe_mul, not_le, επ_num, μ_num]
    have h62 := theorem_6_2 ( by linarith : 14 ≤ x₁ ) x hx₁
    simp_all +decide only [one_div, μ_num_2, Fin.Iio_last_eq_map, Finset.sum_map,
      Fin.coe_castSuccEmb, Fin.coeSucc_eq_succ, ge_iff_le];
    have hεθpos : 0 < εθ_num x₁ := by
      have := exists_Eθ_pos ( x₁ := x₁ ) ; obtain ⟨ y, hy₁, hy₂ ⟩ := this; have := h_εθ_num ( Fin.last N ) y; simp_all +decide [ Real.exp_log ( by linarith : 0 < x₁ ) ] ;
      linarith;
    split_ifs
    · simp_all +decide only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc,
      mul_add, mul_one, ge_iff_le];
      exact absurd ‹_› ( not_le_of_gt hc );
    · simp_all +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
      norm_num [ mul_left_comm ( εθ_num x₁ ), mul_assoc, hεθpos.ne' ];
      nlinarith [ show 0 ≤ εθ_num x₁ by positivity ]

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
  $$ + \frac{\log x_1}{\varepsilon_{\theta,num}(x_1) x_1} \sum_{i=1}^{N-1}
    \varepsilon_{\theta,num}(\exp(b_i))
    \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}\right)$$
  $$ + \frac{\log x_2}{x_2}
    \left( \Li(x_2) - \frac{x_2}{\log x_2} - \Li(x_1) + \frac{x_1}{\log x_1} \right)$$
  and for $x_2 > x_1 \log x_1$, including the case $x_2 = \infty$, we define
  $$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_1) x_1 \log x_0}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$
  $$ + \frac{\log x_1}{\varepsilon_{\theta,num}(x_1) x_1} \sum_{i=1}^{N-1}
    \varepsilon_{\theta,num}(\exp(b_i))
    \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}\right)$$
  $$ + \frac{1}{\log x_1 + \log\log x_1 - 1}.$$
  Then, for all $x_1 \leq x \leq x_2$ we have
  $$ E_\pi(x) \leq \varepsilon_{\pi,num}(x_1,x_2) :=
    \varepsilon_{\theta,num}(x_1)(1 + \mu_{num}(x_0,x_1,x_2)).$$ -/)
  (proof := /-- This follows by combining the three substeps. -/)
  (latexEnv := "theorem")
  (discussion := 718)]
theorem theorem_6_alt {x₀ x₁ : ℝ} (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : ∀ i : Fin (N+1), Eθ.numericalBound (exp (b i)) εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₀ : x₀ ≥ 2) :
  Eπ x ≤ εθ_num x₁ * (1 + μ_num_2 b εθ_num x₀ x₁) := by
  have h6 := theorem_6 (⊤ : EReal) h b hmono h_b_start h_b_end εθ_num h_εθ_num x hx₁ le_top hx₀
  suffices hsuff : μ_num b εθ_num x₀ x₁ (⊤ : EReal) = μ_num_2 b εθ_num x₀ x₁ by
    have heq : επ_num b εθ_num x₀ x₁ ⊤ = εθ_num x₁ * (1 + μ_num_2 b εθ_num x₀ x₁) := by
      dsimp [επ_num]; rw [hsuff]
    linarith
  dsimp [μ_num]; rfl

/-The following lemmas are used for `corollary_8`.
-/

/-
PROBLEM
Helper: In a monotone EReal sequence with first element finite and last element ⊤,
    for any real value v ≥ b'(0), we can find a bin index i < last such that
    b'(i) ≤ v and v < b'(i+1).

PROVIDED SOLUTION
By strong induction on M. When M = 0, Fin 0 is empty so we can't form a Fin M, but b'(0) = b'(Fin.last 0) = ⊤ and hv says v ≥ ⊤ which is impossible for real v — contradiction.

For M+1: If v < b'⟨1, _⟩, then i = ⟨0, _⟩ works since b'⟨0,_⟩ ≤ v (from hv) and v < b'⟨1,_⟩. Otherwise v ≥ b'⟨1,_⟩, and we can apply the result to the shifted sequence b'' = b' ∘ Fin.succ (which has M+1 elements, is monotone, ends at ⊤, and b''(0) = b'(1) ≤ v). This gives i' : Fin M with the bounds, and we take i = ⟨i'.val + 1, _⟩.
-/
lemma find_ereal_bin {M : ℕ} (b' : Fin (M + 1) → EReal)
    (h_end : b' (Fin.last M) = ⊤) (v : ℝ) (hv : (v : EReal) ≥ b' 0) :
    ∃ i : Fin M, b' ⟨i.val, by omega⟩ ≤ (v : EReal) ∧
      (v : EReal) < b' ⟨i.val + 1, by omega⟩ := by
  by_contra! h_contra;
  -- By induction on $i$, we can show that $b' i \leq v$ for all $i$.
  have h_ind : ∀ i : Fin (M + 1), b' i ≤ v := by
    intro i; induction i using Fin.inductionOn <;> aesop;
  exact absurd ( h_ind ( Fin.last M ) ) ( by simp +decide [ h_end ] )

/-
PROBLEM
Helper: Given a monotone EReal sequence b' and an index i such that b'(i) ≤ v (finite),
    the sub-partition (toReal of b' restricted to first i+1 elements) is monotone,
    provided all values b'(j) for j ≤ i are between b'(0) and v.

PROVIDED SOLUTION
For j₁ ≤ j₂ in Fin (i.val + 1), we have ⟨j₁.val, _⟩ ≤ ⟨j₂.val, _⟩ as Fin (M+1), so b'(j₁) ≤ b'(j₂) by monotonicity of b'. Both values are finite: they are ≥ b'(0) ≠ ⊥ (by monotonicity, since j₁ ≥ 0), and ≤ b'(i) ≤ v (finite) so ≠ ⊤. Since both are finite EReal values with b'(j₁) ≤ b'(j₂), we get toReal(b'(j₁)) ≤ toReal(b'(j₂)) by EReal.toReal_le_toReal (for finite values, toReal preserves order).
-/
lemma ereal_toReal_sub_mono {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (i : Fin M) (v : ℝ) (hv : b' ⟨i.val, by omega⟩ ≤ (v : EReal))
    (h_bot : b' 0 ≠ ⊥) :
    Monotone (fun j : Fin (i.val + 1) ↦ (b' ⟨j.val, by omega⟩).toReal) := by
  intro j k hjk
  generalize_proofs at *;
  apply EReal.toReal_le_toReal
  all_goals generalize_proofs at *;
  · exact hmono hjk;
  · exact ne_of_gt ( lt_of_lt_of_le ( lt_of_le_of_ne ( bot_le ) ( Ne.symm h_bot ) ) ( hmono ( Nat.zero_le _ ) ) );
  · have := hmono ( show ⟨ k, by linarith ⟩ ≤ ⟨ i, by linarith ⟩ from Nat.le_of_lt_succ <| by linarith [ Fin.is_lt k, Fin.is_lt i ] ) ; aesop;

/-
PROBLEM
Helper: EReal.toReal of a real cast is the original value

PROVIDED SOLUTION
Since h_b_start : b' 0 = ↑(log x₁), we have (b' 0).toReal = (↑(log x₁)).toReal = log x₁ by EReal.toReal_coe.
-/
lemma ereal_toReal_coe_log {x₁ : ℝ} {M : ℕ} (b' : Fin (M + 1) → EReal)
    (h_b_start : b' 0 = ↑(log x₁)) :
    (b' 0).toReal = log x₁ := by
  aesop

/-
PROBLEM
Helper: for a real v, if b'(i) ≤ v and b'(0) is a finite real cast, then
    exp(b'(i).toReal) ≤ exp v

PROVIDED SOLUTION
Since b'(0) ≠ ⊥ and b' is monotone, b'(i) ≥ b'(0) > ⊥, so b'(i) ≠ ⊥. Also b'(i) ≤ ↑v, so b'(i) ≠ ⊤ (since ↑v < ⊤). Therefore b'(i) is a finite EReal value with b'(i) ≤ ↑v, which means b'(i).toReal ≤ v by EReal.toReal_le_toReal (or similar). Then exp is monotone, so exp(b'(i).toReal) ≤ exp(v).
-/
lemma ereal_exp_toReal_le {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (i : Fin M) (v : ℝ) (hv : b' ⟨i.val, by omega⟩ ≤ (v : EReal))
    (h_bot : b' 0 ≠ ⊥) :
    exp (b' ⟨i.val, by omega⟩).toReal ≤ exp v := by
  by_cases hi : b' ⟨i, by omega⟩ = ⊥ <;> by_cases hi' : b' ⟨i, by omega⟩ = ⊤;
  · aesop;
  · have := hmono ( show 0 ≤ ⟨ i, by linarith [ Fin.is_lt i ] ⟩ from Nat.zero_le _ ) ; aesop;
  · aesop;
  · cases h : b' ⟨ i, by linarith [ Fin.is_lt i ] ⟩
    · aesop
    · aesop
    · contradiction

/-
PROBLEM
Helper: if b'(i) is finite (≠ ⊤) and b' is monotone with b'(0) = log x₁ where x₁ ≥ 14,
    then exp(b'(i).toReal) ≥ max x₁ 14

PROVIDED SOLUTION
Since b' is monotone and i.val ≥ 0, b'(i) ≥ b'(0) = ↑(log x₁). Since b'(i) ≠ ⊤ and b'(i) ≥ ↑(log x₁) (which is finite, so b'(i) ≠ ⊥ too), b'(i) is a finite EReal. Therefore b'(i).toReal ≥ (b'(0)).toReal = log x₁ (using EReal.toReal_le_toReal with the ≠ ⊤ and ≠ ⊥ conditions). Since exp is monotone, exp(b'(i).toReal) ≥ exp(log x₁) = x₁ (using Real.exp_log, noting x₁ > 0 since x₁ ≥ 14). Also x₁ ≥ 14, so max x₁ 14 = x₁. Therefore exp(b'(i).toReal) ≥ max x₁ 14.
-/
lemma ereal_exp_ge_max {x₁ : ℝ} (hx₁ : x₁ ≥ 14) {M : ℕ}
    (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (h_b_start : b' 0 = ↑(log x₁))
    (i : Fin M) (h_ne_top : b' ⟨i.val, by omega⟩ ≠ ⊤) :
    exp (b' ⟨i.val, by omega⟩).toReal ≥ max x₁ 14 := by
  -- Since $b'$ is monotone and $i.val \geq 0$, we have $b' ⟨i.val, by omega⟩ \geq b' 0 = ↑(log x₁)$.
  have h_ge_log_x₁ : b' ⟨i.val, by omega⟩ ≥ ↑(log x₁) := by
    exact h_b_start ▸ hmono ( Nat.zero_le _ );
  have h_toReal_ge_log_x₁ : (b' ⟨i.val, by omega⟩).toReal ≥ Real.log x₁ := by
    cases h : b' ⟨ i, by omega ⟩
    · aesop
    · aesop
    · contradiction
  exact le_trans ( by rw [ max_eq_left ( by linarith ) ] ; exact Real.le_exp_log x₁ |> le_trans <| Real.exp_le_exp.mpr h_toReal_ge_log_x₁ ) le_rfl;

/-
PROBLEM
Helper: for a given bin index i from find_ereal_bin, the bound from theorem_6 applies

PROVIDED SOLUTION
Apply theorem_6 with parameters:
- x₀ := x₁
- x₁ (theorem_6's) := exp(b'⟨i.val, _⟩.toReal)
- x₂ := if ⟨i.val+1, _⟩ = Fin.last M then ⊤ else ↑(exp(b'⟨i.val+1,_⟩.toReal))
- N := i.val
- b := fun j : Fin (i.val+1) ↦ (b' ⟨j.val, _⟩).toReal

Key facts for the hypotheses:
1. b'(i) ≠ ⊤: from h_finite, since i.val < M so ⟨i.val, _⟩ ≠ Fin.last M.
2. b' 0 ≠ ⊥: b' 0 = ↑(log x₁) which is a real cast, not ⊥.
3. exp(b'(i).toReal) ≥ max x₁ 14: use ereal_exp_ge_max with h_ne_top from (1).
4. Sub-partition is monotone: use ereal_toReal_sub_mono with v = log x (since b'(i) ≤ ↑(log x)) and h_bot (from (2)).
5. Sub-partition starts at log x₁: (b' ⟨0, _⟩).toReal = log x₁ by ereal_toReal_coe_log.
6. Sub-partition ends at b'(i).toReal = log(exp(b'(i).toReal)): by Real.log_exp.
7. h_εθ_num for sub-partition: for j, h_εθ_num ⟨j.val, _⟩.
8. exp(b'(i).toReal) ≤ x: use ereal_exp_toReal_le with v = log x, then exp(log x) = x by Real.exp_log (x > 0 since x ≥ 14).
9. x.toEReal ≤ x₂: split on if:
   - If ⟨i.val+1,_⟩ = Fin.last M: x₂ = ⊤, trivially x.toEReal ≤ ⊤.
   - Otherwise: b'(i+1) ≠ ⊤ (by h_finite, since ⟨i.val+1,_⟩ ≠ Fin.last M). Also b'(i+1) ≠ ⊥ (since b'(i+1) > ↑(log x) ≥ ↑(log 14) > ⊥). So b'(i+1) is finite and b'(i+1).toReal > log x (by EReal.toReal preserving strict inequality for finite values). Then exp(b'(i+1).toReal) > exp(log x) = x, so x ≤ exp(b'(i+1).toReal), giving x.toEReal ≤ ↑(exp(b'(i+1).toReal)).
-/
lemma corollary_8_apply_theorem_6 {x₁ : ℝ} (hx₁ : x₁ ≥ 14)
    {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (h_b_start : b' 0 = ↑(log x₁))
    (h_b_end : b' (Fin.last M) = ⊤)
    (h_finite : ∀ j : Fin (M+1), b' j = ⊤ → j = Fin.last M)
    (εθ_num : ℝ → ℝ)
    (h_εθ_num : ∀ i : Fin (M+1), Eθ.numericalBound (exp (b' i).toReal) εθ_num)
    (x : ℝ) (hx : x ≥ x₁)
    (i : Fin M)
    (hi_le : b' ⟨i.val, by omega⟩ ≤ ↑(log x))
    (hi_lt : ↑(log x) < b' ⟨i.val + 1, by omega⟩) :
    Eπ x ≤ επ_num (fun j : Fin (i.val+1) ↦ (b' ⟨j.val, by omega⟩).toReal)
        εθ_num x₁ (exp (b' ⟨i.val, by omega⟩).toReal)
        (if ⟨i.val + 1, by omega⟩ = Fin.last M then ⊤
         else ↑(exp (b' ⟨i.val + 1, by omega⟩).toReal)) := by
  split_ifs <;> simp_all +decide only [Fin.ext_iff];
  · convert theorem_6_alt _ _ _ _ _ _ _ _ _ (show (2 : ℝ) ≤ x₁ from by linarith) using 1;
    any_goals tauto
    all_goals generalize_proofs at *;
    · convert ereal_exp_ge_max hx₁ b' hmono h_b_start ⟨ i, by linarith ⟩ _ using 1 ; aesop;
    · intro j k hjk; exact (by
      apply_rules [ EReal.toReal_le_toReal ];
      · exact ne_of_gt ( lt_of_lt_of_le ( by aesop ) ( hmono ( show 0 ≤ _ from Nat.zero_le _ ) ) );
      · exact fun h => by have := h_finite _ h; exact absurd this ( by linarith [ Fin.is_lt k ] ) ;);
    · aesop;
    · aesop;
    · -- Apply the lemma that states if $b' i \leq \log x$, then $\exp(b' i).toReal \leq \exp(\log x)$.
      have h_exp_le : Real.exp (b' ⟨i.val, by omega⟩).toReal ≤ Real.exp (Real.log x) := by
        apply_rules [ ereal_exp_toReal_le ];
        aesop
      generalize_proofs at *; (
      rwa [ Real.exp_log ( by linarith ) ] at h_exp_le);
  · convert theorem_6 _ _ _ _ _ _ _ _ _ _ _ (show (2 : ℝ) ≤ x₁ from by linarith) using 1
    all_goals generalize_proofs at *;
    · convert ereal_exp_ge_max hx₁ _ _ _ _ using 1
      all_goals generalize_proofs at *;
      rotate_left
      · exact fun j => b' ⟨ j, by linarith [ Fin.is_lt j ] ⟩
      · generalize_proofs at *
        exact fun j k hjk => hmono <| by simpa using hjk
      · apply_rules [ ereal_toReal_coe_log ]
      · exact i
      norm_num [ EReal.toReal_coe ] at *
      exact Or.inl fun h => by have := h_finite _ h; aesop;
    · generalize_proofs at *
      convert ereal_toReal_sub_mono b' hmono i ( Real.log x ) hi_le _ using 1
      generalize_proofs at *
      aesop
    all_goals norm_num [ EReal.toReal_coe ] at *;
    · aesop;
    · exact fun j => h_εθ_num _;
    · have := @ereal_exp_toReal_le;
      exact le_trans ( this b' hmono i ( Real.log x ) hi_le ( by aesop ) ) ( by rw [ Real.exp_log ( by linarith ) ] ) |> le_trans <| by linarith;
    · have h_exp : Real.log x < (b' ⟨i.val + 1, by omega⟩).toReal := by
        have h_exp : b' ⟨i.val + 1, by omega⟩ ≠ ⊤ := by
          exact fun h => ‹¬ ( i : ℕ ) + 1 = M› <| by have := h_finite _ h; aesop;
        generalize_proofs at *; (
        cases h : b' ⟨ i + 1, by linarith ⟩ <;> aesop)
      generalize_proofs at *; (
      rw [ ← Real.log_le_iff_le_exp ( by linarith ) ] ; linarith [ Real.log_le_log ( by linarith ) hx ] ;);



@[blueprint
  "fks2-corollary-8"
  (title := "FKS2 Corollary 8")
  (statement := /--
  Let $\{b'_i\}_{i=1}^M$ be a set of finite subdivisions of $[\log(x_1),\infty)$, with
  $b'_1 = \log(x_1)$ and $b'_M = \infty$. Define
  $$ \varepsilon_{\pi, num}(x_1) :=
    \max_{1 \leq i \leq M-1}\varepsilon_{\pi, num}(\exp(b'_i),
    \exp(b'_{i+1})).$$
  Then $E_\pi(x) \leq \varepsilon_{\pi,num}(x_1)$ for all $x \geq x_1$.
  -/)
  (proof := /-- This follows directly from Theorem \ref{fks2-theorem-6} by taking the supremum over all partitions ending at infinity. -/)
  (latexEnv := "corollary")
  (discussion := 719)]
theorem corollary_8 {x₁ : ℝ} (hx₁ : x₁ ≥ 14)
    {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (h_b_start : b' 0 = log x₁)
    (h_b_end : b' (Fin.last M) = ⊤)
    (h_finite : ∀ j : Fin (M+1), b' j = ⊤ → j = Fin.last M)
    (εθ_num : ℝ → ℝ)
    (h_εθ_num : ∀ i : Fin (M+1), Eθ.numericalBound (exp (b' i).toReal) εθ_num) (x : ℝ) (hx : x ≥ x₁) :
    Eπ x ≤ iSup (fun i : Finset.Iio (Fin.last M) ↦
      επ_num (fun j : Fin (i.val.val+1) ↦ (b' ⟨ j.val, by grind ⟩).toReal)
        εθ_num x₁ (exp (b' i.val).toReal)
        (if (i+1) = Fin.last M then ⊤ else exp (b' (i+1)).toReal)) := by
    obtain ⟨i, hi⟩ : ∃ i : Fin M, b' ⟨i.val, by omega⟩ ≤ ↑(log x) ∧ ↑(log x) < b' ⟨i.val + 1, by omega⟩ := by
      apply find_ereal_bin b' h_b_end (log x) (by
      exact h_b_start.symm ▸ EReal.coe_le_coe_iff.mpr ( Real.log_le_log ( by linarith ) ( by linarith ) ));
    convert corollary_8_apply_theorem_6 hx₁ b' hmono h_b_start h_b_end h_finite εθ_num h_εθ_num x hx i hi.1 hi.2 |> le_trans <| ?_ using 1;
    refine le_csSup ?_ ?_;
    · exact Set.finite_range _ |> Set.Finite.bddAbove;
    · simp +zetaDelta only [ge_iff_le, Set.mem_range, Subtype.exists, Fin.Iio_last_eq_map, Finset.mem_map, Finset.mem_univ,
    Fin.coe_castSuccEmb, true_and] at *;
      refine ⟨ _, ⟨ ⟨ i, by linarith [ Fin.is_lt i ] ⟩, rfl ⟩, ?_ ⟩ ; aesop

blueprint_comment /--
\subsection{Putting everything together}

By merging together the above tools with various parameter choices, we can obtain some clean corollaries.
-/


@[blueprint
  "fks2-corollary-21"
  (title := "FKS2 Corollary 21")
  (statement := /--
  Let $B \geq \max(\frac{3}{2}, 1 + \frac{C^2}{16R})$ and $B > C^2/8R$.  Let $x_0, x_1 > 0$ with
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
    |E_\pi(x_0) - E_\theta(x_0)| + \frac{2 D_+\bigl(\sqrt{\log x_1} - \frac{C}{2\sqrt{R}}\bigr)}
    {\sqrt{\log x_1}}.$$
  -/)
  (proof := /-- This follows by applying Theorem \ref{fks2-theorem-3} with Proposition \ref{fks2-proposition-13}.  The hypothesis $B > C^2/8R$ is not present in original source.-/)
  (latexEnv := "corollary")
  (discussion := 720)]
theorem corollary_21
  (Aψ B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hB' : B > C ^ 2 / (8 * R))
  (hx0 : x₀ > 0)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)))
  (hEψ : Eψ.classicalBound Aψ B C R x₀)
  (hR : R > 0)
  (hAψ : Aψ > 0)
  (hx0_ge2 : x₀ ≥ 2)
  (hsqrt_cond : 0 ≤ √(log x₀) - C / (2 * √R))
  (hx₀_ge7 : 7 ≤ Real.log x₀) :
  let Aθ := Aψ * (1 + ν_asymp Aψ B C R x₀)
  Eπ.classicalBound (Aθ * (1 + (μ_asymp Aθ B C R x₀ x₁))) B C R x₁ :=
  -- NOTE: the hypothesis hB' is not present in the original source material [FKS2]. See
  -- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/issues/720 for more information
  -- NOTE: The hypotheses `hx0_ge2` and `hsqrt_cond` are also not present in [FKS2]. They are added
  -- to facilitate theorem_3, which also had them added due to lemma_12.
  let Aθ := Aψ * (1 + ν_asymp Aψ B C R x₀)
  have hlogpos: 0 < log x₀ := by exact log_pos (show 1 < x₀ by linarith [hx0_ge2])
  have hBKLNW1pos: BKLNW.a₁ (log x₀) > 0 := by
    simp only [BKLNW.a₁]
    unfold BKLNW.Inputs.a₁
    split_ifs
    · have : 0 < log BKLNW.Inputs.default.x₁ := by linarith [BKLNW.Inputs.default.hx₁]
      linarith [BKLNW.Inputs.default.epsilon_nonneg this.le]
    · have : 0 < log x₀ / 2 := by linarith
      linarith [BKLNW.Inputs.default.epsilon_nonneg this.le]
  have hBKLNW2pos : BKLNW.a₂ (log x₀) ≥ 0 := by
    simp only [BKLNW.a₂]
    unfold BKLNW.Inputs.a₂
    have hf_pos (x : ℝ) (hx : x ≥ 0) : BKLNW.f x ≥ 0 := by
      unfold BKLNW.f
      apply Finset.sum_nonneg
      intro n hn
      apply rpow_nonneg hx
    have hα_pos : 0 < BKLNW.Inputs.default.α := by
      apply mul_pos <;> norm_num
    have hterm1: 0 ≤ 1 + BKLNW.Inputs.default.α := by linarith
    have hterm2: 0 ≤ max (BKLNW.f (rexp (log x₀))) (BKLNW.f (2 ^ (⌊log x₀ / log 2⌋₊ + 1))) := by exact le_max_iff.mpr (Or.inl (hf_pos (exp (log x₀)) (exp_nonneg _)))
    nlinarith [hterm1, hterm2]
  have hpostemp: 1 / Aψ * (R / log x₀) ^ B * exp (C * √(log x₀ / R)) > 0 := by positivity [hAψ, log_pos (show 1 < x₀ by linarith [hx0_ge2])]
  have hν_asymp_pos: ν_asymp Aψ B C R x₀ > 0 := by unfold ν_asymp; apply (mul_pos_iff_of_pos_left hpostemp).2; positivity [hBKLNW1pos, hBKLNW2pos]
  have hAθ : Aθ > 0 := by nlinarith [hAψ, hν_asymp_pos]
  theorem_3 Aθ B C R x₀ x₁ hB hx0 (proposition_13 Aψ B C R x₀ hAψ hR hx0 hx₀_ge7 hEψ hB') hx1 hR hAθ hx0_ge2 hsqrt_cond

/-- Values for $\eps_{\pi, num}(x_1) are calculated using Corollary 8 with Theorem 6. Note that here $x_0=1015$ and that our sets $\{b_i\}_{i=1}^N$ and $\{b'_i\}_{i=1}^M$ are more refined than as provided by Tables 1, 2, and 3. -/
def Table_4 : List (ℝ × ℝ) := [
  (44, 1.7893e-8), (45, 1.1449e-8), (46, 7.2959e-9), (47, 4.6388e-9), (48, 2.9451e-9),
  (49, 1.8680e-9), (50, 1.1785e-9), (51, 7.4479e-10), (52, 4.7046e-10), (53, 2.9707e-10),
  (54, 1.8753e-10), (55, 1.1785e-10), (56, 7.4191e-11), (57, 4.6692e-11), (58, 2.9380e-11),
  (59, 1.8774e-11), (60, 1.2330e-11), (61, 8.4134e-12), (62, 6.0325e-12), (63, 4.5827e-12),
  (64, 3.6978e-12), (65, 3.1557e-12), (66, 2.8216e-12), (67, 2.6138e-12), (68, 2.4828e-12),
  (69, 2.3985e-12), (70, 2.3427e-12), (71, 2.3043e-12), (72, 2.2766e-12), (73, 2.2555e-12),
  (74, 2.2387e-12), (75, 2.2244e-12), (76, 2.2120e-12), (77, 2.2006e-12), (78, 2.1901e-12),
  (79, 2.1802e-12), (80, 2.1708e-12), (81, 2.1617e-12), (82, 2.1530e-12), (83, 2.1446e-12),
  (84, 2.1364e-12), (85, 2.1284e-12), (86, 2.1207e-12), (87, 2.1132e-12), (88, 2.1059e-12),
  (89, 2.0988e-12), (90, 2.0919e-12), (91, 2.0851e-12), (92, 2.0786e-12), (93, 2.0721e-12),
  (94, 2.0659e-12), (95, 2.0598e-12), (96, 2.0538e-12), (97, 2.0480e-12), (98, 2.0423e-12),
  (99, 2.0367e-12), (100, 2.0339e-12), (110, 1.9853e-12), (120, 1.9457e-12), (130, 1.9126e-12),
  (140, 1.8847e-12), (150, 1.8608e-12), (160, 1.8401e-12), (170, 1.8219e-12), (180, 1.8059e-12),
  (190, 1.7917e-12), (200, 1.7789e-12), (210, 1.7675e-12), (220, 1.7571e-12), (230, 1.7476e-12),
  (240, 1.7390e-12), (250, 1.7311e-12), (260, 1.7238e-12), (270, 1.7171e-12), (280, 1.7108e-12),
  (290, 1.7051e-12), (300, 1.6997e-12), (310, 1.6946e-12), (320, 1.6899e-12), (330, 1.6855e-12),
  (340, 1.6814e-12), (350, 1.6775e-12), (360, 1.6738e-12), (370, 1.6703e-12), (380, 1.6670e-12), (390, 1.6639e-12),
  (400, 1.6609e-12), (410, 1.6581e-12), (420, 1.6554e-12), (430, 1.6529e-12), (440, 1.6505e-12),
  (450, 1.6481e-12), (475, 1.6428e-12), (500, 1.6380e-12), (525, 1.6336e-12), (550, 1.6296e-12),
  (575, 1.6260e-12), (600, 1.6227e-12), (625, 1.6197e-12), (650, 1.6169e-12), (675, 1.6143e-12),
  (700, 1.6119e-12), (725, 1.6097e-12), (750, 1.6076e-12), (775, 1.6057e-12), (800, 1.6038e-12),
  (825, 1.6021e-12), (850, 1.6005e-12), (875, 1.5990e-12), (900, 1.5976e-12), (925, 1.5962e-12),
  (950, 1.5949e-12), (975, 1.5937e-12), (1000, 1.5925e-12), (1025, 1.5914e-12), (1050, 1.5904e-12),
  (1075, 1.5894e-12), (1100, 1.5885e-12), (1125, 1.5875e-12), (1150, 1.5867e-12), (1175, 1.5858e-12),
  (1200, 1.5850e-12), (1225, 1.5843e-12), (1250, 1.5836e-12), (1275, 1.5828e-12), (1300, 1.5822e-12),
  (1325, 1.5815e-12), (1350, 1.5809e-12), (1375, 1.5803e-12), (1400, 1.5797e-12), (1425, 1.5791e-12),
  (1450, 1.5786e-12), (1475, 1.5781e-12), (1500, 1.5776e-12), (1525, 1.5771e-12), (1550, 1.5766e-12),
  (1575, 1.5761e-12), (1600, 1.5757e-12), (1625, 1.5753e-12), (1650, 1.5749e-12), (1675, 1.5745e-12),
  (1700, 1.5741e-12), (1725, 1.5737e-12), (1750, 1.5733e-12), (1775, 1.5729e-12), (1800, 1.5726e-12),
  (1825, 1.5723e-12), (1850, 1.5719e-12), (1875, 1.5716e-12), (1900, 1.5713e-12), (1925, 1.5710e-12),
  (1950, 1.5707e-12), (1975, 1.5704e-12), (2000, 1.5701e-12), (2100, 1.3254e-12), (2200, 7.1013e-13),
  (2300, 3.8078e-13), (2400, 2.0436e-13), (2500, 1.0977e-13), (2600, 5.9004e-14), (2700, 3.1743e-14),
  (2800, 1.7095e-14), (2900, 9.2127e-15), (3000, 4.9698e-15), (3100, 2.6833e-15), (3200, 1.4502e-15),
  (3300, 7.8459e-16), (3400, 4.2495e-16), (3500, 2.3044e-16), (3600, 1.2511e-16), (3700, 6.8015e-17),
  (3800, 3.7027e-17), (3900, 2.0187e-17), (4000, 1.1024e-17), (4100, 6.0301e-18), (4200, 3.3046e-18),
  (4300, 1.8146e-18), (4400, 9.9846e-19), (4500, 5.5065e-19), (4600, 3.0441e-19), (4700, 1.6903e-19),
  (4800, 9.4404e-20), (4900, 5.3026e-20), (5000, 2.9949e-20), (6000, 1.2979e-22), (7000, 8.5175e-25),
  (8000, 7.7862e-27), (9000, 9.2230e-29), (10000, 1.3682e-30), (20000, 1.9349e-45), (30000, 6.6592e-57),
  (40000, 1.3470e-66), (50000, 3.7292e-75), (60000, 6.6648e-83), (70000, 4.9112e-90), (80000, 1.1133e-96),
  (90000, 6.3306e-103), (100000, 7.7825e-109), (200000, 1.2375e-156), (300000, 2.1902e-193), (400000, 2.1118e-224),
  (500000, 9.5685e-252), (600000, 1.7723e-276), (700000, 3.1360e-299), (800000, 2.0569e-320),
  (900000, 2.5885e-340), (1e6, 3.8635e-359), (1e7, 1.0364e-1153)
]

/-- Table 5.  Sample of values showing $\eps_{\pi, asymp}(x_1)$ interpolates an upper bound for $\eps_{\pi,num}(x_1)$ with $A_\pi = 121.107$, $B = 3.2$, and $C = 2$.  See Corollary 22.  Note that values $\eps_{\pi, num}(x_1,\infty)$ displayed are computed using (12) from Theorem 6 rather than Corollary 8. -/
def Table_5 : List (ℝ × ℝ × ℝ) := [
  (100, 1.9202, 2.0495e-12),
  (1000, 6.6533e-7, 1.5938e-12),
  (2000, 2.8341e-11, 1.5707e-12),
  (3000, 1.0385e-14, 4.9711e-15),
  (4000, 1.2145e-17, 1.1026e-17),
  (5000, 3.0305e-20, 2.9954e-20),
  (6000, 1.3052e-22, 1.2980e-22),
  (7000, 8.5363e-25, 8.5185e-25),
  (8000, 7.7910e-27, 7.7871e-27),
  (9000, 9.3522e-29, 9.2236e-29),
  (10000, 1.4137e-30, 1.3683e-30),
  (11000, 2.6036e-32, 2.4758e-32),
  (12000, 5.6934e-34, 5.3287e-34),
  (13000, 1.4481e-35, 1.3361e-35),
  (14000, 4.2127e-37, 3.8368e-37),
  (15000, 1.3824e-38, 1.2443e-38),
  (16000, 5.0581e-40, 4.5033e-40),
  (17000, 2.0432e-41, 1.8009e-41),
  (18000, 9.0354e-43, 7.8897e-43),
  (19000, 4.3424e-44, 3.7589e-44),
  (20000, 2.2536e-45, 1.9349e-45)
]

/-- Numerical evaluation of `μ_asymp` at the Corollary 22 parameters
(`B = 1.5`, `C = 0.8476`, `R = 1`, `x₀ = 2`, `x₁ = e^20000`):
`μ_asymp ≤ 5.01516e-5`, for any `A ≥ 1`. The Dawson term is evaluated with
`dawson_le_sharp` at `w = 0.117`; the `x₁`-denominator term is below `1e-11`.
This is the bound quoted in the Corollary 22 blueprint proof. -/
theorem mu_asymp_num_le {A : ℝ} (hA : 1 ≤ A) :
    μ_asymp A 1.5 0.8476 1 2 (exp 20000) ≤ 5.01516e-5 := by
  have hs_lo : (141.4213562 : ℝ) ≤ Real.sqrt 20000 := by interval_decide
  have hs_hi : Real.sqrt 20000 ≤ (141.4213563 : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (20000:ℝ) ≤ 141.4213563 ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 141.4213563)] at h
  have hexp32 : Real.exp (-(32:ℝ)) ≤ (1.3e-14 : ℝ) :=
    (le_of_lt (LogTables.exp_neg_32_lt.trans_le (by norm_num)))
  have hexpw : Real.exp ((0.117:ℝ) ^ 2) ≤ (1.0138790 : ℝ) := by
    rw [show ((0.117:ℝ)) ^ 2 = 13689 / 1000000 by norm_num]
    interval_decide
  have hlog2_lo : (0.6931471803 : ℝ) < Real.log 2 := LogTables.log_2_gt_d9
  have hlog2_hi : Real.log 2 < (0.6931471808 : ℝ) := LogTables.log_2_lt_d9
  unfold μ_asymp
  rw [Real.log_exp, Real.sqrt_one]
  -- ===== Term 1 =====
  have hT1 : (2 * 20000) / (admissible_bound A 1.5 0.8476 1 (exp 20000) * exp 20000 * Real.log 2)
      * δ 2 ≤ 1e-11 := by
    have hpc : Nat.primeCounting 2 = 1 := by decide
    have hpi2 : pi 2 = 1 := by
      unfold pi
      rw [show ⌊(2:ℝ)⌋₊ = 2 from by norm_num, hpc]
      norm_num
    have hLi2 : Li 2 = 0 := by
      unfold Li
      exact intervalIntegral.integral_same
    have hθ0 : (0:ℝ) ≤ θ 2 := Chebyshev.theta_nonneg 2
    have hθ3 : θ 2 ≤ 3 := by
      have h4 := theta_le_log4_mul_x (by norm_num : (0:ℝ) ≤ 2)
      have hlog4 : Real.log 4 ≤ 1.4 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        nlinarith [hlog2_hi]
      nlinarith [h4, hlog4]
    have hδ2 : δ 2 ≤ 2 := by
      unfold δ
      rw [hpi2, hLi2]
      have hlogne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      have hform : ((1:ℝ) - 0) / ((2:ℝ) / Real.log 2) = Real.log 2 / 2 := by
        field_simp
        norm_num
      rw [hform, abs_le]
      constructor
      · nlinarith [hθ0, hθ3, hlog2_lo, hlog2_hi]
      · nlinarith [hθ0, hθ3, hlog2_lo, hlog2_hi]
    have hδ0 : (0:ℝ) ≤ δ 2 := abs_nonneg _
    have hbig : (2:ℝ) ^ (60:ℕ) ≤
        admissible_bound A 1.5 0.8476 1 (exp 20000) * exp 20000 := by
      unfold admissible_bound
      rw [Real.log_exp, div_one, ← Real.sqrt_eq_rpow]
      have hP : (1:ℝ) ≤ (20000:ℝ) ^ (1.5:ℝ) :=
        Real.one_le_rpow (by norm_num) (by norm_num)
      have hAP : (1:ℝ) ≤ A * (20000:ℝ) ^ (1.5:ℝ) := by nlinarith [hA, hP]
      have hE : Real.exp (19880:ℝ) ≤
          Real.exp (-0.8476 * Real.sqrt 20000) * Real.exp 20000 := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hs_hi]
      have hEpos : (0:ℝ) < Real.exp (-0.8476 * Real.sqrt 20000) * Real.exp 20000 :=
        mul_pos (Real.exp_pos _) (Real.exp_pos _)
      have hK : (2:ℝ) ^ (60:ℕ) ≤ Real.exp (19880:ℝ) := by
        have h1 : Real.exp (19880:ℝ) = Real.exp 1 ^ (19880:ℕ) := by
          rw [← Real.exp_nat_mul]
          norm_num
        rw [h1]
        calc (2:ℝ) ^ (60:ℕ) ≤ (2:ℝ) ^ (19880:ℕ) :=
              pow_le_pow_right₀ (by norm_num) (by norm_num)
          _ ≤ Real.exp 1 ^ (19880:ℕ) := by
              apply pow_le_pow_left₀ (by norm_num)
              nlinarith [Real.exp_one_gt_d9]
      have hstep : Real.exp (-0.8476 * Real.sqrt 20000) * Real.exp 20000 ≤
          (A * (20000:ℝ) ^ (1.5:ℝ)) *
            (Real.exp (-0.8476 * Real.sqrt 20000) * Real.exp 20000) := by
        nlinarith [mul_nonneg (by linarith [hAP] : (0:ℝ) ≤ A * (20000:ℝ) ^ (1.5:ℝ) - 1)
          hEpos.le]
      calc (2:ℝ) ^ (60:ℕ) ≤ Real.exp (19880:ℝ) := hK
        _ ≤ Real.exp (-0.8476 * Real.sqrt 20000) * Real.exp 20000 := hE
        _ ≤ (A * (20000:ℝ) ^ (1.5:ℝ)) *
              (Real.exp (-0.8476 * Real.sqrt 20000) * Real.exp 20000) := hstep
        _ = A * (20000:ℝ) ^ (1.5:ℝ) * Real.exp (-0.8476 * Real.sqrt 20000) *
              Real.exp 20000 := by ring
    have hpow60 : ((2:ℝ) ^ (60:ℕ)) = 1152921504606846976 := by norm_num
    have hfrac : (2 * 20000) / (admissible_bound A 1.5 0.8476 1 (exp 20000) * exp 20000 *
        Real.log 2) ≤ 40000 / (1152921504606846976 * 0.6931471803) := by
      gcongr
      · norm_num
      · nlinarith [hbig, hlog2_lo, hpow60]
    calc (2 * 20000) / (admissible_bound A 1.5 0.8476 1 (exp 20000) * exp 20000 *
        Real.log 2) * δ 2
        ≤ 40000 / (1152921504606846976 * 0.6931471803) * 2 := by
          apply mul_le_mul hfrac hδ2 hδ0 (by positivity)
      _ ≤ 1e-11 := by norm_num
  -- ===== Term 2: the Dawson term =====
  have hzform : (0.8476:ℝ) / (2 * 1) = 0.4238 := by norm_num
  rw [hzform]
  set z := Real.sqrt 20000 - 0.4238 with hzdef
  have hz_lo : (140.9975562 : ℝ) ≤ z := by rw [hzdef]; linarith
  have hz_hi : z ≤ (140.9975563 : ℝ) := by rw [hzdef]; linarith
  have hz_pos : (0:ℝ) < z := by linarith
  have hD := dawson_le_sharp (z := z) (w := 0.117) (by norm_num) (by linarith) hz_pos
  have b1 : 1 / (2 * z) ≤ 1 / (2 * 140.9975562) := by
    gcongr
  have b2 : Real.exp ((0.117:ℝ) ^ 2) / (4 * z ^ 3) ≤
      1.0138790 / (4 * (140.9975562:ℝ) ^ 3) := by
    gcongr
  have b3 : (z - 0.117) * Real.exp (-(0.117 * (2 * z - 0.117))) ≤
      141 * (1.3e-14 : ℝ) := by
    have hexpo : Real.exp (-(0.117 * (2 * z - 0.117))) ≤ Real.exp (-(32:ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hz_lo]
    have hzw : z - 0.117 ≤ 141 := by linarith
    have hzw0 : (0:ℝ) ≤ z - 0.117 := by linarith
    calc (z - 0.117) * Real.exp (-(0.117 * (2 * z - 0.117)))
        ≤ 141 * Real.exp (-(32:ℝ)) := by
          apply mul_le_mul hzw hexpo (Real.exp_nonneg _) (by norm_num)
      _ ≤ 141 * 1.3e-14 := by nlinarith [hexp32]
  have hDb : dawson z ≤ 1 / (2 * 140.9975562) + 1.0138790 / (4 * (140.9975562:ℝ) ^ 3) +
      141 * 1.3e-14 := by linarith [hD, b1, b2, b3]
  have hD0 : (0:ℝ) ≤ dawson z := dawson_nonneg hz_pos.le
  have hT2 : 2 * dawson z / Real.sqrt 20000 ≤
      2 * (1 / (2 * 140.9975562) + 1.0138790 / (4 * (140.9975562:ℝ) ^ 3) + 141 * 1.3e-14) /
        141.4213562 := by
    gcongr
  linarith [hT1, hT2, show
    (2:ℝ) * (1 / (2 * 140.9975562) + 1.0138790 / (4 * (140.9975562:ℝ) ^ 3) + 141 * 1.3e-14) /
      141.4213562 + 1e-11 ≤ 5.01516e-5 from by norm_num]

/-- The substituted profile `A t³ e^{−Ct}` is antitone for `t ≥ 3/C`. -/
lemma cube_mul_exp_antitoneOn {A C : ℝ} (hA : 0 ≤ A) (hC : 0 < C) :
    AntitoneOn (fun t => A * t ^ 3 * Real.exp (-C * t)) (Set.Ici (3 / C)) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t => A * t ^ 3 * Real.exp (-C * t))
      (A * (3 * t ^ 2) * Real.exp (-C * t) +
        A * t ^ 3 * (Real.exp (-C * t) * (-C))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => A * t ^ 3) (A * (3 * t ^ 2)) t := by
      simpa using (hasDerivAt_pow 3 t).const_mul A
    have h2 : HasDerivAt (fun t : ℝ => -C * t) (-C) t := by
      simpa using (hasDerivAt_id t).const_mul (-C)
    have h3 : HasDerivAt (fun t : ℝ => Real.exp (-C * t))
        (Real.exp (-C * t) * (-C)) t := (Real.hasDerivAt_exp _).comp t h2
    exact h1.mul h3
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact (Continuous.continuousOn (by continuity))
  · intro t ht
    exact (hderiv t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [(hderiv t).deriv]
    have htC : 3 ≤ C * t := by
      rw [Set.mem_Ioi] at ht
      have := (div_lt_iff₀ hC).mp ht
      linarith
    have hexp : (0:ℝ) ≤ Real.exp (-C * t) := Real.exp_nonneg _
    have ht0 : (0:ℝ) ≤ t := by
      rw [Set.mem_Ioi] at ht
      have : (0:ℝ) < 3 / C := by positivity
      linarith
    nlinarith [sq_nonneg t, mul_nonneg (mul_nonneg hA (sq_nonneg t)) hexp,
      mul_nonneg (mul_nonneg (mul_nonneg hA ht0) (sq_nonneg t)) hexp]

/-- `admissible_bound A 1.5 C 1` is antitone beyond `log x ≥ (3/C)²`:
the workhorse for step-function interpolation against Tables 4/5. -/
lemma admissible_bound_anti {A C x y : ℝ} (hA : 0 ≤ A) (hC : 0 < C)
    (hx : (3 / C) ^ 2 ≤ Real.log x) (hxy : x ≤ y) (hx0 : 0 < x) :
    admissible_bound A 1.5 C 1 y ≤ admissible_bound A 1.5 C 1 x := by
  unfold admissible_bound
  rw [div_one, div_one]
  have hLx : (0:ℝ) ≤ Real.log x := le_trans (by positivity) hx
  have hLxy : Real.log x ≤ Real.log y :=
    Real.log_le_log hx0 hxy
  have hLy : (0:ℝ) ≤ Real.log y := le_trans hLx hLxy
  -- rewrite both sides through t = √(log ·)
  have key : ∀ L : ℝ, 0 ≤ L →
      A * L ^ (1.5:ℝ) * Real.exp (-C * L ^ ((1:ℝ)/(2:ℝ))) =
        A * (Real.sqrt L) ^ 3 * Real.exp (-C * Real.sqrt L) := by
    intro L hL
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (L ^ ((1:ℝ)/2)) 3,
      ← Real.rpow_mul hL]
    norm_num
  rw [key _ hLx, key _ hLy]
  have htx : 3 / C ≤ Real.sqrt (Real.log x) := by
    have h := Real.sqrt_le_sqrt hx
    rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ 3 / C)] at h
  have hty : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log y) :=
    Real.sqrt_le_sqrt hLxy
  exact cube_mul_exp_antitoneOn hA hC
    (Set.mem_Ici.mpr htx) (Set.mem_Ici.mpr (le_trans htx hty)) hty

/-- Step-interval bridge for the Table 4/5 interpolation. A constant bound
`V` on `Eπ` over a grid cell `[x₁, x₂]` (as produced by `theorem_6_alt` with
`V = εθ_num x₁ * (1 + μ_num_2 …)`), dominated by the admissible curve at the
right endpoint, yields the classical bound across the whole cell, by
`admissible_bound_anti`. The mid-range verification is this lemma
instantiated once per grid cell, with `hrow` a numeric endpoint check. -/
theorem step_interval_bound {A C V x₁ x₂ : ℝ} (hA : 0 ≤ A) (hC : 0 < C)
    (hlog : (3 / C) ^ 2 ≤ Real.log x₁) (hx₁ : 0 < x₁)
    (hV : ∀ x ∈ Set.Icc x₁ x₂, Eπ x ≤ V)
    (hrow : V ≤ admissible_bound A 1.5 C 1 x₂) :
    ∀ x ∈ Set.Icc x₁ x₂, Eπ x ≤ admissible_bound A 1.5 C 1 x := by
  intro x hx
  have hlogx : (3 / C) ^ 2 ≤ Real.log x :=
    le_trans hlog (Real.log_le_log hx₁ hx.1)
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le hx₁ hx.1
  calc Eπ x ≤ V := hV x hx
    _ ≤ admissible_bound A 1.5 C 1 x₂ := hrow
    _ ≤ admissible_bound A 1.5 C 1 x :=
        admissible_bound_anti hA hC hlogx hx.2 hx0

/-- Corollary 14, converted to the normalized Corollary 22 coordinates. -/
theorem corollary_14_normalized :
    Eθ.classicalBound 9.22023 (3 / 2) 0.8476 1 2 := by
  intro x hx
  have hθ := corollary_14 x hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlognn : 0 ≤ Real.log x := hlogpos.le
  have hsqrtpos : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hcoeff :
      121.0961 / ((5.5666305 : ℝ) ^ (3 / 2 : ℝ)) ≤ 9.22023 := by
    have hsqrt_lb : (2.35937 : ℝ) ≤ Real.sqrt 5.5666305 := by
      calc (2.35937 : ℝ) = Real.sqrt ((2.35937 : ℝ) ^ 2) :=
            (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.35937)).symm
        _ ≤ Real.sqrt 5.5666305 := by
            apply Real.sqrt_le_sqrt
            norm_num
    have hpow_base :
        ((5.5666305 : ℝ) ^ (3 / 2 : ℝ)) = 5.5666305 * Real.sqrt 5.5666305 := by
      rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num,
        Real.rpow_add (by norm_num : (0 : ℝ) < 5.5666305)]
      simp [Real.sqrt_eq_rpow]
    rw [hpow_base]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 5.5666305 * Real.sqrt 5.5666305)]
    calc (121.0961 : ℝ)
        ≤ 9.22023 * 5.5666305 * 2.35937 := by norm_num
      _ ≤ 9.22023 * (5.5666305 * Real.sqrt 5.5666305) := by
          nlinarith [hsqrt_lb]
  have hC : (0.8476 : ℝ) ≤ 2 / Real.sqrt 5.5666305 := by
    have hsqrt_ub : Real.sqrt 5.5666305 ≤ (2.3596 : ℝ) := by
      calc Real.sqrt 5.5666305 ≤ Real.sqrt ((2.3596 : ℝ) ^ 2) := by
            apply Real.sqrt_le_sqrt
            norm_num
        _ = (2.3596 : ℝ) := Real.sqrt_sq (by norm_num)
    calc (0.8476 : ℝ)
        ≤ 2 / (2.3596 : ℝ) := by
            rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2.3596)]
            norm_num
      _ ≤ 2 / Real.sqrt 5.5666305 := by
          gcongr
  have hpow :
      (Real.log x / 5.5666305) ^ (3 / 2 : ℝ) =
        (Real.log x) ^ (3 / 2 : ℝ) / 5.5666305 ^ (3 / 2 : ℝ) := by
    rw [Real.div_rpow hlognn (by norm_num : (0 : ℝ) ≤ 5.5666305)]
  have hsqrt :
      (Real.log x / 5.5666305) ^ ((1 : ℝ) / 2) =
        Real.sqrt (Real.log x) / Real.sqrt 5.5666305 := by
    rw [show ((1 : ℝ) / 2) = (1 / 2 : ℝ) by norm_num,
      Real.div_rpow hlognn (by norm_num : (0 : ℝ) ≤ 5.5666305)]
    simp [Real.sqrt_eq_rpow]
  unfold admissible_bound at hθ ⊢
  simp only [div_one]
  rw [hpow, hsqrt] at hθ
  have hpow_nonneg : 0 ≤ (Real.log x) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hlognn _
  have hExp :
      Real.exp (-(2 * (Real.sqrt (Real.log x) / Real.sqrt 5.5666305))) ≤
        Real.exp (-(0.8476 * (Real.log x) ^ ((1 : ℝ) / 2))) := by
    apply Real.exp_le_exp.mpr
    have hmul :
        0.8476 * Real.sqrt (Real.log x) ≤
          (2 / Real.sqrt 5.5666305) * Real.sqrt (Real.log x) :=
      mul_le_mul_of_nonneg_right hC hsqrtpos
    have hrewrite :
        (2 / Real.sqrt 5.5666305) * Real.sqrt (Real.log x) =
          2 * (Real.sqrt (Real.log x) / Real.sqrt 5.5666305) := by ring
    rw [← Real.sqrt_eq_rpow]
    nlinarith [hmul, hrewrite]
  have hmul :
      121.0961 * ((Real.log x) ^ (3 / 2 : ℝ) / 5.5666305 ^ (3 / 2 : ℝ)) *
          Real.exp (-(2 * (Real.sqrt (Real.log x) / Real.sqrt 5.5666305))) ≤
        9.22023 * (Real.log x) ^ (3 / 2 : ℝ) *
          Real.exp (-(0.8476 * (Real.log x) ^ ((1 : ℝ) / 2))) := by
    calc
      121.0961 * ((Real.log x) ^ (3 / 2 : ℝ) / 5.5666305 ^ (3 / 2 : ℝ)) *
          Real.exp (-(2 * (Real.sqrt (Real.log x) / Real.sqrt 5.5666305)))
          = (121.0961 / 5.5666305 ^ (3 / 2 : ℝ)) *
              (Real.log x) ^ (3 / 2 : ℝ) *
              Real.exp (-(2 * (Real.sqrt (Real.log x) / Real.sqrt 5.5666305))) := by ring
      _ ≤ 9.22023 * (Real.log x) ^ (3 / 2 : ℝ) *
          Real.exp (-(0.8476 * (Real.log x) ^ ((1 : ℝ) / 2))) := by
          gcongr
  have hθ' :
      Eθ x ≤ 121.0961 * ((Real.log x) ^ (3 / 2 : ℝ) / 5.5666305 ^ (3 / 2 : ℝ)) *
          Real.exp (-(2 * (Real.sqrt (Real.log x) / Real.sqrt 5.5666305))) := by
    convert! hθ using 1
    ring_nf
  convert! le_trans hθ' hmul using 1
  ring_nf

/-- Corollary 22 asymptotic tail: from `exp 20000` onward. -/
theorem corollary_22_tail :
    ∀ x ≥ exp 20000, Eπ x ≤ admissible_bound 9.2211 (3 / 2) 0.8476 1 x := by
  have htail :=
    theorem_3 9.22023 (3 / 2) 0.8476 1 2 (exp 20000)
      (by norm_num)
      (by norm_num)
      corollary_14_normalized
      (by
        rw [ge_iff_le, max_le_iff]
        constructor
        · exact le_trans Real.exp_one_gt_two.le
            (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 20000))
        · apply Real.exp_le_exp.mpr
          rw [Real.sqrt_one]
          norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by
        rw [Real.sqrt_one]
        have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hsq : (0.8325 : ℝ) ^ 2 ≤ Real.log 2 := by
          norm_num
          linarith
        have hsqrt : (0.8325 : ℝ) ≤ Real.sqrt (Real.log 2) := by
          calc (0.8325 : ℝ) = Real.sqrt ((0.8325 : ℝ) ^ 2) :=
                (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0.8325)).symm
            _ ≤ Real.sqrt (Real.log 2) := Real.sqrt_le_sqrt hsq
        linarith)
  intro x hx
  have hμ : μ_asymp 9.22023 1.5 0.8476 1 2 (exp 20000) ≤ 5.01516e-5 :=
    mu_asymp_num_le (by norm_num : (1 : ℝ) ≤ 9.22023)
  have hA :
      9.22023 * (1 + μ_asymp 9.22023 (3 / 2) 0.8476 1 2 (exp 20000)) ≤
        9.2211 := by
    have hμ' : μ_asymp 9.22023 (3 / 2) 0.8476 1 2 (exp 20000) ≤ 5.01516e-5 := by
      norm_num at hμ ⊢
      exact hμ
    nlinarith [hμ']
  have hmain := htail x hx
  unfold admissible_bound at hmain ⊢
  rw [div_one] at hmain ⊢
  have hlognn : 0 ≤ Real.log x := by
    have hx1 : (1 : ℝ) ≤ x := by
      exact le_trans (by norm_num : (1 : ℝ) ≤ exp 20000) hx
    exact Real.log_nonneg hx1
  have hpow_nonneg : 0 ≤ (Real.log x) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hlognn _
  have hexp_nonneg : 0 ≤ Real.exp (-(0.8476 * (Real.log x) ^ ((1 : ℝ) / 2))) :=
    Real.exp_nonneg _
  exact le_trans hmain (by gcongr)

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
  $A_\pi, B, C, \log x_0$ as in \cite[Table 6]{FKS2} give an admissible
  asymptotic bound for $E_\pi$ with $R = 5.5666305$.
  -/)
  (proof := /-- The bounds of the form $\eps_{\pi, asymp}(x)$ come from selecting a value $A$ for which Corollary \ref{fks-corollary-22} provides a better bound at $x = e^{7500}$ and from verifying that the bound in Corollary \ref{fks-corollary-22} decreases faster beyond this point. This final verification proceeds by looking at the derivative of the ratio as in Lemma \ref{fks-lemma-10}. To verify these still hold for smaller $x$, we proceed as below. To verify the results for any $x$ in $\log(10^{19}) < \log(x) < 100000$, one simply proceeds as in \cite[Lemmas 5.2, 5.3]{FKS} and interpolates the numerical results of Theorem \ref{fks2-theorem-6}. For instance, we use the values in Table 4 as a step function and verifies that it provides a tighter bound than we are claiming. Note that our verification uses a more refined collection of values than those provided in Table 4 or the tables posted online in https://arxiv.org/src/2206.12557v1/anc/PrimeCountingTables.pdf. To verify results for $x < 10^{19}$, one compares against the results from Theorem \ref{buthe-theorem-2a}, or one checks directly for particularly small $x$. -/)
  (latexEnv := "corollary")
  (discussion := 722)]
theorem corollary_23 (Aπ B C x₀ : ℝ) (h : [Aπ, B, C, x₀] ∈ table6) :
    Eπ.classicalBound Aπ B C 5.5666305 (Real.exp x₀) := sorry

noncomputable def table7 : List ((ℝ → ℝ) × Set ℝ) :=
  [ (fun x ↦ 2 * log x * x^(-(1:ℝ)/2), Set.Icc 1 57),
    (fun x ↦ (log x)^(3/2) * x^(-(1:ℝ)/2), Set.Icc 1 65.65),
    (fun x ↦ (1 / (8 * π)) * (log x)^2 * x^(-(1:ℝ)/2), Set.Icc 8 60.8),
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
  (proof := /-- Same as in Corollary \ref{fks-corollary-23}.-/)
  (latexEnv := "corollary")
  (discussion := 1429)]
theorem corollary_24 (B : ℝ → ℝ) (I : Set ℝ) (h : (B, I) ∈ table7) :
    ∀ x, log x ∈ I → Eπ x ≤ B x := sorry


/-The following three lemmas are used in the proof of corollary_26.
-/
lemma table6_mem : [0.826, 0.25, 1.00, 1.000] ∈ table6 := by
  simp [table6]

lemma sqrt_exp_le_half (v : ℝ) (hv : v ≥ 0) : Real.sqrt v * Real.exp (-v) ≤ 1/2 := by
  -- Let $u = \sqrt{v}$, then the inequality becomes $u e^{-u^2} \leq \frac{1}{2}$.
  set u : ℝ := Real.sqrt v
  have hu : u * Real.exp (-u^2) ≤ 1 / 2 := by
    -- We'll use the fact that $u e^{-u^2} \leq \frac{1}{2}$ for all $u \geq 0$. This follows from the fact that the maximum of $u e^{-u^2}$ occurs at $u = \frac{1}{\sqrt{2}}$.
    have h_max : ∀ u : ℝ, 0 ≤ u → u * Real.exp (-u ^ 2) ≤ 1 / 2 := by
      intro u hu; rw [ Real.exp_neg ] ; ring_nf; norm_num; (
      rw [ ← div_eq_mul_inv, div_le_iff₀ ( Real.exp_pos _ ) ] ; nlinarith [ sq_nonneg ( u - 1 ), Real.add_one_le_exp ( u ^ 2 ) ] ;);
    exact h_max u <| Real.sqrt_nonneg v;
  rwa [ Real.sq_sqrt hv ] at hu

lemma admissible_bound_le_0826 (x : ℝ) (hx : x ≥ 1) : admissible_bound 0.826 0.25 1.00 5.5666305 x ≤ 0.4298 := by
  unfold admissible_bound;
  -- Let $y = \sqrt{\log x / 5.5666305}$. Then the expression becomes $0.826 * y^{1/2} * \exp(-y)$.
  set y : ℝ := Real.sqrt (Real.log x / 5.5666305)
  have h_y : 0.826 * y^(1/2 : ℝ) * Real.exp (-y) ≤ 0.4298 := by
    -- Apply the lemma sqrt_exp_le_half with v = y.
    have h_sqrt_exp : y^(1/2 : ℝ) * Real.exp (-y) ≤ 1 / 2 := by
      convert sqrt_exp_le_half y ( Real.sqrt_nonneg _ ) using 1 ; norm_num [ ← Real.sqrt_eq_rpow ];
    linarith;
  convert h_y using 1 ; norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( div_nonneg ( Real.log_nonneg hx ) ( by norm_num : ( 0 :ℝ ) ≤ 5.5666305 ) ) ] ; ring_nf;
  rw [ show ( log x * ( 2000000 / 11133261 ) ) = ( Real.sqrt ( log x / 5.5666305 ) ) ^ 2 by rw [ Real.sq_sqrt <| by exact div_nonneg ( Real.log_nonneg hx ) <| by norm_num ] ; ring ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num;
  norm_num +zetaDelta at *
  left
  have hnonneg: 0 ≤ (Real.sqrt (Real.log x)) / (Real.sqrt 11133261 / Real.sqrt 2000000) := by positivity
  simpa [one_div] using (Real.pow_rpow_inv_natCast (x := √(Real.log x) / (√11133261 / √2000000)) (n := 2) hnonneg (by decide))

/-- On `[2, e)` the only prime `≤ x` is `2`, so `pi x = 1`. Used to patch the
`[2, exp 1)` gap left by Corollary 23 row 2 (whose threshold is now `exp 1`). -/
lemma pi_eq_one_lt_e {x : ℝ} (hx2 : 2 ≤ x) (hxe : x < Real.exp 1) : pi x = 1 := by
  have hfl : ⌊x⌋₊ = 2 := by
    have he3 : Real.exp 1 < 3 := by nlinarith [Real.exp_one_lt_d9]
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast hx2, by push_cast; linarith⟩
  unfold pi; rw [hfl]; norm_num [Nat.primeCounting, Nat.primeCounting']; decide

/-- `Li x ≥ 0` for `x ≥ 2` (integrand `1/log t > 0`). -/
lemma Li_nonneg_two {x : ℝ} (hx2 : 2 ≤ x) : (0:ℝ) ≤ Li x := by
  unfold Li
  apply intervalIntegral.integral_nonneg hx2
  intro t ht
  simp only [Set.mem_Icc] at ht
  have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
  positivity

/-- `Li x ≤ 2` on `[2, e)`: the integrand `1/log t ≤ 1/log 2`, integrated over a
length `< 1.04` interval. -/
lemma Li_le_two_lt_e {x : ℝ} (hx2 : 2 ≤ x) (hxe : x < Real.exp 1) : Li x ≤ 2 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hint : IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
    exact ContinuousAt.div continuousAt_const
      (Real.continuousAt_log (by linarith [ht.1])) (Real.log_pos (by linarith [ht.1])).ne'
  have hmono : Li x ≤ ∫ _t in (2:ℝ)..x, 1 / Real.log 2 := by
    unfold Li
    apply intervalIntegral.integral_mono_on hx2 hint intervalIntegrable_const
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact div_le_div_of_nonneg_left (by norm_num) hlog2 (Real.log_le_log (by norm_num) ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have he3 : Real.exp 1 < 3 := by nlinarith [Real.exp_one_lt_d9]
  have : (x - 2) * (1 / Real.log 2) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ hlog2]; nlinarith [Real.log_two_gt_d9, hxe, he3]
  linarith [hmono]

/-- The direct `Eπ` bound on `[2, e)`: `|pi x − Li x| ≤ 1` and `x/log x ≥ e`. -/
lemma Eπ_le_on_two_e {x : ℝ} (hx2 : 2 ≤ x) (hxe : x < Real.exp 1) : Eπ x ≤ 0.4298 := by
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
  have hpi  := pi_eq_one_lt_e hx2 hxe
  have hLi0 := Li_nonneg_two hx2
  have hLi2 := Li_le_two_lt_e hx2 hxe
  have habs : |pi x - Li x| ≤ 1 := by rw [hpi, abs_le]; constructor <;> linarith
  have hloge : Real.log x ≤ x / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < x / Real.exp 1 by positivity)
    rwa [Real.log_div (ne_of_gt hxpos) (ne_of_gt (Real.exp_pos 1)),
         Real.log_exp, sub_le_sub_iff_right] at h
  have he9 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hxlogx : (2.7182818283:ℝ) ≤ x / Real.log x := by
    rw [le_div_iff₀ hlogx]
    have hcleared : Real.log x * Real.exp 1 ≤ x := by
      rwa [le_div_iff₀ (Real.exp_pos 1)] at hloge
    nlinarith [hcleared, he9, hlogx]
  unfold Eπ
  rw [div_le_iff₀ (by positivity)]
  calc |pi x - Li x| ≤ 1 := habs
    _ ≤ 0.4298 * (x / Real.log x) := by nlinarith [hxlogx]



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
  (proof := /--
  The paper verifies this by combining explicit small-prime checks, Buthe's
  estimates up to $10^{19}$, and the numerical/asymptotic FKS2 bounds above
  $10^{19}$.  In this formal proof, after the Table 6 threshold convention in
  Corollary \ref{cor:alt1}, the row
  $[0.826, 0.25, 1.00, 1.000]$ only applies for $x \ge \exp(1)$.

  We therefore split at $e$.  For $2 \le x < e$, one has $\pi(x)=1$, and the
  integral definition gives $0 \le \Li(x) \le 2$; together with
  $\log x / x \le 1/e \le 0.4298$, this gives $E_\pi(x) \le 0.4298$.  For
  $x \ge e$, we apply Corollary \ref{cor:alt1} with the row
  $[0.826,0.25,1.00,1.000]$ and then compare the resulting admissible bound to
  $0.4298$.
  -/)
  (latexEnv := "corollary")
  (discussion := 723)]
theorem corollary_26 : Eπ.bound 0.4298 2 := by
  intro x hx
  by_cases hsmall : x < Real.exp 1
  · exact Eπ_le_on_two_e hx hsmall
  · have hxe : Real.exp (1.000 : ℝ) ≤ x := by
      rw [show (1.000 : ℝ) = 1 by norm_num]; exact not_lt.mp hsmall
    have h1 := corollary_23 0.826 0.25 1.00 1.000 table6_mem
    exact le_trans (h1 x hxe) (admissible_bound_le_0826 x (by linarith))

end FKS2
