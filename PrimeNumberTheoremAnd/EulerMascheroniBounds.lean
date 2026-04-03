import Mathlib

open Real Finset

/-!
# Upper and Lower bound for the Euler-Mascheroni constant γ, aka `Real.eulerMascheroniConstant`.

# Key theorems

- hγ_lo : 0.577215 ≤ γ
- hγ_hi : γ ≤ 0.577216

## Key definitions

The Euler-Maclaurin formula gives the asymptotic expansion
  `H_n = log(n) + γ + 1/(2n) - 1/(12n²) + 1/(120n⁴) - 1/(252n⁶) + ⋯`
as an exact equality, where the coefficients of the higher-order terms are `B_{2k}/(2k·n^{2k})` for
Bernoulli numbers `B_{2k}`. This naturally leads us to the following definitions:

- `γ₁(n) = H_n - log n - 1/(2n)`
- `γ₂(n) = H_n - log n - 1/(2n) + 1/(12n²)`
- `γ₃(n) = H_n - log n - 1/(2n) + 1/(12n²) - 1/(120n⁴)`

## Proof strategy

Because the expansion alternates, we have

`γ₃(n) < γ < γ₂(n)`

Instead of using the expansion, we prove that γ₃ is a strictly increasing sequence that converges to
γ, hence γ₃(n) < γ, and similarly that γ₂ is a strictly decreasing sequence that converges to γ,
hence γ < γ₂(n). Then, we evaluate both at `n = 16` to obtain the desired bounds.
-/

/-- The Euler-Mascheroni sequence with linear correction: `H_n - log(n) - 1/(2n)`. -/
noncomputable def γ₁ (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - 1 / (2 * n)

/-- The Euler-Mascheroni sequence with quadratic correction: `H_n - log n - 1/(2n) + 1/(12n²)`. -/
noncomputable def γ₂ (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - 1 / (2 * n) + 1 / (12 * n ^ 2)

/-- The Euler-Mascheroni sequence with quartic correction:
    `γ₃(n) = H_n - log n - 1/(2n) + 1/(12n²) - 1/(120n⁴)`. -/
noncomputable def γ₃ (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - 1 / (2 * n) + 1 / (12 * n ^ 2) - 1 / (120 * n ^ 4)

private lemma one_add_le_exp_quadratic_div {x : ℝ} (hx : 0 ≤ x) :
    1 + x ≤ Real.exp (x * (2 + x) / (2 * (1 + x))) := by
  grw [← (quadratic_le_exp_of_nonneg (by positivity))]
  nlinarith [mul_div_cancel₀ (x * (2 + x)) (by positivity : (2 * (1 + x)) ≠ 0)]

private lemma log_one_add_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) := by
  rw [le_div_iff₀ (by positivity)]
  have := Real.log_le_log (by positivity) (one_add_le_exp_quadratic_div hx)
  rwa [Real.log_exp, le_div_iff₀ (by positivity)] at this

/-- Each step of the Euler-Mascheroni sequence is bounded below. -/
lemma eulerMascheroniSeq_step_lb (k : ℕ) :
    1 / (2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
    eulerMascheroniSeq (k + 1) - eulerMascheroniSeq k := by
  unfold eulerMascheroniSeq
  have h_log_bound : ∀ x : ℝ, 0 ≤ x → Real.log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) :=
    fun x a => log_one_add_le_quadratic a
  have := h_log_bound (1 / (k + 1)) (by positivity)
  norm_num at *
  field_simp at *
  rw [Real.log_div (by positivity) (by positivity)] at this
  grind

/-- For `m ≥ n`, the difference of Euler-Mascheroni sequence values is bounded below
    by a telescoping sum. -/
lemma eulerMascheroniSeq_diff_lb (n m : ℕ) (h : n ≤ m) :
    (1 : ℝ) / (2 * (n + 1)) - 1 / (2 * (m + 1)) ≤
    eulerMascheroniSeq m - eulerMascheroniSeq n := by
  induction h with
  | refl => norm_num
  | @step k _ hk =>
    have h_step : eulerMascheroniSeq (k + 1) - eulerMascheroniSeq k ≥
        1 / (2 * (k + 1) * (k + 2) : ℝ) :=
      eulerMascheroniSeq_step_lb k
    norm_num [Nat.cast_add_one_ne_zero] at *
    nlinarith [inv_pos.mpr (by positivity : 0 < (k : ℝ) + 1),
      inv_pos.mpr (by positivity : 0 < (k : ℝ) + 2),
      mul_inv_cancel₀ (by positivity : (k : ℝ) + 1 ≠ 0),
      mul_inv_cancel₀ (by positivity : (k : ℝ) + 2 ≠ 0),
      mul_inv_cancel₀ (by positivity : (k : ℝ) + 1 + 1 ≠ 0)]

/-- `γ ≥ γ₁(n+1)` for all `n`. -/
lemma eulerMascheroniConstant_lb (n : ℕ) :
    γ₁ (n + 1) ≤ eulerMascheroniConstant := by
  have key : γ₁ (n + 1) = eulerMascheroniSeq n + 1 / (2 * ((n : ℝ) + 1)) := by
    simp only [γ₁, eulerMascheroniSeq]
    rw [harmonic_succ]
    push_cast
    field_simp
    ring
  rw [key]
  have h_lim : Filter.Tendsto (fun m => eulerMascheroniSeq m - eulerMascheroniSeq n) Filter.atTop (nhds (eulerMascheroniConstant - eulerMascheroniSeq n)) :=
    Filter.Tendsto.sub Real.tendsto_eulerMascheroniSeq tendsto_const_nhds
  have h_lim_bound : Filter.Tendsto (fun m => 1 / (2 * (n + 1) : ℝ) - 1 / (2 * (m + 1) : ℝ)) Filter.atTop (nhds (1 / (2 * (n + 1) : ℝ))) :=
    le_trans (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <|
      Filter.Tendsto.const_mul_atTop zero_lt_two <|
      Filter.tendsto_id.atTop_add tendsto_const_nhds) <| by norm_num
  have := h_lim_bound.comp tendsto_natCast_atTop_atTop
  exact le_of_tendsto_of_tendsto this h_lim (Filter.eventually_atTop.mpr
    ⟨n, by intros m hm; simpa using eulerMascheroniSeq_diff_lb n m hm⟩) |>
    fun h => by norm_num at *; grind

/-- If `f` is continuous on `[0, u]`, differentiable on `(0, u)`, `f 0 = 0`, and
    `deriv f` is positive for all positive inputs, then `f u > 0`.
    This is the common MVT argument used in `log_ineq_1`, `log_ineq_2`, and `log_ineq_3`. -/
lemma pos_of_mvt {f : ℝ → ℝ} {u : ℝ} (hu : 0 < u) (hf0 : f 0 = 0)
    (hcont : ContinuousOn f (Set.Icc 0 u))
    (hdiff : ∀ x ∈ Set.Ioo 0 u, DifferentiableAt ℝ f x)
    (hderiv : ∀ x > 0, 0 < deriv f x) : 0 < f u := by
  obtain ⟨c, hc⟩ := exists_deriv_eq_slope f hu hcont
    (fun x hx => (hdiff x hx).differentiableWithinAt)
  have := hderiv c hc.1.1; rw [hc.2, hf0, lt_div_iff₀] at this <;> nlinarith

/-- For u > 0: u²/2 - u + log(1+u) > 0. This is the base case of our chain of
    positivity lemmas, proved by the mean value theorem since the derivative
    u²/(1+u) is positive. -/
lemma log_ineq_1 (u : ℝ) (hu : 0 < u) : 0 < u ^ 2 / 2 - u + Real.log (1 + u) := by
  apply pos_of_mvt hu (by simp [Real.log_one])
  · fun_prop (disch := intro x hx; linarith [hx.1])
  · intro x hx; fun_prop (disch := linarith [hx.1])
  · intro u hu; norm_num [add_comm, show u + 1 ≠ 0 by linarith]; ring_nf
    nlinarith [inv_mul_cancel₀ (by linarith : (1 + u) ≠ 0)]

/-- For u > 0: u³/6 - u²/2 + (1+u)·log(1+u) - u > 0. The derivative of this
    function is u²/2 - u + log(1+u), which is positive by `log_ineq_1`. -/
private lemma log_ineq_2 (u : ℝ) (hu : 0 < u) :
    0 < u ^ 3 / 6 - u ^ 2 / 2 + (1 + u) * Real.log (1 + u) - u := by
  apply pos_of_mvt hu (by simp [Real.log_one])
  · fun_prop (disch := grind)
  · fun_prop (disch := grind)
  · intro u hu; norm_num [add_comm, show u + 1 ≠ 0 by linarith]; ring_nf
    nlinarith [log_ineq_1 u hu]

/-- For u > 0: 12(1+u)²·log(1+u) > 12u + 18u² + 4u³ - u⁴. The derivative of the
    difference is 24·[(1+u)·log(1+u) - u - u²/2 + u³/6], positive by `log_ineq_2`. -/
private lemma log_ineq_3 (u : ℝ) (hu : 0 < u) :
    12 * u + 18 * u ^ 2 + 4 * u ^ 3 - u ^ 4 <
    12 * (1 + u) ^ 2 * Real.log (1 + u) := by
  have hg_deriv_pos : ∀ u > 0,
      0 < 12 * ((1 + u) * Real.log (1 + u) - u - u ^ 2 / 2 + u ^ 3 / 6) :=
    fun u hu => mul_pos (by norm_num) (by linarith [log_ineq_2 u hu])
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 u, deriv (fun u => 12 * (1 + u) ^ 2 * Real.log (1 + u) -
      12 * u - 18 * u ^ 2 - 4 * u ^ 3 + u ^ 4) c =
      (12 * (1 + u) ^ 2 * Real.log (1 + u) - 12 * u - 18 * u ^ 2 - 4 * u ^ 3 + u ^ 4 -
      (12 * (1 + 0) ^ 2 * Real.log (1 + 0) - 12 * 0 - 18 * 0 ^ 2 - 4 * 0 ^ 3 + 0 ^ 4)) /
      (u - 0) := by
    apply_rules [exists_deriv_eq_slope] <;> fun_prop (disch := grind)
  norm_num [add_comm, mul_comm] at *
  norm_num [show c + 1 ≠ 0 by linarith] at hc
  rw [eq_div_iff] at hc <;>
    nlinarith [hg_deriv_pos c hc.1.1,
      mul_inv_cancel_left₀ (by linarith : (c + 1) ≠ 0) (12 * (c + 1))]

/-- `γ₂` is strictly decreasing for `n ≥ 1`. -/
lemma euler_maclaurin_decreasing (n : ℕ) (hn : 1 ≤ n) :
    γ₂ (n + 1) < γ₂ n := by
  unfold γ₂
  suffices h : Real.log ((n + 1 : ℝ) / n) - (2 * n + 1) / (2 * n * (n + 1)) +
      (2 * n + 1) / (12 * n ^ 2 * (n + 1) ^ 2) > 0 by
    rw [Real.log_div] at h <;> norm_num at * <;> try positivity
    field_simp at *; grind
  have h_log_ineq : 12 * (1 + 1 / (n : ℝ)) ^ 2 * Real.log (1 + 1 / (n : ℝ)) >
      12 / (n : ℝ) + 18 / (n : ℝ) ^ 2 + 4 / (n : ℝ) ^ 3 - 1 / (n : ℝ) ^ 4 := by
    have := log_ineq_3 (1 / (n : ℝ)) (by positivity); aesop
  field_simp at *; grind

/-- `γ₂` converges to `γ`. -/
lemma euler_maclaurin_tendsto :
    Filter.Tendsto γ₂ Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  unfold γ₂
  have h : Filter.Tendsto (fun n => (harmonic n : ℝ) - Real.log n - 1 / (2 * n))
      Filter.atTop (nhds eulerMascheroniConstant) := by
    simpa using Filter.Tendsto.sub Real.tendsto_harmonic_sub_log
      (tendsto_inv_atTop_nhds_zero_nat.mul tendsto_const_nhds) |>.congr'
      (by filter_upwards [Filter.eventually_ne_atTop 0] with n hn; aesop)
  simpa using h.add (tendsto_inv_atTop_nhds_zero_nat.pow 2 |>.mul_const _)

/-- `γ < γ₂ n` for all `n ≥ 1`. -/
private lemma euler_maclaurin_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant < γ₂ n := by
  have h_strict_anti : StrictAnti (fun n : ℕ => γ₂ (n + 1)) := by
    refine strictAnti_nat_of_succ_lt ?_
    intro n; have := euler_maclaurin_decreasing (n + 1) (by linarith); grind
  have h_tendsto : Filter.Tendsto (fun n : ℕ => γ₂ (n + 1))
      Filter.atTop (nhds eulerMascheroniConstant) := by
    exact euler_maclaurin_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
  have h_lt : ∀ n : ℕ, γ₂ (n + 1) > eulerMascheroniConstant := by
    intro n
    exact lt_of_le_of_lt
      (le_of_tendsto h_tendsto <| Filter.eventually_atTop.mpr
        ⟨n + 1, fun m hm => h_strict_anti.antitone hm⟩)
      (h_strict_anti <| Nat.lt_succ_self _)
  cases n <;> grind

/-- Computational verification: `γ₂ 16 ≤ 0.577216`, using `log 2 > 0.6931471803`. -/
private lemma euler_maclaurin_numerical : γ₂ 16 ≤ 0.577216 := by
  norm_num [γ₂]
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
  grind [Real.log_pow, Real.log_two_gt_d9]

lemma hγ_hi : Real.eulerMascheroniConstant ≤ 0.577216 :=
  le_of_lt (lt_of_lt_of_le (euler_maclaurin_bound 16 (by norm_num)) (by grind [euler_maclaurin_numerical]))

/-! ## γ₃: Lower bound from the next Euler-Maclaurin truncation

Define `γ₃(n) = H_n - log n - 1/(2n) + 1/(12n²) - 1/(120n⁴)`, the third truncation of the
Euler-Maclaurin expansion. Since the expansion alternates, `γ₃` is increasing and converges
to `γ` from below, giving `γ₃(n) ≤ γ` for all `n ≥ 1`.

The key inequality is that for `u > 0`:
  `120(1+u)⁴ log(1+u) < u⁸ + 4u⁷ - 4u⁶ + 24u⁵ + 250u⁴ + 520u³ + 420u² + 120u`

This is proved by defining `h(u) = RHS - 120(1+u)⁴ log(1+u)` and showing `h(u) > 0` via
a 5-level MVT chain. The base case uses the algebraic identity
  `h⁽⁵⁾(u) · (1+u) = 240 u² (28u² + 70u + 30)`
which is manifestly positive for `u > 0`.
-/

private lemma log_ineq_4 (u : ℝ) (hu : 0 < u) :
    0 < 6720 * u ^ 3 + 10080 * u ^ 2 - 2880 * u + 2880 - 2880 / (1 + u) := by
  have h1u : (0 : ℝ) < 1 + u := by linarith
  rw [sub_pos, div_lt_iff₀ h1u]
  nlinarith [sq_nonneg u, sq_nonneg (u * u)]

private lemma hasDerivAt_log_one_add (x : ℝ) (h : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => Real.log (1 + u)) (1 / (1 + x)) x := by
  have := (Real.hasDerivAt_log h.ne').comp x ((hasDerivAt_id x).const_add 1)
  convert this using 1; ring

private lemma hasDerivAt_one_add_mul_log (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => (1 + u) * Real.log (1 + u)) (Real.log (1 + x) + 1) x := by
  have hlog := hasDerivAt_log_one_add x h1p
  exact (((hasDerivAt_id x).const_add 1).mul hlog).congr_deriv (by simp [id]; field_simp)

private lemma hasDerivAt_one_add_sq_mul_log (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => (1 + u) ^ 2 * Real.log (1 + u))
      (2 * (1 + x) * Real.log (1 + x) + (1 + x)) x := by
  have hlog := hasDerivAt_log_one_add x h1p
  have h1u := (hasDerivAt_id x).const_add (1 : ℝ)
  exact ((h1u.pow 2).mul hlog).congr_deriv (by simp [id]; field_simp)

private lemma hasDerivAt_one_add_pow_three_mul_log (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => (1 + u) ^ 3 * Real.log (1 + u))
      (3 * (1 + x) ^ 2 * Real.log (1 + x) + (1 + x) ^ 2) x := by
  have hlog := hasDerivAt_log_one_add x h1p
  have h1u := (hasDerivAt_id x).const_add (1 : ℝ)
  exact ((h1u.pow 3).mul hlog).congr_deriv (by simp [id]; field_simp)

private lemma hasDerivAt_one_add_pow_four_mul_log (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => (1 + u) ^ 4 * Real.log (1 + u))
      (4 * (1 + x) ^ 3 * Real.log (1 + x) + (1 + x) ^ 3) x := by
  have hlog := hasDerivAt_log_one_add x h1p
  have h1u := (hasDerivAt_id x).const_add (1 : ℝ)
  exact ((h1u.pow 4).mul hlog).congr_deriv (by simp [id]; field_simp)

private lemma hasDerivAt_log_ineq_5 (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => 1680 * u ^ 4 + 3360 * u ^ 3 - 1440 * u ^ 2 + 2880 * u
        - 2880 * Real.log (1 + u))
        (6720 * x ^ 3 + 10080 * x ^ 2 - 2880 * x + 2880 - 2880 / (1 + x)) x := by
  have hlog := hasDerivAt_log_one_add x h1p
  have h1 := ((hasDerivAt_pow 4 x).const_mul 1680).add
    (((hasDerivAt_pow 3 x).const_mul 3360).add
    (((hasDerivAt_pow 2 x).const_mul (-1440)).add
    ((hasDerivAt_mul_const 2880).sub
    (hlog.const_mul 2880))))
  refine h1.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u; simp only [Pi.add_apply, Pi.sub_apply]; ring_nf
  · field_simp; ring

private lemma hasDerivAt_log_ineq_6 (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => 336 * u ^ 5 + 840 * u ^ 4 - 480 * u ^ 3 + 1440 * u ^ 2
        + 2880 * u - 2880 * (1 + u) * Real.log (1 + u))
        (1680 * x ^ 4 + 3360 * x ^ 3 - 1440 * x ^ 2 + 2880 * x
          - 2880 * Real.log (1 + x)) x := by
  have hprod := hasDerivAt_one_add_mul_log x h1p
  have h1 := ((hasDerivAt_pow 5 x).const_mul 336).add
    (((hasDerivAt_pow 4 x).const_mul 840).add
    (((hasDerivAt_pow 3 x).const_mul (-480)).add
    (((hasDerivAt_pow 2 x).const_mul 1440).add
    ((hasDerivAt_mul_const 2880).sub
    (hprod.const_mul 2880)))))
  refine h1.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u; simp only [Pi.add_apply, Pi.sub_apply]; ring_nf
  · ring

private lemma hasDerivAt_log_ineq_7 (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => 56 * u ^ 6 + 168 * u ^ 5 - 120 * u ^ 4 + 480 * u ^ 3
        + 2160 * u ^ 2 + 1440 * u - 1440 * (1 + u) ^ 2 * Real.log (1 + u))
        (336 * x ^ 5 + 840 * x ^ 4 - 480 * x ^ 3 + 1440 * x ^ 2 + 2880 * x
          - 2880 * (1 + x) * Real.log (1 + x)) x := by
  have hprod2 := hasDerivAt_one_add_sq_mul_log x h1p
  have h1 := ((hasDerivAt_pow 6 x).const_mul 56).add
    (((hasDerivAt_pow 5 x).const_mul 168).add
    (((hasDerivAt_pow 4 x).const_mul (-120)).add
    (((hasDerivAt_pow 3 x).const_mul 480).add
    (((hasDerivAt_pow 2 x).const_mul 2160).add
    ((hasDerivAt_mul_const 1440).sub
    (hprod2.const_mul 1440))))))
  refine h1.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u; simp only [Pi.add_apply, Pi.sub_apply]; ring_nf
  · ring

private lemma hasDerivAt_log_ineq_8 (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => 8 * u ^ 7 + 28 * u ^ 6 - 24 * u ^ 5 + 120 * u ^ 4
        + 880 * u ^ 3 + 1200 * u ^ 2 + 480 * u - 480 * (1 + u) ^ 3 * Real.log (1 + u))
        (56 * x ^ 6 + 168 * x ^ 5 - 120 * x ^ 4 + 480 * x ^ 3 + 2160 * x ^ 2 + 1440 * x
          - 1440 * (1 + x) ^ 2 * Real.log (1 + x)) x := by
  have hprod3 := hasDerivAt_one_add_pow_three_mul_log x h1p
  have h1 := ((hasDerivAt_pow 7 x).const_mul 8).add
    (((hasDerivAt_pow 6 x).const_mul 28).add
    (((hasDerivAt_pow 5 x).const_mul (-24)).add
    (((hasDerivAt_pow 4 x).const_mul 120).add
    (((hasDerivAt_pow 3 x).const_mul 880).add
    (((hasDerivAt_pow 2 x).const_mul 1200).add
    ((hasDerivAt_mul_const 480).sub
    (hprod3.const_mul 480)))))))
  refine h1.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u; simp only [Pi.add_apply, Pi.sub_apply]; ring_nf
  · ring

private lemma hasDerivAt_log_ineq_9 (x : ℝ) (h1p : (0 : ℝ) < 1 + x) :
    HasDerivAt (fun u => u ^ 8 + 4 * u ^ 7 - 4 * u ^ 6 + 24 * u ^ 5
        + 250 * u ^ 4 + 520 * u ^ 3 + 420 * u ^ 2 + 120 * u
        - 120 * (1 + u) ^ 4 * Real.log (1 + u))
        (8 * x ^ 7 + 28 * x ^ 6 - 24 * x ^ 5 + 120 * x ^ 4 + 880 * x ^ 3 + 1200 * x ^ 2
          + 480 * x - 480 * (1 + x) ^ 3 * Real.log (1 + x)) x := by
  have hprod4 := hasDerivAt_one_add_pow_four_mul_log x h1p
  have h1 := ((hasDerivAt_pow 8 x).add
    (((hasDerivAt_pow 7 x).const_mul 4).add
    (((hasDerivAt_pow 6 x).const_mul (-4)).add
    (((hasDerivAt_pow 5 x).const_mul 24).add
    (((hasDerivAt_pow 4 x).const_mul 250).add
    (((hasDerivAt_pow 3 x).const_mul 520).add
    (((hasDerivAt_pow 2 x).const_mul 420).add
    ((hasDerivAt_mul_const 120).sub
    (hprod4.const_mul 120)))))))))
  refine h1.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u; simp only [Pi.add_apply, Pi.sub_apply]; ring_nf
  · ring

private lemma log_ineq_5 (u : ℝ) (hu : 0 < u) :
    0 < 1680 * u ^ 4 + 3360 * u ^ 3 - 1440 * u ^ 2 + 2880 * u
      - 2880 * Real.log (1 + u) := by
  apply pos_of_mvt hu (by simp [Real.log_one])
  · fun_prop (disch := intro x hx; linarith [hx.1])
  · intro x hx; fun_prop (disch := linarith [hx.1])
  · intro x hx
    have h1p : (0 : ℝ) < 1 + x := by linarith [hx]
    have hd := hasDerivAt_log_ineq_5 x h1p
    rw [hd.deriv]; exact log_ineq_4 x hx

private lemma log_ineq_6 (u : ℝ) (hu : 0 < u) :
    0 < 336 * u ^ 5 + 840 * u ^ 4 - 480 * u ^ 3 + 1440 * u ^ 2 + 2880 * u
      - 2880 * (1 + u) * Real.log (1 + u) := by
  apply pos_of_mvt hu (by simp [Real.log_one])
  · fun_prop (disch := intro x hx; linarith [hx.1])
  · intro x hx; fun_prop (disch := linarith [hx.1])
  · intro x hx
    have h1p : (0 : ℝ) < 1 + x := by linarith [hx]
    have hd := hasDerivAt_log_ineq_6 x h1p
    rw [hd.deriv]; exact log_ineq_5 x hx

private lemma log_ineq_7 (u : ℝ) (hu : 0 < u) :
    0 < 56 * u ^ 6 + 168 * u ^ 5 - 120 * u ^ 4 + 480 * u ^ 3 + 2160 * u ^ 2 + 1440 * u
      - 1440 * (1 + u) ^ 2 * Real.log (1 + u) := by
  apply pos_of_mvt hu (by simp [Real.log_one])
  · fun_prop (disch := intro x hx; linarith [hx.1])
  · intro x hx; fun_prop (disch := linarith [hx.1])
  · intro x hx
    have h1p : (0 : ℝ) < 1 + x := by linarith [hx]
    have hd := hasDerivAt_log_ineq_7 x h1p
    rw [hd.deriv]; exact log_ineq_6 x hx

private lemma log_ineq_8 (u : ℝ) (hu : 0 < u) :
    0 < 8 * u ^ 7 + 28 * u ^ 6 - 24 * u ^ 5 + 120 * u ^ 4 + 880 * u ^ 3 + 1200 * u ^ 2
      + 480 * u - 480 * (1 + u) ^ 3 * Real.log (1 + u) := by
  apply pos_of_mvt hu (by simp [Real.log_one])
  · fun_prop (disch := grind)
  · fun_prop (disch := grind)
  · intro x hx
    have h1p : (0 : ℝ) < 1 + x := by linarith [hx]
    have hd := hasDerivAt_log_ineq_8 x h1p
    rw [hd.deriv]; exact log_ineq_7 x hx

private lemma log_ineq_9 (u : ℝ) (hu : 0 < u) :
    120 * (1 + u) ^ 4 * Real.log (1 + u) <
    u ^ 8 + 4 * u ^ 7 - 4 * u ^ 6 + 24 * u ^ 5 + 250 * u ^ 4 + 520 * u ^ 3
    + 420 * u ^ 2 + 120 * u := by
  suffices h : 0 < u ^ 8 + 4 * u ^ 7 - 4 * u ^ 6 + 24 * u ^ 5 + 250 * u ^ 4 + 520 * u ^ 3
      + 420 * u ^ 2 + 120 * u - 120 * (1 + u) ^ 4 * Real.log (1 + u) by linarith
  apply pos_of_mvt hu (by simp [Real.log_one])
  · fun_prop (disch := intro x hx; linarith [hx.1])
  · intro x hx; fun_prop (disch := linarith [hx.1])
  · intro x hx
    have h1p : (0 : ℝ) < 1 + x := by linarith [hx]
    have hd := hasDerivAt_log_ineq_9 x h1p
    rw [hd.deriv]; exact log_ineq_8 x hx

/-- `γ₃` is strictly increasing for `n ≥ 1`. -/
lemma γ₃_increasing (n : ℕ) (hn : 1 ≤ n) :
    γ₃ n < γ₃ (n + 1) := by
  unfold γ₃
  suffices h : 0 < (2 * ↑n + 1) / (2 * ↑n * (↑n + 1))
      - Real.log ((↑n + 1 : ℝ) / ↑n)
      - (2 * ↑n + 1) / (12 * ↑n ^ 2 * (↑n + 1) ^ 2)
      + (4 * ↑n ^ 3 + 6 * ↑n ^ 2 + 4 * ↑n + 1) /
        (120 * ↑n ^ 4 * (↑n + 1) ^ 4) by
    rw [Real.log_div] at h <;> norm_num at * <;> try positivity
    field_simp at *; grind
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h_log_ineq := log_ineq_9 (1 / (n : ℝ)) (by positivity)
  rw [show (1 : ℝ) + 1 / (↑n : ℝ) = (↑n + 1) / ↑n by field_simp] at h_log_ineq
  rw [Real.log_div (by positivity) (ne_of_gt hn_pos)] at h_log_ineq
  rw [Real.log_div (by positivity) (ne_of_gt hn_pos)]
  field_simp at *
  nlinarith [sq_nonneg ((n : ℝ)), sq_nonneg ((n : ℝ) - 1),
    pow_pos hn_pos 2, pow_pos hn_pos 3, pow_pos hn_pos 4,
    pow_pos hn_pos 5, pow_pos hn_pos 6, pow_pos hn_pos 7, pow_pos hn_pos 8,
    pow_pos (show (0 : ℝ) < n + 1 by linarith) 2,
    pow_pos (show (0 : ℝ) < n + 1 by linarith) 3,
    pow_pos (show (0 : ℝ) < n + 1 by linarith) 4]

/-- `γ₃` converges to `γ`. -/
private lemma γ₃_tendsto :
    Filter.Tendsto γ₃ Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have h_eq : ∀ n : ℕ, n ≠ 0 → γ₃ n = γ₂ n - 1 / (120 * (↑n : ℝ) ^ 4) := by
    intro n _; unfold γ₃ γ₂; ring
  have h_corr : Filter.Tendsto (fun n : ℕ => 1 / (120 * (↑n : ℝ) ^ 4))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat.pow 4).mul_const (1 / (120 : ℝ))
  have h_sub := euler_maclaurin_tendsto.sub h_corr
  rw [sub_zero] at h_sub
  exact h_sub.congr' (by
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    exact (h_eq n hn).symm)

/-- `γ₃ n < γ` for all `n ≥ 1`. -/
lemma γ₃_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    γ₃ n < Real.eulerMascheroniConstant := by
  have h_strict_mono : StrictMono (fun n : ℕ => γ₃ (n + 1)) :=
    strictMono_nat_of_lt_succ (fun k => γ₃_increasing (k + 1) (by omega))
  have h_tendsto : Filter.Tendsto (fun n : ℕ => γ₃ (n + 1))
      Filter.atTop (nhds eulerMascheroniConstant) :=
    γ₃_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
  have h_lt : ∀ k : ℕ, γ₃ (k + 1) < eulerMascheroniConstant := fun k =>
    lt_of_lt_of_le
      (h_strict_mono <| Nat.lt_succ_self _)
      (ge_of_tendsto h_tendsto <| Filter.eventually_atTop.mpr
        ⟨k + 1, fun m hm => h_strict_mono.monotone hm⟩)
  cases n with
  | zero => omega
  | succ m => exact h_lt m

lemma hγ_lo : (0.577215 : ℝ) ≤ Real.eulerMascheroniConstant := by
  suffices h : (577215 : ℝ) / 1000000 ≤ γ₃ 16 by
    calc (0.577215 : ℝ) = 577215 / 1000000 := by norm_num
      _ ≤ γ₃ 16 := h
      _ ≤ eulerMascheroniConstant := le_of_lt (γ₃_lower_bound 16 (by norm_num))
  -- γ₃ 16 = H(16) - log 16 - 1/32 + 1/3072 - 1/7864320
  -- We bound log 16 = 4 * log 2 < 4 * 0.6931471808
  norm_num [γ₃]
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
  grind [Real.log_pow, Real.log_two_lt_d9]
