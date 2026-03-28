import Mathlib

set_option linter.style.induction false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option linter.flexible false

open Real Finset

/-!
# Upper and Lower bound for the Euler-Mascheroni constant

# Key theorems

- hγ_lo : (0.577215 : ℝ) ≤ eulerMascheroniConstant
- hγ_hi : eulerMascheroniConstant ≤ 0.577216

## Strategy (lower bound)
1. Prove `log(1+x) ≤ x(2+x)/(2(1+x))` for `x ≥ 0` using the quadratic exponential bound.
2. Derive that each step of the Euler-Mascheroni sequence satisfies
   `eulerMascheroniSeq(k+1) - eulerMascheroniSeq(k) ≥ 1/(2(k+1)(k+2))`.
3. Sum these bounds telescopically to get
   `γ ≥ eulerMascheroniSeq(n) + 1/(2(n+1))`.
4. Verify computationally (via `native_decide`) that
   `eulerMascheroniSeq(400) + 1/802 ≥ 0.577215`.

## Strategy (upper bound)
We prove `Real.eulerMascheroniConstant ≤ 0.577216` using an Euler-Maclaurin style bound.
The standard Mathlib bound `γ < H_n - log n` converges too slowly (needs n > 10⁶).
Instead, we prove the tighter bound `γ < H_n - log n - 1/(2n) + 1/(12n²)` by showing
this "corrected" sequence is strictly decreasing and converges to γ.
The key analytical ingredient is the chain of inequalities:
1. `u²/2 - u + log(1+u) > 0` for `u > 0`
2. `u³/6 - u²/2 + (1+u)·log(1+u) - u > 0` for `u > 0`
3. `12(1+u)²·log(1+u) > 12u + 18u² + 4u³ - u⁴` for `u > 0`
Each follows from the previous by the mean value theorem (the derivative of each
function equals the previous one, and all vanish at 0).
Applying the bound at `n = 16` and using `log 2 > 0.6931471803` gives the result.

-/
/-- The quadratic upper bound for log: `log(1+x) ≤ x*(2+x)/(2*(1+x))` for `x ≥ 0`. -/
lemma log_one_add_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) := by
  rw [ le_div_iff₀ ( by linarith ) ];
  have h_exp : Real.exp (x * (2 + x) / (2 * (1 + x))) ≥ 1 + x := by
    have h_exp_bound : ∀ y : ℝ, 0 ≤ y → Real.exp y ≥ 1 + y + y^2 / 2 :=
      fun y a => quadratic_le_exp_of_nonneg a
    exact le_trans ( by nlinarith [ mul_div_cancel₀ ( x * ( 2 + x ) ) ( by linarith : ( 2 * ( 1 + x ) ) ≠ 0 ) ] ) ( h_exp_bound _ ( by positivity ) );
  have := Real.log_le_log ( by positivity ) h_exp;
  rw [ Real.log_exp ] at this ; rw [ le_div_iff₀ ] at this <;> linarith
/-- Each step of the Euler-Mascheroni sequence is bounded below. -/
lemma eulerMascheroniSeq_step_lb (k : ℕ) :
    1 / (2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
    eulerMascheroniSeq (k + 1) - eulerMascheroniSeq k := by
  unfold eulerMascheroniSeq;
  have h_log_bound : ∀ x : ℝ, 0 ≤ x → Real.log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) :=
    fun x a => log_one_add_le_quadratic a
  have := h_log_bound ( 1 / ( k + 1 ) ) ( by positivity ) ; norm_num at *;
  field_simp at *;
  rw [ Real.log_div ( by positivity ) ( by positivity ) ] at this ; nlinarith [ sq ( k : ℝ ) ]
/-- For `m ≥ n`, the difference of Euler-Mascheroni sequence values is bounded below
    by a telescoping sum. -/
lemma eulerMascheroniSeq_diff_lb (n m : ℕ) (h : n ≤ m) :
    (1 : ℝ) / (2 * (↑n + 1)) - 1 / (2 * (↑m + 1)) ≤
    eulerMascheroniSeq m - eulerMascheroniSeq n := by
  induction' h with k hk;
  · norm_num;
  · have h_step : eulerMascheroniSeq (k + 1) - eulerMascheroniSeq k ≥ 1 / (2 * (k + 1) * (k + 2) : ℝ) :=
      eulerMascheroniSeq_step_lb k
    norm_num [ Nat.cast_add_one_ne_zero ] at *;
    nlinarith [ inv_pos.mpr ( by positivity : 0 < ( k : ℝ ) + 1 ), inv_pos.mpr ( by positivity : 0 < ( k : ℝ ) + 2 ), mul_inv_cancel₀ ( by positivity : ( k : ℝ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( k : ℝ ) + 2 ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( k : ℝ ) + 1 + 1 ≠ 0 ) ]
/-- The Euler-Mascheroni constant satisfies `γ ≥ eulerMascheroniSeq(n) + 1/(2(n+1))`. -/
lemma eulerMascheroniConstant_lb (n : ℕ) :
    eulerMascheroniSeq n + 1 / (2 * ((n : ℝ) + 1)) ≤ eulerMascheroniConstant := by
  have h_lim : Filter.Tendsto (fun m => eulerMascheroniSeq m - eulerMascheroniSeq n) Filter.atTop (nhds (eulerMascheroniConstant - eulerMascheroniSeq n)) := by
    exact Filter.Tendsto.sub ( Real.tendsto_eulerMascheroniSeq ) tendsto_const_nhds;
  have h_lim_bound : Filter.Tendsto (fun m => 1 / (2 * (n + 1) : ℝ) - 1 / (2 * (m + 1) : ℝ)) Filter.atTop (nhds (1 / (2 * (n + 1) : ℝ))) := by
    exact le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.Tendsto.const_mul_atTop zero_lt_two <| Filter.tendsto_id.atTop_add tendsto_const_nhds ) <| by norm_num;
  have := h_lim_bound.comp tendsto_natCast_atTop_atTop;
  exact le_of_tendsto_of_tendsto this h_lim ( Filter.eventually_atTop.mpr ⟨ n, by intros m hm; simpa using eulerMascheroniSeq_diff_lb n m hm ⟩ ) |> fun h => by norm_num at * ; linarith;
/-- The ℚ-valued Taylor sum used in the computational verification. -/
def taylorSumQ (x : ℚ) (K : ℕ) : ℚ :=
  (Finset.range K).sum (fun i => x ^ i / (Nat.factorial i : ℚ))
/-- The rational value `harmonic(400) + 1/802 - 577215/1000000`. -/
def r400 : ℚ := harmonic 400 + 1 / (2 * (400 + 1)) - 577215 / 1000000
/-- Computational verification: the Taylor sum exceeds 401. -/
lemma taylorSumQ_r400_gt : taylorSumQ r400 23 > (401 : ℚ) := by native_decide
/-- The ℚ Taylor sum casts to the ℝ Taylor sum. -/
lemma taylorSumQ_cast (x : ℚ) (K : ℕ) :
    (taylorSumQ x K : ℝ) =
    (Finset.range K).sum (fun i => (x : ℝ) ^ i / (Nat.factorial i : ℝ)) := by
  norm_num [ taylorSumQ ]
/-- `r400` is nonneg. -/
lemma r400_nonneg : (0 : ℝ) ≤ (r400 : ℝ) := by
  exact_mod_cast by native_decide;
/-- `exp(r400) > 401`. -/
lemma exp_r400_gt : (401 : ℝ) < Real.exp (r400 : ℝ) := by
  calc (401 : ℝ) < (taylorSumQ r400 23 : ℝ) := by exact_mod_cast taylorSumQ_r400_gt
    _ = (Finset.range 23).sum (fun i => (r400 : ℝ) ^ i / (Nat.factorial i : ℝ)) :=
        taylorSumQ_cast r400 23
    _ ≤ Real.exp (r400 : ℝ) := Real.sum_le_exp_of_nonneg r400_nonneg 23
/-- `r400 > log 401`. -/
lemma r400_gt_log_401 : Real.log 401 < (r400 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 401)]
  exact exp_r400_gt
/-- The main bound: `eulerMascheroniSeq 400 + 1/802 ≥ 577215/1000000`. -/
lemma eulerMascheroniSeq_400_lb :
    (577215 : ℝ) / 1000000 ≤ eulerMascheroniSeq 400 + 1 / (2 * (400 + 1)) := by
  have h1 : (r400 : ℝ) = ↑(harmonic 400 : ℚ) + 1 / (2 * (400 + 1)) - 577215 / 1000000 := by
    simp only [r400]
    push_cast
    ring
  unfold eulerMascheroniSeq
  linarith [r400_gt_log_401]

lemma hγ_lo : (0.577215 : ℝ) ≤ Real.eulerMascheroniConstant := by
  calc (0.577215 : ℝ) = 577215 / 1000000 := by norm_num
    _ ≤ eulerMascheroniSeq 400 + 1 / (2 * ((400 : ℝ) + 1)) := eulerMascheroniSeq_400_lb
    _ ≤ eulerMascheroniConstant := eulerMascheroniConstant_lb 400

open Real in
/-- For u > 0: u²/2 - u + log(1+u) > 0. This is the base case of our chain of
    positivity lemmas, proved by the mean value theorem since the derivative
    u²/(1+u) is positive. -/
lemma log_ineq_1 (u : ℝ) (hu : 0 < u) : 0 < u ^ 2 / 2 - u + Real.log (1 + u) := by
  set f : ℝ → ℝ := fun u => u^2 / 2 - u + Real.log (1 + u)
  have h_deriv_pos : ∀ u > 0, 0 < deriv f u := by
    intro u hu; norm_num [f, add_comm, show u + 1 ≠ 0 by linarith]; ring_nf
    nlinarith [inv_mul_cancel₀ (by linarith : (1 + u) ≠ 0)]
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 u, deriv f c = (f u - f 0) / (u - 0) := by
    apply_rules [exists_deriv_eq_slope]
    · exact continuousOn_of_forall_continuousAt fun x hx => by
        exact ContinuousAt.add (ContinuousAt.sub (ContinuousAt.div_const (continuousAt_id.pow 2) _)
          continuousAt_id) (ContinuousAt.log (continuousAt_const.add continuousAt_id)
          (by linarith [hx.1]))
    · exact fun x hx => DifferentiableAt.differentiableWithinAt (by
        exact DifferentiableAt.add (DifferentiableAt.sub (by norm_num) differentiableAt_id)
          (DifferentiableAt.log (differentiableAt_id.const_add _) (by linarith [hx.1])))
  have := h_deriv_pos c hc.1.1; rw [hc.2, lt_div_iff₀] at this <;> aesop
open Real in
/-- For u > 0: u³/6 - u²/2 + (1+u)·log(1+u) - u > 0. The derivative of this
    function is u²/2 - u + log(1+u), which is positive by `log_ineq_1`. -/
lemma log_ineq_2 (u : ℝ) (hu : 0 < u) :
    0 < u ^ 3 / 6 - u ^ 2 / 2 + (1 + u) * Real.log (1 + u) - u := by
  set g : ℝ → ℝ := fun u => u^3 / 6 - u^2 / 2 + (1 + u) * Real.log (1 + u) - u
  have hg_deriv_pos : ∀ u > 0, 0 < deriv g u := by
    simp +zetaDelta at *
    intro u hu; norm_num [add_comm, show u + 1 ≠ 0 by linarith]; ring_nf
    nlinarith [inv_mul_cancel₀ (by linarith : (1 + u) ≠ 0), log_ineq_1 u hu]
  have h_mvt : ∃ c ∈ Set.Ioo 0 u, deriv g c = (g u - g 0) / (u - 0) := by
    apply_rules [exists_deriv_eq_slope]
    · exact ContinuousOn.sub (ContinuousOn.add (ContinuousOn.sub
        (continuousOn_id.pow 3 |> ContinuousOn.div_const <| 6)
        (continuousOn_id.pow 2 |> ContinuousOn.div_const <| 2))
        (ContinuousOn.mul (continuousOn_const.add continuousOn_id)
        (ContinuousOn.log (continuousOn_const.add continuousOn_id)
        fun x hx => by linarith [hx.1]))) continuousOn_id
    · exact fun x hx => DifferentiableAt.differentiableWithinAt (by
        exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (by norm_num)
          (by norm_num)) (DifferentiableAt.mul (differentiableAt_id.const_add _)
          (DifferentiableAt.log (differentiableAt_id.const_add _) (by linarith [hx.1]))))
          differentiableAt_id)
  simp +zetaDelta at *
  obtain ⟨c, ⟨hc₁, hc₂⟩, hc⟩ := h_mvt
  have := hg_deriv_pos c hc₁; rw [hc, lt_div_iff₀] at this <;> nlinarith
open Real in
/-- For u > 0: 12(1+u)²·log(1+u) > 12u + 18u² + 4u³ - u⁴. The derivative of the
    difference is 24·[(1+u)·log(1+u) - u - u²/2 + u³/6], positive by `log_ineq_2`. -/
lemma log_ineq_3 (u : ℝ) (hu : 0 < u) :
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
    apply_rules [exists_deriv_eq_slope]
    · exact ContinuousOn.add (ContinuousOn.sub (ContinuousOn.sub (ContinuousOn.sub
        (ContinuousOn.mul (continuousOn_const.mul
        (ContinuousOn.pow (continuousOn_const.add continuousOn_id) 2))
        (ContinuousOn.log (continuousOn_const.add continuousOn_id)
        fun x hx => by linarith [hx.1]))
        (continuousOn_const.mul continuousOn_id))
        (continuousOn_const.mul (continuousOn_id.pow 2)))
        (continuousOn_const.mul (continuousOn_id.pow 3))) (continuousOn_id.pow 4)
    · exact DifferentiableOn.add (DifferentiableOn.sub (DifferentiableOn.sub
        (DifferentiableOn.sub (DifferentiableOn.mul (DifferentiableOn.mul (differentiableOn_const _)
        (DifferentiableOn.pow (differentiableOn_id.const_add _) _))
        (DifferentiableOn.log (differentiableOn_id.const_add _)
        (by intro x hx; linarith [hx.1])))
        (DifferentiableOn.mul (differentiableOn_const _) differentiableOn_id))
        (DifferentiableOn.mul (differentiableOn_const _) (differentiableOn_id.pow 2)))
        (DifferentiableOn.mul (differentiableOn_const _) (differentiableOn_id.pow 3)))
        (differentiableOn_id.pow 4)
  norm_num [add_comm, mul_comm] at *
  norm_num [show c + 1 ≠ 0 by linarith] at hc
  rw [eq_div_iff] at hc <;>
    nlinarith [hg_deriv_pos c hc.1.1,
      mul_inv_cancel_left₀ (by linarith : (c + 1) ≠ 0) (12 * (c + 1))]
open Real in
/-- The Euler-Maclaurin corrected sequence t(n) = H_n - log n - 1/(2n) + 1/(12n²)
    is strictly decreasing for n ≥ 1. -/
lemma euler_maclaurin_decreasing (n : ℕ) (hn : 1 ≤ n) :
    (harmonic (n + 1) : ℝ) - Real.log (↑(n + 1)) - 1 / (2 * ↑(n + 1)) +
      1 / (12 * ↑(n + 1) ^ 2) <
    (harmonic n : ℝ) - Real.log ↑n - 1 / (2 * ↑n) + 1 / (12 * ↑n ^ 2) := by
  suffices h : Real.log ((n + 1 : ℝ) / n) - (2 * n + 1) / (2 * n * (n + 1)) +
      (2 * n + 1) / (12 * n ^ 2 * (n + 1) ^ 2) > 0 by
    rw [Real.log_div] at h <;> norm_num at * <;> try positivity
    field_simp at *; grind
  have h_log_ineq : 12 * (1 + 1 / (n : ℝ)) ^ 2 * Real.log (1 + 1 / (n : ℝ)) >
      12 / (n : ℝ) + 18 / (n : ℝ) ^ 2 + 4 / (n : ℝ) ^ 3 - 1 / (n : ℝ) ^ 4 := by
    have := log_ineq_3 (1 / (n : ℝ)) (by positivity); aesop
  field_simp at *; grind
open Real in
/-- The corrected sequence t(n) = H_n - log n - 1/(2n) + 1/(12n²) converges to γ. -/
lemma euler_maclaurin_tendsto :
    Filter.Tendsto
      (fun n : ℕ => (harmonic n : ℝ) - Real.log ↑n - 1 / (2 * ↑n) + 1 / (12 * ↑n ^ 2))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have h : Filter.Tendsto (fun n => (harmonic n : ℝ) - Real.log n - 1 / (2 * n))
      Filter.atTop (nhds eulerMascheroniConstant) := by
    simpa using Filter.Tendsto.sub Real.tendsto_harmonic_sub_log
      (tendsto_inv_atTop_nhds_zero_nat.mul tendsto_const_nhds) |>.congr'
      (by filter_upwards [Filter.eventually_ne_atTop 0] with n hn; aesop)
  simpa using h.add (tendsto_inv_atTop_nhds_zero_nat.pow 2 |>.mul_const _)
open Real in
/-- γ < t(n) for all n ≥ 1, since t is strictly decreasing and converges to γ. -/
lemma euler_maclaurin_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant <
    (harmonic n : ℝ) - Real.log ↑n - 1 / (2 * ↑n) + 1 / (12 * ↑n ^ 2) := by
  have h_strict_anti : StrictAnti (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log (n + 1) -
      1 / (2 * (n + 1)) + 1 / (12 * (n + 1) ^ 2)) := by
    refine strictAnti_nat_of_succ_lt ?_
    intro n; have := euler_maclaurin_decreasing (n + 1) (by linarith); aesop
  have h_tendsto : Filter.Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log (n + 1) -
      1 / (2 * (n + 1)) + 1 / (12 * (n + 1) ^ 2))
      Filter.atTop (nhds eulerMascheroniConstant) := by
    convert euler_maclaurin_tendsto.comp (Filter.tendsto_add_atTop_nat 1) using 2; norm_num [harmonic]
  have h_lt : ∀ n : ℕ, (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1)) +
      1 / (12 * (n + 1) ^ 2) > eulerMascheroniConstant := by
    intro n
    exact lt_of_le_of_lt
      (le_of_tendsto h_tendsto <| Filter.eventually_atTop.mpr
        ⟨n + 1, fun m hm => h_strict_anti.antitone hm⟩)
      (h_strict_anti <| Nat.lt_succ_self _)
  cases n <;> aesop
open Real in
/-- Numerical verification: t(16) ≤ 0.577216, using log 2 > 0.6931471803. -/
lemma euler_maclaurin_numerical :
    (harmonic 16 : ℝ) - Real.log 16 - 1 / (2 * 16) + 1 / (12 * 16 ^ 2) ≤ 0.577216 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  norm_num at *; ring_nf at *; norm_num at *
  have := Real.log_two_gt_d9; norm_num at this; linarith
lemma hγ_hi : Real.eulerMascheroniConstant ≤ 0.577216 :=
  le_of_lt (lt_of_lt_of_le (euler_maclaurin_bound 16 (by norm_num)) euler_maclaurin_numerical)
