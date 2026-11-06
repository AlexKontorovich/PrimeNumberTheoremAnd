module

public import HardyFirstZero.Phase
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/-!
# The corrected trapezoid rule with a fourth-derivative remainder (hunt `hardy_first_zero`)

Item 1 of `RESULTS.md` section 5, the domain-independent half of the order-4
Euler-Maclaurin representation the plan uses for `ζ` on the critical line:

    ∫_a^{a+1} g = (g(a) + g(a+1))/2 - (g'(a+1) - g'(a))/12 + ∫_a^{a+1} k g'''',
    0 ≤ k,  ∫_a^{a+1} k = 1/720,

with the quartic kernel `k(t) = (t-a)²(a+1-t)²/24`. One fundamental-theorem step
does all four integrations by parts at once: since `k'''' = 1`, the function
`k g''' - k' g'' + k'' g' - k''' g` has derivative `k g'''' - g`, and at both ends
`k = k' = 0`, `k'' = 1/12`, `k''' = ∓1/2`.

The lab's `ZetaLean/DHTailBound2.lean` proves the order-2 version
(`norm_trapezoid_sub_integral_le`); at `t = 14.13` the order-2 remainder needs 471
terms of the zeta partial sum where this one needs 15 (`sizing.py`).
-/

open intervalIntegral MeasureTheory Complex

namespace HardyFirstZero

/-- The quartic kernel on `[a, a+1]` and its first three derivatives. -/
noncomputable def kq (a t : ℝ) : ℝ := (t - a) ^ 2 * (a + 1 - t) ^ 2 / 24
noncomputable def kq1 (a t : ℝ) : ℝ := (t - a) * (a + 1 - t) * (2 * a + 1 - 2 * t) / 12
noncomputable def kq2 (a t : ℝ) : ℝ := (1 - 6 * (t - a) + 6 * (t - a) ^ 2) / 12
noncomputable def kq3 (a t : ℝ) : ℝ := (t - a) - 1 / 2

lemma hasDerivAt_kq (a t : ℝ) : HasDerivAt (kq a) (kq1 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h2 : HasDerivAt (fun x : ℝ => a + 1 - x) (-1) t := (hasDerivAt_id' t).const_sub (a + 1)
  have h := ((h1.fun_pow 2).fun_mul (h2.fun_pow 2)).div_const 24
  unfold kq kq1
  convert h using 1
  push_cast
  ring

lemma hasDerivAt_kq1 (a t : ℝ) : HasDerivAt (kq1 a) (kq2 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h2 : HasDerivAt (fun x : ℝ => a + 1 - x) (-1) t := (hasDerivAt_id' t).const_sub (a + 1)
  have h3 : HasDerivAt (fun x : ℝ => 2 * a + 1 - 2 * x) (-(2 * 1)) t :=
    ((hasDerivAt_id' t).const_mul 2).const_sub (2 * a + 1)
  have h := ((h1.fun_mul h2).fun_mul h3).div_const 12
  unfold kq1 kq2
  convert h using 1
  ring

lemma hasDerivAt_kq2 (a t : ℝ) : HasDerivAt (kq2 a) (kq3 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h := (((h1.const_mul 6).const_sub 1).fun_add ((h1.fun_pow 2).const_mul 6)).div_const 12
  unfold kq2 kq3
  convert h using 1
  push_cast
  ring

lemma hasDerivAt_kq3 (a t : ℝ) : HasDerivAt (kq3 a) 1 t :=
  ((hasDerivAt_id' t).sub_const a).sub_const (1 / 2 : ℝ)

lemma kq_nonneg (a t : ℝ) : 0 ≤ kq a t := by unfold kq; positivity

lemma integral_kq (a : ℝ) : ∫ t in a..a + 1, kq a t = 1 / 720 := by
  have hQ : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt
      (fun t => ((t - a) ^ 3 / 3 - (t - a) ^ 4 / 2 + (t - a) ^ 5 / 5) / 24) (kq a t) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
    have h := ((((h1.fun_pow 3).div_const 3).sub ((h1.fun_pow 4).div_const 2)).add
      ((h1.fun_pow 5).div_const 5)).div_const 24
    convert h using 1
    simp only [kq]; push_cast; ring
  rw [integral_eq_sub_of_hasDerivAt hQ
    ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_kq a t).continuousAt).intervalIntegrable _ _)]
  norm_num

/-- **The corrected trapezoid rule.** For a `C⁴` function on `[a, a+1]` whose fourth
derivative is bounded by `M`, the endpoint average corrected by the first
Bernoulli term misses the integral by at most `M/720`. -/
theorem corrected_trapezoid {g g1 g2 g3 g4 : ℝ → ℂ} {a M : ℝ}
    (h0 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g (g1 t) t)
    (h1 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g1 (g2 t) t)
    (h2 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g2 (g3 t) t)
    (h3 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g3 (g4 t) t)
    (hc : ContinuousOn g4 (Set.uIcc a (a + 1)))
    (hM : ∀ t ∈ Set.Icc a (a + 1), ‖g4 t‖ ≤ M) :
    ‖(∫ t in a..a + 1, g t) - ((g a + g (a + 1)) / 2 - (g1 (a + 1) - g1 a) / 12)‖
      ≤ M / 720 := by
  have hab : a ≤ a + 1 := by linarith
  have hcg : ContinuousOn g (Set.uIcc a (a + 1)) := fun t ht =>
    (h0 t ht).continuousAt.continuousWithinAt
  have hck : Continuous fun t => ((kq a t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_kq a t).continuousAt)
  -- the one fundamental-theorem step
  have hF : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt
      (fun t => ((kq a t : ℝ) : ℂ) * g3 t - ((kq1 a t : ℝ) : ℂ) * g2 t
        + ((kq2 a t : ℝ) : ℂ) * g1 t - ((kq3 a t : ℝ) : ℂ) * g t)
      (((kq a t : ℝ) : ℂ) * g4 t - g t) t := by
    intro t ht
    have e0 := (hasDerivAt_kq a t).ofReal_comp.mul (h3 t ht)
    have e1 := (hasDerivAt_kq1 a t).ofReal_comp.mul (h2 t ht)
    have e2 := (hasDerivAt_kq2 a t).ofReal_comp.mul (h1 t ht)
    have e3 := (hasDerivAt_kq3 a t).ofReal_comp.mul (h0 t ht)
    convert ((e0.sub e1).add e2).sub e3 using 1
    push_cast
    ring
  have hint : IntervalIntegrable (fun t => ((kq a t : ℝ) : ℂ) * g4 t - g t) volume a (a + 1) :=
    ((hck.continuousOn.mul hc).sub hcg).intervalIntegrable
  have hftc := integral_eq_sub_of_hasDerivAt hF hint
  have hkg : IntervalIntegrable (fun t => ((kq a t : ℝ) : ℂ) * g4 t) volume a (a + 1) :=
    (hck.continuousOn.mul hc).intervalIntegrable
  rw [integral_sub hkg hcg.intervalIntegrable] at hftc
  have hend : ((kq a (a + 1) : ℝ) : ℂ) = 0 ∧ ((kq1 a (a + 1) : ℝ) : ℂ) = 0
      ∧ ((kq2 a (a + 1) : ℝ) : ℂ) = 1 / 12 ∧ ((kq3 a (a + 1) : ℝ) : ℂ) = 1 / 2
      ∧ ((kq a a : ℝ) : ℂ) = 0 ∧ ((kq1 a a : ℝ) : ℂ) = 0
      ∧ ((kq2 a a : ℝ) : ℂ) = 1 / 12 ∧ ((kq3 a a : ℝ) : ℂ) = -1 / 2 := by
    simp only [kq, kq1, kq2, kq3]; push_cast; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hend
  simp only [e1, e2, e3, e4, e5, e6, e7, e8] at hftc
  have hkey : (∫ t in a..a + 1, g t) - ((g a + g (a + 1)) / 2 - (g1 (a + 1) - g1 a) / 12)
      = ∫ t in a..a + 1, ((kq a t : ℝ) : ℂ) * g4 t := by
    linear_combination (-1 : ℂ) * hftc
  rw [hkey]
  calc ‖∫ t in a..a + 1, ((kq a t : ℝ) : ℂ) * g4 t‖
      ≤ ∫ t in a..a + 1, ‖((kq a t : ℝ) : ℂ) * g4 t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..a + 1, kq a t * M := by
        refine intervalIntegral.integral_mono_on hab hkg.norm ?_ fun t ht => ?_
        · exact ((continuous_iff_continuousAt.mpr fun t =>
            (hasDerivAt_kq a t).continuousAt).mul continuous_const).intervalIntegrable _ _
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kq_nonneg a t)]
          exact mul_le_mul_of_nonneg_left (hM t ht) (kq_nonneg a t)
    _ = M / 720 := by
        rw [intervalIntegral.integral_mul_const, integral_kq]
        ring

/-! ### The zeta block -/

/-- The order-4 block on `[x, x+1]`: the integral of `t^{-s}` minus its corrected
trapezoid, in closed form. -/
noncomputable def eBlock (s : ℂ) (x : ℝ) : ℂ :=
  (((x + 1 : ℝ) : ℂ) ^ (1 - s) - ((x : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
    - (((x : ℝ) : ℂ) ^ (-s) + ((x + 1 : ℝ) : ℂ) ^ (-s)) / 2
    - s / 12 * (((x + 1 : ℝ) : ℂ) ^ (-s - 1) - ((x : ℝ) : ℂ) ^ (-s - 1))

/-- `P(s) = s(s+1)(s+2)(s+3)`, the constant of the fourth derivative of `t^{-s}`. -/
noncomputable def P4 (s : ℂ) : ℂ := s * (s + 1) * (s + 2) * (s + 3)

private lemma ne_zero_of_re_neg {r : ℂ} (h : r.re < 0) : r ≠ 0 := by
  rintro rfl; simp at h

/-- **The block bound**: `‖e(s, x)‖ ≤ ‖P(s)‖ x^{-σ-4} / 720` for `x ≥ 1`, `Re s > 0`, `s ≠ 1`. -/
theorem norm_eBlock_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖eBlock s x‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720 := by
  have hx0 : 0 < x := by linarith
  have hpos : ∀ t ∈ Set.uIcc x (x + 1), 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    linarith [ht.1]
  have r0 : (-s : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r1 : (-s - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r2 : (-s - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r3 : (-s - 1 - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
  set g1 : ℝ → ℂ := fun t => -s * (t : ℂ) ^ (-s - 1)
  set g2 : ℝ → ℂ := fun t => -s * (-s - 1) * (t : ℂ) ^ (-s - 1 - 1)
  set g3 : ℝ → ℂ := fun t => -s * (-s - 1) * (-s - 1 - 1) * (t : ℂ) ^ (-s - 1 - 1 - 1)
  set g4 : ℝ → ℂ := fun t =>
    -s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1) * (t : ℂ) ^ (-s - 1 - 1 - 1 - 1)
  have d0 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g (g1 t) t := fun t ht =>
    hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r0
  have d1 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g1 (g2 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r1).const_mul (-s)
    convert this using 1; simp only [g2]; ring
  have d2 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g2 (g3 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r2).const_mul (-s * (-s - 1))
    convert this using 1; simp only [g3]; ring
  have d3 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g3 (g4 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r3).const_mul
      (-s * (-s - 1) * (-s - 1 - 1))
    convert this using 1; simp only [g4]; ring
  have r4 : (-s - 1 - 1 - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have hc4 : ContinuousOn g4 (Set.uIcc x (x + 1)) := fun t ht =>
    ((hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r4).continuousAt.const_mul
      _).continuousWithinAt
  have hM : ∀ t ∈ Set.Icc x (x + 1), ‖g4 t‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [g4]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hP : ‖-s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1)‖ = ‖P4 s‖ := by
      rw [show -s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1) = P4 s by unfold P4; ring]
    rw [hP]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : (-s - 1 - 1 - 1 - 1).re = -s.re - 4 := by simp; ring
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos hx0 ht.1 (by linarith)
  have hT := corrected_trapezoid d0 d1 d2 d3 hc4 hM
  -- the integral in closed form
  have h0 : (0 : ℝ) ∉ Set.uIcc x (x + 1) := fun h => (lt_irrefl 0) (hpos 0 h)
  have hI : ∫ t in x..x + 1, g t
      = ((((x + 1 : ℝ) : ℂ) ^ (-s + 1) - ((x : ℝ) : ℂ) ^ (-s + 1)) / (-s + 1)) := by
    simp only [g]
    rw [integral_cpow (Or.inr ⟨fun h => hs1 (by linear_combination -h), h0⟩)]
  have hE : eBlock s x
      = (∫ t in x..x + 1, g t) - ((g x + g (x + 1)) / 2 - (g1 (x + 1) - g1 x) / 12) := by
    rw [hI]
    simp only [eBlock, g, g1]
    rw [show (-s + 1 : ℂ) = 1 - s by ring]
    push_cast
    ring
  rw [hE]
  calc _ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720 := hT
    _ = _ := rfl

/-! ### The representation where everything converges: `Re s > 2` -/

/-- The block at a natural point, written with natural-number casts. -/
lemma eBlock_nat (s : ℂ) (n : ℕ) :
    eBlock s (n : ℝ)
      = (((n + 1 : ℕ) : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)
        - ((n : ℂ) ^ (-s) + ((n + 1 : ℕ) : ℂ) ^ (-s)) / 2
        - s / 12 * (((n + 1 : ℕ) : ℂ) ^ (-s - 1) - (n : ℂ) ^ (-s - 1)) := by
  simp only [eBlock]
  push_cast
  ring

/-- The shifted Dirichlet series `Σ_k (k + N)^{-w}`, for `Re w > 1`. -/
lemma hasSum_shift {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    HasSum (fun k : ℕ => ((k + N : ℕ) : ℂ) ^ (-w))
      (riemannZeta w - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w)) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ w) := Complex.summable_one_div_nat_cpow.mpr hw
  have h : HasSum (fun n : ℕ => (n : ℂ) ^ (-w)) (riemannZeta w) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hw]
    convert hsum.hasSum using 1
    funext n; rw [Complex.cpow_neg, one_div]
  exact (hasSum_nat_add_iff' N).mpr h

/-- The same series with one more shift. -/
lemma hasSum_shift_succ {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    HasSum (fun k : ℕ => ((k + 1 + N : ℕ) : ℂ) ^ (-w))
      (riemannZeta w - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w) - (N : ℂ) ^ (-w)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_shift hw N)
  simpa [Finset.sum_range_one, add_comm, add_left_comm, add_assoc] using h

/-- **The order-4 representation on `Re s > 2`**, by absolute convergence. -/
theorem zeta_em4_of_two_lt {s : ℂ} (hs : 2 < s.re) (N : ℕ) :
    riemannZeta s
      = ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
        - ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ) := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have h1s : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hA := hasSum_shift (w := s) (by linarith) N
  have hA1 := hasSum_shift_succ (w := s) (by linarith) N
  have hC := hasSum_shift (w := s - 1) (by simp; linarith) N
  have hC1 := hasSum_shift_succ (w := s - 1) (by simp; linarith) N
  have hD := hasSum_shift (w := s + 1) (by simp; linarith) N
  have hD1 := hasSum_shift_succ (w := s + 1) (by simp; linarith) N
  have hE := (((hC1.sub hC).div_const (1 - s)).sub ((hA.add hA1).div_const 2)).sub
    ((hD1.sub hD).mul_left (s / 12))
  have hfun : (fun k : ℕ => eBlock s ((k + N : ℕ) : ℝ))
      = fun k : ℕ =>
        (((k + 1 + N : ℕ) : ℂ) ^ (-(s - 1)) - ((k + N : ℕ) : ℂ) ^ (-(s - 1))) / (1 - s)
        - (((k + N : ℕ) : ℂ) ^ (-s) + ((k + 1 + N : ℕ) : ℂ) ^ (-s)) / 2
        - s / 12 * (((k + 1 + N : ℕ) : ℂ) ^ (-(s + 1)) - ((k + N : ℕ) : ℂ) ^ (-(s + 1))) := by
    funext k
    rw [eBlock_nat]
    have e1 : (k + N + 1 : ℕ) = k + 1 + N := by omega
    rw [e1, show (-(s - 1) : ℂ) = 1 - s by ring, show (-(s + 1) : ℂ) = -s - 1 by ring]
  rw [← hfun] at hE
  rw [hE.tsum_eq]
  rw [show (-(s - 1) : ℂ) = 1 - s by ring, show (-(s + 1) : ℂ) = -s - 1 by ring]
  field_simp
  ring

/-! ### Continuation to the quarter plane `Re s > 0, Im s > 0` -/

/-- The right side of the representation, as a function of `s`. -/
noncomputable def emRHS (N : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
    + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
    - ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)

/-- The open quarter plane; it contains the critical line above the axis and
avoids the pole at `1`. -/
def QP : Set ℂ := {z | 0 < z.re ∧ 0 < z.im}

lemma isOpen_QP : IsOpen QP :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma convex_QP : Convex ℝ QP := by
  have hre : IsLinearMap ℝ (fun z : ℂ => z.re) :=
    ⟨fun x y => Complex.add_re x y, fun c x => by simp [Complex.real_smul, Complex.mul_re]⟩
  have him : IsLinearMap ℝ (fun z : ℂ => z.im) :=
    ⟨fun x y => Complex.add_im x y, fun c x => by simp [Complex.real_smul, Complex.mul_im]⟩
  exact (convex_halfSpace_gt hre 0).inter (convex_halfSpace_gt him 0)

lemma ne_one_of_QP {z : ℂ} (hz : z ∈ QP) : z ≠ 1 := by
  rintro rfl; simp [QP] at hz

lemma differentiableAt_eBlock {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (fun w => eBlock w x) s := by
  have hb0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hb1 : ((x + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hl : DifferentiableAt ℂ (fun w : ℂ => 1 - w) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have hn : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
  have hn1 : DifferentiableAt ℂ (fun w : ℂ => -w - 1) s := hn.sub (differentiableAt_const _)
  unfold eBlock
  refine (((hl.const_cpow (Or.inl hb1)).sub (hl.const_cpow (Or.inl hb0))).div hl
    (sub_ne_zero.mpr (Ne.symm hs))).sub
    (((hn.const_cpow (Or.inl hb0)).add (hn.const_cpow (Or.inl hb1))).div_const 2) |>.sub
    ((differentiableAt_id.div_const 12).mul
      ((hn1.const_cpow (Or.inl hb1)).sub (hn1.const_cpow (Or.inl hb0))))

private lemma summable_shift_rpow {p : ℝ} (hp : 1 < p) (N : ℕ) :
    Summable (fun k : ℕ => (((k + N : ℕ) : ℝ)) ^ (-p)) := by
  have hbase : Summable (fun k : ℕ => ((k : ℝ)) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (summable_nat_add_iff (f := fun k : ℕ => ((k : ℝ)) ^ (-p)) N).mpr hbase |>.congr
    fun k => by push_cast; ring_nf

lemma differentiableOn_tail {N : ℕ} (hN : 1 ≤ N) :
    DifferentiableOn ℂ (fun s => ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)) QP := by
  intro s₀ hs₀
  obtain ⟨hre0, him0⟩ := hs₀
  set δ : ℝ := min s₀.re s₀.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδre : δ ≤ s₀.re / 2 := by rw [hδ]; linarith [min_le_left s₀.re s₀.im]
  have hδim : δ ≤ s₀.im / 2 := by rw [hδ]; linarith [min_le_right s₀.re s₀.im]
  have hball : ∀ w ∈ Metric.ball s₀ δ, s₀.re / 2 ≤ w.re ∧ 0 < w.im ∧ ‖w‖ ≤ ‖s₀‖ + δ := by
    intro w hw
    have hd : ‖w - s₀‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_re_le_norm (w - s₀)
    have h2 := Complex.abs_im_le_norm (w - s₀)
    rw [Complex.sub_re] at h1
    rw [Complex.sub_im] at h2
    refine ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h2).1], ?_⟩
    calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + δ := by linarith
  set R : ℝ := ‖s₀‖ + δ + 3 with hR
  have hsub : Metric.ball s₀ δ ⊆ QP := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hball w hw
    exact ⟨by linarith, h2⟩
  have hu : Summable (fun k : ℕ => R ^ 4 * (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) / 720) :=
    ((summable_shift_rpow (p := s₀.re / 2 + 4) (by linarith) N).mul_left (R ^ 4)).div_const 720
  have hF_le : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball s₀ δ →
      ‖eBlock w ((k + N : ℕ) : ℝ)‖ ≤ R ^ 4 * (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) / 720 := by
    intro k w hw
    obtain ⟨h1, h2, h3⟩ := hball w hw
    have hx1 : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) := by
      have : 1 ≤ k + N := by omega
      exact_mod_cast this
    refine (norm_eBlock_le (by linarith) (ne_one_of_QP (hsub hw)) hx1).trans ?_
    have hP : ‖P4 w‖ ≤ R ^ 4 := by
      unfold P4
      have e1 : ‖w + 1‖ ≤ R := by
        calc ‖w + 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e2 : ‖w + 2‖ ≤ R := by
        calc ‖w + 2‖ ≤ ‖w‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e3 : ‖w + 3‖ ≤ R := by
        calc ‖w + 3‖ ≤ ‖w‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e0 : ‖w‖ ≤ R := by linarith
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖w‖ * ‖w + 1‖ * ‖w + 2‖ * ‖w + 3‖ ≤ R * R * R * R := by gcongr
        _ = R ^ 4 := by ring
    have hpow : (((k + N : ℕ) : ℝ)) ^ (-w.re - 4) ≤ (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hnn : 0 ≤ (((k + N : ℕ) : ℝ)) ^ (-w.re - 4) := Real.rpow_nonneg (by linarith) _
    have := mul_le_mul hP hpow hnn (by positivity)
    linarith
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (fun w => eBlock w ((k + N : ℕ) : ℝ)) (Metric.ball s₀ δ) :=
    fun k w hw => (differentiableAt_eBlock (by
      have : 1 ≤ k + N := by omega
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one this))
      (ne_one_of_QP (hsub hw))).differentiableWithinAt
  have hD := differentiableOn_tsum_of_summable_norm hu hdiff Metric.isOpen_ball hF_le
  exact (hD.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ0))).differentiableWithinAt

lemma differentiableOn_emRHS {N : ℕ} (hN : 1 ≤ N) : DifferentiableOn ℂ (emRHS N) QP := by
  intro s hs
  have hs0 : s ≠ 0 := by rintro rfl; simp [QP] at hs
  have hs1 := ne_one_of_QP hs
  have hn : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
  have hsum : DifferentiableAt ℂ (fun w => ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w)) s :=
    DifferentiableAt.fun_sum fun i _ => hn.const_cpow (Or.inr (neg_ne_zero.mpr hs0))
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (1 - w) / (w - 1)) s :=
    (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hNne)).div
      (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hs1)
  have h3 : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (-w) / 2) s :=
    (hn.const_cpow (Or.inl hNne)).div_const 2
  have h4 : DifferentiableAt ℂ (fun w : ℂ => w / 12 * (N : ℂ) ^ (-w - 1)) s :=
    (differentiableAt_id.div_const 12).mul
      ((hn.sub (differentiableAt_const _)).const_cpow (Or.inl hNne))
  have h5 : DifferentiableAt ℂ (fun s => ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)) s :=
    (differentiableOn_tail hN).differentiableAt (isOpen_QP.mem_nhds hs)
  exact ((((hsum.add h2).add h3).add h4).sub h5).differentiableWithinAt

/-- **The order-4 representation on the quarter plane**, by the identity theorem. -/
theorem zeta_em4 {s : ℂ} (hs : s ∈ QP) {N : ℕ} (hN : 1 ≤ N) : riemannZeta s = emRHS N s := by
  have hzd : DifferentiableOn ℂ riemannZeta QP := fun z hz =>
    (differentiableAt_riemannZeta (ne_one_of_QP hz)).differentiableWithinAt
  have hz : AnalyticOnNhd ℂ riemannZeta QP := hzd.analyticOnNhd isOpen_QP
  have he : AnalyticOnNhd ℂ (emRHS N) QP := (differentiableOn_emRHS hN).analyticOnNhd isOpen_QP
  have hmem : (3 + I : ℂ) ∈ QP := by simp [QP]
  have hev : riemannZeta =ᶠ[nhds (3 + I : ℂ)] emRHS N := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp; norm_num)) fun z hz => ?_
    exact zeta_em4_of_two_lt hz N
  exact hz.eqOn_of_preconnected_of_eventuallyEq he convex_QP.isPreconnected hmem hev hs

/-! ### The tail, by the integral test -/

theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 2 ≤ N) :
    ‖∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
  set p : ℝ := s.re + 4 with hp
  have hsumb : Summable (fun k : ℕ => (((k + N : ℕ) : ℝ)) ^ (-p)) :=
    summable_shift_rpow (by linarith) N
  have hb : ∀ k : ℕ, ‖eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720 := by
    intro k
    have hx1 : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + N)
    have := norm_eBlock_le hs hs1 hx1
    rwa [show -s.re - 4 = -p by rw [hp]; ring] at this
  have hg : Summable (fun k : ℕ => ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720) :=
    (hsumb.mul_left _).div_const _
  have hnorm : Summable (fun k : ℕ => ‖eBlock s ((k + N : ℕ) : ℝ)‖) :=
    hg.of_nonneg_of_le (fun k => norm_nonneg _) hb
  have hKR : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-p)) (Set.Ici ((N - 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hKR hx) hxy (by linarith)
  have hintg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioi ((N - 1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hKR
  have hnonneg : ∀ t ∈ Set.Ioi ((N - 1 : ℕ) : ℝ), 0 ≤ (fun t : ℝ => t ^ (-p)) t := fun t ht =>
    Real.rpow_nonneg (le_of_lt (lt_of_le_of_lt hKR.le ht)) _
  have htail := AntitoneOn.tsum_comp_add_le_integral (N - 1) hanti hintg hnonneg
  have hidx : ∀ n : ℕ, n + (N - 1) + 1 = n + N := fun n => by omega
  simp only [hidx] at htail
  have hint : ∫ t in Set.Ioi ((N - 1 : ℕ) : ℝ), t ^ (-p)
      = ((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hKR, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one,
      show -p + 1 = -(s.re + 3) by rw [hp]; ring, neg_div_neg_eq]
    congr 1
    ring_nf
  rw [hint] at htail
  calc ‖∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ∑' k : ℕ, ‖eBlock s ((k + N : ℕ) : ℝ)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720 := hnorm.tsum_le_tsum hb hg
    _ = ‖P4 s‖ * (∑' k : ℕ, (((k + N : ℕ) : ℝ)) ^ (-p)) / 720 := by
        rw [tsum_div_const, tsum_mul_left]
    _ ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
        gcongr

/-- **The order-4 Euler-Maclaurin remainder for zeta**, on the quarter plane:
for `Re s > 0`, `Im s > 0` and `N ≥ 2`,

    ‖ζ(s) - (Σ_{n<N} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + s N^{-s-1}/12)‖
      ≤ ‖s(s+1)(s+2)(s+3)‖ (N-1)^{-σ-3} / (720 (σ+3)). -/
theorem zeta_em4_error {s : ℂ} (hs : s ∈ QP) {N : ℕ} (hN : 2 ≤ N) :
    ‖riemannZeta s - (∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1))‖
      ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
  rw [zeta_em4 hs (N := N) (by omega)]
  have h : emRHS N s - (∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1))
      = -∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ) := by
    unfold emRHS; ring
  rw [h, norm_neg]
  exact norm_tail_le hs.1 (ne_one_of_QP hs) hN

end HardyFirstZero
