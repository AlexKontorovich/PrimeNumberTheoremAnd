module

public import HardyTenZeros.TenSupport

@[expose] public section

/-!
# Zeta off the critical line: point boxes, and positivity on a horizontal segment

Support for the piece `horizontal_legs` of hunt #137 (`hunts/rh_height_lean/`). Hunt #133's
`HardyTenZeros.zeta_mem_mainBox` boxes `ζ(1/2 + it)`; the horizontal legs of the contour
need `ζ(σ + iT)` for every `σ` in `[1/2, 2]`. Everything here is general in the point; the
numbers live in the generated files `RHHeight/LegsBottom.lean`, `RHHeight/LegsTop*.lean` and
`RHHeight/LegsArg.lean`.

* `cBoxG_contains`, `mainBoxG_contains`: the order-4 main term
  `M_N(s) = Σ_{n<N} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + s N^{-s-1}/12` as a box at a
  Gaussian-rational point `s = x + iy`, from a table of term boxes;
* `norm_le_normUp`: a rational upper bound on `‖z‖` over a box, the octagon bound
  `max(X, Y) + (5/12) min(X, Y)` with `X`, `Y` the componentwise maxima;
* `norm_mainTerm_sub_le`: along a horizontal segment the main term moves by at most
  `(σ - a) L`, termwise from `‖n^{-s} - n^{-w}‖ ≤ (σ - a) log n ‖n^{-w}‖`;
* `norm_zeta_sub_mainTerm_le`: hunt #132's order-4 remainder `zeta_em4_error`, made uniform
  over the segment;
* `re_pos_of_segment`: `Re ζ(σ + iy) > 0` for every `σ` in `[a, b]`, from one table at the
  left end and one rational inequality;
* `zeta_mem_pointBox`, `arg_mem_of_box`: a box containing `ζ` at one point, and the
  argument bounds a box in the open right half-plane gives.

**The segment inequality.** Let `0 < a ≤ σ ≤ b`, `0 < y`, `2 ≤ N`, `w = a + iy`. Then

    Re ζ(σ + iy) ≥ Re M_N(w) - (σ - a) L - R,
    L = Σ_{n<N} log n ‖n^{-w}‖ + ‖N^{-w}‖ (log N (N/y + 1/2 + (b+y)/(12N)) + N/y² + 1/(12N)),
    R = P ‖(N-1)^{-w}‖ / ((N-1)³ · 720 · (a+3)),   P² ≥ Π_{j<4} ((b+j)² + y²).

`L` comes from `n^{-(σ+iy)} = n^{-w} n^{-(σ-a)}` and `0 ≤ 1 - n^{-δ} ≤ δ log n`, and from
`|c_N(s)| ≤ N/y + 1/2 + (b+y)/(12N)`, `|c_N(s) - c_N(w)| ≤ (σ-a)(N/y² + 1/(12N))`; `R` is
`zeta_em4_error` with `‖P4 s‖` taken at `b`, the power `(N-1)^{-σ-3}` at `a`, and
`(N-1)^{-a} = ‖(N-1)^{-w}‖`. In the rational check (`segSlack`) every norm `‖n^{-w}‖` is
replaced by `normUp` of its term box and every `log n` by `logTab n`, both upper bounds, so
the check reads only the table at the left end.
-/

open Complex Finset ZetaLean ZetaLean.ComplexInterval HardyFirstZero

namespace RHHeight.Legs

/-! ### Points and the main term -/

/-- The Gaussian-rational point `x + iy`. -/
noncomputable def ptQ (x y : ℚ) : ℂ := (x : ℂ) + (y : ℂ) * I

@[simp] lemma ptQ_re (x y : ℚ) : (ptQ x y).re = x := by simp [ptQ]

@[simp] lemma ptQ_im (x y : ℚ) : (ptQ x y).im = y := by simp [ptQ]

lemma ptQ_ne_zero (x : ℚ) {y : ℚ} (hy : y ≠ 0) : ptQ x y ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

lemma exact_contains_ptQ (x y : ℚ) : (ComplexInterval.exact x y).contains (ptQ x y) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [ComplexInterval.exact, Interval.exact]

/-- The order-4 Euler-Maclaurin main term that `zeta_em4_error` subtracts. -/
noncomputable def mainTerm (N : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + s / 12 * (N : ℂ) ^ (-s - 1)

/-- `c_N(s) = N/(s-1) + 1/2 + s/(12N)`, so that `M_N(s) = Σ_{n<N} n^{-s} + N^{-s} c_N(s)`. -/
noncomputable def cN (N : ℕ) (s : ℂ) : ℂ := (N : ℂ) / (s - 1) + 1 / 2 + s / (12 * N)

lemma mainTerm_eq (N : ℕ) (hN : N ≠ 0) (s : ℂ) :
    mainTerm N s = ∑ i ∈ range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (-s) * cN N s := by
  unfold mainTerm cN
  exact main_eq s hN

/-- Real part of `c_N(x + iy)`. -/
def cReG (N : ℕ) (x y : ℚ) : ℚ := N * (x - 1) / ((x - 1) ^ 2 + y ^ 2) + 1 / 2 + x / (12 * N)

/-- Imaginary part of `c_N(x + iy)`. -/
def cImG (N : ℕ) (x y : ℚ) : ℚ := -(N * y) / ((x - 1) ^ 2 + y ^ 2) + y / (12 * N)

theorem cBoxG_contains {N : ℕ} (hN : N ≠ 0) (x y : ℚ) (hy : y ≠ 0) :
    (ComplexInterval.exact (cReG N x y) (cImG N x y)).contains (cN N (ptQ x y)) := by
  have h := contains_exact (cReG N x y) (cImG N x y)
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdq : ((x - 1) ^ 2 + y ^ 2 : ℚ) ≠ 0 := by positivity
  have hd : (((x : ℂ) - 1) ^ 2 + (y : ℂ) ^ 2) ≠ 0 := by
    have h1 : ((((x - 1) ^ 2 + y ^ 2 : ℚ)) : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hdq
    push_cast at h1
    exact h1
  have hs1 : ((x : ℂ) + (y : ℂ) * I - 1) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact hy this
  have key : (N : ℂ) / ((x : ℂ) + (y : ℂ) * I - 1)
      = (N : ℂ) * (((x : ℂ) - 1) - (y : ℂ) * I) / (((x : ℂ) - 1) ^ 2 + (y : ℂ) ^ 2) := by
    rw [div_eq_div_iff hs1 hd]
    linear_combination (N : ℂ) * (y : ℂ) ^ 2 * I_sq
  have hz : (⟨((cReG N x y : ℚ) : ℝ), ((cImG N x y : ℚ) : ℝ)⟩ : ℂ)
      = ((cReG N x y : ℚ) : ℂ) + ((cImG N x y : ℚ) : ℂ) * I := by
    apply Complex.ext <;> simp
  unfold cN ptQ
  rw [key]
  convert h using 1
  rw [hz]
  unfold cReG cImG
  push_cast
  field_simp
  ring

/-- The rectangle for the order-4 main term at `x + iy`, from a table of term boxes. -/
def mainBoxG (T : ℕ → ComplexInterval) (N : ℕ) (x y : ℚ) : ComplexInterval :=
  (sumBoxes T N).add ((T N).mul (ComplexInterval.exact (cReG N x y) (cImG N x y)))

theorem mainBoxG_contains {x y : ℚ} (hy : y ≠ 0) {N : ℕ} (hN : N ≠ 0)
    {T : ℕ → ComplexInterval} (hT : ∀ m < N + 1, (T m).contains ((m : ℂ) ^ (-ptQ x y))) :
    (mainBoxG T N x y).contains (mainTerm N (ptQ x y)) := by
  rw [mainTerm_eq N hN]
  exact contains_add (contains_sumBoxes fun m hm => hT m (by omega))
    (contains_mul (hT N (by omega)) (cBoxG_contains hN x y hy))

/-! ### A norm bound read off a box -/

/-- The componentwise maxima `X = max |re|`, `Y = max |im|` of a box, combined by the octagon
bound `√(X² + Y²) ≤ max(X, Y) + (5/12) min(X, Y)` (`5/12 > √2 - 1`). -/
def normUp (B : ComplexInterval) : ℚ :=
  max (max |B.re.lo| |B.re.hi|) (max |B.im.lo| |B.im.hi|)
    + 5 / 12 * min (max |B.re.lo| |B.re.hi|) (max |B.im.lo| |B.im.hi|)

private lemma abs_le_max_abs {lo t hi : ℝ} (h1 : lo ≤ t) (h2 : t ≤ hi) : |t| ≤ max |lo| |hi| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc -(max |lo| |hi|) ≤ -|lo| := neg_le_neg (le_max_left _ _)
      _ ≤ lo := neg_abs_le lo
      _ ≤ t := h1
  · calc t ≤ hi := h2
      _ ≤ |hi| := le_abs_self hi
      _ ≤ max |lo| |hi| := le_max_right _ _

theorem norm_le_normUp {B : ComplexInterval} {z : ℂ} (h : B.contains z) :
    ‖z‖ ≤ (normUp B : ℝ) := by
  set X : ℝ := ((max |B.re.lo| |B.re.hi| : ℚ) : ℝ) with hX
  set Y : ℝ := ((max |B.im.lo| |B.im.hi| : ℚ) : ℝ) with hY
  have hre : |z.re| ≤ X := by
    rw [hX]; push_cast; exact abs_le_max_abs h.1.1 h.1.2
  have him : |z.im| ≤ Y := by
    rw [hY]; push_cast; exact abs_le_max_abs h.2.1 h.2.2
  have hX0 : 0 ≤ X := (abs_nonneg _).trans hre
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans him
  have hU : (normUp B : ℝ) = max X Y + 5 / 12 * min X Y := by
    rw [hX, hY, normUp]; push_cast; ring
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre2 : z.re ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs z.re]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have him2 : z.im ^ 2 ≤ Y ^ 2 := by
    rw [← sq_abs z.im]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have hoct : X ^ 2 + Y ^ 2 ≤ (max X Y + 5 / 12 * min X Y) ^ 2 := by
    rcases le_total X Y with hxy | hxy
    · rw [max_eq_right hxy, min_eq_left hxy]; nlinarith
    · rw [max_eq_left hxy, min_eq_right hxy]; nlinarith
  have hU0 : 0 ≤ max X Y + 5 / 12 * min X Y := by
    have := le_max_left X Y
    have := le_min hX0 hY0
    linarith
  rw [hU]
  by_contra hc
  push Not at hc
  have := norm_nonneg z
  nlinarith

lemma normUp_nonneg (B : ComplexInterval) : (0 : ℝ) ≤ normUp B := by
  have h1 : (0 : ℚ) ≤ max |B.re.lo| |B.re.hi| := le_max_of_le_left (abs_nonneg _)
  have h2 : (0 : ℚ) ≤ max |B.im.lo| |B.im.hi| := le_max_of_le_left (abs_nonneg _)
  have h3 : (0 : ℚ) ≤ normUp B := by
    unfold normUp
    have h3 : (0 : ℚ) ≤ max (max |B.re.lo| |B.re.hi|) (max |B.im.lo| |B.im.hi|) :=
      le_max_of_le_left h1
    have := le_min h1 h2
    linarith
  exact_mod_cast h3

/-! ### Logarithms -/

/-- A reduction exponent with `n < 2 ^ kOf n` for `n < 64`. -/
def kOf (n : ℕ) : ℕ :=
  if n < 2 then 1 else if n < 4 then 2 else if n < 8 then 3 else if n < 16 then 4
    else if n < 32 then 5 else 6

lemma lt_two_pow_kOf {n : ℕ} (hn : n < 64) : n < 2 ^ kOf n := by
  unfold kOf
  split_ifs <;> omega

/-- A rational upper bound for `log n`, read off `ZetaLean.Interval.logQ`. -/
def logTab (n : ℕ) : ℚ := if n < 2 then 0 else (Interval.logQ 20 (kOf n) (n : ℚ)).hi

theorem log_le_logTab {n : ℕ} (hn : n < 64) : Real.log n ≤ (logTab n : ℝ) := by
  unfold logTab
  split_ifs with h2
  · interval_cases n <;> simp
  · have hk := lt_two_pow_kOf hn
    have hq : ((n : ℚ) : ℝ) = (n : ℝ) := by push_cast; rfl
    have h0 : (0 : ℚ) < (n : ℚ) / 2 ^ kOf n := by
      have : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    have h2' : (n : ℚ) / 2 ^ kOf n < 2 := by
      have hk' : (n : ℚ) < 2 ^ kOf n := by exact_mod_cast hk
      have hp : (0 : ℚ) < 2 ^ kOf n := by positivity
      rw [div_lt_iff₀ hp]
      linarith
    have := (Interval.contains_logQ (n := 20) h0 h2').2
    rw [hq] at this
    exact this

lemma logTab_nonneg {n : ℕ} (hn : n < 64) : (0 : ℝ) ≤ logTab n :=
  (Real.log_natCast_nonneg n).trans (log_le_logTab hn)

/-! ### Moving along a horizontal segment -/

/-- `n^{-s} = n^{-w} · n^{-(Re s - Re w)}` when `s - w` is real. -/
lemma cpow_split {n : ℕ} (hn : 1 ≤ n) {s w : ℂ} (him : s.im = w.im) :
    (n : ℂ) ^ (-s) = (n : ℂ) ^ (-w) * (((n : ℝ) ^ (-(s.re - w.re)) : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs : -s = -w + ((-(s.re - w.re) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp; ring
    · simp [him]
  rw [hs, cpow_add _ _ hn0, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

/-- `|n^{-δ} - 1| ≤ δ log n` for `δ ≥ 0`. -/
lemma abs_rpow_neg_sub_one_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) :
    |(n : ℝ) ^ (-δ) - 1| ≤ δ * Real.log n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hle : (n : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hge : 1 - δ * Real.log n ≤ (n : ℝ) ^ (-δ) := by
    rw [Real.rpow_def_of_pos hn0]
    have := Real.add_one_le_exp (Real.log n * -δ)
    linarith
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **One term**: `‖n^{-s} - n^{-w}‖ ≤ (Re s - Re w) log n ‖n^{-w}‖` when `s - w ≥ 0` is real. -/
theorem norm_cpow_sub_le (n : ℕ) {s w : ℂ} (him : s.im = w.im) (hw : w.im ≠ 0)
    (hre : w.re ≤ s.re) :
    ‖(n : ℂ) ^ (-s) - (n : ℂ) ^ (-w)‖ ≤ (s.re - w.re) * Real.log n * ‖(n : ℂ) ^ (-w)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : -s ≠ 0 := by
      intro h; apply hw; rw [← him]; simpa using congrArg Complex.im h
    have hw0 : -w ≠ 0 := by
      intro h; apply hw; simpa using congrArg Complex.im h
    simp [zero_cpow hs0, zero_cpow hw0]
  · rw [cpow_split hn him]
    rw [show (n : ℂ) ^ (-w) * (((n : ℝ) ^ (-(s.re - w.re)) : ℝ) : ℂ) - (n : ℂ) ^ (-w)
        = (n : ℂ) ^ (-w) * ((((n : ℝ) ^ (-(s.re - w.re)) - 1 : ℝ)) : ℂ) by push_cast; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h := abs_rpow_neg_sub_one_le hn (sub_nonneg.mpr hre)
    have h0 := norm_nonneg ((n : ℂ) ^ (-w))
    calc ‖(n : ℂ) ^ (-w)‖ * |(n : ℝ) ^ (-(s.re - w.re)) - 1|
        ≤ ‖(n : ℂ) ^ (-w)‖ * ((s.re - w.re) * Real.log n) := mul_le_mul_of_nonneg_left h h0
      _ = _ := by ring

lemma norm_sub_one_ge {s : ℂ} : |s.im| ≤ ‖s - 1‖ := by
  have := Complex.abs_im_le_norm (s - 1)
  simpa using this

/-- `‖c_N(s)‖ ≤ N/Im s + 1/2 + (b + Im s)/(12N)` for `0 ≤ Re s ≤ b`, `Im s > 0`. -/
theorem norm_cN_le {N : ℕ} (hN : N ≠ 0) {s : ℂ} (him : 0 < s.im) (hre : 0 ≤ s.re) {b : ℝ}
    (hb : s.re ≤ b) : ‖cN N s‖ ≤ N / s.im + 1 / 2 + (b + s.im) / (12 * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h1 : ‖(N : ℂ) / (s - 1)‖ ≤ N / s.im := by
    rw [norm_div, Complex.norm_natCast]
    have h := (abs_of_pos him) ▸ (norm_sub_one_ge (s := s))
    exact div_le_div_of_nonneg_left hN'.le him h
  have h2 : ‖s / (12 * (N : ℂ))‖ ≤ (b + s.im) / (12 * N) := by
    rw [norm_div, show (12 * (N : ℂ)) = ((12 * N : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hre, abs_of_pos him] at h
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  unfold cN
  calc ‖(N : ℂ) / (s - 1) + 1 / 2 + s / (12 * N)‖
      ≤ ‖(N : ℂ) / (s - 1)‖ + ‖(1 / 2 : ℂ)‖ + ‖s / (12 * (N : ℂ))‖ := norm_add₃_le
    _ ≤ N / s.im + 1 / 2 + (b + s.im) / (12 * N) := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        linarith

/-- `‖c_N(s) - c_N(w)‖ ≤ (Re s - Re w)(N/(Im w)² + 1/(12N))` when `s - w ≥ 0` is real. -/
theorem norm_cN_sub_le {N : ℕ} (hN : N ≠ 0) {s w : ℂ} (him : s.im = w.im) (hpos : 0 < w.im)
    (hre : w.re ≤ s.re) :
    ‖cN N s - cN N w‖ ≤ (s.re - w.re) * (N / w.im ^ 2 + 1 / (12 * N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set δ : ℝ := s.re - w.re with hδ
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hre
  have hsw : s = w + (δ : ℂ) := by apply Complex.ext <;> simp [hδ, him]
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [him] at this; linarith
  have hw1 : w - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hdiff : cN N s - cN N w
      = -((N : ℂ) * δ / ((s - 1) * (w - 1))) + (δ : ℂ) / (12 * N) := by
    unfold cN
    rw [hsw] at hs1 ⊢
    field_simp
    ring
  rw [hdiff]
  have hns : |w.im| ≤ ‖s - 1‖ := by rw [← him]; exact norm_sub_one_ge
  have hnw : |w.im| ≤ ‖w - 1‖ := norm_sub_one_ge
  rw [abs_of_pos hpos] at hns hnw
  have e1 : ‖-((N : ℂ) * δ / ((s - 1) * (w - 1)))‖ ≤ δ * (N / w.im ^ 2) := by
    rw [norm_neg, norm_div, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hδ0]
    have hprod : w.im ^ 2 ≤ ‖s - 1‖ * ‖w - 1‖ := by
      rw [sq]; exact mul_le_mul hns hnw hpos.le (norm_nonneg _)
    have hw2 : 0 < w.im ^ 2 := by positivity
    calc (N : ℝ) * δ / (‖s - 1‖ * ‖w - 1‖) ≤ N * δ / w.im ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hw2 hprod
      _ = δ * (N / w.im ^ 2) := by ring
  have e2 : ‖(δ : ℂ) / (12 * (N : ℂ))‖ = δ * (1 / (12 * N)) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0,
      show (12 * (N : ℂ)) = ((12 * N : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
  calc ‖-((N : ℂ) * δ / ((s - 1) * (w - 1))) + (δ : ℂ) / (12 * N)‖
      ≤ ‖-((N : ℂ) * δ / ((s - 1) * (w - 1)))‖ + ‖(δ : ℂ) / (12 * (N : ℂ))‖ := norm_add_le _ _
    _ ≤ δ * (N / w.im ^ 2) + δ * (1 / (12 * N)) := by rw [e2]; linarith
    _ = δ * (N / w.im ^ 2 + 1 / (12 * N)) := by ring

/-- The `N^{-s} c_N(s)` part of the main term along the segment. -/
theorem norm_tail_sub_le {N : ℕ} (hN : 1 ≤ N) {s w : ℂ} (him : s.im = w.im) (hpos : 0 < w.im)
    (hre : w.re ≤ s.re) (hw0 : 0 ≤ w.re) {b : ℝ} (hb : s.re ≤ b) :
    ‖(N : ℂ) ^ (-s) * cN N s - (N : ℂ) ^ (-w) * cN N w‖
      ≤ (s.re - w.re) * (‖(N : ℂ) ^ (-w)‖ * (Real.log N * (N / w.im + 1 / 2 + (b + w.im) / (12 * N))
          + (N / w.im ^ 2 + 1 / (12 * N)))) := by
  have hN0 : N ≠ 0 := by omega
  set δ : ℝ := s.re - w.re with hδ
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hre
  set r : ℝ := (N : ℝ) ^ (-δ) with hr
  rw [cpow_split hN him]
  rw [show (N : ℂ) ^ (-w) * ((r : ℝ) : ℂ) * cN N s - (N : ℂ) ^ (-w) * cN N w
      = (N : ℂ) ^ (-w) * (((r - 1 : ℝ) : ℂ) * cN N s + (cN N s - cN N w)) by push_cast; ring]
  rw [norm_mul]
  have hc := norm_cN_le hN0 (him ▸ hpos) (hw0.trans hre) hb
  rw [him] at hc
  have hcd := norm_cN_sub_le hN0 him hpos hre
  have hr1 := abs_rpow_neg_sub_one_le hN hδ0
  have hin : ‖((r - 1 : ℝ) : ℂ) * cN N s + (cN N s - cN N w)‖
      ≤ δ * (Real.log N * (N / w.im + 1 / 2 + (b + w.im) / (12 * N))
          + (N / w.im ^ 2 + 1 / (12 * N))) := by
    calc ‖((r - 1 : ℝ) : ℂ) * cN N s + (cN N s - cN N w)‖
        ≤ ‖((r - 1 : ℝ) : ℂ) * cN N s‖ + ‖cN N s - cN N w‖ := norm_add_le _ _
      _ = |r - 1| * ‖cN N s‖ + ‖cN N s - cN N w‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (δ * Real.log N) * (N / w.im + 1 / 2 + (b + w.im) / (12 * N))
            + δ * (N / w.im ^ 2 + 1 / (12 * N)) := by
          gcongr
      _ = _ := by ring
  calc ‖(N : ℂ) ^ (-w)‖ * ‖((r - 1 : ℝ) : ℂ) * cN N s + (cN N s - cN N w)‖
      ≤ ‖(N : ℂ) ^ (-w)‖ * (δ * (Real.log N * (N / w.im + 1 / 2 + (b + w.im) / (12 * N))
          + (N / w.im ^ 2 + 1 / (12 * N)))) := mul_le_mul_of_nonneg_left hin (norm_nonneg _)
    _ = _ := by ring

/-- **The main term along a horizontal segment.** -/
theorem norm_mainTerm_sub_le {N : ℕ} (hN : 1 ≤ N) {s w : ℂ} (him : s.im = w.im)
    (hpos : 0 < w.im) (hre : w.re ≤ s.re) (hw0 : 0 ≤ w.re) {b : ℝ} (hb : s.re ≤ b) :
    ‖mainTerm N s - mainTerm N w‖ ≤ (s.re - w.re) *
      (∑ i ∈ range N, Real.log i * ‖(i : ℂ) ^ (-w)‖
        + ‖(N : ℂ) ^ (-w)‖ * (Real.log N * (N / w.im + 1 / 2 + (b + w.im) / (12 * N))
          + (N / w.im ^ 2 + 1 / (12 * N)))) := by
  have hN0 : N ≠ 0 := by omega
  rw [mainTerm_eq N hN0, mainTerm_eq N hN0]
  rw [show ∑ i ∈ range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (-s) * cN N s
      - (∑ i ∈ range N, (i : ℂ) ^ (-w) + (N : ℂ) ^ (-w) * cN N w)
      = ∑ i ∈ range N, ((i : ℂ) ^ (-s) - (i : ℂ) ^ (-w))
        + ((N : ℂ) ^ (-s) * cN N s - (N : ℂ) ^ (-w) * cN N w) by
    rw [Finset.sum_sub_distrib]; ring]
  have hsum : ‖∑ i ∈ range N, ((i : ℂ) ^ (-s) - (i : ℂ) ^ (-w))‖
      ≤ (s.re - w.re) * ∑ i ∈ range N, Real.log i * ‖(i : ℂ) ^ (-w)‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have := norm_cpow_sub_le i him hpos.ne' hre
    linarith
  have htail := norm_tail_sub_le hN him hpos hre hw0 hb
  calc _ ≤ ‖∑ i ∈ range N, ((i : ℂ) ^ (-s) - (i : ℂ) ^ (-w))‖
        + ‖(N : ℂ) ^ (-s) * cN N s - (N : ℂ) ^ (-w) * cN N w‖ := norm_add_le _ _
    _ ≤ _ := by rw [mul_add]; linarith

/-! ### The rational Lipschitz constant -/

/-- `Σ_{i<n} logTab i · normUp (T i)`. -/
def lipSum (T : ℕ → ComplexInterval) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lipSum T n + logTab n * normUp (T n)

/-- The Lipschitz constant of the main term on `[a, b] + iy`, from the table at `a + iy`. -/
def lipL (T : ℕ → ComplexInterval) (N : ℕ) (b y : ℚ) : ℚ :=
  lipSum T N + normUp (T N) * (logTab N * (N / y + 1 / 2 + (b + y) / (12 * N))
    + (N / y ^ 2 + 1 / (12 * N)))

lemma sum_le_lipSum {T : ℕ → ComplexInterval} {w : ℂ} :
    ∀ {n : ℕ}, n < 64 → (∀ m < n, (T m).contains ((m : ℂ) ^ (-w))) →
      ∑ i ∈ range n, Real.log i * ‖(i : ℂ) ^ (-w)‖ ≤ (lipSum T n : ℝ)
  | 0, _, _ => by simp [lipSum]
  | n + 1, h64, h => by
    rw [Finset.sum_range_succ, lipSum]
    push_cast
    have ih := sum_le_lipSum (T := T) (w := w) (n := n) (by omega) fun m hm => h m (by omega)
    have h1 := log_le_logTab (n := n) (by omega)
    have h2 := norm_le_normUp (h n (by omega))
    have h3 := Real.log_natCast_nonneg n
    have h4 := norm_nonneg ((n : ℂ) ^ (-w))
    have := mul_le_mul h1 h2 h4 (logTab_nonneg (by omega))
    linarith

/-! ### The remainder, uniformly on the segment -/

/-- `Π_{j<4} ((x + j)² + y²)`: the squared norm of `s(s+1)(s+2)(s+3)` at `s = x + iy`. -/
def q4G (x y : ℚ) : ℚ :=
  (x ^ 2 + y ^ 2) * ((x + 1) ^ 2 + y ^ 2) * ((x + 2) ^ 2 + y ^ 2) * ((x + 3) ^ 2 + y ^ 2)

/-- The same polynomial over `ℝ`. -/
noncomputable def q4R (x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) * ((x + 1) ^ 2 + y ^ 2) * ((x + 2) ^ 2 + y ^ 2) * ((x + 3) ^ 2 + y ^ 2)

lemma q4G_cast (x y : ℚ) : ((q4G x y : ℚ) : ℝ) = q4R x y := by
  unfold q4G q4R; push_cast; ring

lemma norm_P4_sq (s : ℂ) : ‖P4 s‖ ^ 2 = q4R s.re s.im := by
  have h : ∀ j : ℝ, ‖s + j‖ ^ 2 = (s.re + j) ^ 2 + s.im ^ 2 := by
    intro j
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [Complex.ofReal_zero, add_zero, Complex.ofReal_one] at h0 h1
  have e2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have e3 : ((3 : ℝ) : ℂ) = (3 : ℂ) := by norm_num
  rw [e2] at h2
  rw [e3] at h3
  unfold P4 q4R
  rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, h0, h1, h2, h3]

/-- `‖P4 s‖ ≤ P` whenever `0 ≤ Re s ≤ b` and `q4R b (Im s) ≤ P²`. -/
lemma norm_P4_le {s : ℂ} (h0 : 0 ≤ s.re) {b : ℝ} (hb : s.re ≤ b) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : q4R b s.im ≤ P ^ 2) : ‖P4 s‖ ≤ P := by
  have hsq := norm_P4_sq s
  have hmono : q4R s.re s.im ≤ q4R b s.im := by
    unfold q4R
    have e0 : s.re ^ 2 + s.im ^ 2 ≤ b ^ 2 + s.im ^ 2 := by nlinarith
    have e1 : (s.re + 1) ^ 2 + s.im ^ 2 ≤ (b + 1) ^ 2 + s.im ^ 2 := by nlinarith
    have e2 : (s.re + 2) ^ 2 + s.im ^ 2 ≤ (b + 2) ^ 2 + s.im ^ 2 := by nlinarith
    have e3 : (s.re + 3) ^ 2 + s.im ^ 2 ≤ (b + 3) ^ 2 + s.im ^ 2 := by nlinarith
    exact mul_le_mul (mul_le_mul (mul_le_mul e0 e1 (by positivity) (by positivity)) e2
      (by positivity) (by positivity)) e3 (by positivity) (by positivity)
  by_contra hc
  push Not at hc
  have := norm_nonneg (P4 s)
  nlinarith

/-- **The order-4 remainder, uniformly on a horizontal segment**: for `s = σ + iy` with
`a ≤ σ ≤ b` and `w = a + iy`, `0 < a`, `0 < y`,
`‖ζ(s) - M_N(s)‖ ≤ P ‖(N-1)^{-w}‖ / ((N-1)³ · 720 · (a + 3))` once `q4R b y ≤ P²`. -/
theorem norm_zeta_sub_mainTerm_le {N : ℕ} (hN : 2 ≤ N) {s w : ℂ} (him : s.im = w.im)
    (hpos : 0 < w.im) (hre : w.re ≤ s.re) (hw0 : 0 < w.re) {b : ℝ} (hb : s.re ≤ b) {P : ℝ}
    (hP0 : 0 ≤ P) (hP : q4R b w.im ≤ P ^ 2) :
    ‖riemannZeta s - mainTerm N s‖
      ≤ P * ‖((N - 1 : ℕ) : ℂ) ^ (-w)‖ / (((N : ℝ) - 1) ^ 3 * 720 * (w.re + 3)) := by
  have hQP : s ∈ QP := ⟨by linarith, by rw [him]; exact hpos⟩
  have h := zeta_em4_error hQP hN
  refine h.trans ?_
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set x : ℝ := (N : ℝ) - 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hx0 : 0 < x := by linarith
  have hP4 : ‖P4 s‖ ≤ P := norm_P4_le (by linarith) hb hP0 (by rw [him]; exact hP)
  have hpow : x ^ (-s.re - 3) ≤ x ^ (-w.re) / x ^ 3 := by
    calc x ^ (-s.re - 3) ≤ x ^ (-w.re - 3) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x ^ (-w.re) * x ^ (-(3 : ℝ)) := by rw [← Real.rpow_add hx0]; ring_nf
      _ = x ^ (-w.re) / x ^ 3 := by
          rw [Real.rpow_neg hx0.le (3 : ℝ), show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast, div_eq_mul_inv]
  have hnorm : ‖((N - 1 : ℕ) : ℂ) ^ (-w)‖ = x ^ (-w.re) := by
    rw [norm_natCast_cpow_of_pos (by omega : 0 < N - 1), Complex.neg_re,
      Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  rw [hnorm]
  have hnum0 : 0 ≤ x ^ (-w.re) / x ^ 3 := by positivity
  have hd1 : x ^ (-s.re - 3) / (s.re + 3) ≤ x ^ (-w.re) / x ^ 3 / (s.re + 3) :=
    div_le_div_of_nonneg_right hpow (by linarith)
  have hd2 : x ^ (-w.re) / x ^ 3 / (s.re + 3) ≤ x ^ (-w.re) / x ^ 3 / (w.re + 3) :=
    div_le_div_of_nonneg_left hnum0 (by linarith) (by linarith)
  have hq0 : 0 ≤ x ^ (-s.re - 3) / (s.re + 3) := by
    have : 0 < s.re + 3 := by linarith
    positivity
  calc ‖P4 s‖ * (x ^ (-s.re - 3) / (s.re + 3)) / 720
      ≤ P * (x ^ (-w.re) / x ^ 3 / (w.re + 3)) / 720 :=
        div_le_div_of_nonneg_right (mul_le_mul hP4 (hd1.trans hd2) hq0 hP0) (by norm_num)
    _ = P * x ^ (-w.re) / (x ^ 3 * 720 * (w.re + 3)) := by
        have : x ^ 3 ≠ 0 := by positivity
        have : w.re + 3 ≠ 0 := by linarith
        field_simp

/-- The rational remainder radius on `[a, b] + iy`, from the table at `a + iy`. -/
def remR (T : ℕ → ComplexInterval) (N : ℕ) (a P : ℚ) : ℚ :=
  P * normUp (T (N - 1)) / (((N : ℚ) - 1) ^ 3 * 720 * (a + 3))

lemma rem_le_remR {T : ℕ → ComplexInterval} {N : ℕ} (hN : 2 ≤ N) {a P : ℚ} (ha : 0 < a)
    (hP0 : 0 ≤ P) {w : ℂ} (hwre : w.re = a)
    (hT : (T (N - 1)).contains (((N - 1 : ℕ) : ℂ) ^ (-w))) :
    (P : ℝ) * ‖((N - 1 : ℕ) : ℂ) ^ (-w)‖ / (((N : ℝ) - 1) ^ 3 * 720 * (w.re + 3))
      ≤ (remR T N a P : ℝ) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hP0' : (0 : ℝ) ≤ P := by exact_mod_cast hP0
  have hD : 0 < ((N : ℝ) - 1) ^ 3 * 720 * ((a : ℝ) + 3) := by
    have : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    positivity
  unfold remR
  push_cast
  rw [hwre]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_le_normUp hT) hP0') hD.le

/-! ### Positivity on a segment -/

/-- The rational slack of one segment: the real part of the main-term box at the left end,
minus the variation of the main term along the segment, minus the remainder radius. -/
def segSlack (T : ℕ → ComplexInterval) (N : ℕ) (a b y P : ℚ) : ℚ :=
  (mainBoxG T N a y).re.lo - (b - a) * lipL T N b y - remR T N a P

/-- **Positivity of `Re ζ` on a horizontal segment.** For `0 < a ≤ σ ≤ b`, `0 < y` and
`2 ≤ N < 64`: a table of boxes for `m^{-(a+iy)}`, `m ≤ N`, a rational `P` with
`q4G b y ≤ P²`, and a positive `segSlack` give `Re ζ(σ + iy) > 0`. -/
theorem re_pos_of_segment {a b y : ℚ} (ha : 0 < a) (hy : 0 < y) {N : ℕ} (hN : 2 ≤ N)
    (hN64 : N < 64) {T : ℕ → ComplexInterval}
    (hT : ∀ m < N + 1, (T m).contains ((m : ℂ) ^ (-ptQ a y)))
    {P : ℚ} (hP0 : 0 ≤ P) (hP : q4G b y ≤ P ^ 2) (hslack : 0 < segSlack T N a b y P)
    (σ : ℝ) (hσa : (a : ℝ) ≤ σ) (hσb : σ ≤ b) :
    0 < (riemannZeta ((σ : ℂ) + (y : ℂ) * I)).re := by
  set s : ℂ := (σ : ℂ) + (y : ℂ) * I with hs
  set w : ℂ := ptQ a y with hw
  have hsre : s.re = σ := by simp [hs]
  have him : s.im = w.im := by simp [hs, hw]
  have hwre : w.re = a := ptQ_re a y
  have hwim : w.im = y := ptQ_im a y
  have hpos : (0 : ℝ) < w.im := by rw [hwim]; exact_mod_cast hy
  have hre : w.re ≤ s.re := by rw [hwre, hsre]; exact hσa
  have hw0 : (0 : ℝ) < w.re := by rw [hwre]; exact_mod_cast ha
  have hb : s.re ≤ (b : ℝ) := by rw [hsre]; exact hσb
  have hN0 : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  -- the main-term box at the left end
  have hB := mainBoxG_contains (x := a) (y := y) hy.ne' hN0 hT
  have hlo : ((mainBoxG T N a y).re.lo : ℝ) ≤ (mainTerm N w).re := hB.1.1
  -- the variation along the segment
  have hvar := norm_mainTerm_sub_le (by omega : 1 ≤ N) him hpos hre hw0.le hb
  set Lr : ℝ := ∑ i ∈ range N, Real.log i * ‖(i : ℂ) ^ (-w)‖
      + ‖(N : ℂ) ^ (-w)‖ * (Real.log N * (N / w.im + 1 / 2 + (b + w.im) / (12 * N))
        + (N / w.im ^ 2 + 1 / (12 * N))) with hLr
  have hLr0 : 0 ≤ Lr := by
    have h1 : 0 ≤ ∑ i ∈ range N, Real.log i * ‖(i : ℂ) ^ (-w)‖ :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Real.log_natCast_nonneg i) (norm_nonneg _)
    have h2 := Real.log_natCast_nonneg N
    have hb0 : (0 : ℝ) ≤ b := by linarith
    have h3 : 0 ≤ Real.log N * (N / w.im + 1 / 2 + (b + w.im) / (12 * N))
        + (N / w.im ^ 2 + 1 / (12 * N)) := by positivity
    have h4 := mul_nonneg (norm_nonneg ((N : ℂ) ^ (-w))) h3
    linarith
  have hLL : Lr ≤ (lipL T N b y : ℝ) := by
    have hsum := sum_le_lipSum (T := T) (w := w) (n := N) hN64 fun m hm => hT m (by omega)
    have hTN := norm_le_normUp (hT N (by omega))
    have hlogN := log_le_logTab hN64
    have hy' : (0 : ℝ) < y := by exact_mod_cast hy
    have hb0 : (0 : ℝ) ≤ b := by linarith
    have hC1 : (0 : ℝ) ≤ N / (y : ℝ) + 1 / 2 + (b + y) / (12 * N) := by positivity
    have hC2 : (0 : ℝ) ≤ N / (y : ℝ) ^ 2 + 1 / (12 * N) := by positivity
    have hin : Real.log N * (N / (y : ℝ) + 1 / 2 + (b + y) / (12 * N))
        + (N / (y : ℝ) ^ 2 + 1 / (12 * N))
        ≤ (logTab N : ℝ) * (N / (y : ℝ) + 1 / 2 + (b + y) / (12 * N))
          + (N / (y : ℝ) ^ 2 + 1 / (12 * N)) := by
      have := mul_le_mul_of_nonneg_right hlogN hC1
      linarith
    have hin0 : 0 ≤ Real.log N * (N / (y : ℝ) + 1 / 2 + (b + y) / (12 * N))
        + (N / (y : ℝ) ^ 2 + 1 / (12 * N)) := by
      have := Real.log_natCast_nonneg N
      positivity
    have hprod := mul_le_mul hTN hin hin0 (normUp_nonneg _)
    rw [hLr, hwim]
    unfold lipL
    push_cast
    linarith
  have hvar' : ‖mainTerm N s - mainTerm N w‖ ≤ ((b : ℝ) - a) * lipL T N b y := by
    refine hvar.trans ?_
    rw [hsre, hwre]
    exact mul_le_mul (by linarith) hLL hLr0 (by linarith)
  -- the remainder
  have hP0' : (0 : ℝ) ≤ P := by exact_mod_cast hP0
  have hP' : q4R b w.im ≤ (P : ℝ) ^ 2 := by
    rw [hwim, ← q4G_cast]; exact_mod_cast hP
  have hrem := (norm_zeta_sub_mainTerm_le hN him hpos hre hw0 hb hP0' hP').trans
    (rem_le_remR hN ha hP0 hwre (hT (N - 1) (by omega)))
  -- assemble
  have hsplit : (riemannZeta s).re = (mainTerm N w).re + (mainTerm N s - mainTerm N w).re
      + (riemannZeta s - mainTerm N s).re := by
    simp only [Complex.sub_re]; ring
  have h2 : -‖mainTerm N s - mainTerm N w‖ ≤ (mainTerm N s - mainTerm N w).re :=
    neg_le_of_abs_le (Complex.abs_re_le_norm _)
  have h3 : -‖riemannZeta s - mainTerm N s‖ ≤ (riemannZeta s - mainTerm N s).re :=
    neg_le_of_abs_le (Complex.abs_re_le_norm _)
  have hsl : (0 : ℝ) < ((mainBoxG T N a y).re.lo : ℝ) - ((b : ℝ) - a) * lipL T N b y
      - remR T N a P := by
    have := (Rat.cast_lt (K := ℝ)).mpr hslack
    unfold segSlack at this
    push_cast at this
    linarith
  linarith

/-! ### One point, and the argument -/

/-- **A box containing `ζ(a + iy)`**: the main-term box inflated by the remainder radius. -/
theorem zeta_mem_pointBox {a y : ℚ} (ha : 0 < a) (hy : 0 < y) {N : ℕ} (hN : 2 ≤ N)
    {T : ℕ → ComplexInterval} (hT : ∀ m < N + 1, (T m).contains ((m : ℂ) ^ (-ptQ a y)))
    {P : ℚ} (hP0 : 0 ≤ P) (hP : q4G a y ≤ P ^ 2) {e : ℚ} (he : remR T N a P ≤ e) :
    ((mainBoxG T N a y).inflate e).contains (riemannZeta (ptQ a y)) := by
  set w : ℂ := ptQ a y with hw
  have hwre : w.re = a := ptQ_re a y
  have hwim : w.im = y := ptQ_im a y
  have hpos : (0 : ℝ) < w.im := by rw [hwim]; exact_mod_cast hy
  have hw0 : (0 : ℝ) < w.re := by rw [hwre]; exact_mod_cast ha
  have hP0' : (0 : ℝ) ≤ P := by exact_mod_cast hP0
  have hP' : q4R (a : ℝ) w.im ≤ (P : ℝ) ^ 2 := by
    rw [hwim, ← q4G_cast]; exact_mod_cast hP
  have hrem := (norm_zeta_sub_mainTerm_le hN rfl hpos le_rfl hw0 (b := a) hwre.le hP0' hP').trans
    (rem_le_remR hN ha hP0 hwre (hT (N - 1) (by omega)))
  have he' : (remR T N a P : ℝ) ≤ e := by exact_mod_cast he
  exact contains_inflate (mainBoxG_contains hy.ne' (by omega) hT) (hrem.trans he')

/-- **The argument from a box** in the open right half-plane with nonpositive imaginary part:
`Im lo / Re lo ≤ arg z ≤ 0`, from `arg z = arctan (Im z / Re z)` and `x ≤ arctan x` for
`x ≤ 0`. -/
theorem arg_mem_of_box {B : ComplexInterval} {z : ℂ} (hB : B.contains z) (hre : 0 < B.re.lo)
    (him : B.im.hi ≤ 0) : ((B.im.lo / B.re.lo : ℚ) : ℝ) ≤ z.arg ∧ z.arg ≤ 0 := by
  have hrl0 : (0 : ℝ) < B.re.lo := by exact_mod_cast hre
  have hrlo : (B.re.lo : ℝ) ≤ z.re := hB.1.1
  have hzre : (0 : ℝ) < z.re := lt_of_lt_of_le hrl0 hrlo
  have hilo : (B.im.lo : ℝ) ≤ z.im := hB.2.1
  have hzim : z.im ≤ 0 := hB.2.2.trans (by exact_mod_cast him)
  constructor
  · have habs : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
    obtain ⟨h1, h2⟩ := abs_lt.mp habs
    have harg : z.arg = Real.arctan (z.im / z.re) := by
      rw [← Complex.tan_arg, Real.arctan_tan h1 h2]
    rw [harg]
    have hq : z.im / z.re ≤ 0 := div_nonpos_of_nonpos_of_nonneg hzim hzre.le
    refine le_trans ?_ (Real.self_le_arctan hq)
    push_cast
    rw [div_le_div_iff₀ hrl0 hzre]
    nlinarith [mul_nonneg (sub_nonneg.mpr hilo) hzre.le,
      mul_nonneg (neg_nonneg.mpr hzim) (sub_nonneg.mpr hrlo)]
  · rcases lt_or_eq_of_le hzim with h | h
    · exact (Complex.arg_neg_iff.mpr h).le
    · rw [Complex.arg_eq_zero_iff.mpr ⟨hzre.le, h⟩]

end RHHeight.Legs
