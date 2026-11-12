module

/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
public import Mathlib
public import ZetaLean.Rigor
public import ZetaLean.IntervalExp

@[expose] public section

/-!
# Certified complex `exp`, and the Dirichlet term `n^{-s}`

The second and third stones of rung 3's numeric half.  `IntervalExp.lean`
certified the real elementary functions; this file lifts `exp` to `ℂ` on the
`ComplexInterval` layer of `ZetaLean/Rigor.lean` and then ties the Dirichlet
term `n^{-s} = exp(-s · log n)` to a kernel-checked enclosure, the gap
`ZetaLean/OracleDH.lean` names as "nothing here is kernel-checked about
`n^{-s}` itself".

* `ComplexInterval.expSumC`: the Taylor partial sum `∑_{i<n} z^i/i!` as
  rectangle arithmetic, sound by induction from `Rigor.lean`.
* `ComplexInterval.expSmall`, `exp` on a box with `normBound ≤ 1`: the
  Taylor sum inflated by the Lagrange-style remainder of Mathlib's
  `Complex.exp_bound`.  Since `exp(it)` has real part `cos t` and imaginary
  part `sin t`, this is simultaneously certified sin/cos, no separate
  trigonometric development is needed.
* `ComplexInterval.expC`: `exp` on a box with `normBound ≤ 2^k`, by `k`
  halvings and certified squarings (`exp z = exp(z/2)²`), mirroring
  `Interval.expI`.
* `ComplexInterval.dirichletTerm`: the enclosure of `m^{-s}` for natural
  `m ≥ 1` and rational `s`, composed from `Interval.logQ` and `expC` through
  Mathlib's `cpow_def_of_ne_zero` bridge.  `contains_dirichletTerm` is the
  theorem the oracle could not fake: the box is computed by kernel-reducible
  rational arithmetic and provably contains `(m : ℂ) ^ (-s)`.

What remains open of rung 3 Phase B after this file: the tail bound for the
analytic continuation (the series does not converge absolutely at
`Re s ≈ 0.808`; see the note at the bottom of `OracleDH.lean`), and the
assembly of the two disk inequalities of
`davenport_heilbronn_of_certified_disk` from term enclosures.

The smoke tests kernel-check digits of `cos 1`, `sin 1` and `cos 2`
end-to-end through the complex pipeline.
-/

namespace ZetaLean

/-- `|t| ≤ max |lo| |hi|` for `t ∈ [lo, hi]`: the endpoint bound that turns
interval containment into a norm bound. -/
private theorem abs_le_max_abs_endpoints {lo t hi : ℝ} (h1 : lo ≤ t) (h2 : t ≤ hi) :
    |t| ≤ max |lo| |hi| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc -(max |lo| |hi|) ≤ -|lo| := neg_le_neg (le_max_left _ _)
      _ ≤ lo := neg_abs_le lo
      _ ≤ t := h1
  · calc t ≤ hi := h2
      _ ≤ |hi| := le_abs_self hi
      _ ≤ max |lo| |hi| := le_max_right _ _

namespace ComplexInterval

open Finset

/-! ### Powers, rational scaling, Taylor partial sums -/

/-- Interval power by iterated corner multiplication. -/
def powI (x : ComplexInterval) : ℕ → ComplexInterval
  | 0 => exact 1 0
  | m + 1 => (powI x m).mul x

theorem contains_powI {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ∀ m, (powI x m).contains (z ^ m)
  | 0 => by
    rw [pow_zero]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [powI, exact, Interval.exact, Interval.contains]
  | m + 1 => by
    rw [pow_succ]
    exact contains_mul (contains_powI hx m) hx

/-- Scale a box by a rational scalar (viewed in `ℂ` through `ℝ`). -/
def smulQ (q : ℚ) (x : ComplexInterval) : ComplexInterval :=
  (exact q 0).mul x

theorem contains_smulQ {q : ℚ} {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    (smulQ q x).contains ((((q : ℚ) : ℝ) : ℂ) * z) := by
  have hq : (exact q 0).contains (((q : ℝ) : ℂ)) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [exact, Interval.exact, Interval.contains]
  exact contains_mul hq hx

/-- The Taylor partial sum `∑_{i<m} z^i / i!` as rectangle arithmetic. -/
def expSumC (x : ComplexInterval) : ℕ → ComplexInterval
  | 0 => exact 0 0
  | m + 1 => (expSumC x m).add (smulQ (1 / m.factorial) (powI x m))

theorem contains_expSumC {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ∀ m, (expSumC x m).contains (∑ i ∈ range m, z ^ i / i.factorial)
  | 0 => by simpa [expSumC] using contains_zero
  | m + 1 => by
    rw [Finset.sum_range_succ]
    have h := contains_smulQ (q := 1 / m.factorial) (contains_powI hx m)
    rw [show ((((1 / m.factorial : ℚ) : ℝ)) : ℂ) * z ^ m = z ^ m / m.factorial by
      push_cast; ring] at h
    exact contains_add (contains_expSumC hx m) h

/-! ### Norm bound and remainder inflation -/

/-- A rational bound on `‖z‖` valid for every `z` in the box: endpoint bounds
per component, combined by the triangle inequality `‖z‖ ≤ |re z| + |im z|`. -/
def normBound (x : ComplexInterval) : ℚ :=
  max |x.re.lo| |x.re.hi| + max |x.im.lo| |x.im.hi|

theorem norm_le_normBound {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ‖z‖ ≤ (normBound x : ℝ) := by
  have hre : |z.re| ≤ ((max |x.re.lo| |x.re.hi| : ℚ) : ℝ) := by
    push_cast
    exact abs_le_max_abs_endpoints hx.1.1 hx.1.2
  have him : |z.im| ≤ ((max |x.im.lo| |x.im.hi| : ℚ) : ℝ) := by
    push_cast
    exact abs_le_max_abs_endpoints hx.2.1 hx.2.2
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ _ := add_le_add hre him
    _ = ((normBound x : ℚ) : ℝ) := by rw [normBound]; push_cast; ring

/-- Widen a box by `|r|` in every direction. -/
def inflate (x : ComplexInterval) (r : ℚ) : ComplexInterval :=
  { re := { lo := x.re.lo - |r|, hi := x.re.hi + |r|,
            le := by have h1 := x.re.le; have h2 := abs_nonneg r; linarith },
    im := { lo := x.im.lo - |r|, hi := x.im.hi + |r|,
            le := by have h1 := x.im.le; have h2 := abs_nonneg r; linarith } }

/-- Soundness of `inflate`: if the box contains `z` and `‖w - z‖ ≤ r`, the
inflated box contains `w`. -/
theorem contains_inflate {x : ComplexInterval} {z w : ℂ} {r : ℚ}
    (hx : x.contains z) (hw : ‖w - z‖ ≤ (r : ℝ)) : (x.inflate r).contains w := by
  have hre : |w.re - z.re| ≤ |(r : ℝ)| :=
    calc |w.re - z.re| = |(w - z).re| := by rw [Complex.sub_re]
      _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
      _ ≤ (r : ℝ) := hw
      _ ≤ |(r : ℝ)| := le_abs_self _
  have him : |w.im - z.im| ≤ |(r : ℝ)| :=
    calc |w.im - z.im| = |(w - z).im| := by rw [Complex.sub_im]
      _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      _ ≤ (r : ℝ) := hw
      _ ≤ |(r : ℝ)| := le_abs_self _
  obtain ⟨hre1, hre2⟩ := abs_le.mp hre
  obtain ⟨him1, him2⟩ := abs_le.mp him
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [inflate] <;> push_cast <;> linarith

/-! ### `exp` on a small box, then on any box by halving and squaring -/

/-- Certified `exp` on a box with `normBound ≤ 1`: Taylor sum plus the
remainder of `Complex.exp_bound`, which is monotone in `‖z‖` and therefore
bounded by the same expression in `normBound`. -/
def expSmall (n : ℕ) (x : ComplexInterval) : ComplexInterval :=
  (expSumC x n).inflate (normBound x ^ n * ((n + 1) / (n.factorial * n)))

theorem contains_expSmall {n : ℕ} (hn : 0 < n) {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) (hb : normBound x ≤ 1) :
    (expSmall n x).contains (Complex.exp z) := by
  have hzb : ‖z‖ ≤ (normBound x : ℝ) := norm_le_normBound hx
  have hz1 : ‖z‖ ≤ 1 := hzb.trans (by exact_mod_cast hb)
  have h := Complex.exp_bound hz1 hn
  refine contains_inflate (contains_expSumC hx n) (h.trans ?_)
  have h1 : ‖z‖ ^ n ≤ (normBound x : ℝ) ^ n :=
    pow_le_pow_left₀ (norm_nonneg z) hzb n
  have h2 : (0 : ℝ) ≤ (n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹ := by positivity
  calc ‖z‖ ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹)
      ≤ (normBound x : ℝ) ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = ((normBound x ^ n * ((n + 1) / (n.factorial * n)) : ℚ) : ℝ) := by
        push_cast [Nat.succ_eq_add_one]
        ring

/-- Componentwise exact halving. -/
def halveC (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.halve, im := x.im.halve }

theorem contains_halveC {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    (halveC x).contains (z / 2) := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  constructor
  · rw [show (z / 2).re = z.re / 2 by rw [h2, Complex.div_ofReal_re]]
    exact Interval.contains_halve hx.1
  · rw [show (z / 2).im = z.im / 2 by rw [h2, Complex.div_ofReal_im]]
    exact Interval.contains_halve hx.2

theorem normBound_halveC (x : ComplexInterval) :
    normBound (halveC x) = normBound x / 2 := by
  simp only [normBound, halveC, Interval.halve, abs_div, abs_two]
  rw [max_div_div_right (by norm_num : (0 : ℚ) ≤ 2),
    max_div_div_right (by norm_num : (0 : ℚ) ≤ 2)]
  ring

/-- Certified `exp` on a box with `normBound ≤ 2^k`: halve `k` times into
the domain of `expSmall`, square back up (`exp z = exp(z/2)²`). -/
def expC (n : ℕ) : ℕ → ComplexInterval → ComplexInterval
  | 0, x => expSmall n x
  | k + 1, x =>
    let y := expC n k (halveC x)
    y.mul y

theorem contains_expC (n : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (x : ComplexInterval) (z : ℂ), x.contains z →
      normBound x ≤ 2 ^ k → (expC n k x).contains (Complex.exp z)
  | 0, x, z, hx, hb => by
    exact contains_expSmall hn hx (by simpa using hb)
  | k + 1, x, z, hx, hb => by
    have hy : (expC n k (halveC x)).contains (Complex.exp (z / 2)) := by
      refine contains_expC n hn k (halveC x) (z / 2) (contains_halveC hx) ?_
      rw [normBound_halveC]
      rw [pow_succ] at hb
      linarith
    have h := contains_mul hy hy
    rwa [show Complex.exp (z / 2) * Complex.exp (z / 2) = Complex.exp z by
      rw [← Complex.exp_add]; ring_nf] at h

/-! ### The Dirichlet term `m^{-s}` -/

/-- The enclosure of `m^{-s}`: `logQ` for `log m`, a corner product with the
exact rectangle for `-s`, and `expC` on the result.  `kL` steers the log
reduction (`m / 2^kL ∈ (0, 2)`), `kE` the exp range reduction
(`normBound ≤ 2^kE`); both side conditions are hypotheses of the containment
theorem, decidable by `norm_num` at any concrete call site. -/
def dirichletTerm (n kL kE : ℕ) (m : ℕ) (sre sim : ℚ) : ComplexInterval :=
  expC n kE ((exact (-sre) (-sim)).mul
    { re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 })

/-- **The oracle gap, closed for individual terms**: the box computed by
`dirichletTerm` provably contains `(m : ℂ) ^ (-s)`.  Every arithmetic step
is kernel-reducible rational interval arithmetic; the analytic inputs are
Mathlib's `Complex.exp_bound`, the `log` series bound, and the `cpow`
definition, no step is an oracle claim. -/
theorem contains_dirichletTerm {n kL kE : ℕ} (hn : 0 < n) {m : ℕ} (hm : 0 < m)
    {sre sim : ℚ}
    (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBound ((exact (-sre) (-sim)).mul
      { re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (dirichletTerm n kL kE m sre sim).contains
      ((m : ℂ) ^ (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ))) := by
  -- the log box contains `log m`, viewed in `ℂ`
  have hlogQ := Interval.contains_logQ (n := n) (k := kL) (q := (m : ℚ)) h0 h2
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlogQ
  have hL : ({ re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 } :
      ComplexInterval).contains ((Real.log m : ℝ) : ℂ) := by
    constructor
    · rw [Complex.ofReal_re]; exact hlogQ
    · rw [Complex.ofReal_im]; norm_num [Interval.contains, Interval.exact]
  -- the exact rectangle contains `-s`
  have hs : (exact (-sre) (-sim)).contains (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ)) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [exact, Interval.exact, Interval.contains, Complex.neg_re, Complex.neg_im]
  -- multiply and exponentiate
  have hexp := contains_expC n hn kE _ _ (contains_mul hs hL) hb
  -- bridge to `cpow`
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show ((m : ℂ) ^ (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ))) =
      Complex.exp (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ) * ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hm0,
      show Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    , mul_comm]]
  exact hexp

/-! ### Outward rounding

Exact rational interval arithmetic doubles digit counts at every squaring:
one Dirichlet term at the oracle point, evaluated without rounding, has
560000-bit endpoints.  `coarsen` is the primitive Arb has and the exact
layer lacked: round the endpoints outward to `p` dyadic bits.  Containment
is preserved, the box only grows, by at most `2^{-p}` per side. -/

/-- Round an interval's endpoints outward to `p` dyadic bits. -/
def _root_.ZetaLean.Interval.coarsen (p : ℕ) (x : Interval) : Interval :=
  { lo := (⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p,
    hi := (⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p,
    le := by
      have h2 : (0 : ℚ) < 2 ^ p := by positivity
      rw [div_le_div_iff_of_pos_right h2]
      calc ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℚ) ≤ x.lo * 2 ^ p := Int.floor_le _
        _ ≤ x.hi * 2 ^ p := by nlinarith [x.le]
        _ ≤ ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℚ) := Int.le_ceil _ }

theorem _root_.ZetaLean.Interval.contains_coarsen (p : ℕ) {x : Interval} {t : ℝ}
    (hx : x.contains t) : (x.coarsen p).contains t := by
  obtain ⟨h1, h2⟩ := hx
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  constructor
  · show (((⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p : ℚ) : ℝ) ≤ t
    rw [show (((⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p : ℚ) : ℝ)
        = ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℝ) / 2 ^ p by push_cast; ring,
      div_le_iff₀ h2p]
    calc ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℝ) ≤ ((x.lo * 2 ^ p : ℚ) : ℝ) := by
          exact_mod_cast Int.floor_le _
      _ = (x.lo : ℝ) * 2 ^ p := by push_cast; ring
      _ ≤ t * 2 ^ p := by nlinarith
  · show t ≤ (((⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p : ℚ) : ℝ)
    rw [show (((⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p : ℚ) : ℝ)
        = ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p by push_cast; ring,
      le_div_iff₀ h2p]
    calc t * 2 ^ p ≤ (x.hi : ℝ) * 2 ^ p := by nlinarith
      _ = ((x.hi * 2 ^ p : ℚ) : ℝ) := by push_cast; ring
      _ ≤ ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℝ) := by exact_mod_cast Int.le_ceil _

/-- Componentwise outward rounding of a rectangle. -/
def coarsen (p : ℕ) (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.coarsen p, im := x.im.coarsen p }

theorem contains_coarsen (p : ℕ) {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : (x.coarsen p).contains z :=
  ⟨Interval.contains_coarsen p hx.1, Interval.contains_coarsen p hx.2⟩

/-- `expC` with outward rounding to `p` bits after every squaring, the
digit-growth-free evaluator.  Identical enclosure semantics, boxes wider by
at most `2^{-p}` per level. -/
def expCr (n p : ℕ) : ℕ → ComplexInterval → ComplexInterval
  | 0, x => (expSmall n x).coarsen p
  | k + 1, x =>
    let y := expCr n p k (halveC x)
    (y.mul y).coarsen p

theorem contains_expCr (n p : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (x : ComplexInterval) (z : ℂ), x.contains z →
      normBound x ≤ 2 ^ k → (expCr n p k x).contains (Complex.exp z)
  | 0, x, z, hx, hb =>
    contains_coarsen p (contains_expSmall hn hx (by simpa using hb))
  | k + 1, x, z, hx, hb => by
    have hy : (expCr n p k (halveC x)).contains (Complex.exp (z / 2)) := by
      refine contains_expCr n p hn k (halveC x) (z / 2) (contains_halveC hx) ?_
      rw [normBound_halveC]
      rw [pow_succ] at hb
      linarith
    have h := contains_mul hy hy
    rw [show Complex.exp (z / 2) * Complex.exp (z / 2) = Complex.exp z by
      rw [← Complex.exp_add]; ring_nf] at h
    exact contains_coarsen p h

/-! ### The boxed-`s` Dirichlet term

The square-contour boundary segments range over sets of `s`, so the
enclosure must accept a rectangle for `s`, not only an exact point.  Same
pipeline; only the `-s` factor changes from an exact rectangle to `S.neg`. -/

/-- The enclosure of `m^{-s}` for every `s` in the box `S`, computed with
outward rounding to `p` bits (`expCr`) so endpoints stay `p`-bit dyadics
instead of doubling digits at every squaring. -/
def dirichletTermBox (n p kL kE : ℕ) (m : ℕ) (S : ComplexInterval) : ComplexInterval :=
  expCr n p kE (S.neg.mul { re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 })

theorem contains_dirichletTermBox {n p kL kE : ℕ} (hn : 0 < n) {m : ℕ} (hm : 0 < m)
    {S : ComplexInterval} {s : ℂ} (hS : S.contains s)
    (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBound (S.neg.mul
      { re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (dirichletTermBox n p kL kE m S).contains ((m : ℂ) ^ (-s)) := by
  have hlogQ := Interval.contains_logQ (n := n) (k := kL) (q := (m : ℚ)) h0 h2
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlogQ
  have hL : ({ re := Interval.logQ n kL (m : ℚ), im := Interval.exact 0 } :
      ComplexInterval).contains ((Real.log m : ℝ) : ℂ) := by
    constructor
    · rw [Complex.ofReal_re]; exact hlogQ
    · rw [Complex.ofReal_im]; norm_num [Interval.contains, Interval.exact]
  have hexp := contains_expCr n p hn kE _ _ (contains_mul (contains_neg hS) hL) hb
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show ((m : ℂ) ^ (-s)) = Complex.exp (-s * ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hm0,
      show Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    , mul_comm]]
  exact hexp

/-! ### Separating the two Taylor orders

`dirichletTermBox` uses one order `n` for both series it runs: the logarithm
`Interval.logQ n kL m` and the exponential `expCr n p kE`.  Measured on plan v2's
worst grid site, that coupling is what makes the plan infeasible, and the two
orders want opposite things:

* The **width** is set almost entirely by the log.  `logRem n q ≈ q^{n+1}/(1-q)`
  with `q ≤ 1/2`, so at `n = 20` the log carries width `7.6e-6`, which `|s| ≈ 86`
  amplifies to `6.6e-4` and the squaring tower to `3.0e-3`.  Multiplied over the
  `5K` terms of one site that is a box width of `1.5` against a `β` of `0.038`,
  infeasible by a factor of 30, before any Lean is generated.  Raising `kE` or
  the coarsening precision does not touch it: at `kE = 18` and `p = 128` the
  final width is still `3.0e-3`.  Raising the log order does: `n = 28` gives
  `3.0e-8` and `n = 32` gives `1.9e-9`.
* The **literal size** is set almost entirely by the exponential.  `expSmall`
  forms `powI x i` up to `i = n`, so `n` multiplies the endpoint bit-width by
  `n`; that is where the "multi-thousand-bit rationals" that defeated one-shot
  `norm_num` evaluation come from.  The log's own endpoints are small and stay
  small, order 20 to 32 takes them from 91 to 158 bits.

So the orders are split.  `nLog` is raised until the width fits; `nExp` stays
small so the generated literals stay evaluable.  Nothing else changes: the two
series are independent and the containment proof is the same argument. -/

/-- `dirichletTermBox` with the logarithm's Taylor order separated from the
exponential's.  `dirichletTermBox n p kL kE m S` is the `nLog = nExp = n` case. -/
def dirichletTermBox2 (nLog nExp p kL kE : ℕ) (m : ℕ) (S : ComplexInterval) :
    ComplexInterval :=
  expCr nExp p kE (S.neg.mul { re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 })

theorem contains_dirichletTermBox2 {nLog nExp p kL kE : ℕ} (hnL : 0 < nLog)
    (hnE : 0 < nExp) {m : ℕ} (hm : 0 < m) {S : ComplexInterval} {s : ℂ}
    (hS : S.contains s) (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBound (S.neg.mul
      { re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (dirichletTermBox2 nLog nExp p kL kE m S).contains ((m : ℂ) ^ (-s)) := by
  have hlogQ := Interval.contains_logQ (n := nLog) (k := kL) (q := (m : ℚ)) h0 h2
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlogQ
  have hL : ({ re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 } :
      ComplexInterval).contains ((Real.log m : ℝ) : ℂ) := by
    constructor
    · rw [Complex.ofReal_re]; exact hlogQ
    · rw [Complex.ofReal_im]; norm_num [Interval.contains, Interval.exact]
  have hexp := contains_expCr nExp p hnE kE _ _ (contains_mul (contains_neg hS) hL) hb
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show ((m : ℂ) ^ (-s)) = Complex.exp (-s * ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hm0,
      show Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    , mul_comm]]
  exact hexp

theorem dirichletTermBox2_self (n p kL kE m : ℕ) (S : ComplexInterval) :
    dirichletTermBox2 n n p kL kE m S = dirichletTermBox n p kL kE m S := rfl

/-! ### Reading a norm lower bound off a computed box -/

/-- The distance from `0` to an interval, `0` when the interval straddles
the origin, otherwise the nearer endpoint's magnitude. -/
def _root_.ZetaLean.Interval.distToZero (x : Interval) : ℚ :=
  max 0 (max x.lo (-x.hi))

theorem _root_.ZetaLean.Interval.distToZero_le_abs {x : Interval} {t : ℝ}
    (hx : x.contains t) : ((x.distToZero : ℚ) : ℝ) ≤ |t| := by
  obtain ⟨h1, h2⟩ := hx
  have ha : t ≤ |t| := le_abs_self t
  have hb : -t ≤ |t| := neg_le_abs t
  rw [Interval.distToZero]
  push_cast
  refine max_le (abs_nonneg t) (max_le ?_ ?_) <;> linarith

/-- The rational lower bound on `‖v‖` a rectangle certifies: the larger of
the two componentwise distances from zero. -/
def normLower (B : ComplexInterval) : ℚ :=
  max B.re.distToZero B.im.distToZero

/-- Reading the bound off the box: if `B` contains `v`, then
`normLower B ≤ ‖v‖`.  Together with `contains_dirichletTermBox` and the
tail bound this is how a boundary segment certifies `ε ≤ ‖DH z‖`. -/
theorem normLower_le_norm {B : ComplexInterval} {v : ℂ} (hB : B.contains v) :
    ((normLower B : ℚ) : ℝ) ≤ ‖v‖ := by
  have hre : ((B.re.distToZero : ℚ) : ℝ) ≤ ‖v‖ :=
    (Interval.distToZero_le_abs hB.1).trans (Complex.abs_re_le_norm v)
  have him : ((B.im.distToZero : ℚ) : ℝ) ≤ ‖v‖ :=
    (Interval.distToZero_le_abs hB.2).trans (Complex.abs_im_le_norm v)
  rw [normLower]
  push_cast
  exact max_le hre him

/-! ### Smoke tests: kernel-checked digits of `cos 1`, `sin 1`, `cos 2`

`exp(it)` has real part `cos t` and imaginary part `sin t`, so the complex
pipeline certifies trigonometric digits with no trigonometric code.  `cos 2`
routes through one halving-and-squaring step, exercising `expC`'s recursion
end-to-end. -/

private lemma exact01_contains_I : (exact 0 1).contains Complex.I := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [exact, Interval.exact, Interval.contains, Complex.I_re, Complex.I_im]

theorem cos_one_gt : (0.5402 : ℝ) < Real.cos 1 := by
  obtain ⟨⟨h1, -⟩, -⟩ := contains_expSmall (n := 8) (by norm_num)
    exact01_contains_I (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp Complex.I).re = Real.cos 1 by
    rw [Complex.exp_re]; norm_num [Complex.I_re, Complex.I_im]] at h1
  refine lt_of_lt_of_le ?_ h1
  norm_num [expSmall, expSumC, smulQ, powI, inflate, normBound, mul, add, exact,
    Interval.exact, Interval.mul, Interval.add, Interval.neg, Interval.sub,
    Nat.factorial]

theorem cos_one_lt : Real.cos 1 < (0.5404 : ℝ) := by
  obtain ⟨⟨-, h2⟩, -⟩ := contains_expSmall (n := 8) (by norm_num)
    exact01_contains_I (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp Complex.I).re = Real.cos 1 by
    rw [Complex.exp_re]; norm_num [Complex.I_re, Complex.I_im]] at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [expSmall, expSumC, smulQ, powI, inflate, normBound, mul, add, exact,
    Interval.exact, Interval.mul, Interval.add, Interval.neg, Interval.sub,
    Nat.factorial]

theorem sin_one_gt : (0.8414 : ℝ) < Real.sin 1 := by
  obtain ⟨-, h1, -⟩ := contains_expSmall (n := 8) (by norm_num)
    exact01_contains_I (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp Complex.I).im = Real.sin 1 by
    rw [Complex.exp_im]; norm_num [Complex.I_re, Complex.I_im]] at h1
  refine lt_of_lt_of_le ?_ h1
  norm_num [expSmall, expSumC, smulQ, powI, inflate, normBound, mul, add, exact,
    Interval.exact, Interval.mul, Interval.add, Interval.neg, Interval.sub,
    Nat.factorial]

theorem sin_one_lt : Real.sin 1 < (0.8415 : ℝ) := by
  obtain ⟨-, -, h2⟩ := contains_expSmall (n := 8) (by norm_num)
    exact01_contains_I (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp Complex.I).im = Real.sin 1 by
    rw [Complex.exp_im]; norm_num [Complex.I_re, Complex.I_im]] at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [expSmall, expSumC, smulQ, powI, inflate, normBound, mul, add, exact,
    Interval.exact, Interval.mul, Interval.add, Interval.neg, Interval.sub,
    Nat.factorial]

private lemma exact02_contains_2I : (exact 0 2).contains ((2 : ℂ) * Complex.I) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [exact, Interval.exact, Interval.contains, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]

theorem cos_two_gt : (-0.4163 : ℝ) < Real.cos 2 := by
  obtain ⟨⟨h1, -⟩, -⟩ := contains_expC 8 (by norm_num) 1 (exact 0 2)
    ((2 : ℂ) * Complex.I) exact02_contains_2I
    (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp ((2 : ℂ) * Complex.I)).re = Real.cos 2 by
    rw [Complex.exp_re]
    norm_num [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]] at h1
  refine lt_of_lt_of_le ?_ h1
  norm_num [expC, expSmall, expSumC, smulQ, powI, inflate, normBound, halveC, mul,
    add, exact, Interval.exact, Interval.mul, Interval.add, Interval.neg,
    Interval.sub, Interval.halve, Nat.factorial]

theorem cos_two_lt : Real.cos 2 < (-0.4159 : ℝ) := by
  obtain ⟨⟨-, h2⟩, -⟩ := contains_expC 8 (by norm_num) 1 (exact 0 2)
    ((2 : ℂ) * Complex.I) exact02_contains_2I
    (by norm_num [normBound, exact, Interval.exact])
  rw [show (Complex.exp ((2 : ℂ) * Complex.I)).re = Real.cos 2 by
    rw [Complex.exp_re]
    norm_num [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]] at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [expC, expSmall, expSumC, smulQ, powI, inflate, normBound, halveC, mul,
    add, exact, Interval.exact, Interval.mul, Interval.add, Interval.neg,
    Interval.sub, Interval.halve, Nat.factorial]

/-- `1^{-s} = 1` runs the whole `dirichletTerm` pipeline and lands on the
exact value, so the enclosure must contain `1`. -/
example : (dirichletTerm 8 0 1 1 (1 / 2) 1).contains 1 := by
  have h := contains_dirichletTerm (n := 8) (kL := 0) (kE := 1)
    (by norm_num) (by norm_num : 0 < 1) (sre := 1 / 2) (sim := 1)
    (by norm_num) (by norm_num)
    (by norm_num [normBound, mul, exact, Interval.logQ, Interval.log2I,
      Interval.log1, Interval.exact, Interval.mul, Interval.add, Interval.neg,
      Interval.sub, Interval.logSum, Interval.logRem, Finset.sum_range_succ])
  rwa [show ((1 : ℕ) : ℂ) ^ (-(⟨((1 / 2 : ℚ) : ℝ), ((1 : ℚ) : ℝ)⟩ : ℂ)) = 1 by
    rw [Nat.cast_one, Complex.one_cpow]] at h

end ComplexInterval

end ZetaLean
