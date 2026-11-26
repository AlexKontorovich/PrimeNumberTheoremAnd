module

public import Mathlib

@[expose] public section

/-!
# Certified Interval Evaluation

Exact rational interval arithmetic with kernel-checked soundness. This is the
Lean analogue of `zeta/rigor.py`'s ball arithmetic: every operation returns an
interval **together with a proved containment lemma**, so a chain of
operations carries its enclosure by construction and nothing is ever silently
upgraded to a certificate.

Two layers:

* `Interval`: closed rational intervals `[lo, hi]` regarded as sets of reals
  via `Interval.contains`, with sound `exact` / `add` / `neg` / `sub` / `mul`.
* `ComplexInterval`: axis-aligned rational rectangles in `ℂ`, componentwise
  on `re` / `im`, with the complex product routed through the real layer via
  `Complex.mul_re` / `Complex.mul_im`.

The only genuinely mathematical step is interval multiplication: the product
of `a ∈ [xl, xu]` and `b ∈ [yl, yu]` is bounded by the four corner products,
in every sign configuration. That is `mul_corners_le` / `le_mul_corners`
below, proved once over `ℝ` and reused by both layers.

Supports Rung 3 Phase B (rigorous evaluation of Dirichlet partial sums for
the Davenport–Heilbronn certificate, `ZetaLean/DirichletEval.lean`).
-/

namespace ZetaLean

/-- Lower corner bound: if `a ∈ [xl, xu]` and `b ∈ [yl, yu]` then `a * b` is
at least the smallest of the four corner products. -/
theorem mul_corners_le {a b xl xu yl yu : ℝ}
    (hx1 : xl ≤ a) (hx2 : a ≤ xu) (hy1 : yl ≤ b) (hy2 : b ≤ yu) :
    min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ a * b := by
  rcases le_total 0 b with hb | hb
  · -- 0 ≤ b: a * b ≥ xl * b, and xl * b is over a corner of the xl row
    refine le_trans (le_trans (min_le_left _ _) ?_)
      (mul_le_mul_of_nonneg_right hx1 hb)
    rcases le_total 0 xl with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy1 h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy2 h)
  · -- b ≤ 0: a * b ≥ xu * b, and xu * b is over a corner of the xu row
    refine le_trans (le_trans (min_le_right _ _) ?_)
      (mul_le_mul_of_nonpos_right hx2 hb)
    rcases le_total 0 xu with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy1 h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy2 h)

/-- Upper corner bound: if `a ∈ [xl, xu]` and `b ∈ [yl, yu]` then `a * b` is
at most the largest of the four corner products. -/
theorem le_mul_corners {a b xl xu yl yu : ℝ}
    (hx1 : xl ≤ a) (hx2 : a ≤ xu) (hy1 : yl ≤ b) (hy2 : b ≤ yu) :
    a * b ≤ max (max (xl * yl) (xl * yu)) (max (xu * yl) (xu * yu)) := by
  rcases le_total 0 b with hb | hb
  · -- 0 ≤ b: a * b ≤ xu * b, bounded by a corner of the xu row
    refine le_trans (mul_le_mul_of_nonneg_right hx2 hb)
      (le_trans ?_ (le_max_right _ _))
    rcases le_total 0 xu with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hy2 h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hy1 h) (le_max_left _ _)
  · -- b ≤ 0: a * b ≤ xl * b, bounded by a corner of the xl row
    refine le_trans (mul_le_mul_of_nonpos_right hx1 hb)
      (le_trans ?_ (le_max_left _ _))
    rcases le_total 0 xl with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hy2 h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hy1 h) (le_max_left _ _)

/-- A closed rational interval `[lo, hi]`, the certified enclosure primitive. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi
  deriving Repr, DecidableEq

namespace Interval

/-- The set of reals an interval encloses. -/
def contains (x : Interval) (r : ℝ) : Prop :=
  (x.lo : ℝ) ≤ r ∧ r ≤ (x.hi : ℝ)

/-- The degenerate interval `[q, q]`. -/
def exact (q : ℚ) : Interval :=
  { lo := q, hi := q, le := le_refl q }

theorem contains_exact (q : ℚ) : (exact q).contains (q : ℝ) :=
  ⟨le_refl _, le_refl _⟩

def add (x y : Interval) : Interval :=
  { lo := x.lo + y.lo,
    hi := x.hi + y.hi,
    le := add_le_add x.le y.le }

theorem contains_add {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.add y).contains (a + b) := by
  refine ⟨?_, ?_⟩ <;> simp only [add] <;> push_cast
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

def neg (x : Interval) : Interval :=
  { lo := -x.hi,
    hi := -x.lo,
    le := neg_le_neg x.le }

theorem contains_neg {x : Interval} {a : ℝ}
    (hx : x.contains a) : x.neg.contains (-a) := by
  refine ⟨?_, ?_⟩ <;> simp only [neg] <;> push_cast
  · exact neg_le_neg hx.2
  · exact neg_le_neg hx.1

def sub (x y : Interval) : Interval :=
  x.add y.neg

theorem contains_sub {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.sub y).contains (a - b) :=
  sub_eq_add_neg a b ▸ contains_add hx (contains_neg hy)

/-- Interval product: the enclosure is the min/max of the four corner
products, which is sound in every sign configuration (`mul_corners_le`,
`le_mul_corners`). -/
def mul (x y : Interval) : Interval :=
  { lo := min (min (x.lo * y.lo) (x.lo * y.hi)) (min (x.hi * y.lo) (x.hi * y.hi)),
    hi := max (max (x.lo * y.lo) (x.lo * y.hi)) (max (x.hi * y.lo) (x.hi * y.hi)),
    le := le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _)) }

theorem contains_mul {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.mul y).contains (a * b) := by
  refine ⟨?_, ?_⟩ <;> simp only [mul] <;> push_cast
  · exact mul_corners_le hx.1 hx.2 hy.1 hy.2
  · exact le_mul_corners hx.1 hx.2 hy.1 hy.2

end Interval

/-- An axis-aligned rational rectangle in `ℂ`: certified enclosures for the
real and imaginary parts. -/
structure ComplexInterval where
  re : Interval
  im : Interval
  deriving Repr, DecidableEq

namespace ComplexInterval

/-- The set of complex numbers a rectangle encloses. -/
def contains (x : ComplexInterval) (z : ℂ) : Prop :=
  x.re.contains z.re ∧ x.im.contains z.im

/-- The degenerate rectangle `{q + r*I}`. -/
def exact (q r : ℚ) : ComplexInterval :=
  { re := Interval.exact q, im := Interval.exact r }

theorem contains_exact (q r : ℚ) :
    (exact q r).contains ⟨(q : ℝ), (r : ℝ)⟩ :=
  ⟨Interval.contains_exact q, Interval.contains_exact r⟩

theorem contains_zero : (exact 0 0).contains 0 := by
  constructor <;> simp [exact, Interval.contains, Interval.exact]

def add (x y : ComplexInterval) : ComplexInterval :=
  { re := x.re.add y.re, im := x.im.add y.im }

theorem contains_add {x y : ComplexInterval} {z w : ℂ}
    (hx : x.contains z) (hy : y.contains w) : (x.add y).contains (z + w) :=
  ⟨Interval.contains_add hx.1 hy.1, Interval.contains_add hx.2 hy.2⟩

def neg (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.neg, im := x.im.neg }

theorem contains_neg {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : x.neg.contains (-z) :=
  ⟨Interval.contains_neg hx.1, Interval.contains_neg hx.2⟩

def sub (x y : ComplexInterval) : ComplexInterval :=
  { re := x.re.sub y.re, im := x.im.sub y.im }

theorem contains_sub {x y : ComplexInterval} {z w : ℂ}
    (hx : x.contains z) (hy : y.contains w) : (x.sub y).contains (z - w) :=
  ⟨Interval.contains_sub hx.1 hy.1, Interval.contains_sub hx.2 hy.2⟩

/-- Complex product, routed through the real layer:
`(z*w).re = z.re*w.re − z.im*w.im` and `(z*w).im = z.re*w.im + z.im*w.re`. -/
def mul (x y : ComplexInterval) : ComplexInterval :=
  { re := (x.re.mul y.re).sub (x.im.mul y.im),
    im := (x.re.mul y.im).add (x.im.mul y.re) }

theorem contains_mul {x y : ComplexInterval} {z w : ℂ}
    (hx : x.contains z) (hy : y.contains w) : (x.mul y).contains (z * w) := by
  refine ⟨?_, ?_⟩
  · have h := Interval.contains_sub
      (Interval.contains_mul hx.1 hy.1) (Interval.contains_mul hx.2 hy.2)
    simpa [mul, Complex.mul_re] using h
  · have h := Interval.contains_add
      (Interval.contains_mul hx.1 hy.2) (Interval.contains_mul hx.2 hy.1)
    simpa [mul, Complex.mul_im] using h

end ComplexInterval

end ZetaLean
