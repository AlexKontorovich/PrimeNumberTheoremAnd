import RSBounds.BacklundLowScalarBase
import ZetaLean.Rigor

/-!
# A kernel-checkable scalar interval evaluator

This evaluator uses exact rational arithmetic, Mathlib's proved bounds for pi,
and the existing twelve-term logarithm certificates. Its soundness theorem
concerns closed scalar expressions only; it asserts no zeta or prime estimate.
-/

namespace TernaryGoldbach.RSBounds.QuarticBudgetNumerics
open BacklundLowScalar

structure Bounds where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def Bounds.Contains (b : Bounds) (x : ℝ) : Prop :=
  (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

def Bounds.exact (q : ℚ) : Bounds := ⟨q, q⟩
def Bounds.add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩
def Bounds.sub (a b : Bounds) : Bounds := ⟨a.lo - b.hi, a.hi - b.lo⟩
def Bounds.mul (a b : Bounds) : Bounds :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩
def Bounds.inv (b : Bounds) : Bounds := ⟨1 / b.hi, 1 / b.lo⟩
def Bounds.pow (b : Bounds) : ℕ → Bounds
  | 0 => .exact 1
  | n + 1 => (b.pow n).mul b

theorem Bounds.contains_add {a b : Bounds} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x + y) := by
  simpa only [Contains, add, Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem Bounds.contains_sub {a b : Bounds} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.sub b).Contains (x - y) := by
  simpa only [Contains, sub, Rat.cast_sub] using
    And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

theorem Bounds.contains_mul {a b : Bounds} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x * y) := by
  simpa only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using
    And.intro (ZetaLean.mul_corners_le hx.1 hx.2 hy.1 hy.2)
      (ZetaLean.le_mul_corners hx.1 hx.2 hy.1 hy.2)

theorem Bounds.contains_inv {b : Bounds} {x : ℝ}
    (hx : b.Contains x) (hb : 0 < b.lo) : b.inv.Contains (1 / x) := by
  have hbR : (0 : ℝ) < (b.lo : ℝ) := by exact_mod_cast hb
  have hx0 : 0 < x := hbR.trans_le hx.1
  constructor
  · simpa only [inv, Rat.cast_div, Rat.cast_one] using
      one_div_le_one_div_of_le hx0 hx.2
  · simpa only [inv, Rat.cast_div, Rat.cast_one] using
      one_div_le_one_div_of_le hbR hx.1

theorem Bounds.contains_pow {b : Bounds} {x : ℝ} (hx : b.Contains x) :
    ∀ n, (b.pow n).Contains (x ^ n)
  | 0 => by simp [pow, exact, Contains]
  | n + 1 => by
    simpa only [pow, pow_succ] using Bounds.contains_mul (contains_pow hx n) hx

def piBounds : Bounds :=
  ⟨314159265358979323846 / 100000000000000000000,
   314159265358979323847 / 100000000000000000000⟩

theorem piBounds_sound : piBounds.Contains Real.pi := by
  constructor
  · convert Real.pi_gt_d20.le using 1 <;> norm_num [piBounds]
  · convert Real.pi_lt_d20.le using 1 <;> norm_num [piBounds]

inductive Expr where
  | rat : ℚ → Expr
  | pi : Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | inv : Expr → Expr
  | pow : Expr → ℕ → Expr
  | log : LogCert → LogCert → Expr → Expr

noncomputable def Expr.eval : Expr → ℝ
  | .rat q => (q : ℝ)
  | .pi => Real.pi
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .inv a => 1 / a.eval
  | .pow a n => a.eval ^ n
  | .log _ _ a => Real.log a.eval

def Expr.bounds : Expr → Bounds
  | .rat q => .exact q
  | .pi => piBounds
  | .add a b => a.bounds.add b.bounds
  | .sub a b => a.bounds.sub b.bounds
  | .mul a b => a.bounds.mul b.bounds
  | .inv a => a.bounds.inv
  | .pow a n => a.bounds.pow n
  | .log c d _ => ⟨c.lower, d.upper⟩

def Expr.check : Expr → Bool
  | .rat _ => true
  | .pi => true
  | .add a b | .sub a b | .mul a b => a.check && b.check
  | .inv a => a.check && decide (0 < a.bounds.lo)
  | .pow a _ => a.check
  | .log c d a => a.check && decide
      (c.Valid ∧ d.Valid ∧ 0 < c.ratio ∧ c.ratio ≤ a.bounds.lo ∧ a.bounds.hi ≤ d.ratio)

theorem Expr.sound (e : Expr) (he : e.check = true) : e.bounds.Contains e.eval := by
  induction e with
  | rat q => exact ⟨le_rfl, le_rfl⟩
  | pi => exact piBounds_sound
  | add a b ha hb =>
    have h : a.check = true ∧ b.check = true := by simpa [check] using he
    exact Bounds.contains_add (ha h.1) (hb h.2)
  | sub a b ha hb =>
    have h : a.check = true ∧ b.check = true := by simpa [check] using he
    exact Bounds.contains_sub (ha h.1) (hb h.2)
  | mul a b ha hb =>
    have h : a.check = true ∧ b.check = true := by simpa [check] using he
    exact Bounds.contains_mul (ha h.1) (hb h.2)
  | inv a ha =>
    have h : a.check = true ∧ 0 < a.bounds.lo := by simpa [check] using he
    exact Bounds.contains_inv (ha h.1) h.2
  | pow a n ha => exact Bounds.contains_pow (ha he) n
  | log c d a ha =>
    have h : a.check = true ∧
        (c.Valid ∧ d.Valid ∧ 0 < c.ratio ∧ c.ratio ≤ a.bounds.lo ∧ a.bounds.hi ≤ d.ratio) := by
      simpa [check] using he
    have hc := h.2
    have harg := ha h.1
    have hpos : (0 : ℝ) < (c.ratio : ℝ) := by exact_mod_cast hc.2.2.1
    have hlo : (c.ratio : ℝ) ≤ a.eval :=
      (show (c.ratio : ℝ) ≤ (a.bounds.lo : ℝ) by exact_mod_cast hc.2.2.2.1).trans harg.1
    have hhi : a.eval ≤ (d.ratio : ℝ) :=
      harg.2.trans (show (a.bounds.hi : ℝ) ≤ (d.ratio : ℝ) by exact_mod_cast hc.2.2.2.2)
    constructor
    · exact (LogCert.log_bounds hc.1).1.trans (Real.log_le_log hpos hlo)
    · exact (Real.log_le_log (hpos.trans_le hlo) hhi).trans (LogCert.log_bounds hc.2.1).2

theorem Expr.eval_lt {e : Expr} (he : e.check = true) {q : ℚ}
    (hq : e.bounds.hi < q) : e.eval < (q : ℝ) :=
  (e.sound he).2.trans_lt (by exact_mod_cast hq)

theorem Expr.eval_pos {e : Expr} (he : e.check = true)
    (hq : 0 < e.bounds.lo) : 0 < e.eval :=
  (show (0 : ℝ) < (e.bounds.lo : ℝ) by exact_mod_cast hq).trans_le (e.sound he).1

end TernaryGoldbach.RSBounds.QuarticBudgetNumerics
