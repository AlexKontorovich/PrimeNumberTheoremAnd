import RSBounds.QuarticBudgetNumericsBase
import RSBounds.BacklundCenterNumericsBase

/-!
# Exact rational-power atoms for the RS75 golden-ratio scalar certificate

This extends the existing checked interval arithmetic by an integer root
certificate. It proves enclosures of closed finite expressions only. No
zeta-derivative or infinite-tail estimate is assumed or asserted here.
-/

namespace TernaryGoldbach.RSBounds.GoldenScalar

open QuarticBudgetNumerics

inductive Expr where
  | known : QuarticBudgetNumerics.Expr → Expr
  | root : ℕ → ℕ → ℕ → ℕ → ℕ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | inv : Expr → Expr
  | pow : Expr → ℕ → Expr

noncomputable def Expr.eval : Expr → ℝ
  | .known e => e.eval
  | .root n p k _ _ => (n : ℝ) ^ (-((p : ℝ) / k))
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .inv a => 1 / a.eval
  | .pow a n => a.eval ^ n

def Expr.bounds : Expr → Bounds
  | .known e => e.bounds
  | .root _ _ _ D b => ⟨(b : ℚ) / D, ((b : ℚ) + 1) / D⟩
  | .add a b => a.bounds.add b.bounds
  | .sub a b => a.bounds.sub b.bounds
  | .mul a b => a.bounds.mul b.bounds
  | .inv a => a.bounds.inv
  | .pow a n => a.bounds.pow n

def Expr.check : Expr → Bool
  | .known e => e.check
  | .root n p k D b => decide
      (0 < n ∧ 0 < k ∧ 0 < D ∧ b ^ k * n ^ p ≤ D ^ k ∧ D ^ k ≤ (b + 1) ^ k * n ^ p)
  | .add a b | .sub a b | .mul a b => a.check && b.check
  | .inv a => a.check && decide (0 < a.bounds.lo)
  | .pow a _ => a.check

theorem Expr.sound (e : Expr) (he : e.check = true) : e.bounds.Contains e.eval := by
  induction e with
  | known e => exact e.sound he
  | root n p k D b =>
      have h : 0 < n ∧ 0 < k ∧ 0 < D ∧
          b ^ k * n ^ p ≤ D ^ k ∧ D ^ k ≤ (b + 1) ^ k * n ^ p := by
        simpa only [check, decide_eq_true_eq] using he
      have hlo := CenterNumerics.root_lower h.1 h.2.1 h.2.2.1 h.2.2.2.1
      have hhi := CenterNumerics.root_upper h.1 h.2.1 h.2.2.1 h.2.2.2.2
      constructor
      · simpa only [bounds, Bounds.Contains, eval, Rat.cast_div, Rat.cast_natCast,
          neg_div] using hlo
      · simpa only [bounds, Bounds.Contains, eval, Rat.cast_div, Rat.cast_natCast,
          Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one, neg_div] using hhi
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

theorem Expr.eval_lt {e : Expr} (he : e.check = true) {q : ℚ}
    (hq : e.bounds.hi < q) : e.eval < (q : ℝ) :=
  (e.sound he).2.trans_lt (by exact_mod_cast hq)

theorem Expr.lt_eval {e : Expr} (he : e.check = true) {q : ℚ}
    (hq : q < e.bounds.lo) : (q : ℝ) < e.eval :=
  (show (q : ℝ) < (e.bounds.lo : ℝ) by exact_mod_cast hq).trans_le (e.sound he).1

end TernaryGoldbach.RSBounds.GoldenScalar
