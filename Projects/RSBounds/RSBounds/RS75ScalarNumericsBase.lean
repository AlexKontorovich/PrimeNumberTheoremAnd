import RSBounds.QuarticBudgetNumericsBase

/-! Add certified rational square roots to the existing scalar interval checker.
All arithmetic soundness lemmas and logarithm certificates are reused. -/
namespace TernaryGoldbach.RSBounds.RS75ScalarNumerics
open QuarticBudgetNumerics

inductive Expr where
  | old : QuarticBudgetNumerics.Expr → Expr
  | sqrtRat : ℚ → ℚ → ℚ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | inv : Expr → Expr
  | pow : Expr → ℕ → Expr

noncomputable def Expr.eval : Expr → ℝ
  | .old e => e.eval
  | .sqrtRat q _ _ => Real.sqrt (q : ℝ)
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .inv a => 1 / a.eval
  | .pow a n => a.eval ^ n

def Expr.bounds : Expr → Bounds
  | .old e => e.bounds
  | .sqrtRat _ l u => ⟨l, u⟩
  | .add a b => a.bounds.add b.bounds
  | .sub a b => a.bounds.sub b.bounds
  | .mul a b => a.bounds.mul b.bounds
  | .inv a => a.bounds.inv
  | .pow a n => a.bounds.pow n

def Expr.check : Expr → Bool
  | .old e => e.check
  | .sqrtRat q l u => decide (0 ≤ l ∧ l ^ 2 ≤ q ∧ q ≤ u ^ 2 ∧ 0 ≤ u)
  | .add a b | .sub a b | .mul a b => a.check && b.check
  | .inv a => a.check && decide (0 < a.bounds.lo)
  | .pow a _ => a.check

theorem Expr.sound (e : Expr) (he : e.check = true) : e.bounds.Contains e.eval := by
  induction e with
  | old e => exact QuarticBudgetNumerics.Expr.sound e he
  | sqrtRat q l u =>
    have h : 0 ≤ l ∧ l ^ 2 ≤ q ∧ q ≤ u ^ 2 ∧ 0 ≤ u := by simpa [check] using he
    have hl : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast h.1
    have hlu : (l : ℝ) ^ 2 ≤ (q : ℝ) := by exact_mod_cast h.2.1
    have huu : (q : ℝ) ≤ (u : ℝ) ^ 2 := by exact_mod_cast h.2.2.1
    have hu : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast h.2.2.2
    exact ⟨Real.le_sqrt_of_sq_le hlu, (Real.sqrt_le_left hu).2 huu⟩
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

end TernaryGoldbach.RSBounds.RS75ScalarNumerics
