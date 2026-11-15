import Mathlib
import RSBounds.RS75ZeroFree1975

/-!
Independent audit of the RS75 zero-free region in `RSBounds.RS75ZeroFree1975`.

The two statements below are written from scratch, using only Mathlib notions
(`_root_.riemannZeta`, `Complex.re`, `Complex.im`, `Real.log`, `abs`), with
finite RH spelled out instead of using the project's `Goals.FiniteRH`.
Each is then proved by the project's theorem, so the project's proof
establishes exactly these statements. Rosser–Schoenfeld (1975), Theorem 1:
no zeros for |t| ≥ 21 and σ ≥ 1 - 1/(R log(|t|/17)), R = 9.645908801.
-/

/-- Unconditional part: no zeros for |t| ≥ 1894439 in the RS75 region. -/
theorem audit_RS75_high (s : ℂ) (ht : (1894439 : ℝ) ≤ |s.im|)
    (hσ : (1 : ℝ) - 1 / ((9.645908801 : ℝ) * Real.log (|s.im| / 17)) ≤ s.re) :
    _root_.riemannZeta s ≠ 0 :=
  TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free_high ht hσ

/-- Full RS75 Theorem 1, assuming every zero with 0 < σ < 1 and
|γ| ≤ 1894439 lies on the critical line. -/
theorem audit_RS75
    (hRH : ∀ ρ : ℂ, _root_.riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ (1894439 : ℝ) → ρ.re = 1 / 2)
    (s : ℂ) (ht : (21 : ℝ) ≤ |s.im|)
    (hσ : (1 : ℝ) - 1 / ((9.645908801 : ℝ) * Real.log (|s.im| / 17)) ≤ s.re) :
    _root_.riemannZeta s ≠ 0 :=
  TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free hRH ht hσ

-- The project's own statements, as elaborated.
#check @TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free_high
#check @TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free
#print TernaryGoldbach.RSBounds.Goals.FiniteRH

#print axioms audit_RS75_high
#print axioms audit_RS75
#print axioms TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free
#print axioms TernaryGoldbach.RSBounds.RS75ZeroFree1975.proved
