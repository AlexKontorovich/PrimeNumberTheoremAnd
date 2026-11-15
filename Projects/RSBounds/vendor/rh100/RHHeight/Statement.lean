module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Analytic.Order

@[expose] public section

/-!
# The target of hunt #137 (`rh_height_lean`): RH to height `T` for Mathlib's zeta

`RHUpToHeight T` says: every zero `ρ` of Mathlib's own `riemannZeta` in the open critical
strip with `0 < Im ρ ≤ T` lies on the critical line and is simple. The first target is
`RHHeight50 = RHUpToHeight 50`, where there are exactly ten such zeros; the second is
`RHHeight100`, with twenty-nine. Nothing in this file is proved about zeta: it holds the
statements as `Prop`s and the elementary facts that pin down what they say.

**Which multiplicity.** "Simple" is `analyticOrderAt riemannZeta ρ = 1`. This is the
multiplicity that the vendored `zeta23` count `Zeta23.Ncount` sums: there
`Zeta23.zeroMult ρ := (analyticOrderAt riemannZeta ρ).toNat`
(`lean/vendor/zeta23/Zeta23/Statement.lean`), and `toNat_analyticOrderAt_eq_one_iff` below
shows that `zeroMult ρ = 1` and `analyticOrderAt riemannZeta ρ = 1` are the same condition.
The window is the one `Zeta23.zerosIn 0 T` uses: `riemannZeta ρ = 0`, `0 < Re ρ < 1`
(`Zeta23.IsNontrivialZero`) and `0 < Im ρ ≤ T` (positive ordinates, not `|Im ρ|`).

**What this does not say.** It is a statement about finitely many zeros. It says nothing
above height `T` and nothing about the Riemann hypothesis (`docs/08`); like every
finite-height check it cannot tell zeta from the Davenport-Heilbronn function below that
function's first off-line zero (height 85.699, as `MISSION.md` records). The statement is
not vacuous: hunt #133 (`hunts/hardy_ten_zeros`) proves ten distinct zeros on the line with
ordinates in `(0, 50)`.

The proof plan is `hunts/rh_height_lean/PLAN.md`.
-/

open Complex

namespace RHHeight

/-- **RH to height `T`, with simplicity**, for Mathlib's `riemannZeta`: every zero `ρ` with
`0 < Re ρ < 1` and `0 < Im ρ ≤ T` has `Re ρ = 1/2` and analytic order exactly `1`. -/
def RHUpToHeight (T : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ T →
    ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1

/-- **The first target of hunt #137**: RH with simplicity to height 50. -/
def RHHeight50 : Prop := RHUpToHeight 50

/-- The second target: RH with simplicity to height 100. -/
def RHHeight100 : Prop := RHUpToHeight 100

/-- The zeros the statement quantifies over: `riemannZeta ρ = 0`, `0 < Re ρ < 1`,
`0 < Im ρ ≤ T`. As a set this is `Zeta23.zerosIn 0 T`. -/
def stripZerosUpTo (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- A companion statement: exactly `n` distinct zeros in the window up to height `T`.
(`Set.ncard` of an infinite set is `0`, so for `n ≠ 0` this also asserts finiteness.)
The planned proof of `RHHeight50` yields `ZeroCountUpTo 50 10` on the way. -/
def ZeroCountUpTo (T : ℝ) (n : ℕ) : Prop := (stripZerosUpTo T).ncard = n

/-- `zeta23`'s multiplicity condition `zeroMult ρ = 1`, written out, is the simplicity
condition of `RHUpToHeight`: `ℕ∞.toNat` sends `⊤` to `0`, so `toNat = 1` forces order `1`. -/
theorem toNat_analyticOrderAt_eq_one_iff (ρ : ℂ) :
    (analyticOrderAt riemannZeta ρ).toNat = 1 ↔ analyticOrderAt riemannZeta ρ = 1 :=
  -- `ENat.toNat_eq_iff` at `n = 1`
  ENat.toNat_eq_iff one_ne_zero

theorem mem_stripZerosUpTo {T : ℝ} {ρ : ℂ} :
    ρ ∈ stripZerosUpTo T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T :=
  Iff.rfl

/-- `RHUpToHeight T` restated over the window set. -/
theorem rhUpToHeight_iff (T : ℝ) :
    RHUpToHeight T ↔
      ∀ ρ ∈ stripZerosUpTo T, ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1 := by
  constructor
  · rintro h ρ ⟨h0, h1, h2, h3, h4⟩
    exact h ρ h0 h1 h2 h3 h4
  · intro h ρ h0 h1 h2 h3 h4
    exact h ρ ⟨h0, h1, h2, h3, h4⟩

/-- A larger height gives the statement at every smaller height. -/
theorem RHUpToHeight.mono {T T' : ℝ} (hT : T' ≤ T) (h : RHUpToHeight T) : RHUpToHeight T' :=
  fun ρ h0 h1 h2 h3 h4 => h ρ h0 h1 h2 h3 (h4.trans hT)

/-- The second target implies the first. -/
theorem RHHeight100.toRHHeight50 (h : RHHeight100) : RHHeight50 :=
  RHUpToHeight.mono (by norm_num) h

end RHHeight
