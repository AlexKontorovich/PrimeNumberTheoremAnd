import Mathlib

/-!
# Independent statements for the check of the finite ψ bounds

Written for the independent check recorded in `verification/PsiFiniteIndependentCheck.md`,
from the mathematical statements, in a file that imports only Mathlib. Nothing from the project
is in scope here, so its declarations cannot change how these statements elaborate.
`PsiFiniteIndependentCheck.lean` then requires the project's theorems to prove exactly these
propositions.

ψ appears in two forms: Mathlib's `Chebyshev.psi`, and the sum Σ_{1 ≤ n ≤ x} Λ(n) written out,
with a proof that the two agree.

Compile, from `Projects/RSBounds`:

    mkdir -p /tmp/psi
    lake env lean -R verification -o /tmp/psi/PsiFiniteIndependentStatements.olean \
      verification/PsiFiniteIndependentStatements.lean
-/

namespace IndepPsiCheck

/-- The Chebyshev function written out: `ψ(x) = Σ_{1 ≤ n ≤ x} Λ(n)`. -/
noncomputable def psiSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n

/-- The written-out sum is Mathlib's `Chebyshev.psi`. -/
theorem psiSum_eq (x : ℝ) : psiSum x = Chebyshev.psi x := by
  have h : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp only [psiSum, Chebyshev.psi, h]

/-- T1: `|ψ(x) - x| ≤ (4/5) √x` for `1500 ≤ x ≤ 10^10`. -/
def T1 : Prop :=
  ∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x

/-- T2: `|ψ(x) - x| ≤ √x` for `8 < x ≤ 10^10`. -/
def T2 : Prop :=
  ∀ x : ℝ, 8 < x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ Real.sqrt x

/-- Büthe's (6.2), cut to `t ≤ 10^10`: `-0.8 ≤ (t - ψ(t))/√t ≤ 0.81` for `100 ≤ t`. -/
def B62 : Prop :=
  ∀ t : ℝ, 100 ≤ t → t ≤ 10 ^ 10 →
    -0.8 ≤ (t - Chebyshev.psi t) / Real.sqrt t ∧ (t - Chebyshev.psi t) / Real.sqrt t ≤ 0.81

/-- T1 with ψ written out. -/
def T1sum : Prop :=
  ∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |psiSum x - x| ≤ 4 / 5 * Real.sqrt x

/-- T2 with ψ written out. -/
def T2sum : Prop :=
  ∀ x : ℝ, 8 < x → x ≤ 10 ^ 10 → |psiSum x - x| ≤ Real.sqrt x

/-- Büthe's (6.2) on `[100, 10^10]` with ψ written out. -/
def B62sum : Prop :=
  ∀ t : ℝ, 100 ≤ t → t ≤ 10 ^ 10 →
    -0.8 ≤ (t - psiSum t) / Real.sqrt t ∧ (t - psiSum t) / Real.sqrt t ≤ 0.81

theorem T1sum_of_T1 (h : T1) : T1sum := fun x h₁ h₂ => by
  rw [psiSum_eq]; exact h x h₁ h₂

theorem T2sum_of_T2 (h : T2) : T2sum := fun x h₁ h₂ => by
  rw [psiSum_eq]; exact h x h₁ h₂

theorem B62sum_of_B62 (h : B62) : B62sum := fun t h₁ h₂ => by
  rw [psiSum_eq]; exact h t h₁ h₂

end IndepPsiCheck
