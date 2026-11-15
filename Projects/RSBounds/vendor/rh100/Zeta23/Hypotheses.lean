module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses.lean — the hypothesis ("axiom") boundary.

Canonical text: the paper.

PRINCIPLE: the fields of PaperInputs are PUBLISHED, CLASSICAL inputs,
stated in the paper's own form with the paper's equation labels. Everything the paper itself derives
(lem:poisson, prop:block, prop:tail, [eq:PiPfacts], [eq:Bdef], prop:trace, thm:traces, §6, taper facts
[eq:phinorms]–[eq:psiints], …) is a proof obligation and must NOT be added here. There are NO Lean
axiom declarations anywhere in this project: hypotheses are fields of the Prop-valued structure
PaperInputs, which every headline theorem takes as an explicit argument, so #print axioms stays at
{propext, Classical.choice, Quot.sound} and the trust boundary is exactly this file.

Every field below: docstring = paper label + verbatim paper statement + literature source + any
deviation in shape (∃-constant form unless the constant is load-bearing).
-/
public import Zeta23.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/-! ## H-EF — Weil's explicit formula in the paper's spectral form  [prop:EF], [eq:EF], [eq:Wdef] -/

/-- **H-EF** [prop:EF]/[eq:EF], verbatim: "Let f,g ∈ C_c²(ℝ) with supp f, supp g ⊂ [−L/2, L/2]. Then
    W(f,g) = ∫_ℝ h_f(τ) conj(h_g(τ)) ν_X(τ) dτ,   X = e^L."
where [eq:Wdef] "W(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)) … converges absolutely; here and below
Σ_ρ runs over the distinct nontrivial zeros (of either sign of γ) and the multiplicity is written
explicitly", h_f = paperFT f, and ν_X = μ + Π_X + P_X is Zeta23.nuX [eq:mudef]–[eq:nudef].
Source: Weil 1952 via [IK04, Theorem 5.12]; the paper's Appendix A [app:EF] derives this exact
normalisation from the literature form [eq:EFstd]. Zeta23/ExplicitFormula.lean proves
(literature form) → ExplicitFormulaPaper.
Shape notes: (i) quantified over every L > 0 (so X = e^L > 1 as the paper requires); (ii) the support
hypothesis is carried explicitly (without it the statement is false); (iii) the
absolute convergence of W and of the right-hand integral ("all integrals absolutely convergent",
App. A) are asserted as part of the package, since Lean's tsum/integral of a non-convergent
expression is 0; (iv) C_c² is rendered as ContDiff ℝ 2 + tsupport ⊆ [−L/2, L/2] (compact). -/
def ExplicitFormulaPaper (Z : ZeroConfig) : Prop :=
  ∀ (L : ℝ), 0 < L → ∀ (f g : ℝ → ℂ), ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    tsupport f ⊆ Icc (-(L / 2)) (L / 2) → tsupport g ⊆ Icc (-(L / 2)) (L / 2) →
    Summable (fun ρ : Z.carrier => Z.Wsummand f g ρ) ∧
    Integrable (fun τ : ℝ => paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ)) ∧
    Z.W f g = ∫ τ : ℝ, paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ)

/-! ## H-RvM — Riemann–von Mangoldt + local zero count  [eq:RvM], [prop:tail] first line -/

/-- **H-RvM**.
* main [eq:RvM], verbatim: "By the Riemann–von Mangoldt formula, with l := log(T/2π),
  N(T,2T) = (T/2π)(l + 2 log 2 − 1) + O(log T)."  (ell1 T = l T + 2 log 2 − 1.) Source: [Tit86, Thm 9.4].
* local_count [prop:tail]: "Let A₀ ≥ 1 be an absolute constant such that N(t+1) − N(t) ≤ A₀ log(t+3)
  for all t ≥ 0" — "classical [Tit86, Theorem 9.2]".
  Deviation (deliberate): stated two-sided, for all real t with
  log(|t|+3), i.e. also for windows of negative ordinate. The paper's proof of prop:tail bounds the
  zeros with γ ≤ 0 using the γ ↦ −γ symmetry of the zero set, which it states in [subsec:weil] but
  which is not a field of ZeroConfig; the two-sided local count is an equally classical consequence
  of [Tit86, 9.2] + that symmetry and removes the extra seam obligation. -/
structure RiemannVonMangoldt (Z : ZeroConfig) : Prop where
  main : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(Z.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T
  local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)

/-! ## H-cheb — Chebyshev–Mertens  [lem:cheb], [eq:cheb1], [eq:cheb2] -/

/-- **H-cheb** [lem:cheb], verbatim: "For x ≥ 2,
  Σ_{n≤x} Λ(n) ≪ x,  Σ_{n≤x} Λ(n)/√n ≤ 3√x (x ≥ x₀),  Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x,
  Σ_{n≤x} Λ(n)² ≪ x log x,                                                          [eq:cheb1]
  Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x),  Σ_{n≤x} Λ(n)²/n (log x − log n) = (log x)³/6 + O((log x)²).
                                                                                    [eq:cheb2]"
Source: [MV07, §2.2] (Chebyshev, Mertens; partial summation). Sums are over n ∈ Finset.Ioc 0 ⌊x⌋₊
(Mathlib's Chebyshev.psi indexing); Λ = ArithmeticFunction.vonMangoldt; the n = 1 terms vanish
(Λ 1 = 0; in cheb1c Lean reads 0/0 as 0). Each ≪ / O(·) is an ∃ C; cheb1b keeps the paper's
literal constant 3 with threshold x₀. Zeta23/Chebyshev.lean proves these fields. -/
structure ChebyshevMertens : Prop where
  cheb1a : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ≤ C * x
  cheb1b : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x
  cheb1c : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) ≤ C * Real.sqrt x / Real.log x
  cheb1d : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 ≤ C * x * Real.log x
  cheb2a : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n - Real.log x ^ 2 / 2| ≤ C * Real.log x
  cheb2b : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6|
      ≤ C * Real.log x ^ 2

/-! ## H-MV — Montgomery–Vaughan weighted Hilbert inequality  [lem:MV] -/

/-- The weighted ("generalised") Hilbert inequality with constant C [lem:MV], verbatim:
"Let λ_1,…,λ_R be distinct real numbers, δ_r := min_{s≠r} |λ_r − λ_s|, and x_r, z_r ∈ ℂ. Then
  |Σ_{r≠s} x_r conj(z_s)/(λ_r − λ_s)| ≤ (3π/2) (Σ_r |x_r|²/δ_r)^{1/2} (Σ_r |z_r|²/δ_r)^{1/2}."
Source: [MV74, Theorem 2] for z = x (the paper citation); the bilinear form is derived in the paper by a
3-line operator-norm argument. "Any absolute constant in place of 3π/2 would suffice below."
Shape notes: index set = any Fintype ι with DecidableEq; distinctness = injectivity of freq; instead
of δ_r := min_{s≠r}|λ_r−λ_s| (undefined for R = 1) we allow ANY admissible weights 0 < δ_r ≤
|λ_r − λ_s| (s ≠ r) — equivalent to the paper's statement since the right side is antitone in δ.
The bilinear (x,z) form is assumed directly (it is what prop:PP/prop:cross consume). -/
def MVHilbert (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x z : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (z s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * Real.sqrt (∑ r, ‖x r‖ ^ 2 / δ r) * Real.sqrt (∑ r, ‖z r‖ ^ 2 / δ r)

/-! ## H-Γ — Stirling-type facts for μ  [eq:mufacts], [eq:muints] -/

/-- **H-Γ** [eq:mufacts], verbatim: "μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1,
  μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²),  μ'(τ) ≪ |τ|⁻¹  (|τ| ≥ 1)"
("(eq:mufacts) is Stirling's formula and Re Γ'/Γ(σ+it) = −γ_E + Σ_{n≥0}(1/(n+1) − (n+σ)/((n+σ)²+t²))"),
and the pure-Γ halves of [eq:muints]:
  "∫_T^{2T} μ(τ) dτ = Tℓ₁/(2π) + O(1/T)",   "∫_T^{2T} μ(τ)² dτ = (Tℓ₁²/4π²)(1 + O(l⁻²))".
(The remaining clause of [eq:muints], "= N(T,2T) + O(l)", is [eq:RvM] and is NOT restated here.)
Source: Stirling for Γ'/Γ (e.g. [MV07, App. C]). This structure only STATES the facts; they are
proved in Zeta23/GammaFacts/Complete.lean (`gammaFacts : GammaFacts`, via the digamma series and a
vertical-line Stirling estimate in Zeta23/GammaFacts/*). "increasing" is rendered as MonotoneOn on [0,∞)
(nondecreasing), which is all prop:trace's Riemann-sum comparison uses. -/
structure GammaFacts : Prop where
  even : ∀ τ : ℝ, mu (-τ) = mu τ
  smooth : ContDiff ℝ ∞ mu
  monotoneOn : MonotoneOn mu (Ici 0)
  mu_zero_le : ∀ τ : ℝ, mu 0 ≤ mu τ
  neg_one_lt_mu_zero : -1 < mu 0
  stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2
  deriv_bound : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv mu τ| ≤ C / |τ|
  int_mu : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T
  int_mu_sq : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2

/-! ## The bundle -/

/-- The published analytic inputs of the paper ([thm:A]: "besides these it uses only Weil's explicit
formula, Stirling's formula for Γ'/Γ, the Riemann–von Mangoldt formula (eq:RvM) and the bound
N(t+1)−N(t) ≪ log(t+3)" + "Chebyshev–Mertens estimates … and the Montgomery–Vaughan generalised
Hilbert inequality"), stated for an abstract zero configuration Z. Every headline theorem takes
(H : PaperInputs Z) explicitly. -/
structure PaperInputs (Z : ZeroConfig) : Prop where
  /-- H-EF  [prop:EF]/[eq:EF] -/
  EF : ExplicitFormulaPaper Z
  /-- H-RvM [eq:RvM] + local count [prop:tail] -/
  RvM : RiemannVonMangoldt Z
  /-- H-cheb [lem:cheb] -/
  cheb : ChebyshevMertens
  /-- H-MV [lem:MV], ∃ absolute constant -/
  MV : ∃ C : ℝ, 0 < C ∧ MVHilbert C
  /-- H-Γ [eq:mufacts] + Γ-halves of [eq:muints] -/
  Gamma : GammaFacts

end Zeta23
