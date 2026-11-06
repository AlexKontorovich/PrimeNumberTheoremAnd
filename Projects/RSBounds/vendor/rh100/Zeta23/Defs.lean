module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs.lean — fixed data of the paper.

Reference text: the paper "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line". Bracketed labels [eq:foo] below are the paper's own labels.

Design (ζ-free abstract layer): nothing in this file mentions
riemannZeta. The zeros enter only through the abstract structure ZeroConfig
("every locally finite multiset of points in the strip 0<β<1 that is invariant under ρ ↦ 1−ρ̄",
paper end of §4). Only Zeta23/Statement.lean instantiates ZeroConfig from Mathlib's ζ.
-/
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Matrix.Basic

@[expose] public section

open scoped BigOperators ArithmeticFunction
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/-! ## 0. Fourier convention dictionary  [Notation], [subsec:weil]

Paper: "Fourier transforms are f̂(τ) := ∫_ℝ f(u) e^{iτu} du, so that ∫ f ḡ = (1/2π) ∫ f̂ conj(ĝ)
and (f∗g)^ = f̂ ĝ."  and  "For f ∈ C_c²(ℝ) put h_f(z) := f̂(z) = ∫ f(u) e^{izu} du, an entire
function".  Mathlib's Real.fourierIntegral 𝓕 is ∫ f(v) e^{−2πi v ξ} dv, so for real τ:
    paperFT f τ = 𝓕 f (−τ / (2π)).
All paper-side statements use paperFT; conversion to 𝓕 happens only inside proofs. -/

/-- Paper Fourier transform / h_f :  paperFT f z = ∫ u, f u * exp (I * z * u)  for complex z
([Notation]; [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u)e^{izu} du"). -/
def paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ))

/-! ## 1. Scalars depending on T only  [Notation], [eq:RvM], [eq:Fdef] -/

/-- l := log(T/2π)  [Notation]. -/
def l (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi))

/-- ℓ₁ := l + 2 log 2 − 1, "so that N(T,2T) = Tℓ₁/2π + O(l)"  [Notation]. -/
def ell1 (T : ℝ) : ℝ := l T + 2 * Real.log 2 - 1

/-- H(λ) := 2 − 1/λ − λ/3  [eq:Fdef]; H(1) = 2/3. -/
def Hfun (x : ℝ) : ℝ := 2 - 1 / x - x / 3

/-- F(λ) := λ / (1 + λ²/3)  [eq:Fdef]; F(1) = 3/4. -/
def Ffun (x : ℝ) : ℝ := x / (1 + x ^ 2 / 3)

/-- D₀ := T^{1/2}  [eq:D0]. -/
def D0 (T : ℝ) : ℝ := Real.sqrt T

/-- I := [T, 2T]  [Notation]. -/
def Iwin (T : ℝ) : Set ℝ := Icc T (2 * T)

/-- I' := (T − D₀, 2T + D₀]  [eq:D0]. -/
def Iprime (T : ℝ) : Set ℝ := Ioc (T - D0 T) (2 * T + D0 T)

lemma Hfun_one : Hfun 1 = 2 / 3 := by norm_num [Hfun]
lemma Ffun_one : Ffun 1 = 3 / 4 := by norm_num [Ffun]

/-! ## 2. The densities μ, Π_X, P_X, ν_X  [eq:mudef]–[eq:nudef]

Paper, verbatim: "Define, for τ ∈ ℝ and X = e^L > 1, s := 1/2 + iτ,
  μ(τ)   := (1/2π) Re Γ'/Γ(1/4 + iτ/2) − (log π)/(2π),                      [eq:mudef]
  Π_X(τ) := 1/(2π(1/4+τ²)) + (1/π) Re (X^s − 1)/s,                           [eq:Pidef]
  P_X(τ) := −(1/π) Σ_{n≤X} Λ(n)/√n · cos(τ log n),                           [eq:Pdef]
  ν_X    := μ + Π_X + P_X."                                                   [eq:nudef]
-/

/-- μ(τ) := (1/2π)·Re (Γ'/Γ)(1/4 + iτ/2) − log π /(2π)   [eq:mudef].
Complex.digamma = logDeriv Gamma = Γ'/Γ (Mathlib Gamma/Digamma.lean). -/
def mu (τ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re
    - Real.log Real.pi / (2 * Real.pi)

/-- Π_X(τ) := 1/(2π(1/4+τ²)) + (1/π)·Re((X^s − 1)/s),  s = 1/2 + iτ  [eq:Pidef]
("the terms h_k(±i/2) coming from the pole of ζ … rewritten as the density Π_X"). -/
def PiX (X : ℝ) (τ : ℝ) : ℝ :=
  let s : ℂ := 1 / 2 + Complex.I * τ
  1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) + (1 / Real.pi) * (((X : ℂ) ^ s - 1) / s).re

/-- P_X(τ) := −(1/π) Σ_{n ≤ X} Λ(n) n^{−1/2} cos(τ log n)  [eq:Pdef]. Sum over n ∈ Finset.Ioc 0 ⌊X⌋₊
(same indexing as Mathlib's Chebyshev.psi; Λ vanishes off prime powers; the n = 1 term is 0). -/
def PX (X : ℝ) (τ : ℝ) : ℝ :=
  -(1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n) / Real.sqrt n * Real.cos (τ * Real.log n)

/-- ν_X := μ + Π_X + P_X  [eq:nudef]. -/
def nuX (X : ℝ) (τ : ℝ) : ℝ := mu τ + PiX X τ + PX X τ

/-! ## 3. Abstract zero configurations  [Results], [subsec:weil], §4 closing paragraph -/

/-- γ_ρ := (ρ − 1/2)/i = γ − i(β − 1/2), "so that ρ = 1/2 + iγ_ρ, |Im γ_ρ| < 1/2, and γ_ρ ∈ ℝ iff
β = 1/2"  [Notation]. -/
def gammaOf (ρ : ℂ) : ℂ := (ρ - 1 / 2) / Complex.I

/-- The reflection ρ ↦ 1 − ρ̄ (same ordinate γ, mirrored β)  [subsec:weil]. -/
def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- An abstract zero configuration: a set (carrier) of DISTINCT points ρ = β+iγ in the closed
strip 0 ≤ β ≤ 1 (the instances built from the zeros of ζ and of L(s,χ) lie in the open strip) with
multiplicities mult ρ ≥ 1, locally finite in the ordinate, and
invariant under ρ ↦ 1−ρ̄ with equal multiplicity. Paper §4 (after prop:zeroside), verbatim:
"Inequalities (eq:zeroside) hold for every locally finite multiset of points in the strip 0<β<1
that is invariant under ρ ↦ 1−ρ̄ and satisfies N(t+1)−N(t) ≪ log(t+3); they contain no
arithmetic."  [subsec:weil]: "The multiset {(γ_ρ,m_ρ)} is invariant under γ ↦ γ̄ (i.e. ρ ↦ 1−ρ̄;
multiplicities agree …)".  The quantitative local count N(t+1)−N(t) ≤ A₀ log(t+3) is not part of
this structure; it is a field of PaperInputs (H-RvM) in Zeta23/Hypotheses.lean.
Distinct points (the set) and multiplicities (the function) are deliberately separate objects. -/
structure ZeroConfig where
  /-- the set 𝒵 of distinct zeros -/
  carrier : Set ℂ
  /-- multiplicity m_ρ (value irrelevant off carrier) -/
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ carrier, 1 ≤ mult ρ
  strip : ∀ ρ ∈ carrier, 0 ≤ ρ.re ∧ ρ.re ≤ 1
  reflect_mem : ∀ ρ ∈ carrier, reflect ρ ∈ carrier
  mult_reflect : ∀ ρ ∈ carrier, mult (reflect ρ) = mult ρ
  /-- local finiteness in the ordinate: finitely many zeros with T₁ < γ ≤ T₂ -/
  finite_window : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

namespace ZeroConfig

variable (Z : ZeroConfig)

/-- {ρ ∈ 𝒵 : T₁ < γ ≤ T₂}, γ = Im ρ (positive-ordinate window convention of [Results]; NOT |γ|). -/
def window (T₁ T₂ : ℝ) : Set ℂ := Z.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- on-line points: β = 1/2. -/
def onLine : Set ℂ := {ρ | ρ.re = 1 / 2}

/-- simple points: m_ρ = 1. -/
def simple : Set ℂ := {ρ | Z.mult ρ = 1}

/-- N(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂} counted WITH multiplicity  [Results]. -/
def N (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ

/-- N_d(T₁,T₂) := same, each distinct point counted once  [Results]. -/
def Nd (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂).ncard

/-- N₀(T₁,T₂) := zeros on the critical line with T₁ < γ ≤ T₂, WITH multiplicity  [Results]. -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ onLine, Z.mult ρ

/-- N₀*(T₁,T₂) := zeros on the critical line with T₁ < γ ≤ T₂, WITHOUT multiplicity  [Results]. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ onLine).ncard

/-- N₀ˢ(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂, β = 1/2, m_ρ = 1}  [Results]. -/
def N0s (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ onLine ∩ Z.simple).ncard

/-- Nˢ(T₁,T₂) := number of simple zeros (any β) with T₁ < γ ≤ T₂  [Results]. -/
def Ns (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ Z.simple).ncard

/-- Summand of Weil's form: m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))  [eq:Wdef]. -/
def Wsummand (f g : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  (Z.mult ρ : ℂ) * paperFT f (gammaOf ρ) * (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (gammaOf ρ)))

/-- W(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)), "Σ_ρ runs over the DISTINCT nontrivial zeros (of
either sign of γ) and the multiplicity is written explicitly"  [eq:Wdef]. As a tsum over the
subtype of carrier; absolute convergence is part of hypothesis H-EF. -/
def W (f g : ℝ → ℂ) : ℂ := ∑' ρ : Z.carrier, Z.Wsummand f g ρ

end ZeroConfig

/-! ## 4. The test family  [subsec:family] -/

/-- "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)"  [subsec:family]. -/
structure TaperProfile (ϱ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 3 ϱ
  monotone : Monotone ϱ
  eq_zero : ∀ x ≤ 0, ϱ x = 0
  eq_one : ∀ x ≥ 1, ϱ x = 1

/-- Fixed (T-independent) parameters: the profile ϱ, the exponent λ (lam; X = (T/2π)^λ), and the
ramp width w ([eq:wrange]: 1 ≤ w ≤ L/8; §6 takes w := 1). T is always a separate argument. -/
structure Params where
  ϱ : ℝ → ℝ
  lam : ℝ
  w : ℝ

/-- Standing assumptions on the fixed parameters: ϱ a taper profile, 0 < λ ≤ 1, w ≥ 1.
(The upper bound w ≤ L/8 of [eq:wrange] depends on T and is stated where used.) -/
structure Params.Valid (P : Params) : Prop where
  taper : TaperProfile P.ϱ
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w

namespace Params

variable (P : Params) (T : ℝ)

/-- L := λ·l  [Notation]. -/
def L : ℝ := P.lam * l T

/-- X := e^L = (T/2π)^λ  [Notation]. -/
def X : ℝ := Real.exp (P.L T)

/-- λ₁ := L/ℓ₁ = λ + O(1/l)  [Notation], [eq:ratio]. Not the same as λ. -/
def lam1 : ℝ := P.L T / ell1 T

/-- grid step h := 2π/L  [eq:fk]. -/
def hgrid : ℝ := 2 * Real.pi / P.L T

/-- d := ⌊T/h⌋ = ⌊LT/2π⌋  [eq:fk]. -/
def d : ℕ := ⌊P.L T * T / (2 * Real.pi)⌋₊

/-- τ_k := T + k h (k ∈ ℤ)  [eq:fk]. -/
def tau (k : ℤ) : ℝ := T + k * P.hgrid T

/-- the taper φ(u) := ϱ((L/2 − |u|)/w)  [eq:phidef]; supp φ = [−L/2, L/2] exactly. -/
def phi (u : ℝ) : ℝ := P.ϱ ((P.L T / 2 - |u|) / P.w)

/-- a := L⁻¹ ∫ φ²  [eq:abdef]. -/
def a : ℝ := (P.L T)⁻¹ * ∫ u : ℝ, (P.phi T u) ^ 2

/-- b := L⁻¹ ∫ φ⁴  [eq:abdef]. -/
def b : ℝ := (P.L T)⁻¹ * ∫ u : ℝ, (P.phi T u) ^ 4

/-- φ̂(z) for complex z (paper convention, = h_φ(z)). -/
def phiHat (z : ℂ) : ℂ := paperFT (fun u => (P.phi T u : ℂ)) z

/-- φ̂ on the real line as a real number ("φ̂ and Φ are real, even, entire"); = Re of phiHat.
That the imaginary part vanishes is proved in Taper.lean, not assumed. -/
def phiHatR (r : ℝ) : ℝ := (P.phiHat T (r : ℂ)).re

/-- Φ := (φ²)^  [eq:PhigA], complex argument. -/
def Phi (z : ℂ) : ℂ := paperFT (fun u => (((P.phi T u) ^ 2 : ℝ) : ℂ)) z

/-- Φ on the real line as a real number; Φ(0) = aL. -/
def PhiR (r : ℝ) : ℝ := (P.Phi T (r : ℂ)).re

/-- (v ⋆ v)(y) := ∫ v(u) v(u+y) du  [eq:PhigA]. -/
def autocorr (v : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, v u * v (u + y)

/-- g := φ² ⋆ φ²  [eq:PhigA]; Φ² = ĝ on ℝ, g(0) = bL. -/
def g (y : ℝ) : ℝ := autocorr (fun u => (P.phi T u) ^ 2) y

/-- A_φ := φ ⋆ φ  [eq:PhigA]; φ̂² = (A_φ)^. -/
def Aphi (y : ℝ) : ℝ := autocorr (P.phi T) y

/-- c_ϱ := 4‖ϱ'‖_∞ + 4‖ϱ''‖₁ (≥ 4)  [eq:phinorms]. -/
def crho : ℝ :=
  4 * (⨆ x : ℝ, |deriv P.ϱ x|) + 4 * ∫ x : ℝ, |deriv (deriv P.ϱ) x|

/-- ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))  [eq:psidef]; at r = 0 the paper's value is L (2/0 = ∞), which
Lean's 2/0 = 0 would get wrong, hence the explicit case. -/
def psi (r : ℝ) : ℝ := if r = 0 then P.L T else min (P.L T) (min (2 / |r|) (P.crho / (P.w * r ^ 2)))

/-- f_k(u) := φ(u) e^{−iτ_k u}  [eq:fk]; h_{f_k}(z) = φ̂(z − τ_k). -/
def fk (k : ℤ) (u : ℝ) : ℂ := (P.phi T u : ℂ) * Complex.exp (-(Complex.I * P.tau T k * u))

/-- ℰ_T := w/L + (l² + X) log l /(T l) + T^{λ/2 − 1}  [thm:traces]. -/
def calE : ℝ :=
  P.w / P.L T + (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) + T ^ (P.lam / 2 - 1)

/-! ### The prime-side matrix (second expression in [eq:Gdef]) -/

/-- G_{kl} via the PRIME side: ∫_ℝ φ̂(τ−τ_k) φ̂(τ−τ_l) ν_X(τ) dτ, X = e^L  [eq:Gdef, 2nd expression],
for arbitrary integer indices k, l. Real-valued. -/
def Gentry (k l : ℤ) : ℝ :=
  ∫ τ : ℝ, P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) * nuX (P.X T) τ

/-- The d×d prime-side matrix G = (G_{kl})_{0≤k,l<d} as a complex matrix (entries are real;
complex so that RHLinalg's RCLike lemmas and the zero-side matrix share one type). -/
def Gp : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => (P.Gentry T (k : ℤ) (l : ℤ) : ℂ)

/-- tr G̃ as the real number L⁻¹ Σ_{k<d} G_{kk} (what §5 computes)  [prop:trace]. -/
def trGtilde : ℝ := (P.L T)⁻¹ * ∑ k : Fin (P.d T), P.Gentry T k k

/-- tr G̃² = Σ_{k,l<d} G̃_{kl}² (= ‖G̃‖_F², G real symmetric)  [sec:prime intro]. -/
def trGtildeSq : ℝ := (P.L T)⁻¹ ^ 2 * ∑ k : Fin (P.d T), ∑ l : Fin (P.d T), P.Gentry T k l ^ 2

/-- scaling to tilde units M ↦ M/L  [eq:Gdef], [eq:AE]  (G̃, Ã, Ẽ). -/
def tilde {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ := ((P.L T)⁻¹ : ℂ) • M

/-- scaling to hat units M ↦ M/(aL²)  [eq:hatunits]  (Ĝ, Â, Ê). Not to be mixed with tilde
units. -/
def hat {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ := ((P.a T * P.L T ^ 2)⁻¹ : ℂ) • M

end Params

/-! ### The zero-side matrices  [eq:Gdef] first expression, [eq:AE], §4 Block structure -/

namespace ZeroConfig

/-- zero-side summand m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l). -/
def Gsummand (Z : ZeroConfig) (P : Params) (T : ℝ) (k l : ℤ) (ρ : ℂ) : ℂ :=
  (Z.mult ρ : ℂ) * P.phiHat T (gammaOf ρ - P.tau T k) * P.phiHat T (gammaOf ρ - P.tau T l)

/-- G_{kl} := W(f_k,f_l) = Σ_ρ m_ρ φ̂(γ_ρ−τ_k) φ̂(γ_ρ−τ_l)  [eq:Gdef, 1st expression] (zero side;
tsum over all distinct zeros). H-EF gives Z.Gz P T = P.Gp T. -/
def Gz (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => ∑' ρ : Z.carrier, Z.Gsummand P T k l ρ

/-- 𝒵(I') := distinct zeros with ordinate γ ∈ I' = (T−D₀, 2T+D₀]  [§4 Block structure]. -/
def ZIprime (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.window (T - D0 T) (2 * T + D0 T)

/-- A_{kl} := Σ_{ρ : γ ∈ I'} m_ρ φ̂(γ_ρ−τ_k) φ̂(γ_ρ−τ_l)  [eq:AE] (a FINITE sum, finsum). -/
def Az (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => ∑ᶠ ρ ∈ Z.ZIprime T, Z.Gsummand P T k l ρ

/-- E := G − A  [eq:AE] (the tail: zeros with γ ∉ I', INCLUDING negative ordinates). -/
def Ez (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  Z.Gz P T - Z.Az P T

/-- 𝒮₁: β = 1/2 and m_ρ = 1, within 𝒵(I'). s₁ := #𝒮₁  [§4 Block structure]. -/
def S1 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ Z.simple
/-- 𝒮₂: β = 1/2 and m_ρ ≥ 2, within 𝒵(I'). s₂ := #𝒮₂. -/
def S2 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ {ρ | 2 ≤ Z.mult ρ}
/-- off-line points of 𝒵(I') (β ≠ 1/2); 𝒫 = unordered pairs {ρ, 1−ρ̄} of these, #offLine = 2p. -/
def offLine (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ {ρ | ρ.re ≠ 1 / 2}

/-- s₁ := #𝒮₁. -/
def s1 (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.S1 T).ncard
/-- s₂ := #𝒮₂. -/
def s2 (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.S2 T).ncard
/-- p := number of unordered off-line pairs {ρ,1−ρ̄} in 𝒵(I'); #offLine = 2p. -/
def p (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.offLine T).ncard / 2

/-- N(I') := N(T−D₀, 2T+D₀)  [eq:Ncount]. -/
def NIprime (Z : ZeroConfig) (T : ℝ) : ℕ := Z.N (T - D0 T) (2 * T + D0 T)
/-- N_on(I') := Σ_{ρ ∈ 𝒮₁ ∪ 𝒮₂} m_ρ  [§4]. -/
def NonIprime (Z : ZeroConfig) (T : ℝ) : ℕ := Z.N0 (T - D0 T) (2 * T + D0 T)

end ZeroConfig

end Zeta23
