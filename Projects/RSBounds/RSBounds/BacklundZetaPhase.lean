/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in licenses/Gersh-LICENSE.

The horizontal phase lift is selectively adapted from
`gersh/ternary-goldbach-lean` commit 27df23af6a712895f22204d0d81102baa74f0ebe,
BacklundArgSweep.lean §§0–2, BacklundArgVarAssembly.lean,
BacklundArgVarVertical.lean, and ZetaInterlacingAssembly.lean §1.
The quantitative reflection bridge reuses our checked IEANTN gamma estimates.
-/
import RSBounds.BacklundCountDefinitions
import RSBounds.BacklundGammaReflection
import RSBounds.BacklundPairedPower

/-!
# An actual continuous horizontal zeta phase

At a nonzero ordinate-free height, the phase is defined by integrating the
imaginary logarithmic derivative. Its polar identity is proved by a real
integrating factor and the zero-derivative constancy theorem. No argument
lifting, zero-crossing, zero-count, or phase identity is assumed.

The principal argument at the anchor is used only to set the horizontal
phase's additive constant. We do not identify it with the continuous vertical
argument at the anchor; all reflection estimates involve phase differences.
-/

noncomputable section
open Complex Real MeasureTheory
open scoped Topology ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundZetaPhase
open BacklundCountIdentity

lemma riemannZeta_horizontal_ne_zero {T : ℝ} (hgood : zetaGoodHeight T)
    (σ : ℝ) : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0 := by
  intro h
  have := hgood _ h
  simp at this

lemma hasDerivAt_horizontal_line (T σ : ℝ) :
    HasDerivAt (fun u : ℝ => (u : ℂ) + T * Complex.I) 1 σ := by
  have h : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 σ :=
    Complex.ofRealCLM.hasDerivAt (x := σ)
  simpa using h.add_const ((T : ℂ) * Complex.I)

lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

/-! ## §0  Horizontal derivative & continuity for `T ≠ 0` -/

/-- For `T ≠ 0`, the point `σ + iT` is not the pole `s = 1`. -/
lemma horizontal_ne_one_of_ne_zero {T : ℝ} (hT : T ≠ 0) (σ : ℝ) :
    (σ : ℂ) + T * Complex.I ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
    Complex.one_im, zero_add] at him
  exact hT him

/-- `σ ↦ ζ(σ+iT)` has derivative `ζ'(σ+iT)` for `T ≠ 0`. -/
lemma hasDerivAt_zeta_horiz {T : ℝ} (hT : T ≠ 0) (σ : ℝ) :
    HasDerivAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I))
      (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) σ := by
  have hz : HasDerivAt riemannZeta
      (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) ((σ : ℂ) + T * Complex.I) :=
    (differentiableAt_riemannZeta (horizontal_ne_one_of_ne_zero hT σ)).hasDerivAt
  refine (hz.scomp σ (hasDerivAt_horizontal_line T σ)).congr_deriv ?_
  exact one_smul ℝ _

/-- The `ℂ`-valued log-derivative `σ ↦ (ζ'/ζ)(σ+iT)` is continuous on ℝ at an
ordinate-free height (`T ≠ 0`, no zero on the line). -/
lemma continuous_logDeriv_horiz {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) :
    Continuous (fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)) := by
  rw [continuous_iff_continuousAt]; intro σ
  have hline : ContinuousAt (fun u : ℝ => (u : ℂ) + T * Complex.I) σ :=
    (Complex.continuous_ofReal.add continuous_const).continuousAt
  have hana : AnalyticAt ℂ riemannZeta ((σ : ℂ) + T * Complex.I) :=
    analyticAt_riemannZeta_of_ne_one (horizontal_ne_one_of_ne_zero hT σ)
  have hζ : ContinuousAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I)) σ :=
    ContinuousAt.comp (g := riemannZeta) (f := fun u : ℝ => (u : ℂ) + T * Complex.I)
      hana.continuousAt hline
  have hζ' : ContinuousAt (fun u : ℝ => deriv riemannZeta ((u : ℂ) + T * Complex.I)) σ :=
    ContinuousAt.comp (g := deriv riemannZeta) (f := fun u : ℝ => (u : ℂ) + T * Complex.I)
      hana.deriv.continuousAt hline
  have hne := riemannZeta_horizontal_ne_zero hgood σ
  have : ContinuousAt (fun u : ℝ =>
      deriv riemannZeta ((u : ℂ) + T * Complex.I) /
        riemannZeta ((u : ℂ) + T * Complex.I)) σ := hζ'.div hζ hne
  simpa only [logDeriv_apply] using this

/-! ## §1  The continuous argument and the auxiliary constant function -/

/-- **The continuous argument** of `ζ` along the horizontal segment at height `T`,
anchored at `σ = a`:  `θ(σ) = arg ζ(a+iT) + ∫_a^σ Im((ζ'/ζ)(u+iT)) du`. -/
def zetaHArg (T a σ : ℝ) : ℝ :=
  (riemannZeta ((a : ℂ) + T * Complex.I)).arg
    + ∫ u in a..σ, (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im

/-- The real integrating-factor exponent `∫_a^σ Re((ζ'/ζ)(u+iT)) du`. -/
def zetaHReInt (T a σ : ℝ) : ℝ :=
  ∫ u in a..σ, (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).re

/-- The rotated function `Ψ(σ) = ζ(σ+iT)·exp(-iθ(σ))`. -/
def zetaHPsi (T a σ : ℝ) : ℂ :=
  riemannZeta ((σ : ℂ) + T * Complex.I) * Complex.exp (-(zetaHArg T a σ : ℂ) * Complex.I)

/-- The auxiliary `G(σ) = Ψ(σ)·exp(-∫_a^σ Re(ζ'/ζ))`, which is constant. -/
def zetaHG (T a σ : ℝ) : ℂ :=
  zetaHPsi T a σ * Complex.exp (-(zetaHReInt T a σ : ℂ))

/-- FTC: `θ` is differentiable with derivative `Im((ζ'/ζ)(σ+iT))`. -/
lemma hasDerivAt_zetaHArg {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    HasDerivAt (zetaHArg T a)
      ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im) σ := by
  have hcont : Continuous (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im) :=
    Complex.continuous_im.comp (continuous_logDeriv_horiz hT hgood)
  have hFTC := (hcont.integral_hasStrictDerivAt a σ).hasDerivAt
  unfold zetaHArg
  exact hFTC.const_add _

/-- FTC: the integrating-factor exponent has derivative `Re((ζ'/ζ)(σ+iT))`. -/
lemma hasDerivAt_zetaHReInt {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    HasDerivAt (zetaHReInt T a)
      ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re) σ := by
  have hcont : Continuous (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).re) :=
    Complex.continuous_re.comp (continuous_logDeriv_horiz hT hgood)
  have hFTC := (hcont.integral_hasStrictDerivAt a σ).hasDerivAt
  unfold zetaHReInt
  exact hFTC

/-- `Ψ' = Re((ζ'/ζ)(σ+iT))·Ψ`  (the ODE with REAL log-derivative). -/
lemma hasDerivAt_zetaHPsi {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    HasDerivAt (zetaHPsi T a)
      (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * zetaHPsi T a σ) σ := by
  have hne := riemannZeta_horizontal_ne_zero hgood σ
  have hA : HasDerivAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I))
      (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) σ := hasDerivAt_zeta_horiz hT σ
  have hθ : HasDerivAt (zetaHArg T a)
      ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im) σ :=
    hasDerivAt_zetaHArg hT hgood a σ
  have hθc : HasDerivAt (fun s => ((zetaHArg T a s : ℝ) : ℂ))
      (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ)) σ := hθ.ofReal_comp
  have hexpArg : HasDerivAt (fun s => (-(zetaHArg T a s : ℂ)) * Complex.I)
      ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I) σ :=
    (hθc.neg).mul_const Complex.I
  have hB : HasDerivAt (fun s => Complex.exp ((-(zetaHArg T a s : ℂ)) * Complex.I))
      (Complex.exp ((-(zetaHArg T a σ : ℂ)) * Complex.I)
        * ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I)) σ :=
    hexpArg.cexp
  have hmul := hA.mul hB
  have hDL : logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)
        * riemannZeta ((σ : ℂ) + T * Complex.I)
      = deriv riemannZeta ((σ : ℂ) + T * Complex.I) := by
    rw [logDeriv_apply]; field_simp
  have hkey : logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)
        - ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ) * Complex.I
      = ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) := by
    have := Complex.re_add_im (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I))
    linear_combination -this
  have hval :
      deriv riemannZeta ((σ : ℂ) + T * Complex.I)
          * Complex.exp ((-(zetaHArg T a σ : ℂ)) * Complex.I)
        + riemannZeta ((σ : ℂ) + T * Complex.I)
          * (Complex.exp ((-(zetaHArg T a σ : ℂ)) * Complex.I)
            * ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I))
      = ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * zetaHPsi T a σ := by
    unfold zetaHPsi
    rw [← hDL]
    linear_combination
      (riemannZeta ((σ : ℂ) + T * Complex.I)
        * Complex.exp ((-(zetaHArg T a σ : ℂ)) * Complex.I)) * hkey
  rw [hval] at hmul
  exact hmul

/-- `G' = 0`:  the integrating factor cancels the `Re(ζ'/ζ)` leg. -/
lemma hasDerivAt_zetaHG {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    HasDerivAt (zetaHG T a) 0 σ := by
  have hP := hasDerivAt_zetaHPsi hT hgood a σ
  have hgg := hasDerivAt_zetaHReInt hT hgood a σ
  have hggc : HasDerivAt (fun s => ((zetaHReInt T a s : ℝ) : ℂ))
      (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)) σ := hgg.ofReal_comp
  have hExpG : HasDerivAt (fun s => Complex.exp (-(zetaHReInt T a s : ℂ)))
      (Complex.exp (-(zetaHReInt T a σ : ℂ))
        * (-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)))) σ :=
    (hggc.neg).cexp
  have hmul := hP.mul hExpG
  have hval :
      (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * zetaHPsi T a σ)
          * Complex.exp (-(zetaHReInt T a σ : ℂ))
        + zetaHPsi T a σ
          * (Complex.exp (-(zetaHReInt T a σ : ℂ))
            * (-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)))) = 0 := by ring
  rw [hval] at hmul
  exact hmul

/-! ## §2  The `cis` identity (`ζ = ‖ζ‖·e^{iθ}`) -/

/-- **The continuous-argument polar form.**  At an ordinate-free height `T ≠ 0`,
`ζ(σ+iT) = ‖ζ(σ+iT)‖ · exp(θ(σ)·I)` where `θ = zetaHArg T a`.  Proved fully. -/
theorem zeta_eq_norm_mul_cis {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    riemannZeta ((σ : ℂ) + T * Complex.I)
      = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ)
        * Complex.exp ((zetaHArg T a σ : ℂ) * Complex.I) := by
  -- G is constant
  have hGall : ∀ x, HasDerivAt (zetaHG T a) 0 x := fun x => hasDerivAt_zetaHG hT hgood a x
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun x => (hGall x).differentiableAt) (fun x => (hGall x).deriv) σ a
  -- evaluate `G a = ‖ζ(a+iT)‖`
  have hGa : zetaHG T a a = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) := by
    unfold zetaHG zetaHPsi zetaHReInt zetaHArg
    rw [intervalIntegral.integral_same, intervalIntegral.integral_same]
    simp only [Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one, add_zero]
    -- goal : ζ(a+iT) * exp(-(arg ζ(a+iT)) * I) = ‖ζ(a+iT)‖
    set w := riemannZeta ((a : ℂ) + T * Complex.I) with hw
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I w]
    rw [mul_assoc, ← Complex.exp_add]
    rw [show (Complex.arg w : ℂ) * Complex.I + (-(Complex.arg w : ℂ)) * Complex.I = 0 by ring]
    rw [Complex.exp_zero, mul_one]
  rw [hGa] at hconst
  -- unravel `G σ = ‖ζ(a+iT)‖`
  have hEne : Complex.exp (-(zetaHReInt T a σ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hGσ : zetaHPsi T a σ * Complex.exp (-(zetaHReInt T a σ : ℂ))
      = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) := hconst
  have hEinv : (Complex.exp (-(zetaHReInt T a σ : ℂ)))⁻¹
      = ((Real.exp (zetaHReInt T a σ)) : ℂ) := by
    rw [Complex.exp_neg, inv_inv, ← Complex.ofReal_exp]
  have hpsiσ : zetaHPsi T a σ
      = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) * ((Real.exp (zetaHReInt T a σ)) : ℂ) := by
    have h := eq_div_of_mul_eq hEne hGσ
    rwa [div_eq_mul_inv, hEinv] at h
  -- `Ψ σ` is a nonnegative real, of norm `‖ζ(σ+iT)‖`
  have hr_nonneg : 0 ≤ ‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (zetaHReInt T a σ) := by
    positivity
  have hpsiσ' : zetaHPsi T a σ
      = ((‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (zetaHReInt T a σ) : ℝ) : ℂ) := by
    rw [hpsiσ]; push_cast; ring
  have hnormψ : ‖zetaHPsi T a σ‖ = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ := by
    unfold zetaHPsi
    rw [norm_mul, Complex.norm_exp]
    simp
  have hr_eq : ‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (zetaHReInt T a σ)
      = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ := by
    have h := hnormψ
    rw [hpsiσ', Complex.norm_real, Real.norm_of_nonneg hr_nonneg] at h
    exact h
  have hpsiσ_norm : zetaHPsi T a σ = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ) := by
    rw [hpsiσ', hr_eq]
  -- rearrange the polar form
  have h1 : riemannZeta ((σ : ℂ) + T * Complex.I)
      * Complex.exp (-(zetaHArg T a σ : ℂ) * Complex.I)
      = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ) := by
    have := hpsiσ_norm; unfold zetaHPsi at this; exact this
  calc riemannZeta ((σ : ℂ) + T * Complex.I)
      = riemannZeta ((σ : ℂ) + T * Complex.I)
          * Complex.exp (-(zetaHArg T a σ : ℂ) * Complex.I)
          * Complex.exp ((zetaHArg T a σ : ℂ) * Complex.I) := by
        rw [mul_assoc, ← Complex.exp_add]
        rw [show (-(zetaHArg T a σ : ℂ) * Complex.I) + (zetaHArg T a σ : ℂ) * Complex.I = 0 by ring]
        rw [Complex.exp_zero, mul_one]
    _ = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ)
          * Complex.exp ((zetaHArg T a σ : ℂ) * Complex.I) := by rw [h1]

/-- **de Moivre with the continuous argument.**
`(ζ(σ+iT)^N).re = ‖ζ(σ+iT)‖^N · cos(N·θ(σ))`. -/
theorem re_zeta_pow_eq {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) (N : ℕ) :
    ((riemannZeta ((σ : ℂ) + T * Complex.I)) ^ N).re
      = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ ^ N
        * Real.cos ((N : ℝ) * zetaHArg T a σ) := by
  conv_lhs => rw [zeta_eq_norm_mul_cis hT hgood a σ]
  rw [mul_pow, ← Complex.exp_nat_mul,
    show (N : ℂ) * ((zetaHArg T a σ : ℂ) * Complex.I)
        = ((N : ℝ) * zetaHArg T a σ : ℝ) * Complex.I by push_cast; ring,
    ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Anchor-free increments** (mirror of `lChiHArg_sub_eq_integral`, but GLOBAL —
the good height makes `Im (ζ'/ζ)` continuous on the whole line): the increment of
the continuous argument `zetaHArg T a` between any two points is the horizontal
integral of `Im (ζ'/ζ)` between them (the anchor `arg ζ(a+iT)` cancels). -/
theorem zetaHArg_sub_eq_integral {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T)
    (a x y : ℝ) :
    zetaHArg T a x - zetaHArg T a y
      = ∫ σ in y..x, (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im := by
  have hcontIm : Continuous
      (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im) :=
    Complex.continuous_im.comp (continuous_logDeriv_horiz hT hgood)
  have hIx : IntervalIntegrable
      (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im)
      volume a x := hcontIm.intervalIntegrable a x
  have hIy : IntervalIntegrable
      (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im)
      volume a y := hcontIm.intervalIntegrable a y
  have hkey := intervalIntegral.integral_interval_sub_left hIx hIy
  unfold zetaHArg
  rw [← hkey]
  ring

/-- Global continuity of the anchored continuous argument at a good height. -/
theorem zetaHArg_continuous {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T)
    (a : ℝ) : Continuous (zetaHArg T a) :=
  continuous_iff_continuousAt.mpr fun σ =>
    (hasDerivAt_zetaHArg hT hgood a σ).continuousAt

/-- Conjugate zeta translates at real points. -/
theorem zeta_translate_conj (T x : ℝ) :
    riemannZeta ((x : ℂ) - T * Complex.I) =
      conj (riemannZeta ((x : ℂ) + T * Complex.I)) := by
  rw [← riemannZeta_conj]
  congr 1
  simp [sub_eq_add_neg]

/-- At real points, Backlund's symmetric power function is the real power. -/
theorem powerAverage_zeta_real (T x : ℝ) (n : ℕ) :
    BacklundJensen.powerAverage
      (fun z => riemannZeta (z + T * Complex.I))
      (fun z => riemannZeta (z - T * Complex.I)) n (x : ℂ) =
        ((riemannZeta ((x : ℂ) + T * Complex.I) ^ n).re : ℂ) :=
  BacklundJensen.powerAverage_center (zeta_translate_conj T x) n

/-- Every half-turn of the actual continuous phase is a genuine power zero. -/
theorem powerAverage_zeta_eq_zero_of_cos {T : ℝ} (hT : T ≠ 0)
    (hgood : zetaGoodHeight T) (a x : ℝ) (n : ℕ)
    (hcos : Real.cos ((n : ℝ) * zetaHArg T a x) = 0) :
    BacklundJensen.powerAverage
      (fun z => riemannZeta (z + T * Complex.I))
      (fun z => riemannZeta (z - T * Complex.I)) n (x : ℂ) = 0 := by
  rw [powerAverage_zeta_real, re_zeta_pow_eq hT hgood a x n, hcos, mul_zero,
    Complex.ofReal_zero]

/-- The phase's reflected increment is exactly the integrated zeta reflection
correction. The additive phase constant cancels. -/
theorem phase_reflection_eq_integral {T : ℝ} (hT : T ≠ 0)
    (hgood : zetaGoodHeight T) (a δ : ℝ) :
    (zetaHArg T a (1 / 2 + δ) - zetaHArg T a (1 / 2)) -
      (zetaHArg T a (1 / 2) - zetaHArg T a (1 / 2 - δ)) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ),
        BacklundGammaReflection.zetaReflectionDifference σ T := by
  let f : ℝ → ℝ := fun σ =>
    (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
  have hc : Continuous f :=
    Complex.continuous_im.comp (continuous_logDeriv_horiz hT hgood)
  have hrc : Continuous (fun σ => f (1 - σ)) :=
    hc.comp (continuous_const.sub continuous_id)
  rw [zetaHArg_sub_eq_integral hT hgood a (1 / 2 + δ) (1 / 2),
    zetaHArg_sub_eq_integral hT hgood a (1 / 2) (1 / 2 - δ)]
  change (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ) -
      (∫ σ in (1 / 2 - δ : ℝ)..(1 / 2), f σ) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ - f (1 - σ)
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (hrc.intervalIntegrable _ _)]
  congr 1
  convert (intervalIntegral.integral_comp_sub_left f (a := (1 / 2 : ℝ))
    (b := 1 / 2 + δ) 1).symm using 1 <;> congr 1 <;> ring

/-- Quantitative Backlund reflection for the actual zeta phase, reusing the
checked IEANTN digamma difference bounds. -/
theorem abs_phase_reflection_le {T δ : ℝ} (hT : 1 ≤ T)
    (hgood : zetaGoodHeight T) (a : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    |(zetaHArg T a (1 / 2 + δ) - zetaHArg T a (1 / 2)) -
      (zetaHArg T a (1 / 2) - zetaHArg T a (1 / 2 - δ))| ≤ 4 * δ ^ 2 / T := by
  rw [phase_reflection_eq_integral (by linarith : T ≠ 0) hgood a δ]
  exact BacklundGammaReflection.abs_integral_zetaReflectionDifference_le hT hδ0 hδ1
    (fun σ _ => ⟨riemannZeta_horizontal_ne_zero hgood σ,
      riemannZeta_horizontal_ne_zero hgood (1 - σ)⟩)

/-- A uniform `4/T` reflection error on all segments used in Rosser's disk. -/
theorem abs_phase_reflection_le_four_div {T δ : ℝ} (hT : 1 ≤ T)
    (hgood : zetaGoodHeight T) (a : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    |(zetaHArg T a (1 / 2 + δ) - zetaHArg T a (1 / 2)) -
      (zetaHArg T a (1 / 2) - zetaHArg T a (1 / 2 - δ))| ≤ 4 / T := by
  refine (abs_phase_reflection_le hT hgood a hδ0 hδ1).trans ?_
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ T)
  nlinarith

/-- Analyticity of the two translated zeta functions on Rosser's disk,
proved directly from the distance of the disk to the pole. -/
theorem analyticOnNhd_zeta_translate {T R : ℝ} (hRT : R < T) :
    AnalyticOnNhd ℂ (fun z => riemannZeta (z + T * Complex.I))
        (Metric.closedBall (5 / 4 : ℂ) R) ∧
      AnalyticOnNhd ℂ (fun z => riemannZeta (z - T * Complex.I))
        (Metric.closedBall (5 / 4 : ℂ) R) := by
  have him (z : ℂ) (hz : z ∈ Metric.closedBall (5 / 4 : ℂ) R) : |z.im| ≤ R := by
    have hd : ‖z - (5 / 4 : ℂ)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hi := Complex.abs_im_le_norm (z - (5 / 4 : ℂ))
    simpa using hi.trans hd
  constructor
  · intro z hz
    have hp : z + T * Complex.I ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp only [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re, Complex.one_im] at hh
      have hb := (abs_le.mp (him z hz)).1
      linarith
    exact (analyticAt_riemannZeta_of_ne_one hp).comp
      (f := fun w : ℂ => w + T * Complex.I) (x := z)
      (analyticAt_id.add analyticAt_const)
  · intro z hz
    have hp : z - T * Complex.I ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re, Complex.one_im] at hh
      have hb := (abs_le.mp (him z hz)).2
      linarith
    exact (analyticAt_riemannZeta_of_ne_one hp).comp
      (f := fun w : ℂ => w - T * Complex.I) (x := z)
      (analyticAt_id.sub analyticAt_const)

/-- Rosser's reflected Jensen bound for the actual horizontal zeta argument.
All phase and crossing hypotheses of the generic theorem are discharged here.
The remaining input is a common angular majorant for the two zeta translates. -/
theorem horizontal_argument_bound {T R : ℝ} {B : ℂ → ℝ}
    (hT : 1 ≤ T) (hgood : zetaGoodHeight T)
    (hR : 3 / 4 < R) (hRT : R < T)
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖riemannZeta (z + T * Complex.I)‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖riemannZeta (z - T * Complex.I)‖ ≤ Real.exp (B z)) :
    |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
      (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖riemannZeta ((5 / 4 : ℂ) + T * Complex.I)‖) /
          (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hf, hg⟩ := analyticOnNhd_zeta_translate hRT
  have h := BacklundPairedPower.argument_bound
    (f := fun z => riemannZeta (z + T * Complex.I))
    (g := fun z => riemannZeta (z - T * Complex.I))
    (θ := zetaHArg T (5 / 4)) (E := 4 / T) hR (by positivity) hf hg
    (by simpa using riemannZeta_horizontal_ne_zero hgood (5 / 4))
    (by simpa using zeta_translate_conj T (5 / 4)) hB hB0 hfb hgb
    (zetaHArg_continuous hT0.ne' hgood (5 / 4)).continuousOn
    (fun n x _ hx => powerAverage_zeta_eq_zero_of_cos hT0.ne' hgood (5 / 4) x n hx)
    (fun δ hδ0 hδ1 => abs_phase_reflection_le_four_div hT hgood (5 / 4) hδ0.le hδ1)
  rw [zetaHArg_sub_eq_integral hT0.ne' hgood (5 / 4) (5 / 4) (1 / 2)] at h
  convert h using 1 <;> ring

end TernaryGoldbach.RSBounds.BacklundZetaPhase
