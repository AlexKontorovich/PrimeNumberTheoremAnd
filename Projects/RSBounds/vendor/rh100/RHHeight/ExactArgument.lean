module

public import RHHeight.Skeleton
public import Zeta23.RvM.MainTerm

@[expose] public section

/-!
# `exact_argument`: the folded count of hunt #137 as an exact identity

The piece `ExactArgument` of `RHHeight/Skeleton.lean` (key `exact_argument`,
`hunts/rh_height_lean/PLAN.md` section 4.3). For heights `1 ≤ T₁ < T₂` at which
`Re ζ(σ + iT) > 0` on the whole horizontal leg `σ ∈ [1/2, 2]`,

    Ncount T₁ T₂ = ∫_{T₁}^{T₂} μ + (arg ζ(1/2 + iT₂) - arg ζ(1/2 + iT₁)) / π,

with no error term. Nothing in this file is numerical: the zeta half of the vendored folded
argument principle telescopes exactly once `log ζ` is a primitive along the whole half
contour. `count_eq_ten_of` (`RHHeight/Skeleton.lean`) turns this identity, with the
enclosures `GammaIncrement` and `HorizontalLegs`, into `Ncount 3 52 = 10`.

The route:

1. `goodHeight_of_re_pos`: positivity on a leg makes its height a `GoodHeight`, so the
   identity needs no `GoodHeight` hypothesis. A nontrivial zero at height `T` with
   `Re ρ ≥ 1/2` lies on the leg, where `ζ ≠ 0`. One with `Re ρ < 1/2` has the reflected zero
   `1 - conj ρ` (`zetaSeam.reflect_zero`) at the same height, with real part in `(1/2, 1)`.
2. `integral_logDeriv_horizontal`: where `Re ζ(σ + iT) > 0`, the value lies in the slit
   plane, so `σ ↦ log ζ(σ + iT)` is a primitive of `ζ'/ζ(σ + iT)` on `[1/2, 2]`, endpoints
   included (the pattern of the vendored `im_integral_le_two_pi`, with sign `+1` throughout),
   and the fundamental theorem of calculus evaluates the leg integral.
3. `integral_logDeriv_vertical`: on `σ = 2` the same, with the vendored primitive
   `hasDerivAt_log_riemannZeta_two`, valid at every height because `Re ζ(2 + it) > 0`.
4. `halfContour_logDeriv_riemannZeta`: the three legs telescope. The two corner values at
   `σ = 2` cancel and `log ζ(1/2 + iT₂) - log ζ(1/2 + iT₁)` is left; its imaginary part is the
   difference of the principal arguments (`Complex.log_im`). No winding correction appears,
   because a single continuous branch, the principal `Complex.log`, serves on every leg.
5. `exact_argument`: the vendored `N_eq_halfContour_completedZeta`,
   `halfContour_completedZeta_split` (`Zeta23/RvM/MainTerm.lean`) and `gamma_side`
   (`Zeta23/RvM/GammaSide.lean`).

`exact_argument` has exactly the type of the skeleton's `Prop` `ExactArgument`, and
`exact_argument_holds` records that match.

**Imports.** `Zeta23.RvM.MainTerm` brings 33 modules of the vendored `zeta23` package (its
import closure, which reaches `Zeta23.FromPNTPlus.StrongPNTPrefix` through `RvM.Backlund` and
`RvM.LocalCount`). The build order is in `hunts/rh_height_lean/PIECE_exact_argument.md`.
-/

open Complex Set

namespace RHHeight

open Zeta23 Zeta23.RvM

/-- **Good heights from positivity.** If `Re ζ(σ + iT) > 0` for every `σ ∈ [1/2, 2]`, no
nontrivial zero of `ζ` has ordinate `T`. -/
theorem goodHeight_of_re_pos {T : ℝ}
    (hleg : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T * I)).re) : GoodHeight T := by
  -- a zero at height `T` with real part in `[1/2, 1)` would sit on the leg
  have key : ∀ z : ℂ, IsNontrivialZero z → z.im = T → 1 / 2 ≤ z.re → False := by
    intro z hz hzim hzre
    have hmem : z.re ∈ Icc (1 / 2 : ℝ) 2 := ⟨hzre, by linarith [hz.2.2]⟩
    have hz' : (z.re : ℂ) + T * I = z := by
      apply Complex.ext <;> simp [hzim]
    have hpos := hleg z.re hmem
    rw [hz', hz.1] at hpos
    simp at hpos
  intro ρ hρ him
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with h | h
  · exact key ρ hρ him h
  · -- `Re ρ < 1/2`: the reflected zero `1 - conj ρ` has the same height and real part `> 1/2`
    refine key (reflect ρ) (zetaSeam.reflect_zero ρ hρ) ?_ ?_
    · simp [reflect, him]
    · simp [reflect]
      linarith

/-- **A horizontal leg.** If `Re ζ(σ + iT) > 0` on `[1/2, 2]`, then `log ζ(σ + iT)` is a
primitive of `ζ'/ζ(σ + iT)` there and the leg integral is a difference of logarithms. -/
theorem integral_logDeriv_horizontal {T : ℝ} (hT : T ≠ 0)
    (hleg : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T * I)).re) :
    ∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I) =
      Complex.log (riemannZeta (2 + T * I)) - Complex.log (riemannZeta (1 / 2 + T * I)) := by
  have hnz : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0 := by
    intro σ hσ h
    have hpos := hleg σ hσ
    rw [h] at hpos
    simp at hpos
  have hderiv : ∀ σ ∈ uIcc (1 / 2 : ℝ) 2,
      HasDerivAt (fun x : ℝ => Complex.log (riemannZeta (x + T * I)))
        (logDeriv riemannZeta (σ + T * I)) σ := by
    intro σ hσ
    rw [uIcc_of_le (by norm_num)] at hσ
    -- `Re ζ > 0` puts the value in the slit plane, where `Complex.log` is differentiable
    have h := (hasDerivAt_riemannZeta_horizontal hT σ).clog_real (Or.inl (hleg σ hσ))
    rwa [logDeriv_apply]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_logDeriv_horizontal hT hnz ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩)]
  push_cast
  rfl

/-- **The vertical leg `σ = 2`.** `log ζ(2 + it)` is a primitive of `ζ'/ζ(2 + it) · i` at
every height (vendored `hasDerivAt_log_riemannZeta_two`). -/
theorem integral_logDeriv_vertical (T₁ T₂ : ℝ) :
    (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I =
      Complex.log (riemannZeta (2 + T₂ * I)) - Complex.log (riemannZeta (2 + T₁ * I)) := by
  rw [← intervalIntegral.integral_mul_const]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_log_riemannZeta_two t)
    (continuous_logDeriv_riemannZeta_two.intervalIntegrable _ _)

/-- **The zeta half telescopes.** With `Re ζ > 0` on both horizontal legs, the half-contour
integral of `ζ'/ζ` is `log ζ(1/2 + iT₂) - log ζ(1/2 + iT₁)`: the corner values at `σ = 2`
cancel. -/
theorem halfContour_logDeriv_riemannZeta {T₁ T₂ : ℝ} (hT₁ : T₁ ≠ 0) (hT₂ : T₂ ≠ 0)
    (hleg₁ : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₁ * I)).re)
    (hleg₂ : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₂ * I)).re) :
    halfContour (logDeriv riemannZeta) T₁ T₂ =
      Complex.log (riemannZeta (1 / 2 + T₂ * I)) - Complex.log (riemannZeta (1 / 2 + T₁ * I)) := by
  unfold halfContour
  rw [integral_logDeriv_horizontal hT₁ hleg₁, integral_logDeriv_vertical,
    integral_logDeriv_horizontal hT₂ hleg₂]
  ring

/-- The imaginary part of the zeta half is the change of the principal argument between the
two left corners `1/2 + iT₁` and `1/2 + iT₂`. -/
theorem im_halfContour_logDeriv_riemannZeta {T₁ T₂ : ℝ} (hT₁ : T₁ ≠ 0) (hT₂ : T₂ ≠ 0)
    (hleg₁ : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₁ * I)).re)
    (hleg₂ : ∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₂ * I)).re) :
    (halfContour (logDeriv riemannZeta) T₁ T₂).im =
      (riemannZeta (1 / 2 + T₂ * I)).arg - (riemannZeta (1 / 2 + T₁ * I)).arg := by
  rw [halfContour_logDeriv_riemannZeta hT₁ hT₂ hleg₁ hleg₂, Complex.sub_im, Complex.log_im,
    Complex.log_im]

/-- **`exact_argument`.** For `1 ≤ T₁ < T₂` with `Re ζ > 0` on both horizontal legs
`[1/2, 2] + iT₁` and `[1/2, 2] + iT₂`, the number of zeros with `T₁ < Im ρ ≤ T₂`, counted with
multiplicity, is exactly `∫_{T₁}^{T₂} μ + (arg ζ(1/2 + iT₂) - arg ζ(1/2 + iT₁)) / π`. -/
theorem exact_argument (T₁ T₂ : ℝ) (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hleg₁ : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₁ * I)).re)
    (hleg₂ : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₂ * I)).re) :
    (Zeta23.Ncount T₁ T₂ : ℝ) = (∫ t in T₁..T₂, Zeta23.mu t) +
      ((riemannZeta (1 / 2 + T₂ * I)).arg - (riemannZeta (1 / 2 + T₁ * I)).arg) / Real.pi := by
  have hT₁ : 0 < T₁ := by linarith
  have hT₂ : 0 < T₂ := by linarith
  have hg₁ := goodHeight_of_re_pos hleg₁
  have hg₂ := goodHeight_of_re_pos hleg₂
  rw [N_eq_halfContour_completedZeta h1 h12 hg₁ hg₂,
    halfContour_completedZeta_split h1 h12 hg₁ hg₂, Complex.add_im, mul_add,
    gamma_side hT₁ hT₂, im_halfContour_logDeriv_riemannZeta hT₁.ne' hT₂.ne' hleg₁ hleg₂]
  ring

/-- `exact_argument` proves the skeleton's `Prop` `ExactArgument` as stated. -/
theorem exact_argument_holds : ExactArgument := exact_argument

end RHHeight
