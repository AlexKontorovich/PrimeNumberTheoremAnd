import Mathlib.Analysis.Complex.HasPrimitives
import PrimeNumberTheoremAnd.BorelCaratheodory
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.PNT1_ComplexAnalysis

/-!
# Taxicab Primitives for Holomorphic Functions

This file provides infrastructure for constructing primitives of holomorphic functions
on open sets using the taxicab (axis-aligned) integral approach from `StrongPNT`.

The main result is `exists_local_primitive`, which shows that any holomorphic function
on an open set has a primitive on a small ball around each point.

## Main Results

* `exists_local_primitive` - Local primitives via taxicab integration
* `DifferentiableOn.isExactOn_convex` - Global primitives on convex open sets

## References

* StrongPNT/PNT1_ComplexAnalysis.lean - Original taxicab primitive machinery

-/

open Complex Set Metric MeasureTheory Filter
open scoped Topology Interval

noncomputable section

namespace TaxicabPrimitive

/-! ## Translation Infrastructure

We translate the StrongPNT machinery (which works on balls centered at 0) to
balls centered at arbitrary points. -/

/-- Translate a function to be centered at 0. -/
def translateFun (z₀ : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := fun w => f (z₀ + w)

/-- The translated function is analytic if the original is. -/
lemma analyticOnNhd_translateFun {z₀ : ℂ} {R : ℝ} {f : ℂ → ℂ} (_hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R)) :
    AnalyticOnNhd ℂ (translateFun z₀ f) (Metric.closedBall 0 R) := by
  intro w hw
  have hz₀w : z₀ + w ∈ Metric.closedBall z₀ R := by
    simp only [Metric.mem_closedBall] at hw ⊢
    simp only [dist_zero_right] at hw
    simp only [dist_self_add_left]
    exact hw
  have hf_at : AnalyticAt ℂ f (z₀ + w) := hf (z₀ + w) hz₀w
  have hadd : AnalyticAt ℂ (fun v => z₀ + v) w := analyticAt_const.add analyticAt_id
  exact hf_at.comp hadd

/-- Given a local primitive G₀ on closedBall 0 r centered at 0,
    construct a primitive G on ball z₀ r centered at z₀. -/
def translatePrimitive (z₀ : ℂ) (G₀ : ℂ → ℂ) : ℂ → ℂ := fun w => G₀ (w - z₀)

lemma hasDerivAt_translatePrimitive {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {G₀ : ℂ → ℂ} {f : ℂ → ℂ}
    (hG₀_diff : DifferentiableOn ℂ G₀ (Metric.closedBall 0 r))
    (hG₀_deriv : ∀ w ∈ Metric.closedBall (0 : ℂ) r, derivWithin G₀ (Metric.closedBall 0 r) w = translateFun z₀ f w)
    {z : ℂ} (hz : z ∈ Metric.ball z₀ r) :
    HasDerivAt (translatePrimitive z₀ G₀) (f z) z := by
  -- z - z₀ is in the interior of closedBall 0 r
  have hz' : z - z₀ ∈ Metric.ball (0 : ℂ) r := by
    simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [← dist_eq_norm, dist_comm z z₀]
    rwa [dist_comm] at hz
  have hz'' : z - z₀ ∈ Metric.closedBall (0 : ℂ) r := Metric.ball_subset_closedBall hz'
  -- G₀ is differentiable at z - z₀ (in the interior)
  have hG₀_at : DifferentiableAt ℂ G₀ (z - z₀) := by
    have hmem : Metric.closedBall (0 : ℂ) r ∈ 𝓝 (z - z₀) :=
      Metric.closedBall_mem_nhds_of_mem hz'
    exact hG₀_diff.differentiableAt hmem
  -- Compute the derivative of translatePrimitive
  have hcomp : HasDerivAt (translatePrimitive z₀ G₀) (deriv G₀ (z - z₀) * 1) z := by
    have hsub : HasDerivAt (fun w => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
    exact hG₀_at.hasDerivAt.comp z hsub
  simp only [mul_one] at hcomp
  -- The derivative is f z
  have hderiv_eq : deriv G₀ (z - z₀) = f z := by
    have huniq : UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) r) (z - z₀) :=
      uniqueDiffWithinAt_closedBall_complex_of_mem hr hz''
    have hderiv_within : derivWithin G₀ (Metric.closedBall 0 r) (z - z₀) = translateFun z₀ f (z - z₀) :=
      hG₀_deriv (z - z₀) hz''
    rw [derivWithin_of_mem_nhds (Metric.closedBall_mem_nhds_of_mem hz')] at hderiv_within
    simp only [translateFun, add_sub_cancel] at hderiv_within
    exact hderiv_within
  rw [hderiv_eq] at hcomp
  exact hcomp

/-! ## Local Primitive Existence -/

/-- On an open set, any holomorphic function has a local primitive around each point.
    This uses the StrongPNT taxicab integral machinery. -/
theorem exists_local_primitive {U : Set ℂ} (hU_open : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (z₀ : ℂ) (hz₀ : z₀ ∈ U) :
    ∃ r > 0, ∃ G : ℂ → ℂ,
      Metric.ball z₀ r ⊆ U ∧
      DifferentiableOn ℂ G (Metric.ball z₀ r) ∧
      ∀ z ∈ Metric.ball z₀ r, HasDerivAt G (f z) z := by
  -- Get a ball around z₀ contained in U
  obtain ⟨R₀, hR₀_pos, hR₀_ball⟩ := Metric.isOpen_iff.mp hU_open z₀ hz₀
  -- Choose R such that closedBall z₀ R ⊆ ball z₀ R₀ ⊆ U, with R small enough for StrongPNT
  let R := min (R₀ / 2) (1 / 4)
  have hR_pos : 0 < R := lt_min (half_pos hR₀_pos) (by norm_num)
  have hR_lt_R₀ : R < R₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hR₀_pos)
  have hR_lt_half : R ≤ 1 / 4 := min_le_right _ _
  have hR_ball : Metric.closedBall z₀ R ⊆ U := by
    intro w hw
    apply hR₀_ball
    calc dist w z₀ ≤ R := hw
      _ < R₀ := hR_lt_R₀
  -- f is analytic on closedBall z₀ R (since holomorphic on an open set containing it)
  have hf_analytic : AnalyticOnNhd ℂ f (Metric.closedBall z₀ R) := by
    intro w hw
    have hw_U : w ∈ U := hR_ball hw
    -- Use: AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z
    apply analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hU_open.mem_nhds hw_U] with v hv
    exact hf.differentiableAt (hU_open.mem_nhds hv)
  -- Translate to center at 0
  let f₀ := translateFun z₀ f
  have hf₀ : AnalyticOnNhd ℂ f₀ (Metric.closedBall 0 R) :=
    analyticOnNhd_translateFun hR_pos hf_analytic
  -- Choose parameters for If_ext: r₁ < R' < R₁ < 1 with R₁ < R
  let r₁ := R / 4
  let R' := R / 2
  let R₁ := 3 * R / 4
  have hr₁_pos : 0 < r₁ := by positivity
  have hr₁_lt_R' : r₁ < R' := by simp only [r₁, R']; linarith
  have hR'_lt_R₁ : R' < R₁ := by simp only [R', R₁]; linarith
  have hR₁_lt_one : R₁ < 1 := by
    simp only [R₁]
    have h1 : R ≤ 1 / 4 := hR_lt_half
    have h2 : 3 * R ≤ 3 * (1 / 4) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h3 : 3 * R / 4 ≤ 3 * (1 / 4) / 4 := div_le_div_of_nonneg_right h2 (by norm_num)
    calc 3 * R / 4 ≤ 3 * (1 / 4) / 4 := h3
      _ = 3 / 16 := by norm_num
      _ < 1 := by norm_num
  have hR'_lt_R : R' < R := by simp only [R']; linarith
  -- f₀ is analytic on closedBall 0 R' (since R' < R)
  have hf₀' : AnalyticOnNhd ℂ f₀ (Metric.closedBall 0 R') := by
    apply hf₀.mono
    exact Metric.closedBall_subset_closedBall (le_of_lt hR'_lt_R)
  -- Apply the StrongPNT result
  have hIf := If_is_differentiable_on hr₁_pos hr₁_lt_R' hR'_lt_R₁ hR₁_lt_one hf₀'
  rcases hIf with ⟨hIf_diff, hIf_deriv⟩
  -- Define G by translating back
  let G₀ := If_ext hr₁_pos hr₁_lt_R' hR'_lt_R₁ hR₁_lt_one f₀ hf₀'
  let G := translatePrimitive z₀ G₀
  -- The radius for our result
  use r₁, hr₁_pos, G
  constructor
  · -- ball z₀ r₁ ⊆ U
    intro w hw
    apply hR_ball
    have hdist : dist w z₀ < r₁ := hw
    apply Metric.mem_closedBall.mpr
    have hlt : r₁ < R := by simp only [r₁]; linarith
    exact le_of_lt (lt_trans hdist hlt)
  constructor
  · -- G is differentiable on ball z₀ r₁
    intro w hw
    have hw' : w - z₀ ∈ Metric.ball (0 : ℂ) r₁ := by
      simp only [Metric.mem_ball, dist_zero_right] at hw ⊢
      rw [← dist_eq_norm, dist_comm w z₀]
      rwa [dist_comm] at hw
    have hw'' : w - z₀ ∈ Metric.closedBall (0 : ℂ) r₁ := Metric.ball_subset_closedBall hw'
    have hG₀_at : DifferentiableAt ℂ G₀ (w - z₀) := by
      have hmem : Metric.closedBall (0 : ℂ) r₁ ∈ 𝓝 (w - z₀) :=
        Metric.closedBall_mem_nhds_of_mem hw'
      exact hIf_diff.differentiableAt hmem
    have hsub : DifferentiableAt ℂ (fun v => v - z₀) w := differentiableAt_id.sub_const z₀
    exact (hG₀_at.comp w hsub).differentiableWithinAt
  · -- HasDerivAt G (f w) w for all w in ball z₀ r₁
    intro w hw
    have hw' : w - z₀ ∈ Metric.closedBall (0 : ℂ) r₁ := by
      have hdist : dist w z₀ < r₁ := hw
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [← dist_eq_norm, dist_comm w z₀, dist_comm]
      exact le_of_lt hdist
    -- The derivative of G₀ at w - z₀ is f₀ (w - z₀) = f w
    have hderiv_eq : derivWithin G₀ (Metric.closedBall 0 r₁) (w - z₀) = f₀ (w - z₀) :=
      hIf_deriv (w - z₀) hw'
    -- Use the translation lemma
    apply hasDerivAt_translatePrimitive hr₁_pos hIf_diff
    · intro v hv
      exact hIf_deriv v hv
    · exact hw

end TaxicabPrimitive

/-! ## Global Primitives on Convex Sets -/

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A set U is rectangularly convex if for any two points in U, the points forming the
    corners of the rectangle defined by them are also in U. -/
def RectangularConvex (U : Set ℂ) : Prop :=
  ∀ ⦃x y⦄, x ∈ U → y ∈ U → (x.re + y.im * I) ∈ U ∧ (y.re + x.im * I) ∈ U

lemma mem_segment_add_im_of_mem_uIcc {a b x y : ℝ} (hx : x ∈ uIcc a b) :
    (x : ℂ) + y * I ∈ segment ℝ ((a : ℂ) + y * I) ((b : ℂ) + y * I) := by
  rw [← segment_eq_uIcc, segment_eq_image'] at hx
  rcases hx with ⟨t, ht, rfl⟩
  rw [segment_eq_image']
  refine ⟨t, ht, ?_⟩
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, smul_eq_mul]
  ring

lemma mem_segment_add_re_of_mem_uIcc {a b x y : ℝ} (hy : y ∈ uIcc a b) :
    (x : ℂ) + y * I ∈ segment ℝ ((x : ℂ) + a * I) ((x : ℂ) + b * I) := by
  rw [← segment_eq_uIcc, segment_eq_image'] at hy
  rcases hy with ⟨t, ht, rfl⟩
  rw [segment_eq_image']
  refine ⟨t, ht, ?_⟩
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, smul_eq_mul]
  ring

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma intervalIntegrable_seg_h {U : Set ℂ} {f : ℂ → E} (hf : ContinuousOn f U)
    {a b y : ℝ} (h_seg : segment ℝ ((a : ℂ) + y * I) ((b : ℂ) + y * I) ⊆ U) :
    IntervalIntegrable (fun x => f (x + y * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (continuous_ofReal.add continuous_const).continuousOn
  intro x hx
  apply h_seg
  exact mem_segment_add_im_of_mem_uIcc hx

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma intervalIntegrable_seg_v {U : Set ℂ} {f : ℂ → E} (hf : ContinuousOn f U)
    {a b x : ℝ} (h_seg : segment ℝ ((x : ℂ) + a * I) ((x : ℂ) + b * I) ⊆ U) :
    IntervalIntegrable (fun y => f (x + y * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
  intro y hy
  apply h_seg
  exact mem_segment_add_re_of_mem_uIcc hy

/-- A holomorphic function with zero derivative on a convex open set is constant. -/
theorem eq_of_deriv_eq_zero_on_convex {U : Set ℂ} (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hf' : ∀ z ∈ U, deriv f z = 0) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    f x = f y := by
  have hf_real : DifferentiableOn ℝ f U := hf.restrictScalars ℝ
  have hfderiv_zero : ∀ z ∈ U, fderivWithin ℝ f U z = 0 := by
    intro z hz
    have hf_at := hf.differentiableAt (hU_open.mem_nhds hz)
    have hderiv_z := hf' z hz
    rw [fderivWithin_of_isOpen hU_open hz]
    have h1 : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
      (hf_at.hasFDerivAt.restrictScalars ℝ).fderiv
    have h2 : fderiv ℂ f z = 0 := by
      rw [← deriv_fderiv, hderiv_z]
      ext
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
                 smul_zero, ContinuousLinearMap.zero_apply]
    rw [h1, h2]; simp
  exact hU_convex.is_const_of_fderivWithin_eq_zero hf_real hfderiv_zero hx hy

omit [CompleteSpace E] in
/-- A holomorphic E-valued function with zero derivative on a convex open set is constant. -/
theorem eq_of_fderiv_eq_zero_on_convex_E {U : Set ℂ} (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U) {f : ℂ → E} (hf : DifferentiableOn ℂ f U)
    (hf' : ∀ z ∈ U, fderiv ℂ f z = 0) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    f x = f y := by
  have hf_real : DifferentiableOn ℝ f U := hf.restrictScalars ℝ
  have hfderiv_zero : ∀ z ∈ U, fderivWithin ℝ f U z = 0 := by
    intro z hz
    have hf_at := hf.differentiableAt (hU_open.mem_nhds hz)
    have hderiv_z := hf' z hz
    rw [fderivWithin_of_isOpen hU_open hz]
    have h1 : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
      (hf_at.hasFDerivAt.restrictScalars ℝ).fderiv
    rw [h1, hderiv_z]; simp
  exact hU_convex.is_const_of_fderivWithin_eq_zero hf_real hfderiv_zero hx hy

omit [CompleteSpace E] in
/-- A holomorphic E-valued function with zero derivative on a convex open set is constant.
    Version using `deriv` instead of `fderiv`. -/
theorem eq_of_deriv_eq_zero_on_convex_E {U : Set ℂ} (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U) {f : ℂ → E} (hf : DifferentiableOn ℂ f U)
    (hf' : ∀ z ∈ U, deriv f z = 0) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    f x = f y := by
  apply eq_of_fderiv_eq_zero_on_convex_E hU_open hU_convex hf _ hx hy
  intro z hz
  have hf_at := hf.differentiableAt (hU_open.mem_nhds hz)
  have hderiv_z := hf' z hz
  rw [← deriv_fderiv, hderiv_z]
  ext; simp

omit [CompleteSpace E] in
/-- wedgeIntegral z z f = 0 for any z and f. -/
@[simp] lemma wedgeIntegral_self (z : ℂ) (f : ℂ → E) : wedgeIntegral z z f = 0 := by
  unfold wedgeIntegral
  simp only [intervalIntegral.integral_same, smul_zero, add_zero]

/-- On a ball, wedgeIntegral from the center has derivative f at every point of the ball.
This is the key Mathlib result that we build upon. -/
lemma hasDerivAt_wedgeIntegral_center_ball {c : ℂ} {r : ℝ} (_hr : 0 < r)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (z : ℂ) (hz : z ∈ Metric.ball c r) :
    HasDerivAt (fun w => wedgeIntegral c w f) (f z) z :=
  hf.isConservativeOn.hasDerivAt_wedgeIntegral hf.continuousOn hz

omit [CompleteSpace E] in
/-- Two primitives of the same function on a convex open set differ by a constant. -/
lemma primitives_differ_by_constant {U : Set ℂ} (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U) {f : ℂ → E} {g₁ g₂ : ℂ → E}
    (hg₁ : ∀ z ∈ U, HasDerivAt g₁ (f z) z) (hg₂ : ∀ z ∈ U, HasDerivAt g₂ (f z) z)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    g₁ x - g₂ x = g₁ y - g₂ y := by
  have hdiff : DifferentiableOn ℂ (fun z => g₁ z - g₂ z) U := fun z hz =>
    ((hg₁ z hz).differentiableAt.sub (hg₂ z hz).differentiableAt).differentiableWithinAt
  have hdiff_deriv : ∀ z ∈ U, deriv (fun w => g₁ w - g₂ w) z = 0 := fun z hz => by
    have h := (hg₁ z hz).sub (hg₂ z hz)
    simp only [sub_self] at h
    exact h.deriv
  exact eq_of_deriv_eq_zero_on_convex_E hU_open hU_convex hdiff hdiff_deriv hx hy

/-- On a convex open set that is also rectangularly convex, a holomorphic function has primitives.

This uses Mathlib's `DifferentiableOn.isExactOn_ball` result. At each point z ∈ U,
we find a ball B centered at z in U. The global primitive is defined by choosing a
base point c ∈ U and setting g(z) = wedgeIntegral c z f.

The proof that g has derivative f at each point uses that on any ball B centered at z,
wedgeIntegral z · f has derivative f (by Mathlib), and g differs from this local primitive
by a constant near z (using path additivity via conservation on U).

The `RectangularConvex` hypothesis ensures that the paths used in the wedge integrals remain in U. -/
theorem DifferentiableOn.isExactOn_rectangularConvex {U : Set ℂ} (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U) (hU_rect : RectangularConvex U) (hU_ne : U.Nonempty)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) : IsExactOn f U := by
  obtain ⟨c, hc⟩ := hU_ne
  refine ⟨fun z => wedgeIntegral c z f, ?_⟩
  intro z hz
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hU_open z hz
  have hlocal_z : HasDerivAt (fun w => wedgeIntegral z w f) (f z) z :=
    hasDerivAt_wedgeIntegral_center_ball hr_pos (hf.mono hr_ball) z (Metric.mem_ball_self hr_pos)
  have h_path_add : ∀ w ∈ Metric.ball z r,
      wedgeIntegral c w f = wedgeIntegral c z f + wedgeIntegral z w f := by
    intro w hw
    have hw_in_U : w ∈ U := hr_ball hw
    have hc_z : (z.re + c.im * I) ∈ U := (hU_rect hz hc).1
    have hc_w : (w.re + c.im * I) ∈ U := (hU_rect hw_in_U hc).1
    have hz_w : (w.re + z.im * I) ∈ U := (hU_rect hw_in_U hz).1
    have p3_eq_z : ((z.re + c.im * I).re : ℂ) + (w.re + z.im * I).im * I = z := by
      apply Complex.ext <;> simp
    have hz' : ((z.re + c.im * I).re : ℂ) + (w.re + z.im * I).im * I ∈ U := by
      rw [p3_eq_z]; exact hz
    have p4_eq_hc_w : ((w.re + z.im * I).re : ℂ) + (z.re + c.im * I).im * I = w.re + c.im * I := by
      apply Complex.ext <;> simp
    have hc_w' : ((w.re + z.im * I).re : ℂ) + (z.re + c.im * I).im * I ∈ U := by
      rw [p4_eq_hc_w]; exact hc_w
    have h_rect_sub : Rectangle (z.re + c.im * I) (w.re + z.im * I) ⊆ U :=
      hU_convex.rectangle_subset hc_z hz_w hz' hc_w'
    have h_cons : IsConservativeOn f U := hf.isConservativeOn
    let P := z.re + c.im * I
    let R := w.re + z.im * I

    -- The path additivity follows from IsConservativeOn
    -- For conservative functions, ∮ around any rectangle = 0
    -- So wedgeIntegral P R f + wedgeIntegral R P f = 0
    have h_sum : wedgeIntegral c w f - wedgeIntegral c z f - wedgeIntegral z w f =
                 wedgeIntegral P R f + wedgeIntegral R P f := by
      -- Use the conservative property: integral around the rectangle P-R is zero
      -- The difference of paths c→w and (c→z + z→w) equals the loop P→R→P
      unfold wedgeIntegral
      -- Simplify the coordinates of P and R
      simp only [P, R, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                 mul_zero, mul_one, sub_zero, add_zero, zero_add]
      -- All integrands need normalization to canonical form
      -- Convert all f(a + b*I) to f(b*I + a) or f(I*b + a)
      have hNorm := fun (a b : ℂ) => congrArg f (show a + b = b + a from add_comm a b)
      -- The goal has many integral terms. Rather than rewriting each individually,
      -- we use a more direct approach: show both sides are equal after simplification
      -- First combine the integrals using add_adjacent
      have hc_eq : (c.re : ℂ) + c.im * I = c := by simp
      have h1 := intervalIntegrable_seg_h hf.continuousOn
                   (hU_convex.segment_subset (by rw [hc_eq]; exact hc) hc_z)
      have h2 := intervalIntegrable_seg_h hf.continuousOn (hU_convex.segment_subset hc_z hc_w)
      have hw_eq : (w.re : ℂ) + w.im * I = w := by simp
      have h3 := intervalIntegrable_seg_v hf.continuousOn (hU_convex.segment_subset hc_w hz_w)
      have h4 := intervalIntegrable_seg_v hf.continuousOn
                   (hU_convex.segment_subset hz_w (by rw [hw_eq]; exact hw_in_U))
      -- Combine c.re..z.re + z.re..w.re = c.re..w.re at height c.im
      rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
      -- Combine c.im..z.im + z.im..w.im = c.im..w.im at x=w.re
      rw [← intervalIntegral.integral_add_adjacent_intervals h3 h4]
      -- Apply integral symmetry to normalize bounds
      rw [intervalIntegral.integral_symm w.re z.re, intervalIntegral.integral_symm z.im c.im]
      rw [intervalIntegral.integral_symm c.im z.im]
      -- Distribute smul and simplify
      simp only [smul_add, neg_neg]
      -- Normalize integrands: f(a+b) = f(b+a)
      have hn1 : ∫ x in c.re..z.re, f (↑x + ↑c.im * I) = ∫ x in c.re..z.re, f (↑c.im * I + ↑x) :=
        intervalIntegral.integral_congr fun x _ => hNorm _ _
      have hn2 : ∫ x in z.re..w.re, f (↑x + ↑z.im * I) = ∫ x in z.re..w.re, f (↑z.im * I + ↑x) :=
        intervalIntegral.integral_congr fun x _ => hNorm _ _
      have hn3 : ∫ y in c.im..z.im, f (↑z.re + ↑y * I) = ∫ y in c.im..z.im, f (↑y * I + ↑z.re) :=
        intervalIntegral.integral_congr fun y _ => hNorm _ _
      have hn4 : ∫ y in z.im..c.im, f (↑z.re + ↑y * I) = ∫ y in z.im..c.im, f (↑y * I + ↑z.re) :=
        intervalIntegral.integral_congr fun y _ => hNorm _ _
      rw [hn1, hn2, hn3, hn4]
      -- Normalize more integrands on RHS
      have hn5 : ∫ x in w.re..z.re, f (↑x + ↑c.im * I) = ∫ x in w.re..z.re, f (↑c.im * I + ↑x) :=
        intervalIntegral.integral_congr fun x _ => hNorm _ _
      have hn6 : ∫ x in w.re..z.re, f (↑x + ↑z.im * I) = ∫ x in w.re..z.re, f (↑z.im * I + ↑x) :=
        intervalIntegral.integral_congr fun x _ => hNorm _ _
      rw [hn5, hn6]
      -- Use symmetry: ∫ a..b = -∫ b..a (for the RHS)
      have hsym1 : ∫ x in w.re..z.re, f (↑z.im * I + ↑x) = -∫ x in z.re..w.re, f (↑z.im * I + ↑x) := by
        rw [intervalIntegral.integral_symm]
      have hsym2 : I • ∫ y in z.im..c.im, f (↑y * I + ↑z.re) = -I • ∫ y in c.im..z.im, f (↑y * I + ↑z.re) := by
        rw [intervalIntegral.integral_symm, smul_neg, neg_smul]
      rw [hsym1, hsym2]
      -- Normalize -1 • I • A to (-1 * I) • A = -I • A
      simp only [neg_smul]
      -- Now all terms cancel
      abel
    rw [← sub_eq_zero, sub_add_eq_sub_sub, h_sum]
    have h_rect_zero : wedgeIntegral P R f = - wedgeIntegral R P f :=
      h_cons P R h_rect_sub
    rw [h_rect_zero, neg_add_cancel]
  have hlocal_c : HasDerivAt (fun w => wedgeIntegral z w f + wedgeIntegral c z f) (f z) z :=
    hlocal_z.add_const _
  have heq_near' : (fun w => wedgeIntegral c w f) =ᶠ[𝓝 z]
      (fun w => wedgeIntegral z w f + wedgeIntegral c z f) := by
    filter_upwards [Metric.ball_mem_nhds z hr_pos] with w hw
    rw [h_path_add w hw, add_comm]
  exact hlocal_c.congr_of_eventuallyEq heq_near'

end Complex
