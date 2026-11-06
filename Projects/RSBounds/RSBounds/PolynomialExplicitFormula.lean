import TernaryGoldbach.Explicit.Datum
import RSBounds.PolynomialResidue
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Contour shifting with degree-four smoothing

The Mellin transform of a fourfold polynomial smoothing decays as the inverse
fifth power of the ordinate. This file uses that polynomial decay directly.
It does not impose an exponential-decay hypothesis.

The finite rectangle and limiting formulas explicitly include the possible
pole at zero. A supplied good-height sequence can be shared between several
real arguments, as needed when taking a fourth finite difference.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.PolynomialExplicit

open TernaryGoldbach.Explicit

/-- Bounds appropriate to a Mellin transform with decay `|t|^(-5)`.
The horizontal bound is away from the possible pole at zero. -/
structure DecayFive (M : ℂ → ℂ) (K : ℝ) : Prop where
  nonneg : 0 ≤ K
  continuous_line : ∀ σ : ℝ, σ = -1 / 2 ∨ σ = 3 / 2 →
    Continuous (fun t : ℝ => M ((σ : ℂ) + t * I))
  line_bound : ∀ σ : ℝ, σ = -1 / 2 ∨ σ = 3 / 2 → ∀ t : ℝ,
    ‖M ((σ : ℂ) + t * I)‖ ≤ K / (1 + |t|) ^ 5
  strip_bound : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
    ‖M s‖ ≤ K / |s.im| ^ 5

/-- A single sequence of good rectangle heights, independent of the Mellin
kernel and the real argument. This permits taking finite differences of
several explicit-formula evaluations along the same zero sums. -/
structure GoodHeights (f : ℂ → ℂ) (B : ℝ → ℝ) (T : ℕ → ℝ) : Prop where
  mem : ∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)
  bounds : ∀ k : ℕ, ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]],
    (f ((σ : ℂ) + ((T k : ℝ) : ℂ) * I) ≠ 0 ∧
      f ((σ : ℂ) + ((-T k : ℝ) : ℂ) * I) ≠ 0) ∧
    (‖logDeriv f ((σ : ℂ) + ((T k : ℝ) : ℂ) * I)‖ ≤ HkD B (k + 1) ∧
      ‖logDeriv f ((σ : ℂ) + ((-T k : ℝ) : ℂ) * I)‖ ≤ HkD B (k + 1))

theorem exists_goodHeights {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ}
    (hd : LDatum f B D CR) : ∃ T : ℕ → ℝ, GoodHeights f B T := by
  choose T hT hgood using fun k : ℕ => good_heightD hd (k + 1)
  refine ⟨T, ?_, hgood⟩
  intro k
  have h := hT k
  push_cast at h
  constructor <;> linarith [h.1, h.2]

/-- Polynomial decay of order five absorbs the linear growth used on the
left vertical line. -/
theorem weighted_integrable_of_decay_five {g : ℝ → ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hc : Continuous g)
    (hg : ∀ t, ‖g t‖ ≤ K / (1 + |t|) ^ 5) :
    Integrable (fun t : ℝ => (1 + |t|) * ‖g t‖) := by
  refine (integrable_inv_one_add_sq.const_mul K).mono' (by fun_prop)
    (Eventually.of_forall fun t => ?_)
  have ha : 0 ≤ |t| := abs_nonneg t
  have hp : 0 < 1 + |t| := by positivity
  have hp4 : 1 + t ^ 2 ≤ (1 + |t|) ^ 4 := by
    have ht : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [pow_nonneg ha 3, pow_nonneg ha 4]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (1 + |t|) * ‖g t‖ ≤ (1 + |t|) * (K / (1 + |t|) ^ 5) :=
      mul_le_mul_of_nonneg_left (hg t) hp.le
    _ = K / (1 + |t|) ^ 4 := by field_simp
    _ ≤ K / (1 + t ^ 2) :=
      div_le_div_of_nonneg_left hK (by positivity) hp4
    _ = K * (1 + t ^ 2)⁻¹ := by ring

theorem DecayFive.weighted_integrable {M : ℂ → ℂ} {K : ℝ}
    (hM : DecayFive M K) {σ : ℝ} (hσ : σ = -1 / 2 ∨ σ = 3 / 2) :
    Integrable (fun t : ℝ => (1 + |t|) * ‖M ((σ : ℂ) + t * I)‖) :=
  weighted_integrable_of_decay_five hM.nonneg (hM.continuous_line σ hσ)
    (hM.line_bound σ hσ)

theorem DecayFive.integrable_line {M : ℂ → ℂ} {K : ℝ}
    (hM : DecayFive M K) {σ : ℝ} (hσ : σ = -1 / 2 ∨ σ = 3 / 2) :
    Integrable (fun t : ℝ => M ((σ : ℂ) + t * I)) := by
  refine (hM.weighted_integrable hσ).mono'
    (hM.continuous_line σ hσ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  exact le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg t])

/-- The integrand for an abstract Mellin transform `M`. -/
noncomputable def contourIntegrand (f M : ℂ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  logDeriv f s * (M s * (x : ℂ) ^ s)

/-- The finite rectangle identity for a meromorphic kernel `H(s)/s`, with
its pole at zero explicitly included. Only the numerator is required to be
holomorphic across zero. -/
theorem rect_identity_pole_zero {f H : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ}
    (hd : LDatum f B D CR) (hf0 : f 0 ≠ 0)
    (hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ H s)
    {x T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hbot : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]],
      f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (htop : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]],
      f ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) :
    rectInt (contourIntegrand f (fun s => H s / s) x) (zT T) (wT T) =
      2 * π * I * ((∑ u ∈ zerosRectD f T, (multRectD f T u : ℂ) *
        (H u / u * (x : ℂ) ^ u)) + logDeriv f 0 * H 0) := by
  have hf2 : f 2 ≠ 0 := hd.nz_right _ (by norm_num)
  have hR : 0 < RT T := by unfold RT; linarith
  have hrect : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆
      Metric.ball 2 (RT T / 2) := by
    intro s hs
    rw [mem_reProdIm, zT_re, wT_re, zT_im, wT_im,
      Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by linarith)] at hs
    rw [Metric.mem_ball, dist_eq_norm, RT]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat,
      Complex.im_ofNat, sub_zero]
    have h1 : |s.re - 2| ≤ 5 / 2 := by
      rw [abs_le]; constructor <;> linarith [hs.1.1, hs.1.2]
    have h2 : |s.im| ≤ T := by
      rw [abs_le]; constructor <;> linarith [hs.2.1, hs.2.2]
    linarith
  have hbd : NoZerosOnSides f (zT T) (wT T) := by
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_, fun y _ => ?_, fun y _ => ?_⟩
    · rw [zT_re, wT_re] at hσ; simpa using hbot σ hσ
    · rw [zT_re, wT_re] at hσ; simpa using htop σ hσ
    · exact hd.nz_right _ (by simp; norm_num)
    · exact hd.nz_strip _ (by simp; norm_num) (by simp; norm_num)
  let U : Set ℂ := {s | -1 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsubU : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆ U := by
    intro s hs
    rw [mem_reProdIm, zT_re, wT_re, Set.uIcc_of_le (by norm_num)] at hs
    show -1 < s.re
    linarith [hs.1.1]
  have hG : DifferentiableOn ℂ (fun s => H s * (x : ℂ) ^ s) U := by
    intro s hs
    exact ((hH s hs).mul
      (differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))).differentiableWithinAt
  have hres := rectInt_logDeriv_mul_div_zero hd.diff hR hf2
    (by simp; norm_num : (zT T).re < (wT T).re)
    (by simp; linarith : (zT T).im < (wT T).im) hrect hbd
    (by simp; norm_num : (zT T).re < 0)
    (by simp : 0 < (wT T).re)
    (by simp; linarith : (zT T).im < 0)
    (by simp; linarith : 0 < (wT T).im)
    hf0 hUo hsubU hG
  change rectInt (fun s => logDeriv f s * (H s / s * (x : ℂ) ^ s)) (zT T) (wT T) = _
  simpa only [zerosRectD, multRectD, div_mul_eq_mul_div,
    Complex.cpow_zero, mul_one] using hres

theorem integrable_contour_right {f M : ℂ → ℂ} {B : ℝ → ℝ} {D CR K : ℝ}
    (hd : LDatum f B D CR) (hM : DecayFive M K) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + t * I)) := by
  have hcont : Continuous (fun t : ℝ => contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    unfold contourIntegrand
    refine (continuous_logDeriv_lineD hd (3 / 2) (fun t => hd.nz_right _ (by simp; norm_num))).mul
      ((hM.continuous_line (3 / 2) (Or.inr rfl)).mul ?_)
    exact continuous_iff_continuousAt.2 fun t =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  have hCR : 0 ≤ CR := (norm_nonneg _).trans (hd.right_bound 0)
  refine ((hM.weighted_integrable (Or.inr rfl)).const_mul (CR * x ^ (3 / 2 : ℝ))).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [contourIntegrand, norm_mul, norm_mul, norm_cpow_x hx]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
  have hnorm := hd.right_bound t
  have hweight : ‖M (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (1 + |t|) * ‖M (((3 / 2 : ℝ) : ℂ) + t * I)‖ := by
    exact le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg t])
  calc
    ‖logDeriv f (((3 / 2 : ℝ) : ℂ) + t * I)‖ *
        (‖M (((3 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (3 / 2 : ℝ))
      ≤ CR * (((1 + |t|) * ‖M (((3 / 2 : ℝ) : ℂ) + t * I)‖) * x ^ (3 / 2 : ℝ)) := by
        gcongr
    _ = _ := by ring

theorem integrable_contour_left {f M : ℂ → ℂ} {B : ℝ → ℝ} {D CR K : ℝ}
    (hd : LDatum f B D CR) (hM : DecayFive M K) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
  have hcont : Continuous (fun t : ℝ => contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
    unfold contourIntegrand
    refine (continuous_logDeriv_lineD hd (-1 / 2) (fun t =>
      hd.nz_strip _ (by simp; norm_num) (by simp; norm_num))).mul
      ((hM.continuous_line (-1 / 2) (Or.inl rfl)).mul ?_)
    exact continuous_iff_continuousAt.2 fun t =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  let c₁ : ℝ := 2 / Real.log 2 + 4.8
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hD : 0 ≤ D := hd.D_nonneg
  have hbound (t : ℝ) : ‖logDeriv f (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      c₁ * (D + 40) * (1 + |t|) := by
    have h := norm_logDeriv_leftD hd t
    have hB := hd.logB_lin t
    have heq : Real.log (B t / 0.355) / Real.log 2 / (1 / 2) +
        4.8 * Real.log (B t / 0.355) = c₁ * Real.log (B t / 0.355) := by
      dsimp [c₁]; ring
    rw [heq] at h
    have hm := mul_le_mul_of_nonneg_left hB hc₁
    have hDt : 0 ≤ D * |t| := mul_nonneg hD (abs_nonneg t)
    have hu : D + 37 + 2.6 * |t| ≤ (D + 40) * (1 + |t|) := by
      nlinarith [abs_nonneg t]
    simpa only [mul_assoc] using h.trans (hm.trans (mul_le_mul_of_nonneg_left hu hc₁))
  refine ((hM.weighted_integrable (Or.inl rfl)).const_mul
    (c₁ * (D + 40) * x ^ (-1 / 2 : ℝ))).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [contourIntegrand, norm_mul, norm_mul, norm_cpow_x hx]
  have hre : (((-1 / 2 : ℝ) : ℂ) + t * I).re = -1 / 2 := by simp
  rw [hre]
  calc
    ‖logDeriv f (((-1 / 2 : ℝ) : ℂ) + t * I)‖ *
        (‖M (((-1 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (-1 / 2 : ℝ))
      ≤ (c₁ * (D + 40) * (1 + |t|)) *
        (‖M (((-1 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (-1 / 2 : ℝ)) := by
          gcongr
          exact hbound t
    _ = _ := by ring

/-- The quadratic good-height bound is killed by fifth-power decay. -/
theorem tendsto_HkD_div_fifth {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ}
    (hd : LDatum f B D CR) :
    Tendsto (fun k : ℕ => HkD B (k + 1) / ((k : ℝ) + 1) ^ 5) atTop (𝓝 0) := by
  let a : ℝ := D + 40
  have hnn (k : ℕ) : 0 ≤ HkD B (k + 1) / ((k : ℝ) + 1) ^ 5 := by
    unfold HkD
    have hB := hd.B_ge (((k + 1 : ℕ) : ℝ) + 1)
    have hl : 0 ≤ Real.log (B (((k + 1 : ℕ) : ℝ) + 1) / 0.355) :=
      Real.log_nonneg ((le_div_iff₀ (by norm_num)).2 (by linarith))
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl106 : 0 < Real.log (10 / 6 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hmajor (k : ℕ) : HkD B (k + 1) / ((k : ℝ) + 1) ^ 5 ≤
      ((a + 2.6 * ((k : ℝ) + 1)) *
        ((4 * (a + 2.6 * ((k : ℝ) + 1)) / 0.51 + 2) / 0.69 + 4.8)) /
          ((k : ℝ) + 1) ^ 5 := by
    have h := HkD_le hd (k + 1)
    push_cast at h
    exact div_le_div_of_nonneg_right h (by positivity)
  refine squeeze_zero hnn hmajor ?_
  have hlim (r : ℝ) (n : ℕ) (hn : n ≠ 0) :
      Tendsto (fun k : ℕ => r / ((k : ℝ) + 1) ^ n) atTop (𝓝 0) := by
    have h := (tendsto_const_div_pow r n hn).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have heq (k : ℕ) :
      ((a + 2.6 * ((k : ℝ) + 1)) *
        ((4 * (a + 2.6 * ((k : ℝ) + 1)) / 0.51 + 2) / 0.69 + 4.8)) /
          ((k : ℝ) + 1) ^ 5 =
      (a * ((4 * a / 0.51 + 2) / 0.69 + 4.8)) / ((k : ℝ) + 1) ^ 5 +
      (2.6 * ((4 * a / 0.51 + 2) / 0.69 + 4.8) + a * (4 * 2.6 / 0.51 / 0.69)) /
        ((k : ℝ) + 1) ^ 4 +
      (2.6 * (4 * 2.6 / 0.51 / 0.69)) / ((k : ℝ) + 1) ^ 3 := by
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hk]
    <;> ring
  simp_rw [heq]
  simpa using ((hlim _ 5 (by norm_num)).add (hlim _ 4 (by norm_num))).add
    (hlim _ 3 (by norm_num))


/-- Passing the finite-rectangle residue formula to the limit using only
fifth-power Mellin decay. `residueZero` is explicitly retained. -/
theorem contour_limit_of_residue_formula_at_heights {f M : ℂ → ℂ} {B : ℝ → ℝ} {D CR K : ℝ}
    (hd : LDatum f B D CR) (hM : DecayFive M K) {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hHeights : GoodHeights f B T)
    (residueZero : ℂ)
    (hrectFormula : ∀ T : ℝ, 0 < T →
      (∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
      (∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) →
      rectInt (contourIntegrand f M x) (zT T) (wT T) =
        2 * π * I * ((∑ u ∈ zerosRectD f T, (multRectD f T u : ℂ) *
          (M u * (x : ℂ) ^ u)) + residueZero)) :
    Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
        (M u * (x : ℂ) ^ u)) atTop
        (𝓝 ((1 / (2 * π) : ℂ) *
          ((∫ y : ℝ, contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + y * I)) -
            ∫ y : ℝ, contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + y * I)) - residueZero)) := by
  have hT' := hHeights.mem
  have hgood := hHeights.bounds
  have hTpos : ∀ k, 0 < T k := fun k => by linarith [(hT' k).1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  set Rinf := ∫ y : ℝ, contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + y * I) with hRinf
  set Linf := ∫ y : ℝ, contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + y * I) with hLinf
  set Sk := fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) * (M u * (x : ℂ) ^ u)
  set Bot := fun k => ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), contourIntegrand f M x ((σ : ℂ) + ((-T k : ℝ) : ℂ) * I)
  set Top := fun k => ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), contourIntegrand f M x ((σ : ℂ) + ((T k : ℝ) : ℂ) * I)
  set Right := fun k => ∫ y in (-T k)..(T k), contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + y * I)
  set Left := fun k => ∫ y in (-T k)..(T k), contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + y * I)
  -- the rectangle identity, expanded
  have hrect : ∀ k, Bot k - Top k + I * Right k - I * Left k = 2 * π * I * (Sk k + residueZero) := by
    intro k
    have h := hrectFormula (T k) (hTpos k) (fun σ hσ => ((hgood k σ hσ).1).2)
      (fun σ hσ => ((hgood k σ hσ).1).1)
    rw [← h]
    unfold rectInt
    simp only [zT_re, zT_im, wT_re, wT_im, smul_eq_mul]
    rfl
  -- The fifth-power kernel estimate, without exponential decay.
  have hside : ∀ k, ∀ S : ℝ, (S = T k ∨ S = -T k) →
      ‖∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), contourIntegrand f M x ((σ : ℂ) + (S : ℂ) * I)‖ ≤
        (HkD B (k + 1) / ((k : ℝ) + 1) ^ 5) *
          (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) *
          |(3 / 2 : ℝ) - (-1 / 2)| := by
    intro k S hS
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    have hσ' : σ ∈ [[(-1 / 2 : ℝ), 3 / 2]] := Set.uIoc_subset_uIcc hσ
    have hσ2 : -1 / 2 ≤ σ ∧ σ ≤ 3 / 2 := by
      rw [Set.uIcc_of_le (by norm_num)] at hσ'; exact hσ'
    have hb : ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ ≤ HkD B (k + 1) := by
      rcases hS with rfl | rfl
      · exact ((hgood k σ hσ').2).1
      · exact ((hgood k σ hσ').2).2
    have hS' : |S| = T k := by
      rcases hS with rfl | rfl
      · exact abs_of_pos (hTpos k)
      · rw [abs_neg]; exact abs_of_pos (hTpos k)
    have hTk : (k : ℝ) + 1 ≤ T k := (hT' k).1
    have hK1 : 1 ≤ T k := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hG := hM.strip_bound ((σ : ℂ) + (S : ℂ) * I)
      (by simp; linarith) (by simp; linarith) (by simpa [hS'] using hK1)
    have him : ((σ : ℂ) + (S : ℂ) * I).im = S := by simp
    have hre : ((σ : ℂ) + (S : ℂ) * I).re = σ := by simp
    rw [him, hS'] at hG
    have hden : K / (T k) ^ 5 ≤ K / ((k : ℝ) + 1) ^ 5 :=
      div_le_div_of_nonneg_left hM.nonneg (by positivity)
        (pow_le_pow_left₀ (by positivity) hTk 5)
    have hxσ := rpow_le_of_mem hx hσ2.1 hσ2.2
    have hHk0 : 0 ≤ HkD B (k + 1) := le_trans (norm_nonneg _) hb
    rw [contourIntegrand, norm_mul, norm_mul, norm_cpow_x hx, hre]
    calc
      ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ *
          (‖M ((σ : ℂ) + (S : ℂ) * I)‖ * x ^ σ)
        ≤ HkD B (k + 1) * ((K / ((k : ℝ) + 1) ^ 5) *
          (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) := by
            exact mul_le_mul hb
              (mul_le_mul (hG.trans hden) hxσ (by positivity)
                (div_nonneg hM.nonneg (by positivity)))
              (by positivity) hHk0
      _ = _ := by ring
  have hdecay : Tendsto (fun k : ℕ => (HkD B (k + 1) / ((k : ℝ) + 1) ^ 5) *
      (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) *
      |(3 / 2 : ℝ) - (-1 / 2)|) atTop (𝓝 0) := by
    have h := ((tendsto_HkD_div_fifth hd).mul_const
      (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ)))).mul_const
      |(3 / 2 : ℝ) - (-1 / 2)|
    simpa using h
  have hBot : Tendsto Bot atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hside k (-T k) (Or.inr rfl)) hdecay
  have hTop : Tendsto Top atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hside k (T k) (Or.inl rfl)) hdecay
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun k => (hT' k).1) (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hRight : Tendsto Right atTop (𝓝 Rinf) :=
    intervalIntegral_tendsto_integral (integrable_contour_right hd hM hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hLeft : Tendsto Left atTop (𝓝 Linf) :=
    intervalIntegral_tendsto_integral (integrable_contour_left hd hM hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hSk : ∀ k, Sk k = (Bot k - Top k + I * Right k - I * Left k) / (2 * π * I) - residueZero := by
    intro k
    have hne : (2 * π * I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    rw [hrect k]; field_simp; ring
  have hlim := ((((hBot.sub hTop).add (hRight.const_mul I)).sub (hLeft.const_mul I)).div_const
    (2 * π * I)).sub_const residueZero
  rw [show Sk = fun k => (Bot k - Top k + I * Right k - I * Left k) / (2 * π * I) - residueZero from funext hSk]
  convert hlim using 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Existential form of the preceding limit theorem. The stronger
`…_at_heights` theorem is used when several real arguments must share the
same sequence of truncated zero sums. -/
theorem contour_limit_of_residue_formula {f M : ℂ → ℂ} {B : ℝ → ℝ} {D CR K : ℝ}
    (hd : LDatum f B D CR) (hM : DecayFive M K) {x : ℝ} (hx : 0 < x)
    (residueZero : ℂ)
    (hrectFormula : ∀ T : ℝ, 0 < T →
      (∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) →
      (∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) →
      rectInt (contourIntegrand f M x) (zT T) (wT T) =
        2 * π * I * ((∑ u ∈ zerosRectD f T, (multRectD f T u : ℂ) *
          (M u * (x : ℂ) ^ u)) + residueZero)) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
        (M u * (x : ℂ) ^ u)) atTop
        (𝓝 ((1 / (2 * π) : ℂ) *
          ((∫ y : ℝ, contourIntegrand f M x (((3 / 2 : ℝ) : ℂ) + y * I)) -
            ∫ y : ℝ, contourIntegrand f M x (((-1 / 2 : ℝ) : ℂ) + y * I)) - residueZero)) := by
  obtain ⟨T, hT⟩ := exists_goodHeights hd
  exact ⟨T, hT.mem,
    contour_limit_of_residue_formula_at_heights hd hM hx hT residueZero hrectFormula⟩

/-- Pole-zero formula along any supplied good-height sequence. -/
theorem explicit_formula_pole_zero_at_heights {f H : ℂ → ℂ} {B : ℝ → ℝ} {D CR K : ℝ}
    (hd : LDatum f B D CR) (hf0 : f 0 ≠ 0)
    (hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ H s)
    (hM : DecayFive (fun s => H s / s) K) {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hT : GoodHeights f B T) :
    Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
      (H u / u * (x : ℂ) ^ u)) atTop
      (𝓝 ((1 / (2 * π) : ℂ) *
        ((∫ y : ℝ, contourIntegrand f (fun s => H s / s) x
          (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, contourIntegrand f (fun s => H s / s) x
            (((-1 / 2 : ℝ) : ℂ) + y * I)) - logDeriv f 0 * H 0)) :=
  contour_limit_of_residue_formula_at_heights hd hM hx hT (logDeriv f 0 * H 0)
    (fun _ hT hbot htop => rect_identity_pole_zero hd hf0 hH hx hT hbot htop)

/-- The polynomial-decay explicit formula on the fixed strip. The contribution
at zero is evaluated, while the left vertical integral remains explicit. -/
theorem explicit_formula_pole_zero {f H : ℂ → ℂ} {B : ℝ → ℝ} {D CR K : ℝ}
    (hd : LDatum f B D CR) (hf0 : f 0 ≠ 0)
    (hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ H s)
    (hM : DecayFive (fun s => H s / s) K) {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
        (H u / u * (x : ℂ) ^ u)) atTop
        (𝓝 ((1 / (2 * π) : ℂ) *
          ((∫ y : ℝ, contourIntegrand f (fun s => H s / s) x
            (((3 / 2 : ℝ) : ℂ) + y * I)) -
            ∫ y : ℝ, contourIntegrand f (fun s => H s / s) x
              (((-1 / 2 : ℝ) : ℂ) + y * I)) - logDeriv f 0 * H 0)) :=
  contour_limit_of_residue_formula hd hM hx (logDeriv f 0 * H 0)
    (fun _ hT hbot htop => rect_identity_pole_zero hd hf0 hH hx hT hbot htop)


end TernaryGoldbach.RSBounds.PolynomialExplicit
