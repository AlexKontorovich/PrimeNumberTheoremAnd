import RSBounds.BacklundGammaPhaseArctan
import Mathlib.Analysis.Calculus.Deriv.Slope

open Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

theorem hasDerivAt_arctan_quotient {τ x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ ↦ Real.arctan (τ / u)) (-τ / (x ^ 2 + τ ^ 2)) x := by
  have h := ((hasDerivAt_const x τ).div (hasDerivAt_id x) hx.ne').arctan
  simp only [Pi.div_apply, id_eq, zero_mul, zero_sub, mul_one] at h
  convert h using 1
  have hden : 0 < 1 + (τ / x) ^ 2 := by positivity
  field_simp <;> ring

theorem hasDerivAt_arctan_quotient_deriv {τ x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ ↦ -τ / (u ^ 2 + τ ^ 2))
      (2 * τ * x / (x ^ 2 + τ ^ 2) ^ 2) x := by
  have hden : 0 < x ^ 2 + τ ^ 2 := by positivity
  have h := (hasDerivAt_const x (-τ)).div
    ((hasDerivAt_pow 2 x).add_const (τ ^ 2)) hden.ne'
  convert h using 1 <;> ring

noncomputable def arctanPrimitive (τ x : ℝ) : ℝ :=
  x * Real.arctan (τ / x) + τ / 2 * Real.log (x ^ 2 + τ ^ 2)

theorem hasDerivAt_arctanPrimitive {τ x : ℝ} (hx : 0 < x) :
    HasDerivAt (arctanPrimitive τ) (Real.arctan (τ / x)) x := by
  have hden : 0 < x ^ 2 + τ ^ 2 := by positivity
  have hlog := (((hasDerivAt_pow 2 x).add_const (τ ^ 2)).log hden.ne').const_mul (τ / 2)
  have hp := (hasDerivAt_id x).mul (hasDerivAt_arctan_quotient (τ := τ) hx)
  convert hp.add hlog using 1
  · rfl
  · simp only [id_eq]
    field_simp <;> ring

theorem integral_arctan_quotient {a : ℝ} (ha : 0 < a) (τ : ℝ) (N : ℕ) :
    (∫ x in a..(a + N), Real.arctan (τ / x)) =
      arctanPrimitive τ (a + N) - arctanPrimitive τ a := by
  have hle : a ≤ a + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact hasDerivAt_arctanPrimitive (ha.trans_le hx.1)
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact (hasDerivAt_arctan_quotient (τ := τ) (ha.trans_le hx.1)).continuousAt.continuousWithinAt

theorem tendsto_mul_arctan_quotient {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    Tendsto (fun N : ℕ ↦ ((N : ℝ) + a) * Real.arctan (τ / ((N : ℝ) + a)))
      atTop (𝓝 τ) := by
  have hr : Tendsto (fun N : ℕ ↦ τ / ((N : ℝ) + a)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop)
    · exact Filter.Eventually.of_forall (fun N ↦ div_pos hτ (by positivity))
  have hs : Tendsto (fun u : ℝ ↦ Real.arctan u / u) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hh := (Real.hasDerivAt_arctan 0).tendsto_slope.mono_left
      (nhdsGT_le_nhdsNE (0 : ℝ))
    simpa [slope_fun_def_field] using hh
  have hm := (hs.comp hr).mul_const τ
  convert hm using 1
  · funext N
    have hn : (N : ℝ) + a ≠ 0 := by positivity
    dsimp only [Function.comp_apply]
    field_simp [hn, hτ.ne'] <;> ring
  · ring

theorem tendsto_arctanPrimitive_sub_log {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    Tendsto (fun N : ℕ ↦ arctanPrimitive τ (a + N) - τ * Real.log N)
      atTop (𝓝 τ) := by
  have harg := tendsto_mul_arctan_quotient ha hτ
  have hd : Tendsto (fun N : ℕ ↦ Real.log ((N : ℝ) + a) - Real.log N)
      atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log a).comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun N : ℕ ↦ τ / ((N : ℝ) + a)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun N : ℕ ↦ Real.log (1 + (τ / ((N : ℝ) + a)) ^ 2))
      atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds.add (hr.pow 2)).log (by norm_num : (1 : ℝ) + 0 ^ 2 ≠ 0)
    simpa using hh
  have hm := (harg.add (hd.const_mul τ)).add (hl.const_mul (τ / 2))
  convert hm using 1
  · funext N
    have hx : 0 < (N : ℝ) + a := by positivity
    have he : ((N : ℝ) + a) ^ 2 + τ ^ 2 =
        ((N : ℝ) + a) ^ 2 * (1 + (τ / ((N : ℝ) + a)) ^ 2) := by
      field_simp <;> ring
    dsimp [arctanPrimitive]
    rw [add_comm a (N : ℝ), he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  · ring

theorem phase_correction_eq {τ : ℝ} (hτ : 0 < τ) :
    arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
        (τ * Real.log τ - τ - Real.pi / 8) =
      τ / 2 * Real.log (1 + ((1 / 4) / τ) ^ 2) +
        (1 / 4) * Real.arctan ((1 / 4) / τ) := by
  have he : (1 / 4 : ℝ) ^ 2 + τ ^ 2 = τ ^ 2 * (1 + ((1 / 4) / τ) ^ 2) := by
    field_simp
    ring
  have hat : Real.arctan (τ / (1 / 4)) = Real.pi / 2 - Real.arctan ((1 / 4) / τ) := by
    simpa only [inv_div] using Real.arctan_inv_of_pos (by positivity : 0 < (1 / 4 : ℝ) / τ)
  unfold arctanPrimitive
  rw [hat, he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

theorem phase_correction_bounds {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
        (τ * Real.log τ - τ - Real.pi / 8) ∧
    arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
        (τ * Real.log τ - τ - Real.pi / 8) ≤ 3 / (32 * τ) := by
  rw [phase_correction_eq hτ]
  have hl0 : 0 ≤ Real.log (1 + ((1 / 4) / τ) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg ((1 / 4 : ℝ) / τ)])
  have ha0 : 0 ≤ Real.arctan ((1 / 4) / τ) := Real.arctan_nonneg.mpr (by positivity)
  have hlu : Real.log (1 + ((1 / 4) / τ) ^ 2) ≤ ((1 / 4) / τ) ^ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ((1 / 4 : ℝ) / τ) ^ 2)
    linarith
  have hau := arctan_le_self' (by positivity : 0 ≤ (1 / 4 : ℝ) / τ)
  constructor
  · positivity
  · calc
      _ ≤ τ / 2 * (((1 / 4) / τ) ^ 2) + (1 / 4) * ((1 / 4) / τ) := by gcongr
      _ = 3 / (32 * τ) := by field_simp; ring

end TernaryGoldbach.RSBounds.BacklundGammaPhase
