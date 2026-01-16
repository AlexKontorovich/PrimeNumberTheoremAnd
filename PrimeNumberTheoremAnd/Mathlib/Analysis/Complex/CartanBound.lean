import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardLogSingularity

/-!
## Cartan / minimum-modulus infrastructure for intrinsic Hadamard factorization

This file contains the “probabilistic radius” / averaging lemmas used in Tao’s proof of
Hadamard factorization (Theorem 22 in the blog notes), in a form that does **not** depend on
`ZeroData`.  The key analytic input is the soft bound

`max 0 (log (1 / |1 - t|)) ≤ sqrt (2 / |1 - t|)`,

which yields an integrable majorant for the logarithmic singularity when averaging on dyadic
intervals.

The later “application” layer will plug in `a := ‖zero‖` and weights equal to the divisor
multiplicity.
-/

noncomputable section

namespace Complex.Hadamard

open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal

/-! ### A radial majorant for the logarithmic singularity on a circle -/

lemma posLog_log_one_div_norm_one_sub_le_posLog_log_one_div_abs_one_sub
    {t : ℝ} (ht : t ≠ 1) (w : ℂ) (hw : ‖w‖ = t) :
    max 0 (Real.log (1 / ‖(1 : ℂ) - w‖))
      ≤ max 0 (Real.log (1 / |1 - t|)) := by
  -- Reverse triangle: `|1 - t| = |‖1‖ - ‖w‖| ≤ ‖1 - w‖`.
  have hrev : |(‖(1 : ℂ)‖ : ℝ) - ‖w‖| ≤ ‖(1 : ℂ) - w‖ :=
    abs_norm_sub_norm_le (1 : ℂ) w
  have hrev' : |1 - t| ≤ ‖(1 : ℂ) - w‖ := by
    simpa [hw] using hrev
  have ht0 : |1 - t| ≠ 0 := by
    have : (1 : ℝ) - t ≠ 0 := by
      intro h
      have : (t : ℝ) = 1 := (sub_eq_zero.mp h).symm
      exact ht this
    simpa [abs_eq_zero] using this
  have htpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm ht0)
  by_cases hw0 : ‖(1 : ℂ) - w‖ = 0
  · -- Then `w = 1`, hence `t = 1`, contradicting `ht`.
    have hw1 : w = (1 : ℂ) := by
      have : (1 : ℂ) - w = 0 := by simpa [norm_eq_zero] using hw0
      simpa [eq_comm] using (sub_eq_zero.mp this)
    have : t = 1 := by
      have : ‖w‖ = (1 : ℝ) := by simp [hw1]
      simpa [hw] using this
    exact (ht this).elim
  have hwpos : 0 < ‖(1 : ℂ) - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  have hdiv :
      (1 / ‖(1 : ℂ) - w‖ : ℝ) ≤ (1 / |1 - t| : ℝ) :=
    one_div_le_one_div_of_le htpos hrev'
  have hlog :
      Real.log (1 / ‖(1 : ℂ) - w‖) ≤ Real.log (1 / |1 - t|) := by
    have hposL : 0 < (1 / ‖(1 : ℂ) - w‖ : ℝ) := by positivity
    exact Real.log_le_log hposL hdiv
  -- Apply `max` monotonicity.
  exact max_le_max le_rfl hlog

/-! ### A coarse dyadic-interval bound for the singularity average -/

namespace LogSingularity

def φ (t : ℝ) : ℝ :=
  max 0 (Real.log (1 / |1 - t|))

lemma φ_nonneg (t : ℝ) : 0 ≤ φ t := by simp [φ]

lemma φ_le_sqrt (t : ℝ) : φ t ≤ Real.sqrt (2 / |1 - t|) := by
  simpa [φ] using (Complex.Hadamard.posLog_log_one_div_abs_one_sub_le_sqrt (t := t))

lemma log_ge_neg_max0_log_inv {x : ℝ} (_hx : 0 ≤ x) :
    Real.log x ≥ - max 0 (Real.log (1 / x)) := by
  have : max 0 (Real.log (1 / x)) = max 0 (-Real.log x) := by
    simp [Real.log_inv]
  rw [this]
  by_cases hlog : 0 ≤ Real.log x
  · have hmax : max 0 (-Real.log x) = 0 := max_eq_left (by linarith)
    simpa [hmax] using hlog
  · have hlog' : Real.log x ≤ 0 := le_of_not_ge hlog
    have hmax : max 0 (-Real.log x) = -Real.log x := max_eq_right (by linarith)
    simp [hmax]

noncomputable def K : ℝ :=
  ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume

lemma K_nonneg : 0 ≤ K := by
  have hle : (1 / 4 : ℝ) ≤ (4 : ℝ) := by norm_num
  have hnn : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (4 : ℝ), 0 ≤ Real.sqrt (2 / |1 - t|) := by
    intro _t _ht
    exact Real.sqrt_nonneg _
  simpa [K] using (intervalIntegral.integral_nonneg (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)

noncomputable def Cφ : ℝ :=
  Real.log 2 + 4 * K + 1

lemma Cφ_pos : 0 < Cφ := by
  have hlog : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hK : 0 ≤ K := K_nonneg
  have : 0 < Real.log 2 + 4 * K := by nlinarith
  have : 0 < Real.log 2 + 4 * K + 1 := by linarith
  simpa [Cφ] using this

lemma intervalIntegrable_sqrt_two_div_abs_one_sub_Icc :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (4 : ℝ) := by
  -- Reduce to integrability of `u ↦ sqrt(2/|u|)` on `[0,3]`, then split at the singularity.
  let f : ℝ → ℝ := fun u => Real.sqrt (2 / |u|)

  have hf0 : IntervalIntegrable f volume (0 : ℝ) (3 : ℝ) := by
    have hpow : IntervalIntegrable (fun u : ℝ => u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (3 : ℝ))
          (r := (- (2⁻¹ : ℝ))) (by linarith : (-1 : ℝ) < - (2⁻¹ : ℝ)))
    have hpow2 :
        IntervalIntegrable (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) :=
      hpow.const_mul (Real.sqrt 2)
    have hEq :
        Set.EqOn f (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (Set.uIoc (0 : ℝ) (3 : ℝ)) := by
      intro u hu
      have hu' : u ∈ Set.Ioc (0 : ℝ) (3 : ℝ) := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 3 by norm_num)] using hu
      have hu0 : 0 < u := hu'.1
      have hu0' : 0 ≤ u := le_of_lt hu0
      have habs : |u| = u := abs_of_nonneg hu0'
      have : f u = Real.sqrt (2 / u) := by simp [f, habs]
      calc
        f u = Real.sqrt (2 / u) := this
        _ = Real.sqrt 2 / Real.sqrt u := by simp
        _ = Real.sqrt 2 * (Real.sqrt u)⁻¹ := by simp [div_eq_mul_inv]
        _ = Real.sqrt 2 * (u ^ (2⁻¹ : ℝ))⁻¹ := by simp [Real.sqrt_eq_rpow]
        _ = Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ)) := by
              have h : (u ^ (2⁻¹ : ℝ))⁻¹ = u ^ (- (2⁻¹ : ℝ)) := by
                simpa using (Real.rpow_neg hu0' (2⁻¹ : ℝ)).symm
              simp [h]
    exact (IntervalIntegrable.congr (a := (0 : ℝ)) (b := (3 : ℝ)) (μ := (volume : MeasureTheory.Measure ℝ))
      (f := fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (g := f) hEq.symm) hpow2

  have hf0' : IntervalIntegrable f volume (0 : ℝ) (3 / 4 : ℝ) :=
    hf0.mono_set (by
      intro u hu
      have hsub : Set.uIcc (0 : ℝ) (3 / 4 : ℝ) ⊆ Set.uIcc (0 : ℝ) (3 : ℝ) := by
        refine Set.uIcc_subset_uIcc ?_ ?_
        · simp
        ·
          have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) := by nlinarith
          have h1 : (3 / 4 : ℝ) ≤ (3 : ℝ) := by nlinarith
          exact (Set.mem_uIcc).2 (Or.inl ⟨h0, h1⟩)
      exact hsub hu)

  -- Left part: `t ∈ [1/4,1]` corresponds to `u = 1 - t ∈ [0,3/4]`.
  have hleft : IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (1 : ℝ) := by
    have htmp : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 : ℝ) ((1 : ℝ) - (3 / 4 : ℝ)) := by
      simpa using (hf0'.comp_sub_left (c := (1 : ℝ)))
    have htmp' : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume ((1 : ℝ) - (3 / 4 : ℝ)) (1 : ℝ) := htmp.symm
    have hsub : ((1 : ℝ) - (3 / 4 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    have htmp'' : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 / 4 : ℝ) (1 : ℝ) := by
      simpa [hsub] using htmp'
    simpa [f] using htmp''

  -- Right part: `t ∈ [1,4]` corresponds to `u = t - 1 ∈ [0,3]`.
  have hright : IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 : ℝ) (4 : ℝ) := by
    have htmp : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) ((3 : ℝ) + (1 : ℝ)) := by
      simpa using (hf0.comp_sub_right (c := (1 : ℝ)))
    have hsub : ((3 : ℝ) + (1 : ℝ)) = (4 : ℝ) := by norm_num
    have htmp' : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) (4 : ℝ) := by
      simpa [hsub] using htmp
    have hcongr :
        Set.EqOn (fun t : ℝ => f (t - 1)) (fun t : ℝ => Real.sqrt (2 / |1 - t|)) (Set.uIoc (1 : ℝ) (4 : ℝ)) := by
      intro t _ht
      simp [f, abs_sub_comm]
    exact (IntervalIntegrable.congr (a := (1 : ℝ)) (b := (4 : ℝ)) (μ := (volume : MeasureTheory.Measure ℝ))
      (f := fun t : ℝ => f (t - 1)) (g := fun t : ℝ => Real.sqrt (2 / |1 - t|)) hcongr) htmp'

  exact hleft.trans hright

lemma intervalIntegrable_phi_dyadic {A : ℝ} (hA : 0 ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  classical
  by_cases hA0 : A = 0
  · subst hA0
    simp
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hA_le : A ≤ 2 * A := by nlinarith

  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      have hφ_le : ∀ t ∈ Set.Icc A (2 * A), φ t ≤ Real.log 2 := by
        intro t ht
        have ht_le : t ≤ (1 / 2 : ℝ) := by
          have : t ≤ 2 * A := ht.2
          exact this.trans (by nlinarith [hsmall])
        have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
          have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
          have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
          simpa [abs_of_nonneg hnonneg] using this
        have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
          have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
          have := one_div_le_one_div_of_le hhalfpos hden
          simpa [one_div, div_eq_mul_inv] using this
        have hxpos : 0 < (1 / |1 - t| : ℝ) := by positivity
        have hlog : Real.log (1 / |1 - t|) ≤ Real.log 2 := Real.log_le_log hxpos hfrac
        have hlog2_nonneg : 0 ≤ Real.log 2 := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact Real.log_nonneg this
        have : max 0 (Real.log (1 / |1 - t|)) ≤ Real.log 2 := by
          simpa [max_le_iff] using And.intro hlog2_nonneg hlog
        simpa [φ] using this

      have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
        intervalIntegral.intervalIntegrable_const
      have hmeas : AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) := by
        have : Measurable φ := by
          unfold φ
          fun_prop
        exact this.aestronglyMeasurable
      have hdom :
          (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))] fun _ => ‖(Real.log 2 : ℝ)‖ := by
        refine MeasureTheory.ae_restrict_of_forall_mem
          (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.uIoc A (2 * A))
          (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A (2 * A)))) ?_
        intro t ht
        have htIoc : t ∈ Set.Ioc A (2 * A) := by
          simpa [Set.uIoc_of_le hA_le] using ht
        have ht' : t ∈ Set.Icc A (2 * A) := ⟨le_of_lt htIoc.1, htIoc.2⟩
        have hφt : φ t ≤ Real.log 2 := hφ_le t ht'
        have hφt0 : 0 ≤ φ t := φ_nonneg t
        have hlog2_nn : 0 ≤ (Real.log 2 : ℝ) := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact Real.log_nonneg this
        simpa [Real.norm_eq_abs, abs_of_nonneg hφt0, abs_of_nonneg hlog2_nn] using hφt
      exact IntervalIntegrable.mono_fun hconst hmeas hdom
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          have hEq : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIoc A (2 * A)) := by
            intro t ht
            have htIoc : t ∈ Set.Ioc A (2 * A) := by
              simpa [Set.uIoc_of_le hA_le] using ht
            have ht2 : (2 : ℝ) ≤ t := le_trans hbig (le_of_lt htIoc.1)
            have hden : (1 : ℝ) ≤ |1 - t| := by
              have : (1 : ℝ) ≤ t - 1 := by linarith
              have : (1 : ℝ) ≤ |t - 1| := by
                simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
              simpa [abs_sub_comm] using this
            have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := by
              have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) hden
              exact (div_le_one hpos).2 hden
            have hpos : 0 < (1 / |1 - t| : ℝ) := by positivity
            have hlog : Real.log (1 / |1 - t|) ≤ 0 :=
              le_trans (Real.log_le_log hpos hfrac) (by simp)
            have : max 0 (Real.log (1 / |1 - t|)) = 0 := max_eq_left hlog
            simpa [φ] using this
          have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A (2 * A) :=
            intervalIntegral.intervalIntegrable_const
          exact (IntervalIntegrable.congr (a := A) (b := (2 * A)) (μ := (volume : MeasureTheory.Measure ℝ))
            (f := fun _ => (0 : ℝ)) (g := fun t => φ t) (by
              intro t ht
              simpa using (hEq (x := t) ht).symm)) hz
      | inr hA_le_two =>
          have hsqrt_big :
              IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (4 : ℝ) :=
            intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
          have hsqrt :
              IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) := by
            refine hsqrt_big.mono_set ?_
            refine Set.uIcc_subset_uIcc ?_ ?_
            · exact (Set.mem_uIcc).2 (Or.inl ⟨hge_quarter, by nlinarith [hA_le_two]⟩)
            · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hge_quarter], by nlinarith [hA_le_two]⟩)
          have hmeas : AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) := by
            have : Measurable φ := by
              unfold φ
              fun_prop
            exact this.aestronglyMeasurable
          have hdom :
              (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
                fun t => ‖Real.sqrt (2 / |1 - t|)‖ := by
            refine MeasureTheory.ae_restrict_of_forall_mem
              (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.uIoc A (2 * A))
              (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A (2 * A)))) ?_
            intro t ht
            have htIoc : t ∈ Set.Ioc A (2 * A) := by
              simpa [Set.uIoc_of_le hA_le] using ht
            have ht' : t ∈ Set.Icc A (2 * A) := ⟨le_of_lt htIoc.1, htIoc.2⟩
            have hle : φ t ≤ Real.sqrt (2 / |1 - t|) := φ_le_sqrt t
            have hφ0 : 0 ≤ φ t := φ_nonneg t
            have hs0 : 0 ≤ Real.sqrt (2 / |1 - t|) := Real.sqrt_nonneg _
            calc
              ‖φ t‖ = φ t := by rw [Real.norm_of_nonneg hφ0]
              _ ≤ Real.sqrt (2 / |1 - t|) := hle
              _ = ‖Real.sqrt (2 / |1 - t|)‖ := by
                    symm
                    rw [Real.norm_of_nonneg hs0]
          exact IntervalIntegrable.mono_fun hsqrt hmeas hdom

lemma intervalIntegrable_phi_div {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    IntervalIntegrable (fun r : ℝ => φ (r / a)) volume R (2 * R) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hRa_nonneg : 0 ≤ R / a := by
    exact div_nonneg hR (le_of_lt ha)
  have hφ : IntervalIntegrable φ volume (R / a) (2 * (R / a)) :=
    intervalIntegrable_phi_dyadic (A := (R / a)) hRa_nonneg
  have := (hφ.comp_mul_right (c := (a⁻¹ : ℝ)))
  have hupper : a * (R * (a⁻¹ * 2)) = (2 * R) := by
    field_simp [ha0]
  simpa [div_eq_mul_inv, ha0, hupper, mul_assoc, mul_left_comm, mul_comm] using this

lemma integral_phi_le_Cφ_mul {A : ℝ} (hA : 0 ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  classical
  by_cases hA0 : A = 0
  · subst hA0
    simp [Cφ, φ, K]
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hA_le : A ≤ 2 * A := by nlinarith
  have hCφ_nn : 0 ≤ Cφ := le_of_lt Cφ_pos

  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      have hφ_le : ∀ t ∈ Set.Icc A (2 * A), φ t ≤ Real.log 2 := by
        intro t ht
        have ht_le : t ≤ (1 / 2 : ℝ) := by
          have : t ≤ 2 * A := ht.2
          have : t ≤ (1 / 2 : ℝ) := this.trans (by nlinarith [hsmall])
          exact this
        have hlog2_nonneg : 0 ≤ Real.log 2 := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact Real.log_nonneg this
        have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
          have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
          have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
          simpa [abs_of_nonneg hnonneg] using this
        have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
          have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
          have := one_div_le_one_div_of_le hhalfpos hden
          simpa [one_div, div_eq_mul_inv] using this
        have hxpos : 0 < (1 / |1 - t| : ℝ) := by positivity
        have hlog : Real.log (1 / |1 - t|) ≤ Real.log 2 := Real.log_le_log hxpos hfrac
        have : max 0 (Real.log (1 / |1 - t|)) ≤ Real.log 2 := by
          simpa [max_le_iff] using And.intro hlog2_nonneg hlog
        simpa [φ] using this

      have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
        intervalIntegral.intervalIntegrable_const
      have hmeas : AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) := by
        have : Measurable φ := by
          unfold φ
          fun_prop
        exact this.aestronglyMeasurable
      have hdom : (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))] fun _ => ‖(Real.log 2 : ℝ)‖ := by
        refine MeasureTheory.ae_restrict_of_forall_mem
          (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.uIoc A (2 * A))
          (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A (2 * A)))) ?_
        intro t ht
        have htIoc : t ∈ Set.Ioc A (2 * A) := by
          simpa [Set.uIoc_of_le hA_le] using ht
        have ht' : t ∈ Set.Icc A (2 * A) := ⟨le_of_lt htIoc.1, htIoc.2⟩
        have hφt : φ t ≤ Real.log 2 := hφ_le t ht'
        have hφt0 : 0 ≤ φ t := φ_nonneg t
        have hlog2_nn : 0 ≤ (Real.log 2 : ℝ) := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact Real.log_nonneg this
        simpa [Real.norm_eq_abs, abs_of_nonneg hφt0, abs_of_nonneg hlog2_nn] using hφt
      have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
        IntervalIntegrable.mono_fun hconst hmeas hdom
      have hle_int :
          (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ ∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume := by
        refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ)) hA_le hφ_int hconst ?_
        intro t ht
        exact hφ_le t ht
      have hRHS : (∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume) = A * Real.log 2 := by
        simp [intervalIntegral.integral_const, sub_eq_add_neg, add_assoc, two_mul]
      have hcoef : A * Real.log 2 ≤ Cφ * A := by
        have hlog_le : Real.log 2 ≤ Cφ := by
          dsimp [Cφ]
          have hK : 0 ≤ K := K_nonneg
          linarith [hK]
        have := mul_le_mul_of_nonneg_left hlog_le hA
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      calc
        (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
            ≤ A * Real.log 2 := by simpa [hRHS] using hle_int
        _ ≤ Cφ * A := hcoef

  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          have hφ0 : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIcc A (2 * A)) := by
            intro t ht
            have ht' : t ∈ Set.Icc A (2 * A) := by
              simpa [Set.uIcc_of_le hA_le] using ht
            have htA : A ≤ t := ht'.1
            have ht2 : 2 ≤ t := le_trans hbig htA
            have hden : 1 ≤ |1 - t| := by
              have : (1 : ℝ) ≤ t - 1 := by linarith
              have : (1 : ℝ) ≤ |t - 1| := by simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
              simpa [abs_sub_comm] using this
            have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := by
              have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) hden
              exact (div_le_one hpos).2 hden
            have hpos : 0 < (1 / |1 - t| : ℝ) := by positivity
            have hlog : Real.log (1 / |1 - t|) ≤ 0 :=
              le_trans (Real.log_le_log hpos hfrac) (by simp)
            have : max 0 (Real.log (1 / |1 - t|)) = 0 := max_eq_left hlog
            simpa [φ] using this
          have : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) = 0 := by
            simpa using intervalIntegral.integral_congr (μ := (volume : MeasureTheory.Measure ℝ)) hφ0
          have hnonneg : (0 : ℝ) ≤ Cφ * A := mul_nonneg hCφ_nn hA
          simpa [this] using hnonneg
      | inr hA_le_two =>
          have hA_lower : (1 / 4 : ℝ) ≤ A := hge_quarter
          have hA_upper : (2 * A : ℝ) ≤ 4 := by nlinarith [hA_le_two]
          let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
          have hsqrt_big :
              IntervalIntegrable s volume (1 / 4 : ℝ) (4 : ℝ) :=
            intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
          have hsqrt :
              IntervalIntegrable s volume A (2 * A) := by
            refine hsqrt_big.mono_set ?_
            refine Set.uIcc_subset_uIcc ?_ ?_
            · exact (Set.mem_uIcc).2 (Or.inl ⟨hA_lower, by nlinarith [hA_le_two]⟩)
            · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hA_lower], hA_upper⟩)
          have hmeasφ : AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) := by
            have : Measurable φ := by
              unfold φ
              fun_prop
            exact this.aestronglyMeasurable
          have hdomφ : (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))] fun t => ‖s t‖ := by
            refine MeasureTheory.ae_restrict_of_forall_mem
              (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.uIoc A (2 * A))
              (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A (2 * A)))) ?_
            intro t ht
            have htIoc : t ∈ Set.Ioc A (2 * A) := by
              simpa [Set.uIoc_of_le hA_le] using ht
            have ht' : t ∈ Set.Icc A (2 * A) := ⟨le_of_lt htIoc.1, htIoc.2⟩
            have hle : φ t ≤ s t := φ_le_sqrt t
            have hφ0 : 0 ≤ φ t := φ_nonneg t
            have hs0 : 0 ≤ s t := Real.sqrt_nonneg _
            simpa [Real.norm_eq_abs, abs_of_nonneg hφ0, abs_of_nonneg hs0] using hle
          have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
            IntervalIntegrable.mono_fun hsqrt hmeasφ hdomφ
          have hle_int :
              (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
                ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := by
            refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ)) hA_le hφ_int hsqrt ?_
            intro t _ht
            exact φ_le_sqrt t
          have hle_K :
              (∫ (t : ℝ) in A..(2 * A), s t ∂volume)
                ≤ ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume := by
            refine intervalIntegral.integral_mono_interval (μ := (volume : MeasureTheory.Measure ℝ))
              (c := (1 / 4 : ℝ)) (d := (4 : ℝ)) (a := A) (b := (2 * A))
              hA_lower hA_le hA_upper ?_ hsqrt_big
            exact Filter.Eventually.of_forall (fun _t => Real.sqrt_nonneg _)
          have hKdef : (∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume) = K := by
            rfl
          have hK : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ K := by
            -- Ensure both sides use the same unfolded integrand to avoid `simp` rewriting only one side.
            simpa [hKdef, K, s] using hle_K
          -- `∫_{A}^{2A} s ≤ K` and `K ≤ (Cφ - log 2 - 1)/4`; package as `Cφ*A` bound.
          have : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ (4 * K + 1) * A := by
            have hA_le4 : A ≤ 4 := le_trans hA_le_two (by norm_num)
            -- crude: `∫ ≤ K` and `K ≤ (4K+1)*A` for `A ≥ 1/4`
            have : K ≤ (4 * K + 1) * A := by
              have hcoef : 1 ≤ 4 * A := by nlinarith [hA_lower]
              have hK' : 0 ≤ K := K_nonneg
              nlinarith [hK', hcoef]
            exact le_trans hK this
          have hlog2 : (Real.log 2) * A ≤ Cφ * A := by
            have hlog_le : Real.log 2 ≤ Cφ := by
              dsimp [Cφ]
              have hK : 0 ≤ K := K_nonneg
              linarith [hK]
            have := mul_le_mul_of_nonneg_left hlog_le hA
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
          -- Combine the middle-scale estimate with the `log 2` additive slack.
          calc
            (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
                ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := hle_int
            _ ≤ (4 * K + 1) * A := this
            _ ≤ Cφ * A := by
                  -- `4*K+1 ≤ log2 + 4*K + 1 = Cφ`
                  have : (4 * K + 1 : ℝ) ≤ Cφ := by
                    dsimp [Cφ]
                    have hlog_nonneg : 0 ≤ Real.log 2 := by
                      exact Real.log_nonneg (by norm_num)
                    linarith [hlog_nonneg]
                  exact mul_le_mul_of_nonneg_right this hA

end LogSingularity
end Complex.Hadamard
