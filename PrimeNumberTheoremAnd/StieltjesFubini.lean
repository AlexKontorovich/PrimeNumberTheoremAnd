import Architect
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Topology.EMetricSpace.BoundedVariation
import PrimeNumberTheoremAnd.Fourier
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics
import PrimeNumberTheoremAnd.SmoothExistence

open MeasureTheory Set Filter Complex ContinuousLinearMap
open scoped ENNReal

lemma p_sub_p (p : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    (p b - p a : ℂ) = ∫ _x in Ioc a b, (1 : ℂ) ∂p.measure := by
  have H1 : ∫ _x in Ioc a b, (1 : ℂ) ∂p.measure = (p.measure (Ioc a b)).toReal := by
    rw [integral_const]
    simp [measureReal_def]
  have h_meas : p.measure (Ioc a b) = ENNReal.ofReal (p b - p a) := p.measure_Ioc a b
  rw [H1, h_meas, ENNReal.toReal_ofReal (sub_nonneg.mpr (p.mono hab))]
  push_cast
  rfl

lemma FubiniIntegrabilityGap (p : StieltjesFunction ℝ) (a b : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (hab : a ≤ b) (F : ℝ → ℝ → ℂ)
    (hF : F = fun x t ↦ if x ∈ Ioc a t then f t else 0) :
    Integrable (Function.uncurry fun t x ↦ F x t)
      ((volume.restrict (Ioc a b)).prod (p.measure.restrict (Ioc a b))) := by
  let S : Set (ℝ × ℝ) := { tx | a < tx.2 ∧ tx.2 ≤ tx.1 }
  have hS_meas : MeasurableSet S := by
    have h1 : MeasurableSet { tx : ℝ × ℝ | a < tx.2 } :=
      measurableSet_lt measurable_const measurable_snd
    have h2 : MeasurableSet { tx : ℝ × ℝ | tx.2 ≤ tx.1 } :=
      measurableSet_le measurable_snd measurable_fst
    exact h1.inter h2
  have hF_eq : (Function.uncurry fun t x ↦ F x t) = S.indicator (fun tx ↦ f tx.1) := by
    ext tx
    simp only [Function.uncurry, hF, S, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioc]
  have h_cont : Continuous (fun tx : ℝ × ℝ ↦ f tx.1) := hf.comp continuous_fst
  have hF_meas : StronglyMeasurable (Function.uncurry fun t x ↦ F x t) := by
    rw [hF_eq]
    exact (h_cont.stronglyMeasurable.indicator hS_meas)
  have h_comp : IsCompact (Icc a b) := isCompact_Icc
  have h_cont_norm : ContinuousOn (fun x ↦ ‖f x‖) (Icc a b) := hf.continuousOn.norm
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Icc a b, ‖f x‖ ≤ C := by
    have : BddAbove ((fun x ↦ ‖f x‖) '' Icc a b) :=
      h_comp.bddAbove_image h_cont_norm
    rcases this with ⟨C, hC⟩
    use C
    intro x hx
    exact hC (Set.mem_image_of_mem _ hx)
  haveI h_fin_p : IsFiniteMeasure (p.measure.restrict (Ioc a b)) := ⟨by simp [p.measure_Ioc]⟩
  haveI h_fin_vol : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp⟩
  have h_int_const :
      Integrable (fun _ : ℝ × ℝ ↦ (C : ℂ))
        ((volume.restrict (Ioc a b)).prod (p.measure.restrict (Ioc a b))) := by
    apply integrable_const
  apply h_int_const.mono hF_meas.aestronglyMeasurable
  have h_prod_restrict :
      (volume.restrict (Ioc a b)).prod (p.measure.restrict (Ioc a b)) =
        (volume.prod p.measure).restrict (Ioc a b ×ˢ Ioc a b) :=
    Measure.prod_restrict (Ioc a b) (Ioc a b)
  rw [h_prod_restrict]
  have h_meas_prod : MeasurableSet (Ioc a b ×ˢ Ioc a b) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  filter_upwards [ae_restrict_mem h_meas_prod] with tx htx
  rw [hF_eq]
  simp only [Set.indicator_apply]
  have h_norm_C : ‖(C : ℂ)‖ = C := by
    have hC_pos : 0 ≤ C := (norm_nonneg (f a)).trans (hC a (left_mem_Icc.mpr hab))
    have h1 : ‖(C : ℂ)‖ = ‖C‖ := Complex.norm_real C
    have h2 : ‖C‖ = C := Real.norm_of_nonneg hC_pos
    rw [h1, h2]
  rw [h_norm_C]
  split_ifs with h_S
  · exact hC tx.1 ⟨htx.1.1.le, htx.1.2⟩
  · simp only [norm_zero]
    exact (norm_nonneg (f a)).trans (hC a (left_mem_Icc.mpr hab))

theorem integral_stieltjes_fubini_swap (p : StieltjesFunction ℝ) (a b : ℝ) (hab : a ≤ b)
    (f : ℝ → ℂ) (hf : Continuous f) :
    ∫ t in a..b, (p t - p a : ℂ) * f t =
      ∫ x in Ioc a b, (∫ t in x..b, f t) ∂p.measure := by
  rw [intervalIntegral.integral_of_le hab]
  have h_inner : ∀ t ∈ Ioc a b,
      (p t - p a : ℂ) * f t = ∫ x in Ioc a t, f t ∂p.measure := by
    intro t ht
    have H_smul :
        (∫ x in Ioc a t, (1 : ℂ) ∂p.measure) * f t =
          f t • (∫ x in Ioc a t, (1 : ℂ) ∂p.measure) := mul_comm _ _
    rw [p_sub_p p ht.1.le, H_smul, ← integral_smul]
    simp
  have H :
      ∫ t in Ioc a b, (p t - p a : ℂ) * f t =
        ∫ t in Ioc a b, ∫ x in Ioc a t, f t ∂p.measure ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact h_inner t ht
  let F : ℝ → ℝ → ℂ := fun x t ↦ if x ∈ Ioc a t then f t else 0
  have H_F_LHS : ∀ t ∈ Ioc a b,
      ∫ x in Ioc a t, f t ∂p.measure = ∫ x in Ioc a b, F x t ∂p.measure := by
    intro t ht
    have : (fun x ↦ F x t) = (Ioc a t).indicator (fun _ ↦ f t) := by
      ext x
      simp only [F, indicator_apply]
    rw [this, integral_indicator measurableSet_Ioc]
    have h_inter : Ioc a t ∩ Ioc a b = Ioc a t :=
      inter_eq_left.mpr (Ioc_subset_Ioc le_rfl ht.2)
    rw [Measure.restrict_restrict measurableSet_Ioc, h_inter]
  have H_F_RHS : ∀ x ∈ Ioc a b,
      ∫ t in Ioc a b, F x t ∂volume = ∫ t in Ioc x b, f t ∂volume := by
    intro x hx
    have : ∫ t in Ioc a b, F x t ∂volume = ∫ t in Icc x b, f t ∂volume := by
      have : (fun t ↦ F x t) = (Ici x).indicator (fun t ↦ f t) := by
        ext t
        have heq : x ∈ Ioc a t ↔ t ∈ Ici x := by
          simp only [mem_Ioc, mem_Ici]
          exact and_iff_right hx.1
        simp only [F, indicator_apply, heq]
      rw [this, integral_indicator measurableSet_Ici]
      have h_inter : Ici x ∩ Ioc a b = Icc x b := by
        ext t
        simp only [mem_inter_iff, mem_Icc, mem_Ioc, mem_Ici]
        constructor
        · rintro ⟨hxt, ⟨hat, htb⟩⟩
          exact ⟨hxt, htb⟩
        · rintro ⟨hxt, htb⟩
          exact ⟨hxt, ⟨hx.1.trans_le hxt, htb⟩⟩
      rw [Measure.restrict_restrict measurableSet_Ici, h_inter]
    rw [this]
    exact integral_Icc_eq_integral_Ioc
  have H_swap :
      ∫ t in Ioc a b, ∫ x in Ioc a b, F x t ∂p.measure ∂volume =
        ∫ x in Ioc a b, ∫ t in Ioc a b, F x t ∂volume ∂p.measure := by
    apply integral_integral_swap
    exact FubiniIntegrabilityGap p a b f hf hab F rfl
  have H_LHS :
      ∫ t in Ioc a b, (p t - p a : ℂ) * f t =
        ∫ t in Ioc a b, ∫ x in Ioc a b, F x t ∂p.measure ∂volume := by
    rw [H]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact H_F_LHS t ht
  have H_RHS :
      ∫ x in Ioc a b, ∫ t in Ioc x b, f t ∂volume ∂p.measure =
        ∫ x in Ioc a b, ∫ t in Ioc a b, F x t ∂volume ∂p.measure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (H_F_RHS x hx).symm
  rw [H_LHS, H_swap, ← H_RHS]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact (intervalIntegral.integral_of_le hx.2).symm

theorem integral_stieltjes_by_parts_sub_base (p : StieltjesFunction ℝ) (a b : ℝ)
    (hab : a ≤ b) (g g' : ℝ → ℂ) (hg : Continuous g) (hg' : Continuous g')
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) :
    ∫ x in Ioc a b, g x ∂p.measure =
      g b * (p b - p a : ℂ) - ∫ t in a..b, (p t - p a : ℂ) * g' t := by
  have hswap := integral_stieltjes_fubini_swap p a b hab g' hg'
  have hinner : ∀ x ∈ Ioc a b, ∫ t in x..b, g' t = g b - g x := by
    intro x hx
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.2 hg.continuousOn ?_ ?_
    · intro y hy
      exact hderiv y ⟨hx.1.le.trans hy.1.le, hy.2.le⟩
    · exact hg'.intervalIntegrable x b
  have hswap' :
      ∫ t in a..b, (p t - p a : ℂ) * g' t =
        ∫ x in Ioc a b, (g b - g x) ∂p.measure := by
    rw [hswap]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hinner x hx
  have hfinite : p.measure (Ioc a b) ≠ ∞ := by
    simp [p.measure_Ioc]
  have hg_int : Integrable g (p.measure.restrict (Ioc a b)) := by
    have h_comp : IsCompact (Icc a b) := isCompact_Icc
    have h_cont_norm : ContinuousOn (fun x => ‖g x‖) (Icc a b) := hg.continuousOn.norm
    obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Icc a b, ‖g x‖ ≤ C := by
      have : BddAbove ((fun x => ‖g x‖) '' Icc a b) :=
        h_comp.bddAbove_image h_cont_norm
      rcases this with ⟨C, hC⟩
      exact ⟨C, fun x hx => hC (mem_image_of_mem _ hx)⟩
    exact Measure.integrableOn_of_bounded hfinite hg.aestronglyMeasurable
      (M := C) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact hC x ⟨hx.1.le, hx.2⟩)
  haveI : IsFiniteMeasure (p.measure.restrict (Ioc a b)) := ⟨by simp⟩
  have hconst_int : Integrable (fun _ : ℝ => g b) (p.measure.restrict (Ioc a b)) :=
    integrable_const _
  have hsplit :
      ∫ x in Ioc a b, (g b - g x) ∂p.measure =
        g b * (p b - p a : ℂ) - ∫ x in Ioc a b, g x ∂p.measure := by
    rw [integral_sub hconst_int hg_int, integral_const]
    simp [measureReal_def, p.measure_Ioc, ENNReal.toReal_ofReal,
      sub_nonneg.mpr (p.mono hab), mul_comm]
  rw [hswap', hsplit]
  ring

theorem integral_signed_stieltjes_by_parts_sub_base (p q : StieltjesFunction ℝ) (a b : ℝ)
    (hab : a ≤ b) (g g' : ℝ → ℂ) (hg : Continuous g) (hg' : Continuous g')
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hp_int : IntervalIntegrable (fun t => (p t - p a : ℂ) * g' t) volume a b)
    (hq_int : IntervalIntegrable (fun t => (q t - q a : ℂ) * g' t) volume a b) :
    (∫ x in Ioc a b, g x ∂p.measure) - (∫ x in Ioc a b, g x ∂q.measure) =
      g b * ((p b - p a : ℂ) - (q b - q a : ℂ)) -
        ∫ t in a..b, ((p t - p a : ℂ) - (q t - q a : ℂ)) * g' t := by
  have hp := integral_stieltjes_by_parts_sub_base p a b hab g g' hg hg' hderiv
  have hq := integral_stieltjes_by_parts_sub_base q a b hab g g' hg hg' hderiv
  rw [hp, hq]
  let A := g b * (p b - p a : ℂ)
  let B := g b * (q b - q a : ℂ)
  let Ip := ∫ t in a..b, (p t - p a : ℂ) * g' t
  let Iq := ∫ t in a..b, (q t - q a : ℂ) * g' t
  have hI :
      Ip - Iq =
        ∫ t in a..b, ((p t - p a : ℂ) - (q t - q a : ℂ)) * g' t := by
    dsimp [Ip, Iq]
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro t ht
      ring
    · exact hp_int
    · exact hq_int
  change (A - Ip) - (B - Iq) =
    g b * ((p b - p a : ℂ) - (q b - q a : ℂ)) -
      ∫ t in a..b, ((p t - p a : ℂ) - (q t - q a : ℂ)) * g' t
  rw [show (A - Ip) - (B - Iq) = (A - B) - (Ip - Iq) by ring, hI]
  dsimp [A, B]
  ring
