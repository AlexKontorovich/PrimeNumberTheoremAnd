import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.VectorMeasure.AddContent
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory.VectorMeasure

variable {α E : Type*} [MeasurableSpace α] [AddCommGroup E] [TopologicalSpace E] [T2Space E]

lemma ext_of_generateFrom_of_univ {S : Set (Set α)} {μ ν : VectorMeasure α E}
    (h_gen : ‹MeasurableSpace α› = MeasurableSpace.generateFrom S) (h_inter : IsPiSystem S)
    (h_univ : μ univ = ν univ) (h_eq : ∀ s ∈ S, μ s = ν s) : μ = ν := by
  refine VectorMeasure.ext ?_
  intro t ht
  induction t, ht using MeasurableSpace.induction_on_inter h_gen h_inter with
  | empty => simp
  | basic u hu => exact h_eq u hu
  | compl u hu ihu =>
      rw [VectorMeasure.of_compl hu, VectorMeasure.of_compl hu, h_univ, ihu]
  | iUnion f hfd hfm ihf =>
      rw [VectorMeasure.of_disjoint_iUnion hfm hfd, VectorMeasure.of_disjoint_iUnion hfm hfd]
      exact tsum_congr ihf

end MeasureTheory.VectorMeasure

namespace BoundedVariationOn

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : ℝ → E}

theorem vectorMeasure_variation_univ_le_eVariationOn (hf : BoundedVariationOn f Set.univ) :
    (hf.vectorMeasure).variation Set.univ ≤ eVariationOn f Set.univ := by
  let μaux : Measure ℝ := (hf.stieltjesFunctionRightLim (0 : ℝ)).measure
  haveI : IsFiniteMeasure μaux := by
    dsimp [μaux]
    apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
      (C := (eVariationOn f.rightLim Set.univ).toReal)
    intro x
    exact variationOnFromTo.abs_le_eVariationOn hf.rightLim
  let m : AddContent E {s : Set ℝ | ∃ u v, u ≤ v ∧ s = Ioc u v} :=
    AddContent.onIoc f.rightLim
  have hdom : ∀ s ∈ {s : Set ℝ | ∃ u v, u ≤ v ∧ s = Ioc u v}, ‖m s‖ₑ ≤ μaux s := by
    rintro s ⟨u, v, huv, rfl⟩
    rw [AddContent.onIoc_apply huv]
    simp only [μaux, StieltjesFunction.measure_Ioc,
      BoundedVariationOn.stieltjesFunctionRightLim_apply]
    rw [← variationOnFromTo.add hf.rightLim.locallyBoundedVariationOn
      (mem_univ (0 : ℝ)) (mem_univ u) (mem_univ v)]
    simp only [add_sub_cancel_left, variationOnFromTo, huv, ↓reduceIte, univ_inter]
    rw [ENNReal.ofReal_toReal]
    · rw [← edist_eq_enorm_sub]
      exact eVariationOn.edist_le _ (by grind) (by grind)
    · exact ((eVariationOn.mono _ (subset_univ _)).trans_lt hf.rightLim.lt_top).ne
  have hgen_le : (inferInstance : MeasurableSpace ℝ) =
      MeasurableSpace.generateFrom {s : Set ℝ | ∃ u v, u ≤ v ∧ s = Ioc u v} := by
    borelize ℝ
    change borel ℝ = MeasurableSpace.generateFrom {s : Set ℝ | ∃ u v, u ≤ v ∧ s = Ioc u v}
    rw [borel_eq_generateFrom_Ioc_le ℝ]
    congr 1
    ext s
    constructor
    · rintro ⟨u, v, huv, hs⟩
      exact ⟨u, v, huv, hs.symm⟩
    · rintro ⟨u, v, huv, hs⟩
      exact ⟨u, v, huv, hs.symm⟩
  rcases VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    MeasureTheory.IsSetSemiring.Ioc hdom hgen_le with ⟨m', hm', hm_bound⟩
  have h_on_le : ∀ s ∈ {s : Set ℝ | ∃ u v, u ≤ v ∧ s = Ioc u v},
      m' s = hf.vectorMeasure s := by
    rintro s ⟨u, v, huv, rfl⟩
    rw [hm' _ ⟨u, v, huv, rfl⟩, AddContent.onIoc_apply huv, hf.vectorMeasure_Ioc huv]
  have h_univ : m' Set.univ = hf.vectorMeasure Set.univ := by
    have hsets : (⋃ n : ℤ, Ioc ((n : ℤ) : ℝ) (((n : ℤ) : ℝ) + 1)) =
        (Set.univ : Set ℝ) := by
      simpa using iUnion_Ioc_intCast ℝ
    rw [← hsets]
    rw [VectorMeasure.of_disjoint_iUnion, VectorMeasure.of_disjoint_iUnion]
    · apply tsum_congr
      intro n
      exact h_on_le _ ⟨(n : ℝ), (n : ℝ) + 1, by linarith, rfl⟩
    · intro i
      exact measurableSet_Ioc
    · exact Set.pairwise_disjoint_Ioc_intCast ℝ
    · intro i
      exact measurableSet_Ioc
    · exact Set.pairwise_disjoint_Ioc_intCast ℝ
  have hgen_strict : (inferInstance : MeasurableSpace ℝ) =
      MeasurableSpace.generateFrom {s : Set ℝ | ∃ u v, u < v ∧ Ioc u v = s} := by
    borelize ℝ
    exact borel_eq_generateFrom_Ioc ℝ
  have h_ext : m' = hf.vectorMeasure := by
    refine VectorMeasure.ext_of_generateFrom_of_univ hgen_strict
      (isPiSystem_Ioc (fun x : ℝ => x) (fun x : ℝ => x)) h_univ ?_
    rintro s ⟨u, v, huv, rfl⟩
    exact h_on_le _ ⟨u, v, huv.le, rfl⟩
  rw [← h_ext]
  have hvar_le : m'.variation ≤ μaux :=
    VectorMeasure.variation_le_of_forall_enorm_le fun s _hs => hm_bound s
  calc
    m'.variation Set.univ ≤ μaux Set.univ := hvar_le Set.univ
    _ ≤ eVariationOn f Set.univ := by
      have hcover : (⋃ n : ℕ, Ioc (-(n : ℝ)) (n : ℝ)) = (Set.univ : Set ℝ) := by
        ext x
        simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
        obtain ⟨n, hn⟩ := exists_nat_gt |x|
        refine ⟨n, ?_, ?_⟩
        · linarith [neg_abs_le x]
        · exact (le_abs_self x).trans hn.le
      have hmono : Monotone (fun n : ℕ => Ioc (-(n : ℝ)) (n : ℝ)) := by
        intro n m hnm
        have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
        exact Set.Ioc_subset_Ioc (by linarith) hnmR
      calc
        μaux Set.univ = μaux (⋃ n : ℕ, Ioc (-(n : ℝ)) (n : ℝ)) := by rw [hcover]
        _ = ⨆ n : ℕ, μaux (Ioc (-(n : ℝ)) (n : ℝ)) := hmono.measure_iUnion
        _ ≤ eVariationOn f Set.univ := by
          rw [iSup_le_iff]
          intro n
          have hnnonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
          have hnle : -(n : ℝ) ≤ (n : ℝ) := by linarith
          calc
            μaux (Ioc (-(n : ℝ)) (n : ℝ))
                = eVariationOn f.rightLim (Set.univ ∩ Icc (-(n : ℝ)) (n : ℝ)) := by
              simp only [μaux, StieltjesFunction.measure_Ioc,
                BoundedVariationOn.stieltjesFunctionRightLim_apply]
              rw [← variationOnFromTo.add hf.rightLim.locallyBoundedVariationOn
                (mem_univ (0 : ℝ)) (mem_univ (-(n : ℝ))) (mem_univ (n : ℝ))]
              simp only [add_sub_cancel_left, variationOnFromTo, hnle, ↓reduceIte]
              rw [ENNReal.ofReal_toReal]
              exact ((eVariationOn.mono _ inter_subset_left).trans_lt hf.rightLim.lt_top).ne
            _ ≤ eVariationOn f.rightLim Set.univ := eVariationOn.mono _ inter_subset_left
            _ ≤ eVariationOn f Set.univ := eVariationOn.eVariationOn_rightLim_le

theorem limUnder_atTop_eq_zero_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) :
    limUnder atTop f = 0 := by
  apply IntegrableAtFilter.eq_zero_of_tendsto (hfi.integrableAtFilter atTop) ?_
    hf.tendsto_atTop_limUnder
  intro s hs
  rcases mem_atTop_sets.mp hs with ⟨a, ha⟩
  rw [← top_le_iff]
  calc
    ∞ = volume (Set.Ici a) := by rw [Real.volume_Ici]
    _ ≤ volume s := measure_mono ha

theorem tendsto_atTop_zero_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) :
    Tendsto f atTop (𝓝 0) := by
  simpa [hf.limUnder_atTop_eq_zero_of_integrable hfi] using hf.tendsto_atTop_limUnder

theorem limUnder_atBot_eq_zero_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) :
    limUnder atBot f = 0 := by
  apply IntegrableAtFilter.eq_zero_of_tendsto (hfi.integrableAtFilter atBot) ?_
    hf.tendsto_atBot_limUnder
  intro s hs
  rcases mem_atBot_sets.mp hs with ⟨a, ha⟩
  rw [← top_le_iff]
  calc
    ∞ = volume (Set.Iic a) := by rw [Real.volume_Iic]
    _ ≤ volume s := measure_mono ha

theorem tendsto_atBot_zero_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) :
    Tendsto f atBot (𝓝 0) := by
  simpa [hf.limUnder_atBot_eq_zero_of_integrable hfi] using hf.tendsto_atBot_limUnder

theorem ae_eq_rightLim_real {f : ℝ → ℝ} (hf : BoundedVariationOn f Set.univ) :
    f =ᵐ[volume] f.rightLim := by
  rcases hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn with
    ⟨p, q, hp, hq, hpq⟩
  have hp_mono : Monotone p := monotoneOn_univ.mp hp
  have hq_mono : Monotone q := monotoneOn_univ.mp hq
  have h_count : Set.Countable {x | ¬ ContinuousAt f x} := by
    refine (hp_mono.countable_not_continuousAt.union hq_mono.countable_not_continuousAt).mono ?_
    intro x hx
    by_contra hx'
    have hp_cont : ContinuousAt p x := by
      by_contra hp_cont'
      exact hx' (Or.inl hp_cont')
    have hq_cont : ContinuousAt q x := by
      by_contra hq_cont'
      exact hx' (Or.inr hq_cont')
    exact hx (by rw [hpq]; exact hp_cont.sub hq_cont)
  have h_null : volume {x | ¬ ContinuousAt f x} = 0 :=
    h_count.measure_zero volume
  have h_eq : ∀ x, ContinuousAt f x → f x = f.rightLim x := by
    intro x hx
    exact hx.continuousWithinAt.rightLim_eq.symm
  have h_sub : {x | f x ≠ f.rightLim x} ⊆ {x | ¬ ContinuousAt f x} := by
    intro x hx
    by_contra hx'
    exact hx (h_eq x (not_not.mp hx'))
  exact ae_iff.mpr (measure_mono_null h_sub h_null)

theorem ae_eq_rightLim_complex {f : ℝ → ℂ} (hf : BoundedVariationOn f Set.univ) :
    f =ᵐ[volume] f.rightLim := by
  have hre_bv : BoundedVariationOn (fun x : ℝ => (f x).re) Set.univ :=
    Complex.reCLM.lipschitz.comp_boundedVariationOn hf
  have him_bv : BoundedVariationOn (fun x : ℝ => (f x).im) Set.univ :=
    Complex.imCLM.lipschitz.comp_boundedVariationOn hf
  have hre_ae := hre_bv.ae_eq_rightLim_real
  have him_ae := him_bv.ae_eq_rightLim_real
  have hre_lim (x : ℝ) :
      (fun y : ℝ => (f y).re).rightLim x = (f.rightLim x).re := by
    exact tendsto_nhds_unique (hre_bv.tendsto_rightLim x)
      (Complex.continuous_re.continuousAt.tendsto.comp (hf.tendsto_rightLim x))
  have him_lim (x : ℝ) :
      (fun y : ℝ => (f y).im).rightLim x = (f.rightLim x).im := by
    exact tendsto_nhds_unique (him_bv.tendsto_rightLim x)
      (Complex.continuous_im.continuousAt.tendsto.comp (hf.tendsto_rightLim x))
  filter_upwards [hre_ae, him_ae] with x hxre hxim
  exact Complex.ext (by simpa [hre_lim x] using hxre) (by simpa [him_lim x] using hxim)

theorem vectorMeasure_univ_eq_zero_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) :
    hf.vectorMeasure Set.univ = 0 := by
  rw [hf.vectorMeasure_univ, hf.limUnder_atTop_eq_zero_of_integrable hfi,
    hf.limUnder_atBot_eq_zero_of_integrable hfi, sub_self]

theorem vectorMeasure_Ici_eq_neg_leftLim_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) (a : ℝ) :
    hf.vectorMeasure (Set.Ici a) = -f.leftLim a := by
  rw [hf.vectorMeasure_Ici, hf.limUnder_atTop_eq_zero_of_integrable hfi, zero_sub]

theorem vectorMeasure_Ioi_eq_neg_rightLim_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) (a : ℝ) :
    hf.vectorMeasure (Set.Ioi a) = -f.rightLim a := by
  rw [hf.vectorMeasure_Ioi, hf.limUnder_atTop_eq_zero_of_integrable hfi, zero_sub]

theorem vectorMeasure_Iic_eq_rightLim_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) (a : ℝ) :
    hf.vectorMeasure (Set.Iic a) = f.rightLim a := by
  rw [hf.vectorMeasure_Iic, hf.limUnder_atBot_eq_zero_of_integrable hfi, sub_zero]

theorem vectorMeasure_Iio_eq_leftLim_of_integrable (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) (a : ℝ) :
    hf.vectorMeasure (Set.Iio a) = f.leftLim a := by
  rw [hf.vectorMeasure_Iio, hf.limUnder_atBot_eq_zero_of_integrable hfi, sub_zero]

theorem mapRange_re_vectorMeasure_eq {f : ℝ → ℂ} (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) :
    hf.vectorMeasure.mapRange Complex.reCLM.toAddMonoidHom Complex.continuous_re =
      (Complex.reCLM.lipschitz.comp_boundedVariationOn hf).vectorMeasure := by
  let hfre : BoundedVariationOn (fun x : ℝ => (f x).re) Set.univ :=
    Complex.reCLM.lipschitz.comp_boundedVariationOn hf
  have hfre_i : Integrable (fun x : ℝ => (f x).re) volume :=
    ContinuousLinearMap.integrable_comp Complex.reCLM hfi
  have hre_lim (x : ℝ) :
      (fun y : ℝ => (f y).re).rightLim x = (f.rightLim x).re := by
    exact tendsto_nhds_unique (hfre.tendsto_rightLim x)
      (Complex.continuous_re.continuousAt.tendsto.comp (hf.tendsto_rightLim x))
  have h_univ :
      hf.vectorMeasure.mapRange Complex.reCLM.toAddMonoidHom Complex.continuous_re Set.univ =
        hfre.vectorMeasure Set.univ := by
    rw [VectorMeasure.mapRange_apply]
    rw [hf.vectorMeasure_univ_eq_zero_of_integrable hfi,
      hfre.vectorMeasure_univ_eq_zero_of_integrable hfre_i]
    simp
  have hgen : (inferInstance : MeasurableSpace ℝ) =
      MeasurableSpace.generateFrom {s : Set ℝ | ∃ u v, u < v ∧ Ioc u v = s} := by
    borelize ℝ
    exact borel_eq_generateFrom_Ioc ℝ
  refine MeasureTheory.VectorMeasure.ext_of_generateFrom_of_univ hgen
    (isPiSystem_Ioc (fun x : ℝ => x) (fun x : ℝ => x)) h_univ ?_
  rintro s ⟨u, v, huv, rfl⟩
  rw [VectorMeasure.mapRange_apply, hf.vectorMeasure_Ioc huv.le,
    (Complex.reCLM.lipschitz.comp_boundedVariationOn hf).vectorMeasure_Ioc huv.le]
  simp [Function.comp_def, hre_lim u, hre_lim v]

theorem mapRange_im_vectorMeasure_eq {f : ℝ → ℂ} (hf : BoundedVariationOn f Set.univ)
    (hfi : Integrable f volume) :
    hf.vectorMeasure.mapRange Complex.imCLM.toAddMonoidHom Complex.continuous_im =
      (Complex.imCLM.lipschitz.comp_boundedVariationOn hf).vectorMeasure := by
  let hfim : BoundedVariationOn (fun x : ℝ => (f x).im) Set.univ :=
    Complex.imCLM.lipschitz.comp_boundedVariationOn hf
  have hfim_i : Integrable (fun x : ℝ => (f x).im) volume :=
    ContinuousLinearMap.integrable_comp Complex.imCLM hfi
  have him_lim (x : ℝ) :
      (fun y : ℝ => (f y).im).rightLim x = (f.rightLim x).im := by
    exact tendsto_nhds_unique (hfim.tendsto_rightLim x)
      (Complex.continuous_im.continuousAt.tendsto.comp (hf.tendsto_rightLim x))
  have h_univ :
      hf.vectorMeasure.mapRange Complex.imCLM.toAddMonoidHom Complex.continuous_im Set.univ =
        hfim.vectorMeasure Set.univ := by
    rw [VectorMeasure.mapRange_apply]
    rw [hf.vectorMeasure_univ_eq_zero_of_integrable hfi,
      hfim.vectorMeasure_univ_eq_zero_of_integrable hfim_i]
    simp
  have hgen : (inferInstance : MeasurableSpace ℝ) =
      MeasurableSpace.generateFrom {s : Set ℝ | ∃ u v, u < v ∧ Ioc u v = s} := by
    borelize ℝ
    exact borel_eq_generateFrom_Ioc ℝ
  refine MeasureTheory.VectorMeasure.ext_of_generateFrom_of_univ hgen
    (isPiSystem_Ioc (fun x : ℝ => x) (fun x : ℝ => x)) h_univ ?_
  rintro s ⟨u, v, huv, rfl⟩
  rw [VectorMeasure.mapRange_apply, hf.vectorMeasure_Ioc huv.le,
    (Complex.imCLM.lipschitz.comp_boundedVariationOn hf).vectorMeasure_Ioc huv.le]
  simp [Function.comp_def, him_lim u, him_lim v]

end BoundedVariationOn
