import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.VectorMeasure.AddContent
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

open Set MeasureTheory
open scoped ENNReal

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

end BoundedVariationOn
