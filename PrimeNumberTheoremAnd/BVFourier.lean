import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Measure

open scoped Real

open Real MeasureTheory Set Filter FourierTransform Function

namespace BVFourier

open scoped BigOperators

private lemma sum_Icc_edist_add_zsmul_le_eVariationOn (ψ : ℝ → ℂ) (x p : ℝ) (hp : 0 < p)
    (m : ℕ) :
    (∑ n ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        edist (ψ (x + (n + 1) • p)) (ψ (x + n • p))) ≤ eVariationOn ψ Set.univ := by
  classical
  -- Rewrite the finite sum over `Finset.Icc` as a sum over a range, then apply the definition of
  -- `eVariationOn` to the corresponding monotone sequence.
  set a : ℤ := -(m : ℤ)
  set b : ℤ := (m : ℤ)
  set N : ℕ := (b + 1 - a).toNat
  have hN : N = 2 * m + 1 := by
    -- `b + 1 - a = 2m + 1 ≥ 0`, so `toNat` is just coercion.
    -- We keep the proof as a `simp`-style arithmetic step.
    dsimp [N, a, b]
    -- `simp` knows `Int.toNat_of_nonneg` and `Int.neg_ofNat_eq` etc.
    omega
  -- The arithmetic progression `u k = x + (a + k)•p`.
  let u : ℕ → ℝ := fun k ↦ x + ((a + (k : ℤ)) • p)
  have hu : Monotone u := by
    intro i j hij
    have hij' : (a + (i : ℤ)) ≤ a + (j : ℤ) := by
      exact add_le_add_right (Int.ofNat_le.mpr hij) a
    -- Convert `zsmul` to multiplication to use monotonicity of multiplication by a nonnegative
    -- scalar.
    have : ((a + (i : ℤ)) : ℝ) * p ≤ ((a + (j : ℤ)) : ℝ) * p := by
      have : ((a + (i : ℤ)) : ℝ) ≤ ((a + (j : ℤ)) : ℝ) := by exact_mod_cast hij'
      exact mul_le_mul_of_nonneg_right this hp.le
    -- Now rewrite back to `zsmul`.
    simpa [u, zsmul_eq_mul] using add_le_add_right this x
  have hsum_le :
      (∑ i ∈ Finset.range N, edist (ψ (u (i + 1))) (ψ (u i))) ≤ eVariationOn ψ Set.univ :=
    eVariationOn.sum_le ψ N hu (fun _ ↦ mem_univ _)
  -- Convert the original sum to the range-sum appearing in `hsum_le`.
  have hrewrite :
      (∑ n ∈ Finset.Icc a b, edist (ψ (x + (n + 1) • p)) (ψ (x + n • p))) =
        ∑ i ∈ Finset.range N, edist (ψ (u (i + 1))) (ψ (u i)) := by
    -- Expand `Finset.Icc` using the `LocallyFiniteOrder` structure on `ℤ`.
    -- `Int.Icc_eq_finset_map` gives the required parametrization.
    simp [Int.Icc_eq_finset_map, N, u, a, b, Finset.sum_map, add_assoc, add_left_comm, add_comm]
  -- Finish.
  calc
    (∑ n ∈ Finset.Icc a b, edist (ψ (x + (n + 1) • p)) (ψ (x + n • p))) =
        ∑ i ∈ Finset.range N, edist (ψ (u (i + 1))) (ψ (u i)) := hrewrite
    _ ≤ eVariationOn ψ Set.univ := hsum_le

lemma tsum_edist_add_zsmul_le_eVariationOn (ψ : ℝ → ℂ) (x p : ℝ) (hp : 0 < p) :
    (∑' n : ℤ, edist (ψ (x + (n + 1) • p)) (ψ (x + n • p))) ≤ eVariationOn ψ Set.univ := by
  classical
  -- Use `tsum = iSup` of finite sums and bound each finite sum by a big interval.
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro s
  by_cases hs : s = ∅
  · simp [hs]
  -- Let `m` bound the absolute values of the finitely many indices in `s`.
  have hs' : s.Nonempty := Finset.nonempty_iff_ne_empty.2 hs
  have hsimg : (s.image Int.natAbs).Nonempty := hs'.image _
  let m : ℕ := (s.image Int.natAbs).max' hsimg
  have hsIcc : s ⊆ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    intro z hz
    have hzabs : z.natAbs ≤ m := by
      have : z.natAbs ∈ s.image Int.natAbs := Finset.mem_image.2 ⟨z, hz, rfl⟩
      exact Finset.le_max' _ _ this
    have hz_le : z ≤ (m : ℤ) := by
      calc
        z ≤ (z.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := z))
        _ ≤ (m : ℤ) := by exact_mod_cast hzabs
    have hm_le_z : (-(m : ℤ)) ≤ z := by
      -- `-z ≤ natAbs z ≤ m`, then negate.
      have hz_neg_le : (-z) ≤ (z.natAbs : ℤ) := by
        -- Use `Int.le_natAbs` applied to `-z`.
        simpa [Int.natAbs_neg] using (Int.le_natAbs (a := -z))
      have hz_neg_le_m : (-z) ≤ (m : ℤ) := le_trans hz_neg_le (by exact_mod_cast hzabs)
      simpa using (neg_le_neg hz_neg_le_m)
    exact Finset.mem_Icc.2 ⟨hm_le_z, hz_le⟩
  have hmono :
      Monotone (fun t : Finset ℤ =>
        ∑ n ∈ t, edist (ψ (x + (n + 1) • p)) (ψ (x + n • p))) :=
    Finset.sum_mono_set _
  have hle :
      (∑ n ∈ s, edist (ψ (x + (n + 1) • p)) (ψ (x + n • p))) ≤
        ∑ n ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), edist (ψ (x + (n + 1) • p)) (ψ (x + n • p)) :=
    hmono hsIcc
  exact hle.trans (sum_Icc_edist_add_zsmul_le_eVariationOn ψ x p hp m)

theorem lintegral_enorm_sub_translate_le (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (hvar : BoundedVariationOn ψ Set.univ) (h : ℝ) :
    (∫⁻ t : ℝ, ‖ψ (t + h) - ψ t‖ₑ) ≤ ENNReal.ofReal |h| * eVariationOn ψ Set.univ := by
  classical
  by_cases h0 : h = 0
  · subst h0
    simp
  -- Positive step size bound.
  have pos_case (p : ℝ) (hp : 0 < p) :
      (∫⁻ t : ℝ, ‖ψ (t + p) - ψ t‖ₑ) ≤ ENNReal.ofReal p * eVariationOn ψ Set.univ := by
    -- Partition `ℝ` into translates of `Ioc 0 p`.
    have hcover : (⋃ n : ℤ, Ioc (n • p) ((n + 1) • p)) = (Set.univ : Set ℝ) :=
      iUnion_Ioc_zsmul hp
    have hdisj : Pairwise (Disjoint on fun n : ℤ => Ioc (n • p) ((n + 1) • p)) :=
      by simpa [zero_add] using (pairwise_disjoint_Ioc_add_zsmul (0 : ℝ) p)
    have hmeas : ∀ n : ℤ, MeasurableSet (Ioc (n • p) ((n + 1) • p)) := fun _ =>
      measurableSet_Ioc
    have hcover' : (⋃ n : ℤ, Ioc (↑n * p) ((↑n + 1) * p)) = (Set.univ : Set ℝ) := by
      simpa [zsmul_eq_mul, add_assoc, add_left_comm, add_comm] using hcover
    -- Use `lintegral_iUnion` over the disjoint union.
    have hsum :
        (∫⁻ t : ℝ, ‖ψ (t + p) - ψ t‖ₑ) =
          ∑' n : ℤ, ∫⁻ t in Ioc (n • p) ((n + 1) • p), ‖ψ (t + p) - ψ t‖ₑ := by
      -- First rewrite as a set integral over `⋃ n, ... = univ`.
      simpa [MeasureTheory.setLIntegral_univ, hcover', zsmul_eq_mul, add_assoc, add_left_comm,
        add_comm] using
        (MeasureTheory.lintegral_iUnion (μ := volume) hmeas hdisj fun t =>
          ‖ψ (t + p) - ψ t‖ₑ)
    rw [hsum]
    -- Change variables on each interval to `Ioc 0 p`.
    have htrans (n : ℤ) :
        (∫⁻ t in Ioc (n • p) ((n + 1) • p), ‖ψ (t + p) - ψ t‖ₑ) =
          ∫⁻ x in Ioc 0 p, ‖ψ (x + (n + 1) • p) - ψ (x + n • p)‖ₑ := by
      -- Use measure-preserving translation by `n•p`.
      have hmp : MeasurePreserving (fun x : ℝ => x + n • p) volume volume := by
        simpa [add_comm] using (measurePreserving_add_right (μ := volume) (n • p))
      have hme : MeasurableEmbedding (fun x : ℝ => x + n • p) :=
        (MeasurableEquiv.addRight (n • p)).measurableEmbedding
      have himage :
          (fun x : ℝ => x + n • p) '' Ioc 0 p = Ioc (n • p) ((n + 1) • p) := by
        calc
          (fun x : ℝ => x + n • p) '' Ioc 0 p = Ioc ((0 : ℝ) + n • p) (p + n • p) :=
            Set.image_add_const_Ioc (n • p) (0 : ℝ) p
          _ = Ioc (n • p) ((n + 1) • p) := by
            have hn : p + n • p = (n + 1) • p := by
              calc
                p + n • p = n • p + p := by simpa [add_comm]
                _ = n • p + (1 : ℤ) • p := by simp
                _ = (n + 1) • p := by
                  simpa using (add_zsmul p n (1 : ℤ)).symm
            rw [hn]
            simp
      have hchange :
          (∫⁻ x in Ioc 0 p, ‖ψ ((x + n • p) + p) - ψ (x + n • p)‖ₑ) =
            ∫⁻ t in Ioc (n • p) ((n + 1) • p), ‖ψ (t + p) - ψ t‖ₑ := by
        have hchange' :
            (∫⁻ x in Ioc 0 p, ‖ψ ((x + n • p) + p) - ψ (x + n • p)‖ₑ) =
              ∫⁻ t in (fun x : ℝ => x + n • p) '' Ioc 0 p, ‖ψ (t + p) - ψ t‖ₑ := by
          simpa [add_assoc] using
            (hmp.setLIntegral_comp_emb hme (fun t : ℝ => ‖ψ (t + p) - ψ t‖ₑ) (Ioc 0 p))
        rw [himage] at hchange'
        exact hchange'
      simpa [add_assoc, add_left_comm, add_comm, add_mul, one_mul, mul_one, add_zsmul, one_zsmul] using
        hchange.symm
    simp_rw [htrans]
    -- Swap sum and integral.
    have hmeas_f : ∀ n : ℤ, AEMeasurable (fun x : ℝ => ‖ψ (x + (n + 1) • p) - ψ (x + n • p)‖ₑ)
        (volume.restrict (Ioc 0 p)) := by
      intro n
      have hψ₁ : Integrable (fun x : ℝ => ψ (x + (n + 1) • p)) := by
        simpa [Function.comp] using hψ.comp_add_right ((n + 1) • p)
      have hψ₂ : Integrable (fun x : ℝ => ψ (x + n • p)) := by
        simpa [Function.comp] using hψ.comp_add_right (n • p)
      have hmeas1 : AEMeasurable (fun x : ℝ => ψ (x + (n + 1) • p)) volume := hψ₁.aemeasurable
      have hmeas2 : AEMeasurable (fun x : ℝ => ψ (x + n • p)) volume := hψ₂.aemeasurable
      exact (hmeas1.sub hmeas2).enorm.restrict
    have hswap :
        (∑' n : ℤ, ∫⁻ x in Ioc 0 p, ‖ψ (x + (n + 1) • p) - ψ (x + n • p)‖ₑ) =
          ∫⁻ x in Ioc 0 p, ∑' n : ℤ, ‖ψ (x + (n + 1) • p) - ψ (x + n • p)‖ₑ := by
      simpa using
        (MeasureTheory.lintegral_tsum (μ := volume.restrict (Ioc 0 p)) hmeas_f).symm
    rw [hswap]
    -- Pointwise bound by total variation.
    have hpoint : ∀ x : ℝ,
        (∑' n : ℤ, ‖ψ (x + (n + 1) • p) - ψ (x + n • p)‖ₑ) ≤ eVariationOn ψ Set.univ := by
      intro x
      simpa [edist_eq_enorm_sub] using (tsum_edist_add_zsmul_le_eVariationOn ψ x p hp)
    -- Integrate the pointwise bound.
    have hle :
        (∫⁻ x in Ioc 0 p, ∑' n : ℤ, ‖ψ (x + (n + 1) • p) - ψ (x + n • p)‖ₑ) ≤
          ∫⁻ x in Ioc 0 p, eVariationOn ψ Set.univ := by
      refine MeasureTheory.setLIntegral_mono (μ := volume) (s := Ioc 0 p) (f := fun x =>
        ∑' n : ℤ, ‖ψ (x + (n + 1) • p) - ψ (x + n • p)‖ₑ) (g := fun _ => eVariationOn ψ Set.univ)
        measurable_const ?_
      intro x _
      exact hpoint x
    -- Compute the right-hand side integral of a constant.
    have hconst :
        (∫⁻ x in Ioc 0 p, eVariationOn ψ Set.univ) =
          ENNReal.ofReal p * eVariationOn ψ Set.univ := by
      simp [Real.volume_Ioc, mul_comm, mul_left_comm, mul_assoc]
    -- Put everything together.
    calc
      (∫⁻ x in Ioc 0 p, ∑' n : ℤ, ‖ψ (x + (n + 1) • p) - ψ (x + n • p)‖ₑ) ≤
          ∫⁻ x in Ioc 0 p, eVariationOn ψ Set.univ := hle
      _ = ENNReal.ofReal p * eVariationOn ψ Set.univ := hconst
  -- Reduce to the positive case by symmetry in `h`.
  rcases le_total 0 h with hh | hh
  · have hh' : 0 < h := lt_of_le_of_ne' hh (by simpa using h0)
    have := pos_case h hh'
    simpa [abs_of_nonneg hh] using this
  · have hlt : h < 0 := lt_of_le_of_ne hh (by simpa using h0)
    have hh' : 0 < -h := neg_pos.mpr hlt
    have heq :
        (∫⁻ t : ℝ, ‖ψ (t + h) - ψ t‖ₑ) = ∫⁻ t : ℝ, ‖ψ (t + (-h)) - ψ t‖ₑ := by
      have hmp : MeasurePreserving (fun t : ℝ => t + h) volume volume := by
        simpa [add_comm] using (measurePreserving_add_right (μ := volume) h)
      have hme : MeasurableEmbedding (fun t : ℝ => t + h) :=
        (MeasurableEquiv.addRight h).measurableEmbedding
      have := hmp.lintegral_comp_emb (μ := volume) (ν := volume) hme
        (fun t : ℝ => ‖ψ (t + (-h)) - ψ t‖ₑ)
      simpa [add_assoc, add_left_comm, add_comm, enorm_sub_rev] using this
    have hneg := pos_case (-h) hh'
    have : (∫⁻ t : ℝ, ‖ψ (t + h) - ψ t‖ₑ) ≤ ENNReal.ofReal (-h) * eVariationOn ψ Set.univ := by
      simpa [heq] using hneg
    simpa [abs_of_neg hlt] using this

theorem integral_norm_sub_translate_le (ψ : ℝ → ℂ) (hψ : Integrable ψ)
    (hvar : BoundedVariationOn ψ Set.univ) (h : ℝ) :
    ∫ t : ℝ, ‖ψ (t + h) - ψ t‖ ≤ |h| * (eVariationOn ψ Set.univ).toReal := by
  -- Convert to a `lintegral` bound and take `toReal`.
  have hlin :
      (∫⁻ t : ℝ, ‖ψ (t + h) - ψ t‖ₑ) ≤ ENNReal.ofReal |h| * eVariationOn ψ Set.univ :=
    lintegral_enorm_sub_translate_le ψ hψ hvar h
  -- Identify the integral as the `toReal` of the `lintegral`.
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ψ (t + h) - ψ t) volume := by
    have hψ_trans : Integrable (fun t : ℝ => ψ (t + h)) := by
      simpa [Function.comp] using hψ.comp_add_right h
    exact hψ_trans.1.sub hψ.1
  have hint :
      (∫ t : ℝ, ‖ψ (t + h) - ψ t‖) = (∫⁻ t : ℝ, ‖ψ (t + h) - ψ t‖ₑ).toReal := by
    simpa [integral_norm_eq_lintegral_enorm hmeas] using
      (integral_norm_eq_lintegral_enorm (μ := volume) (f := fun t : ℝ => ψ (t + h) - ψ t) hmeas)
  -- Take `toReal` of the `lintegral` inequality.
  have hb : ENNReal.ofReal |h| * eVariationOn ψ Set.univ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvar
  have ha : (∫⁻ t : ℝ, ‖ψ (t + h) - ψ t‖ₑ) ≠ ⊤ := ne_top_of_le_ne_top hb hlin
  have hreal :
      (∫⁻ t : ℝ, ‖ψ (t + h) - ψ t‖ₑ).toReal ≤
        (ENNReal.ofReal |h| * eVariationOn ψ Set.univ).toReal :=
    (ENNReal.toReal_le_toReal ha hb).2 hlin
  -- Simplify.
  simpa [hint, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg h)] using hreal

end BVFourier
