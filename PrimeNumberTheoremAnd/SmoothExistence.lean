import Batteries.Tactic.Lemma
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Bound

set_option lang.lemmaCmd true

open MeasureTheory Set Real
open scoped ContDiff

-- This version makes the support of Ψ explicit, and this is easier for some later proofs
lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧ Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧
    Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧ (Function.support Ψ = Set.Ioo a d) := by

  have := exists_msmooth_zero_iff_one_iff_of_isClosed
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici)
    (isClosed_Icc)
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc,
        Set.mem_empty_iff_false, and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)

  rcases this with ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩

  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x|>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x|>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]

lemma Function.support_id : Function.support (fun x : ℝ ↦ x) = Iio 0 ∪ Ioi 0 := by
  ext x; simp only [mem_support, ne_eq, Iio_union_Ioi, mem_compl_iff, mem_singleton_iff]

/-%%
Let $\nu$ be a bumpfunction.
\begin{theorem}[SmoothExistence]\label{SmoothExistence}\lean{SmoothExistence}\leanok
There exists a smooth (once differentiable would be enough), nonnegative ``bumpfunction'' $\nu$,
 supported in $[1/2,2]$ with total mass one:
$$
\int_0^\infty \nu(x)\frac{dx}{x} = 1.
$$
\end{theorem}
%%-/

attribute [-simp] one_div in

lemma SmoothExistence : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    rcases h with ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]

  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3/2) (d := 2) (by linarith)
    (by linarith)
  rcases this with ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply', hνSupport, Function.support_id]
      have : (Ioo (1 / 2 : ℝ) 2 ∩ (Iio 0 ∪ Ioi 0) ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ici, mem_Iio, mem_Ioi, mem_union]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h; linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h; simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        apply subset_trans (by apply inter_subset_left) Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]; intros;linarith
/-%%
\begin{proof}\leanok
\uses{smooth-ury}
Same idea as Urysohn-type argument.
\end{proof}
%%-/
