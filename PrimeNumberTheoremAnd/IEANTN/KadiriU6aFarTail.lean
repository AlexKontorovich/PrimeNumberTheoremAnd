import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeights
import PrimeNumberTheoremAnd.IEANTN.KadiriContourShift
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# U6a far-tail lane: the zero-sum remainder from a single local-count atom

This file reorganizes the open partial-fraction estimate
`U6aZeroSumRemainderBoundHypothesis` around one named analytic atom, the
classical unit-window zero count `N(t+1) - N(t) = O(log t)`
(`U6aLocalZeroCountLogHypothesis`).  Every count-free piece is composed here:
the global xi Hadamard sum splits into the finite nearby fiber plus the far
remainder, the nearby residue is the already-proved convergence-factor bound,
and the triangle inequality assembles the target estimate from the far-tail
bound and the count atom.

The analytic discharge of the atom (and of the far tail, which follows from
the atom at shifted heights through the anchor-difference argument) requires
strip growth of `(s-1) * zeta s` left of `Re = 0`, which in turn rides
Stirling-grade decay of the complex Gamma function — the named upstream arc.
Until that lands, this file isolates exactly what remains.
-/

namespace Kadiri

open Complex MeasureTheory
open scoped Topology

noncomputable section

/-- The single remaining analytic atom of the U6a partial-fraction route: the
classical local zero count `N(t+1) - N(t) = O(log t)` over Kadiri's nearby
window, multiplicity-weighted.  Classically true (Backlund / Davenport
paragraph 15); its in-tree discharge is gated on strip growth of the completed
zeta function, hence on complex Stirling decay. -/
def U6aLocalZeroCountLogHypothesis (C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ t : ℝ, Tₘᵢₙ ≤ |t| → 3 ≤ |t| →
    u6aNearbyZeroCount (-1) 2 t ≤ C * Real.log |t|

/-- The far part of the global xi Hadamard zero sum: everything outside the
finite nearby fiber. -/
noncomputable def u6aXiFarHadamardRemainder (t : ℝ) (s : ℂ) : ℂ :=
  u6aXiHadamardZeroSum s - u6aXiFiberNearbyHadamardSum t s

/-- The far-tail estimate, the second count-gated input: classically it
follows from the count atom at shifted heights through the anchor-difference
argument at `2 + i t`. -/
def U6aFarTailBoundHypothesis (C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ s : ℂ, s.re ∈ Set.uIcc (-1 : ℝ) 2 → Tₘᵢₙ ≤ |s.im| → 3 ≤ |s.im| →
    ‖u6aXiFarHadamardRemainder s.im s‖ ≤ C * Real.log |s.im|

/-- Exact decomposition: the zero-sum remainder is the far tail plus the
nearby fiber residue. -/
theorem u6aXiHadamardZeroSum_sub_nearbyPrincipal_eq (t : ℝ) (s : ℂ) :
    u6aXiHadamardZeroSum s - u6aNearbyZeroPrincipalSum (-1) 2 t s =
      u6aXiFarHadamardRemainder t s +
        (u6aXiFiberNearbyHadamardSum t s - u6aNearbyZeroPrincipalSum (-1) 2 t s) := by
  unfold u6aXiFarHadamardRemainder
  ring

/-- The open `U6aZeroSumRemainderBoundHypothesis` composes from the far-tail
bound and the local-count atom: the count-free content of the partial-fraction
zero-sum estimate. -/
theorem U6aZeroSumRemainderBoundHypothesis_of_farTail_and_count
    {Cfar Ccnt Tₘᵢₙ : ℝ}
    (hfar : U6aFarTailBoundHypothesis Cfar Tₘᵢₙ)
    (hcnt : U6aLocalZeroCountLogHypothesis Ccnt Tₘᵢₙ) :
    U6aZeroSumRemainderBoundHypothesis (-1) 2 (Cfar + Ccnt) Tₘᵢₙ := by
  obtain ⟨hCfar, hfar⟩ := hfar
  obtain ⟨hCcnt, hcnt⟩ := hcnt
  refine ⟨by linarith, fun s hre hT h3 => ?_⟩
  rw [u6aXiHadamardZeroSum_sub_nearbyPrincipal_eq s.im s]
  have h1 := hfar s hre hT h3
  have h2 := norm_u6aXiFiberNearbyHadamardSum_sub_nearbyZeroPrincipalSum_le_nearbyZeroCount
    (t := s.im) s (by linarith)
  have h3' := hcnt s.im hT h3
  calc ‖u6aXiFarHadamardRemainder s.im s +
        (u6aXiFiberNearbyHadamardSum s.im s - u6aNearbyZeroPrincipalSum (-1) 2 s.im s)‖
      ≤ ‖u6aXiFarHadamardRemainder s.im s‖ +
        ‖u6aXiFiberNearbyHadamardSum s.im s - u6aNearbyZeroPrincipalSum (-1) 2 s.im s‖ :=
        norm_add_le _ _
    _ ≤ Cfar * Real.log |s.im| + Ccnt * Real.log |s.im| := by
        have := le_trans h2 h3'
        linarith
    _ = (Cfar + Ccnt) * Real.log |s.im| := by ring

/-! ## The finite/global bridge: splitting the Hadamard tsum at the window -/

/-- The nearby window of zeta zeros, as a set. -/
def u6aFTNearbyWindow (t : ℝ) : Set ℂ :=
  riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2) (Set.Icc (t - 1) (t + 1))

theorem u6aFTNearbyWindow_finite (t : ℝ) : (u6aFTNearbyWindow t).Finite := by
  have h := zeroes_rect_uIcc_finite ((-1 : ℂ) + (t - 1) * I) ((2 : ℂ) + (t + 1) * I)
  have hre1 : ((-1 : ℂ) + (t - 1) * I).re = -1 := by simp
  have hre2 : ((2 : ℂ) + (t + 1) * I).re = 2 := by simp
  have him1 : ((-1 : ℂ) + (t - 1) * I).im = t - 1 := by simp
  have him2 : ((2 : ℂ) + (t + 1) * I).im = t + 1 := by simp
  rw [hre1, hre2, him1, him2, Set.uIcc_of_le (by linarith : t - 1 ≤ t + 1)] at h
  exact h

/-- The nearby window pulled back to the xi divisor index: the union of the
finite fibers over the windowed zeros. -/
noncomputable def u6aXiNearbyIndexFinset (t : ℝ) :
    Finset (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
  letI : DecidableEq (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
    Classical.decEq _
  (u6aFTNearbyWindow_finite t).toFinset.biUnion
    fun ρ => Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ

/-- Membership in the pulled-back window is membership of the value in the
window. -/
theorem mem_u6aXiNearbyIndexFinset_iff (t : ℝ)
    (p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    p ∈ u6aXiNearbyIndexFinset t ↔
      Complex.Hadamard.divisorZeroIndex₀_val p ∈ u6aFTNearbyWindow t := by
  unfold u6aXiNearbyIndexFinset
  letI : DecidableEq (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
    Classical.decEq _
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨ρ, hρ, hp⟩
    rw [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] at hp
    rw [hp]
    exact (Set.Finite.mem_toFinset _).mp hρ
  · intro hval
    exact ⟨Complex.Hadamard.divisorZeroIndex₀_val p, (Set.Finite.mem_toFinset _).mpr hval,
      (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset _ _ _).mpr rfl⟩

/-- The nearby fiber double sum is the single sum over the pulled-back window. -/
theorem u6aXiFiberNearbyHadamardSum_eq_indexFinset_sum (t : ℝ) (s : ℂ) :
    u6aXiFiberNearbyHadamardSum t s =
      ∑ p ∈ u6aXiNearbyIndexFinset t,
        ((1 : ℂ) / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  letI : DecidableEq (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
    Classical.decEq _
  unfold u6aXiFiberNearbyHadamardSum u6aXiNearbyIndexFinset
  rw [Finset.sum_biUnion (by
    intro ρ₁ _ ρ₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] at hp1 hp2
    exact hne (hp1 ▸ hp2))]
  refine Finset.sum_congr ?_ fun ρ _ => rfl
  ext ρ
  simp only [Set.Finite.mem_toFinset]
  rfl

/-- The finite/global bridge: at any point off the indexed zero set, the
global xi Hadamard sum splits into the nearby fiber sum plus the far-tail
tsum over the complement of the pulled-back window. -/
theorem u6aXiHadamardZeroSum_eq_nearby_add_farTail (t : ℝ) {s : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    u6aXiHadamardZeroSum s =
      u6aXiFiberNearbyHadamardSum t s +
        ∑' p : {p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) //
            p ∉ u6aXiNearbyIndexFinset t},
          ((1 : ℂ) / (s - Complex.Hadamard.divisorZeroIndex₀_val p.val) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p.val) := by
  have hsum := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (z := s) hz
  have hsplit := hsum.sum_add_tsum_subtype_compl (u6aXiNearbyIndexFinset t)
  unfold u6aXiHadamardZeroSum
  rw [← hsplit, u6aXiFiberNearbyHadamardSum_eq_indexFinset_sum]

/-- The far remainder is exactly the complement tsum: the analytic far-tail
estimate may now be attacked termwise. -/
theorem u6aXiFarHadamardRemainder_eq_tsum_compl (t : ℝ) {s : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    u6aXiFarHadamardRemainder t s =
      ∑' p : {p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) //
          p ∉ u6aXiNearbyIndexFinset t},
        ((1 : ℂ) / (s - Complex.Hadamard.divisorZeroIndex₀_val p.val) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p.val) := by
  unfold u6aXiFarHadamardRemainder
  linear_combination u6aXiHadamardZeroSum_eq_nearby_add_farTail t hz

/-! ## Location of the xi zeros and the off-window geometry -/

theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  have h := riemannXi_one_sub 1
  simpa [riemannXi_zero] using h.symm

/-- The xi function does not vanish right of the critical strip. -/
theorem riemannXi_ne_zero_of_one_lt_re {z : ℂ} (hz : 1 < z.re) : riemannXi z ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz; linarith
  have hz1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz
  rw [riemannXi_eq_mul_completedRiemannZeta hz0 hz1]
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hΓ : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hcompleted : completedRiemannZeta z ≠ 0 := by
    intro h
    apply hζ
    rw [riemannZeta_def_of_ne_zero hz0, h, zero_div]
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hz0 hsub) hcompleted) two_ne_zero

/-- The xi zeros lie in the closed critical strip. -/
theorem riemannXi_zero_re_mem {z : ℂ} (hz : riemannXi z = 0) :
    z.re ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · by_contra h
    push Not at h
    have h1z : 1 < (1 - z).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    exact riemannXi_ne_zero_of_one_lt_re h1z (by rw [riemannXi_one_sub]; exact hz)
  · by_contra h
    push Not at h
    exact riemannXi_ne_zero_of_one_lt_re h hz
/-- A xi zero away from `0` and `1` is a zeta zero. -/
theorem riemannZeta_eq_zero_of_riemannXi_eq_zero {z : ℂ} (hz : riemannXi z = 0)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) : riemannZeta z = 0 := by
  have hcompleted : completedRiemannZeta z = 0 := by
    have h := riemannXi_eq_mul_completedRiemannZeta hz0 hz1
    rw [hz] at h
    have h2 : z * (z - 1) * completedRiemannZeta z = 0 := by linear_combination (-2 : ℂ) * h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hz0
      · exact absurd (by linear_combination h4) hz1
    · exact h3
  rw [riemannZeta_def_of_ne_zero hz0, hcompleted, zero_div]

/-- Index points of the xi divisor are xi zeros. -/
theorem riemannXi_val_eq_zero
    (p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    riemannXi (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
  by_contra hxi
  have hmero : MeromorphicOn riemannXi Set.univ := fun x _ =>
    (Differentiable.analyticAt (f := riemannXi) differentiable_riemannXi x).meromorphicAt
  have han : AnalyticAt ℂ riemannXi (Complex.Hadamard.divisorZeroIndex₀_val p) :=
    Differentiable.analyticAt (f := riemannXi) differentiable_riemannXi _
  have hdiv : (MeromorphicOn.divisor riemannXi Set.univ)
      (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
    rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ _), han.meromorphicOrderAt_eq]
    have horder : analyticOrderAt riemannXi (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hxi)
    simp [horder]
  exact Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p hdiv

/-- Off the pulled-back window, an index point is imaginary-far from the
height: its value is either a nontrivial zeta zero outside the window strip,
or a real exceptional point, and both force `|Im - t| > 1` once `|t| ≥ 3`. -/
theorem u6aFT_offWindow_im_far {t : ℝ} (ht : 3 ≤ |t|)
    (p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ))
    (hp : p ∉ u6aXiNearbyIndexFinset t) :
    1 < |(Complex.Hadamard.divisorZeroIndex₀_val p).im - t| := by
  by_contra h
  push Not at h
  apply hp
  rw [mem_u6aXiNearbyIndexFinset_iff]
  set z := Complex.Hadamard.divisorZeroIndex₀_val p with hzdef
  have hxi : riemannXi z = 0 := riemannXi_val_eq_zero p
  have habs := abs_le.mp h
  have him : z.im ∈ Set.Icc (t - 1) (t + 1) :=
    ⟨by linarith [habs.1], by linarith [habs.2]⟩
  have himne : z.im ≠ 0 := by
    intro h0
    rw [h0] at him
    have habs2 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [him.2], by linarith [him.1]⟩
    linarith
  have hz0 : z ≠ 0 := fun hc => himne (by rw [hc]; simp)
  have hz1 : z ≠ 1 := fun hc => himne (by rw [hc]; simp)
  have hζ : riemannZeta z = 0 := riemannZeta_eq_zero_of_riemannXi_eq_zero hxi hz0 hz1
  have hre := riemannXi_zero_re_mem hxi
  refine ⟨?_, him, hζ⟩
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-! ## The anchor estimate: counting the pulled-back window -/

/-- A zeta zero off the real axis lies strictly inside the critical strip:
right of it zeta does not vanish, and left of it the completed functional
equation reflects to the nonvanishing region. -/
theorem riemannZeta_zero_re_mem_Ioo_of_im_ne_zero' {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (him : ρ.im ≠ 0) : ρ.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hρ0 : ρ ≠ 0 := fun h => him (by rw [h]; simp)
  constructor
  · by_contra h
    push Not at h
    have hΓℝ : Complex.Gammaℝ ρ ≠ 0 := by
      rw [Complex.Gammaℝ_def]
      refine mul_ne_zero ?_ (Complex.Gamma_ne_zero fun m hc => him (by
        have h2 : ρ = -(2 * m : ℂ) := by linear_combination (2 : ℂ) * hc
        have h3 := congrArg Complex.im h2
        simpa using h3))
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
      exact Complex.exp_ne_zero _
    have hcompleted : completedRiemannZeta ρ = 0 := by
      have hdef := riemannZeta_def_of_ne_zero hρ0
      rw [hζ] at hdef
      rcases div_eq_zero_iff.mp hdef.symm with h2 | h2
      · exact h2
      · exact absurd h2 hΓℝ
    have hFE : completedRiemannZeta (1 - ρ) = 0 := by
      rw [completedRiemannZeta_one_sub]
      exact hcompleted
    have h1ρ : (1 : ℂ) - ρ ≠ 0 := fun hc => him (by
      have h3 := congrArg Complex.im hc
      simpa using h3)
    have hζ1 : riemannZeta (1 - ρ) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1ρ, hFE, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re
      (by rw [Complex.sub_re, Complex.one_re]; linarith) hζ1
  · by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hζ

/-- The pulled-back window has at most the multiplicity-weighted nearby count
many index points. -/
theorem u6aXiNearbyIndexFinset_card_le_count {t : ℝ} (ht : 3 ≤ |t|) :
    ((u6aXiNearbyIndexFinset t).card : ℝ) ≤ u6aNearbyZeroCount (-1) 2 t := by
  letI : DecidableEq (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
    Classical.decEq _
  have hcount := riemannZeta.zeroes_sum_eq_finset_of_finite (I := Set.uIcc (-1 : ℝ) 2)
    (J := Set.Icc (t - 1) (t + 1)) (fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite t)
  unfold u6aNearbyZeroCount
  rw [hcount]
  simp only [one_mul]
  unfold u6aXiNearbyIndexFinset
  refine le_trans (Nat.cast_le.mpr (Finset.card_biUnion_le)) ?_
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hρmem : ρ ∈ u6aFTNearbyWindow t := (Set.Finite.mem_toFinset _).mp hρ
  obtain ⟨hre, him, hζρ⟩ := hρmem
  have hζ0 : riemannZeta ρ = 0 := hζρ
  have himne : ρ.im ≠ 0 := by
    intro h0
    rw [h0] at him
    have habs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [him.2], by linarith [him.1]⟩
    linarith
  have hIoo := riemannZeta_zero_re_mem_Ioo_of_im_ne_zero' hζ0 himne
  have hρ0 : ρ ≠ 0 := fun h => himne (by rw [h]; simp)
  rw [Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor
    (f := riemannXi) hρ0,
    u6aRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip hIoo.1 hIoo.2]
  have hord : 0 < riemannZeta.order ρ := riemannZeta_order_pos_of_zero_ne_one
    (fun h => by
      rw [h] at hζ0
      exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hζ0) hζ0
  have hcast : ((Int.toNat (riemannZeta.order ρ) : ℕ) : ℝ) =
      ((riemannZeta.order ρ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hord.le]
  rw [hcast]

end

end Kadiri
