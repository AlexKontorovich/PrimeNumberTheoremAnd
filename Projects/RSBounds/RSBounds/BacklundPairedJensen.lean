/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0; see licenses/Gersh-LICENSE.
Adapted and extended to radii below 3/2 by OpenAI, 2026.
-/
import RSBounds.BacklundJensen

/-!
# Reflected pairs in Jensen's formula

The circle can have any radius `R > 3/4`, including Rosser's `R = 1.32`.
A reflected partner outside the circle contributes zero, but the corresponding
right zero then contributes at least the whole paired weight. Thus the factor
of two does not require the circle to contain the entire reflected interval.
-/

open Real Complex Metric MeasureTheory MeromorphicOn Set

namespace TernaryGoldbach.RSBounds.BacklundPairedJensen

/-- A genuine zero of an analytic function nonzero at the disk center has
positive divisor multiplicity. -/
theorem divisor_at_zero_ge_one {f : ℂ → ℂ} {c u : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0)
    (hu : u ∈ closedBall c R) (hzero : f u = 0) :
    1 ≤ divisor f (closedBall c R) u := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  have hz := (hf u hu).analyticOrderAt_ne_zero.mpr hzero
  have hc : c ∈ closedBall c R := by simpa using hR
  have hct : analyticOrderAt f c ≠ ⊤ := by
    rw [(hf c hc).analyticOrderAt_eq_zero.mpr hfc]
    exact ENat.natCast_ne_top 0
  have hut := hf.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall _ _).isPreconnected hc hu hct
  cases h : analyticOrderAt f u with
  | top => exact absurd h hut
  | coe n =>
    simp only [ENat.map_natCast, WithTop.untop₀_coe]
    have hn : 0 < n := by
      rw [h] at hz
      have : n ≠ 0 := by rintro rfl; exact hz rfl
      omega
    exact_mod_cast hn

/-- Near-pair geometry, before taking logarithms. -/
theorem reflected_distance_product_le {a b : ℝ}
    (ha : a < 5 / 4) (hb : 1 - a ≤ b) :
    (5 / 4 - a) * (5 / 4 - b) ≤ (3 / 4 : ℝ) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (show 5 / 4 - b ≤ 1 / 4 + a by linarith)
    (show 0 ≤ 5 / 4 - a by linarith)
  nlinarith [sq_nonneg (a - 1 / 2)]

/-- The two logarithmic weights of a reflected pair have the full doubled
weight. This inequality is useful even before deciding disk membership. -/
theorem paired_log_weight {R a b : ℝ} (hR : 0 < R)
    (ha : a < 5 / 4) (hb : b ≤ 1 / 2) (hpair : 1 - a ≤ b) :
    2 * Real.log (R / (3 / 4)) ≤
      Real.log (R / (5 / 4 - a)) + Real.log (R / (5 / 4 - b)) := by
  have hu : 0 < 5 / 4 - a := by linarith
  have hv : 0 < 5 / 4 - b := by linarith
  have hp := reflected_distance_product_le ha hpair
  have hh : (R / (3 / 4)) ^ 2 ≤ (R / (5 / 4 - a)) * (R / (5 / 4 - b)) := by
    rw [div_mul_div_comm, le_div_iff₀ (mul_pos hu hv)]
    nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg R)]
  have hl := Real.log_le_log (show 0 < (R / (3 / 4)) ^ 2 by positivity) hh
  rw [Real.log_pow, Real.log_mul (ne_of_gt (div_pos hR hu))
    (ne_of_gt (div_pos hR hv))] at hl
  simpa using hl

/-- If the partner is outside the circle, the right zero alone has the
full doubled weight. -/
theorem far_log_weight {R a b : ℝ} (hR : 0 < R)
    (ha : a < 5 / 4) (hpair : 1 - a ≤ b) (hout : R < 5 / 4 - b) :
    2 * Real.log (R / (3 / 4)) ≤ Real.log (R / (5 / 4 - a)) := by
  have hu : 0 < 5 / 4 - a := by linarith
  have hp := reflected_distance_product_le ha hpair
  have hRu : R * (5 / 4 - a) ≤ (3 / 4 : ℝ) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left hout hu]
  have hh : (R / (3 / 4)) ^ 2 ≤ R / (5 / 4 - a) := by
    rw [le_div_iff₀ hu]
    nlinarith [mul_le_mul_of_nonneg_left hRu hR.le]
  have hl := Real.log_le_log (show 0 < (R / (3 / 4)) ^ 2 by positivity) hh
  simpa only [Real.log_pow, Nat.cast_ofNat] using hl

/-- Jensen's full factor of two from distinct reflected zero pairs, including
partners outside the circle. No zero-count theorem is assumed. -/
theorem paired_jensen_lower {f : ℂ → ℂ} {R : ℝ} (hR : 3 / 4 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) {n : ℕ} {a b : ℕ → ℝ}
    (ha_zero : ∀ i, i < n → f (a i : ℂ) = 0)
    (ha_lo : ∀ i, i < n → 1 / 2 ≤ a i)
    (ha_hi : ∀ i, i < n → a i < 5 / 4)
    (ha_inj : ∀ i j, i < n → j < n → a i = a j → i = j)
    (hb_zero : ∀ i, i < n → f (b i : ℂ) = 0)
    (hb_pair : ∀ i, i < n → 1 - a i ≤ b i)
    (hb_hi : ∀ i, i < n → b i ≤ 1 / 2)
    (hb_inj : ∀ i j, i < n → j < n → b i = b j → i = j)
    (hdisj : ∀ i j, i < n → j < n → a i ≠ b j) :
    2 * (n : ℝ) * Real.log (R / (3 / 4)) ≤
      circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
        Real.log ‖f (5 / 4 : ℂ)‖ := by
  classical
  have hR0 : 0 < R := by linarith
  let c : ℂ := 5 / 4
  let D := divisor f (closedBall c R)
  let w : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)
  have hDfin : (D.support : Set ℂ).Finite := D.finiteSupport (isCompact_closedBall c R)
  have hwfin : w.support.Finite := hDfin.subset (by
    intro u hu
    simp only [Function.mem_support, w, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hu
    exact hu.1)
  have hw_nonneg : ∀ u, 0 ≤ w u := by
    intro u
    by_cases hDu : D u = 0
    · simp [w, hDu]
    have hu : u ∈ closedBall c R := D.supportWithinDomain (by
      simpa only [Function.mem_support] using hDu)
    have huc : c ≠ u := by
      intro he
      apply hDu
      subst u
      change divisor f (closedBall c R) c = 0
      rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu,
        (hf c hu).meromorphicOrderAt_eq, (hf c hu).analyticOrderAt_eq_zero.mpr hfc]
      rfl
    have hd : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc)
    apply mul_nonneg (by exact_mod_cast (hf.divisor_nonneg u))
    apply Real.log_nonneg
    rw [← div_eq_mul_inv, one_le_div hd]
    simpa only [mem_closedBall, dist_eq_norm'] using hu
  have hj : (∑ᶠ u, w u) = circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
    have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR0] using hf
    have h := hfa.circleAverage_log_norm hR0.ne' hfc
    rw [abs_of_pos hR0] at h
    simpa only [w, D] using (eq_sub_iff_add_eq.mpr h.symm)
  have hnrm (x : ℝ) (hx : x < 5 / 4) : ‖c - (x : ℂ)‖ = 5 / 4 - x := by
    have he : c - (x : ℂ) = ((5 / 4 - x : ℝ) : ℂ) := by dsimp [c]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hw_real (x : ℝ) (hx : x < 5 / 4) (hd : 5 / 4 - x ≤ R) (hz : f (x : ℂ) = 0) :
      Real.log (R / (5 / 4 - x)) ≤ w (x : ℂ) := by
    have hu : (x : ℂ) ∈ closedBall c R := by
      simpa only [mem_closedBall, dist_eq_norm', hnrm x hx] using hd
    have hD1 : (1 : ℝ) ≤ (D (x : ℂ) : ℝ) := by
      exact_mod_cast divisor_at_zero_ge_one hR0.le hf hfc hu hz
    have hl : 0 ≤ Real.log (R / (5 / 4 - x)) :=
      Real.log_nonneg ((one_le_div (by linarith)).mpr hd)
    dsimp [w]
    rw [hnrm x hx, ← div_eq_mul_inv]
    exact le_mul_of_one_le_left hl hD1
  have hp (i : ℕ) (hi : i < n) :
      2 * Real.log (R / (3 / 4)) ≤ w (a i : ℂ) + w (b i : ℂ) := by
    have ha := hw_real (a i) (ha_hi i hi) (by linarith [ha_lo i hi]) (ha_zero i hi)
    by_cases hb : 5 / 4 - b i ≤ R
    · have hbw := hw_real (b i) (by linarith [hb_hi i hi]) hb (hb_zero i hi)
      linarith [paired_log_weight hR0 (ha_hi i hi) (hb_hi i hi) (hb_pair i hi)]
    · have hw := hw_nonneg (b i : ℂ)
      linarith [far_log_weight hR0 (ha_hi i hi) (hb_pair i hi) (lt_of_not_ge hb)]
  let Za : Finset ℂ := (Finset.range n).image (fun i => (a i : ℂ))
  let Zb : Finset ℂ := (Finset.range n).image (fun i => (b i : ℂ))
  have hai : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, (a i : ℂ) = (a j : ℂ) → i = j := by
    intro i hi j hj he
    exact ha_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by exact_mod_cast he)
  have hbi : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, (b i : ℂ) = (b j : ℂ) → i = j := by
    intro i hi j hj he
    exact hb_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by exact_mod_cast he)
  have hdj : Disjoint Za Zb := by
    rw [Finset.disjoint_left]
    intro z hza hzb
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hza
    obtain ⟨j, hj, he'⟩ := Finset.mem_image.mp hzb
    exact hdisj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (by exact_mod_cast (he.trans he'.symm))
  have hsum : 2 * (n : ℝ) * Real.log (R / (3 / 4)) ≤ ∑ z ∈ Za ∪ Zb, w z := by
    rw [Finset.sum_union hdj, Finset.sum_image hai, Finset.sum_image hbi,
      ← Finset.sum_add_distrib]
    have hh : (∑ _i ∈ Finset.range n, 2 * Real.log (R / (3 / 4))) ≤
        ∑ i ∈ Finset.range n, (w (a i : ℂ) + w (b i : ℂ)) :=
      Finset.sum_le_sum (fun i hi => hp i (Finset.mem_range.mp hi))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc,
      mul_left_comm] using hh
  let F := hwfin.toFinset
  have hsum_le : ∑ z ∈ Za ∪ Zb, w z ≤ ∑ z ∈ F, w z := by
    calc
      _ ≤ ∑ z ∈ (Za ∪ Zb) ∪ F, w z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hw_nonneg z)
      _ = ∑ z ∈ F, w z := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z _ hz
        have hz' : z ∉ w.support := by simpa only [F, Set.Finite.mem_toFinset] using hz
        simpa only [Function.mem_support, not_not] using hz'
  have hfinsum : (∑ᶠ u, w u) = ∑ z ∈ F, w z :=
    finsum_eq_sum_of_support_subset_of_finite w (le_refl _) hwfin
  exact hsum.trans (hsum_le.trans_eq (hfinsum.symm.trans hj))

/-- Retain the unmatched right zeros as well. Each costs one Jensen weight,
whereas a paired right zero costs two. This halves the reflection-error loss. -/
theorem paired_jensen_with_unpaired_lower {f : ℂ → ℂ} {R : ℝ} (hR : 3 / 4 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) {k n : ℕ} {a b : ℕ → ℝ}
    (ha_zero : ∀ i, i < k + n → f (a i : ℂ) = 0)
    (ha_lo : ∀ i, i < k + n → 1 / 2 ≤ a i)
    (ha_hi : ∀ i, i < k + n → a i < 5 / 4)
    (ha_inj : ∀ i j, i < k + n → j < k + n → a i = a j → i = j)
    (hb_zero : ∀ i, i < n → f (b i : ℂ) = 0)
    (hb_pair : ∀ i, i < n → 1 - a (i + k) ≤ b i)
    (hb_hi : ∀ i, i < n → b i ≤ 1 / 2)
    (hb_inj : ∀ i j, i < n → j < n → b i = b j → i = j)
    (hdisj : ∀ i j, i < k + n → j < n → a i ≠ b j) :
    (2 * (n : ℝ) + k) * Real.log (R / (3 / 4)) ≤
      circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
        Real.log ‖f (5 / 4 : ℂ)‖ := by
  classical
  have hR0 : 0 < R := by linarith
  let c : ℂ := 5 / 4
  let D := divisor f (closedBall c R)
  let w : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)
  have hDfin : (D.support : Set ℂ).Finite := D.finiteSupport (isCompact_closedBall c R)
  have hwfin : w.support.Finite := hDfin.subset (by
    intro u hu
    simp only [Function.mem_support, w, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hu
    exact hu.1)
  have hw_nonneg : ∀ u, 0 ≤ w u := by
    intro u
    by_cases hDu : D u = 0
    · simp [w, hDu]
    have hu : u ∈ closedBall c R := D.supportWithinDomain (by
      simpa only [Function.mem_support] using hDu)
    have huc : c ≠ u := by
      intro he
      apply hDu
      subst u
      change divisor f (closedBall c R) c = 0
      rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu,
        (hf c hu).meromorphicOrderAt_eq, (hf c hu).analyticOrderAt_eq_zero.mpr hfc]
      rfl
    have hd : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc)
    apply mul_nonneg (by exact_mod_cast (hf.divisor_nonneg u))
    apply Real.log_nonneg
    rw [← div_eq_mul_inv, one_le_div hd]
    simpa only [mem_closedBall, dist_eq_norm'] using hu
  have hj : (∑ᶠ u, w u) = circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
    have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR0] using hf
    have h := hfa.circleAverage_log_norm hR0.ne' hfc
    rw [abs_of_pos hR0] at h
    simpa only [w, D] using (eq_sub_iff_add_eq.mpr h.symm)
  have hnrm (x : ℝ) (hx : x < 5 / 4) : ‖c - (x : ℂ)‖ = 5 / 4 - x := by
    have he : c - (x : ℂ) = ((5 / 4 - x : ℝ) : ℂ) := by dsimp [c]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hw_real (x : ℝ) (hx : x < 5 / 4) (hd : 5 / 4 - x ≤ R) (hz : f (x : ℂ) = 0) :
      Real.log (R / (5 / 4 - x)) ≤ w (x : ℂ) := by
    have hu : (x : ℂ) ∈ closedBall c R := by
      simpa only [mem_closedBall, dist_eq_norm', hnrm x hx] using hd
    have hD1 : (1 : ℝ) ≤ (D (x : ℂ) : ℝ) := by
      exact_mod_cast divisor_at_zero_ge_one hR0.le hf hfc hu hz
    have hl : 0 ≤ Real.log (R / (5 / 4 - x)) :=
      Real.log_nonneg ((one_le_div (by linarith)).mpr hd)
    dsimp [w]
    rw [hnrm x hx, ← div_eq_mul_inv]
    exact le_mul_of_one_le_left hl hD1
  have hp (i : ℕ) (hi : i < n) :
      2 * Real.log (R / (3 / 4)) ≤ w (a (i + k) : ℂ) + w (b i : ℂ) := by
    have hik : i + k < k + n := by omega
    have ha := hw_real (a (i + k)) (ha_hi (i + k) hik)
      (by linarith [ha_lo (i + k) hik]) (ha_zero (i + k) hik)
    by_cases hb : 5 / 4 - b i ≤ R
    · have hbw := hw_real (b i) (by linarith [hb_hi i hi]) hb (hb_zero i hi)
      linarith [paired_log_weight hR0 (ha_hi (i + k) (by omega)) (hb_hi i hi) (hb_pair i hi)]
    · have hw := hw_nonneg (b i : ℂ)
      linarith [far_log_weight hR0 (ha_hi (i + k) (by omega)) (hb_pair i hi) (lt_of_not_ge hb)]
  let Za : Finset ℂ := (Finset.range (k + n)).image (fun i => (a i : ℂ))
  let Zb : Finset ℂ := (Finset.range n).image (fun i => (b i : ℂ))
  have hai : ∀ i ∈ Finset.range (k + n), ∀ j ∈ Finset.range (k + n), (a i : ℂ) = (a j : ℂ) → i = j := by
    intro i hi j hj he
    exact ha_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by exact_mod_cast he)
  have hbi : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, (b i : ℂ) = (b j : ℂ) → i = j := by
    intro i hi j hj he
    exact hb_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by exact_mod_cast he)
  have hdj : Disjoint Za Zb := by
    rw [Finset.disjoint_left]
    intro z hza hzb
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hza
    obtain ⟨j, hj, he'⟩ := Finset.mem_image.mp hzb
    exact hdisj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (by exact_mod_cast (he.trans he'.symm))
  have hsingle (i : ℕ) (hi : i < k) : Real.log (R / (3 / 4)) ≤ w (a i : ℂ) := by
    have hii : i < k + n := by omega
    have ha := hw_real (a i) (ha_hi i hii) (by linarith [ha_lo i hii]) (ha_zero i hii)
    have hd : 0 < 5 / 4 - a i := by linarith [ha_hi i hii]
    have hh : R / (3 / 4) ≤ R / (5 / 4 - a i) :=
      div_le_div_of_nonneg_left hR0.le hd (by linarith [ha_lo i hii])
    exact (Real.log_le_log (by positivity) hh).trans ha
  have hsingle_sum : (k : ℝ) * Real.log (R / (3 / 4)) ≤ ∑ i ∈ Finset.range k, w (a i : ℂ) := by
    have hh := Finset.sum_le_sum (fun i hi => hsingle i (Finset.mem_range.mp hi))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
  have hpair_sum : 2 * (n : ℝ) * Real.log (R / (3 / 4)) ≤
      ∑ i ∈ Finset.range n, (w (a (i + k) : ℂ) + w (b i : ℂ)) := by
    have hh := Finset.sum_le_sum (fun i hi => hp i (Finset.mem_range.mp hi))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc,
      mul_left_comm] using hh
  have hsum : (2 * (n : ℝ) + k) * Real.log (R / (3 / 4)) ≤ ∑ z ∈ Za ∪ Zb, w z := by
    rw [Finset.sum_union hdj, Finset.sum_image hai, Finset.sum_image hbi,
      Finset.sum_range_add, add_assoc, ← Finset.sum_add_distrib]
    simp only [Nat.add_comm k] at *
    nlinarith [hsingle_sum, hpair_sum]
  let F := hwfin.toFinset
  have hsum_le : ∑ z ∈ Za ∪ Zb, w z ≤ ∑ z ∈ F, w z := by
    calc
      _ ≤ ∑ z ∈ (Za ∪ Zb) ∪ F, w z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hw_nonneg z)
      _ = ∑ z ∈ F, w z := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z _ hz
        have hz' : z ∉ w.support := by simpa only [F, Set.Finite.mem_toFinset] using hz
        simpa only [Function.mem_support, not_not] using hz'
  have hfinsum : (∑ᶠ u, w u) = ∑ z ∈ F, w z :=
    finsum_eq_sum_of_support_subset_of_finite w (le_refl _) hwfin
  exact hsum.trans (hsum_le.trans_eq (hfinsum.symm.trans hj))

end TernaryGoldbach.RSBounds.BacklundPairedJensen
