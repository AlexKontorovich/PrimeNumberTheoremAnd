import PrimeNumberTheoremAnd.IEANTN.KadiriU6aFarTailClose
import PrimeNumberTheoremAnd.IEANTN.KadiriU6aAvgComparison
import PrimeNumberTheoremAnd.IEANTN.KadiriFunctionalEquation
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# U6a endpoint closure: the unconditional horizontal bounds

`KadiriU6aFarTailClose` discharges the zero-sum remainder hypothesis on the
strip `[-1, 2]` unconditionally, and `KadiriU6aAvgComparison` turns any such
discharge into cofinal horizontal-segment `log² T` bounds via the count-atom
height selector.  This file instantiates the second at the first, exporting
the unsuffixed `(-1, 2)` endpoint with no hypothesis arguments remaining,
and then widens the strip to arbitrary edges `σ₁ σ₂` by a three-region clip
at the same selected heights:

* middle `x ∈ [-1, 2]`: the `(-1, 2)` bound itself;
* right `x > 2`: the Dirichlet-series bound
  `dlog_riemannZeta_bdd_on_vertical_lines_generalized`, a constant uniform in
  both `x` and the height;
* left `x < -1`: the completed functional-equation transport
  `neg_logDeriv_zeta_left_eq_reflected`, whose reflected zeta term lands in
  the right region and whose digamma terms are log-grade on vertical strips
  (the strip bound is extended below to arbitrary left edges via the
  recurrence `Complex.digamma_apply_add_one`).

Zero-freeness of the wider segments follows from the `(-1, 2)` zero-freeness
alone, since off the real axis every zeta zero has real part in `(0, 1)`
(`riemannZeta_zero_re_mem_Ioo_of_im_ne_zero'`).
-/

namespace Kadiri

open Complex

/-- Cofinal heights `T` at which `ζ'/ζ` is `O(log² T)` along the horizontal
segments `re ∈ [-1, 2]`, `|im| = T`, with both segments zero- and pole-free.
Unconditional. -/
theorem exists_arbitrarily_large_horizontalSegmentLogDerivBound_neg_one_two :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨Czero, Tzero, hZero⟩ := exists_U6aZeroSumRemainderBoundHypothesis
  exact exists_arbitrarily_large_horizontalSegmentLogDerivBound_of_zeroSumRemainder hZero

/-! ## Real-imaginary helpers -/

private lemma u6aEC_mk_re (a b : ℝ) : ((a : ℂ) + (b : ℂ) * I).re = a := by simp

private lemma u6aEC_mk_im (a b : ℝ) : ((a : ℂ) + (b : ℂ) * I).im = b := by simp

/-! ## The digamma strip bound for arbitrary left edges -/

/-- The digamma recurrence iterated: away from the real axis the shift by a
natural number costs a finite sum of reciprocals. -/
private lemma u6aEC_digamma_add_nat (z : ℂ) (him : z.im ≠ 0) (n : ℕ) :
    digamma (z + n) = digamma z + ∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : ∀ m : ℕ, z + (n : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have h2 := congrArg Complex.im hm
      simp only [Complex.add_im, Complex.natCast_im, Complex.neg_im, add_zero,
        neg_zero] at h2
      exact him h2
    have hstep := Complex.digamma_apply_add_one (z + n) hne
    have hcast : z + ((n + 1 : ℕ) : ℂ) = z + n + 1 := by push_cast; ring
    rw [hcast, hstep, ih, Finset.sum_range_succ, add_assoc]

/-- The digamma strip bound extended to strips with arbitrary (possibly
nonpositive) left edge, away from the real axis: shifting right by a natural
number costs only a bounded sum of reciprocals, each at most `1` when
`1 ≤ |im|`. -/
private lemma u6aEC_exists_norm_digamma_le_log (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖digamma z‖ ≤ C * Real.log (|z.im| + 2) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 ≤ a + n :=
    ⟨⌈1 - a⌉₊, by linarith [Nat.le_ceil (1 - a)]⟩
  obtain ⟨C₀, hC₀, h₀⟩ :=
    Complex.exists_norm_digamma_le_log (a := 1) (b := b + n) one_pos
  refine ⟨C₀ + n, by positivity, fun z hza hzb him => ?_⟩
  have hzim : z.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at him
    linarith
  have hdig : digamma z = digamma (z + n) - ∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹ := by
    rw [u6aEC_digamma_add_nat z hzim n]; ring
  have hshift_bound : ‖digamma (z + n)‖ ≤ C₀ * Real.log (|z.im| + 2) := by
    have h1 : (1 : ℝ) ≤ (z + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    have h2 : (z + (n : ℂ)).re ≤ b + n := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    have h := h₀ (z + n) h1 h2
    have him_eq : (z + (n : ℂ)).im = z.im := by
      simp only [Complex.add_im, Complex.natCast_im, add_zero]
    rwa [him_eq] at h
  have hsum : ‖∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖ ≤ (n : ℝ) := by
    have hterm : ∀ k ∈ Finset.range n, ‖(z + (k : ℂ))⁻¹‖ ≤ 1 := by
      intro k _
      have hge : (1 : ℝ) ≤ ‖z + (k : ℂ)‖ := by
        have h2 := Complex.abs_im_le_norm (z + (k : ℂ))
        have h3 : (z + (k : ℂ)).im = z.im := by
          simp only [Complex.add_im, Complex.natCast_im, add_zero]
        rw [h3] at h2
        linarith
      rw [norm_inv, ← one_div]
      have h4 := one_div_le_one_div_of_le one_pos hge
      simpa using h4
    calc ‖∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖
        ≤ ∑ k ∈ Finset.range n, ‖(z + (k : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (n : ℝ) := by simp
  have hlog1 : (1 : ℝ) ≤ Real.log (|z.im| + 2) := by
    have h := (Real.lt_log_iff_exp_lt
        (by linarith [abs_nonneg z.im] : (0 : ℝ) < |z.im| + 2)).mpr
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 < |z.im| + 2)
    linarith
  have hnlog : (n : ℝ) ≤ (n : ℝ) * Real.log (|z.im| + 2) :=
    le_mul_of_one_le_right (Nat.cast_nonneg n) hlog1
  calc ‖digamma z‖
      = ‖digamma (z + n) - ∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖ := by rw [hdig]
    _ ≤ ‖digamma (z + n)‖ + ‖∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖ :=
        norm_sub_le _ _
    _ ≤ C₀ * Real.log (|z.im| + 2) + (n : ℝ) * Real.log (|z.im| + 2) := by
        linarith
    _ = (C₀ + n) * Real.log (|z.im| + 2) := by ring

/-! ## The right region: a height-uniform constant for `re ≥ 2` -/

/-- On the closed half-plane `re ≥ 2` the zeta log-derivative is bounded by
the Dirichlet-series constant at `σ₀ = 2`, uniformly in both coordinates. -/
private lemma u6aEC_right_region_bound (x t : ℝ) (hx : 2 ≤ x) :
    ‖deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) /
        riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ ≤
      ‖deriv riemannZeta ((2 : ℝ) : ℂ) / riemannZeta ((2 : ℝ) : ℂ)‖ := by
  have h := dlog_riemannZeta_bdd_on_vertical_lines_generalized 2 x t (by norm_num) hx
  rwa [neg_div, norm_neg] at h

/-! ## Zero-freeness widens to arbitrary strips -/

/-- Horizontal zero-freeness widens from the strip `[-1, 2]` to any strip:
off the real axis every zeta zero has real part in `(0, 1)`, and the pole
point `1` is real. -/
theorem horizontalSegmentZeroFree_widen {σ₁ σ₂ T : ℝ} (hT : 3 ≤ T)
    (h : horizontalSegmentZeroFree (-1) 2 T) :
    horizontalSegmentZeroFree σ₁ σ₂ T := by
  have key : ∀ z : ℂ, z.im = T ∨ z.im = -T → riemannZeta z ≠ 0 ∧ z ≠ 1 := by
    intro z him
    have hzim : z.im ≠ 0 := by
      intro h0
      rcases him with h' | h' <;> rw [h0] at h' <;> linarith
    refine ⟨fun hzero => ?_, fun h1 => ?_⟩
    · have hre := riemannZeta_zero_re_mem_Ioo_of_im_ne_zero' hzero hzim
      have hmem : z.re ∈ Set.uIcc (-1 : ℝ) 2 :=
        Set.mem_uIcc_of_le (by linarith [hre.1]) (by linarith [hre.2])
      rcases him with h' | h'
      · exact (h.1 z hmem h').1 hzero
      · exact (h.2 z hmem h').1 hzero
    · rw [h1] at hzim
      exact hzim Complex.one_im
  exact ⟨fun z _ him => key z (Or.inl him), fun z _ him => key z (Or.inr him)⟩

/-! ## The left region: functional-equation transport -/

/-- Triangle inequality for the six-term functional-equation expression. -/
private lemma u6aEC_norm_add6_le (u v w d e f : ℂ) :
    ‖u + v + w - d + e + f‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  calc ‖u + v + w - d + e + f‖
      ≤ ‖u + v + w - d + e‖ + ‖f‖ := norm_add_le _ _
    _ ≤ ‖u + v + w - d‖ + ‖e‖ + ‖f‖ := by linarith [norm_add_le (u + v + w - d) e]
    _ ≤ ‖u + v + w‖ + ‖d‖ + ‖e‖ + ‖f‖ := by linarith [norm_sub_le (u + v + w) d]
    _ ≤ ‖u + v‖ + ‖w‖ + ‖d‖ + ‖e‖ + ‖f‖ := by linarith [norm_add_le (u + v) w]
    _ ≤ ‖u‖ + ‖v‖ + ‖w‖ + ‖d‖ + ‖e‖ + ‖f‖ := by linarith [norm_add_le u v]

/-- Left-region transport: for `x ∈ [σm, -1]` at heights `|t| ≥ 3` the zeta
log-derivative is log-grade, by the completed functional equation reflected
into the `re ≥ 2` Dirichlet region.  The constant depends only on `σm`. -/
private lemma u6aEC_left_region_bound (σm : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x t : ℝ, σm ≤ x → x ≤ -1 → 3 ≤ |t| →
      ‖deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) /
          riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ ≤ K * Real.log (|t| + 2) := by
  obtain ⟨CL, hCL, hdigL⟩ := u6aEC_exists_norm_digamma_le_log (σm / 2 + 1) (1 / 2)
  obtain ⟨CR, hCR, hdigR⟩ :=
    Complex.exists_norm_digamma_le_log (a := 1) (b := (1 - σm) / 2 + 1) one_pos
  have hπ0 : (0 : ℝ) ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  set Cz : ℝ := ‖deriv riemannZeta ((2 : ℝ) : ℂ) / riemannZeta ((2 : ℝ) : ℂ)‖
    with hCz_def
  have hCz0 : (0 : ℝ) ≤ Cz := norm_nonneg _
  refine ⟨Cz + 1 + Real.log Real.pi + CL + CR, by linarith, fun x t hxm hx1 ht => ?_⟩
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    linarith
  set z : ℂ := (x : ℂ) + (t : ℂ) * I with hz_def
  have hz_re : z.re = x := by rw [hz_def]; exact u6aEC_mk_re x t
  have hz_im : z.im = t := by rw [hz_def]; exact u6aEC_mk_im x t
  have hzim_ne : z.im ≠ 0 := by rw [hz_im]; exact ht0
  have hz0 : z ≠ 0 := by
    intro h
    apply hzim_ne
    rw [h, Complex.zero_im]
  have hz1 : z ≠ 1 := by
    intro h
    apply hzim_ne
    rw [h, Complex.one_im]
  have hζz : riemannZeta z ≠ 0 := by
    intro hzero
    have hre := riemannZeta_zero_re_mem_Ioo_of_im_ne_zero' hzero hzim_ne
    rw [hz_re] at hre
    linarith [hre.1]
  have hζref : riemannZeta (1 - z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re
      (by rw [Complex.sub_re, Complex.one_re, hz_re]; linarith)
  have hΓz_diff : ∀ m : ℕ, z / 2 + 1 ≠ -(m : ℂ) := by
    intro m hm
    have h2 : z = -(2 * (m : ℂ)) - 2 := by linear_combination (2 : ℂ) * hm
    have h3 := congrArg Complex.im h2
    rw [hz_im] at h3
    simp at h3
    exact ht0 h3
  have hΓref_diff : ∀ m : ℕ, (1 - z) / 2 + 1 ≠ -(m : ℂ) := by
    intro m hm
    have h2 : z = 3 + 2 * (m : ℂ) := by linear_combination (-2 : ℂ) * hm
    have h3 := congrArg Complex.im h2
    rw [hz_im] at h3
    simp at h3
    exact ht0 h3
  have hΓz : zetaGammaFactor z ≠ 0 := by
    unfold zetaGammaFactor
    exact Complex.Gamma_ne_zero hΓz_diff
  have hΓref : zetaGammaFactor (1 - z) ≠ 0 := by
    unfold zetaGammaFactor
    exact Complex.Gamma_ne_zero hΓref_diff
  have hFE := neg_logDeriv_zeta_left_eq_reflected hz0 hz1 hζz hζref
    hΓz_diff hΓref_diff hΓz hΓref
  -- the six pieces
  have hA : ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)‖ ≤ Cz := by
    have h := u6aEC_right_region_bound (1 - x) (-t) (by linarith)
    rw [show ((1 - x : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - z by
      rw [hz_def]; push_cast; ring] at h
    rw [hCz_def]
    exact h
  have hB : ‖(1 : ℂ) / (z - 1)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_one]
    have him_eq : (z - 1).im = t := by
      rw [Complex.sub_im, Complex.one_im, hz_im]; ring
    have hge : (3 : ℝ) ≤ ‖z - 1‖ := by
      have h2 := Complex.abs_im_le_norm (z - 1)
      rw [him_eq] at h2
      linarith
    exact one_div_le_one_div_of_le (by norm_num) hge
  have hC : ‖(1 : ℂ) / ((1 - z) - 1)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_one]
    have him_eq : ((1 - z) - 1).im = -t := by
      rw [Complex.sub_im, Complex.sub_im, Complex.one_im, hz_im]
      ring
    have hge : (3 : ℝ) ≤ ‖(1 - z) - 1‖ := by
      have h2 := Complex.abs_im_le_norm ((1 - z) - 1)
      rw [him_eq, abs_neg] at h2
      linarith
    exact one_div_le_one_div_of_le (by norm_num) hge
  have hD : ‖((Real.log Real.pi : ℝ) : ℂ)‖ = Real.log Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hπ0]
  have hlog0 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have habs2 : |t / 2| = |t| / 2 := by
    rw [abs_div]
    norm_num
  have hloghalf : Real.log (|t| / 2 + 2) ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by linarith) (by linarith [abs_nonneg t])
  have hE : ‖digamma (z / 2 + 1)‖ ≤ CL * Real.log (|t| + 2) := by
    have hz2 : z / 2 + 1 = ((x / 2 + 1 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      rw [hz_def]; push_cast; ring
    rw [hz2]
    have h := hdigL (((x / 2 + 1 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)
      (by rw [u6aEC_mk_re]; linarith) (by rw [u6aEC_mk_re]; linarith)
      (by rw [u6aEC_mk_im, habs2]; linarith)
    rw [u6aEC_mk_im, habs2] at h
    exact h.trans (mul_le_mul_of_nonneg_left hloghalf hCL.le)
  have hF : ‖digamma ((1 - z) / 2 + 1)‖ ≤ CR * Real.log (|t| + 2) := by
    have hzF : (1 - z) / 2 + 1 =
        (((1 - x) / 2 + 1 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * I := by
      rw [hz_def]; push_cast; ring
    rw [hzF]
    have h := hdigR ((((1 - x) / 2 + 1 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * I)
      (by rw [u6aEC_mk_re]; linarith) (by rw [u6aEC_mk_re]; linarith)
    rw [u6aEC_mk_im, abs_neg, habs2] at h
    exact h.trans (mul_le_mul_of_nonneg_left hloghalf hCR.le)
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  have hEhalf : ‖(1 / 2 : ℂ) * digamma (z / 2 + 1)‖ ≤ CL * Real.log (|t| + 2) := by
    rw [norm_mul, hhalf]
    have hnn : (0 : ℝ) ≤ CL * Real.log (|t| + 2) := mul_nonneg hCL.le hlog0
    linarith [hE, norm_nonneg (digamma (z / 2 + 1))]
  have hFhalf : ‖(1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)‖ ≤
      CR * Real.log (|t| + 2) := by
    rw [norm_mul, hhalf]
    have hnn : (0 : ℝ) ≤ CR * Real.log (|t| + 2) := mul_nonneg hCR.le hlog0
    linarith [hF, norm_nonneg (digamma ((1 - z) / 2 + 1))]
  have hlog1 : (1 : ℝ) ≤ Real.log (|t| + 2) := by
    have h := (Real.lt_log_iff_exp_lt (by linarith : (0 : ℝ) < |t| + 2)).mpr
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 < |t| + 2)
    linarith
  calc ‖deriv riemannZeta z / riemannZeta z‖
      = ‖-deriv riemannZeta z / riemannZeta z‖ := by rw [neg_div, norm_neg]
    _ = ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)
          + 1 / (z - 1) + 1 / ((1 - z) - 1)
          - (Real.log Real.pi : ℂ)
          + (1 / 2 : ℂ) * digamma (z / 2 + 1)
          + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)‖ := by rw [hFE]
    _ ≤ ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)‖ + ‖(1 : ℂ) / (z - 1)‖
          + ‖(1 : ℂ) / ((1 - z) - 1)‖ + ‖((Real.log Real.pi : ℝ) : ℂ)‖
          + ‖(1 / 2 : ℂ) * digamma (z / 2 + 1)‖
          + ‖(1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)‖ :=
        u6aEC_norm_add6_le _ _ _ _ _ _
    _ ≤ Cz + 1 / 3 + 1 / 3 + Real.log Real.pi
          + CL * Real.log (|t| + 2) + CR * Real.log (|t| + 2) := by
        rw [hD]
        linarith [hA, hB, hC, hEhalf, hFhalf]
    _ ≤ (Cz + 1 + Real.log Real.pi + CL + CR) * Real.log (|t| + 2) := by
        nlinarith [mul_nonneg hCz0 (sub_nonneg.mpr hlog1),
          mul_nonneg hπ0 (sub_nonneg.mpr hlog1)]

/-! ## The endpoint: arbitrary strip edges -/

/-- Sub-unit U6a, closed for arbitrary strip edges: there exist arbitrarily
large heights `T` at which `ζ'/ζ` is `O(log² T)` uniformly on the strip
`σ ∈ uIcc σ₁ σ₂`, with both horizontal segments zero- and pole-free.  This is
the exact shape of the sorried contour-pull target
(`56e3a7d:KadiriContourPull.lean:329-331`): generic edges, constant after the
edges.  Three-region clip at the `(-1, 2)` selected heights. -/
theorem exists_arbitrarily_large_horizontalSegmentLogDerivBound (σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentLogDerivBound σ₁ σ₂ T C := by
  obtain ⟨Cm, hCm, hmid⟩ :=
    exists_arbitrarily_large_horizontalSegmentLogDerivBound_neg_one_two
  obtain ⟨K, hK, hleft⟩ := u6aEC_left_region_bound (min σ₁ σ₂)
  set Cz : ℝ := ‖deriv riemannZeta ((2 : ℝ) : ℂ) / riemannZeta ((2 : ℝ) : ℂ)‖
    with hCz_def
  have hCz0 : (0 : ℝ) ≤ Cz := norm_nonneg _
  refine ⟨Cm + 2 * K + Cz, by linarith, fun T₀ => ?_⟩
  obtain ⟨T, hT₀, hT3, hbound⟩ := hmid T₀
  have hlogT1 : (1 : ℝ) ≤ Real.log T := by
    have h := (Real.lt_log_iff_exp_lt (by linarith : (0 : ℝ) < T)).mpr
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 < T)
    linarith
  have hsq0 : (0 : ℝ) ≤ Real.log T ^ 2 := sq_nonneg _
  have hsq1 : (1 : ℝ) ≤ Real.log T ^ 2 := by nlinarith
  have hloglin : Real.log T ≤ Real.log T ^ 2 := by nlinarith
  refine ⟨T, hT₀, hT3, horizontalSegmentZeroFree_widen hT3 hbound.1, ?_⟩
  intro x hx t ht
  by_cases hx1 : x ≤ -1
  · -- left region
    have hxm : min σ₁ σ₂ ≤ x := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact (min_le_left _ _).trans h1
      · exact (min_le_right _ _).trans h1
    have hb := hleft x t hxm hx1 (by rw [ht]; exact hT3)
    have hlog_sq : Real.log (T ^ 2) = 2 * Real.log T := by
      rw [Real.log_pow]
      norm_num
    have hlog2 : Real.log (T + 2) ≤ 2 * Real.log T := by
      have h1 : T + 2 ≤ T ^ 2 := by nlinarith
      have h2 := Real.log_le_log (by linarith) h1
      rwa [hlog_sq] at h2
    calc ‖deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) /
          riemannZeta ((x : ℂ) + (t : ℂ) * I)‖
        ≤ K * Real.log (|t| + 2) := hb
      _ = K * Real.log (T + 2) := by rw [ht]
      _ ≤ K * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlog2 hK.le
      _ = 2 * K * Real.log T := by ring
      _ ≤ 2 * K * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_left hloglin (by linarith)
      _ ≤ (Cm + 2 * K + Cz) * Real.log T ^ 2 := by
          nlinarith [mul_nonneg hCm.le hsq0, mul_nonneg hCz0 hsq0]
  · by_cases hx2 : x ≤ 2
    · -- middle region
      have hx' : x ∈ Set.uIcc (-1 : ℝ) 2 :=
        Set.mem_uIcc_of_le (by linarith [not_le.mp hx1]) hx2
      have hb := hbound.2 x hx' t ht
      calc ‖deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) /
            riemannZeta ((x : ℂ) + (t : ℂ) * I)‖
          ≤ Cm * Real.log T ^ 2 := hb
        _ ≤ (Cm + 2 * K + Cz) * Real.log T ^ 2 := by
            nlinarith [mul_nonneg hK.le hsq0, mul_nonneg hCz0 hsq0]
    · -- right region
      have hb := u6aEC_right_region_bound x t (le_of_lt (not_le.mp hx2))
      rw [← hCz_def] at hb
      calc ‖deriv riemannZeta ((x : ℂ) + (t : ℂ) * I) /
            riemannZeta ((x : ℂ) + (t : ℂ) * I)‖
          ≤ Cz := hb
        _ ≤ Cz * Real.log T ^ 2 := le_mul_of_one_le_right hCz0 hsq1
        _ ≤ (Cm + 2 * K + Cz) * Real.log T ^ 2 := by
            nlinarith [mul_nonneg hCm.le hsq0, mul_nonneg hK.le hsq0]

end Kadiri
