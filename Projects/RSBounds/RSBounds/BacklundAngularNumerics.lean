import RSBounds.BacklundAngularCoefficients

/-! Kernel-checked scalar bounds for Backlund's angular coefficients. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Real Finset
open TernaryGoldbach.RSBounds.BacklundRightArc
namespace TernaryGoldbach.RSBounds.BacklundAngularCoefficients

private lemma cos_gamma_lo : (25 / 132 : ℝ) ≤ Real.cos (6901 / 5000 : ℝ) := by
  have hs : (9999990916480827 : ℝ) / 10000000000000000 ≤ Real.cos ((6901 / 5000 : ℝ) / 1024) :=
    cos_initial_lower (by norm_num) le_rfl (by norm_num)
  have he := cosDoubleCheck_sound (by norm_num : 0 < 10000000000000000) hs
    (by decide +kernel : cosDoubleCheck 10000000000000000 9999990916480827 [9999963665939810, 9999854664023272, 9999418660317597, 9997674708861553, 9990699916841987, 9962816965677297, 9851544378317476, 9410585327591732, 7711823241576957, 1894443541865304] = true)
  norm_num [cosEnd] at he
  linarith

private lemma cos_gamma_hi : Real.cos (13803 / 10000 : ℝ) ≤ (25 / 132 : ℝ) := by
  have hs : (9999985207781639 : ℝ) / 10000000000000000 ≤ Real.cos ((Real.pi - (13803 / 10000 : ℝ)) / 1024) := by
    apply cos_initial_lower (show 0 ≤ (Real.pi - (13803 / 10000 : ℝ)) / 1024 by linarith [Real.pi_gt_three])
      (show (Real.pi - (13803 / 10000 : ℝ)) / 1024 ≤ (3.141593 - (13803 / 10000 : ℝ)) / 1024 by linarith [Real.pi_lt_d6])
    norm_num
  have he := cosDoubleCheck_sound (by norm_num : 0 < 10000000000000000) hs
    (by decide +kernel : cosDoubleCheck 10000000000000000 9999985207781639 [9999940831170317, 9999763325381458, 9999053312728807, 9996213430158585, 9984856588256572, 9939472217610134, 9758621592928742, 9046139078795019, 6366526446580478, -1893468200998271] = true)
  norm_num only [cosEnd, List.length_cons, List.length_nil, Nat.reduceAdd] at he
  rw [show (1024 : ℝ) * ((Real.pi - (13803 / 10000 : ℝ)) / 1024) = Real.pi - (13803 / 10000 : ℝ) by ring,
    Real.cos_pi_sub] at he
  norm_num at he
  linarith

private lemma cos_delta_lo : (125 / 132 : ℝ) ≤ Real.cos (3271 / 10000 : ℝ) := by
  have hs : (9999999489810895 : ℝ) / 10000000000000000 ≤ Real.cos ((3271 / 10000 : ℝ) / 1024) :=
    cos_initial_lower (by norm_num) le_rfl (by norm_num)
  have he := cosDoubleCheck_sound (by norm_num : 0 < 10000000000000000) hs
    (by decide +kernel : cosDoubleCheck 10000000000000000 9999999489810895 [9999997959243632, 9999991836975360, 9999967347914766, 9999869391872295, 9999477570900876, 9997910338189936, 9991642226097040, 9966582874865082, 9866554840310784, 9469780883372032] = true)
  norm_num [cosEnd] at he
  linarith

private lemma cos_delta_hi : Real.cos (409 / 1250 : ℝ) ≤ (125 / 132 : ℝ) := by
  have hs : (9999962230644424 : ℝ) / 10000000000000000 ≤ Real.cos ((Real.pi - (409 / 1250 : ℝ)) / 1024) := by
    apply cos_initial_lower (show 0 ≤ (Real.pi - (409 / 1250 : ℝ)) / 1024 by linarith [Real.pi_gt_three])
      (show (Real.pi - (409 / 1250 : ℝ)) / 1024 ≤ (3.141593 - (409 / 1250 : ℝ)) / 1024 by linarith [Real.pi_lt_d6])
    norm_num
  have he := cosDoubleCheck_sound (by norm_num : 0 < 10000000000000000) hs
    (by decide +kernel : cosDoubleCheck 10000000000000000 9999962230644424 [9999848922863000, 9999395696016860, 9997582857104100, 9990332596932355, 9961349079465834, 9845695096594963, 9387542387022819, 7625190413630017, 1628705768823021, -9469463503720523] = true)
  norm_num only [cosEnd, List.length_cons, List.length_nil, Nat.reduceAdd] at he
  rw [show (1024 : ℝ) * ((Real.pi - (409 / 1250 : ℝ)) / 1024) = Real.pi - (409 / 1250 : ℝ) by ring,
    Real.cos_pi_sub] at he
  norm_num at he
  linarith

lemma gamma_bounds : (1.3802 : ℝ) ≤ Real.arccos (25 / 132) ∧
    Real.arccos (25 / 132) ≤ 1.3803 := by
  constructor
  · have h := Real.arccos_le_arccos cos_gamma_lo
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
    convert h using 1 <;> norm_num
  · have h := Real.arccos_le_arccos cos_gamma_hi
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
    convert h using 1 <;> norm_num

lemma delta_bounds : (0.3271 : ℝ) ≤ Real.arccos (125 / 132) ∧
    Real.arccos (125 / 132) ≤ 0.3272 := by
  constructor
  · have h := Real.arccos_le_arccos cos_delta_lo
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
    convert h using 1 <;> norm_num
  · have h := Real.arccos_le_arccos cos_delta_hi
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
    convert h using 1 <;> norm_num

lemma q_bounds : (0.5653 : ℝ) ≤ q ∧ q ≤ 0.5654 := by
  unfold q
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num)).mpr
    have h := Real.exp_bound' (x := (0.5653 : ℝ)) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith
  · apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (x := (0.5654 : ℝ)) (by norm_num) 12
    norm_num [Finset.sum_range_succ] at h
    linarith

lemma log_two_pi_lower : (1.8378 : ℝ) ≤ Real.log (2 * Real.pi) := by
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  have h := Real.exp_bound' (x := (0.9189 : ℝ)) (by norm_num) (by norm_num) (n := 14) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  have h1 : Real.exp (0.9189 : ℝ) ≤ 2.5066 := by linarith
  have h2 := pow_le_pow_left₀ (Real.exp_nonneg (0.9189 : ℝ)) h1 2
  rw [← Real.exp_nat_mul] at h2
  norm_num at h2
  nlinarith [Real.pi_gt_d6]

lemma log_center_upper : Real.log (3.426 : ℝ) ≤ 1.2315 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (x := (1.2315 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma first_sine_bounds : (5.1844 : ℝ) / 4 ≤ radius * Real.sin alpha ∧
    radius * Real.sin alpha ≤ 5.1845 / 4 := by
  have hcos : Real.cos alpha = -(25 / 132 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
  have hs0 : 0 ≤ radius * Real.sin alpha := mul_nonneg (by norm_num [radius])
    (Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
  have hs := Real.sin_sq_add_cos_sq alpha
  rw [hcos] at hs
  constructor
  · apply (sq_le_sq₀ (by norm_num) hs0).mp
    unfold radius
    nlinarith
  · apply (sq_le_sq₀ hs0 (by norm_num)).mp
    unfold radius
    nlinarith

lemma second_sine_bounds : (1.6965 : ℝ) / 4 ≤ radius * Real.sin beta ∧
    radius * Real.sin beta ≤ 1.6966 / 4 := by
  have hcos : Real.cos beta = -(125 / 132 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
  have hs0 : 0 ≤ radius * Real.sin beta := mul_nonneg (by norm_num [radius])
    (Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
  have hs := Real.sin_sq_add_cos_sq beta
  rw [hcos] at hs
  constructor
  · apply (sq_le_sq₀ (by norm_num) hs0).mp
    unfold radius
    nlinarith
  · apply (sq_le_sq₀ hs0 (by norm_num)).mp
    unfold radius
    nlinarith

lemma slopeA_bounds : (0.1359 : ℝ) ≤ slopeA ∧ slopeA ≤ 0.1361 := by
  have hq0 : 0 < q := q_pos
  have hα : Real.pi - alpha = Real.arccos (25 / 132) := by unfold alpha; rw [Real.arccos_neg]; ring
  have hβ : Real.pi - beta = Real.arccos (125 / 132) := by unfold beta; rw [Real.arccos_neg]; ring
  have hdenpos : 0 < 4 * Real.pi * q := by positivity [q_pos]
  have hdenlo : 4 * (3.141592 : ℝ) * 0.5653 ≤ 4 * Real.pi * q := by
    gcongr
    · exact Real.pi_gt_d6.le
    · exact q_bounds.1
  have hdenhi : 4 * Real.pi * q ≤ 4 * (3.141593 : ℝ) * 0.5654 := by
    gcongr
    · exact Real.pi_lt_d6.le
    · exact q_bounds.2
  unfold slopeA
  rw [hα, hβ]
  constructor
  · apply (le_div_iff₀ hdenpos).mpr
    nlinarith [first_sine_bounds.1, second_sine_bounds.1, gamma_bounds.2, delta_bounds.2]
  · apply (div_le_iff₀ hdenpos).mpr
    nlinarith [first_sine_bounds.2, second_sine_bounds.2, gamma_bounds.1, delta_bounds.1]

lemma slopeB_le : slopeB ≤ (0.4423 : ℝ) := by
  unfold slopeB
  apply (div_le_iff₀ (by positivity [q_pos])).mpr
  nlinarith [q_bounds.1]

lemma intercept_le_strong : intercept 0.1361 ≤ (1.5803 : ℝ) := by
  have hq0 : 0 < q := q_pos
  have hA0 : 0 ≤ slopeA := by linarith [slopeA_bounds.1]
  have hlog0 : 0 ≤ Real.log (3.426 : ℝ) := Real.log_nonneg (by norm_num)
  have h1 : (0.1361 : ℝ) / q ≤ 0.1361 / 0.5653 := by
    gcongr
    exact q_bounds.1
  have h2 : Real.log (3.426 : ℝ) / (2 * q) ≤ 1.2315 / (2 * 0.5653) := by
    gcongr
    · exact log_center_upper
    · exact q_bounds.1
  have h3 : (0.1359 : ℝ) * 1.8378 ≤ slopeA * Real.log (2 * Real.pi) := by
    gcongr
    · exact slopeA_bounds.1
    · exact log_two_pi_lower
  unfold intercept
  linarith

lemma intercept_le : intercept 0.1361 ≤ (1.581 : ℝ) := by
  linarith [intercept_le_strong]

end TernaryGoldbach.RSBounds.BacklundAngularCoefficients
