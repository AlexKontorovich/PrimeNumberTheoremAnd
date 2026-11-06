import RSBounds.BacklundCircleMajorantDef
import RSBounds.BacklundRightArc
import RSBounds.BacklundLeftZetaBoundary

open Complex Real Set

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

theorem height_bounds {T t : ℝ} (hT : 100 ≤ T) (ht : T - radius ≤ t) :
    50 ≤ t := by
  dsimp [radius] at ht
  linarith

theorem log_height_pos {T : ℝ} (hT : 100 ≤ T) : 0 < Real.log (T + radius) :=
  Real.log_pos (by dsimp [radius]; linarith)

theorem heightLog_nonneg {T : ℝ} (hT : 100 ≤ T) : 0 ≤ heightLog T := by
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
    (show (3 : ℝ) ≤ T + radius by dsimp [radius]; linarith)
  exact Real.log_nonneg (by linarith [Real.log_three_gt_d9])

theorem powerLog_nonneg {T : ℝ} (hT : 100 ≤ T) : 0 ≤ powerLog T := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
  dsimp [radius]
  nlinarith [Real.pi_lt_four]

theorem strip_den_pos {T : ℝ} (hT : 100 ≤ T) : 0 < (T - radius) ^ 2 - 4 := by
  have hl : 50 ≤ T - radius := height_bounds hT le_rfl
  nlinarith

theorem stripLog_nonneg {T : ℝ} (hT : 100 ≤ T) : 0 ≤ stripLog T := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (strip_den_pos hT)]
  linarith

theorem scalar_nonneg {H L V σ : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (hV : 0 ≤ V) :
    0 ≤ scalar H L V σ := by
  unfold scalar
  split_ifs with hσ hstrip
  · exact BacklundRightArc.logZeta_nonneg (by linarith)
  · positivity
  · positivity

theorem majorant_nonneg {T : ℝ} (hT : 100 ≤ T) (z : ℂ) : 0 ≤ majorant T z :=
  scalar_nonneg (heightLog_nonneg hT) (powerLog_nonneg hT) (stripLog_nonneg hT)

theorem exp_heightLog {T : ℝ} (hT : 100 ≤ T) :
    Real.exp (heightLog T) = Real.log (T + radius) := Real.exp_log (log_height_pos hT)

theorem exp_stripLog {T : ℝ} (hT : 100 ≤ T) :
    Real.exp (stripLog T) = (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
  have hl : 0 < T - radius := by have := height_bounds hT (t := T - radius) le_rfl; linarith
  apply Real.exp_log
  exact div_pos (sq_pos_of_pos hl) (strip_den_pos hT)

theorem exp_height_power {T e : ℝ} (hT : 100 ≤ T) :
    Real.exp (heightLog T + e * powerLog T) =
      Real.log (T + radius) * ((T + radius) / (2 * Real.pi)) ^ e := by
  have hupper : 0 < T + radius := by dsimp [radius]; linarith
  have hbase : 0 < (T + radius) / (2 * Real.pi) := by positivity
  rw [Real.exp_add, exp_heightLog hT, Real.rpow_def_of_pos hbase]
  congr 2
  unfold powerLog
  ring

theorem exp_height_power_strip {T e : ℝ} (hT : 100 ≤ T) :
    Real.exp (heightLog T + e * powerLog T + stripLog T) =
      Real.log (T + radius) * ((T + radius) / (2 * Real.pi)) ^ e *
        ((T - radius) ^ 2 / ((T - radius) ^ 2 - 4)) := by
  rw [Real.exp_add, exp_height_power hT, exp_stripLog hT]

theorem scalar_right {H L V σ : ℝ} (hσ : 5 / 4 ≤ σ) :
    scalar H L V σ = Real.log ‖riemannZeta (σ : ℂ)‖ := by simp [scalar, hσ]

theorem scalar_one {H L V σ : ℝ} (hσ : 1 ≤ σ) (hσ' : σ < 5 / 4) :
    scalar H L V σ = H := by
  simp [scalar, not_le.mpr hσ', max_eq_right (by linarith : 1 - σ ≤ 0),
    max_eq_right (by linarith : -σ ≤ 0), not_lt.mpr hσ]

theorem scalar_middle {H L V σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1) :
    scalar H L V σ = H + ((1 - σ) / 2) * L + V := by
  simp [scalar, show ¬5 / 4 ≤ σ by linarith, hσ, hσ',
    max_eq_left (by linarith : 0 ≤ 1 - σ)]
  ring

theorem scalar_left {H L V σ : ℝ} (hσ : σ < 0) :
    scalar H L V σ = H + (1 / 2 - σ) * L := by
  simp [scalar, show ¬5 / 4 ≤ σ by linarith, not_le.mpr hσ,
    max_eq_left (by linarith : 0 ≤ 1 - σ), max_eq_left (by linarith : 0 ≤ -σ)]
  ring

theorem power_log_mono {T t e : ℝ} (hT : 100 ≤ T)
    (ht0 : T - radius ≤ t) (ht1 : t ≤ T + radius) (he : 0 ≤ e) :
    (t / (2 * Real.pi)) ^ e * Real.log t ≤
      ((T + radius) / (2 * Real.pi)) ^ e * Real.log (T + radius) := by
  have ht50 := height_bounds hT ht0
  have hT0 : 0 < T := by linarith
  have hupper : 0 < T + radius := by dsimp [radius]; linarith
  have hbase : 0 ≤ t / (2 * Real.pi) := by positivity
  apply mul_le_mul
  · exact Real.rpow_le_rpow hbase (div_le_div_of_nonneg_right ht1 (by positivity)) he
  · exact Real.log_le_log (by linarith) ht1
  · exact Real.log_nonneg (by linarith)
  · positivity

theorem strip_ratio_antitone {T t : ℝ} (hT : 100 ≤ T) (ht : T - radius ≤ t) :
    t ^ 2 / (t ^ 2 - 4) ≤ (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
  have hl := height_bounds hT (t := T - radius) le_rfl
  have ht50 := height_bounds hT ht
  have hd : 0 < t ^ 2 - 4 := by nlinarith
  have hs : (T - radius) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by linarith) ht 2
  rw [div_le_div_iff₀ hd (strip_den_pos hT)]
  nlinarith

theorem sphere_coordinates {z : ℂ}
    (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
    -(1 / 2 : ℝ) ≤ z.re ∧ |z.im| ≤ radius := by
  have hn : ‖z - (5 / 4 : ℂ)‖ = radius := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z - (5 / 4 : ℂ))
  have hi := Complex.abs_im_le_norm (z - (5 / 4 : ℂ))
  rw [hn] at hr hi
  norm_num [Complex.sub_re, Complex.sub_im] at hr hi
  refine ⟨?_, hi⟩
  have hlo := (abs_le.mp hr).1
  dsimp [radius] at hlo
  linarith

theorem sphere_heights {T : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
    (T - radius ≤ T + z.im ∧ T + z.im ≤ T + radius) ∧
      (T - radius ≤ T - z.im ∧ T - z.im ≤ T + radius) := by
  rcases abs_le.mp (sphere_coordinates hz).2 with ⟨hlo, hhi⟩
  constructor <;> constructor <;> linarith

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
