import RSBounds.SchoenfeldReciprocalSquare
import RSBounds.PolynomialZeroCountBridge
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# The absolutely convergent degree-two zero potential

The indexing type consists of actual nonreal zeta zeros, and the coefficient
uses their actual analytic multiplicity. The finite reciprocal-square bound
implies summability of the ordinate majorant. Dominated convergence
then makes the degree-two potential tend to zero as `x → ∞`, using only the
strict critical strip. There is no RH or effective PNT assumption.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.MertensZeroPotential

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialZeroCountBridge
  BacklundCountIdentity SchoenfeldReciprocalSquare

def IsZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ ρ.im ≠ 0

abbrev Zero := {ρ : ℂ // IsZero ρ}

noncomputable def multiplicity (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

noncomputable def zeroFinset (T : ℝ) : Finset Zero := by
  classical
  exact (zerosRectD zetaF T).subtype IsZero

theorem mem_zeroFinset {T : ℝ} (hT : 0 < T) (ρ : Zero) :
    ρ ∈ zeroFinset T ↔ |ρ.val.im| < T := by
  classical
  simp [zeroFinset, mem_zerosRectD_zetaF_iff hT, ρ.property.1, ρ.property.2]

theorem zero_re_strip (ρ : Zero) : 0 < ρ.val.re ∧ ρ.val.re < 1 :=
  xiF_zero_re_strip (xiF_eq_zero_of_zeta_zero ρ.property.2 ρ.property.1)

theorem sum_zeroFinset {E : Type*} [AddCommMonoid E] {T : ℝ} (hT : 0 < T)
    (f : ℂ → E) :
    (∑ ρ ∈ zeroFinset T, f ρ.val) = ∑ ρ ∈ zerosRectD zetaF T, f ρ := by
  classical
  exact Finset.sum_subtype_of_mem f (fun ρ hρ =>
    ⟨((mem_zerosRectD_zetaF_iff hT).mp hρ).1,
      ((mem_zerosRectD_zetaF_iff hT).mp hρ).2.1⟩)

/-- Exhaustion of all actual nonreal zeros does not assume a zero enumeration. -/
theorem tendsto_zeroFinset {T : ℕ → ℝ} {B : ℝ → ℝ}
    (hT : GoodHeights zetaF B T) : Tendsto (fun k => zeroFinset (T k)) atTop atTop := by
  classical
  have hp (k : ℕ) : 0 < T k := by
    linarith [(hT.mem k).1, Nat.cast_nonneg (α := ℝ) k]
  have hm : Monotone (fun k => zeroFinset (T k)) := by
    intro j k hjk ρ hρ
    rw [mem_zeroFinset (hp j)] at hρ
    rw [mem_zeroFinset (hp k)]
    rcases eq_or_lt_of_le hjk with rfl | hjk
    · exact hρ
    · have hcast : (j : ℝ) + 1 ≤ k := by exact_mod_cast (Nat.succ_le_of_lt hjk)
      exact hρ.trans_le (by linarith [(hT.mem j).2, (hT.mem k).1])
  apply hm.tendsto_atTop_finset
  intro ρ
  obtain ⟨k, hk⟩ := exists_nat_gt |ρ.val.im|
  exact ⟨k, (mem_zeroFinset (hp k) ρ).mpr
    (hk.trans_le (by linarith [(hT.mem k).1]))⟩

theorem zetaGoodHeight_of_heights {T : ℕ → ℝ} {B : ℝ → ℝ}
    (hT : GoodHeights zetaF B T) (k : ℕ) : zetaGoodHeight (T k) := by
  have hp : 0 < T k := by linarith [(hT.mem k).1, Nat.cast_nonneg (α := ℝ) k]
  intro ρ hz he
  have him : ρ.im ≠ 0 := by rw [he]; exact hp.ne'
  have hxi := xiF_eq_zero_of_zeta_zero him hz
  have hr := xiF_zero_re_strip hxi
  have hs : ρ.re ∈ uIcc (-1 / 2 : ℝ) (3 / 2) := by
    rw [uIcc_of_le (by norm_num)]
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hn := ((hT.bounds k ρ.re hs).1).1
  have hρ : (ρ.re : ℂ) + (T k : ℂ) * I = ρ := by
    apply Complex.ext <;> simp [he]
  rw [hρ, zetaF_of_ne (by intro h; simp [h] at hr), hz, mul_zero] at hn
  exact hn rfl

noncomputable def moment (ρ : Zero) : ℝ := (multiplicity ρ.val : ℝ) / |ρ.val.im| ^ 2

theorem moment_nonneg (ρ : Zero) : 0 ≤ moment ρ := by
  unfold moment
  positivity

noncomputable def momentAllowance : ℝ := 1.0013 * (2 * (logDeriv xiF 1).re)

theorem momentAllowance_lt : momentAllowance < 0.0463 := normalized_allowance_lt

/-- Every finite set of actual zeros satisfies one common moment bound. -/
theorem sum_moment_le_allowance (S : Finset Zero) :
    (∑ ρ ∈ S, moment ρ) ≤ momentAllowance := by
  classical
  have hS : ∀ ρ ∈ S.image Subtype.val, xiF ρ = 0 := by
    intro ρ hρ
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hρ
    exact xiF_eq_zero_of_zeta_zero z.property.2 z.property.1
  have h : (∑ ρ ∈ S.image Subtype.val,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ρ.im ^ 2) ≤ momentAllowance := by
    change _ ≤ 1.0013 * (2 * (logDeriv xiF 1).re)
    convert finite_xi_reciprocal_square_sum_le (S.image Subtype.val) hS using 1
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [analyticOrderAt_xi_eq_zeta (hS ρ hρ)]
  have he : (∑ ρ ∈ S, moment ρ) =
      ∑ ρ ∈ S.image Subtype.val, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ρ.im ^ 2 := by
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    simp only [moment, multiplicity, sq_abs]
  rw [he]
  exact h

/-- The actual finite-zero bound supplies the global reciprocal-square majorant. -/
theorem summable_moment : Summable moment :=
  summable_of_sum_le moment_nonneg sum_moment_le_allowance

theorem tsum_moment_le_allowance : (∑' ρ : Zero, moment ρ) ≤ momentAllowance :=
  summable_moment.tsum_le_of_sum_le sum_moment_le_allowance

theorem tsum_moment_lt : (∑' ρ : Zero, moment ρ) < 0.0463 :=
  tsum_moment_le_allowance.trans_lt momentAllowance_lt

/-- One actual multiplicity-weighted degree-two coefficient. -/
noncomputable def coefficient (x : ℝ) (ρ : Zero) : ℂ :=
  (multiplicity ρ.val : ℂ) * (x : ℂ) ^ (ρ.val - 1) / (ρ.val * (ρ.val - 1))

theorem norm_coefficient_le_power_moment {x : ℝ} (hx : 0 < x) (ρ : Zero) :
    ‖coefficient x ρ‖ ≤ x ^ (ρ.val.re - 1) * moment ρ := by
  have hi : 0 < |ρ.val.im| := abs_pos.mpr ρ.property.2
  have hden : |ρ.val.im| ^ 2 ≤ ‖ρ.val‖ * ‖ρ.val - 1‖ := by
    have h1 := Complex.abs_im_le_norm ρ.val
    have h2 := Complex.abs_im_le_norm (ρ.val - 1)
    simp only [sub_im, one_im, sub_zero] at h2
    simpa only [pow_two] using mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  rw [coefficient, norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_mul]
  simp only [sub_re, one_re]
  calc
    (multiplicity ρ.val : ℝ) * x ^ (ρ.val.re - 1) / (‖ρ.val‖ * ‖ρ.val - 1‖)
      ≤ (multiplicity ρ.val : ℝ) * x ^ (ρ.val.re - 1) / |ρ.val.im| ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by unfold moment; ring

theorem norm_coefficient_le_moment {x : ℝ} (hx : 1 ≤ x) (ρ : Zero) :
    ‖coefficient x ρ‖ ≤ moment ρ := by
  have hx0 : 0 < x := by linarith
  have hp : x ^ (ρ.val.re - 1) ≤ (1 : ℝ) := by
    exact (Real.rpow_le_rpow_of_exponent_le hx (by linarith [(zero_re_strip ρ).2])).trans_eq
      (Real.rpow_zero x)
  exact (norm_coefficient_le_power_moment hx0 ρ).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (moment_nonneg ρ))

theorem summable_coefficient {x : ℝ} (hx : 1 ≤ x) : Summable (coefficient x) :=
  Summable.of_norm_bounded summable_moment (norm_coefficient_le_moment hx)

noncomputable def potential (x : ℝ) : ℂ := ∑' ρ : Zero, coefficient x ρ

theorem coefficient_tendsto_zero (ρ : Zero) :
    Tendsto (fun x : ℝ => coefficient x ρ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_rpow_neg_atTop
    (show 0 < 1 - ρ.val.re by linarith [(zero_re_strip ρ).2])).const_mul
      ((multiplicity ρ.val : ℝ) / (‖ρ.val‖ * ‖ρ.val - 1‖))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [coefficient, norm_div, norm_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [sub_re, one_re]
  rw [show -(1 - ρ.val.re) = ρ.val.re - 1 by ring]
  ring

/-- Absolute convergence makes the potential decay without an RH premise. -/
theorem potential_tendsto_zero : Tendsto potential atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence summable_moment coefficient_tendsto_zero
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact norm_coefficient_le_moment hx)
  change Tendsto (fun x : ℝ => ∑' ρ : Zero, coefficient x ρ) atTop (𝓝 0)
  simpa only [tsum_zero] using h

/-- The actual finite rectangle sums converge to the absolutely convergent potential. -/
theorem sum_tendsto_potential {x : ℝ} (hx : 1 ≤ x) {T : ℕ → ℝ} {B : ℝ → ℝ}
    (hT : GoodHeights zetaF B T) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) *
        ((x : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)))) atTop (𝓝 (potential x)) := by
  have h := (summable_coefficient hx).hasSum.comp (tendsto_zeroFinset hT)
  unfold potential
  convert h using 1
  ext k
  have hp : 0 < T k := by linarith [(hT.mem k).1, Nat.cast_nonneg (α := ℝ) k]
  change _ = ∑ ρ ∈ zeroFinset (T k),
    (multiplicity ρ.val : ℂ) * (x : ℂ) ^ (ρ.val - 1) / (ρ.val * (ρ.val - 1))
  rw [sum_zeroFinset hp (fun ρ : ℂ =>
    (multiplicity ρ : ℂ) * (x : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)))]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [multRectD_zetaF_eq_analyticOrder hp hρ]
  unfold multiplicity
  ring

end TernaryGoldbach.RSBounds.MertensZeroPotential
