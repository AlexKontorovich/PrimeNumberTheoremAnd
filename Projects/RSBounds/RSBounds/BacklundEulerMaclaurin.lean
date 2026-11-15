import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# The second-order Euler--Maclaurin step for Backlund's zeta bound

Backlund's equation (8), and consequently his sharp right-edge estimate,
need one more integration by parts than the existing first-order sawtooth
formula. This file proves the local quadrature identity and its sharp
`1/12` error bound directly from Mathlib integration by parts.
-/

open Complex MeasureTheory Set Filter
open scoped Interval Topology

namespace TernaryGoldbach.RSBounds.BacklundEulerMaclaurin

noncomputable def firstWeight (a x : ℝ) : ℂ := ((x - a - 1 / 2 : ℝ) : ℂ)

noncomputable def secondWeight (a x : ℝ) : ℂ :=
  (((x - a) ^ 2 - (x - a) + 1 / 6 : ℝ) / 2 : ℝ)

theorem hasDerivAt_firstWeight (a x : ℝ) :
    HasDerivAt (firstWeight a) 1 x := by
  unfold firstWeight
  convert (((hasDerivAt_id x).sub_const a).sub_const (1 / 2)).ofReal_comp using 1 <;> simp

theorem hasDerivAt_secondWeight (a x : ℝ) :
    HasDerivAt (secondWeight a) (firstWeight a x) x := by
  unfold secondWeight firstWeight
  convert ((((hasDerivAt_id x).sub_const a).pow 2).sub
    ((hasDerivAt_id x).sub_const a) |>.add_const (1 / 6) |>.div_const 2).ofReal_comp using 1 <;>
    simp <;> ring

theorem norm_secondWeight_le (a : ℝ) {x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    ‖secondWeight a x‖ ≤ 1 / 12 := by
  rw [secondWeight, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hu : 0 ≤ x - a := by linarith [hx.1]
  have hv : x - a ≤ 1 := by linarith [hx.2]
  have hp : (x - a) ^ 2 ≤ x - a := by nlinarith
  constructor <;> nlinarith [sq_nonneg (x - a - 1 / 2)]

/-- The exact one-interval formula, before discarding the Bernoulli weight. -/
theorem local_identity {f g h : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a (a + 1), HasDerivAt g (h x) x)
    (hgi : IntervalIntegrable g volume a (a + 1))
    (hhi : IntervalIntegrable h volume a (a + 1)) :
    (f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x)
      - (g (a + 1) - g a) / 12 =
      -(∫ x in a..a + 1, secondWeight a x * h x) := by
  have hab : a ≤ a + 1 := by linarith
  have hfi : IntervalIntegrable f volume a (a + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := firstWeight a) (u' := fun _ => (1 : ℂ)) (v := f) (v' := g)
    (fun x _ => hasDerivAt_firstWeight a x)
    (fun x hx => hf x (by simpa [uIcc_of_le hab] using hx))
    intervalIntegrable_const hgi
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := secondWeight a) (u' := firstWeight a) (v := g) (v' := h)
    (fun x _ => hasDerivAt_secondWeight a x)
    (fun x hx => hg x (by simpa [uIcc_of_le hab] using hx))
    ((show Continuous (firstWeight a) by unfold firstWeight; fun_prop).intervalIntegrable _ _) hhi
  simp only [one_mul] at h1
  rw [h1] at h2
  norm_num [firstWeight, secondWeight] at h2
  unfold secondWeight
  push_cast
  linear_combination h2

/-- A sharp local second-order quadrature bound. -/
theorem local_error_le {f g h : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a (a + 1), HasDerivAt g (h x) x)
    (hgi : IntervalIntegrable g volume a (a + 1))
    (hhi : IntervalIntegrable h volume a (a + 1)) :
    ‖(f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x)
      - (g (a + 1) - g a) / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in a..a + 1, ‖h x‖ := by
  rw [local_identity hf hg hgi hhi, norm_neg, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ (hhi.norm.const_mul _)
  · filter_upwards with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_secondWeight_le a ⟨hx.1.le, hx.2⟩) (norm_nonneg _)

/-- The finite second-order Euler--Maclaurin estimate with an integral
remainder majorant. The hypotheses are derivatives, not a zeta estimate. -/
theorem finite_error_le {f g h : ℝ → ℂ} (N M : ℕ) (hNM : N ≤ M)
    (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
    (hc : ContinuousOn h (Ici (N : ℝ))) :
    ‖(∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
        - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M, ‖h x‖ := by
  have hfc : ContinuousOn f (Ici (N : ℝ)) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Ici (N : ℝ)) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hint {u v : ℝ} (hu : (N : ℝ) ≤ u) (huv : u ≤ v) :
      IntervalIntegrable f volume u v ∧ IntervalIntegrable g volume u v ∧
        IntervalIntegrable h volume u v := by
    have hsub : uIcc u v ⊆ Ici (N : ℝ) := by
      rw [uIcc_of_le huv]
      exact fun x hx => hu.trans hx.1
    exact ⟨(hfc.mono hsub).intervalIntegrable,
      (hgc.mono hsub).intervalIntegrable, (hc.mono hsub).intervalIntegrable⟩
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
    have hM1 : (M : ℝ) ≤ M + 1 := by linarith
    have hI1 := hint (u := N) (v := M) le_rfl hNM'
    have hI2 := hint (u := M) (v := M + 1) hNM' hM1
    have hloc := local_error_le (a := (M : ℝ))
      (fun x hx => hf x (hNM'.trans hx.1))
      (fun x hx => hg x (hNM'.trans hx.1)) hI2.2.1 hI2.2.2
    have hsumF := intervalIntegral.integral_add_adjacent_intervals hI1.1 hI2.1
    have hsumH := intervalIntegral.integral_add_adjacent_intervals hI1.2.2.norm hI2.2.2.norm
    rw [Finset.sum_Ico_succ_top hNM]
    push_cast
    calc
      _ = ‖((∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
          - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12)
          + ((f M + f (M + 1)) / 2 - (∫ x in (M : ℝ)..M + 1, f x)
            - (g (M + 1) - g M) / 12)‖ := by
        congr 1
        rw [← hsumF]
        ring
      _ ≤ ‖(∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
          - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12‖
          + ‖(f M + f (M + 1)) / 2 - (∫ x in (M : ℝ)..M + 1, f x)
            - (g (M + 1) - g M) / 12‖ := norm_add_le _ _
      _ ≤ (1 / 12 : ℝ) * (∫ x in (N : ℝ)..M, ‖h x‖)
          + (1 / 12 : ℝ) * (∫ x in (M : ℝ)..M + 1, ‖h x‖) :=
        add_le_add ih hloc
      _ = (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M + 1, ‖h x‖ := by
        rw [← mul_add, hsumH]

/-- The infinite-tail form. The limiting and integrability assumptions are
the elementary hypotheses that will be supplied by powers `x^(-s)`. -/
theorem infinite_error_le {f g h : ℝ → ℂ} (N : ℕ) {S : ℂ}
    (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
    (hc : ContinuousOn h (Ici (N : ℝ)))
    (hsum : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M, f k) atTop (𝓝 S))
    (hf0 : Tendsto (fun M : ℕ => f M) atTop (𝓝 0))
    (hg0 : Tendsto (fun M : ℕ => g M) atTop (𝓝 0))
    (hfi : IntegrableOn f (Ioi (N : ℝ)))
    (hhi : IntegrableOn h (Ioi (N : ℝ))) :
    ‖S - (∑ k ∈ Finset.range N, f k) - f N / 2
        - (∫ x in Ioi (N : ℝ), f x) + g N / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in Ioi (N : ℝ), ‖h x‖ := by
  have hsum' : Tendsto (fun M : ℕ => ∑ k ∈ Finset.Ico N M, f k) atTop
      (𝓝 (S - ∑ k ∈ Finset.range N, f k)) := by
    apply (hsum.sub_const _).congr'
    filter_upwards [eventually_ge_atTop N] with M hM
    exact (Finset.sum_Ico_eq_sub _ hM).symm
  have hIF := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hfi
    tendsto_natCast_atTop_atTop
  have hIH := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hhi.norm
    tendsto_natCast_atTop_atTop
  have hL := (((hsum'.add ((hf0.sub_const (f N)).div_const 2)).sub hIF).sub
    ((hg0.sub_const (g N)).div_const 12)).norm
  have hR := hIH.const_mul (1 / 12 : ℝ)
  have hlim := le_of_tendsto_of_tendsto hL hR
    (show ∀ᶠ M : ℕ in atTop,
      ‖(∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
        - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12‖ ≤
        (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M, ‖h x‖ from by
      filter_upwards [eventually_ge_atTop N] with M hM
      exact finite_error_le N M hM hf hg hc)
  convert hlim using 1 <;> congr 1 <;> ring

/-- The regularized version only asks for a limit of `sum − integral`.
Unlike separate convergence, this applies to zeta throughout `Re s > 0`. -/
theorem regularized_infinite_error_le {f g h : ℝ → ℂ} (N : ℕ) {L : ℂ}
    (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
    (hc : ContinuousOn h (Ici (N : ℝ)))
    (hsumint : Tendsto (fun M : ℕ => (∑ k ∈ Finset.Ico N M, f k) -
      (∫ x in (N : ℝ)..M, f x)) atTop (𝓝 L))
    (hf0 : Tendsto (fun M : ℕ => f M) atTop (𝓝 0))
    (hg0 : Tendsto (fun M : ℕ => g M) atTop (𝓝 0))
    (hhi : IntegrableOn h (Ioi (N : ℝ))) :
    ‖L - f N / 2 + g N / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in Ioi (N : ℝ), ‖h x‖ := by
  have hIH := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hhi.norm
    tendsto_natCast_atTop_atTop
  have hL := ((hsumint.add ((hf0.sub_const (f N)).div_const 2)).sub
    ((hg0.sub_const (g N)).div_const 12)).norm
  have hR := hIH.const_mul (1 / 12 : ℝ)
  have hlim := le_of_tendsto_of_tendsto hL hR
    (show ∀ᶠ M : ℕ in atTop,
      ‖((∑ k ∈ Finset.Ico N M, f k) - (∫ x in (N : ℝ)..M, f x)) +
        (f M - f N) / 2 - (g M - g N) / 12‖ ≤
        (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M, ‖h x‖ from by
      filter_upwards [eventually_ge_atTop N] with M hM
      convert finite_error_le N M hM hf hg hc using 1 <;> congr 1 <;> ring)
  convert hlim using 1 <;> congr 1 <;> ring

end TernaryGoldbach.RSBounds.BacklundEulerMaclaurin
