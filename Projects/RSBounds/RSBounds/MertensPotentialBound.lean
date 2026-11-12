import RSBounds.MertensZeroPotential
import RSBounds.RosserSquareTail
import RSBounds.RS75DecayingHighZeros
import RSBounds.Targets
import RSBounds.MertensTailScalars
import RSBounds.MertensSignedLimit
import RSBounds.MertensDLimit
import RSBounds.MertensModerateBudget

/-!
# Finite-RH bounds for the signed-tail zero potential

The low part uses finite RH only through the displayed height A; the high
part uses the unconditional actual-zero count. This estimate is intended for
a bounded range of log x. Its fixed high-tail constant is not a substitute
for a decaying estimate on an unbounded range.
-/

open Complex Set Filter
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.MertensPotentialBound

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialExplicit PolynomialZeroCountBridge
  MertensZeroPotential WeightedZetaZeros RosserSquareTail

noncomputable def tailMoment (A : ℝ) (ρ : Zero) : ℝ :=
  if A < |ρ.val.im| then moment ρ else 0

theorem tailMoment_nonneg (A : ℝ) (ρ : Zero) : 0 ≤ tailMoment A ρ := by
  unfold tailMoment
  split_ifs
  · exact moment_nonneg ρ
  · exact le_rfl

theorem tailMoment_le (A : ℝ) (ρ : Zero) : tailMoment A ρ ≤ moment ρ := by
  unfold tailMoment
  split_ifs
  · exact le_rfl
  · exact moment_nonneg ρ

theorem summable_tailMoment (A : ℝ) : Summable (tailMoment A) :=
  summable_moment.of_norm_bounded (fun ρ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (tailMoment_nonneg A ρ)]
    exact tailMoment_le A ρ)

theorem sum_tailMoment_zeroFinset {A T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    (∑ ρ ∈ zeroFinset T, tailMoment A ρ) =
      2 * weightedSum A T (fun t => 1 / t ^ 2) := by
  classical
  change (∑ ρ ∈ zeroFinset T, if A < |ρ.val.im| then
    (multiplicity ρ.val : ℝ) / |ρ.val.im| ^ 2 else 0) = _
  rw [sum_zeroFinset hT (fun ρ : ℂ => if A < |ρ.im| then
    (multiplicity ρ : ℝ) / |ρ.im| ^ 2 else 0)]
  rw [← RS75DecayingHighZeros.sum_filtered_weight_eq_two hT hg A (fun t => 1 / t ^ 2),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [multRectD_zetaF_eq_analyticOrder hT hρ]
  simp only [MertensZeroPotential.multiplicity, mul_one_div]

theorem sum_tailMoment_le {A : ℝ} (hA : 7 ≤ A) (S : Finset Zero) :
    (∑ ρ ∈ S, tailMoment A ρ) ≤ 2 * squareAllowance A := by
  classical
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  have hev : ∀ᶠ k : ℕ in atTop, S ⊆ zeroFinset (T k) :=
    (tendsto_zeroFinset hT).eventually (eventually_ge_atTop S)
  have hTop : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun k => (hT.mem k).1)
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨k, hS, hAT⟩ := (hev.and (hTop.eventually (eventually_ge_atTop A))).exists
  have hp : 0 < T k := by linarith
  calc
    _ ≤ ∑ ρ ∈ zeroFinset (T k), tailMoment A ρ :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun ρ _ _ => tailMoment_nonneg A ρ)
    _ = 2 * weightedSum A (T k) (fun t => 1 / t ^ 2) :=
      sum_tailMoment_zeroFinset hp (zetaGoodHeight_of_heights hT k)
    _ ≤ _ := mul_le_mul_of_nonneg_left (square_sum_le hA hAT) (by norm_num)

theorem tsum_tailMoment_le {A : ℝ} (hA : 7 ≤ A) :
    (∑' ρ : Zero, tailMoment A ρ) ≤ 2 * squareAllowance A :=
  (summable_tailMoment A).tsum_le_of_sum_le (sum_tailMoment_le hA)

/-- The finite-RH premise is used only for zeros whose absolute ordinate is ≤A. -/
theorem norm_coefficient_le_head_add_tail {A x : ℝ} (hRH : Goals.FiniteRH A)
    (hx : 1 ≤ x) (ρ : Zero) :
    ‖coefficient x ρ‖ ≤ x ^ (-1 / 2 : ℝ) * moment ρ + tailMoment A ρ := by
  by_cases hA : A < |ρ.val.im|
  · rw [tailMoment, if_pos hA]
    exact (norm_coefficient_le_moment hx ρ).trans
      (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (moment_nonneg ρ)))
  · have hre := hRH ρ.val ρ.property.1 (zero_re_strip ρ).1 (zero_re_strip ρ).2
      (le_of_not_gt hA)
    have h := norm_coefficient_le_power_moment (by linarith : 0 < x) ρ
    rw [hre] at h
    rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] at h
    simpa only [tailMoment, if_neg hA, add_zero] using h

/-- A sharp low-zero coefficient and an explicit uniform high-zero allowance.
The conclusion deliberately retains the finite-RH hypothesis. -/
theorem norm_potential_le {A x : ℝ} (hA : 7 ≤ A) (hRH : Goals.FiniteRH A)
    (hx : 1 ≤ x) :
    ‖potential x‖ ≤ 0.0463 * x ^ (-1 / 2 : ℝ) + 2 * squareAllowance A := by
  have hn : Summable (fun ρ : Zero => ‖coefficient x ρ‖) :=
    summable_moment.of_norm_bounded (fun ρ => by
      rw [norm_norm]
      exact norm_coefficient_le_moment hx ρ)
  have hb : Summable (fun ρ : Zero =>
      x ^ (-1 / 2 : ℝ) * moment ρ + tailMoment A ρ) :=
    (summable_moment.mul_left _).add (summable_tailMoment A)
  calc
    ‖potential x‖ ≤ ∑' ρ : Zero, ‖coefficient x ρ‖ := by
      change ‖∑' ρ : Zero, coefficient x ρ‖ ≤ _
      exact norm_tsum_le_tsum_norm hn
    _ ≤ ∑' ρ : Zero, (x ^ (-1 / 2 : ℝ) * moment ρ + tailMoment A ρ) :=
      hn.tsum_le_tsum (norm_coefficient_le_head_add_tail hRH hx) hb
    _ = x ^ (-1 / 2 : ℝ) * (∑' ρ : Zero, moment ρ) +
        ∑' ρ : Zero, tailMoment A ρ := by
      rw [Summable.tsum_add (summable_moment.mul_left _) (summable_tailMoment A),
        tsum_mul_left]
    _ ≤ _ := by
      have hp : 0 ≤ x ^ (-1 / 2 : ℝ) := by positivity
      have hm := mul_le_mul_of_nonneg_left tsum_moment_lt.le hp
      have ht := tsum_tailMoment_le hA
      nlinarith only [hm, ht]

theorem squareAllowance_A_lt : squareAllowance 1894439 < 1.2e-6 := by
  unfold squareAllowance squarePrimitive RosserTailIntegrals.coefficient rosserR
  exact MertensTailScalars.square_tail_A_lt

/-- A numerical moderate-range zero-potential estimate, with finite RH explicit. -/
theorem norm_potential_A_lt {x : ℝ} (hRH : Goals.FiniteRH 1894439) (hx : 1 ≤ x) :
    ‖potential x‖ < 0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 := by
  have h := norm_potential_le (by norm_num : (7 : ℝ) ≤ 1894439) hRH hx
  linarith [squareAllowance_A_lt]

/-- The corresponding explicit bound for the actual improper signed psi tail. -/
theorem norm_signedLimit_A_lt {x : ℝ} (hRH : Goals.FiniteRH 1894439) (hx : 1 ≤ x) :
    ‖MertensSignedLimit.signedLimit x‖ <
      0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
        Real.log (2 * Real.pi) / x := by
  have h := MertensSignedLimit.norm_signedLimit_le hx
  have hp := norm_potential_A_lt hRH hx
  linarith

/-- A single numerical budget controls the whole improper tail u≥x. -/
theorem norm_signedLimit_A_lt_uniform {x u : ℝ}
    (hRH : Goals.FiniteRH 1894439) (hx : 1 ≤ x) (hxu : x ≤ u) :
    ‖MertensSignedLimit.signedLimit u‖ <
      0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
        Real.log (2 * Real.pi) / x := by
  have hx0 : 0 < x := by linarith
  have h := norm_signedLimit_A_lt hRH (hx.trans hxu)
  have h1 := Real.rpow_le_rpow_of_nonpos hx0 hxu (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have h3 := Real.rpow_le_rpow_of_nonpos hx0 hxu (by norm_num : (-3 / 2 : ℝ) ≤ 0)
  have hl : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hi := div_le_div_of_nonneg_left hl hx0 hxu
  linarith

/-- The uniform budget is bound to the actual signed function in Lemma 8. -/
theorem abs_J_A_lt_uniform {x u : ℝ}
    (hRH : Goals.FiniteRH 1894439) (hx : 1 ≤ x) (hxu : x ≤ u) :
    |MertensSecondSigned.J u| <
      0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
        Real.log (2 * Real.pi) / x := by
  rw [MertensDLimit.J_eq_signedLimit (hx.trans hxu)]
  exact (Complex.abs_re_le_norm _).trans_lt (norm_signedLimit_A_lt_uniform hRH hx hxu)

/-- The scalar budget closes the whole finite-to-b23 range once the actual
moderate psi estimate is supplied. The displayed psi premise is a theorem
interface, not an axiom. -/
theorem mertens_lower_of_moderate_psi {x : ℝ}
    (hRH : Goals.FiniteRH 1894439) (hx : 100000 ≤ x) (hlog : Real.log x ≤ 23)
    (hpsi : |Chebyshev.psi x - x| ≤ 0.0023 * x + 6 * Real.sqrt x) :
    Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x := by
  refine MertensDLimit.mertens_lower_of_errors
    (e := 0.0023 + 6 / Real.sqrt x)
    (j := 0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
      Real.log (2 * Real.pi) / x) (by linarith) ?_ ?_
    (MertensModerateBudget.budget_lt hx hlog)
  · rw [MertensModerateBudget.error_mul_eq (by linarith : 0 < x)]
    exact hpsi
  · exact (norm_signedLimit_A_lt hRH (by linarith)).le

/-- The actual signed-tail budget closes the b23 range through log x=2400. -/
theorem mertens_lower_of_b23_psi {x : ℝ}
    (hRH : Goals.FiniteRH 1894439) (hx : 1000000000 ≤ x) (hlog : Real.log x ≤ 2400)
    (hpsi : |Chebyshev.psi x - x| ≤ 0.00020211 * x) :
    Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x := by
  exact MertensDLimit.mertens_lower_of_errors
    (j := 0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
      Real.log (2 * Real.pi) / x) (by linarith) hpsi
    (norm_signedLimit_A_lt hRH (by linarith)).le
    (MertensModerateBudget.b23_budget_lt hx hlog)

end TernaryGoldbach.RSBounds.MertensPotentialBound
