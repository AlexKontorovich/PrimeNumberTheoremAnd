/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import PrimeNumberTheoremAnd.IEANTN.KadiriContourPull
import PrimeNumberTheoremAnd.IEANTN.KadiriEq1618Assembly

/-!
# Wiring the contour pull into the equation (16)-(18) assembly (sprint U8)

This file discharges the two contour-side named hypotheses of the U8 assembly
skeleton (`U8ContourPullIdentity` and `U8ZeroWindowLimit`) from the good-heights
contour machinery of `KadiriContourPull.lean`, and assembles the end-to-end form of
the repaired `kadiri_thm_3_1_q1` statement.

After this file the theorem `u8_kadiri_thm_3_1_q1_of_line_identifications` carries,
besides the analytic hypotheses of `kadiri_thm_3_1_q1` itself: the two line-value
identifications `U8RightLineInversionHypothesis` and
`U8LeftLineFunctionalEquationSplitHypothesis` (the Mellin-inversion and
functional-equation layers; per the convention ruling these are closed rightward,
with the rational terms contributing kernel values, and no leftward-vanishing
argument is used or assumed here), the vertical-line and band decay inputs for the
transform `Φ`, and the good-heights log-derivative bound (sub-unit U6a; now proved
in `KadiriU6aEndpointClose`, so the chain carries no `sorry`).
-/

open Complex MeasureTheory Filter Set Asymptotics
open ArithmeticFunction hiding log

namespace Kadiri

/-! ## Discharging the contour-pull identity -/

/-- The contour-pull identity of the U8 skeleton, from the good-heights contour pull. -/
theorem u8ContourPullIdentity_of_good_heights {Φ : ℂ → ℂ} {σL σR : ℝ} {T : ℕ → ℝ}
    (hσL2 : -2 < σL) (hσL0 : σL < 0) (hσR : 1 < σR)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (hT0 : ∀ k, 0 < T k)
    (hgood : ∀ k, horizontalSegmentZeroFree σL σR (T k))
    (hΦ_an : ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR → AnalyticAt ℂ (fun u => Φ (-u)) s)
    (hleft : MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σL : ℂ) + t * I) * (-(Φ (-((σL : ℂ) + t * I)))))
    (hright : MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σR : ℂ) + t * I) * (-(Φ (-((σR : ℂ) + t * I)))))
    (hbot : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
        -logDeriv riemannZeta ((x : ℂ) + (-(T k)) * I) *
          (-(Φ (-((x : ℂ) + (-(T k)) * I))))) Filter.atTop (nhds 0))
    (htop : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
        -logDeriv riemannZeta ((x : ℂ) + (T k) * I) *
          (-(Φ (-((x : ℂ) + (T k) * I))))) Filter.atTop (nhds 0)) :
    U8ContourPullIdentity Φ σL σR T := by
  have h := tendsto_zeroes_sum_of_good_heights hσL2 hσL0 hσR hT hT0 hgood hΦ_an
    hleft hright hbot htop
  unfold U8ContourPullIdentity u8ZeroWindow u8ContourPullSourceTarget u8ContourIntegrand
  exact h

/-! ## Discharging the zero-window limit -/

/-- The zero-window limit of the U8 skeleton, from the index-set bridge and the
window-exhaustion lemma; the summability input is exactly the `hΦ_sum` hypothesis
shape of `kadiri_thm_3_1_q1` at `g = Φ(-·)`. -/
theorem u8ZeroWindowLimit_of_summable {Φ : ℂ → ℂ} {σL σR : ℝ} {T : ℕ → ℝ}
    (hσL2 : -2 < σL) (hσL0 : σL < 0) (hσR : 1 < σR)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hsum : Summable (fun ρ : riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.univ : Set ℝ) =>
      Φ (-ρ.val) * (riemannZeta.order ρ.val : ℂ))) :
    U8ZeroWindowLimit Φ σL σR T := by
  have h2 := tendsto_zeroes_sum_window (I := Set.Ioo 0 1) (g := fun z => Φ (-z)) hT hsum
  have hbr : ∀ k : ℕ,
      riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.uIcc (-(T k)) (T k)) (fun ρ => Φ (-ρ))
        = u8ZeroWindow Φ σL σR T k := by
    intro k
    have hset := (zeroes_rect_band_eq_critical hσL2 hσL0 hσR (Set.uIcc (-(T k)) (T k))).symm
    exact congrArg
      (fun S : Set ℂ => ∑' ρ : S, (fun z => Φ (-z)) ρ.val * (riemannZeta.order ρ.val : ℂ))
      hset
  unfold U8ZeroWindowLimit
  exact h2.congr fun k => hbr k

/-! ## The end-to-end assembly -/

/-- The summability hypothesis of `kadiri_thm_3_1_q1` rewritten in the `u8Phi`
spelling (the two differ by `-(-ρ) = ρ` inside the Laplace kernel). -/
lemma summable_u8Phi_of_hΦ_sum {φ : ℝ → ℂ}
    (hΦ_sum : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (∫ y in (.Ioi (0 : ℝ)), φ y * exp (ρ.val * (y : ℂ)) ∂volume) *
        (riemannZeta.order ρ.val : ℂ))) :
    Summable (fun ρ : riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.univ : Set ℝ) =>
      u8Phi φ (-ρ.val) * (riemannZeta.order ρ.val : ℂ)) := by
  refine hΦ_sum.congr fun ρ => ?_
  unfold u8Phi
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  congr 1
  ring_nf

/-- End-to-end U8: the exact conclusion of the repaired `kadiri_thm_3_1_q1`, carrying
its own analytic hypotheses, the two line-value identifications (Mellin inversion on
the right line, functional-equation split on the left line), and the `Φ`-side decay
and analyticity inputs for the contour. The good-heights log-derivative bound enters
through `exists_logDerivBound_seq`, proved unconditionally in
`KadiriU6aEndpointClose` (sub-unit U6a, closed). No hypothesis constrains `Φ` left of the contour
band: the closure is rightward throughout, per the convention ruling. -/
theorem u8_kadiri_thm_3_1_q1_of_line_identifications {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
      =O[cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
      =O[cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (hΦ_sum : Summable (fun ρ :
      riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
        (∫ y in (.Ioi (0 : ℝ)), φ y * exp (ρ.val * (y : ℂ)) ∂volume) *
          (riemannZeta.order ρ.val : ℂ)))
    (hΓ_int : Integrable (fun t : ℝ =>
      ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y in (.Ioi (0 : ℝ)),
          φ y * exp (((1 / 2 : ℂ) + (t : ℂ) * I) * (y : ℂ)) ∂volume))
    {σL σR : ℝ} (hσL2 : -2 < σL) (hσL0 : σL < 0) (hσR : 1 < σR)
    (hΦ_an : ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR →
      AnalyticAt ℂ (fun u => u8Phi φ (-u)) s)
    (hleft : MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σL : ℂ) + t * I) * (-(u8Phi φ (-((σL : ℂ) + t * I)))))
    (hright : MeasureTheory.Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σR : ℂ) + t * I) * (-(u8Phi φ (-((σR : ℂ) + t * I)))))
    {CΦ Y₀ : ℝ} (hΦband : ∀ x ∈ Set.uIcc σL σR, ∀ t : ℝ, Y₀ ≤ |t| →
      ‖u8Phi φ (-((x : ℂ) + t * I))‖ ≤ CΦ / t ^ 2)
    (hRight : U8RightLineInversionHypothesis φ (u8Phi φ) σR)
    (hLeft : U8LeftLineFunctionalEquationSplitHypothesis φ (u8Phi φ) σL) :
    let Φ : ℂ → ℂ := fun z ↦ ∫ y in (.Ioi (0 : ℝ)), φ y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      Φ (-1) + Φ 0
        - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ Φ (-ρ))
        - φ 0 * ((Real.log Real.pi : ℝ) : ℂ)
        + ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-((1 / 2 : ℂ) + (t : ℂ) * I)) := by
  -- the good-heights sequence with the U6a bound
  obtain ⟨C, hC0, T, hT, hT3, hbound⟩ := exists_logDerivBound_seq σL σR
  have hT0 : ∀ k, 0 < T k := fun k => by linarith [hT3 k]
  have hgood : ∀ k, horizontalSegmentZeroFree σL σR (T k) := fun k => (hbound k).1
  -- the horizontal edges vanish
  have hbot0 := tendsto_horizontal_edge_zero_of_logDerivBound (Φ := u8Phi φ)
    (ε := fun k => -(T k)) hT hT3
    (fun k => by rw [abs_neg, abs_of_pos (hT0 k)]) hbound hΦband hC0.le
  have htop0 := tendsto_horizontal_edge_zero_of_logDerivBound (Φ := u8Phi φ)
    (ε := T) hT hT3 (fun k => abs_of_pos (hT0 k)) hbound hΦband hC0.le
  have hbot : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
      -logDeriv riemannZeta ((x : ℂ) + (-(T k)) * I) *
        (-(u8Phi φ (-((x : ℂ) + (-(T k)) * I))))) Filter.atTop (nhds 0) := by
    refine hbot0.congr fun k => ?_
    simp only [Complex.ofReal_neg]
  have htop : Filter.Tendsto (fun k : ℕ => ∫ x in σL..σR,
      -logDeriv riemannZeta ((x : ℂ) + (T k) * I) *
        (-(u8Phi φ (-((x : ℂ) + (T k) * I))))) Filter.atTop (nhds 0) := htop0
  -- the two contour-side U8 hypotheses
  have hContour : U8ContourPullIdentity (u8Phi φ) σL σR T :=
    u8ContourPullIdentity_of_good_heights hσL2 hσL0 hσR hT hT0 hgood hΦ_an
      hleft hright hbot htop
  have hZeroLimit : U8ZeroWindowLimit (u8Phi φ) σL σR T :=
    u8ZeroWindowLimit_of_summable hσL2 hσL0 hσR hT (summable_u8Phi_of_hΦ_sum hΦ_sum)
  exact u8_kadiri_thm_3_1_q1_exact_statement_skeleton hφ hb hφ_decay hφ'_decay
    hΦ_sum hΓ_int hContour hZeroLimit hRight hLeft

end Kadiri
