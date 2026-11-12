/- Copyright (c) 2026 Gershon Bialer. All rights reserved.
SPDX-License-Identifier: MIT -/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Exact prime-power endpoint reduction for a square-root psi bound

The integer-to-real normalization proof below is adapted from
`gersh/attested-compute@028462066f8537e3b90fcd83c32194f1cd526e46`,
`SparkInterval/TernaryGoldbach/PsiEndpointArithmetic.lean`,
`upperEndpointSafe_real_generic`. The scale and rational constant remain
parameters; allowing an arbitrary signed numerator lets the same proof
handle both sides of a gap. Original MIT notice is retained.

The new real-variable lemmas prove the endpoint reduction and specialize
it to Mathlib's actual Chebyshev psi using absence of prime-power jumps.
No sieve, logarithm enclosure, or finite numerical campaign is asserted here.
-/

namespace TernaryGoldbach.RSBounds.PsiSieveEndpointReduction

open Set

/-- The nonpositive branch is automatic; the positive branch uses exact
integer squaring. This is a proposition about supplied integer data. -/
def SignedEndpointSafe (point scaleN numerator denominator : ℕ)
    (difference : ℤ) : Prop :=
  difference ≤ 0 ∨ difference.natAbs ^ 2 * denominator ^ 2 ≤
    numerator ^ 2 * point * scaleN ^ 2

/-- Generalized form of the checked integer normalization in attested-compute.
Both post-jump upper errors and pre-jump lower deficits have this form. -/
theorem signedEndpointSafe_real_generic
    {point scaleN numerator denominator : ℕ} {difference : ℤ}
    (hscaleNat : 0 < scaleN) (hnumNat : 0 < numerator)
    (hdenNat : 0 < denominator)
    (hsafe : SignedEndpointSafe point scaleN numerator denominator difference) :
    (difference : ℝ) / scaleN ≤
      ((numerator : ℝ) / denominator) * Real.sqrt point := by
  change difference ≤ 0 ∨
      difference.natAbs ^ 2 * denominator ^ 2 ≤
        numerator ^ 2 * point * scaleN ^ 2 at hsafe
  have hscale : (0 : Real) < scaleN := by exact_mod_cast hscaleNat
  have hnum : (0 : Real) < numerator := by exact_mod_cast hnumNat
  have hden : (0 : Real) < denominator := by exact_mod_cast hdenNat
  by_cases hdNonpos : difference ≤ 0
  · have hdNonposReal : (difference : Real) ≤ 0 := by
      exact_mod_cast hdNonpos
    have hpoint : (difference : Real) / scaleN ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hdNonposReal hscale.le
    exact hpoint.trans (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  · have hsquare := hsafe.resolve_left hdNonpos
    have hdPos : 0 < difference := lt_of_not_ge hdNonpos
    have habsInt : (difference.natAbs : Int) = difference :=
      Int.natAbs_of_nonneg hdPos.le
    have habsReal : (difference.natAbs : Real) = (difference : Real) := by
      calc
        (difference.natAbs : Real) = ((difference.natAbs : Int) : Real) := by
          norm_num
        _ = (difference : Real) :=
          congrArg (fun value : Int ↦ (value : Real)) habsInt
    have hsquareReal :
        (difference.natAbs : Real) ^ 2 * (denominator : Real) ^ 2 ≤
          (numerator : Real) ^ 2 * (point : Real) * (scaleN : Real) ^ 2 := by
      have hcast :
          ((difference.natAbs ^ 2 * denominator ^ 2 : Nat) : Real) ≤
            ((numerator ^ 2 * point * scaleN ^ 2 : Nat) : Real) :=
        (Nat.cast_le (α := Real)).2 hsquare
      norm_num only [Nat.cast_mul, Nat.cast_pow] at hcast
      exact hcast
    rw [habsReal] at hsquareReal
    have hdiff : 0 ≤ (difference : Real) := by exact_mod_cast hdPos.le
    let normalized : Real :=
      (difference : Real) / scaleN * denominator / numerator
    have hnormalized : 0 ≤ normalized := by
      dsimp [normalized]
      positivity
    have hnormalizedSq : normalized ^ 2 ≤ (point : Real) := by
      have hdenominator :
          0 < (scaleN : Real) ^ 2 * (numerator : Real) ^ 2 :=
        mul_pos (sq_pos_of_pos hscale) (sq_pos_of_pos hnum)
      have hdiv :
          (difference : Real) ^ 2 * (denominator : Real) ^ 2 /
                ((scaleN : Real) ^ 2 * (numerator : Real) ^ 2) ≤
              (point : Real) := by
        apply (div_le_iff₀ hdenominator).2
        calc
          (difference : Real) ^ 2 * (denominator : Real) ^ 2 ≤
              (numerator : Real) ^ 2 * (point : Real) *
                (scaleN : Real) ^ 2 := hsquareReal
          _ = (point : Real) *
              ((scaleN : Real) ^ 2 * (numerator : Real) ^ 2) := by ring
      calc
        normalized ^ 2 =
            (difference : Real) ^ 2 * (denominator : Real) ^ 2 /
              ((scaleN : Real) ^ 2 * (numerator : Real) ^ 2) := by
                dsimp [normalized]
                field_simp
        _ ≤ (point : Real) := hdiv
    have hnormalizedLe : normalized ≤ Real.sqrt point :=
      (Real.le_sqrt hnormalized (by positivity)).2 hnormalizedSq
    calc
      (difference : Real) / scaleN =
          ((numerator : Real) / denominator) * normalized := by
            dsimp [normalized]
            field_simp
      _ ≤ ((numerator : Real) / denominator) * Real.sqrt point :=
        mul_le_mul_of_nonneg_left hnormalizedLe (by positivity)


/-- A post-jump upper guard for a rational upper enclosure of psi. -/
theorem upperEndpointSafe_real_generic
    {point upper scaleN numerator denominator : ℕ}
    (hscale : 0 < scaleN) (hnum : 0 < numerator) (hden : 0 < denominator)
    (hsafe : SignedEndpointSafe point scaleN numerator denominator
      ((upper : ℤ) - (point : ℤ) * scaleN)) :
    (upper : ℝ) / scaleN - point ≤
      ((numerator : ℝ) / denominator) * Real.sqrt point := by
  have h := signedEndpointSafe_real_generic hscale hnum hden hsafe
  have hd : (0 : ℝ) < scaleN := by exact_mod_cast hscale
  convert h using 1 <;> push_cast <;> field_simp [hd.ne'] <;> ring

/-- A pre-jump lower guard for a rational lower enclosure of the constant state. -/
theorem lowerEndpointSafe_real_generic
    {point lower scaleN numerator denominator : ℕ}
    (hscale : 0 < scaleN) (hnum : 0 < numerator) (hden : 0 < denominator)
    (hsafe : SignedEndpointSafe point scaleN numerator denominator
      ((point : ℤ) * scaleN - lower)) :
    (point : ℝ) - (lower : ℝ) / scaleN ≤
      ((numerator : ℝ) / denominator) * Real.sqrt point := by
  have h := signedEndpointSafe_real_generic hscale hnum hden hsafe
  have hd : (0 : ℝ) < scaleN := by exact_mod_cast hscale
  convert h using 1 <;> push_cast <;> field_simp [hd.ne'] <;> ring

/-- Normalized signed error decreases throughout a gap with nonnegative state. -/
theorem normalized_error_antitone {C : ℝ} (hC : 0 ≤ C) :
    AntitoneOn (fun x : ℝ => (C - x) / Real.sqrt x) (Ioi 0) := by
  intro a ha b hb hab
  have hs := Real.sqrt_le_sqrt hab
  have hd := div_le_div_of_nonneg_left hC (Real.sqrt_pos.mpr ha) hs
  simpa only [sub_div, Real.div_sqrt] using sub_le_sub hd hs

/-- A post-jump upper check at a and pre-jump lower check at b control
all intermediate real points, without evaluating another square root. -/
theorem constant_gap_abs_le {a b x C k : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) (hC : 0 ≤ C)
    (hupper : C - a ≤ k * Real.sqrt a)
    (hlower : b - C ≤ k * Real.sqrt b) :
    |C - x| ≤ k * Real.sqrt x := by
  have hx : 0 < x := ha.trans_le hax
  have hb : 0 < b := hx.trans_le hxb
  have hmono := normalized_error_antitone hC
  have hu : (C - a) / Real.sqrt a ≤ k :=
    (div_le_iff₀ (Real.sqrt_pos.mpr ha)).mpr hupper
  have hl : -k ≤ (C - b) / Real.sqrt b := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
    linarith
  apply abs_le.mpr
  constructor
  · have hh := (le_div_iff₀ (Real.sqrt_pos.mpr hx)).mp
      (hl.trans (hmono hx hb hxb))
    simpa only [neg_mul] using hh
  · exact (div_le_iff₀ (Real.sqrt_pos.mpr hx)).mp ((hmono ha hx hax).trans hu)

/-- Actual psi is constant when no prime-power event lies between the points. -/
theorem psi_eq_of_no_prime_powers {a x : ℝ} (hax : a ≤ x)
    (hgap : ∀ n : ℕ, a < (n : ℝ) → (n : ℝ) ≤ x → ¬ IsPrimePow n) :
    Chebyshev.psi x = Chebyshev.psi a := by
  unfold Chebyshev.psi
  symm
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hax))
  intro n hnx hna
  rcases Finset.mem_Ioc.mp hnx with ⟨hnpos, hnle⟩
  have han : a < (n : ℝ) := Nat.lt_of_floor_lt (Nat.lt_of_not_ge (by
    intro hn
    exact hna (Finset.mem_Ioc.mpr ⟨hnpos, hn⟩)))
  have hreal : (n : ℝ) ≤ x := (Nat.le_floor_iff' hnpos.ne').mp hnle
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (hgap n han hreal)

/-- Sufficient endpoint conditions for actual psi on an entire prime-power gap.
The right condition uses the pre-jump state psi(a), even at the right ordinate. -/
theorem psi_gap_abs_le {a b x k : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hxb : x < b)
    (hgap : ∀ n : ℕ, a < (n : ℝ) → (n : ℝ) < b → ¬ IsPrimePow n)
    (hupper : Chebyshev.psi a - a ≤ k * Real.sqrt a)
    (hlower : b - Chebyshev.psi a ≤ k * Real.sqrt b) :
    |Chebyshev.psi x - x| ≤ k * Real.sqrt x := by
  have he := psi_eq_of_no_prime_powers hax
    (fun n han hnx => hgap n han (hnx.trans_lt hxb))
  rw [he]
  exact constant_gap_abs_le ha hax hxb.le (Chebyshev.psi_nonneg a) hupper hlower

/-- The 4/5 certificate interface for one actual prime-power gap. The supplied
rational bounds concern psi at the left endpoint; the right guard is checked
at the next event's ordinate using this same pre-jump state. -/
theorem psi_gap_abs_le_four_fifths_of_guards
    {a b lower upper scaleN : ℕ} {x : ℝ}
    (ha : 0 < a) (hscale : 0 < scaleN)
    (hax : (a : ℝ) ≤ x) (hxb : x < (b : ℝ))
    (hgap : ∀ n : ℕ, (a : ℝ) < n → (n : ℝ) < b → ¬ IsPrimePow n)
    (henclosure : (lower : ℝ) / scaleN ≤ Chebyshev.psi a ∧
      Chebyshev.psi a ≤ (upper : ℝ) / scaleN)
    (hupper : SignedEndpointSafe a scaleN 4 5
      ((upper : ℤ) - (a : ℤ) * scaleN))
    (hlower : SignedEndpointSafe b scaleN 4 5
      ((b : ℤ) * scaleN - lower)) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  have hu := upperEndpointSafe_real_generic hscale (by norm_num : 0 < (4 : ℕ))
    (by norm_num : 0 < (5 : ℕ)) hupper
  have hl := lowerEndpointSafe_real_generic hscale (by norm_num : 0 < (4 : ℕ))
    (by norm_num : 0 < (5 : ℕ)) hlower
  norm_num only [Nat.cast_ofNat] at hu hl
  apply psi_gap_abs_le (by exact_mod_cast ha) hax hxb hgap
  · exact (sub_le_sub_right henclosure.2 (a : ℝ)).trans hu
  · exact (sub_le_sub_left henclosure.1 (b : ℝ)).trans hl

/-- For integer event endpoints, the pre-jump state at b is psi(b-1). -/
theorem psi_prejump_state {a b : ℕ} (hab : a < b)
    (hgap : ∀ n : ℕ, a < n → n < b → ¬ IsPrimePow n) :
    Chebyshev.psi ((b - 1 : ℕ) : ℝ) = Chebyshev.psi a := by
  have hpred : a ≤ b - 1 := by omega
  apply psi_eq_of_no_prime_powers (by exact_mod_cast hpred)
  intro n han hnb
  apply hgap n (by exact_mod_cast han)
  have hn : n ≤ b - 1 := by exact_mod_cast hnb
  omega

/-- A finite integer-gap coverage statement and the actual terminal check
control every real x in the interval. The cover is only required for integers
L ≤ n < R; its gap endpoints carry the post-upper and pre-lower checks. -/
theorem psi_interval_abs_le_of_gap_cover {L R : ℕ} {k : ℝ}
    (hL : 0 < L)
    (hterminal : |Chebyshev.psi R - R| ≤ k * Real.sqrt R)
    (hcover : ∀ n : ℕ, L ≤ n → n < R → ∃ a b : ℕ,
      0 < a ∧ a ≤ n ∧ n < b ∧
      (∀ m : ℕ, a < m → m < b → ¬ IsPrimePow m) ∧
      Chebyshev.psi a - a ≤ k * Real.sqrt a ∧
      (b : ℝ) - Chebyshev.psi a ≤ k * Real.sqrt b)
    {x : ℝ} (hLx : (L : ℝ) ≤ x) (hxR : x ≤ (R : ℝ)) :
    |Chebyshev.psi x - x| ≤ k * Real.sqrt x := by
  by_cases hx : x = (R : ℝ)
  · simpa only [hx] using hterminal
  have hxlt : x < (R : ℝ) := lt_of_le_of_ne hxR hx
  have hxpos : 0 < x := (by exact_mod_cast hL : (0 : ℝ) < L).trans_le hLx
  have hfloorL : L ≤ ⌊x⌋₊ := (Nat.le_floor_iff hxpos.le).mpr hLx
  have hfloorR : ⌊x⌋₊ < R := (Nat.floor_lt hxpos.le).mpr hxlt
  obtain ⟨a, b, ha, han, hnb, hgap, hu, hl⟩ := hcover ⌊x⌋₊ hfloorL hfloorR
  have hax : (a : ℝ) ≤ x :=
    (by exact_mod_cast han : (a : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hxpos.le)
  have hxb : x < (b : ℝ) := (Nat.floor_lt hxpos.le).mp hnb
  apply psi_gap_abs_le (by exact_mod_cast ha) hax hxb
  · intro m ham hmb
    exact hgap m (by exact_mod_cast ham) (by exact_mod_cast hmb)
  · exact hu
  · exact hl

end TernaryGoldbach.RSBounds.PsiSieveEndpointReduction
