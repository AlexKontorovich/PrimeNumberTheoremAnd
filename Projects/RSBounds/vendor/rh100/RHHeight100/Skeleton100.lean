module

public import RHHeight.Skeleton

@[expose] public section

/-!
# The proof skeleton of hunt #137 at height 100

The height-100 analogue of `RHHeight/Skeleton.lean`. The target is `RHHeight.RHHeight100 =
RHUpToHeight 100`, whose window `0 < Im ρ ≤ 100` holds exactly twenty-nine zeros. The
pieces are `Prop`s here and nothing in this file assumes one is true:

* `GammaIncrement100`: an enclosure of `∫_3^100 μ`;
* `HorizontalLegs100`: `Re ζ > 0` on the legs `[1/2, 2] + 3i` and `[1/2, 2] + 100i`, with
  short intervals for the arguments of `ζ` at their left ends;
* `ExactArgument` and `LowHeight` are reused from `RHHeight.Skeleton` unchanged;
* `TwentyNineZerosOnLine`: twenty-nine distinct zeros `1/2 + i t_k` with `0 < t_k < 100`.

Proved here: `count_eq_twenty_nine_of` (the integer step: the enclosures put the count in
`(28, 30)`), `rhUpToHeight100_of_pieces`, `zeroCount100_of_pieces`.
-/

open Complex Set

namespace RHHeight100

open Zeta23 RHHeight

/-- Twenty-nine distinct zeros `1/2 + i t_k` of `ζ` with `0 < t_0 < ⋯ < t_28 < 100`. -/
def TwentyNineZerosOnLine : Prop :=
  ∃ ts : Fin 29 → ℝ, StrictMono ts ∧
    ∀ k, 0 < ts k ∧ ts k < 100 ∧ riemannZeta (1 / 2 + ts k * I) = 0

/-- **`gamma_increment` at height 100**: the Gamma side `∫_3^100 μ` lies in `[28.1, 29.7]`. -/
def GammaIncrement100 : Prop :=
  (281 / 10 : ℝ) ≤ ∫ t in (3 : ℝ)..100, mu t ∧ ∫ t in (3 : ℝ)..100, mu t ≤ 297 / 10

/-- **`horizontal_legs` at height 100**: `Re ζ > 0` on both horizontal legs and the
arguments of `ζ` at the two left ends lie in `[-1/5, 0]`. -/
def HorizontalLegs100 : Prop :=
  (∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 3 * I)).re) ∧
  (∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 100 * I)).re) ∧
  -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧ (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 ∧
  -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 100 * I)).arg ∧
    (riemannZeta (1 / 2 + 100 * I)).arg ≤ 0

/-- From the identity of `ExactArgument` and the two enclosures, the count of zeros with
`3 < Im ρ ≤ 100` is exactly `29`: the enclosures put it in `(28, 30)`. -/
theorem count_eq_twenty_nine_of (hΓ : GammaIncrement100) (hH : HorizontalLegs100)
    (hE : ExactArgument) : Ncount 3 100 = 29 := by
  obtain ⟨hleg₁, hleg₂, ha₁lo, ha₁hi, ha₂lo, ha₂hi⟩ := hH
  have h3 : ((3 : ℝ) : ℂ) = 3 := by norm_num
  have h100 : ((100 : ℝ) : ℂ) = 100 := by norm_num
  have hid := hE 3 100 (by norm_num) (by norm_num)
    (fun σ hσ => by simpa only [h3] using hleg₁ σ hσ)
    (fun σ hσ => by simpa only [h100] using hleg₂ σ hσ)
  rw [h3, h100] at hid
  obtain ⟨hGlo, hGhi⟩ := hΓ
  set a₁ := (riemannZeta (1 / 2 + 3 * I)).arg
  set a₂ := (riemannZeta (1 / 2 + 100 * I)).arg
  set G := ∫ t in (3 : ℝ)..100, mu t
  set D := (a₂ - a₁) / Real.pi with hD
  have hπ := Real.pi_pos
  have hDhi : D < 1 / 10 := by
    rw [hD, div_lt_iff₀ hπ]
    linarith [Real.pi_gt_three]
  have hDlo : -(1 / 10 : ℝ) < D := by
    rw [hD, lt_div_iff₀ hπ]
    linarith [Real.pi_gt_three]
  have hlt : (Ncount 3 100 : ℝ) < 30 := by rw [hid]; linarith
  have hgt : (28 : ℝ) < Ncount 3 100 := by rw [hid]; linarith
  have h1 : Ncount 3 100 < 30 := by exact_mod_cast hlt
  have h2 : 28 < Ncount 3 100 := by exact_mod_cast hgt
  omega

/-- **RH with simplicity to height 100, from the pieces and twenty-nine located zeros.** -/
theorem rhUpToHeight100_of_pieces (hΓ : GammaIncrement100) (hH : HorizontalLegs100)
    (hE : ExactArgument) (hL : LowHeight) (h29 : TwentyNineZerosOnLine) :
    RHUpToHeight 100 := by
  obtain ⟨ts, hmono, hts⟩ := h29
  have hN : Ncount 3 100 ≤ 29 := (count_eq_twenty_nine_of hΓ hH hE).le
  have hts' : ∀ k, (3 : ℝ) < ts k ∧ ts k ≤ 100 ∧ riemannZeta (1 / 2 + ts k * I) = 0 := by
    intro k
    obtain ⟨h0, h100, hz⟩ := hts k
    refine ⟨?_, by linarith, hz⟩
    by_contra hle
    exact hL (1 / 2 + ts k * I) hz (by norm_num) (by norm_num) (by simpa using h0)
      (by simpa using not_lt.mp hle)
  have hwin := on_line_and_simple_of_count ts hmono.injective hts' hN
  intro ρ h0 h1 h2 h3 h4
  by_cases hlow : ρ.im ≤ 3
  · exact (hL ρ h0 h1 h2 h3 hlow).elim
  · exact hwin ρ ⟨⟨h0, h1, h2⟩, not_le.mp hlow, h4⟩

/-- **Exactly twenty-nine zeros with `0 < Im ρ ≤ 100`**, from the same hypotheses. -/
theorem zeroCount100_of_pieces (hΓ : GammaIncrement100) (hH : HorizontalLegs100)
    (hE : ExactArgument) (hL : LowHeight) (h29 : TwentyNineZerosOnLine) :
    ZeroCountUpTo 100 29 := by
  classical
  obtain ⟨ts, hmono, hts⟩ := h29
  have hN : Ncount 3 100 ≤ 29 := (count_eq_twenty_nine_of hΓ hH hE).le
  have hgt3 : ∀ k, (3 : ℝ) < ts k := by
    intro k
    obtain ⟨h0, -, hz⟩ := hts k
    by_contra hle
    exact hL (1 / 2 + ts k * I) hz (by norm_num) (by norm_num) (by simpa using h0)
      (by simpa using not_lt.mp hle)
  set f : Fin 29 → ℂ := fun k => 1 / 2 + ts k * I with hf
  have hfinj : Function.Injective f := by
    intro j k hjk
    apply hmono.injective
    have := congrArg Complex.im hjk
    simpa [hf] using this
  set S := Finset.univ.image f
  have hcard : S.card = 29 := by
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
  have hS : ∀ ρ ∈ S, ρ ∈ zerosIn 3 100 := by
    intro ρ hρ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨h0, h100, hz⟩ := hts k
    have h3 := hgt3 k
    refine ⟨⟨hz, ?_, ?_⟩, ?_, ?_⟩
    · norm_num [hf]
    · norm_num [hf]
    · simpa [hf] using h3
    · simp only [hf, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
      norm_num
      linarith
  have hmem := mem_and_simple_of_Ncount_le S hS hcard hN
  have hset : stripZerosUpTo 100 = (S : Set ℂ) := by
    ext ρ
    constructor
    · rintro ⟨h0, h1, h2, h3, h4⟩
      by_cases hlow : ρ.im ≤ 3
      · exact (hL ρ h0 h1 h2 h3 hlow).elim
      · exact (hmem ρ ⟨⟨h0, h1, h2⟩, not_le.mp hlow, by linarith⟩).1
    · intro hρ
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
      obtain ⟨h0, h100, hz⟩ := hts k
      refine ⟨hz, ?_, ?_, ?_, ?_⟩
      · norm_num [hf]
      · norm_num [hf]
      · simpa [hf] using h0
      · simp only [hf, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
        norm_num
        linarith
  unfold ZeroCountUpTo
  rw [hset, Set.ncard_coe_finset, hcard]

end RHHeight100
