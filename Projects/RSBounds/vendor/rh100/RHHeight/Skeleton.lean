module

public import RHHeight.Statement
public import Zeta23.Statement.SeamClosed
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The proof skeleton of hunt #137 (`rh_height_lean`)

The target `RHHeight50` (`RHHeight/Statement.lean`) reduced, in Lean, to four named pieces
and the ten located zeros of hunt #133. Each piece is a `Prop` here; nothing in this file
assumes one is true. `rhHeight50_of_pieces` proves the target from the five hypotheses with
no `sorry`, so the work left is exactly to prove

* `GammaIncrement` (key `gamma_increment`): an enclosure of `∫_3^52 μ = (θ(52) - θ(3))/π`;
* `HorizontalLegs` (key `horizontal_legs`): `Re ζ > 0` on the two horizontal legs
  `[1/2, 2] + 3i` and `[1/2, 2] + 52i`, and the arguments of `ζ` at their left ends;
* `ExactArgument` (key `exact_argument`): under that positivity the folded argument
  principle of `zeta23` collapses to `N(T₁, T₂) = ∫ μ + (arg ζ(1/2 + iT₂) - arg ζ(1/2 + iT₁))/π`,
  exactly;
* `LowHeight` (key `low_height`): no zero with `0 < Im ρ ≤ 3`;

and to plug in `HardyTenZeros.ten_zeros_on_line_below_fifty`, whose type is
`TenZerosOnLine` below; `RHHeight/Assembly.lean` does that, so that the target there is
conditional on the four pieces alone.

The design, the numbers behind the constants `3`, `52`, `92/10`, `109/10`, `1/5`, `1/3`,
and the route to each piece are in `hunts/rh_height_lean/PLAN.md`. The constants were chosen
from floating-point measurements (mpmath), which prove nothing; the reduction below does not
depend on how they were found, only on the four `Prop`s holding as stated.

What is proved here (no `sorry`; each theorem is an implication from its stated hypotheses):

* `count_eq_ten_of`: the integer step, from the identity of `ExactArgument` and the two
  enclosures to `Ncount 3 52 = 10`;
* `on_line_and_simple_of_count`: if the window `(T₁, T₂]` carries `n` distinct zeros on the
  line and `Ncount T₁ T₂ ≤ n`, every zero in the window is one of them and is simple;
* `rhUpToHeight52_of_pieces`, `rhHeight50_of_pieces`: the assembly.
-/

open Complex Set

namespace RHHeight

open Zeta23

/-! ## The input from hunt #133 -/

/-- The statement of `HardyTenZeros.ten_zeros_on_line_below_fifty` (hunt #133, kernel-checked
there): ten distinct zeros `1/2 + i t_k` with `0 < t_0 < ⋯ < t_9 < 50`. -/
def TenZerosOnLine : Prop :=
  ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
    ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * I) = 0

/-! ## The four missing pieces -/

/-- **`gamma_increment`.** The Gamma side of the folded count at the planned heights
`T₁ = 3`, `T₂ = 52`: `∫_3^52 μ`, which equals `(θ(52) - θ(3))/π` with `θ` the
Riemann-Siegel theta function. Measured value `10.04261`; the planned proof (vendored
`digamma_stirling` with the exact `log |w|` and `1/(2w)` terms) gives `[9.427, 10.626]`,
inside the stated `[9.2, 10.9]` with room for cruder elementary bounds. -/
def GammaIncrement : Prop :=
  (92 / 10 : ℝ) ≤ ∫ t in (3 : ℝ)..52, mu t ∧ ∫ t in (3 : ℝ)..52, mu t ≤ 109 / 10

/-- **`horizontal_legs`.** `ζ` has positive real part on both horizontal legs of the half
contour, and its arguments at the two left ends lie in short intervals. Measured:
`min Re ζ` is `0.53` on the bottom leg and `1.0` on the top leg;
`arg ζ(1/2 + 3i) = -0.14703`, `arg ζ(1/2 + 52i) = -0.28090`. -/
def HorizontalLegs : Prop :=
  (∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 3 * I)).re) ∧
  (∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 52 * I)).re) ∧
  -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧ (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 ∧
  -(1 / 3 : ℝ) ≤ (riemannZeta (1 / 2 + 52 * I)).arg ∧ (riemannZeta (1 / 2 + 52 * I)).arg ≤ 0

/-- **`exact_argument`.** When `Re ζ > 0` on both horizontal legs (it is automatic on the
vertical leg `σ = 2`, vendored `re_riemannZeta_two_pos`), `log ζ` is a primitive of `ζ'/ζ`
along the whole half contour, the zeta half of `halfContour` telescopes to
`log ζ(1/2 + iT₂) - log ζ(1/2 + iT₁)`, and the folded argument principle
(`N_eq_halfContour_completedZeta`, `halfContour_completedZeta_split`, `gamma_side`) becomes
an exact identity. Positivity on a leg also makes its height a good height (by the
reflection `ρ ↦ 1 - conj ρ` for `Re ρ < 1/2`), so no `GoodHeight` hypothesis appears. -/
def ExactArgument : Prop :=
  ∀ T₁ T₂ : ℝ, 1 ≤ T₁ → T₁ < T₂ →
    (∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₁ * I)).re) →
    (∀ σ ∈ Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₂ * I)).re) →
    (Ncount T₁ T₂ : ℝ) = (∫ t in T₁..T₂, mu t) +
      ((riemannZeta (1 / 2 + T₂ * I)).arg - (riemannZeta (1 / 2 + T₁ * I)).arg) / Real.pi

/-- **`low_height`.** No zero of `ζ` in the strip with `0 < Im ρ ≤ 3`. Planned proof:
hunt #132's representation `zeta_em4` at `N = 1` gives
`ζ(s) = (s+2)(s+3)/(12(s-1)) - E(s)` with `‖E(s)‖ ≤ ‖s(s+1)(s+2)(s+3)‖ (1 + 1/(σ+3))/720`,
and the remainder is below the main term on `(0,1) × (0,3]` (measured ratio at most `0.713`). -/
def LowHeight : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 3 → False

/-! ## The integer step -/

/-- From the identity of `exact_argument` and the two enclosures, the count of zeros with
`3 < Im ρ ≤ 52` is exactly `10`: the stated enclosures put it in `(9.09, 11)`, which holds
one integer. -/
theorem count_eq_ten_of (hΓ : GammaIncrement) (hH : HorizontalLegs) (hE : ExactArgument) :
    Ncount 3 52 = 10 := by
  obtain ⟨hleg₁, hleg₂, ha₁lo, ha₁hi, ha₂lo, ha₂hi⟩ := hH
  have h3 : ((3 : ℝ) : ℂ) = 3 := by norm_num
  have h52 : ((52 : ℝ) : ℂ) = 52 := by norm_num
  have hid := hE 3 52 (by norm_num) (by norm_num)
    (fun σ hσ => by simpa only [h3] using hleg₁ σ hσ)
    (fun σ hσ => by simpa only [h52] using hleg₂ σ hσ)
  rw [h3, h52] at hid
  obtain ⟨hGlo, hGhi⟩ := hΓ
  set a₁ := (riemannZeta (1 / 2 + 3 * I)).arg
  set a₂ := (riemannZeta (1 / 2 + 52 * I)).arg
  set G := ∫ t in (3 : ℝ)..52, mu t
  set D := (a₂ - a₁) / Real.pi with hD
  have hπ := Real.pi_pos
  have hDhi : D < 1 / 10 := by
    rw [hD, div_lt_iff₀ hπ]
    linarith [Real.pi_gt_three]
  have hDlo : -(11 / 100 : ℝ) < D := by
    rw [hD, lt_div_iff₀ hπ]
    linarith [Real.pi_gt_d2]
  have hlt : (Ncount 3 52 : ℝ) < 11 := by rw [hid]; linarith
  have hgt : (9 : ℝ) < Ncount 3 52 := by rw [hid]; linarith
  have h1 : Ncount 3 52 < 11 := by exact_mod_cast hlt
  have h2 : 9 < Ncount 3 52 := by exact_mod_cast hgt
  omega

/-! ## From a count to "on the line and simple" -/

/-- **The counting step.** If `S` is a set of `n` zeros in the window `(T₁, T₂]` and the
multiplicity-weighted count `Ncount T₁ T₂` is at most `n`, then every zero in the window
lies in `S` and is simple. Uses only `zeta23`'s seam facts: the window is finite
(`zerosIn_finite`) and every nontrivial zero has multiplicity at least one
(`zetaSeam.one_le_mult`). -/
theorem mem_and_simple_of_Ncount_le {T₁ T₂ : ℝ} {n : ℕ} (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zerosIn T₁ T₂) (hcard : S.card = n) (hN : Ncount T₁ T₂ ≤ n) :
    ∀ ρ ∈ zerosIn T₁ T₂, ρ ∈ S ∧ zeroMult ρ = 1 := by
  classical
  have hfin := zerosIn_finite T₁ T₂
  set F := hfin.toFinset with hF
  have hSF : S ⊆ F := fun ρ hρ => hfin.mem_toFinset.mpr (hS ρ hρ)
  have hsum : Ncount T₁ T₂ = ∑ ρ ∈ F, zeroMult ρ := by
    unfold Ncount
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hone : ∀ ρ ∈ F, 1 ≤ zeroMult ρ := fun ρ hρ =>
    zetaSeam.one_le_mult ρ (hfin.mem_toFinset.mp hρ).1
  have hsplit := Finset.sum_sdiff (f := zeroMult) hSF
  have hS1 : S.card ≤ ∑ ρ ∈ S, zeroMult ρ := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun ρ hρ => hone ρ (hSF hρ)
  have hR1 : (F \ S).card ≤ ∑ ρ ∈ F \ S, zeroMult ρ := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun ρ hρ => hone ρ (Finset.sdiff_subset hρ)
  have hRe : F \ S = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  have hSeq : ∑ ρ ∈ S, zeroMult ρ = ∑ ρ ∈ S, 1 := by
    rw [← Finset.card_eq_sum_ones]
    omega
  have heach := (Finset.sum_eq_sum_iff_of_le
    (fun ρ hρ => hone ρ (hSF hρ) : ∀ ρ ∈ S, 1 ≤ zeroMult ρ)).mp hSeq.symm
  intro ρ hρ
  have hρF : ρ ∈ F := hfin.mem_toFinset.mpr hρ
  have hρS : ρ ∈ S := by
    by_contra hnot
    have : ρ ∈ F \ S := Finset.mem_sdiff.mpr ⟨hρF, hnot⟩
    rw [hRe] at this
    exact Finset.notMem_empty ρ this
  exact ⟨hρS, (heach ρ hρS).symm⟩

/-- **The counting step for zeros on the line.** `n` distinct ordinates `T₁ < t_k ≤ T₂` of
zeros `1/2 + i t_k`, and `Ncount T₁ T₂ ≤ n`: every zero in the window is on the line and
simple. -/
theorem on_line_and_simple_of_count {T₁ T₂ : ℝ} {n : ℕ} (ts : Fin n → ℝ)
    (hinj : Function.Injective ts)
    (hts : ∀ k, T₁ < ts k ∧ ts k ≤ T₂ ∧ riemannZeta (1 / 2 + ts k * I) = 0)
    (hN : Ncount T₁ T₂ ≤ n) :
    ∀ ρ ∈ zerosIn T₁ T₂, ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1 := by
  classical
  set f : Fin n → ℂ := fun k => 1 / 2 + ts k * I with hf
  have hfinj : Function.Injective f := by
    intro j k hjk
    apply hinj
    have := congrArg Complex.im hjk
    simpa [hf] using this
  set S := Finset.univ.image f
  have hcard : S.card = n := by
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
  have hS : ∀ ρ ∈ S, ρ ∈ zerosIn T₁ T₂ := by
    intro ρ hρ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨h1, h2, h3⟩ := hts k
    refine ⟨⟨h3, ?_, ?_⟩, ?_, ?_⟩
    · norm_num [hf]
    · norm_num [hf]
    · simpa [hf] using h1
    · simpa [hf] using h2
  intro ρ hρ
  obtain ⟨hρS, hmult⟩ := mem_and_simple_of_Ncount_le S hS hcard hN ρ hρ
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hρS
  refine ⟨by simp [hf], ?_⟩
  exact (toNat_analyticOrderAt_eq_one_iff _).mp hmult

/-! ## The assembly -/

/-- **RH with simplicity to height 52, and exactly ten zeros there, from the four pieces and
hunt #133's ten zeros.** -/
theorem rhUpToHeight52_of_pieces (hΓ : GammaIncrement) (hH : HorizontalLegs)
    (hE : ExactArgument) (hL : LowHeight) (h10 : TenZerosOnLine) :
    RHUpToHeight 52 := by
  obtain ⟨ts, hmono, hts⟩ := h10
  have hN : Ncount 3 52 ≤ 10 := (count_eq_ten_of hΓ hH hE).le
  have hts' : ∀ k, (3 : ℝ) < ts k ∧ ts k ≤ 52 ∧ riemannZeta (1 / 2 + ts k * I) = 0 := by
    intro k
    obtain ⟨h0, h50, hz⟩ := hts k
    refine ⟨?_, by linarith, hz⟩
    by_contra hle
    exact hL (1 / 2 + ts k * I) hz (by norm_num) (by norm_num) (by simpa using h0)
      (by simpa using not_lt.mp hle)
  have hwin := on_line_and_simple_of_count ts hmono.injective hts' hN
  intro ρ h0 h1 h2 h3 h4
  by_cases hlow : ρ.im ≤ 3
  · exact (hL ρ h0 h1 h2 h3 hlow).elim
  · exact hwin ρ ⟨⟨h0, h1, h2⟩, not_le.mp hlow, h4⟩

/-- **The target of hunt #137 at `T = 50`, from the four pieces and hunt #133.** -/
theorem rhHeight50_of_pieces (hΓ : GammaIncrement) (hH : HorizontalLegs)
    (hE : ExactArgument) (hL : LowHeight) (h10 : TenZerosOnLine) :
    RHHeight50 :=
  RHUpToHeight.mono (by norm_num) (rhUpToHeight52_of_pieces hΓ hH hE hL h10)

/-- **Exactly ten zeros with `0 < Im ρ ≤ 50`**, from the same hypotheses: the window holds
the ten zeros of hunt #133 and nothing else. -/
theorem zeroCount50_of_pieces (hΓ : GammaIncrement) (hH : HorizontalLegs)
    (hE : ExactArgument) (hL : LowHeight) (h10 : TenZerosOnLine) :
    ZeroCountUpTo 50 10 := by
  classical
  obtain ⟨ts, hmono, hts⟩ := h10
  have hN : Ncount 3 52 ≤ 10 := (count_eq_ten_of hΓ hH hE).le
  have hgt3 : ∀ k, (3 : ℝ) < ts k := by
    intro k
    obtain ⟨h0, -, hz⟩ := hts k
    by_contra hle
    exact hL (1 / 2 + ts k * I) hz (by norm_num) (by norm_num) (by simpa using h0)
      (by simpa using not_lt.mp hle)
  set f : Fin 10 → ℂ := fun k => 1 / 2 + ts k * I with hf
  have hfinj : Function.Injective f := by
    intro j k hjk
    apply hmono.injective
    have := congrArg Complex.im hjk
    simpa [hf] using this
  set S := Finset.univ.image f
  have hcard : S.card = 10 := by
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
  have hS : ∀ ρ ∈ S, ρ ∈ zerosIn 3 52 := by
    intro ρ hρ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨h0, h50, hz⟩ := hts k
    have h3 := hgt3 k
    refine ⟨⟨hz, ?_, ?_⟩, ?_, ?_⟩
    · norm_num [hf]
    · norm_num [hf]
    · simpa [hf] using h3
    · simp only [hf, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
      norm_num
      linarith
  have hmem := mem_and_simple_of_Ncount_le S hS hcard hN
  have hset : stripZerosUpTo 50 = (S : Set ℂ) := by
    ext ρ
    constructor
    · rintro ⟨h0, h1, h2, h3, h4⟩
      by_cases hlow : ρ.im ≤ 3
      · exact (hL ρ h0 h1 h2 h3 hlow).elim
      · exact (hmem ρ ⟨⟨h0, h1, h2⟩, not_le.mp hlow, by linarith⟩).1
    · intro hρ
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
      obtain ⟨h0, h50, hz⟩ := hts k
      refine ⟨hz, ?_, ?_, ?_, ?_⟩
      · norm_num [hf]
      · norm_num [hf]
      · simpa [hf] using h0
      · simp only [hf, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
        norm_num
        linarith
  unfold ZeroCountUpTo
  rw [hset, Set.ncard_coe_finset, hcard]

end RHHeight
