import PrimeNumberTheoremAnd.CH2_part1

open Real MeasureTheory FourierTransform Chebyshev Asymptotics
open ArithmeticFunction hiding log
open Complex hiding log

namespace CH2

blueprint_comment /--
\subsection{Contour shifting}\label{ch2-contour-sec}

TODO: incorporate material from \cite[Section 5]{CH2}.
-/

/-- To state the contour integral results of CH2 cleanly we introduce the concept of a "LadderParams" which generates a
"ladder" as well as an "admissible contour" - a contour going up from `1` to `1 + I * δ` then backwards to `-∞ + I * δ`.
(We use `δ` for the contour height rather than the paper's `ε`, since `ε` already denotes the `±1` sign throughout the
extremal-approximant section above.) -/
class LadderParams where
  σ : ℕ → ℝ
  T : ℝ
  δ : ℝ
  h0 : σ 0 = 1
  hσ : ∀ n, σ n ≤ 1
  hlim : Filter.Tendsto σ Filter.atTop Filter.atBot
  hδ : δ ∈ Set.Ioo 0 (T/4)

lemma LadderParams.hT (l : LadderParams) : 0 < l.T := by
  have := l.hδ; grind

/-- The "ladder" on page 2 of CH2, where functions need to be bounded (and have no poles). -/
def LadderParams.ladder (l : LadderParams) : Set ℂ :=
  {z : ℂ | (∃ n, z.re = l.σ n ∧ |z.im| ≤ l.T) ∨ (z.re ≤ 1 ∧ |z.im| = l.T) }

/-- The set `L` from \cite[(5.1)]{CH2}: the union of the vertical ladder columns `σ n + i[-T, T]`
for `n ≥ 1` (excluding the `σ 0 = 1` column, which is part of `∂R`). This is the set on which
`G^\circ` and `G^\star` are assumed bounded with no poles in Lemma 5.1. -/
def LadderParams.L (l : LadderParams) : Set ℂ :=
  {z : ℂ | ∃ n, 1 ≤ n ∧ z.re = l.σ n ∧ |z.im| ≤ l.T}

/-- The "admissible contour", which we will fix to be of a simplified form. -/
def LadderParams.admissible_contour (l : LadderParams) : Set ℂ :=
  {z : ℂ | (z.re ≤ 1 ∧ z.im = l.δ) ∨ (z.re = 1 ∧ z.im ∈ Set.Icc 0 l.δ) }

/-- Describes the property that a function is bounded with no poles on a given set -/
def IsBoundedNoPolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop := ∃ M, ∀ z ∈ s, ‖f z‖ ≤ M ∧ 0 ≤ meromorphicOrderAt f z

/-- The main rectangle the ladder and contour lie in -/
def LadderParams.R (l : LadderParams) : Set ℂ := { z | z.re ≤ 1 ∧ |z.im| ≤ l.T }

/-- The boundary curve -/
def LadderParams.Rboundary (l : LadderParams) : Set ℂ :=
{ z | (z.re = 1 ∧ |z.im| ≤ l.T) ∨ (z.re ≤ 1 ∧ |z.im| = l.T) }

/-- An upper quarter of the rectangle -/
def LadderParams.R4 (l : LadderParams) : Set ℂ := { z | z.re ≤ 1 ∧ z.im ∈ Set.Icc 0 (l.T/4) }

/-- The closed subregion of `R` above the (simplified) contour `C`: the strip
`{re ≤ 1, δ ≤ im ≤ T}`. The paper's `R^+`. -/
def LadderParams.Rpos (l : LadderParams) : Set ℂ := {z | z.re ≤ 1 ∧ z.im ∈ Set.Icc l.δ l.T}

/-- The closed subregion of `R` below the conjugate contour `C̄`: the strip
`{re ≤ 1, -T ≤ im ≤ -δ}`. The paper's `\overline{R^+}`, the conjugate of `Rpos`. -/
def LadderParams.RposBar (l : LadderParams) : Set ℂ :=
  {z | z.re ≤ 1 ∧ z.im ∈ Set.Icc (-l.T) (-l.δ)}

/-- The closed subregion of `R` between the contour `C` and its conjugate `C̄`:
`{re ≤ 1, |im| ≤ δ}`. The paper's `R_C`. -/
def LadderParams.RC (l : LadderParams) : Set ℂ := {z | z.re ≤ 1 ∧ |z.im| ≤ l.δ}

/-- The open strip lying strictly between the (simplified) contour and the real axis: points with
`re < 1` and `0 < im < δ`. -/
def LadderParams.belowContour (l : LadderParams) : Set ℂ := {z | z.re < 1 ∧ z.im ∈ Set.Ioo 0 l.δ}

/-- Describes the property that `f` has no poles strictly between the contour and the real axis,
i.e. no poles in `belowContour`. Together with the paper's convention that real poles lie below the
contour, this expresses that every pole `ρ` with `ℑρ > 0` lies on or above the contour. -/
def LadderParams.HasGoodPoles (l : LadderParams) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ l.belowContour, 0 ≤ meromorphicOrderAt f z

/-! Basic geometry of the ladder, rectangle and contour: the inclusions and membership facts
that the contour-shifting results will rely on. -/

/-- The boundary of the rectangle lies inside the rectangle. -/
lemma LadderParams.Rboundary_subset_R (l : LadderParams) : l.Rboundary ⊆ l.R := by
  intro z hz
  simp only [LadderParams.Rboundary, LadderParams.R, Set.mem_setOf_eq] at hz ⊢
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1.le, h2⟩
  · exact ⟨h1, h2.le⟩

/-- The upper quarter-rectangle lies inside the rectangle. -/
lemma LadderParams.R4_subset_R (l : LadderParams) : l.R4 ⊆ l.R := by
  intro z hz
  simp only [LadderParams.R4, LadderParams.R, Set.mem_setOf_eq, Set.mem_Icc] at hz ⊢
  obtain ⟨hre, h0, h4⟩ := hz
  refine ⟨hre, ?_⟩
  rw [abs_of_nonneg h0]
  have := l.hT
  linarith

/-- The (simplified) admissible contour lies in the upper quarter-rectangle, since `δ < T/4`. -/
lemma LadderParams.admissible_contour_subset_R4 (l : LadderParams) :
    l.admissible_contour ⊆ l.R4 := by
  intro z hz
  simp only [LadderParams.admissible_contour, LadderParams.R4, Set.mem_setOf_eq, Set.mem_Icc] at hz ⊢
  obtain ⟨h0δ, hδT⟩ := l.hδ
  rcases hz with ⟨hre, him⟩ | ⟨hre, h0, hδ'⟩
  · exact ⟨hre, by rw [him]; exact h0δ.le, by rw [him]; exact hδT.le⟩
  · exact ⟨hre.le, h0, hδ'.trans hδT.le⟩

/-- The admissible contour lies inside the rectangle. -/
lemma LadderParams.admissible_contour_subset_R (l : LadderParams) :
    l.admissible_contour ⊆ l.R :=
  fun _ hz ↦ l.R4_subset_R (l.admissible_contour_subset_R4 hz)

/-- The boundary of the rectangle is part of the ladder (the right edge is the `σ 0 = 1` rung). -/
lemma LadderParams.Rboundary_subset_ladder (l : LadderParams) : l.Rboundary ⊆ l.ladder := by
  intro z hz
  simp only [LadderParams.Rboundary, LadderParams.ladder, Set.mem_setOf_eq] at hz ⊢
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨0, h1.trans l.h0.symm, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- The ladder columns `L` lie in the rectangle (uses `σ n ≤ 1`). -/
lemma LadderParams.L_subset_R (l : LadderParams) : l.L ⊆ l.R := by
  intro z hz
  simp only [LadderParams.L, LadderParams.R, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨n, _, hre, him⟩ := hz
  exact ⟨by rw [hre]; exact l.hσ n, him⟩

/-- The columns `L` are part of the page-2 ladder. -/
lemma LadderParams.L_subset_ladder (l : LadderParams) : l.L ⊆ l.ladder := by
  intro z hz
  simp only [LadderParams.L, LadderParams.ladder, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨n, _, hre, him⟩ := hz
  exact Or.inl ⟨n, hre, him⟩

/-- The base point `1` of the contour. -/
lemma LadderParams.one_mem_admissible_contour (l : LadderParams) :
    (1 : ℂ) ∈ l.admissible_contour := by
  simp only [LadderParams.admissible_contour, Set.mem_setOf_eq, Complex.one_re, Complex.one_im,
    Set.mem_Icc]
  exact Or.inr ⟨trivial, le_rfl, l.hδ.1.le⟩

/-- The corner `1 + iδ` of the contour. -/
lemma LadderParams.one_add_I_mul_delta_mem_admissible_contour (l : LadderParams) :
    (1 + Complex.I * (l.δ : ℂ)) ∈ l.admissible_contour := by
  have hre : (1 + Complex.I * (l.δ : ℂ)).re = 1 := by simp
  have him : (1 + Complex.I * (l.δ : ℂ)).im = l.δ := by simp
  simp only [LadderParams.admissible_contour, Set.mem_setOf_eq]
  exact Or.inl ⟨le_of_eq hre, him⟩

/-! The rectangle, ladder and boundary are symmetric about the real axis (closed under complex
conjugation), since their definitions only constrain `z.re` and `|z.im|`. This is what makes the
paper's conjugate contour `C̄` and the conjugate-pairing of poles available. -/

/-- The rectangle `R` is invariant under conjugation. -/
lemma LadderParams.conj_mem_R_iff (l : LadderParams) {z : ℂ} :
    (starRingEnd ℂ) z ∈ l.R ↔ z ∈ l.R := by
  simp only [LadderParams.R, Set.mem_setOf_eq, Complex.conj_re, Complex.conj_im, abs_neg]

/-- The ladder is invariant under conjugation. -/
lemma LadderParams.conj_mem_ladder_iff (l : LadderParams) {z : ℂ} :
    (starRingEnd ℂ) z ∈ l.ladder ↔ z ∈ l.ladder := by
  simp only [LadderParams.ladder, Set.mem_setOf_eq, Complex.conj_re, Complex.conj_im, abs_neg]

/-- The boundary `∂R` is invariant under conjugation. -/
lemma LadderParams.conj_mem_Rboundary_iff (l : LadderParams) {z : ℂ} :
    (starRingEnd ℂ) z ∈ l.Rboundary ↔ z ∈ l.Rboundary := by
  simp only [LadderParams.Rboundary, Set.mem_setOf_eq, Complex.conj_re, Complex.conj_im, abs_neg]

/-! The strip `belowContour` (where `HasGoodPoles` forbids poles) sits inside the upper
quarter-rectangle, and is disjoint from the contour itself. -/

/-- `belowContour` lies in the upper quarter-rectangle (since `δ < T/4`). -/
lemma LadderParams.belowContour_subset_R4 (l : LadderParams) : l.belowContour ⊆ l.R4 := by
  intro z hz
  simp only [LadderParams.belowContour, LadderParams.R4, Set.mem_setOf_eq, Set.mem_Ioo,
    Set.mem_Icc] at hz ⊢
  obtain ⟨hre, h0, hδ'⟩ := hz
  obtain ⟨-, hδT⟩ := l.hδ
  exact ⟨hre.le, h0.le, (hδ'.trans hδT).le⟩

/-- `belowContour` lies in the rectangle. -/
lemma LadderParams.belowContour_subset_R (l : LadderParams) : l.belowContour ⊆ l.R :=
  fun _ hz ↦ l.R4_subset_R (l.belowContour_subset_R4 hz)

/-- A point strictly below the contour does not lie on the contour. -/
lemma LadderParams.belowContour_disjoint_admissible_contour (l : LadderParams) :
    Disjoint l.belowContour l.admissible_contour := by
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [LadderParams.belowContour, LadderParams.admissible_contour, Set.mem_setOf_eq,
    Set.mem_Ioo, Set.mem_Icc] at hz hz'
  obtain ⟨hre, _, hδ'⟩ := hz
  rcases hz' with ⟨_, him⟩ | ⟨hre', _⟩
  · exact absurd him (ne_of_lt hδ')
  · exact absurd hre' (ne_of_lt hre)

/-! The three sub-regions of `R` partitioned by the contour `C` and its conjugate `C̄`:
`Rpos` (above `C`), `RposBar` (below `C̄`), and `RC` (between them). Inclusions into `R`,
conjugate symmetry, and how `belowContour` and the contour itself relate to `RC`. -/

/-- `Rpos` lies in the rectangle. -/
lemma LadderParams.Rpos_subset_R (l : LadderParams) : l.Rpos ⊆ l.R := by
  intro z hz
  simp only [LadderParams.Rpos, LadderParams.R, Set.mem_setOf_eq, Set.mem_Icc] at hz ⊢
  obtain ⟨hre, hδ, hT⟩ := hz
  refine ⟨hre, ?_⟩
  rw [abs_of_nonneg (l.hδ.1.le.trans hδ)]
  exact hT

/-- `RposBar` lies in the rectangle. -/
lemma LadderParams.RposBar_subset_R (l : LadderParams) : l.RposBar ⊆ l.R := by
  intro z hz
  simp only [LadderParams.RposBar, LadderParams.R, Set.mem_setOf_eq, Set.mem_Icc] at hz ⊢
  obtain ⟨hre, hT, hδ⟩ := hz
  refine ⟨hre, ?_⟩
  have hz_nonpos : z.im ≤ 0 := hδ.trans (neg_nonpos.mpr l.hδ.1.le)
  rw [abs_of_nonpos hz_nonpos]
  linarith

/-- `RC` lies in the rectangle. -/
lemma LadderParams.RC_subset_R (l : LadderParams) : l.RC ⊆ l.R := by
  intro z hz
  simp only [LadderParams.RC, LadderParams.R, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨hre, h⟩ := hz
  refine ⟨hre, ?_⟩
  have := l.hδ.2
  have := l.hT
  linarith

/-- `RC` is invariant under conjugation (the strip `|im| ≤ δ` is symmetric about the real axis). -/
lemma LadderParams.conj_mem_RC_iff (l : LadderParams) {z : ℂ} :
    (starRingEnd ℂ) z ∈ l.RC ↔ z ∈ l.RC := by
  simp only [LadderParams.RC, Set.mem_setOf_eq, Complex.conj_re, Complex.conj_im, abs_neg]

/-- Conjugation swaps `Rpos` and `RposBar`. -/
lemma LadderParams.conj_mem_Rpos_iff_mem_RposBar (l : LadderParams) {z : ℂ} :
    (starRingEnd ℂ) z ∈ l.Rpos ↔ z ∈ l.RposBar := by
  simp only [LadderParams.Rpos, LadderParams.RposBar, Set.mem_setOf_eq,
    Complex.conj_re, Complex.conj_im, Set.mem_Icc]
  constructor <;> rintro ⟨hre, h1, h2⟩ <;> exact ⟨hre, by linarith, by linarith⟩

/-- The open strip below the contour lies in the closed strip between `C` and `C̄`. -/
lemma LadderParams.belowContour_subset_RC (l : LadderParams) : l.belowContour ⊆ l.RC := by
  intro z hz
  simp only [LadderParams.belowContour, LadderParams.RC, Set.mem_setOf_eq, Set.mem_Ioo] at hz ⊢
  obtain ⟨hre, h0, hδ'⟩ := hz
  refine ⟨hre.le, ?_⟩
  rw [abs_of_nonneg h0.le]
  exact hδ'.le

/-- The (simplified) admissible contour sits on the upper boundary of `RC`. -/
lemma LadderParams.admissible_contour_subset_RC (l : LadderParams) :
    l.admissible_contour ⊆ l.RC := by
  intro z hz
  simp only [LadderParams.admissible_contour, LadderParams.RC, Set.mem_setOf_eq,
    Set.mem_Icc] at hz ⊢
  rcases hz with ⟨hre, him⟩ | ⟨hre, h0, hδ'⟩
  · refine ⟨hre, ?_⟩
    rw [him]
    exact (abs_of_nonneg l.hδ.1.le).le
  · refine ⟨hre.le, ?_⟩
    rw [abs_of_nonneg h0]
    exact hδ'

/-! ## Contour integrals for Lemma 5.1 (Stage 2)

Definitions of the line integrals appearing in the statement and proof of Lemma 5.1 of
\cite{CH2}, together with corresponding integrability predicates. The integrand is a generic
`F : ℂ → ℂ`; in applications it will typically be `s ↦ G s * x ^ s` or `s ↦ G⋆ s * x ^ s`.
The constant factors `1/(2πi)` and `1/π · Im` from Lemma 5.1 are *not* baked in — they appear
at call sites. -/

/-! ### Primitives: oriented segment and ray integrals -/

/-- Oriented line integral of `F` along the vertical segment from `c + i·a` to `c + i·b`
(parametrized `s = c + i t`, `t : a → b`, `ds = i dt`). Reversing `a, b` negates the integral. -/
noncomputable def intVSeg (c a b : ℝ) (F : ℂ → ℂ) : ℂ :=
  ∫ t in a..b, F (c + t * Complex.I) * Complex.I

/-- Oriented line integral of `F` along the horizontal segment from `a + i·h` to `b + i·h`
(parametrized `s = r + i h`, `r : a → b`, `ds = dr`). -/
noncomputable def intHSeg (h a b : ℝ) (F : ℂ → ℂ) : ℂ :=
  ∫ r in a..b, F (r + h * Complex.I)

/-- Line integral of `F` along the horizontal ray `(-∞, b] + i·h`, oriented left-to-right
(`s = r + i h`, `r ∈ (-∞, b]`, `ds = dr`). A contour traversing this ray rightward-to-`-∞`
carries a minus sign at the call site. -/
noncomputable def intHRay (h b : ℝ) (F : ℂ → ℂ) : ℂ :=
  ∫ r in Set.Iic b, F (r + h * Complex.I)

/-- `F` is integrable along the vertical segment from `c + i·a` to `c + i·b`. -/
def IntegrableOnVSeg (c a b : ℝ) (F : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun t : ℝ ↦ F (c + t * Complex.I)) volume a b

/-- `F` is integrable along the horizontal segment from `a + i·h` to `b + i·h`. -/
def IntegrableOnHSeg (h a b : ℝ) (F : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun r : ℝ ↦ F (r + h * Complex.I)) volume a b

/-- `F` is integrable along the horizontal ray `(-∞, b] + i·h`. -/
def IntegrableOnHRay (h b : ℝ) (F : ℂ → ℂ) : Prop :=
  IntegrableOn (fun r : ℝ ↦ F (r + h * Complex.I)) (Set.Iic b)

/-! ### The contours of Lemma 5.1, built from the primitives -/

/-- The oriented line integral of `F` along the vertical segment from `c - iT` to `c + iT`. Used
for the LHS of Lemma 5.1 (`c = 1`) and the ladder columns `c = σ n` in its proof. -/
noncomputable def LadderParams.intVerticalAt (l : LadderParams) (c : ℝ) (F : ℂ → ℂ) : ℂ :=
  intVSeg c (-l.T) l.T F

/-- `F` is integrable along the vertical segment from `c - iT` to `c + iT`. -/
def LadderParams.IntegrableOnVerticalAt (l : LadderParams) (c : ℝ) (F : ℂ → ℂ) : Prop :=
  IntegrableOnVSeg c (-l.T) l.T F

/-- The oriented line integral of `F` along `C∞`: the upper horizontal ray `-∞ + iT → 1 + iT`,
minus the lower ray `-∞ - iT → 1 - iT` (which the contour traverses `1 - iT → -∞ - iT`, hence the
minus sign). -/
noncomputable def LadderParams.intCinf (l : LadderParams) (F : ℂ → ℂ) : ℂ :=
  intHRay l.T 1 F - intHRay (-l.T) 1 F

/-- `F` is integrable on both horizontal rays comprising `C∞`. -/
def LadderParams.IntegrableOnCinf (l : LadderParams) (F : ℂ → ℂ) : Prop :=
  IntegrableOnHRay l.T 1 F ∧ IntegrableOnHRay (-l.T) 1 F

/-- The oriented line integral of `F` along the simplified admissible contour `C`: up the segment
`1 → 1 + iδ`, then along the horizontal ray `1 + iδ → -∞ + iδ` (traversed leftward, hence the
minus sign on the ray). -/
noncomputable def LadderParams.intC (l : LadderParams) (F : ℂ → ℂ) : ℂ :=
  intVSeg 1 0 l.δ F - intHRay l.δ 1 F

/-- `F` is integrable on both pieces (vertical segment and horizontal ray) of the contour `C`. -/
def LadderParams.IntegrableOnC (l : LadderParams) (F : ℂ → ℂ) : Prop :=
  IntegrableOnVSeg 1 0 l.δ F ∧ IntegrableOnHRay l.δ 1 F

/-! ### Truncated contours for the proof of Lemma 5.1

The proof of Lemma 5.1 of \cite{CH2} works at a finite truncation level `σ n` and takes `n → ∞`. -/

/-- The truncated contour `C_n^+` from the proof of Lemma 5.1 of \cite{CH2}: from `1`, follow the
contour `C` leftwards to `σ n + iδ` (up `1 → 1+iδ`, then left along `im = δ`), then up to
`σ n + iT`, then right to `1 + iT`. -/
noncomputable def LadderParams.intCnPlus (l : LadderParams) (n : ℕ) (F : ℂ → ℂ) : ℂ :=
  intVSeg 1 0 l.δ F + intHSeg l.δ 1 (l.σ n) F +
    intVSeg (l.σ n) l.δ l.T F + intHSeg l.T (l.σ n) 1 F

/-- `F` is integrable along each of the four segments comprising `C_n^+`. -/
def LadderParams.IntegrableOnCnPlus (l : LadderParams) (n : ℕ) (F : ℂ → ℂ) : Prop :=
  IntegrableOnVSeg 1 0 l.δ F ∧ IntegrableOnHSeg l.δ 1 (l.σ n) F ∧
    IntegrableOnVSeg (l.σ n) l.δ l.T F ∧ IntegrableOnHSeg l.T (l.σ n) 1 F

/-- The truncated contour `C_n^-` from the proof of Lemma 5.1 of \cite{CH2}: the conjugate of
`C_n^+` traversed backwards, i.e. from `1 - iT` left to `σ n - iT`, up to `σ n - iδ`, right to
`1 - iδ`, then up to `1`. -/
noncomputable def LadderParams.intCnMinus (l : LadderParams) (n : ℕ) (F : ℂ → ℂ) : ℂ :=
  intHSeg (-l.T) 1 (l.σ n) F + intVSeg (l.σ n) (-l.T) (-l.δ) F +
    intHSeg (-l.δ) (l.σ n) 1 F + intVSeg 1 (-l.δ) 0 F

/-- `F` is integrable along each of the four segments comprising `C_n^-`. -/
def LadderParams.IntegrableOnCnMinus (l : LadderParams) (n : ℕ) (F : ℂ → ℂ) : Prop :=
  IntegrableOnHSeg (-l.T) 1 (l.σ n) F ∧ IntegrableOnVSeg (l.σ n) (-l.T) (-l.δ) F ∧
    IntegrableOnHSeg (-l.δ) (l.σ n) 1 F ∧ IntegrableOnVSeg 1 (-l.δ) 0 F

/-- `C_{n,1}^+`: the part of `C_n^+` other than the top segment `σ n + iT → 1 + iT`, i.e.
`1 → 1+iδ → σ n+iδ → σ n+iT`. -/
noncomputable def LadderParams.intCn1Plus (l : LadderParams) (n : ℕ) (F : ℂ → ℂ) : ℂ :=
  intVSeg 1 0 l.δ F + intHSeg l.δ 1 (l.σ n) F + intVSeg (l.σ n) l.δ l.T F

/-- `F` is integrable along each segment of `C_{n,1}^+`. -/
def LadderParams.IntegrableOnCn1Plus (l : LadderParams) (n : ℕ) (F : ℂ → ℂ) : Prop :=
  IntegrableOnVSeg 1 0 l.δ F ∧ IntegrableOnHSeg l.δ 1 (l.σ n) F ∧ IntegrableOnVSeg (l.σ n) l.δ l.T F

/-- `C_{n,1}^-`: the part of `C_n^-` other than the bottom segment `1 - iT → σ n - iT`, i.e.
`σ n - iT → σ n - iδ → 1 - iδ → 1`. -/
noncomputable def LadderParams.intCn1Minus (l : LadderParams) (n : ℕ) (F : ℂ → ℂ) : ℂ :=
  intVSeg (l.σ n) (-l.T) (-l.δ) F + intHSeg (-l.δ) (l.σ n) 1 F + intVSeg 1 (-l.δ) 0 F

/-- `F` is integrable along each segment of `C_{n,1}^-`. -/
def LadderParams.IntegrableOnCn1Minus (l : LadderParams) (n : ℕ) (F : ℂ → ℂ) : Prop :=
  IntegrableOnVSeg (l.σ n) (-l.T) (-l.δ) F ∧ IntegrableOnHSeg (-l.δ) (l.σ n) 1 F ∧
    IntegrableOnVSeg 1 (-l.δ) 0 F

/-! ## Residues and sums of residues (Stage 3)

There is no general complex `residue` in Mathlib, so we define the simple-pole residue as a limit
(matching the convention of `Phi_circ.residue`/`Phi_star.residue`), and the sum of residues over a
region as a `tsum`. The `tsum` is robust to the (mathematically delicate) possibility of infinitely
many poles: points of analyticity contribute `0`, and when only finitely many poles lie in the
region the sum collapses to the finite sum of their residues. Summability — i.e. finiteness of the
pole set in the region — is the implicit hypothesis to supply when formalizing Lemma 5.1. -/

/-- **Placeholder definition — valid only for simple poles.** The residue of `f` at `z₀`, defined
as the simple-pole limit `lim_{z → z₀} (z - z₀) · f z` (matching the convention of
`Phi_circ.residue` / `Phi_star.residue`). At a point of analyticity this is `0` and at a simple
pole it is the usual residue, but at a higher-order or essential singularity the limit diverges
and this returns a junk value.

A general complex residue (and the residue theorem) is planned for Mathlib but not yet available,
so results stated in terms of this `residue` are likely **not provable in full generality** with
the current API. This is a deliberate stopgap, to be replaced with the robust notion once the
Mathlib residue-theorem API lands. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z ↦ (z - z₀) * f z)

/-- The sum of residues of `f` over a region `S`, as a `tsum` over `S`. Points of analyticity
contribute `0`, so this is effectively the sum over the poles of `f` in `S`; when finitely many
poles lie in `S` the `tsum` equals the finite sum of their residues, regardless of `|S|`. (With
infinitely many poles, summability must be assumed for the value to be meaningful.) -/
noncomputable def sumResiduesIn (f : ℂ → ℂ) (S : Set ℂ) : ℂ :=
  ∑' z : S, residue f z

/-- The conjugation-antisymmetry condition `g(s̄) = -\overline{g(s)}`. In Lemma 5.1 this is imposed
on the odd part `G⋆`; it is what makes the integrals over the contour `C` and its conjugate `C̄`
combine into the single `(1/π) ℑ ∫_C G⋆ x^s` term (the integrand `s ↦ G⋆ s * x^s` inherits the
condition since `x` is real). -/
def ConjAntisymm (g : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, g (starRingEnd ℂ s) = - starRingEnd ℂ (g s)

section ContourShifting

/- Shared context for Lemma 5.1 and its sub-lemmas: the ladder parameters `l`, the functions
`G = G◦ + sgn(ℑ·) G⋆`, and the reals `x₀ ≤ x`. The structural (`Prop`) hypotheses stay explicit
on each lemma. -/
variable {l : LadderParams} {G G_circ G_star : ℂ → ℂ} {x₀ x : ℝ}

@[blueprint
  "ch2-lemma-5-1-a"
  (title := "Contour shifting, upper half (CH2 Lemma 5.1, eq. 1)")
  (statement := /--
  For each $n$, shifting the upper half $1 \to 1 + iT$ of the central line leftwards to the
  truncated contour $C_n^+$ picks up the residues of $G$ in $R^+$ to the right of $\sigma_n$:
  $$ \frac{1}{2\pi i}\int_1^{1+iT} G(s) x^s\, ds = \frac{1}{2\pi i}\int_{C_n^+} G(s) x^s\, ds + \sum_{\rho \in R^+,\ \Re\rho > \sigma_n} \mathrm{Res}_{s=\rho} G(s) x^s. $$ -/)
  (proof := /-- The residue theorem on the region of $R^+$ between $[1, 1+iT]$ and $C_n^+$. -/)
  (latexEnv := "lemma")]
theorem lemma_5_1_a (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}.Finite) :
    (2 * (π : ℂ) * Complex.I)⁻¹ * intVSeg 1 0 l.T (fun s ↦ G s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCnPlus n (fun s ↦ G s * (x : ℂ) ^ s) +
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.Rpos ∩ {z | l.σ n < z.re}) := by
  sorry

@[blueprint
  "ch2-lemma-5-1-b"
  (title := "Contour shifting, lower half (CH2 Lemma 5.1, eq. 2)")
  (statement := /--
  For each $n$, shifting the lower half $1 - iT \to 1$ of the central line leftwards to the
  truncated contour $C_n^-$ picks up the residues of $G$ in $\overline{R^+}$ to the right of $\sigma_n$:
  $$ \frac{1}{2\pi i}\int_{1-iT}^{1} G(s) x^s\, ds = \frac{1}{2\pi i}\int_{C_n^-} G(s) x^s\, ds + \sum_{\rho \in \overline{R^+},\ \Re\rho > \sigma_n} \mathrm{Res}_{s=\rho} G(s) x^s. $$ -/)
  (proof := /-- The residue theorem on the region of $\overline{R^+}$ between $[1-iT, 1]$ and $C_n^-$. -/)
  (latexEnv := "lemma")]
theorem lemma_5_1_b (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}.Finite) :
    (2 * (π : ℂ) * Complex.I)⁻¹ * intVSeg 1 (-l.T) 0 (fun s ↦ G s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCnMinus n (fun s ↦ G s * (x : ℂ) ^ s) +
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.RposBar ∩ {z | l.σ n < z.re}) := by
  sorry

@[blueprint
  "ch2-lemma-5-1-c"
  (title := "$G^\\circ$ shift to the $\\sigma_n$ column (CH2 Lemma 5.1, eq. 3)")
  (statement := /--
  Shifting the $C_{n,1}^{\pm}$ parts of the truncated contours onto the line $\Re s = \sigma_n$
  replaces them by the $\sigma_n$ column, picking up the residues of $G^\circ$ in $R_C$ to the
  right of $\sigma_n$:
  $$ \frac{1}{2\pi i}\left(\int_{C_{n,1}^+} + \int_{C_{n,1}^-}\right) G^\circ(s) x^s\, ds = \frac{1}{2\pi i}\int_{\sigma_n - iT}^{\sigma_n + iT} G^\circ(s) x^s\, ds + \sum_{\rho \in R_C,\ \Re\rho > \sigma_n} \mathrm{Res}_{s=\rho} G^\circ(s) x^s. $$ -/)
  (proof := /-- The residue theorem on the region of $R_C$ between $C_{n,1}^+ \cup C_{n,1}^-$ and the $\sigma_n$ column. -/)
  (latexEnv := "lemma")]
theorem lemma_5_1_c (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}.Finite) :
    (2 * (π : ℂ) * Complex.I)⁻¹ *
        (l.intCn1Plus n (fun s ↦ G_circ s * (x : ℂ) ^ s) +
          l.intCn1Minus n (fun s ↦ G_circ s * (x : ℂ) ^ s)) =
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intVerticalAt (l.σ n) (fun s ↦ G_circ s * (x : ℂ) ^ s) +
      sumResiduesIn (fun s ↦ G_circ s * (x : ℂ) ^ s) (l.RC ∩ {z | l.σ n < z.re}) := by
  sorry

@[blueprint
  "ch2-lemma-5-1-d"
  (title := "$G^\\star$ reflection (CH2 Lemma 5.1, eq. 4)")
  (statement := /--
  Since $C_{n,1}^-$ is the conjugate of $C_{n,1}^+$ traversed backwards and $G^\star(\bar s) =
  -\overline{G^\star(s)}$, the two $G^\star$ contour integrals combine into a single imaginary part:
  $$ \int_{C_{n,1}^+} G^\star(s) x^s\, ds - \int_{C_{n,1}^-} G^\star(s) x^s\, ds = 2i\, \Im \int_{C_{n,1}^+} G^\star(s) x^s\, ds. $$ -/)
  (proof := /-- For the conjugation-antisymmetric integrand $G^\star x^s$, $\int_{C_{n,1}^-} = \overline{\int_{C_{n,1}^+}}$, and $z - \bar z = 2i\, \Im z$. -/)
  (latexEnv := "lemma")]
theorem lemma_5_1_d (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}.Finite) :
    l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s) -
        l.intCn1Minus n (fun s ↦ G_star s * (x : ℂ) ^ s) =
      2 * Complex.I * ((l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im : ℂ) := by
  sorry

@[blueprint
  "ch2-lemma-5-1-e"
  (title := "The $C_\\infty$ limit (CH2 Lemma 5.1, eq. 5)")
  (statement := /--
  As $n \to \infty$ (so $\sigma_n \to -\infty$), the top segment of $C_n^+$ together with the
  bottom segment of $C_n^-$ converge to the contour $C_\infty$:
  $$ \lim_{n\to\infty} \left( \int_{\sigma_n + iT}^{1 + iT} + \int_{1 - iT}^{\sigma_n - iT} \right) G(s) x^s\, ds = \int_{C_\infty} G(s) x^s\, ds. $$ -/)
  (proof := /-- As $\sigma_n \to -\infty$ the truncated horizontal segments exhaust the rays of $C_\infty$; uses boundedness of $G x_0^s$ on $\partial R$ and $x > x_0$. -/)
  (latexEnv := "lemma")]
theorem lemma_5_1_e
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}.Finite) :
    Filter.Tendsto
      (fun n ↦ intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) +
        intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s))
      Filter.atTop (nhds (l.intCinf (fun s ↦ G s * (x : ℂ) ^ s))) := by
  sorry

@[blueprint
  "ch2-lemma-5-1-f"
  (title := "The $\\sigma_n$ column vanishes (CH2 Lemma 5.1, eq. 6)")
  (statement := /--
  As $n \to \infty$ (so $\sigma_n \to -\infty$), the integral of $G^\circ x^s$ over the $\sigma_n$
  column tends to $0$:
  $$ \lim_{n\to\infty} \int_{\sigma_n - iT}^{\sigma_n + iT} G^\circ(s) x^s\, ds = 0. $$ -/)
  (proof := /-- The integrand is $O((x/x_0)^{\sigma_n})$ via boundedness of $G^\circ x_0^s$ on $L$, and $(x/x_0)^{\sigma_n} \to 0$ since $x > x_0 \geq 1$ and $\sigma_n \to -\infty$. -/)
  (latexEnv := "lemma")]
theorem lemma_5_1_f
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}.Finite) :
    Filter.Tendsto (fun n ↦ l.intVerticalAt (l.σ n) (fun s ↦ G_circ s * (x : ℂ) ^ s))
      Filter.atTop (nhds (0 : ℂ)) := by
  sorry

@[blueprint
  "ch2-lemma-5-1-g"
  (title := "Residue-sum exhaustion (CH2 Lemma 5.1, residue limit)")
  (statement := /--
  If $f$ has only finitely many poles in a region $S$, then the truncated residue sums over
  $S \cap \{\Re s > \sigma_n\}$ converge, as $n \to \infty$, to the full sum over $S$. (Indeed
  they are eventually equal to it, once $\sigma_n$ has dropped below the real part of every pole.) -/)
  (proof := /-- Since $\sigma_n \to -\infty$ and there are finitely many poles in $S$, for all
  large $n$ the set $\{\Re s > \sigma_n\}$ contains every pole of $f$ in $S$; the truncated sum is
  then constant and equals the full residue sum over $S$ (analytic points contribute $0$). -/)
  (latexEnv := "lemma")]
theorem lemma_5_1_g (f : ℂ → ℂ) (S : Set ℂ)
    (hfin : {z ∈ S | meromorphicOrderAt f z < 0}.Finite) :
    Filter.Tendsto (fun n ↦ sumResiduesIn f (S ∩ {z | l.σ n < z.re})) Filter.atTop
      (nhds (sumResiduesIn f S)) := by
  sorry

@[blueprint
  "ch2-lemma-5-1-h"
  (title := "$C_{n,1}^+ \\to C$ (CH2 Lemma 5.1, contour limit)")
  (statement := /--
  As $n \to \infty$ (so $\sigma_n \to -\infty$), the integral of $G^\star x^s$ over $C_{n,1}^+$
  converges to its integral over the full contour $C$:
  $$ \lim_{n\to\infty} \int_{C_{n,1}^+} G^\star(s) x^s\, ds = \int_C G^\star(s) x^s\, ds. $$ -/)
  (proof := /-- $C_{n,1}^+$ differs from $C$ (truncated at height $\delta$) only in its horizontal
  segment $1 + i\delta \to \sigma_n + i\delta$, which exhausts the ray $1 + i\delta \to -\infty + i\delta$, and its
  vertical segment $\sigma_n + i\delta \to \sigma_n + iT$, which vanishes --- both as in
  \ref{ch2-lemma-5-1-e}, \ref{ch2-lemma-5-1-f}, here at height $\delta$, using boundedness of
  $G^\star x_0^s$ on $L$ and on $C$. -/)
  (latexEnv := "lemma")]
theorem lemma_5_1_h
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}.Finite) :
    Filter.Tendsto (fun n ↦ l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)) Filter.atTop
      (nhds (l.intC (fun s ↦ G_star s * (x : ℂ) ^ s))) := by
  sorry

@[blueprint
  "ch2-lemma-5-1"
  (title := "Contour shifting (CH2 Lemma 5.1)")
  (statement := /--
  Let $G = G^\circ + \mathrm{sgn}(\Im s)\, G^\star$ with $G^\circ, G^\star$ meromorphic on
  $R = (-\infty,1] + i[-T,T]$, and suppose $G^\star(\bar s) = -\overline{G^\star(s)}$. Suppose for
  some $x_0 \geq 1$ that $G(s) x_0^s$ is bounded with no poles on $\partial R$, and both
  $G^\circ(s) x_0^s$ and $G^\star(s) x_0^s$ are bounded with no poles on the ladder $L$ and the
  contour $C$. Then for any $x > x_0$,
  $$ \frac{1}{2\pi i} \int_{1-iT}^{1+iT} G(s) x^s\, ds = \frac{1}{2\pi i} \int_{C_\infty} G(s) x^s\, ds + \frac{1}{\pi} \Im \int_C G^\star(s) x^s\, ds + \sum_{\rho \in R \setminus R_C} \mathrm{Res}_{s=\rho} G(s) x^s + \sum_{\rho \in R_C} \mathrm{Res}_{s=\rho} G^\circ(s) x^s, $$
  where the two residue sums run over the poles of $G$ (resp.\ $G^\circ$) in the indicated
  regions, which we assume to be finite. -/)
  (proof := /-- Assemble from the sub-lemmas. Split the central line into its upper half $[1,1+iT]$
  and lower half $[1-iT,1]$, and apply Lemmas \ref{ch2-lemma-5-1-a} and \ref{ch2-lemma-5-1-b} to
  rewrite each as the truncated contour $C_n^+$ (resp.\ $C_n^-$) plus the residues of $G$ over
  $R^+ \cap \{\Re s > \sigma_n\}$ (resp.\ $\overline{R^+} \cap \{\Re s > \sigma_n\}$). Split each
  $C_n^{\pm}$ into its horizontal $\Im s = \pm T$ segment and the remainder $C_{n,1}^{\pm}$. On
  $C_{n,1}^{\pm}$ substitute $G = G^\circ + \mathrm{sgn}(\Im s)\, G^\star$: by
  \ref{ch2-lemma-5-1-c} the $G^\circ$ part becomes the $\sigma_n$ column plus the residues of
  $G^\circ$ over $R_C \cap \{\Re s > \sigma_n\}$, and by \ref{ch2-lemma-5-1-d} the $G^\star$ part
  combines into $2i\, \Im \int_{C_{n,1}^+} G^\star x^s$. Now let $n \to \infty$: the
  $\Im s = \pm T$ segments converge to $C_\infty$ (\ref{ch2-lemma-5-1-e}); the $\sigma_n$ column
  vanishes (\ref{ch2-lemma-5-1-f}); $C_{n,1}^+ \to C$ (\ref{ch2-lemma-5-1-h}), so
  $\Im \int_{C_{n,1}^+} G^\star x^s \to \Im \int_C G^\star x^s$; and the truncated residue sums
  converge to the full sums (\ref{ch2-lemma-5-1-g}), with $R^+ \sqcup \overline{R^+} = R \setminus
  R_C$. Collecting terms, and using $\frac{1}{2\pi i} \cdot 2i = \frac{1}{\pi}$, yields the claim. -/)
  (latexEnv := "lemma")]
theorem lemma_5_1
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    -- finiteness of the pole sets in each region (our addition; the paper does not address the
    -- possibility of infinitely many poles):
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}.Finite) :
    (2 * (π : ℂ) * Complex.I)⁻¹ * l.intVerticalAt 1 (fun s ↦ G s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCinf (fun s ↦ G s * (x : ℂ) ^ s) +
      (↑(π⁻¹ * (l.intC (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ) +
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.R \ l.RC) +
      sumResiduesIn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.RC := by
  sorry

end ContourShifting

/-- The rescaling `z(s) = (s - 1)/(iT)` (CH2 §4–5), carrying the central line `1 + i[-T, T]`
onto `[-1, 1]`. -/
noncomputable def LadderParams.zOf (l : LadderParams) (s : ℂ) : ℂ := (s - 1) / (Complex.I * l.T)

/-- The combined Graham–Vaaler weight `Φ^ε_λ` (the paper's `Φ^±_λ`, with the sign `±` carried by
`ε`): `Φ^ε_λ(z) = Phi_circ |λ| ε (sgn λ · z) + sgn λ · sgn (Re z) · Phi_star |λ| ε (sgn λ · z)`. -/
noncomputable def Phi_lambda (lam ε : ℝ) (z : ℂ) : ℂ :=
  Phi_circ |lam| ε ((Real.sign lam : ℂ) * z) +
    (Real.sign lam : ℂ) * (Real.sign z.re : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * z)

/-- The conjugate-symmetry (Schwarz reflection) condition `F(s̄) = conj (F s)` assumed of `F` in
Proposition 5.2; it makes the derived odd part `G⋆` satisfy `ConjAntisymm`. -/
def ConjSymm (F : ℂ → ℂ) : Prop := ∀ s : ℂ, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)

section Proposition52

/- Shared context for Proposition 5.2 and its sub-lemmas: the ladder parameters `l`, the
meromorphic function `F`, the parameter `λ` (`lam`) and sign `ε`, and the reals `x₀ ≤ x`. The
structural (`Prop`) hypotheses stay explicit on each lemma. -/
variable {l : LadderParams} {F : ℂ → ℂ} {lam ε x₀ x : ℝ}

@[blueprint
  "ch2-prop-5-2-a"
  (title := "Proposition 5.2: reduction to Lemma 5.1")
  (statement := /--
  Under the hypotheses of \ref{ch2-prop-5-2}, with $G$, $G^\circ$, $G^\star$, $z(s)$ as there, the
  decomposition $G = G^\circ + \mathrm{sgn}(\Im s)\, G^\star$ holds (as $\mathrm{sgn}(\Re z(s)) =
  \mathrm{sgn}(\Im s)$, since $\Re z(s) = \Im s / T$ and $T > 0$), $G^\star$ is
  conjugation-antisymmetric, and the boundedness hypotheses of Lemma \ref{ch2-lemma-5-1} hold;
  hence Lemma \ref{ch2-lemma-5-1} gives
  $$ \frac{1}{2\pi i}\int_{1-iT}^{1+iT} G(s) x^s\, ds = \frac{1}{2\pi i}\int_{C_\infty} G(s) x^s\, ds + \frac{1}{\pi}\Im\int_C G^\star(s) x^s\, ds + \sum_{\rho \in R \setminus R_C}\mathrm{Res}_{s=\rho} G(s) x^s + \sum_{\rho \in R_C}\mathrm{Res}_{s=\rho} G^\circ(s) x^s. $$ -/)
  (proof := /-- Apply Lemma \ref{ch2-lemma-5-1}. The $G^\star$ reflection is the conjugation
  symmetry of $\Phi^\star$ together with $F(\bar s) = \overline{F(s)}$; boundedness follows from
  $\Phi^\circ$ bounded and $\Phi^\star = O(|z|)$ (CH2 Lemma 4.3). -/)
  (latexEnv := "lemma")]
theorem prop_5_2_a
    (hF_mero : MeromorphicOn F l.R)
    (hF_symm : ConjSymm F)
    (hlam : lam ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hx₀ : 1 ≤ x₀)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC |
        meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC |
        meromorphicOrderAt
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) z
          < 0}.Finite) :
    (2 * (π : ℂ) * Complex.I)⁻¹ *
        l.intVerticalAt 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ *
          l.intCinf (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) +
        (↑(π⁻¹ * (l.intC (fun s ↦ (Real.sign lam : ℂ) *
            Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)).im) : ℂ) +
        sumResiduesIn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) +
        sumResiduesIn
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.RC := by
  sorry

@[blueprint
  "ch2-prop-5-2-b"
  (title := "Proposition 5.2: bound on the $C_\\infty$ integral")
  (statement := /--
  On the rays of $C_\infty$, $z(r \pm iT) = \pm 1 + i\,\frac{1-r}{T}$, so
  $|\Phi^\varepsilon_\lambda(z(s))| \leq \frac{1-r}{T}$ (CH2 Lemma 4.3); substituting $t = 1 - r$,
  $$ \left\| \frac{1}{2\pi i}\int_{C_\infty} G(s) x^s\, ds \right\| \leq \frac{1}{2\pi} \cdot \frac{1}{T} \sum_{\xi = \pm 1} \int_0^\infty t\, |F(1 - t + i\xi T)|\, x^{1-t}\, dt. $$ -/)
  (proof := /-- $|\Phi^\varepsilon_\lambda(\pm 1 + ir')| \leq |r'|$ (CH2 Lemma 4.3), $|x^s| = x^{\Re s}$. -/)
  (latexEnv := "lemma")]
theorem prop_5_2_b
    (hF_mero : MeromorphicOn F l.R)
    (hF_symm : ConjSymm F)
    (hlam : lam ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hx₀ : 1 ≤ x₀)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC |
        meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC |
        meromorphicOrderAt
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) z
          < 0}.Finite) :
    ‖(2 * (π : ℂ) * Complex.I)⁻¹ *
        l.intCinf (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s)‖ ≤
      (1 / (2 * π)) * ((1 / l.T) *
        ((∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t + l.T * Complex.I)‖ * x ^ (1 - t)) +
          ∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t - l.T * Complex.I)‖ * x ^ (1 - t))) := by
  sorry

@[blueprint
  "ch2-prop-5-2-c"
  (title := "Proposition 5.2: bound on the contour integral")
  (statement := /--
  Since $G^\star = \mathrm{sgn}(\lambda)\, \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(\cdot)) F$ and $|\Im w| \leq |w|$,
  $$ \left\| \frac{1}{\pi}\Im\int_C G^\star(s) x^s\, ds \right\| \leq \frac{1}{2\pi} \cdot 2\left\| \int_C \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s) x^s\, ds \right\|. $$ -/)
  (proof := /-- `intC` is linear, $|\mathrm{sgn}(\lambda)| = 1$, and $|\Im w| \leq |w|$. -/)
  (latexEnv := "lemma")]
theorem prop_5_2_c
    (hF_mero : MeromorphicOn F l.R)
    (hF_symm : ConjSymm F)
    (hlam : lam ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hx₀ : 1 ≤ x₀)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC |
        meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC |
        meromorphicOrderAt
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) z
          < 0}.Finite) :
    ‖(↑(π⁻¹ * (l.intC (fun s ↦ (Real.sign lam : ℂ) *
          Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)).im) : ℂ)‖ ≤
      (1 / (2 * π)) *
        (2 * ‖l.intC (fun s ↦ Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)‖) := by
  sorry

@[blueprint
  "ch2-prop-5-2"
  (title := "Specialisation to the Graham--Vaaler weight (CH2 Proposition 5.2)")
  (statement := /--
  This specialises Lemma \ref{ch2-lemma-5-1} to the weight $\Phi^\varepsilon_\lambda$ built from the
  Graham--Vaaler approximants. \emph{The notation differs from \cite{CH2}:} the paper's sign $\pm$
  is here the parameter $\varepsilon \in \{+1, -1\}$ carried by $\Phi^\circ$, $\Phi^\star$ (the
  formalisation's \texttt{Phi\_circ}, \texttt{Phi\_star}), and the paper's contour height
  $\varepsilon$ is our $\delta$ (so $C$ is the \texttt{LadderParams} contour at height $\delta$).

  Let $F \colon \mathbb{C} \to \mathbb{C}$ be meromorphic on $R = (-\infty, 1] + i[-T, T]$ with
  $F(\bar s) = \overline{F(s)}$, and suppose for some $x_0 \geq 1$ that $F(s) x_0^s$ is bounded with
  no poles on $\partial R \cup C \cup L$. Fix $\lambda \neq 0$ and $\varepsilon \in \{+1, -1\}$,
  write $z(s) = \frac{s - 1}{iT}$, and set
  $$ \Phi^\varepsilon_\lambda(z) = \Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z) + \mathrm{sgn}(\lambda)\, \mathrm{sgn}(\Re z)\, \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z). $$
  This is the $G = G^\circ + \mathrm{sgn}(\Im s)\, G^\star$ of Lemma \ref{ch2-lemma-5-1}, with
  $G(s) = \Phi^\varepsilon_\lambda(z(s)) F(s)$,
  $G^\circ(s) = \Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s)$, and
  $G^\star(s) = \mathrm{sgn}(\lambda)\, \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s)$.
  Then, for any $x > x_0$,
  $$ \frac{1}{2\pi i} \int_{1-iT}^{1+iT} \Phi^\varepsilon_\lambda(z(s)) F(s) x^s\, ds = \sum_{\rho \in R \setminus R_C} \mathrm{Res}_{s=\rho} \Phi^\varepsilon_\lambda(z(s)) F(s) x^s + \sum_{\rho \in R_C} \mathrm{Res}_{s=\rho} \Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s) x^s + \frac{1}{2\pi} O^*(E), $$
  where the second sum is over the poles of $\Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s)$ in $R_C$ (these include the pole of $\Phi^\circ$ at $1 + \frac{\lambda T}{2\pi}$ when $\lambda < 0$), and
  $$ E = \frac{1}{T} \sum_{\xi = \pm 1} \int_0^\infty t\, |F(1 - t + i\xi T)|\, x^{1-t}\, dt + 2 \left| \int_C \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s) x^s\, ds \right|. $$
  Here $O^*(E)$ is rendered as $\| \cdot \| \leq E$. The first part of $E$ bounds the $C_\infty$
  integral of Lemma \ref{ch2-lemma-5-1} (via $|\Phi^\varepsilon_\lambda(\pm 1 + ir)| \leq |r|$ on
  the lines $\Re s = \pm 1$), and the second is its $\frac{1}{\pi} \Im \int_C G^\star$ term. -/)
  (proof := /-- By \ref{ch2-prop-5-2-a} the left side equals the $C_\infty$ integral, the
  $\frac{1}{\pi} \Im \int_C G^\star$ term, and the two residue sums; subtracting the residue sums
  (which match exactly) and applying the triangle inequality with \ref{ch2-prop-5-2-b} and
  \ref{ch2-prop-5-2-c} gives the $\frac{1}{2\pi} O^*(E)$ bound. -/)
  (latexEnv := "proposition")]
theorem prop_5_2
    (hF_mero : MeromorphicOn F l.R)
    (hF_symm : ConjSymm F)
    (hlam : lam ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hx₀ : 1 ≤ x₀)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC |
        meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) z < 0}.Finite)
    (hfin_circ : {z ∈ l.RC |
        meromorphicOrderAt
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) z
          < 0}.Finite) :
    ‖(2 * (π : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) -
        sumResiduesIn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) -
        sumResiduesIn
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.RC‖ ≤
      (1 / (2 * π)) *
        ((1 / l.T) *
            ((∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t + l.T * Complex.I)‖ * x ^ (1 - t)) +
              ∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t - l.T * Complex.I)‖ * x ^ (1 - t)) +
          2 * ‖l.intC (fun s ↦ Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)‖) := by
  have hLHS :
      (2 * (π : ℂ) * Complex.I)⁻¹ *
            l.intVerticalAt 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) -
          sumResiduesIn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) -
          sumResiduesIn
            (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.RC =
        (2 * (π : ℂ) * Complex.I)⁻¹ *
            l.intCinf (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) +
          (↑(π⁻¹ * (l.intC (fun s ↦ (Real.sign lam : ℂ) *
              Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)).im) : ℂ) := by
    rw [prop_5_2_a hF_mero hF_symm hlam hε hx₀ hF_bdd hx hfin hfin_circ]
    ring
  rw [hLHS]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add
    (prop_5_2_b hF_mero hF_symm hlam hε hx₀ hF_bdd hx hfin hfin_circ)
    (prop_5_2_c hF_mero hF_symm hlam hε hx₀ hF_bdd hx hfin hfin_circ)) ?_
  apply le_of_eq
  ring

end Proposition52

blueprint_comment /--
\subsection{The main theorem}\label{ch2-main-thm-sec}

TODO: incorporate material from \cite[Section 6]{CH2}.
-/

blueprint_comment /--
\subsection{Applications to psi}\label{ch2-psi-sec}

TODO: incorporate material from \cite[Section 7]{CH2} onwards.
-/



@[blueprint
  "CH2-cor-1-2-a"
  (title := "Corollary 1.2, part a")
  (statement := /--
  Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$|\psi(x) - x \cdot \frac{\pi}{T} \coth(\frac{\pi}{T})| \leq \pi T^{-1} \cdot x + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \sqrt{x},$$
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_2_a {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    |ψ x - x * π * T⁻¹ * (coth (π * T⁻¹)).re| ≤
      π * T⁻¹ * x + ((1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π))) * Real.sqrt x := by sorry

@[blueprint
  "CH2-cor-1-2-b"
  (title := "Corollary 1.2, part b")
  (statement := /--
  Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$\sum_{n \leq x} \frac{\Lambda(n)}{n} \leq \pi \sqrt{T}^{-1} + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \frac{1}{x},$$
where $\gamma = 0.577215...$ is Euler’s constant.
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_2_b {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n ≤
      π * Real.sqrt T⁻¹ + (1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π)) / x := by sorry

@[blueprint
  "CH2-cor-1-3-a"
  (title := "Corollary 1.3, part a")
  (statement := /--
For $x \geq 1$,
$$|\psi(x) - x| \leq \pi \cdot 3 \cdot 10^{-12} \cdot x + 113.67 \sqrt{x},$$
where $\psi(x)$ is the Chebyshev function.
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_3_a (x : ℝ) (hx : 1 ≤ x) :
    |ψ x - x| ≤ π * 3 * 10 ^ (-12 : ℝ) * x + 113.67 * Real.sqrt x := by sorry

@[blueprint
  "CH2-cor-1-3-b"
  (title := "Corollary 1.3, part b")
  (statement := /--
For $x \geq 1$,
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x - \gamma + O^*(\pi \cdot \sqrt{3} \cdot 10^{-12} + 113.67 / x).$$
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_3_b (x : ℝ) (hx : 1 ≤ x) : ∃ E,
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n =
      log x - eulerMascheroniConstant + E ∧ |E| ≤ π * Real.sqrt 3 * 10 ^ (-12 : ℝ) + 113.67 / x := by sorry

end CH2
