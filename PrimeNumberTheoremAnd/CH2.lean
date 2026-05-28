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
  fun _ hz => l.R4_subset_R (l.admissible_contour_subset_R4 hz)

/-- The boundary of the rectangle is part of the ladder (the right edge is the `σ 0 = 1` rung). -/
lemma LadderParams.Rboundary_subset_ladder (l : LadderParams) : l.Rboundary ⊆ l.ladder := by
  intro z hz
  simp only [LadderParams.Rboundary, LadderParams.ladder, Set.mem_setOf_eq] at hz ⊢
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨0, h1.trans l.h0.symm, h2⟩
  · exact Or.inr ⟨h1, h2⟩

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
  fun _ hz => l.R4_subset_R (l.belowContour_subset_R4 hz)

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

/-- The oriented line integral of `F` along the vertical segment from `c - iT` to `c + iT`,
parametrized as `s = c + it`, `t ∈ [-T, T]`, `ds = i dt`. Used for the LHS of Lemma 5.1
(`c = 1`) and for the ladder columns `c = σ n` in its proof. -/
noncomputable def LadderParams.intVerticalAt (l : LadderParams) (c : ℝ) (F : ℂ → ℂ) : ℂ :=
  ∫ t in Set.Icc (-l.T) l.T, F (c + t * Complex.I) * Complex.I

/-- `F` is integrable along the vertical segment from `c - iT` to `c + iT`. -/
def LadderParams.IntegrableOnVerticalAt (l : LadderParams) (c : ℝ) (F : ℂ → ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => F (c + t * Complex.I)) (Set.Icc (-l.T) l.T)

/-- The oriented line integral of `F` along `C∞`: the upper horizontal ray from `-∞ + iT` to
`1 + iT` (parametrized `s = r + iT`, `r ∈ (-∞, 1]` increasing, orientation matches), plus the
lower horizontal ray from `1 - iT` to `-∞ - iT` (parametrized similarly, orientation reversed,
hence the minus sign). -/
noncomputable def LadderParams.intCinf (l : LadderParams) (F : ℂ → ℂ) : ℂ :=
  (∫ r in Set.Iic (1:ℝ), F (r + l.T * Complex.I)) -
    (∫ r in Set.Iic (1:ℝ), F (r - l.T * Complex.I))

/-- `F` is integrable on both horizontal rays comprising `C∞`. -/
def LadderParams.IntegrableOnCinf (l : LadderParams) (F : ℂ → ℂ) : Prop :=
  IntegrableOn (fun r : ℝ => F (r + l.T * Complex.I)) (Set.Iic 1) ∧
  IntegrableOn (fun r : ℝ => F (r - l.T * Complex.I)) (Set.Iic 1)

/-- The oriented line integral of `F` along the simplified admissible contour `C`: vertically
from `1` to `1 + iδ` (parametrized `s = 1 + it`, `t ∈ [0, δ]`, `ds = i dt`), then horizontally
from `1 + iδ` to `-∞ + iδ` (parametrized `s = r + iδ`, `r ∈ (-∞, 1]` increasing, orientation
reversed, hence the minus sign on the horizontal piece). -/
noncomputable def LadderParams.intC (l : LadderParams) (F : ℂ → ℂ) : ℂ :=
  (∫ t in Set.Icc (0:ℝ) l.δ, F (1 + t * Complex.I) * Complex.I) -
    (∫ r in Set.Iic (1:ℝ), F (r + l.δ * Complex.I))

/-- `F` is integrable on both pieces (vertical and horizontal) of the contour `C`. -/
def LadderParams.IntegrableOnC (l : LadderParams) (F : ℂ → ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => F (1 + t * Complex.I)) (Set.Icc 0 l.δ) ∧
  IntegrableOn (fun r : ℝ => F (r + l.δ * Complex.I)) (Set.Iic 1)

/-! ## Residues and sums of residues (Stage 3)

There is no general complex `residue` in Mathlib, so we define the simple-pole residue as a limit
(matching the convention of `Phi_circ.residue`/`Phi_star.residue`), and the sum of residues over a
region as a `tsum`. The `tsum` is robust to the (mathematically delicate) possibility of infinitely
many poles: points of analyticity contribute `0`, and when only finitely many poles lie in the
region the sum collapses to the finite sum of their residues. Summability — i.e. finiteness of the
pole set in the region — is the implicit hypothesis to supply when formalizing Lemma 5.1. -/

/-- The residue of `f` at `z₀`, defined as the simple-pole limit `lim_{z → z₀} (z - z₀) · f z`.
At a point of analyticity this is `0`; for a simple pole it is the usual residue; at higher-order
or essential singularities the limit diverges and this returns a junk value (acceptable, since the
CH2 application has only simple poles). -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z => (z - z₀) * f z)

/-- The sum of residues of `f` over a region `S`, as a `tsum` over `S`. Points of analyticity
contribute `0`, so this is effectively the sum over the poles of `f` in `S`; when finitely many
poles lie in `S` the `tsum` equals the finite sum of their residues, regardless of `|S|`. (With
infinitely many poles, summability must be assumed for the value to be meaningful.) -/
noncomputable def sumResiduesIn (f : ℂ → ℂ) (S : Set ℂ) : ℂ :=
  ∑' z : S, residue f z

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
