import PrimeNumberTheoremAnd.IEANTN.CH2.CH2_part1
import Mathlib.Analysis.Meromorphic.NormalForm
open Real MeasureTheory FourierTransform Chebyshev Asymptotics
open ArithmeticFunction hiding log
open Complex hiding log

namespace CH2

blueprint_comment /--
\subsection{Contour shifting}\label{ch2-contour-sec}

This section formalises \cite[Section 5]{CH2}. We collect here the notation and the standing
hypotheses shared by Lemma \ref{ch2-lemma-5-1} (contour shifting) and its sub-lemmas.

\textbf{Ladder parameters.} We fix:
\begin{itemize}
  \item a half-height $T > 0$ and a contour height $\delta \in (0, T/4)$. (We write $\delta$ for the
    paper's contour height $\varepsilon$, since $\varepsilon$ already denotes the $\pm 1$ sign in the
    extremal-approximant notation above.)
  \item truncation abscissae $\sigma \colon \mathbb{N} \to \mathbb{R}$ with $\sigma_0 = 1$,
    $\sigma_n \leq 1$, and $\sigma_n \to -\infty$; these are the leftward shift levels in the proof.
\end{itemize}

\textbf{Regions and contours.} Write $s = \Re s + i\, \Im s$. We use:
\begin{itemize}
  \item the rectangle $R = \{ s : \Re s \leq 1,\ |\Im s| \leq T \}$ and its boundary $\partial R$;
  \item the ladder $L = \bigcup_{n \geq 1} \{ \sigma_n + i t : |t| \leq T \}$ (the columns above
    $\sigma_n$ for $n \geq 1$; the $\sigma_0 = 1$ column is part of $\partial R$);
  \item the (simplified) admissible contour $C$: up from $1$ to $1 + i\delta$, then leftward along
    $\Im s = \delta$ to $-\infty$, with conjugate $\overline{C}$;
  \item $R^+ = \{ \Re s \leq 1,\ \delta \leq \Im s \leq T \}$ (the part of $R$ above $C$), its
    conjugate $\overline{R^+} = \{ \Re s \leq 1,\ -T \leq \Im s \leq -\delta \}$ (below
    $\overline{C}$), and $R_C = \{ \Re s \leq 1,\ |\Im s| \leq \delta \}$ (between $C$ and
    $\overline{C}$). Thus $R = R^+ \sqcup R_C \sqcup \overline{R^+}$, so
    $R \setminus R_C = R^+ \sqcup \overline{R^+}$;
  \item the horizontal rays $C_\infty$: $\{ \Im s = \pm T,\ \Re s \leq 1 \}$ (the top and bottom of
    $R$ continued to $-\infty$).
\end{itemize}

\textbf{The function $G$.} We are given a decomposition $G(s) = G^\circ(s) + \mathrm{sgn}(\Im s)\,
G^\star(s)$ in which $G^\circ$ and $G^\star$ are meromorphic on $R$ and $G^\star$ is
\emph{conjugation-antisymmetric}, $G^\star(\bar s) = -\overline{G^\star(s)}$ (so for real $x$ the
integrand $s \mapsto G^\star(s) x^s$ is too; this is what lets the integrals over $C$ and
$\overline{C}$ combine into a single $\frac{1}{\pi} \Im \int_C G^\star x^s$ term). We fix reals
$1 \leq x_0 < x$ and assume $G(s) x_0^s$ is bounded with no poles on $\partial R$, and that both
$G^\circ(s) x_0^s$ and $G^\star(s) x_0^s$ are bounded with no poles on the ladder $L$ and on the
contour $C$.

\textbf{Truncated contours (used in the proof).} At truncation level $n$:
\begin{itemize}
  \item $C_n^+$: from $1$, follow $C$ leftward to $\sigma_n + i\delta$, then up to $\sigma_n + iT$,
    then right to $1 + iT$; $C_n^-$ is the conjugate, traversed backwards;
  \item $C_{n,1}^\pm$: the contour $C_n^\pm$ with its horizontal $\Im s = \pm T$ segment removed;
  \item the $\sigma_n$ column $\{ \sigma_n + it : |t| \leq T \}$.
\end{itemize}
Each contour integral carries the orientation just described; the prefactors $\frac{1}{2\pi i}$ and
$\frac{1}{\pi} \Im$ are written explicitly at each occurrence rather than baked into the contours.

\textbf{Residues (temporary scaffold).} Mathlib has no general residue theorem yet, so
$\mathrm{Res}_{s=\rho}$ denotes the simple-pole residue $\lim_{s \to \rho} (s - \rho) f(s)$, and a
sum $\sum_{\rho \in S} \mathrm{Res}_{s=\rho}$ is the sum of these over the poles of the integrand in
$S$. Over the bounded off-axis region $R \setminus R_C$ this is a finite sum (we assume finitely
many poles there). Over $R_C$, which may contain infinitely many poles on the real axis (e.g. the
trivial zeros of $\zeta$), it is taken in the \emph{improper} sense
$\lim_{n \to \infty} \sum_{\rho \in R_C,\ \Re\rho > \sigma_n} \mathrm{Res}_{s=\rho}$. We also assume
throughout that every pole in $R$ is at most simple. These last conventions are scaffolding to be
removed once Mathlib gains a general (higher-order) residue theorem.
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

/-- Every pole of `f` in `s` is at most simple: the meromorphic order is `≥ -1` everywhere on `s`
(no poles of order `≤ -2`).

**Temporary scaffold.** The placeholder `residue` below (and Mathlib's current residue-theorem API)
is only correct for simple poles, so this hypothesis is added to Lemma 5.1 / Proposition 5.2 and
their sub-lemmas to make them provable with the present API. It holds in the intended applications
(e.g. `ζ'/ζ`, whose poles are all simple) and is to be removed once Mathlib gains general
higher-order residue support. -/
def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z

lemma HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by
  intro z hz
  exact h z (hst hz)

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

/-- The rectangle used in `lemma_5_1_a` is contained in `Rpos`. -/
lemma LadderParams.upperRectangle_subset_Rpos (l : LadderParams) (n : ℕ) :
    Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.Rpos := by
  intro z hz
  have hδ_le_T : l.δ ≤ l.T := by
    have hδ := l.hδ.2
    have hT : 0 < l.T := l.hT
    linarith
  rcases (mem_Rect
      (z := ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I))
      (w := (1 + (l.T : ℂ) * Complex.I))
      (p := z)
      (zRe_lt_wRe := by simpa using l.hσ n)
      (zIm_lt_wIm := by simpa using hδ_le_T)).1 hz with
    ⟨hz_re_left, hz_re_right, hz_im_bot, hz_im_top⟩
  simp only [LadderParams.Rpos, Set.mem_setOf_eq, Set.mem_Icc]
  exact ⟨by simpa using hz_re_right, ⟨by simpa using hz_im_bot, by simpa using hz_im_top⟩⟩

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

lemma residue_eq_of_tendsto {f : ℂ → ℂ} {p c : ℂ}
    (h : Filter.Tendsto (fun z ↦ (z - p) * f z) (nhdsWithin p {p}ᶜ) (nhds c)) :
    residue f p = c := by
  unfold residue
  exact h.limUnder_eq

lemma residue_analyticAt_eq_zero {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    residue f p = 0 := by
  apply residue_eq_of_tendsto
  have hsub : Filter.Tendsto (fun z : ℂ ↦ z - p) (nhdsWithin p {p}ᶜ) (nhds 0) := by
    simpa using
      ((continuous_id.sub continuous_const).continuousAt.continuousWithinAt.tendsto :
        Filter.Tendsto (fun z : ℂ ↦ z - p) (nhdsWithin p {p}ᶜ) (nhds (p - p)))
  have hf' : Filter.Tendsto f (nhdsWithin p {p}ᶜ) (nhds (f p)) :=
    hf.continuousAt.continuousWithinAt.tendsto
  simpa using hsub.mul hf'

lemma simplePole_sub_residue_isBigO_one {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = (-1 : ℤ)) :
    (f - (fun z ↦ residue f p / (z - p))) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg_analytic, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hres : residue f p = g p :=
    residue_eq_of_tendsto (hg_analytic.continuousAt.continuousWithinAt.tendsto.congr'
      (show (fun z ↦ (z - p) * f z) =ᶠ[nhdsWithin p {p}ᶜ] g from by
        filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz_ne
        simp [hz, sub_ne_zero.mpr hz_ne]).symm)
  have hdslope : (fun z ↦ (z - p)⁻¹ * (g z - g p)) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
    have hcont : ContinuousAt (dslope g p) p :=
      continuousAt_dslope_same.2 hg_analytic.differentiableAt
    have hbig : dslope g p =O[nhds p] (1 : ℂ → ℂ) :=
      hcont.norm.isBoundedUnder_le.isBigO_one ℂ
    have hbig_ne : dslope g p =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) :=
      IsBigO.mono hbig inf_le_left
    simpa [slope] using hbig_ne.congr' (dslope_eventuallyEq_slope_nhdsNE (f := g) (a := p)) .rfl
  refine hdslope.congr' ?_ .rfl
  filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz_ne
  simp [hz, hres, div_eq_mul_inv, sub_eq_add_neg]; ring

/-- The improper sum of residues of `f` over `S`, in the sense of the ladder `l`: sum the residues
in the truncation `S ∩ {z | σ n < ℜ z}` and let `n → ∞` (so `σ n → -∞` exhausts `S` from the
right). This is the convention of \cite{CH2} for regions with infinitely many poles --- e.g. the
trivial zeros of `ζ` on the negative real axis, where the ordinary `sumResiduesIn` `tsum` need not
converge --- and it reduces to `sumResiduesIn f S` when the poles of `f` in `S` are finite (the
content of `lemma_5_1_g`). -/
noncomputable def LadderParams.sumResiduesLim (l : LadderParams) (f : ℂ → ℂ) (S : Set ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun n ↦ sumResiduesIn f (S ∩ {z | l.σ n < z.re}))

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

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)
private lemma intervalIntegral_congr_ae_of_codiscreteWithin_along_path
    {f g : ℂ → ℂ} {R : Set ℂ}
    (heq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    {a b : ℝ} {φ : ℝ → ℂ}
    (hφ_an : AnalyticOnNhd ℝ φ (Set.uIcc a b))
    (hφ_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst φ (nhds x))
    (hφ_maps : Set.MapsTo φ (Set.uIcc a b) R) :
    ∫ x in a..b, f (φ x) = ∫ x in a..b, g (φ x) := by
  refine intervalIntegral.integral_congr_ae_restrict (μ := volume) ?_
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  change {x : ℝ | f (φ x) = g (φ x)} ∈ Filter.codiscreteWithin (Set.uIoc a b)
  simpa [Set.preimage] using Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc
    (hφ_an.preimage_mem_codiscreteWithin hφ_nonconst
      (Filter.codiscreteWithin_mono
        (by intro s hs; rcases hs with ⟨x, hx, rfl⟩; exact hφ_maps hx) heq))

private lemma ae_eq_of_codiscreteWithin_along_path
    {f g : ℂ → ℂ} {R : Set ℂ}
    (heq : f =ᶠ[Filter.codiscreteWithin R] g)
    {a b : ℝ} {φ : ℝ → ℂ}
    (hφ_an : AnalyticOnNhd ℝ φ (Set.uIcc a b))
    (hφ_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst φ (nhds x))
    (hφ_maps : Set.MapsTo φ (Set.uIcc a b) R) :
    (fun x ↦ f (φ x)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] (fun x ↦ g (φ x)) := by
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  change {x : ℝ | f (φ x) = g (φ x)} ∈ Filter.codiscreteWithin (Set.uIoc a b)
  simpa [Set.preimage] using Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc
    (hφ_an.preimage_mem_codiscreteWithin hφ_nonconst
      (Filter.codiscreteWithin_mono
        (by intro s hs; rcases hs with ⟨x, hx, rfl⟩; exact hφ_maps hx) heq))

private lemma continuousOn_cpow_vertical_path (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ ↦ (x : ℂ) ^ (1 + t * Complex.I)) s :=
  ((continuous_iff_continuousAt.mpr (fun _ ↦ continuousAt_const_cpow
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : x > 0))))).comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).continuousOn



-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.
private lemma meromorphicOrderAt_eq_neg_one_of_simplePole
    {f : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hpU : p ∈ U)
    (hf_simple : HasSimplePolesOn f U)
    (hpneg : meromorphicOrderAt f p < 0) :
    meromorphicOrderAt f p = (-1 : ℤ) := by
  lift meromorphicOrderAt f p to ℤ using hpneg.ne_top with n hn
  have hsimple : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.mp (hn ▸ hf_simple p hpU)
  simp [show n = -1 from by linarith [WithTop.coe_lt_coe.mp hpneg]]

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.
private lemma residue_toMeromorphicNFOn_eq_residue
    {f : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hpU : p ∈ U)
    (hf_mero : MeromorphicOn f U)
    (hf_simple : HasSimplePolesOn f U)
    (hpneg : meromorphicOrderAt f p < 0) :
    residue (toMeromorphicNFOn f U) p = residue f p := by
  have hmero : MeromorphicAt f p := hf_mero p hpU
  have h_exists : ∃ c, Filter.Tendsto (fun z : ℂ ↦ (z - p) * f z) (nhdsWithin p ({p}ᶜ)) (nhds c) := by
    have hmul_mero : MeromorphicAt (fun z : ℂ ↦ (z - p) * f z) p :=
      (by fun_prop : MeromorphicAt (fun z : ℂ ↦ z - p) p).mul hmero
    have hmul_nonneg : 0 ≤ meromorphicOrderAt (fun z : ℂ ↦ (z - p) * f z) p := by
      change 0 ≤ meromorphicOrderAt ((fun z ↦ z - p) * f) p
      rw [meromorphicOrderAt_mul (by fun_prop : MeromorphicAt (fun z : ℂ ↦ z - p) p) hmero,
        meromorphicOrderAt_id_sub_const,
        meromorphicOrderAt_eq_neg_one_of_simplePole hpU hf_simple hpneg]
      norm_num
    exact tendsto_nhds_of_meromorphicOrderAt_nonneg hmul_mero hmul_nonneg
  have h_tendsto : Filter.Tendsto (fun z : ℂ ↦ (z - p) * f z) (nhdsWithin p ({p}ᶜ)) (nhds (residue f p)) := by
    simpa [residue] using tendsto_nhds_limUnder h_exists
  have h_eq :
      (fun z ↦ (z - p) * toMeromorphicNFOn f U z) =ᶠ[nhdsWithin p ({p}ᶜ)]
        (fun z ↦ (z - p) * f z) := by
    filter_upwards [hf_mero.toMeromorphicNFOn_eq_self_on_nhdsNE hpU] with z hz
    simp [hz]
  exact residue_eq_of_tendsto
    (h_tendsto.congr' h_eq.symm)

-- Non-constancy of horizontal paths `x ↦ x + h * I`.
private lemma horizontalPath_not_eventuallyConst (h : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have := hc.deriv.eq_of_nhds
  simp at this

-- Non-constancy of vertical paths `y ↦ r + y * I`.
private lemma verticalPath_not_eventuallyConst (r : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have heq := hc.deriv.eq_of_nhds
  have hd : deriv (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) x = Complex.I := by
    have := (hasDerivAt_const x (r : ℂ)).add
      ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I)
    simp
  exact Complex.I_ne_zero (hd.symm.trans (heq.trans (deriv_const x c)))

-- Helper for horizontal integral congruence on codiscrete set
private lemma HIntegral_congr_codiscreteWithin {f g : ℂ → ℂ} {R : Set ℂ} {a b c : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ x ∈ Set.uIcc a b, (↑x + ↑c * Complex.I) ∈ R) :
    HIntegral f a b c = HIntegral g a b c := by
  unfold HIntegral
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path h_eq
    (by intro x _; exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)
    (fun x _ ↦ horizontalPath_not_eventuallyConst c x) hmaps

-- Helper for vertical integral congruence on codiscrete set
private lemma VIntegral_congr_codiscreteWithin {f g : ℂ → ℂ} {R : Set ℂ} {c a b : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ y ∈ Set.uIcc a b, (↑c + ↑y * Complex.I) ∈ R) :
    VIntegral f c a b = VIntegral g c a b := by
  unfold VIntegral; simp only [smul_eq_mul]; congr 1
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path h_eq
    (by intro y _; exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
    (fun x _ ↦ verticalPath_not_eventuallyConst c x) hmaps

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.
private lemma rectangleIntegral'_toMeromorphicNFOn_eq {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w)) :
    RectangleIntegral' f z w = RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w := by
  classical
  let R : Set ℂ := Rectangle z w
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  have h_eq : {s : ℂ | f s = fNF s} ∈ Filter.codiscreteWithin R := by
    simpa [Filter.EventuallyEq, Filter.Eventually, fNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (f := f) (U := R) f_mero)
  have hbot := HIntegral_congr_codiscreteWithin h_eq (by simpa [R] using mapsTo_rectangle_left_im z w)
  have htop := HIntegral_congr_codiscreteWithin h_eq (by simpa [R] using mapsTo_rectangle_right_im z w)
  have hright := VIntegral_congr_codiscreteWithin h_eq (by simpa [R] using mapsTo_rectangle_right_re z w)
  have hleft := VIntegral_congr_codiscreteWithin h_eq (by simpa [R] using mapsTo_rectangle_left_re z w)
  unfold RectangleIntegral'; congr 1; unfold RectangleIntegral
  rw [hbot, htop, hright, hleft]

private lemma principalPart_meromorphicOn {R : Set ℂ} {polesFin : Finset ℂ} {c : ℂ → ℂ} :
    MeromorphicOn (fun s ↦ ∑ p ∈ polesFin, c p / (s - p)) R := by
  intro x _
  refine MeromorphicAt.fun_sum (G := fun p s ↦ c p / (s - p)) ?_
  intro p _
  exact (analyticAt_const.meromorphicAt.div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt))

private lemma sub_principalPart_analyticAt_of_not_mem_poles
    {f : ℂ → ℂ} {polesFin : Finset ℂ} {x : ℂ}
    (h_nf : MeromorphicNFAt f x)
    (hxnp : x ∉ polesFin)
    (hxneg : 0 ≤ meromorphicOrderAt f x) :
    AnalyticAt ℂ (f - fun s ↦ ∑ p ∈ polesFin, residue f p / (s - p)) x := by
  have h_f_analytic : AnalyticAt ℂ f x :=
    h_nf.meromorphicOrderAt_nonneg_iff_analyticAt.1 hxneg
  have h_principal_analytic : AnalyticAt ℂ (fun s ↦ ∑ p ∈ polesFin, residue f p / (s - p)) x := by
    refine Finset.analyticAt_fun_sum polesFin ?_
    intro p hp
    have hxp : x ≠ p := by
      intro heq
      subst heq
      exact hxnp hp
    have : AnalyticAt ℂ (fun z : ℂ ↦ residue f p / (z - p)) x := by
      fun_prop (disch := exact sub_ne_zero.mpr hxp)
    simpa using this
  exact h_f_analytic.sub h_principal_analytic

private lemma meromorphicOrderAt_sub_principalPart_nonneg
    {f : ℂ → ℂ} {polesFin : Finset ℂ} {p : ℂ}
    (hpFin : p ∈ polesFin)
    (h_mero : MeromorphicAt f p)
    (h_ord : meromorphicOrderAt f p = -1) :
    0 ≤ meromorphicOrderAt (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) p := by
  have hcore : (f - fun z ↦ residue f p / (z - p)) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    exact simplePole_sub_residue_isBigO_one h_mero h_ord
  let rest : ℂ → ℂ := fun z ↦ ∑ q ∈ polesFin.erase p, residue f q / (z - q)
  have hrest_cont : ContinuousAt rest p := by
    dsimp [rest]
    refine tendsto_finsetSum _ (fun q hq ↦ ?_)
    have hpq : p - q ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hq).1.symm
    have h_cont : ContinuousAt (fun z : ℂ ↦ residue f q / (z - q)) p := by
      fun_prop (disch := exact hpq)
    exact h_cont
  have hrest : rest =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    have hbig : rest =O[nhds p] (1 : ℂ → ℂ) :=
      hrest_cont.norm.isBoundedUnder_le.isBigO_one ℂ
    exact IsBigO.mono hbig inf_le_left
  have hraw_big : (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    have htmp : (fun z : ℂ ↦ (f z - residue f p / (z - p)) - rest z) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) :=
      hcore.sub hrest
    have hdecomp : (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) =
        (fun z : ℂ ↦ (f z - residue f p / (z - p)) - rest z) := by
      funext z
      dsimp [rest]
      rw [← Finset.add_sum_erase (s := polesFin) (f := fun q ↦ residue f q / (z - q)) hpFin]
      simp [sub_eq_add_neg, add_assoc, add_comm]
    simpa [hdecomp, rest] using htmp
  by_contra hneg
  have hnorm : Filter.Tendsto (fun z : ℂ ↦ ‖(f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) z‖) (nhdsWithin p ({p}ᶜ)) Filter.atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg (not_le.mp hneg)
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop hnorm) hraw_big.isBoundedUnder_le

private lemma holoPart_holomorphicOn {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w))
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite) :
    HolomorphicOn (toMeromorphicNFOn (toMeromorphicNFOn f (Rectangle z w) -
      fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) (Rectangle z w)) (Rectangle z w) := by
  classical
  let R := Rectangle z w
  let poles := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin := f_poles_finite.toFinset
  let fNF := toMeromorphicNFOn f R
  let principalPart := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart := toMeromorphicNFOn (fNF - principalPart) R
  have h_fNF_mero : MeromorphicOn fNF R := by
    simpa [fNF] using
      (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R)).meromorphicOn
  have h_principalPart_mero : MeromorphicOn principalPart R := principalPart_meromorphicOn
  have h_raw_mero : MeromorphicOn (fNF - principalPart) R := h_fNF_mero.sub h_principalPart_mero
  intro x hx
  have h_raw_nonneg : 0 ≤ meromorphicOrderAt (fNF - principalPart) x := by
    by_cases hxp : x ∈ poles
    · have hpFin : x ∈ polesFin := by simpa [polesFin, poles] using hxp
      have hord : meromorphicOrderAt f x = (-1 : ℤ) :=
        meromorphicOrderAt_eq_neg_one_of_simplePole hxp.1 f_simple_poles hxp.2
      have hordNF : meromorphicOrderAt fNF x = (-1 : ℤ) := by
        rw [show meromorphicOrderAt fNF x = meromorphicOrderAt f x by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hxp.1)]
        exact hord
      exact meromorphicOrderAt_sub_principalPart_nonneg hpFin (h_fNF_mero x hxp.1) hordNF
    · have hxnp : x ∉ polesFin := by
        intro h
        exact hxp (by simpa [polesFin, poles] using h)
      have h_fNF_nonneg : 0 ≤ meromorphicOrderAt fNF x := by
        rw [show meromorphicOrderAt fNF x = meromorphicOrderAt f x by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hx)]
        exact le_of_not_gt fun hxneg => hxp ⟨hx, hxneg⟩
      have h_fNF_nf : MeromorphicNFAt fNF x := by
        simpa [fNF] using
          (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R) hx)
      exact (sub_principalPart_analyticAt_of_not_mem_poles h_fNF_nf hxnp h_fNF_nonneg).meromorphicOrderAt_nonneg
  have h_nf : MeromorphicNFAt holoPart x := by
    simpa [holoPart] using
      (meromorphicNFOn_toMeromorphicNFOn (f := fNF - principalPart) (U := R) hx)
  have h_ord :
      meromorphicOrderAt holoPart x = meromorphicOrderAt (fNF - principalPart) x := by
    simpa [holoPart] using
      (meromorphicOrderAt_toMeromorphicNFOn (f := fNF - principalPart) (U := R) h_raw_mero hx)
  exact (h_nf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (h_ord.symm ▸ h_raw_nonneg)).differentiableAt.differentiableWithinAt

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.
private lemma principalPart_borderIntegrable {f : ℂ → ℂ} {z w : ℂ}
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite) :
    RectangleBorderIntegrable (fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) z w := by
  classical
  let R := Rectangle z w
  let poles := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin := f_poles_finite.toFinset
  let fNF := toMeromorphicNFOn f R
  let principalPart := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  refine ContinuousOn.rectangleBorder_integrable ?_
  dsimp [principalPart]
  refine continuousOn_finsetSum _ ?_
  intro p hp s hs
  have hsp : s ≠ p := fun hsp => Set.disjoint_right.mp f_no_poles_boundary
    ((by simpa [polesFin, poles] using hp : p ∈ poles).2) (hsp ▸ hs)
  have : ContinuousAt (fun z : ℂ ↦ residue fNF p / (z - p)) s := by
    fun_prop (disch := exact sub_ne_zero.mpr hsp)
  exact this.continuousWithinAt

private lemma rectangle_mem_nhds_of_interior {z w p : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hpR : p ∈ Rectangle z w) (hpnot : p ∉ RectangleBorder z w) :
    Rectangle z w ∈ nhds p := by
  rw [mem_Rect zRe_le_wRe zIm_le_wIm] at hpR
  have hp_re_left : z.re < p.re :=
    lt_of_le_of_ne hpR.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.2.2.1, hpR.2.2.2, zIm_le_wIm, mem_reProdIm])
  have hp_re_right : p.re < w.re :=
    lt_of_le_of_ne hpR.2.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.2.2.1, hpR.2.2.2, zIm_le_wIm, mem_reProdIm])
  have hp_im_left : z.im < p.im :=
    lt_of_le_of_ne hpR.2.2.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.1, hpR.2.1, zRe_le_wRe, mem_reProdIm])
  have hp_im_right : p.im < w.im :=
    lt_of_le_of_ne hpR.2.2.2 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.1, hpR.2.1, zRe_le_wRe, mem_reProdIm])
  rw [rectangle_mem_nhds_iff, mem_reProdIm, Set.uIoo_of_le zRe_le_wRe, Set.uIoo_of_le zIm_le_wIm]
  exact ⟨⟨hp_re_left, hp_re_right⟩, ⟨hp_im_left, hp_im_right⟩⟩

private lemma sum_div_rectangleBorderIntegrable {z w : ℂ} {S : Finset ℂ}
    (hS_disjoint : Disjoint (RectangleBorder z w) S) (c : ℂ → ℂ) :
    RectangleBorderIntegrable (fun s ↦ ∑ p ∈ S, c p / (s - p)) z w := by
  refine ContinuousOn.rectangleBorder_integrable ?_
  refine continuousOn_finsetSum _ ?_
  intro p hp s hs
  have hsp : s ≠ p := fun hsp => Set.disjoint_right.mp hS_disjoint hp (hsp ▸ hs)
  have : ContinuousAt (fun z : ℂ ↦ c p / (z - p)) s := by
    fun_prop (disch := exact sub_ne_zero.mpr hsp)
  exact this.continuousWithinAt

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.
private lemma rectangleIntegral'_sum_div_sub {z w : ℂ} (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    {S : Finset ℂ} (hS_subset : (S : Set ℂ) ⊆ Rectangle z w)
    (hS_disjoint : Disjoint (RectangleBorder z w) S)
    (c : ℂ → ℂ) :
    RectangleIntegral' (fun s ↦ ∑ p ∈ S, c p / (s - p)) z w = ∑ p ∈ S, c p := by
  classical
  have h_partial_border : ∀ (S' : Finset ℂ), S' ⊆ S → RectangleBorderIntegrable (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w := by
    intro S' hS'
    exact sum_div_rectangleBorderIntegrable (Disjoint.mono_right hS' hS_disjoint) c
  have h_term_integral : ∀ {p : ℂ}, p ∈ S → RectangleIntegral' (fun s ↦ c p / (s - p)) z w = c p :=
    fun {p} hp => ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm
      (rectangle_mem_nhds_of_interior zRe_le_wRe zIm_le_wIm
        (hS_subset hp) (Set.disjoint_right.mp hS_disjoint hp))
  have h_partial_integral :
      ∀ (S' : Finset ℂ), S' ⊆ S →
        RectangleIntegral' (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w =
          ∑ p ∈ S', c p := by
    intro S' hS'
    revert hS'
    refine Finset.induction_on S' ?_ ?_
    · intro _
      simp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral]
    · intro a S' ha ih hS'
      obtain ⟨haFin, hSsub⟩ := Finset.insert_subset_iff.mp hS'
      have hterm_border :
          RectangleBorderIntegrable (fun s ↦ c a / (s - a)) z w :=
        by simpa using h_partial_border ({a} : Finset ℂ) (Finset.singleton_subset_iff.mpr haFin)
      have hfun :
          (fun s ↦ ∑ p ∈ insert a S', c p / (s - p)) =
            (fun s ↦ c a / (s - a)) +
              (fun s ↦ ∑ p ∈ S', c p / (s - p)) := by
        funext s; simp [Finset.sum_insert, ha]
      have h_add_primed :
          RectangleIntegral' ((fun s ↦ c a / (s - a)) + (fun s ↦ ∑ p ∈ S', c p / (s - p))) z w =
            RectangleIntegral' (fun s ↦ c a / (s - a)) z w +
              RectangleIntegral' (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w := by
        unfold RectangleIntegral'
        rw [RectangleBorderIntegrable.add hterm_border (h_partial_border S' hSsub), smul_add]
      rw [hfun, h_add_primed, h_term_integral haFin, ih hSsub, Finset.sum_insert ha]
  exact h_partial_integral S (by intro p hp; exact hp)

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.
private lemma toMeromorphicNFOn_add_integral {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite)
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w)) :
    RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w =
      RectangleIntegral' (toMeromorphicNFOn (toMeromorphicNFOn f (Rectangle z w) -
        fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) (Rectangle z w)) z w +
      RectangleIntegral' (fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) z w := by
  let R : Set ℂ := Rectangle z w
  let poles : Set ℂ := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin : Finset ℂ := f_poles_finite.toFinset
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  let principalPart : ℂ → ℂ := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart : ℂ → ℂ := toMeromorphicNFOn (fNF - principalPart) R
  have h_holoPart_border : RectangleBorderIntegrable holoPart z w :=
    (holoPart_holomorphicOn f_mero f_simple_poles f_poles_finite).rectangleBorderIntegrable
  have h_fNF_eq :
      Set.EqOn fNF (holoPart + principalPart) (RectangleBorder z w) := by
    intro s hs
    have hsR : s ∈ R := rectangleBorder_subset_rectangle z w hs
    have hsnp : s ∉ poles := fun hsp => Set.disjoint_right.mp f_no_poles_boundary hsp.2 hs
    have hraw_analytic : AnalyticAt ℂ (fNF - principalPart) s := by
      have h_fNF_nonneg : 0 ≤ meromorphicOrderAt fNF s := by
        rw [show meromorphicOrderAt fNF s = meromorphicOrderAt f s by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hsR)]
        exact le_of_not_gt fun hsneg => hsnp ⟨hsR, hsneg⟩
      exact sub_principalPart_analyticAt_of_not_mem_poles
        (by simpa [fNF] using meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R) hsR)
        (fun h => hsnp (by simpa [polesFin, poles] using h))
        h_fNF_nonneg
    have hs_eq : holoPart s = (fNF - principalPart) s := by
      rw [show holoPart = toMeromorphicNFOn (fNF - principalPart) R by rfl]
      have h_fNF_mero : MeromorphicOn fNF R := by
        simpa [fNF] using (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R)).meromorphicOn
      have hf_sub_mero : MeromorphicOn (fNF - principalPart) R :=
        h_fNF_mero.sub principalPart_meromorphicOn
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (f := fNF - principalPart) (U := R) hf_sub_mero hsR]
      exact congr_fun (toMeromorphicNFAt_eq_self.2 hraw_analytic.meromorphicNFAt) s
    calc
      fNF s = (fNF - principalPart) s + principalPart s := by simp
      _ = holoPart s + principalPart s := by rw [← hs_eq]
  rw [RectangleIntegral'_congr h_fNF_eq, RectangleIntegral',
    RectangleBorderIntegrable.add h_holoPart_border
      (principalPart_borderIntegrable f_no_poles_boundary f_poles_finite), smul_add]

/-- The Residue Theorem on a rectangle for functions with simple poles. -/
lemma RectangleIntegral'_eq_sumResiduesIn {f : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite)
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w)) :
    RectangleIntegral' f z w = sumResiduesIn f (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}) := by
  let R : Set ℂ := Rectangle z w
  let poles : Set ℂ := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin : Finset ℂ := f_poles_finite.toFinset
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  let principalPart : ℂ → ℂ := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart : ℂ → ℂ := toMeromorphicNFOn (fNF - principalPart) R
  have h_residue_congr : sumResiduesIn f poles = sumResiduesIn fNF poles := by
    rw [sumResiduesIn, sumResiduesIn]
    apply tsum_congr
    intro p
    exact (residue_toMeromorphicNFOn_eq_residue p.2.1 f_mero f_simple_poles p.2.2).symm
  have h_principalPart_integral : RectangleIntegral' principalPart z w = sumResiduesIn fNF poles := by
    have h_sum : RectangleIntegral' principalPart z w = ∑ p ∈ polesFin, residue fNF p := by
      apply rectangleIntegral'_sum_div_sub zRe_le_wRe zIm_le_wIm
      · intro p hp
        dsimp [polesFin, poles, R] at hp
        simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hp
        exact hp.1
      · exact Disjoint.mono_right (by rw [f_poles_finite.coe_toFinset]; exact Set.inter_subset_right) f_no_poles_boundary
    rw [h_sum]
    have h_eq_poles : poles = ↑polesFin := by
      dsimp [poles, polesFin, R]
      exact f_poles_finite.coe_toFinset.symm
    rw [sumResiduesIn, h_eq_poles,
      tsum_fintype (f := fun p : (polesFin : Set ℂ) => residue fNF p),
      ← Finset.sum_coe_sort polesFin]; rfl
  calc
    RectangleIntegral' f z w = RectangleIntegral' fNF z w := rectangleIntegral'_toMeromorphicNFOn_eq f_mero
    _ = RectangleIntegral' holoPart z w + RectangleIntegral' principalPart z w :=
      toMeromorphicNFOn_add_integral f_mero f_no_poles_boundary f_poles_finite f_simple_poles
    _ = 0 + sumResiduesIn fNF poles := by
      rw [h_principalPart_integral]
      rw [RectangleIntegral',
        (holoPart_holomorphicOn f_mero f_simple_poles f_poles_finite).vanishesOnRectangle subset_rfl]
      simp
    _ = sumResiduesIn fNF poles := by simp
    _ = sumResiduesIn f poles := h_residue_congr.symm

lemma analyticAt_rpow {x : ℝ} (hx : 0 < x) (s : ℂ) : AnalyticAt ℂ (fun t : ℂ ↦ (x : ℂ) ^ t) s := by
  rw [show (fun t : ℂ ↦ (x : ℂ) ^ t) = fun t : ℂ ↦ Complex.exp (Complex.log (x : ℂ) * t) by
    funext t
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]]
  simpa [mul_comm] using analyticAt_cexp.comp (by fun_prop : AnalyticAt ℂ (fun t : ℂ ↦ Complex.log (x : ℂ) * t) s)

lemma meromorphicAt_rpow {x : ℝ} (hx : 0 < x) (s : ℂ) : MeromorphicAt (fun t : ℂ ↦ (x : ℂ) ^ t) s :=
  (analyticAt_rpow hx s).meromorphicAt

lemma meromorphicOrderAt_rpow {x : ℝ} (hx : 0 < x) (s : ℂ) : meromorphicOrderAt (fun t : ℂ ↦ (x : ℂ) ^ t) s = 0 := by
  rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (meromorphicAt_rpow hx s)]
  refine ⟨_, ?_, (analyticAt_rpow hx s).continuousAt.continuousWithinAt⟩
  exact (Complex.cpow_ne_zero_iff).2 (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))

lemma residue_eq_zero_of_not_pole_of_meromorphicAt {F : ℂ → ℂ} {s : ℂ}
    (hs_mero : MeromorphicAt F s) (hs_not_pole : 0 ≤ meromorphicOrderAt F s) :
    residue F s = 0 := by
  apply residue_eq_of_tendsto
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hs_mero hs_not_pole
  have hsub : Filter.Tendsto (fun z : ℂ ↦ z - s) (nhdsWithin s {s}ᶜ) (nhds 0) := by
    simpa using
      ((continuous_id.sub continuous_const).continuousAt.continuousWithinAt.tendsto :
        Filter.Tendsto (fun z : ℂ ↦ z - s) (nhdsWithin s {s}ᶜ) (nhds (s - s)))
  simpa using hsub.mul hc

private lemma meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn {z : ℂ} {F H : ℂ → ℂ} {S : Set ℂ}
    (hF_mero : MeromorphicAt F z) (hH_mero : MeromorphicAt H z) (hH_order : meromorphicOrderAt H z = 0)
    (h_bdd : IsBoundedNoPolesOn (fun s ↦ F s * H s) S)
    (hz_S : z ∈ S) : 0 ≤ meromorphicOrderAt F z := by
  rcases h_bdd with ⟨M, hM⟩
  have h_prod_order := (hM z hz_S).2
  rw [show (fun s ↦ F s * H s) = F * H by rfl,
    meromorphicOrderAt_mul hF_mero hH_mero, hH_order, add_zero] at h_prod_order
  exact h_prod_order

private lemma meromorphicOrderAt_add_nonneg {F G H : ℂ → ℂ} {z : ℂ}
    (hF : MeromorphicAt F z) (hG : MeromorphicAt G z)
    (hH_eq : H =ᶠ[nhds z] F + G)
    (hF_nonneg : 0 ≤ meromorphicOrderAt F z) (hG_nonneg : 0 ≤ meromorphicOrderAt G z) :
    0 ≤ meromorphicOrderAt H z := by
  have h_sum_order : 0 ≤ meromorphicOrderAt (F + G) z := by
    exact (le_min hF_nonneg hG_nonneg).trans (meromorphicOrderAt_add hF hG)
  rwa [← meromorphicOrderAt_congr (hH_eq.filter_mono nhdsWithin_le_nhds)] at h_sum_order

private lemma upperRectangle_poles_subset_R_minus_RC (l : LadderParams) (n : ℕ) {P : Set ℂ}
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)) P) :
    Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ∩ P ⊆ (l.R \ l.RC) ∩ P := by
  rintro z ⟨hz_rect, hz_pole⟩
  have hz_not_boundary : z ∉ RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) :=
    fun h_bound => Set.disjoint_left.mp h_no_poles_boundary h_bound hz_pole
  have hz_R : z ∈ l.R :=
    (Set.Subset.trans (l.upperRectangle_subset_Rpos n) l.Rpos_subset_R) hz_rect
  have hδ_le_T : l.δ ≤ l.T := by linarith [l.hδ.2, l.hT]
  obtain ⟨hz_re_left, hz_re_right, hz_im_low, hz_im_high⟩ :=
    (mem_Rect (by simpa using l.hσ n) (by simpa using hδ_le_T) z).mp hz_rect
  have hz_im_gt_delta : l.δ < z.im := by
    refine lt_of_le_of_ne (by simpa using hz_im_low) ?_
    intro heq
    apply hz_not_boundary
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff]
    refine Or.inl (Or.inl (Or.inl ?_))
    have hz_re_bounds : z.re ∈ Set.uIcc ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I).re (1 + (l.T : ℂ) * Complex.I).re := by
      rw [Set.uIcc_of_le (by simpa using l.hσ n), Set.mem_Icc]
      exact ⟨by simpa using hz_re_left, by simpa using hz_re_right⟩
    have hz_im_eq : z.im = ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I).im := by simpa using heq.symm
    exact ⟨hz_re_bounds, hz_im_eq⟩
  have hz_not_RC : z ∉ l.RC :=
    fun h_RC => by linarith [(le_abs_self z.im).trans h_RC.2, hz_im_gt_delta]
  exact ⟨⟨hz_R, hz_not_RC⟩, hz_pole⟩

private lemma upperRectangle_inter_poles_eq (l : LadderParams) (n : ℕ) {P : Set ℂ}
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)) P) :
    Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ∩ P =
    (l.Rpos ∩ {z | l.σ n < z.re}) ∩ P := by
  ext s
  let Rn := Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)
  have hδ_le_T : l.δ ≤ l.T := by linarith [l.hδ.2, l.hT]
  constructor
  · rintro ⟨hs_rect, hs_pole⟩
    have hs_Rpos : s ∈ l.Rpos := l.upperRectangle_subset_Rpos n hs_rect
    have hs_not_boundary :
        s ∉ RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) :=
      fun hs_boundary => (Set.disjoint_left.mp h_no_poles_boundary) hs_boundary hs_pole
    obtain ⟨hs_re_left, hs_re_right, hs_im_low, hs_im_high⟩ :=
      (mem_Rect (by simpa using l.hσ n) (by simpa using hδ_le_T) s).1 hs_rect
    have hs_re_lt : l.σ n < s.re := by
      have hs_re_left' : l.σ n ≤ s.re := by simpa using hs_re_left
      refine lt_of_le_of_ne hs_re_left' ?_
      intro hs_eq
      apply hs_not_boundary
      have hs_left : s ∈ ({l.σ n} : Set ℝ) ×ℂ Set.uIcc l.δ l.T := by
        rw [Complex.mem_reProdIm]
        constructor
        · simpa using hs_eq.symm
        · have hs_im_low' : l.δ ≤ s.im := by simpa using hs_im_low
          have hs_im_high' : s.im ≤ l.T := by simpa using hs_im_high
          simpa [Set.uIcc_of_le hδ_le_T] using And.intro hs_im_low' hs_im_high'
      refine Or.inl (Or.inl (Or.inr ?_))
      simpa [Set.uIcc_of_le hδ_le_T] using hs_left
    exact ⟨⟨hs_Rpos, hs_re_lt⟩, hs_pole⟩
  · rintro ⟨⟨hs_Rpos, hs_re_lt⟩, hs_pole⟩
    have hs_rect : s ∈ Rn := by
      have hs_re_lt' : l.σ n < s.re := by simpa using hs_re_lt
      have hs_re_lt'' : ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I).re < s.re := by simpa using hs_re_lt'
      have hs_re_right' : s.re ≤ (1 + (l.T : ℂ) * Complex.I).re := by simpa using hs_Rpos.1
      have hs_im_low' : ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I).im ≤ s.im := by simpa using hs_Rpos.2.1
      have hs_im_high' : s.im ≤ (1 + (l.T : ℂ) * Complex.I).im := by simpa using hs_Rpos.2.2
      rw [mem_Rect (by simpa using l.hσ n) (by simpa using hδ_le_T)]
      exact ⟨le_of_lt hs_re_lt'', hs_re_right', hs_im_low', hs_im_high'⟩
    exact ⟨hs_rect, hs_pole⟩

lemma upperRectangle_meromorphicOn (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x) :
    MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)) := by
  intro s hs
  have h_rect_subset_Rpos :
      Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.Rpos :=
    l.upperRectangle_subset_Rpos n
  have h_rect_subset_R :
      Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.R :=
    Set.Subset.trans h_rect_subset_Rpos l.Rpos_subset_R
  have hs_Rpos : s ∈ l.Rpos := h_rect_subset_Rpos hs
  have hs_R : s ∈ l.R := h_rect_subset_R hs
  have hs_im_pos : 0 < s.im := lt_of_lt_of_le l.hδ.1 hs_Rpos.2.1
  have h_eq :
      (fun t : ℂ ↦ G t * (x : ℂ) ^ t) =ᶠ[nhdsWithin s {s}ᶜ]
        (fun t : ℂ ↦ (G_circ t + G_star t) * (x : ℂ) ^ t) := by
    have hpos_mem : {t : ℂ | 0 < t.im} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hs_im_pos
    have hpos_mem' : {t : ℂ | 0 < t.im} ∈ nhdsWithin s {s}ᶜ := nhdsWithin_le_nhds hpos_mem
    filter_upwards [hpos_mem'] with t ht
    have hsign : (Real.sign t.im : ℂ) = 1 := by simp [Real.sign_of_pos ht]
    simp [hG t, hsign]
  refine MeromorphicAt.congr ?_ h_eq.symm
  have hx_pos : 0 < x := by linarith
  exact ((hG_circ_mero s hs_R).add (hG_star_mero s hs_R)).mul (meromorphicAt_rpow hx_pos s)

lemma upperRectangleIntegral'_eq_sumResiduesIn (n : ℕ)
    (h_rect_mero : MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)))
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I))
      {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0})
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R) :
    RectangleIntegral' (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) =
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}) := by
  have h_rect_subset_Rpos :
      Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.Rpos :=
    l.upperRectangle_subset_Rpos n
  have h_rect_subset_R :
      Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.R :=
    Set.Subset.trans h_rect_subset_Rpos l.Rpos_subset_R
  apply RectangleIntegral'_eq_sumResiduesIn
  · simpa using l.hσ n
  · simpa using show l.δ ≤ l.T by linarith [l.hδ.2, l.hT]
  · exact h_rect_mero
  · exact h_no_poles_boundary
  · exact Set.Finite.subset hfin (upperRectangle_poles_subset_R_minus_RC l n h_no_poles_boundary)
  · exact HasSimplePolesOn.mono hsimple h_rect_subset_R

lemma intVSeg_eq_intCnPlus_add_rectangleIntegral (l : LadderParams) (n : ℕ) (F : ℂ → ℂ)
    (h_integrable1 : IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume 0 l.δ)
    (h_integrable2 : IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume l.δ l.T) :
    intVSeg 1 0 l.T F = l.intCnPlus n F + RectangleIntegral F ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) := by
  have h1 : l.intCnPlus n F = (intVSeg 1 0 l.δ F + intHSeg l.δ 1 (l.σ n) F + intVSeg (l.σ n) l.δ l.T F + intHSeg l.T (l.σ n) 1 F) := rfl
  have h2 : RectangleIntegral F ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) = (intHSeg l.δ (l.σ n) 1 F - intHSeg l.T (l.σ n) 1 F + intVSeg 1 l.δ l.T F - intVSeg (l.σ n) l.δ l.T F) := by
    have hH1 : HIntegral F (l.σ n) 1 l.δ = intHSeg l.δ (l.σ n) 1 F := rfl
    have hH2 : HIntegral F (l.σ n) 1 l.T = intHSeg l.T (l.σ n) 1 F := rfl
    have hV1 : Complex.I * ∫ (y : ℝ) in l.δ..l.T, F (1 + ↑y * Complex.I) =
      intVSeg 1 l.δ l.T F := by
      rw [intVSeg, ← smul_eq_mul, ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr (fun y _ ↦ ?_)
      rw [smul_eq_mul, mul_comm]; rfl
    have hV2 : Complex.I * ∫ (y : ℝ) in l.δ..l.T, F (↑(l.σ n) + ↑y * Complex.I) =
      intVSeg (l.σ n) l.δ l.T F := by
      rw [intVSeg, ← smul_eq_mul, ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr (fun y _ ↦ ?_)
      rw [smul_eq_mul, mul_comm]
    rw [RectangleIntegral]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
    dsimp [VIntegral]
    rw [hH1, hH2, hV1, hV2]
  have h_unfolded : l.intCnPlus n F +
    RectangleIntegral F ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) =
    (intVSeg 1 0 l.δ F + intHSeg l.δ 1 (l.σ n) F +
     intVSeg (l.σ n) l.δ l.T F + intHSeg l.T (l.σ n) 1 F) +
    (intHSeg l.δ (l.σ n) 1 F - intHSeg l.T (l.σ n) 1 F +
     intVSeg 1 l.δ l.T F - intVSeg (l.σ n) l.δ l.T F) := by
      rw [h1, h2]
  have h_δ_cancel : intHSeg l.δ 1 (l.σ n) F + intHSeg l.δ (l.σ n) 1 F = 0 := by
    rw [intHSeg, intHSeg, intervalIntegral.integral_symm]
    ring
  have h_cancelled : (intVSeg 1 0 l.δ F + intHSeg l.δ 1 (l.σ n) F +
     intVSeg (l.σ n) l.δ l.T F + intHSeg l.T (l.σ n) 1 F) +
    (intHSeg l.δ (l.σ n) 1 F - intHSeg l.T (l.σ n) 1 F +
     intVSeg 1 l.δ l.T F - intVSeg (l.σ n) l.δ l.T F) =
    intVSeg 1 0 l.δ F + intVSeg 1 l.δ l.T F := by
      calc
        _ = (intVSeg 1 0 l.δ F + intVSeg 1 l.δ l.T F) +
            (intHSeg l.δ 1 (l.σ n) F + intHSeg l.δ (l.σ n) 1 F) := by ring
        _ = intVSeg 1 0 l.δ F + intVSeg 1 l.δ l.T F := by rw [h_δ_cancel, add_zero]
  have h_adjacent : intVSeg 1 0 l.δ F + intVSeg 1 l.δ l.T F =
    intVSeg 1 0 l.T F := by
      rw [intVSeg, intVSeg, intVSeg]; push_cast
      rw [intervalIntegral.integral_add_adjacent_intervals h_integrable1 h_integrable2]
  rw [h_unfolded, h_cancelled, h_adjacent]

lemma sumResiduesIn_upperRectangle_eq_sumResiduesIn_Rpos (l : LadderParams) (n : ℕ) (F : ℂ → ℂ)
    (h_rect_mero : MeromorphicOn F (Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)))
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I))
      {z | meromorphicOrderAt F z < 0}) :
    sumResiduesIn F (Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt F z < 0}) =
      sumResiduesIn F (l.Rpos ∩ {z | l.σ n < z.re}) := by
  let Rn : Set ℂ :=
    Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)
  let P : Set ℂ := {z | meromorphicOrderAt F z < 0}
  let S2 : Set ℂ := l.Rpos ∩ {z | l.σ n < z.re}
  have hδ_le_T : l.δ ≤ l.T := by linarith [l.hδ.2, l.hT]
  have h_rect_subset_Rpos : Rn ⊆ l.Rpos :=
    l.upperRectangle_subset_Rpos n
  have h_set_eq : Rn ∩ P = S2 ∩ P := upperRectangle_inter_poles_eq l n h_no_poles_boundary
  have h_residue_zero :
      ∀ s ∈ S2, s ∉ P → residue F s = 0 := by
    intro s hs_S2 hs_not_pole
    have hs_rect : s ∈ Rn := by
      have hs_re_lt' : l.σ n < s.re := by simpa using hs_S2.2
      have hs_re_lt'' : ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I).re < s.re := by simpa using hs_re_lt'
      have hs_re_right' : s.re ≤ (1 + (l.T : ℂ) * Complex.I).re := by simpa using hs_S2.1.1
      have hs_im_low' : ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I).im ≤ s.im := by simpa using hs_S2.1.2.1
      have hs_im_high' : s.im ≤ (1 + (l.T : ℂ) * Complex.I).im := by simpa using hs_S2.1.2.2
      rw [mem_Rect (by simpa using l.hσ n) (by simpa using hδ_le_T)]
      exact ⟨le_of_lt hs_re_lt'', hs_re_right', hs_im_low', hs_im_high'⟩
    exact residue_eq_zero_of_not_pole_of_meromorphicAt (h_rect_mero s hs_rect) (le_of_not_gt hs_not_pole)
  have h_goal : sumResiduesIn F (Rn ∩ P) = sumResiduesIn F S2 := by
    rw [sumResiduesIn, sumResiduesIn, tsum_subtype, tsum_subtype]
    apply tsum_congr
    intro s
    by_cases hs_S2 : s ∈ S2
    · by_cases hs_pole : s ∈ P
      · have hs_rect_pole : s ∈ Rn ∩ P := h_set_eq.symm ▸ ⟨hs_S2, hs_pole⟩
        simp [hs_S2, hs_rect_pole]
      · have hs_not_rect_pole : s ∉ Rn ∩ P := fun hs => hs_pole hs.2
        have hres0 : residue F s = 0 := h_residue_zero s hs_S2 hs_pole
        simp [hs_S2, hs_not_rect_pole, hres0]
    · have hs_not_rect_pole : s ∉ Rn ∩ P := fun hs => hs_S2 (h_set_eq ▸ hs).1
      simp [hs_S2, hs_not_rect_pole]
  simpa [Rn, P, S2, h_set_eq] using h_goal

lemma upperRectangle_no_poles_boundary (l : LadderParams) (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x) :
    Disjoint (RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I))
      {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0} := by
  rw [Set.disjoint_left]
  rintro z hz hz_pole
  simp only [Set.mem_setOf_eq] at hz_pole
  have h_rect_subset_Rpos :
      Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.Rpos :=
    l.upperRectangle_subset_Rpos n
  have h_rect_subset_R :
      Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.R :=
    Set.Subset.trans h_rect_subset_Rpos l.Rpos_subset_R
  have hz_rect : z ∈ Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) :=
    rectangleBorder_subset_rectangle _ _ hz
  have h_im_bounds : z.im ∈ Set.Icc l.δ l.T := by
    have h_mem := (mem_Rect (by simpa using l.hσ n) (by simpa using show l.δ ≤ l.T by linarith [l.hδ.2, l.hT]) z).mp hz_rect
    exact ⟨by simpa using h_mem.2.2.1, by simpa using h_mem.2.2.2⟩
  have hz_im_pos : 0 < z.im := lt_of_lt_of_le l.hδ.1 h_im_bounds.1
  have h_sign : (Real.sign z.im : ℂ) = 1 := by simp [Real.sign_of_pos hz_im_pos]
  have abs_zim_le : |z.im| ≤ l.T := by
    rw [abs_of_pos hz_im_pos]
    exact h_im_bounds.2
  have hG_eq : G =ᶠ[nhds z] G_circ + G_star := by
    have hpos_mem : {t : ℂ | 0 < t.im} ∈ nhds z :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz_im_pos
    filter_upwards [hpos_mem] with t ht
    have hsign : (Real.sign t.im : ℂ) = 1 := by simp [Real.sign_of_pos ht]
    simp [hG t, hsign]
  have hz_R : z ∈ l.R := h_rect_subset_R hz_rect
  have hGc_mero : MeromorphicAt G_circ z := hG_circ_mero z hz_R
  have hGs_mero : MeromorphicAt G_star z := hG_star_mero z hz_R
  have hG_mero : MeromorphicAt G z :=
    (hGc_mero.add hGs_mero).congr (Filter.EventuallyEq.filter_mono hG_eq.symm nhdsWithin_le_nhds)
  have hx_pos : 0 < x := by linarith
  have hx₀_pos : 0 < x₀ := by linarith
  have hpow_mero : MeromorphicAt (fun s ↦ (x : ℂ) ^ s) z := meromorphicAt_rpow hx_pos z
  have hpow_order : meromorphicOrderAt (fun s ↦ (x : ℂ) ^ s) z = 0 := meromorphicOrderAt_rpow hx_pos z
  have hpow0_mero : MeromorphicAt (fun s ↦ (x₀ : ℂ) ^ s) z := meromorphicAt_rpow hx₀_pos z
  have hpow0_order : meromorphicOrderAt (fun s ↦ (x₀ : ℂ) ^ s) z = 0 := meromorphicOrderAt_rpow hx₀_pos z
  have extract_order : ∀ (F : ℂ → ℂ) (S : Set ℂ) (hF_mero : MeromorphicAt F z),
      IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) S → z ∈ S → 0 ≤ meromorphicOrderAt F z :=
    fun F S hF_mero h_bdd hz_S ↦ meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn hF_mero hpow0_mero hpow0_order h_bdd hz_S
  have combine_orders : 0 ≤ meromorphicOrderAt G_circ z → 0 ≤ meromorphicOrderAt G_star z → 0 ≤ meromorphicOrderAt G z :=
    meromorphicOrderAt_add_nonneg hGc_mero hGs_mero hG_eq
  have h_nonneg_G : 0 ≤ meromorphicOrderAt G z := by
    have h_sigma_le : l.σ n ≤ 1 := l.hσ n
    have h_delta_le : l.δ ≤ l.T := by linarith [l.hδ.1, l.hδ.2, l.hT]
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, add_zero, sub_zero, mul_one, zero_add,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.one_re, Complex.one_im,
      Set.uIcc_of_le h_sigma_le, Set.uIcc_of_le h_delta_le] at hz
    rcases hz with (((⟨hz_re, hz_im⟩ | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩)
    · have hz_contour : z ∈ l.admissible_contour := by
        left
        exact ⟨hz_re.2, hz_im⟩
      exact combine_orders (extract_order G_circ l.admissible_contour hGc_mero hGc_contour hz_contour)
                           (extract_order G_star l.admissible_contour hGs_mero hGs_contour hz_contour)
    · cases n with
      | zero =>
        have hz_Rb : z ∈ l.Rboundary := by
          left
          exact ⟨by rw [hz_re, l.h0], abs_zim_le⟩
        exact extract_order G l.Rboundary hG_mero hG_bdd hz_Rb
      | succ n_pred =>
        have hz_L : z ∈ l.L := by
          use n_pred + 1
          exact ⟨by omega, hz_re, abs_zim_le⟩
        exact combine_orders (extract_order G_circ l.L hGc_mero hGc_L hz_L)
                             (extract_order G_star l.L hGs_mero hGs_L hz_L)
    · have hz_Rb : z ∈ l.Rboundary := by
        right
        exact ⟨hz_re.2, by simpa [hz_im] using l.hT.le⟩
      exact extract_order G l.Rboundary hG_mero hG_bdd hz_Rb
    · have hz_Rb : z ∈ l.Rboundary := by
        left
        exact ⟨hz_re, abs_zim_le⟩
      exact extract_order G l.Rboundary hG_mero hG_bdd hz_Rb
  have h_prod_eq : (fun s ↦ G s * (x : ℂ) ^ s) = G * (fun s : ℂ ↦ (x : ℂ) ^ s) := rfl
  have h_prod_order : meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z = meromorphicOrderAt G z := by
    rw [h_prod_eq, meromorphicOrderAt_mul hG_mero hpow_mero, hpow_order, add_zero]
  have h_pole_contra : meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0 := hz_pole
  rw [h_prod_order] at h_pole_contra
  exact not_lt.mpr h_nonneg_G h_pole_contra

private lemma continuousOn_toMeromorphicNFOn_Rboundary {F : ℂ → ℂ} (l : LadderParams)
    (hF_mero : MeromorphicOn F l.R)
    (hF_nopoles : ∀ s ∈ l.Rboundary, 0 ≤ meromorphicOrderAt F s) :
    ContinuousOn (toMeromorphicNFOn F l.R) l.Rboundary := by
  intro s hs
  have h_NF_mero := meromorphicNFOn_toMeromorphicNFOn F l.R (LadderParams.Rboundary_subset_R l hs)
  have h_order : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn F l.R) s :=
    (meromorphicOrderAt_toMeromorphicNFOn hF_mero (LadderParams.Rboundary_subset_R l hs)).symm ▸ hF_nopoles s hs
  have h_anal := h_NF_mero.meromorphicOrderAt_nonneg_iff_analyticAt.1 h_order
  exact h_anal.continuousAt.continuousWithinAt

private lemma continuousOn_toMeromorphicNFOn_upperRboundary {F : ℂ → ℂ} (l : LadderParams)
    (hF_mero : MeromorphicOn F l.R)
    (hF_nopoles : ∀ s ∈ l.Rboundary, 0 ≤ s.im → 0 ≤ meromorphicOrderAt F s) :
    ContinuousOn (toMeromorphicNFOn F l.R) (l.Rboundary ∩ {s | 0 ≤ s.im}) := by
  intro s hs
  have h_NF_mero := meromorphicNFOn_toMeromorphicNFOn F l.R (LadderParams.Rboundary_subset_R l hs.1)
  have h_order : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn F l.R) s :=
    (meromorphicOrderAt_toMeromorphicNFOn hF_mero (LadderParams.Rboundary_subset_R l hs.1)).symm ▸ hF_nopoles s hs.1 hs.2
  have h_anal := h_NF_mero.meromorphicOrderAt_nonneg_iff_analyticAt.1 h_order
  exact h_anal.continuousAt.continuousWithinAt

private lemma mapsTo_vseg_Rboundary (l : LadderParams) {a b : ℝ} (ha_nonneg : 0 ≤ a) (hb_le_T : b ≤ l.T) :
    Set.MapsTo (fun t : ℝ ↦ 1 + t * Complex.I) (Set.Icc a b) l.Rboundary := by
  intro t ht
  left
  refine ⟨by simp, ?_⟩
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
    Complex.ofReal_re, Complex.I_re, mul_one, add_zero, mul_zero, zero_add]
  rw [abs_of_nonneg (by linarith [ha_nonneg, ht.1])]
  exact by linarith [hb_le_T, ht.2]

private lemma ae_eq_NF_vseg {F : ℂ → ℂ} (l : LadderParams) {a b : ℝ} (ha_nonneg : 0 ≤ a) (hab : a ≤ b) (hb_le_T : b ≤ l.T)
    (hF_mero : MeromorphicOn F l.R) :
    (fun t : ℝ ↦ F (1 + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
    (fun t : ℝ ↦ toMeromorphicNFOn F l.R (1 + t * Complex.I)) := by
  have h_uIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have h_ae := toMeromorphicNFOn_eqOn_codiscrete hF_mero
  have h_maps : Set.MapsTo (fun t : ℝ ↦ (1:ℂ) + t * Complex.I) (Set.uIcc a b) l.R := by
    intro t ht
    rw [h_uIcc, Set.mem_Icc] at ht
    simp only [LadderParams.R, Set.mem_setOf_eq, add_re, one_re, mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
      add_im, one_im, zero_add, le_refl, true_and]
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    rw [abs_of_nonneg (by linarith [ha_nonneg, ht.1])]
    linarith [hb_le_T, ht.2]
  exact ae_eq_of_codiscreteWithin_along_path h_ae
    (fun y _ => analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
    (fun y _ ↦ verticalPath_not_eventuallyConst 1 y) h_maps

private lemma G_mul_cpow_integrable_vseg (l : LadderParams)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀)
    (hG_nopoles : ∀ s ∈ l.Rboundary, 0 ≤ s.im → 0 ≤ meromorphicOrderAt (G_circ + G_star) s)
    (hx : x₀ < x) (a b : ℝ) (ha_nonneg : 0 ≤ a) (hab : a ≤ b) (hb_le_T : b ≤ l.T) :
    IntervalIntegrable (fun t : ℝ ↦ (G (1 + t * Complex.I) * (x : ℂ) ^ (1 + t * Complex.I)) * Complex.I) volume a b := by
  let H_upper := fun (t : ℝ) ↦
    toMeromorphicNFOn (G_circ + G_star) l.R ((1:ℂ) + t * Complex.I) *
    (x : ℂ) ^ ((1:ℂ) + t * Complex.I) * Complex.I
  have h_ae : (fun t : ℝ ↦ (G (1 + t * Complex.I) * (x : ℂ) ^ (1 + t * Complex.I)) * Complex.I)
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] H_upper := by
    have h_sum_path := ae_eq_NF_vseg l ha_nonneg hab hb_le_T (hG_circ_mero.add hG_star_mero)
    have h_mem_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc a b)), t ∈ Set.uIoc a b :=
      MeasureTheory.ae_restrict_mem measurableSet_uIoc
    filter_upwards [h_sum_path, h_mem_ae] with t ht_sum ht_mem
    have ht_pos : 0 < t := by linarith [ha_nonneg, (Set.uIoc_of_le hab ▸ ht_mem).1]
    have hsign : (Real.sign ((1:ℂ) + t * Complex.I).im : ℂ) = 1 := by simp [Real.sign_of_pos ht_pos]
    dsimp [H_upper]
    rw [hG ((1:ℂ) + t * Complex.I), hsign, one_mul]
    have h_fold : G_circ (1 + t * Complex.I) + G_star (1 + t * Complex.I) = (G_circ + G_star) (1 + t * Complex.I) := rfl
    rw [h_fold, ht_sum]
  refine IntervalIntegrable.congr_ae ?_ h_ae.symm
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  have h_cont_sum_NF : ContinuousOn (toMeromorphicNFOn (G_circ + G_star) l.R) (l.Rboundary ∩ {s | 0 ≤ s.im}) :=
    continuousOn_toMeromorphicNFOn_upperRboundary l (hG_circ_mero.add hG_star_mero) hG_nopoles
  have h_maps_rb : Set.MapsTo (fun t : ℝ ↦ 1 + t * Complex.I) (Set.Icc a b) (l.Rboundary ∩ {s | 0 ≤ s.im}) := by
    intro t ht
    refine ⟨mapsTo_vseg_Rboundary l ha_nonneg hb_le_T ht, ?_⟩
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, add_zero, mul_zero, zero_add, Set.mem_setOf_eq]
    linarith [ht.1]
  exact (ContinuousOn.comp h_cont_sum_NF (Continuous.continuousOn (by fun_prop)) h_maps_rb).mul
    (continuousOn_cpow_vertical_path hx₀ hx _) |>.mul_const Complex.I

@[blueprint
  "ch2-lemma-5-1-a"
  (title := "Contour shifting, upper half (CH2 Lemma 5.1, eq. 1)")
  (statement := /--
  For each $n$, shifting the upper half $1 \to 1 + iT$ of the central line leftwards to the
  truncated contour $C_n^+$ picks up the residues of $G$ in $R^+$ to the right of $\sigma_n$:
  $$ \frac{1}{2\pi i}\int_1^{1+iT} G(s) x^s\, ds = \frac{1}{2\pi i}\int_{C_n^+} G(s) x^s\, ds + \sum_{\rho \in R^+,\ \Re\rho > \sigma_n} \mathrm{Res}_{s=\rho} G(s) x^s. $$ -/)
  (proof := /-- The residue theorem on the region of $R^+$ between $[1, 1+iT]$ and $C_n^+$. -/)
  (latexEnv := "sublemma")
  (discussion := 1448)]
theorem lemma_5_1_a (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R) :
    (2 * (π : ℂ) * Complex.I)⁻¹ * intVSeg 1 0 l.T (fun s ↦ G s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCnPlus n (fun s ↦ G s * (x : ℂ) ^ s) +
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.Rpos ∩ {z | l.σ n < z.re}) := by
  have hG_nopoles : ∀ s ∈ l.Rboundary, 0 ≤ s.im → 0 ≤ meromorphicOrderAt (G_circ + G_star) s := by
    intro s hs hs_im
    by_cases hs_im_pos : 0 < s.im
    · -- Case 1: s.im > 0, so G = G_circ + G_star near s, and G has no poles on Rboundary (hG_bdd)
      have hpos_mem : {t : ℂ | 0 < t.im} ∈ nhds s :=
        (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hs_im_pos
      have hG_eq : G =ᶠ[nhds s] G_circ + G_star := by
        filter_upwards [hpos_mem] with t ht
        have hsign : (Real.sign t.im : ℂ) = 1 := by simp [Real.sign_of_pos ht]
        simp [hG t, hsign]
      have hG_eq' : G =ᶠ[nhdsWithin s {s}ᶜ] G_circ + G_star := hG_eq.filter_mono nhdsWithin_le_nhds
      rw [← meromorphicOrderAt_congr hG_eq']
      have hG_mero : MeromorphicAt G s :=
        ((hG_circ_mero s (l.Rboundary_subset_R hs)).add (hG_star_mero s (l.Rboundary_subset_R hs))).congr (hG_eq.symm.filter_mono nhdsWithin_le_nhds)
      have hx₀_pos : 0 < x₀ := by linarith [hx₀]
      have hpow0_mero : MeromorphicAt (fun s ↦ (x₀ : ℂ) ^ s) s := meromorphicAt_rpow hx₀_pos s
      have hpow0_order : meromorphicOrderAt (fun s ↦ (x₀ : ℂ) ^ s) s = 0 := meromorphicOrderAt_rpow hx₀_pos s
      exact meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn hG_mero hpow0_mero hpow0_order hG_bdd hs
    · -- Case 2: s.im = 0, so s = 1. G_circ and G_star have no poles at 1 from hGc_contour and hGs_contour since 1 ∈ admissible_contour
      have hs_im_zero : s.im = 0 := by linarith [hs_im, hs_im_pos]
      have hs_re : s.re = 1 := by
        have h_Rbd : s ∈ l.Rboundary := hs
        simp only [LadderParams.Rboundary, Set.mem_setOf_eq] at h_Rbd
        rcases h_Rbd with ⟨hre, _⟩ | ⟨_, him⟩
        · exact hre
        · rw [hs_im_zero, abs_zero] at him
          have hT_gt_zero := l.hT
          linarith [him]
      have hs_eq : s = 1 := by rw [Complex.ext_iff]; simp [hs_re, hs_im_zero]
      have h1_contour : (1 : ℂ) ∈ l.admissible_contour := Or.inr ⟨by rfl, ⟨le_rfl, l.hδ.1.le⟩⟩
      have hGc_order : 0 ≤ meromorphicOrderAt G_circ s := by
        have hx₀_pos : 0 < x₀ := by linarith [hx₀]
        have hpow0_mero : MeromorphicAt (fun s ↦ (x₀ : ℂ) ^ s) s := meromorphicAt_rpow hx₀_pos s
        have hpow0_order : meromorphicOrderAt (fun s ↦ (x₀ : ℂ) ^ s) s = 0 := meromorphicOrderAt_rpow hx₀_pos s
        have hGc_mero : MeromorphicAt G_circ s := hG_circ_mero s (l.Rboundary_subset_R hs)
        have hs_contour : s ∈ l.admissible_contour := hs_eq ▸ h1_contour
        exact meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn hGc_mero hpow0_mero hpow0_order hGc_contour hs_contour
      have hGs_order : 0 ≤ meromorphicOrderAt G_star s := by
        have hx₀_pos : 0 < x₀ := by linarith [hx₀]
        have hpow0_mero : MeromorphicAt (fun s ↦ (x₀ : ℂ) ^ s) s := meromorphicAt_rpow hx₀_pos s
        have hpow0_order : meromorphicOrderAt (fun s ↦ (x₀ : ℂ) ^ s) s = 0 := meromorphicOrderAt_rpow hx₀_pos s
        have hGs_mero : MeromorphicAt G_star s := hG_star_mero s (l.Rboundary_subset_R hs)
        have hs_contour : s ∈ l.admissible_contour := hs_eq ▸ h1_contour
        exact meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn hGs_mero hpow0_mero hpow0_order hGs_contour hs_contour
      have hGc_mero : MeromorphicAt G_circ s := hG_circ_mero s (l.Rboundary_subset_R hs)
      have hGs_mero : MeromorphicAt G_star s := hG_star_mero s (l.Rboundary_subset_R hs)
      exact meromorphicOrderAt_add_nonneg hGc_mero hGs_mero (Filter.EventuallyEq.refl (nhds s) (G_circ + G_star)) hGc_order hGs_order
  have h_unprimed_eq : intVSeg 1 0 l.T (fun s ↦ G s * (x : ℂ) ^ s) =
    l.intCnPlus n (fun s ↦ G s * (x : ℂ) ^ s) +
    RectangleIntegral (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) :=
      intVSeg_eq_intCnPlus_add_rectangleIntegral l n (fun s ↦ G s * (x : ℂ) ^ s)
        (G_mul_cpow_integrable_vseg l hG hG_circ_mero hG_star_mero hx₀ hG_nopoles hx 0 l.δ (by rfl) (le_of_lt l.hδ.1) (by linarith [l.hδ.2, l.hT]))
        (G_mul_cpow_integrable_vseg l hG hG_circ_mero hG_star_mero hx₀ hG_nopoles hx l.δ l.T (le_of_lt (by linarith [l.hδ.1])) (by linarith [l.hδ.2, l.hT]) le_rfl)
  have h_int_eq : (2 * (π : ℂ) * Complex.I)⁻¹ * intVSeg 1 0 l.T (fun s ↦ G s * (x : ℂ) ^ s) =
    (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCnPlus n (fun s ↦ G s * (x : ℂ) ^ s) +
    RectangleIntegral' (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) := by
    rw [h_unprimed_eq, mul_add, RectangleIntegral', smul_eq_mul]; ring_nf
  have h_rect_subset_Rpos :
      Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.Rpos :=
    l.upperRectangle_subset_Rpos n
  have h_rect_subset_R :
      Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ⊆ l.R :=
    Set.Subset.trans h_rect_subset_Rpos l.Rpos_subset_R
  have h_rect_mero : MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)) :=
    upperRectangle_meromorphicOn n hG hG_circ_mero hG_star_mero hx₀ hx
  have h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I))
    {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0} :=
      upperRectangle_no_poles_boundary l n hG hG_circ_mero hG_star_mero hx₀ hG_bdd hGc_L hGc_contour hGs_L hGs_contour hx
  have h_residue_thm : RectangleIntegral' (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) =
    sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}) :=
      upperRectangleIntegral'_eq_sumResiduesIn n h_rect_mero h_no_poles_boundary hfin hsimple
  have h_residue_set_eq : sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}) =
    sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.Rpos ∩ {z | l.σ n < z.re}) :=
      sumResiduesIn_upperRectangle_eq_sumResiduesIn_Rpos l n (fun s ↦ G s * (x : ℂ) ^ s) h_rect_mero h_no_poles_boundary
  have h_residue := h_residue_thm.trans h_residue_set_eq
  rw [h_int_eq, h_residue]


@[blueprint
  "ch2-lemma-5-1-b"
  (title := "Contour shifting, lower half (CH2 Lemma 5.1, eq. 2)")
  (statement := /--
  For each $n$, shifting the lower half $1 - iT \to 1$ of the central line leftwards to the
  truncated contour $C_n^-$ picks up the residues of $G$ in $\overline{R^+}$ to the right of $\sigma_n$:
  $$ \frac{1}{2\pi i}\int_{1-iT}^{1} G(s) x^s\, ds = \frac{1}{2\pi i}\int_{C_n^-} G(s) x^s\, ds + \sum_{\rho \in \overline{R^+},\ \Re\rho > \sigma_n} \mathrm{Res}_{s=\rho} G(s) x^s. $$ -/)
  (proof := /-- The residue theorem on the region of $\overline{R^+}$ between $[1-iT, 1]$ and $C_n^-$. -/)
  (latexEnv := "sublemma")
  (discussion := 1449)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R)
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
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
  (latexEnv := "sublemma")
  (discussion := 1450)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R)
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
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
  (latexEnv := "sublemma")
  (discussion := 1451)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R)
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
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
  (latexEnv := "sublemma")
  (discussion := 1452)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R)
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
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
  (latexEnv := "sublemma")
  (discussion := 1453)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R)
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
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
  (latexEnv := "sublemma")
  (discussion := 1454)]
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
  (latexEnv := "sublemma")
  (discussion := 1455)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R)
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
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
  where the first sum runs over the (finitely many --- see the hypotheses) poles of $G$ in the
  bounded off-axis strip $R \setminus R_C$, while the second is the \emph{improper} residue sum of
  $G^\circ$ over $R_C$, i.e.\ the limit of the truncations $R_C \cap \{\Re s > \sigma_n\}$ as
  $n \to \infty$. The improper sum allows infinitely many poles on the real axis (e.g.\ the trivial
  zeros of $\zeta$), where an ordinary sum need not converge.

  \emph{Temporary scaffold:} we additionally assume every pole of $G$ (resp.\ $G^\circ$) in $R$ is
  at most simple ($\mathrm{HasSimplePolesOn}$). The formalised residue and the current Mathlib
  residue-theorem API are only valid for simple poles; this hypothesis holds in the intended
  applications and is to be dropped once higher-order residue support lands. -/)
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
  $\Im \int_{C_{n,1}^+} G^\star x^s \to \Im \int_C G^\star x^s$; the off-axis truncated sums converge
  to the full (finite) residue sums over $R^+ \sqcup \overline{R^+} = R \setminus R_C$
  (\ref{ch2-lemma-5-1-g}), while the $R_C$ truncated sum converges to the improper residue sum by
  definition. Collecting terms, and using $\frac{1}{2\pi i} \cdot 2i = \frac{1}{\pi}$, yields the
  claim. -/)
  (latexEnv := "lemma")
  (discussion := 1456)]
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
    -- finiteness of the off-real-line pole set (our addition; off the real line there are only
    -- finitely many poles in the bounded strip `R \ R_C`). The `R_C` residue sum is taken in the
    -- improper `sumResiduesLim` sense, allowing infinitely many poles on the real line (e.g. the
    -- trivial zeros of `ζ`), so no finiteness is assumed there.
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    -- temporary scaffold: the placeholder `residue` and Mathlib's current residue-theorem API only
    -- handle simple poles, so we assume all poles in `R` are simple (true in the applications;
    -- remove once higher-order residue support lands):
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R)
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
    (2 * (π : ℂ) * Complex.I)⁻¹ * l.intVerticalAt 1 (fun s ↦ G s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCinf (fun s ↦ G s * (x : ℂ) ^ s) +
      (↑(π⁻¹ * (l.intC (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ) +
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.R \ l.RC) +
      l.sumResiduesLim (fun s ↦ G_circ s * (x : ℂ) ^ s) l.RC := by
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
  (latexEnv := "sublemma")
  (discussion := 1457)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) l.R)
    (hsimple_circ :
        HasSimplePolesOn
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.R) :
    (2 * (π : ℂ) * Complex.I)⁻¹ *
        l.intVerticalAt 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ *
          l.intCinf (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) +
        (↑(π⁻¹ * (l.intC (fun s ↦ (Real.sign lam : ℂ) *
            Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)).im) : ℂ) +
        sumResiduesIn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) +
        l.sumResiduesLim
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
  (latexEnv := "sublemma")
  (discussion := 1458)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) l.R)
    (hsimple_circ :
        HasSimplePolesOn
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.R) :
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
  (latexEnv := "sublemma")
  (discussion := 1459)]
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
    (hsimple : HasSimplePolesOn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) l.R)
    (hsimple_circ :
        HasSimplePolesOn
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.R) :
    ‖(↑(π⁻¹ * (l.intC (fun s   ↦ (Real.sign lam : ℂ) *
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
  where the second sum is the \emph{improper} residue sum (a limit of truncations $R_C \cap \{\Re s > \sigma_n\}$, allowing the infinitely many real-axis poles) of $\Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s)$ over $R_C$, whose poles include that of $\Phi^\circ$ at $1 + \frac{\lambda T}{2\pi}$ when $\lambda < 0$, and
  $$ E = \frac{1}{T} \sum_{\xi = \pm 1} \int_0^\infty t\, |F(1 - t + i\xi T)|\, x^{1-t}\, dt + 2 \left| \int_C \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s) x^s\, ds \right|. $$
  Here $O^*(E)$ is rendered as $\| \cdot \| \leq E$. The first part of $E$ bounds the $C_\infty$
  integral of Lemma \ref{ch2-lemma-5-1} (via $|\Phi^\varepsilon_\lambda(\pm 1 + ir)| \leq |r|$ on
  the lines $\Re s = \pm 1$), and the second is its $\frac{1}{\pi} \Im \int_C G^\star$ term.

  \emph{Temporary scaffold:} as in Lemma \ref{ch2-lemma-5-1}, we assume every pole in $R$ is at most
  simple ($\mathrm{HasSimplePolesOn}$), since the formalised residue is only valid for simple poles;
  this is to be removed once Mathlib gains higher-order residue support. -/)
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
    (hsimple : HasSimplePolesOn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) l.R)
    (hsimple_circ :
        HasSimplePolesOn
          (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.R) :
    ‖(2 * (π : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) -
        sumResiduesIn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) (l.R \ l.RC) -
        l.sumResiduesLim
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
          l.sumResiduesLim
            (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s) l.RC =
        (2 * (π : ℂ) * Complex.I)⁻¹ *
            l.intCinf (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s) +
          (↑(π⁻¹ * (l.intC (fun s ↦ (Real.sign lam : ℂ) *
              Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)).im) : ℂ) := by
    rw [prop_5_2_a hF_mero hF_symm hlam hε hx₀ hF_bdd hx hfin hsimple hsimple_circ]
    ring
  rw [hLHS]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add
    (prop_5_2_b hF_mero hF_symm hlam hε hx₀ hF_bdd hx hfin hsimple hsimple_circ)
    (prop_5_2_c hF_mero hF_symm hlam hε hx₀ hF_bdd hx hfin hsimple hsimple_circ)) ?_
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
