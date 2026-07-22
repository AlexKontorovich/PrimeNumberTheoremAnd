import Mathlib.Analysis.Meromorphic.NormalForm
import PrimeNumberTheoremAnd.IEANTN.CH2.CH2_part1
import PrimeNumberTheoremAnd.ZetaConj
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

private lemma LadderParams.mem_admissible_contour_of_re_eq_one_of_im_nonneg (l : LadderParams)
    {z : ℂ} (hz_re : z.re = 1) (hz_im : z.im ∈ Set.Icc 0 l.δ) :
    z ∈ l.admissible_contour := by
  simp only [LadderParams.admissible_contour, Set.mem_setOf_eq]
  exact Or.inr ⟨hz_re, hz_im⟩

private lemma LadderParams.star_mem_admissible_contour_of_re_eq_one_of_im_nonpos
    (l : LadderParams) {z : ℂ} (hz_re : z.re = 1) (hz_im : z.im ∈ Set.Icc (-l.δ) 0) :
    starRingEnd ℂ z ∈ l.admissible_contour := by
  refine l.mem_admissible_contour_of_re_eq_one_of_im_nonneg ?_ ?_
  · rw [starRingEnd_apply, star_def, Complex.conj_re, hz_re]
  · rw [starRingEnd_apply, star_def, Complex.conj_im, Set.mem_Icc]
    constructor <;> linarith [hz_im.1, hz_im.2]

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

private lemma continuousOn_cpow_vertical_path (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (c : ℝ) (s : Set ℝ) :
    ContinuousOn (fun t : ℝ ↦ (x : ℂ) ^ (c + t * Complex.I)) s :=
  ((continuous_iff_continuousAt.mpr (fun _ ↦ continuousAt_const_cpow
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : x > 0))))).comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).continuousOn

private lemma continuousOn_cpow_horizontal_path (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (h : ℝ) (s : Set ℝ) :
    ContinuousOn (fun r : ℝ ↦ (x : ℂ) ^ (r + h * Complex.I)) s :=
  ((continuous_iff_continuousAt.mpr (fun _ ↦ continuousAt_const_cpow
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : x > 0))))).comp
    (Complex.continuous_ofReal.add continuous_const)).continuousOn

private lemma horizontalPath_not_eventuallyConst (h : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have := hc.deriv.eq_of_nhds
  simp at this




lemma analyticAt_rpow {x : ℝ} (hx : 0 < x) (s : ℂ) : AnalyticAt ℂ (fun t : ℂ ↦ (x : ℂ) ^ t) s := by
  rw [show (fun t : ℂ ↦ (x : ℂ) ^ t) = fun t : ℂ ↦ Complex.exp (Complex.log (x : ℂ) * t) by
    funext t
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]]
  simpa [mul_comm] using! analyticAt_cexp.comp (by fun_prop : AnalyticAt ℂ (fun t : ℂ ↦ Complex.log (x : ℂ) * t) s)

lemma meromorphicAt_rpow {x : ℝ} (hx : 0 < x) (s : ℂ) : MeromorphicAt (fun t : ℂ ↦ (x : ℂ) ^ t) s :=
  (analyticAt_rpow hx s).meromorphicAt

lemma meromorphicOrderAt_rpow {x : ℝ} (hx : 0 < x) (s : ℂ) : meromorphicOrderAt (fun t : ℂ ↦ (x : ℂ) ^ t) s = 0 := by
  rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (meromorphicAt_rpow hx s)]
  refine ⟨_, ?_, (analyticAt_rpow hx s).continuousAt.continuousWithinAt⟩
  exact (Complex.cpow_ne_zero_iff).2 (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))


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

private lemma rectangle_left_edge_mem_border_of_re_eq {z z0 w : ℂ}
    (hz_rect : z ∈ Rectangle z0 w) (hz0w_re : z0.re ≤ w.re) (hz0w_im : z0.im ≤ w.im)
    (hz_eq : z0.re = z.re) :
    z ∈ RectangleBorder z0 w := by
  obtain ⟨_, _, hz_im_low, hz_im_high⟩ := (mem_Rect hz0w_re hz0w_im z).1 hz_rect
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff]
  refine Or.inl <| Or.inl <| Or.inr ?_
  constructor
  · simpa using hz_eq.symm
  · have hz_im_low' : z0.im ≤ z.im := by simpa using hz_im_low
    have hz_im_high' : z.im ≤ w.im := by simpa using hz_im_high
    simpa [Set.uIcc_of_le hz0w_im] using And.intro hz_im_low' hz_im_high'

private lemma rectangle_left_re_lt_of_mem_of_not_mem_border {z z0 w : ℂ}
    (hz_rect : z ∈ Rectangle z0 w) (hz_not_boundary : z ∉ RectangleBorder z0 w)
    (hz0w_re : z0.re ≤ w.re) (hz0w_im : z0.im ≤ w.im) :
    z0.re < z.re := by
  obtain ⟨hz_re_left, _, _, _⟩ := (mem_Rect hz0w_re hz0w_im z).1 hz_rect
  refine lt_of_le_of_ne ?_ ?_
  · simpa using hz_re_left
  · intro hz_eq
    exact hz_not_boundary (rectangle_left_edge_mem_border_of_re_eq hz_rect hz0w_re hz0w_im hz_eq)

private lemma upperRectangle_inter_poles_eq (l : LadderParams) (n : ℕ) {P : Set ℂ}
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)) P) :
    Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) ∩ P =
    (l.Rpos ∩ {z | l.σ n < z.re}) ∩ P := by
  ext s
  have hδ_le_T : l.δ ≤ l.T := by linarith [l.hδ.2, l.hT]
  constructor
  · rintro ⟨hs_rect, hs_pole⟩
    have hs_Rpos : s ∈ l.Rpos := l.upperRectangle_subset_Rpos n hs_rect
    have hs_not_boundary :
        s ∉ RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) :=
      fun hs_boundary => (Set.disjoint_left.mp h_no_poles_boundary) hs_boundary hs_pole
    have hs_re_lt : l.σ n < s.re := by
      simpa using
        rectangle_left_re_lt_of_mem_of_not_mem_border hs_rect hs_not_boundary
          (by simpa using l.hσ n) (by simpa using hδ_le_T)
    exact ⟨⟨hs_Rpos, hs_re_lt⟩, hs_pole⟩
  · rintro ⟨⟨hs_Rpos, hs_re_lt⟩, hs_pole⟩
    have hs_rect : s ∈ Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) := by
      have hs_re_right' : s.re ≤ (1 + (l.T : ℂ) * Complex.I).re := by simpa using hs_Rpos.1
      have hs_im_low' : ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I).im ≤ s.im := by simpa using hs_Rpos.2.1
      have hs_im_high' : s.im ≤ (1 + (l.T : ℂ) * Complex.I).im := by simpa using hs_Rpos.2.2
      rw [mem_Rect (by simpa using l.hσ n) (by simpa using hδ_le_T)]
      exact ⟨by simpa using le_of_lt hs_re_lt, hs_re_right', hs_im_low', hs_im_high'⟩
    exact ⟨hs_rect, hs_pole⟩

private lemma filter_eventuallyEq_G_pos {G G_circ G_star : ℂ → ℂ} {z : ℂ}
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hz_im_pos : 0 < z.im) :
    G =ᶠ[nhds z] G_circ + G_star := by
  have hpos_mem : {t : ℂ | 0 < t.im} ∈ nhds z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz_im_pos
  filter_upwards [hpos_mem] with t ht
  have hsign : (Real.sign t.im : ℂ) = 1 := by simp [Real.sign_of_pos ht]
  simp [hG t, hsign]

private lemma filter_eventuallyEq_G_neg {G G_circ G_star : ℂ → ℂ} {z : ℂ}
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hz_im_neg : z.im < 0) :
    G =ᶠ[nhds z] G_circ - G_star := by
  have hneg_mem : {t : ℂ | t.im < 0} ∈ nhds z :=
    (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz_im_neg
  filter_upwards [hneg_mem] with t ht
  have hsign : (Real.sign t.im : ℂ) = -1 := by simp [Real.sign_of_neg ht]
  have ht_eq := hG t
  rw [hsign] at ht_eq
  change G t = G_circ t - G_star t
  rw [ht_eq]
  ring

private lemma meromorphicOrderAt_neg_nonneg {F : ℂ → ℂ} {z : ℂ}
    (hF_mero : MeromorphicAt F z)
    (hF_nonneg : 0 ≤ meromorphicOrderAt F z) :
    0 ≤ meromorphicOrderAt (-F) z := by
  have h_neg_eq : -F = (fun x ↦ -1) * F := by ext x; change -(F x) = -1 * F x; ring
  rw [h_neg_eq]
  have h_order_add := meromorphicOrderAt_mul (f := fun _ ↦ (-1 : ℂ)) (show AnalyticAt ℂ (fun _ ↦ (-1:ℂ)) z from analyticAt_const).meromorphicAt hF_mero
  rw [h_order_add]
  have h_const : meromorphicOrderAt (fun (x : ℂ) ↦ (-1 : ℂ)) z = 0 := by simp [meromorphicOrderAt_const]
  rw [h_const, zero_add]
  exact hF_nonneg

private lemma meromorphicOrderAt_mul_cpow_eq {F : ℂ → ℂ} {x : ℝ} {z : ℂ}
    (hx_pos : 0 < x) (hF_mero : MeromorphicAt F z) :
    meromorphicOrderAt (fun s ↦ F s * (x : ℂ) ^ s) z = meromorphicOrderAt F z := by
  have h_prod_eq : (fun s ↦ F s * (x : ℂ) ^ s) = F * (fun s : ℂ ↦ (x : ℂ) ^ s) := rfl
  have hpow_mero : MeromorphicAt (fun s ↦ (x : ℂ) ^ s) z := meromorphicAt_rpow hx_pos z
  have hpow_order : meromorphicOrderAt (fun s ↦ (x : ℂ) ^ s) z = 0 := meromorphicOrderAt_rpow hx_pos z
  rw [h_prod_eq, meromorphicOrderAt_mul hF_mero hpow_mero, hpow_order, add_zero]

private lemma mem_RectangleBorder_upper_cases (l : LadderParams) (n : ℕ) {z : ℂ}
    (hz : z ∈ RectangleBorder ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I)) :
    z ∈ l.admissible_contour ∨ z ∈ l.L ∨ z ∈ l.Rboundary := by
  have h_sigma_le : l.σ n ≤ 1 := l.hσ n
  have h_delta_le : l.δ ≤ l.T := by linarith [l.hδ.1, l.hδ.2, l.hT]
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, sub_zero, mul_one, zero_add,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.one_re, Complex.one_im,
    Set.uIcc_of_le h_sigma_le, Set.uIcc_of_le h_delta_le] at hz
  rcases hz with (((⟨hz_re, hz_im⟩ | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩)
  · left
    exact Or.inl ⟨hz_re.2, hz_im⟩
  · have abs_zim_le : |z.im| ≤ l.T := by
      rw [abs_of_pos (by linarith [l.hδ.1, hz_im.1])]
      exact hz_im.2
    cases n with
    | zero =>
      right; right; left
      exact ⟨by rw [hz_re, l.h0], abs_zim_le⟩
    | succ n_pred =>
      right; left
      use n_pred + 1
      exact ⟨by omega, hz_re, abs_zim_le⟩
  · right; right; right
    exact ⟨hz_re.2, by simpa [hz_im] using l.hT.le⟩
  · right; right; left
    have abs_zim_le : |z.im| ≤ l.T := by
      rw [abs_of_pos (by linarith [l.hδ.1, hz_im.1])]
      exact hz_im.2
    exact ⟨hz_re, abs_zim_le⟩

private lemma mem_RectangleBorder_lower_cases (l : LadderParams) (n : ℕ) {z : ℂ}
    (hz : z ∈ RectangleBorder ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I)) :
    (starRingEnd ℂ z) ∈ l.admissible_contour ∨ z ∈ l.L ∨ z ∈ l.Rboundary := by
  have h_sigma_le : l.σ n ≤ 1 := l.hσ n
  have h_negT_le_negDelta : -l.T ≤ -l.δ := by linarith [l.hδ.1, l.hδ.2, l.hT]
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, sub_zero, mul_one, zero_sub,
    Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.one_re, Complex.one_im,
    Set.uIcc_of_le h_sigma_le, Set.uIcc_of_le h_negT_le_negDelta] at hz
  rcases hz with (((⟨hz_re, hz_im⟩ | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩)
  · right; right; right
    exact ⟨hz_re.2, by simpa [hz_im] using l.hT.le⟩
  · have abs_zim_le : |z.im| ≤ l.T := by
      rw [abs_of_neg (by linarith [l.hδ.1, hz_im.2])]
      exact by linarith [hz_im.1]
    cases n with
    | zero =>
      right; right; left
      exact ⟨by rw [hz_re, l.h0], abs_zim_le⟩
    | succ n_pred =>
      right; left
      use n_pred + 1
      exact ⟨by omega, hz_re, abs_zim_le⟩
  · left; left
    exact ⟨hz_re.2, by simp [hz_im]⟩
  · right; right; left
    have abs_zim_le : |z.im| ≤ l.T := by
      rw [abs_of_neg (by linarith [l.hδ.1, hz_im.2])]
      exact by linarith [hz_im.1]
    exact ⟨hz_re, abs_zim_le⟩

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
    have heq : G =ᶠ[nhdsWithin s {s}ᶜ] G_circ + G_star :=
      (filter_eventuallyEq_G_pos hG hs_im_pos).filter_mono nhdsWithin_le_nhds
    filter_upwards [heq] with t ht
    rw [ht]; rfl
  refine MeromorphicAt.congr ?_ h_eq.symm
  have hx_pos : 0 < x := by linarith
  exact ((hG_circ_mero s hs_R).add (hG_star_mero s hs_R)).mul (meromorphicAt_rpow hx_pos s)


private lemma sumResiduesIn_eq_of_inter_poles_eq_and_subset {F : ℂ → ℂ} {Rn S2 : Set ℂ}
    (hRn_mero : MeromorphicOn F Rn)
    (h_set_eq : Rn ∩ {z | meromorphicOrderAt F z < 0} = S2 ∩ {z | meromorphicOrderAt F z < 0})
    (hS2_subset : S2 ⊆ Rn) :
    sumResiduesIn F (Rn ∩ {z | meromorphicOrderAt F z < 0}) = sumResiduesIn F S2 := by
  refine sumResiduesIn_inter_eq_of_set_eq h_set_eq ?_
  intro s hs_S2 hs_not_pole
  have hs_not_pole' : ¬ meromorphicOrderAt F s < 0 := by
    simpa only [Set.mem_setOf_eq] using hs_not_pole
  exact residue_eq_zero_of_not_pole_of_meromorphicAt (hRn_mero s (hS2_subset hs_S2))
    (le_of_not_gt hs_not_pole')

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
  have hRn_mero : MeromorphicOn F Rn := by
    simpa [Rn] using h_rect_mero
  have h_set_eq : Rn ∩ P = S2 ∩ P := by
    simpa [Rn, P, S2] using
      (upperRectangle_inter_poles_eq (l := l) (n := n) (P := P) h_no_poles_boundary)
  have hS2_subset : S2 ⊆ Rn := by
    intro s hs_S2
    have hs_S2' : s ∈ l.Rpos ∩ {z | l.σ n < z.re} := by
      simpa [S2] using hs_S2
    rw [show Rn = Rectangle ((l.σ n : ℂ) + (l.δ : ℂ) * Complex.I) (1 + (l.T : ℂ) * Complex.I) by
      rfl]
    rw [mem_Rect (by simpa using l.hσ n) (by simpa using hδ_le_T)]
    exact ⟨by simpa using le_of_lt hs_S2'.2, by simpa using hs_S2'.1.1,
      by simpa using hs_S2'.1.2.1, by simpa using hs_S2'.1.2.2⟩
  exact sumResiduesIn_eq_of_inter_poles_eq_and_subset hRn_mero h_set_eq hS2_subset

private lemma meromorphicOrderAt_nonneg_of_bounded {F : ℂ → ℂ} {S : Set ℂ} {z : ℂ} {x₀ : ℝ}
    (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicAt F z)
    (h_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) S) (hz_S : z ∈ S) :
    0 ≤ meromorphicOrderAt F z := by
  have hx₀_pos : 0 < x₀ := by linarith [hx₀]
  have hpow0_mero : MeromorphicAt (fun s ↦ (x₀ : ℂ) ^ s) z := meromorphicAt_rpow hx₀_pos z
  have hpow0_order : meromorphicOrderAt (fun s ↦ (x₀ : ℂ) ^ s) z = 0 := meromorphicOrderAt_rpow hx₀_pos z
  exact meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn hF_mero hpow0_mero hpow0_order h_bdd hz_S

private lemma meromorphicOrderAt_nonneg_on_of_bounded {F : ℂ → ℂ} {S : Set ℂ} {x₀ : ℝ}
    (l : LadderParams) (hx₀ : 1 ≤ x₀) (hS_subset : S ⊆ l.R) (hF_mero : MeromorphicOn F l.R)
    (h_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) S) :
    ∀ s ∈ S, 0 ≤ meromorphicOrderAt F s := by
  intro s hs
  exact meromorphicOrderAt_nonneg_of_bounded hx₀ (hF_mero _ (hS_subset hs)) h_bdd hs

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
  have hpow_mero : MeromorphicAt (fun s ↦ (x : ℂ) ^ s) z := meromorphicAt_rpow hx_pos z
  have hpow_order : meromorphicOrderAt (fun s ↦ (x : ℂ) ^ s) z = 0 := meromorphicOrderAt_rpow hx_pos z
  have extract_order : ∀ (F : ℂ → ℂ) (S : Set ℂ) (hF_mero : MeromorphicAt F z),
      IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) S → z ∈ S → 0 ≤ meromorphicOrderAt F z :=
    fun F S hF_mero h_bdd hz_S ↦ meromorphicOrderAt_nonneg_of_bounded hx₀ hF_mero h_bdd hz_S
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

private lemma continuousOn_toMeromorphicNFOn_subset {F : ℂ → ℂ} {S : Set ℂ} (l : LadderParams)
    (hS_sub : S ⊆ l.R)
    (hF_mero : MeromorphicOn F l.R)
    (hF_nopoles : ∀ s ∈ S, 0 ≤ meromorphicOrderAt F s) :
    ContinuousOn (toMeromorphicNFOn F l.R) S := by
  intro s hs
  have h_NF_mero := meromorphicNFOn_toMeromorphicNFOn F l.R (hS_sub hs)
  have h_order : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn F l.R) s :=
    (meromorphicOrderAt_toMeromorphicNFOn hF_mero (hS_sub hs)).symm ▸ hF_nopoles s hs
  have h_anal := h_NF_mero.meromorphicOrderAt_nonneg_iff_analyticAt.1 h_order
  exact h_anal.continuousAt.continuousWithinAt

private lemma ae_eq_NF_vseg_general {F : ℂ → ℂ} (l : LadderParams) (c : ℝ) {a b : ℝ}
    (h_maps_R : ∀ t ∈ Set.uIcc a b, c + t * Complex.I ∈ l.R)
    (hF_mero : MeromorphicOn F l.R) :
    (fun t : ℝ ↦ F (c + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
    (fun t : ℝ ↦ toMeromorphicNFOn F l.R (c + t * Complex.I)) := by
  have h_ae := toMeromorphicNFOn_eqOn_codiscrete hF_mero
  exact ae_eq_of_codiscreteWithin_along_path h_ae
    (fun y _ => analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
    (fun y _ ↦ verticalPath_not_eventuallyConst c y) h_maps_R

private lemma G_circ_mul_cpow_integrable_vseg_general (l : LadderParams) (G_circ : ℂ → ℂ)
    (hG_circ_mero : MeromorphicOn G_circ l.R)
    (x₀ x : ℝ) (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (S : Set ℂ)
    (h_subset_R : S ⊆ l.R)
    (hGc_nopoles : ∀ s ∈ S, 0 ≤ meromorphicOrderAt G_circ s)
    (c a b : ℝ) (hab : a ≤ b)
    (h_maps_S : ∀ t ∈ Set.Icc a b, c + t * Complex.I ∈ S) :
    IntervalIntegrable (fun t : ℝ ↦ (G_circ (c + t * Complex.I) * (x : ℂ) ^ (c + t * Complex.I)) * Complex.I) volume a b := by
  let H_upper := fun (t : ℝ) ↦
    toMeromorphicNFOn G_circ l.R (c + t * Complex.I) *
    (x : ℂ) ^ (c + t * Complex.I) * Complex.I
  have h_maps_R : ∀ t ∈ Set.uIcc a b, c + t * Complex.I ∈ l.R := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact h_subset_R (h_maps_S t ht)
  have h_ae : (fun t : ℝ ↦ G_circ (c + t * Complex.I))
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      (fun t : ℝ ↦ toMeromorphicNFOn G_circ l.R (c + t * Complex.I)) :=
    ae_eq_NF_vseg_general l c h_maps_R hG_circ_mero
  have h_ae_full : (fun t : ℝ ↦ (G_circ (c + t * Complex.I) * (x : ℂ) ^ (c + t * Complex.I)) * Complex.I)
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] H_upper := by
    filter_upwards [h_ae] with t ht
    dsimp [H_upper]
    rw [ht]
  refine IntervalIntegrable.congr_ae ?_ h_ae_full.symm
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  have h_cont_sum_NF : ContinuousOn (toMeromorphicNFOn G_circ l.R) S :=
    continuousOn_toMeromorphicNFOn_subset l h_subset_R hG_circ_mero hGc_nopoles
  have h_maps : Set.MapsTo (fun t : ℝ ↦ c + t * Complex.I) (Set.Icc a b) S := h_maps_S
  exact (ContinuousOn.comp h_cont_sum_NF (Continuous.continuousOn (by fun_prop)) h_maps).mul
    (continuousOn_cpow_vertical_path hx₀ hx c _) |>.mul_const Complex.I

private lemma G_circ_mul_cpow_integrable_hseg_general (l : LadderParams) (G_circ : ℂ → ℂ)
    (hG_circ_mero : MeromorphicOn G_circ l.R)
    (x₀ x : ℝ) (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (S : Set ℂ)
    (h_subset_R : S ⊆ l.R)
    (hGc_nopoles : ∀ s ∈ S, 0 ≤ meromorphicOrderAt G_circ s)
    (h a b : ℝ) (hab : a ≤ b)
    (h_maps_S : ∀ r ∈ Set.Icc a b, (r : ℂ) + h * Complex.I ∈ S) :
    IntervalIntegrable (fun r : ℝ ↦ G_circ ((r : ℂ) + h * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + h * Complex.I)) volume a b := by
  let H := fun (r : ℝ) ↦
    toMeromorphicNFOn G_circ l.R ((r : ℂ) + h * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + h * Complex.I)
  have h_maps_R : ∀ r ∈ Set.uIcc a b, (r : ℂ) + h * Complex.I ∈ l.R := by
    intro r hr
    rw [Set.uIcc_of_le hab] at hr
    exact h_subset_R (h_maps_S r hr)
  have h_ae : (fun r : ℝ ↦ G_circ ((r : ℂ) + h * Complex.I))
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      (fun r : ℝ ↦ toMeromorphicNFOn G_circ l.R ((r : ℂ) + h * Complex.I)) := by
    have h_ae' := toMeromorphicNFOn_eqOn_codiscrete hG_circ_mero
    exact ae_eq_of_codiscreteWithin_along_path h_ae'
      (fun y _ => (Complex.ofRealCLM.analyticAt y).add analyticAt_const)
      (fun y _ ↦ horizontalPath_not_eventuallyConst h y) h_maps_R
  have h_ae_full : (fun r : ℝ ↦ G_circ ((r : ℂ) + h * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + h * Complex.I))
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] H := by
    filter_upwards [h_ae] with r hr
    dsimp [H]
    rw [hr]
  refine IntervalIntegrable.congr_ae ?_ h_ae_full.symm
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  have h_cont_sum_NF : ContinuousOn (toMeromorphicNFOn G_circ l.R) S :=
    continuousOn_toMeromorphicNFOn_subset l h_subset_R hG_circ_mero hGc_nopoles
  have h_maps : Set.MapsTo (fun r : ℝ ↦ (r : ℂ) + h * Complex.I) (Set.Icc a b) S := h_maps_S
  exact (ContinuousOn.comp h_cont_sum_NF (Continuous.continuousOn (by fun_prop)) h_maps).mul
    (continuousOn_cpow_horizontal_path hx₀ hx h _)

private lemma mapsTo_vseg_Rboundary (l : LadderParams) {a b : ℝ} (ha : -l.T ≤ a) (hb : b ≤ l.T) :
    Set.MapsTo (fun t : ℝ ↦ 1 + t * Complex.I) (Set.Icc a b) l.Rboundary := by
  intro t ht
  left
  refine ⟨by simp, ?_⟩
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
    Complex.ofReal_re, Complex.I_re, mul_one, add_zero, mul_zero, zero_add]
  have h1 : -l.T ≤ t := ha.trans ht.1
  have h2 : t ≤ l.T := ht.2.trans hb
  exact abs_le.mpr ⟨h1, h2⟩

private lemma ae_eq_NF_vseg {F : ℂ → ℂ} (l : LadderParams) {a b : ℝ}
    (hab : a ≤ b) (ha : -l.T ≤ a) (hb : b ≤ l.T)
    (hF_mero : MeromorphicOn F l.R) :
    (fun t : ℝ ↦ F (1 + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
    (fun t : ℝ ↦ toMeromorphicNFOn F l.R (1 + t * Complex.I)) := by
  have h_uIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have h_ae := toMeromorphicNFOn_eqOn_codiscrete hF_mero
  have h_maps : Set.MapsTo (fun t : ℝ ↦ (1:ℂ) + t * Complex.I) (Set.uIcc a b) l.R := by
    rw [h_uIcc]
    apply Set.MapsTo.mono_right (mapsTo_vseg_Rboundary l ha hb)
    exact LadderParams.Rboundary_subset_R l
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
  have ha_gen : -l.T ≤ a := by
    have hT_pos : 0 < l.T := l.hT
    linarith [ha_nonneg]
  have h_ae : (fun t : ℝ ↦ (G (1 + t * Complex.I) * (x : ℂ) ^ (1 + t * Complex.I)) * Complex.I)
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] H_upper := by
    have h_sum_path := ae_eq_NF_vseg l hab ha_gen hb_le_T (hG_circ_mero.add hG_star_mero)
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
    continuousOn_toMeromorphicNFOn_subset l (Set.Subset.trans Set.inter_subset_left (LadderParams.Rboundary_subset_R l)) (hG_circ_mero.add hG_star_mero) (fun s hs => hG_nopoles s hs.1 hs.2)
  have h_maps_rb : Set.MapsTo (fun t : ℝ ↦ 1 + t * Complex.I) (Set.Icc a b) (l.Rboundary ∩ {s | 0 ≤ s.im}) := by
    intro t ht
    refine ⟨mapsTo_vseg_Rboundary l ha_gen hb_le_T ht, ?_⟩
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, add_zero, mul_zero, zero_add, Set.mem_setOf_eq]
    linarith [ht.1]
  exact (ContinuousOn.comp h_cont_sum_NF (Continuous.continuousOn (by fun_prop)) h_maps_rb).mul
    (continuousOn_cpow_vertical_path hx₀ hx 1 _) |>.mul_const Complex.I

private lemma G_circ_star_no_poles_at_one (l : LadderParams)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour) :
    0 ≤ meromorphicOrderAt G_circ 1 ∧ 0 ≤ meromorphicOrderAt G_star 1 := by
  have h1_contour : (1 : ℂ) ∈ l.admissible_contour := Or.inr ⟨by rfl, ⟨le_rfl, l.hδ.1.le⟩⟩
  have hx₀_pos : 0 < x₀ := by linarith [hx₀]
  have hpow0_mero : MeromorphicAt (fun s : ℂ ↦ (x₀ : ℂ) ^ s) 1 := meromorphicAt_rpow hx₀_pos 1
  have hpow0_order : meromorphicOrderAt (fun s : ℂ ↦ (x₀ : ℂ) ^ s) 1 = 0 := meromorphicOrderAt_rpow hx₀_pos 1
  have h1_R : (1 : ℂ) ∈ l.R := by
    simp only [LadderParams.R, Set.mem_setOf_eq, one_re, one_im, le_refl, true_and]
    rw [abs_zero]
    exact l.hT.le
  have hGc_mero : MeromorphicAt G_circ 1 := hG_circ_mero 1 h1_R
  have hGs_mero : MeromorphicAt G_star 1 := hG_star_mero 1 h1_R
  have hGc_order : 0 ≤ meromorphicOrderAt G_circ 1 :=
    meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn hGc_mero hpow0_mero hpow0_order hGc_contour h1_contour
  have hGs_order : 0 ≤ meromorphicOrderAt G_star 1 :=
    meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn hGs_mero hpow0_mero hpow0_order hGs_contour h1_contour
  exact ⟨hGc_order, hGs_order⟩

private lemma upper_Rboundary_no_poles (l : LadderParams)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour) :
    ∀ s ∈ l.Rboundary, 0 ≤ s.im → 0 ≤ meromorphicOrderAt (G_circ + G_star) s := by
  intro s hs hs_im
  by_cases hs_im_pos : 0 < s.im
  · have hpos_mem : {t : ℂ | 0 < t.im} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hs_im_pos
    have hG_eq : G =ᶠ[nhds s] G_circ + G_star := by
      filter_upwards [hpos_mem] with t ht
      have hsign : (Real.sign t.im : ℂ) = 1 := by simp [Real.sign_of_pos ht]
      simp [hG t, hsign]
    have hG_eq' : G =ᶠ[nhdsWithin s {s}ᶜ] G_circ + G_star := hG_eq.filter_mono nhdsWithin_le_nhds
    rw [← meromorphicOrderAt_congr hG_eq']
    have hG_mero : MeromorphicAt G s :=
      ((hG_circ_mero s (l.Rboundary_subset_R hs)).add (hG_star_mero s (l.Rboundary_subset_R hs))).congr (hG_eq.symm.filter_mono nhdsWithin_le_nhds)
    exact meromorphicOrderAt_nonneg_of_bounded hx₀ hG_mero hG_bdd hs
  · have hs_im_zero : s.im = 0 := by linarith [hs_im, hs_im_pos]
    have hs_re : s.re = 1 := by
      have h_Rbd : s ∈ l.Rboundary := hs
      simp only [LadderParams.Rboundary, Set.mem_setOf_eq] at h_Rbd
      rcases h_Rbd with ⟨hre, _⟩ | ⟨_, him⟩
      · exact hre
      · rw [hs_im_zero, abs_zero] at him
        have hT_gt_zero := l.hT
        linarith [him]
    have hs_eq : s = 1 := by rw [Complex.ext_iff]; simp [hs_re, hs_im_zero]
    obtain ⟨hGc_order, hGs_order⟩ := G_circ_star_no_poles_at_one l hG_circ_mero hG_star_mero hx₀ hGc_contour hGs_contour
    have hGc_mero : MeromorphicAt G_circ s := hG_circ_mero s (l.Rboundary_subset_R hs)
    have hGs_mero : MeromorphicAt G_star s := hG_star_mero s (l.Rboundary_subset_R hs)
    exact meromorphicOrderAt_add_nonneg hGc_mero hGs_mero (Filter.EventuallyEq.refl (nhds s) (G_circ + G_star)) (hs_eq ▸ hGc_order) (hs_eq ▸ hGs_order)

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
  have hG_nopoles : ∀ s ∈ l.Rboundary, 0 ≤ s.im → 0 ≤ meromorphicOrderAt (G_circ + G_star) s :=
    upper_Rboundary_no_poles l hG hG_circ_mero hG_star_mero hx₀ hG_bdd hGc_contour hGs_contour
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

private lemma G_mul_cpow_integrable_vseg_lower (l : LadderParams)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀)
    (hG_nopoles_lower : ∀ s ∈ l.Rboundary, s.im ≤ 0 → 0 ≤ meromorphicOrderAt (G_circ - G_star) s)
    (hx : x₀ < x) (a b : ℝ) (ha_ge_negT : -l.T ≤ a) (hab : a ≤ b) (hb_nonpos : b ≤ 0) :
    IntervalIntegrable (fun t : ℝ ↦ (G (1 + t * Complex.I) * (x : ℂ) ^ (1 + t * Complex.I)) * Complex.I) volume a b := by
  let H_lower := fun (t : ℝ) ↦
    toMeromorphicNFOn (G_circ - G_star) l.R ((1:ℂ) + t * Complex.I) * ((x : ℂ) ^ ((1:ℂ) + t * Complex.I)) * Complex.I
  have hb_gen : b ≤ l.T := hb_nonpos.trans l.hT.le
  have h_mem_ae : ∀ᵐ (t : ℝ) ∂MeasureTheory.volume.restrict (Set.uIoc a b), t < 0 := by
    have h_uIoc : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
    rw [h_uIoc]
    have h1 : ∀ t ∈ Set.Ioc a b, ¬(t < 0) ↔ t = 0 := by
      intro t ht; constructor
      · intro h_not_lt; exact le_antisymm (hb_nonpos.trans' ht.2) (not_lt.mp h_not_lt)
      · intro h_eq; rw [h_eq]; simp
    have h2 : {t ∈ Set.Ioc a b | ¬(t < 0)} ⊆ {0} := by
      intro t ht; rw [Set.mem_singleton_iff]; exact (h1 t ht.1).mp ht.2
    have h3 : MeasureTheory.volume {t ∈ Set.Ioc a b | ¬(t < 0)} = 0 := measure_mono_null h2 (MeasureTheory.measure_singleton 0)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
    have h4 : {a_1 | ¬(a_1 ∈ Set.Ioc a b → a_1 < 0)} = {t ∈ Set.Ioc a b | ¬(t < 0)} := by
      ext t; simp only [Set.mem_Ioc, Set.mem_setOf_eq]; tauto
    rw [h4]
    exact h3
  have h_ae : (fun t : ℝ ↦ G ((1:ℂ) + t * Complex.I) * (x : ℂ) ^ ((1:ℂ) + t * Complex.I) * Complex.I) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] H_lower := by
    filter_upwards [ae_eq_NF_vseg l hab ha_ge_negT hb_gen (hG_circ_mero.sub hG_star_mero), h_mem_ae] with t ht_NF ht_lt
    dsimp [H_lower]
    rw [hG, show (Real.sign ((1:ℂ) + t * Complex.I).im : ℂ) = -1 by simp [Real.sign_of_neg ht_lt]]
    simpa [sub_eq_add_neg] using
      congrArg (fun z => z * (x : ℂ) ^ ((1 : ℂ) + t * Complex.I) * Complex.I) ht_NF
  refine IntervalIntegrable.congr_ae ?_ h_ae.symm
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  have h_cont_sum_NF : ContinuousOn (toMeromorphicNFOn (G_circ - G_star) l.R) (l.Rboundary ∩ {s | s.im ≤ 0}) :=
    continuousOn_toMeromorphicNFOn_subset l
      (Set.Subset.trans Set.inter_subset_left (LadderParams.Rboundary_subset_R l))
      (hG_circ_mero.sub hG_star_mero) (fun s hs => hG_nopoles_lower s hs.1 hs.2)
  have h_maps_rb : Set.MapsTo (fun t : ℝ ↦ 1 + t * Complex.I) (Set.Icc a b) (l.Rboundary ∩ {s | s.im ≤ 0}) := by
    intro t ht
    refine ⟨mapsTo_vseg_Rboundary l ha_ge_negT hb_gen ht, ?_⟩
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, add_zero, mul_zero, zero_add, Set.mem_setOf_eq]
    linarith [ht.2]
  exact (ContinuousOn.comp h_cont_sum_NF (Continuous.continuousOn (by fun_prop)) h_maps_rb).mul
    (continuousOn_cpow_vertical_path hx₀ hx 1 _) |>.mul_const Complex.I

/-- The conjugate-symmetry (Schwarz reflection) condition `F(s̄) = conj (F s)` assumed of `F` in
Proposition 5.2; it makes the derived odd part `G⋆` satisfy `ConjAntisymm`. -/
def ConjSymm (F : ℂ → ℂ) : Prop := ∀ s : ℂ, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)

lemma intVSeg_eq_intCnMinus_add_rectangleIntegral (l : LadderParams) (n : ℕ) (F : ℂ → ℂ)
    (h_integrable1 : IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume (-l.T) (-l.δ))
    (h_integrable2 : IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume (-l.δ) 0) :
    intVSeg 1 (-l.T) 0 F = l.intCnMinus n F + RectangleIntegral F ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) := by
  have h1 : l.intCnMinus n F = (intHSeg (-l.T) 1 (l.σ n) F + intVSeg (l.σ n) (-l.T) (-l.δ) F + intHSeg (-l.δ) (l.σ n) 1 F + intVSeg 1 (-l.δ) 0 F) := rfl
  have h2 : RectangleIntegral F ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) = (intHSeg (-l.T) (l.σ n) 1 F - intHSeg (-l.δ) (l.σ n) 1 F + intVSeg 1 (-l.T) (-l.δ) F - intVSeg (l.σ n) (-l.T) (-l.δ) F) := by
    have hH1 : HIntegral F (l.σ n) 1 (-l.T) = intHSeg (-l.T) (l.σ n) 1 F := rfl
    have hH2 : HIntegral F (l.σ n) 1 (-l.δ) = intHSeg (-l.δ) (l.σ n) 1 F := rfl
    have hV1 : Complex.I * ∫ (y : ℝ) in (-l.T)..(-l.δ), F (1 + ↑y * Complex.I) =
      intVSeg 1 (-l.T) (-l.δ) F := by
      rw [intVSeg, ← smul_eq_mul, ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr (fun y _ ↦ ?_)
      rw [smul_eq_mul, mul_comm]; rfl
    have hV2 : Complex.I * ∫ (y : ℝ) in (-l.T)..(-l.δ), F (↑(l.σ n) + ↑y * Complex.I) =
      intVSeg (l.σ n) (-l.T) (-l.δ) F := by
      rw [intVSeg, ← smul_eq_mul, ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr (fun y _ ↦ ?_)
      rw [smul_eq_mul, mul_comm]
    rw [RectangleIntegral]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, mul_zero,
      sub_zero, add_zero, mul_one, zero_sub]
    dsimp [VIntegral]
    rw [hH1, hH2, hV1, hV2]
  have h_T_cancel : intHSeg (-l.T) 1 (l.σ n) F + intHSeg (-l.T) (l.σ n) 1 F = 0 := by
    rw [intHSeg, intHSeg, intervalIntegral.integral_symm]
    ring
  have h_cancelled : l.intCnMinus n F +
    RectangleIntegral F ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) =
    intVSeg 1 (-l.T) (-l.δ) F + intVSeg 1 (-l.δ) 0 F := by
      rw [h1, h2]
      calc
        _ = (intVSeg 1 (-l.T) (-l.δ) F + intVSeg 1 (-l.δ) 0 F) +
            (intHSeg (-l.T) 1 (l.σ n) F + intHSeg (-l.T) (l.σ n) 1 F) := by ring
        _ = intVSeg 1 (-l.T) (-l.δ) F + intVSeg 1 (-l.δ) 0 F := by rw [h_T_cancel, add_zero]
  have h_adjacent : intVSeg 1 (-l.T) (-l.δ) F + intVSeg 1 (-l.δ) 0 F =
    intVSeg 1 (-l.T) 0 F := by
      rw [intVSeg, intVSeg, intVSeg]; push_cast
      rw [intervalIntegral.integral_add_adjacent_intervals h_integrable1 h_integrable2]
  rw [h_cancelled, h_adjacent]

lemma LadderParams.lowerRectangle_subset_RposBar (l : LadderParams) (n : ℕ) :
    Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ⊆ l.RposBar := by
  intro z hz
  have hδ_le_T : -l.T ≤ -l.δ := by linarith [l.hδ.2, l.hT]
  rcases (mem_Rect
      (z := ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I))
      (w := (1 - (l.δ : ℂ) * Complex.I)) (p := z)
      (zRe_lt_wRe := by simpa using l.hσ n) (zIm_lt_wIm := by simpa using hδ_le_T)).1 hz with
    ⟨hz_re_left, hz_re_right, hz_im_bot, hz_im_top⟩
  simp only [LadderParams.RposBar, Set.mem_setOf_eq, Set.mem_Icc]
  exact ⟨by simpa using hz_re_right, ⟨by simpa using hz_im_bot, by simpa using hz_im_top⟩⟩

lemma lowerRectangle_meromorphicOn (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x) :
    MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I)) := by
  intro s hs
  have hs_RposBar := l.lowerRectangle_subset_RposBar n hs
  have hs_im_neg : s.im < 0 := hs_RposBar.2.2.trans_lt (neg_lt_zero.mpr l.hδ.1)
  have h_eq : (fun t : ℂ ↦ G t * (x : ℂ) ^ t) =ᶠ[nhds s] (fun t : ℂ ↦ (G_circ t - G_star t) * (x : ℂ) ^ t) := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hs_im_neg] with t ht
    rw [hG t, show (Real.sign t.im : ℂ) = -1 by simp [Real.sign_of_neg ht]]
    ring
  refine MeromorphicAt.congr ?_ (h_eq.filter_mono nhdsWithin_le_nhds).symm
  exact ((hG_circ_mero s (l.RposBar_subset_R hs_RposBar)).sub (hG_star_mero s (l.RposBar_subset_R hs_RposBar))).mul (meromorphicAt_rpow (by linarith) s)

private def conj_reflect (G : ℂ → ℂ) : ℂ → ℂ :=
  fun w ↦ starRingEnd ℂ (G (starRingEnd ℂ w))

private lemma conj_reflect_involutive (G : ℂ → ℂ) :
    conj_reflect (conj_reflect G) = G := by
  ext w
  simp [conj_reflect]

-- Conjugation carries neighborhoods at `conj a` back to neighborhoods at `a`.
private lemma tendsto_starRingEnd_nhds {a : ℂ} :
    Filter.Tendsto (fun w : ℂ ↦ starRingEnd ℂ w) (nhds (starRingEnd ℂ a)) (nhds a) := by
  convert (Complex.continuous_conj.continuousAt (x := starRingEnd ℂ a)).tendsto
  exact (starRingEnd_self_apply a).symm

-- Meromorphic order is computed on punctured neighborhoods, so this transport is the key filter step.
private lemma tendsto_starRingEnd_nhdsWithin_ne {a : ℂ} :
    Filter.Tendsto (fun w : ℂ ↦ starRingEnd ℂ w)
      (nhdsWithin (starRingEnd ℂ a) {(starRingEnd ℂ a)}ᶜ) (nhdsWithin a {a}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (tendsto_starRingEnd_nhds (a := a)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    intro h
    apply hw
    simpa using congrArg (starRingEnd ℂ) h

-- Reflection across the real axis turns analytic germs into analytic germs at conjugate points.
private lemma analyticAt_conj_reflect {g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (conj_reflect g) (starRingEnd ℂ a) := by
  rcases hg with ⟨p, hp⟩
  refine ⟨FormalMultilinearSeries.ofScalars ℂ (fun n ↦ starRingEnd ℂ (p.coeff n)), ?_⟩
  rw [hasFPowerSeriesAt_iff']
  rw [hasFPowerSeriesAt_iff'] at hp
  have hp' :
      ∀ᶠ w in nhds (starRingEnd ℂ a),
        HasSum (fun n ↦ ((starRingEnd ℂ w - a) ^ n) • p.coeff n) (g (starRingEnd ℂ w)) :=
    (tendsto_starRingEnd_nhds (a := a)).eventually hp
  filter_upwards [hp'] with w hw
  have hw' :
      HasSum
        (fun n ↦ starRingEnd ℂ ((((starRingEnd ℂ w) - a) ^ n) • p.coeff n))
        (starRingEnd ℂ (g (starRingEnd ℂ w))) :=
    (Complex.hasSum_conj').2 hw
  simpa [conj_reflect, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, map_mul, map_sub,
    starRingEnd_self_apply] using hw'

private lemma meromorphicAt_conj_reflect {G : ℂ → ℂ} {a : ℂ} (hG : MeromorphicAt G a) :
    MeromorphicAt (conj_reflect G) (starRingEnd ℂ a) := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at hG ⊢
  rcases hG with ⟨n, g, hg_an, hg_eq⟩
  refine ⟨n, conj_reflect g, analyticAt_conj_reflect hg_an, ?_⟩
  have hg_eq' :
      ∀ᶠ w in nhdsWithin (starRingEnd ℂ a) {(starRingEnd ℂ a)}ᶜ,
        G (starRingEnd ℂ w) = ((starRingEnd ℂ w) - a) ^ n • g (starRingEnd ℂ w) :=
    (tendsto_starRingEnd_nhdsWithin_ne (a := a)).eventually hg_eq
  filter_upwards [hg_eq'] with w hw
  simpa [conj_reflect, smul_eq_mul, map_mul, map_sub, starRingEnd_self_apply] using
    congrArg (starRingEnd ℂ) hw

private lemma meromorphicAt_conj_reflect_iff {G : ℂ → ℂ} {a : ℂ} :
    MeromorphicAt (conj_reflect G) (starRingEnd ℂ a) ↔ MeromorphicAt G a := by
  constructor
  · intro h
    simpa [conj_reflect_involutive] using
      meromorphicAt_conj_reflect (G := conj_reflect G) (a := starRingEnd ℂ a) h
  · exact meromorphicAt_conj_reflect

-- Reflection preserves the local zero/pole order, so symmetry reduces to eventual equality.
private lemma meromorphicOrderAt_conj_reflect {G : ℂ → ℂ} {a : ℂ} :
    meromorphicOrderAt (conj_reflect G) (starRingEnd ℂ a) = meromorphicOrderAt G a := by
  by_cases hG_mero : MeromorphicAt G a
  · by_cases htop : meromorphicOrderAt G a = ⊤
    · have hzero : ∀ᶠ w in nhdsWithin a {a}ᶜ, G w = 0 := (meromorphicOrderAt_eq_top_iff).1 htop
      have hzero_ref : ∀ᶠ w in nhdsWithin (starRingEnd ℂ a) {(starRingEnd ℂ a)}ᶜ, conj_reflect G w = 0 := by
        have hzero' := (tendsto_starRingEnd_nhdsWithin_ne (a := a)).eventually hzero
        filter_upwards [hzero'] with w hw
        simp [conj_reflect, hw]
      have htop_ref : meromorphicOrderAt (conj_reflect G) (starRingEnd ℂ a) = ⊤ :=
        (meromorphicOrderAt_eq_top_iff).2 hzero_ref
      rw [htop_ref, htop]
    · have hGref_mero : MeromorphicAt (conj_reflect G) (starRingEnd ℂ a) :=
        meromorphicAt_conj_reflect (G := G) (a := a) hG_mero
      obtain ⟨n, hn : meromorphicOrderAt G a = n⟩ := Option.ne_none_iff_exists'.mp htop
      obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hG_mero).1 hn
      have hn_ref : meromorphicOrderAt (conj_reflect G) (starRingEnd ℂ a) = n := by
        apply (meromorphicOrderAt_eq_int_iff hGref_mero).2
        refine ⟨conj_reflect g, analyticAt_conj_reflect hg_an, ?_, ?_⟩
        · dsimp [conj_reflect]
          intro h
          apply hg_ne
          simpa [starRingEnd_self_apply] using congrArg (starRingEnd ℂ) h
        · have hg_eq' := (tendsto_starRingEnd_nhdsWithin_ne (a := a)).eventually hg_eq
          filter_upwards [hg_eq'] with w hw
          simpa [conj_reflect, smul_eq_mul, map_mul, map_sub, starRingEnd_self_apply] using
            congrArg (starRingEnd ℂ) hw
      rw [hn_ref, hn]
  · have hGref_not : ¬ MeromorphicAt (conj_reflect G) (starRingEnd ℂ a) := by
      intro h
      exact hG_mero ((meromorphicAt_conj_reflect_iff (G := G) (a := a)).1 h)
    rw [meromorphicOrderAt_of_not_meromorphicAt hGref_not,
      meromorphicOrderAt_of_not_meromorphicAt hG_mero]

lemma meromorphicOrderAt_starRingEnd {F : ℂ → ℂ} {z : ℂ}
    (hF_symm : ConjSymm F ∨ ConjAntisymm F) :
    meromorphicOrderAt F z = meromorphicOrderAt F (starRingEnd ℂ z) := by
  rcases hF_symm with hF | hF
  · have hreflect : conj_reflect F =ᶠ[nhdsWithin (starRingEnd ℂ z) {(starRingEnd ℂ z)}ᶜ] F := by
      apply Filter.Eventually.of_forall
      intro w
      dsimp [conj_reflect]
      simpa [starRingEnd_self_apply] using congrArg (starRingEnd ℂ) (hF w)
    calc
      meromorphicOrderAt F z = meromorphicOrderAt (conj_reflect F) (starRingEnd ℂ z) := by
        symm
        exact meromorphicOrderAt_conj_reflect (G := F) (a := z)
      _ = meromorphicOrderAt F (starRingEnd ℂ z) := meromorphicOrderAt_congr hreflect
  · have hreflect_neg : conj_reflect F =ᶠ[nhdsWithin (starRingEnd ℂ z) {(starRingEnd ℂ z)}ᶜ] -F := by
      apply Filter.Eventually.of_forall
      intro w
      dsimp [conj_reflect]
      simpa [starRingEnd_self_apply] using congrArg (starRingEnd ℂ) (hF w)
    have h_neg_order :
        meromorphicOrderAt (-F) (starRingEnd ℂ z) = meromorphicOrderAt F (starRingEnd ℂ z) := by
      have hneg_eq : -F = (fun _ : ℂ ↦ (-1 : ℂ)) * F := by
        ext w
        simp
      rw [hneg_eq]
      exact meromorphicOrderAt_mul_of_ne_zero
        (f := F) (g := fun _ : ℂ ↦ (-1 : ℂ))
        (show AnalyticAt ℂ (fun _ : ℂ ↦ (-1 : ℂ)) (starRingEnd ℂ z) from analyticAt_const)
        (by simp)
    calc
      meromorphicOrderAt F z = meromorphicOrderAt (conj_reflect F) (starRingEnd ℂ z) := by
        symm
        exact meromorphicOrderAt_conj_reflect (G := F) (a := z)
      _ = meromorphicOrderAt (-F) (starRingEnd ℂ z) := meromorphicOrderAt_congr hreflect_neg
      _ = meromorphicOrderAt F (starRingEnd ℂ z) := h_neg_order

lemma lowerRectangle_no_poles_boundary (l : LadderParams) (n : ℕ)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hG_circ_symm : ConjSymm G_circ)
    (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x) :
    Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I))
      {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0} := by
  rw [Set.disjoint_left]
  rintro z hz (hz_pole : meromorphicOrderAt _ z < 0)
  have hz_rect := rectangleBorder_subset_rectangle _ _ hz
  have h_rect_R := Set.Subset.trans (l.lowerRectangle_subset_RposBar n) l.RposBar_subset_R
  have hz_R : z ∈ l.R := h_rect_R hz_rect
  have hT_le_delta : -l.T ≤ -l.δ := by linarith [l.hδ.2, l.hT]
  obtain ⟨_, _, hz_im_bot, hz_im_top⟩ :=
    (mem_Rect (by simpa using l.hσ n) (by simpa using hT_le_delta) z).mp hz_rect
  have hz_im_neg : z.im < 0 := lt_of_le_of_lt (by simpa using hz_im_top) (neg_lt_zero.mpr l.hδ.1)
  have abs_zim_le : |z.im| ≤ l.T := by rw [abs_of_neg hz_im_neg]; linarith [show -l.T ≤ z.im by simpa using hz_im_bot]
  have hG_eq : G =ᶠ[nhds z] G_circ - G_star := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz_im_neg] with t ht
    have ht_eq_G := hG t
    rw [show (Real.sign t.im : ℂ) = -1 by simp [Real.sign_of_neg ht]] at ht_eq_G
    change G t = G_circ t - G_star t
    rw [ht_eq_G]
    ring
  have hGc_mero := hG_circ_mero z hz_R
  have hGs_mero := hG_star_mero z hz_R
  have hG_mero := (hGc_mero.sub hGs_mero).congr (hG_eq.symm.filter_mono nhdsWithin_le_nhds)
  have extract_order : ∀ (F : ℂ → ℂ) (S : Set ℂ) (hF_mero : MeromorphicAt F z),
      IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) S → z ∈ S → 0 ≤ meromorphicOrderAt F z :=
    fun F S hF_mero h_bdd hz_S ↦ meromorphicOrderAt_nonneg_of_bounded hx₀ hF_mero h_bdd hz_S
  have combine_orders (hc : 0 ≤ meromorphicOrderAt G_circ z) (hs : 0 ≤ meromorphicOrderAt G_star z) : 0 ≤ meromorphicOrderAt G z :=
    meromorphicOrderAt_add_nonneg hGc_mero hGs_mero.neg hG_eq hc (meromorphicOrderAt_neg_nonneg hGs_mero hs)
  have h_nonneg_G : 0 ≤ meromorphicOrderAt G z := by
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
      Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, mul_one, zero_sub, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.one_re, Complex.one_im, Set.uIcc_of_le (l.hσ n)] at hz
    rcases hz with (((⟨hz_re, hz_im⟩ | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩)
    · exact extract_order G l.Rboundary hG_mero hG_bdd (Or.inr ⟨hz_re.2, by simpa [hz_im] using l.hT.le⟩)
    · cases n with
      | zero => exact extract_order G l.Rboundary hG_mero hG_bdd (Or.inl ⟨by rw [hz_re, l.h0], abs_zim_le⟩)
      | succ n_pred =>
        have hz_L : z ∈ l.L := ⟨n_pred + 1, by omega, hz_re, abs_zim_le⟩
        exact combine_orders (extract_order G_circ l.L hGc_mero hGc_L hz_L) (extract_order G_star l.L hGs_mero hGs_L hz_L)
    · have hw_contour : starRingEnd ℂ z ∈ l.admissible_contour := Or.inl ⟨hz_re.2, by simp [hz_im]⟩
      have hw_pow_mero := meromorphicAt_rpow (show 0 < x₀ by linarith) (starRingEnd ℂ z)
      have hw_pow_order := meromorphicOrderAt_rpow (show 0 < x₀ by linarith) (starRingEnd ℂ z)
      have hz_R_star : starRingEnd ℂ z ∈ l.R := ⟨hz_R.1, by simpa using hz_R.2⟩
      have hGc_order : 0 ≤ meromorphicOrderAt G_circ z := by
        rw [meromorphicOrderAt_starRingEnd (Or.inl hG_circ_symm)]
        exact meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn (hG_circ_mero _ hz_R_star) hw_pow_mero hw_pow_order hGc_contour hw_contour
      have hGs_order : 0 ≤ meromorphicOrderAt G_star z := by
        rw [meromorphicOrderAt_starRingEnd (Or.inr hG_star_symm)]
        exact meromorphicOrderAt_nonneg_of_isBoundedNoPolesOn (hG_star_mero _ hz_R_star) hw_pow_mero hw_pow_order hGs_contour hw_contour
      exact combine_orders hGc_order hGs_order
    · exact extract_order G l.Rboundary hG_mero hG_bdd (Or.inl ⟨hz_re, abs_zim_le⟩)
  rw [show (fun s ↦ G s * (x : ℂ) ^ s) = G * (fun s : ℂ ↦ (x : ℂ) ^ s) from rfl,
    meromorphicOrderAt_mul hG_mero (meromorphicAt_rpow (show 0 < x by linarith) z),
    meromorphicOrderAt_rpow (show 0 < x by linarith) z, add_zero] at hz_pole
  exact not_lt.mpr h_nonneg_G hz_pole

private lemma lowerRectangle_poles_subset_R_minus_RC (l : LadderParams) (n : ℕ) {P : Set ℂ}
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I)) P) :
    Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ∩ P ⊆ (l.R \ l.RC) ∩ P := by
  rintro z ⟨hz_rect, hz_pole⟩
  have hz_not_boundary := fun h ↦ Set.disjoint_left.mp h_no_poles_boundary h hz_pole
  have hz_R : z ∈ l.R := l.RposBar_subset_R (l.lowerRectangle_subset_RposBar n hz_rect)
  obtain ⟨hz_re_left, hz_re_right, -, hz_im_high⟩ :=
    (mem_Rect (by simpa using l.hσ n) (by simpa using show -l.T ≤ -l.δ by linarith [l.hδ.2, l.hT]) z).mp hz_rect
  have hz_im_lt_neg_delta : z.im < -l.δ := by
    refine lt_of_le_of_ne (by simpa using hz_im_high) (fun heq ↦ hz_not_boundary ?_)
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff]
    exact Or.inl <| Or.inr ⟨by rw [Set.uIcc_of_le (by simpa using l.hσ n), Set.mem_Icc]; exact ⟨by simpa using hz_re_left, by simpa using hz_re_right⟩, by simpa using heq⟩
  have hz_not_RC : z ∉ l.RC := fun h_RC ↦ by linarith [h_RC.2, neg_le_abs z.im]
  exact ⟨⟨hz_R, hz_not_RC⟩, hz_pole⟩

lemma lowerRectangleIntegral'_eq_sumResiduesIn (n : ℕ)
    (h_rect_mero : MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I)))
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I))
      {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0})
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R) :
    RectangleIntegral' (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) =
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}) := by
  apply RectangleIntegral'_eq_sumResiduesIn (by simpa using l.hσ n) (by simpa using show -l.T ≤ -l.δ by linarith [l.hδ.2, l.hT]) h_rect_mero h_no_poles_boundary
  · exact Set.Finite.subset hfin (lowerRectangle_poles_subset_R_minus_RC l n h_no_poles_boundary)
  · exact HasSimplePolesOn.mono hsimple (Set.Subset.trans (l.lowerRectangle_subset_RposBar n) l.RposBar_subset_R)

private lemma lowerRectangle_inter_poles_eq (l : LadderParams) (n : ℕ) {P : Set ℂ}
    (h_no_poles_boundary : Disjoint
      (RectangleBorder ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I)) P) :
    Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ∩ P =
      (l.RposBar ∩ {z | l.σ n < z.re}) ∩ P := by
  ext z
  have hnegT_le_negδ : -l.T ≤ -l.δ := by
    linarith [l.hδ.2, l.hT]
  constructor
  · rintro ⟨hz_rect, hz_pole⟩
    have hz_not_boundary :
        z ∉ RectangleBorder ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) :=
      fun h => Set.disjoint_left.mp h_no_poles_boundary h hz_pole
    have hz_re_gt_sigma : l.σ n < z.re := by
      simpa using
        rectangle_left_re_lt_of_mem_of_not_mem_border hz_rect hz_not_boundary
          (by simpa using l.hσ n) (by simpa using hnegT_le_negδ)
    exact ⟨⟨l.lowerRectangle_subset_RposBar n hz_rect, hz_re_gt_sigma⟩, hz_pole⟩
  · rintro ⟨⟨hz_RposBar, hz_re_gt⟩, hz_pole⟩
    have hz_rect :
        z ∈ Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) := by
      rw [mem_Rect (by simpa using l.hσ n) (by simpa using hnegT_le_negδ)]
      exact ⟨by simpa using le_of_lt hz_re_gt, by simpa using hz_RposBar.1,
        by simpa using hz_RposBar.2.1, by simpa using hz_RposBar.2.2⟩
    exact ⟨hz_rect, hz_pole⟩

lemma sumResiduesIn_lowerRectangle_eq_sumResiduesIn_RposBar (l : LadderParams) (n : ℕ) (F : ℂ → ℂ)
    (h_rect_mero : MeromorphicOn F (Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I)))
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I))
      {z | meromorphicOrderAt F z < 0}) :
    sumResiduesIn F (Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt F z < 0}) =
      sumResiduesIn F (l.RposBar ∩ {z | l.σ n < z.re}) := by
  let Rn : Set ℂ := Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I)
  let P : Set ℂ := {z | meromorphicOrderAt F z < 0}
  let S2 : Set ℂ := l.RposBar ∩ {z | l.σ n < z.re}
  have hnegT_le_negδ : -l.T ≤ -l.δ := by
    linarith [l.hδ.2, l.hT]
  have hRn_mero : MeromorphicOn F Rn := by
    simpa [Rn] using h_rect_mero
  have h_set_eq : Rn ∩ P = S2 ∩ P := by
    simpa [Rn, P, S2] using
      (lowerRectangle_inter_poles_eq (l := l) (n := n) (P := P) h_no_poles_boundary)
  have hS2_subset : S2 ⊆ Rn := by
    intro s hs_S2
    have hs_S2' : s ∈ l.RposBar ∩ {z | l.σ n < z.re} := by
      simpa [S2] using hs_S2
    rw [show Rn = Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) by
      rfl]
    rw [mem_Rect (by simpa using l.hσ n) (by simpa using hnegT_le_negδ)]
    exact ⟨by simpa using le_of_lt hs_S2'.2, by simpa using hs_S2'.1.1,
      by simpa using hs_S2'.1.2.1, by simpa using hs_S2'.1.2.2⟩
  exact sumResiduesIn_eq_of_inter_poles_eq_and_subset hRn_mero h_set_eq hS2_subset


private lemma lower_Rboundary_no_poles (l : LadderParams)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour) :
    ∀ s ∈ l.Rboundary, s.im ≤ 0 → 0 ≤ meromorphicOrderAt (G_circ - G_star) s := by
  intro s hs hs_im
  by_cases hs_im_neg : s.im < 0
  · have hneg_mem : {t : ℂ | t.im < 0} ∈ nhds s :=
      (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hs_im_neg
    have hG_eq : G =ᶠ[nhds s] G_circ - G_star := by
      filter_upwards [hneg_mem] with t ht
      have hsign : (Real.sign t.im : ℂ) = -1 := by simp [Real.sign_of_neg ht]
      rw [hG t, hsign]
      change G_circ t + -1 * G_star t = G_circ t - G_star t
      ring
    have hG_eq' : G =ᶠ[nhdsWithin s {s}ᶜ] G_circ - G_star := hG_eq.filter_mono nhdsWithin_le_nhds
    rw [← meromorphicOrderAt_congr hG_eq']
    have hG_mero : MeromorphicAt G s :=
      ((hG_circ_mero s (l.Rboundary_subset_R hs)).sub (hG_star_mero s (l.Rboundary_subset_R hs))).congr (hG_eq.symm.filter_mono nhdsWithin_le_nhds)
    exact meromorphicOrderAt_nonneg_of_bounded hx₀ hG_mero hG_bdd hs
  · have hs_im_zero : s.im = 0 := by linarith [hs_im, hs_im_neg]
    have hs_re : s.re = 1 := by
      have h_Rbd : s ∈ l.Rboundary := hs
      simp only [LadderParams.Rboundary, Set.mem_setOf_eq] at h_Rbd
      rcases h_Rbd with ⟨hre, _⟩ | ⟨_, him⟩
      · exact hre
      · rw [hs_im_zero, abs_zero] at him
        have hT_gt_zero := l.hT
        linarith [him]
    have hs_eq : s = 1 := by rw [Complex.ext_iff]; simp [hs_re, hs_im_zero]
    obtain ⟨hGc_order, hGs_order⟩ := G_circ_star_no_poles_at_one l hG_circ_mero hG_star_mero hx₀ hGc_contour hGs_contour
    have hGc_mero : MeromorphicAt G_circ s := hG_circ_mero s (l.Rboundary_subset_R hs)
    have hGs_mero : MeromorphicAt G_star s := hG_star_mero s (l.Rboundary_subset_R hs)
    have h_sub : G_circ - G_star = G_circ + (-G_star) := rfl
    rw [h_sub]
    have h_neg_order : 0 ≤ meromorphicOrderAt (-G_star) s := by
      have h_neg_eq : -G_star = (fun x => -1) * G_star := by
        ext x; change -(G_star x) = -1 * G_star x; ring
      rw [h_neg_eq]
      have h_order_add := meromorphicOrderAt_mul (f := fun _ => (-1 : ℂ)) (show AnalyticAt ℂ (fun _ => (-1:ℂ)) s from analyticAt_const).meromorphicAt hGs_mero
      rw [h_order_add]
      have h_const : meromorphicOrderAt (fun (x : ℂ) => (-1 : ℂ)) s = 0 := by simp [meromorphicOrderAt_const]
      rw [h_const, zero_add]
      exact hs_eq ▸ hGs_order
    exact meromorphicOrderAt_add_nonneg hGc_mero hGs_mero.neg (Filter.EventuallyEq.refl (nhds s) _) (hs_eq ▸ hGc_order) h_neg_order

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
    (hG_circ_symm : ConjSymm G_circ) (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite)
    (hsimple : HasSimplePolesOn (fun s ↦ G s * (x : ℂ) ^ s) l.R) :
    (2 * (π : ℂ) * Complex.I)⁻¹ * intVSeg 1 (-l.T) 0 (fun s ↦ G s * (x : ℂ) ^ s) =
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCnMinus n (fun s ↦ G s * (x : ℂ) ^ s) +
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.RposBar ∩ {z | l.σ n < z.re}) := by
  have hG_nopoles_lower : ∀ s ∈ l.Rboundary, s.im ≤ 0 → 0 ≤ meromorphicOrderAt (G_circ - G_star) s :=
    lower_Rboundary_no_poles l hG hG_circ_mero hG_star_mero hx₀ hG_bdd hGc_contour hGs_contour
  have h_integrable1 : IntervalIntegrable (fun t : ℝ ↦ (G (1 + t * Complex.I) * (x : ℂ) ^ (1 + t * Complex.I)) * Complex.I) volume (-l.T) (-l.δ) :=
    G_mul_cpow_integrable_vseg_lower l hG hG_circ_mero hG_star_mero hx₀ hG_nopoles_lower hx (-l.T) (-l.δ) (by linarith [l.hT]) (by linarith [l.hδ.2, l.hT]) (by linarith [l.hδ.1])
  have h_integrable2 : IntervalIntegrable (fun t : ℝ ↦ (G (1 + t * Complex.I) * (x : ℂ) ^ (1 + t * Complex.I)) * Complex.I) volume (-l.δ) 0 :=
    G_mul_cpow_integrable_vseg_lower l hG hG_circ_mero hG_star_mero hx₀ hG_nopoles_lower hx (-l.δ) 0 (by linarith [l.hδ.2, l.hT]) (by linarith [l.hδ.1]) le_rfl
  have h_unprimed_eq : intVSeg 1 (-l.T) 0 (fun s ↦ G s * (x : ℂ) ^ s) =
    l.intCnMinus n (fun s ↦ G s * (x : ℂ) ^ s) +
    RectangleIntegral (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) :=
    intVSeg_eq_intCnMinus_add_rectangleIntegral l n (fun s ↦ G s * (x : ℂ) ^ s) h_integrable1 h_integrable2
  have h_int_eq : (2 * (π : ℂ) * Complex.I)⁻¹ * intVSeg 1 (-l.T) 0 (fun s ↦ G s * (x : ℂ) ^ s) =
    (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCnMinus n (fun s ↦ G s * (x : ℂ) ^ s) +
    RectangleIntegral' (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) := by
    rw [h_unprimed_eq, mul_add]
    congr 1
    simp only [smul_eq_mul]
    ring
  have h_rect_subset_RposBar :
      Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ⊆ l.RposBar :=
    l.lowerRectangle_subset_RposBar n
  have h_rect_subset_R :
      Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ⊆ l.R :=
    Set.Subset.trans h_rect_subset_RposBar l.RposBar_subset_R
  have h_rect_mero : MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I)) :=
    lowerRectangle_meromorphicOn n hG hG_circ_mero hG_star_mero hx₀ hx
  have h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I))
    {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0} :=
    lowerRectangle_no_poles_boundary l n hG hG_circ_mero hG_star_mero hG_circ_symm hG_star_symm hx₀ hG_bdd hGc_L hGc_contour hGs_L hGs_contour hx
  have h_residue_thm : RectangleIntegral' (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) =
    sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}) :=
    lowerRectangleIntegral'_eq_sumResiduesIn n h_rect_mero h_no_poles_boundary hfin hsimple
  have h_residue_set_eq : sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}) =
    sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.RposBar ∩ {z | l.σ n < z.re}) :=
    sumResiduesIn_lowerRectangle_eq_sumResiduesIn_RposBar l n (fun s ↦ G s * (x : ℂ) ^ s) h_rect_mero h_no_poles_boundary
  have h_residue : RectangleIntegral' (fun s ↦ G s * (x : ℂ) ^ s) ((l.σ n : ℂ) - (l.T : ℂ) * Complex.I) (1 - (l.δ : ℂ) * Complex.I) =
    sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.RposBar ∩ {z | l.σ n < z.re}) := by
      rw [h_residue_thm, h_residue_set_eq]
  rw [h_int_eq, h_residue]

lemma intCn1Plus_add_intCn1Minus_eq_rectangleIntegral_add_verticalAt (l : LadderParams) (n : ℕ) (F : ℂ → ℂ)
    (h_int_σ1 : IntervalIntegrable (fun t : ℝ ↦ F ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume (-l.T) (-l.δ))
    (h_int_σ2 : IntervalIntegrable (fun t : ℝ ↦ F ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume (-l.δ) l.δ)
    (h_int_σ3 : IntervalIntegrable (fun t : ℝ ↦ F ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume l.δ l.T)
    (h_int_11 : IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume (-l.δ) 0)
    (h_int_12 : IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume 0 l.δ) :
    l.intCn1Plus n F + l.intCn1Minus n F =
    RectangleIntegral F ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) + l.intVerticalAt (l.σ n) F := by
  have h1 : l.intCn1Plus n F = intVSeg 1 0 l.δ F + intHSeg l.δ 1 (l.σ n) F + intVSeg (l.σ n) l.δ l.T F := rfl
  have h2 : l.intCn1Minus n F = intVSeg (l.σ n) (-l.T) (-l.δ) F + intHSeg (-l.δ) (l.σ n) 1 F + intVSeg 1 (-l.δ) 0 F := rfl
  have h3 : RectangleIntegral F ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) = intHSeg (-l.δ) (l.σ n) 1 F - intHSeg l.δ (l.σ n) 1 F + intVSeg 1 (-l.δ) l.δ F - intVSeg (l.σ n) (-l.δ) l.δ F := by
    have hH1 : HIntegral F (l.σ n) 1 (-l.δ) = intHSeg (-l.δ) (l.σ n) 1 F := rfl
    have hH2 : HIntegral F (l.σ n) 1 l.δ = intHSeg l.δ (l.σ n) 1 F := rfl
    have hV1 : Complex.I * ∫ (y : ℝ) in (-l.δ)..l.δ, F (1 + ↑y * Complex.I) =
      intVSeg 1 (-l.δ) l.δ F := by
      rw [intVSeg, ← smul_eq_mul, ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr (fun y _ ↦ ?_)
      rw [smul_eq_mul, mul_comm]; rfl
    have hV2 : Complex.I * ∫ (y : ℝ) in (-l.δ)..l.δ, F (↑(l.σ n) + ↑y * Complex.I) =
      intVSeg (l.σ n) (-l.δ) l.δ F := by
      rw [intVSeg, ← smul_eq_mul, ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr (fun y _ ↦ ?_)
      rw [smul_eq_mul, mul_comm]
    rw [RectangleIntegral]
    simp only [Complex.sub_re, Complex.add_re, Complex.add_im, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, mul_zero, sub_zero, add_zero, mul_one, zero_add, zero_sub]
    dsimp [VIntegral]
    rw [hH1, hH2, hV1, hV2]
  have h4 : l.intVerticalAt (l.σ n) F = intVSeg (l.σ n) (-l.T) l.T F := rfl
  have h5 : intVSeg (l.σ n) (-l.T) (-l.δ) F + intVSeg (l.σ n) (-l.δ) l.δ F + intVSeg (l.σ n) l.δ l.T F = intVSeg (l.σ n) (-l.T) l.T F := by
    rw [intVSeg, intVSeg, intVSeg, intVSeg]
    rw [intervalIntegral.integral_add_adjacent_intervals h_int_σ1 h_int_σ2]
    rw [intervalIntegral.integral_add_adjacent_intervals (IntervalIntegrable.trans h_int_σ1 h_int_σ2) h_int_σ3]
  have h6 : intVSeg 1 (-l.δ) 0 F + intVSeg 1 0 l.δ F = intVSeg 1 (-l.δ) l.δ F := by
    rw [intVSeg, intVSeg, intVSeg]; push_cast
    rw [intervalIntegral.integral_add_adjacent_intervals h_int_11 h_int_12]
  have h7 : intHSeg l.δ 1 (l.σ n) F = - intHSeg l.δ (l.σ n) 1 F := by
    rw [intHSeg, intHSeg, intervalIntegral.integral_symm]
  rw [h1, h2, h3, h4, h7, ← h5, ← h6]
  ring

lemma centralRectangle_subset_RC (l : LadderParams) (n : ℕ) :
    Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) ⊆ l.RC := by
  intro z hz
  rcases (mem_Rect
      (z := ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I))
      (w := (1 + (l.δ : ℂ) * Complex.I))
      (p := z)
      (zRe_lt_wRe := by simpa using l.hσ n)
      (zIm_lt_wIm := by
        simpa only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
          zero_add, add_zero, zero_sub, sub_zero, one_mul, mul_one, neg_le_self_iff] using
          l.hδ.1.le)).1 hz with
    ⟨_, hz_re_right, hz_im_low, hz_im_high⟩
  simp only [LadderParams.RC, Set.mem_setOf_eq]
  refine ⟨by simpa using hz_re_right, ?_⟩
  exact abs_le.mpr ⟨by simpa using hz_im_low, by simpa using hz_im_high⟩

private lemma LadderParams.centralRectangle_subset_R (l : LadderParams) (n : ℕ) :
    Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) ⊆ l.R :=
  Set.Subset.trans (centralRectangle_subset_RC l n) l.RC_subset_R

lemma centralRectangle_meromorphicOn (l : LadderParams) (n : ℕ) (G_circ : ℂ → ℂ) (x : ℝ) (hx₀ : 1 ≤ x)
    (hG_circ_mero : MeromorphicOn G_circ l.R) :
    MeromorphicOn (fun s ↦ G_circ s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)) := by
  refine MeromorphicOn.mul ?_ ?_
  · intro z hz
    exact hG_circ_mero z (l.centralRectangle_subset_R n hz)
  · intro z _
    exact meromorphicAt_rpow (by linarith [hx₀]) z

private lemma mem_RectangleBorder_central_cases (l : LadderParams) (n : ℕ) (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ RectangleBorder ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)) :
    z ∈ l.admissible_contour ∨ (starRingEnd ℂ z) ∈ l.admissible_contour ∨ z ∈ l.L := by
  have h_sigma_le : l.σ n ≤ 1 := l.hσ n
  have h_negδ_le_δ : -l.δ ≤ l.δ := by
    simpa only [neg_le_self_iff] using l.hδ.1.le
  have hδ_le_T : l.δ ≤ l.T := by
    linarith [l.hδ.2, l.hT]
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, mul_zero, add_zero, zero_add,
    sub_zero, zero_sub, mul_one, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Set.uIcc_of_le h_sigma_le, Set.uIcc_of_le h_negδ_le_δ] at hz
  rcases hz with (((⟨hz_re, hz_im⟩ | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩)
  · right
    left
    rw [LadderParams.admissible_contour, Set.mem_setOf_eq]
    left
    constructor
    · rw [starRingEnd_apply, star_def, Complex.conj_re]
      exact hz_re.2
    · rw [starRingEnd_apply, star_def, Complex.conj_im, hz_im]
      simp
  · right
    right
    rw [LadderParams.L, Set.mem_setOf_eq]
    have abs_zim_le : |z.im| ≤ l.T := (abs_le.mpr ⟨hz_im.1, hz_im.2⟩).trans hδ_le_T
    exact ⟨n, hn, hz_re, abs_zim_le⟩
  · left
    rw [LadderParams.admissible_contour, Set.mem_setOf_eq]
    left
    exact ⟨hz_re.2, hz_im⟩
  · by_cases hz_im_nonneg : 0 ≤ z.im
    · left
      rw [LadderParams.admissible_contour, Set.mem_setOf_eq]
      right
      constructor
      · exact hz_re
      · rw [Set.mem_Icc]
        exact ⟨hz_im_nonneg, hz_im.2⟩
    · right
      left
      rw [LadderParams.admissible_contour, Set.mem_setOf_eq]
      right
      have hz_im_neg : z.im < 0 := lt_of_not_ge hz_im_nonneg
      constructor
      · rw [starRingEnd_apply, star_def, Complex.conj_re]
        exact hz_re
      · rw [starRingEnd_apply, star_def, Complex.conj_im, Set.mem_Icc]
        constructor
        · linarith
        · linarith [hz_im.1]

private lemma centralRectangle_boundary_order_nonneg (l : LadderParams) (n : ℕ) (G_circ : ℂ → ℂ) (x x₀ : ℝ)
    (hn : 1 ≤ n)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_circ_symm : ConjSymm G_circ)
    (hx₀ : 1 ≤ x₀)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x) :
    ∀ z ∈ RectangleBorder ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I),
      0 ≤ meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z := by
  have hGc_contour_order :
      ∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt G_circ s :=
    meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.admissible_contour_subset_R hG_circ_mero
      hGc_contour
  have hGc_L_order : ∀ s ∈ l.L, 0 ≤ meromorphicOrderAt G_circ s :=
    meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.L_subset_R hG_circ_mero hGc_L
  intro z hz
  rw [meromorphicOrderAt_mul_cpow_eq (by linarith [hx₀, hx])
    (hG_circ_mero z (l.centralRectangle_subset_R n (rectangleBorder_subset_rectangle _ _ hz)))]
  rcases mem_RectangleBorder_central_cases l n hn hz with hz_contour | hz_star | hz_L
  · exact hGc_contour_order z hz_contour
  · rw [meromorphicOrderAt_starRingEnd (Or.inl hG_circ_symm)]
    exact hGc_contour_order (starRingEnd ℂ z) hz_star
  · exact hGc_L_order z hz_L

private lemma centralRectangle_poles_finite (l : LadderParams) (n : ℕ) (G_circ : ℂ → ℂ) (x : ℝ)
    (h_rect_mero : MeromorphicOn (fun s ↦ G_circ s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I))) :
    (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) ∩
      {z | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}).Finite := by
  have h_rect_compact :
      IsCompact (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)) := by
    apply IsCompact.reProdIm <;> apply isCompact_uIcc
  have hdiv_finite :
      (MeromorphicOn.divisor (fun s ↦ G_circ s * (x : ℂ) ^ s)
        (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I))).support.Finite :=
    (MeromorphicOn.divisor (fun s ↦ G_circ s * (x : ℂ) ^ s)
      (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I))).finiteSupport
        h_rect_compact
  refine Set.Finite.subset hdiv_finite ?_
  intro z hz
  rcases hz with ⟨hz_rect, hz_pole⟩
  have hz_pole_lt : meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0 := by
    simpa only [Set.mem_setOf_eq] using hz_pole
  simp only [Function.mem_support, ne_eq]
  rw [MeromorphicOn.divisor_apply h_rect_mero hz_rect]
  rw [WithTop.untop₀_eq_zero]
  rintro (hz_zero | hz_top)
  · exact hz_pole_lt.ne hz_zero
  · simp [hz_top] at hz_pole_lt

lemma centralRectangle_no_poles_boundary (l : LadderParams) (n : ℕ) (G_circ : ℂ → ℂ) (x x₀ : ℝ)
    (hn : 1 ≤ n)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_circ_symm : ConjSymm G_circ)
    (hx₀ : 1 ≤ x₀)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    : Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I))
      {z | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0} := by
  rw [Set.disjoint_left]
  intro z hz hz_pole
  exact not_lt_of_ge
    (centralRectangle_boundary_order_nonneg l n G_circ x x₀ hn hG_circ_mero hG_circ_symm hx₀
      hGc_L hGc_contour hx z hz)
    (by simpa only [Set.mem_setOf_eq] using hz_pole)

lemma centralRectangleIntegral'_eq_sumResiduesIn (l : LadderParams) (n : ℕ) (G_circ : ℂ → ℂ) (x : ℝ)
    (h_rect_mero : MeromorphicOn (fun s ↦ G_circ s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)))
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)) {z | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0})
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
    RectangleIntegral' (fun s ↦ G_circ s * (x : ℂ) ^ s) ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) =
    sumResiduesIn (fun s ↦ G_circ s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}) := by
  refine RectangleIntegral'_eq_sumResiduesIn (by simpa using l.hσ n)
    (by simpa using show -l.δ ≤ l.δ by linarith [l.hδ.1]) h_rect_mero h_no_poles_boundary
    (centralRectangle_poles_finite l n G_circ x h_rect_mero) ?_
  exact HasSimplePolesOn.mono hsimple_circ (l.centralRectangle_subset_R n)

private lemma centralRectangle_inter_poles_eq (l : LadderParams) (n : ℕ) {P : Set ℂ}
    (h_no_poles_boundary : Disjoint
      (RectangleBorder ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)) P) :
    Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) ∩ P =
      (l.RC ∩ {z | l.σ n < z.re}) ∩ P := by
  ext z
  have hnegδ_le_δ : -l.δ ≤ l.δ := by
    simpa only [neg_le_self_iff] using l.hδ.1.le
  constructor
  · rintro ⟨hz_rect, hz_pole⟩
    have hz_not_boundary :
        z ∉ RectangleBorder ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) :=
      fun h => Set.disjoint_left.mp h_no_poles_boundary h hz_pole
    have hz_re_gt_sigma : l.σ n < z.re := by
      simpa using
        rectangle_left_re_lt_of_mem_of_not_mem_border hz_rect hz_not_boundary
          (by simpa using l.hσ n) (by simpa using hnegδ_le_δ)
    exact ⟨⟨centralRectangle_subset_RC l n hz_rect, hz_re_gt_sigma⟩, hz_pole⟩
  · rintro ⟨⟨hz_RC, hz_re_gt⟩, hz_pole⟩
    have hz_im_bounds := abs_le.mp hz_RC.2
    have hz_rect :
        z ∈ Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) := by
      rw [mem_Rect (by simpa using l.hσ n) (by simpa using hnegδ_le_δ)]
      exact ⟨by simpa using le_of_lt hz_re_gt, by simpa using hz_RC.1,
        by simpa using hz_im_bounds.1, by simpa using hz_im_bounds.2⟩
    exact ⟨hz_rect, hz_pole⟩

lemma sumResiduesIn_centralRectangle_eq_sumResiduesIn_RC (l : LadderParams) (n : ℕ) (G_circ : ℂ → ℂ) (x : ℝ)
    (h_rect_mero : MeromorphicOn (fun s ↦ G_circ s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)))
    (h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)) {z | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}) :
    sumResiduesIn (fun s ↦ G_circ s * (x : ℂ) ^ s) (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt (fun s ↦ G_circ s * (x : ℂ) ^ s) z < 0}) =
      sumResiduesIn (fun s ↦ G_circ s * (x : ℂ) ^ s) (l.RC ∩ {z | l.σ n < z.re}) := by
  let F := fun s ↦ G_circ s * (x : ℂ) ^ s
  let Rn := Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)
  let P := {z | meromorphicOrderAt F z < 0}
  let S2 := l.RC ∩ {z | l.σ n < z.re}
  have hnegδ_le_δ : -l.δ ≤ l.δ := by
    simpa only [neg_le_self_iff] using l.hδ.1.le
  have hRn_mero : MeromorphicOn F Rn := by
    simpa [F, Rn] using h_rect_mero
  have h_set_eq : Rn ∩ P = S2 ∩ P := by
    simpa [F, Rn, P, S2] using
      (centralRectangle_inter_poles_eq (l := l) (n := n) (P := P) h_no_poles_boundary)
  have hS2_subset : S2 ⊆ Rn := by
    intro s hs_S2
    have hs_S2' : s ∈ l.RC ∩ {z | l.σ n < z.re} := by
      simpa [S2] using hs_S2
    have hs_im_bounds := abs_le.mp hs_S2'.1.2
    change s ∈ Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)
    rw [mem_Rect (by simpa using l.hσ n) (by simpa using hnegδ_le_δ)]
    exact ⟨by simpa using le_of_lt hs_S2'.2, by simpa using hs_S2'.1.1,
      by simpa using hs_im_bounds.1, by simpa using hs_im_bounds.2⟩
  exact sumResiduesIn_eq_of_inter_poles_eq_and_subset hRn_mero h_set_eq hS2_subset

-- Helper for integrating on a vertical segment in L
private lemma integrable_vseg_L {F G_circ : ℂ → ℂ} {x₀ x : ℝ} (hF : F = fun s ↦ G_circ s * (x : ℂ) ^ s) (l : LadderParams) (n : ℕ) (hn : 1 ≤ n)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (hG_circ_mero : MeromorphicOn G_circ l.R)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    {a b : ℝ} (hab : a ≤ b) (ha : -l.T ≤ a) (hb : b ≤ l.T) :
    IntervalIntegrable (fun t : ℝ ↦ F ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume a b := by
  rw [hF]
  refine G_circ_mul_cpow_integrable_vseg_general l G_circ hG_circ_mero x₀ x hx₀ hx l.L
    l.L_subset_R (meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.L_subset_R hG_circ_mero
      hGc_L) (l.σ n) a b hab ?_
  rintro t ⟨ht₁, ht₂⟩
  exact ⟨n, hn, by simp, by
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
    rw [abs_le]
    constructor <;> linarith⟩

-- Helper for integrating on the lower half of the Re=1 segment
private lemma integrable_vseg_11 {F G_circ : ℂ → ℂ} {x₀ x : ℝ} (hF : F = fun s ↦ G_circ s * (x : ℂ) ^ s) (l : LadderParams)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (hG_circ_symm : ConjSymm G_circ)
    (hG_circ_mero : MeromorphicOn G_circ l.R)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour) :
    IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume (-l.δ) 0 := by
  rw [hF]
  refine G_circ_mul_cpow_integrable_vseg_general l G_circ hG_circ_mero x₀ x hx₀ hx
    {z | z.re = 1 ∧ z.im ∈ Set.Icc (-l.δ) 0} ?_ ?_ 1 (-l.δ) 0
    (by linarith [l.hδ.1, l.hδ.2, l.hT]) ?_
  · rintro z ⟨hz_re, hz_im⟩
    exact ⟨by simp [hz_re], by
      rw [abs_le]
      constructor
      · linarith [hz_im.1, l.hδ.1, l.hδ.2, l.hT]
      · linarith [hz_im.2, l.hδ.1, l.hδ.2, l.hT]⟩
  · have hGc_contour_order :
        ∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt G_circ s :=
      meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.admissible_contour_subset_R hG_circ_mero
        hGc_contour
    rintro z ⟨hz_re, hz_im⟩
    have hz_star : starRingEnd ℂ z ∈ l.admissible_contour :=
      l.star_mem_admissible_contour_of_re_eq_one_of_im_nonpos hz_re hz_im
    rw [meromorphicOrderAt_starRingEnd (Or.inl hG_circ_symm)]
    exact hGc_contour_order (starRingEnd ℂ z) hz_star
  · intro t ht
    exact ⟨by simp, by
      simpa only [ofReal_one, add_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
        mul_zero, add_zero, zero_add, Set.mem_Icc] using ht⟩

-- Helper for integrating on the upper half of the Re=1 segment
private lemma integrable_vseg_12 {F G_circ : ℂ → ℂ} {x₀ x : ℝ} (hF : F = fun s ↦ G_circ s * (x : ℂ) ^ s) (l : LadderParams)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x)
    (hG_circ_mero : MeromorphicOn G_circ l.R)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour) :
    IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume 0 l.δ := by
  rw [hF]
  refine G_circ_mul_cpow_integrable_vseg_general l G_circ hG_circ_mero x₀ x hx₀ hx
    l.admissible_contour l.admissible_contour_subset_R
    (meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.admissible_contour_subset_R hG_circ_mero
      hGc_contour) 1 0 l.δ (by linarith [l.hδ.1, l.hδ.2, l.hT]) ?_
  intro t ht
  exact l.mem_admissible_contour_of_re_eq_one_of_im_nonneg (z := 1 + t * Complex.I) (by simp) (by
    simpa only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add, Set.mem_Icc] using ht)

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
theorem lemma_5_1_c (n : ℕ) (hn : 1 ≤ n)
    (hG_circ_mero : MeromorphicOn G_circ l.R)
    (hG_circ_symm : ConjSymm G_circ)
    (hx₀ : 1 ≤ x₀)
    (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x)
    (hsimple_circ : HasSimplePolesOn (fun s ↦ G_circ s * (x : ℂ) ^ s) l.R) :
    (2 * (π : ℂ) * Complex.I)⁻¹ *
        (l.intCn1Plus n (fun s ↦ G_circ s * (x : ℂ) ^ s) +
          l.intCn1Minus n (fun s ↦ G_circ s * (x : ℂ) ^ s)) =
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intVerticalAt (l.σ n) (fun s ↦ G_circ s * (x : ℂ) ^ s) +
      sumResiduesIn (fun s ↦ G_circ s * (x : ℂ) ^ s) (l.RC ∩ {z | l.σ n < z.re}) := by
  let F := fun s ↦ G_circ s * (x : ℂ) ^ s
  have hF : F = fun s ↦ G_circ s * (x : ℂ) ^ s := rfl
  have h_int_σ1 : IntervalIntegrable (fun t : ℝ ↦ F ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume (-l.T) (-l.δ) :=
    integrable_vseg_L hF l n hn hx₀ hx hG_circ_mero hGc_L (by linarith [l.hδ.1, l.hδ.2, l.hT]) (by linarith) (by linarith [l.hδ.1, l.hδ.2, l.hT])
  have h_int_σ2 : IntervalIntegrable (fun t : ℝ ↦ F ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume (-l.δ) l.δ :=
    integrable_vseg_L hF l n hn hx₀ hx hG_circ_mero hGc_L (by linarith [l.hδ.1, l.hδ.2, l.hT]) (by linarith [l.hδ.1, l.hδ.2, l.hT]) (by linarith [l.hδ.1, l.hδ.2, l.hT])
  have h_int_σ3 : IntervalIntegrable (fun t : ℝ ↦ F ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume l.δ l.T :=
    integrable_vseg_L hF l n hn hx₀ hx hG_circ_mero hGc_L (by linarith [l.hδ.1, l.hδ.2, l.hT]) (by linarith [l.hδ.1, l.hδ.2, l.hT]) (by linarith)
  have h_int_11 : IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume (-l.δ) 0 :=
    integrable_vseg_11 hF l hx₀ hx hG_circ_symm hG_circ_mero hGc_contour
  have h_int_12 : IntervalIntegrable (fun t : ℝ ↦ F (1 + t * Complex.I) * Complex.I) volume 0 l.δ :=
    integrable_vseg_12 hF l hx₀ hx hG_circ_mero hGc_contour
  have h_rect_mero : MeromorphicOn F (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)) :=
    centralRectangle_meromorphicOn l n G_circ x (le_trans hx₀ (le_of_lt hx)) hG_circ_mero
  have h_no_poles_boundary : Disjoint (RectangleBorder ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I)) {z | meromorphicOrderAt F z < 0} :=
    centralRectangle_no_poles_boundary l n G_circ x x₀ hn hG_circ_mero hG_circ_symm hx₀ hGc_L hGc_contour hx
  have h_int_eq : l.intCn1Plus n F + l.intCn1Minus n F =
      RectangleIntegral F ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) + l.intVerticalAt (l.σ n) F :=
    intCn1Plus_add_intCn1Minus_eq_rectangleIntegral_add_verticalAt l n F h_int_σ1 h_int_σ2 h_int_σ3 h_int_11 h_int_12
  have h_residue_thm : RectangleIntegral' F ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) =
      sumResiduesIn F (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt F z < 0}) :=
    centralRectangleIntegral'_eq_sumResiduesIn l n G_circ x h_rect_mero h_no_poles_boundary hsimple_circ
  have h_residue_set_eq : sumResiduesIn F (Rectangle ((l.σ n : ℂ) - (l.δ : ℂ) * Complex.I) (1 + (l.δ : ℂ) * Complex.I) ∩ {z | meromorphicOrderAt F z < 0}) =
      sumResiduesIn F (l.RC ∩ {z | l.σ n < z.re}) :=
    sumResiduesIn_centralRectangle_eq_sumResiduesIn_RC l n G_circ x h_rect_mero h_no_poles_boundary
  have h_residue := h_residue_thm.trans h_residue_set_eq
  rw [h_int_eq, mul_add, ← h_residue, RectangleIntegral', smul_eq_mul]
  ring_nf; simp; rfl

lemma conj_intVSeg_of_antisymm (c a b : ℝ) (F : ℂ → ℂ) (hF : ∀ s, starRingEnd ℂ (F s) = -F (starRingEnd ℂ s)) :
    starRingEnd ℂ (intVSeg c a b F) = intVSeg c (-b) (-a) F := by
  unfold intVSeg
  rw [← intervalIntegral_conj]
  have h_integrand : ∀ t : ℝ, starRingEnd ℂ (F (↑c + ↑t * I) * I) = F (↑c + ↑(-t) * I) * I := by
    intro t
    rw [map_mul, conj_I]
    have h1 : starRingEnd ℂ (↑c + ↑t * I) = ↑c + ↑(-t) * I := by
      rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
      push_cast
      ring
    have h2 := hF (↑c + ↑t * I)
    rw [h1] at h2
    rw [h2]
    ring
  simp_rw [h_integrand]
  rw [← intervalIntegral.integral_comp_neg]

lemma conj_intHSeg_of_antisymm (h a b : ℝ) (F : ℂ → ℂ) (hF : ∀ s, starRingEnd ℂ (F s) = -F (starRingEnd ℂ s)) :
    starRingEnd ℂ (intHSeg h a b F) = intHSeg (-h) b a F := by
  unfold intHSeg
  rw [← intervalIntegral_conj]
  have h_integrand : ∀ t : ℝ, starRingEnd ℂ (F (↑t + ↑h * I)) = - F (↑t + ↑(-h) * I) := by
    intro t
    have h1 : starRingEnd ℂ (↑t + ↑h * I) = ↑t + ↑(-h) * I := by
      rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
      push_cast
      ring
    have h2 := hF (↑t + ↑h * I)
    rw [h1] at h2
    rw [h2]
  simp_rw [h_integrand]
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_neg, neg_neg]

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
theorem lemma_5_1_d (n : ℕ) (hG_star_symm : ConjAntisymm G_star)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x) :
    l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s) -
        l.intCn1Minus n (fun s ↦ G_star s * (x : ℂ) ^ s) =
      2 * Complex.I * ((l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im : ℂ) := by
  have hF : ∀ s, starRingEnd ℂ (G_star s * (x : ℂ) ^ s) = - (G_star (starRingEnd ℂ s) * (x : ℂ) ^ (starRingEnd ℂ s)) := by
    intro s
    rw [map_mul]
    have h_x_symm : starRingEnd ℂ ((x:ℂ)^s) = (x:ℂ)^(starRingEnd ℂ s) := by
      have hx_pos : 0 ≤ x := by linarith [hx₀, hx]
      have harg : (x : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hx_pos]
        exact Real.pi_ne_zero.symm
      have h1 := Complex.cpow_conj (x : ℂ) s harg
      rw [h1, conj_ofReal]
    rw [h_x_symm]
    have hG_symm := hG_star_symm s
    rw [hG_symm]
    ring
  have h_plus_minus : starRingEnd ℂ (l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)) = l.intCn1Minus n (fun s ↦ G_star s * (x : ℂ) ^ s) := by
    unfold LadderParams.intCn1Plus LadderParams.intCn1Minus
    rw [map_add, map_add]
    have h1 := conj_intHSeg_of_antisymm l.δ 1 (l.σ n) (fun s ↦ G_star s * (x : ℂ) ^ s) hF
    have h2 := conj_intVSeg_of_antisymm 1 0 l.δ (fun s ↦ G_star s * (x : ℂ) ^ s) hF
    have h3 := conj_intVSeg_of_antisymm (l.σ n) l.δ l.T (fun s ↦ G_star s * (x : ℂ) ^ s) hF
    rw [h1, h2, h3]
    ring_nf
  have h_sub : l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s) - l.intCn1Minus n (fun s ↦ G_star s * (x : ℂ) ^ s) =
      l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s) - starRingEnd ℂ (l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)) := by
    rw [h_plus_minus]
  rw [h_sub, Complex.sub_conj]
  simp; ring_nf

private lemma aestronglyMeasurable_horizontal_path_mul_cpow_of_meromorphic
    (l : LadderParams) (F : ℂ → ℂ)
    (x₀ x h : ℝ) (hx₀ : 1 ≤ x₀) (hx : x₀ < x)
    (hS_sub : {z : ℂ | z.re ≤ 1 ∧ z.im = h} ⊆ l.R)
    (hF_mero : MeromorphicOn F l.R)
    (h_order : ∀ z ∈ {z : ℂ | z.re ≤ 1 ∧ z.im = h}, 0 ≤ meromorphicOrderAt F z) :
    AEStronglyMeasurable (fun r : ℝ ↦ F (r + h * Complex.I) * (x : ℂ) ^ (r + h * Complex.I))
      (MeasureTheory.volume.restrict (Set.Iic 1)) := by
  let γ : ℝ → ℂ := fun r ↦ r + h * Complex.I
  have hγ_inj : Function.Injective γ := fun _ _ hEq ↦ by simpa [γ] using congrArg Complex.re hEq
  let S_h : Set ℂ := {z : ℂ | z.re ≤ 1 ∧ z.im = h}
  let Fnf : ℂ → ℂ := toMeromorphicNFOn F l.R
  have hF_nf : MeromorphicNFOn Fnf l.R := by
    simpa [Fnf] using (meromorphicNFOn_toMeromorphicNFOn F l.R)
  have hS_h_sub : S_h ⊆ l.R := by
    intro z hz
    exact hS_sub (by simpa [S_h] using hz)
  have hF_cont : ContinuousOn Fnf S_h := by
    exact continuousOn_toMeromorphicNFOn_subset l hS_h_sub hF_mero (by
      intro z hz
      exact h_order z (by simpa [S_h] using hz))
  have h_path_maps : Set.MapsTo γ (Set.Iic 1) S_h := fun r hr ↦ ⟨by simpa [γ] using hr, by simp [γ]⟩
  have h_proxy_meas :
      AEStronglyMeasurable (fun r : ℝ ↦ Fnf (γ r) * (x : ℂ) ^ (γ r))
        (MeasureTheory.volume.restrict (Set.Iic 1)) := by
    exact (ContinuousOn.comp hF_cont
      (Continuous.continuousOn (Complex.continuous_ofReal.add continuous_const)) h_path_maps).mul
      (continuousOn_cpow_horizontal_path hx₀ hx h (Set.Iic 1)) |>.aestronglyMeasurable
        measurableSet_Iic
  have h_eq_ae :
      (fun r : ℝ ↦ F (γ r) * (x : ℂ) ^ (γ r)) =ᵐ[MeasureTheory.volume.restrict (Set.Iic 1)]
        (fun r : ℝ ↦ Fnf (γ r) * (x : ℂ) ^ (γ r)) := by
    have h_good : ∀ᵐ r ∂ MeasureTheory.volume.restrict (Set.Iic 1), r ∉ γ ⁻¹' ({z : ℂ | AnalyticAt ℂ F z}ᶜ ∩ l.R) := by
      rw [ae_iff]
      simpa using! (hF_mero.countable_compl_analyticAt_inter.preimage hγ_inj).measure_zero (MeasureTheory.volume.restrict (Set.Iic 1))
    filter_upwards [h_good, MeasureTheory.ae_restrict_mem measurableSet_Iic] with r hr_good hr
    have hz_Sh : γ r ∈ S_h := h_path_maps hr
    have hz_R : γ r ∈ l.R := hS_h_sub hz_Sh
    have hF_analytic : AnalyticAt ℂ F (γ r) := by simpa using fun hz_compl ↦ hr_good ⟨hz_compl, hz_R⟩
    dsimp [Fnf]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hF_mero hz_R, toMeromorphicNFAt_eq_self.2 hF_analytic.meromorphicNFAt]
  exact AEStronglyMeasurable.congr h_proxy_meas h_eq_ae.symm

private lemma aestronglyMeasurable_hray_of_meromorphic (l : LadderParams) (F : ℂ → ℂ)
    (x₀ x h : ℝ) (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (h_abs_h : |h| = l.T)
    (hF_mero : MeromorphicOn F l.R)
    (h_order : ∀ z ∈ l.Rboundary, z.im = h → 0 ≤ meromorphicOrderAt F z) :
    AEStronglyMeasurable (fun r : ℝ ↦ F (r + h * Complex.I) * (x : ℂ) ^ (r + h * Complex.I))
      (MeasureTheory.volume.restrict (Set.Iic 1)) := by
  refine aestronglyMeasurable_horizontal_path_mul_cpow_of_meromorphic
    l F x₀ x h hx₀ hx ?_ hF_mero ?_
  · intro z hz
    have hz_Rbd : z ∈ l.Rboundary := by
      right
      exact ⟨hz.1, by rw [hz.2]; exact h_abs_h⟩
    exact l.Rboundary_subset_R hz_Rbd
  · intro z hz
    have hz_Rbd : z ∈ l.Rboundary := by
      right
      exact ⟨hz.1, by rw [hz.2]; exact h_abs_h⟩
    exact h_order z hz_Rbd hz.2

private lemma norm_G_mul_cpow_le_of_base_bound (G : ℂ → ℂ) (x₀ x h r M : ℝ)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x)
    (hM : ‖G ((r : ℂ) + h * Complex.I) * (x₀ : ℂ) ^ ((r : ℂ) + h * Complex.I)‖ ≤ M) :
    ‖G ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖
      ≤ max M 0 * Real.exp (Real.log (x / x₀) * r) := by
  let C : ℝ := max M 0
  let z : ℂ := (r : ℂ) + h * Complex.I
  have h_bdd : ‖G z * (x₀ : ℂ) ^ z‖ ≤ C := by
    simpa [C, z] using hM.trans (le_max_left M 0)
  have hx₀_pos : 0 < x₀ := by linarith
  have hx_pos : 0 < x := by linarith
  have hratio_pos : 0 < x / x₀ := div_pos hx_pos hx₀_pos
  have hratio_nonneg : 0 ≤ x / x₀ := hratio_pos.le
  have hnorm_x : ‖(x : ℂ) ^ z‖ = x ^ r := by
    dsimp [z]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    simp
  have hnorm_x₀ : ‖(x₀ : ℂ) ^ z‖ = x₀ ^ r := by
    dsimp [z]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx₀_pos]
    simp
  have h_bdd' : ‖G z‖ * x₀ ^ r ≤ C := by
    simpa [norm_mul, hnorm_x₀] using h_bdd
  have hx_split : x₀ * (x / x₀) = x := by
    field_simp [hx₀_pos.ne']
  have hpow_split : x ^ r = x₀ ^ r * (x / x₀) ^ r := by
    conv_lhs => rw [← hx_split]
    rw [Real.mul_rpow hx₀_pos.le hratio_nonneg]
  have hratio_exp : (x / x₀) ^ r = Real.exp (Real.log (x / x₀) * r) := by
    rw [Real.rpow_def_of_pos hratio_pos]
  calc ‖G z * (x : ℂ) ^ z‖ = ‖G z‖ * x₀ ^ r * (x / x₀) ^ r := by rw [norm_mul, hnorm_x, hpow_split]; ring
    _ ≤ C * (x / x₀) ^ r := mul_le_mul_of_nonneg_right h_bdd' (Real.rpow_nonneg hratio_nonneg _)
    _ = C * Real.exp (Real.log (x / x₀) * r) := by rw [hratio_exp]

private lemma bound_G_mul_cpow_hray (l : LadderParams) (G : ℂ → ℂ)
    (x₀ x h M : ℝ) (hx₀ : 1 ≤ x₀) (hx : x₀ < x)
    (h_abs_h : |h| = l.T)
    (hM : ∀ z ∈ l.Rboundary, ‖G z * (x₀ : ℂ) ^ z‖ ≤ M)
    (r : ℝ) (hr : r ≤ 1) :
    ‖G (r + h * Complex.I) * (x : ℂ) ^ (r + h * Complex.I)‖ ≤ max M 0 * Real.exp (Real.log (x / x₀) * r) := by
  refine norm_G_mul_cpow_le_of_base_bound G x₀ x h r M hx₀ hx ?_
  exact hM _ (Or.inr ⟨by simpa using hr, by simpa using h_abs_h⟩)

private lemma G_mul_cpow_integrable_hray (l : LadderParams)
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R)
    (x₀ x h : ℝ) (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (h_abs_h : |h| = l.T)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour) :
    IntegrableOnHRay h 1 (fun s ↦ G s * (x : ℂ) ^ s) := by
  unfold IntegrableOnHRay
  obtain ⟨M, hM⟩ := hG_bdd
  let C : ℝ := max M 0
  have hx₀_pos : 0 < x₀ := by linarith
  have hx_pos : 0 < x := by linarith
  have hratio_pos : 0 < x / x₀ := div_pos hx_pos hx₀_pos
  have hlog_ratio_pos : 0 < Real.log (x / x₀) := Real.log_pos (by rw [one_lt_div hx₀_pos]; linarith)
  have h_int_bound : IntegrableOn (fun r : ℝ ↦ C * Real.exp (Real.log (x / x₀) * r)) (Set.Iic 1) :=
    (integrableOn_exp_mul_Iic hlog_ratio_pos 1).const_mul C
  have h_meas :
      AEStronglyMeasurable (fun r : ℝ ↦ G (r + h * Complex.I) * (x : ℂ) ^ (r + h * Complex.I))
        (MeasureTheory.volume.restrict (Set.Iic 1)) := by
    by_cases hh_pos : 0 < h
    · let F := G_circ + G_star
      have hF_mero : MeromorphicOn F l.R := hG_circ_mero.add hG_star_mero
      have h_order : ∀ z ∈ l.Rboundary, z.im = h → 0 ≤ meromorphicOrderAt F z := fun z hz_Rbd hz_im ↦
        upper_Rboundary_no_poles (l := l) (G := G) (G_circ := G_circ) (G_star := G_star) (x₀ := x₀) hG hG_circ_mero hG_star_mero hx₀ ⟨M, hM⟩ hGc_contour hGs_contour z hz_Rbd (by rw [hz_im]; exact hh_pos.le)
      have hF_meas := aestronglyMeasurable_hray_of_meromorphic l F x₀ x h hx₀ hx h_abs_h hF_mero h_order
      exact AEStronglyMeasurable.congr hF_meas <| ae_of_all _ fun r ↦ by
        have hsign : (Real.sign (r + h * Complex.I).im : ℂ) = 1 := by simp [Real.sign_of_pos hh_pos]
        calc F (r + h * Complex.I) * (x : ℂ) ^ (r + h * Complex.I)
          _ = (G_circ (r + h * Complex.I) + 1 * G_star (r + h * Complex.I)) * (x : ℂ) ^ (r + h * Complex.I) := by unfold F; simp
          _ = (G_circ (r + h * Complex.I) + (Real.sign (r + h * Complex.I).im : ℂ) * G_star (r + h * Complex.I)) * (x : ℂ) ^ (r + h * Complex.I) := by rw [hsign]
          _ = G (r + h * Complex.I) * (x : ℂ) ^ (r + h * Complex.I) := by rw [← hG (r + h * Complex.I)]
    · have hh_neg : h < 0 := lt_of_le_of_ne (not_lt.mp hh_pos) (fun hh_zero ↦ by rw [hh_zero, abs_zero] at h_abs_h; linarith [l.hT])
      let F := G_circ - G_star
      have hF_mero : MeromorphicOn F l.R := hG_circ_mero.sub hG_star_mero
      have h_order : ∀ z ∈ l.Rboundary, z.im = h → 0 ≤ meromorphicOrderAt F z := fun z hz_Rbd hz_im ↦
        lower_Rboundary_no_poles (l := l) (G := G) (G_circ := G_circ) (G_star := G_star) (x₀ := x₀) hG hG_circ_mero hG_star_mero hx₀ ⟨M, hM⟩ hGc_contour hGs_contour z hz_Rbd (by rw [hz_im]; exact hh_neg.le)
      have hF_meas := aestronglyMeasurable_hray_of_meromorphic l F x₀ x h hx₀ hx h_abs_h hF_mero h_order
      exact AEStronglyMeasurable.congr hF_meas <| ae_of_all _ fun r ↦ by
        have hsign : (Real.sign (r + h * Complex.I).im : ℂ) = -1 := by simp [Real.sign_of_neg hh_neg]
        calc F (r + h * Complex.I) * (x : ℂ) ^ (r + h * Complex.I)
          _ = (G_circ (r + h * Complex.I) + (-1) * G_star (r + h * Complex.I)) * (x : ℂ) ^ (r + h * Complex.I) := by unfold F; simp; ring_nf; simp
          _ = (G_circ (r + h * Complex.I) + (Real.sign (r + h * Complex.I).im : ℂ) * G_star (r + h * Complex.I)) * (x : ℂ) ^ (r + h * Complex.I) := by rw [hsign]
          _ = G (r + h * Complex.I) * (x : ℂ) ^ (r + h * Complex.I) := by rw [← hG (r + h * Complex.I)]
  refine h_int_bound.mono' h_meas <| (ae_restrict_iff' measurableSet_Iic).mpr <| ae_of_all _ (fun r hr ↦
    bound_G_mul_cpow_hray l G x₀ x h M hx₀ hx h_abs_h (fun z hz => (hM z hz).1) r hr)

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
    (hG_circ_mero : MeromorphicOn G_circ l.R) (hG_star_mero : MeromorphicOn G_star l.R) (hx₀ : 1 ≤ x₀)
    (hG_bdd : IsBoundedNoPolesOn (fun s ↦ G s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hGc_contour : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour)
    (hx : x₀ < x) :
    Filter.Tendsto
      (fun n ↦ intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) +
        intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s))
      Filter.atTop (nhds (l.intCinf (fun s ↦ G s * (x : ℂ) ^ s))) := by
  have h_int_top : IntegrableOnHRay l.T 1 (fun s ↦ G s * (x : ℂ) ^ s) :=
    G_mul_cpow_integrable_hray l hG hG_circ_mero hG_star_mero x₀ x l.T hx₀ hx (abs_of_nonneg l.hT.le) hG_bdd hGc_contour hGs_contour
  have h_int_bot : IntegrableOnHRay (-l.T) 1 (fun s ↦ G s * (x : ℂ) ^ s) :=
    G_mul_cpow_integrable_hray l hG hG_circ_mero hG_star_mero x₀ x (-l.T) hx₀ hx (by rw [abs_of_nonpos (neg_nonpos.mpr l.hT.le)]; ring) hG_bdd hGc_contour hGs_contour
  have h_symm : ∀ n, intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s) = - intHSeg (-l.T) (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) :=
    fun n ↦ by unfold intHSeg; rw [intervalIntegral.integral_symm]
  have h_seq_eq : (fun n ↦ intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) + intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s)) =
      (fun n ↦ intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) - intHSeg (-l.T) (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s)) :=
    funext fun n ↦ by rw [h_symm n, sub_eq_add_neg]
  have h_tendsto_top := MeasureTheory.intervalIntegral_tendsto_integral_Iic 1 h_int_top l.hlim
  have h_tendsto_bot := MeasureTheory.intervalIntegral_tendsto_integral_Iic 1 h_int_bot l.hlim
  rw [h_seq_eq]
  exact h_tendsto_top.sub h_tendsto_bot

private lemma intVSeg_tendsto_zero_of_bounded_on_L (l : LadderParams) (F : ℂ → ℂ)
    (x₀ x a b : ℝ) (hx₀ : 1 ≤ x₀) (hx : x₀ < x)
    (ha_abs : |a| ≤ l.T) (hb_le : b ≤ l.T) (hab : a ≤ b)
    (hF_L : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.L) :
    Filter.Tendsto (fun n ↦ intVSeg (l.σ n) a b (fun s ↦ F s * (x : ℂ) ^ s))
      Filter.atTop (nhds (0 : ℂ)) := by
  obtain ⟨M, hM⟩ := hF_L
  let C : ℝ := max M 0
  have hx₀_pos : 0 < x₀ := by linarith
  have hx_pos : 0 < x := by linarith
  have hratio_pos : 0 < x / x₀ := div_pos hx_pos hx₀_pos
  have hratio_nonneg : 0 ≤ x / x₀ := hratio_pos.le
  have hratio_gt_one : 1 < x / x₀ := by
    rw [one_lt_div hx₀_pos]
    linarith
  have h_decay : Filter.Tendsto (fun n ↦ (|b - a| * C) * (x / x₀) ^ (l.σ n))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul (|b - a| * C) <|
        (tendsto_rpow_atBot_of_base_gt_one (x / x₀) hratio_gt_one).comp l.hlim
  have h_eventual_bound : ∀ᶠ n in Filter.atTop,
    ‖intVSeg (l.σ n) a b (fun s ↦ F s * (x : ℂ) ^ s)‖ ≤ (|b - a| * C) * (x / x₀) ^ (l.σ n) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h_pointwise : ∀ t ∈ Set.Icc a b, ‖(F ((l.σ n : ℂ) + t * Complex.I) * (x : ℂ) ^ ((l.σ n : ℂ) + t * Complex.I)) * Complex.I‖
      ≤ C * (x / x₀) ^ (l.σ n) := fun t ht ↦ by
      let z : ℂ := (l.σ n : ℂ) + t * Complex.I
      have ht_abs : |t| ≤ l.T := by
        by_cases ht_nonneg : 0 ≤ t
        · rw [abs_of_nonneg ht_nonneg]
          exact le_trans ht.2 hb_le
        · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
          have ha_neg : a < 0 := lt_of_le_of_lt ht.1 ht_neg
          rw [abs_of_neg ht_neg]
          calc
            -t ≤ -a := neg_le_neg ht.1
            _ = |a| := by rw [abs_of_neg ha_neg]
            _ ≤ l.T := ha_abs
      have hz_L : z ∈ l.L := ⟨n, hn, by simp [z], by simpa [z] using ht_abs⟩
      have h_bdd : ‖F z * (x₀ : ℂ) ^ z‖ ≤ C := (hM z hz_L).1.trans (le_max_left _ _)
      have hnorm_x : ‖(x : ℂ) ^ z‖ = x ^ (l.σ n) := by
        dsimp [z]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
        simp
      have hnorm_x₀ : ‖(x₀ : ℂ) ^ z‖ = x₀ ^ (l.σ n) := by
        dsimp [z]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx₀_pos]
        simp
      have h_bdd' : ‖F z‖ * x₀ ^ (l.σ n) ≤ C := by
        simpa [norm_mul, hnorm_x₀] using h_bdd
      have hpow_split : x ^ (l.σ n) = x₀ ^ (l.σ n) * (x / x₀) ^ (l.σ n) := by
        conv_lhs => rw [← show x₀ * (x / x₀) = x by field_simp [hx₀_pos.ne']]
        rw [Real.mul_rpow hx₀_pos.le hratio_nonneg]
      calc
        ‖(F z * (x : ℂ) ^ z) * Complex.I‖ = ‖F z‖ * x₀ ^ (l.σ n) * (x / x₀) ^ (l.σ n) := by
          rw [norm_mul, norm_mul, hnorm_x, hpow_split]
          simp
          ring
        _ ≤ C * (x / x₀) ^ (l.σ n) :=
          mul_le_mul_of_nonneg_right h_bdd' (Real.rpow_nonneg hratio_nonneg _)
    unfold intVSeg
    calc
      ‖∫ t in a..b, (F ((l.σ n : ℂ) + t * Complex.I) * (x : ℂ) ^ ((l.σ n : ℂ) + t * Complex.I)) *
          Complex.I‖ ≤ (C * (x / x₀) ^ (l.σ n)) * |b - a| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦
            let htIoc : t ∈ Set.Ioc a b := by simpa [Set.uIoc_of_le hab] using ht
            h_pointwise t ⟨htIoc.1.le, htIoc.2⟩
      _ = (|b - a| * C) * (x / x₀) ^ (l.σ n) := by
        rw [abs_sub_comm]; ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n ↦ norm_nonneg _) h_eventual_bound h_decay

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
theorem lemma_5_1_f (hx₀ : 1 ≤ x₀) (hx : x₀ < x)
  (hGc_L : IsBoundedNoPolesOn (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) l.L) :
    Filter.Tendsto (fun n ↦ l.intVerticalAt (l.σ n) (fun s ↦ G_circ s * (x : ℂ) ^ s))
      Filter.atTop (nhds (0 : ℂ)) := by
  simpa [LadderParams.intVerticalAt] using
    intVSeg_tendsto_zero_of_bounded_on_L l G_circ x₀ x (-l.T) l.T hx₀ hx
      (by rw [abs_of_nonpos (neg_nonpos.mpr l.hT.le)]; linarith)
      le_rfl
      (by linarith [l.hT])
      hGc_L

@[blueprint
  "ch2-lemma-5-1-g"
  (title := "Residue-sum exhaustion (CH2 Lemma 5.1, residue limit)")
  (statement := /--
  If $f$ is meromorphic on a region $S$ and has only finitely many poles there, then the truncated
  residue sums over $S \cap \{\Re s > \sigma_n\}$ converge, as $n \to \infty$, to the full sum
  over $S$. (Indeed they are eventually equal to it, once $\sigma_n$ has dropped below the real
  part of every pole.) -/)
  (proof := /-- Since $\sigma_n \to -\infty$ and there are finitely many poles in $S$, for all
  large $n$ the set $\{\Re s > \sigma_n\}$ contains every pole of $f$ in $S$; meromorphicity on
  $S$ makes the residue vanish at non-poles, so the truncated sum is then constant and equals the
  full residue sum over $S$. -/)
  (latexEnv := "sublemma")
  (discussion := 1454)]
theorem lemma_5_1_g (f : ℂ → ℂ) (S : Set ℂ)
    (hmero : MeromorphicOn f S)
    (hfin : {z ∈ S | meromorphicOrderAt f z < 0}.Finite) :
    Filter.Tendsto (fun n ↦ sumResiduesIn f (S ∩ {z | l.σ n < z.re})) Filter.atTop
      (nhds (sumResiduesIn f S)) := by
  let P : Set ℂ := {z | meromorphicOrderAt f z < 0}
  have hP_fin : (S ∩ P).Finite := by
    simpa [P, Set.setOf_and] using hfin
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z ∈ S ∩ P, B ≤ z.re := by
    obtain ⟨B, hB⟩ := (hP_fin.image Complex.re).exists_ge
    exact ⟨B, fun z hz ↦ hB z.re ⟨z, hz, rfl⟩⟩
  have h_residue_zero : ∀ s ∈ S, s ∉ P → residue f s = 0 := fun s hsS hs_not_pole ↦
    residue_eq_zero_of_not_pole_of_meromorphicAt (hmero s hsS)
      (le_of_not_gt (fun h ↦ hs_not_pole h))
  have h_eventually_eq : ∀ᶠ n in Filter.atTop, sumResiduesIn f (S ∩ {z | l.σ n < z.re}) = sumResiduesIn f S := by
    filter_upwards [l.hlim.eventually_lt_atBot B] with n hn
    have h_set_eq : (S ∩ {z | l.σ n < z.re}) ∩ P = S ∩ P :=
      Set.Subset.antisymm (fun z hz ↦ ⟨hz.1.1, hz.2⟩) (fun z hz ↦ ⟨⟨hz.1, lt_of_lt_of_le hn (hB z hz)⟩, hz.2⟩)
    have h_trunc_eq : sumResiduesIn f ((S ∩ {z | l.σ n < z.re}) ∩ P) = sumResiduesIn f (S ∩ {z | l.σ n < z.re}) :=
      sumResiduesIn_inter_eq_of_set_eq (F := f) (Rn := S ∩ {z | l.σ n < z.re}) (S2 := S ∩ {z | l.σ n < z.re}) (P := P)
        rfl (fun s hs_trunc hs_not_pole ↦ h_residue_zero s hs_trunc.1 hs_not_pole)
    calc
      sumResiduesIn f (S ∩ {z | l.σ n < z.re}) = sumResiduesIn f ((S ∩ {z | l.σ n < z.re}) ∩ P) := h_trunc_eq.symm
      _ = sumResiduesIn f (S ∩ P) := by rw [h_set_eq]
      _ = sumResiduesIn f S := sumResiduesIn_inter_eq_of_set_eq (F := f) (Rn := S) (S2 := S) (P := P) rfl h_residue_zero
  exact tendsto_nhds_of_eventually_eq h_eventually_eq

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
theorem lemma_5_1_h (hx₀ : 1 ≤ x₀) (hx : x₀ < x)
    (hG_star_mero : MeromorphicOn G_star l.R)
    (hGs_L : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.L)
    (hGs_contour : IsBoundedNoPolesOn (fun s ↦ G_star s * (x₀ : ℂ) ^ s) l.admissible_contour) :
  Filter.Tendsto (fun n ↦ l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)) Filter.atTop
    (nhds (l.intC (fun s ↦ G_star s * (x : ℂ) ^ s))) := by
  let F : ℂ → ℂ := fun s ↦ G_star s * (x : ℂ) ^ s
  have h_meas_mul : AEStronglyMeasurable (fun r : ℝ ↦ G_star (r + l.δ * Complex.I) * (x : ℂ) ^ (r + l.δ * Complex.I))
    (MeasureTheory.volume.restrict (Set.Iic 1)) := aestronglyMeasurable_horizontal_path_mul_cpow_of_meromorphic
      l G_star x₀ x l.δ hx₀ hx (fun z hz ↦ l.admissible_contour_subset_R (Or.inl hz)) hG_star_mero
      fun z hz ↦ meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.admissible_contour_subset_R hG_star_mero hGs_contour z (Or.inl hz)
  have h_meas : AEStronglyMeasurable (fun r : ℝ ↦ F ((r : ℂ) + l.δ * Complex.I))
        (MeasureTheory.volume.restrict (Set.Iic 1)) := by simpa [F] using h_meas_mul
  have h_int_ray : IntegrableOnHRay l.δ 1 F := by
    unfold IntegrableOnHRay
    obtain ⟨M, hM⟩ := hGs_contour
    let C : ℝ := max M 0
    have hx₀_pos : 0 < x₀ := by linarith
    have hx_pos : 0 < x := by linarith
    have hratio_pos : 0 < x / x₀ := div_pos hx_pos hx₀_pos
    have hlog_ratio_pos : 0 < Real.log (x / x₀) := Real.log_pos (by rw [one_lt_div hx₀_pos]; linarith)
    have h_int_bound :
        IntegrableOn (fun r : ℝ ↦ C * Real.exp (Real.log (x / x₀) * r)) (Set.Iic 1) :=
      (integrableOn_exp_mul_Iic hlog_ratio_pos 1).const_mul C
    have h_bound : ∀ r ∈ Set.Iic (1 : ℝ), ‖F ((r : ℂ) + l.δ * Complex.I)‖ ≤ C * Real.exp (Real.log (x / x₀) * r) := by
      intro r hr
      have hr' : r ≤ 1 := by simpa using hr
      have hz_ac : (r : ℂ) + l.δ * Complex.I ∈ l.admissible_contour := by
        left
        exact ⟨by simpa using hr', by simp⟩
      simpa [F, C] using norm_G_mul_cpow_le_of_base_bound G_star x₀ x l.δ r M hx₀ hx ((hM _ hz_ac).1)
    exact h_int_bound.mono' h_meas <| (ae_restrict_iff' measurableSet_Iic).mpr <| ae_of_all _ (fun r hr ↦ h_bound r hr)
  have h_horiz :
      Filter.Tendsto (fun n : ℕ ↦ intHSeg l.δ 1 (l.σ n) F) Filter.atTop
        (nhds (-intHRay l.δ 1 F)) := by
    have h_symm : ∀ n, intHSeg l.δ 1 (l.σ n) F = - intHSeg l.δ (l.σ n) 1 F :=
      fun n ↦ by unfold intHSeg; rw [intervalIntegral.integral_symm]
    have h_seq_eq : (fun n ↦ intHSeg l.δ 1 (l.σ n) F) = (fun n ↦ - intHSeg l.δ (l.σ n) 1 F) :=
      funext fun n ↦ h_symm n
    have h_tendsto_ray : Filter.Tendsto (fun n ↦ intHSeg l.δ (l.σ n) 1 F) Filter.atTop (nhds (intHRay l.δ 1 F)) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Iic 1 h_int_ray l.hlim
    rw [h_seq_eq]
    simpa using h_tendsto_ray.neg
  have h_vert : Filter.Tendsto (fun n : ℕ ↦ intVSeg (l.σ n) l.δ l.T F) Filter.atTop (nhds 0) := by
    simpa [F] using intVSeg_tendsto_zero_of_bounded_on_L l G_star x₀ x l.δ l.T hx₀ hx
        (by rw [abs_of_nonneg l.hδ.1.le]; linarith [l.hδ.2, l.hT]) le_rfl
        (by linarith [l.hδ.1, l.hδ.2, l.hT]) hGs_L
  have h_sum : Filter.Tendsto (fun n : ℕ ↦ intVSeg 1 0 l.δ F + (intHSeg l.δ 1 (l.σ n) F + intVSeg (l.σ n) l.δ l.T F))
        Filter.atTop (nhds (intVSeg 1 0 l.δ F + (-intHRay l.δ 1 F + 0))) :=
        Filter.Tendsto.add tendsto_const_nhds (Filter.Tendsto.add h_horiz h_vert)
  simpa [LadderParams.intCn1Plus, LadderParams.intC, F, sub_eq_add_neg, add_assoc] using h_sum

private lemma intVSeg_split_upper {G G_circ G_star : ℂ → ℂ} {x : ℝ}
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (c a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : IntervalIntegrable (fun t : ℝ ↦ G_circ (c + t * Complex.I) *
      (x : ℂ) ^ (c + t * Complex.I) * Complex.I) volume a b)
    (hs : IntervalIntegrable (fun t : ℝ ↦ G_star (c + t * Complex.I) *
      (x : ℂ) ^ (c + t * Complex.I) * Complex.I) volume a b) :
    intVSeg c a b (fun s ↦ G s * (x : ℂ) ^ s) =
      intVSeg c a b (fun s ↦ G_circ s * (x : ℂ) ^ s) +
        intVSeg c a b (fun s ↦ G_star s * (x : ℂ) ^ s) := by
  simp only [intVSeg]
  rw [← intervalIntegral.integral_add hc hs]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [] with t ht
  rw [Set.uIoc_of_le hab] at ht
  have htpos : 0 < t := lt_of_le_of_lt ha ht.1
  rw [hG, show (Real.sign ((c : ℂ) + t * Complex.I).im : ℂ) = 1 by
    simp [Real.sign_of_pos htpos]]
  ring

private lemma intVSeg_split_lower {G G_circ G_star : ℂ → ℂ} {x : ℝ}
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (c a b : ℝ) (hb : b ≤ 0) (hab : a ≤ b)
    (hc : IntervalIntegrable (fun t : ℝ ↦ G_circ (c + t * Complex.I) *
      (x : ℂ) ^ (c + t * Complex.I) * Complex.I) volume a b)
    (hs : IntervalIntegrable (fun t : ℝ ↦ G_star (c + t * Complex.I) *
      (x : ℂ) ^ (c + t * Complex.I) * Complex.I) volume a b) :
    intVSeg c a b (fun s ↦ G s * (x : ℂ) ^ s) =
      intVSeg c a b (fun s ↦ G_circ s * (x : ℂ) ^ s) -
        intVSeg c a b (fun s ↦ G_star s * (x : ℂ) ^ s) := by
  simp only [intVSeg]
  rw [← intervalIntegral.integral_sub hc hs]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with t htne ht
  rw [Set.uIoc_of_le hab] at ht
  have htneg : t < 0 := lt_of_le_of_ne (le_trans ht.2 hb) htne
  rw [hG, show (Real.sign ((c : ℂ) + t * Complex.I).im : ℂ) = -1 by
    simp [Real.sign_of_neg htneg]]
  ring

private lemma intHSeg_split_upper {G G_circ G_star : ℂ → ℂ} {x : ℝ}
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (h a b : ℝ) (hh : 0 < h)
    (hc : IntervalIntegrable (fun r : ℝ ↦ G_circ ((r : ℂ) + h * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + h * Complex.I)) volume a b)
    (hs : IntervalIntegrable (fun r : ℝ ↦ G_star ((r : ℂ) + h * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + h * Complex.I)) volume a b) :
    intHSeg h a b (fun s ↦ G s * (x : ℂ) ^ s) =
      intHSeg h a b (fun s ↦ G_circ s * (x : ℂ) ^ s) +
        intHSeg h a b (fun s ↦ G_star s * (x : ℂ) ^ s) := by
  simp only [intHSeg]
  rw [← intervalIntegral.integral_add hc hs]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [] with r _
  rw [hG, show (Real.sign (((r : ℂ) + h * Complex.I).im) : ℂ) = 1 by
    simp [Real.sign_of_pos hh]]
  ring

private lemma intHSeg_split_lower {G G_circ G_star : ℂ → ℂ} {x : ℝ}
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (h a b : ℝ) (hh : h < 0)
    (hc : IntervalIntegrable (fun r : ℝ ↦ G_circ ((r : ℂ) + h * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + h * Complex.I)) volume a b)
    (hs : IntervalIntegrable (fun r : ℝ ↦ G_star ((r : ℂ) + h * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + h * Complex.I)) volume a b) :
    intHSeg h a b (fun s ↦ G s * (x : ℂ) ^ s) =
      intHSeg h a b (fun s ↦ G_circ s * (x : ℂ) ^ s) -
        intHSeg h a b (fun s ↦ G_star s * (x : ℂ) ^ s) := by
  simp only [intHSeg]
  rw [← intervalIntegral.integral_sub hc hs]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [] with r _
  rw [hG, show (Real.sign (((r : ℂ) + h * Complex.I).im) : ℂ) = -1 by
    simp [Real.sign_of_neg hh]]
  ring

private lemma intCn1Plus_split (l : LadderParams) (n : ℕ)
    {G G_circ G_star : ℂ → ℂ} {x : ℝ}
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (h1c : IntervalIntegrable (fun t : ℝ ↦ G_circ (1 + t * Complex.I) *
      (x : ℂ) ^ (1 + t * Complex.I) * Complex.I) volume 0 l.δ)
    (h1s : IntervalIntegrable (fun t : ℝ ↦ G_star (1 + t * Complex.I) *
      (x : ℂ) ^ (1 + t * Complex.I) * Complex.I) volume 0 l.δ)
    (h2c : IntervalIntegrable (fun r : ℝ ↦ G_circ ((r : ℂ) + l.δ * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + l.δ * Complex.I)) volume 1 (l.σ n))
    (h2s : IntervalIntegrable (fun r : ℝ ↦ G_star ((r : ℂ) + l.δ * Complex.I) *
      (x : ℂ) ^ ((r : ℂ) + l.δ * Complex.I)) volume 1 (l.σ n))
    (h3c : IntervalIntegrable (fun t : ℝ ↦ G_circ ((l.σ n : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume l.δ l.T)
    (h3s : IntervalIntegrable (fun t : ℝ ↦ G_star ((l.σ n : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume l.δ l.T) :
    l.intCn1Plus n (fun s ↦ G s * (x : ℂ) ^ s) =
      l.intCn1Plus n (fun s ↦ G_circ s * (x : ℂ) ^ s) +
        l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s) := by
  simp only [LadderParams.intCn1Plus]
  rw [intVSeg_split_upper hG 1 0 l.δ le_rfl l.hδ.1.le h1c h1s,
    intHSeg_split_upper hG l.δ 1 (l.σ n) l.hδ.1 h2c h2s,
    intVSeg_split_upper hG (l.σ n) l.δ l.T l.hδ.1.le
      (by linarith [l.hδ.2, l.hT]) h3c h3s]
  ring

private lemma intCn1Minus_split (l : LadderParams) (n : ℕ)
    {G G_circ G_star : ℂ → ℂ} {x : ℝ}
    (hG : ∀ s, G s = G_circ s + (Real.sign s.im : ℂ) * G_star s)
    (h1c : IntervalIntegrable (fun t : ℝ ↦ G_circ ((l.σ n : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume (-l.T) (-l.δ))
    (h1s : IntervalIntegrable (fun t : ℝ ↦ G_star ((l.σ n : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume (-l.T) (-l.δ))
    (h2c : IntervalIntegrable (fun r : ℝ ↦ G_circ ((r : ℂ) + ((-l.δ : ℝ) : ℂ) *
      Complex.I) * (x : ℂ) ^ ((r : ℂ) + ((-l.δ : ℝ) : ℂ) * Complex.I)) volume (l.σ n) 1)
    (h2s : IntervalIntegrable (fun r : ℝ ↦ G_star ((r : ℂ) + ((-l.δ : ℝ) : ℂ) *
      Complex.I) * (x : ℂ) ^ ((r : ℂ) + ((-l.δ : ℝ) : ℂ) * Complex.I)) volume (l.σ n) 1)
    (h3c : IntervalIntegrable (fun t : ℝ ↦ G_circ (1 + t * Complex.I) *
      (x : ℂ) ^ (1 + t * Complex.I) * Complex.I) volume (-l.δ) 0)
    (h3s : IntervalIntegrable (fun t : ℝ ↦ G_star (1 + t * Complex.I) *
      (x : ℂ) ^ (1 + t * Complex.I) * Complex.I) volume (-l.δ) 0) :
    l.intCn1Minus n (fun s ↦ G s * (x : ℂ) ^ s) =
      l.intCn1Minus n (fun s ↦ G_circ s * (x : ℂ) ^ s) -
        l.intCn1Minus n (fun s ↦ G_star s * (x : ℂ) ^ s) := by
  simp only [LadderParams.intCn1Minus]
  rw [intVSeg_split_lower hG (l.σ n) (-l.T) (-l.δ) (by linarith [l.hδ.1])
      (by linarith [l.hδ.2, l.hT]) h1c h1s,
    intHSeg_split_lower hG (-l.δ) (l.σ n) 1 (by linarith [l.hδ.1]) h2c h2s,
    intVSeg_split_lower hG 1 (-l.δ) 0 le_rfl (by linarith [l.hδ.1]) h3c h3s]
  ring

private lemma sumResiduesIn_Rpos_add_RposBar (l : LadderParams) (f : ℂ → ℂ)
    (hmero_pos : MeromorphicOn f l.Rpos) (hmero_neg : MeromorphicOn f l.RposBar)
    (hmero_diff : MeromorphicOn f (l.R \ l.RC))
    (hfin : {z ∈ l.R \ l.RC | meromorphicOrderAt f z < 0}.Finite)
    (h_no_pole_upper : ∀ z : ℂ, z.re ≤ 1 → z.im = l.δ → 0 ≤ meromorphicOrderAt f z)
    (h_no_pole_lower : ∀ z : ℂ, z.re ≤ 1 → z.im = -l.δ → 0 ≤ meromorphicOrderAt f z) :
    sumResiduesIn f l.Rpos + sumResiduesIn f l.RposBar = sumResiduesIn f (l.R \ l.RC) := by
  set P : Set ℂ := {z | meromorphicOrderAt f z < 0} with hP
  have h_pos : sumResiduesIn f (l.Rpos ∩ P) = sumResiduesIn f l.Rpos :=
    sumResiduesIn_inter_eq_of_set_eq rfl (fun s hs hsP ↦
      residue_eq_zero_of_not_pole_of_meromorphicAt (hmero_pos s hs) (le_of_not_gt hsP))
  have h_neg : sumResiduesIn f (l.RposBar ∩ P) = sumResiduesIn f l.RposBar :=
    sumResiduesIn_inter_eq_of_set_eq rfl (fun s hs hsP ↦
      residue_eq_zero_of_not_pole_of_meromorphicAt (hmero_neg s hs) (le_of_not_gt hsP))
  have h_diff : sumResiduesIn f ((l.R \ l.RC) ∩ P) = sumResiduesIn f (l.R \ l.RC) :=
    sumResiduesIn_inter_eq_of_set_eq rfl (fun s hs hsP ↦
      residue_eq_zero_of_not_pole_of_meromorphicAt (hmero_diff s hs) (le_of_not_gt hsP))
  have h_disj : Disjoint (l.Rpos ∩ P) (l.RposBar ∩ P) := by
    rw [Set.disjoint_left]
    rintro z ⟨hz_pos, _⟩ ⟨hz_neg, _⟩
    linarith [hz_pos.2.1, hz_neg.2.2, l.hδ.1]
  have h_union : (l.Rpos ∩ P) ∪ (l.RposBar ∩ P) = (l.R \ l.RC) ∩ P := by
    ext z
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, hP, Set.mem_setOf_eq,
      LadderParams.Rpos, LadderParams.RposBar, LadderParams.R, LadderParams.RC, Set.mem_Icc]
    constructor
    · rintro (⟨⟨hre, him1, him2⟩, hpole⟩ | ⟨⟨hre, him1, him2⟩, hpole⟩)
      · refine ⟨⟨⟨hre, ?_⟩, ?_⟩, hpole⟩
        · rw [abs_of_nonneg (by linarith [l.hδ.1] : (0 : ℝ) ≤ z.im)]
          exact him2
        · rintro ⟨_, hle⟩
          have hne : z.im ≠ l.δ := fun h ↦
            absurd (h_no_pole_upper z hre h) (not_le.mpr hpole)
          rw [abs_of_nonneg (by linarith [l.hδ.1] : (0 : ℝ) ≤ z.im)] at hle
          exact absurd hle (not_le_of_gt (lt_of_le_of_ne him1 (Ne.symm hne)))
      · refine ⟨⟨⟨hre, ?_⟩, ?_⟩, hpole⟩
        · rw [abs_of_nonpos (by linarith [l.hδ.1] : z.im ≤ 0)]
          linarith
        · rintro ⟨_, hle⟩
          have hne : z.im ≠ -l.δ := fun h ↦
            absurd (h_no_pole_lower z hre h) (not_le.mpr hpole)
          rw [abs_of_nonpos (by linarith [l.hδ.1] : z.im ≤ 0)] at hle
          have : z.im < -l.δ := lt_of_le_of_ne him2 hne
          linarith
    · rintro ⟨⟨⟨hre, habs⟩, hRC⟩, hpole⟩
      have hgt : l.δ < |z.im| := by
        by_contra h
        exact hRC ⟨hre, not_lt.mp h⟩
      rcases le_or_gt 0 z.im with him | him
      · left
        rw [abs_of_nonneg him] at hgt habs
        exact ⟨⟨hre, hgt.le, habs⟩, hpole⟩
      · right
        rw [abs_of_neg him] at hgt habs
        exact ⟨⟨hre, by linarith, by linarith⟩, hpole⟩
  have hfin' : ((l.R \ l.RC) ∩ P).Finite := hfin.subset fun z hz ↦ ⟨hz.1, hz.2⟩
  have hfin_pos : (l.Rpos ∩ P).Finite := hfin'.subset (by
    rw [← h_union]
    exact Set.subset_union_left)
  have hfin_neg : (l.RposBar ∩ P).Finite := hfin'.subset (by
    rw [← h_union]
    exact Set.subset_union_right)
  rw [← h_pos, ← h_neg, ← h_diff, ← h_union, sumResiduesIn, sumResiduesIn, sumResiduesIn]
  rw [Summable.tsum_union_disjoint h_disj (hfin_pos.summable _) (hfin_neg.summable _)]

@[blueprint
  "ch2-lemma-5-1"
  (title := "Contour shifting (CH2 Lemma 5.1)")
  (statement := /--
  Let $G = G^\circ + \mathrm{sgn}(\Im s)\, G^\star$ with $G^\circ, G^\star$ meromorphic on
  $R = (-\infty,1] + i[-T,T]$, and suppose $G^\star(\bar s) = -\overline{G^\star(s)}$. The
  formalisation additionally assumes $G^\circ(\bar s) = \overline{G^\circ(s)}$: this makes explicit
  an implicit requirement, not visibly stated in the displayed paper statement, needed to transfer
  no-pole information to the lower contour. Suppose for
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
    (hG_star_symm : ConjAntisymm G_star) (hG_circ_symm : ConjSymm G_circ)
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
  have hx_pos : 0 < x := by linarith
  have hGc_contour_ord : ∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt G_circ s :=
    meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.admissible_contour_subset_R
      hG_circ_mero hGc_contour
  have hGs_contour_ord : ∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt G_star s :=
    meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.admissible_contour_subset_R
      hG_star_mero hGs_contour
  have hGc_L_ord : ∀ s ∈ l.L, 0 ≤ meromorphicOrderAt G_circ s :=
    meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.L_subset_R hG_circ_mero hGc_L
  have hGs_L_ord : ∀ s ∈ l.L, 0 ≤ meromorphicOrderAt G_star s :=
    meromorphicOrderAt_nonneg_on_of_bounded l hx₀ l.L_subset_R hG_star_mero hGs_L
  have ord_conj_contour : ∀ (H : ℂ → ℂ), (ConjSymm H ∨ ConjAntisymm H) →
      (∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt H s) →
      ∀ z : ℂ, z.re = 1 → z.im ∈ Set.Icc (-l.δ) 0 → 0 ≤ meromorphicOrderAt H z := by
    intro H hsymm hord z hre him
    rw [meromorphicOrderAt_starRingEnd hsymm]
    exact hord _ (l.star_mem_admissible_contour_of_re_eq_one_of_im_nonpos hre him)
  have ord_conj_line : ∀ (H : ℂ → ℂ), (ConjSymm H ∨ ConjAntisymm H) →
      (∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt H s) →
      ∀ z : ℂ, z.re ≤ 1 → z.im = -l.δ → 0 ≤ meromorphicOrderAt H z := by
    intro H hsymm hord z hre him
    rw [meromorphicOrderAt_starRingEnd hsymm]
    refine hord _ (Or.inl ⟨by simpa using hre, ?_⟩)
    simp [him]
  have mk_vseg : ∀ (H : ℂ → ℂ), MeromorphicOn H l.R → ∀ (S : Set ℂ), S ⊆ l.R →
      (∀ s ∈ S, 0 ≤ meromorphicOrderAt H s) → ∀ (c a b : ℝ), a ≤ b →
      (∀ t ∈ Set.Icc a b, (c : ℂ) + t * Complex.I ∈ S) →
      IntervalIntegrable (fun t : ℝ ↦ H ((c : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((c : ℂ) + t * Complex.I) * Complex.I) volume a b :=
    fun H hH S hSR hSord c a b hab hmaps ↦
      G_circ_mul_cpow_integrable_vseg_general l H hH x₀ x hx₀ hx S hSR hSord
        c a b hab hmaps
  have mk_hseg : ∀ (H : ℂ → ℂ), MeromorphicOn H l.R → ∀ (S : Set ℂ), S ⊆ l.R →
      (∀ s ∈ S, 0 ≤ meromorphicOrderAt H s) → ∀ (h a b : ℝ), a ≤ b →
      (∀ r ∈ Set.Icc a b, (r : ℂ) + h * Complex.I ∈ S) →
      IntervalIntegrable (fun r : ℝ ↦ H ((r : ℂ) + h * Complex.I) *
        (x : ℂ) ^ ((r : ℂ) + h * Complex.I)) volume a b :=
    fun H hH S hSR hSord h a b hab hmaps ↦
      G_circ_mul_cpow_integrable_hseg_general l H hH x₀ x hx₀ hx S hSR hSord
        h a b hab hmaps
  have hδT : l.δ ≤ l.T := by linarith [l.hδ.1, l.hδ.2, l.hT]
  have col_mem_L : ∀ (n : ℕ), 1 ≤ n → ∀ t : ℝ, |t| ≤ l.T →
      (l.σ n : ℂ) + t * Complex.I ∈ l.L := by
    intro n hn t ht
    refine ⟨n, hn, ?_, ?_⟩
    · simp
    · simpa using ht
  have key : ∀ n : ℕ, 1 ≤ n →
      (2 * (π : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt 1 (fun s ↦ G s * (x : ℂ) ^ s) =
        (2 * (π : ℂ) * Complex.I)⁻¹ *
            l.intVerticalAt (l.σ n) (fun s ↦ G_circ s * (x : ℂ) ^ s) +
          (↑(π⁻¹ * (l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ) +
          (2 * (π : ℂ) * Complex.I)⁻¹ *
            (intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) +
              intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s)) +
          sumResiduesIn (fun s ↦ G_circ s * (x : ℂ) ^ s)
            (l.RC ∩ {z | l.σ n < z.re}) +
          (sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s)
              (l.Rpos ∩ {z | l.σ n < z.re}) +
            sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s)
              (l.RposBar ∩ {z | l.σ n < z.re})) := by
    intro n hn
    have hσn : l.σ n ≤ 1 := l.hσ n
    have iU1 : ∀ (H : ℂ → ℂ), MeromorphicOn H l.R →
        (∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt H s) →
        IntervalIntegrable (fun t : ℝ ↦ H (1 + t * Complex.I) *
          (x : ℂ) ^ (1 + t * Complex.I) * Complex.I) volume 0 l.δ := by
      intro H hH hord
      simpa using mk_vseg H hH l.admissible_contour l.admissible_contour_subset_R hord
        1 0 l.δ l.hδ.1.le (fun t ht ↦
          l.mem_admissible_contour_of_re_eq_one_of_im_nonneg (by simp) (by simpa using ht))
    have iU2 : ∀ (H : ℂ → ℂ), MeromorphicOn H l.R →
        (∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt H s) →
        IntervalIntegrable (fun r : ℝ ↦ H ((r : ℂ) + l.δ * Complex.I) *
          (x : ℂ) ^ ((r : ℂ) + l.δ * Complex.I)) volume 1 (l.σ n) := by
      intro H hH hord
      refine (mk_hseg H hH l.admissible_contour l.admissible_contour_subset_R hord
        l.δ (l.σ n) 1 hσn ?_).symm
      intro r hr
      simp only [Set.mem_Icc] at hr
      refine Or.inl ⟨?_, by simp⟩
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      exact hr.2
    have iU3 : ∀ (H : ℂ → ℂ), MeromorphicOn H l.R →
        (∀ s ∈ l.L, 0 ≤ meromorphicOrderAt H s) →
        IntervalIntegrable (fun t : ℝ ↦ H ((l.σ n : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((l.σ n : ℂ) + t * Complex.I) * Complex.I) volume l.δ l.T := by
      intro H hH hord
      exact mk_vseg H hH l.L l.L_subset_R hord (l.σ n) l.δ l.T hδT
        (fun t ht ↦ col_mem_L n hn t (by
          rw [abs_of_pos (by linarith [l.hδ.1, ht.1] : (0 : ℝ) < t)]
          exact ht.2))
    have iL1 : ∀ (H : ℂ → ℂ), MeromorphicOn H l.R →
        (∀ s ∈ l.L, 0 ≤ meromorphicOrderAt H s) →
        IntervalIntegrable (fun t : ℝ ↦ H ((l.σ n : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((l.σ n : ℂ) + t * Complex.I) * Complex.I)
          volume (-l.T) (-l.δ) := by
      intro H hH hord
      exact mk_vseg H hH l.L l.L_subset_R hord (l.σ n) (-l.T) (-l.δ)
        (by linarith [l.hδ.1]) (fun t ht ↦ col_mem_L n hn t (by
          rw [abs_of_neg (by linarith [l.hδ.1, ht.2] : t < 0)]
          linarith [ht.1, ht.2]))
    have iL2 : ∀ (H : ℂ → ℂ), MeromorphicOn H l.R →
        (ConjSymm H ∨ ConjAntisymm H) →
        (∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt H s) →
        IntervalIntegrable (fun r : ℝ ↦
          H ((r : ℂ) + ((-l.δ : ℝ) : ℂ) * Complex.I) *
            (x : ℂ) ^ ((r : ℂ) + ((-l.δ : ℝ) : ℂ) * Complex.I)) volume (l.σ n) 1 := by
      intro H hH hsymm hord
      have hSR : {z : ℂ | z.re ≤ 1 ∧ z.im = -l.δ} ⊆ l.R := by
        intro z hz
        refine ⟨hz.1, ?_⟩
        rw [hz.2, abs_neg, abs_of_pos l.hδ.1]
        linarith [l.hδ.2, l.hT]
      have hSord : ∀ s ∈ {z : ℂ | z.re ≤ 1 ∧ z.im = -l.δ},
          0 ≤ meromorphicOrderAt H s :=
        fun z hz ↦ ord_conj_line H hsymm hord z hz.1 hz.2
      refine mk_hseg H hH {z : ℂ | z.re ≤ 1 ∧ z.im = -l.δ} hSR hSord
        (-l.δ) (l.σ n) 1 hσn ?_
      intro r hr
      simp only [Set.mem_Icc] at hr
      refine ⟨?_, by simp⟩
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      linarith [hr.2]
    have iL3 : ∀ (H : ℂ → ℂ), MeromorphicOn H l.R →
        (ConjSymm H ∨ ConjAntisymm H) →
        (∀ s ∈ l.admissible_contour, 0 ≤ meromorphicOrderAt H s) →
        IntervalIntegrable (fun t : ℝ ↦ H (1 + t * Complex.I) *
          (x : ℂ) ^ (1 + t * Complex.I) * Complex.I) volume (-l.δ) 0 := by
      intro H hH hsymm hord
      have hSR : {z : ℂ | z.re = 1 ∧ z.im ∈ Set.Icc (-l.δ) 0} ⊆ l.R := by
        intro z hz
        refine ⟨le_of_eq hz.1, ?_⟩
        rw [abs_of_nonpos hz.2.2]
        linarith [hz.2.1, l.hδ.2, l.hT]
      have hSord : ∀ s ∈ {z : ℂ | z.re = 1 ∧ z.im ∈ Set.Icc (-l.δ) 0},
          0 ≤ meromorphicOrderAt H s :=
        fun z hz ↦ ord_conj_contour H hsymm hord z hz.1 hz.2
      simpa using mk_vseg H hH {z : ℂ | z.re = 1 ∧ z.im ∈ Set.Icc (-l.δ) 0}
        hSR hSord 1 (-l.δ) 0 (by linarith [l.hδ.1])
        (fun t ht ↦ ⟨by simp, by simpa using ht⟩)
    have ha := lemma_5_1_a (l := l) (G := G) (G_circ := G_circ)
      (G_star := G_star) (x₀ := x₀) (x := x) n hG hG_circ_mero hG_star_mero hx₀
      hG_bdd hGc_L hGc_contour hGs_L hGs_contour hx hfin hsimple
    have hb := lemma_5_1_b (l := l) (G := G) (G_circ := G_circ)
      (G_star := G_star) (x₀ := x₀) (x := x) n hG hG_circ_mero hG_star_mero
      hG_circ_symm hG_star_symm hx₀ hG_bdd hGc_L hGc_contour hGs_L hGs_contour
      hx hfin hsimple
    have hG_nopoles : ∀ s ∈ l.Rboundary, 0 ≤ s.im →
        0 ≤ meromorphicOrderAt (G_circ + G_star) s :=
      upper_Rboundary_no_poles l hG hG_circ_mero hG_star_mero hx₀ hG_bdd
        hGc_contour hGs_contour
    have hG_nopoles_lower : ∀ s ∈ l.Rboundary, s.im ≤ 0 →
        0 ≤ meromorphicOrderAt (G_circ - G_star) s :=
      lower_Rboundary_no_poles l hG hG_circ_mero hG_star_mero hx₀ hG_bdd
        hGc_contour hGs_contour
    have hint_up : IntervalIntegrable (fun t : ℝ ↦ G (1 + t * Complex.I) *
        (x : ℂ) ^ (1 + t * Complex.I) * Complex.I) volume 0 l.T :=
      G_mul_cpow_integrable_vseg l hG hG_circ_mero hG_star_mero hx₀ hG_nopoles hx
        0 l.T le_rfl l.hT.le le_rfl
    have hint_lo : IntervalIntegrable (fun t : ℝ ↦ G (1 + t * Complex.I) *
        (x : ℂ) ^ (1 + t * Complex.I) * Complex.I) volume (-l.T) 0 :=
      G_mul_cpow_integrable_vseg_lower l hG hG_circ_mero hG_star_mero hx₀
        hG_nopoles_lower hx (-l.T) 0 (by linarith [l.hT]) (by linarith [l.hT]) le_rfl
    have e_split : l.intVerticalAt 1 (fun s ↦ G s * (x : ℂ) ^ s) =
        intVSeg 1 (-l.T) 0 (fun s ↦ G s * (x : ℂ) ^ s) +
          intVSeg 1 0 l.T (fun s ↦ G s * (x : ℂ) ^ s) := by
      simp only [LadderParams.intVerticalAt, intVSeg, Complex.ofReal_one]
      rw [intervalIntegral.integral_add_adjacent_intervals hint_lo hint_up]
    have e_cn : l.intCnPlus n (fun s ↦ G s * (x : ℂ) ^ s) +
        l.intCnMinus n (fun s ↦ G s * (x : ℂ) ^ s) =
      (l.intCn1Plus n (fun s ↦ G s * (x : ℂ) ^ s) +
        l.intCn1Minus n (fun s ↦ G s * (x : ℂ) ^ s)) +
      (intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) +
        intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s)) := by
      simp only [LadderParams.intCnPlus, LadderParams.intCnMinus,
        LadderParams.intCn1Plus, LadderParams.intCn1Minus]
      ring
    have e_p : l.intCn1Plus n (fun s ↦ G s * (x : ℂ) ^ s) =
        l.intCn1Plus n (fun s ↦ G_circ s * (x : ℂ) ^ s) +
          l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s) :=
      intCn1Plus_split l n hG (iU1 G_circ hG_circ_mero hGc_contour_ord)
        (iU1 G_star hG_star_mero hGs_contour_ord)
        (iU2 G_circ hG_circ_mero hGc_contour_ord)
        (iU2 G_star hG_star_mero hGs_contour_ord)
        (iU3 G_circ hG_circ_mero hGc_L_ord) (iU3 G_star hG_star_mero hGs_L_ord)
    have e_m : l.intCn1Minus n (fun s ↦ G s * (x : ℂ) ^ s) =
        l.intCn1Minus n (fun s ↦ G_circ s * (x : ℂ) ^ s) -
          l.intCn1Minus n (fun s ↦ G_star s * (x : ℂ) ^ s) :=
      intCn1Minus_split l n hG (iL1 G_circ hG_circ_mero hGc_L_ord)
        (iL1 G_star hG_star_mero hGs_L_ord)
        (iL2 G_circ hG_circ_mero (Or.inl hG_circ_symm) hGc_contour_ord)
        (iL2 G_star hG_star_mero (Or.inr hG_star_symm) hGs_contour_ord)
        (iL3 G_circ hG_circ_mero (Or.inl hG_circ_symm) hGc_contour_ord)
        (iL3 G_star hG_star_mero (Or.inr hG_star_symm) hGs_contour_ord)
    have hc := lemma_5_1_c (l := l) (G_circ := G_circ) (x₀ := x₀) (x := x)
      n hn hG_circ_mero hG_circ_symm hx₀ hGc_L hGc_contour hx hsimple_circ
    have hd := lemma_5_1_d (l := l) (G_star := G_star) (x₀ := x₀) (x := x)
      n hG_star_symm hx₀ hx
    have hscal : (2 * (π : ℂ) * Complex.I)⁻¹ *
        (2 * Complex.I *
          ((l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im : ℂ)) =
        (↑(π⁻¹ * (l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ) := by
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    set k : ℂ := (2 * (π : ℂ) * Complex.I)⁻¹ with hk
    linear_combination k * e_split + ha + hb + k * e_cn + k * e_p + k * e_m +
      hc + k * hd + hscal
  have mero_pt : ∀ z : ℂ, z ∈ l.R → z.im ≠ 0 →
      MeromorphicAt (fun s ↦ G s * (x : ℂ) ^ s) z := by
    intro z hzR hzim
    rcases lt_or_gt_of_ne hzim with hneg | hpos
    · have h_eq : (fun t : ℂ ↦ G t * (x : ℂ) ^ t) =ᶠ[nhdsWithin z {z}ᶜ]
          (fun t : ℂ ↦ (G_circ t - G_star t) * (x : ℂ) ^ t) := by
        filter_upwards [(filter_eventuallyEq_G_neg hG hneg).filter_mono
          nhdsWithin_le_nhds] with t ht
        rw [ht]
        rfl
      exact (((hG_circ_mero z hzR).sub (hG_star_mero z hzR)).mul
        (meromorphicAt_rpow hx_pos z)).congr h_eq.symm
    · have h_eq : (fun t : ℂ ↦ G t * (x : ℂ) ^ t) =ᶠ[nhdsWithin z {z}ᶜ]
          (fun t : ℂ ↦ (G_circ t + G_star t) * (x : ℂ) ^ t) := by
        filter_upwards [(filter_eventuallyEq_G_pos hG hpos).filter_mono
          nhdsWithin_le_nhds] with t ht
        rw [ht]
        rfl
      exact (((hG_circ_mero z hzR).add (hG_star_mero z hzR)).mul
        (meromorphicAt_rpow hx_pos z)).congr h_eq.symm
  have hGmero_pos : MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s) l.Rpos := fun z hz ↦
    mero_pt z (l.Rpos_subset_R hz) (by linarith [hz.2.1, l.hδ.1])
  have hGmero_neg : MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s) l.RposBar := fun z hz ↦
    mero_pt z (l.RposBar_subset_R hz) (by linarith [hz.2.2, l.hδ.1])
  have hGmero_diff : MeromorphicOn (fun s ↦ G s * (x : ℂ) ^ s) (l.R \ l.RC) :=
    fun z hz ↦ mero_pt z hz.1 (by
      intro h
      exact hz.2 ⟨hz.1.1, by rw [h]; simpa using l.hδ.1.le⟩)
  have h_no_pole_upper : ∀ z : ℂ, z.re ≤ 1 → z.im = l.δ →
      0 ≤ meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z := by
    intro z hre him
    have hz_pos : 0 < z.im := by rw [him]; exact l.hδ.1
    have hzR : z ∈ l.R := ⟨hre, by
      rw [him, abs_of_pos l.hδ.1]
      linarith [l.hδ.2, l.hT]⟩
    have hz_ac : z ∈ l.admissible_contour := Or.inl ⟨hre, him⟩
    rw [meromorphicOrderAt_mul_cpow_eq (by linarith) (by
      refine ((hG_circ_mero z hzR).add (hG_star_mero z hzR)).congr ?_
      exact ((filter_eventuallyEq_G_pos hG hz_pos).filter_mono nhdsWithin_le_nhds).symm)]
    refine meromorphicOrderAt_add_nonneg (hG_circ_mero z hzR) (hG_star_mero z hzR)
      (filter_eventuallyEq_G_pos hG hz_pos) (hGc_contour_ord z hz_ac)
      (hGs_contour_ord z hz_ac)
  have h_no_pole_lower : ∀ z : ℂ, z.re ≤ 1 → z.im = -l.δ →
      0 ≤ meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z := by
    intro z hre him
    have hz_neg : z.im < 0 := by rw [him]; linarith [l.hδ.1]
    have hzR : z ∈ l.R := ⟨hre, by
      rw [him, abs_neg, abs_of_pos l.hδ.1]
      linarith [l.hδ.2, l.hT]⟩
    rw [meromorphicOrderAt_mul_cpow_eq (by linarith) (by
      refine ((hG_circ_mero z hzR).sub (hG_star_mero z hzR)).congr ?_
      exact ((filter_eventuallyEq_G_neg hG hz_neg).filter_mono nhdsWithin_le_nhds).symm)]
    have hGc_ord := ord_conj_line G_circ (Or.inl hG_circ_symm)
      hGc_contour_ord z hre him
    have hGs_ord := ord_conj_line G_star (Or.inr hG_star_symm)
      hGs_contour_ord z hre him
    have h_eq_neg : G =ᶠ[nhds z] G_circ - G_star := filter_eventuallyEq_G_neg hG hz_neg
    have h_sub_eq : (G_circ - G_star) = (G_circ + (-G_star)) := sub_eq_add_neg _ _
    refine meromorphicOrderAt_add_nonneg (hG_circ_mero z hzR)
      ((hG_star_mero z hzR).neg) (h_eq_neg.trans (by rw [h_sub_eq])) hGc_ord ?_
    exact meromorphicOrderAt_neg_nonneg (hG_star_mero z hzR) hGs_ord
  have hfin_pos : {z ∈ l.Rpos |
      meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite := by
    apply hfin.subset
    rintro z ⟨hzpos, hzpole⟩
    have him : l.δ < z.im := by
      rcases eq_or_lt_of_le hzpos.2.1 with h | h
      · exact absurd hzpole (not_lt.mpr (h_no_pole_upper z hzpos.1 h.symm))
      · exact h
    refine ⟨⟨l.Rpos_subset_R hzpos, fun h ↦ ?_⟩, hzpole⟩
    have : |z.im| ≤ l.δ := h.2
    rw [abs_of_nonneg (by linarith [l.hδ.1])] at this
    linarith
  have hfin_neg : {z ∈ l.RposBar |
      meromorphicOrderAt (fun s ↦ G s * (x : ℂ) ^ s) z < 0}.Finite := by
    apply hfin.subset
    rintro z ⟨hzneg, hzpole⟩
    have him : z.im < -l.δ := by
      rcases eq_or_lt_of_le hzneg.2.2 with h | h
      · exact absurd hzpole (not_lt.mpr (h_no_pole_lower z hzneg.1 h))
      · exact h
    refine ⟨⟨l.RposBar_subset_R hzneg, fun h ↦ ?_⟩, hzpole⟩
    have : |z.im| ≤ l.δ := h.2
    rw [abs_of_nonpos (by linarith [l.hδ.1])] at this
    linarith
  have tf : Filter.Tendsto (fun n ↦ (2 * (π : ℂ) * Complex.I)⁻¹ *
      l.intVerticalAt (l.σ n) (fun s ↦ G_circ s * (x : ℂ) ^ s)) Filter.atTop
      (nhds 0) := by
    have := (lemma_5_1_f (l := l) (G_circ := G_circ) (x₀ := x₀) (x := x)
      hx₀ hx hGc_L).const_mul (2 * (π : ℂ) * Complex.I)⁻¹
    simpa using this
  have th : Filter.Tendsto (fun n ↦
      (↑(π⁻¹ * (l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ))
      Filter.atTop
      (nhds (↑(π⁻¹ * (l.intC (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ)) := by
    have hh := lemma_5_1_h (l := l) (G_star := G_star) (x₀ := x₀) (x := x)
      hx₀ hx hG_star_mero hGs_L hGs_contour
    have him : Filter.Tendsto
        (fun n ↦ (l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im)
        Filter.atTop (nhds ((l.intC (fun s ↦ G_star s * (x : ℂ) ^ s)).im)) :=
      (Complex.continuous_im.tendsto _).comp hh
    exact (Complex.continuous_ofReal.tendsto _).comp (him.const_mul π⁻¹)
  have te : Filter.Tendsto (fun n ↦ (2 * (π : ℂ) * Complex.I)⁻¹ *
      (intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) +
        intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s))) Filter.atTop
      (nhds ((2 * (π : ℂ) * Complex.I)⁻¹ *
        l.intCinf (fun s ↦ G s * (x : ℂ) ^ s))) :=
    (lemma_5_1_e (l := l) (G := G) (G_circ := G_circ) (G_star := G_star)
      (x₀ := x₀) (x := x) hG hG_circ_mero hG_star_mero hx₀ hG_bdd hGc_contour
      hGs_contour hx).const_mul _
  have tg_pos : Filter.Tendsto (fun n ↦ sumResiduesIn
      (fun s ↦ G s * (x : ℂ) ^ s) (l.Rpos ∩ {z | l.σ n < z.re})) Filter.atTop
      (nhds (sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) l.Rpos)) :=
    lemma_5_1_g (l := l) (fun s ↦ G s * (x : ℂ) ^ s) l.Rpos hGmero_pos hfin_pos
  have tg_neg : Filter.Tendsto (fun n ↦ sumResiduesIn
      (fun s ↦ G s * (x : ℂ) ^ s) (l.RposBar ∩ {z | l.σ n < z.re})) Filter.atTop
      (nhds (sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) l.RposBar)) :=
    lemma_5_1_g (l := l) (fun s ↦ G s * (x : ℂ) ^ s) l.RposBar hGmero_neg hfin_neg
  have h_res_add : sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) l.Rpos +
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) l.RposBar =
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.R \ l.RC) :=
    sumResiduesIn_Rpos_add_RposBar l (fun s ↦ G s * (x : ℂ) ^ s) hGmero_pos
      hGmero_neg hGmero_diff hfin h_no_pole_upper h_no_pole_lower
  set RestLim : ℂ :=
    (↑(π⁻¹ * (l.intC (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ) +
      (2 * (π : ℂ) * Complex.I)⁻¹ * l.intCinf (fun s ↦ G s * (x : ℂ) ^ s) +
      sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s) (l.R \ l.RC) with hRestLim
  have t_rest : Filter.Tendsto (fun n ↦
      (2 * (π : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt (l.σ n) (fun s ↦ G_circ s * (x : ℂ) ^ s) +
        (↑(π⁻¹ * (l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ) +
        (2 * (π : ℂ) * Complex.I)⁻¹ *
          (intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) +
            intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s)) +
        (sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s)
            (l.Rpos ∩ {z | l.σ n < z.re}) +
          sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s)
            (l.RposBar ∩ {z | l.σ n < z.re}))) Filter.atTop (nhds RestLim) := by
    have := (((tf.add th).add te).add (tg_pos.add tg_neg))
    rw [hRestLim]
    convert this using 2
    · rw [h_res_add]
      ring
  set rcseq : ℕ → ℂ := fun n ↦ sumResiduesIn (fun s ↦ G_circ s * (x : ℂ) ^ s)
    (l.RC ∩ {z | l.σ n < z.re}) with hrcseq
  set Cst : ℂ := (2 * (π : ℂ) * Complex.I)⁻¹ *
    l.intVerticalAt 1 (fun s ↦ G s * (x : ℂ) ^ s) with hCst
  have t_rc : Filter.Tendsto rcseq Filter.atTop (nhds (Cst - RestLim)) := by
    have h_eq : ∀ᶠ n in Filter.atTop, rcseq n = Cst -
        (fun n ↦ (2 * (π : ℂ) * Complex.I)⁻¹ *
            l.intVerticalAt (l.σ n) (fun s ↦ G_circ s * (x : ℂ) ^ s) +
          (↑(π⁻¹ * (l.intCn1Plus n (fun s ↦ G_star s * (x : ℂ) ^ s)).im) : ℂ) +
          (2 * (π : ℂ) * Complex.I)⁻¹ *
            (intHSeg l.T (l.σ n) 1 (fun s ↦ G s * (x : ℂ) ^ s) +
              intHSeg (-l.T) 1 (l.σ n) (fun s ↦ G s * (x : ℂ) ^ s)) +
          (sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s)
              (l.Rpos ∩ {z | l.σ n < z.re}) +
            sumResiduesIn (fun s ↦ G s * (x : ℂ) ^ s)
              (l.RposBar ∩ {z | l.σ n < z.re}))) n := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have := key n hn
      simp only [hrcseq]
      linear_combination -this
    exact (tendsto_const_nhds.sub t_rest).congr' (Filter.EventuallyEq.symm h_eq)
  have hsumRC : l.sumResiduesLim (fun s ↦ G_circ s * (x : ℂ) ^ s) l.RC =
      Cst - RestLim := t_rc.limUnder_eq
  change Cst = _
  rw [hsumRC, hRestLim]
  ring

end ContourShifting

/-- The rescaling `z(s) = (s - 1)/(iT)` (CH2 §4–5), carrying the central line `1 + i[-T, T]`
onto `[-1, 1]`. -/
noncomputable def LadderParams.zOf (l : LadderParams) (s : ℂ) : ℂ := (s - 1) / (Complex.I * l.T)

/-- The combined Graham–Vaaler weight `Φ^ε_λ` (the paper's `Φ^±_λ`, with the sign `±` carried by
`ε`): `Φ^ε_λ(z) = Phi_circ |λ| ε (sgn λ · z) + sgn λ · sgn (Re z) · Phi_star |λ| ε (sgn λ · z)`. -/
noncomputable def Phi_lambda (lam ε : ℝ) (z : ℂ) : ℂ :=
  Phi_circ |lam| ε ((Real.sign lam : ℂ) * z) +
    (Real.sign lam : ℂ) * (Real.sign z.re : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * z)

/-- For positive `λ`, `Phi_lambda` on `1 + i y` is bounded by `y`. -/
theorem norm_Phi_lambda_one_add_I_mul_le_of_pos (lam ε y : ℝ) (hlam : 0 < lam)
    (hε : ε = 1 ∨ ε = -1) (hy : 0 ≤ y) :
    ‖Phi_lambda lam ε (1 + I * (y : ℂ))‖ ≤ y := by
  have hν : 0 < |lam| := abs_pos.mpr (ne_of_gt hlam)
  have hphi :
      Phi_lambda lam ε (1 + I * (y : ℂ)) = Phi_star |lam| ε (I * (y : ℂ)) := by
    rw [Phi_lambda]
    simp [Real.sign_of_pos hlam, Real.sign_of_pos (by norm_num : (0 : ℝ) < 1),
      shift_upwards_phi_sum |lam| ε hν y hy]
  rw [hphi]
  exact (norm_Phi_star_I_mul_le |lam| ε y hε).trans_eq (abs_of_nonneg hy)

/-- For positive `λ`, `Phi_lambda` on `-1 + i y` is bounded by `y`. -/
theorem norm_Phi_lambda_neg_one_add_I_mul_le_of_pos (lam ε y : ℝ) (hlam : 0 < lam)
    (hε : ε = 1 ∨ ε = -1) (hy : 0 ≤ y) :
    ‖Phi_lambda lam ε (-1 + I * (y : ℂ))‖ ≤ y := by
  have hν : 0 < |lam| := abs_pos.mpr (ne_of_gt hlam)
  have hphi :
      Phi_lambda lam ε (-1 + I * (y : ℂ)) = -Phi_star |lam| ε (I * (y : ℂ)) := by
    have hsign_lam : (Real.sign lam : ℂ) = 1 := by simp [Real.sign_of_pos hlam]
    have hsign_re : (Real.sign ((-1 + I * (y : ℂ)).re) : ℂ) = -1 := by
      simp [Real.sign_of_neg (by norm_num : (-1 : ℝ) < 0)]
    rw [Phi_lambda]
    rw [hsign_lam, hsign_re]
    simp only [one_mul, neg_mul]
    rw [show Phi_circ |lam| ε (-1 + I * ↑y) + -Phi_star |lam| ε (-1 + I * ↑y) =
        Phi_circ |lam| ε (-1 + I * ↑y) - Phi_star |lam| ε (-1 + I * ↑y) by ring]
    exact shift_upwards_phi_diff |lam| ε hν y hy
  rw [hphi, norm_neg]
  exact (norm_Phi_star_I_mul_le |lam| ε y hε).trans_eq (abs_of_nonneg hy)

/-- For negative `λ`, `Phi_lambda` on `1 + i y` is bounded by `y` away from the downward pole. -/
theorem norm_Phi_lambda_one_add_I_mul_le_of_neg (lam ε y : ℝ) (hlam : lam < 0)
    (hε : ε = 1 ∨ ε = -1) (hy : 0 ≤ y) (hpole : y ≠ |lam| / (2 * π)) :
    ‖Phi_lambda lam ε (1 + I * (y : ℂ))‖ ≤ y := by
  have hν : 0 < |lam| := abs_pos.mpr (ne_of_lt hlam)
  have hphi :
      Phi_lambda lam ε (1 + I * (y : ℂ)) = -Phi_star |lam| ε (-I * (y : ℂ)) := by
    have hsign_lam : (Real.sign lam : ℂ) = -1 := by simp [Real.sign_of_neg hlam]
    have hsign_re : (Real.sign ((1 + I * (y : ℂ)).re) : ℂ) = 1 := by
      simp [Real.sign_of_pos (by norm_num : (0 : ℝ) < 1)]
    rw [Phi_lambda]
    rw [hsign_lam, hsign_re]
    simp only [one_mul, neg_mul]
    rw [show -(1 + I * ↑y) = -1 - I * ↑y by ring]
    rw [show Phi_circ |lam| ε (-1 - I * ↑y) + -Phi_star |lam| ε (-1 - I * ↑y) =
        Phi_circ |lam| ε (-1 - I * ↑y) - Phi_star |lam| ε (-1 - I * ↑y) by ring]
    convert shift_downwards_phi_diff |lam| ε hν y hpole using 3
    ring
  rw [hphi, norm_neg]
  exact (norm_Phi_star_neg_I_mul_le |lam| ε y hε).trans_eq (abs_of_nonneg hy)

/-- For negative `λ`, `Phi_lambda` on `-1 + i y` is bounded by `y` away from the downward pole. -/
theorem norm_Phi_lambda_neg_one_add_I_mul_le_of_neg (lam ε y : ℝ) (hlam : lam < 0)
    (hε : ε = 1 ∨ ε = -1) (hy : 0 ≤ y) (hpole : y ≠ |lam| / (2 * π)) :
    ‖Phi_lambda lam ε (-1 + I * (y : ℂ))‖ ≤ y := by
  have hν : 0 < |lam| := abs_pos.mpr (ne_of_lt hlam)
  have hphi :
      Phi_lambda lam ε (-1 + I * (y : ℂ)) = Phi_star |lam| ε (-I * (y : ℂ)) := by
    have hsign_lam : (Real.sign lam : ℂ) = -1 := by simp [Real.sign_of_neg hlam]
    have hsign_re : (Real.sign ((-1 + I * (y : ℂ)).re) : ℂ) = -1 := by
      simp [Real.sign_of_neg (by norm_num : (-1 : ℝ) < 0)]
    rw [Phi_lambda]
    rw [hsign_lam, hsign_re]
    simp only [one_mul, neg_mul]
    rw [show -(-1 + I * ↑y) = 1 - I * ↑y by ring]
    simp only [neg_neg]
    convert shift_downwards_phi_sum |lam| ε hν y hpole using 2
    ring
  rw [hphi]
  exact (norm_Phi_star_neg_I_mul_le |lam| ε y hε).trans_eq (abs_of_nonneg hy)

/-- On the upper horizontal ray of `C∞`, `zOf` has real part `1` and height `(1-r)/T`. -/
theorem LadderParams.zOf_top_hray (l : LadderParams) (r : ℝ) :
    l.zOf (r + l.T * Complex.I) = 1 + Complex.I * (((1 - r) / l.T : ℝ) : ℂ) := by
  rw [LadderParams.zOf]
  field_simp [l.hT.ne']
  ring_nf
  simp [Complex.I_sq]
  field_simp [l.hT.ne']
  ring

/-- On the lower horizontal ray of `C∞`, `zOf` has real part `-1` and height `(1-r)/T`. -/
theorem LadderParams.zOf_bot_hray (l : LadderParams) (r : ℝ) :
    l.zOf (r - l.T * Complex.I) = -1 + Complex.I * (((1 - r) / l.T : ℝ) : ℂ) := by
  rw [LadderParams.zOf]
  field_simp [l.hT.ne']
  ring_nf
  simp [Complex.I_sq]
  field_simp [l.hT.ne']
  ring

/-- The squared norm of the denominator `iT` of the rescaling equals `T²`. -/
theorem LadderParams.normSq_I_mul_T (l : LadderParams) :
    Complex.normSq (Complex.I * (l.T : ℂ)) = l.T ^ 2 := by
  simp [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, sq]

/-- The real part of the rescaling: `Re z(s) = Im s / T`. -/
theorem LadderParams.zOf_re (l : LadderParams) (s : ℂ) : (l.zOf s).re = s.im / l.T := by
  have hT : l.T ≠ 0 := l.hT.ne'
  rw [LadderParams.zOf, Complex.div_re, (by simp : (Complex.I * (l.T : ℂ)).re = 0),
    (by simp : (Complex.I * (l.T : ℂ)).im = l.T), l.normSq_I_mul_T]
  simp only [Complex.sub_im, Complex.one_im, sub_zero, mul_zero, zero_div, zero_add]
  field_simp

/-- The sign of `Re z(s)` agrees with the sign of `Im s` (since `Re z(s) = Im s / T`, `T > 0`). -/
theorem LadderParams.sign_zOf_re (l : LadderParams) (s : ℂ) :
    Real.sign (l.zOf s).re = Real.sign s.im := by
  rw [l.zOf_re]
  rcases lt_trichotomy s.im 0 with h | h | h
  · rw [Real.sign_of_neg (div_neg_of_neg_of_pos h l.hT), Real.sign_of_neg h]
  · rw [h, zero_div]
  · rw [Real.sign_of_pos (div_pos h l.hT), Real.sign_of_pos h]

/-- The rescaling intertwines conjugation with negation: `z(s̄) = -\overline{z(s)}`. -/
theorem LadderParams.zOf_conj (l : LadderParams) (s : ℂ) :
    l.zOf (starRingEnd ℂ s) = -(starRingEnd ℂ (l.zOf s)) := by
  simp only [LadderParams.zOf, map_div₀, map_mul, map_sub, map_one, Complex.conj_I,
    Complex.conj_ofReal]
  field_simp

/-- The rescaling is analytic everywhere (an affine map divided by the nonzero constant `iT`). -/
theorem LadderParams.analyticAt_zOf (l : LadderParams) (c s : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => c * l.zOf w) s := by
  have hden : (Complex.I * (l.T : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero, false_or]
    exact l.hT.ne'
  unfold LadderParams.zOf
  exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).div analyticAt_const hden)

/-- Conjugation symmetry of `Φ^\star`: `Φ^\star(-\overline{w}) = -\overline{Φ^\star(w)}`. This is the
complex-argument generalization of `Phi_star_conj_symm`. -/
theorem Phi_star_conj_neg (ν ε : ℝ) (w : ℂ) :
    Phi_star ν ε (-(starRingEnd ℂ w)) = -(starRingEnd ℂ (Phi_star ν ε w)) := by
  dsimp [Phi_star]
  simp only [neg_mul, map_div₀, map_sub, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [B_conj]
  simp only [map_add, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [B_conj]
  simp only [Complex.conj_ofReal]
  rw [show -(2 * (π : ℂ) * I * -(starRingEnd ℂ) w) + (ν : ℂ)
        = -(2 * (π : ℂ) * -I * (starRingEnd ℂ) w) + (ν : ℂ) by ring,
    mul_neg, div_neg, neg_neg]

/-- The imaginary part of the rescaling: `Im z(s) = (1 - Re s)/T` (hence `≥ 0` on `R`). -/
theorem LadderParams.zOf_im (l : LadderParams) (s : ℂ) : (l.zOf s).im = (1 - s.re) / l.T := by
  rw [LadderParams.zOf, Complex.div_im, (by simp : (Complex.I * (l.T : ℂ)).re = 0),
    (by simp : (Complex.I * (l.T : ℂ)).im = l.T), l.normSq_I_mul_T]
  simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.sub_re, Complex.one_re,
    mul_zero]
  field_simp [l.hT.ne']
  ring

/-- The rescaling sends `{Re s ≤ 1}` (in particular `R`) into the closed upper half-plane. -/
theorem LadderParams.zOf_im_nonneg (l : LadderParams) {s : ℂ} (hs : s.re ≤ 1) :
    0 ≤ (l.zOf s).im := by
  rw [l.zOf_im]; exact div_nonneg (by linarith) l.hT.le

/-- Restriction of `IsBoundedNoPolesOn` to a subset. -/
lemma IsBoundedNoPolesOn.mono {f : ℂ → ℂ} {S T : Set ℂ} (h : IsBoundedNoPolesOn f T)
    (hST : S ⊆ T) : IsBoundedNoPolesOn f S := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun z hz ↦ hM z (hST hz)⟩

/-- Multiplying a bounded-with-no-poles function by an analytic factor that is uniformly bounded on
the set preserves `IsBoundedNoPolesOn`. -/
lemma IsBoundedNoPolesOn.analytic_mul {g h : ℂ → ℂ} {S : Set ℂ} {C : ℝ}
    (hh : IsBoundedNoPolesOn h S) (hh_mero : ∀ z ∈ S, MeromorphicAt h z)
    (hg_an : ∀ z ∈ S, AnalyticAt ℂ g z) (hg_bd : ∀ z ∈ S, ‖g z‖ ≤ C) :
    IsBoundedNoPolesOn (fun s ↦ g s * h s) S := by
  obtain ⟨M, hM⟩ := hh
  refine ⟨C * M, fun z hz ↦ ⟨?_, ?_⟩⟩
  · have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hg_bd z hz)
    calc ‖g z * h z‖ = ‖g z‖ * ‖h z‖ := norm_mul _ _
      _ ≤ C * ‖h z‖ := mul_le_mul_of_nonneg_right (hg_bd z hz) (norm_nonneg _)
      _ ≤ C * M := mul_le_mul_of_nonneg_left (hM z hz).1 hCnn
  · rw [show (fun s ↦ g s * h s) = g * h from rfl,
      meromorphicOrderAt_mul (hg_an z hz).meromorphicAt (hh_mero z hz)]
    exact add_nonneg (hg_an z hz).meromorphicOrderAt_nonneg (hM z hz).2

/-- Norm arithmetic for a linearly-growing factor: from `‖φ‖ ≤ C(‖w‖+1)`, a bound `‖h‖ ≤ Mh`, and a
bound `‖w‖·‖h‖ ≤ Mwh` on the weighted product, conclude `‖φ·h‖ ≤ |C|·Mwh + |C|·Mh`. -/
private lemma norm_mul_le_of_linear_growth {φ w h : ℂ} {C Mh Mwh : ℝ}
    (hφ : ‖φ‖ ≤ C * (‖w‖ + 1)) (hh : ‖h‖ ≤ Mh) (hwh : ‖w‖ * ‖h‖ ≤ Mwh) :
    ‖φ * h‖ ≤ |C| * Mwh + |C| * Mh := by
  have hCnn : (0 : ℝ) ≤ |C| := abs_nonneg C
  have hb1 : ‖φ‖ ≤ |C| * (‖w‖ + 1) :=
    hφ.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  calc ‖φ * h‖ = ‖φ‖ * ‖h‖ := norm_mul _ _
    _ ≤ |C| * (‖w‖ + 1) * ‖h‖ := mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
    _ = |C| * (‖w‖ * ‖h‖) + |C| * ‖h‖ := by ring
    _ ≤ |C| * Mwh + |C| * Mh :=
        add_le_add (mul_le_mul_of_nonneg_left hwh hCnn) (mul_le_mul_of_nonneg_left hh hCnn)

/-- Multiplying a bounded-with-no-poles function `h` by an analytic factor `φ` whose growth is
controlled by a weight `w` — `‖φ‖ ≤ C(‖w‖+1)` — preserves `IsBoundedNoPolesOn`, provided the
weighted product `w · h` is itself bounded with no poles. (Used for the `Φ^\star = O(|z|)` factors:
the linear growth is absorbed by the extra decay of `w · h = z(s) · F · x₀^s`.) -/
lemma IsBoundedNoPolesOn.linear_mul {φ w h : ℂ → ℂ} {S : Set ℂ} {C : ℝ}
    (hh : IsBoundedNoPolesOn h S) (hwh : IsBoundedNoPolesOn (fun s ↦ w s * h s) S)
    (hh_mero : ∀ z ∈ S, MeromorphicAt h z)
    (hφ_an : ∀ z ∈ S, AnalyticAt ℂ φ z) (hφ_bd : ∀ z ∈ S, ‖φ z‖ ≤ C * (‖w z‖ + 1)) :
    IsBoundedNoPolesOn (fun s ↦ φ s * h s) S := by
  obtain ⟨Mh, hMh⟩ := hh
  obtain ⟨Mwh, hMwh⟩ := hwh
  refine ⟨|C| * Mwh + |C| * Mh, fun z hz ↦ ⟨?_, ?_⟩⟩
  · have hwh_z : ‖w z‖ * ‖h z‖ ≤ Mwh := by
      have := (hMwh z hz).1; rwa [norm_mul] at this
    exact norm_mul_le_of_linear_growth (hφ_bd z hz) (hMh z hz).1 hwh_z
  · rw [show (fun s ↦ φ s * h s) = φ * h from rfl,
      meromorphicOrderAt_mul (hφ_an z hz).meromorphicAt (hh_mero z hz)]
    exact add_nonneg (hφ_an z hz).meromorphicOrderAt_nonneg (hMh z hz).2

/-- If `f` is bounded on a punctured neighborhood of `z`, its meromorphic order there is `≥ 0`.
(If `f` is not meromorphic at `z` the order is the junk value `0`; otherwise a negative order would
force `f → ∞`, contradicting the bound.) -/
lemma meromorphicOrderAt_nonneg_of_eventually_bounded {f : ℂ → ℂ} {z : ℂ} {M : ℝ}
    (hbdd : ∀ᶠ s in nhdsWithin z {z}ᶜ, ‖f s‖ ≤ M) : 0 ≤ meromorphicOrderAt f z := by
  by_cases hmero : MeromorphicAt f z
  · rw [← not_lt, ← tendsto_cobounded_iff_meromorphicOrderAt_neg hmero,
      ← tendsto_norm_atTop_iff_cobounded]
    intro htend
    obtain ⟨s, hs1, hs2⟩ := ((htend.eventually_gt_atTop M).and hbdd).exists
    exact absurd hs1 (not_lt.mpr hs2)
  · rw [meromorphicOrderAt_of_not_meromorphicAt hmero]

/-- The complex sign factor `(sgn x : ℂ)` has norm `≤ 1`. -/
private lemma norm_sign_le (x : ℝ) : ‖(Real.sign x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [h, Real.sign_zero]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

/-- For `λ > 0`, the complex sign factor `(sgn λ : ℂ)` is `1`. -/
private lemma sign_cast_one_of_pos {lam : ℝ} (hlam : 0 < lam) : (Real.sign lam : ℂ) = 1 := by
  rw [Real.sign_of_pos hlam]; norm_num

/-- For `λ > 0`, `Φ^\circ(|λ| · w)` is uniformly bounded on the closed upper half-plane. -/
private lemma exists_norm_Phi_circ_bound {lam : ℝ} (hlam : 0 < lam) (ε : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, 0 ≤ w.im → ‖Phi_circ |lam| ε w‖ ≤ C := by
  have hν : (0 : ℝ) < |lam| := abs_pos.mpr hlam.ne'
  have hc : (0 : ℝ) > -|lam| / (2 * π) :=
    div_neg_of_neg_of_pos (by linarith [hν]) (by positivity)
  obtain ⟨C, hC⟩ := ϕ_circ_bound_right |lam| |lam| ε 0 hc
  exact ⟨C, fun w hw ↦ hC |lam| (by simp) w hw⟩

/-- For `λ > 0`, `Φ^\star(|λ| · w)` grows at most linearly on the closed upper half-plane. -/
private lemma exists_norm_Phi_star_bound {lam : ℝ} (hlam : 0 < lam) (ε : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, 0 ≤ w.im → ‖Phi_star |lam| ε w‖ ≤ C * (‖w‖ + 1) := by
  have hν : (0 : ℝ) < |lam| := abs_pos.mpr hlam.ne'
  have hc : (0 : ℝ) > -|lam| / (2 * π) :=
    div_neg_of_neg_of_pos (by linarith [hν]) (by positivity)
  obtain ⟨C, hC⟩ := ϕ_star_bound_right |lam| |lam| ε 0 hν le_rfl hc
  exact ⟨C, fun w hw ↦ hC |lam| (by simp) w hw⟩

/-- Pointwise: `Φ_λ(w)` is bounded by `‖Φ^\circ(sgn λ·w)‖ + ‖Φ^\star(sgn λ·w)‖` (the `sgn` factors
have norm `≤ 1`). -/
private lemma norm_Phi_lambda_le_sum (lam ε : ℝ) (w : ℂ) :
    ‖Phi_lambda lam ε w‖ ≤
      ‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * w)‖ +
        ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * w)‖ := by
  rw [Phi_lambda]
  refine (norm_add_le _ _).trans ?_
  gcongr
  rw [norm_mul, norm_mul]
  calc ‖(Real.sign lam : ℂ)‖ * ‖(Real.sign w.re : ℂ)‖ *
        ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * w)‖
      ≤ 1 * 1 * ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * w)‖ := by
        gcongr
        · exact norm_sign_le lam
        · exact norm_sign_le w.re
    _ = ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * w)‖ := by ring

/-- For `λ > 0`, `Φ_λ(w)` is `O(|w|)` on the closed upper half-plane: it is bounded by
`‖Φ^\circ(w)‖ + ‖Φ^\star(w)‖` (the `sgn` factors have norm `≤ 1`), each `O(|w|)`. -/
private lemma norm_Phi_lambda_le_of_im_nonneg {lam ε : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, ∀ w : ℂ, 0 ≤ w.im → ‖Phi_lambda lam ε w‖ ≤ C * (‖w‖ + 1) := by
  have hsign : (Real.sign lam : ℂ) = 1 := sign_cast_one_of_pos hlam
  obtain ⟨C₁, hC₁⟩ := exists_norm_Phi_circ_bound hlam ε
  obtain ⟨C₂, hC₂⟩ := exists_norm_Phi_star_bound hlam ε
  refine ⟨|C₁| + |C₂|, fun w hw ↦ ?_⟩
  have hwim : ((Real.sign lam : ℂ) * w).im ≥ 0 := by rw [hsign, one_mul]; exact hw
  have hwnorm : ‖(Real.sign lam : ℂ) * w‖ = ‖w‖ := by rw [hsign, one_mul]
  have e1 : ‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * w)‖ ≤ C₁ := hC₁ _ hwim
  have e2 : ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * w)‖ ≤ C₂ * (‖w‖ + 1) := by
    rw [← hwnorm]; exact hC₂ _ hwim
  calc ‖Phi_lambda lam ε w‖
      ≤ ‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * w)‖ +
          ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * w)‖ := norm_Phi_lambda_le_sum lam ε w
    _ ≤ C₁ + C₂ * (‖w‖ + 1) := add_le_add e1 e2
    _ ≤ |C₁| * (‖w‖ + 1) + |C₂| * (‖w‖ + 1) := by
        gcongr
        · exact (le_abs_self C₁).trans
            (le_mul_of_one_le_right (abs_nonneg _) (by linarith [norm_nonneg w]))
        · exact le_abs_self C₂
    _ = (|C₁| + |C₂|) * (‖w‖ + 1) := by ring

/-- For `λ > 0`, the factor `Φ^\circ(sgn λ · z(s))` is analytic and uniformly bounded on any subset
of `R` (its argument has `Im ≥ 0`, away from the poles, and `coth` is bounded there). Hence on such
a set `Φ^\circ(sgn λ · z(s)) · F · x₀^s` inherits `IsBoundedNoPolesOn` from `F · x₀^s`. -/
private lemma isBoundedNoPolesOn_Phi_circ_mul (l : LadderParams) {F : ℂ → ℂ} {lam ε x₀ : ℝ}
    (hlam : 0 < lam) (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    {S : Set ℂ} (hS : S ⊆ l.R)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) S) :
    IsBoundedNoPolesOn
      (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x₀ : ℂ) ^ s) S := by
  have hν : (0 : ℝ) < |lam| := abs_pos.mpr hlam.ne'
  have hx₀_pos : (0 : ℝ) < x₀ := by linarith
  have hsign : (Real.sign lam : ℂ) = 1 := sign_cast_one_of_pos hlam
  obtain ⟨C, hC⟩ := exists_norm_Phi_circ_bound hlam ε
  simp only [mul_assoc]
  refine hF_bdd.analytic_mul (C := C)
    (fun z hz ↦ (hF_mero z (hS hz)).mul (meromorphicAt_rpow hx₀_pos z))
    (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · have him : (0 : ℝ) ≤ ((Real.sign lam : ℂ) * l.zOf z).im := by
      rw [hsign, one_mul]; exact l.zOf_im_nonneg (hS hz).1
    exact (Phi_circ.analyticAt_of_im_nonneg |lam| ε ((Real.sign lam : ℂ) * l.zOf z) hν
      him).comp_of_eq (l.analyticAt_zOf (Real.sign lam : ℂ) z) rfl
  · rw [hsign, one_mul]
    exact hC (l.zOf z) (l.zOf_im_nonneg (hS hz).1)

/-- For `λ > 0`, the factor `sgn λ · Φ^\star(sgn λ · z(s))` is analytic and `O(|z(s)|)` on any
subset of `R`. Combined with the weighted bound on `z(s) · F · x₀^s` (the strengthened decay
hypothesis on `F`), the product `sgn λ · Φ^\star(sgn λ · z(s)) · F · x₀^s` is bounded with no
poles. -/
private lemma isBoundedNoPolesOn_Phi_star_mul (l : LadderParams) {F : ℂ → ℂ} {lam ε x₀ : ℝ}
    (hlam : 0 < lam) (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    {S : Set ℂ} (hS : S ⊆ l.R)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) S)
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) S) :
    IsBoundedNoPolesOn
      (fun s ↦ (Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
        F s * (x₀ : ℂ) ^ s) S := by
  have hν : (0 : ℝ) < |lam| := abs_pos.mpr hlam.ne'
  have hx₀_pos : (0 : ℝ) < x₀ := by linarith
  have hsign : (Real.sign lam : ℂ) = 1 := sign_cast_one_of_pos hlam
  obtain ⟨C, hC⟩ := exists_norm_Phi_star_bound hlam ε
  have him : ∀ z ∈ S, (0 : ℝ) ≤ ((Real.sign lam : ℂ) * l.zOf z).im := by
    intro z hz
    rw [hsign, one_mul]; exact l.zOf_im_nonneg (hS hz).1
  have hwh : IsBoundedNoPolesOn (fun s ↦ l.zOf s * (F s * (x₀ : ℂ) ^ s)) S := by
    have heqw : (fun s ↦ l.zOf s * (F s * (x₀ : ℂ) ^ s))
        = (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) := by funext s; ring
    rw [heqw]; exact hFw_bdd
  have heq :
      (fun s ↦ (Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
          F s * (x₀ : ℂ) ^ s)
        = (fun s ↦ ((Real.sign lam : ℂ) * Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) *
          (F s * (x₀ : ℂ) ^ s)) := by funext s; ring
  rw [heq]
  refine hF_bdd.linear_mul (w := l.zOf) (C := C) hwh
    (fun z hz ↦ (hF_mero z (hS hz)).mul (meromorphicAt_rpow hx₀_pos z))
    (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · exact analyticAt_const.mul
      ((Phi_star.analyticAt_of_im_nonneg |lam| ε ((Real.sign lam : ℂ) * l.zOf z) hν
        (him z hz)).comp_of_eq (l.analyticAt_zOf (Real.sign lam : ℂ) z) rfl)
  · rw [norm_mul, hsign]
    simp only [norm_one, one_mul]
    exact hC (l.zOf z) (l.zOf_im_nonneg (hS hz).1)

/-- The order of `Φ_λ(z(s)) · F · x₀^s` at a point `z ∈ R` is `≥ 0`: `Φ_λ ∘ z` has a `sgn`
discontinuity at `Im s = 0` (so the product may be non-meromorphic there, giving junk order `0`),
but it is bounded near `z` (`Φ^\circ, Φ^\star` are continuous at `z(z)` and `F · x₀^s` converges
since its order is `≥ 0`), so the order is `≥ 0`. -/
private lemma meromorphicOrderAt_Phi_lambda_mul_nonneg (l : LadderParams) {F : ℂ → ℂ}
    {lam ε x₀ : ℝ} (hlam : 0 < lam) (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    {z : ℂ} (hz : z ∈ l.R)
    (hFord : 0 ≤ meromorphicOrderAt (fun s ↦ F s * (x₀ : ℂ) ^ s) z) :
    0 ≤ meromorphicOrderAt (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x₀ : ℂ) ^ s) z := by
  have hν : (0 : ℝ) < |lam| := abs_pos.mpr hlam.ne'
  have hx₀_pos : (0 : ℝ) < x₀ := by linarith
  have hsign : (Real.sign lam : ℂ) = 1 := sign_cast_one_of_pos hlam
  have hsign_im : (0 : ℝ) ≤ ((Real.sign lam : ℂ) * l.zOf z).im := by
    rw [hsign, one_mul]; exact l.zOf_im_nonneg hz.1
  have hφc : ContinuousAt (fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) z :=
    ((Phi_circ.analyticAt_of_im_nonneg |lam| ε _ hν hsign_im).comp_of_eq
      (l.analyticAt_zOf (Real.sign lam : ℂ) z) rfl).continuousAt
  have hφs : ContinuousAt (fun s ↦ Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) z :=
    ((Phi_star.analyticAt_of_im_nonneg |lam| ε _ hν hsign_im).comp_of_eq
      (l.analyticAt_zOf (Real.sign lam : ℂ) z) rfl).continuousAt
  have hFp_mero : MeromorphicAt (fun s ↦ F s * (x₀ : ℂ) ^ s) z :=
    (hF_mero z hz).mul (meromorphicAt_rpow hx₀_pos z)
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hFp_mero hFord
  set L : ℝ := (‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf z)‖ +
      ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf z)‖) * ‖c‖ with hLdef
  have hg : Filter.Tendsto
      (fun s ↦ (‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖ +
        ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖) * ‖F s * (x₀ : ℂ) ^ s‖)
      (nhdsWithin z {z}ᶜ) (nhds L) :=
    ((((hφc.norm).tendsto.mono_left nhdsWithin_le_nhds).add
      ((hφs.norm).tendsto.mono_left nhdsWithin_le_nhds)).mul hc.norm)
  refine meromorphicOrderAt_nonneg_of_eventually_bounded (M := L + 1) ?_
  filter_upwards [hg.eventually_lt_const (lt_add_one L)] with s hs
  calc ‖Phi_lambda lam ε (l.zOf s) * F s * (x₀ : ℂ) ^ s‖
      = ‖Phi_lambda lam ε (l.zOf s)‖ * ‖F s * (x₀ : ℂ) ^ s‖ := by rw [mul_assoc, norm_mul]
    _ ≤ (‖Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖ +
          ‖Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s)‖) * ‖F s * (x₀ : ℂ) ^ s‖ :=
        mul_le_mul_of_nonneg_right (norm_Phi_lambda_le_sum lam ε (l.zOf s)) (norm_nonneg _)
    _ ≤ L + 1 := le_of_lt hs

/-- For `λ > 0`, the factor `Φ_λ(z(s))` is `O(|z(s)|)` on `R` (its argument has `Im ≥ 0`), so on a
subset of `R` the product `Φ_λ(z(s)) · F · x₀^s` is bounded with no poles, given the bound on
`F · x₀^s` and the growth-weighted bound on `z(s) · F · x₀^s`. -/
private lemma isBoundedNoPolesOn_Phi_lambda_mul (l : LadderParams) {F : ℂ → ℂ} {lam ε x₀ : ℝ}
    (hlam : 0 < lam) (hx₀ : 1 ≤ x₀) (hF_mero : MeromorphicOn F l.R)
    {S : Set ℂ} (hS : S ⊆ l.R)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) S)
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s) S) :
    IsBoundedNoPolesOn (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x₀ : ℂ) ^ s) S := by
  obtain ⟨Cl, hCl⟩ := norm_Phi_lambda_le_of_im_nonneg (ε := ε) hlam
  obtain ⟨Mh, hMh⟩ := hF_bdd
  obtain ⟨Mwh, hMwh⟩ := hFw_bdd
  refine ⟨|Cl| * Mwh + |Cl| * Mh, fun z hz ↦ ⟨?_, ?_⟩⟩
  · have hwh_z : ‖l.zOf z‖ * ‖F z * (x₀ : ℂ) ^ z‖ ≤ Mwh := by
      have h := (hMwh z hz).1
      change ‖l.zOf z * F z * (x₀ : ℂ) ^ z‖ ≤ Mwh at h
      rwa [mul_assoc, norm_mul] at h
    change ‖Phi_lambda lam ε (l.zOf z) * F z * (x₀ : ℂ) ^ z‖ ≤ |Cl| * Mwh + |Cl| * Mh
    rw [mul_assoc]
    exact norm_mul_le_of_linear_growth (hCl (l.zOf z) (l.zOf_im_nonneg (hS hz).1))
      (hMh z hz).1 hwh_z
  · exact meromorphicOrderAt_Phi_lambda_mul_nonneg l hlam hx₀ hF_mero (hS hz) (hMh z hz).2

/-- Change variables from the left ray `(-∞, 1]` to the positive half-line by `t = 1-r`. -/
theorem integral_Iic_one_eq_integral_Ioi_one_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ r in Set.Iic (1 : ℝ), f r) = ∫ t in Set.Ioi (0 : ℝ), f (1 - t) := by
  have hshift : (∫ x in Set.Iic (0 : ℝ), f (1 + x)) = ∫ x in Set.Iic (1 : ℝ), f x := by
    have A : MeasurableEmbedding (fun x : ℝ => 1 + x) :=
      (Homeomorph.addLeft (1 : ℝ)).measurableEmbedding
    have h := MeasurableEmbedding.setIntegral_map (μ := volume) A f (Set.Iic (1 : ℝ))
    rw [map_add_left_eq_self volume (1 : ℝ)] at h
    have hpre : (fun x : ℝ => 1 + x) ⁻¹' Set.Iic (1 : ℝ) = Set.Iic (0 : ℝ) := by
      ext x
      simp [Set.mem_Iic]
    rw [hpre] at h
    exact h.symm
  have hneg := integral_comp_neg_Iic (c := (0 : ℝ)) (f := fun t : ℝ => f (1 - t))
  rw [neg_zero] at hneg
  rw [← hneg]
  rw [← hshift]
  refine setIntegral_congr_fun (measurableSet_Iic : MeasurableSet (Set.Iic (0 : ℝ))) ?_
  intro x hx
  congr 1
  ring

/-- Lebesgue measure is invariant under the reflection-translation `r ↦ 1 - r`. -/
private theorem map_subLeft_one_eq_self : Measure.map (fun x : ℝ => 1 - x) volume = volume := by
  have hmap : Measure.map (fun x : ℝ => 1 + -x) volume = volume := by
    have hfun : (fun x : ℝ => 1 + -x) = (fun y : ℝ => 1 + y) ∘ (fun x : ℝ => -x) := rfl
    rw [hfun, ← Measure.map_map (g := fun y : ℝ => 1 + y) (f := fun x : ℝ => -x)
      (measurable_const.add measurable_id) measurable_neg]
    rw [Measure.map_neg_eq_self, map_add_left_eq_self]
  convert! hmap using 1

/-- The weighted exponential majorant needed on the horizontal rays of `C∞`. -/
private lemma integrableOn_one_sub_mul_exp_mul_Iic (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => (1 - r) * Real.exp (a * r)) (Set.Iic (1 : ℝ)) := by
  have hmp : MeasurePreserving (fun x : ℝ => 1 - x) volume volume :=
    ⟨measurable_const.sub measurable_id, map_subLeft_one_eq_self⟩
  have hpre : (fun x : ℝ => 1 - x) ⁻¹' Set.Ici (0 : ℝ) = Set.Iic (1 : ℝ) := by
    ext x
    simp [Set.mem_Iic]
  have hbase :
      IntegrableOn (fun t : ℝ => t ^ (1 : ℝ) * Real.exp (-a * t ^ (1 : ℝ)))
        (Set.Ioi (0 : ℝ)) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : (-1 : ℝ) < 1) le_rfl ha
  have hbase_Ici :
      IntegrableOn (fun t : ℝ => t ^ (1 : ℝ) * Real.exp (-a * t ^ (1 : ℝ)))
        (Set.Ici (0 : ℝ)) :=
    hbase.congr_set_ae (Ioi_ae_eq_Ici : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ici (0 : ℝ)).symm
  have hcomp :=
    (hmp.integrableOn_comp_preimage (Homeomorph.subLeft (1 : ℝ)).measurableEmbedding).2 hbase_Ici
  rw [hpre] at hcomp
  have hscaled :
      IntegrableOn
        (fun r : ℝ =>
          Real.exp a * (((1 - r) ^ (1 : ℝ)) * Real.exp (-a * ((1 - r) ^ (1 : ℝ)))))
        (Set.Iic (1 : ℝ)) :=
    hcomp.const_mul (Real.exp a)
  refine hscaled.congr_fun ?_ measurableSet_Iic
  intro r hr
  change
    Real.exp a * ((1 - r) ^ (1 : ℝ) * Real.exp (-a * (1 - r) ^ (1 : ℝ))) =
      (1 - r) * Real.exp (a * r)
  rw [Real.rpow_one]
  rw [show -a * (1 - r) = -a + a * r by ring]
  rw [Real.exp_add]
  ring_nf
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- The affine height `r ↦ (1-r)/T` avoids any prescribed value a.e. on the horizontal ray. -/
private lemma ae_one_sub_div_ne (T c : ℝ) (hT : T ≠ 0) :
    ∀ᵐ r ∂volume.restrict (Set.Iic (1 : ℝ)), (1 - r) / T ≠ c := by
  have hsingleton :
      {r : ℝ | (1 - r) / T = c} = {1 - T * c} := by
    ext r
    constructor
    · intro hr
      rw [Set.mem_singleton_iff]
      have hmul : 1 - r = T * c := by
        field_simp [hT] at hr
        exact hr
      linarith
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      rw [hr]
      change (1 - (1 - T * c)) / T = c
      field_simp [hT]
      ring
  rw [ae_iff]
  simpa only [not_not, hsingleton] using
    (measure_mono_null (by intro r hr; exact hr)
      (by simp [MeasureTheory.measure_singleton]) :
        (volume.restrict (Set.Iic (1 : ℝ))) {1 - T * c} = 0)

section Proposition52

/- Shared context for Proposition 5.2 and its sub-lemmas: the ladder parameters `l`, the
meromorphic function `F`, the parameter `λ` (`lam`) and sign `ε`, and the reals `x₀ ≤ x`. The
structural (`Prop`) hypotheses stay explicit on each lemma. -/
variable {l : LadderParams} {F : ℂ → ℂ} {lam ε x₀ x : ℝ}

private lemma ae_norm_Phi_lambda_top_hray_le (hlam : lam ≠ 0) (hε : ε = 1 ∨ ε = -1) :
    ∀ᵐ r : ℝ ∂volume.restrict (Set.Iic (1 : ℝ)),
      ‖Phi_lambda lam ε (l.zOf ((r : ℂ) + l.T * Complex.I))‖ ≤ (1 - r) / l.T := by
  by_cases hpos : 0 < lam
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with r hr
    have hy : 0 ≤ (1 - r) / l.T := div_nonneg (sub_nonneg.mpr (by simpa using hr)) l.hT.le
    rw [LadderParams.zOf_top_hray]
    exact norm_Phi_lambda_one_add_I_mul_le_of_pos lam ε ((1 - r) / l.T) hpos hε hy
  · have hneg : lam < 0 := lt_of_le_of_ne (not_lt.mp hpos) hlam
    filter_upwards [ae_one_sub_div_ne l.T (|lam| / (2 * π)) l.hT.ne',
      MeasureTheory.ae_restrict_mem measurableSet_Iic] with r hpole hr
    have hy : 0 ≤ (1 - r) / l.T := div_nonneg (sub_nonneg.mpr (by simpa using hr)) l.hT.le
    rw [LadderParams.zOf_top_hray]
    exact norm_Phi_lambda_one_add_I_mul_le_of_neg lam ε ((1 - r) / l.T) hneg hε hy hpole

private lemma ae_norm_Phi_lambda_bot_hray_le (hlam : lam ≠ 0) (hε : ε = 1 ∨ ε = -1) :
    ∀ᵐ r : ℝ ∂volume.restrict (Set.Iic (1 : ℝ)),
      ‖Phi_lambda lam ε (l.zOf ((r : ℂ) + ((-l.T : ℝ) : ℂ) * Complex.I))‖ ≤
        (1 - r) / l.T := by
  by_cases hpos : 0 < lam
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with r hr
    have hy : 0 ≤ (1 - r) / l.T := div_nonneg (sub_nonneg.mpr (by simpa using hr)) l.hT.le
    rw [show (r : ℂ) + ((-l.T : ℝ) : ℂ) * Complex.I = r - (l.T : ℂ) * Complex.I by
      rw [Complex.ofReal_neg]
      ring]
    rw [LadderParams.zOf_bot_hray]
    exact norm_Phi_lambda_neg_one_add_I_mul_le_of_pos lam ε ((1 - r) / l.T) hpos hε hy
  · have hneg : lam < 0 := lt_of_le_of_ne (not_lt.mp hpos) hlam
    filter_upwards [ae_one_sub_div_ne l.T (|lam| / (2 * π)) l.hT.ne',
      MeasureTheory.ae_restrict_mem measurableSet_Iic] with r hpole hr
    have hy : 0 ≤ (1 - r) / l.T := div_nonneg (sub_nonneg.mpr (by simpa using hr)) l.hT.le
    rw [show (r : ℂ) + ((-l.T : ℝ) : ℂ) * Complex.I = r - (l.T : ℂ) * Complex.I by
      rw [Complex.ofReal_neg]
      ring]
    rw [LadderParams.zOf_bot_hray]
    exact norm_Phi_lambda_neg_one_add_I_mul_le_of_neg lam ε ((1 - r) / l.T) hneg hε hy hpole

private lemma weighted_F_mul_cpow_norm_integrable_hray (h : ℝ)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (h_abs_h : |h| = l.T)
    (hF_mero : MeromorphicOn F l.R)
    (hF_Rbd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.Rboundary) :
    IntegrableOn
      (fun r : ℝ => ((1 - r) / l.T) *
        ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖)
      (Set.Iic (1 : ℝ)) := by
  obtain ⟨M, hM⟩ := hF_Rbd
  let C : ℝ := max M 0
  have hx₀_pos : 0 < x₀ := by linarith
  have hx_pos : 0 < x := by linarith
  have hlog_ratio_pos : 0 < Real.log (x / x₀) := by
    exact Real.log_pos (by rw [one_lt_div hx₀_pos]; linarith)
  have h_int_bound :
      IntegrableOn
        (fun r : ℝ => (C / l.T) * ((1 - r) * Real.exp (Real.log (x / x₀) * r)))
        (Set.Iic (1 : ℝ)) :=
    (integrableOn_one_sub_mul_exp_mul_Iic (Real.log (x / x₀)) hlog_ratio_pos).const_mul
      (C / l.T)
  have h_order : ∀ z ∈ l.Rboundary, z.im = h → 0 ≤ meromorphicOrderAt F z := by
    intro z hz_Rbd _hz_im
    exact meromorphicOrderAt_nonneg_of_bounded hx₀ (hF_mero z (l.Rboundary_subset_R hz_Rbd))
      ⟨M, hM⟩ hz_Rbd
  have h_meas_prod :
      AEStronglyMeasurable
        (fun r : ℝ ↦ F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I))
        (volume.restrict (Set.Iic (1 : ℝ))) :=
    aestronglyMeasurable_hray_of_meromorphic l F x₀ x h hx₀ hx h_abs_h hF_mero h_order
  have h_meas_weight :
      AEStronglyMeasurable (fun r : ℝ => (1 - r) / l.T)
        (volume.restrict (Set.Iic (1 : ℝ))) :=
    ((measurable_const.sub measurable_id).div_const l.T).aestronglyMeasurable
  have h_meas :
      AEStronglyMeasurable
        (fun r : ℝ => ((1 - r) / l.T) *
          ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖)
        (volume.restrict (Set.Iic (1 : ℝ))) :=
    h_meas_weight.mul h_meas_prod.norm
  refine h_int_bound.mono' h_meas ?_
  rw [ae_restrict_iff' measurableSet_Iic]
  refine ae_of_all _ ?_
  intro r hr
  have hr_le : r ≤ 1 := by simpa using hr
  have hweight_nonneg : 0 ≤ (1 - r) / l.T :=
    div_nonneg (sub_nonneg.mpr hr_le) l.hT.le
  have hbound :
      ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖ ≤
        C * Real.exp (Real.log (x / x₀) * r) := by
    simpa [C] using
      bound_G_mul_cpow_hray l F x₀ x h M hx₀ hx h_abs_h (fun z hz => (hM z hz).1) r hr_le
  have hnorm_nonneg :
      0 ≤ ((1 - r) / l.T) *
        ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖ :=
    mul_nonneg hweight_nonneg (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnorm_nonneg]
  calc
    ((1 - r) / l.T) *
        ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖
        ≤ ((1 - r) / l.T) * (C * Real.exp (Real.log (x / x₀) * r)) :=
          mul_le_mul_of_nonneg_left hbound hweight_nonneg
    _ = (C / l.T) * ((1 - r) * Real.exp (Real.log (x / x₀) * r)) := by ring

private lemma norm_intHRay_Phi_lambda_le_weighted (h : ℝ)
    (hx₀ : 1 ≤ x₀) (hx : x₀ < x) (h_abs_h : |h| = l.T)
    (hF_mero : MeromorphicOn F l.R)
    (hF_Rbd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.Rboundary)
    (hPhi :
      ∀ᵐ r : ℝ ∂volume.restrict (Set.Iic (1 : ℝ)),
        ‖Phi_lambda lam ε (l.zOf ((r : ℂ) + h * Complex.I))‖ ≤ (1 - r) / l.T) :
    ‖intHRay h 1 (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s)‖ ≤
      ∫ r in Set.Iic (1 : ℝ), ((1 - r) / l.T) *
        ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖ := by
  have h_int_weighted :
      Integrable
        (fun r : ℝ => ((1 - r) / l.T) *
          ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖)
        (volume.restrict (Set.Iic (1 : ℝ))) := by
    simpa [IntegrableOn] using
      weighted_F_mul_cpow_norm_integrable_hray (l := l) (F := F) (x₀ := x₀) (x := x)
        h hx₀ hx h_abs_h hF_mero hF_Rbd
  have h_bound :
      ∀ᵐ r : ℝ ∂volume.restrict (Set.Iic (1 : ℝ)),
        ‖Phi_lambda lam ε (l.zOf ((r : ℂ) + h * Complex.I)) *
            F ((r : ℂ) + h * Complex.I) *
            (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖ ≤
          ((1 - r) / l.T) *
            ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖ := by
    filter_upwards [hPhi] with r hPhi_r
    calc
      ‖Phi_lambda lam ε (l.zOf ((r : ℂ) + h * Complex.I)) *
          F ((r : ℂ) + h * Complex.I) *
          (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖
          = ‖Phi_lambda lam ε (l.zOf ((r : ℂ) + h * Complex.I))‖ *
              ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖ := by
            rw [mul_assoc, norm_mul]
      _ ≤ ((1 - r) / l.T) *
              ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖ :=
            mul_le_mul_of_nonneg_right hPhi_r (norm_nonneg _)
  simpa [intHRay] using norm_integral_le_of_norm_le h_int_weighted h_bound

private lemma integral_weighted_F_mul_cpow_hray_eq_Ioi (h : ℝ)
    (hx_pos : 0 < x) :
    (∫ r in Set.Iic (1 : ℝ), ((1 - r) / l.T) *
        ‖F ((r : ℂ) + h * Complex.I) * (x : ℂ) ^ ((r : ℂ) + h * Complex.I)‖) =
      (1 / l.T) *
        ∫ t in Set.Ioi (0 : ℝ), t * ‖F ((1 - t : ℝ) + h * Complex.I)‖ * x ^ (1 - t) := by
  rw [integral_Iic_one_eq_integral_Ioi_one_sub]
  calc
    (∫ t in Set.Ioi (0 : ℝ), ((1 - (1 - t)) / l.T) *
        ‖F (((1 - t : ℝ) : ℂ) + h * Complex.I) *
          (x : ℂ) ^ (((1 - t : ℝ) : ℂ) + h * Complex.I)‖)
        = ∫ t in Set.Ioi (0 : ℝ),
            (1 / l.T) * (t * ‖F ((1 - t : ℝ) + h * Complex.I)‖ * x ^ (1 - t)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          have hnorm_x :
              ‖(x : ℂ) ^ (((1 - t : ℝ) : ℂ) + h * Complex.I)‖ = x ^ (1 - t) := by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
            simp
          change ((1 - (1 - t)) / l.T) *
              ‖F (((1 - t : ℝ) : ℂ) + h * Complex.I) *
                (x : ℂ) ^ (((1 - t : ℝ) : ℂ) + h * Complex.I)‖ =
            (1 / l.T) * (t * ‖F (((1 - t : ℝ) : ℂ) + h * Complex.I)‖ * x ^ (1 - t))
          rw [norm_mul, hnorm_x]
          ring
    _ = (1 / l.T) *
        ∫ t in Set.Ioi (0 : ℝ), t * ‖F ((1 - t : ℝ) + h * Complex.I)‖ * x ^ (1 - t) := by
          rw [integral_const_mul]

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
  symmetry of $\Phi^\star$ together with $F(\bar s) = \overline{F(s)}$. For $\lambda > 0$ the rescaled
  argument $\mathrm{sgn}(\lambda)\, z(s)$ has $\Im \geq 0$ on $R$, so $\Phi^\circ$, $\Phi^\star$ are
  pole-free there; $\Phi^\circ$ is bounded and $\Phi^\star, \Phi_\lambda = O(|z|)$ (CH2 Lemma 4.3),
  the linear growth being absorbed by the assumed bound on $z(s)\, F(s)\, x_0^s$. -/)
  (latexEnv := "sublemma")
  (discussion := 1457)]
theorem prop_5_2_a
    (hF_mero : MeromorphicOn F l.R)
    (hF_symm : ConjSymm F)
    (hlam : 0 < lam) (_hε : ε = 1 ∨ ε = -1)
    (hx₀ : 1 ≤ x₀)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s)
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
  refine lemma_5_1
    (G := fun s ↦ Phi_lambda lam ε (l.zOf s) * F s)
    (G_circ := fun s ↦ Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s)
    (G_star := fun s ↦ (Real.sign lam : ℂ) *
        Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s)
    ?hG ?hGc_mero ?hGs_mero ?hGs_symm ?hGc_symm hx₀ ?hG_bdd ?hGc_L ?hGc_contour
    ?hGs_L ?hGs_contour hx ?hfin ?hsimple ?hsimple_circ
  case hfin => exact hfin
  case hsimple => exact hsimple
  case hsimple_circ => exact hsimple_circ
  -- remaining genuine subgoals (to be discharged):
  case hG =>
    intro s
    simp only [Phi_lambda, l.sign_zOf_re]
    ring
  case hGc_mero =>
    intro z hz
    refine MeromorphicAt.mul ?_ (hF_mero z hz)
    exact (Phi_circ.meromorphic |lam| ε _).comp_analyticAt (l.analyticAt_zOf _ z)
  case hGs_mero =>
    intro z hz
    refine MeromorphicAt.mul ?_ (hF_mero z hz)
    exact (MeromorphicAt.const (Real.sign lam : ℂ) z).mul
      ((Phi_star.meromorphic |lam| ε _).comp_analyticAt (l.analyticAt_zOf _ z))
  case hGs_symm =>
    intro s
    simp only []
    rw [l.zOf_conj, hF_symm,
      show (Real.sign lam : ℂ) * -(starRingEnd ℂ (l.zOf s)) =
          -(starRingEnd ℂ ((Real.sign lam : ℂ) * l.zOf s)) by
        rw [map_mul, Complex.conj_ofReal]; ring,
      Phi_star_conj_neg, map_mul, map_mul, Complex.conj_ofReal]
    ring
  case hGc_symm =>
    intro s
    simp only []
    have hPhi : Phi_circ |lam| ε
        (-(starRingEnd ℂ ((Real.sign lam : ℂ) * l.zOf s))) =
        starRingEnd ℂ (Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s)) := by
      unfold Phi_circ
      simp only [map_mul, map_add, map_div₀, Complex.conj_ofReal, neg_mul, mul_neg,
        neg_neg, coth_conj, map_one, map_ofNat, Complex.conj_I, map_neg]
    rw [l.zOf_conj, hF_symm,
      show (Real.sign lam : ℂ) * -(starRingEnd ℂ (l.zOf s)) =
          -(starRingEnd ℂ ((Real.sign lam : ℂ) * l.zOf s)) by
        rw [map_mul, Complex.conj_ofReal]
        ring,
      hPhi, map_mul]
  case hG_bdd =>
    exact isBoundedNoPolesOn_Phi_lambda_mul l hlam hx₀ hF_mero l.Rboundary_subset_R
      (hF_bdd.mono (Set.subset_union_left.trans Set.subset_union_left))
      (hFw_bdd.mono (Set.subset_union_left.trans Set.subset_union_left))
  case hGc_L =>
    exact isBoundedNoPolesOn_Phi_circ_mul l hlam hx₀ hF_mero l.L_subset_R
      (hF_bdd.mono Set.subset_union_right)
  case hGc_contour =>
    exact isBoundedNoPolesOn_Phi_circ_mul l hlam hx₀ hF_mero l.admissible_contour_subset_R
      (hF_bdd.mono (Set.subset_union_right.trans Set.subset_union_left))
  case hGs_L =>
    exact isBoundedNoPolesOn_Phi_star_mul l hlam hx₀ hF_mero l.L_subset_R
      (hF_bdd.mono Set.subset_union_right) (hFw_bdd.mono Set.subset_union_right)
  case hGs_contour =>
    exact isBoundedNoPolesOn_Phi_star_mul l hlam hx₀ hF_mero l.admissible_contour_subset_R
      (hF_bdd.mono (Set.subset_union_right.trans Set.subset_union_left))
      (hFw_bdd.mono (Set.subset_union_right.trans Set.subset_union_left))

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
  have _ := hF_symm
  have _ := hfin
  have _ := hsimple
  have _ := hsimple_circ
  let G : ℂ → ℂ := fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s
  let Itop : ℝ :=
    ∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t + l.T * Complex.I)‖ * x ^ (1 - t)
  let Ibot : ℝ :=
    ∫ t in Set.Ioi (0 : ℝ), t * ‖F (1 - t - l.T * Complex.I)‖ * x ^ (1 - t)
  obtain ⟨M, hM⟩ := hF_bdd
  have hF_Rbd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s) l.Rboundary := by
    exact ⟨M, fun z hz ↦ hM z (by simp [hz])⟩
  have hx_pos : 0 < x := by linarith
  have htop :
      ‖intHRay l.T 1 G‖ ≤ (1 / l.T) * Itop := by
    have hweighted :
        ‖intHRay l.T 1 G‖ ≤
          ∫ r in Set.Iic (1 : ℝ), ((1 - r) / l.T) *
            ‖F ((r : ℂ) + l.T * Complex.I) *
              (x : ℂ) ^ ((r : ℂ) + l.T * Complex.I)‖ := by
      simpa [G] using
        norm_intHRay_Phi_lambda_le_weighted (l := l) (F := F) (lam := lam) (ε := ε)
          (x₀ := x₀) (x := x) l.T hx₀ hx (abs_of_nonneg l.hT.le) hF_mero hF_Rbd
          (ae_norm_Phi_lambda_top_hray_le (l := l) (lam := lam) (ε := ε) hlam hε)
    have htransport :=
      integral_weighted_F_mul_cpow_hray_eq_Ioi (l := l) (F := F) (x := x) l.T hx_pos
    exact hweighted.trans (le_of_eq (by simpa [Itop] using htransport))
  have hbot :
      ‖intHRay (-l.T) 1 G‖ ≤ (1 / l.T) * Ibot := by
    have hweighted :
        ‖intHRay (-l.T) 1 G‖ ≤
          ∫ r in Set.Iic (1 : ℝ), ((1 - r) / l.T) *
            ‖F ((r : ℂ) + (-l.T) * Complex.I) *
              (x : ℂ) ^ ((r : ℂ) + (-l.T) * Complex.I)‖ := by
      simpa [G] using
        norm_intHRay_Phi_lambda_le_weighted (l := l) (F := F) (lam := lam) (ε := ε)
          (x₀ := x₀) (x := x) (-l.T) hx₀ hx
          (by rw [abs_of_nonpos (neg_nonpos.mpr l.hT.le)]; ring)
          hF_mero hF_Rbd
          (ae_norm_Phi_lambda_bot_hray_le (l := l) (lam := lam) (ε := ε) hlam hε)
    have htransport :=
      integral_weighted_F_mul_cpow_hray_eq_Ioi (l := l) (F := F) (x := x) (-l.T) hx_pos
    exact hweighted.trans (le_of_eq (by simpa [Ibot, sub_eq_add_neg] using htransport))
  have hCinf :
      ‖l.intCinf G‖ ≤ (1 / l.T) * Itop + (1 / l.T) * Ibot := by
    unfold LadderParams.intCinf
    calc
      ‖intHRay l.T 1 G - intHRay (-l.T) 1 G‖
          ≤ ‖intHRay l.T 1 G‖ + ‖intHRay (-l.T) 1 G‖ := norm_sub_le _ _
      _ ≤ (1 / l.T) * Itop + (1 / l.T) * Ibot := add_le_add htop hbot
  have hfactor :
      ‖(2 * (π : ℂ) * Complex.I)⁻¹‖ = (1 / (2 * π) : ℝ) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos Real.pi_pos]
    ring
  have hfactor_nonneg : 0 ≤ (1 / (2 * π) : ℝ) := by positivity
  calc
    ‖(2 * (π : ℂ) * Complex.I)⁻¹ *
        l.intCinf (fun s ↦ Phi_lambda lam ε (l.zOf s) * F s * (x : ℂ) ^ s)‖
        = (1 / (2 * π) : ℝ) * ‖l.intCinf G‖ := by
          rw [norm_mul, hfactor]
    _ ≤ (1 / (2 * π) : ℝ) * ((1 / l.T) * Itop + (1 / l.T) * Ibot) :=
      mul_le_mul_of_nonneg_left hCinf hfactor_nonneg
    _ = (1 / (2 * π)) * ((1 / l.T) * (Itop + Ibot)) := by ring

lemma LadderParams.intC_const_mul (c : ℂ) (F : ℂ → ℂ) :
    l.intC (fun x ↦ c * F x) = c * l.intC (fun x ↦ F x) := by
  simp [LadderParams.intC, intVSeg, intHRay, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const, integral_const_mul, mul_assoc, mul_sub]

@[blueprint
  "ch2-prop-5-2-c"
  (title := "Proposition 5.2: bound on the contour integral")
  (statement := /--
  Since $G^\star = \mathrm{sgn}(\lambda)\, \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(\cdot)) F$ and $|\Im w| \leq |w|$,
  $$ \left\| \frac{1}{\pi}\Im\int_C G^\star(s) x^s\, ds \right\| \leq \frac{1}{2\pi} \cdot 2\left\| \int_C \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s) x^s\, ds \right\|. $$ -/)
  (proof := /-- `intC` is linear, $|\mathrm{sgn}(\lambda)| = 1$, and $|\Im w| \leq |w|$. -/)
  (latexEnv := "sublemma")
  (discussion := 1459)]
theorem prop_5_2_c (hlam : lam ≠ 0) :
    ‖(↑(π⁻¹ * (l.intC (fun s   ↦ (Real.sign lam : ℂ) *
          Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)).im) : ℂ)‖ ≤
      (1 / (2 * π)) *
        (2 * ‖l.intC (fun s ↦ Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * F s * (x : ℂ) ^ s)‖) := by
  conv in _ * ↑x ^ _ => rw [mul_assoc, mul_assoc]
  grw [norm_real, norm_eq_abs, abs_mul, abs_im_le_norm, l.intC_const_mul, norm_mul, norm_real]
  apply le_of_eq
  grind [Real.sign, Real.pi_pos, norm_eq_abs, - abs_div, - abs_mul]

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
  $F(\bar s) = \overline{F(s)}$, and suppose for some $x_0 \geq 1$ that both $F(s) x_0^s$ and
  $z(s) F(s) x_0^s$ are bounded with no poles on $\partial R \cup C \cup L$ (the second condition is
  the extra decay of $F$ that absorbs the $O(|z|)$ growth of $\Phi^\star$). Fix $\lambda > 0$ and
  $\varepsilon \in \{+1, -1\}$, write $z(s) = \frac{s - 1}{iT}$, and set
  $$ \Phi^\varepsilon_\lambda(z) = \Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z) + \mathrm{sgn}(\lambda)\, \mathrm{sgn}(\Re z)\, \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z). $$
  This is the $G = G^\circ + \mathrm{sgn}(\Im s)\, G^\star$ of Lemma \ref{ch2-lemma-5-1}, with
  $G(s) = \Phi^\varepsilon_\lambda(z(s)) F(s)$,
  $G^\circ(s) = \Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s)$, and
  $G^\star(s) = \mathrm{sgn}(\lambda)\, \Phi^\star_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s)$.
  Then, for any $x > x_0$,
  $$ \frac{1}{2\pi i} \int_{1-iT}^{1+iT} \Phi^\varepsilon_\lambda(z(s)) F(s) x^s\, ds = \sum_{\rho \in R \setminus R_C} \mathrm{Res}_{s=\rho} \Phi^\varepsilon_\lambda(z(s)) F(s) x^s + \sum_{\rho \in R_C} \mathrm{Res}_{s=\rho} \Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s) x^s + \frac{1}{2\pi} O^*(E), $$
  where the second sum is the \emph{improper} residue sum (a limit of truncations $R_C \cap \{\Re s > \sigma_n\}$, allowing the infinitely many real-axis poles) of $\Phi^\circ_{|\lambda|, \varepsilon}(\mathrm{sgn}(\lambda) z(s)) F(s)$ over $R_C$ (for $\lambda > 0$, $\Phi^\circ \circ z$ is pole-free on $R$, so these are the poles of $F$), and
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
    (hlam : 0 < lam) (hε : ε = 1 ∨ ε = -1)
    (hx₀ : 1 ≤ x₀)
    (hF_bdd : IsBoundedNoPolesOn (fun s ↦ F s * (x₀ : ℂ) ^ s)
      (l.Rboundary ∪ l.admissible_contour ∪ l.L))
    (hFw_bdd : IsBoundedNoPolesOn (fun s ↦ l.zOf s * F s * (x₀ : ℂ) ^ s)
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
    rw [prop_5_2_a hF_mero hF_symm hlam hε hx₀ hF_bdd hFw_bdd hx hfin hsimple hsimple_circ]
    ring
  rw [hLHS]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add
    (prop_5_2_b hF_mero hF_symm hlam.ne' hε hx₀ hF_bdd hx hfin hsimple hsimple_circ)
    (prop_5_2_c hlam.ne')) ?_
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
$$|\psi(x) - x \cdot \frac{\pi}{T} \coth(\frac{\pi}{T})| \leq \frac{\pi}{T-1} \cdot x + \left(\frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi))\right) \sqrt{x},$$
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_2_a {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    |ψ x - x * π * T⁻¹ * (coth (π * T⁻¹)).re| ≤
      π / (T - 1) * x + ((1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π))) * Real.sqrt x := by sorry

@[blueprint
  "CH2-cor-1-2-b"
  (title := "Corollary 1.2, part b")
  (statement := /--
  Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$\left|\sum_{n \leq x} \frac{\Lambda(n)}{n} - (\log x - \gamma)\right| \leq \frac{\pi}{T-1} + \left(\frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi))\right) \frac{1}{\sqrt{x}},$$
where $\gamma = 0.577215...$ is Euler’s constant.
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_2_b {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    |∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n - (log x - eulerMascheroniConstant)| ≤
      π / (T - 1) + ((1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π))) / Real.sqrt x := by sorry

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
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x - \gamma + O^*(\pi \cdot \sqrt{3} \cdot 10^{-12} + 113.67 / \sqrt{x}).$$
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_3_b (x : ℝ) (hx : 1 ≤ x) : ∃ E,
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n =
      log x - eulerMascheroniConstant + E ∧ |E| ≤ π * Real.sqrt 3 * 10 ^ (-12 : ℝ) + 113.67 / Real.sqrt x := by sorry

end CH2
