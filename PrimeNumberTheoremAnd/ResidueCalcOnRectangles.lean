import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Meromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import EulerProducts.LSeries

open Complex BigOperators  Nat Classical Real Topology Filter Set MeasureTheory

open scoped Interval

lemma Complex.abs_neg (z : ℂ) : Complex.abs (-z) = Complex.abs z :=
  AbsoluteValue.map_neg abs z

/-%%

In this section, we develop residue calculus on rectangles for \emph{simple} poles.

\begin{definition}\label{Rectangle}\lean{Rectangle}\leanok
A Rectangle has corners $z$ and $w \in \C$.
\end{definition}
%%-/
/-- A `Rectangle` has corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

lemma Rectangle.symm {z w : ℂ} : Rectangle z w = Rectangle w z := by
  simp_rw [Rectangle, Set.uIcc_comm]

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)

lemma Square_apply (p : ℂ) {c : ℝ} (cpos : c > 0) :
    Square p c =
      Icc (-c + p.re) (c + p.re) ×ℂ Icc (-c + p.im) (c + p.im) := by
  rw [Square, Rectangle, uIcc_of_le (by simp; linarith), uIcc_of_le (by simp; linarith)]
  simp

/-%%
\begin{definition}[RectangleIntegral]\label{RectangleIntegral}\lean{RectangleIntegral}\leanok
A RectangleIntegral of a function $f$ is one over a rectangle determined by $z$ and $w$ in $\C$.
We will sometimes denote it by $\int_{z}^{w} f$. (There is also a primed version, which is $1/(2\pi i)$ times the original.)
\end{definition}
%%-/
/-- A `RectangleIntegral` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

noncomputable abbrev RectangleIntegral' (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    (1/(2 * π * I)) * RectangleIntegral f z w

/-%%
The border of a rectangle is the union of its four sides.
\begin{definition}[RectangleBorder]\label{RectangleBorder}\lean{RectangleBorder}\leanok
A Rectangle's border, given corners $z$ and $w$ is the union of the four sides.
\end{definition}
%%-/
/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

/-%%
An UpperUIntegral is the integral of a function over a |\_| shape.
\begin{definition}\label{UpperUIntegral}\lean{UpperUIntegral}\leanok
An UpperUIntegral of a function $f$ comes from $\sigma+i\infty$ down to $\sigma+iT$, over to $\sigma'+iT$, and back up to $\sigma'+i\infty$.
\end{definition}
%%-/
noncomputable def UpperUIntegral (f : ℂ → ℂ) (σ σ' T : ℝ) : ℂ :=
    ((∫ x : ℝ in σ..σ', f (x + T * I))
     + I • (∫ y : ℝ in Ici T, f (σ' + y * I)) - I • ∫ y : ℝ in Ici T, f (σ + y * I))

/-%%
A LowerUIntegral is the integral of a function over a |-| shape.
\begin{definition}[LowerUIntegral]\label{LowerUIntegral}\lean{LowerUIntegral}\leanok
A LowerUIntegral of a function $f$ comes from $\sigma-i\infty$ up to $\sigma-iT$, over to $\sigma'-iT$, and back down to $\sigma'-i\infty$.
\end{definition}
%%-/
noncomputable def LowerUIntegral (f : ℂ → ℂ) (σ σ' T : ℝ) : ℂ :=
    ((∫ x : ℝ in σ..σ', f (x - T * I))
     - I • (∫ y : ℝ in Iic (-T), f (σ' + y * I)) + I • ∫ y : ℝ in Iic (-T), f (σ + y * I))


/-%%
It is very convenient to define integrals along vertical lines in the complex plane, as follows.
\begin{definition}[VerticalIntegral]\label{VerticalIntegral}\leanok
Let $f$ be a function from $\mathbb{C}$ to $\mathbb{C}$, and let $\sigma$ be a real number. Then we define
$$\int_{(\sigma)}f(s)ds = \int_{\sigma-i\infty}^{\sigma+i\infty}f(s)ds.$$
\end{definition}
%%-/

noncomputable def VerticalIntegral (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  I • ∫ t : ℝ, f (σ + t * I)

--%% We also have a version with a factor of $1/(2\pi i)$.
noncomputable abbrev VerticalIntegral' (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * VerticalIntegral f σ


-- From PR #9598
/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

-- From PR #9598
/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  simp_rw [← preimage_equivRealProd_prod, equivRealProd.preimage_subset]

-- From PR #9598
/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ :=
  reProdIm_subset_iff.trans prod_subset_prod_iff

/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. Golfed from mathlib4\#9598.-/
lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm, reProdIm]
  exact congrArg _ <| Set.ext <| by simpa [Complex.ext_iff] using by tauto

/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. Golfed from mathlib4\#9598.-/
lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  rw [Rectangle, segment_reProdIm_segment_eq_convexHull]
  exact convexHull_min (by simp_all [insert_subset_iff]) U_convex

lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔ z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc

lemma SquareMemNhds (p : ℂ) {c : ℝ} (cpos : c > 0) :
    Square p c ∈ 𝓝 p := by
  rw [Square_apply p cpos, mem_nhds_iff, ← preimage_equivRealProd_prod]
  refine ⟨Ioo (-c + p.re) (c + p.re) ×ℂ Ioo (-c + p.im) (c + p.im), ?_, ?_,
    ⟨by simp [cpos], by simp [cpos]⟩⟩
  · rw [← preimage_equivRealProd_prod]
    simp only [Equiv.range_eq_univ, subset_univ, preimage_subset_preimage_iff]
    rw [prod_subset_prod_iff]
    left
    refine ⟨Ioo_subset_Icc_self, Ioo_subset_Icc_self⟩
  · rw [← preimage_equivRealProd_prod]
    apply (isOpen_Ioo.prod isOpen_Ioo).preimage
    exact equivRealProdCLM.continuous

/-%%
\begin{lemma}[DiffVertRect_eq_UpperLowerUs]\label{DiffVertRect_eq_UpperLowerUs}\lean{DiffVertRect_eq_UpperLowerUs}\leanok
The difference of two vertical integrals and a rectangle is the difference of an upper and a lower U integrals.
\end{lemma}
%%-/
lemma DiffVertRect_eq_UpperLowerUs {f : ℂ → ℂ} {σ σ' T : ℝ}
    (f_int_σ : Integrable (fun (t : ℝ) ↦ f (σ + t * I)))
    (f_int_σ' : Integrable (fun (t : ℝ) ↦ f (σ' + t * I))) :
  (VerticalIntegral f σ') - (VerticalIntegral f σ) - (RectangleIntegral f (σ - I * T) (σ' + I * T)) = (UpperUIntegral f σ σ' T) - (LowerUIntegral f σ σ' T) := by
  dsimp only [VerticalIntegral, UpperUIntegral, RectangleIntegral, LowerUIntegral]
  have h₁ : (I • ∫ (t : ℝ), f (↑σ' + ↑t * I)) =
      (I • ∫ (y : ℝ) in (↑σ - I * ↑T).im..(↑σ' + I * ↑T).im, f (↑(↑σ' + I * ↑T).re + ↑y * I)) +
      (I • ∫ (t : ℝ) in Set.Ici T, f (↑σ' + ↑t * I)) +
      (I • ∫ (y : ℝ) in Set.Iic (-T), f (↑σ' + ↑y * I)) := by
    simp only [smul_eq_mul, add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
      sub_self, add_zero, sub_im, mul_im, one_mul, zero_add, zero_sub, add_im]
    rw [← intervalIntegral.integral_Iic_sub_Iic (Integrable.restrict f_int_σ')
        (Integrable.restrict f_int_σ'), ← @intervalIntegral.integral_Iio_add_Ici _ _ _ T _ _
        (Integrable.restrict f_int_σ') (Integrable.restrict f_int_σ'), mul_sub, mul_add,
        ← integral_comp_neg_Ioi, ← integral_Ici_eq_integral_Ioi,
        ← integral_Iic_eq_integral_Iio, sub_add_eq_add_sub, sub_add]
    convert (sub_zero _).symm
    simp only [ofReal_neg, neg_mul, sub_self]
  have h₂ : (I • ∫ (t : ℝ), f (↑σ + ↑t * I)) =
      (I • ∫ (y : ℝ) in (↑σ - I * ↑T).im..(↑σ' + I * ↑T).im, f (↑(↑σ - I * ↑T).re + ↑y * I)) +
      (I • ∫ (y : ℝ) in Set.Iic (-T), f (↑σ + ↑y * I)) +
      (I • ∫ (t : ℝ) in Set.Ici T, f (↑σ + ↑t * I)) := by
    simp only [smul_eq_mul, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_self, sub_zero, sub_im, mul_im, one_mul, zero_add, zero_sub, add_im]
    rw [← intervalIntegral.integral_Iic_sub_Iic (Integrable.restrict f_int_σ)
        (Integrable.restrict f_int_σ), ← @intervalIntegral.integral_Iio_add_Ici _ _ _ T _ _
        (Integrable.restrict f_int_σ) (Integrable.restrict f_int_σ), mul_sub, mul_add,
        ← integral_comp_neg_Ioi, ← integral_Ici_eq_integral_Ioi,
        ← integral_Iic_eq_integral_Iio]
    simp only [ofReal_neg, neg_mul, sub_add_cancel]
  rw [h₁, h₂]
  simp only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_sub, sub_re, mul_re,  add_re,
    add_im, ← integral_comp_neg_Ioi, ← integral_Ici_eq_integral_Ioi, ← integral_Ici_eq_integral_Ioi,
    ofReal_neg, mul_neg, neg_mul, add_left_inj]
  ring_nf

/-%%
\begin{proof}\uses{UpperUIntegral, LowerUIntegral}\leanok
Follows directly from the definitions.
\end{proof}
%%-/

/-- A function is `HolomorphicOn` a set if it is complex differentiable on that set. -/
abbrev HolomorphicOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (s : Set ℂ) :
    Prop := DifferentiableOn ℂ f s


/-%%
\begin{theorem}[existsDifferentiableOn_of_bddAbove]\label{existsDifferentiableOn_of_bddAbove}\lean{existsDifferentiableOn_of_bddAbove}\leanok
If $f$ is differentiable on a set $s$ except at $c\in s$, and $f$ is bounded above on $s\setminus\{c\}$, then there exists a differentiable function $g$ on $s$ such that $f$ and $g$ agree on $s\setminus\{c\}$.
\end{theorem}
%%-/
theorem existsDifferentiableOn_of_bddAbove {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E), HolomorphicOn g s ∧ (Set.EqOn f g (s \ {c})) := by
  refine ⟨(Function.update f c (limUnder (nhdsWithin c {c}ᶜ) f)),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb, ?_⟩
  intro z hz
  by_cases h : z = c
  · exfalso
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hz
    exact hz.2 h
  · simp [h]
/-%%
\begin{proof}\leanok
This is the Reimann Removable Singularity Theorem, slightly rephrased from what's in Mathlib. (We don't care what the function $g$ is, just that it's holomorphic.)
\end{proof}
%%-/

/-%%
\begin{theorem}[HolomorphicOn.vanishesOnRectangle]\label{HolomorphicOn.vanishesOnRectangle}\lean{HolomorphicOn.vanishesOnRectangle}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$, then the integral of $f$ over the rectangle with corners $z$ and $w$ is $0$.
\end{theorem}
%%-/
theorem HolomorphicOn.vanishesOnRectangle {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (f_holo : HolomorphicOn f U) (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w (f_holo.mono hU)
/-%%
\begin{proof}\leanok
This is in a Mathlib PR.
\end{proof}
%%-/

-- ## Rectangle API ##

lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩

lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := ⟨right_mem_uIcc, right_mem_uIcc⟩

lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  use fun h ↦ ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  intro ⟨⟨⟨hz're_ge, hz're_le⟩, ⟨hz'im_ge, hz'im_le⟩⟩,
    ⟨⟨hw're_ge, hw're_le⟩, ⟨hw'im_ge, hw'im_le⟩⟩⟩ x ⟨⟨hxre_ge, hxre_le⟩, ⟨hxim_ge, hxim_le⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_inf hz're_ge hw're_ge).trans hxre_ge
  · exact (le_sup_iff.mp hxre_le).casesOn (fun h ↦ h.trans hz're_le) (fun h ↦ h.trans hw're_le)
  · exact (le_inf hz'im_ge hw'im_ge).trans hxim_ge
  · exact (le_sup_iff.mp hxim_le).casesOn (fun h ↦ h.trans hz'im_le) (fun h ↦ h.trans hw'im_le)

lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁) (x₁_le_x₂ : x₁ ≤ x₂)
    (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁) (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆ Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff, mem_Rect, mem_Rect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simpa using by linarith

lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re) (x₁_le_x₂ : z₁.re ≤ z₂.re)
    (x₂_le_x₃ : z₂.re ≤ z₃.re) (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [← re_add_im z₀, ← re_add_im z₁, ← re_add_im z₂, ← re_add_im z₃]
  exact RectSubRect x₀_le_x₁ x₁_le_x₂ x₂_le_x₃ y₀_le_y₁ y₁_le_y₂ y₂_le_y₃

lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

/-- Note: try using `by simp` for `h`. -/
lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  refine disjoint_singleton_right.mpr (not_and_or.mpr ?_)
  obtain h | h | h | h := h
  · exact Or.inl (not_mem_uIcc_of_lt h.1 h.2)
  · exact Or.inr (not_mem_uIcc_of_lt h.1 h.2)
  · exact Or.inl (not_mem_uIcc_of_gt h.1 h.2)
  · exact Or.inr (not_mem_uIcc_of_gt h.1 h.2)

lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩, fun hc ↦ h.2.1 hc.1⟩

lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_diff.mpr ⟨by apply RectSubRect' <;> tauto, rectangle_disjoint_singleton hp⟩

lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_diff.mpr ⟨
    (rectangleBorder_subset_rectangle _ _).trans (by apply RectSubRect' <;> tauto),
    rectangleBorder_disjoint_singleton hp⟩

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment.
Golfed from mathlib\#9598.-/
lemma horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} :=
  Set.ext fun _ => ⟨fun hx ↦ hx.casesOn fun _ ⟨_, hx⟩ ↦ by simpa [← hx, reProdIm],
    fun hx ↦ hx.casesOn (by simp_all [Complex.ext_iff])⟩

/-- A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment.
Golfed from mathlib\#9598.-/
lemma verticalSegment_eq (a b₁ b₂ : ℝ) :
    (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] = {a} ×ℂ [[b₁, b₂]] :=
  Set.ext fun _ => ⟨fun hx ↦ hx.casesOn fun _ ⟨_, hx⟩ ↦ by simpa [← hx, reProdIm],
    fun hx ↦ hx.casesOn (by simp_all [Complex.ext_iff])⟩

theorem RectangleIntegral_congr {f g : ℂ → ℂ} {z w : ℂ} (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral
  congr 2; swap; congr 1; swap; congr 1
  all_goals refine intervalIntegral.integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr {f g : ℂ → ℂ} {z w : ℂ} (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

def RectangleBorderIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → ℂ} {z w : ℂ} (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral]
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1, intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

lemma mapsTo_rectangle_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_rectangle_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_rectangle_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_rectangle_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦ by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦ by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦ by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦ by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangle_left_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_left_re z w).mono_right (Set.subset_diff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_right_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_right_re z w).mono_right (Set.subset_diff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_left_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_left_im z w).mono_right (Set.subset_diff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_right_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_right_im z w).mono_right (Set.subset_diff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem ContinuousOn.rectangleBorder_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (RectangleBorder z w)) : RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

theorem ContinuousOn.rectangleBorderIntegrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  (hf.mono (rectangleBorder_subset_rectangle z w)).rectangleBorder_integrable

theorem ContinuousOn.rectangleBorderNoPIntegrable {f : ℂ → ℂ} {z w p : ℂ}
    (hf : ContinuousOn f (Rectangle z w \ {p}))
    (pNotOnBorder : p ∉ RectangleBorder z w) : RectangleBorderIntegrable f z w := by
  refine (hf.mono (Set.subset_diff.mpr ?_)).rectangleBorder_integrable
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

-- ## End Rectangle API ##

/--
Given `x₀ a x₁ : ℝ`, and `y₀ y₁ : ℝ` and a function `f : ℂ → ℂ` so that
both `(t : ℝ) ↦ f(t + y₀ * I)` and `(t : ℝ) ↦ f(t + y₁ * I)` are integrable over both
`t ∈ Icc x₀ a` and `t ∈ Icc a x₁`, we have that
`RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I)` is the sum of
`RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I)` and
`RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I)`.
-/
lemma RectangleIntegralHSplit {f : ℂ → ℂ} {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  rw [← intervalIntegral.integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot,
    ← intervalIntegral.integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top]
  ring

lemma RectangleIntegralHSplit' {f : ℂ → ℂ} {a x₀ x₁ y₀ y₁ : ℝ} (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)

lemma RectangleIntegralVSplit {f : ℂ → ℂ} {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  rw [← intervalIntegral.integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left,
    ← intervalIntegral.integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right]
  ring

lemma RectangleIntegralVSplit' {f : ℂ → ℂ} {b x₀ x₁ y₀ y₁ : ℝ} (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)

lemma SmallSquareInRectangle {z w p : ℂ} (pInRectInterior : Rectangle z w ∈ nhds p) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, Square p c ⊆ Rectangle z w := by
  rw [mem_nhds_iff] at pInRectInterior
  obtain ⟨nhdP, nhdSubRect, nhdOpen, pInNhd⟩ := pInRectInterior
  have : ∃ c₁ > 0, Metric.ball p c₁ ⊆ nhdP := by
    simp_all
    refine Metric.mem_nhds_iff.mp ?_
    exact IsOpen.mem_nhds nhdOpen pInNhd
--%% Let $c_1$ be small enough that a ball of radius $c_1$ about $p$ is contained in the rectangle.
  obtain ⟨c₁, c₁Pos, c₁SubNhd⟩ := this
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (half_pos c₁Pos)]
  intro c cPos
  simp only [mem_Ioo] at cPos
  have c_ge_0 : 0 ≤ c := by linarith [mem_Ioo.mp cPos]
  have sqrt2le : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
  have normC : Complex.abs (c + c * I) = c * Real.sqrt 2 := by
    simp only [Complex.abs, normSq, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, AbsoluteValue.coe_mk,
      MulHom.coe_mk, add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
      add_zero, add_im, mul_im, one_mul, zero_add]
    ring_nf
    rw [sqrt_mul (sq_nonneg _), sqrt_sq c_ge_0]
  have normC' : Complex.abs (-c + c * I) = c * Real.sqrt 2 := by
    simp only [Complex.abs, normSq, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, AbsoluteValue.coe_mk,
      MulHom.coe_mk, add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, mul_neg, neg_mul, neg_neg, add_im, neg_im, neg_zero, mul_im, zero_add]
    ring_nf
    rw [sqrt_mul (sq_nonneg _), sqrt_sq c_ge_0]
  apply subset_trans ?_ nhdSubRect
  apply subset_trans ?_ c₁SubNhd
  apply rectangle_in_convex (convex_ball _ _)
  · simp only [Metric.mem_ball, dist_add_self_left, Complex.norm_eq_abs]
    rw [(by ring: -(c : ℂ) - c * I = -(c + c * I)), Complex.abs_neg, normC]
    nlinarith
  · simp only [Metric.mem_ball, dist_add_self_left, Complex.norm_eq_abs]
    rw [normC]
    nlinarith
  · simp only [add_re, sub_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, sub_zero, ofReal_add, ofReal_neg, add_im, mul_im, add_zero, zero_add]
    rw [(by ring : -(c : ℂ) + p.re + (c + p.im) * I = -c + c * I + (p.re + p.im * I))]
    rw [re_add_im]
    simp only [Metric.mem_ball, dist_add_self_left, Complex.norm_eq_abs]
    rw [normC']
    nlinarith
  · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, ofReal_add, add_im, sub_im, neg_im, neg_zero, mul_im, zero_sub, ofReal_neg]
    rw [(by ring : (c : ℂ) + p.re + (-c + p.im) * I = c - c * I + (p.re + p.im * I)), re_add_im]
    simp only [Metric.mem_ball, dist_add_self_left, Complex.norm_eq_abs]
    rw [← Complex.abs_neg, neg_sub, sub_eq_add_neg, add_comm, normC']
    nlinarith

/-%%
The next lemma allows to zoom a big rectangle down to a small square, centered at a pole.

\begin{lemma}[RectanglePullToNhdOfPole]\label{RectanglePullToNhdOfPole}\lean{RectanglePullToNhdOfPole}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$ except at a point $p$, then the integral of $f$
over the rectangle with corners $z$ and $w$ is the same as the integral of $f$ over a small square
centered at $p$.
\end{lemma}
%%-/
/-- Given `f` holomorphic on a rectangle `z` and `w` except at a point `p`, the integral of `f` over
the rectangle with corners `z` and `w` is the same as the integral of `f` over a small square
centered at `p`. -/
lemma RectanglePullToNhdOfPole {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    (zIm_lt_wIm : z.im < w.im) (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, RectangleIntegral f z w =
      RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
--%% \begin{proof}\uses{HolomorphicOn.vanishesOnRectangle}\leanok
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' zero_lt_one, SmallSquareInRectangle pInRectInterior]
  intro c ⟨cpos, _⟩ hc
  have fCont : ContinuousOn f (Rectangle z w \ {p}) := fHolo.continuousOn

  have : z.re ≤ p.re - c := by
    suffices p.re - c ∈ [[z.re, w.re]] from (Set.uIcc_of_lt zRe_lt_wRe ▸ this).1
    simpa [sub_eq_neg_add] using (rect_subset_iff.mp hc).1.1
  have : p.re - c < p.re + c := by linarith
  have : p.re + c ≤ w.re := by
    suffices p.re + c ∈ [[z.re, w.re]] from (Set.uIcc_of_lt zRe_lt_wRe ▸ this).2
    simpa [add_comm] using (rect_subset_iff.mp hc).2.1
  have : z.im ≤ p.im - c := by
    suffices p.im - c ∈ [[z.im, w.im]] from (Set.uIcc_of_lt zIm_lt_wIm ▸ this).1
    simpa [sub_eq_neg_add] using (rect_subset_iff.mp hc).1.2
  have : p.im - c < p.im + c := by linarith
  have : p.im + c ≤ w.im := by
    suffices p.im + c ∈ [[z.im, w.im]] from (Set.uIcc_of_lt zIm_lt_wIm ▸ this).2
    simpa [add_comm] using (rect_subset_iff.mp hc).2.2

/-%%
Chop the big rectangle with two vertical cuts and two horizontal cuts into smaller rectangles,
the middle one being the desired square. The integral over each of the outer rectangles
vanishes, since $f$ is holomorphic there. (The constant $c$ being ``small enough'' here just means
that the inner square is strictly contained in the big rectangle.)
%%-/
  have hbot : RectangleBorderIntegrable f (↑z.re + ↑z.im * I) (↑w.re + ↑w.im * I) := by
    refine (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_)).rectangleBorder_integrable
    · simpa using ⟨by linarith, by linarith⟩
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  have htop : RectangleBorderIntegrable f (↑z.re + ↑(p.im - c) * I) (↑w.re + ↑w.im * I) := by
    refine (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_)).rectangleBorder_integrable
    · simpa using ⟨by linarith, by linarith, by linarith⟩
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hleft : RectangleBorderIntegrable f (↑z.re + ↑(p.im - c) * I) (↑w.re + ↑(p.im + c) * I) := by
    refine (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_)).rectangleBorder_integrable
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hright : RectangleBorderIntegrable f (↑(p.re - c) + ↑(p.im - c) * I) (w.re + ↑(p.im + c) * I)
  · refine (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_)).rectangleBorder_integrable
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hbot' : p.im - c ∈ [[z.im, w.im]] :=
    Set.uIcc_of_le zIm_lt_wIm.le ▸ ⟨by linarith, by linarith⟩
  have htop' : p.im + c ∈ [[p.im - c, w.im]] :=
    Set.uIcc_of_le (by linarith : p.im - c ≤ w.im) ▸ ⟨by linarith, by linarith⟩
  have hleft' : p.re - c ∈ [[z.re, w.re]] :=
    Set.uIcc_of_le zRe_lt_wRe.le ▸ ⟨by linarith, by linarith⟩
  have hright' : p.re + c ∈ [[p.re - c, w.re]] :=
    Set.uIcc_of_le (by linarith : p.re - c ≤ w.re) ▸ ⟨by linarith, by linarith⟩
  have hbot'' : Rectangle (↑z.re + ↑z.im * I) (↑w.re + ↑(p.im - c) * I) ⊆ Rectangle z w \ {p} := by
    apply rectangle_subset_punctured_rect
    · simpa using ⟨by linarith, by linarith, by linarith⟩
    · simp [cpos, (by linarith : z.im < p.im)]
  have htop'' : Rectangle (↑z.re + ↑(p.im + c) * I) (↑w.re + ↑w.im * I) ⊆ Rectangle z w \ {p} := by
    apply rectangle_subset_punctured_rect
    · simpa using ⟨by linarith, by linarith, by linarith⟩
    · simp [cpos, (by linarith : p.im < w.im)]
  have hleft'' :
      Rectangle (↑z.re + ↑(p.im - c) * I) (↑(p.re - c) + ↑(p.im + c) * I) ⊆ Rectangle z w \ {p}
  · apply rectangle_subset_punctured_rect
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · simp [cpos, (by linarith : z.re < p.re)]
  have hright'' :
      Rectangle (↑(p.re + c) + ↑(p.im - c) * I) (↑w.re + ↑(p.im + c) * I) ⊆ Rectangle z w \ {p}
  · apply rectangle_subset_punctured_rect
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · simp [cpos, (by linarith : p.re < w.re)]

  rw [← re_add_im z, ← re_add_im w,
    RectangleIntegralVSplit' hbot' hbot, fHolo.vanishesOnRectangle hbot'', zero_add,
    RectangleIntegralVSplit' htop' htop, fHolo.vanishesOnRectangle htop'', add_zero,
    RectangleIntegralHSplit' hleft' hleft, fHolo.vanishesOnRectangle hleft'', zero_add,
    RectangleIntegralHSplit' hright' hright, fHolo.vanishesOnRectangle hright'', add_zero]
  congr 1 <;> apply Complex.ext <;> simp [sub_eq_neg_add, add_comm]
--%%\end{proof}

theorem ResidueTheoremAtOrigin_aux1a_aux1 (x : ℝ)
  : 1 / (1 + (ofReal' x) ^ 2) = ofReal' (1 / (1 + x ^ 2)) := by
  simp only [one_div, ofReal_inv, ofReal_add, ofReal_one, ofReal_pow]

theorem ResidueTheoremAtOrigin_aux1a_aux2 :
  ∫ (x : ℝ) in (-1)..1, (1 / (1 + x ^ 2) : ℂ) = ∫ (x : ℝ) in (-1)..1, (1 / (1 + x ^ 2) : ℝ) := by
  simp_rw [ResidueTheoremAtOrigin_aux1a_aux1]
  exact intervalIntegral.integral_ofReal (f := (fun x => 1 / (1 + x ^ 2)))

theorem ResidueTheoremAtOrigin_aux1a :
  ∫ (x : ℝ) in (-1)..1, (1 / (1 + x ^ 2) : ℂ) = ↑(arctan 1) - ↑(arctan (-1)) := by
  rw [ResidueTheoremAtOrigin_aux1a_aux2]
  simp only [one_div, integral_inv_one_add_sq, arctan_one, arctan_neg, sub_neg_eq_add, ofReal_add,
    ofReal_div, ofReal_ofNat, ofReal_neg]

theorem ResidueTheoremAtOrigin_aux1b (x : ℝ)
  : (x + -I)⁻¹ - (x + I)⁻¹ = (2 * I) * (1 / (1 + (x : ℝ)^2))
  := by
  have hu₁ : IsUnit (x + -I) := by
    apply Ne.isUnit
    by_contra h
    have h₁ : (x + -I).im = -1 := by
      simp only [add_im, ofReal_im, neg_im, I_im, zero_add]
    have h₂ : (x + -I).im = 0 := by
      rw [h]
      exact rfl
    linarith
  apply hu₁.mul_left_cancel
  rw [mul_sub, (IsUnit.mul_inv_eq_one hu₁).mpr rfl]
  have hu₂ : IsUnit (x + I) := by
    apply Ne.isUnit
    by_contra h
    have h₁ : (x + I).im = 1 := by
      simp only [add_im, ofReal_im, I_im, zero_add, eq_neg_self_iff, one_ne_zero]
    have h₂ : (x + I).im = 0 := by
      rw [h]
      exact rfl
    linarith
  apply hu₂.mul_left_cancel
  rw [mul_sub, ← mul_assoc]
  nth_rw 2 [mul_comm]
  rw [← mul_assoc, (IsUnit.inv_mul_eq_one hu₂).mpr rfl]
  symm
  rw [← mul_assoc]
  have : (x + I) * (x + -I) = 1 + x^2 := by
    ring_nf
    simp only [I_sq, sub_neg_eq_add]
    rw [add_comm]
  rw [this]
  simp only [one_div, mul_one, one_mul, add_sub_add_left_eq_sub, sub_neg_eq_add]
  rw [← mul_assoc, mul_comm, ← mul_assoc]
  have : IsUnit (1 + (x : ℂ)^2) := by
    have : (x + I) * (x + -I) = 1 + (x : ℂ)^2 := by
      ring_nf
      simp only [I_sq, sub_neg_eq_add]
      rw [add_comm]
    rw [← this]
    exact IsUnit.mul hu₂ hu₁
  rw [(IsUnit.inv_mul_eq_one this).mpr rfl]
  ring

@[deprecated ContinuousOn.intervalIntegrable]
theorem integrable_of_continuous (a b : ℝ) (A : Type) [NormedRing A] (f : ℝ → A) (hf : ContinuousOn f [[a,b]]) :
    IntervalIntegrable f volume a b :=
  hf.intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y + I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (↑y + -I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1 :
  (∫ (x : ℝ) in (-1 - 0)..(1 + 0), 1 / (x + (-0 - 1 : ℝ) * I)) -
    ∫ (x : ℝ) in (-1 - 0)..(1 + 0), 1 / (x + (0 + 1 : ℝ) * I) = π * I
  := by
  simp only [neg_zero, zero_sub, ofReal_neg, ofReal_one, neg_mul, one_mul, one_div, sub_zero,
    add_zero, zero_add]
  rw [← intervalIntegral.integral_sub]
  · have : ∀ x : ℝ, (x + -I)⁻¹ - (x + I)⁻¹ = (2 * I) * (1 / (1 + (x : ℝ)^2)) := by
      intro x
      exact ResidueTheoremAtOrigin_aux1b x
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul (2 * I), ResidueTheoremAtOrigin_aux1a]
    simp only [arctan_one, ofReal_div, ofReal_ofNat, arctan_neg, ofReal_neg, sub_neg_eq_add]
    ring
  exact ResidueTheoremAtOrigin_aux1c' (-1) 1
  exact ResidueTheoremAtOrigin_aux1c (-1) 1

theorem ResidueTheoremAtOrigin_aux2b (y : ℝ) : (1 + y * I)⁻¹ - (-1 + y * I)⁻¹ = 2 * (1 / (1 + y ^ 2)) := by
  have hu₁ : IsUnit (1 + y * I) := by
    apply Ne.isUnit
    by_contra h
    have h₁ : (1 + y * I).re = 1 := by
      simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
    have h₂ : (1 + y * I).re = 0 := by
      rw [h]
      exact rfl
    linarith
  apply hu₁.mul_left_cancel
  rw [mul_sub, (IsUnit.mul_inv_eq_one hu₁).mpr rfl]
  have hu₂ : IsUnit (-1 + y * I) := by
    apply Ne.isUnit
    by_contra h
    have h₁ : (-1 + y * I).re = -1 := by
      simp only [add_re, neg_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
    have h₂ : (-1 + y * I).re = 0 := by
      rw [h]
      exact rfl
    linarith
  apply hu₂.mul_left_cancel
  rw [mul_sub, ← mul_assoc]
  nth_rw 3 [mul_comm]
  rw [← mul_assoc, (IsUnit.inv_mul_eq_one hu₂).mpr rfl]
  symm
  rw [← mul_assoc]
  have : (-1 + y * I) * (1 + y * I) = -1 - y ^ 2 := by
    ring_nf
    simp only [I_sq, mul_neg, mul_one]
    rfl
  rw [this]
  simp only [one_div, mul_one, one_mul, add_sub_add_right_eq_sub]
  rw [← mul_assoc, mul_comm, ← mul_assoc]
  have : (-1 - (y : ℂ)^2) = -(1 + y ^ 2) := by
    ring
  rw [this, mul_neg]
  have : IsUnit (1 + (y : ℂ) ^ 2) := by
    have : (1 - y * I) * (1 + y * I) = 1 + y ^ 2 := by
      ring_nf
      simp only [I_sq, mul_neg, mul_one, sub_neg_eq_add]
    rw [← this]
    have hu₂' : IsUnit (1 - y * I) := by
      apply Ne.isUnit
      by_contra h
      have h₁ : (1 - y * I).re = 1 := by
        simp only [sub_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, sub_zero]
      have h₂ : (1 - y * I).re = 0 := by
        rw [h]
        exact rfl
      linarith
    exact IsUnit.mul hu₂' hu₁
  rw [(IsUnit.inv_mul_eq_one this).mpr rfl]
  norm_num

theorem ResidueTheoremAtOrigin_aux2c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (1 + ↑y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (-1 + ↑y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2 :
  (I * ∫ (y : ℝ) in (-0 - 1)..0 + 1, 1 / ((1 + 0 : ℝ) + y * I)) -
    I * ∫ (y : ℝ) in (-0 - 1)..0 + 1, 1 / ((-1 - 0 : ℝ) + y * I) = π * I
  := by
  simp only [add_zero, ofReal_one, one_div, neg_zero, zero_sub, zero_add, sub_zero, ofReal_neg]
  rw [← mul_sub, mul_comm (π : ℂ) I]
  simp only [mul_eq_mul_left_iff, I_ne_zero, or_false]
  rw [← intervalIntegral.integral_sub]
  · have : ∀ y : ℝ, (1 + y * I)⁻¹ - (-1 + y * I)⁻¹ = 2 * (1 / (1 + (y : ℝ)^2)) := by
      intro y
      exact ResidueTheoremAtOrigin_aux2b y
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul 2, ResidueTheoremAtOrigin_aux1a]
    simp only [arctan_one, ofReal_div, ofReal_ofNat, arctan_neg, ofReal_neg, sub_neg_eq_add]
    ring
  exact ResidueTheoremAtOrigin_aux2c (-1) 1
  exact ResidueTheoremAtOrigin_aux2c' (-1) 1

/-%%
\begin{lemma}[ResidueTheoremAtOrigin]\label{ResidueTheoremAtOrigin}
\lean{ResidueTheoremAtOrigin}\leanok
The rectangle (square) integral of $f(s) = 1/s$ with corners $-1-i$ and $1+i$ is equal to $2\pi i$.
\end{lemma}
%%-/
lemma ResidueTheoremAtOrigin :
    RectangleIntegral' (fun s ↦ 1 / s) (-1 - I) (1 + I) = 1 := by
  dsimp [RectangleIntegral', RectangleIntegral]
  rw [ResidueTheoremAtOrigin_aux1, add_sub_assoc]
  have := ResidueTheoremAtOrigin_aux2
  rw [ResidueTheoremAtOrigin_aux2]
  have : (2 * π * I) ≠ 0 := by
    norm_num
    exact pi_ne_zero
  field_simp
  ring
/-%%
\begin{proof}\leanok
The bottom is:
$$
\frac1{2\pi i}
\int_{-1-i}^{1-i} \frac1z dz
=
\frac1{2\pi i}
\int_{-1}^1 \frac1{x-i} dx,
$$
and the top is the negative of:
$$
\frac1{2\pi i}
\int_{-1+i}^{1+i} \frac1z dz
=
\frac1{2\pi i}
\int_{-1}^1 \frac1{x+i} dx.
$$
The two together add up to:
$$
\frac1{2\pi i}
\int_{-1}^1
\left(\frac1{x-i}-\frac1{x+i} \right)dx
=
\frac1{\pi}
\int_{-1}^1
\frac{1}{x^2+1}dx,
$$
which is the arctan at $1$ (namely $\pi/4$) minus that at $-1$. In total, this contributes $1/2$ to the integral.

The vertical sides are:
$$
\frac1{2\pi i}
\int_{1-i}^{1+i} \frac1z dz
=
\frac1{2\pi}
\int_{-1}^1 \frac1{1+iy} dy
$$
and the negative of
$$
\frac1{2\pi i}
\int_{-1-i}^{-1+i} \frac1z dz
=
\frac1{2\pi}
\int_{-1}^1 \frac1{-1+iy} dy.
$$
This difference comes out to:
$$
\frac1{2\pi}
\int_{-1}^1 \left(\frac1{1+iy}-\frac1{-1+iy}\right) dy
=
\frac1{2\pi}
\int_{-1}^1 \left(\frac{-2}{-1-y^2}\right) dy,
$$
which contributes another factor of $1/2$. (Fun! Each of the vertical/horizontal sides contributes half of the winding.)
\end{proof}
%%-/

/-%%
\begin{lemma}[ResidueTheoremOnRectangleWithSimplePole]\label{ResidueTheoremOnRectangleWithSimplePole}
\lean{ResidueTheoremOnRectangleWithSimplePole}\leanok
Suppose that $f$ is a holomorphic function on a rectangle, except for a simple pole
at $p$. By the latter, we mean that there is a function $g$ holomorphic on the rectangle such that, $f = g + A/(s-p)$ for some $A\in\C$. Then the integral of $f$ over the
rectangle is $A$.
\end{lemma}
%%-/
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (pInRectInterior : Rectangle z w ∈ nhds p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) (g)
      (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  sorry
/-%%
\begin{proof}\uses{ResidueTheoremAtOrigin, RectanglePullToNhdOfPole, HolomorphicOn.vanishesOnRectangle}
Replace $f$ with $g + A/(s-p)$ in the integral.
The integral of $g$ vanishes by Lemma \ref{HolomorphicOn.vanishesOnRectangle}.
 To evaluate the integral of $1/(s-p)$,
pull everything to a square about the origin using Lemma \ref{RectanglePullToNhdOfPole},
and rescale by $c$;
what remains is handled by Lemma \ref{ResidueTheoremAtOrigin}.
\end{proof}
%%-/
