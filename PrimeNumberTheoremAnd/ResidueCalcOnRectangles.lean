import Mathlib.Analysis.Complex.CauchyIntegral
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
  dsimp [Rectangle]
  rw [Set.uIcc_comm z.re w.re, Set.uIcc_comm z.im w.im]

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
  rw [← @preimage_equivRealProd_prod s t, ← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

-- From PR #9598
/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert prod_subset_prod_iff
  exact reProdIm_subset_iff

/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. -/
lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by sorry -- already exists in mathlib4\#9598

lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔ z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  simp only [Rectangle, uIcc_of_le (by linarith : z.re ≤ w.re),
    uIcc_of_le (by linarith : z.im ≤ w.im), ← preimage_equivRealProd_prod, Icc_prod_Icc,
    mem_preimage, equivRealProd_apply, mem_Icc, Prod.mk_le_mk]
  tauto

-- Exists in Mathlib; need to update version
/-- The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
noncomputable def equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (Real.sqrt 2) equivRealProd_apply_le' fun p =>
    abs_le_sqrt_two_mul_max (equivRealProd.symm p)

lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁) (x₁_le_x₂ : x₁ ≤ x₂)
    (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁) (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆ Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  have x₀_le_x₃ : x₀ ≤ x₃ := by linarith
  have y₀_le_y₃ : y₀ ≤ y₃ := by linarith
  dsimp [Rectangle]
  rw [reProdIm_subset_iff']
  left
  constructor
  · simp only [mul_zero, mul_one, sub_self, add_zero, ge_iff_le, x₁_le_x₂, Set.uIcc_of_le,
    x₀_le_x₃]
    apply Icc_subset_Icc <;> assumption
  · simp only [mul_one, mul_zero, add_zero, zero_add, ge_iff_le, y₁_le_y₂, uIcc_of_le, y₀_le_y₃]
    apply Icc_subset_Icc <;> assumption

lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re) (x₁_le_x₂ : z₁.re ≤ z₂.re)
    (x₂_le_x₃ : z₂.re ≤ z₃.re) (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [← re_add_im z₀, ← re_add_im z₁, ← re_add_im z₂, ← re_add_im z₃]
  exact RectSubRect x₀_le_x₁ x₁_le_x₂ x₂_le_x₃ y₀_le_y₁ y₁_le_y₂ y₂_le_y₃

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

/-- Note: Try using `by simp` for `h''`. -/
lemma rect_subset_of_rect_subset {z w z' w' z'' w'' : ℂ} (h' : Rectangle z' w' ⊆ Rectangle z w)
    (h'': z''.re ∈ ({z.re, w.re, z'.re, w'.re} : Set ℝ) ∧
      z''.im ∈ ({z.im, w.im, z'.im, w'.im} : Set ℝ) ∧
      w''.re ∈ ({z.re, w.re, z'.re, w'.re} : Set ℝ) ∧
      w''.im ∈ ({z.im, w.im, z'.im, w'.im} : Set ℝ)) :
    Rectangle z'' w'' ⊆ Rectangle z w := by
  rw [rect_subset_iff]
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := rect_subset_iff.mp h'
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain _ | _ | _ | _ := h''.1 <;> simp_all
  · obtain _ | _ | _ | _ := h''.2.1 <;> simp_all
  · obtain _ | _ | _ | _ := h''.2.2.1 <;> simp_all
  · obtain _ | _ | _ | _ := h''.2.2.2 <;> simp_all

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

/-- Note: try using `by simp` for `h''`, `hp`. -/
lemma rect_subset_punctured_rect {z w z' w' z'' w'' p : ℂ} (h' : Rectangle z' w' ⊆ Rectangle z w)
    (h'': z''.re ∈ ({z.re, w.re, z'.re, w'.re} : Set ℝ) ∧
      z''.im ∈ ({z.im, w.im, z'.im, w'.im} : Set ℝ) ∧
      w''.re ∈ ({z.re, w.re, z'.re, w'.re} : Set ℝ) ∧
      w''.im ∈ ({z.im, w.im, z'.im, w'.im} : Set ℝ))
    (hp : (p.re < z''.re ∧ p.re < w''.re) ∨ (p.im < z''.im ∧ p.im < w''.im) ∨
      (z''.re < p.re ∧ w''.re < p.re) ∨ (z''.im < p.im ∧ w''.im < p.im)) :
    Rectangle z'' w'' ⊆ Rectangle z w \ {p} :=
  Set.subset_diff.mpr ⟨rect_subset_of_rect_subset h' h'', rectangle_disjoint_singleton hp⟩

theorem RectangleIntegral_congr {f g : ℂ → ℂ} {z w : ℂ} (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  dsimp [RectangleIntegral]
  congr! 2
  · congr! 1
    · apply intervalIntegral.integral_congr
      intro x hx
      simp only
      have : x + z.im * I ∈ RectangleBorder z w := by
        dsimp [RectangleBorder]
        simp only [mem_union]
        left
        left
        left
        rw [← preimage_equivRealProd_prod]
        simp only [prod_singleton, mem_preimage, equivRealProd_apply, add_re, ofReal_re, mul_re,
          I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add,
          mem_image, Prod.mk.injEq, and_true, exists_eq_right, hx]
      exact h this
    apply intervalIntegral.integral_congr
    intro x hx
    simp only
    have : x + w.im * I ∈ RectangleBorder z w := by
      dsimp [RectangleBorder]
      simp only [mem_union]
      left
      right
      rw [← preimage_equivRealProd_prod]
      simp only [prod_singleton, mem_preimage, equivRealProd_apply, add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, mem_image,
        Prod.mk.injEq, and_true, exists_eq_right, hx]
    exact h this
  · congr! 1
    apply intervalIntegral.integral_congr
    intro y hy
    simp only
    have : w.re + y * I ∈ RectangleBorder z w := by
      dsimp [RectangleBorder]
      simp only [mem_union]
      right
      rw [← preimage_equivRealProd_prod]
      simp only [singleton_prod, mem_preimage, equivRealProd_apply, add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, mem_image,
        Prod.mk.injEq, true_and, exists_eq_right, hy]
    exact h this
  apply intervalIntegral.integral_congr
  intro y hy
  simp only
  have : z.re + y * I ∈ RectangleBorder z w := by
    dsimp [RectangleBorder]
    simp only [mem_union]
    left
    left
    right
    rw [← preimage_equivRealProd_prod]
    simp only [singleton_prod, mem_preimage, equivRealProd_apply, add_re, ofReal_re, mul_re, I_re,
      mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, mem_image,
      Prod.mk.injEq, true_and, exists_eq_right, hy]
  exact h this

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

lemma mapsTo_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_left_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  intro y hy
  simp only [mem_diff, mem_singleton_iff]
  refine ⟨⟨by simp, by simp [hy]⟩, ?_⟩
  intro h
  simp only [RectangleBorder, mem_union] at pNotOnBorder
  push_neg at pNotOnBorder
  have := pNotOnBorder.1.1.2
  rw [← h] at this
  apply this
  refine ⟨by simp, ?_⟩
  simp only [mem_preimage, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add, hy]

lemma mapsTo_right_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  intro y hy
  simp only [mem_diff, mem_singleton_iff]
  refine ⟨⟨by simp, by simp [hy]⟩, ?_⟩
  intro h
  simp only [RectangleBorder, mem_union] at pNotOnBorder
  push_neg at pNotOnBorder
  have := pNotOnBorder.2
  rw [← h] at this
  apply this
  refine ⟨by simp, ?_⟩
  simp only [mem_preimage, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add, hy]

lemma mapsTo_left_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  intro x hx
  simp only [mem_diff, mem_singleton_iff]
  refine ⟨⟨by simp [hx], by simp⟩, ?_⟩
  intro h
  simp only [RectangleBorder, mem_union] at pNotOnBorder
  push_neg at pNotOnBorder
  have := pNotOnBorder.1.1.1
  rw [← h] at this
  apply this
  refine ⟨?_, by simp⟩
  simp only [mem_preimage, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, hx]

lemma mapsTo_right_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  intro x hx
  simp only [mem_diff, mem_singleton_iff]
  refine ⟨⟨by simp [hx], by simp⟩, ?_⟩
  intro h
  simp only [RectangleBorder, mem_union] at pNotOnBorder
  push_neg at pNotOnBorder
  have := pNotOnBorder.1.2
  rw [← h] at this
  apply this
  refine ⟨?_, by simp⟩
  simp only [mem_preimage, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, hx]

attribute [fun_prop] Complex.continuous_ofReal

theorem ContinuousOn.rectangleBorderIntegrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := by
  exact ⟨(hf.comp (by fun_prop) (mapsTo_left_im z w)).intervalIntegrable,
  (hf.comp (by fun_prop) (mapsTo_right_im z w)).intervalIntegrable,
  (hf.comp (by fun_prop) (mapsTo_right_re z w)).intervalIntegrable,
  (hf.comp (by fun_prop) (mapsTo_left_re z w)).intervalIntegrable⟩

theorem ContinuousOn.rectangleBorderNoPIntegrable {f : ℂ → ℂ} {z w p : ℂ}
    (hf : ContinuousOn f (Rectangle z w \ {p}))
    (pNotOnBorder : p ∉ RectangleBorder z w) : RectangleBorderIntegrable f z w := by
  exact ⟨(hf.comp (by fun_prop) (mapsTo_left_im_NoP z w pNotOnBorder)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_right_im_NoP z w pNotOnBorder)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_right_re_NoP z w pNotOnBorder)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_left_re_NoP z w pNotOnBorder)).intervalIntegrable⟩

/-- TODO: could probably generalize these next two lemmas without making them much harder to use
  in the following application -/
lemma RectPull_re_aux  {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w) :
    z.re < p.re ∧ p.re < w.re := by
  use (uIcc_of_lt zRe_lt_wRe ▸ (rect_subset_iff.mp hc).1.1).1.trans_lt (by simp [cpos])
  exact LT.lt.trans_le (by simp [cpos]) (uIcc_of_lt zRe_lt_wRe ▸ (rect_subset_iff.mp hc).2.1).2

lemma RectPull_im_aux  {z w p : ℂ} (zIm_lt_wIm : z.im < w.im)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w) :
    z.im < p.im ∧ p.im < w.im := by
  use (uIcc_of_lt zIm_lt_wIm ▸ (rect_subset_iff.mp hc).1.2).1.trans_lt (by simp [cpos])
  exact LT.lt.trans_le (by simp [cpos]) (uIcc_of_lt zIm_lt_wIm ▸ (rect_subset_iff.mp hc).2.2).2

theorem RectangleIntegral'_congr {f g : ℂ → ℂ} {z w : ℂ} (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  dsimp [RectangleIntegral']
  congr! 1
  exact RectangleIntegral_congr h

-- ## End Rectangle API ##

/--
Given `x₀ a x₁ : ℝ`, and `y₀ y₁ : ℝ` and a function `f : ℂ → ℂ` so that
both `(t : ℝ) ↦ f(t + y₀ * I)` and `(t : ℝ) ↦ f(t + y₁ * I)` are integrable over both
`t ∈ Icc x₀ a` and `t ∈ Icc a x₁`, we have that
`RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I)` is the sum of
`RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I)` and
`RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I)`.
-/
lemma RectangleIntegralHSplit {f : ℂ → ℂ} (a : ℝ) {x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  set botInt := ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₀ * I)
  set topInt := ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₁ * I)
  set leftInt := I * ∫ (y : ℝ) in y₀..y₁, f (↑x₀ + ↑y * I)
  set rightInt := I * ∫ (y : ℝ) in y₀..y₁, f (↑x₁ + ↑y * I)
  set midInt := I * ∫ (y : ℝ) in y₀..y₁, f (↑a + ↑y * I)
  set botInt1 := ∫ (x : ℝ) in x₀..a, f (↑x + ↑y₀ * I)
  set botInt2 := ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₀ * I)
  set topInt1 := ∫ (x : ℝ) in x₀..a, f (↑x + ↑y₁ * I)
  set topInt2 := ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₁ * I)
  have : botInt = botInt1 + botInt2 :=
    (intervalIntegral.integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot).symm
  rw [this]
  have : topInt = topInt1 + topInt2 :=
    (intervalIntegral.integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top).symm
  rw [this]
  ring

lemma RectangleIntegralVSplit {f : ℂ → ℂ} (b : ℝ) {x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  set leftInt := ∫ (y : ℝ) in y₀..y₁, f (↑x₀ + ↑y * I)
  set rightInt := ∫ (y : ℝ) in y₀..y₁, f (↑x₁ + ↑y * I)
  set midInt := ∫ (y : ℝ) in y₀..y₁, f (↑b + ↑y * I)
  set leftInt1 := ∫ (y : ℝ) in y₀..b, f (↑x₀ + ↑y * I)
  set leftInt2 := ∫ (y : ℝ) in b..y₁, f (↑x₀ + ↑y * I)
  set rightInt1 := ∫ (y : ℝ) in y₀..b, f (↑x₁ + ↑y * I)
  set rightInt2 := ∫ (y : ℝ) in b..y₁, f (↑x₁ + ↑y * I)
  have : leftInt = leftInt1 + leftInt2 :=
    (intervalIntegral.integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left).symm
  rw [this]
  have : rightInt = rightInt1 + rightInt2 :=
    (intervalIntegral.integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right).symm
  rw [this]
  ring

lemma SmallSquareInRectangle {z w p : ℂ} (pInRectInterior : Rectangle z w ∈ nhds p) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w := by
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
  have normC : Complex.abs (c + I * c) = c * Real.sqrt 2 := by
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
    rw [(by ring: -(c : ℂ) - I * c = -(c + I * c)), Complex.abs_neg, normC]
    nlinarith
  · simp only [Metric.mem_ball, dist_add_self_left, Complex.norm_eq_abs]
    rw [normC]
    nlinarith
  · simp only [add_re, sub_re, neg_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
    mul_zero, sub_self, sub_zero, ofReal_add, ofReal_neg, add_im, mul_im, one_mul, zero_add]
    rw[(by ring : -(c : ℂ) + p.re + (c + p.im) * I = -c + c * I + (p.re + p.im * I))]
    rw [re_add_im]
    simp only [Metric.mem_ball, dist_add_self_left, Complex.norm_eq_abs]
    rw [normC']
    nlinarith
  · simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
    add_zero, ofReal_add, add_im, sub_im, neg_im, neg_zero, mul_im, one_mul, zero_add, zero_sub,
    ofReal_neg]
    rw [(by ring : (c : ℂ) + p.re + (-c + p.im) * I = c - c * I + (p.re + p.im * I)), re_add_im]
    simp only [Metric.mem_ball, dist_add_self_left, Complex.norm_eq_abs]
    rw [← Complex.abs_neg, neg_sub, sub_eq_add_neg, add_comm, normC']
    nlinarith

lemma RectPull_rectSub1 {z w p : ℂ} (zIm_lt_wIm : z.im < w.im)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w) :
    Rectangle (z.re + z.im * I) (w.re + (p.im - c : ℝ) * I) ⊆ Rectangle z w \ {p} :=
  rect_subset_punctured_rect hc (by simp [sub_eq_neg_add])
    (by simp [cpos, RectPull_im_aux zIm_lt_wIm cpos hc])

lemma RectPull_rectSub2 {z w p : ℂ} (zIm_lt_wIm : z.im < w.im)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w) :
    Rectangle (z.re + (p.im + c : ℝ) * I) (w.re + w.im * I) ⊆ Rectangle z w \ {p}:=
  rect_subset_punctured_rect hc (by simp [add_comm])
    (by simp [cpos, RectPull_im_aux zIm_lt_wIm cpos hc])

lemma RectPull_rectSub3 {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w) :
    Rectangle (z.re + (p.im - c : ℝ) * I) ((p.re - c : ℝ) + (p.im + c : ℝ) * I)
      ⊆ Rectangle z w \ {p} :=
  rect_subset_punctured_rect hc (by simp [sub_eq_neg_add, add_comm])
    (by simp [cpos, RectPull_re_aux zRe_lt_wRe cpos hc])

lemma RectPull_rectSub4 {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w) :
    Rectangle ((p.re + c : ℝ) + (p.im - c : ℝ) * I) (w.re + (p.im + c : ℝ) * I)
      ⊆ Rectangle z w \ {p} :=
  rect_subset_punctured_rect hc (by simp [sub_eq_neg_add, add_comm])
    (by simp [cpos, RectPull_re_aux zRe_lt_wRe cpos hc])


lemma RectPull_aux1 {f : ℂ → ℂ} {z w p : ℂ} (zIm_lt_wIm : z.im < w.im)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (y : ℝ) ↦ f (z.re + y * I)) volume z.im (p.im - c) := by
  have := fCont.rectangleBorderNoPIntegrable
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub1 zIm_lt_wIm cpos hc)
  simpa using mapsTo_left_re z (↑w.re + ↑(p.im - c) * I)

lemma RectPull_aux2 {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (y : ℝ) ↦ f (z.re + y * I)) volume (p.im - c) w.im := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ <| rect_subset_punctured_rect
    (z'' := z.re + (p.im - c) * I) (w'' := z.re + w.im * I)
    hc (by simp [sub_eq_neg_add]) (by simp [cpos, RectPull_re_aux zRe_lt_wRe cpos hc])
  simpa using mapsTo_left_re (↑z.re + (↑p.im - ↑c) * I) (↑z.re + w.im * I)

lemma RectPull_aux3 {f : ℂ → ℂ} {z w p : ℂ} (zIm_lt_wIm : z.im < w.im)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (y : ℝ) ↦ f (w.re + y * I)) volume z.im (p.im - c) := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub1 zIm_lt_wIm cpos hc)
  simpa using mapsTo_right_re z (↑w.re + ↑(p.im - c) * I)

lemma RectPull_aux4 {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (y : ℝ) ↦ f (w.re + y * I)) volume (p.im - c) w.im := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ <| rect_subset_punctured_rect
    (z'' := w.re + (p.im - c) * I) (w'' := w.re + w.im * I)
    hc (by simp [sub_eq_neg_add]) (by simp [cpos, RectPull_re_aux zRe_lt_wRe cpos hc])
  simpa using mapsTo_right_re (↑w.re + (↑p.im - ↑c) * I) (↑w.re + w.im * I)

lemma RectPull_aux5 {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (y : ℝ) ↦ f (z.re + y * I)) volume (p.im - c) (p.im + c) := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub3 zRe_lt_wRe cpos hc)
  simpa using mapsTo_left_re (↑z.re + ↑(p.im - c) * I) (↑(p.re - c) + ↑(p.im + c) * I)

lemma RectPull_aux6 {f : ℂ → ℂ} {z w p : ℂ} (zIm_lt_wIm : z.im < w.im)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (y : ℝ) ↦ f (z.re + y * I)) volume (p.im + c) w.im := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub2 zIm_lt_wIm cpos hc)
  simpa using mapsTo_left_re (↑z.re + ↑(p.im + c) * I) (↑w.re + ↑w.im * I)

lemma RectPull_aux7 {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (y : ℝ) ↦ f (w.re + y * I)) volume (p.im - c) (p.im + c) := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub4 zRe_lt_wRe cpos hc)
  simpa using mapsTo_right_re (↑(p.re + c) + ↑(p.im - c) * I) (↑w.re + ↑(p.im + c) * I)

lemma RectPull_aux8 {f : ℂ → ℂ} {z w p : ℂ} (zIm_lt_wIm : z.im < w.im)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (y : ℝ) ↦ f (w.re + y * I)) volume (p.im + c) w.im := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub2 zIm_lt_wIm cpos hc)
  simpa using mapsTo_right_re (↑z.re + ↑(p.im + c) * I) (↑w.re + ↑w.im * I)

lemma RectPull_aux9 {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (x : ℝ) ↦ f (x + (p.im - c : ℝ) * I)) volume z.re (p.re - c) := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub3 zRe_lt_wRe cpos hc)
  simpa using mapsTo_left_im (↑z.re + ↑(p.im - c) * I) (↑(p.re - c) + ↑(p.im + c) * I)

lemma RectPull_aux10 {f : ℂ → ℂ} {z w p : ℂ}
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (x : ℝ) ↦ f (x + (p.im - c : ℝ) * I)) volume (p.re - c) w.re := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ <| rect_subset_punctured_rect
    (z'' := (p.re - c) + (p.im - c) * I) (w'' := w.re + (p.im - c) * I)
    hc (by simp [sub_eq_neg_add]) (by simp [cpos])
  simpa using mapsTo_left_im (↑p.re - ↑c + (↑p.im - ↑c) * I) (↑w.re + (↑p.im - ↑c) * I)

lemma RectPull_aux11 {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (x : ℝ) ↦ f (x + (p.im + c : ℝ) * I)) volume z.re (p.re - c) := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub3 zRe_lt_wRe cpos hc)
  simpa using mapsTo_right_im (↑z.re + ↑(p.im - c) * I) (↑(p.re - c) + ↑(p.im + c) * I)

lemma RectPull_aux12 {f : ℂ → ℂ} {z w p : ℂ}
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (x : ℝ) ↦ f (x + (p.im + c : ℝ) * I)) volume (p.re - c) w.re := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ <| rect_subset_punctured_rect
    (z'' := (p.re - c) + (p.im + c) * I) (w'' := w.re + (p.im + c) * I)
    hc (by simp [sub_eq_neg_add, add_comm]) (by simp [cpos])
  simpa using mapsTo_right_im (↑p.re - ↑c + (↑p.im + ↑c) * I) (↑w.re + (↑p.im + ↑c) * I)

lemma RectPull_aux13 {f : ℂ → ℂ} {z w p : ℂ}
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (x : ℝ) ↦ f (x + (p.im - c : ℝ) * I)) volume (p.re - c) (p.re + c) := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ <| rect_subset_punctured_rect
    (z'' := (p.re - c) + (p.im - c) * I) (w'' := (p.re + c) + (p.im - c) * I)
    hc (by simp [sub_eq_neg_add, add_comm]) (by simp [cpos])
  simpa using mapsTo_left_im (↑p.re - ↑c + (↑p.im - ↑c) * I) (↑p.re + ↑c + (↑p.im - ↑c) * I)

lemma RectPull_aux14 {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (x : ℝ) ↦ f (x + (p.im - c : ℝ) * I)) volume (p.re + c) w.re := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub4 zRe_lt_wRe cpos hc)
  simpa using mapsTo_left_im (↑(p.re + c) + ↑(p.im - c) * I) (↑w.re + ↑(p.im + c) * I)

lemma RectPull_aux15 {f : ℂ → ℂ} {z w p : ℂ}
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (x : ℝ) ↦ f (x + (p.im + c : ℝ) * I)) volume (p.re - c) (p.re + c) := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ <| rect_subset_punctured_rect
    (z'' := (p.re - c) + (p.im + c) * I) (w'' := (p.re + c) + (p.im + c) * I)
    hc (by simp [sub_eq_neg_add, add_comm]) (by simp [cpos])
  simpa using mapsTo_right_im (↑p.re - ↑c + (↑p.im + ↑c) * I) (↑p.re + ↑c + (↑p.im + ↑c) * I)

lemma RectPull_aux16 {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    {c : ℝ} (cpos : 0 < c) (hc : Rectangle (-c - I * c + p) (c + I * c + p) ⊆ Rectangle z w)
    (fCont : ContinuousOn f (Rectangle z w \ {p})) :
    IntervalIntegrable (fun (x : ℝ) ↦ f (x + (p.im + c : ℝ) * I)) volume (p.re + c) w.re := by
  refine (fCont.comp (by fun_prop) ?_).intervalIntegrable
  refine MapsTo.mono_right ?_ (RectPull_rectSub4 zRe_lt_wRe cpos hc)
  simpa using mapsTo_right_im (↑(p.re + c) + ↑(p.im - c) * I) (↑w.re + ↑(p.im + c) * I)

/-%%
The next lemma allows to zoom a big rectangle down to a small square, centered at a pole.

\begin{lemma}[RectanglePullToNhdOfPole]\label{RectanglePullToNhdOfPole}\lean{RectanglePullToNhdOfPole}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$ except at a point $p$, then the integral of $f$
over the rectangle with corners $z$ and $w$ is the same as the integral of $f$ over a small square
centered at $p$.
\end{lemma}
%%-/
lemma RectanglePullToNhdOfPole {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    (zIm_lt_wIm : z.im < w.im) (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, RectangleIntegral f z w =
      RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
--%% \begin{proof}\uses{HolomorphicOn.vanishesOnRectangle}\leanok
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' zero_lt_one, SmallSquareInRectangle pInRectInterior]
  intro c ⟨cpos, _⟩ hc
  have fCont : ContinuousOn f (Rectangle z w \ {p}) := fHolo.continuousOn
  rw [← re_add_im z, ← re_add_im w,
-- First chop off the bottom of the rectangle
    RectangleIntegralVSplit (p.im - c)
    (RectPull_aux1 zIm_lt_wIm cpos hc fCont) (RectPull_aux2 zRe_lt_wRe cpos hc fCont)
    (RectPull_aux3 zIm_lt_wIm cpos hc fCont) (RectPull_aux4 zRe_lt_wRe cpos hc fCont),
    HolomorphicOn.vanishesOnRectangle fHolo (RectPull_rectSub1 zIm_lt_wIm cpos hc), zero_add,
-- Then chop off the top of the rectangle
    RectangleIntegralVSplit (p.im + c)
    (RectPull_aux5 zRe_lt_wRe cpos hc fCont) (RectPull_aux6 zIm_lt_wIm cpos hc fCont)
    (RectPull_aux7 zRe_lt_wRe cpos hc fCont) (RectPull_aux8 zIm_lt_wIm cpos hc fCont),
    HolomorphicOn.vanishesOnRectangle fHolo (RectPull_rectSub2 zIm_lt_wIm cpos hc), add_zero,
-- Then chop off the left of the rectangle
    RectangleIntegralHSplit (p.re - c)
    (RectPull_aux9 zRe_lt_wRe cpos hc fCont) (RectPull_aux10 cpos hc fCont)
    (RectPull_aux11 zRe_lt_wRe cpos hc fCont) (RectPull_aux12 cpos hc fCont),
    HolomorphicOn.vanishesOnRectangle fHolo (RectPull_rectSub3 zRe_lt_wRe cpos hc), zero_add,
-- Then chop off the right of the rectangle
    RectangleIntegralHSplit (p.re + c)
    (RectPull_aux13 cpos hc fCont) (RectPull_aux14 zRe_lt_wRe cpos hc fCont)
    (RectPull_aux15 cpos hc fCont) (RectPull_aux16 zRe_lt_wRe cpos hc fCont),
    HolomorphicOn.vanishesOnRectangle fHolo (RectPull_rectSub4 zRe_lt_wRe cpos hc), add_zero]
  congr 1 <;> apply Complex.ext <;> simp [sub_eq_neg_add, add_comm]
/-%%
Chop the big rectangle with two vertical cuts and two horizontal cuts into smaller rectangles,
the middle one being the desired square. The integral over each of the outer rectangles
vanishes, since $f$ is holomorphic there. (The constant $c$ being ``small enough'' here just means
that the inner square is strictly contained in the big rectangle.)
\end{proof}
%%-/

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
