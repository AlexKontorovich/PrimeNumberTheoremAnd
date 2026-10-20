import Architect
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

/-! ## Support lemmas for norm, scalar embedding, and products -/

open Complex Set

/-- Taking the norm preserves the support. -/
@[blueprint "Function.support_abs"
  (title := "Support of the norm")
  (statement := /-- The support of $x\mapsto\lVert f(x)\rVert$ is the support of $f$. -/)
  (proof := /-- A vector has zero norm exactly when it is zero. -/), simp]
lemma Function.support_abs {α E : Type*} [NormedAddGroup E] (f : α → E) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

/-- Embedding a real-valued function into the complex numbers preserves its support. -/
@[blueprint "Function.support_ofReal"
  (title := "Support under real-to-complex embedding")
  (statement := /-- The real and complex interpretations of $f$ have the same support. -/)
  (proof := /-- The real-to-complex embedding is injective and preserves zero. -/), simp]
lemma Function.support_ofReal {α : Type*} {f : α → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

/-- A pointwise product is supported wherever its first factor is supported. -/
@[blueprint "Function.support_mul_subset_of_subset"
  (title := "Support of a pointwise product")
  (statement := /-- If the support of $f$ lies in $s$, then so does the support of $fg$.
    This holds even in the presence of zero divisors. -/)
  (proof := /-- A nonzero product has a nonzero first factor. -/)]
lemma Function.support_mul_subset_of_subset {α M : Type*} [MulZeroClass M]
    {s : Set α} {f g : α → M}
    (fSupp : f.support ⊆ s) : (f * g).support ⊆ s := by
  exact (Function.support_mul_subset_left f g).trans fSupp

/-- Fiberwise support bounds combine to give a product support bound. -/
@[blueprint "Function.support_of_along_fiber_subset_subset"
  (title := "Support from fiberwise bounds")
  (statement := /-- If every horizontal fiber is supported in $s$ and every vertical
    fiber is supported in $t$, then the function is supported in $s\times t$. -/)
  (proof := /-- Apply the two fiberwise assumptions at each nonzero value. -/)]
lemma Function.support_of_along_fiber_subset_subset {α β M : Type*} [Zero M]
    {f : α × β → M} {s : Set α} {t : Set β}
    (hx : ∀ (y : β), (fun x ↦ f (x, y)).support ⊆ s)
    (hy : ∀ (x : α), (fun y ↦ f (x, y)).support ⊆ t) :
    f.support ⊆ s ×ˢ t := by
  intro ⟨x, y⟩ hxy
  constructor
  · exact hx y (by simp only [Function.mem_support, ne_eq] at hxy ⊢; exact hxy)
  · exact hy x (by simp only [Function.mem_support, ne_eq] at hxy ⊢; exact hxy)
