import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.ZetaConj
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Zero counting and square-tail summability for the non-trivial zeta zeros

This file develops the zero-counting layer needed by the Kadiri explicit-formula work:
finiteness of the non-trivial zeros in horizontal strips, and summability of the
height-square tails `Sum_rho 1/|Im rho|^2` (and their shifts `Sum_rho 1/|Im (s-rho)|^2`)
from a Riemann-von Mangoldt zero-counting estimate, taken throughout as an explicit
hypothesis `riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1` (Backlund's constants).

The route is dyadic. The count of zeros with `|Im rho| < 2^(k+1)` is compared with the
project counting function `N(T)`: conjugation symmetry handles negative heights, the
real-axis bucket is finite, and multiplicities only increase the count. Then `N(T)` is
bounded by the explicit Backlund majorant
`|T/2pi log (T/2pi) - T/2pi + 7/8| + RvM(T)`, which grows like `(k+1) * 2^k` on dyadic
heights, so the dyadic shell masses are summable against `(k+1) * 2^(-k)`.

Since the counting estimate stays hypothetical, this file imports only `ZetaDefinitions`
and `ZetaConj` from the project.
-/

noncomputable section

namespace Kadiri

open Complex Filter


/-- The non-trivial zeta zeros as currently represented in the project. -/
abbrev NontrivialZeros : Set ℂ :=
  riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ)

/-- Local source form for conjugation stability of zeta zeros. -/
def riemannZetaConjZeroSource : Prop :=
  ∀ z : ℂ, riemannZeta z = 0 → riemannZeta ((starRingEnd ℂ) z) = 0

theorem riemannZetaConjZeroSource_of_riemannZeta_conj :
    riemannZetaConjZeroSource := by
  intro z hz
  rw [riemannZeta_conj, hz]
  simp

lemma nontrivialZero_ne_one (rho : NontrivialZeros) : (rho : ℂ) ≠ 1 := by
  intro h
  have hre : (rho : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := rho.property.1
  rw [h] at hre
  norm_num at hre

lemma riemannZeta_analyticAt_nontrivialZero (rho : NontrivialZeros) :
    AnalyticAt ℂ riemannZeta (rho : ℂ) := by
  exact riemannZeta_analyticOn_compl_one (rho : ℂ)
    (by simpa [Set.mem_compl_iff] using nontrivialZero_ne_one rho)

lemma riemannZeta_nontrivialZero_zero (rho : NontrivialZeros) :
    riemannZeta (rho : ℂ) = 0 := by
  exact rho.property.2.2

lemma riemannZeta_eventually_ne_zero_punctured_nontrivialZero (rho : NontrivialZeros) :
    ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ), riemannZeta z ≠ 0 := by
  have hmem_compl_one : (rho : ℂ) ∈ ({1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff] using nontrivialZero_ne_one rho
  have hdisj : Disjoint (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
      (𝓟 (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)) := by
    exact (mem_codiscreteWithin.mp riemannZeta.zeroes_codiscreteWithin_compl_one)
      (rho : ℂ) hmem_compl_one
  have hnot_zeroes : (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)ᶜ ∈
      nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ) :=
    Filter.disjoint_principal_right.mp hdisj
  have heventually_compl_one : ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ),
      z ∈ ({1} : Set ℂ)ᶜ := by
    exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hmem_compl_one)
  filter_upwards [hnot_zeroes, heventually_compl_one] with z hznot hz_compl_one hzero
  have hz_zero : z ∈ riemannZeta.zeroes := by
    simpa [riemannZeta.zeroes] using hzero
  exact hznot ⟨hz_compl_one, by simpa using hz_zero⟩

lemma riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero (rho : NontrivialZeros) :
    meromorphicOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
  have han := riemannZeta_analyticAt_nontrivialZero rho
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2
    (riemannZeta_eventually_ne_zero_punctured_nontrivialZero rho)

lemma riemannZeta_order_pos_nontrivialZero (rho : NontrivialZeros) :
    0 < riemannZeta.order (rho : ℂ) := by
  have han := riemannZeta_analyticAt_nontrivialZero rho
  have hzero := riemannZeta_nontrivialZero_zero rho
  have horder_ne_top := riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero rho
  have hanOrder_ne_zero : analyticOrderAt riemannZeta (rho : ℂ) ≠ 0 := by
    intro h
    exact (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold riemannZeta.order
  cases hO : analyticOrderAt riemannZeta (rho : ℂ) with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have hn_pos : 0 < n := by
        exact Nat.pos_of_ne_zero (by
          intro hn
          exact hanOrder_ne_zero (by simp [hO, hn]))
      rw [han.meromorphicOrderAt_eq, hO, ENat.map_coe, WithTop.untopD_coe]
      exact_mod_cast hn_pos

lemma riemannZeta_one_le_order_nontrivialZero (rho : NontrivialZeros) :
    (1 : ℤ) ≤ riemannZeta.order (rho : ℂ) := by
  exact_mod_cast riemannZeta_order_pos_nontrivialZero rho

def positiveHeightNontrivialZeroEquivZeroesRect (T : ℝ) :
    {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} ≃
      riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T) where
  toFun rho :=
    ⟨(rho : ℂ),
      rho.1.property.1,
      by exact ⟨rho.2.1, rho.2.2⟩,
      rho.1.property.2.2⟩
  invFun rho :=
    ⟨⟨(rho : ℂ),
        rho.property.1,
        Set.mem_univ _,
        rho.property.2.2⟩,
      by exact ⟨rho.property.2.1.1, rho.property.2.1.2⟩⟩
  left_inv rho := by
    ext
    rfl
  right_inv rho := by
    ext
    rfl

lemma zeroes_rect_Ioo_critical_positive_height_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T)).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) ∩
    (Complex.im ⁻¹' Set.Icc (0 : ℝ) T)
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨Set.Ioo_subset_Icc_self hre, Set.Ioo_subset_Icc_self him⟩, hzeta⟩

lemma zeroes_rect_positive_height_card_le_zeroes_sum_order (T : ℝ) :
    (Nat.card (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T)) : ℝ) ≤
      riemannZeta.zeroes_sum (.Ioo 0 1) (.Ioo 0 T) (fun _ ↦ (1 : ℝ)) := by
  classical
  haveI : Finite (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T)) :=
    Set.finite_coe_iff.mpr (zeroes_rect_Ioo_critical_positive_height_finite T)
  letI := Fintype.ofFinite (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T))
  unfold riemannZeta.zeroes_sum
  rw [tsum_fintype]
  calc
    (Nat.card (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T)) : ℝ)
        = ∑ _rho : riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T), (1 : ℝ) := by
          simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ rho : riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T),
          (riemannZeta.order (rho : ℂ) : ℝ) := by
          refine Finset.sum_le_sum fun rho _ ↦ ?_
          have horder : (1 : ℤ) ≤ riemannZeta.order (rho : ℂ) :=
            riemannZeta_one_le_order_nontrivialZero
              ⟨(rho : ℂ), rho.property.1, Set.mem_univ _, rho.property.2.2⟩
          exact_mod_cast horder
    _ = ∑ rho : riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T),
          (1 : ℝ) * (riemannZeta.order (rho : ℂ) : ℝ) := by
          simp

lemma positive_height_nontrivial_zero_count_le_NPrime (T : ℝ) :
    (Nat.card {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} : ℝ) ≤
      riemannZeta.N' 0 T := by
  have hcard :
      Nat.card {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} =
        Nat.card (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T)) :=
    Nat.card_congr (positiveHeightNontrivialZeroEquivZeroesRect T)
  rw [hcard, riemannZeta.N']
  exact zeroes_rect_positive_height_card_le_zeroes_sum_order T

lemma positiveHeightZero_ne_one {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (rho : ℂ) ≠ 1 := by
  intro h
  have him : (rho : ℂ).im ∈ Set.Ioo (0 : ℝ) T := rho.property.2.1
  rw [h] at him
  norm_num at him

lemma riemannZeta_analyticAt_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    AnalyticAt ℂ riemannZeta (rho : ℂ) := by
  exact riemannZeta_analyticOn_compl_one (rho : ℂ)
    (by simpa [Set.mem_compl_iff] using positiveHeightZero_ne_one rho)

lemma riemannZeta_positiveHeightZero_zero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    riemannZeta (rho : ℂ) = 0 := by
  exact rho.property.2.2

lemma riemannZeta_eventually_ne_zero_punctured_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ), riemannZeta z ≠ 0 := by
  have hmem_compl_one : (rho : ℂ) ∈ ({1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff] using positiveHeightZero_ne_one rho
  have hdisj : Disjoint (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
      (𝓟 (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)) := by
    exact (mem_codiscreteWithin.mp riemannZeta.zeroes_codiscreteWithin_compl_one)
      (rho : ℂ) hmem_compl_one
  have hnot_zeroes : (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)ᶜ ∈
      nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ) :=
    Filter.disjoint_principal_right.mp hdisj
  have heventually_compl_one : ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ),
      z ∈ ({1} : Set ℂ)ᶜ := by
    exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hmem_compl_one)
  filter_upwards [hnot_zeroes, heventually_compl_one] with z hznot hz_compl_one hzero
  have hz_zero : z ∈ riemannZeta.zeroes := by
    simpa [riemannZeta.zeroes] using hzero
  exact hznot ⟨hz_compl_one, by simpa using hz_zero⟩

lemma riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    meromorphicOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
  have han := riemannZeta_analyticAt_positiveHeightZero rho
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2
    (riemannZeta_eventually_ne_zero_punctured_positiveHeightZero rho)

lemma riemannZeta_order_pos_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    0 < riemannZeta.order (rho : ℂ) := by
  have han := riemannZeta_analyticAt_positiveHeightZero rho
  have hzero := riemannZeta_positiveHeightZero_zero rho
  have horder_ne_top := riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero rho
  have hanOrder_ne_zero : analyticOrderAt riemannZeta (rho : ℂ) ≠ 0 := by
    intro h
    exact (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold riemannZeta.order
  cases hO : analyticOrderAt riemannZeta (rho : ℂ) with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have hn_pos : 0 < n := by
        exact Nat.pos_of_ne_zero (by
          intro hn
          exact hanOrder_ne_zero (by simp [hO, hn]))
      rw [han.meromorphicOrderAt_eq, hO, ENat.map_coe, WithTop.untopD_coe]
      exact_mod_cast hn_pos

lemma riemannZeta_one_le_order_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (1 : ℤ) ≤ riemannZeta.order (rho : ℂ) := by
  exact_mod_cast riemannZeta_order_pos_positiveHeightZero rho

lemma riemannZeta_ne_zero_of_re_nonpos_im_ne_zero {z : ℂ}
    (hre : z.re ≤ 0) (him : z.im ≠ 0) : riemannZeta z ≠ 0 := by
  let w : ℂ := 1 - z
  have hw_im : w.im ≠ 0 := by
    dsimp [w]
    simp [him]
  have hw_re : 1 ≤ w.re := by
    dsimp [w]
    simp
    linarith
  have hzeta_w : riemannZeta w ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hw_re
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have : w.im = 0 := by
      rw [hn]
      simp
    exact hw_im this
  have hw_ne_one : w ≠ 1 := by
    intro h
    have : w.im = 0 := by
      rw [h]
      simp
    exact hw_im this
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero hw_neg_nat
  have hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hleft : (↑Real.pi * w / 2).im ≠ 0 := by
      rw [show (↑Real.pi * w / 2).im = Real.pi * w.im / 2 by
        simp [div_eq_mul_inv, mul_assoc]]
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hw_im) two_ne_zero
    have hright : (((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2).im) = 0 := by
      simp [div_eq_mul_inv, mul_assoc]
    exact hleft (by rw [hk, hright])
  have hfactor : 2 * (2 * ↑Real.pi : ℂ) ^ (-w) * Complex.Gamma w *
      Complex.cos (↑Real.pi * w / 2) * riemannZeta w ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos)
      hzeta_w
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  have hone : 1 - w = z := by
    dsimp [w]
    ring
  rw [hone] at hfe
  rw [hfe]
  exact hfactor

lemma positiveHeightZero_re_mem_Ioo {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (rho : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := by
  have him_pos : 0 < (rho : ℂ).im := rho.property.2.1.1
  have hzeta : riemannZeta (rho : ℂ) = 0 := rho.property.2.2
  have hnot_re_nonpos : ¬ (rho : ℂ).re ≤ 0 := by
    intro hre
    exact (riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hre him_pos.ne') hzeta
  have hre_pos : 0 < (rho : ℂ).re := lt_of_not_ge hnot_re_nonpos
  have hnot_re_one_le : ¬ 1 ≤ (rho : ℂ).re := by
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta
  have hre_lt_one : (rho : ℂ).re < 1 := lt_of_not_ge hnot_re_one_le
  exact ⟨hre_pos, hre_lt_one⟩

lemma zeroes_rect_univ_positive_height_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).Finite := by
  have hsub :
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T) ⊆
        riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo 0 T) := by
    intro z hz
    exact ⟨positiveHeightZero_re_mem_Ioo ⟨z, hz⟩, hz.2.1, hz.2.2⟩
  exact (zeroes_rect_Ioo_critical_positive_height_finite T).subset hsub

theorem zeroImagDyadicNOrderSummableSource_of_positive_height_zero_free :
    ∀ k : ℕ,
      Summable (fun rho : riemannZeta.zeroes_rect (.univ : Set ℝ)
          (.Ioo 0 ((2 : ℝ) ^ (k + 1))) =>
        (riemannZeta.order (rho : ℂ) : ℝ)) := by
  intro k
  haveI : Finite (riemannZeta.zeroes_rect (.univ : Set ℝ)
      (.Ioo 0 ((2 : ℝ) ^ (k + 1)))) :=
    Set.finite_coe_iff.mpr
      (zeroes_rect_univ_positive_height_finite ((2 : ℝ) ^ (k + 1)))
  exact Summable.of_finite

/-- Non-trivial zeros on the real axis, kept as a separate finite bucket. -/
abbrev ZeroHeightNontrivialZeros : Type :=
  {rho : NontrivialZeros // (rho : ℂ).im = 0}

def zeroHeightNontrivialZeroEquivZeroesRectZero :
    ZeroHeightNontrivialZeros ≃
      riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc 0 0) where
  toFun rho :=
    ⟨(rho : ℂ),
      rho.1.property.1,
      by simp [rho.2],
      rho.1.property.2.2⟩
  invFun rho :=
    ⟨⟨(rho : ℂ),
        rho.property.1,
        Set.mem_univ _,
        rho.property.2.2⟩,
      by exact le_antisymm rho.property.2.1.2 rho.property.2.1.1⟩
  left_inv rho := by
    ext
    rfl
  right_inv rho := by
    ext
    rfl

lemma zeroes_rect_Ioo_critical_zero_height_finite :
    (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc 0 0)).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) ∩
    (Complex.im ⁻¹' Set.Icc (0 : ℝ) 0)
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨Set.Ioo_subset_Icc_self hre, him⟩, hzeta⟩

lemma zeroHeightNontrivialZeros_finite : Finite ZeroHeightNontrivialZeros := by
  haveI : Finite (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc 0 0)) :=
    Set.finite_coe_iff.mpr zeroes_rect_Ioo_critical_zero_height_finite
  exact Finite.of_equiv _ zeroHeightNontrivialZeroEquivZeroesRectZero.symm

/-- Square tail against the zero set, shifted by `a`. -/
def zeroSquareTail (a : ℂ) (rho : NontrivialZeros) : ℝ :=
  (‖a - (rho : ℂ)‖)⁻¹ ^ (2 : ℕ)

/-- Source contract: square zero tails are summable at shift `a`. -/
def zeroSquareTailSummable (a : ℂ) : Prop :=
  Summable (fun rho : NontrivialZeros ↦ zeroSquareTail a rho)

/-- Height-square tail for zeros, the form produced by zero-counting estimates. -/
def zeroImagSquareTail (rho : NontrivialZeros) : ℝ :=
  |(rho : ℂ).im|⁻¹ ^ (2 : ℕ)

/-- Source contract: the height-square zero tail is summable. -/
def zeroImagSquareTailSummable : Prop :=
  Summable (fun rho : NontrivialZeros ↦ zeroImagSquareTail rho)


/-- Dyadic height shell for non-trivial zeros. -/
def zeroHeightDyadicShell (k : ℕ) (rho : NontrivialZeros) : Prop :=
  (2 : ℝ) ^ k ≤ |(rho : ℂ).im| ∧ |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)

/-- Source contract: dyadic-shell height-square summability. -/
def zeroImagDyadicShellSummableSource : Prop :=
  Summable
    (fun p : Sigma (fun k : ℕ =>
        {rho : NontrivialZeros // zeroHeightDyadicShell k rho}) =>
      zeroImagSquareTail p.2.1)

/-- The height-square mass in a dyadic shell. -/
def zeroHeightDyadicShellMass (k : ℕ) : ℝ :=
  ∑' rho : {rho : NontrivialZeros // zeroHeightDyadicShell k rho},
    zeroImagSquareTail rho.1

/-- Source contract: Backlund-shaped dyadic shell count growth. -/
def zeroImagDyadicShellCountBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} : ℝ) ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)

/--
Source contract: cumulative Backlund-shaped zero counts below dyadic height.
This is closer to the `N(T)` input; the shell contract follows by inclusion.
-/
def zeroImagDyadicCumulativeCountBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)

/-- Main term used by the local Riemann-von Mangoldt API. -/
def zetaCountingMainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8

/-- Absolute-value majorant supplied by an RvM estimate. -/
def zetaCountingBacklundMajorant (b₁ b₂ b₃ T : ℝ) : ℝ :=
  |zetaCountingMainTerm T| + riemannZeta.RvM b₁ b₂ b₃ T

/-- The Backlund majorant on dyadic heights. -/
def zetaCountingDyadicMajorant (b₁ b₂ b₃ : ℝ) (k : ℕ) : ℝ :=
  zetaCountingBacklundMajorant b₁ b₂ b₃ ((2 : ℝ) ^ (k + 1))

/-- Source contract: dyadic growth of the RvM main term. -/
def zetaCountingMainTermDyadicGrowthSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    |zetaCountingMainTerm ((2 : ℝ) ^ (k + 1))| ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)

/-- Source contract: dyadic growth of the explicit Backlund majorant. -/
def zetaCountingDyadicMajorantGrowthSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    zetaCountingDyadicMajorant 0.137 0.443 6.1 k ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)

/--
Source contract: cumulative unweighted zero counts are bounded by the
multiplicity-counting `N(T)` API on dyadic heights.
-/
def zeroImagDyadicCumulativeCountByNSource : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))|

/--
Count by `N(T)` with an additive finite bucket. This is the honest form when
zero-height non-trivial zeros have not been ruled out in Lean.
-/
def zeroImagDyadicCumulativeCountByNWithZeroHeightSource : Prop :=
  ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D

/--
Source contract: absolute-height dyadic counts reduce to positive-height
critical-strip counts. This is the symmetry/strip-localisation part, separate
from multiplicity.
-/
def zeroImagDyadicAbsToPositiveCountSource : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ)

/--
Source contract with the real-axis bucket kept explicit. Conjugation gives the
two positive-height buckets; zero-height non-trivial zeros must be handled
separately unless a no-real-nontrivial-zero lemma is imported.
-/
def zeroImagDyadicAbsToPositiveCountWithZeroHeightSource : Prop :=
  ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ) + D

/--
Source contract: the positive critical-strip count `N' 0 T` is controlled by
the project-level `N(T)` API on dyadic heights.
-/
def zeroImagDyadicNPrimeToNSource : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ,
    |riemannZeta.N' 0 ((2 : ℝ) ^ (k + 1))| ≤
      B * |riemannZeta.N ((2 : ℝ) ^ (k + 1))|

/--
Source contract: the positive-height multiplicity series defining `N(T)` is
summable at the dyadic heights needed by the comparison source.
-/
def zeroImagDyadicNOrderSummableSource : Prop :=
  ∀ k : ℕ,
    Summable (fun rho : riemannZeta.zeroes_rect (.univ : Set ℝ)
        (.Ioo 0 ((2 : ℝ) ^ (k + 1))) =>
      (riemannZeta.order (rho : ℂ) : ℝ))

/-- Source contract: dyadic shell mass is bounded by a summable geometric majorant. -/
def zeroImagDyadicShellMassBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    zeroHeightDyadicShellMass k ≤ C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ k

/-- Assign each zero of height at least one to its dyadic shell. -/
def highZeroToDyadicShell (rho : {rho : NontrivialZeros // 1 ≤ |(rho : ℂ).im|}) :
    Sigma (fun k : ℕ => {rho : NontrivialZeros // zeroHeightDyadicShell k rho}) :=
  let hnear := exists_nat_pow_near
    (x := |((rho.1 : ℂ).im)|) (y := (2 : ℝ)) rho.2 (by norm_num)
  ⟨hnear.choose, ⟨rho.1, hnear.choose_spec⟩⟩

/-- Include a dyadic shell into the cumulative height set with the same top edge. -/
def dyadicShellToCumulative (k : ℕ) :
    {rho : NontrivialZeros // zeroHeightDyadicShell k rho} →
      {rho : NontrivialZeros // |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} :=
  fun rho => ⟨rho.1, rho.2.2⟩

lemma dyadicShellToCumulative_injective (k : ℕ) :
    Function.Injective (dyadicShellToCumulative k) := by
  intro rho eta h
  apply Subtype.ext
  exact congrArg
    (fun z : {rho : NontrivialZeros // |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} =>
      (z : NontrivialZeros)) h

/-- Non-trivial zeros are nonzero in the current `zeroes_rect` representation. -/
lemma nontrivialZero_ne_zero (rho : NontrivialZeros) : (rho : ℂ) ≠ 0 := by
  intro h
  have hpos : 0 < (rho : ℂ).re := rho.property.1.1
  rw [h] at hpos
  norm_num at hpos

/-- Only finitely many non-trivial zeros lie in a bounded norm ball. -/
lemma nontrivialZeros_norm_lt_finite (R : ℝ) :
    ({rho : NontrivialZeros | ‖(rho : ℂ)‖ < R} : Set NontrivialZeros).Finite := by
  refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.coe_injective)
  apply Set.Finite.subset
    (riemannZeta.zeroes_on_Compact_finite' (ProperSpace.isCompact_closedBall (0 : ℂ) R))
  intro z hz
  rcases hz with ⟨rho, hrho, rfl⟩
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hrho
  · exact rho.property.2.2

/-- Only finitely many non-trivial zeros have height less than one in absolute value. -/
lemma nontrivialZeros_abs_im_lt_one_finite :
    ({rho : NontrivialZeros | |(rho : ℂ).im| < 1} : Set NontrivialZeros).Finite := by
  apply Set.Finite.subset (nontrivialZeros_norm_lt_finite 2)
  intro rho hrho
  rw [Set.mem_setOf_eq] at hrho ⊢
  have hre_nonneg : 0 ≤ (rho : ℂ).re := le_of_lt rho.property.1.1
  have hre_abs_lt_one : |(rho : ℂ).re| < 1 := by
    rw [abs_of_nonneg hre_nonneg]
    exact rho.property.1.2
  have hnorm_le : ‖(rho : ℂ)‖ ≤ |(rho : ℂ).re| + |(rho : ℂ).im| :=
    Complex.norm_le_abs_re_add_abs_im (rho : ℂ)
  linarith

/-- Only finitely many non-trivial zeros have bounded absolute height. -/
lemma nontrivialZeros_abs_im_lt_finite (T : ℝ) :
    ({rho : NontrivialZeros | |(rho : ℂ).im| < T} : Set NontrivialZeros).Finite := by
  apply Set.Finite.subset (nontrivialZeros_norm_lt_finite (T + 1))
  intro rho hrho
  rw [Set.mem_setOf_eq] at hrho ⊢
  have hre_nonneg : 0 ≤ (rho : ℂ).re := le_of_lt rho.property.1.1
  have hre_abs_lt_one : |(rho : ℂ).re| < 1 := by
    rw [abs_of_nonneg hre_nonneg]
    exact rho.property.1.2
  have hnorm_le : ‖(rho : ℂ)‖ ≤ |(rho : ℂ).re| + |(rho : ℂ).im| :=
    Complex.norm_le_abs_re_add_abs_im (rho : ℂ)
  linarith

/-- Every dyadic height shell contains finitely many non-trivial zeros. -/
lemma nontrivialZeros_dyadic_shell_finite (k : ℕ) :
    ({rho : NontrivialZeros | zeroHeightDyadicShell k rho} : Set NontrivialZeros).Finite := by
  apply Set.Finite.subset (nontrivialZeros_norm_lt_finite (((2 : ℝ) ^ (k + 1)) + 1))
  intro rho hrho
  rw [Set.mem_setOf_eq] at hrho ⊢
  have hre_nonneg : 0 ≤ (rho : ℂ).re := le_of_lt rho.property.1.1
  have hre_abs_lt_one : |(rho : ℂ).re| < 1 := by
    rw [abs_of_nonneg hre_nonneg]
    exact rho.property.1.2
  have him_lt : |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) := hrho.2
  have hnorm_le : ‖(rho : ℂ)‖ ≤ |(rho : ℂ).re| + |(rho : ℂ).im| :=
    Complex.norm_le_abs_re_add_abs_im (rho : ℂ)
  linarith

/-- Only finitely many non-trivial zeros have shifted height less than one. -/
lemma nontrivialZeros_shifted_abs_im_lt_one_finite (s : ℂ) :
    ({rho : NontrivialZeros | |(s - (rho : ℂ)).im| < 1} :
      Set NontrivialZeros).Finite := by
  apply Set.Finite.subset (nontrivialZeros_norm_lt_finite (|s.im| + 2))
  intro rho hrho
  rw [Set.mem_setOf_eq] at hrho ⊢
  have hre_nonneg : 0 ≤ (rho : ℂ).re := le_of_lt rho.property.1.1
  have hre_abs_lt_one : |(rho : ℂ).re| < 1 := by
    rw [abs_of_nonneg hre_nonneg]
    exact rho.property.1.2
  have him_eq : (rho : ℂ).im = s.im - (s - (rho : ℂ)).im := by
    simp only [Complex.sub_im]
    ring
  have him_le : |(rho : ℂ).im| ≤ |s.im| + |(s - (rho : ℂ)).im| := by
    rw [him_eq]
    exact abs_sub s.im (s - (rho : ℂ)).im
  have him_lt : |(rho : ℂ).im| < |s.im| + 1 := by
    linarith
  have hnorm_le : ‖(rho : ℂ)‖ ≤ |(rho : ℂ).re| + |(rho : ℂ).im| :=
    Complex.norm_le_abs_re_add_abs_im (rho : ℂ)
  linarith

/-- The dyadic shell assignment is injective on zeros of height at least one. -/
lemma highZeroToDyadicShell_injective : Function.Injective highZeroToDyadicShell := by
  intro a b h
  apply Subtype.ext
  have hval := congrArg
    (fun p : Sigma (fun k : ℕ =>
        {rho : NontrivialZeros // zeroHeightDyadicShell k rho}) =>
      (p.2.1 : NontrivialZeros)) h
  simpa [highZeroToDyadicShell] using hval

/-- If `Re s > 1`, then `s-rho` cannot vanish for a non-trivial zero `rho`. -/
lemma sub_nontrivialZero_ne_zero {s : ℂ} (hs : 1 < s.re)
    (rho : NontrivialZeros) : s - (rho : ℂ) ≠ 0 := by
  intro h
  have heq : s = (rho : ℂ) := sub_eq_zero.mp h
  have hlt : (rho : ℂ).re < 1 := rho.property.1.2
  rw [heq] at hs
  exact (not_lt_of_ge hs.le) hlt

/-- Away from finitely many small zeros, a shifted square tail is controlled by the zero tail. -/
lemma zeroSquareTail_shift_le_four_zero {s : ℂ} {rho : NontrivialZeros}
    (hlarge : 2 * ‖s‖ ≤ ‖(rho : ℂ)‖) :
    zeroSquareTail s rho ≤ 4 * zeroSquareTail 0 rho := by
  have hrho : (rho : ℂ) ≠ 0 := nontrivialZero_ne_zero rho
  have hrho_norm_pos : 0 < ‖(rho : ℂ)‖ := norm_pos_iff.mpr hrho
  have hhalf_pos : 0 < ‖(rho : ℂ)‖ / 2 := half_pos hrho_norm_pos
  have hs_le_half : ‖s‖ ≤ ‖(rho : ℂ)‖ / 2 := by nlinarith
  have hhalf_le_sub : ‖(rho : ℂ)‖ / 2 ≤ ‖(rho : ℂ)‖ - ‖s‖ := by
    nlinarith
  have hrev : ‖(rho : ℂ)‖ - ‖s‖ ≤ ‖(rho : ℂ) - s‖ :=
    norm_sub_norm_le (rho : ℂ) s
  have hhalf_le_w : ‖(rho : ℂ)‖ / 2 ≤ ‖s - (rho : ℂ)‖ := by
    exact le_trans hhalf_le_sub (by simpa [norm_sub_rev] using hrev)
  have hinv : ‖s - (rho : ℂ)‖⁻¹ ≤ (‖(rho : ℂ)‖ / 2)⁻¹ :=
    inv_anti₀ hhalf_pos hhalf_le_w
  have hinv_eq : (‖(rho : ℂ)‖ / 2)⁻¹ = 2 * ‖(rho : ℂ)‖⁻¹ := by
    field_simp [norm_ne_zero_iff.mpr hrho]
  have hinv_bound : ‖s - (rho : ℂ)‖⁻¹ ≤ 2 * ‖(rho : ℂ)‖⁻¹ := by
    simpa [hinv_eq] using hinv
  have hinv_nonneg : 0 ≤ ‖s - (rho : ℂ)‖⁻¹ :=
    inv_nonneg.mpr (norm_nonneg _)
  have hpow :
      ‖s - (rho : ℂ)‖⁻¹ ^ (2 : ℕ) ≤
        (2 * ‖(rho : ℂ)‖⁻¹) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hinv_nonneg hinv_bound 2
  have hpow_eq :
      (2 * ‖(rho : ℂ)‖⁻¹) ^ (2 : ℕ) =
        4 * ‖(rho : ℂ)‖⁻¹ ^ (2 : ℕ) := by
    ring
  unfold zeroSquareTail
  rw [zero_sub, norm_neg]
  exact le_trans hpow (by rw [hpow_eq])

/-- Shifted square zero tails follow from the unshifted square zero tail. -/
theorem zeroSquareTailSummable_shift_of_zero {s : ℂ}
    (htail0 : zeroSquareTailSummable 0) :
    zeroSquareTailSummable s := by
  unfold zeroSquareTailSummable at htail0 ⊢
  refine Summable.of_norm_bounded_eventually (htail0.mul_left 4) ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (nontrivialZeros_norm_lt_finite (2 * ‖s‖))
  intro rho hbad
  rw [Set.mem_setOf_eq] at hbad ⊢
  by_contra hsmall
  have hlarge : 2 * ‖s‖ ≤ ‖(rho : ℂ)‖ := le_of_not_gt hsmall
  have hle := zeroSquareTail_shift_le_four_zero (s := s) (rho := rho) hlarge
  have hnorm : ‖zeroSquareTail s rho‖ = zeroSquareTail s rho := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hbad (by simpa [hnorm] using hle)

/-- Above height one, the norm-square tail is bounded by the height-square tail. -/
lemma zeroSquareTail_le_imagSquareTail_of_large_im {rho : NontrivialZeros}
    (hlarge : 1 ≤ |(rho : ℂ).im|) :
    zeroSquareTail 0 rho ≤ zeroImagSquareTail rho := by
  have him_pos : 0 < |(rho : ℂ).im| := lt_of_lt_of_le zero_lt_one hlarge
  have hinv : ‖(rho : ℂ)‖⁻¹ ≤ |(rho : ℂ).im|⁻¹ :=
    inv_anti₀ him_pos (Complex.abs_im_le_norm (rho : ℂ))
  have hinv_nonneg : 0 ≤ ‖(rho : ℂ)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hpow := pow_le_pow_left₀ hinv_nonneg hinv 2
  unfold zeroSquareTail zeroImagSquareTail
  rw [zero_sub, norm_neg]
  exact hpow

/-- The unshifted norm-square zero tail follows from the height-square zero tail. -/
theorem zeroSquareTailSummable_of_imag_tail
    (him : zeroImagSquareTailSummable) :
    zeroSquareTailSummable 0 := by
  unfold zeroImagSquareTailSummable at him
  unfold zeroSquareTailSummable
  refine Summable.of_norm_bounded_eventually him ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset nontrivialZeros_abs_im_lt_one_finite
  intro rho hbad
  rw [Set.mem_setOf_eq] at hbad ⊢
  by_contra hsmall
  have hlarge : 1 ≤ |(rho : ℂ).im| := le_of_not_gt hsmall
  have hle := zeroSquareTail_le_imagSquareTail_of_large_im (rho := rho) hlarge
  have hnorm : ‖zeroSquareTail 0 rho‖ = zeroSquareTail 0 rho := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hbad (by simpa [hnorm] using hle)

/-- Dyadic-shell height mass is nonnegative. -/
lemma zeroHeightDyadicShellMass_nonneg (k : ℕ) :
    0 ≤ zeroHeightDyadicShellMass k := by
  unfold zeroHeightDyadicShellMass
  exact tsum_nonneg fun rho => sq_nonneg _

/-- Inside dyadic shell `k`, each height-square term is bounded by `2^(-2k)`. -/
lemma zeroImagSquareTail_le_dyadic_inv_sq {k : ℕ} {rho : NontrivialZeros}
    (hrho : zeroHeightDyadicShell k rho) :
    zeroImagSquareTail rho ≤ (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
  unfold zeroImagSquareTail
  have hpow_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hinv : |(rho : ℂ).im|⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := inv_anti₀ hpow_pos hrho.1
  have hinv_nonneg : 0 ≤ |(rho : ℂ).im|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  exact pow_le_pow_left₀ hinv_nonneg hinv 2

/-- Dyadic-shell mass is bounded by shell cardinality times `2^(-2k)`. -/
lemma zeroHeightDyadicShellMass_le_count_inv_sq (k : ℕ) :
    zeroHeightDyadicShellMass k ≤
      (Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} : ℝ) *
        (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
  classical
  haveI : Finite {rho : NontrivialZeros // zeroHeightDyadicShell k rho} :=
    Set.finite_coe_iff.mpr (nontrivialZeros_dyadic_shell_finite k)
  letI := Fintype.ofFinite {rho : NontrivialZeros // zeroHeightDyadicShell k rho}
  unfold zeroHeightDyadicShellMass
  rw [tsum_fintype]
  calc
    (∑ rho : {rho : NontrivialZeros // zeroHeightDyadicShell k rho},
        zeroImagSquareTail rho.1)
        ≤ ∑ _rho : {rho : NontrivialZeros // zeroHeightDyadicShell k rho},
            (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
          exact Finset.sum_le_sum fun rho _ =>
            zeroImagSquareTail_le_dyadic_inv_sq rho.2
    _ = (Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} : ℝ) *
          (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
          simp [Nat.card_eq_fintype_card]

/-- A dyadic shell has no more zeros than the cumulative set below its top edge. -/
lemma zeroHeightDyadicShellCount_le_cumulative_count (k : ℕ) :
    Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} ≤
      Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} := by
  classical
  haveI : Finite {rho : NontrivialZeros //
      |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} :=
    Set.finite_coe_iff.mpr
      (nontrivialZeros_abs_im_lt_finite ((2 : ℝ) ^ (k + 1)))
  exact Nat.card_le_card_of_injective (dyadicShellToCumulative k)
    (dyadicShellToCumulative_injective k)

/-- Any RvM estimate gives an absolute-value bound for `N(T)`. -/
theorem zetaCounting_abs_N_le_backlund_majorant {b₁ b₂ b₃ T : ℝ}
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) (hT : 2 ≤ T) :
    |riemannZeta.N T| ≤ zetaCountingBacklundMajorant b₁ b₂ b₃ T := by
  have hbound := hRvM T hT
  unfold zetaCountingBacklundMajorant zetaCountingMainTerm
  calc
    |riemannZeta.N T|
        = |(riemannZeta.N T -
              (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
                T / (2 * Real.pi) + 7 / 8)) +
              (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
                T / (2 * Real.pi) + 7 / 8)| := by
          ring_nf
    _ ≤ |riemannZeta.N T -
              (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
                T / (2 * Real.pi) + 7 / 8)| +
          |T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
                T / (2 * Real.pi) + 7 / 8| := by
          exact abs_add_le _ _
    _ ≤ riemannZeta.RvM b₁ b₂ b₃ T +
          |T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
                T / (2 * Real.pi) + 7 / 8| := by
          exact add_le_add_left hbound _
    _ = |T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
                T / (2 * Real.pi) + 7 / 8| + riemannZeta.RvM b₁ b₂ b₃ T := by
          ring

/-- An RvM estimate with Backlund's constants gives the dyadic `N(T)` bound by the
explicit majorant. -/
theorem zetaCountingDyadic_abs_N_le_backlund_majorant
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1) (k : ℕ) :
    |riemannZeta.N ((2 : ℝ) ^ (k + 1))| ≤
      zetaCountingDyadicMajorant 0.137 0.443 6.1 k := by
  have hk : (1 : ℕ) ≤ k + 1 := by omega
  have hT : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    have hpow : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by exact_mod_cast hk)
    norm_num at hpow
    exact hpow
  exact zetaCounting_abs_N_le_backlund_majorant hRvM hT

/-- The dyadic scale `(k+1) 2^k` is at least one. -/
lemma dyadicCountScale_ge_one (k : ℕ) :
    (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos k
  have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [mul_le_mul hk1 hp1 (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))]

/-- The logarithm of a dyadic height is bounded by the dyadic count scale. -/
lemma log_dyadic_le_count_scale (k : ℕ) :
    Real.log ((2 : ℝ) ^ (k + 1)) ≤
      ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hk_nonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hlog_le_k :
      ((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hlog2_le_one hk_nonneg
  have hk_le_target :
      ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
    simpa using mul_le_mul_of_nonneg_left hpow1 hk_nonneg
  calc
    Real.log ((2 : ℝ) ^ (k + 1))
        = ((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) := by
          rw [Real.log_pow]
    _ ≤ ((k + 1 : ℕ) : ℝ) := hlog_le_k
    _ ≤ ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := hk_le_target

/-- The logarithm of a dyadic height is bounded by its dyadic exponent. -/
lemma log_dyadic_le_nat_succ (k : ℕ) :
    Real.log ((2 : ℝ) ^ (k + 1)) ≤ ((k + 1 : ℕ) : ℝ) := by
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hk_nonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  calc
    Real.log ((2 : ℝ) ^ (k + 1))
        = ((k + 1 : ℕ) : ℝ) * Real.log (2 : ℝ) := by
          rw [Real.log_pow]
    _ ≤ ((k + 1 : ℕ) : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left hlog2_le_one hk_nonneg
    _ = ((k + 1 : ℕ) : ℝ) := by ring

/-- Absolute size of the dyadic main-term denominator factor. -/
lemma dyadic_div_two_pi_abs_eq (k : ℕ) :
    |((2 : ℝ) ^ (k + 1)) / (2 * Real.pi)| =
      (2 * |(2 * Real.pi)⁻¹|) * (2 : ℝ) ^ k := by
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (k + 1) := pow_nonneg (by norm_num) _
  rw [div_eq_mul_inv, abs_mul, abs_of_nonneg hpow_nonneg, pow_succ']
  ring

/-- Log size of the dyadic main-term denominator factor. -/
lemma abs_log_dyadic_div_two_pi_le (k : ℕ) :
    |Real.log (((2 : ℝ) ^ (k + 1)) / (2 * Real.pi))| ≤
      (1 + |Real.log (2 * Real.pi)|) * ((k + 1 : ℕ) : ℝ) := by
  have hT_pos : 0 < (2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  have hden_pos : 0 < 2 * Real.pi := by positivity
  have hTge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hlog_nonneg : 0 ≤ Real.log ((2 : ℝ) ^ (k + 1)) :=
    Real.log_nonneg hTge1
  have hlog_le : Real.log ((2 : ℝ) ^ (k + 1)) ≤ ((k + 1 : ℕ) : ℝ) :=
    log_dyadic_le_nat_succ k
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos k
  have hL_nonneg : 0 ≤ |Real.log (2 * Real.pi)| := abs_nonneg _
  rw [Real.log_div hT_pos.ne' hden_pos.ne']
  calc
    |Real.log ((2 : ℝ) ^ (k + 1)) - Real.log (2 * Real.pi)|
        ≤ |Real.log ((2 : ℝ) ^ (k + 1))| + |Real.log (2 * Real.pi)| :=
          abs_sub _ _
    _ = Real.log ((2 : ℝ) ^ (k + 1)) + |Real.log (2 * Real.pi)| := by
          rw [abs_of_nonneg hlog_nonneg]
    _ ≤ ((k + 1 : ℕ) : ℝ) + |Real.log (2 * Real.pi)| := by
          exact add_le_add_left hlog_le _
    _ ≤ (1 + |Real.log (2 * Real.pi)|) * ((k + 1 : ℕ) : ℝ) := by
          nlinarith

/-- Triangle bound for the RvM main term after writing `A = T/(2*pi)`. -/
lemma abs_zetaCountingMainTerm_core_le (A : ℝ) :
    |A * Real.log A - A + 7 / 8| ≤
      |A * Real.log A| + |A| + (1 : ℝ) := by
  have hconst : |(7 / 8 : ℝ)| ≤ (1 : ℝ) := by norm_num
  calc
    |A * Real.log A - A + 7 / 8|
        = |(A * Real.log A - A) + (7 / 8 : ℝ)| := by ring_nf
    _ ≤ |A * Real.log A - A| + |(7 / 8 : ℝ)| := abs_add_le _ _
    _ ≤ (|A * Real.log A| + |A|) + |(7 / 8 : ℝ)| := by
          exact add_le_add_left (abs_sub _ _) _
    _ ≤ (|A * Real.log A| + |A|) + 1 := by
          exact add_le_add_right hconst _
    _ = |A * Real.log A| + |A| + 1 := by ring

/-- The RvM main term has the dyadic growth needed by the zero-tail route. -/
theorem zetaCountingMainTermDyadicGrowthSource_of_elementary :
    zetaCountingMainTermDyadicGrowthSource := by
  let B : ℝ := 2 * |(2 * Real.pi)⁻¹|
  let L : ℝ := |Real.log (2 * Real.pi)|
  refine ⟨B * (1 + L) + B + 1, by positivity, ?_⟩
  intro k
  let scale : ℝ := ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
  let A : ℝ := ((2 : ℝ) ^ (k + 1)) / (2 * Real.pi)
  have hscale_ge_one : (1 : ℝ) ≤ scale := dyadicCountScale_ge_one k
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ k := pow_nonneg (by norm_num) _
  have hpow_le_scale : (2 : ℝ) ^ k ≤ scale := by
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos k
    nlinarith
  have hB_nonneg : 0 ≤ B := by positivity
  have hA_abs_eq : |A| = B * (2 : ℝ) ^ k := by
    dsimp [A, B]
    exact dyadic_div_two_pi_abs_eq k
  have hA_abs_le_scale : |A| ≤ B * scale := by
    calc
      |A| = B * (2 : ℝ) ^ k := hA_abs_eq
      _ ≤ B * scale := mul_le_mul_of_nonneg_left hpow_le_scale hB_nonneg
  have hlog_abs_le : |Real.log A| ≤ (1 + L) * ((k + 1 : ℕ) : ℝ) := by
    dsimp [A, L]
    exact abs_log_dyadic_div_two_pi_le k
  have hprod_le : |A * Real.log A| ≤ B * (1 + L) * scale := by
    rw [abs_mul]
    have hmul := mul_le_mul (show |A| ≤ B * (2 : ℝ) ^ k from hA_abs_eq.le)
      hlog_abs_le (abs_nonneg _) (mul_nonneg hB_nonneg hpow_nonneg)
    calc
      |A| * |Real.log A| ≤
          (B * (2 : ℝ) ^ k) * ((1 + L) * ((k + 1 : ℕ) : ℝ)) := hmul
      _ = B * (1 + L) * scale := by ring
  have htri := abs_zetaCountingMainTerm_core_le A
  unfold zetaCountingMainTerm
  dsimp [A] at htri hA_abs_le_scale hprod_le
  calc
    |(2 ^ (k + 1)) / (2 * Real.pi) *
          Real.log ((2 ^ (k + 1)) / (2 * Real.pi)) -
        (2 ^ (k + 1)) / (2 * Real.pi) + 7 / 8|
        ≤ |(2 ^ (k + 1)) / (2 * Real.pi) *
            Real.log ((2 ^ (k + 1)) / (2 * Real.pi))| +
          |(2 ^ (k + 1)) / (2 * Real.pi)| + 1 := htri
    _ ≤ B * (1 + L) * scale + B * scale + 1 := by
          exact add_le_add (add_le_add hprod_le hA_abs_le_scale) le_rfl
    _ ≤ B * (1 + L) * scale + B * scale + scale := by
          exact add_le_add_right hscale_ge_one _
    _ = (B * (1 + L) + B + 1) * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
          dsimp [scale]
          ring

/-- The RvM error term has the dyadic growth needed by the zero-tail route. -/
theorem zetaCountingRvM_dyadic_le (k : ℕ) :
    riemannZeta.RvM 0.137 0.443 6.1 ((2 : ℝ) ^ (k + 1)) ≤
      7 * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
  let target : ℝ := ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
  have htarget_ge_one : (1 : ℝ) ≤ target := dyadicCountScale_ge_one k
  have hlog_le : Real.log ((2 : ℝ) ^ (k + 1)) ≤ target :=
    log_dyadic_le_count_scale k
  have hTge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hlog_nonneg : 0 ≤ Real.log ((2 : ℝ) ^ (k + 1)) :=
    Real.log_nonneg hTge1
  have hloglog_le : Real.log (Real.log ((2 : ℝ) ^ (k + 1))) ≤ target := by
    exact (Real.log_le_self hlog_nonneg).trans hlog_le
  unfold riemannZeta.RvM
  nlinarith

/-- Main-term dyadic growth gives growth of the full Backlund majorant. -/
theorem zetaCountingDyadicMajorantGrowthSource_of_main_term_growth
    (hmain : zetaCountingMainTermDyadicGrowthSource) :
    zetaCountingDyadicMajorantGrowthSource := by
  rcases hmain with ⟨C, hC_nonneg, hmain⟩
  refine ⟨C + 7, by nlinarith, ?_⟩
  intro k
  have hmaink := hmain k
  have hrvm := zetaCountingRvM_dyadic_le k
  unfold zetaCountingDyadicMajorant zetaCountingBacklundMajorant
  calc
    |zetaCountingMainTerm ((2 : ℝ) ^ (k + 1))| +
        riemannZeta.RvM 0.137 0.443 6.1 ((2 : ℝ) ^ (k + 1))
        ≤ C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) +
          7 * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
          exact add_le_add hmaink hrvm
    _ = (C + 7) * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by ring

/-- The shifted `n^(-3/2)` majorant is summable. -/
theorem summable_rpow_three_halves_shift (C : ℝ) :
    Summable (fun n : ℕ =>
      C * (((n + 3 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := by
  have hp : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := by
    exact Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ =>
      (((n + 3 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := by
    exact (summable_nat_add_iff 3).mpr hp
  exact hshift.mul_left C

/-- A linear term times `2^(-k)` is summable. -/
theorem summable_linear_geometric_inv_two (C : ℝ) :
    Summable (fun k : ℕ => C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ k) := by
  have hgeom : Summable (fun k : ℕ =>
      ((k : ℝ) ^ (1 : ℕ)) * ((2 : ℝ)⁻¹) ^ k) := by
    exact summable_pow_mul_geometric_of_norm_lt_one 1
      (by norm_num : ‖((2 : ℝ)⁻¹)‖ < 1)
  have hgeom0 : Summable (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) := by
    exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hsum : Summable (fun k : ℕ =>
      (((k : ℝ) ^ (1 : ℕ)) + 1) * ((2 : ℝ)⁻¹) ^ k) := by
    simpa [add_mul] using hgeom.add hgeom0
  have hsum' : Summable (fun k : ℕ =>
      ((k + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ k) := by
    simpa using hsum
  simpa [mul_assoc] using hsum'.mul_left C

/-- A dyadic mass bound gives dyadic-shell height summability. -/
theorem zeroImagDyadicShellSummableSource_of_mass_bound
    (hsrc : zeroImagDyadicShellMassBoundSource) :
    zeroImagDyadicShellSummableSource := by
  rcases hsrc with ⟨C, _hC, hbound⟩
  unfold zeroImagDyadicShellSummableSource
  rw [summable_sigma_of_nonneg]
  · constructor
    · intro k
      haveI : Finite {rho : NontrivialZeros // zeroHeightDyadicShell k rho} :=
        Set.finite_coe_iff.mpr (nontrivialZeros_dyadic_shell_finite k)
      exact Summable.of_finite
    · exact Summable.of_nonneg_of_le
        (fun k => zeroHeightDyadicShellMass_nonneg k) hbound
        (summable_linear_geometric_inv_two C)
  · intro p
    exact sq_nonneg _

/-- A cumulative dyadic count source gives the dyadic shell-count source. -/
theorem zeroImagDyadicShellCountBoundSource_of_cumulative_count_bound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    zeroImagDyadicShellCountBoundSource := by
  rcases hsrc with ⟨C, hC_nonneg, hcount⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro k
  have hcard_nat := zeroHeightDyadicShellCount_le_cumulative_count k
  have hcard :
      (Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} : ℝ) ≤
        (Nat.card {rho : NontrivialZeros //
          |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) := by
    exact_mod_cast hcard_nat
  exact hcard.trans (hcount k)

/--
The remaining `N(T)` count source splits into two counting inputs once the
finite-strip multiplicity comparison is proved: absolute-height reduction to
positive-height zeros, and comparison of `N' 0 T` to the project `N(T)`.
-/
theorem zeroImagDyadicCumulativeCountByNSource_of_positive_bridge
    (habs : zeroImagDyadicAbsToPositiveCountSource)
    (hNprime : zeroImagDyadicNPrimeToNSource) :
    zeroImagDyadicCumulativeCountByNSource := by
  rcases habs with ⟨A, hA_nonneg, habs⟩
  rcases hNprime with ⟨B, hB_nonneg, hNprime⟩
  refine ⟨A * B, mul_nonneg hA_nonneg hB_nonneg, ?_⟩
  intro k
  let T : ℝ := (2 : ℝ) ^ (k + 1)
  have hpositive :=
    positive_height_nontrivial_zero_count_le_NPrime T
  have hpositive_nonneg :
      0 ≤ (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} : ℝ) := by
    exact_mod_cast Nat.zero_le
      (Nat.card {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < T})
  have hNprime_nonneg : 0 ≤ riemannZeta.N' 0 T :=
    hpositive_nonneg.trans hpositive
  have hpositive_abs :
      (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} : ℝ) ≤
        |riemannZeta.N' 0 T| := by
    rw [abs_of_nonneg hNprime_nonneg]
    exact hpositive
  have habsk := habs k
  have hstep1 :
      (Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < T} : ℝ) ≤
        A * |riemannZeta.N' 0 T| := by
    exact habsk.trans (mul_le_mul_of_nonneg_left hpositive_abs hA_nonneg)
  have hstep2 :
      A * |riemannZeta.N' 0 T| ≤
        A * (B * |riemannZeta.N T|) := by
    dsimp [T]
    exact mul_le_mul_of_nonneg_left (hNprime k) hA_nonneg
  calc
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ)
        ≤ A * |riemannZeta.N' 0 T| := by
          dsimp [T] at hstep1
          exact hstep1
    _ ≤ A * (B * |riemannZeta.N T|) := hstep2
    _ = A * B * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| := by
          dsimp [T]
          ring

/--
The same bridge with the finite zero-height bucket preserved as an additive
constant.
-/
theorem zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_positive_bridge
    (habs : zeroImagDyadicAbsToPositiveCountWithZeroHeightSource)
    (hNprime : zeroImagDyadicNPrimeToNSource) :
    zeroImagDyadicCumulativeCountByNWithZeroHeightSource := by
  rcases habs with ⟨A, D, hA_nonneg, hD_nonneg, habs⟩
  rcases hNprime with ⟨B, hB_nonneg, hNprime⟩
  refine ⟨A * B, D, mul_nonneg hA_nonneg hB_nonneg, hD_nonneg, ?_⟩
  intro k
  let T : ℝ := (2 : ℝ) ^ (k + 1)
  have hpositive :=
    positive_height_nontrivial_zero_count_le_NPrime T
  have hpositive_nonneg :
      0 ≤ (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} : ℝ) := by
    exact_mod_cast Nat.zero_le
      (Nat.card {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < T})
  have hNprime_nonneg : 0 ≤ riemannZeta.N' 0 T :=
    hpositive_nonneg.trans hpositive
  have hpositive_abs :
      (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} : ℝ) ≤
        |riemannZeta.N' 0 T| := by
    rw [abs_of_nonneg hNprime_nonneg]
    exact hpositive
  have habsk := habs k
  have hstep1 :
      (Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < T} : ℝ) ≤
        A * |riemannZeta.N' 0 T| + D := by
    have habskT :
        (Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < T} : ℝ) ≤
          A * (Nat.card {rho : NontrivialZeros //
            0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} : ℝ) + D := by
      dsimp [T]
      exact habsk
    have hmul :=
      mul_le_mul_of_nonneg_left hpositive_abs hA_nonneg
    calc
      (Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < T} : ℝ)
          ≤ A * (Nat.card {rho : NontrivialZeros //
            0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} : ℝ) + D := habskT
      _ ≤ A * |riemannZeta.N' 0 T| + D := add_le_add_left hmul D
  have hstep2 :
      A * |riemannZeta.N' 0 T| + D ≤
        A * (B * |riemannZeta.N T|) + D := by
    have hNprimeT : |riemannZeta.N' 0 T| ≤ B * |riemannZeta.N T| := by
      dsimp [T]
      exact hNprime k
    have hmul :=
      mul_le_mul_of_nonneg_left hNprimeT hA_nonneg
    exact add_le_add_left hmul D
  calc
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ)
        ≤ A * |riemannZeta.N' 0 T| + D := by
          dsimp [T] at hstep1
          exact hstep1
    _ ≤ A * (B * |riemannZeta.N T|) + D := hstep2
    _ = A * B * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D := by
          dsimp [T]
          ring

/--
Conjugation symmetry reduces absolute-height counts to two positive-height
buckets plus the finite zero-height bucket.
-/
theorem zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_conj
    (hconj : riemannZetaConjZeroSource) :
    zeroImagDyadicAbsToPositiveCountWithZeroHeightSource := by
  classical
  refine ⟨2, (Nat.card ZeroHeightNontrivialZeros : ℝ), by norm_num, ?_, ?_⟩
  · exact_mod_cast Nat.zero_le (Nat.card ZeroHeightNontrivialZeros)
  intro k
  let T : ℝ := (2 : ℝ) ^ (k + 1)
  have hT_pos : 0 < T := by
    exact pow_pos (by norm_num) _
  let Abs := {rho : NontrivialZeros // |(rho : ℂ).im| < T}
  let Pos := {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < T}
  let Z := ZeroHeightNontrivialZeros
  haveI : Finite Pos := by
    haveI : Finite (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo 0 T)) :=
      Set.finite_coe_iff.mpr (zeroes_rect_Ioo_critical_positive_height_finite T)
    exact Finite.of_equiv _ (positiveHeightNontrivialZeroEquivZeroesRect T).symm
  haveI : Finite Z := zeroHeightNontrivialZeros_finite
  let toBucket : Abs → ((Pos ⊕ Pos) ⊕ Z) := fun rho =>
    if hpos : 0 < (rho.1 : ℂ).im then
      Sum.inl (Sum.inl
        ⟨rho.1,
          by
            constructor
            · exact hpos
            · have hlt := rho.2
              rwa [abs_of_pos hpos] at hlt⟩)
    else if hzero : (rho.1 : ℂ).im = 0 then
      Sum.inr ⟨rho.1, hzero⟩
    else
      have hle : (rho.1 : ℂ).im ≤ 0 := le_of_not_gt hpos
      have hneg : (rho.1 : ℂ).im < 0 := lt_of_le_of_ne hle hzero
      Sum.inl (Sum.inr
        ⟨⟨((starRingEnd ℂ) (rho.1 : ℂ)),
            by simpa [Complex.conj_re] using rho.1.property.1,
            Set.mem_univ _,
            by exact hconj (rho.1 : ℂ) rho.1.property.2.2⟩,
          by
            constructor
            · rw [Complex.conj_im]
              exact neg_pos.mpr hneg
            · rw [Complex.conj_im]
              simpa [abs_of_neg hneg] using rho.2⟩)
  let recover : ((Pos ⊕ Pos) ⊕ Z) → NontrivialZeros := fun bucket =>
    match bucket with
    | Sum.inl (Sum.inl rho) => rho.1
    | Sum.inl (Sum.inr rho) =>
        ⟨((starRingEnd ℂ) (rho.1 : ℂ)),
          by simpa [Complex.conj_re] using rho.1.property.1,
          Set.mem_univ _,
          by exact hconj (rho.1 : ℂ) rho.1.property.2.2⟩
    | Sum.inr rho => rho.1
  have hrecover : ∀ rho : Abs, recover (toBucket rho) = rho.1 := by
    intro rho
    by_cases hpos : 0 < (rho.1 : ℂ).im
    · simp [toBucket, recover, hpos]
    · by_cases hzero : (rho.1 : ℂ).im = 0
      · simp [toBucket, recover, hzero]
      · simp [toBucket, recover, hpos, hzero]
  have hinj : Function.Injective toBucket := by
    intro rho eta h
    apply Subtype.ext
    calc
      rho.1 = recover (toBucket rho) := (hrecover rho).symm
      _ = recover (toBucket eta) := by rw [h]
      _ = eta.1 := hrecover eta
  have hcard_nat :
      Nat.card Abs ≤ Nat.card ((Pos ⊕ Pos) ⊕ Z) :=
    Nat.card_le_card_of_injective toBucket hinj
  have hcard_real :
      (Nat.card Abs : ℝ) ≤ (Nat.card ((Pos ⊕ Pos) ⊕ Z) : ℝ) := by
    exact_mod_cast hcard_nat
  have htarget :
      (Nat.card ((Pos ⊕ Pos) ⊕ Z) : ℝ) =
        2 * (Nat.card Pos : ℝ) + (Nat.card Z : ℝ) := by
    rw [Nat.card_sum, Nat.card_sum]
    norm_num [Nat.cast_add]
    ring
  calc
    (Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ)
        = (Nat.card Abs : ℝ) := by rfl
    _ ≤ (Nat.card ((Pos ⊕ Pos) ⊕ Z) : ℝ) := hcard_real
    _ = 2 * (Nat.card Pos : ℝ) + (Nat.card Z : ℝ) := htarget
    _ = 2 * (Nat.card {rho : NontrivialZeros //
          0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ) +
        (Nat.card ZeroHeightNontrivialZeros : ℝ) := by
          rfl

theorem zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_riemannZeta_conj :
    zeroImagDyadicAbsToPositiveCountWithZeroHeightSource :=
  zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_conj
    riemannZetaConjZeroSource_of_riemannZeta_conj

/--
The `N' 0 T` comparison with `N(T)` is sum monotonicity over the rectangle
inclusion, once the larger positive-height `N(T)` series is known summable.
-/
theorem zeroImagDyadicNPrimeToNSource_of_order_summable
    (hsum : zeroImagDyadicNOrderSummableSource) :
    zeroImagDyadicNPrimeToNSource := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro k
  let T : ℝ := (2 : ℝ) ^ (k + 1)
  let Crit := riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo 0 T)
  let All := riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)
  have hcrit_finite : Finite Crit := by
    exact Set.finite_coe_iff.mpr (zeroes_rect_Ioo_critical_positive_height_finite T)
  letI : Fintype Crit := Fintype.ofFinite Crit
  let inc : Crit ↪ All := {
    toFun := fun rho =>
      ⟨(rho : ℂ), Set.mem_univ _, rho.property.2.1, rho.property.2.2⟩
    inj' := fun rho eta h => by
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
  }
  let fAll : All → ℝ := fun rho => (riemannZeta.order (rho : ℂ) : ℝ)
  have hsumAll : Summable fAll := by
    dsimp [fAll, All, T]
    simpa [T] using hsum k
  have hnonnegAll : ∀ rho : All, 0 ≤ fAll rho := by
    intro rho
    have horder : (0 : ℤ) ≤ riemannZeta.order (rho : ℂ) := by
      exact le_of_lt (riemannZeta_order_pos_positiveHeightZero rho)
    change 0 ≤ ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ)
    exact_mod_cast horder
  have hNprime_eq :
      riemannZeta.N' 0 T =
        ∑ rho : Crit, (riemannZeta.order (rho : ℂ) : ℝ) := by
    unfold riemannZeta.N' riemannZeta.zeroes_sum
    rw [tsum_fintype]
    simp [Crit]
  have hN_eq :
      riemannZeta.N T = ∑' rho : All, fAll rho := by
    unfold riemannZeta.N riemannZeta.zeroes_sum
    simp [All, fAll]
  have hpartial :
      (∑ rho : Crit, (riemannZeta.order (rho : ℂ) : ℝ)) ≤
        ∑' rho : All, fAll rho := by
    have hmap :
        (∑ rho : Crit, (riemannZeta.order (rho : ℂ) : ℝ)) =
          ∑ rho ∈ Finset.univ.map inc, fAll rho := by
      simp [inc, fAll]
    rw [hmap]
    exact Summable.sum_le_tsum (Finset.univ.map inc)
      (fun rho _ => hnonnegAll rho) hsumAll
  have hNprime_nonneg : 0 ≤ riemannZeta.N' 0 T := by
    rw [hNprime_eq]
    exact Finset.sum_nonneg fun rho _ => by
      have horder : (0 : ℤ) ≤ riemannZeta.order (rho : ℂ) := by
        exact le_of_lt (riemannZeta_order_pos_positiveHeightZero (inc rho))
      change 0 ≤ ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ)
      exact_mod_cast horder
  have hN_nonneg : 0 ≤ riemannZeta.N T := by
    rw [hN_eq]
    exact tsum_nonneg hnonnegAll
  have hNprime_le_N : riemannZeta.N' 0 T ≤ riemannZeta.N T := by
    rw [hNprime_eq, hN_eq]
    exact hpartial
  calc
    |riemannZeta.N' 0 ((2 : ℝ) ^ (k + 1))| = riemannZeta.N' 0 T := by
      dsimp [T]
      exact abs_of_nonneg hNprime_nonneg
    _ ≤ riemannZeta.N T := hNprime_le_N
    _ = |riemannZeta.N T| := (abs_of_nonneg hN_nonneg).symm
    _ = 1 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| := by
      dsimp [T]
      ring

/--
Conjugation plus positive-height `N(T)` order summability gives the honest
count-by-`N(T)` source with the zero-height bucket kept additive.
-/
theorem zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_order_summable
    (hsum : zeroImagDyadicNOrderSummableSource) :
    zeroImagDyadicCumulativeCountByNWithZeroHeightSource :=
  zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_positive_bridge
    zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_riemannZeta_conj
    (zeroImagDyadicNPrimeToNSource_of_order_summable hsum)

theorem zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_positive_height_zero_free :
    zeroImagDyadicCumulativeCountByNWithZeroHeightSource :=
  zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_order_summable
    zeroImagDyadicNOrderSummableSource_of_positive_height_zero_free

/--
The cumulative dyadic count source follows from a comparison with `N(T)` and
dyadic growth of the explicit Backlund majorant.
-/
theorem zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_and_backlund_growth
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNSource)
    (hgrowth : zetaCountingDyadicMajorantGrowthSource) :
    zeroImagDyadicCumulativeCountBoundSource := by
  rcases hcountN with ⟨A, hA_nonneg, hcountN⟩
  rcases hgrowth with ⟨C, hC_nonneg, hgrowth⟩
  refine ⟨A * C, mul_nonneg hA_nonneg hC_nonneg, ?_⟩
  intro k
  have hN := zetaCountingDyadic_abs_N_le_backlund_majorant hRvM k
  have hto_majorant :
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| ≤
        A * zetaCountingDyadicMajorant 0.137 0.443 6.1 k := by
    exact mul_le_mul_of_nonneg_left hN hA_nonneg
  have hto_growth :
      A * zetaCountingDyadicMajorant 0.137 0.443 6.1 k ≤
        A * (C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)) := by
    exact mul_le_mul_of_nonneg_left (hgrowth k) hA_nonneg
  calc
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ)
        ≤ A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| := hcountN k
    _ ≤ A * zetaCountingDyadicMajorant 0.137 0.443 6.1 k := hto_majorant
    _ ≤ A * (C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)) := hto_growth
    _ = A * C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by ring

/--
The additive zero-height bucket is harmless for the dyadic growth source,
because `(k+1) * 2^k ≥ 1` for all dyadic shells.
-/
theorem zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height_and_backlund_growth
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNWithZeroHeightSource)
    (hgrowth : zetaCountingDyadicMajorantGrowthSource) :
    zeroImagDyadicCumulativeCountBoundSource := by
  rcases hcountN with ⟨A, D, hA_nonneg, hD_nonneg, hcountN⟩
  rcases hgrowth with ⟨C, hC_nonneg, hgrowth⟩
  refine ⟨A * C + D, add_nonneg (mul_nonneg hA_nonneg hC_nonneg) hD_nonneg, ?_⟩
  intro k
  let G : ℝ := ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
  have hN := zetaCountingDyadic_abs_N_le_backlund_majorant hRvM k
  have hto_majorant :
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D ≤
        A * zetaCountingDyadicMajorant 0.137 0.443 6.1 k + D := by
    exact add_le_add_left (mul_le_mul_of_nonneg_left hN hA_nonneg) D
  have hto_growth :
      A * zetaCountingDyadicMajorant 0.137 0.443 6.1 k + D ≤
        A * (C * G) + D := by
    have hgrowthk :
        zetaCountingDyadicMajorant 0.137 0.443 6.1 k ≤ C * G := by
      dsimp [G]
      calc
        zetaCountingDyadicMajorant 0.137 0.443 6.1 k
            ≤ C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := hgrowth k
        _ = C * (((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)) := by ring
    exact add_le_add_left (mul_le_mul_of_nonneg_left hgrowthk hA_nonneg) D
  have hk_one : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hpow_one : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hG_one : (1 : ℝ) ≤ G := by
    dsimp [G]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) :=
          mul_le_mul hk_one hpow_one (by norm_num) (le_trans (by norm_num) hk_one)
  have hD_absorb : D ≤ D * G := by
    calc
      D = D * 1 := by ring
      _ ≤ D * G := mul_le_mul_of_nonneg_left hG_one hD_nonneg
  calc
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ)
        ≤ A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D := hcountN k
    _ ≤ A * zetaCountingDyadicMajorant 0.137 0.443 6.1 k + D := hto_majorant
    _ ≤ A * (C * G) + D := hto_growth
    _ ≤ A * (C * G) + D * G := add_le_add_right hD_absorb (A * (C * G))
    _ = (A * C + D) * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
          dsimp [G]
          ring

/--
The cumulative dyadic count source follows from count by `N(T)` plus dyadic
growth of the RvM main term; the RvM error term is already bounded above.
-/
theorem zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_and_main_term_growth
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNSource)
    (hmain : zetaCountingMainTermDyadicGrowthSource) :
    zeroImagDyadicCumulativeCountBoundSource :=
  zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_and_backlund_growth
    hRvM hcountN (zetaCountingDyadicMajorantGrowthSource_of_main_term_growth hmain)

/--
Additive zero-height version, with dyadic growth of the RvM main term as the
remaining explicit growth source.
-/
theorem zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height_and_main_term_growth
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNWithZeroHeightSource)
    (hmain : zetaCountingMainTermDyadicGrowthSource) :
    zeroImagDyadicCumulativeCountBoundSource :=
  zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height_and_backlund_growth
    hRvM hcountN (zetaCountingDyadicMajorantGrowthSource_of_main_term_growth hmain)

/-- A count comparison with `N(T)` gives the cumulative dyadic count source. -/
theorem zeroImagDyadicCumulativeCountBoundSource_of_count_by_N
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNSource) :
    zeroImagDyadicCumulativeCountBoundSource :=
  zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_and_main_term_growth
    hRvM hcountN zetaCountingMainTermDyadicGrowthSource_of_elementary

/-- Additive zero-height version of the count comparison with `N(T)`. -/
theorem zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNWithZeroHeightSource) :
    zeroImagDyadicCumulativeCountBoundSource :=
  zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height_and_main_term_growth
    hRvM hcountN zetaCountingMainTermDyadicGrowthSource_of_elementary

/-- A dyadic shell-count source gives the dyadic mass bound. -/
theorem zeroImagDyadicShellMassBoundSource_of_count_bound
    (hsrc : zeroImagDyadicShellCountBoundSource) :
    zeroImagDyadicShellMassBoundSource := by
  rcases hsrc with ⟨C, hC_nonneg, hcount⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro k
  have hmass := zeroHeightDyadicShellMass_le_count_inv_sq k
  have hcountk := hcount k
  have hsq_nonneg : 0 ≤ (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := sq_nonneg _
  have hmul :
      (Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} : ℝ) *
          (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) ≤
        (C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)) *
          (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_right hcountk hsq_nonneg
  have hpow_ne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hcancel :
      (C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)) *
          (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) =
        C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ k := by
    rw [← inv_pow]
    field_simp [hpow_ne]
    rw [mul_assoc, ← mul_pow]
    norm_num
  exact hmass.trans (hcancel ▸ hmul)

/-- A cumulative dyadic count source gives the dyadic mass bound. -/
theorem zeroImagDyadicShellMassBoundSource_of_cumulative_count_bound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    zeroImagDyadicShellMassBoundSource :=
  zeroImagDyadicShellMassBoundSource_of_count_bound
    (zeroImagDyadicShellCountBoundSource_of_cumulative_count_bound hsrc)

/-- A dyadic shell-count source gives dyadic-shell height summability. -/
theorem zeroImagDyadicShellSummableSource_of_count_bound
    (hsrc : zeroImagDyadicShellCountBoundSource) :
    zeroImagDyadicShellSummableSource :=
  zeroImagDyadicShellSummableSource_of_mass_bound
    (zeroImagDyadicShellMassBoundSource_of_count_bound hsrc)

/-- A cumulative dyadic count source gives dyadic-shell height summability. -/
theorem zeroImagDyadicShellSummableSource_of_cumulative_count_bound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    zeroImagDyadicShellSummableSource :=
  zeroImagDyadicShellSummableSource_of_count_bound
    (zeroImagDyadicShellCountBoundSource_of_cumulative_count_bound hsrc)

/-- Dyadic-shell height summability gives height-square zero-tail summability. -/
theorem zeroImagSquareTailSummable_of_dyadic_shell_source
    (hshell : zeroImagDyadicShellSummableSource) :
    zeroImagSquareTailSummable := by
  unfold zeroImagDyadicShellSummableSource at hshell
  have hhigh : Summable
      (fun rho : {rho : NontrivialZeros // 1 ≤ |(rho : ℂ).im|} =>
        zeroImagSquareTail rho.1) := by
    simpa [Function.comp_def, highZeroToDyadicShell] using
      hshell.comp_injective highZeroToDyadicShell_injective
  have hlow_set : ({rho : NontrivialZeros | ¬ 1 ≤ |(rho : ℂ).im|} :
      Set NontrivialZeros).Finite := by
    apply Set.Finite.subset nontrivialZeros_abs_im_lt_one_finite
    intro rho hrho
    rw [Set.mem_setOf_eq] at hrho ⊢
    exact lt_of_not_ge hrho
  haveI : Finite {rho : NontrivialZeros // ¬ 1 ≤ |(rho : ℂ).im|} :=
    Set.finite_coe_iff.mpr hlow_set
  have hlow : Summable
      (fun rho : {rho : NontrivialZeros // ¬ 1 ≤ |(rho : ℂ).im|} =>
        zeroImagSquareTail rho.1) := by
    exact Summable.of_finite
  unfold zeroImagSquareTailSummable
  exact (summable_subtype_and_compl
    (s := {rho : NontrivialZeros | 1 ≤ |(rho : ℂ).im|})).mp ⟨hhigh, hlow⟩

/-- A dyadic shell-count source gives height-square zero-tail summability. -/
theorem zeroImagSquareTailSummable_of_dyadic_count_bound
    (hsrc : zeroImagDyadicShellCountBoundSource) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_dyadic_shell_source
    (zeroImagDyadicShellSummableSource_of_count_bound hsrc)

/-- A cumulative dyadic count source gives height-square zero-tail summability. -/
theorem zeroImagSquareTailSummable_of_cumulative_dyadic_count_bound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_dyadic_count_bound
    (zeroImagDyadicShellCountBoundSource_of_cumulative_count_bound hsrc)

/--
Height-square zero-tail summability from the split Backlund route:
count by `N(T)` plus dyadic growth of the explicit Backlund majorant.
-/
theorem zeroImagSquareTailSummable_of_count_by_N_and_backlund_growth
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNSource)
    (hgrowth : zetaCountingDyadicMajorantGrowthSource) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_cumulative_dyadic_count_bound
    (zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_and_backlund_growth
      hRvM hcountN hgrowth)

/-- Height-square zero-tail summability from count by `N(T)` plus main-term growth. -/
theorem zeroImagSquareTailSummable_of_count_by_N_and_main_term_growth
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNSource)
    (hmain : zetaCountingMainTermDyadicGrowthSource) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_count_by_N_and_backlund_growth hRvM hcountN
    (zetaCountingDyadicMajorantGrowthSource_of_main_term_growth hmain)

/-- Height-square zero-tail summability from a count comparison with `N(T)`. -/
theorem zeroImagSquareTailSummable_of_count_by_N
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNSource) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_count_by_N_and_main_term_growth
    hRvM hcountN zetaCountingMainTermDyadicGrowthSource_of_elementary

/--
Height-square zero-tail summability from the additive zero-height count by
`N(T)` plus dyadic growth of the explicit Backlund majorant.
-/
theorem zeroImagSquareTailSummable_of_count_by_N_with_zero_height_and_backlund_growth
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNWithZeroHeightSource)
    (hgrowth : zetaCountingDyadicMajorantGrowthSource) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_cumulative_dyadic_count_bound
    (zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height_and_backlund_growth
      hRvM hcountN hgrowth)

/--
Height-square zero-tail summability from the additive zero-height count by
`N(T)` plus main-term growth.
-/
theorem zeroImagSquareTailSummable_of_count_by_N_with_zero_height_and_main_term_growth
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNWithZeroHeightSource)
    (hmain : zetaCountingMainTermDyadicGrowthSource) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_count_by_N_with_zero_height_and_backlund_growth
    hRvM hcountN (zetaCountingDyadicMajorantGrowthSource_of_main_term_growth hmain)

theorem zeroImagSquareTailSummable_of_count_by_N_with_zero_height
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    (hcountN : zeroImagDyadicCumulativeCountByNWithZeroHeightSource) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_count_by_N_with_zero_height_and_main_term_growth
    hRvM hcountN zetaCountingMainTermDyadicGrowthSource_of_elementary

/-!
### Shifted height tails
-/

/-- Away from finitely many low zeros, a shifted height-square tail is controlled by the
unshifted height-square tail. -/
lemma zeroImagSquareTail_shifted_le_four {s : ℂ} {rho : NontrivialZeros}
    (hlarge : 2 * |s.im| + 2 ≤ |(rho : ℂ).im|) :
    |(s - (rho : ℂ)).im|⁻¹ ^ (2 : ℕ) ≤ 4 * zeroImagSquareTail rho := by
  have hs_abs : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have him_pos : 0 < |(rho : ℂ).im| := by linarith
  have hhalf_pos : 0 < |(rho : ℂ).im| / 2 := by linarith
  have hlower : |(rho : ℂ).im| / 2 ≤ |(s - (rho : ℂ)).im| := by
    have hsub_im : (s - (rho : ℂ)).im = s.im - (rho : ℂ).im := Complex.sub_im s (rho : ℂ)
    have h1 : |(rho : ℂ).im| - |s.im| ≤ |s.im - (rho : ℂ).im| := by
      calc |(rho : ℂ).im| - |s.im| ≤ |(rho : ℂ).im - s.im| := abs_sub_abs_le_abs_sub _ _
        _ = |s.im - (rho : ℂ).im| := abs_sub_comm _ _
    rw [hsub_im]
    linarith
  have hinv : |(s - (rho : ℂ)).im|⁻¹ ≤ (|(rho : ℂ).im| / 2)⁻¹ :=
    inv_anti₀ hhalf_pos hlower
  have hinv_eq : (|(rho : ℂ).im| / 2)⁻¹ = 2 * |(rho : ℂ).im|⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  have hinv' : |(s - (rho : ℂ)).im|⁻¹ ≤ 2 * |(rho : ℂ).im|⁻¹ := by
    rw [← hinv_eq]
    exact hinv
  have hinv_nonneg : 0 ≤ |(s - (rho : ℂ)).im|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  unfold zeroImagSquareTail
  calc |(s - (rho : ℂ)).im|⁻¹ ^ (2 : ℕ)
      ≤ (2 * |(rho : ℂ).im|⁻¹) ^ (2 : ℕ) := pow_le_pow_left₀ hinv_nonneg hinv' 2
    _ = 4 * |(rho : ℂ).im|⁻¹ ^ (2 : ℕ) := by ring

/-- The shifted height-square tail is summable once the unshifted height-square tail is. -/
theorem summable_zeroImagSquareTail_shifted
    (him : zeroImagSquareTailSummable) (s : ℂ) :
    Summable (fun rho : NontrivialZeros ↦ |(s - (rho : ℂ)).im|⁻¹ ^ (2 : ℕ)) := by
  unfold zeroImagSquareTailSummable at him
  refine Summable.of_norm_bounded_eventually (him.mul_left 4) ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (nontrivialZeros_abs_im_lt_finite (2 * |s.im| + 2))
  intro rho hbad
  rw [Set.mem_setOf_eq] at hbad ⊢
  by_contra hsmall
  have hlarge : 2 * |s.im| + 2 ≤ |(rho : ℂ).im| := le_of_not_gt hsmall
  have hle := zeroImagSquareTail_shifted_le_four (s := s) (rho := rho) hlarge
  have hnorm : ‖|(s - (rho : ℂ)).im|⁻¹ ^ (2 : ℕ)‖ = |(s - (rho : ℂ)).im|⁻¹ ^ (2 : ℕ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hbad (by simpa [hnorm] using hle)

/-!
### Square-tail summability from the Riemann-von Mangoldt counting hypothesis
-/

/-- Height-square zero-tail summability from an explicit Riemann-von Mangoldt
zero-counting estimate with Backlund's constants. -/
theorem zeroImagSquareTailSummable_of_RvM
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1) :
    zeroImagSquareTailSummable :=
  zeroImagSquareTailSummable_of_count_by_N_with_zero_height hRvM
    zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_positive_height_zero_free

/-- Shifted height-square zero-tail summability from an explicit Riemann-von Mangoldt
zero-counting estimate with Backlund's constants. -/
theorem summable_zeroImagSquareTail_shifted_of_RvM
    (hRvM : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1) (s : ℂ) :
    Summable (fun rho : NontrivialZeros ↦ |(s - (rho : ℂ)).im|⁻¹ ^ (2 : ℕ)) :=
  summable_zeroImagSquareTail_shifted (zeroImagSquareTailSummable_of_RvM hRvM) s

end Kadiri
