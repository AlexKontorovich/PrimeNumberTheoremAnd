import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.ZetaConj
import PrimeNumberTheoremAnd.Backlund.ZeroCountCrude
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

The final section feeds the unconditional crude majorant
`Backlund.zetaCounting_crude_majorant` (`|N(T)| <= A * T^(3/2)`) through a weighted
form of the same dyadic chain, making the square-tail summability hypothesis-free.
The explicit RvM-hypothesis route stays as the path to the chapter's numerics.
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

/-- Shared functional-equation factorization: if `1 ≤ Re w` and `cos(π w / 2) ≠ 0`, then the
reflected value `ζ(1 - w)` is non-zero. (The factors `2`, `(2π)^{-w}`, `Γ(w)`, `ζ(w)` are all
non-zero for `Re w ≥ 1`, so only the cosine factor can vanish.) -/
lemma riemannZeta_one_sub_ne_zero_of_one_le_re {w : ℂ}
    (hw_re : 1 ≤ w.re) (hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0) :
    riemannZeta (1 - w) ≠ 0 := by
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have hre' : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hre'] at hw_re; linarith
  have hw_ne_one : w ≠ 1 := by
    rintro rfl
    refine hcos ?_
    have h2 : (↑Real.pi * (1 : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_neg_nat
  have hzeta_w : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  rw [hfe]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos) hzeta_w

/-- `ζ` does not vanish on the real segment `(-1, 0]`. (The non-trivial zeros lie in the
critical strip and the trivial zeros are at `-2, -4, …`; `ζ(0) = -1/2`.) Reusable for the left
edge / real point of the eq.(12) rectangle. -/
lemma riemannZeta_ne_zero_of_real_neg {σ : ℝ} (h1 : -1 < σ) (h2 : σ ≤ 0) :
    riemannZeta ((σ : ℝ) : ℂ) ≠ 0 := by
  rcases lt_or_eq_of_le h2 with hlt | h0
  · have hrw : ((σ : ℝ) : ℂ) = 1 - ((1 - σ : ℝ) : ℂ) := by push_cast; ring
    rw [hrw]
    refine riemannZeta_one_sub_ne_zero_of_one_le_re ?_ ?_
    · simp only [Complex.ofReal_re]; linarith
    · have harg : (↑Real.pi * ((1 - σ : ℝ) : ℂ) / 2) = ((Real.pi * (1 - σ) / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [harg, ← Complex.ofReal_cos, Complex.ofReal_ne_zero, Real.cos_ne_zero_iff]
      intro k hk
      have hk2 : Real.pi * (1 - σ) = Real.pi * (2 * (k : ℝ) + 1) := by
        have h2' : Real.pi * (1 - σ) / 2 = Real.pi * (2 * (k : ℝ) + 1) / 2 := by rw [hk]; ring
        linarith
      have heq : 1 - σ = 2 * (k : ℝ) + 1 := mul_left_cancel₀ Real.pi_ne_zero hk2
      have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
      have hk_lt : (k : ℝ) < 1 := by linarith
      have : 0 < k := by exact_mod_cast hk_pos
      have : k < 1 := by exact_mod_cast hk_lt
      omega
  · rw [h0, show ((0 : ℝ) : ℂ) = 0 by norm_num, riemannZeta_zero]; norm_num

lemma riemannZeta_ne_zero_of_re_nonpos_im_ne_zero {z : ℂ}
    (hre : z.re ≤ 0) (him : z.im ≠ 0) : riemannZeta z ≠ 0 := by
  set w : ℂ := 1 - z with hw
  have hw_im : w.im ≠ 0 := by rw [hw]; simp [him]
  have hw_re : 1 ≤ w.re := by rw [hw]; simp; linarith
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
  have hres := riemannZeta_one_sub_ne_zero_of_one_le_re hw_re hcos
  rwa [show (1 : ℂ) - w = z by rw [hw]; ring] at hres

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

/-!
### Unconditional square-tail summability from the crude counting majorant

The contracts above consume the counting estimate through the `(k+1) * 2^k` dyadic
growth shape. The crude majorant `|N(T)| <= A * T^(3/2)` grows faster than that shape,
but its `4^(-k)`-weighted dyadic series is still geometric (`2^(3(k+1)/2) / 4^k` decays
like `2^(-k/2)`), which is all the shell route needs.
-/

/-- Square-tail summability from any cumulative dyadic count bound whose
`4^(-k)`-weighted series is summable. -/
theorem zeroImagSquareTailSummable_of_cumulative_count_le {g : ℕ → ℝ}
    (hg : Summable fun k : ℕ => g k * (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ))
    (hcount : ∀ k : ℕ, (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤ g k) :
    zeroImagSquareTailSummable := by
  apply zeroImagSquareTailSummable_of_dyadic_shell_source
  unfold zeroImagDyadicShellSummableSource
  rw [summable_sigma_of_nonneg]
  · constructor
    · intro k
      haveI : Finite {rho : NontrivialZeros // zeroHeightDyadicShell k rho} :=
        Set.finite_coe_iff.mpr (nontrivialZeros_dyadic_shell_finite k)
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le
        (fun k => zeroHeightDyadicShellMass_nonneg k) (fun k => ?_) hg
      have hmass := zeroHeightDyadicShellMass_le_count_inv_sq k
      have hcard :
          (Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} : ℝ) ≤
            g k := by
        refine le_trans ?_ (hcount k)
        exact_mod_cast zeroHeightDyadicShellCount_le_cumulative_count k
      exact hmass.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
  · intro p
    exact sq_nonneg _

/-- The crude counting majorant at dyadic heights, in geometric form:
`(2^(k+1))^(3/2) = (2 * sqrt 2)^(k+1) <= 3^(k+1)`. -/
lemma zetaCountingDyadic_abs_N_le_geometric :
    ∃ E : ℝ, 0 < E ∧ ∀ k : ℕ,
      |riemannZeta.N ((2 : ℝ) ^ (k + 1))| ≤ E * 3 ^ k := by
  obtain ⟨A, hA0, hA⟩ := Backlund.zetaCounting_crude_majorant
  refine ⟨3 * A, by linarith, fun k => ?_⟩
  have hT2 : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ one_le_two (by omega)
  have hpow32 : ((2 : ℝ) ^ (k + 1)) ^ (3 / 2 : ℝ) =
      ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ (k + 1) := by
    rw [← Real.rpow_natCast (2 : ℝ) (k + 1),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hbase : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hbase0 : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  calc |riemannZeta.N ((2 : ℝ) ^ (k + 1))|
      ≤ A * ((2 : ℝ) ^ (k + 1)) ^ (3 / 2 : ℝ) := hA ((2 : ℝ) ^ (k + 1)) hT2
    _ = A * ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ (k + 1) := by rw [hpow32]
    _ ≤ A * 3 ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase (k + 1)) hA0.le
    _ = 3 * A * 3 ^ k := by ring

/-- Unconditional height-square zero-tail summability, from the crude majorant. -/
theorem zeroImagSquareTailSummable_of_crude_majorant :
    zeroImagSquareTailSummable := by
  obtain ⟨E, hE0, hE⟩ := zetaCountingDyadic_abs_N_le_geometric
  obtain ⟨A, D, hA0, hD0, hcountN⟩ :=
    zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_positive_height_zero_free
  refine zeroImagSquareTailSummable_of_cumulative_count_le
    (g := fun k => A * (E * 3 ^ k) + D) ?_ (fun k => ?_)
  · have hterm : ∀ k : ℕ,
        A * E * (3 / 4 : ℝ) ^ k + D * ((4 : ℝ)⁻¹) ^ k =
          (A * (E * 3 ^ k) + D) * (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
      intro k
      have h4 : (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) = ((4 : ℝ)⁻¹) ^ k := by
        rw [inv_pow, ← pow_mul, mul_comm k 2, pow_mul, ← inv_pow]
        norm_num
      have h34 : ((3 : ℝ) / 4) ^ k = 3 ^ k * ((4 : ℝ)⁻¹) ^ k := by
        rw [← mul_pow]
        norm_num
      rw [h4, h34]
      ring
    exact (((summable_geometric_of_lt_one (by norm_num)
      (by norm_num : (3 / 4 : ℝ) < 1)).mul_left (A * E)).add
      ((summable_geometric_of_lt_one (by norm_num)
        (by norm_num : ((4 : ℝ)⁻¹) < 1)).mul_left D)).congr hterm
  · exact (hcountN k).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hE k) hA0) le_rfl)

/-- Unconditional shifted height-square zero-tail summability. -/
theorem summable_zeroImagSquareTail_shifted_unconditional (s : ℂ) :
    Summable (fun rho : NontrivialZeros => |(s - (rho : ℂ)).im|⁻¹ ^ (2 : ℕ)) :=
  summable_zeroImagSquareTail_shifted zeroImagSquareTailSummable_of_crude_majorant s

/-!
### Conjugation transport for zero orders

`conj ∘ ζ ∘ conj = ζ` by `riemannZeta_conj`, so the zero order of `ζ` is symmetric
under conjugation. The general double-conjugation transport is built here from the
slope characterization of the derivative; mathlib does not provide it directly.
-/

/-- If `f` has derivative `f'` at `conj z₀`, the double conjugate has derivative
`conj f'` at `z₀`. -/
private lemma hasDerivAt_conj_conj {f : ℂ → ℂ} {f' z₀ : ℂ}
    (hf : HasDerivAt f f' ((starRingEnd ℂ) z₀)) :
    HasDerivAt (fun w ↦ (starRingEnd ℂ) (f ((starRingEnd ℂ) w)))
      ((starRingEnd ℂ) f') z₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  have hconj_tendsto : Filter.Tendsto (starRingEnd ℂ)
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhdsWithin ((starRingEnd ℂ) z₀) {(starRingEnd ℂ) z₀}ᶜ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (Complex.continuous_conj.tendsto z₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      have := congrArg (starRingEnd ℂ) h
      simpa [Complex.conj_conj] using this
  have hcomp := (Complex.continuous_conj.tendsto f').comp (hf.comp hconj_tendsto)
  refine Filter.Tendsto.congr (fun u ↦ ?_) hcomp
  simp only [Function.comp_apply, slope_def_field, map_div₀, map_sub, Complex.conj_conj]

/-- Analyticity of the double conjugate. -/
private lemma analyticAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f ((starRingEnd ℂ) z₀)) :
    AnalyticAt ℂ (fun w ↦ (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) z₀ := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have hc : Filter.Tendsto (starRingEnd ℂ) (nhds z₀) (nhds ((starRingEnd ℂ) z₀)) :=
    Complex.continuous_conj.tendsto z₀
  filter_upwards [hc.eventually hf] with w hw
  exact (hasDerivAt_conj_conj hw.hasDerivAt).differentiableAt

/-- The analytic order of the double conjugate at `z₀` is the analytic order of `f`
at `conj z₀`. -/
private lemma analyticOrderAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f ((starRingEnd ℂ) z₀)) :
    analyticOrderAt (fun w ↦ (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) z₀ =
      analyticOrderAt f ((starRingEnd ℂ) z₀) := by
  have hcfc := analyticAt_conj_conj hf
  have hc : Filter.Tendsto (starRingEnd ℂ) (nhds z₀) (nhds ((starRingEnd ℂ) z₀)) :=
    Complex.continuous_conj.tendsto z₀
  cases h : analyticOrderAt f ((starRingEnd ℂ) z₀) with
  | top =>
      rw [analyticOrderAt_eq_top] at h ⊢
      filter_upwards [hc.eventually h] with w hw
      rw [hw, map_zero]
  | coe n =>
      rw [hf.analyticOrderAt_eq_natCast] at h
      obtain ⟨g, hg, hg0, hfg⟩ := h
      rw [hcfc.analyticOrderAt_eq_natCast]
      refine ⟨fun w ↦ (starRingEnd ℂ) (g ((starRingEnd ℂ) w)),
        analyticAt_conj_conj hg, ?_, ?_⟩
      · intro h0
        apply hg0
        have := congrArg (starRingEnd ℂ) h0
        simpa [Complex.conj_conj] using this
      · filter_upwards [hc.eventually hfg] with w hw
        rw [hw]
        simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]

/-- The zero order of `ζ` is conjugation-symmetric away from `1`. -/
theorem riemannZeta_order_conj {ρ : ℂ} (hρ : ρ ≠ 1) :
    riemannZeta.order ((starRingEnd ℂ) ρ) = riemannZeta.order ρ := by
  have hρ' : (starRingEnd ℂ) ρ ≠ 1 := by
    intro h
    apply hρ
    have := congrArg (starRingEnd ℂ) h
    simpa [Complex.conj_conj] using this
  have han : AnalyticAt ℂ riemannZeta ρ :=
    riemannZeta_analyticOn_compl_one ρ (by simpa [Set.mem_compl_iff] using hρ)
  have han' : AnalyticAt ℂ riemannZeta ((starRingEnd ℂ) ρ) :=
    riemannZeta_analyticOn_compl_one _ (by simpa [Set.mem_compl_iff] using hρ')
  have hfun : (fun w ↦ (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) w))) = riemannZeta := by
    funext w
    rw [riemannZeta_conj, Complex.conj_conj]
  have hkey := analyticOrderAt_conj_conj (f := riemannZeta)
    (z₀ := (starRingEnd ℂ) ρ) (by simpa [Complex.conj_conj] using han)
  rw [hfun, Complex.conj_conj] at hkey
  unfold riemannZeta.order
  rw [han.meromorphicOrderAt_eq, han'.meromorphicOrderAt_eq, hkey]


/-!
### The weighted (order-carrying) zero accounting

The order-weighted count of zeros below a dyadic height is controlled by the
multiplicity-counting `N`: positive heights are `N`'s own index, negative heights
reindex through conjugation (`riemannZeta_order_conj`), and the real-axis bucket
is finite and height-independent.
-/

/-- Zero orders are nonnegative away from `1`. -/
lemma riemannZeta_order_nonneg {ρ : ℂ} (hρ : ρ ≠ 1) :
    0 ≤ riemannZeta.order ρ := by
  have han : AnalyticAt ℂ riemannZeta ρ :=
    riemannZeta_analyticOn_compl_one ρ (by simpa [Set.mem_compl_iff] using hρ)
  unfold riemannZeta.order
  rw [han.meromorphicOrderAt_eq]
  cases h : analyticOrderAt riemannZeta ρ with
  | top => simp
  | coe n =>
      simp only [ENat.map_coe, WithTop.untopD_coe]
      exact_mod_cast Nat.zero_le n

/-- `N` is the order sum over its own window. -/
private lemma riemannZeta_N_eq_tsum_order (T : ℝ) :
    riemannZeta.N T =
      ∑' ρ : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T),
        ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
  unfold riemannZeta.N riemannZeta.zeroes_sum
  exact tsum_congr fun ρ ↦ one_mul _

/-- The fixed weighted real-axis bucket. -/
noncomputable def weightedZeroHeightBucket : ℝ :=
  ∑' ρ : ZeroHeightNontrivialZeros,
    ((riemannZeta.order ((ρ : NontrivialZeros) : ℂ) : ℤ) : ℝ)

lemma weightedZeroHeightBucket_nonneg : 0 ≤ weightedZeroHeightBucket := by
  refine tsum_nonneg fun ρ ↦ ?_
  exact_mod_cast riemannZeta_order_nonneg (nontrivialZero_ne_one ρ.1)

/-- The weighted cumulative dyadic count against the multiplicity count `N`:
positive heights land in `N`'s window, negative heights reindex through
conjugation, the real axis lands in the fixed bucket. -/
theorem weighted_cumulative_count_le (k : ℕ) :
    (∑' ρ : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)},
        ((riemannZeta.order ((ρ : NontrivialZeros) : ℂ) : ℤ) : ℝ)) ≤
      2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + weightedZeroHeightBucket := by
  classical
  haveI hXf : Fintype {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} :=
    (nontrivialZeros_abs_im_lt_finite ((2 : ℝ) ^ (k + 1))).fintype
  haveI hRf : Fintype (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 ((2 : ℝ) ^ (k + 1)))) :=
    (zeroes_rect_univ_positive_height_finite ((2 : ℝ) ^ (k + 1))).fintype
  haveI hZf : Fintype ZeroHeightNontrivialZeros :=
    @Fintype.ofFinite _ zeroHeightNontrivialZeros_finite
  have hRnonneg : ∀ z ∈ Finset.univ.image (fun ρ : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 ((2 : ℝ) ^ (k + 1))) ↦ (ρ : ℂ)), (0 : ℝ) ≤ ((riemannZeta.order z : ℤ) : ℝ) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨ρ, -, rfl⟩ := hz
    have hne : (ρ : ℂ) ≠ 1 := by
      intro h
      have him := ρ.property.2.1.1
      rw [h] at him
      simp [Complex.one_im] at him
    exact_mod_cast riemannZeta_order_nonneg hne
  have hZnonneg : ∀ z ∈ Finset.univ.image (fun ρ : ZeroHeightNontrivialZeros ↦ ((ρ.1 : NontrivialZeros) : ℂ)), (0 : ℝ) ≤ ((riemannZeta.order z : ℤ) : ℝ) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨ρ, -, rfl⟩ := hz
    exact_mod_cast riemannZeta_order_nonneg (nontrivialZero_ne_one ρ.1)
  have hN : riemannZeta.N ((2 : ℝ) ^ (k + 1)) =
      ∑ z ∈ Finset.univ.image (fun ρ : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 ((2 : ℝ) ^ (k + 1))) ↦ (ρ : ℂ)), ((riemannZeta.order z : ℤ) : ℝ) := by
    rw [riemannZeta_N_eq_tsum_order, tsum_fintype,
      Finset.sum_image (g := fun ρ : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 ((2 : ℝ) ^ (k + 1))) ↦ (ρ : ℂ))
        (fun a _ b _ hab ↦ Subtype.ext hab)]
  have hB : weightedZeroHeightBucket =
      ∑ z ∈ Finset.univ.image (fun ρ : ZeroHeightNontrivialZeros ↦ ((ρ.1 : NontrivialZeros) : ℂ)), ((riemannZeta.order z : ℤ) : ℝ) := by
    unfold weightedZeroHeightBucket
    rw [tsum_fintype,
      Finset.sum_image (g := fun ρ : ZeroHeightNontrivialZeros ↦ ((ρ.1 : NontrivialZeros) : ℂ))
        (fun a _ b _ hab ↦ Subtype.ext (Subtype.ext hab))]
  rw [tsum_fintype]
  have hsplit1 := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)})
    (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ 0 < (x.1 : ℂ).im)
    (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ 0 < (x.1 : ℂ).im))
    (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ).im < 0)
    (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ))
  have hpos : (∑ x ∈ (Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ 0 < (x.1 : ℂ).im),
      ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ)) ≤
      ∑ z ∈ Finset.univ.image (fun ρ : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 ((2 : ℝ) ^ (k + 1))) ↦ (ρ : ℂ)), ((riemannZeta.order z : ℤ) : ℝ) := by
    have himg : (∑ x ∈ (Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ 0 < (x.1 : ℂ).im),
        ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ)) =
        ∑ z ∈ ((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ 0 < (x.1 : ℂ).im)).image (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ)),
          ((riemannZeta.order z : ℤ) : ℝ) :=
      (Finset.sum_image (f := fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ)) (g := fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ))
        (fun a _ b _ hab ↦ Subtype.ext (Subtype.ext hab))).symm
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z hz _ ↦ hRnonneg z hz)
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_image]
    exact ⟨⟨(x.1 : ℂ), Set.mem_univ _,
      ⟨hx.2, lt_of_le_of_lt (le_abs_self _) x.property⟩,
      x.1.property.2.2⟩, Finset.mem_univ _, rfl⟩
  have hneg : (∑ x ∈ ((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ 0 < (x.1 : ℂ).im)).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ).im < 0),
      ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ)) ≤
      ∑ z ∈ Finset.univ.image (fun ρ : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 ((2 : ℝ) ^ (k + 1))) ↦ (ρ : ℂ)), ((riemannZeta.order z : ℤ) : ℝ) := by
    have hcongr : ∀ x ∈ ((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ 0 < (x.1 : ℂ).im)).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ).im < 0),
        ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ) =
        ((riemannZeta.order ((starRingEnd ℂ) (x.1 : ℂ)) : ℤ) : ℝ) := by
      intro x hx
      rw [riemannZeta_order_conj (nontrivialZero_ne_one x.1)]
    rw [Finset.sum_congr rfl hcongr]
    have himg : (∑ x ∈ ((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ 0 < (x.1 : ℂ).im)).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ).im < 0),
        ((riemannZeta.order ((starRingEnd ℂ) (x.1 : ℂ)) : ℤ) : ℝ)) =
        ∑ z ∈ (((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ 0 < (x.1 : ℂ).im)).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ).im < 0)).image (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (starRingEnd ℂ) (x.1 : ℂ)),
          ((riemannZeta.order z : ℤ) : ℝ) :=
      (Finset.sum_image (f := fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ)) (g := fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (starRingEnd ℂ) (x.1 : ℂ))
        (fun a _ b _ hab ↦ Subtype.ext (Subtype.ext (by
          have h2 := congrArg (starRingEnd ℂ) hab
          simpa [Complex.conj_conj] using h2)))).symm
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z hz _ ↦ hRnonneg z hz)
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Finset.mem_filter] at hx
    have hx2 := hx.2
    rw [Finset.mem_image]
    refine ⟨⟨(starRingEnd ℂ) (x.1 : ℂ), Set.mem_univ _, ⟨?_, ?_⟩, ?_⟩,
      Finset.mem_univ _, rfl⟩
    · simpa [Complex.conj_im] using hx2
    · have h1 : |(x.1 : ℂ).im| < (2 : ℝ) ^ (k + 1) := x.property
      rw [abs_of_neg hx2] at h1
      simpa [Complex.conj_im] using h1
    · show riemannZeta ((starRingEnd ℂ) (x.1 : ℂ)) = 0
      rw [riemannZeta_conj, x.1.property.2.2, map_zero]
  have hzero : (∑ x ∈ ((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ 0 < (x.1 : ℂ).im)).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ (x.1 : ℂ).im < 0),
      ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ)) ≤
      ∑ z ∈ Finset.univ.image (fun ρ : ZeroHeightNontrivialZeros ↦ ((ρ.1 : NontrivialZeros) : ℂ)), ((riemannZeta.order z : ℤ) : ℝ) := by
    have himg : (∑ x ∈ ((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ 0 < (x.1 : ℂ).im)).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ (x.1 : ℂ).im < 0),
        ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ)) =
        ∑ z ∈ (((Finset.univ : Finset {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)}).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ 0 < (x.1 : ℂ).im)).filter (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ¬ (x.1 : ℂ).im < 0)).image (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ)),
          ((riemannZeta.order z : ℤ) : ℝ) :=
      (Finset.sum_image (f := fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ)) (g := fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ (x.1 : ℂ))
        (fun a _ b _ hab ↦ Subtype.ext (Subtype.ext hab))).symm
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z hz _ ↦ hZnonneg z hz)
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Finset.mem_filter] at hx
    have hx2 := hx.2
    have hx1 := hx.1
    rw [Finset.mem_filter] at hx1
    have him0 : (x.1 : ℂ).im = 0 :=
      le_antisymm (not_lt.mp hx1.2) (not_lt.mp hx2)
    rw [Finset.mem_image]
    exact ⟨⟨x.1, him0⟩, Finset.mem_univ _, rfl⟩
  have hNabs : riemannZeta.N ((2 : ℝ) ^ (k + 1)) ≤
      |riemannZeta.N ((2 : ℝ) ^ (k + 1))| := le_abs_self _
  linarith [hsplit1, hsplit2, hpos, hneg, hzero]

/-!
### The weighted square tail

The order-weighted height-square tail over the zeros is summable: shell masses
carry the order weight into the weighted cumulative count, which the crude
majorant makes geometric.
-/

/-- The weighted dyadic shell mass is controlled by the weighted cumulative count. -/
private lemma weighted_shell_mass_le (k : ℕ) :
    (∑' ρ : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ},
        ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) *
          zeroImagSquareTail ρ.1) ≤
      (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + weightedZeroHeightBucket) *
        (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
  classical
  haveI : Finite {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ} :=
    Set.finite_coe_iff.mpr (nontrivialZeros_dyadic_shell_finite k)
  haveI : Finite {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} :=
    Set.finite_coe_iff.mpr (nontrivialZeros_abs_im_lt_finite ((2 : ℝ) ^ (k + 1)))
  have hstep1 : (∑' ρ : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ},
      ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) *
        zeroImagSquareTail ρ.1) ≤
      ∑' ρ : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ},
        ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) *
          (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
    refine Summable.tsum_le_tsum (fun ρ ↦ ?_) Summable.of_finite Summable.of_finite
    have hord : (0 : ℝ) ≤
        ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) := by
      exact_mod_cast riemannZeta_order_nonneg (nontrivialZero_ne_one ρ.1)
    exact mul_le_mul_of_nonneg_left (zeroImagSquareTail_le_dyadic_inv_sq ρ.2) hord
  have hstep2 : (∑' ρ : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ},
      ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) *
        (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ)) =
      (∑' ρ : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ},
        ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ)) *
        (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := tsum_mul_right
  have hstep3 : (∑' ρ : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ},
      ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ)) ≤
      ∑' ρ : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)},
        ((riemannZeta.order ((ρ : NontrivialZeros) : ℂ) : ℤ) : ℝ) := by
    classical
    haveI hSf : Fintype {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ} :=
      (nontrivialZeros_dyadic_shell_finite k).fintype
    haveI hCf : Fintype {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} :=
      (nontrivialZeros_abs_im_lt_finite ((2 : ℝ) ^ (k + 1))).fintype
    rw [tsum_fintype, tsum_fintype]
    have himgS : (∑ x : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ},
        ((riemannZeta.order ((x.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ)) =
        ∑ z ∈ Finset.univ.image (fun x : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ} ↦ ((x.1 : NontrivialZeros) : ℂ)),
          ((riemannZeta.order z : ℤ) : ℝ) :=
      (Finset.sum_image (f := fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ))
        (g := fun x : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ} ↦ ((x.1 : NontrivialZeros) : ℂ))
        (fun a _ b _ hab ↦ Subtype.ext (Subtype.ext hab))).symm
    have himgC : (∑ x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)},
        ((riemannZeta.order ((x : NontrivialZeros) : ℂ) : ℤ) : ℝ)) =
        ∑ z ∈ Finset.univ.image (fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ((x.1 : NontrivialZeros) : ℂ)),
          ((riemannZeta.order z : ℤ) : ℝ) :=
      (Finset.sum_image (f := fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ))
        (g := fun x : {ρ : NontrivialZeros // |(ρ : ℂ).im| < (2 : ℝ) ^ (k + 1)} ↦ ((x.1 : NontrivialZeros) : ℂ))
        (fun a _ b _ hab ↦ Subtype.ext (Subtype.ext hab))).symm
    rw [himgS, himgC]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨x, -, rfl⟩ := hz
      rw [Finset.mem_image]
      exact ⟨⟨x.1, x.2.2⟩, Finset.mem_univ _, rfl⟩
    · intro z hz _
      rw [Finset.mem_image] at hz
      obtain ⟨x, -, rfl⟩ := hz
      exact_mod_cast riemannZeta_order_nonneg (nontrivialZero_ne_one x.1)
  have h4nn : (0 : ℝ) ≤ (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := sq_nonneg _
  have hfinal : (∑' ρ : {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ},
      ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) *
        (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ)) ≤
      (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + weightedZeroHeightBucket) *
        (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
    rw [hstep2]
    exact mul_le_mul_of_nonneg_right
      (hstep3.trans (weighted_cumulative_count_le k)) h4nn
  exact hstep1.trans hfinal

/-- The weighted dyadic-shell sigma sum is summable. -/
private lemma weighted_shell_sigma_summable :
    Summable (fun p : Sigma (fun k : ℕ ↦
        {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ}) ↦
      ((riemannZeta.order ((p.2.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) *
        zeroImagSquareTail p.2.1) := by
  classical
  rw [summable_sigma_of_nonneg]
  · constructor
    · intro k
      haveI : Finite {ρ : NontrivialZeros // zeroHeightDyadicShell k ρ} :=
        Set.finite_coe_iff.mpr (nontrivialZeros_dyadic_shell_finite k)
      exact Summable.of_finite
    · obtain ⟨E, hE0, hE⟩ := zetaCountingDyadic_abs_N_le_geometric
      have hterm : ∀ k : ℕ,
          (2 * E) * ((3 / 4 : ℝ)) ^ k +
            weightedZeroHeightBucket * ((4 : ℝ)⁻¹) ^ k =
          (2 * (E * 3 ^ k) + weightedZeroHeightBucket) *
            (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := by
        intro k
        have h4 : (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) = ((4 : ℝ)⁻¹) ^ k := by
          rw [inv_pow, ← pow_mul, mul_comm k 2, pow_mul, ← inv_pow]
          norm_num
        have h34 : ((3 : ℝ) / 4) ^ k = 3 ^ k * ((4 : ℝ)⁻¹) ^ k := by
          rw [← mul_pow]
          norm_num
        rw [h4, h34]
        ring
      have hgeom : Summable (fun k : ℕ ↦
          (2 * (E * 3 ^ k) + weightedZeroHeightBucket) *
            (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ)) :=
        (((summable_geometric_of_lt_one (by norm_num)
          (by norm_num : (3 / 4 : ℝ) < 1)).mul_left (2 * E)).add
          ((summable_geometric_of_lt_one (by norm_num)
            (by norm_num : ((4 : ℝ)⁻¹) < 1)).mul_left
              weightedZeroHeightBucket)).congr hterm
      refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hgeom
      · refine tsum_nonneg fun ρ ↦ mul_nonneg ?_ (sq_nonneg _)
        exact_mod_cast riemannZeta_order_nonneg (nontrivialZero_ne_one ρ.1)
      · refine (weighted_shell_mass_le k).trans ?_
        have hb := weightedZeroHeightBucket_nonneg
        have hNk := hE k
        have h4nn : (0 : ℝ) ≤ (((2 : ℝ) ^ k)⁻¹) ^ (2 : ℕ) := sq_nonneg _
        refine mul_le_mul_of_nonneg_right ?_ h4nn
        linarith
  · intro p
    refine mul_nonneg ?_ (sq_nonneg _)
    exact_mod_cast riemannZeta_order_nonneg (nontrivialZero_ne_one p.2.1)

/-- The order-weighted height-square zero tail is summable, unconditionally. -/
theorem weighted_zeroImagSquareTail_summable :
    Summable (fun ρ : NontrivialZeros ↦
      ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) * zeroImagSquareTail ρ) := by
  classical
  have hhigh : Summable (fun ρ : {ρ : NontrivialZeros // 1 ≤ |(ρ : ℂ).im|} ↦
      ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) *
        zeroImagSquareTail ρ.1) := by
    have h := weighted_shell_sigma_summable.comp_injective
      highZeroToDyadicShell_injective
    simpa [Function.comp_def, highZeroToDyadicShell] using h
  have hlow_set : ({ρ : NontrivialZeros | ¬ 1 ≤ |(ρ : ℂ).im|} :
      Set NontrivialZeros).Finite := by
    apply Set.Finite.subset nontrivialZeros_abs_im_lt_one_finite
    intro ρ hρ
    rw [Set.mem_setOf_eq] at hρ ⊢
    exact lt_of_not_ge hρ
  haveI : Finite {ρ : NontrivialZeros // ¬ 1 ≤ |(ρ : ℂ).im|} :=
    Set.finite_coe_iff.mpr hlow_set
  have hlow : Summable (fun ρ : {ρ : NontrivialZeros // ¬ 1 ≤ |(ρ : ℂ).im|} ↦
      ((riemannZeta.order ((ρ.1 : NontrivialZeros) : ℂ) : ℤ) : ℝ) *
        zeroImagSquareTail ρ.1) := Summable.of_finite
  exact (summable_subtype_and_compl
    (s := {ρ : NontrivialZeros | 1 ≤ |(ρ : ℂ).im|})).mp ⟨hhigh, hlow⟩

/-- The order-weighted shifted height-square tail is summable for every shift. -/
theorem weighted_zeroImagSquareTail_shifted_summable (s : ℂ) :
    Summable (fun ρ : NontrivialZeros ↦
      ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) * (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ))) := by
  refine Summable.of_norm_bounded_eventually
    (weighted_zeroImagSquareTail_summable.mul_left 4) ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (nontrivialZeros_abs_im_lt_finite (2 * |s.im| + 2))
  intro ρ hbad
  rw [Set.mem_setOf_eq] at hbad ⊢
  by_contra hsmall
  have hlarge : 2 * |s.im| + 2 ≤ |(ρ : ℂ).im| := le_of_not_gt hsmall
  apply hbad
  have hle := zeroImagSquareTail_shifted_le_four (s := s) (rho := ρ) hlarge
  have hord : (0 : ℝ) ≤ ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
    exact_mod_cast riemannZeta_order_nonneg (nontrivialZero_ne_one ρ)
  have hshift_nn : (0 : ℝ) ≤ |(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hord hshift_nn)]
  calc ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) * (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ))
      ≤ ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) * (4 * zeroImagSquareTail ρ) :=
        mul_le_mul_of_nonneg_left hle hord
    _ = 4 * (((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) * zeroImagSquareTail ρ) := by
        ring

end Kadiri
