import RSBounds.BacklundCountIdentity

/-!
# Including zeros at the upper endpoint

Finiteness of zeros in a slightly taller rectangle supplies an interval
immediately above each height with no zero ordinates. The open count is
constant there and equals the closed count at the original height.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

noncomputable def closedPositiveZeros (T : ℝ) : Finset ℂ :=
  (positiveZeros (T + 1)).filter (fun ρ => ρ.im ≤ T)

noncomputable def N_le (T : ℝ) : ℕ :=
  ∑ ρ ∈ closedPositiveZeros T, (analyticOrderAt riemannZeta ρ).toNat

theorem mem_closedPositiveZeros_iff {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
    ρ ∈ closedPositiveZeros T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  rw [closedPositiveZeros, Finset.mem_filter, mem_positiveZeros_iff_zeta (by linarith)]
  constructor
  · rintro ⟨⟨hz, h0, _⟩, hT⟩
    exact ⟨hz, h0, hT⟩
  · rintro ⟨hz, h0, hT⟩
    exact ⟨⟨hz, h0, by linarith⟩, hT⟩

private theorem finite_right_gap (S : Finset ℂ) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ρ ∈ S, T < ρ.im → T + δ ≤ ρ.im := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨δ, hδ0, hδ1, hgap⟩ := ih
    by_cases haT : T < a.im
    · refine ⟨min δ ((a.im - T) / 2), lt_min hδ0 (by linarith),
        (min_le_left _ _).trans hδ1, ?_⟩
      intro ρ hρ hρT
      rcases Finset.mem_insert.mp hρ with rfl | hρ
      · linarith [min_le_right δ ((ρ.im - T) / 2)]
      · exact (add_le_add le_rfl (min_le_left _ _)).trans (hgap ρ hρ hρT)
    · refine ⟨δ, hδ0, hδ1, ?_⟩
      intro ρ hρ hρT
      rcases Finset.mem_insert.mp hρ with rfl | hρ
      · exact (haT hρT).elim
      · exact hgap ρ hρ hρT

theorem exists_right_interval_good_count {T : ℝ} (hT : 0 < T) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ S ∈ Ioo T (T + δ),
      zetaGoodHeight S ∧ N S = N_le T := by
  obtain ⟨δ, hδ0, hδ1, hgap⟩ := finite_right_gap (positiveZeros (T + 1)) T
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro S hS
  have hS0 : 0 < S := hT.trans hS.1
  have hS1 : S < T + 1 := lt_of_lt_of_le hS.2 (by linarith)
  have hg : zetaGoodHeight S := by
    intro ρ hz he
    have hρ : ρ ∈ positiveZeros (T + 1) :=
      (mem_positiveZeros_iff_zeta (by linarith)).mpr ⟨hz, by simpa [he] using hS0,
        by simpa [he] using hS1⟩
    have hh := hgap ρ hρ (by simpa [he] using hS.1)
    rw [he] at hh
    linarith [hS.2]
  refine ⟨hg, ?_⟩
  have hsets : positiveZeros S = closedPositiveZeros T := by
    apply Finset.ext
    intro ρ
    rw [mem_positiveZeros_iff_zeta hS0, mem_closedPositiveZeros_iff hT]
    constructor
    · rintro ⟨hz, h0, hρS⟩
      refine ⟨hz, h0, ?_⟩
      by_contra h
      have hTρ : T < ρ.im := lt_of_not_ge h
      have hρ : ρ ∈ positiveZeros (T + 1) :=
        (mem_positiveZeros_iff_zeta (by linarith)).mpr ⟨hz, h0, hρS.trans hS1⟩
      linarith [hgap ρ hρ hTρ, hS.2]
    · rintro ⟨hz, h0, hρT⟩
      exact ⟨hz, h0, hρT.trans_lt hS.1⟩
  rw [N_eq_sum_zetaMultiplicity hS0, hsets]
  rfl

/-- A continuous bound at all nearby good heights extends to the closed
count at the endpoint. No zero-count or RH hypothesis enters this step. -/
theorem closed_count_le_of_good_height_bound {T : ℝ} (hT : 0 < T) {F : ℝ → ℝ}
    (hF : ContinuousAt F T)
    (hbound : ∀ S : ℝ, T < S → zetaGoodHeight S → (N S : ℝ) ≤ F S) :
    (N_le T : ℝ) ≤ F T := by
  obtain ⟨δ, hδ0, hδ1, hloc⟩ := exists_right_interval_good_count hT
  let S : ℕ → ℝ := fun n => T + (δ / 2) * (1 / ((n : ℝ) + 1))
  have hSmem (n : ℕ) : S n ∈ Ioo T (T + δ) := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hrec : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).mpr hn1
    have hp : 0 < (δ / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    have hq := mul_le_mul_of_nonneg_left hrec (show 0 ≤ δ / 2 by positivity)
    dsimp [S]
    constructor <;> nlinarith
  have hlim : Tendsto S atTop (𝓝 T) := by
    have hh : Tendsto (fun n : ℕ => T + (δ / 2) * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (T + (δ / 2) * 0)) := tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 2))
    simpa [S] using hh
  have hb : ∀ n : ℕ, (N_le T : ℝ) ≤ F (S n) := by
    intro n
    have hl := hloc (S n) (hSmem n)
    rw [← hl.2]
    exact hbound (S n) (hSmem n).1 hl.1
  exact ge_of_tendsto (hF.tendsto.comp hlim) (Eventually.of_forall hb)

/-- Strict envelopes remain strict when the estimate at good heights is
proved with a positive margin at the endpoint. -/
theorem closed_count_lt_of_good_height_bound {T : ℝ} (hT : 0 < T) {F : ℝ → ℝ} {B : ℝ}
    (hF : ContinuousAt F T)
    (hbound : ∀ S : ℝ, T < S → zetaGoodHeight S → (N S : ℝ) ≤ F S)
    (hgap : F T < B) : (N_le T : ℝ) < B :=
  (closed_count_le_of_good_height_bound hT hF hbound).trans_lt hgap

/-- Transfer an absolute-error estimate to the inclusive endpoint count. -/
theorem closed_count_abs_le_of_good_height_bound {T : ℝ} (hT : 0 < T)
    {M B : ℝ → ℝ} (hM : ContinuousAt M T) (hB : ContinuousAt B T)
    (hbound : ∀ S : ℝ, T < S → zetaGoodHeight S → |(N S : ℝ) - M S| ≤ B S) :
    |(N_le T : ℝ) - M T| ≤ B T := by
  obtain ⟨δ, hδ0, hδ1, hloc⟩ := exists_right_interval_good_count hT
  let S : ℕ → ℝ := fun n => T + (δ / 2) * (1 / ((n : ℝ) + 1))
  have hSmem (n : ℕ) : S n ∈ Ioo T (T + δ) := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hrec : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).mpr hn1
    have hp : 0 < (δ / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    have hq := mul_le_mul_of_nonneg_left hrec (show 0 ≤ δ / 2 by positivity)
    dsimp [S]
    constructor <;> nlinarith
  have hlim : Tendsto S atTop (𝓝 T) := by
    have hh : Tendsto (fun n : ℕ => T + (δ / 2) * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (T + (δ / 2) * 0)) := tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 2))
    simpa [S] using hh
  have hb : ∀ n : ℕ, |(N_le T : ℝ) - M (S n)| ≤ B (S n) := by
    intro n
    have hl := hloc (S n) (hSmem n)
    rw [← hl.2]
    exact hbound (S n) (hSmem n).1 hl.1
  exact le_of_tendsto_of_tendsto
    ((tendsto_const_nhds.sub (hM.tendsto.comp hlim)).abs)
    (hB.tendsto.comp hlim) (Eventually.of_forall hb)

theorem closed_count_abs_lt_of_good_height_bound {T : ℝ} (hT : 0 < T)
    {M B : ℝ → ℝ} {C : ℝ} (hM : ContinuousAt M T) (hB : ContinuousAt B T)
    (hbound : ∀ S : ℝ, T < S → zetaGoodHeight S → |(N S : ℝ) - M S| ≤ B S)
    (hgap : B T < C) : |(N_le T : ℝ) - M T| < C :=
  (closed_count_abs_le_of_good_height_bound hT hM hB hbound).trans_lt hgap

end TernaryGoldbach.RSBounds.BacklundCountIdentity
