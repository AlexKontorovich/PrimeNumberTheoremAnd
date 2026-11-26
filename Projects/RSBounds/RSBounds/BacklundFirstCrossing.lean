/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in licenses/Gersh-LICENSE.
-/
/-
# First-crossing consecutive-level lemmas (pure real analysis)

Keystone of the sound interlacing proof for the Riemann–von-Mangoldt discharge
(Trudgian (3.2)-style sweep).  For a continuous `φ : ℝ → ℝ` on `[a, b]`:

* `exists_firstCrossing`  — the FIRST time `φ` crosses a level `ℓ` with
  `φ a < ℓ < φ b`: a point `c ∈ (a,b)` with `φ c = ℓ` and `φ < ℓ` on `[a, c)`.
* `exists_lastCrossing`   — the LAST such crossing: `φ c = ℓ` and `φ > ℓ` on `(c, b]`.
* `exists_firstCrossing_family` — first crossings of the ascending level family
  `ℓ₀ + i·π` (`i = 0, …, m−1`), strictly increasing in `i`.
* `exists_lastCrossing_family`  — last crossings of the descending level family
  `ℓ₀ − i·π`, strictly decreasing in `i` (right-endpoint–anchored sweep).
* `exists_first_halfturn_level` / `exists_last_halfturn_level` — the first
  half-turn level `π/2 + kπ` strictly above (resp. strictly below) a given real,
  within distance `π`.
* `cos_eq_zero_of_halfturn` — `cos` vanishes at every half-turn level.

Everything is pure IVT + `csInf`/`csSup`; no L-function theory, no axioms
beyond the base trio.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace TernaryGoldbach.RSBounds.BacklundFirstCrossing

open Set

/-- **First crossing from the left.**  If `φ` is continuous on `[a, b]` with
`φ a < ℓ < φ b`, there is a first crossing `c ∈ (a, b)`: `φ c = ℓ` and
`φ x < ℓ` for every `x ∈ [a, c)`. -/
theorem exists_firstCrossing {φ : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b)) (hlo : φ a < ℓ) (hhi : ℓ < φ b) :
    ∃ c ∈ Set.Ioo a b, φ c = ℓ ∧ ∀ x ∈ Set.Ico a c, φ x < ℓ := by
  set S : Set ℝ := Set.Icc a b ∩ φ ⁻¹' {ℓ} with hSdef
  -- `S` is nonempty by the intermediate value theorem.
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hcont ⟨hlo.le, hhi.le⟩
    exact ⟨x, hx, hfx⟩
  -- `S` is closed (crossing set of a continuous function on a closed set).
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  set c : ℝ := sInf S with hcdef
  have hcS : c ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hcIcc : c ∈ Set.Icc a b := hcS.1
  have hφc : φ c = ℓ := hcS.2
  have hac : a < c := by
    refine hcIcc.1.lt_of_ne ?_
    intro h
    exact hlo.ne (by rw [h]; exact hφc)
  have hcb : c < b := by
    refine hcIcc.2.lt_of_ne ?_
    intro h
    exact hhi.ne' (by rw [← h]; exact hφc)
  refine ⟨c, ⟨hac, hcb⟩, hφc, ?_⟩
  -- minimality: strictly below the level before the first crossing
  intro x hx
  have hxb : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le.trans hcIcc.2⟩
  by_contra hge
  push Not at hge
  have hne : φ x ≠ ℓ := by
    intro heq
    have hxS : x ∈ S := ⟨hxb, heq⟩
    exact absurd hx.2 (not_lt.mpr (csInf_le hSbdd hxS))
  have hlt : ℓ < φ x := lt_of_le_of_ne hge (Ne.symm hne)
  -- IVT on `[a, x]` produces an earlier crossing, contradicting `c = sInf S`.
  have hsub : Set.Icc a x ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hxb.2
  obtain ⟨y, hy, hfy⟩ :=
    intermediate_value_Icc hx.1 (hcont.mono hsub) ⟨hlo.le, hlt.le⟩
  have hyS : y ∈ S := ⟨⟨hy.1, hy.2.trans hxb.2⟩, hfy⟩
  have hcy : c ≤ y := csInf_le hSbdd hyS
  exact absurd (hcy.trans hy.2) (not_le.mpr hx.2)

/-- **Last crossing from the right.**  If `φ` is continuous on `[a, b]` with
`φ a < ℓ < φ b`, there is a last crossing `c ∈ (a, b)`: `φ c = ℓ` and
`ℓ < φ x` for every `x ∈ (c, b]`. -/
theorem exists_lastCrossing {φ : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b)) (hlo : φ a < ℓ) (hhi : ℓ < φ b) :
    ∃ c ∈ Set.Ioo a b, φ c = ℓ ∧ ∀ x ∈ Set.Ioc c b, ℓ < φ x := by
  set S : Set ℝ := Set.Icc a b ∩ φ ⁻¹' {ℓ} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hcont ⟨hlo.le, hhi.le⟩
    exact ⟨x, hx, hfx⟩
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  set c : ℝ := sSup S with hcdef
  have hcS : c ∈ S := hSclosed.csSup_mem hSne hSbdd
  have hcIcc : c ∈ Set.Icc a b := hcS.1
  have hφc : φ c = ℓ := hcS.2
  have hac : a < c := by
    refine hcIcc.1.lt_of_ne ?_
    intro h
    exact hlo.ne (by rw [h]; exact hφc)
  have hcb : c < b := by
    refine hcIcc.2.lt_of_ne ?_
    intro h
    exact hhi.ne' (by rw [← h]; exact hφc)
  refine ⟨c, ⟨hac, hcb⟩, hφc, ?_⟩
  -- maximality: strictly above the level after the last crossing
  intro x hx
  have hxb : x ∈ Set.Icc a b := ⟨hcIcc.1.trans hx.1.le, hx.2⟩
  by_contra hge
  push Not at hge
  have hne : φ x ≠ ℓ := by
    intro heq
    have hxS : x ∈ S := ⟨hxb, heq⟩
    exact absurd hx.1 (not_lt.mpr (le_csSup hSbdd hxS))
  have hlt : φ x < ℓ := lt_of_le_of_ne hge hne
  -- IVT on `[x, b]` produces a later crossing, contradicting `c = sSup S`.
  have hsub : Set.Icc x b ⊆ Set.Icc a b := Set.Icc_subset_Icc hxb.1 le_rfl
  obtain ⟨y, hy, hfy⟩ :=
    intermediate_value_Icc hx.2 (hcont.mono hsub) ⟨hlt.le, hhi.le⟩
  have hyS : y ∈ S := ⟨⟨hxb.1.trans hy.1, hy.2⟩, hfy⟩
  have hyc : y ≤ c := le_csSup hSbdd hyS
  exact absurd (hy.1.trans hyc) (not_le.mpr hx.1)

/-- **First-crossing family for the ascending levels `ℓ₀ + i·π`, `i < m`.**
If `φ a < ℓ₀` and `ℓ₀ + (m−1)π < φ b`, then each level `ℓ₀ + i·π` (`i < m`)
has a first crossing `c i ∈ (a, b)`; the `c i` are strictly increasing in `i`,
`φ (c i)` equals the level, and `φ` is strictly below the level on `[a, c i)`. -/
theorem exists_firstCrossing_family {φ : ℝ → ℝ} {a b ℓ₀ : ℝ} {m : ℕ}
    (hab : a ≤ b) (hcont : ContinuousOn φ (Set.Icc a b))
    (hℓ₀ : φ a < ℓ₀) (htop : ℓ₀ + ((m : ℝ) - 1) * Real.pi < φ b) :
    ∃ c : ℕ → ℝ,
      (∀ i, i < m → c i ∈ Set.Ioo a b) ∧
      (∀ i j, i < j → j < m → c i < c j) ∧
      (∀ i, i < m → φ (c i) = ℓ₀ + (i : ℝ) * Real.pi) ∧
      (∀ i, i < m → ∀ x ∈ Set.Ico a (c i), φ x < ℓ₀ + (i : ℝ) * Real.pi) := by
  have hpi := Real.pi_pos
  have key : ∀ i : ℕ, i < m →
      ∃ c ∈ Set.Ioo a b, φ c = ℓ₀ + (i : ℝ) * Real.pi ∧
        ∀ x ∈ Set.Ico a c, φ x < ℓ₀ + (i : ℝ) * Real.pi := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) * Real.pi :=
      mul_nonneg (Nat.cast_nonneg i) hpi.le
    have hlo : φ a < ℓ₀ + (i : ℝ) * Real.pi := by linarith
    have hcast : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
    have hmul : (i : ℝ) * Real.pi ≤ ((m : ℝ) - 1) * Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) hpi.le
    have hhi : ℓ₀ + (i : ℝ) * Real.pi < φ b := by linarith
    exact exists_firstCrossing hab hcont hlo hhi
  choose! c hmem hval hmin using key
  refine ⟨c, hmem, ?_, hval, hmin⟩
  intro i j hij hjm
  have him : i < m := hij.trans hjm
  have hstep : (i : ℝ) * Real.pi < (j : ℝ) * Real.pi := by
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_right this hpi
  by_contra hle
  push Not at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- `c j` would lie strictly before the first crossing of the LOWER level `i`
    have h1 : φ (c j) < ℓ₀ + (i : ℝ) * Real.pi :=
      hmin i him (c j) ⟨(hmem j hjm).1.le, hlt⟩
    have h2 : φ (c j) = ℓ₀ + (j : ℝ) * Real.pi := hval j hjm
    linarith
  · -- equal crossing points would force equal levels
    have h1 : φ (c i) = ℓ₀ + (i : ℝ) * Real.pi := hval i him
    have h2 : φ (c j) = ℓ₀ + (j : ℝ) * Real.pi := hval j hjm
    rw [heq] at h2
    linarith

/-- **Last-crossing family for the descending levels `ℓ₀ − i·π`, `i < m`**
(the left-segment version, sweep anchored at the RIGHT endpoint `b`).
If `ℓ₀ < φ b` and `φ a < ℓ₀ − (m−1)π`, then each level `ℓ₀ − i·π` (`i < m`)
has a last crossing `c i ∈ (a, b)`; the `c i` are strictly DEcreasing in `i`,
`φ (c i)` equals the level, and `φ` is strictly above the level on `(c i, b]`. -/
theorem exists_lastCrossing_family {φ : ℝ → ℝ} {a b ℓ₀ : ℝ} {m : ℕ}
    (hab : a ≤ b) (hcont : ContinuousOn φ (Set.Icc a b))
    (hℓ₀ : ℓ₀ < φ b) (hbot : φ a < ℓ₀ - ((m : ℝ) - 1) * Real.pi) :
    ∃ c : ℕ → ℝ,
      (∀ i, i < m → c i ∈ Set.Ioo a b) ∧
      (∀ i j, i < j → j < m → c j < c i) ∧
      (∀ i, i < m → φ (c i) = ℓ₀ - (i : ℝ) * Real.pi) ∧
      (∀ i, i < m → ∀ x ∈ Set.Ioc (c i) b, ℓ₀ - (i : ℝ) * Real.pi < φ x) := by
  have hpi := Real.pi_pos
  have key : ∀ i : ℕ, i < m →
      ∃ c ∈ Set.Ioo a b, φ c = ℓ₀ - (i : ℝ) * Real.pi ∧
        ∀ x ∈ Set.Ioc c b, ℓ₀ - (i : ℝ) * Real.pi < φ x := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) * Real.pi :=
      mul_nonneg (Nat.cast_nonneg i) hpi.le
    have hcast : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
    have hmul : (i : ℝ) * Real.pi ≤ ((m : ℝ) - 1) * Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) hpi.le
    have hlo : φ a < ℓ₀ - (i : ℝ) * Real.pi := by linarith
    have hhi : ℓ₀ - (i : ℝ) * Real.pi < φ b := by linarith
    exact exists_lastCrossing hab hcont hlo hhi
  choose! c hmem hval hmax using key
  refine ⟨c, hmem, ?_, hval, hmax⟩
  intro i j hij hjm
  have him : i < m := hij.trans hjm
  have hstep : (i : ℝ) * Real.pi < (j : ℝ) * Real.pi := by
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_right this hpi
  by_contra hle
  push Not at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- `c j` would lie strictly after the last crossing of the HIGHER level `i`
    have h1 : ℓ₀ - (i : ℝ) * Real.pi < φ (c j) :=
      hmax i him (c j) ⟨hlt, (hmem j hjm).2.le⟩
    have h2 : φ (c j) = ℓ₀ - (j : ℝ) * Real.pi := hval j hjm
    linarith
  · -- equal crossing points would force equal levels
    have h1 : φ (c i) = ℓ₀ - (i : ℝ) * Real.pi := hval i him
    have h2 : φ (c j) = ℓ₀ - (j : ℝ) * Real.pi := hval j hjm
    rw [← heq] at h2
    linarith

/-- **The first half-turn level strictly above `x`.**  There is
`ℓ = π/2 + kπ` (`k : ℤ`) with `x < ℓ ≤ x + π`. -/
theorem exists_first_halfturn_level (x : ℝ) :
    ∃ ℓ : ℝ, (∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) ∧
      x < ℓ ∧ ℓ ≤ x + Real.pi := by
  have hpi := Real.pi_pos
  set y : ℝ := (x - Real.pi / 2) / Real.pi with hy
  have hyπ : y * Real.pi = x - Real.pi / 2 := div_mul_cancel₀ _ hpi.ne'
  refine ⟨Real.pi / 2 + ((⌊y⌋ + 1 : ℤ) : ℝ) * Real.pi, ⟨⌊y⌋ + 1, rfl⟩, ?_, ?_⟩
  · have h1 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    have h3 : y * Real.pi < ((⌊y⌋ : ℝ) + 1) * Real.pi :=
      mul_lt_mul_of_pos_right h1 hpi
    push_cast
    linarith
  · have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have h3 : (⌊y⌋ : ℝ) * Real.pi ≤ y * Real.pi :=
      mul_le_mul_of_nonneg_right h1 hpi.le
    push_cast
    linarith

/-- **The last half-turn level strictly below `x`.**  There is
`ℓ = π/2 + kπ` (`k : ℤ`) with `x − π ≤ ℓ < x`. -/
theorem exists_last_halfturn_level (x : ℝ) :
    ∃ ℓ : ℝ, (∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) ∧
      ℓ < x ∧ x - Real.pi ≤ ℓ := by
  have hpi := Real.pi_pos
  set y : ℝ := (x - Real.pi / 2) / Real.pi with hy
  have hyπ : y * Real.pi = x - Real.pi / 2 := div_mul_cancel₀ _ hpi.ne'
  refine ⟨Real.pi / 2 + ((⌈y⌉ - 1 : ℤ) : ℝ) * Real.pi, ⟨⌈y⌉ - 1, rfl⟩, ?_, ?_⟩
  · have h1 : (⌈y⌉ : ℝ) < y + 1 := Int.ceil_lt_add_one y
    have h3 : ((⌈y⌉ : ℝ) - 1) * Real.pi < y * Real.pi :=
      mul_lt_mul_of_pos_right (by linarith) hpi
    push_cast
    linarith
  · have h1 : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
    have h3 : (y - 1) * Real.pi ≤ ((⌈y⌉ : ℝ) - 1) * Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) hpi.le
    push_cast
    linarith

/-- `cos` vanishes at every half-turn level `π/2 + kπ`. -/
theorem cos_eq_zero_of_halfturn {ℓ : ℝ}
    (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) : Real.cos ℓ = 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [Real.cos_eq_zero_iff]
  exact ⟨k, by ring⟩

/-- Shifting a half-turn level up by `n·π` (`n : ℕ`) stays a half-turn level
(so `cos` vanishes at every level of the ascending family). -/
theorem halfturn_add_nat_mul {ℓ : ℝ}
    (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) (n : ℕ) :
    ∃ k : ℤ, ℓ + (n : ℝ) * Real.pi = Real.pi / 2 + (k : ℝ) * Real.pi := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + n, by push_cast; ring⟩

/-- Shifting a half-turn level down by `n·π` (`n : ℕ`) stays a half-turn level
(so `cos` vanishes at every level of the descending family). -/
theorem halfturn_sub_nat_mul {ℓ : ℝ}
    (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) (n : ℕ) :
    ∃ k : ℤ, ℓ - (n : ℝ) * Real.pi = Real.pi / 2 + (k : ℝ) * Real.pi := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k - n, by push_cast; ring⟩

end TernaryGoldbach.RSBounds.BacklundFirstCrossing

