/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0; see licenses/Gersh-LICENSE.
Generalized to the exact circle-average Jensen budget by OpenAI, 2026.
-/
import RSBounds.BacklundPairedJensen
import RSBounds.BacklundFirstCrossing

/-!
# Constructive reflected crossings and the sharp Jensen budget

The reflected zero pairs are constructed from continuous argument levels.
They are not assumed. The radius need only exceed 3/4, so this result applies
at Rosser's radius 1.32. All boundary information remains an exact circle average.
-/

open Real Complex Metric MeasureTheory MeromorphicOn Set
open TernaryGoldbach.RSBounds.BacklundFirstCrossing
open TernaryGoldbach.RSBounds.BacklundPairedJensen

namespace TernaryGoldbach.RSBounds.BacklundPairedCrossing

/-- Every full half-turn of a continuous argument costs a doubled Jensen
weight, apart from an explicitly bounded reflection loss and two crossings. -/
theorem crossing_count_le {f : ℂ → ℂ} {R E : ℝ}
    (hR : 3 / 4 < R) (hE : 0 < E)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) {ψ : ℝ → ℝ}
    (hψcont : ContinuousOn ψ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
    (hψzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
      Real.cos (ψ x) = 0 → f (x : ℂ) = 0)
    (hψdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(ψ (1 / 2 + δ) - ψ (1 / 2)) - (ψ (1 / 2) - ψ (1 / 2 - δ))| ≤ E)
    {m₁ : ℕ} (hsweep : (m₁ : ℝ) * Real.pi < ψ (5 / 4) - ψ (1 / 2)) :
    (m₁ : ℝ) ≤ (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
      Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 1 + E / (2 * Real.pi) := by
  let J := circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
    Real.log ‖f (5 / 4 : ℂ)‖
  have hlog : 0 < Real.log (R / (3 / 4)) :=
    Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
  have hJ : 0 ≤ J := by
    have hh := BacklundJensen.zeroCount_mul_log_le_circleAverage
      (by norm_num : (0 : ℝ) < 3 / 4) hR hf hfc
    have hn : 0 ≤ BacklundJensen.zeroCount f (5 / 4 : ℂ) (3 / 4) := by
      unfold BacklundJensen.zeroCount
      apply finsum_nonneg
      intro u
      exact_mod_cast (hf.mono (closedBall_subset_closedBall hR.le)).divisor_nonneg u
    exact le_trans (mul_nonneg hn hlog.le) hh
  have hJnonneg : 0 ≤ J / (2 * Real.log (R / (3 / 4))) := div_nonneg hJ (by positivity)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the pairing offset `D = 1 + ⌈N·E/π⌉`
  set D : ℕ := 1 + ⌈E / Real.pi⌉₊ with hD_def
  have hD_cast : (D : ℝ) = 1 + (⌈E / Real.pi⌉₊ : ℝ) := by
    rw [hD_def]; push_cast; ring
  have hceil_ge : E
      ≤ (⌈E / Real.pi⌉₊ : ℝ) * Real.pi := by
    have h1 : E / Real.pi
        ≤ (⌈E / Real.pi⌉₊ : ℝ) := Nat.le_ceil _
    have h2 := mul_le_mul_of_nonneg_right h1 hπ.le
    rwa [div_mul_cancel₀ _ hπ.ne'] at h2
  have hDπ_ge : E + Real.pi ≤ (D : ℝ) * Real.pi := by
    have hexp : (D : ℝ) * Real.pi
        = Real.pi + (⌈E / Real.pi⌉₊ : ℝ) * Real.pi := by
      rw [hD_cast]; ring
    linarith [hceil_ge]
  have hD_le : (D : ℝ) ≤ 2 + E / Real.pi := by
    have h0 : (0 : ℝ) ≤ E / Real.pi := by positivity
    have h1 : (⌈E / Real.pi⌉₊ : ℝ)
        < E / Real.pi + 1 := Nat.ceil_lt_add_one h0
    linarith [hD_cast, h1]
  -- RIGHT family
  obtain ⟨ℓ₀, hℓ₀_ht, hℓ₀_gt, hℓ₀_le⟩ := exists_first_halfturn_level (ψ (1 / 2))
  have hsub_right : Set.Icc (1 / 2 : ℝ) (5 / 4 : ℝ)
      ⊆ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ) := Set.Icc_subset_Icc (by norm_num) le_rfl
  have htop : ℓ₀ + ((m₁ : ℝ) - 1) * Real.pi < ψ (5 / 4) := by
    have hexp : ℓ₀ + ((m₁ : ℝ) - 1) * Real.pi
        = ℓ₀ + (m₁ : ℝ) * Real.pi - Real.pi := by ring
    linarith [hℓ₀_le, hsweep, hexp]
  obtain ⟨c, hc_mem, hc_mono, hc_val, _hc_min⟩ :=
    exists_firstCrossing_family (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)
      (hψcont.mono hsub_right) hℓ₀_gt htop
  have hc_zero : ∀ i, i < m₁ → f (c i : ℂ) = 0 := by
    intro i hi
    have hmem := hc_mem i hi
    refine hψzero (c i) ⟨by linarith [hmem.1], hmem.2.le⟩ ?_
    rw [hc_val i hi]
    exact cos_eq_zero_of_halfturn (halfturn_add_nat_mul hℓ₀_ht i)
  have hc_inj : ∀ i j, i < m₁ → j < m₁ → c i = c j → i = j := by
    intro i j hi hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (ne_of_lt (hc_mono i j hij hj)) heq
    · exact (ne_of_lt (hc_mono j i hji hi)) heq.symm
  have hJmul : J / (2 * Real.log (R / (3 / 4))) * (2 * Real.log (R / (3 / 4))) = J :=
    div_mul_cancel₀ _ (by positivity)
  have hEdiv : E / (2 * Real.pi) = (E / Real.pi) / 2 := by ring
  by_cases hm₁D : m₁ ≤ D
  · have hm₁R : (m₁ : ℝ) ≤ (D : ℝ) := by exact_mod_cast hm₁D
    have hj := paired_jensen_with_unpaired_lower (k := m₁) (n := 0)
      (a := c) (b := fun _ => 0) hR hf hfc
      (fun i hi => hc_zero i (by simpa using hi))
      (fun i hi => (hc_mem i (by simpa using hi)).1.le)
      (fun i hi => (hc_mem i (by simpa using hi)).2)
      (fun i j hi hj he => hc_inj i j (by simpa using hi) (by simpa using hj) he)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hcnt : (m₁ : ℝ) ≤ J / (2 * Real.log (R / (3 / 4))) + (D : ℝ) / 2 := by
      have hm := mul_le_mul_of_nonneg_right hm₁R hlog.le
      dsimp [J] at hJmul ⊢
      norm_num only [Nat.cast_zero, zero_mul, zero_add] at hj
      nlinarith
    linarith [hD_le, hEdiv]
  · -- main branch: `D < m₁`
    have hDlt : D < m₁ := not_le.mp hm₁D
    set n' : ℕ := m₁ - D with hn'_def
    have hn'_cast : (n' : ℝ) = (m₁ : ℝ) - (D : ℝ) := by
      have h : n' + D = m₁ := by omega
      have h2 : (n' : ℝ) + (D : ℝ) = (m₁ : ℝ) := by exact_mod_cast h
      linarith
    have hn'π : (n' : ℝ) * Real.pi = (m₁ : ℝ) * Real.pi - (D : ℝ) * Real.pi := by
      rw [hn'_cast]; ring
    have hdelta34 := hψdelta (3 / 4) (by norm_num) le_rfl
    rw [show (1 / 2 : ℝ) + 3 / 4 = 5 / 4 by norm_num,
      show (1 / 2 : ℝ) - 3 / 4 = -1 / 4 by norm_num] at hdelta34
    have hVL34 : (m₁ : ℝ) * Real.pi - E
        < ψ (1 / 2) - ψ (-1 / 4) := by
      have h2 := (abs_le.mp hdelta34).2
      linarith [hsweep]
    obtain ⟨ℓ'₀, hℓ'₀_ht, hℓ'₀_lt, hℓ'₀_ge⟩ := exists_last_halfturn_level (ψ (1 / 2))
    have hsub_left : Set.Icc (-1 / 4 : ℝ) (1 / 2 : ℝ)
        ⊆ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ) := Set.Icc_subset_Icc le_rfl (by norm_num)
    have hbot : ψ (-1 / 4) < ℓ'₀ - ((n' : ℝ) - 1) * Real.pi := by
      have hexp : ℓ'₀ - ((n' : ℝ) - 1) * Real.pi
          = ℓ'₀ - (n' : ℝ) * Real.pi + Real.pi := by ring
      linarith [hℓ'₀_ge, hDπ_ge, hVL34, hn'π, hexp]
    obtain ⟨l, hl_mem, hl_anti, hl_val, hl_max⟩ :=
      exists_lastCrossing_family (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 2)
        (hψcont.mono hsub_left) hℓ'₀_lt hbot
    have hl_zero : ∀ j, j < n' → f (l j : ℂ) = 0 := by
      intro j hj
      have hmem := hl_mem j hj
      refine hψzero (l j) ⟨hmem.1.le, by linarith [hmem.2]⟩ ?_
      rw [hl_val j hj]
      exact cos_eq_zero_of_halfturn (halfturn_sub_nat_mul hℓ'₀_ht j)
    have hinterlace : ∀ k, k < n' → 1 - c (k + D) ≤ l k := by
      intro k hk
      have hkD : k + D < m₁ := by omega
      have hmemc := hc_mem (k + D) hkD
      set δ : ℝ := c (k + D) - 1 / 2 with hδ_def
      have hδ_pos : 0 < δ := by rw [hδ_def]; linarith [hmemc.1]
      have hδ_le : δ ≤ 3 / 4 := by rw [hδ_def]; linarith [hmemc.2]
      have h12δ : (1 / 2 : ℝ) + δ = c (k + D) := by rw [hδ_def]; ring
      have hd := hψdelta δ hδ_pos hδ_le
      rw [h12δ] at hd
      have hval := hc_val (k + D) hkD
      have hcastπ : ((k + D : ℕ) : ℝ) * Real.pi
          = (k : ℝ) * Real.pi + (D : ℝ) * Real.pi := by push_cast; ring
      have hVL_gt : ((k : ℝ) + 1) * Real.pi < ψ (1 / 2) - ψ (1 / 2 - δ) := by
        have h2 := (abs_le.mp hd).2
        linarith [hℓ₀_gt, hDπ_ge, hval, hcastπ]
      have hlt : ψ (1 / 2 - δ) < ℓ'₀ - (k : ℝ) * Real.pi := by
        linarith [hVL_gt, hℓ'₀_ge]
      by_contra hcon
      push Not at hcon
      have h1c : (1 : ℝ) - c (k + D) = 1 / 2 - δ := by rw [hδ_def]; ring
      have hxmem : (1 / 2 - δ : ℝ) ∈ Set.Ioc (l k) (1 / 2 : ℝ) :=
        Set.mem_Ioc.mpr ⟨by rw [← h1c]; exact hcon, by linarith⟩
      have hgt := hl_max k hk (1 / 2 - δ) hxmem
      linarith [hlt, hgt]
    have ha_inj : ∀ i j, i < n' → j < n' → c (i + D) = c (j + D) → i = j := by
      intro i j hi hj heq
      by_contra hne'
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact absurd heq (ne_of_lt (hc_mono (i + D) (j + D) (by omega) (by omega)))
      · have hgt : j < i := lt_of_le_of_ne hge (Ne.symm hne')
        exact absurd heq.symm
          (ne_of_lt (hc_mono (j + D) (i + D) (by omega) (by omega)))
    have ha'_inj : ∀ i j, i < n' → j < n' → l i = l j → i = j := by
      intro i j hi hj heq
      by_contra hne'
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact absurd heq (ne_of_gt (hl_anti i j hlt hj))
      · have hgt : j < i := lt_of_le_of_ne hge (Ne.symm hne')
        exact absurd heq.symm (ne_of_gt (hl_anti j i hgt hi))
    have hdisj : ∀ i j, i < n' → j < n' → c (i + D) ≠ l j := by
      intro i j hi hj
      have h1 : (1 / 2 : ℝ) < c (i + D) := (hc_mem (i + D) (by omega)).1
      have h2 : l j < 1 / 2 := (hl_mem j hj).2
      exact ne_of_gt (lt_trans h2 h1)
    have hdisj_all : ∀ i j, i < D + n' → j < n' → c i ≠ l j := by
      intro i j hi hj
      have h1 := (hc_mem i (by omega)).1
      have h2 := (hl_mem j hj).2
      exact ne_of_gt (lt_trans h2 h1)
    have hj := paired_jensen_with_unpaired_lower (k := D) (n := n')
      (a := c) (b := l) hR hf hfc
      (fun i hi => hc_zero i (by omega))
      (fun i hi => ((hc_mem i (by omega)).1).le)
      (fun i hi => (hc_mem i (by omega)).2)
      (fun i j hi hj he => hc_inj i j (by omega) (by omega) he)
      hl_zero hinterlace (fun i hi => ((hl_mem i hi).2).le) ha'_inj hdisj_all
    have hcnt : (m₁ : ℝ) ≤ J / (2 * Real.log (R / (3 / 4))) + (D : ℝ) / 2 := by
      dsimp [J] at hJmul ⊢
      nlinarith [hj, hn'_cast]
    linarith [hcnt, hD_le, hEdiv]

/-- Convert the bound on all fully crossed half-turns to an absolute argument
bound; the sole additional cost is one half-turn. -/
theorem abs_argument_le {f : ℂ → ℂ} {R E : ℝ}
    (hR : 3 / 4 < R) (hE : 0 < E)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) {ψ : ℝ → ℝ}
    (hψcont : ContinuousOn ψ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
    (hψzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
      Real.cos (ψ x) = 0 → f (x : ℂ) = 0)
    (hψdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(ψ (1 / 2 + δ) - ψ (1 / 2)) - (ψ (1 / 2) - ψ (1 / 2 - δ))| ≤ E) :
    |ψ (5 / 4) - ψ (1 / 2)| / Real.pi ≤
      (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
        Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 2 + E / (2 * Real.pi) := by
  let B := (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
    Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 1 + E / (2 * Real.pi)
  have hc (m : ℕ) (hm : (m : ℝ) * Real.pi < |ψ (5 / 4) - ψ (1 / 2)|) : (m : ℝ) ≤ B := by
    rcases lt_abs.mp hm with hp | hn
    · exact crossing_count_le hR hE hf hfc hψcont hψzero hψdelta hp
    · apply crossing_count_le hR hE hf hfc hψcont.neg
        (ψ := fun x => -ψ x)
      · intro x hx hz
        exact hψzero x hx (by simpa only [Real.cos_neg] using hz)
      · intro δ hδ0 hδ1
        convert hψdelta δ hδ0 hδ1 using 1
        rw [show (-ψ (1 / 2 + δ) - -ψ (1 / 2)) -
            (-ψ (1 / 2) - -ψ (1 / 2 - δ)) =
            -((ψ (1 / 2 + δ) - ψ (1 / 2)) -
              (ψ (1 / 2) - ψ (1 / 2 - δ))) by ring, abs_neg]
      · linarith
  by_cases hz : |ψ (5 / 4) - ψ (1 / 2)| = 0
  · have hlog : 0 < Real.log (R / (3 / 4)) := Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
    have hh := BacklundJensen.zeroCount_mul_log_le_circleAverage
      (by norm_num : (0 : ℝ) < 3 / 4) hR hf hfc
    have hn : 0 ≤ BacklundJensen.zeroCount f (5 / 4 : ℂ) (3 / 4) := by
      unfold BacklundJensen.zeroCount
      apply finsum_nonneg
      intro u
      exact_mod_cast (hf.mono (closedBall_subset_closedBall hR.le)).divisor_nonneg u
    have hj : 0 ≤ (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
        Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) :=
      div_nonneg ((mul_nonneg hn hlog.le).trans hh) (by positivity)
    rw [hz, zero_div]
    positivity
  have hpos : 0 < |ψ (5 / 4) - ψ (1 / 2)| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
  have hB : 0 ≤ B := by simpa only [Nat.cast_zero] using hc 0 (by simpa using hpos)
  have hfinal : |ψ (5 / 4) - ψ (1 / 2)| / Real.pi ≤ B + 1 := by
    by_contra hn
    have hlt : B + 1 < |ψ (5 / 4) - ψ (1 / 2)| / Real.pi := lt_of_not_ge hn
    have hfl := Nat.floor_le (show 0 ≤ B + 1 by linarith)
    have hfr := Nat.lt_floor_add_one (B + 1)
    have hsw : (⌊B + 1⌋₊ : ℝ) * Real.pi < |ψ (5 / 4) - ψ (1 / 2)| := by
      apply (lt_div_iff₀ Real.pi_pos).mp
      exact hfl.trans_lt hlt
    linarith [hc ⌊B + 1⌋₊ hsw]
  dsimp [B] at hfinal
  linarith

end TernaryGoldbach.RSBounds.BacklundPairedCrossing
