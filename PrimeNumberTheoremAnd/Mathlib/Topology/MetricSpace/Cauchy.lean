/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# A Cauchy-sequence criterion

A tail estimate controlled by a scalar sequence tending to zero gives a Cauchy sequence.
-/

@[expose] public section

open Filter
open scoped Topology

variable {α : Type*} [PseudoMetricSpace α]

/-- If `dist (s n) (s m) ≤ b m` for all `1 ≤ m ≤ n` and `b` tends to zero, then `s` is Cauchy. -/
theorem cauchySeq_of_dist_le_of_one_le {s : ℕ → α} {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hb₀ : Tendsto b atTop (𝓝 0))
    (h : ∀ m n, 1 ≤ m → m ≤ n → dist (s n) (s m) ≤ b m) : CauchySeq s := by
  refine (Metric.cauchySeq_iff).2 fun ε ε0 => ?_
  have h_ball : ∀ᶠ m in atTop, b m < ε / 2 := by
    have hdist : ∀ᶠ m in atTop, dist (b m) 0 < ε / 2 :=
      hb₀ (Metric.ball_mem_nhds 0 (half_pos ε0))
    refine hdist.mono ?_
    intro m hm
    have : |b m| < ε / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using hm
    simpa [abs_of_nonneg (hb m)] using this
  rcases eventually_atTop.1 h_ball with ⟨M, hMb⟩
  refine ⟨max M 1, ?_⟩
  intro n hn k hk
  set a := max M 1
  have ha1 : 1 ≤ a := le_max_right _ _
  have hn_a : a ≤ n := hn
  have hk_a : a ≤ k := hk
  have hb_a : b a < ε / 2 := hMb a (le_max_left _ _)
  have htri : dist (s n) (s k) ≤ dist (s n) (s a) + dist (s a) (s k) := dist_triangle _ _ _
  have h1 : dist (s n) (s a) ≤ b a := h a n ha1 hn_a
  have h2 : dist (s a) (s k) ≤ b a := by
    simpa [dist_comm] using h a k ha1 hk_a
  exact lt_of_le_of_lt (le_trans htri (add_le_add h1 h2)) (by linarith [hb_a])
