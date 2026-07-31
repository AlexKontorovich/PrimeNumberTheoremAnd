import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_dispatch

/-! # Verification of Table 11

Table 11 of \cite{BKLNW} lists, for each `b₀`, constants `B_k(b₀)` intended to satisfy
`|θ(x) - x| ≤ B_k(b₀) x / (log x)^k` on the whole range `x ∈ [e^{b₀}, e^K]`.

Unlike Table 10, whose entries track a single strip, a Table-11 entry is a maximum over
**two regimes**, split at `10^19`:

* below `10^19` the printed values (for small `b₀` and `k ≤ 3`) are the Corollary-9.1
  constants `C_{b₀,k}` of Table 12;
* above `10^19` they are the supremum of the Table-10 strip constants over the strips
  `b ≥ max b₀ (19 log 10)`.

The theorem originally encoded in `BKLNW.lean` compared the printed values against
`B_8_1' k b₀` — the Table-10 strip supremum taken from `b₀` itself — and is false: at
`b₀ = 20, k = 1` that supremum is `≈ 1.81e-3`, above the printed `1.6844e-3`
(Robby955, issue #1257), precisely because it sweeps in strips *below* `10^19` where the
smaller Corollary-9.1 constant is the one that applies. The statement below is the
split-domain repair, greenlit by the maintainer on 2026-07-07.

As with Table 10 (see `table_10_margin`), the printed values are attained only up to
rounding, so the bound carries a `table_11_margin` factor. The binding row is
`b₀ = 44, k = 1`, which needs `≥ 1.001983`; the repo's standard chained margin
`table_11_margin = table_10_margin * 1.001 = 1.003003001` clears it.

This file sits downstream of `BKLNW_table10_dispatch.lean` because the above-`10^19`
branch consumes `bklnw_table_10_verification`, while the Table-10 row files already
import `BKLNW.lean` (for `B_8_exact`). `bklnw_table_10_verification` lives here for the
same reason.
-/

namespace BKLNW

open Chebyshev Finset Real

/-- Recover a full Table-10 row from one of its `b`-entries. `table_10_entries` only
remembers the first component, but every consumer of a strip bound
(`bklnw_table_10_verification`) needs the row's five printed values as a function
`B : ℕ → ℝ`. -/
lemma table_10_row_of_entry {b : ℝ} (hb : b ∈ table_10_entries) :
    ∃ B : ℕ → ℝ, (b, B 1, B 2, B 3, B 4, B 5) ∈ table_10 := by
  simp only [List.mem_toFinset, List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  refine ⟨fun i ↦ if i = 1 then p.2.1 else if i = 2 then p.2.2.1 else
    if i = 3 then p.2.2.2.1 else if i = 4 then p.2.2.2.2.1 else p.2.2.2.2.2, ?_⟩
  simpa using hp

/-- The above-`10^19` engine, stated once and reused by every Table-11 row.

Given a Table-10 entry `b₀'` and a constant `C` dominating `B_k^{t10}(b) * table_10_margin`
over the whole Table-10 **suffix** `b ≥ b₀'`, the θ-bound with constant `C` holds on all of
`[e^{b₀'}, e^K]`.

This is the `B_8_exact` analogue of `bklnw_cor_8_1b`: the same coverage argument, but
routed through the exact Lemma-8 interval supremum rather than the Corollary-8.1 endpoint
surrogate `B_8_1`, because it is `B_8_exact` — not `B_8_1` — that Table 10's printed
values actually dominate (issue #1255). -/
lemma theta_bound_of_table_10_suffix (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 5) (b₀' C : ℝ)
    (hb₀' : b₀' ∈ table_10_entries)
    (hnum : ∀ b ∈ table_10_entries, ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 → b₀' ≤ b → Bt k * table_10_margin ≤ C) :
    ∀ x ∈ Set.Icc (exp b₀') (exp K), |θ x - x| ≤ C * x / (log x) ^ k := by
  intro x hx
  have hx_pos : 0 < x := (exp_pos b₀').trans_le hx.1
  have hlog_lower : b₀' ≤ log x := by simpa using log_le_log (exp_pos b₀') hx.1
  have hlog_upper : log x ≤ K := by simpa using log_le_log hx_pos hx.2
  obtain ⟨b, hb_in, hb₀_le, hb_le_logx, hlogx_le_next⟩ :=
    table_10_coverage b₀' (log x) hb₀' hlog_lower hlog_upper
  have hxb : exp b ≤ x := by simpa [exp_log hx_pos] using exp_le_exp.mpr hb_le_logx
  have hxnext : x ≤ exp (table_10_next b) := by
    simpa [exp_log hx_pos] using exp_le_exp.mpr hlogx_le_next
  have hb20 : (20 : ℝ) ≤ b := table_10_entries_ge_20 b hb_in
  have hbk : b ≥ max 7 (2 * (k : ℝ)) := by
    have hk5 : (k : ℝ) ≤ 5 := by exact_mod_cast hk.2
    exact max_le (by linarith) (by linarith)
  have hsub : |θ x - x| ≤ (B_8_exact k b (table_10_next b)) * x / (log x) ^ k :=
    bklnw_cor_8_1a_exact k b (table_10_next b) hk hbk x ⟨hxb, hxnext⟩
  obtain ⟨Bt, hBt⟩ := table_10_row_of_entry hb_in
  have hchain : B_8_exact k b (table_10_next b) ≤ C :=
    (bklnw_table_10_verification b Bt hBt k (Finset.mem_Icc.mpr hk)).trans
      (hnum b hb_in Bt hBt hb₀_le)
  have hx_gt_one : 1 < x := by
    have : (1 : ℝ) < exp b := by simpa using exp_strictMono (by linarith : (0 : ℝ) < b)
    exact this.trans_le hxb
  exact hsub.trans <|
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hchain hx_pos.le)
      (pow_nonneg (log_pos hx_gt_one).le k)

/-- **Numeric obligation, above `10^19`.** For each Table-11 row `(b₀, B 1, …, B 5)` and
each `k`, the Table-10 printed values over the suffix `b ≥ max b₀ (19 log 10)`, inflated by
`table_10_margin`, stay under the Table-11 value inflated by `table_11_margin`.

All quantities here are decimal literals: this is a pure rational-arithmetic check, with no
`log`/`exp` left in it. -/
lemma table_11_suffix_dominates (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) (k : ℕ) (hk : k ∈ Finset.Icc 1 5) :
    ∀ b ∈ table_10_entries, ∀ Bt : ℕ → ℝ, (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      max b₀ (19 * log 10) ≤ b → Bt k * table_10_margin ≤ B k * table_11_margin := by
  sorry

/-- **Numeric obligation, below `10^19`.** On `[e^{b₀}, 10^19]` the Table-11 entries are the
Corollary-9.1 constants `C_{b₀,k}` of Table 12, so this branch is discharged from
`bklnw_corollary_9_1` exactly as `bklnw_table_12_verification` is.

Vacuous for the rows with `b₀ ≥ 19 log 10`. -/
lemma table_11_below_bound (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) (k : ℕ) (hk : k ∈ Finset.Icc 1 5) :
    ∀ x ∈ Set.Icc (exp b₀) (exp K), x ≤ (10 : ℝ) ^ 19 →
      |θ x - x| ≤ B k * table_11_margin * x / (log x) ^ k := by
  sorry

/-- **Above-`10^19` dispatch.** `max b₀ (19 log 10)` is a Table-10 entry for every Table-11
row except the last (`b₀ = K = 25000`, whose domain is the single point `e^K`), so the
suffix engine applies verbatim. -/
lemma table_11_above_bound (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) (k : ℕ) (hk : k ∈ Finset.Icc 1 5)
    (hentry : max b₀ (19 * log 10) ∈ table_10_entries) :
    ∀ x ∈ Set.Icc (exp b₀) (exp K), (10 : ℝ) ^ 19 < x →
      |θ x - x| ≤ B k * table_11_margin * x / (log x) ^ k := by
  intro x hx hsplit
  have hk' : 1 ≤ k ∧ k ≤ 5 := Finset.mem_Icc.mp hk
  have hx19 : exp (19 * log 10) ≤ x := by
    have : exp (19 * log 10) = (10 : ℝ) ^ 19 := by
      rw [mul_comm, exp_mul, exp_log (by norm_num : (0:ℝ) < 10)]
      norm_num
    exact this ▸ hsplit.le
  have hx' : x ∈ Set.Icc (exp (max b₀ (19 * log 10))) (exp K) := by
    refine ⟨?_, hx.2⟩
    rcases max_choice b₀ (19 * log 10) with hm | hm <;> rw [hm]
    · exact hx.1
    · exact hx19
  have := theta_bound_of_table_10_suffix k hk' (max b₀ (19 * log 10))
    (B k * table_11_margin) hentry (table_11_suffix_dominates b₀ B h k hk) x hx'
  simpa [mul_div_assoc] using this

/-- Every Table-11 row starts at a `b₀` for which `max b₀ (19 log 10)` is a Table-10
entry — except the last row, `b₀ = K = 25000`, which is the right endpoint of the whole
range and is *not* a Table-10 entry (Table 10 stops at `24000`, with `K` supplied
separately by `table_10_bs`). Proved by enumerating the rows. -/
lemma table_11_entry_or_top (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) :
    max b₀ (19 * log 10) ∈ table_10_entries ∨ b₀ = (K : ℝ) := by
  sorry

/-- The last Table-11 row, `b₀ = K`, has the degenerate domain `[e^K, e^K] = {e^K}`. That
single point sits in the final Table-10 strip `[e^{24000}, e^{25000}]`, so the bound comes
from row `24000` directly rather than from the suffix engine. -/
lemma table_11_top_row_bound (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) (hb₀ : b₀ = (K : ℝ))
    (k : ℕ) (hk : k ∈ Finset.Icc 1 5) :
    ∀ x ∈ Set.Icc (exp b₀) (exp K),
      |θ x - x| ≤ B k * table_11_margin * x / (log x) ^ k := by
  sorry

@[blueprint
  "bklnw-table-11-verification"
  (title := "BKLNW Table 11 verification")
  (statement := /--  Verification of the entries of Table 11. -/)
  (proof := /-- The range $[e^{b_0},e^K]$ splits at $10^{19}$. Below $10^{19}$ the printed
entries are the Corollary 9.1 constants and the bound comes from Table 12. Above
$10^{19}$, Corollary 8.1 covers $x$ by a Table 10 strip $b \ge \max(b_0, 19\log 10)$, and
Table 10's verification bounds that strip's constant by its printed value; the residual
obligation is rational. -/)
  (latexEnv := "proposition")
  (discussion := 1257)]
theorem bklnw_table_11_verification (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) :
    ∀ k ∈ Finset.Icc 1 5, ∀ x ∈ Set.Icc (exp b₀) (exp K),
      |θ x - x| ≤ B k * table_11_margin * x / (log x) ^ k := by
  intro k hk x hx
  rcases table_11_entry_or_top b₀ B h with hentry | htop
  · rcases le_or_gt x ((10 : ℝ) ^ 19) with hsplit | hsplit
    · exact table_11_below_bound b₀ B h k hk x hx hsplit
    · exact table_11_above_bound b₀ B h k hk hentry x hx hsplit
  · exact table_11_top_row_bound b₀ B h htop k hk x hx

end BKLNW
