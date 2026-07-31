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
rounding, so the bound carries a `table_11_margin` factor, and it is genuinely needed: the
printed values are *not* upper bounds for the unrounded quantities. Sweeping every
obligation, the tightest are

* above `10^19`: `b₀ = 20, k = 4`, where the Table-10 suffix supremum and the Table-11
  entry are the same printed number `5.7184e1`, so the requirement is exactly
  `table_10_margin ≤ table_11_margin`;
* below `10^19`: `b₀ = 25, k = 1`, needing `≥ 1.000107` (Table 12's row 25 was itself
  corrected upward from the paper — see the correction note on `table_12`).

The repo's standard chained margin
`table_11_margin = table_10_margin * 1.001 = 1.003003001` clears both.

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

/-- Membership of a Table-10 row's `b`-entry in `table_10_entries`, addressed by list
index. Addressing rows by index (rather than searching the 287-element list with `simp`)
is what keeps the per-row certificates below cheap; it is the same device
`table_10_values_of_mem_aux` uses. -/
lemma mem_entries_get (N : ℕ) (hN : N < table_10.length) :
    (table_10.get ⟨N, hN⟩).1 ∈ table_10_entries := by
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨_, List.get_mem _ _, rfl⟩

/-- `mem_entries_get` with the row contents supplied by `rfl` at the call site. -/
lemma mem_entries_idx (N : ℕ) (hN : N < 287) (b : ℝ)
    (hb : (table_10.get ⟨N, table_10_length_eq ▸ hN⟩).1 = b) : b ∈ table_10_entries :=
  hb ▸ mem_entries_get N _

/-- `10^19 = e^{19 log 10}` is itself a Table-10 grid node (row 24), sitting between the
rows `43` and `44`. This is what makes the split at `10^19` land on a strip boundary
instead of cutting a strip in half. -/
lemma mem_entries_19log10 : (19 : ℝ) * log 10 ∈ table_10_entries :=
  mem_entries_idx 24 (by norm_num) _ rfl

lemma table_10_next_le_of_mem {b b' : ℝ} (hb' : b' ∈ table_10_bs) (hlt : b < b') :
    table_10_next b ≤ b' := by
  have hmem : b' ∈ table_10_bs.filter (b < ·) := Finset.mem_filter.mpr ⟨hb', hlt⟩
  rw [table_10_next_eq_min' b ⟨b', hmem⟩]
  exact Finset.min'_le _ _ hmem

/-- **Gap principle.** There is no Table-10 entry strictly between `b` and
`table_10_next b` — immediate from `table_10_next` being an infimum. So an entry `≥ b` is
either `b` itself or already at the next grid node.

This is what makes a suffix bound over the 287-row grid provable by a *chain* of 287 cheap
steps (each row versus the next) instead of a quadratic sweep of every row against every
Table-11 row. -/
lemma eq_or_ge_next {b b' : ℝ} (hb' : b' ∈ table_10_entries) (hge : b ≤ b') :
    b' = b ∨ table_10_next b ≤ b' := by
  rcases eq_or_lt_of_le hge with h | h
  · exact Or.inl h.symm
  · exact Or.inr (table_10_next_le_of_mem (Finset.mem_union_left _ hb') h)

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

The absolute value collapses to one side here: `bklnw_eq_3_17` gives `θ x < x` throughout
`x ≤ 10^19`, so `|θ x - x| = x - θ x`, which is exactly what Corollary 9.1 bounds. (Cor 9.1
is a one-sided statement — it has no upper bound on `θ x - x` — so without `eq_3_17` this
branch would not close.)

Vacuous for the rows with `b₀ ≥ 19 log 10`. -/
lemma table_11_below_bound (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) (k : ℕ) (hk : k ∈ Finset.Icc 1 5) :
    ∀ x ∈ Set.Icc (exp b₀) (exp K), x < (10 : ℝ) ^ 19 →
      |θ x - x| ≤ B k * table_11_margin * x / (log x) ^ k := by
  sorry

/-- **Above-`10^19` dispatch.** `max b₀ (19 log 10)` is a Table-10 entry for every Table-11
row except the last (`b₀ = K = 25000`, whose domain is the single point `e^K`), so the
suffix engine applies verbatim. -/
lemma table_11_above_bound (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) (k : ℕ) (hk : k ∈ Finset.Icc 1 5)
    (hentry : max b₀ (19 * log 10) ∈ table_10_entries) :
    ∀ x ∈ Set.Icc (exp b₀) (exp K), (10 : ℝ) ^ 19 ≤ x →
      |θ x - x| ≤ B k * table_11_margin * x / (log x) ^ k := by
  intro x hx hsplit
  have hk' : 1 ≤ k ∧ k ≤ 5 := Finset.mem_Icc.mp hk
  have hx19 : exp (19 * log 10) ≤ x := by
    have : exp (19 * log 10) = (10 : ℝ) ^ 19 := by
      rw [mul_comm, exp_mul, exp_log (by norm_num : (0:ℝ) < 10)]
      norm_num
    exact this ▸ hsplit
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
  have hgt := LogTables.log_10_gt
  have hlt := LogTables.log_10_lt
  simp only [table_11, List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at h
  casesm* _ ∨ _
  all_goals try contradiction
  all_goals obtain ⟨rfl, -⟩ := h
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (20:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (21:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (22:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (23:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (24:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (25:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (26:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (27:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (28:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (29:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (30:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_right (by linarith : (43:ℝ) ≤ 19 * log 10)]
    exact mem_entries_19log10
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 44)]
    exact mem_entries_idx 25 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 45)]
    exact mem_entries_idx 26 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 46)]
    exact mem_entries_idx 27 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 47)]
    exact mem_entries_idx 28 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 54)]
    exact mem_entries_idx 35 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 55)]
    exact mem_entries_idx 36 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 56)]
    exact mem_entries_idx 37 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 2275)]
    exact mem_entries_idx 84 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 2300)]
    exact mem_entries_idx 85 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 2325)]
    exact mem_entries_idx 86 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 2350)]
    exact mem_entries_idx 87 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 2375)]
    exact mem_entries_idx 88 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 2400)]
    exact mem_entries_idx 89 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 9800)]
    exact mem_entries_idx 241 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 9900)]
    exact mem_entries_idx 242 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 10000)]
    exact mem_entries_idx 243 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 11000)]
    exact mem_entries_idx 253 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 12000)]
    exact mem_entries_idx 263 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 13000)]
    exact mem_entries_idx 273 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 14000)]
    exact mem_entries_idx 276 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 15000)]
    exact mem_entries_idx 277 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 16000)]
    exact mem_entries_idx 278 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 17000)]
    exact mem_entries_idx 279 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 18000)]
    exact mem_entries_idx 280 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 19000)]
    exact mem_entries_idx 281 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 20000)]
    exact mem_entries_idx 282 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 21000)]
    exact mem_entries_idx 283 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 22000)]
    exact mem_entries_idx 284 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 23000)]
    exact mem_entries_idx 285 (by norm_num) _ rfl
  · refine Or.inl ?_
    rw [max_eq_left (by linarith : (19:ℝ) * log 10 ≤ 24000)]
    exact mem_entries_idx 286 (by norm_num) _ rfl
  · exact Or.inr (by norm_num [K])

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
  · rcases lt_or_ge x ((10 : ℝ) ^ 19) with hsplit | hsplit
    · exact table_11_below_bound b₀ B h k hk x hx hsplit
    · exact table_11_above_bound b₀ B h k hk hentry x hx hsplit
  · exact table_11_top_row_bound b₀ B h htop k hk x hx

end BKLNW
