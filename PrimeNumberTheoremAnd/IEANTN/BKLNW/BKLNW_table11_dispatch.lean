import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table11_suffix

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

So the minimal viable margin is exactly `table_10_margin` itself, and
`table_11_margin = table_10_margin` would already suffice. The value used here is the
repo's standard chained one, `table_11_margin = table_10_margin * 1.001 = 1.003003001`
(mirroring `table_10_margin = table_8_margin * 1.001`): it keeps the per-table chaining
convention and leaves headroom, since the tight choice would make the `b₀ = 20, k = 4`
obligation an exact equality and so break on any re-rounding of a table entry. The cost is
a constant 0.1% weaker than strictly necessary.

This file sits downstream of `BKLNW_table10_dispatch.lean` because the above-`10^19`
branch consumes `bklnw_table_10_verification`, while the Table-10 row files already
import `BKLNW.lean` (for `B_8_exact`). `bklnw_table_10_verification` lives here for the
same reason.

File layout: the dispatch/suffix split is the intended long-term shape, not scaffolding to
be inlined later. It mirrors Table 10, where `BKLNW_table10_dispatch.lean` is a generated
dispatch sitting over the row certificates of `BKLNW_table10_rows_*.lean`; here
`BKLNW_table11_suffix.lean` holds the generated certificate chain and this file holds the
hand-written statement and dispatch. The 263 `table_11_suffix_from_<b>` lemmas are data
rather than boilerplate — each carries the running suffix maximum of the five printed
columns at its own node — and they are consumed one node at a time because the grid's
successor function is itself encoded upstream as 287 separate `table_10_next_cert_<b>`
lemmas (`BKLNW_table10_next.lean`). Collapsing the chain into a single induction over the
grid would mean re-encoding Table 10, i.e. changing merged code, so it is deliberately out
of scope here.

Axiom surface: nothing here is `sorry`. The generated chain in `BKLNW_table11_suffix.lean`
together with its dispatch (`table_11_suffix_dominates`, `table_11_top_row_dominates`)
needs exactly `propext` / `Classical.choice` / `Quot.sound` plus two `native_decide`
axioms, and those two come from the pre-existing `LogTables.log_10_gt` / `log_10_lt`:
placing the `10^19` node `19 log 10` on the Table-10 grid needs numeric bounds on `log 10`.
No new `native_decide` obligation is introduced here — the grid walk itself is clean
(`eq_or_ge_next` needs none), since it only compares printed values against printed values.
The theorem as a whole still reports `sorryAx`, but
entirely from pre-existing upstream stubs it inherits, on both branches: `cor_5_1` (via
`bklnw_cor_8_1a_exact`) above `10^19`, and `Buthe.theorem_2a` / `2c` (via `bklnw_eq_3_17`)
below it. `bklnw_table_10_verification` already carried the same contingency.
-/

namespace BKLNW

open Chebyshev Finset Real

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

/-- Below `10^19` the absolute value collapses to a single side: `bklnw_eq_3_17` (from
Buthe) gives `θ x < x - 0.05 √x < x` throughout. This is what makes the one-sided
Corollary 9.1 sufficient here — on its own it bounds only `x - θ x`. -/
lemma abs_theta_sub_of_le_1e19 {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    |θ x - x| = x - θ x := by
  have h := bklnw_eq_3_17 hx1 hx2
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  rw [abs_of_nonpos (by linarith)]; ring

/-- Table-11 rows starting above the `10^19` node have an empty below-`10^19` range. -/
private lemma below_vacuous {b₀ x : ℝ} (hb₀ : 19 * log 10 < b₀)
    (hx : exp b₀ ≤ x) (hlt : x < (10 : ℝ) ^ 19) : False := by
  have h19 : ((10 : ℝ) ^ 19) = exp (19 * log 10) := by
    rw [mul_comm, exp_mul, exp_log (by norm_num : (0 : ℝ) < 10)]; norm_num
  rw [h19] at hlt
  exact absurd (exp_lt_exp.mp (lt_of_le_of_lt hx hlt)) (by linarith)

/-- The below-`10^19` engine: Corollary 9.1 with a Table-12 row, turned into a bound on
`|θ x - x|` by `abs_theta_sub_of_le_1e19`, then widened to the Table-11 entry. -/
lemma theta_bound_below_engine (b₀ c C M : ℝ) (Cb B : ℕ → ℝ)
    (ht12 : (b₀, Cb 1, Cb 2, Cb 3, Cb 4, Cb 5, c, C, M) ∈ BKLNW.table_12)
    (hb₀ : (20 : ℝ) ≤ b₀)
    (h1 : Cb 1 ≤ B 1 * table_11_margin) (h2 : Cb 2 ≤ B 2 * table_11_margin)
    (h3 : Cb 3 ≤ B 3 * table_11_margin) (h4 : Cb 4 ≤ B 4 * table_11_margin)
    (h5 : Cb 5 ≤ B 5 * table_11_margin)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 5) :
    ∀ x ∈ Set.Icc (exp b₀) (exp K), x < (10 : ℝ) ^ 19 →
      |θ x - x| ≤ B k * table_11_margin * x / (log x) ^ k := by
  obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
  intro x hx hlt
  have hxpos : (0 : ℝ) < x := (exp_pos b₀).trans_le hx.1
  have hlogx : b₀ ≤ log x := by simpa using log_le_log (exp_pos b₀) hx.1
  have hx1 : (1 : ℝ) ≤ x := by
    have : (1 : ℝ) < exp b₀ := by simpa using exp_strictMono (by linarith : (0 : ℝ) < b₀)
    linarith [hx.1]
  have hpow : (0 : ℝ) < (log x) ^ k := pow_pos (by linarith) k
  have hq : (0 : ℝ) ≤ x / (log x) ^ k := le_of_lt (div_pos hxpos hpow)
  have hcor := bklnw_corollary_9_1_explicit b₀ c C M Cb ht12 x ⟨hx.1, hlt⟩ k hk
  rw [abs_theta_sub_of_le_1e19 hx1 hlt.le]
  have hstep : x - θ x ≤ Cb k * x / (log x) ^ k := by
    rw [ge_iff_le, neg_mul, neg_div, neg_le] at hcor; linarith
  refine hstep.trans ?_
  rw [mul_div_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hq
  interval_cases k <;> assumption

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
  have hgt := LogTables.log_10_gt
  have hlt := LogTables.log_10_lt
  simp only [table_11, List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at h
  casesm* _ ∨ _
  all_goals try contradiction
  all_goals obtain ⟨rfl, e1, e2, e3, e4, e5⟩ := h
  · exact theta_bound_below_engine 20 0.8 0.81 5e10
      (fun i => if i = 1 then 1.68440e-3 else if i = 2 then 3.36880e-2 else
        if i = 3 then 6.73750e-1 else if i = 4 then 1.34750e1 else 2.69500e2) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 21 0.8 0.81 5e10
      (fun i => if i = 1 then 1.06840e-3 else if i = 2 then 2.24350e-2 else
        if i = 3 then 4.71140e-1 else if i = 4 then 9.89390e0 else 2.07780e2) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 22 0.8 0.81 5e10
      (fun i => if i = 1 then 6.76540e-4 else if i = 2 then 1.48840e-2 else
        if i = 3 then 3.27450e-1 else if i = 4 then 7.20380e0 else 1.58490e2) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 23 0.8 0.81 5e10
      (fun i => if i = 1 then 4.27800e-4 else if i = 2 then 9.83920e-3 else
        if i = 3 then 2.26310e-1 else if i = 4 then 5.20500e0 else 1.19720e2) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 24 0.8 0.81 5e10
      (fun i => if i = 1 then 2.70120e-4 else if i = 2 then 6.48290e-3 else
        if i = 3 then 1.55590e-1 else if i = 4 then 3.73410e0 else 8.96190e1) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 25 0.88 0.86 32e12
      (fun i => if i = 1 then 1.750020e-4 else if i = 2 then 4.375050e-3 else
        if i = 3 then 1.093770e-1 else if i = 4 then 2.734410e0 else 6.836010e1) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 26 0.88 0.86 32e12
      (fun i => if i = 1 then 1.10220e-4 else if i = 2 then 2.86560e-3 else
        if i = 3 then 7.45050e-2 else if i = 4 then 1.93720e0 else 5.03650e1) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 27 0.88 0.86 32e12
      (fun i => if i = 1 then 6.93270e-5 else if i = 2 then 1.87190e-3 else
        if i = 3 then 5.05400e-2 else if i = 4 then 1.36460e0 else 3.68430e1) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 28 0.88 0.86 32e12
      (fun i => if i = 1 then 4.35580e-5 else if i = 2 then 1.21970e-3 else
        if i = 3 then 3.41500e-2 else if i = 4 then 9.56180e-1 else 2.67730e1) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 29 0.88 0.86 32e12
      (fun i => if i = 1 then 2.73380e-5 else if i = 2 then 7.92780e-4 else
        if i = 3 then 2.29910e-2 else if i = 4 then 6.66730e-1 else 1.93360e1) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 30 0.88 0.86 32e12
      (fun i => if i = 1 then 1.71400e-5 else if i = 2 then 5.14180e-4 else
        if i = 3 then 1.54260e-2 else if i = 4 then 4.62760e-1 else 1.38830e1) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact theta_bound_below_engine 43 0.94 0.94 1e19
      (fun i => if i = 1 then 3.83820e-8 else if i = 2 then 1.65050e-6 else
        if i = 3 then 7.09680e-5 else if i = 4 then 3.05170e-3 else 1.31220e-1) B
      (by norm_num [table_12]) (by norm_num)
      (by rw [e1]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e2]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e3]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e4]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      (by rw [e5]; norm_num [table_11_margin, table_10_margin, BKLNW_app.table_8_margin])
      k hk
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim
  · exact fun x hx hx19 ↦ (below_vacuous (by linarith) hx.1 hx19).elim

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
    max b₀ (19 * log 10) ∈ table_10_entries ∨
      (b₀ = (K : ℝ) ∧ B 1 = 1.3804e-43 ∧ B 2 = 3.4508e-39 ∧ B 3 = 8.6269e-35 ∧
        B 4 = 2.1568e-30 ∧ B 5 = 5.3919e-26) := by
  have hgt := LogTables.log_10_gt
  have hlt := LogTables.log_10_lt
  simp only [table_11, List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at h
  casesm* _ ∨ _
  all_goals try contradiction
  all_goals obtain ⟨rfl, _e1, _e2, _e3, _e4, _e5⟩ := h
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
  · exact Or.inr ⟨by norm_num [K], _e1, _e2, _e3, _e4, _e5⟩

/-- The last Table-11 row, `b₀ = K`, has the degenerate domain `[e^K, e^K] = {e^K}`. That
single point sits in the final Table-10 strip `[e^{24000}, e^{25000}]`, so the bound comes
from row `24000` directly rather than from the suffix engine. -/
lemma table_11_top_row_bound (b₀ : ℝ) (B : ℕ → ℝ) (hb₀ : b₀ = (K : ℝ))
    (v1 : B 1 = 1.3804e-43) (v2 : B 2 = 3.4508e-39) (v3 : B 3 = 8.6269e-35)
    (v4 : B 4 = 2.1568e-30) (v5 : B 5 = 5.3919e-26)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 5) :
    ∀ x ∈ Set.Icc (exp b₀) (exp K),
      |θ x - x| ≤ B k * table_11_margin * x / (log x) ^ k := by
  intro x hx
  have hx' : x ∈ Set.Icc (exp 24000) (exp K) :=
    ⟨le_trans (exp_le_exp.mpr (by norm_num [K] : (24000 : ℝ) ≤ (K : ℝ))) (hb₀ ▸ hx.1), hx.2⟩
  have := theta_bound_of_table_10_suffix k (Finset.mem_Icc.mp hk) 24000
    (B k * table_11_margin) (mem_entries_idx 286 (by norm_num) _ rfl)
    (table_11_top_row_dominates B k hk v1 v2 v3 v4 v5) x hx'
  simpa [mul_div_assoc] using this

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
  · obtain ⟨htop, v1, v2, v3, v4, v5⟩ := htop
    exact table_11_top_row_bound b₀ B htop v1 v2 v3 v4 v5 k hk x hx

end BKLNW
