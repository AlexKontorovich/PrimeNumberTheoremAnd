import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import LeanCert.Tactic.IntervalAuto
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_a2_bounds

/-!
# Table 10 (#1255): the Lemma-8 `B` vs the Corollary-8.1 endpoint `B_8_1`

This file pins down, for the first row of Table 10 (`b = 20`, `k = 5`), the
statement mismatch identified in issue #1255 and confirmed by the maintainers:

* `table10_verification_statement_false` — the *current* target of
  `bklnw_table_10_verification`, which bounds the Corollary-8.1 endpoint
  quantity `B_8_1` (eq. (3.13)), is **false**: at `b = 20` the endpoint value
  `B_8_1 5 20 21 ≈ 326.96` exceeds the listed `291.60`.

* `table_10_row20_k5` — for the `k = 5` column, the *exact* Lemma-8 supremum `B`
  (eq. (3.10)) over `[e^20, e^21]` **does** satisfy the listed `k = 5` value:
  `B_8_exact 5 20 21 ≤ 291.60`. Only `k = 5` is claimed here: at the bare listed
  values `k = 3, 4, 5` hold, while for `k = 1, 2` the bare entries *undershoot* the
  exact-B supremum (by ~1.9e-8 and ~3.8e-7) and so need the repo's table margin —
  this is deliberately a one-column anchor, not a whole-row claim.

Together these formalize the (3.13)-vs-(3.10) confusion noted in the thread:
Table 10 tracks the Lemma-8 `B`, not the Corollary-8.1 `B_8_1`.

Numeric steps are discharged by `interval_decide` (LeanCert); `#print axioms`
therefore lists `native_decide` plus a `sorryAx` **inherited from the in-progress
upstream BKLNW analytic inputs** — it enters only via `Inputs.default`, whose
proof fields `hε`, `hx₁'`, `hα` reduce to `BKLNW_app.theorem_2` (the ψ−x bound),
`buthe_eq_1_7`/`Buthe.theorem_2c` (the small-`x` θ bound), and `cor_2_1`, all
still on `sorry` upstream (`#print axioms` on each shows `sorryAx`). **No
new `sorry` is introduced here**, and the `sorryAx` is not load-bearing for the
two numeric inequalities themselves: their `interval_decide` cores
(`table10_row20_endpoint_lower_data`, `G_le_table`) are `sorryAx`-free. The
honest status is therefore *"proved modulo the upstream BKLNW analytic-NT
results,"* not *axiom-clean.*
-/

open Real Set Finset

namespace BKLNW

/-! ## Numeric majorant `G` and its convexity bound on [20,21] (self-contained). -/

noncomputable def expT   (c y : ℝ) : ℝ := y ^ 5 * Real.exp (-(c * y))
noncomputable def expTd  (c y : ℝ) : ℝ := (5 * y ^ 4 - c * y ^ 5) * Real.exp (-(c * y))
noncomputable def expTdd (c y : ℝ) : ℝ := (c ^ 2 * y ^ 5 - 10 * c * y ^ 4 + 20 * y ^ 3) * Real.exp (-(c * y))

lemma expT_hasDerivAt (c y : ℝ) : HasDerivAt (expT c) (expTd c y) y := by
  unfold expT expTd
  have hp : HasDerivAt (fun u : ℝ => u ^ 5) (5 * y ^ 4) y := by simpa using hasDerivAt_pow 5 y
  have hlin : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y := ((hasDerivAt_id y).const_mul c).neg
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(c * u))) (Real.exp (-(c * y)) * (-(c * 1))) y := hlin.exp
  convert hp.mul he using 1
  ring

lemma expTd_hasDerivAt (c y : ℝ) : HasDerivAt (expTd c) (expTdd c y) y := by
  unfold expTd expTdd
  have hP : HasDerivAt (fun u : ℝ => 5 * u ^ 4 - c * u ^ 5) (20 * y ^ 3 - 5 * c * y ^ 4) y := by
    have h4 : HasDerivAt (fun u : ℝ => u ^ 4) (4 * y ^ 3) y := by simpa using hasDerivAt_pow 4 y
    have h5 : HasDerivAt (fun u : ℝ => u ^ 5) (5 * y ^ 4) y := by simpa using hasDerivAt_pow 5 y
    convert (h4.const_mul (5 : ℝ)).sub (h5.const_mul c) using 1
    ring
  have hlin : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y := ((hasDerivAt_id y).const_mul c).neg
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(c * u))) (Real.exp (-(c * y)) * (-(c * 1))) y := hlin.exp
  convert hP.mul he using 1
  ring

noncomputable def G (y : ℝ) : ℝ :=
  (1.00000002) * expT (1 / 2) y + (1.4263) * expT (2 / 3) y + (4.2676e-5) * y ^ 5
noncomputable def G' (y : ℝ) : ℝ :=
  (1.00000002) * expTd (1 / 2) y + (1.4263) * expTd (2 / 3) y + (4.2676e-5) * (5 * y ^ 4)
noncomputable def G'' (y : ℝ) : ℝ :=
  (1.00000002) * expTdd (1 / 2) y + (1.4263) * expTdd (2 / 3) y + (4.2676e-5) * (20 * y ^ 3)

lemma G_hasDerivAt (y : ℝ) : HasDerivAt G (G' y) y := by
  unfold G G'
  have h1 := (expT_hasDerivAt (1 / 2) y).const_mul (1.00000002 : ℝ)
  have h2 := (expT_hasDerivAt (2 / 3) y).const_mul (1.4263 : ℝ)
  have h3 : HasDerivAt (fun u : ℝ => (4.2676e-5 : ℝ) * u ^ 5) ((4.2676e-5) * (5 * y ^ 4)) y := by
    have h5 : HasDerivAt (fun u : ℝ => u ^ 5) (5 * y ^ 4) y := by simpa using hasDerivAt_pow 5 y
    exact h5.const_mul _
  convert (h1.add h2).add h3 using 1

lemma G'_hasDerivAt (y : ℝ) : HasDerivAt G' (G'' y) y := by
  unfold G' G''
  have h1 := (expTd_hasDerivAt (1 / 2) y).const_mul (1.00000002 : ℝ)
  have h2 := (expTd_hasDerivAt (2 / 3) y).const_mul (1.4263 : ℝ)
  have h3 : HasDerivAt (fun u : ℝ => (4.2676e-5 : ℝ) * (5 * u ^ 4)) ((4.2676e-5) * (20 * y ^ 3)) y := by
    have h4 : HasDerivAt (fun u : ℝ => u ^ 4) (4 * y ^ 3) y := by simpa using hasDerivAt_pow 4 y
    convert (h4.const_mul (5 : ℝ)).const_mul (4.2676e-5 : ℝ) using 1
    ring
  convert (h1.add h2).add h3 using 1

lemma G_continuous : Continuous G := by unfold G expT; fun_prop

lemma G''_nonneg {y : ℝ} (hy : y ∈ Set.Ioo (20 : ℝ) 21) : 0 ≤ G'' y := by
  obtain ⟨h20, _h21⟩ := hy
  have hy3 : (0 : ℝ) ≤ y ^ 3 := by positivity
  unfold G'' expTdd
  have t1 : (0 : ℝ) ≤ (1.00000002) *
      (((1 / 2 : ℝ) ^ 2 * y ^ 5 - 10 * (1 / 2) * y ^ 4 + 20 * y ^ 3) * Real.exp (-((1 / 2 : ℝ) * y))) := by
    apply mul_nonneg (by norm_num)
    apply mul_nonneg _ (Real.exp_pos _).le
    have hbr : (0 : ℝ) ≤ (1 / 4 : ℝ) * y ^ 2 - 5 * y + 20 := by nlinarith [h20, sq_nonneg (y - 20)]
    nlinarith [mul_nonneg hy3 hbr]
  have t2 : (0 : ℝ) ≤ (1.4263) *
      (((2 / 3 : ℝ) ^ 2 * y ^ 5 - 10 * (2 / 3) * y ^ 4 + 20 * y ^ 3) * Real.exp (-((2 / 3 : ℝ) * y))) := by
    apply mul_nonneg (by norm_num)
    apply mul_nonneg _ (Real.exp_pos _).le
    have hbr : (0 : ℝ) ≤ (4 / 9 : ℝ) * y ^ 2 - (20 / 3) * y + 20 := by nlinarith [h20, sq_nonneg (y - 20)]
    nlinarith [mul_nonneg hy3 hbr]
  have t3 : (0 : ℝ) ≤ (4.2676e-5) * (20 * y ^ 3) := by positivity
  linarith [t1, t2, t3]

lemma G_convexOn : ConvexOn ℝ (Set.Icc (20 : ℝ) 21) G := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) G_continuous.continuousOn
  · intro y _; exact (G_hasDerivAt y).hasDerivWithinAt
  · intro y _; exact (G'_hasDerivAt y).hasDerivWithinAt
  · intro y hy; rw [interior_Icc] at hy; exact G''_nonneg hy

theorem G_le_table : ∀ y ∈ Set.Icc (20 : ℝ) 21, G y ≤ 291.60 := by
  intro y hy
  have h20 : G 20 ≤ 291.60 := by unfold G expT; norm_num; interval_decide
  have h21 : G 21 ≤ 291.60 := by unfold G expT; norm_num; interval_decide
  calc G y ≤ max (G 20) (G 21) :=
        G_convexOn.le_max_of_mem_Icc (left_mem_Icc.mpr (by norm_num)) (right_mem_Icc.mpr (by norm_num)) hy
    _ ≤ 291.60 := max_le h20 h21

/-! ## Bridge: exact Lemma-8 `B` → pointwise → coefficient bounds → `G`. -/

private lemma B_le_of_forall_log (k n : ℕ) (a : ℕ → ℝ) (ε : ℝ → ℝ) {b b' C : ℝ}
    (hbb' : b ≤ b')
    (hC : ∀ y ∈ Set.Icc b b',
        (∑ ℓ ∈ Finset.Icc 1 n, a ℓ * y ^ k * Real.exp (-((ℓ : ℝ) / (ℓ + 1) * y))) + ε b * y ^ k ≤ C) :
    B k n a ε b b' ≤ C := by
  unfold B
  haveI h_nonempty : Nonempty (Set.Icc (exp b) (exp b')) := by
    refine ⟨exp b, ?_⟩
    simp only [Set.mem_Icc, le_refl, true_and]
    exact exp_le_exp.mpr hbb'
  refine ciSup_le ?_
  rintro ⟨x, hx⟩
  have hx_pos : 0 < x := (exp_pos b).trans_le hx.1
  have hy : log x ∈ Set.Icc b b' := by
    constructor
    · exact (log_exp b).symm ▸ log_le_log (exp_pos b) hx.1
    · exact (log_exp b').symm ▸ log_le_log hx_pos hx.2
  have h_sum_eq :
      (∑ ℓ ∈ Finset.Icc 1 n, a ℓ * (log x) ^ k * x ^ (-(ℓ : ℝ) / (ℓ + 1)))
        = ∑ ℓ ∈ Finset.Icc 1 n, a ℓ * (log x) ^ k * exp (-((ℓ : ℝ) / (ℓ + 1) * log x)) := by
    apply Finset.sum_congr rfl
    intro ℓ _
    have h_x_pow : x ^ (-(ℓ : ℝ) / (ℓ + 1)) = exp (-((ℓ : ℝ) / (ℓ + 1) * log x)) := by
      rw [rpow_def_of_pos hx_pos]; congr 1; ring
    rw [h_x_pow]
  show (∑ ℓ ∈ Finset.Icc 1 n, a ℓ * (log x) ^ k * x ^ (-(ℓ : ℝ) / (ℓ + 1)))
        + ε b * (log x) ^ k ≤ C
  rw [h_sum_eq]
  exact hC (log x) hy

private lemma row20_eps_le : Inputs.default.ε (20 : ℝ) ≤ (4.2676e-5 : ℝ) := by
  exact BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_20 le_rfl

private lemma row20_a2_le : Inputs.default.a₂ (20 : ℝ) ≤ (1.4263 : ℝ) := by
  have hf : (0 : ℝ) ≤ f (exp 20) := by
    unfold f
    exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (exp_pos 20).le _)
  have hmax : (0 : ℝ) ≤ max (f (exp 20)) (f ((2 : ℝ) ^ (⌊(20 : ℝ) / log 2⌋₊ + 1))) :=
    le_trans hf (le_max_left _ _)
  have hα : Inputs.default.α ≤ 193571378 / (10 : ℝ) ^ 16 := by
    show (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 193571378 / (10 : ℝ) ^ 16
    norm_num [BKLNW_app.table_8_margin]
  unfold Inputs.a₂
  calc (1 + Inputs.default.α) * max (f (exp 20)) (f ((2 : ℝ) ^ (⌊(20 : ℝ) / log 2⌋₊ + 1)))
      ≤ (1 + 193571378 / (10 : ℝ) ^ 16) * max (f (exp 20)) (f ((2 : ℝ) ^ (⌊(20 : ℝ) / log 2⌋₊ + 1))) := by
        gcongr
    _ ≤ 1.4262 + 1 / 10 ^ 4 := a2_20_mem_Icc.2
    _ ≤ 1.4263 := by norm_num

private lemma row20_a1_le : Inputs.default.a₁ (20 : ℝ) ≤ (1.00000002 : ℝ) := by
  have hlog : (43 : ℝ) < log Inputs.default.x₁ ∧ log Inputs.default.x₁ < 44 := by
    show (43 : ℝ) < log (1e19 : ℝ) ∧ log (1e19 : ℝ) < 44
    have h1e19 : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
    rw [h1e19, Real.log_pow]; push_cast
    constructor <;> nlinarith [LogTables.log_10_gt, LogTables.log_10_lt]
  have hε19 : Inputs.default.ε (log Inputs.default.x₁) ≤ 1.93378e-8 * BKLNW_app.table_8_margin := by
    show BKLNW_app.table_8_ε (log Inputs.default.x₁) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    grw [BKLNW_app.table_8_ε.le_simp (log Inputs.default.x₁) (by linarith [hlog.1])]
    grind [BKLNW_app.table_8_ε']
  unfold Inputs.a₁
  rw [if_pos (by linarith [hlog.1] : (20 : ℝ) ≤ 2 * log Inputs.default.x₁)]
  have hb : (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1.00000002 - 1 := by
    norm_num [BKLNW_app.table_8_margin]
  linarith [hε19, hb]

/-! ## The fix: row 20, k = 5, exact Lemma-8 `B` satisfies the listed bound. -/

noncomputable def B_8_exact (k : ℕ) (b b' : ℝ) : ℝ :=
  B k 2 (fun ℓ => if ℓ = 1 then Inputs.default.a₁ b else if ℓ = 2 then Inputs.default.a₂ b else 0)
    Inputs.default.ε b b'

theorem table_10_row20_k5 : B_8_exact 5 20 21 ≤ (291.60 : ℝ) := by
  unfold B_8_exact
  apply B_le_of_forall_log
  · norm_num
  · intro y hy
    have hy0 : (0 : ℝ) ≤ y := by have := hy.1; linarith
    have hy5 : (0 : ℝ) ≤ y ^ 5 := pow_nonneg hy0 5
    have hG : G y ≤ 291.60 := G_le_table y hy
    unfold G expT at hG
    rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_insert (by decide), Finset.sum_singleton]
    have hif1 : (if (1 : ℕ) = 1 then Inputs.default.a₁ 20 else if (1 : ℕ) = 2 then Inputs.default.a₂ 20 else 0)
        = Inputs.default.a₁ 20 := by norm_num
    have hif2 : (if (2 : ℕ) = 1 then Inputs.default.a₁ 20 else if (2 : ℕ) = 2 then Inputs.default.a₂ 20 else 0)
        = Inputs.default.a₂ 20 := by norm_num
    have ce1 : Real.exp (-(((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(1 / 2 * y)) := by
      congr 1; push_cast; ring
    have ce2 : Real.exp (-(((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(2 / 3 * y)) := by
      congr 1; push_cast; ring
    rw [hif1, hif2, ce1, ce2]
    have e1 : (0 : ℝ) ≤ y ^ 5 * Real.exp (-(1 / 2 * y)) := mul_nonneg hy5 (Real.exp_pos _).le
    have e2 : (0 : ℝ) ≤ y ^ 5 * Real.exp (-(2 / 3 * y)) := mul_nonneg hy5 (Real.exp_pos _).le
    have h1 : Inputs.default.a₁ 20 * y ^ 5 * Real.exp (-(1 / 2 * y))
        ≤ 1.00000002 * (y ^ 5 * Real.exp (-(1 / 2 * y))) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right row20_a1_le e1
    have h2 : Inputs.default.a₂ 20 * y ^ 5 * Real.exp (-(2 / 3 * y))
        ≤ 1.4263 * (y ^ 5 * Real.exp (-(2 / 3 * y))) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right row20_a2_le e2
    have h3 : Inputs.default.ε 20 * y ^ 5 ≤ 4.2676e-5 * y ^ 5 :=
      mul_le_mul_of_nonneg_right row20_eps_le hy5
    linarith [h1, h2, h3, hG]

/-! ## The bug: the current `B_8_1`-based target is false at row 20. -/

theorem inputs_default_epsilon_rfl : Inputs.default.ε = BKLNW_app.table_8_ε := rfl

theorem inputs_default_alpha_rfl :
    Inputs.default.α = 1.93378e-8 * BKLNW_app.table_8_margin := rfl

lemma table10_next_20_eq : table_10_next 20 = 21 := by
  have hne : (table_10_bs.filter (fun x => (20 : ℝ) < x)).Nonempty :=
    ⟨21, by norm_num [table_10_bs, table_10_entries, table_10, K]⟩
  rw [table_10_next_eq_min' 20 hne]
  · apply le_antisymm
    · apply Finset.min'_le
      norm_num [table_10_bs, table_10_entries, table_10, K]
    · apply Finset.le_min'
      intro y hy
      simp only [table_10_bs, table_10_entries, table_10, K, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil, Finset.union_singleton, Finset.mem_filter,
        Finset.mem_insert] at hy
      rcases hy with ⟨hy_mem, hy_gt⟩
      rcases hy_mem with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | hy_false
      · change (21 : ℝ) ≤ 25000
        norm_num
      all_goals
        try norm_num at hy_gt ⊢
        try nlinarith [LogTables.log_10_gt]
        try cases hy_false

lemma table10_a1_20_ge_one : (1 : ℝ) ≤ Inputs.default.a₁ 20 := by
  unfold Inputs.a₁
  split_ifs
  · have hx₁_ge_one : 1 ≤ Inputs.default.x₁ :=
      (one_le_exp (by positivity)).trans Inputs.default.hx₁
    have hε : 0 ≤ Inputs.default.ε (log Inputs.default.x₁) :=
      Pre_inputs.epsilon_nonneg Inputs.default.toPre_inputs (log_nonneg hx₁_ge_one)
    linarith
  · have hε : 0 ≤ Inputs.default.ε (20 / 2) :=
      Pre_inputs.epsilon_nonneg Inputs.default.toPre_inputs (by positivity)
    linarith

lemma table10_a2_20_nonneg : 0 ≤ Inputs.default.a₂ 20 := by
  have hα_pos : 0 < 1 + Inputs.default.α := by
    unfold Inputs.default
    positivity
  have hmax_nonneg :
      0 ≤ max (f (exp 20)) (f (2 ^ (⌊20 / log 2⌋₊ + 1))) :=
    le_max_iff.2 (Or.inl (Finset.sum_nonneg (by intros; positivity)))
  unfold Inputs.a₂
  exact mul_nonneg hα_pos.le hmax_nonneg

set_option maxRecDepth 10000 in
lemma table8_eps_ge_of_le20 {p : ℝ × ℝ} (hp : p ∈ BKLNW_app.table_8) (hp20 : p.1 ≤ 20) :
    (4.2676e-5 : ℝ) ≤ p.2 := by
  rcases p with ⟨b, ε⟩
  norm_num [BKLNW_app.table_8] at hp hp20 ⊢
  repeat' (first | rcases hp with hp | hp)
  all_goals
    subst_vars
    norm_num at *

lemma table10_eps_20_ge : (4.2676e-5 : ℝ) ≤ Inputs.default.ε 20 := by
  change (4.2676e-5 : ℝ) ≤ BKLNW_app.table_8_ε 20
  unfold BKLNW_app.table_8_ε
  refine le_csInf ?nonempty ?lower
  · exact ⟨(4.2676e-5 : ℝ),
      ⟨(20, 4.2676e-5), BKLNW_app.table_8_mem_20, by norm_num, rfl⟩⟩
  · intro ε hε
    rcases hε with ⟨p, hp_mem, hp_le, rfl⟩
    exact table8_eps_ge_of_le20 hp_mem hp_le

def table10_row20_B : ℕ → ℝ
  | 1 => 1.8077e-3
  | 2 => 3.6154e-2
  | 3 => 7.2309e-1
  | 4 => 1.4462e1
  | 5 => 2.9160e2
  | _ => 0

lemma table10_row20_mem :
    (20, table10_row20_B 1, table10_row20_B 2, table10_row20_B 3,
      table10_row20_B 4, table10_row20_B 5) ∈ table_10 := by
  norm_num [table10_row20_B, table_10]

theorem table10_row20_endpoint_lower_data :
    (2.9160e2 : ℝ) <
      (1 : ℝ) * 20 ^ (5 : ℕ) * exp (-20 / 2) +
        21 ^ (5 : ℕ) * (4.2676e-5 : ℝ) := by
  interval_decide

theorem table10_row20_endpoint_lower_data_actual_next :
    (2.9160e2 : ℝ) <
      (1 : ℝ) * 20 ^ (5 : ℕ) * exp (-20 / 2) +
        (table_10_next 20) ^ (5 : ℕ) * (4.2676e-5 : ℝ) := by
  rw [table10_next_20_eq]
  exact table10_row20_endpoint_lower_data

theorem table10_row20_k5_counterexample_of_eps20_ge
    (ha1 : (1 : ℝ) ≤ Inputs.default.a₁ 20)
    (ha2 : 0 ≤ Inputs.default.a₂ 20)
    (hε : (4.2676e-5 : ℝ) ≤ Inputs.default.ε 20) :
    (2.9160e2 : ℝ) < B_8_1 5 20 21 := by
  have hnum :
      (2.9160e2 : ℝ) <
        (1 : ℝ) * 20 ^ (5 : ℕ) * exp (-20 / 2) +
          21 ^ (5 : ℕ) * (4.2676e-5 : ℝ) := by
    exact table10_row20_endpoint_lower_data
  unfold B_8_1
  nlinarith [hnum, ha1, ha2, hε, exp_pos (-20 / 2), exp_pos (-2 * 20 / 3)]

theorem table10_row20_k5_counterexample_of_eps20_ge_actual_next
    (hε : (4.2676e-5 : ℝ) ≤ Inputs.default.ε 20) :
    (2.9160e2 : ℝ) < B_8_1 5 20 (table_10_next 20) := by
  rw [table10_next_20_eq]
  exact table10_row20_k5_counterexample_of_eps20_ge
    table10_a1_20_ge_one table10_a2_20_nonneg hε

theorem table10_row20_k5_counterexample_actual :
    (2.9160e2 : ℝ) < B_8_1 5 20 (table_10_next 20) :=
  table10_row20_k5_counterexample_of_eps20_ge_actual_next table10_eps_20_ge

theorem table10_row20_current_target_false :
    ¬ ∀ k ∈ Finset.Icc 1 5, B_8_1 k 20 (table_10_next 20) ≤ table10_row20_B k := by
  intro h
  have h5 : B_8_1 5 20 (table_10_next 20) ≤ (2.9160e2 : ℝ) := by
    simpa [table10_row20_B] using h 5 (by norm_num)
  linarith [h5, table10_row20_k5_counterexample_actual]

theorem table10_verification_statement_false :
    ¬ ∀ (b : ℝ) (B : ℕ → ℝ),
        (b, B 1, B 2, B 3, B 4, B 5) ∈ table_10 →
          ∀ k ∈ Finset.Icc 1 5, B_8_1 k b (table_10_next b) ≤ B k := by
  intro h
  exact table10_row20_current_target_false (h 20 table10_row20_B table10_row20_mem)

#print axioms table_10_row20_k5
#print axioms table10_verification_statement_false

end BKLNW
