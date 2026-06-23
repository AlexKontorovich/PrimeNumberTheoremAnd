import PrimeNumberTheoremAnd.IEANTN.FKS2Floor.Cor22Floor
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtGenCore

/-!
# FKS2 Corollary 23 — per-row proofs

Corollary 23 asserts, for each row `(A,B,C,x₀)` of Table 6, the admissible
classical bound `Eπ.classicalBound A B C 5.5666305 (exp x₀)`.  Each row is
proven by the same three-segment decomposition used for Corollary 22:

* **floor** `[exp x₀, e^10]` — tight small-`x` `Eπ` via Buthe (`theorem_2e/2f`);
* **mid** `[e^10, e^20000]` — the numerical envelope `allCells` transported to
  the row curve by `cell_Epi_le_admissible_gen` (this file's generalized dyadic
  cell transport);
* **tail/loose** `[e^20000, ∞)` — domination by the (looser) Corollary 22 curve,
  or `theorem_3` from `corollary_14` for the rows that stay sharp.

**Template row = row 5** `(A=2.22, B=3/2, C=3/2, x₀=3)`: its curve clears the
envelope on every cell with a ≥46× margin, so the mid is the cleanest.

This file lives downstream of `Cor22Floor` (floor θ-engine) and `Table4ExtGenCore`
(transport); `corollary_23` itself cannot be proven inside `FKS2.lean`, which is
upstream of both — exactly as `corollary_22` lives in `Cor22Floor.lean`.
-/

namespace FKS2
open Real Table4Ext

/-! ## Row 5 (`A=2.22, B=3/2, C=3/2`, threshold `exp 3`) -/

/-- Row-5 cell-check parameters: `k = 2B = 3`, `ĉ = 0.6358 ≥ C/√R = 0.635763`
(so `c64 = ĉ/64`), `rB = 13.1338 ≥ R^{3/2} = 13.133745`, `Aq = A = 2.22`. -/
def P5 : CellParams := ⟨3179/320000, 3, 131338/10000, 222/100⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-5 dyadic check (verified by the
dyadic interval kernel over all 13590 cells). -/
theorem allCells_checked_row5 : allCells.all (fun c => checkCellGen P5 c) = true := by
  native_decide

/-- Row-5 mid-range: `Eπ ≤` the row-5 admissible curve on `[e^10, e^20000]`,
via the envelope `allCells_trusted` transported by `cell_Epi_le_admissible_gen`. -/
theorem mid_row5 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x := by
  intro x hx
  have hx_lo : exp ((10:ℕ):ℝ) ≤ x := by simpa using hx.1
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]; simpa using hx.2
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo hx_hi
  have hck : checkCellGen P5 c = true := List.all_eq_true.mp allCells_checked_row5 c hcmem
  have hsqrtR_lb : (2.359370:ℝ) ≤ Real.sqrt 5.5666305 := by
    rw [show (2.359370:ℝ) = Real.sqrt (2.359370^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtR_ub : Real.sqrt 5.5666305 ≤ (2.359379:ℝ) := by
    rw [show (2.359379:ℝ) = Real.sqrt (2.359379^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine cell_Epi_le_admissible_gen P5 2.22 1.5 1.5 5.5666305
    (by norm_num [P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [P5])
    ?_ ?_ c hck (allCells_trusted c hcmem) x hcx
  · -- hCge : 1.5 / √R ≤ (P5.c64 * 64 : ℝ) = 0.6358
    have hrhs : (((P5.c64 * 64 : ℚ)):ℝ) = 3179/5000 := by norm_num [P5]
    rw [hrhs, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [hsqrtR_lb]
  · -- hrB : R^{1.5} ≤ (P5.rB : ℝ) = 13.1338
    have hrhs : (((P5.rB : ℚ)):ℝ) = 131338/10000 := by norm_num [P5]
    rw [hrhs]
    have hpow : (5.5666305:ℝ) ^ (1.5:ℝ) = 5.5666305 * Real.sqrt 5.5666305 := by
      rw [show (1.5:ℝ) = 1 + 1/2 by norm_num,
        Real.rpow_add (by norm_num : (0:ℝ) < 5.5666305), Real.rpow_one]
      simp [Real.sqrt_eq_rpow]
    rw [hpow]; nlinarith [hsqrtR_ub, Real.sqrt_nonneg (5.5666305:ℝ)]

/-- Row-5 floor `[exp 3, e^10]`: tight small-`x` `Eπ` bound via Buthe. **WIP.** -/
theorem floor_row5 : ∀ x ∈ Set.Icc (exp (3:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x := by
  sorry

/-- `admissible_bound A (3/2) C R x` in terms of `s = √(log x)`:
`= (A / R^{3/2}) · s³ · exp(−(C/√R)·s)`.  Reusable for tail domination. -/
lemma admissible_three_halves_eq (A C R x : ℝ) (hL : 0 ≤ Real.log x) (hR : 0 < R) :
    admissible_bound A 1.5 C R x
      = (A / R ^ (1.5:ℝ)) * Real.sqrt (Real.log x) ^ 3
        * Real.exp (-(C / Real.sqrt R) * Real.sqrt (Real.log x)) := by
  unfold admissible_bound
  set s := Real.sqrt (Real.log x) with hs_def
  have hs : s = Real.log x ^ ((1:ℝ)/2) := by rw [hs_def, Real.sqrt_eq_rpow]
  have e1 : (Real.log x / R) ^ (1.5:ℝ) = s ^ 3 / R ^ (1.5:ℝ) := by
    rw [Real.div_rpow hL hR.le]
    congr 1
    rw [hs, ← Real.rpow_natCast (Real.log x ^ ((1:ℝ)/2)) 3, ← Real.rpow_mul hL]
    norm_num
  have e2 : (Real.log x / R) ^ ((1:ℝ)/2) = s / Real.sqrt R := by
    rw [Real.div_rpow hL hR.le, ← hs, Real.sqrt_eq_rpow R]
  rw [e1, e2, show -C * (s / Real.sqrt R) = -(C / Real.sqrt R) * s by ring]
  ring

/-- Row-5 tail `[e^20000, ∞)`: `Eπ ≤` the row-5 curve, by domination of the
(looser) Corollary 22 curve `Eπ ≤ 9.2211·…` (which crosses below the row-5 curve
well before `e^20000`). -/
theorem tail_row5 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x := by
  intro x hx
  have he2 : (2:ℝ) ≤ Real.exp 20000 := by
    have := Real.add_one_le_exp (20000:ℝ); linarith
  have hx2 : (2:ℝ) ≤ x := le_trans he2 hx
  have hcor := corollary_22 x hx2
  refine le_trans hcor ?_
  have hL : (20000:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20000]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [admissible_three_halves_eq 9.2211 0.8476 1 x hLnn (by norm_num),
      admissible_three_halves_eq 2.22 1.5 5.5666305 x hLnn (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs141 : (141:ℝ) ≤ s := by
    rw [hs_def, show (141:ℝ) = Real.sqrt (141^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hL])
  have hsqrtR_lb : (2.359370:ℝ) ≤ Real.sqrt 5.5666305 := by
    rw [show (2.359370:ℝ) = Real.sqrt (2.359370^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtR_ub : Real.sqrt 5.5666305 ≤ (2.359379:ℝ) := by
    rw [show (2.359379:ℝ) = Real.sqrt (2.359379^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtR_pos : (0:ℝ) < Real.sqrt 5.5666305 := by positivity
  have hR15_ub : (5.5666305:ℝ) ^ (1.5:ℝ) ≤ 13.1338 := by
    have hpow : (5.5666305:ℝ) ^ (1.5:ℝ) = 5.5666305 * Real.sqrt 5.5666305 := by
      rw [show (1.5:ℝ) = 1 + 1/2 by norm_num,
        Real.rpow_add (by norm_num : (0:ℝ) < 5.5666305), Real.rpow_one]
      simp [Real.sqrt_eq_rpow]
    rw [hpow]; nlinarith [hsqrtR_ub, hsqrtR_pos]
  have hR15_pos : (0:ℝ) < (5.5666305:ℝ) ^ (1.5:ℝ) := by positivity
  have hcoeff : (2.22:ℝ) / 13.1338 ≤ 2.22 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hR15_pos hR15_ub
  have hCR : (1.5:ℝ) / Real.sqrt 5.5666305 ≤ 0.63577 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  have hexpRHS : Real.exp (-(0.63577:ℝ) * s) ≤ Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have hCRs : (1.5 / Real.sqrt 5.5666305) * s ≤ 0.63577 * s :=
      mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith [hCRs]
  have hexp4 : (54.598:ℝ) ≤ Real.exp 4 := by
    have he : Real.exp 4 = (Real.exp 1) ^ (4:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (54.598:ℝ) ≤ (2.7182818283:ℝ) ^ (4:ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (4:ℕ) := by gcongr; exact Real.exp_one_gt_d9.le
  have h4le : (4:ℝ) ≤ 0.21183 * s := by nlinarith [hs141]
  have hexp_small : Real.exp (-(0.21183:ℝ) * s) ≤ Real.exp (-4) := by
    apply Real.exp_le_exp.mpr; simp only [neg_mul]; linarith [h4le]
  have hexp_neg4 : Real.exp (-(4:ℝ)) ≤ 1 / 54.598 := by
    rw [Real.exp_neg, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hexp4
  have hscalar : (9.2211:ℝ) * Real.exp (-(0.8476) * s)
      ≤ (2.22 / 13.1338) * Real.exp (-(0.63577:ℝ) * s) := by
    have hsplit : Real.exp (-(0.8476:ℝ) * s)
        = Real.exp (-(0.21183:ℝ) * s) * Real.exp (-(0.63577:ℝ) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit,
      show (9.2211:ℝ) * (Real.exp (-(0.21183) * s) * Real.exp (-(0.63577) * s))
        = (9.2211 * Real.exp (-(0.21183) * s)) * Real.exp (-(0.63577) * s) by ring]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc (9.2211:ℝ) * Real.exp (-(0.21183) * s)
        ≤ 9.2211 * (1 / 54.598) :=
          mul_le_mul_of_nonneg_left (le_trans hexp_small hexp_neg4) (by norm_num)
      _ ≤ 2.22 / 13.1338 := by norm_num
  have hfinal : (9.2211:ℝ) * Real.exp (-(0.8476) * s)
      ≤ (2.22 / (5.5666305:ℝ) ^ (1.5:ℝ)) * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) :=
    le_trans hscalar (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) (by positivity))
  have hs3 : (0:ℝ) ≤ s ^ 3 := by positivity
  rw [show (1:ℝ) ^ (1.5:ℝ) = 1 by norm_num, Real.sqrt_one]
  simp only [div_one]
  calc (9.2211:ℝ) * s ^ 3 * Real.exp (-(0.8476) * s)
      = (9.2211 * Real.exp (-(0.8476) * s)) * s ^ 3 := by ring
    _ ≤ ((2.22 / (5.5666305:ℝ) ^ (1.5:ℝ)) * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s)) * s ^ 3 :=
        mul_le_mul_of_nonneg_right hfinal hs3
    _ = 2.22 / (5.5666305:ℝ) ^ (1.5:ℝ) * s ^ 3 * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by
        ring

/-- **Corollary 23, row 5** `(A=2.22, B=3/2, C=3/2, x₀=3)`. -/
theorem corollary_23_row5 : Eπ.classicalBound 2.22 1.5 1.5 5.5666305 (exp 3) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row5 x ⟨hx, h10⟩
  · push_neg at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row5 x ⟨le_of_lt h10, h20k⟩
    · push_neg at h20k
      exact tail_row5 x (le_of_lt h20k)

end FKS2
