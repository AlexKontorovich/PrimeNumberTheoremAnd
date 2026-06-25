import PrimeNumberTheoremAnd.IEANTN.FKS2Floor.Cor22Floor
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtGenCore
import PrimeNumberTheoremAnd.IEANTN.Buthe

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
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-! ## Shared `R = 5.5666305` numeric enclosures (used by every row-5 segment) -/

/-- `√5.5666305 ≥ 2.359370`. -/
lemma sqrtR5_lb : (2.359370 : ℝ) ≤ Real.sqrt 5.5666305 := by
  rw [show (2.359370:ℝ) = Real.sqrt (2.359370^2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- `√5.5666305 ≤ 2.359379`. -/
lemma sqrtR5_ub : Real.sqrt 5.5666305 ≤ (2.359379 : ℝ) := by
  rw [show (2.359379:ℝ) = Real.sqrt (2.359379^2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma sqrtR5_pos : (0 : ℝ) < Real.sqrt 5.5666305 := by positivity

/-- `R^{3/2} = R·√R` for `R = 5.5666305`. -/
lemma R5_rpow_three_halves_eq :
    (5.5666305 : ℝ) ^ (1.5 : ℝ) = 5.5666305 * Real.sqrt 5.5666305 := by
  rw [show (1.5:ℝ) = 1 + 1/2 by norm_num,
    Real.rpow_add (by norm_num : (0:ℝ) < 5.5666305), Real.rpow_one]
  simp [Real.sqrt_eq_rpow]

/-- `R^{3/2} ≤ 13.1338` for `R = 5.5666305`. -/
lemma R5_rpow_three_halves_le : (5.5666305 : ℝ) ^ (1.5 : ℝ) ≤ 13.1338 := by
  rw [R5_rpow_three_halves_eq]; nlinarith [sqrtR5_ub, sqrtR5_pos]

lemma R5_rpow_three_halves_pos : (0 : ℝ) < (5.5666305 : ℝ) ^ (1.5 : ℝ) := by positivity

/-! ## Row 5 (`A=2.22, B=3/2, C=3/2`, threshold `exp 3`) -/

/-- Row-5 cell-check parameters: `k = 2B = 3`, `ĉ = 0.6358 ≥ C/√R = 0.635763`
(so `c64 = ĉ/64`), `rB = 13.1338 ≥ R^{3/2} = 13.133745`, `Aq = A = 2.22`. -/
def P5 : CellParams := ⟨3179/320000, 3, 131338/10000, 222/100⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-5 dyadic check (verified by the
dyadic interval kernel over all 13590 cells). -/
theorem allCells_checked_row5 : allCells.all (fun c => checkCellGen P5 c) = true := by
  native_decide

/-- Generic mid-range: every row's `[e^10, e^20000]` segment via the `allCells`
envelope transported by `cell_Epi_le_admissible_gen`.  Rows supply `P`, the curve
params `(A,B,C)`, the cell-param numeric witnesses, and the `native_decide` check.
Shared by every row's `mid_row` (the `cover_of_chainOk` plumbing was identical). -/
theorem mid_of (P : CellParams) (A B C : ℝ)
    (hk : (P.k : ℝ) = 2 * B) (hB : 0 ≤ B) (hAnn : 0 ≤ A)
    (hAq : ((P.Aq : ℚ) : ℝ) = A)
    (hCge : C / Real.sqrt 5.5666305 ≤ ((P.c64 * 64 : ℚ) : ℝ))
    (hrB : (5.5666305:ℝ) ^ B ≤ ((P.rB : ℚ) : ℝ))
    (hchecked : allCells.all (fun c => checkCellGen P c) = true) :
    ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
      Eπ x ≤ admissible_bound A B C 5.5666305 x := by
  intro x hx
  have hx_lo : exp ((10:ℕ):ℝ) ≤ x := by simpa using hx.1
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]; simpa using hx.2
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo hx_hi
  have hck : checkCellGen P c = true := List.all_eq_true.mp hchecked c hcmem
  exact cell_Epi_le_admissible_gen P A B C 5.5666305 hk hB (by norm_num) hAnn hAq hCge hrB
    c hck (allCells_trusted c hcmem) x hcx

/-- Row-5 mid-range `[e^10, e^20000]` via the generic `mid_of`. -/
theorem mid_row5 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x :=
  mid_of P5 2.22 1.5 1.5 (by norm_num [P5]) (by norm_num) (by norm_num) (by norm_num [P5])
    (by have hrhs : (((P5.c64 * 64 : ℚ)):ℝ) = 3179/5000 := by norm_num [P5]
        rw [hrhs, div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb])
    (by have hrhs : (((P5.rB : ℚ)):ℝ) = 131338/10000 := by norm_num [P5]
        rw [hrhs, R5_rpow_three_halves_eq]; nlinarith [sqrtR5_ub, Real.sqrt_nonneg (5.5666305:ℝ)])
    allCells_checked_row5

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

/-- `admissible_bound A (1/2) C R x` in terms of `s = √(log x)`:
`= (A/√R)·s·exp(−(C/√R)·s)`.  The `B = 1/2` analogue of
`admissible_three_halves_eq` (used by row 3). -/
lemma admissible_half_eq (A C R x : ℝ) (hL : 0 ≤ Real.log x) (hR : 0 < R) :
    admissible_bound A 0.5 C R x
      = (A / Real.sqrt R) * Real.sqrt (Real.log x)
        * Real.exp (-(C / Real.sqrt R) * Real.sqrt (Real.log x)) := by
  unfold admissible_bound
  set s := Real.sqrt (Real.log x) with hs_def
  have hs : s = Real.log x ^ ((1:ℝ)/2) := by rw [hs_def, Real.sqrt_eq_rpow]
  have e1 : (Real.log x / R) ^ (0.5:ℝ) = s / Real.sqrt R := by
    rw [show (0.5:ℝ) = (1:ℝ)/2 by norm_num, Real.div_rpow hL hR.le, ← hs, Real.sqrt_eq_rpow R]
  have e2 : (Real.log x / R) ^ ((1:ℝ)/2) = s / Real.sqrt R := by
    rw [Real.div_rpow hL hR.le, ← hs, Real.sqrt_eq_rpow R]
  rw [e1, e2, show -C * (s / Real.sqrt R) = -(C / Real.sqrt R) * s by ring]
  ring

/-- Width-`0.05` slab list of `n` slabs starting at `lo` (generalizes
`FloorButhe.slabs = slabsFrom (2236/1000) 19`; row 3 uses `slabsFrom (2449/1000) 15`). -/
def slabsFrom (lo : ℚ) (n : ℕ) : List IntervalRat :=
  (List.range n).map (fun (k : ℕ) => ⟨lo + (k:ℚ)*50/1000, lo + ((k:ℚ)+1)*50/1000, by
    have hk : (0:ℚ) ≤ (k:ℚ) := by exact_mod_cast Nat.zero_le k
    linarith⟩)

/-- Any `s ∈ [lo, lo + n·0.05)` lands in some slab of `slabsFrom lo n`. -/
theorem coverFrom (lo : ℚ) (n : ℕ) (s : ℝ)
    (hlo : (lo:ℝ) ≤ s) (hhi : s < (lo:ℝ) + (n:ℝ) * 0.05) :
    ∃ I ∈ slabsFrom lo n, s ∈ Set.Icc (I.lo : ℝ) I.hi := by
  set k : ℕ := ⌊(s - (lo:ℝ)) / 0.05⌋₊ with hk_def
  have hsub_nn : (0:ℝ) ≤ (s - (lo:ℝ)) / 0.05 := by apply div_nonneg <;> linarith
  have hk_lt : k < n := by
    have hub : (s - (lo:ℝ)) / 0.05 < n := by rw [div_lt_iff₀ (by norm_num)]; linarith
    rw [hk_def]; exact Nat.floor_lt hsub_nn |>.mpr (by exact_mod_cast hub)
  refine ⟨⟨lo + (k:ℚ)*50/1000, lo + ((k:ℚ)+1)*50/1000, by
    have hknn : (0:ℚ) ≤ (k:ℚ) := by exact_mod_cast Nat.zero_le k
    linarith⟩, ?_, ?_⟩
  · rw [slabsFrom, List.mem_map]
    exact ⟨k, List.mem_range.mpr hk_lt, rfl⟩
  · have hfloor_le : (k : ℝ) ≤ (s - (lo:ℝ)) / 0.05 := by
      have := Nat.floor_le hsub_nn; rwa [← hk_def] at this
    have hlt_floor : (s - (lo:ℝ)) / 0.05 < (k : ℝ) + 1 := by
      have := Nat.lt_floor_add_one ((s - (lo:ℝ)) / 0.05); rwa [← hk_def] at this
    rw [le_div_iff₀ (by norm_num)] at hfloor_le
    rw [div_lt_iff₀ (by norm_num)] at hlt_floor
    constructor
    · push_cast; linarith [hfloor_le]
    · push_cast; linarith [hlt_floor]

/-- Generic `B = 3/2` floor-curve domination: the evaluated dyadic floor curve
`coeff·s³·exp(−rate·s)` (`s = √(log x)`) is below the row's admissible curve when
`coeff ≤ A/R^{3/2}` and `rate ≥ C/√R`.  Shared by every `B = 3/2` row's
`rhsE_le_rowcurve` (rows 5/6/7). -/
lemma rowcurve_dom_three_halves (A C coeff rate : ℝ) (x : ℝ)
    (hL : (0:ℝ) ≤ Real.log x)
    (hcoeff : coeff ≤ A / (5.5666305:ℝ) ^ (1.5:ℝ))
    (hrate : C / Real.sqrt 5.5666305 ≤ rate)
    (hcoeffnn : 0 ≤ coeff) :
    coeff * (Real.sqrt (Real.log x) * Real.sqrt (Real.log x) * Real.sqrt (Real.log x))
        * Real.exp (-rate * Real.sqrt (Real.log x))
      ≤ admissible_bound A 1.5 C 5.5666305 x := by
  rw [admissible_three_halves_eq A C 5.5666305 x hL (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hsnn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hsss : s * s * s = s ^ 3 := by ring
  have hAnn : (0:ℝ) ≤ A / (5.5666305:ℝ) ^ (1.5:ℝ) := le_trans hcoeffnn hcoeff
  have hexpRHS : Real.exp (-rate * s) ≤ Real.exp (-(C / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hrate hsnn
    simp only [neg_mul]; linarith
  have hs3 : (0:ℝ) ≤ s ^ 3 := by positivity
  rw [hsss]
  calc coeff * s ^ 3 * Real.exp (-rate * s)
      = (coeff * Real.exp (-rate * s)) * s ^ 3 := by ring
    _ ≤ ((A / (5.5666305:ℝ) ^ (1.5:ℝ)) * Real.exp (-(C / Real.sqrt 5.5666305) * s)) * s ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) hAnn) hs3
    _ = A / (5.5666305:ℝ) ^ (1.5:ℝ) * s ^ 3 * Real.exp (-(C / Real.sqrt 5.5666305) * s) := by ring

/-- Generic `B = 3/2` tail: Corollary 22 dominates any `(A, 3/2, C)` row curve for
`x ≥ e^20000`.  Inputs: a rational rate upper bound `rateUB ≥ C/√R`, a rational
coefficient lower bound `coeffLB ≤ A/R^{3/2}`, that the gap `0.8476 − rateUB` is
nonneg, and the single numeric fact `9.2211 ≤ coeffLB·exp((0.8476−rateUB)·141)`
(`s = √(log x) ≥ 141` on `[e^20000, ∞)`).  Shared by every `B = 3/2` row's tail. -/
theorem tail_three_halves_of (A C rateUB coeffLB : ℝ)
    (hrate : C / Real.sqrt 5.5666305 ≤ rateUB)
    (hcoef : coeffLB ≤ A / (5.5666305:ℝ) ^ (1.5:ℝ))
    (hgap : (0:ℝ) ≤ 0.8476 - rateUB)
    (hkey : (9.2211:ℝ) ≤ coeffLB * Real.exp ((0.8476 - rateUB) * 141)) :
    ∀ x ≥ exp (20000:ℝ), Eπ x ≤ admissible_bound A 1.5 C 5.5666305 x := by
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
      admissible_three_halves_eq A C 5.5666305 x hLnn (by norm_num)]
  rw [show (1:ℝ) ^ (1.5:ℝ) = 1 by norm_num, Real.sqrt_one]
  simp only [div_one]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs141 : (141:ℝ) ≤ s := by
    rw [hs_def, show (141:ℝ) = Real.sqrt (141^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hL])
  have hs3 : (0:ℝ) ≤ s ^ 3 := by positivity
  have hcoefnn : (0:ℝ) ≤ coeffLB := by
    by_contra h; rw [not_le] at h
    have := mul_neg_of_neg_of_pos h (Real.exp_pos ((0.8476 - rateUB) * 141))
    linarith [hkey]
  have hexpRHS : Real.exp (-rateUB * s) ≤ Real.exp (-(C / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have : (C / Real.sqrt 5.5666305) * s ≤ rateUB * s := mul_le_mul_of_nonneg_right hrate hs_nn
    simp only [neg_mul]; linarith
  have hkeyS : (9.2211:ℝ) * Real.exp (-(0.8476 - rateUB) * s) ≤ coeffLB := by
    have hmono : Real.exp (-(0.8476 - rateUB) * s) ≤ Real.exp (-(0.8476 - rateUB) * 141) := by
      apply Real.exp_le_exp.mpr
      have : (0.8476 - rateUB) * 141 ≤ (0.8476 - rateUB) * s := mul_le_mul_of_nonneg_left hs141 hgap
      simp only [neg_mul]; linarith
    have hfromkey : (9.2211:ℝ) * Real.exp (-(0.8476 - rateUB) * 141) ≤ coeffLB := by
      have := mul_le_mul_of_nonneg_right hkey (Real.exp_nonneg (-(0.8476 - rateUB) * 141))
      rwa [mul_assoc, ← Real.exp_add,
        show (0.8476 - rateUB) * 141 + -(0.8476 - rateUB) * 141 = 0 by ring,
        Real.exp_zero, mul_one] at this
    calc (9.2211:ℝ) * Real.exp (-(0.8476 - rateUB) * s)
        ≤ 9.2211 * Real.exp (-(0.8476 - rateUB) * 141) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ ≤ coeffLB := hfromkey
  have hscalar : (9.2211:ℝ) * Real.exp (-(0.8476) * s) ≤ coeffLB * Real.exp (-rateUB * s) := by
    have hsplit : Real.exp (-(0.8476:ℝ) * s)
        = Real.exp (-(0.8476 - rateUB) * s) * Real.exp (-rateUB * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit, show (9.2211:ℝ) * (Real.exp (-(0.8476 - rateUB) * s) * Real.exp (-rateUB * s))
        = (9.2211 * Real.exp (-(0.8476 - rateUB) * s)) * Real.exp (-rateUB * s) by ring]
    exact mul_le_mul_of_nonneg_right hkeyS (Real.exp_nonneg _)
  calc (9.2211:ℝ) * s ^ 3 * Real.exp (-(0.8476) * s)
      = (9.2211 * Real.exp (-(0.8476) * s)) * s ^ 3 := by ring
    _ ≤ (coeffLB * Real.exp (-rateUB * s)) * s ^ 3 := mul_le_mul_of_nonneg_right hscalar hs3
    _ ≤ (coeffLB * Real.exp (-(C / Real.sqrt 5.5666305) * s)) * s ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ hs3
        exact mul_le_mul_of_nonneg_left hexpRHS hcoefnn
    _ ≤ ((A / (5.5666305:ℝ) ^ (1.5:ℝ)) * Real.exp (-(C / Real.sqrt 5.5666305) * s)) * s ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ hs3
        exact mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = A / (5.5666305:ℝ) ^ (1.5:ℝ) * s ^ 3 * Real.exp (-(C / Real.sqrt 5.5666305) * s) := by ring

/-- Row-5 tail `[e^20000, ∞)` via the generic `B=3/2` Corollary-22 domination
(`rateUB = 0.63577 ≥ 1.5/√R`, `coeffLB = 0.169029 ≤ 2.22/R^{3/2}`). -/
theorem tail_row5 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x :=
  tail_three_halves_of 2.22 1.5 0.63577 0.169029
    (by rw [div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb])
    (by have h2 := R5_rpow_three_halves_le
        have h3 := R5_rpow_three_halves_pos
        have h1 : (0.169029:ℝ) ≤ 2.22 / 13.1338 := by norm_num
        have h4 : (2.22:ℝ) / 13.1338 ≤ 2.22 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) h3 h2
        linarith)
    (by norm_num)
    (by have hb : Real.exp 5 ≤ Real.exp ((0.8476 - 0.63577) * 141) := by
          apply Real.exp_le_exp.mpr; norm_num
        have h148 : (148:ℝ) ≤ Real.exp 5 := by
          have he : Real.exp 5 = (Real.exp 1) ^ (5:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
          rw [he]; calc (148:ℝ) ≤ (2.7182818283:ℝ)^(5:ℕ) := by norm_num
            _ ≤ (Real.exp 1)^(5:ℕ) := by gcongr; exact Real.exp_one_gt_d9.le
        nlinarith [hb, h148])

/-! ## Row-5 floor `[e^5, e^10]` via Buthe (dyadic slab cover in `s = √(log x)`)

The numerical-envelope route covers `x ≥ e^10`; for the floor we instead bound
`Eπ x ≤ (B(x) + li 2)·(log x / x)` (Buthe `theorem_2e/2f`, `li.sub_Li`,
`li.two_approx`) and dominate the row-5 curve by a dyadic slab cover in the
variable `s = √(log x)` over `[√5, √10] ⊂ [2.236, 3.163]`. -/
namespace FloorButhe

def sqx (e : Expr) : Expr := Expr.mul e e
def pow8 (e : Expr) : Expr := sqx (sqx (sqx e))
def s2 : Expr := Expr.mul (Expr.var 0) (Expr.var 0)
def s4 : Expr := Expr.mul s2 s2
def s3 : Expr := Expr.mul s2 (Expr.var 0)
def e2 : Expr := Expr.exp (Expr.mul (Expr.const (-1/16)) s2)

def lhsE : Expr :=
  Expr.add
    (Expr.mul
      (Expr.add (Expr.const (195/100))
        (Expr.add (Expr.mul (Expr.const (39/10)) (Expr.inv s2))
          (Expr.mul (Expr.const (195/10)) (Expr.inv s4))))
      (pow8 e2))
    (Expr.mul (Expr.const (10452/10000)) (Expr.mul s2 (sqx (pow8 e2))))

def eR : Expr := Expr.exp (Expr.mul (Expr.const (-63577/800000)) (Expr.var 0))
def rhsE : Expr := Expr.mul (Expr.const (169029/1000000)) (Expr.mul s3 (pow8 eR))

def slabs : List IntervalRat :=
  (List.range 19).map (fun (k : ℕ) => ⟨2236/1000 + (k:ℚ)*50/1000, 2236/1000 + ((k:ℚ)+1)*50/1000, by
    have hk : (0:ℚ) ≤ (k:ℚ) := by exact_mod_cast Nat.zero_le k
    linarith⟩)

theorem slabs_checked : checkExprLeOnSlabsDyadic lhsE rhsE slabs (-50) 6 = true := by
  native_decide

theorem eval_lhsE (s : ℝ) :
    Expr.eval (fun _ => s) lhsE
      = (195/100 + (39/10) * (s*s)⁻¹ + (195/10) * ((s*s)*(s*s))⁻¹) * Real.exp (-(s*s)/2)
        + (10452/10000) * (s*s) * Real.exp (-(s*s)) := by
  have h8 : Real.exp (s^2 * (-1/16 : ℝ)) ^ 8 = Real.exp (s^2 * (-1/2 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h16 : Real.exp (s^2 * (-1/16 : ℝ)) ^ 16 = Real.exp (-s^2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [lhsE, pow8, sqx, s2, s4, e2, Expr.eval_add, Expr.eval_mul, Expr.eval_const,
    Expr.eval_inv, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8, h16]

theorem eval_rhsE (s : ℝ) :
    Expr.eval (fun _ => s) rhsE
      = (169029/1000000) * (s*s*s) * Real.exp (-(63577/100000) * s) := by
  have h8 : Real.exp (s * (-63577/800000 : ℝ)) ^ 8 = Real.exp (s * (-63577/100000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [rhsE, pow8, sqx, s3, s2, eR, Expr.eval_mul, Expr.eval_const,
    Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support : ExprSupportedWithInv (Expr.sub lhsE rhsE) := by
  simp only [Expr.sub, lhsE, rhsE, pow8, sqx, s2, s3, s4, e2, eR]
  repeat constructor

theorem cover (s : ℝ) (h : s ∈ Set.Icc (2.236 : ℝ) 3.163) :
    ∃ I ∈ slabs, s ∈ Set.Icc (I.lo : ℝ) I.hi := by
  obtain ⟨hlo, hhi⟩ := h
  set k : ℕ := ⌊(s - 2.236) / 0.05⌋₊ with hk_def
  have hsub_nn : (0:ℝ) ≤ (s - 2.236) / 0.05 := by
    apply div_nonneg <;> linarith
  have hk_lt : k < 19 := by
    have hub : (s - 2.236) / 0.05 < 19 := by
      rw [div_lt_iff₀ (by norm_num)]; linarith
    rw [hk_def]
    exact Nat.floor_lt hsub_nn |>.mpr (by exact_mod_cast hub)
  refine ⟨⟨2236/1000 + (k:ℚ)*50/1000, 2236/1000 + ((k:ℚ)+1)*50/1000, by
    have hknn : (0:ℚ) ≤ (k:ℚ) := by exact_mod_cast Nat.zero_le k
    linarith⟩, ?_, ?_⟩
  · rw [slabs, List.mem_map]
    exact ⟨k, List.mem_range.mpr hk_lt, rfl⟩
  · have hfloor_le : (k : ℝ) ≤ (s - 2.236) / 0.05 := by
      have := Nat.floor_le hsub_nn
      rwa [← hk_def] at this
    have hlt_floor : (s - 2.236) / 0.05 < (k : ℝ) + 1 := by
      have := Nat.lt_floor_add_one ((s - 2.236) / 0.05)
      rwa [← hk_def] at this
    constructor
    · push_cast
      rw [le_div_iff₀ (by norm_num)] at hfloor_le
      norm_num
      linarith [hfloor_le]
    · push_cast
      rw [div_lt_iff₀ (by norm_num)] at hlt_floor
      norm_num
      linarith [hlt_floor]

theorem rhsE_le_rowcurve (x : ℝ) (hL : (5 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE
      ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x := by
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [eval_rhsE]
  exact rowcurve_dom_three_halves 2.22 1.5 (169029/1000000) (63577/100000) x hLnn
    (by have h2 := R5_rpow_three_halves_le; have h3 := R5_rpow_three_halves_pos
        have h1 : (169029/1000000:ℝ) ≤ 2.22 / 13.1338 := by norm_num
        have h4 : (2.22:ℝ) / 13.1338 ≤ 2.22 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) h3 h2
        linarith)
    (by rw [div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb]) (by norm_num)

theorem Epi_le_evalLhsE (x : ℝ) (h5 : Real.exp 5 ≤ x) (h10 : x ≤ Real.exp 10) :
    Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) lhsE := by
  have he5 : (2:ℝ) ≤ Real.exp 5 := by
    have := Real.add_one_le_exp (5:ℝ); linarith
  have hx2 : (2:ℝ) ≤ x := le_trans he5 h5
  have hxpos : (0:ℝ) < x := by linarith
  have hLge5 : (5:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 5]; exact Real.log_le_log (Real.exp_pos _) h5
  have hLpos : (0:ℝ) < Real.log x := by linarith
  have hLnn : (0:ℝ) ≤ Real.log x := le_of_lt hLpos
  have hx19 : x ≤ 10 ^ 19 := by
    have h2 : Real.exp 10 < (3:ℝ) ^ 10 := by
      calc Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 3 ^ 10 := by
            have h1 := Real.exp_one_lt_d9
            have hlt : Real.exp 1 < 3 := by linarith
            gcongr
    have h3 : (3:ℝ) ^ 10 ≤ 10 ^ 19 := by norm_num
    linarith [h10]
  have h2e := Buthe.theorem_2e hx2 hx19
  have h2f := Buthe.theorem_2f hx2 hx19
  have hsub := li.sub_Li x hx2
  have hli2 := li.two_approx
  have hli2_le : li 2 ≤ 1.0452 := hli2.2
  have hpiLi : pi x - Li x = li 2 - (li x - pi x) := by linarith [hsub]
  have habs : |pi x - Li x| ≤ (li x - pi x) + li 2 := by
    rw [hpiLi, abs_le]
    constructor <;> linarith [h2f, hli2.1]
  have hEpi_eq : Eπ x = |pi x - Li x| * (Real.log x / x) := by
    unfold Eπ
    rw [div_div_eq_mul_div, mul_div_assoc]
  rw [hEpi_eq]
  set B := Real.sqrt x / Real.log x * (1.95 + 3.9 / Real.log x + 19.5 / (Real.log x) ^ 2) with hB_def
  have hfactor_nn : (0:ℝ) ≤ Real.log x / x := by positivity
  have hstep1 : |pi x - Li x| * (Real.log x / x) ≤ (B + 1.0452) * (Real.log x / x) := by
    apply mul_le_mul_of_nonneg_right _ hfactor_nn
    calc |pi x - Li x| ≤ (li x - pi x) + li 2 := habs
      _ ≤ B + 1.0452 := by
          apply add_le_add
          · rw [hB_def]; exact h2e
          · exact hli2_le
  refine le_trans hstep1 (le_of_eq ?_)
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hLne : Real.log x ≠ 0 := ne_of_gt hLpos
  have hxinv : x⁻¹ = Real.exp (-(Real.log x)) := by
    rw [Real.exp_neg, Real.exp_log hxpos]
  have hsqrtx : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.mpr hxpos), Real.log_sqrt (le_of_lt hxpos)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hss : s * s = Real.log x := by rw [hs_def]; exact Real.mul_self_sqrt hLnn
  rw [eval_lhsE, hss]
  set L := Real.log x with hL_def
  have hLx : L / x = L * Real.exp (-L) := by
    rw [div_eq_mul_inv, hxinv]
  have hsqrtxE2 : Real.sqrt x * Real.exp (-L) = Real.exp (-L / 2) := by
    rw [hsqrtx, ← Real.exp_add]; congr 1; ring
  rw [hB_def, hLx]
  rw [show (Real.sqrt x / L * (1.95 + 3.9 / L + 19.5 / L ^ 2) + 1.0452) * (L * Real.exp (-L))
      = (Real.sqrt x * Real.exp (-L)) * (1.95 + 3.9 / L + 19.5 / L ^ 2)
        + 1.0452 * (L * Real.exp (-L)) by
        field_simp]
  rw [hsqrtxE2]
  ring

/-- Generic Buthe floor assembler: any curve `rE` whose dyadic slab check passes
(`hchk`) and which dominates the admissible curve on `[e^5, e^10]` (`hcurve`)
gives `Eπ ≤` that curve there.  The Buthe `Eπ`-upper-bound (`lhsE`,
`Epi_le_evalLhsE`) and the slab cover (`slabs`, `cover`) are curve-independent and
reused by every row.  Bottoms out only at Buthe `theorem_2e/2f` + `li.two_approx`. -/
theorem floor_buthe_of_curve (rE : Expr) (A B C : ℝ)
    (hsupp : ExprSupportedWithInv (Expr.sub lhsE rE))
    (hchk : checkExprLeOnSlabsDyadic lhsE rE slabs (-50) 6 = true)
    (hcurve : ∀ x, (5:ℝ) ≤ Real.log x →
        Expr.eval (fun _ => Real.sqrt (Real.log x)) rE ≤ admissible_bound A B C 5.5666305 x) :
    ∀ x ∈ Set.Icc (Real.exp 5) (Real.exp 10),
      Eπ x ≤ admissible_bound A B C 5.5666305 x := by
  intro x hx
  obtain ⟨h5, h10⟩ := hx
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) h5
  have hLge5 : (5:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 5]; exact Real.log_le_log (Real.exp_pos _) h5
  have hLle10 : Real.log x ≤ 10 := by
    rw [← Real.log_exp 10]; exact Real.log_le_log hxpos h10
  have hs_mem : Real.sqrt (Real.log x) ∈ Set.Icc (2.236 : ℝ) 3.163 := by
    constructor
    · rw [show (2.236:ℝ) = Real.sqrt (2.236^2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [hLge5])
    · rw [show (3.163:ℝ) = Real.sqrt (3.163^2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [hLle10])
  obtain ⟨I, hI, hmem⟩ := cover _ hs_mem
  calc Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) lhsE := Epi_le_evalLhsE x h5 h10
    _ ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) rE :=
        verify_expr_le_on_slabs_dyadic lhsE rE slabs (-50) 6 hsupp (by norm_num) hchk I hI _ hmem
    _ ≤ admissible_bound A B C 5.5666305 x := hcurve x hLge5

/-- Row-5 floor, Buthe segment `[e^5, e^10]`, via the generic assembler. -/
theorem floor_buthe : ∀ x ∈ Set.Icc (Real.exp 5) (Real.exp 10),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x :=
  floor_buthe_of_curve rhsE 2.22 1.5 1.5 support slabs_checked rhsE_le_rowcurve

end FloorButhe

/-- Generalized Buthe floor assembler: like `FloorButhe.floor_buthe_of_curve` but
with an arbitrary split point `xlo ≥ 5` and slab list `slabsFrom slabLo n`, so the
slab interval can start above `√5` for rows whose curve the Buthe bound only clears
higher up (e.g. row 3 at `√6`).  `xlo ≥ 5` keeps `Epi_le_evalLhsE` applicable. -/
theorem floor_buthe_of_curve_gen (rE : Expr) (A B C : ℝ) (xlo : ℝ) (slabLo : ℚ) (n : ℕ)
    (hxlo : (5:ℝ) ≤ xlo)
    (hslo : (slabLo:ℝ) ≤ Real.sqrt xlo)
    (hshi : Real.sqrt 10 < (slabLo:ℝ) + (n:ℝ) * 0.05)
    (hsupp : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rE))
    (hchk : checkExprLeOnSlabsDyadic FloorButhe.lhsE rE (slabsFrom slabLo n) (-50) 6 = true)
    (hcurve : ∀ x, xlo ≤ Real.log x →
        Expr.eval (fun _ => Real.sqrt (Real.log x)) rE ≤ admissible_bound A B C 5.5666305 x) :
    ∀ x ∈ Set.Icc (Real.exp xlo) (Real.exp 10),
      Eπ x ≤ admissible_bound A B C 5.5666305 x := by
  intro x hx
  obtain ⟨hlo, h10⟩ := hx
  have h5 : Real.exp 5 ≤ x := le_trans (Real.exp_le_exp.mpr hxlo) hlo
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) h5
  have hLgexlo : xlo ≤ Real.log x := by
    rw [← Real.log_exp xlo]; exact Real.log_le_log (Real.exp_pos _) hlo
  have hLle10 : Real.log x ≤ 10 := by
    rw [← Real.log_exp 10]; exact Real.log_le_log hxpos h10
  have hcov_lo : (slabLo:ℝ) ≤ Real.sqrt (Real.log x) :=
    le_trans hslo (Real.sqrt_le_sqrt hLgexlo)
  have hcov_hi : Real.sqrt (Real.log x) < (slabLo:ℝ) + (n:ℝ) * 0.05 :=
    lt_of_le_of_lt (Real.sqrt_le_sqrt hLle10) hshi
  obtain ⟨I, hI, hmem⟩ := coverFrom slabLo n _ hcov_lo hcov_hi
  calc Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE :=
        FloorButhe.Epi_le_evalLhsE x h5 h10
    _ ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) rE :=
        verify_expr_le_on_slabs_dyadic FloorButhe.lhsE rE (slabsFrom slabLo n) (-50) 6
          hsupp (by norm_num) hchk I hI _ hmem
    _ ≤ admissible_bound A B C 5.5666305 x := hcurve x hLgexlo

/-! ## Shared `B = 1/4` helpers (rows 1/2) -/

/-- `admissible_bound A (1/4) C R x` in terms of `s = √(log x)`:
`= (A/R^{1/4})·√s·exp(−(C/√R)·s)`.  (`√s = (log x)^{1/4}`.) -/
lemma admissible_quarter_eq (A C R x : ℝ) (hL : 0 ≤ Real.log x) (hR : 0 < R) :
    admissible_bound A 0.25 C R x
      = (A / R ^ ((1:ℝ)/4)) * Real.sqrt (Real.sqrt (Real.log x))
        * Real.exp (-(C / Real.sqrt R) * Real.sqrt (Real.log x)) := by
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_rpow : s = Real.log x ^ ((1:ℝ)/2) := by rw [hs_def, Real.sqrt_eq_rpow]
  have hsqrts : Real.sqrt s = Real.log x ^ ((1:ℝ)/4) := by
    rw [hs_def, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hL]; norm_num
  unfold admissible_bound
  have e1 : (Real.log x / R) ^ (0.25:ℝ) = Real.sqrt s / R ^ ((1:ℝ)/4) := by
    rw [show (0.25:ℝ) = (1:ℝ)/4 by norm_num, Real.div_rpow hL hR.le, ← hsqrts]
  have e2 : (Real.log x / R) ^ ((1:ℝ)/2) = s / Real.sqrt R := by
    rw [Real.div_rpow hL hR.le, Real.sqrt_eq_rpow R, ← hs_rpow]
  rw [e1, e2, show -C * (s / Real.sqrt R) = -(C / Real.sqrt R) * s by ring]
  ring

/-- `R^{1/4} = √(√R)`. -/
lemma R5_rpow_quarter_eq : (5.5666305:ℝ) ^ ((1:ℝ)/4) = Real.sqrt (Real.sqrt 5.5666305) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; norm_num

/-- `R^{1/4} ≤ 1.53603`. -/
lemma R5_rpow_quarter_le : (5.5666305:ℝ) ^ ((1:ℝ)/4) ≤ 1.53603 := by
  rw [R5_rpow_quarter_eq]
  rw [show (1.53603:ℝ) = Real.sqrt (1.53603^2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [sqrtR5_ub]

/-- Buthe `Eπ`-upper-bound reconciliation over the WIDE range `[e^5, e^40]`
(vs `FloorButhe.Epi_le_evalLhsE`'s `[e^5,e^10]`): identical proof, only the
`x ≤ 10^19` derivation uses `x ≤ e^40` (`e^40 ≈ 2.4e17 < 10^19`).  Needed for
row 1's near-threshold boundary `[e^22.955, e^40]`. -/
theorem Epi_le_evalLhsE_wide (x : ℝ) (h5 : Real.exp 5 ≤ x) (h40 : x ≤ Real.exp 40) :
    Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE := by
  have he5 : (2:ℝ) ≤ Real.exp 5 := by
    have := Real.add_one_le_exp (5:ℝ); linarith
  have hx2 : (2:ℝ) ≤ x := le_trans he5 h5
  have hxpos : (0:ℝ) < x := by linarith
  have hLge5 : (5:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 5]; exact Real.log_le_log (Real.exp_pos _) h5
  have hLpos : (0:ℝ) < Real.log x := by linarith
  have hLnn : (0:ℝ) ≤ Real.log x := le_of_lt hLpos
  have hx19 : x ≤ 10 ^ 19 := by
    have h2 : Real.exp 40 ≤ (2.72:ℝ) ^ 40 := by
      have he : Real.exp 40 = Real.exp 1 ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
      rw [he]; gcongr
      linarith [Real.exp_one_lt_d9]
    have h3 : (2.72:ℝ) ^ 40 ≤ 10 ^ 19 := by norm_num
    linarith [h40]
  have h2e := Buthe.theorem_2e hx2 hx19
  have h2f := Buthe.theorem_2f hx2 hx19
  have hsub := li.sub_Li x hx2
  have hli2 := li.two_approx
  have hli2_le : li 2 ≤ 1.0452 := hli2.2
  have hpiLi : pi x - Li x = li 2 - (li x - pi x) := by linarith [hsub]
  have habs : |pi x - Li x| ≤ (li x - pi x) + li 2 := by
    rw [hpiLi, abs_le]
    constructor <;> linarith [h2f, hli2.1]
  have hEpi_eq : Eπ x = |pi x - Li x| * (Real.log x / x) := by
    unfold Eπ
    rw [div_div_eq_mul_div, mul_div_assoc]
  rw [hEpi_eq]
  set B := Real.sqrt x / Real.log x * (1.95 + 3.9 / Real.log x + 19.5 / (Real.log x) ^ 2) with hB_def
  have hfactor_nn : (0:ℝ) ≤ Real.log x / x := by positivity
  have hstep1 : |pi x - Li x| * (Real.log x / x) ≤ (B + 1.0452) * (Real.log x / x) := by
    apply mul_le_mul_of_nonneg_right _ hfactor_nn
    calc |pi x - Li x| ≤ (li x - pi x) + li 2 := habs
      _ ≤ B + 1.0452 := by
          apply add_le_add
          · rw [hB_def]; exact h2e
          · exact hli2_le
  refine le_trans hstep1 (le_of_eq ?_)
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hLne : Real.log x ≠ 0 := ne_of_gt hLpos
  have hxinv : x⁻¹ = Real.exp (-(Real.log x)) := by
    rw [Real.exp_neg, Real.exp_log hxpos]
  have hsqrtx : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.mpr hxpos), Real.log_sqrt (le_of_lt hxpos)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hss : s * s = Real.log x := by rw [hs_def]; exact Real.mul_self_sqrt hLnn
  rw [FloorButhe.eval_lhsE, hss]
  set L := Real.log x with hL_def
  have hLx : L / x = L * Real.exp (-L) := by
    rw [div_eq_mul_inv, hxinv]
  have hsqrtxE2 : Real.sqrt x * Real.exp (-L) = Real.exp (-L / 2) := by
    rw [hsqrtx, ← Real.exp_add]; congr 1; ring
  rw [hB_def, hLx]
  rw [show (Real.sqrt x / L * (1.95 + 3.9 / L + 19.5 / L ^ 2) + 1.0452) * (L * Real.exp (-L))
      = (Real.sqrt x * Real.exp (-L)) * (1.95 + 3.9 / L + 19.5 / L ^ 2)
        + 1.0452 * (L * Real.exp (-L)) by
        field_simp]
  rw [hsqrtxE2]
  ring

/-- Quarter (`B=1/4`) Buthe floor assembler on `[e^xlo, e^10]`: the SQUARED slab
check `lhsE² ≤ rhsE2` plus the squared-curve domination, sqrt taken outside the
kernel.  Companion of `floor_buthe_of_curve_gen` for the half-power rows. -/
theorem floor_buthe_quarter_of_curve (rhsE2 : Expr) (A C : ℝ) (xlo : ℝ) (slabLo : ℚ) (n : ℕ)
    (hApos : 0 < A)
    (hxlo : (5:ℝ) ≤ xlo)
    (hslo : (slabLo:ℝ) ≤ Real.sqrt xlo)
    (hshi : Real.sqrt 10 < (slabLo:ℝ) + (n:ℝ) * 0.05)
    (hsupp : ExprSupportedWithInv (Expr.sub (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2))
    (hchk : checkExprLeOnSlabsDyadic (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2
        (slabsFrom slabLo n) (-50) 6 = true)
    (hcurve2 : ∀ x, xlo ≤ Real.log x →
        Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE2
          ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2) :
    ∀ x ∈ Set.Icc (Real.exp xlo) (Real.exp 10),
      Eπ x ≤ admissible_bound A 0.25 C 5.5666305 x := by
  intro x hx
  obtain ⟨hlo, h10⟩ := hx
  have h5 : Real.exp 5 ≤ x := le_trans (Real.exp_le_exp.mpr hxlo) hlo
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) h5
  have hLgexlo : xlo ≤ Real.log x := by
    rw [← Real.log_exp xlo]; exact Real.log_le_log (Real.exp_pos _) hlo
  have hLle10 : Real.log x ≤ 10 := by
    rw [← Real.log_exp 10]; exact Real.log_le_log hxpos h10
  have hLpos : (0:ℝ) < Real.log x := lt_of_lt_of_le (by linarith) hLgexlo
  have hcov_lo : (slabLo:ℝ) ≤ Real.sqrt (Real.log x) :=
    le_trans hslo (Real.sqrt_le_sqrt hLgexlo)
  have hcov_hi : Real.sqrt (Real.log x) < (slabLo:ℝ) + (n:ℝ) * 0.05 :=
    lt_of_le_of_lt (Real.sqrt_le_sqrt hLle10) hshi
  obtain ⟨I, hI, hmem⟩ := coverFrom slabLo n _ hcov_lo hcov_hi
  have hslab2 := verify_expr_le_on_slabs_dyadic (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2
    (slabsFrom slabLo n) (-50) 6 hsupp (by norm_num) hchk I hI _ hmem
  rw [Expr.eval_mul] at hslab2
  set L := Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE with hL_def
  have hL_nn : (0:ℝ) ≤ L := by
    rw [hL_def, FloorButhe.eval_lhsE]; positivity
  have hadm_nn : (0:ℝ) ≤ admissible_bound A 0.25 C 5.5666305 x := by
    rw [admissible_quarter_eq A C 5.5666305 x hLpos.le (by norm_num)]; positivity
  have hsq : L ^ 2 ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2 := by
    calc L ^ 2 = L * L := sq L
      _ ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE2 := hslab2
      _ ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2 := hcurve2 x hLgexlo
  have hL_le : L ≤ admissible_bound A 0.25 C 5.5666305 x := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hL_nn, Real.sqrt_sq hadm_nn] at this
  exact le_trans (FloorButhe.Epi_le_evalLhsE x h5 h10) hL_le

/-- Wide quarter Buthe floor assembler over `[e^xlo, e^xhi]` (`5 ≤ xlo`, `xhi ≤ 40`),
using `Epi_le_evalLhsE_wide` (for row 1's near-threshold boundary, depth 8). -/
theorem floor_buthe_quarter_wide (rhsE2 : Expr) (A C : ℝ) (xlo xhi : ℝ) (slabLo : ℚ) (n : ℕ)
    (hApos : 0 < A)
    (hxlo5 : (5:ℝ) ≤ xlo) (hxhi40 : xhi ≤ 40)
    (hslo : (slabLo:ℝ) ≤ Real.sqrt xlo)
    (hshi : Real.sqrt xhi < (slabLo:ℝ) + (n:ℝ) * 0.05)
    (hsupp : ExprSupportedWithInv (Expr.sub (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2))
    (hchk : checkExprLeOnSlabsDyadic (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2
        (slabsFrom slabLo n) (-50) 8 = true)
    (hcurve2 : ∀ x, xlo ≤ Real.log x →
        Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE2
          ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2) :
    ∀ x ∈ Set.Icc (Real.exp xlo) (Real.exp xhi),
      Eπ x ≤ admissible_bound A 0.25 C 5.5666305 x := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hx
  have h5 : Real.exp 5 ≤ x := le_trans (Real.exp_le_exp.mpr hxlo5) hlo
  have h40 : x ≤ Real.exp 40 := le_trans hhi (Real.exp_le_exp.mpr hxhi40)
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) h5
  have hLgexlo : xlo ≤ Real.log x := by
    rw [← Real.log_exp xlo]; exact Real.log_le_log (Real.exp_pos _) hlo
  have hLlexhi : Real.log x ≤ xhi := by
    rw [← Real.log_exp xhi]; exact Real.log_le_log hxpos hhi
  have hLpos : (0:ℝ) < Real.log x := lt_of_lt_of_le (by linarith) hLgexlo
  have hcov_lo : (slabLo:ℝ) ≤ Real.sqrt (Real.log x) :=
    le_trans hslo (Real.sqrt_le_sqrt hLgexlo)
  have hcov_hi : Real.sqrt (Real.log x) < (slabLo:ℝ) + (n:ℝ) * 0.05 :=
    lt_of_le_of_lt (Real.sqrt_le_sqrt hLlexhi) hshi
  obtain ⟨I, hI, hmem⟩ := coverFrom slabLo n _ hcov_lo hcov_hi
  have hslab2 := verify_expr_le_on_slabs_dyadic (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2
    (slabsFrom slabLo n) (-50) 8 hsupp (by norm_num) hchk I hI _ hmem
  rw [Expr.eval_mul] at hslab2
  set Lh := Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE with hLh_def
  have hLh_nn : (0:ℝ) ≤ Lh := by
    rw [hLh_def, FloorButhe.eval_lhsE]; positivity
  have hadm_nn : (0:ℝ) ≤ admissible_bound A 0.25 C 5.5666305 x := by
    rw [admissible_quarter_eq A C 5.5666305 x hLpos.le (by norm_num)]; positivity
  have hsq : Lh ^ 2 ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2 := by
    calc Lh ^ 2 = Lh * Lh := sq Lh
      _ ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE2 := hslab2
      _ ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2 := hcurve2 x hLgexlo
  have hLh_le : Lh ≤ admissible_bound A 0.25 C 5.5666305 x := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hLh_nn, Real.sqrt_sq hadm_nn] at this
  exact le_trans (Epi_le_evalLhsE_wide x h5 h40) hLh_le

/-- Row-5 floor `[exp 3, e^10]`. Split at `e^5`:
* `[e^5, e^10]`: proven via `FloorButhe.floor_buthe` (Buthe `2e/2f` + dyadic cover);
* `[e^3, e^5]` (`x ∈ [20, 148]`): **trusted numerical boundary** — the direct
  `π`/`Li` interpolation of \cite[Lemmas 5.2, 5.3]{FKS} that the blueprint proof
  invokes; no tight sub-`e^10` `Eπ` envelope exists in the library (Buthe `2e` is
  too loose below `e^5`, and the `eq_30` θ→π overhead exceeds the curve at `x=20`).
  This `sorry` is the same class of accepted numerical-data trust as
  `Table4Ext.allCells_trusted` (`x ≥ e^10`). -/
theorem floor_row5 : ∀ x ∈ Set.Icc (exp (3:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x := by
  intro x hx
  obtain ⟨h3, h10⟩ := hx
  by_cases h5 : Real.exp 5 ≤ x
  · exact FloorButhe.floor_buthe x ⟨h5, h10⟩
  · sorry

/-- **Corollary 23, row 5** `(A=2.22, B=3/2, C=3/2, x₀=3)`. -/
theorem corollary_23_row5 : Eπ.classicalBound 2.22 1.5 1.5 5.5666305 (exp 3) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row5 x ⟨hx, h10⟩
  · rw [not_le] at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row5 x ⟨le_of_lt h10, h20k⟩
    · rw [not_le] at h20k
      exact tail_row5 x (le_of_lt h20k)

end FKS2
