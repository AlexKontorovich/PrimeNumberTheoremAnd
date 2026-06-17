import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.List.Sort
import LeanCert.Tactic.IntervalAuto
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_a2_bounds

open Real Set Finset

namespace BKLNW

/-! Table 10 next-certificate machinery.

The scalable route is to prove the b-column strictly sorted once, then instantiate
`table_10_next_get` for adjacent entries. That avoids per-row `sInf` case splits over the
287-row table. -/

/-- The b-column of the unabridged Table 10. -/
noncomputable abbrev table_10_bcol : List ℝ := BKLNW.table_10.map (·.1)

set_option maxRecDepth 100000 in
lemma table_10_bcol_length : table_10_bcol.length = 287 := by
  simp [table_10_bcol, BKLNW.table_10]

set_option maxRecDepth 100000 in
lemma table_10_bcol_sortedLT : table_10_bcol.SortedLT := by
  rw [List.sortedLT_iff_isChain]
  simp only [table_10_bcol, table_10, List.map_cons, List.map_nil]
  repeat' constructor
  all_goals
    try norm_num
    try nlinarith [LogTables.log_10_gt]
    try nlinarith [LogTables.log_10_lt]

set_option maxRecDepth 100000 in
lemma table_10_bcol_le_K :
    ∀ idx : Fin table_10_bcol.length, table_10_bcol.get idx ≤ (K : ℝ) := by
  intro idx
  have hmem : table_10_bcol.get idx ∈ table_10_entries := by
    simpa [table_10_entries, table_10_bcol] using List.get_mem table_10_bcol idx
  exact (table_10_entry_lt_K _ hmem).le

set_option maxRecDepth 100000 in
def table_10_bidx (idx : Fin table_10.length) : Fin table_10_bcol.length :=
  ⟨idx.1, by
    change idx.1 < (table_10.map (·.1)).length
    simpa only [List.length_map] using idx.2⟩

set_option maxRecDepth 100000 in
lemma table_10_bcol_get_bidx (idx : Fin table_10.length) :
    table_10_bcol.get (table_10_bidx idx) = (table_10.get idx).1 := by
  simp [table_10_bidx, table_10_bcol]

set_option maxRecDepth 100000 in
lemma table_10_bidx_eq_of_get_eq {i : Fin table_10_bcol.length} {j : Fin table_10.length}
    (h : table_10_bcol.get i = (table_10.get j).1) : i = table_10_bidx j := by
  apply table_10_bcol_sortedLT.strictMono_get.injective
  simpa [table_10_bcol_get_bidx] using! h

lemma table_10_bs_mem_iff {z : ℝ} :
    z ∈ table_10_bs ↔ z ∈ table_10_bcol ∨ z = (K : ℝ) := by
  simp only [table_10_bs, Finset.union_singleton, Finset.mem_insert, List.mem_toFinset,
    table_10_entries, table_10_bcol]
  tauto

lemma table_10_next_eq_of_adjacent {x y : ℝ} (hxy : x < y) (hy : y ∈ table_10_bs)
    (hmin : ∀ z ∈ table_10_bs, x < z → y ≤ z) : table_10_next x = y := by
  have hne : (table_10_bs.filter (x < ·)).Nonempty :=
    ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
  rw [table_10_next_eq_min' x hne]
  apply le_antisymm
  · exact Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hy, hxy⟩)
  · apply Finset.le_min'
    intro z hz
    obtain ⟨hz_mem, hz_gt⟩ := Finset.mem_filter.mp hz
    exact hmin z hz_mem hz_gt

lemma table_10_next_get (hs : table_10_bcol.SortedLT)
    (htop : ∀ idx : Fin table_10_bcol.length, table_10_bcol.get idx ≤ (K : ℝ))
    (i : ℕ) (h1 : i + 1 < table_10_bcol.length) :
    table_10_next (table_10_bcol.get ⟨i, by omega⟩) =
      table_10_bcol.get ⟨i + 1, h1⟩ := by
  have hmono : StrictMono table_10_bcol.get := hs.strictMono_get
  apply table_10_next_eq_of_adjacent
  · exact hmono (show (⟨i, by omega⟩ : Fin table_10_bcol.length) < ⟨i + 1, h1⟩ by
      simp [Fin.lt_def])
  · exact table_10_bs_mem_iff.mpr (Or.inl (table_10_bcol.get_mem _))
  · intro z hz hgt
    rcases table_10_bs_mem_iff.mp hz with hzL | hzK
    · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hzL
      have hij : (⟨i, by omega⟩ : Fin table_10_bcol.length) < j := by
        by_contra hle
        push Not at hle
        exact absurd (hmono.le_iff_le.mpr hle) (not_le.mpr hgt)
      have hle' : (⟨i + 1, h1⟩ : Fin table_10_bcol.length) ≤ j := by
        simp only [Fin.lt_def, Fin.le_def] at hij ⊢
        omega
      exact hmono.le_iff_le.mpr hle'
    · rw [hzK]
      exact htop _

/-! Generic one-term derivative machinery (parametric in the decay rate `c`). -/

noncomputable def expT (c y : ℝ) : ℝ := y ^ 5 * Real.exp (-(c * y))
noncomputable def expTd (c y : ℝ) : ℝ := (5 * y ^ 4 - c * y ^ 5) * Real.exp (-(c * y))
noncomputable def expTdd (c y : ℝ) : ℝ := (c ^ 2 * y ^ 5 - 10 * c * y ^ 4 + 20 * y ^ 3) * Real.exp (-(c * y))

lemma expT_hasDerivAt (c y : ℝ) : HasDerivAt (expT c) (expTd c y) y := by
  unfold expT expTd
  have hp : HasDerivAt (fun u : ℝ => u ^ 5) (5 * y ^ 4) y := by simpa using hasDerivAt_pow 5 y
  have hlin : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y := ((hasDerivAt_id y).const_mul c).neg
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(c * u))) (Real.exp (-(c * y)) * (-(c * 1))) y := hlin.exp
  convert! hp.mul he using 1
  ring

lemma expTd_hasDerivAt (c y : ℝ) : HasDerivAt (expTd c) (expTdd c y) y := by
  unfold expTd expTdd
  have hP : HasDerivAt (fun u : ℝ => 5 * u ^ 4 - c * u ^ 5) (20 * y ^ 3 - 5 * c * y ^ 4) y := by
    have h4 : HasDerivAt (fun u : ℝ => u ^ 4) (4 * y ^ 3) y := by simpa using hasDerivAt_pow 4 y
    have h5 : HasDerivAt (fun u : ℝ => u ^ 5) (5 * y ^ 4) y := by simpa using hasDerivAt_pow 5 y
    convert! (h4.const_mul (5 : ℝ)).sub (h5.const_mul c) using 1
    ring
  have hlin : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y := ((hasDerivAt_id y).const_mul c).neg
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(c * u))) (Real.exp (-(c * y)) * (-(c * 1))) y := hlin.exp
  convert! hP.mul he using 1
  ring

/-! Parameterized majorant `Gp A₁ A₂ E` and its convexity on any [b,b'] with 20 ≤ b. -/

noncomputable def Gp (A₁ A₂ E y : ℝ) : ℝ := A₁ * expT (1 / 2) y + A₂ * expT (2 / 3) y + E * y ^ 5
noncomputable def Gp' (A₁ A₂ E y : ℝ) : ℝ := A₁ * expTd (1 / 2) y + A₂ * expTd (2 / 3) y + E * (5 * y ^ 4)
noncomputable def Gp'' (A₁ A₂ E y : ℝ) : ℝ := A₁ * expTdd (1 / 2) y + A₂ * expTdd (2 / 3) y + E * (20 * y ^ 3)

lemma Gp_hasDerivAt (A₁ A₂ E y : ℝ) : HasDerivAt (Gp A₁ A₂ E) (Gp' A₁ A₂ E y) y := by
  unfold Gp Gp'
  have h1 := (expT_hasDerivAt (1 / 2) y).const_mul A₁
  have h2 := (expT_hasDerivAt (2 / 3) y).const_mul A₂
  have h3 : HasDerivAt (fun u : ℝ => E * u ^ 5) (E * (5 * y ^ 4)) y := by
    have h5 : HasDerivAt (fun u : ℝ => u ^ 5) (5 * y ^ 4) y := by simpa using hasDerivAt_pow 5 y
    exact h5.const_mul _
  convert! (h1.add h2).add h3 using 1

lemma Gp'_hasDerivAt (A₁ A₂ E y : ℝ) : HasDerivAt (Gp' A₁ A₂ E) (Gp'' A₁ A₂ E y) y := by
  unfold Gp' Gp''
  have h1 := (expTd_hasDerivAt (1 / 2) y).const_mul A₁
  have h2 := (expTd_hasDerivAt (2 / 3) y).const_mul A₂
  have h3 : HasDerivAt (fun u : ℝ => E * (5 * u ^ 4)) (E * (20 * y ^ 3)) y := by
    have h4 : HasDerivAt (fun u : ℝ => u ^ 4) (4 * y ^ 3) y := by simpa using hasDerivAt_pow 4 y
    convert! (h4.const_mul (5 : ℝ)).const_mul E using 1
    ring
  convert! (h1.add h2).add h3 using 1

lemma Gp_continuous (A₁ A₂ E : ℝ) : Continuous (Gp A₁ A₂ E) := by unfold Gp expT; fun_prop

lemma Gp''_nonneg {A₁ A₂ E : ℝ} (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) (hE : 0 ≤ E)
    {y : ℝ} (hy20 : 20 ≤ y) : 0 ≤ Gp'' A₁ A₂ E y := by
  have hy3 : (0 : ℝ) ≤ y ^ 3 := pow_nonneg (by linarith) 3
  unfold Gp'' expTdd
  have t1 : (0 : ℝ) ≤ A₁ *
      (((1 / 2 : ℝ) ^ 2 * y ^ 5 - 10 * (1 / 2) * y ^ 4 + 20 * y ^ 3) * Real.exp (-((1 / 2 : ℝ) * y))) := by
    apply mul_nonneg hA1
    apply mul_nonneg _ (Real.exp_pos _).le
    have hbr : (0 : ℝ) ≤ (1 / 4 : ℝ) * y ^ 2 - 5 * y + 20 := by nlinarith [hy20, sq_nonneg (y - 20)]
    nlinarith [mul_nonneg hy3 hbr]
  have t2 : (0 : ℝ) ≤ A₂ *
      (((2 / 3 : ℝ) ^ 2 * y ^ 5 - 10 * (2 / 3) * y ^ 4 + 20 * y ^ 3) * Real.exp (-((2 / 3 : ℝ) * y))) := by
    apply mul_nonneg hA2
    apply mul_nonneg _ (Real.exp_pos _).le
    have hbr : (0 : ℝ) ≤ (4 / 9 : ℝ) * y ^ 2 - (20 / 3) * y + 20 := by nlinarith [hy20, sq_nonneg (y - 20)]
    nlinarith [mul_nonneg hy3 hbr]
  have t3 : (0 : ℝ) ≤ E * (20 * y ^ 3) := mul_nonneg hE (by positivity)
  linarith [t1, t2, t3]

lemma Gp_convexOn {A₁ A₂ E : ℝ} (b b' : ℝ) (_hbb' : b ≤ b') (hb20 : 20 ≤ b)
    (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) (hE : 0 ≤ E) :
    ConvexOn ℝ (Set.Icc b b') (Gp A₁ A₂ E) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) (Gp_continuous A₁ A₂ E).continuousOn
  · intro y _; exact (Gp_hasDerivAt A₁ A₂ E y).hasDerivWithinAt
  · intro y _; exact (Gp'_hasDerivAt A₁ A₂ E y).hasDerivWithinAt
  · intro y hy; rw [interior_Icc] at hy; exact Gp''_nonneg hA1 hA2 hE (by linarith [hy.1])

/-! Keystone bridge from logarithmic pointwise bounds to `B`. -/

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
  change (∑ ℓ ∈ Finset.Icc 1 n, a ℓ * (log x) ^ k * x ^ (-(ℓ : ℝ) / (ℓ + 1)))
        + ε b * (log x) ^ k ≤ C
  rw [h_sum_eq]
  exact hC (log x) hy

/-! ## The parameterized row lemma: proven once; every row instantiates it. -/

-- (B_8_exact now declared in-tree at BKLNW.lean:1354 by the A+ retarget)

/-- Given coefficient upper bounds and the two endpoint values of the majorant under `291.60`,
    the exact Lemma-8 supremum for any row `[b,b']` (k=5, 20 ≤ b) is `≤ T`. -/
theorem row_bound_k5 (b b' A₁ A₂ E T : ℝ)
    (hbb' : b ≤ b') (hb20 : 20 ≤ b)
    (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) (hE : 0 ≤ E)
    (ha1 : Inputs.default.a₁ b ≤ A₁) (ha2 : Inputs.default.a₂ b ≤ A₂) (heps : Inputs.default.ε b ≤ E)
    (hGb : Gp A₁ A₂ E b ≤ T) (hGb' : Gp A₁ A₂ E b' ≤ T) :
    B_8_exact 5 b b' ≤ T := by
  unfold B_8_exact
  refine B_le_of_forall_log _ _ _ _ hbb' ?_
  intro y hy
  have hy0 : (0 : ℝ) ≤ y := by have := hy.1; linarith
  have hy5 : (0 : ℝ) ≤ y ^ 5 := pow_nonneg hy0 5
  have hconv : Gp A₁ A₂ E y ≤ T :=
    le_trans ((Gp_convexOn b b' hbb' hb20 hA1 hA2 hE).le_max_of_mem_Icc
      (left_mem_Icc.mpr hbb') (right_mem_Icc.mpr hbb') hy) (max_le hGb hGb')
  rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_insert (by decide), Finset.sum_singleton]
  have hif1 : (if (1 : ℕ) = 1 then Inputs.default.a₁ b else if (1 : ℕ) = 2 then Inputs.default.a₂ b else 0)
      = Inputs.default.a₁ b := by norm_num
  have hif2 : (if (2 : ℕ) = 1 then Inputs.default.a₁ b else if (2 : ℕ) = 2 then Inputs.default.a₂ b else 0)
      = Inputs.default.a₂ b := by norm_num
  have ce1 : Real.exp (-(((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(1 / 2 * y)) := by
    congr 1; push_cast; ring
  have ce2 : Real.exp (-(((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(2 / 3 * y)) := by
    congr 1; push_cast; ring
  rw [hif1, hif2, ce1, ce2]
  have e1 : (0 : ℝ) ≤ y ^ 5 * Real.exp (-(1 / 2 * y)) := mul_nonneg hy5 (Real.exp_pos _).le
  have e2 : (0 : ℝ) ≤ y ^ 5 * Real.exp (-(2 / 3 * y)) := mul_nonneg hy5 (Real.exp_pos _).le
  have h1 : Inputs.default.a₁ b * y ^ 5 * Real.exp (-(1 / 2 * y)) ≤ A₁ * (y ^ 5 * Real.exp (-(1 / 2 * y))) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ha1 e1
  have h2 : Inputs.default.a₂ b * y ^ 5 * Real.exp (-(2 / 3 * y)) ≤ A₂ * (y ^ 5 * Real.exp (-(2 / 3 * y))) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ha2 e2
  have h3 : Inputs.default.ε b * y ^ 5 ≤ E * y ^ 5 := mul_le_mul_of_nonneg_right heps hy5
  have hGpy : Gp A₁ A₂ E y
      = A₁ * (y ^ 5 * Real.exp (-(1 / 2 * y))) + A₂ * (y ^ 5 * Real.exp (-(2 / 3 * y))) + E * y ^ 5 := by
    unfold Gp expT; ring
  rw [hGpy] at hconv
  linarith [h1, h2, h3, hconv]

/-! Cert-free crude `a₂` bound + regime-2 row 60 (b'=65, crude a₂, convexity template). -/

lemma f_crude_le (x : ℝ) (hx : 1 ≤ x) : f x ≤ (⌊log x / log 2⌋₊ : ℝ) := by
  have hcard : ((Finset.Icc 3 ⌊log x / log 2⌋₊).card : ℝ) ≤ (⌊log x / log 2⌋₊ : ℝ) := by
    rw [Nat.card_Icc]
    have h : ⌊log x / log 2⌋₊ + 1 - 3 ≤ ⌊log x / log 2⌋₊ := by omega
    exact_mod_cast h
  unfold f
  calc ∑ k ∈ Finset.Icc 3 ⌊log x / log 2⌋₊, x ^ (1 / (k : ℝ) - 1 / 3)
      ≤ ∑ _k ∈ Finset.Icc 3 ⌊log x / log 2⌋₊, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
        apply Real.rpow_le_one_of_one_le_of_nonpos hx
        have hkr : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
        have : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hkr
        linarith
    _ = ((Finset.Icc 3 ⌊log x / log 2⌋₊).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (⌊log x / log 2⌋₊ : ℝ) := hcard

lemma a2_crude_le (b : ℝ) (hb : 0 ≤ b) :
    Inputs.default.a₂ b ≤ (1 + Inputs.default.α) * ((⌊b / log 2⌋₊ : ℝ) + 1) := by
  have hα : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hfe : f (exp b) ≤ (⌊b / log 2⌋₊ : ℝ) + 1 := by
    have := f_crude_le (exp b) (Real.one_le_exp hb)
    rw [Real.log_exp] at this
    linarith
  have hf2 : f ((2 : ℝ) ^ (⌊b / log 2⌋₊ + 1)) ≤ (⌊b / log 2⌋₊ : ℝ) + 1 := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (⌊b / log 2⌋₊ + 1) := one_le_pow₀ (by norm_num)
    have := f_crude_le ((2 : ℝ) ^ (⌊b / log 2⌋₊ + 1)) h1
    rw [Real.log_pow] at this
    rw [mul_div_assoc, div_self hlog2.ne', mul_one, Nat.floor_natCast] at this
    push_cast at this ⊢
    linarith
  have hmax : max (f (exp b)) (f ((2 : ℝ) ^ (⌊b / log 2⌋₊ + 1))) ≤ (⌊b / log 2⌋₊ : ℝ) + 1 :=
    max_le hfe hf2
  unfold Inputs.a₂
  gcongr

/-! ## v14: mid-tier cert-free a₂ bound (kills P3 of the big-PR plan)

Split `f`'s head (k = 3..12) explicitly and bound the tail (k ≥ 13) by its count times
the k = 13 term. Numerically this clears EVERY dense small-b row 20..43 of the unabridged
Table 10 (worst slack ~10%, row 23), so no per-row LeanCert a₂ certs are needed at all. -/

/-- Closed form: `f (exp b)` is the finite sum of `exp (b * (1/k - 1/3))`. -/
lemma f_exp_eq (b : ℝ) (K : ℕ) (hK : ⌊b / log 2⌋₊ = K) :
    f (Real.exp b) = ∑ k ∈ Finset.Icc 3 K, Real.exp (b * (1 / (k : ℝ) - 1 / 3)) := by
  unfold f
  rw [Real.log_exp, hK]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos b), Real.log_exp]

/-- The second `max` argument of `a₂` is dominated by the same exp-sum with one more term. -/
lemma f_two_pow_le (b : ℝ) (hb : 0 < b) (K : ℕ) (hK : ⌊b / log 2⌋₊ = K) :
    f ((2 : ℝ) ^ (K + 1)) ≤ ∑ k ∈ Finset.Icc 3 (K + 1), Real.exp (b * (1 / (k : ℝ) - 1 / 3)) := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have h2pow : (1 : ℝ) ≤ (2 : ℝ) ^ (K + 1) := one_le_pow₀ (by norm_num)
  have hidx : ⌊Real.log ((2 : ℝ) ^ (K + 1)) / Real.log 2⌋₊ = K + 1 := by
    rw [Real.log_pow, mul_div_assoc, div_self hlog2.ne', mul_one, Nat.floor_natCast]
  have hexp_le : Real.exp b ≤ (2 : ℝ) ^ (K + 1) := by
    have hb_lt : b < ((K : ℝ) + 1) * Real.log 2 := by
      have hfloor : b / Real.log 2 < (K : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (b / Real.log 2)
        rw [hK] at this
        exact_mod_cast this
      calc b = (b / Real.log 2) * Real.log 2 := by field_simp
        _ < ((K : ℝ) + 1) * Real.log 2 := by
            exact mul_lt_mul_of_pos_right hfloor hlog2
    calc Real.exp b ≤ Real.exp (((K : ℝ) + 1) * Real.log 2) := Real.exp_le_exp.mpr hb_lt.le
      _ = (2 : ℝ) ^ (K + 1) := by
          rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0:ℝ) < 2),
              show ((K : ℝ) + 1) = ((K + 1 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_natCast]
  unfold f
  rw [hidx]
  apply Finset.sum_le_sum
  intro k hk
  have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
  have hek : (1 : ℝ) / (k : ℝ) - 1 / 3 ≤ 0 := by
    have hkr : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    have : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hkr
    linarith
  rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < (2:ℝ) ^ (K + 1))]
  apply Real.exp_le_exp.mpr
  have hlogs : b ≤ Real.log ((2 : ℝ) ^ (K + 1)) := by
    calc b = Real.log (Real.exp b) := (Real.log_exp b).symm
      _ ≤ Real.log ((2 : ℝ) ^ (K + 1)) :=
          Real.log_le_log (Real.exp_pos b) hexp_le
  nlinarith [hlogs, hek]

/-- Mid-tier cert-free `a₂` bound: explicit head (k = 3..12) plus tail count times
    the k = 13 term. Valid for any `b > 0` with `⌊b / log 2⌋₊ = K ≥ 12`. -/
lemma a2_mid_le (b : ℝ) (hb : 0 < b) (K : ℕ) (hK : ⌊b / log 2⌋₊ = K) (h12 : 12 ≤ K) :
    Inputs.default.a₂ b ≤ (1 + Inputs.default.α) *
      ((∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp (b * (1 / (k : ℝ) - 1 / 3))) +
        ((K : ℝ) - 11) * Real.exp (b * (1 / 13 - 1 / 3))) := by
  have hα : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  -- the common dominating sum, with the k = 13.. tail collapsed
  set S : ℝ := (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp (b * (1 / (k : ℝ) - 1 / 3))) +
      ((K : ℝ) - 11) * Real.exp (b * (1 / 13 - 1 / 3)) with hS
  have hsplit : ∀ (M : ℕ), 12 ≤ M →
      (∑ k ∈ Finset.Icc 3 M, Real.exp (b * (1 / (k : ℝ) - 1 / 3))) ≤
      (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp (b * (1 / (k : ℝ) - 1 / 3))) +
        ((M : ℝ) - 12) * Real.exp (b * (1 / 13 - 1 / 3)) := by
    intro M hM
    have hunion : Finset.Icc 3 M = Finset.Icc (3:ℕ) 12 ∪ Finset.Icc 13 M := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    rw [hunion, Finset.sum_union (by
      apply Finset.disjoint_left.mpr
      intro a ha hb'
      have h1 := (Finset.mem_Icc.mp ha).2
      have h2 := (Finset.mem_Icc.mp hb').1
      omega)]
    refine add_le_add le_rfl ?_
    calc (∑ k ∈ Finset.Icc 13 M, Real.exp (b * (1 / (k : ℝ) - 1 / 3)))
        ≤ (Finset.Icc 13 M).card • Real.exp (b * (1 / 13 - 1 / 3)) := by
          apply Finset.sum_le_card_nsmul
          intro k hk
          have hk13 : 13 ≤ k := (Finset.mem_Icc.mp hk).1
          apply Real.exp_le_exp.mpr
          have hkr : (13 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk13
          have : (1 : ℝ) / (k : ℝ) ≤ 1 / 13 := one_div_le_one_div_of_le (by norm_num) hkr
          nlinarith [hb]
      _ ≤ ((M : ℝ) - 12) * Real.exp (b * (1 / 13 - 1 / 3)) := by
          rw [nsmul_eq_mul, Nat.card_Icc]
          have : ((M + 1 - 13 : ℕ) : ℝ) ≤ (M : ℝ) - 12 := by
            have h13 : 13 ≤ M + 1 := by omega
            rw [Nat.cast_sub h13]
            push_cast
            linarith
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hfe : f (Real.exp b) ≤ S := by
    rw [f_exp_eq b K hK, hS]
    calc (∑ k ∈ Finset.Icc 3 K, Real.exp (b * (1 / (k : ℝ) - 1 / 3)))
        ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp (b * (1 / (k : ℝ) - 1 / 3))) +
            ((K : ℝ) - 12) * Real.exp (b * (1 / 13 - 1 / 3)) := hsplit K h12
      _ ≤ _ := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
          linarith
  have hf2 : f ((2 : ℝ) ^ (K + 1)) ≤ S := by
    refine (f_two_pow_le b hb K hK).trans ?_
    rw [hS]
    calc (∑ k ∈ Finset.Icc 3 (K + 1), Real.exp (b * (1 / (k : ℝ) - 1 / 3)))
        ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp (b * (1 / (k : ℝ) - 1 / 3))) +
            (((K + 1 : ℕ) : ℝ) - 12) * Real.exp (b * (1 / 13 - 1 / 3)) := hsplit (K + 1) (by omega)
      _ ≤ _ := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
          push_cast; linarith
  have hmax : max (f (Real.exp b)) (f ((2 : ℝ) ^ (⌊b / log 2⌋₊ + 1))) ≤ S := by
    rw [hK]
    exact max_le hfe hf2
  unfold Inputs.a₂
  gcongr



/-! ## k-parametric machinery

    The `k = 1` column uses `row_bound_k1`; columns `k = 2..5` use `row_bound_kge2`
    reparametrized as `k = m + 2`. Each template is proven once, and every row of
    every column instantiates one of them. -/


noncomputable def eT (c y : ℝ) : ℝ := y * Real.exp (-(c * y))
noncomputable def eTd (c y : ℝ) : ℝ := (1 - c * y) * Real.exp (-(c * y))
noncomputable def eTdd (c y : ℝ) : ℝ := (c ^ 2 * y - 2 * c) * Real.exp (-(c * y))

lemma eT_hasDerivAt (c y : ℝ) : HasDerivAt (eT c) (eTd c y) y := by
  unfold eT eTd
  have hlin : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y := ((hasDerivAt_id y).const_mul c).neg
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(c * u))) (Real.exp (-(c * y)) * (-(c * 1))) y := hlin.exp
  convert! (hasDerivAt_id y).mul he using 1
  simp only [id_eq]; ring

lemma eTd_hasDerivAt (c y : ℝ) : HasDerivAt (eTd c) (eTdd c y) y := by
  unfold eTd eTdd
  have hP : HasDerivAt (fun u : ℝ => 1 - c * u) (-(c * 1)) y := by
    convert! (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).const_mul c) using 1
    ring
  have hlin : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y := ((hasDerivAt_id y).const_mul c).neg
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(c * u))) (Real.exp (-(c * y)) * (-(c * 1))) y := hlin.exp
  convert! hP.mul he using 1
  ring

noncomputable def G1 (A₁ A₂ E y : ℝ) : ℝ := A₁ * eT (1 / 2) y + A₂ * eT (2 / 3) y + E * y
noncomputable def G1' (A₁ A₂ E y : ℝ) : ℝ := A₁ * eTd (1 / 2) y + A₂ * eTd (2 / 3) y + E
noncomputable def G1'' (A₁ A₂ _E y : ℝ) : ℝ := A₁ * eTdd (1 / 2) y + A₂ * eTdd (2 / 3) y

lemma G1_hasDerivAt (A₁ A₂ E y : ℝ) : HasDerivAt (G1 A₁ A₂ E) (G1' A₁ A₂ E y) y := by
  unfold G1 G1'
  have h1 := (eT_hasDerivAt (1 / 2) y).const_mul A₁
  have h2 := (eT_hasDerivAt (2 / 3) y).const_mul A₂
  have h3 : HasDerivAt (fun u : ℝ => E * u) E y := by
    simpa using (hasDerivAt_id y).const_mul E
  convert! (h1.add h2).add h3 using 1

lemma G1'_hasDerivAt (A₁ A₂ E y : ℝ) : HasDerivAt (G1' A₁ A₂ E) (G1'' A₁ A₂ E y) y := by
  unfold G1' G1''
  have h1 := (eTd_hasDerivAt (1 / 2) y).const_mul A₁
  have h2 := (eTd_hasDerivAt (2 / 3) y).const_mul A₂
  have h3 : HasDerivAt (fun _ : ℝ => E) 0 y := hasDerivAt_const y E
  convert! (h1.add h2).add h3 using 1
  ring

lemma G1_continuous (A₁ A₂ E : ℝ) : Continuous (G1 A₁ A₂ E) := by unfold G1 eT; fun_prop

lemma G1''_nonneg {A₁ A₂ E : ℝ} (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) {y : ℝ} (hy20 : 20 ≤ y) :
    0 ≤ G1'' A₁ A₂ E y := by
  unfold G1'' eTdd
  have t1 : (0 : ℝ) ≤ A₁ * (((1 / 2 : ℝ) ^ 2 * y - 2 * (1 / 2)) * Real.exp (-((1 / 2 : ℝ) * y))) := by
    apply mul_nonneg hA1
    apply mul_nonneg _ (Real.exp_pos _).le
    nlinarith [hy20]
  have t2 : (0 : ℝ) ≤ A₂ * (((2 / 3 : ℝ) ^ 2 * y - 2 * (2 / 3)) * Real.exp (-((2 / 3 : ℝ) * y))) := by
    apply mul_nonneg hA2
    apply mul_nonneg _ (Real.exp_pos _).le
    nlinarith [hy20]
  linarith [t1, t2]

lemma G1_convexOn {A₁ A₂ E : ℝ} (b b' : ℝ) (_hbb' : b ≤ b') (hb20 : 20 ≤ b)
    (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) :
    ConvexOn ℝ (Set.Icc b b') (G1 A₁ A₂ E) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) (G1_continuous A₁ A₂ E).continuousOn
  · intro y _; exact (G1_hasDerivAt A₁ A₂ E y).hasDerivWithinAt
  · intro y _; exact (G1'_hasDerivAt A₁ A₂ E y).hasDerivWithinAt
  · intro y hy; rw [interior_Icc] at hy; exact G1''_nonneg hA1 hA2 (by linarith [hy.1])

/-- k = 1 row template (majorant `y·e^{-cy}`, no pow machinery): given coefficient upper
    bounds and the two endpoint majorant values under `T`, the exact Lemma-8 supremum for
    any row `[b,b']` (20 ≤ b) is `≤ T`. -/
theorem row_bound_k1 (b b' A₁ A₂ E T : ℝ)
    (hbb' : b ≤ b') (hb20 : 20 ≤ b)
    (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) (_hE : 0 ≤ E)
    (ha1 : Inputs.default.a₁ b ≤ A₁) (ha2 : Inputs.default.a₂ b ≤ A₂) (heps : Inputs.default.ε b ≤ E)
    (hGb : G1 A₁ A₂ E b ≤ T) (hGb' : G1 A₁ A₂ E b' ≤ T) :
    B_8_exact 1 b b' ≤ T := by
  unfold B_8_exact
  refine B_le_of_forall_log _ _ _ _ hbb' ?_
  intro y hy
  have hy0 : (0 : ℝ) ≤ y := by have := hy.1; linarith
  have hconv : G1 A₁ A₂ E y ≤ T :=
    le_trans ((G1_convexOn b b' hbb' hb20 hA1 hA2).le_max_of_mem_Icc
      (left_mem_Icc.mpr hbb') (right_mem_Icc.mpr hbb') hy) (max_le hGb hGb')
  rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_insert (by decide), Finset.sum_singleton]
  have hif1 : (if (1 : ℕ) = 1 then Inputs.default.a₁ b else if (1 : ℕ) = 2 then Inputs.default.a₂ b else 0)
      = Inputs.default.a₁ b := by norm_num
  have hif2 : (if (2 : ℕ) = 1 then Inputs.default.a₁ b else if (2 : ℕ) = 2 then Inputs.default.a₂ b else 0)
      = Inputs.default.a₂ b := by norm_num
  have ce1 : Real.exp (-(((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(1 / 2 * y)) := by
    congr 1; push_cast; ring
  have ce2 : Real.exp (-(((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(2 / 3 * y)) := by
    congr 1; push_cast; ring
  rw [hif1, hif2, ce1, ce2]
  simp only [pow_one]
  have e1 : (0 : ℝ) ≤ y * Real.exp (-(1 / 2 * y)) := mul_nonneg hy0 (Real.exp_pos _).le
  have e2 : (0 : ℝ) ≤ y * Real.exp (-(2 / 3 * y)) := mul_nonneg hy0 (Real.exp_pos _).le
  have h1 : Inputs.default.a₁ b * y * Real.exp (-(1 / 2 * y)) ≤ A₁ * (y * Real.exp (-(1 / 2 * y))) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ha1 e1
  have h2 : Inputs.default.a₂ b * y * Real.exp (-(2 / 3 * y)) ≤ A₂ * (y * Real.exp (-(2 / 3 * y))) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ha2 e2
  have h3 : Inputs.default.ε b * y ≤ E * y := mul_le_mul_of_nonneg_right heps hy0
  have hG1y : G1 A₁ A₂ E y
      = A₁ * (y * Real.exp (-(1 / 2 * y))) + A₂ * (y * Real.exp (-(2 / 3 * y))) + E * y := by
    unfold G1 eT; ring
  rw [hG1y] at hconv
  linarith [h1, h2, h3, hconv]

/-! ### One-term majorant `y^(m+2)·e^{-cy}` and its two derivatives (general `m`). -/

noncomputable def pT (m : ℕ) (c y : ℝ) : ℝ := y ^ (m + 2) * Real.exp (-(c * y))
noncomputable def pTd (m : ℕ) (c y : ℝ) : ℝ :=
  (((m + 2 : ℕ) : ℝ) * y ^ (m + 1) - c * y ^ (m + 2)) * Real.exp (-(c * y))
noncomputable def pTdd (m : ℕ) (c y : ℝ) : ℝ :=
  (c ^ 2 * y ^ (m + 2) - 2 * c * ((m + 2 : ℕ) : ℝ) * y ^ (m + 1)
      + ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * y ^ m) * Real.exp (-(c * y))

lemma pT_hasDerivAt (m : ℕ) (c y : ℝ) : HasDerivAt (pT m c) (pTd m c y) y := by
  unfold pT pTd
  have hp : HasDerivAt (fun u : ℝ => u ^ (m + 2)) (((m + 2 : ℕ) : ℝ) * y ^ (m + 1)) y :=
    hasDerivAt_pow (m + 2) y
  have hlin : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y := ((hasDerivAt_id y).const_mul c).neg
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(c * u))) (Real.exp (-(c * y)) * (-(c * 1))) y := hlin.exp
  convert! hp.mul he using 1
  ring

lemma pTd_hasDerivAt (m : ℕ) (c y : ℝ) : HasDerivAt (pTd m c) (pTdd m c y) y := by
  unfold pTd pTdd
  have hP : HasDerivAt (fun u : ℝ => ((m + 2 : ℕ) : ℝ) * u ^ (m + 1) - c * u ^ (m + 2))
      (((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * y ^ m) - c * (((m + 2 : ℕ) : ℝ) * y ^ (m + 1))) y := by
    have ha : HasDerivAt (fun u : ℝ => u ^ (m + 1)) (((m + 1 : ℕ) : ℝ) * y ^ m) y :=
      hasDerivAt_pow (m + 1) y
    have hb : HasDerivAt (fun u : ℝ => u ^ (m + 2)) (((m + 2 : ℕ) : ℝ) * y ^ (m + 1)) y :=
      hasDerivAt_pow (m + 2) y
    exact (ha.const_mul _).sub (hb.const_mul _)
  have hlin : HasDerivAt (fun u : ℝ => -(c * u)) (-(c * 1)) y := ((hasDerivAt_id y).const_mul c).neg
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(c * u))) (Real.exp (-(c * y)) * (-(c * 1))) y := hlin.exp
  convert! hP.mul he using 1
  ring

/-! ### Convexity: the second derivative is nonneg on `[20, ∞)` for `m ≤ 3`. -/

lemma quad_nonneg {c y : ℝ} (hc : 1 / 2 ≤ c) (hy20 : 20 ≤ y) {M : ℝ} (_hM0 : 0 ≤ M) (hM3 : M ≤ 3) :
    0 ≤ c ^ 2 * y ^ 2 - 2 * c * (M + 2) * y + (M + 2) * (M + 1) := by
  have hcy : (10 : ℝ) ≤ c * y := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0 : ℝ) ≤ y by linarith), hy20]
  nlinarith [hcy, _hM0, hM3, sq_nonneg (c * y - M - 7)]

lemma pTdd_nonneg {c : ℝ} (hc : 1 / 2 ≤ c) {m : ℕ} (hm : m ≤ 3) {y : ℝ} (hy20 : 20 ≤ y) :
    0 ≤ pTdd m c y := by
  unfold pTdd
  apply mul_nonneg _ (Real.exp_pos _).le
  have hM0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hM3 : (m : ℝ) ≤ 3 := by exact_mod_cast hm
  have hym : (0 : ℝ) ≤ y ^ m := pow_nonneg (by linarith) m
  push_cast
  have hfac : c ^ 2 * y ^ (m + 2) - 2 * c * ((m : ℝ) + 2) * y ^ (m + 1)
        + ((m : ℝ) + 2) * ((m : ℝ) + 1) * y ^ m
      = y ^ m * (c ^ 2 * y ^ 2 - 2 * c * ((m : ℝ) + 2) * y + ((m : ℝ) + 2) * ((m : ℝ) + 1)) := by
    ring
  rw [hfac]
  exact mul_nonneg hym (quad_nonneg hc hy20 hM0 hM3)

/-! ### Parameterized majorant `Pp m A₁ A₂ E` and its convexity on any [b,b'] with 20 ≤ b. -/

noncomputable def Pp (m : ℕ) (A₁ A₂ E y : ℝ) : ℝ :=
  A₁ * pT m (1 / 2) y + A₂ * pT m (2 / 3) y + E * y ^ (m + 2)
noncomputable def Pp' (m : ℕ) (A₁ A₂ E y : ℝ) : ℝ :=
  A₁ * pTd m (1 / 2) y + A₂ * pTd m (2 / 3) y + E * (((m + 2 : ℕ) : ℝ) * y ^ (m + 1))
noncomputable def Pp'' (m : ℕ) (A₁ A₂ E y : ℝ) : ℝ :=
  A₁ * pTdd m (1 / 2) y + A₂ * pTdd m (2 / 3) y
    + E * (((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * y ^ m))

lemma Pp_hasDerivAt (m : ℕ) (A₁ A₂ E y : ℝ) : HasDerivAt (Pp m A₁ A₂ E) (Pp' m A₁ A₂ E y) y := by
  unfold Pp Pp'
  have h1 := (pT_hasDerivAt m (1 / 2) y).const_mul A₁
  have h2 := (pT_hasDerivAt m (2 / 3) y).const_mul A₂
  have h3 : HasDerivAt (fun u : ℝ => E * u ^ (m + 2)) (E * (((m + 2 : ℕ) : ℝ) * y ^ (m + 1))) y :=
    (hasDerivAt_pow (m + 2) y).const_mul E
  exact (h1.add h2).add h3

lemma Pp'_hasDerivAt (m : ℕ) (A₁ A₂ E y : ℝ) : HasDerivAt (Pp' m A₁ A₂ E) (Pp'' m A₁ A₂ E y) y := by
  unfold Pp' Pp''
  have h1 := (pTd_hasDerivAt m (1 / 2) y).const_mul A₁
  have h2 := (pTd_hasDerivAt m (2 / 3) y).const_mul A₂
  have h3 : HasDerivAt (fun u : ℝ => E * (((m + 2 : ℕ) : ℝ) * u ^ (m + 1)))
      (E * (((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * y ^ m))) y := by
    have hb : HasDerivAt (fun u : ℝ => u ^ (m + 1)) (((m + 1 : ℕ) : ℝ) * y ^ m) y :=
      hasDerivAt_pow (m + 1) y
    exact (hb.const_mul (((m + 2 : ℕ) : ℝ))).const_mul E
  exact (h1.add h2).add h3

lemma Pp_continuous (m : ℕ) (A₁ A₂ E : ℝ) : Continuous (Pp m A₁ A₂ E) := by
  unfold Pp pT; fun_prop

lemma Pp''_nonneg {A₁ A₂ E : ℝ} (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) (hE : 0 ≤ E)
    {m : ℕ} (hm : m ≤ 3) {y : ℝ} (hy20 : 20 ≤ y) : 0 ≤ Pp'' m A₁ A₂ E y := by
  unfold Pp''
  have t1 : (0 : ℝ) ≤ A₁ * pTdd m (1 / 2) y := mul_nonneg hA1 (pTdd_nonneg (by norm_num) hm hy20)
  have t2 : (0 : ℝ) ≤ A₂ * pTdd m (2 / 3) y := mul_nonneg hA2 (pTdd_nonneg (by norm_num) hm hy20)
  have t3 : (0 : ℝ) ≤ E * (((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * y ^ m)) := by
    apply mul_nonneg hE
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (pow_nonneg (by linarith) m))
  linarith [t1, t2, t3]

lemma Pp_convexOn {A₁ A₂ E : ℝ} (m : ℕ) (b b' : ℝ) (_hbb' : b ≤ b') (hb20 : 20 ≤ b) (hm : m ≤ 3)
    (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) (hE : 0 ≤ E) :
    ConvexOn ℝ (Set.Icc b b') (Pp m A₁ A₂ E) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) (Pp_continuous m A₁ A₂ E).continuousOn
  · intro y _; exact (Pp_hasDerivAt m A₁ A₂ E y).hasDerivWithinAt
  · intro y _; exact (Pp'_hasDerivAt m A₁ A₂ E y).hasDerivWithinAt
  · intro y hy; rw [interior_Icc] at hy; exact Pp''_nonneg hA1 hA2 hE hm (by linarith [hy.1])


/-- General-k (k = m+2, m ≤ 3) row template: given coefficient upper bounds and the two endpoint
    majorant values under `T`, the exact Lemma-8 supremum for any row `[b,b']` (20 ≤ b) is `≤ T`.
    Proven ONCE; rows 20-... for every column k ∈ {2,3,4,5} instantiate it. -/
theorem row_bound_kge2 (m : ℕ) (hm : m ≤ 3) (b b' A₁ A₂ E T : ℝ)
    (hbb' : b ≤ b') (hb20 : 20 ≤ b)
    (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) (hE : 0 ≤ E)
    (ha1 : Inputs.default.a₁ b ≤ A₁) (ha2 : Inputs.default.a₂ b ≤ A₂) (heps : Inputs.default.ε b ≤ E)
    (hPb : Pp m A₁ A₂ E b ≤ T) (hPb' : Pp m A₁ A₂ E b' ≤ T) :
    B_8_exact (m + 2) b b' ≤ T := by
  unfold B_8_exact
  refine B_le_of_forall_log _ _ _ _ hbb' ?_
  intro y hy
  have hy0 : (0 : ℝ) ≤ y := by have := hy.1; linarith
  have hyk : (0 : ℝ) ≤ y ^ (m + 2) := pow_nonneg hy0 (m + 2)
  have hconv : Pp m A₁ A₂ E y ≤ T :=
    le_trans ((Pp_convexOn m b b' hbb' hb20 hm hA1 hA2 hE).le_max_of_mem_Icc
      (left_mem_Icc.mpr hbb') (right_mem_Icc.mpr hbb') hy) (max_le hPb hPb')
  rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_insert (by decide), Finset.sum_singleton]
  have hif1 : (if (1 : ℕ) = 1 then Inputs.default.a₁ b else if (1 : ℕ) = 2 then Inputs.default.a₂ b else 0)
      = Inputs.default.a₁ b := by norm_num
  have hif2 : (if (2 : ℕ) = 1 then Inputs.default.a₁ b else if (2 : ℕ) = 2 then Inputs.default.a₂ b else 0)
      = Inputs.default.a₂ b := by norm_num
  have ce1 : Real.exp (-(((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(1 / 2 * y)) := by
    congr 1; push_cast; ring
  have ce2 : Real.exp (-(((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(2 / 3 * y)) := by
    congr 1; push_cast; ring
  rw [hif1, hif2, ce1, ce2]
  have e1 : (0 : ℝ) ≤ y ^ (m + 2) * Real.exp (-(1 / 2 * y)) := mul_nonneg hyk (Real.exp_pos _).le
  have e2 : (0 : ℝ) ≤ y ^ (m + 2) * Real.exp (-(2 / 3 * y)) := mul_nonneg hyk (Real.exp_pos _).le
  have h1 : Inputs.default.a₁ b * y ^ (m + 2) * Real.exp (-(1 / 2 * y))
      ≤ A₁ * (y ^ (m + 2) * Real.exp (-(1 / 2 * y))) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ha1 e1
  have h2 : Inputs.default.a₂ b * y ^ (m + 2) * Real.exp (-(2 / 3 * y))
      ≤ A₂ * (y ^ (m + 2) * Real.exp (-(2 / 3 * y))) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ha2 e2
  have h3 : Inputs.default.ε b * y ^ (m + 2) ≤ E * y ^ (m + 2) := mul_le_mul_of_nonneg_right heps hyk
  have hPy : Pp m A₁ A₂ E y
      = A₁ * (y ^ (m + 2) * Real.exp (-(1 / 2 * y))) + A₂ * (y ^ (m + 2) * Real.exp (-(2 / 3 * y)))
          + E * y ^ (m + 2) := by
    unfold Pp pT; ring
  rw [hPy] at hconv
  linarith [h1, h2, h3, hconv]


/-- General a₁ bound on the constant branch: valid for every `b ≤ 86`. -/
lemma a1_le_small {b : ℝ} (hb : b ≤ 86) : Inputs.default.a₁ b ≤ (1.00000002 : ℝ) := by
  have hlog : (43 : ℝ) < log Inputs.default.x₁ ∧ log Inputs.default.x₁ < 44 := by
    change (43 : ℝ) < log (1e19 : ℝ) ∧ log (1e19 : ℝ) < 44
    have h1e19 : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
    rw [h1e19, Real.log_pow]; push_cast
    constructor <;> nlinarith [LogTables.log_10_gt, LogTables.log_10_lt]
  have hε19 : Inputs.default.ε (log Inputs.default.x₁) ≤ 1.93378e-8 * BKLNW_app.table_8_margin := by
    change BKLNW_app.table_8_ε (log Inputs.default.x₁) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    grw [BKLNW_app.table_8_ε.le_simp (log Inputs.default.x₁) (by linarith [hlog.1])]
    grind [BKLNW_app.table_8_ε']
  unfold Inputs.a₁
  rw [if_pos (by linarith [hlog.1] : b ≤ 2 * log Inputs.default.x₁)]
  have hb' : (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1.00000002 - 1 := by
    norm_num [BKLNW_app.table_8_margin]
  linarith [hε19, hb']


/-! ## Regime-3 pointwise template (b ≳ 80): no convexity, no derivative machinery,
    uniform in every column k. Per-term endpoint bounds reduce the supremum to ONE
    constant inequality, dischargeable by `interval_decide` per row. Ported from the
    compiled `row100_pointwise.lean` exemplar, parameterized over k + coefficients. -/

theorem row_bound_pointwise (k : ℕ) (b b' A₁ A₂ E T : ℝ)
    (hbb' : b ≤ b') (hb0 : 0 ≤ b)
    (hA1 : 0 ≤ A₁) (hA2 : 0 ≤ A₂) (hE : 0 ≤ E)
    (ha1 : Inputs.default.a₁ b ≤ A₁) (ha2 : Inputs.default.a₂ b ≤ A₂)
    (heps : Inputs.default.ε b ≤ E)
    (hT : A₁ * b' ^ k * Real.exp (-(1 / 2 * b)) + A₂ * b' ^ k * Real.exp (-(2 / 3 * b))
            + E * b' ^ k ≤ T) :
    B_8_exact k b b' ≤ T := by
  have hb'0 : (0 : ℝ) ≤ b' := le_trans hb0 hbb'
  unfold B_8_exact
  refine B_le_of_forall_log _ _ _ _ hbb' ?_
  intro y hy
  obtain ⟨hyb, hyb'⟩ := hy
  have hy0 : (0 : ℝ) ≤ y := le_trans hb0 hyb
  have hyk : (0 : ℝ) ≤ y ^ k := pow_nonneg hy0 k
  rw [show Finset.Icc 1 2 = {1, 2} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have hif1 : (if (1 : ℕ) = 1 then Inputs.default.a₁ b else if (1 : ℕ) = 2 then Inputs.default.a₂ b else 0)
      = Inputs.default.a₁ b := by norm_num
  have hif2 : (if (2 : ℕ) = 1 then Inputs.default.a₁ b else if (2 : ℕ) = 2 then Inputs.default.a₂ b else 0)
      = Inputs.default.a₂ b := by norm_num
  have ce1 : Real.exp (-(((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(1 / 2 * y)) := by
    congr 1; push_cast; ring
  have ce2 : Real.exp (-(((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 1) * y)) = Real.exp (-(2 / 3 * y)) := by
    congr 1; push_cast; ring
  rw [hif1, hif2, ce1, ce2]
  have hpow : y ^ k ≤ b' ^ k := by gcongr
  have ht1 : Inputs.default.a₁ b * y ^ k * Real.exp (-(1 / 2 * y))
      ≤ A₁ * b' ^ k * Real.exp (-(1 / 2 * b)) :=
    mul_le_mul (mul_le_mul ha1 hpow hyk hA1)
      (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (mul_nonneg hA1 (pow_nonneg hb'0 k))
  have ht2 : Inputs.default.a₂ b * y ^ k * Real.exp (-(2 / 3 * y))
      ≤ A₂ * b' ^ k * Real.exp (-(2 / 3 * b)) :=
    mul_le_mul (mul_le_mul ha2 hpow hyk hA2)
      (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (mul_nonneg hA2 (pow_nonneg hb'0 k))
  have ht3 : Inputs.default.ε b * y ^ k ≤ E * b' ^ k :=
    mul_le_mul heps hpow hyk hE
  linarith [ht1, ht2, ht3, hT]

end BKLNW
