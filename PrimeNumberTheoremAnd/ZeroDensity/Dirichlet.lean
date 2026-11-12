/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZeroDensity.MeanValue

/-!
# Mean value theorem for Dirichlet polynomials: `(T + O(N log N)) ∑ |a n|^2`

For `S ⊆ [1, N]` and `F(t) = ∑_{n ∈ S} a n n^{-it}`:
  `|∫_0^T |F t|^2 dt - T ∑ |a n|^2| ≤ 4 N (1 + log N) ∑ |a n|^2`.
-/

@[expose] public section

open Complex Finset

namespace ZeroDensity

/-- `dpoly` with frequencies `log n` is the Dirichlet polynomial `∑ a n n^{-it}`. -/
lemma dpoly_log_eq (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℂ) (t : ℝ) :
    dpoly S a (fun n => Real.log n) t = ∑ n ∈ S, a n * (n : ℂ) ^ (-((t : ℂ) * I)) := by
  unfold dpoly
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by have := hS n hn; exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  congr 2; ring

/-- Real harmonic sum. -/
noncomputable def harm (N : ℕ) : ℝ := ∑ k ∈ Icc 1 N, (k : ℝ)⁻¹

lemma harm_le (N : ℕ) : harm N ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [harm] using h

lemma harm_nonneg (N : ℕ) : 0 ≤ harm N :=
  Finset.sum_nonneg fun k _ => by positivity

lemma log_gap {m n N : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmN : m ≤ N) (hnN : n ≤ N) :
    |(n : ℝ) - m| / N ≤ |Real.log n - Real.log m| := by
  have key : ∀ {p q : ℕ}, 1 ≤ p → 1 ≤ q → p ≤ N → q ≤ N → p < q →
      |(q : ℝ) - p| / N ≤ |Real.log q - Real.log p| := by
    intro p q hp hq _ hqN hpq
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
    have hN : (q : ℝ) ≤ N := by exact_mod_cast hqN
    have hlog : Real.log q - Real.log p = Real.log (q / p) := by
      rw [Real.log_div hq0.ne' hp0.ne']
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hq0 hp0)
    rw [inv_div] at h1
    have h2 : 0 ≤ Real.log q - Real.log p := by
      rw [hlog]; exact Real.log_nonneg (by rw [le_div_iff₀ hp0]; linarith)
    rw [abs_of_pos (by linarith), abs_of_nonneg h2, hlog]
    refine le_trans ?_ h1
    have e : 1 - (p:ℝ) / q = (q - p) / q := by field_simp
    rw [e]; exact div_le_div_of_nonneg_left (by linarith) hq0 hN
  rcases lt_trichotomy m n with h | h | h
  · exact key hm hn hmN hnN h
  · subst h; simp
  · rw [abs_sub_comm, abs_sub_comm (Real.log n)]; exact key hn hm hnN hmN h

lemma sum_inv_dist_le (N n : ℕ) (hn : n ≤ N) :
    ∑ m ∈ (Icc 1 N).erase n, (|(n : ℝ) - m|)⁻¹ ≤ 2 * harm N := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun m => m < n), two_mul]
  apply add_le_add
  · refine Finset.sum_le_sum_of_injOn (fun m => n - m) ?_ ?_ ?_ ?_
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_erase, Finset.mem_Icc, Set.mem_ofPred_eq] at hx hy
      simp only at hxy; omega
    · intro k hk
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc] at hk ⊢
      obtain ⟨x, hx, rfl⟩ := hk
      omega
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc] at hm
      have hlt : (m:ℝ) < n := by exact_mod_cast hm.2
      rw [Nat.cast_sub hm.2.le, abs_of_pos (by linarith)]
    · intro k _ _; positivity
  · refine Finset.sum_le_sum_of_injOn (fun m => m - n) ?_ ?_ ?_ ?_
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_erase, Finset.mem_Icc, Set.mem_ofPred_eq] at hx hy
      simp only at hxy; omega
    · intro k hk
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc] at hk ⊢
      obtain ⟨x, hx, rfl⟩ := hk
      omega
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc] at hm
      have hlt : n < m := by omega
      have hlt' : (n:ℝ) < m := by exact_mod_cast hlt
      rw [Nat.cast_sub hlt.le, abs_sub_comm, abs_of_pos (by linarith)]
    · intro k _ _; positivity

/-- **Mean value theorem for Dirichlet polynomials** (explicit `(T + O(N log N))` form). -/
@[blueprint
  "zd-mvt-dirichlet"
  (title := "Mean value theorem for Dirichlet polynomials")
  (statement := /--
    For $S\subseteq[1,N]$ and $a_n\in\mathbb{C}$,
    $$\Bigl|\int_0^T\Bigl|\sum_{n\in S}a_n n^{-it}\Bigr|^2dt-T\sum_{n\in S}|a_n|^2\Bigr|
      \le 4N H_N\sum_{n\in S}|a_n|^2,$$
    where $H_N=\sum_{k\le N}1/k\le 1+\log N$; in particular the integral is
    $(T+O(N\log N))\sum|a_n|^2$.
  -/)]
theorem mean_value_dirichlet (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N) (a : ℕ → ℂ) (T : ℝ) :
    |(∫ t in (0:ℝ)..T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2) -
        T * ∑ n ∈ S, ‖a n‖ ^ 2| ≤
      4 * N * harm N * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hS1 : ∀ n ∈ S, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp (hS hn)).1
  have hSN : ∀ n ∈ S, n ≤ N := fun n hn => (Finset.mem_Icc.mp (hS hn)).2
  simp_rw [← dpoly_log_eq S hS1 a]
  have hinj : Set.InjOn (fun n : ℕ => Real.log n) S := by
    intro x hx y hy hxy
    have hx0 : (0:ℝ) < x := by have := hS1 x hx; exact_mod_cast (by omega : 0 < x)
    have hy0 : (0:ℝ) < y := by have := hS1 y hy; exact_mod_cast (by omega : 0 < y)
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr hy0) hxy
  refine (mean_value_explicit S a _ hinj T).trans ?_
  set w : ℕ → ℕ → ℝ := fun m n => (N : ℝ) * (|(n : ℝ) - m|)⁻¹ with hw
  -- step 1: pointwise bound
  have step1 : ∀ m ∈ S, ∀ n ∈ S.erase m,
      2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| ≤ (‖a m‖ ^ 2 + ‖a n‖ ^ 2) * w m n := by
    intro m hm n hn
    have hnS := Finset.mem_of_mem_erase hn
    have hne : n ≠ m := Finset.ne_of_mem_erase hn
    have hd : (0:ℝ) < |(n:ℝ) - m| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
    have hNpos : (0:ℝ) < N := by have := hS1 n hnS; have := hSN n hnS; exact_mod_cast (by omega : 0 < N)
    have hg := log_gap (hS1 m hm) (hS1 n hnS) (hSN m hm) (hSN n hnS)
    have hgpos : 0 < |(n:ℝ) - m| / N := div_pos hd hNpos
    have hamn : 2 * ‖a m‖ * ‖a n‖ ≤ ‖a m‖ ^ 2 + ‖a n‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a m‖ - ‖a n‖)]
    calc 2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m|
        ≤ 2 * ‖a m‖ * ‖a n‖ / (|(n:ℝ) - m| / N) :=
          div_le_div_of_nonneg_left (by positivity) hgpos hg
      _ ≤ (‖a m‖ ^ 2 + ‖a n‖ ^ 2) / (|(n:ℝ) - m| / N) :=
          div_le_div_of_nonneg_right hamn hgpos.le
      _ = (‖a m‖ ^ 2 + ‖a n‖ ^ 2) * w m n := by
          simp only [hw]; field_simp
  have hwsym : ∀ m n, w m n = w n m := by
    intro m n; simp only [hw]; rw [abs_sub_comm]
  have hrow : ∀ m ∈ S, ∑ n ∈ S.erase m, w m n ≤ N * (2 * harm N) := by
    intro m hm
    have hsub : S.erase m ⊆ (Icc 1 N).erase m := Finset.erase_subset_erase _ hS
    calc ∑ n ∈ S.erase m, w m n ≤ ∑ n ∈ (Icc 1 N).erase m, w m n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by simp only [hw]; positivity)
      _ = N * ∑ n ∈ (Icc 1 N).erase m, (|(m:ℝ) - n|)⁻¹ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_
          simp only [hw]; rw [abs_sub_comm]
      _ ≤ N * (2 * harm N) := by gcongr; exact sum_inv_dist_le N m (hSN m hm)
  calc ∑ m ∈ S, ∑ n ∈ S.erase m, 2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m|
      ≤ ∑ m ∈ S, ∑ n ∈ S.erase m, (‖a m‖ ^ 2 + ‖a n‖ ^ 2) * w m n :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => step1 m hm n hn
    _ = ∑ m ∈ S, ∑ n ∈ S.erase m, ‖a m‖ ^ 2 * w m n +
          ∑ m ∈ S, ∑ n ∈ S.erase m, ‖a n‖ ^ 2 * w m n := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ = 2 * ∑ m ∈ S, ‖a m‖ ^ 2 * ∑ n ∈ S.erase m, w m n := by
        have hswap : ∑ m ∈ S, ∑ n ∈ S.erase m, ‖a n‖ ^ 2 * w m n =
            ∑ m ∈ S, ∑ n ∈ S.erase m, ‖a m‖ ^ 2 * w m n := by
          rw [Finset.sum_comm' (t' := S) (s' := fun n => S.erase n)]
          · refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
            rw [hwsym]
          · intro m n
            simp only [Finset.mem_erase]
            aesop
        rw [hswap, two_mul]
        congr 1 <;> refine Finset.sum_congr rfl fun m _ => ?_ <;> rw [Finset.mul_sum]
    _ ≤ 2 * ∑ m ∈ S, ‖a m‖ ^ 2 * (N * (2 * harm N)) := by
        gcongr with m hm; exact hrow m hm
    _ = 4 * N * harm N * ∑ n ∈ S, ‖a n‖ ^ 2 := by
        rw [← Finset.sum_mul]; ring

end ZeroDensity

namespace ZeroDensity
open Complex Finset

/-- Corollary: `∫_0^T |∑ a n n^{-it}|^2 = T ∑|a n|^2 + E`, `|E| ≤ 4 N (1 + log N) ∑ |a n|^2`. -/
theorem mean_value_dirichlet_log (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N) (a : ℕ → ℂ) (T : ℝ) :
    |(∫ t in (0:ℝ)..T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2) -
        T * ∑ n ∈ S, ‖a n‖ ^ 2| ≤
      4 * N * (1 + Real.log N) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  refine (mean_value_dirichlet N S hS a T).trans ?_
  have h0 : 0 ≤ ∑ n ∈ S, ‖a n‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  gcongr
  exact harm_le N

end ZeroDensity
