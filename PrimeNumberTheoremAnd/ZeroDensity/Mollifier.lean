/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZeroDensity.ApproxZeta

/-!
# Mollifier arithmetic for the Carlson-type density bound
`M_X(s) = Σ_{d≤X} μ(d) d^{-s}`, `D_N(s) = Σ_{n≤N} n^{-s}`, and the coefficients of `D_N M_X`.
Author: Devon Wright (formalized with Grok Bot).
-/

open Complex Finset ArithmeticFunction

@[expose] public noncomputable section
namespace ZeroDensity

def Mx (X : ℕ) (s : ℂ) : ℂ := ∑ d ∈ Icc 1 X, ((moebius d : ℤ) : ℂ) * (d : ℂ) ^ (-s)
def Dn (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s)
def cf (N X n : ℕ) : ℂ :=
  ∑ d ∈ Icc 1 X, ∑ m ∈ Icc 1 N, if m * d = n then ((moebius d : ℤ) : ℂ) else 0
/-- number of divisors of `n` that are `≤ X` -/
def dX (X n : ℕ) : ℕ := ((Icc 1 X).filter (· ∣ n)).card

lemma Dn_mul_Mx (N X : ℕ) (s : ℂ) :
    Dn N s * Mx X s = ∑ n ∈ Icc 1 (N * X), cf N X n * (n : ℂ) ^ (-s) := by
  simp only [cf, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  have : ∀ d ∈ Icc 1 X, (∑ n ∈ Icc 1 (N * X), ∑ m ∈ Icc 1 N,
      if m * d = n then ((moebius d : ℤ) : ℂ) * (n : ℂ) ^ (-s) else 0) =
      ∑ m ∈ Icc 1 N, (m : ℂ) ^ (-s) * (((moebius d : ℤ) : ℂ) * (d : ℂ) ^ (-s)) := by
    intro d hd
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_ite_eq]
    have hmem : m * d ∈ Icc 1 (N * X) := by
      simp only [Finset.mem_Icc] at hd hm ⊢
      exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.mul_le_mul hm.2 hd.2⟩
    rw [ite_eq_left hmem]
    push_cast
    rw [natCast_mul_natCast_cpow]; ring
  rw [Finset.sum_congr rfl this, Dn, Mx, Finset.sum_mul_sum, Finset.sum_comm]

lemma sum_moebius_divisors (n : ℕ) (_hn : 0 < n) :
    ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  rw [← Int.cast_sum, h]; split_ifs <;> simp

lemma cf_inner {N d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hnN : n ≤ N) :
    (∑ m ∈ Icc 1 N, if m * d = n then ((moebius d : ℤ) : ℂ) else 0) =
      if d ∣ n then ((moebius d : ℤ) : ℂ) else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Finset.sum_eq_single k]
    · rw [ite_eq_left (mul_comm k d)]
    · intro b _ hb; rw [ite_eq_right]; intro e
      exact hb (Nat.eq_of_mul_eq_mul_right (show 0 < d by omega) (by rw [e]; ring))
    · intro hk; exfalso; apply hk
      simp only [Finset.mem_Icc]
      constructor
      · rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at hn
        · exact h0
      · exact le_trans (Nat.le_mul_of_pos_left k (by omega)) hnN
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [ite_eq_right]; intro e; exact h ⟨m, by rw [← e]; ring⟩

lemma cf_one {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) : cf N X 1 = 1 := by
  unfold cf
  rw [Finset.sum_congr rfl fun d hd => cf_inner (Finset.mem_Icc.1 hd).1 le_rfl hN]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b hb hb1; rw [ite_eq_right]; intro h; exact hb1 (Nat.dvd_one.1 h)
  · intro h; exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hX⟩) h

lemma cf_small {N X n : ℕ} (hn : 2 ≤ n) (hnX : n ≤ X) (hXN : X ≤ N) : cf N X n = 0 := by
  unfold cf
  rw [Finset.sum_congr rfl fun d hd => cf_inner (Finset.mem_Icc.1 hd).1 (by omega) (by omega)]
  rw [← Finset.sum_filter]
  have : (Icc 1 X).filter (· ∣ n) = n.divisors := by
    ext d; simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hnX⟩, h⟩
  rw [this, sum_moebius_divisors n (by omega), ite_eq_right (by omega)]

lemma norm_cf_le (N X n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) : ‖cf N X n‖ ≤ dX X n := by
  unfold cf dX
  rw [Finset.sum_congr rfl fun d hd => cf_inner (Finset.mem_Icc.1 hd).1 hn hnN,
    ← Finset.sum_filter]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  have := abs_moebius_le_one (n := d)
  rw [Complex.norm_intCast]; push_cast; exact_mod_cast this


lemma norm_cf_inner_le (N d n : ℕ) (hd : 1 ≤ d) :
    ‖∑ m ∈ Icc 1 N, if m * d = n then ((moebius d : ℤ) : ℂ) else 0‖ ≤
      if d ∣ n then (1 : ℝ) else 0 := by
  have hμ : ‖((moebius d : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    have : ∀ m, (m * d = d * k ↔ m = k) := fun m => by
      constructor
      · intro e; exact Nat.eq_of_mul_eq_mul_right (show 0 < d by omega) (by rw [e]; ring)
      · rintro rfl; ring
    simp_rw [this, Finset.sum_ite_eq']
    split_ifs
    · exact hμ
    · simp
  · rw [Finset.sum_eq_zero, norm_zero]
    intro m _; rw [ite_eq_right]; intro e; exact h ⟨m, by rw [← e]; ring⟩

lemma norm_cf_le' (N X n : ℕ) : ‖cf N X n‖ ≤ dX X n := by
  unfold cf dX
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  refine (norm_cf_inner_le N d n (Finset.mem_Icc.1 hd).1).trans ?_
  split_ifs <;> simp

lemma dX_le (X n : ℕ) : (dX X n : ℝ) ≤ X := by
  unfold dX
  have := Finset.card_filter_le (Icc 1 X) (· ∣ n)
  simp only [Nat.card_Icc, add_tsub_cancel_right] at this; exact_mod_cast this

/-- `D_N M_X - 1` only involves `n > X`. -/
lemma Dn_mul_Mx_sub_one {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) (s : ℂ) :
    Dn N s * Mx X s - 1 = ∑ n ∈ Ioc X (N * X), cf N X n * (n : ℂ) ^ (-s) := by
  rw [Dn_mul_Mx]
  have hsplit : Icc 1 (N * X) = Icc 1 X ∪ Ioc X (N * X) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · intro h; by_cases h' : n ≤ X
      · left; exact ⟨h.1, h'⟩
      · right; exact ⟨by omega, h.2⟩
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans (Nat.le_mul_of_pos_left X (by omega))⟩
      · exact ⟨by omega, h.2⟩
  have hdisj : Disjoint (Icc 1 X) (Ioc X (N * X)) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have : ∑ n ∈ Icc 1 X, cf N X n * (n : ℂ) ^ (-s) = 1 := by
    rw [Finset.sum_eq_single 1]
    · rw [cf_one (by omega) hX]; simp
    · intro n hn hn1
      have := Finset.mem_Icc.1 hn
      rw [cf_small (by omega) this.2 hXN, zero_mul]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hX⟩) h
  rw [this]; ring

/-! ### Mean square of the divisor-count weights -/

/-- `S α = Σ_{k ≥ 1} k^{-α}` (with the `k = 0` term equal to `0` for `α > 0`). -/
def Sz (α : ℝ) : ℝ := ∑' k : ℕ, ((k : ℝ) ^ α)⁻¹

lemma sum_mult_le {α : ℝ} (hα : 1 < α) {l : ℕ} (hl : 1 ≤ l) (L : ℕ) :
    ∑ n ∈ Icc 1 L, (if l ∣ n then ((n : ℝ) ^ α)⁻¹ else 0) ≤ ((l : ℝ) ^ α)⁻¹ * Sz α := by
  rw [← Finset.sum_filter]
  have hsub : (Icc 1 L).filter (l ∣ ·) ⊆ (Icc 1 L).image (l * ·) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hn ⊢
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at h1
      · exact h
    · exact le_trans (Nat.le_mul_of_pos_left k (by omega)) h2
  have hpos : ∀ n : ℕ, 0 ≤ ((n : ℝ) ^ α)⁻¹ := fun n => by positivity
  calc _ ≤ ∑ n ∈ (Icc 1 L).image (l * ·), ((n : ℝ) ^ α)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hpos n
    _ = ∑ k ∈ Icc 1 L, ((l : ℝ) ^ α)⁻¹ * ((k : ℝ) ^ α)⁻¹ := by
        rw [Finset.sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity), mul_inv]
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hpos l)
        exact Summable.sum_le_tsum _ (fun k _ => hpos k) (Real.summable_nat_rpow_inv.2 hα)

lemma sum_dvd_inv_le {g : ℕ} (hg : 1 ≤ g) (X : ℕ) :
    ∑ a ∈ Icc 1 X, (if g ∣ a then (a : ℝ)⁻¹ else 0) ≤ harm X / g := by
  rw [← Finset.sum_filter]
  have hsub : (Icc 1 X).filter (g ∣ ·) ⊆ (Icc 1 X).image (g * ·) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hn ⊢
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at h1
      · exact h
    · exact le_trans (Nat.le_mul_of_pos_left k (by omega)) h2
  calc _ ≤ ∑ n ∈ (Icc 1 X).image (g * ·), (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ = _ := by
        rw [Finset.sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h, harm,
          Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast; rw [mul_inv]; ring

lemma inv_lcm_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (X : ℕ) (haX : a ≤ X) :
    ((Nat.lcm a b : ℕ) : ℝ)⁻¹ ≤ ∑ g ∈ Icc 1 X,
      (if g ∣ a then (if g ∣ b then (g : ℝ) * (a : ℝ)⁻¹ * (b : ℝ)⁻¹ else 0) else 0) := by
  have hmem : Nat.gcd a b ∈ Icc 1 X := Finset.mem_Icc.2
    ⟨Nat.gcd_pos_of_pos_left _ (by omega), (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)).trans haX⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun g => (if g ∣ a then (if g ∣ b then
    (g : ℝ) * (a : ℝ)⁻¹ * (b : ℝ)⁻¹ else 0) else 0)) (fun g _ => by
      split_ifs <;> positivity) hmem)
  rw [ite_eq_left (Nat.gcd_dvd_left a b), ite_eq_left (Nat.gcd_dvd_right a b)]
  have h := Nat.gcd_mul_lcm a b
  have h' : ((Nat.gcd a b : ℕ) : ℝ) * (Nat.lcm a b : ℕ) = (a : ℝ) * b := by exact_mod_cast h
  have hl : (0 : ℝ) < (Nat.lcm a b : ℕ) := by exact_mod_cast Nat.lcm_pos (by omega) (by omega)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_iff_eq_or_lt]; left
  field_simp
  linarith

lemma dX_sq_sum_le {α : ℝ} (hα : 1 < α) (X L : ℕ) :
    ∑ n ∈ Icc 1 L, ((dX X n : ℝ)) ^ 2 * ((n : ℝ) ^ α)⁻¹ ≤ Sz α * harm X ^ 3 := by
  have hS : 0 ≤ Sz α := tsum_nonneg fun k => by positivity
  -- expand dX²
  have hexp : ∀ n, ((dX X n : ℝ)) ^ 2 = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      (if Nat.lcm a b ∣ n then (1 : ℝ) else 0) := by
    intro n
    simp only [dX, Finset.card_filter, Nat.cast_sum, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : a ∣ n <;> by_cases h2 : b ∣ n <;> simp [h1, h2, Nat.lcm_dvd_iff]
  calc _ = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ∑ n ∈ Icc 1 L,
        (if Nat.lcm a b ∣ n then ((n : ℝ) ^ α)⁻¹ else 0) := by
        simp_rw [hexp, Finset.sum_mul, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, Sz α * ((Nat.lcm a b : ℕ) : ℝ)⁻¹ := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
        have ha1 := (Finset.mem_Icc.1 ha).1; have hb1 := (Finset.mem_Icc.1 hb).1
        have hl : 1 ≤ Nat.lcm a b := Nat.lcm_pos (by omega) (by omega)
        refine (sum_mult_le hα hl L).trans ?_
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ hS
        have h1 : (1 : ℝ) ≤ (Nat.lcm a b : ℕ) := by exact_mod_cast hl
        exact inv_anti₀ (by positivity)
          (by simpa using Real.self_le_rpow_of_one_le h1 hα.le)
    _ ≤ ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, Sz α * ∑ g ∈ Icc 1 X,
        (if g ∣ a then (if g ∣ b then (g : ℝ) * (a : ℝ)⁻¹ * (b : ℝ)⁻¹ else 0) else 0) := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
        exact mul_le_mul_of_nonneg_left (inv_lcm_le (Finset.mem_Icc.1 ha).1
          (Finset.mem_Icc.1 hb).1 X (Finset.mem_Icc.1 ha).2) hS
    _ = Sz α * ∑ g ∈ Icc 1 X, (g : ℝ) * ((∑ a ∈ Icc 1 X, if g ∣ a then (a : ℝ)⁻¹ else 0) *
        (∑ b ∈ Icc 1 X, if g ∣ b then (b : ℝ)⁻¹ else 0)) := by
        simp_rw [← Finset.mul_sum]
        congr 1
        have e : ∀ f : ℕ → ℕ → ℕ → ℝ, ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ∑ g ∈ Icc 1 X, f a b g =
            ∑ g ∈ Icc 1 X, ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, f a b g := fun f => by
          calc _ = ∑ a ∈ Icc 1 X, ∑ g ∈ Icc 1 X, ∑ b ∈ Icc 1 X, f a b g :=
                Finset.sum_congr rfl fun a _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
        rw [e]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> ring
    _ ≤ Sz α * ∑ g ∈ Icc 1 X, (g : ℝ) * ((harm X / g) * (harm X / g)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g hg => ?_) hS
        have hg1 := (Finset.mem_Icc.1 hg).1
        have h0 : 0 ≤ ∑ a ∈ Icc 1 X, (if g ∣ a then (a : ℝ)⁻¹ else 0) :=
          Finset.sum_nonneg fun a _ => by split_ifs <;> positivity
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul (sum_dvd_inv_le hg1 X) (sum_dvd_inv_le hg1 X) h0
          (div_nonneg (harm_nonneg X) (by positivity))
    _ = Sz α * harm X ^ 3 := by
        congr 1
        rw [show harm X ^ 3 = harm X ^ 2 * harm X by ring, harm, Finset.mul_sum, ← harm]
        refine Finset.sum_congr rfl fun g hg => ?_
        have : (g : ℝ) ≠ 0 := by
          have := (Finset.mem_Icc.1 hg).1; positivity
        field_simp

end ZeroDensity
