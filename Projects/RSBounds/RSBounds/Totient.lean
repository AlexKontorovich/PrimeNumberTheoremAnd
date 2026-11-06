import RSBounds.SmallTotientProduct

/-!
# A finite-range Rosser--Schoenfeld totient bound

The numerical constant 2.50637 is proved for integers with at most twenty
prime factors, and hence for every natural q with 3 <= q <= 10^27.
The unrestricted theorem is not claimed. The general reduction leaves the
prime-product input as an explicit argument, not an axiom.

Elementary exchange and comparison proofs are adapted from
`TernaryGoldbach/Prelim/MertensProduct.lean` at upstream
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`. That conditional module is not
imported here. No RH, Buethe, or Ramare sum estimate is assumed.
-/

open Finset

namespace TernaryGoldbach.RSBounds.Totient

noncomputable def primeTheta (x : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log p

noncomputable def primeProduct (x : ℕ) : ℝ :=
  ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1))

/-- `q/φ(q) = ∏_{p ∣ q} p/(p−1)`. -/
theorem div_totient_eq_prod {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) / Nat.totient q = ∏ p ∈ q.primeFactors, ((p : ℝ) / (p - 1)) := by
  have h := Nat.totient_mul_prod_primeFactors q
  have h' : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
      q * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]; congr 1
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hP : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    refine prod_pos fun p hp => ?_
    have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  rw [prod_div_distrib, div_eq_div_iff hφ.ne' hP.ne']
  linarith

/-- The `p/(p−1)` factors decrease. -/
theorem frac_anti {a b : ℕ} (hb : 2 ≤ b) (hab : b ≤ a) :
    (a : ℝ) / (a - 1) ≤ (b : ℝ) / (b - 1) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hab' : (b : ℝ) ≤ a := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

/-- Exchange: a set of `k` primes has `∏ p/(p−1)` at most, and product at least, those of the first
`k` primes. -/
theorem exch (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, ((p : ℝ) / (p - 1)) ≤
        ∏ i ∈ range P.card, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) ∧
      ∏ i ∈ range P.card, Nat.nth Nat.Prime i ≤ ∏ p ∈ P, p := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a.Prime := hP a (mem_insert_self a s)
    have ih := ih (fun p hp => hP p (mem_insert_of_mem hp))
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    -- `a ≥ nth (card s)`
    have hcount : s.card < Nat.count Nat.Prime (a + 1) := by
      rw [Nat.count_eq_card_filter_range]
      have : insert a s ⊆ (range (a + 1)).filter (fun x => Nat.Prime x) := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨mem_range.2 (by omega), ha⟩
        · exact mem_filter.2 ⟨mem_range.2 (by have := hlt x hx; omega),
            hP x (mem_insert_of_mem hx)⟩
      have := card_le_card this
      rw [card_insert_of_notMem has] at this
      omega
    have hnth : Nat.nth Nat.Prime s.card ≤ a := by
      have := Nat.nth_lt_of_lt_count hcount; omega
    have hn2 : 2 ≤ Nat.nth Nat.Prime s.card := (Nat.prime_nth_prime _).two_le
    rw [card_insert_of_notMem has, prod_insert has, prod_insert has, prod_range_succ, prod_range_succ]
    constructor
    · have h1 := frac_anti hn2 hnth
      have h0 : (0 : ℝ) ≤ (a : ℝ) / (a - 1) := by
        have : (1 : ℝ) < a := by exact_mod_cast ha.one_lt
        exact div_nonneg (by linarith) (by linarith)
      have h0' : (0 : ℝ) ≤ ∏ p ∈ s, ((p : ℝ) / (p - 1)) := by
        refine prod_nonneg fun p hp => ?_
        have : (1 : ℝ) < p := by exact_mod_cast (hP p (mem_insert_of_mem hp)).one_lt
        exact div_nonneg (by linarith) (by linarith)
      calc (a : ℝ) / (a - 1) * ∏ p ∈ s, ((p : ℝ) / (p - 1)) ≤
            (Nat.nth Nat.Prime s.card : ℝ) / (Nat.nth Nat.Prime s.card - 1) *
              ∏ i ∈ range s.card, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) :=
            mul_le_mul h1 ih.1 h0' (by
              have : (2 : ℝ) ≤ Nat.nth Nat.Prime s.card := by exact_mod_cast hn2
              exact div_nonneg (by linarith) (by linarith))
        _ = _ := by ring
    · calc (∏ i ∈ range s.card, Nat.nth Nat.Prime i) * Nat.nth Nat.Prime s.card ≤
            (∏ p ∈ s, p) * a := Nat.mul_le_mul ih.2 hnth
        _ = a * ∏ p ∈ s, p := by ring

/-- The first `k` primes are the primes up to the `k`-th one. -/
theorem image_nth (k : ℕ) (hk : 1 ≤ k) :
    (range k).image (Nat.nth Nat.Prime) = (Icc 1 (Nat.nth Nat.Prime (k - 1))).filter Nat.Prime := by
  ext p
  simp only [mem_image, mem_range, mem_filter, mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨(Nat.prime_nth_prime i).one_lt.le,
      Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)⟩, Nat.prime_nth_prime i⟩
  · rintro ⟨⟨_, hp⟩, hpp⟩
    refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hpp⟩
    have h1 := Nat.count_monotone Nat.Prime hp
    rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at h1
    have h2 : Nat.count Nat.Prime p < Nat.count Nat.Prime (p + 1) := by
      rw [Nat.count_succ]; simp [hpp]
    omega

theorem exp_gamma_ge : 1.625 ≤ Real.exp Real.eulerMascheroniConstant := by
  have h1 := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
  have h2 : Real.exp (1 / 2) ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.exp_le_exp.2 Real.one_half_lt_eulerMascheroniConstant.le
  norm_num at h1; linarith

theorem bigF_gt {r : ℝ} (hr : 3 ≤ r) :
    3.75 < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) := by
  have hl1 : 1 < Real.log r := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    exact Real.exp_one_lt_d9.trans_le (by linarith)
  set t := Real.log (Real.log r)
  have ht : 0 < t := Real.log_pos hl1
  have hG := exp_gamma_ge
  have h1 : 1.625 * t ≤ Real.exp Real.eulerMascheroniConstant * t :=
    mul_le_mul_of_nonneg_right hG ht.le
  have h2 : 3.75 < 1.625 * t + 2.50637 / t := by
    rw [← sub_pos]
    have e : 1.625 * t + 2.50637 / t - 3.75 = (1.625 * t ^ 2 - 3.75 * t + 2.50637) / t := by
      field_simp; ring
    rw [e]; apply div_pos _ ht
    nlinarith [sq_nonneg (t - 1.15385)]
  linarith

theorem totient_ratio_lt_of_prime_product_at_rank {q : ℕ} (hq : 1 ≤ q)
    {r : ℝ} (hr : 3 ≤ r) (hqr : (q : ℝ) ≤ r)
    (hproduct : 4 ≤ q.primeFactors.card →
      primeProduct (Nat.nth Nat.Prime (q.primeFactors.card - 1)) <
        Real.exp Real.eulerMascheroniConstant *
            Real.log (primeTheta (Nat.nth Nat.Prime (q.primeFactors.card - 1))) +
          2.50637 / Real.log (primeTheta (Nat.nth Nat.Prime (q.primeFactors.card - 1)))) :
    (q : ℝ) / Nat.totient q < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) := by
  set P := q.primeFactors with hP
  set k := P.card with hk
  set G := Real.exp Real.eulerMascheroniConstant with hGdef
  have hex := exch P (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [div_totient_eq_prod hq]
  have hF3 := bigF_gt hr
  have hgpos : ∀ i, (0 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1) := by
    intro i
    have : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
    exact div_nonneg (by linarith) (by linarith)
  have hg1 : ∀ i, (1 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1) := by
    intro i
    have : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).two_le
    rw [le_div_iff₀ (by linarith)]; linarith
  rcases le_or_gt k 3 with hk3 | hk3
  · have h1 : ∏ i ∈ range k, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) ≤
        ∏ i ∈ range 3, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) :=
      prod_le_prod_of_subset_of_one_le₀ (range_subset_range.2 hk3) (fun i _ => hgpos i)
        (fun i _ _ => hg1 i)
    have h2 : ∏ i ∈ range 3, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) = 3.75 := by
      simp only [prod_range_succ, prod_range_zero, Nat.nth_prime_zero_eq_two,
        Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
      norm_num
    linarith [hex.1]
  -- `k ≥ 4`: compare with the primes up to `x = p_k`
  set x := Nat.nth Nat.Prime (k - 1) with hx
  have himg := image_nth k (by omega)
  have hinj : Set.InjOn (Nat.nth Nat.Prime) (range k : Set ℕ) :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective.injOn
  have hprodF : ∏ i ∈ range k, ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1)) =
      ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) := by
    rw [← himg, prod_image (fun a ha b hb h => hinj ha hb h)]
  have hθ : primeTheta x = Real.log (∏ i ∈ range k, (Nat.nth Nat.Prime i : ℝ)) := by
    rw [primeTheta, ← himg, sum_image (fun a ha b hb h => hinj ha hb h), Real.log_prod]
    intro i _
    exact_mod_cast (Nat.prime_nth_prime i).pos.ne'
  have hx7 : 7 ≤ x := by
    rw [hx, ← Nat.nth_prime_three_eq_seven]
    exact Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)
  have hF := hproduct (by simpa only [← hP, ← hk] using (show 4 ≤ k by omega))
  change primeProduct x < _ at hF
  dsimp only [primeProduct] at hF
  -- `θ(x) ≤ log r`
  have hprodpos : (0 : ℝ) < ∏ i ∈ range k, (Nat.nth Nat.Prime i : ℝ) :=
    prod_pos fun i _ => by exact_mod_cast (Nat.prime_nth_prime i).pos
  have hθr : primeTheta x ≤ Real.log r := by
    rw [hθ]
    apply Real.log_le_log hprodpos
    have h1 : ∏ i ∈ range k, Nat.nth Nat.Prime i ≤ q :=
      hex.2.trans (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q))
    have h2 : ((∏ i ∈ range k, Nat.nth Nat.Prime i : ℕ) : ℝ) ≤ q := by exact_mod_cast h1
    push_cast at h2
    linarith
  -- `θ(x) ≥ log 210 ≥ 4`
  have hθ4 : 4 ≤ primeTheta x := by
    rw [hθ]
    have h1 : ∏ i ∈ range 4, Nat.nth Nat.Prime i ≤ ∏ i ∈ range k, Nat.nth Nat.Prime i :=
      prod_le_prod_of_subset_of_one_le (range_subset_range.2 (by omega))
        (fun i _ _ => (Nat.prime_nth_prime i).one_lt.le)
    have h2 : ∏ i ∈ range 4, Nat.nth Nat.Prime i = 210 := by
      simp only [prod_range_succ, prod_range_zero, Nat.nth_prime_zero_eq_two,
        Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
      norm_num
    rw [h2] at h1
    have h3 : (210 : ℝ) ≤ ∏ i ∈ range k, (Nat.nth Nat.Prime i : ℝ) := by exact_mod_cast h1
    rw [Real.le_log_iff_exp_le hprodpos]
    have := Real.exp_one_lt_d9
    calc Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 4
      _ ≤ 210 := by norm_num
      _ ≤ _ := h3
  -- monotonicity of `t ↦ G t + c/t`
  set t₁ := Real.log (primeTheta x) with ht₁
  set t₂ := Real.log (Real.log r) with ht₂
  have ht₁0 : 1.386 ≤ t₁ := by
    have : Real.log 4 ≤ t₁ := Real.log_le_log (by norm_num) hθ4
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have ht₁₂ : t₁ ≤ t₂ := Real.log_le_log (by linarith) hθr
  have hG := exp_gamma_ge
  have hmono : G * t₁ + 2.50637 / t₁ ≤ G * t₂ + 2.50637 / t₂ := by
    have ht0 : 0 < t₁ := by linarith
    have ht0' : 0 < t₂ := by linarith
    have e : G * t₂ + 2.50637 / t₂ - (G * t₁ + 2.50637 / t₁) =
        (t₂ - t₁) * (G - 2.50637 / (t₁ * t₂)) := by field_simp; ring
    have h1 : 2.50637 / (t₁ * t₂) ≤ 1.625 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have : 0 ≤ (t₂ - t₁) * (G - 2.50637 / (t₁ * t₂)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  linarith [hex.1]

/-- The finite certificate suffices whenever there are at most twenty prime factors. -/
theorem totient_ratio_lt_of_card_le_twenty {q : ℕ} (hq : 1 ≤ q)
    (hcard : q.primeFactors.card ≤ 20) {r : ℝ} (hr : 3 ≤ r) (hqr : (q : ℝ) ≤ r) :
    (q : ℝ) / Nat.totient q < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) := by
  apply totient_ratio_lt_of_prime_product_at_rank hq hr hqr
  intro h4
  have hc : Nat.count Nat.Prime 72 = 20 := by decide +kernel
  have hx : Nat.nth Nat.Prime (q.primeFactors.card - 1) ≤ 71 := by
    have hlt : q.primeFactors.card - 1 < Nat.count Nat.Prime 72 := by omega
    have := Nat.nth_lt_of_lt_count hlt
    omega
  have h5 : 5 ≤ Nat.nth Nat.Prime (q.primeFactors.card - 1) := by
    rw [← Nat.nth_prime_two_eq_five]
    apply Nat.nth_monotone Nat.infinite_setOfPred_prime
    omega
  exact SmallTotientProduct.mertens_product_kernel _ (Nat.prime_nth_prime _) h5 hx

/-- Twenty-one distinct prime factors force an integer to exceed 10^27. -/
theorem primeFactors_card_le_twenty {q : ℕ} (hq : 1 ≤ q) (hmax : q ≤ 10 ^ 27) :
    q.primeFactors.card ≤ 20 := by
  by_contra h
  have hk : 21 ≤ q.primeFactors.card := by omega
  have hex := (exch q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)).2
  have hsmall : ∏ i ∈ range 21, Nat.nth Nat.Prime i ≤
      ∏ i ∈ range q.primeFactors.card, Nat.nth Nat.Prime i :=
    prod_le_prod_of_subset_of_one_le (range_subset_range.2 hk)
      (fun i _ _ => (Nat.prime_nth_prime i).one_lt.le)
  have hprodq : ∏ i ∈ range 21, Nat.nth Nat.Prime i ≤ q :=
    hsmall.trans (hex.trans (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)))
  have hc : Nat.count Nat.Prime 73 = 20 := by decide +kernel
  have hn : Nat.nth Nat.Prime 20 = 73 := by
    have h73 : Nat.Prime 73 := by decide
    simpa only [hc] using Nat.nth_count h73
  have hi := image_nth 21 (by norm_num)
  norm_num only at hi
  rw [hn] at hi
  have heq : (∏ i ∈ range 21, Nat.nth Nat.Prime i) =
      ∏ p ∈ (Icc 1 73).filter Nat.Prime, p := by
    rw [← hi, prod_image]
    exact fun a _ b _ hab => (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hab
  have hv : (∏ p ∈ (Icc 1 73).filter Nat.Prime, p) = 40729680599249024150621323470 := by
    decide +kernel
  rw [heq, hv] at hprodq
  norm_num at hmax
  omega

/-- Exact RS62 coefficient throughout the finite range needed here. -/
theorem totient_ratio_lt_of_le_1e27 {q : ℕ} (hq : 1 ≤ q) (hmax : q ≤ 10 ^ 27)
    {r : ℝ} (hr : 3 ≤ r) (hqr : (q : ℝ) ≤ r) :
    (q : ℝ) / Nat.totient q < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) :=
  totient_ratio_lt_of_card_le_twenty hq (primeFactors_card_le_twenty hq hmax) hr hqr

/-- The usual single-variable form, proved for 3 <= q <= 10^27. -/
theorem totient_ratio_lt_self_of_le_1e27 {q : ℕ} (hq : 3 ≤ q) (hmax : q ≤ 10 ^ 27) :
    (q : ℝ) / Nat.totient q <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (q : ℝ)) +
        2.50637 / Real.log (Real.log (q : ℝ)) :=
  totient_ratio_lt_of_le_1e27 (by omega) hmax (by exact_mod_cast hq) le_rfl

end TernaryGoldbach.RSBounds.Totient
