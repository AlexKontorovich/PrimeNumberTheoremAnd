/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.Selberg
/-!
# Bounds for the Selberg sieve
This file proves a number of results to help bound `Sieve.selbergSum`

## Main Results
* `selbergBoundingSum_ge_sum_div`: If `ν` is completely multiplicative then `S ≥ ∑_{n ≤ √y}, ν n`
* `boundingSum_ge_log`: If `ν n = 1 / n` then `S ≥ log y / 2`
* `rem_sum_le_of_const`: If `R_d ≤ C` then the error term is at most `C * y * (1 + log y)^3`
-/

open scoped Nat ArithmeticFunction BigOperators Classical

noncomputable section
namespace Sieve

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p in s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)] at h_dvd
    cases' Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h_dvd with q hq
    rw [Finset.mem_erase] at hq
    exact hq.1.1 $ symm $ (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p in s, p := Trans.trans (dvd_mul_right p p) h_dvd
    cases' Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) this with q hq
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2

theorem zeta_pos_of_prime : ∀ (p : ℕ), Nat.Prime p → (0:ℝ) < (↑ζ:ArithmeticFunction ℝ) p := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime : ∀ (p : ℕ), Nat.Prime p → (↑ζ:ArithmeticFunction ℝ) p < (p:ℝ) := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num;
  exact Nat.succ_le.mp (Nat.Prime.two_le hp)

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    let h' : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h
    cases' h' with q hq
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ.mpr h, hp⟩

theorem siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1) (z : ℝ) (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    s.siftedSum = (s.support.filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [Sieve.siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr;
  rw [hP]
  ext d; constructor
  · intro hd
    rw [Finset.mem_filter] at *
    constructor
    · exact hd.1
    · intro p hpp hpy
      rw [←Nat.Prime.coprime_iff_not_dvd hpp]
      apply Nat.Coprime.coprime_dvd_left _ hd.2
      rw [prime_dvd_primorial_iff _ _ hpp]
      apply Nat.le_floor hpy
  · intro h
    rw [Finset.mem_filter] at *
    constructor
    · exact h.1
    refine Nat.coprime_of_dvd ?_
    intro p hp
    erw [prime_dvd_primorial_iff _ _ hp]
    intro hpy
    apply h.2 p hp
    trans ↑(Nat.floor z)
    · norm_cast
    · apply Nat.floor_le
      linarith only [hz]
  simp_rw [Nat.cast_one]
  intro x hx
  simp only [Finset.filter_congr_decidable, Finset.mem_filter] at hx
  apply hw x hx.1

def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop := f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, ite_false, Nat.cast_one,
    mul_eq_zero, Nat.cast_ite, CharP.cast_eq_zero, mul_ite, mul_zero, true_and]
  intro a b;
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [if_neg, if_neg hb, if_neg ha]; ring
  push_neg; exact ⟨ha, hb⟩

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
    constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simp_rw [pow_zero, hf.1]
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
  (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ)  (hd : Squarefree d)  (hf_size : ∀n, n.Prime → n ∣ d → f n < 1):
    f d * ∏ p in d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p in d.primeFactors, ∑ n in Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p in d.primeFactors, 1 / (1 - f p)
    = ∏ p in d.primeFactors, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
        rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw[one_div, div_eq_mul_inv]
  _ ≥ ∏ p in d.primeFactors, ∑ n in Finset.Icc 1 M, (f p)^n  := by
    gcongr with p hp
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
    rw [←Nat.Ico_succ_right, geom_sum_Ico, ←mul_div_mul_left (c:= (-1:ℝ)) (f p ^ Nat.succ M - f p ^ 1)]
    gcongr
    · apply hf_nonneg
    · linarith [hf_size p hp.1 hp.2]
    · rw [pow_one]
      have : 0 ≤ f p ^ (M.succ) := by
        apply pow_nonneg
        apply hf_nonneg
      linarith only [this]
    · linarith only
    · norm_num
    · apply ne_of_lt $ hf_size p hp.1 hp.2
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)

  _ = ∏ p in d.primeFactors, ∑ n in Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d):
    ∏ p in d.primeFactors, ∑ n in Finset.Icc 1 M, f (p^n)
    = ∑ m in (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p in d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self (Nat.prime_of_mem_factors $ List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]; push_neg
        exact fun _ => hq
        exact Nat.prime_of_mem_factors $ List.mem_toFinset.mp q.2
        exact (Nat.prime_of_mem_factors $ List.mem_toFinset.mp hp).ne_one
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_factors (List.mem_toFinset.mp q.2)))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_non_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      refine ⟨?_, hd.ne_zero⟩
      trans q
      · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      · apply Nat.dvd_of_mem_factors $ List.mem_toFinset.mp hq

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_factors (List.mem_toFinset.mp p.property)))
  save
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d^M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero (hi_ne_zero a ha),
      ←Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _;
      rw [hfact_i a ha]
      by_cases hp :  p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num;
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  save
  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p in d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_factors (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp $ Nat.prime_of_mem_factors (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.eq hc)

  save
  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp

  save
  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => (Nat.factorization b) p) ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      -- erw [List.mem_toFinset] at hp
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt $ Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt $ Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push_neg at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push_neg
        exact ⟨hpp.dvd_of_dvd_pow (h.trans hb.1.1), hd.ne_zero⟩
      · left; exact hpp

  exact Finset.sum_bij i hi i_inj i_surj h

theorem prod_primes_dvd_of_dvd (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime):
    ∏ p in s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  refine le_self_pow hx ?right.h
  norm_num

lemma Nat.squarefree_dvd_pow (a b N: ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [Squarefree.dvd_pow_iff_dvd ha hN] at hab
  exact hab

/-
Proposed generalisation :

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
  (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1):
    s.selbergBoundingSum ≥ ∑ m in
      (Finset.Icc 1 (Nat.floor $ Real.sqrt s.level)).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes),
      s.nu m

-/

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)
  (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1):
    s.selbergBoundingSum ≥ ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), s.nu m := by
  unfold SelbergSieve.selbergBoundingSum
  calc ∑ l in s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then s.selbergTerms l else 0)
     ≥ ∑ l in s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m in (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), s.nu m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p in l.primeFactors, ∑ n in Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
    · exact hnu
    · exact hlsq
    · rw [ne_eq, Nat.floor_eq_zero, not_lt]
      exact s.one_le_level
    rw [s.selbergTerms_apply l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg

  rw [←Finset.sum_biUnion]; apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm;
    have hprod_pos : 0 < (∏ p in m.primeFactors, p) := by
      apply Finset.prod_pos;
      intro p hp; exact Nat.pos_of_mem_factors $ List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p in m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    have hm_ne_zero : m ≠ 0 := by
      exact ne_of_gt $ Nat.succ_le.mp hm.1
    use ∏ p in m.primeFactors, p
    constructor; constructor; constructor
    · apply prod_primes_dvd_of_dvd <;> intro p hp
      · apply hP p $ Nat.prime_of_mem_primeFactors hp
        trans (m:ℝ)
        · norm_cast; exact Nat.le_of_mem_primeFactors hp
        trans (Real.sqrt s.level)
        · exact hm.2
        apply sqrt_le_self s.level s.one_le_level
      exact Nat.prime_of_mem_primeFactors hp
    · exact s.prodPrimes_ne_zero
    · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
      trans (m:ℝ)
      · norm_cast; apply Nat.le_of_dvd (Nat.succ_le.mp hm.1)
        exact Nat.prod_primeFactors_dvd m
      exact hm.2
      apply le_of_lt; norm_cast;
    constructor; constructor
    · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
      intro p
      have hy_mul_prod_nonneg : 0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p in m.primeFactors, p)) p := by
        apply mul_nonneg; apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]; norm_num
      trans (Nat.factorization m) p * 1
      · rw [mul_one];
      trans ⌊s.level⌋₊ * Nat.factorization (∏ p in m.primeFactors, p) p
      swap
      · apply le_rfl
      by_cases hpp : p.Prime
      swap;
      · rw [Nat.factorization_eq_zero_of_non_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
      by_cases hpdvd : p ∣ m
      swap
      · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
      apply mul_le_mul
      trans m
      · apply le_of_lt $ Nat.factorization_lt _ _
        apply hm_ne_zero
      apply Nat.le_floor
      refine le_trans hm.2 ?_
      apply sqrt_le_self _ s.one_le_level
      rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp $ ne_of_gt hprod_pos, pow_one]
      apply Finset.dvd_prod_of_mem
      rw [Nat.mem_primeFactors]
      · exact ⟨hpp, hpdvd, hm_ne_zero⟩
      norm_num
      norm_num
      exact hm_ne_zero
    · exact hprod_ne_zero
    · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i _ _
    apply (hnu_nonneg _)
  · intro i hi j hj hij
    intro t hti htj
    intro x hx;
    simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (s.squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij $ Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), 1 / (m:ℝ) := by
  trans ∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), (ζ : ArithmeticFunction ℝ).pdiv .id m
  rw[←hnu]
  apply selbergBoundingSum_ge_sum_div
  · intro p hpp hple
    apply hP p hpp hple
  · rw[hnu]
    exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
  · intro n;
    rw[hnu]
    apply div_nonneg
    · by_cases h : n = 0 <;> simp[h]
    simp
  · intro p hpp _
    rw[hnu]
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
      ArithmeticFunction.id_apply]
    rw [if_neg, one_div]
    apply inv_lt_one; norm_cast
    exact hpp.one_lt
    exact hpp.ne_zero
  apply le_of_eq
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
    ArithmeticFunction.id_apply];

theorem boundingSum_ge_log (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)  :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m in Finset.Icc 1 (Nat.floor $ Real.sqrt s.level), 1 / (m:ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log $ Real.sqrt s.level)
  rw [ge_iff_le]; simp_rw[one_div]
  apply Aux.log_le_sum_inv (Real.sqrt s.level)
  rw [Real.le_sqrt] <;> linarith[s.one_le_level]
  apply ge_of_eq
  refine Real.log_sqrt ?h.hx
  linarith[s.one_le_level]

open ArithmeticFunction

theorem rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |s.rem d| ≤ C) :
    ∑ d in s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |s.rem d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d in  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.toSieve.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| s.rem 1, hrem 1 (by norm_num)]
  push_cast
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply Sieve.prodPrimes_squarefree

end Sieve
end
