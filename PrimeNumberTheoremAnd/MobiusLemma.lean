import Architect
import PrimeNumberTheoremAnd.PrimaryDefinitions
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.NormNum.RealSqrt

blueprint_comment /--
\section{A Lemma involving the M\"obius Function}
-/

blueprint_comment /--
In this section we establish a lemma involving sums of the M\"obius function.
-/

namespace MobiusLemma

open ArithmeticFunction Real Finset MeasureTheory Measurable Complex

@[blueprint
  "Q-def"
  (title := "Q")
  (statement := /-- $Q(x)$ is the number of squarefree integers $\leq x$. -/)]
noncomputable def Q (x : ℝ) : ℕ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if Squarefree n then 1 else 0

@[blueprint
  "R-def"
  (title := "R")
  (statement := /-- $R(x) = Q(x) - x / \zeta(2)$. -/)]
noncomputable def R (x : ℝ) : ℝ := Q x - x / (riemannZeta 2).re

@[blueprint
  "M-def"
  (title := "M")
  (statement := /-- $M(x)$ is the summatory function of the M\"obius function. -/)]
noncomputable def M (x : ℝ) : ℤ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, moebius n

/-- The function `f(n) = ∑_{d² ∣ n} μ(d)`. -/
noncomputable def sum_sq_div_moebius (n : ℕ) : ℤ :=
    ∑ d ∈ n.divisors.filter (fun d ↦ d ^ 2 ∣ n), (moebius d : ℤ)

/-- If `m, n` are coprime and `a ∣ m`, `b ∣ n`, then `(ab)² ∣ mn` iff `a² ∣ m` and `b² ∣ n`. -/
lemma sq_dvd_mul_iff_of_coprime {m n a b : ℕ} (hmn : m.Coprime n) (ha : a ∣ m) (hb : b ∣ n) :
    (a * b) ^ 2 ∣ m * n ↔ a ^ 2 ∣ m ∧ b ^ 2 ∣ n := by
  refine ⟨fun h ↦ ?_, fun ⟨ha', hb'⟩ ↦ ?_⟩
  · rw [mul_pow] at h
    constructor
    · exact ((hmn.coprime_dvd_left ha).pow_left 2).dvd_of_dvd_mul_right
        ((dvd_mul_right _ _).trans h)
    · exact ((hmn.coprime_dvd_right hb).symm.pow_left 2).dvd_of_dvd_mul_left
        ((dvd_mul_left _ _).trans h)
  · rw [mul_pow ..]; exact mul_dvd_mul ha' hb'

/-- The function `sum_sq_div_moebius` is multiplicative (explicitly stated). -/
lemma sum_sq_div_moebius_is_multiplicative_explicit : (sum_sq_div_moebius 1 = 1) ∧
    (∀ m n : ℕ, Nat.Coprime m n →
      sum_sq_div_moebius (m * n) = sum_sq_div_moebius m * sum_sq_div_moebius n) := by
  have h_map : ∀ m n, m.Coprime n →
      (Nat.divisors (m * n)).filter (fun d ↦ d ^ 2 ∣ m * n) =
        image (fun p : ℕ × ℕ ↦ p.1 * p.2)
          ((Nat.divisors m).filter (fun d ↦ d ^ 2 ∣ m) ×ˢ
            (Nat.divisors n).filter (fun d ↦ d ^ 2 ∣ n)) := by
    intro m n hmn
    ext d
    simp only [mem_filter, Nat.mem_divisors, ne_eq, mul_eq_zero, not_or, mem_image,
      mem_product, Prod.exists]
    refine ⟨fun hd ↦ ?_, ?_⟩
    swap
    · rintro ⟨a, b, ⟨⟨⟨ha₁, ha₂⟩, ha₃⟩, ⟨⟨hb₁, hb₂⟩, hb₃⟩⟩, rfl⟩
      exact ⟨⟨mul_dvd_mul ha₁ hb₁, ha₂, hb₂⟩, by convert mul_dvd_mul ha₃ hb₃ using 1; ring⟩
    obtain ⟨hd_div, hd_sq_div⟩ := hd
    obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b : ℕ, a ∣ m ∧ b ∣ n ∧ d = a * b :=
      Exists.imp (by grind) (Nat.dvd_mul.mp hd_div.1)
    simp_all only [mul_pow, not_false_eq_true, and_true]
    exact ⟨a, b, ⟨⟨ha, (hmn.coprime_dvd_left ha).pow_left 2 |>.dvd_of_dvd_mul_right <|
      dvd_of_mul_right_dvd hd_sq_div⟩, hb,
      (hmn.symm.coprime_dvd_left hb).pow_left 2 |>.dvd_of_dvd_mul_left <|
        dvd_of_mul_left_dvd hd_sq_div⟩, rfl⟩
  have h_sum : ∀ m n : ℕ, Nat.Coprime m n →
      ∑ d ∈ (Nat.divisors (m * n)).filter (fun d ↦ d ^ 2 ∣ m * n), (moebius d : ℤ) =
        ∑ a ∈ (Nat.divisors m).filter (fun d ↦ d ^ 2 ∣ m),
          ∑ b ∈ (Nat.divisors n).filter (fun d ↦ d ^ 2 ∣ n), (moebius (a * b) : ℤ) := by
    intro m n hmn
    rw [h_map m n hmn, sum_image, sum_product]
    intro p hp q hq h_eq
    have hp1_eq_q1 : p.1 = q.1 := by
      norm_num at *
      have hdvd : p.1 ∣ q.1 ∧ q.1 ∣ p.1 :=
        ⟨(hmn.coprime_dvd_left (by grind)).coprime_dvd_right (by grind) |>.dvd_of_dvd_mul_right <|
          h_eq ▸ dvd_mul_right _ _,
         (hmn.coprime_dvd_left (by grind)).coprime_dvd_right (by grind) |>.dvd_of_dvd_mul_right <|
          h_eq.symm ▸ dvd_mul_right _ _⟩
      exact Nat.dvd_antisymm hdvd.1 hdvd.2
    aesop
  have h_inner : ∀ m n, m.Coprime n → ∀ a ∈ (Nat.divisors m).filter (fun d ↦ d ^ 2 ∣ m),
      ∀ b ∈ (Nat.divisors n).filter (fun d ↦ d ^ 2 ∣ n),
        (moebius (a * b) : ℤ) = (moebius a : ℤ) * (moebius b : ℤ) := by
    intro m n hmn a ha b hb
    simp only [moebius, mem_filter, Nat.mem_divisors, ne_eq, Int.reduceNeg, coe_mk,
      mul_ite, ite_mul, zero_mul, mul_zero] at *
    split_ifs with h <;> simp_all only [Nat.squarefree_mul_iff, and_self, and_true, ne_eq,
      Int.reduceNeg, zero_eq_mul, pow_eq_zero_iff', neg_eq_zero, one_ne_zero,
      cardFactors_eq_zero_iff_eq_zero_or_one, not_or, false_and, or_self, and_false]
    · rw [← pow_add, cardFactors_mul]
      · intro a; simp_all [Int.reduceNeg]
      · intro a; simp_all [Int.reduceNeg]
    · exact h (hmn.coprime_dvd_left ha.1.1 |>.coprime_dvd_right hb.1.1)
  dsimp only [sum_sq_div_moebius]
  exact ⟨by simp [sum_filter], fun m n hmn ↦ by
    rw [h_sum m n hmn, sum_mul]
    exact sum_congr rfl fun i hi ↦ by
      rw [mul_sum]; exact sum_congr rfl fun j hj ↦ h_inner m n hmn i hi j hj⟩

/- For a prime power `p^k`, `sum_sq_div_moebius` is `1` if `k < 2` and `0` otherwise. -/
lemma sum_sq_div_moebius_prime_pow (p k : ℕ) (hp : Nat.Prime p) :
    sum_sq_div_moebius (p ^ k) = if k < 2 then 1 else 0 := by
  dsimp only [sum_sq_div_moebius]
  split_ifs <;> simp_all only [Nat.divisors_prime_pow, moebius, Int.reduceNeg, coe_mk,
    not_lt, Int.reduceNeg]
  · interval_cases k <;> norm_num [sum_filter, sum_range_succ]
    exact fun h ↦ absurd h <| Nat.not_dvd_of_pos_of_lt hp.pos <| by nlinarith [hp.two_le]
  · rcases k with (_ | _ | k) <;> simp_all [sum_filter, sum_range_succ', Nat.squarefree_pow_iff,
      hp.ne_zero, hp.ne_one, pow_dvd_pow_iff, hp.squarefree]

/-- The function `sum_sq_div_moebius` is equal to the indicator function of squarefree numbers. -/
lemma sum_sq_div_moebius_eq_squarefree (n : ℕ) (hn : n > 0) :
    sum_sq_div_moebius n = if Squarefree n then 1 else 0 := by
  induction n using Nat.strongRecOn with | _ n ih =>
  by_cases h_prime_pow : ∃ p k, p.Prime ∧ n = p ^ k;
  · obtain ⟨p, k, hp, rfl⟩ := h_prime_pow;
    rw [sum_sq_div_moebius_prime_pow]
    · rcases k with (_ | _ | k) <;> simp_all only [zero_add, pow_one, gt_iff_lt,
        Nat.one_lt_ofNat, ↓reduceIte, left_eq_ite_iff, one_ne_zero, imp_false, Decidable.not_not]
      · simp_all
      · exact hp.squarefree
      · rw [if_neg (by grind), if_neg (by rw [Nat.squarefree_pow_iff] <;> aesop)]
    · assumption
  · obtain ⟨m, n', hm, hn', h_coprime⟩ : ∃ m n' : ℕ, 1 < m ∧ 1 < n' ∧ m.Coprime n' ∧ n = m * n' := by
      obtain ⟨p, hp⟩ : ∃ p, p.Prime ∧ p ∣ n :=
        Nat.exists_prime_and_dvd fun rfl ↦ h_prime_pow ⟨2, 0, Nat.prime_two, rfl⟩
      obtain ⟨k, m, hm⟩ : ∃ k m, n = p ^ k * m ∧ ¬p ∣ m :=
        ⟨Nat.factorization n p, n / p ^ Nat.factorization n p, by
          rw [Nat.mul_div_cancel' (Nat.ordProj_dvd n p)], Nat.not_dvd_ordCompl hp.1 hn.ne'⟩
      simp only [gt_iff_lt, exists_and_left, not_exists, not_and] at *
      exact ⟨p ^ k, one_lt_pow₀ hp.1.one_lt (by specialize h_prime_pow p hp.1 k; aesop), m,
        Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨by grind, by specialize h_prime_pow p hp.1 k; grind⟩,
          Nat.Coprime.pow_left _ (hp.1.coprime_iff_not_dvd.mpr hm.2), hm.1⟩
    have h_mul : sum_sq_div_moebius n = sum_sq_div_moebius m * sum_sq_div_moebius n' :=
      h_coprime.2.symm ▸ sum_sq_div_moebius_is_multiplicative_explicit.2 _ _ h_coprime.1
    simp_all [Nat.squarefree_mul_iff]
    aesop

@[blueprint
  "mobius-lemma-1-sub"
  (title := "Mobius Lemma 1, initial step")
  (statement := /--
    For any $x>0$, $$Q(x) = \sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right)$$.
  -/)
  (proof := /--
    We compute
    $$Q(x) = \sum_{n\leq x} \sum_{d: d^2|n} \mu(d) = \sum_{k, d: k d^2\leq x} \mu(d)$$
    giving the claim.
  -/)
  (latexEnv := "sublemma")
  (discussion := 526)]
theorem mobius_lemma_1_sub (x : ℝ) (hx : x > 0) :
    Q x = ∑ k ∈ Ioc 0 ⌊x⌋₊, M (sqrt (x / k)) := by
  have h_exercise : ∑ n ∈ Ioc 0 ⌊x⌋₊, (if Squarefree n then 1 else 0) =
      ∑ k ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ filter (fun d ↦ d ^ 2 ∣ k) (Nat.divisors k), (moebius d : ℤ) :=
    sum_congr rfl fun n hn ↦ by
      rw [← sum_sq_div_moebius_eq_squarefree n (mem_Ioc.mp hn).1]; rfl
  have h_rewrite : ∑ k ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ filter (fun d ↦ d ^ 2 ∣ k) (Nat.divisors k),
      (moebius d : ℤ) = ∑ d ∈ Icc 1 ⌊sqrt x⌋₊, ∑ k ∈ Icc 1 ⌊x / (d ^ 2)⌋₊, (moebius d : ℤ) := by
    have h_reorder : ∑ k ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ filter (fun d ↦ d ^ 2 ∣ k) (Nat.divisors k),
        (moebius d : ℤ) =
          ∑ d ∈ Icc 1 ⌊sqrt x⌋₊, ∑ k ∈ filter (fun k ↦ d ^ 2 ∣ k) (Ioc 0 ⌊x⌋₊),
            (moebius d : ℤ) := by
      repeat rw [sum_sigma']
      apply sum_bij (fun p hp ↦ ⟨p.snd, p.fst⟩)
      · simp only [mem_sigma, mem_Ioc, mem_filter, Nat.mem_divisors, mem_Icc, and_imp] at *
        exact fun a ha₁ ha₂ ha₃ ha₄ ha₅ ↦ ⟨⟨Nat.pos_of_dvd_of_pos ha₃ ha₁, Nat.le_floor <|
          le_sqrt_of_sq_le <| le_trans (mod_cast Nat.le_of_dvd ha₁ ha₅) (Nat.floor_le hx.le |>
            le_trans (Nat.cast_le.mpr ha₂))⟩, ⟨ha₁, ha₂⟩, ha₅⟩
      · aesop
      · simp only [mem_sigma, mem_Icc, mem_filter, mem_Ioc, Nat.mem_divisors, Sigma.exists,
          and_imp]
        exact fun b hb₁ hb₂ hb₃ hb₄ hb₅ ↦
          ⟨b.snd, b.fst, ⟨⟨hb₃, hb₄⟩, ⟨dvd_of_mul_left_dvd hb₅, by grind⟩, hb₅⟩, rfl⟩
      · grind
    have h_div : ∀ d ∈ Icc 1 ⌊sqrt x⌋₊,
        filter (fun k ↦ d ^ 2 ∣ k) (Ioc 0 ⌊x⌋₊) =
          image (fun m ↦ d ^ 2 * m) (Icc 1 ⌊x / (d ^ 2)⌋₊) := by
      intro d hd
      ext k
      simp only [mem_filter, mem_Ioc, mem_image, mem_Icc]
      refine ⟨fun hk ↦ ?_, ?_⟩
      · obtain ⟨a, rfl⟩ := hk.2
        refine ⟨a, ⟨by nlinarith [mem_Icc.mp hd], Nat.le_floor ?_⟩, rfl⟩
        rw [le_div_iff₀ (by norm_cast; nlinarith [mem_Icc.mp hd])]
        exact Nat.floor_le hx.le |> le_trans (mod_cast by nlinarith)
      · simp only [mem_Icc, forall_exists_index, and_imp] at *
        rintro m hm₁ hm₂ rfl
        refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
        rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by norm_cast; nlinarith)] at *
        norm_cast at *
        simpa [mul_comm] using hm₂
    simp_all only [sum_const]
    exact sum_congr rfl fun i hi ↦ by
      rw [card_image_of_injective _ fun a b h ↦
        mul_left_cancel₀ (pow_ne_zero 2 <| Nat.ne_of_gt <| (mem_Icc.mp hi).1) h]
  have h_interchange : ∑ d ∈ Icc 1 ⌊Real.sqrt x⌋₊, ∑ k ∈ Icc 1 ⌊x / (d ^ 2)⌋₊, (moebius d : ℤ) =
      ∑ k ∈ Ioc 0 ⌊x⌋₊, ∑ d ∈ Icc 1 ⌊Real.sqrt (x / k)⌋₊, (moebius d : ℤ) := by
    rw [sum_sigma', sum_sigma']
    apply sum_bij (fun p hp ↦ ⟨p.snd, p.fst⟩)
    · norm_num at *
      refine fun a ha₁ ha₂ ha₃ ha₄ ↦ ⟨⟨ha₃, ha₄.trans (Nat.floor_mono <| div_le_self hx.le <|
        mod_cast Nat.one_le_pow _ _ ha₁)⟩, ha₁, ?_⟩
      rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by positivity)] at *
      exact le_sqrt_of_sq_le (by nlinarith [mul_self_sqrt (Nat.cast_nonneg a.snd)])
    · grind
    · simp only [Nat.cast_nonneg, sqrt_div', mem_sigma, mem_Ioc, mem_Icc, Sigma.exists,
        and_imp] at *
      refine fun ⟨a, b⟩ ha hb ha' hb' ↦ ⟨b, a, ?_, rfl⟩
      rw [Nat.le_floor_iff (by positivity), le_div_iff₀] at * <;> norm_num at *
      · refine ⟨⟨ha', le_trans (le_mul_of_one_le_right (by positivity)
          (le_sqrt_of_sq_le (mod_cast ha))) hb'⟩, ha, Nat.le_floor ?_⟩
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_self_sqrt (Nat.cast_nonneg a), mul_self_sqrt (show 0 ≤ x by positivity),
          sqrt_nonneg a, sqrt_nonneg x, mul_le_mul_of_nonneg_left hb' (sqrt_nonneg a),
            mul_le_mul_of_nonneg_left hb' (sqrt_nonneg a)]
      · positivity
    · intro a ha; simp_all
  simp_all only [Q, M, sum_boole, Nat.cast_id]; rfl

/-- The sum `∑' n, μ(n) / n² = 1 / ζ(2)`. -/
theorem sum_moebius_div_sq : ∑' n, (moebius n) / (n : ℝ) ^ 2 = 1 / (riemannZeta 2).re := by
  have h_sum : ∑' n, (moebius n) / (n : ℂ) ^ 2 = 1 / riemannZeta 2 := by
    have h_zeta2 : riemannZeta 2 * ∑' n, (moebius n : ℂ) / (n : ℂ) ^ 2 = 1 := by
      convert LSeries_zeta_mul_Lseries_moebius (show 1 < (2 : ℂ).re by norm_num) using 1
      norm_num [LSeries]; congr! 1
      · rw [zeta_eq_tsum_one_div_nat_cpow] <;> norm_num [LSeries.term]
        exact tsum_congr fun n ↦ by aesop
      · norm_num [LSeries.term]; exact tsum_congr fun n ↦ by aesop
    exact eq_one_div_of_mul_eq_one_right h_zeta2
  convert congr_arg re h_sum using 1
  · rw_mod_cast [re_tsum]
    · rfl
    · contrapose! h_sum
      rw [tsum_eq_zero_of_not_summable h_sum]; norm_num [riemannZeta_two]
      exact (div_ne_zero (by norm_num)
        (pow_ne_zero 2 (ofReal_ne_zero.mpr Real.pi_ne_zero))).symm
  · norm_num [normSq, div_re]
    rw [inv_eq_one_div, div_eq_div_iff] <;> norm_num [riemannZeta_two]
    · norm_cast
    · norm_cast; positivity
    · norm_cast; positivity

/-- The integral `∫ u in 0..x, M(√(x/u)) = x · ∑' n, μ(n)/n²`. -/
theorem integral_M_sqrt_div (x : ℝ) (hx : 0 < x) :
    ∫ u in 0..x, (M (sqrt (x / u)) : ℝ) = x * ∑' n : ℕ, (moebius n : ℝ) / (n : ℝ) ^ 2 := by
  have h_abs : ∀ n : ℕ, |(moebius n : ℝ)| ≤ 1 := fun n ↦ by
    simp only [moebius, coe_mk]; split_ifs <;> norm_num
  have h_integral : ∫ u in (0 : ℝ)..x, (M (sqrt (x / u)) : ℝ) =
      ∑' n : ℕ, (moebius n : ℝ) * ∫ u in (0 : ℝ)..x, if n ≤ sqrt (x / u) then 1 else 0 := by
    have h_rewrite : ∫ u in (0 : ℝ)..x, (M (sqrt (x / u)) : ℝ) =
        ∫ u in (0 : ℝ)..x, ∑' n : ℕ, (moebius n : ℝ) * (if n ≤ sqrt (x / u) then 1 else 0) := by
      refine intervalIntegral.integral_congr fun u _ ↦ ?_
      rw [tsum_eq_sum (s := Ioc 0 ⌊sqrt (x / u)⌋₊)]
      · simp only [M, Int.cast_sum]
        refine sum_congr rfl fun i hi ↦ ?_
        rw [mul_ite, mul_one, mul_zero, if_pos]
        exact le_trans (Nat.cast_le.mpr (mem_Ioc.mp hi).2) (Nat.floor_le (sqrt_nonneg _))
      · intro n hn
        simp only [mul_ite, mul_one, mul_zero]
        by_cases hn0 : n = 0
        · simp [hn0, moebius]
        · rw [if_neg]; intro hle; apply hn; rw [mem_Ioc]
          exact ⟨Nat.pos_of_ne_zero hn0, Nat.le_floor hle⟩
    rw [h_rewrite, intervalIntegral.integral_of_le hx.le, integral_tsum]
    · exact tsum_congr fun n ↦ by rw [intervalIntegral.integral_of_le hx.le, integral_const_mul]
    · exact fun n ↦ (measurable_const.mul
        (Measurable.ite (measurableSet_le measurable_const
          (continuous_sqrt.measurable.comp (measurable_const.div measurable_id')))
            measurable_const measurable_const)).aestronglyMeasurable
    · refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun n ↦ ENNReal.ofReal
        (|moebius n| * (x / n ^ 2))) ?_) ?_)
      · intro n
        by_cases hn : n = 0
        · simp [hn]
        · have hdiv_le : x / (n : ℝ) ^ 2 ≤ x :=
            div_le_self hx.le (mod_cast Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn))
          calc ∫⁻ u in Set.Ioc 0 x,
              ‖(moebius n : ℝ) * if n ≤ sqrt (x / u) then 1 else 0‖ₑ
            _ ≤ ∫⁻ u in Set.Ioc 0 x, (Set.Ioc 0 (x / n ^ 2)).indicator
                  (fun _ ↦ ENNReal.ofReal |(moebius n : ℝ)|) u := by
                apply lintegral_mono_ae
                filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
                simp only [Set.mem_Ioc] at hu
                by_cases h1 : (n : ℝ) ≤ sqrt (x / u)
                · have h2 : u ≤ x / n ^ 2 := by
                    rw [le_sqrt (by positivity) (div_nonneg hx.le hu.1.le)] at h1
                    rwa [le_div_iff₀ hu.1, mul_comm, ← le_div_iff₀ (by positivity)] at h1
                  simp only [h1, ↓reduceIte, mul_one]
                  rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu.1, h2⟩)]
                  rw [enorm_eq_ofReal_abs]
                · simp only [h1, ↓reduceIte, mul_zero]
                  rw [enorm_zero]
                  exact zero_le _
            _ = ∫⁻ u in Set.Ioc 0 (x / n ^ 2), ENNReal.ofReal |(moebius n : ℝ)| := by
                rw [lintegral_indicator measurableSet_Ioc,
                  Measure.restrict_restrict measurableSet_Ioc]
                congr 1
                exact Measure.restrict_congr_set
                  (Set.inter_eq_left.mpr (Set.Ioc_subset_Ioc_right hdiv_le)).eventuallyEq
            _ = ENNReal.ofReal |(moebius n : ℝ)| * volume (Set.Ioc 0 (x / n ^ 2)) :=
                setLIntegral_const ..
            _ = ENNReal.ofReal |(moebius n : ℝ)| * ENNReal.ofReal (x / n ^ 2) := by
                rw [Real.volume_Ioc, sub_zero]
            _ = ENNReal.ofReal (|(moebius n : ℝ)| * (x / n ^ 2)) := by
                rw [← ENNReal.ofReal_mul (abs_nonneg _)]
            _ = ENNReal.ofReal (|moebius n| * (x / n ^ 2)) := by rw [Int.cast_abs]
      · rw [← ENNReal.ofReal_tsum_of_nonneg]
        · exact ENNReal.ofReal_lt_top
        · exact fun n ↦ mul_nonneg (by positivity : (0 : ℝ) ≤ |moebius n|)
            (div_nonneg hx.le (sq_nonneg _))
        · refine Summable.of_nonneg_of_le
            (fun n ↦ mul_nonneg (by positivity) (div_nonneg hx.le (sq_nonneg _)))
            (fun n ↦ mul_le_of_le_one_left (div_nonneg hx.le (sq_nonneg _)) ?_)
            (Summable.mul_left _ <| summable_nat_pow_inv.2 one_lt_two)
          rw [Int.cast_abs]; exact h_abs n
  have h_inner : ∀ n : ℕ, n ≠ 0 →
      ∫ u in (0 : ℝ)..x, (if n ≤ sqrt (x / u) then 1 else 0) = x / n ^ 2 := by
    intro n hn_ne
    have h_equiv : ∀ u ∈ Set.Ioc 0 x, (n : ℝ) ≤ sqrt (x / u) ↔ u ≤ x / n ^ 2 := fun u hu ↦ by
      rw [le_sqrt (by positivity) (div_nonneg hx.le hu.1.le), le_div_iff₀ hu.1, le_div_iff₀
        (by positivity : (0 : ℝ) < n ^ 2)]
      ring_nf
    have h_inner_eval : ∫ u in (0 : ℝ)..x, (if n ≤ sqrt (x / u) then 1 else 0) =
        ∫ u in (0 : ℝ)..x / n ^ 2, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_of_le (by positivity),
          ← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
      congr 1 with u
      simp only [Set.indicator]
      by_cases hu1 : 0 < u
      · by_cases hu2 : u ≤ x
        · simp only [Set.mem_Ioc, hu1, hu2, and_self, ↓reduceIte]
          by_cases hu3 : u ≤ x / n ^ 2
          · simp [hu3, (h_equiv u ⟨hu1, hu2⟩).mpr hu3]
          · simp [hu3, mt (h_equiv u ⟨hu1, hu2⟩).mp hu3]
        · have hle : x / n ^ 2 < u := lt_of_le_of_lt
            (div_le_self hx.le (mod_cast Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn_ne)))
            (lt_of_not_ge hu2)
          simp [not_and_of_not_right _ (not_le.mpr (lt_of_not_ge hu2)),
            not_and_of_not_right _ (not_le.mpr hle)]
      · simp [not_and_of_not_left _ (not_lt.mpr <| le_of_not_gt hu1)]
    simp only [h_inner_eval, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  rw [h_integral, ← tsum_mul_left]
  congr 1; ext n
  by_cases hn : n = 0
  · simp [hn]
  · rw [h_inner n hn]; ring

@[blueprint
  "mobius-lemma-1"
  (title := "Mobius Lemma 1")
  (statement := /--
    For any $x>0$,
    \begin{equation}\label{eq:antenor}
    R(x) = \sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right) -
      \int_0^x M\left(\sqrt{\frac{x}{u}}\right) du.
    \end{equation}
  -/)
  (proof := /--
    The equality is immediate from Theorem \ref{mobius-lemma-1-sub} and exchanging the order of
    $\sum$ and $\int$, as is justified by
    $\sum_n |\mu(n)|\int_0^{x/n^2} du \leq \sum_n x/n^2 < \infty$)
    $$\int_0^x M\left(\sqrt{\frac{x}{u}}\right) du = \int_0^x \sum_{n\leq \sqrt{\frac{x}{u}}}
    \mu(n) du = \sum_n \mu(n) \int_0^{\frac{x}{n^2}} du = x \sum_n \frac{\mu(n)}{n^2}
    = \frac{x}{\zeta(2)}.$$
  -/)
  (latexEnv := "lemma")
  (discussion := 527)]
theorem mobius_lemma_1 (x : ℝ) (hx : x > 0) :
    R x = ∑ k ∈ Ioc 0 ⌊x⌋₊, M (sqrt (x / k)) - ∫ u in 0..x, (M (sqrt (x / u)) : ℝ) := by
  unfold R
  congr 1
  · exact mod_cast mobius_lemma_1_sub x hx ▸ rfl
  · rw [integral_M_sqrt_div x hx, div_eq_mul_inv, mul_eq_mul_left_iff]
    exact Or.inl <| by simpa using sum_moebius_div_sq.symm

blueprint_comment /--
Since our sums start from $1$, the sum $\sum_{k\leq K}$ is empty for $K=0$.
-/

@[blueprint
  "mobius-lemma-2-sub-1"
  (title := "Mobius Lemma 2 - first step")
  (statement := /--
    For any $K \leq x$,
    $$
    \sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right) = \sum_{k\leq K} M\left(\sqrt{\frac{x}{k}}\right)
    + \sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}}
      M\left(\sqrt{\frac{x}{k}}\right) du.
    $$
  -/)
  (proof := /-- This is just splitting the sum at $K$. -/)
  (latexEnv := "sublemma")
  (discussion := 528)]
theorem mobius_lemma_2_sub_1 (x : ℝ) (hx : x > 0) (K : ℕ) (hK : (K : ℝ) ≤ x) :
    ∑ k ∈ Ioc 0 ⌊x⌋₊, M (sqrt (x / k)) = ∑ k ∈ range (K + 1), M (sqrt (x / k)) +
      ∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), ∫ _ in (k - 0.5)..(k + 0.5), (M (sqrt (x / k)) : ℝ) := by
  norm_num [sum_Ico_eq_sub]
  rw [sum_range_add_sum_Ico]
  · erw [← Icc_succ_left_eq_Ioc, sum_Ico_eq_sub _]
    · norm_num [Finset.sum_range_succ, M]
      rw [Nat.floor_eq_zero.mpr]
      · norm_num
      · rw [div_lt_one (by positivity), sqrt_lt_sqrt_iff] <;> linarith [Nat.lt_floor_add_one x]
    · simp
  · linarith [Nat.le_floor hK]

@[blueprint
  "mobius-lemma-2-sub-2"
  (title := "Mobius Lemma 2 - second step")
  (statement := /--
    For any $K \leq x$, for $f(u) = M(\sqrt{x/u})$,
    \[\sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}} f(u) du =
      \int_{K+\frac{1}{2}}^{\lfloor x\rfloor + \frac{3}{2}} f(u) du =
      \int_{K+\frac{1}{2}}^x f(u) du,\]
  -/)
  (proof := /--
    This is just splitting the integral at $K$, since $f(u) = M(\sqrt{x/u}) = 0$ for $x>u$.
  -/)
  (latexEnv := "sublemma")
  (discussion := 529)]
theorem mobius_lemma_2_sub_2 (x : ℝ) (K : ℕ) (hK : (K : ℝ) ≤ x) :
    let f : ℝ → ℝ := fun u ↦ (M (sqrt (x / u)) : ℝ)
    ∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), ∫ u in (k - 0.5)..(k + 0.5), f u =
      ∫ u in (K + 0.5)..(⌊x⌋₊ + 1.5), f u := by
  intro f
  have h_split : ∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), ∫ u in ((k : ℝ) - 0.5)..((k : ℝ) + 0.5), f u =
      ∫ u in (↑(K + 1) - 0.5)..(↑(⌊x⌋₊ + 2) - 0.5), f u := by
    rw [sum_Ico_eq_sum_range]
    convert intervalIntegral.sum_integral_adjacent_intervals _ using 3
    · push_cast; ring
    · rw [Nat.add_sub_of_le (by linarith [Nat.le_floor hK])]
    · intro k hk
      apply_rules [IntegrableOn.intervalIntegrable]
      refine Integrable.mono' (g := fun u ↦ 2 ^ (Nat.floor (Real.sqrt (x / u)))) ?_ ?_ ?_
      · refine Integrable.mono'
          (g := fun u ↦ 2 ^ (Nat.floor (Real.sqrt (x / ((K + 1 + k : ℝ) - 0.5))) + 1)) ?_ ?_ ?_
        · exact Continuous.integrableOn_Icc (by continuity)
        · exact aestronglyMeasurable <| by measurability
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
          norm_num at *
          refine pow_le_pow_right₀ (by norm_num) ?_
          refine Nat.le_of_lt_succ ?_
          rw [Nat.floor_lt', Real.sqrt_lt'] <;> norm_num <;> try positivity
          rw [div_lt_iff₀]
          · have := Nat.lt_floor_add_one (Real.sqrt (x / (K + 1 + k - 1 / 2)))
            rw [sqrt_lt' <| by positivity] at this
            rw [div_lt_iff₀] at this <;>
              nlinarith [show (⌊sqrt (x / (K + 1 + k - 1 / 2))⌋₊ : ℝ) ≥ 0 by positivity]
          · linarith
      · refine aestronglyMeasurable ?_
        have h_meas_floor : Measurable (fun u ↦ Nat.floor (sqrt (x / u))) :=
          nat_floor (.sqrt (measurable_const.div measurable_id'))
        have h_meas_sum : Measurable (fun n : ℕ ↦ ∑ k ∈ Ioc 0 n, (moebius k : ℤ)) := by fun_prop
        exact Measurable.comp (by fun_prop) (h_meas_sum.comp h_meas_floor)
      · refine Filter.Eventually.of_forall fun u ↦ ?_
        norm_num [f, M, moebius]
        refine le_trans (abs_sum_le_sum_abs ..) ?_
        refine le_trans (sum_le_sum (g := fun _ ↦ 1) fun i hi ↦ ?_) ?_
        · split_ifs <;> norm_num
        · induction ⌊sqrt (x / u)⌋₊ with
          | zero => simp
          | succ n ih =>
            norm_num [Nat.pow_succ', sum_Ioc_succ_top] at *
            rw [pow_succ']
            linarith [show (1 : ℝ) ≤ 2 ^ n by exact one_le_pow₀ (by norm_num)]
  convert h_split using 2 <;>
  · push_cast; ring

@[blueprint
  "mobius-lemma-2"
  (title := "Mobius Lemma 2")
  (statement := /--
    For any $x>0$ and any integer $K\geq 0$,
    \begin{equation}\label{eq:singdot}
    \begin{aligned}
    R(x) &= \sum_{k\leq K} M\left(\sqrt{\frac{x}{k}}\right)  -
    \int_0^{K+\frac{1}{2}} M\left(\sqrt{\frac{x}{u}}\right) du \\
    &-\sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}}
      \left(M\left(\sqrt{\frac{x}{u}}\right) -M\left(\sqrt{\frac{x}{k}}\right)\right) du
    \end{aligned}
    \end{equation}
  -/)
  (proof := /--
    We split into two cases. If $K>x$, the second line of \eqref{eq:singdot} is empty, and the
    first one equals \eqref{eq:antenor}, by $M(t)=0$ for $t<1$, so \eqref{eq:singdot} holds.

    Now suppose that $K \leq x$. Then we combine Sublemma \ref{mobius-lemma-2-sub-1} and Sublemma
    \ref{mobius-lemma-2-sub-2} with Lemma \ref{mobius-lemma-1} to give the claim.
  -/)
  (latexEnv := "lemma")
  (discussion := 530)]
theorem mobius_lemma_2 (x : ℝ) (hx : x > 0) (K : ℕ) : R x =
    ∑ k ∈ Finset.range (K + 1), M (Real.sqrt (x / k)) -
    (∫ u in 0..(K + 0.5), (M (Real.sqrt (x / u)) : ℝ)) -
    ∑ k ∈ Finset.Ico (K + 1) (⌊x⌋₊ + 2),
      ∫ u in (k - 0.5)..(k + 0.5), (M (Real.sqrt (x / u)) - M (Real.sqrt (x / k)) : ℝ) := by
    let f : ℝ → ℝ := fun u ↦ (M (sqrt (x / u)) : ℝ)
    have hM_zero {x y : ℝ} (hx : x > 0) (hxy : x < y):  M (Real.sqrt (x / y)) = 0 := by
      rw [M, Nat.floor_eq_zero.mpr (show sqrt (x / y) < 1 by exact (sqrt_lt_sqrt (div_pos hx (lt_trans hx hxy)).le ((div_lt_one (lt_trans hx hxy)).mpr hxy)).trans_eq sqrt_one), Finset.Ioc_self]
      simp
    have hM_norm_le {t : ℝ} (ht : 0 ≤ t) : ‖(M t : ℝ)‖ ≤ t := by
      have abs_M_le_floor (t : ℝ) : |M t| ≤ (⌊t⌋₊ : ℤ) := by
        unfold M
        refine le_trans (abs_sum_le_sum_abs (s := Finset.Ioc 0 ⌊t⌋₊) (f := fun n => moebius n)) ?_
        refine le_trans
          (Finset.sum_le_sum (s := Finset.Ioc 0 ⌊t⌋₊)
            (f := fun n => |(moebius n : ℤ)|)
            (g := fun _ => (1 : ℤ)) ?_) ?_
        · intro n hn
          have abs_moebius_le_one (n : ℕ) : |(moebius n : ℤ)| ≤ 1 := by
            by_cases hsq : Squarefree n <;> simp [ArithmeticFunction.moebius, hsq]
          exact abs_moebius_le_one n
        · simp
      calc
        ‖(M t : ℝ)‖ = (|M t| : ℝ) := by simp
        _ ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast (abs_M_le_floor t)
        _ ≤ t := by simpa using (Nat.floor_le ht)
    have hM_int {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable (fun u ↦ (M (Real.sqrt (x / u)) : ℝ)) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine Integrable.mono' (g := fun u : ℝ => Real.sqrt (x / u)) ?_ ?_ ?_
      · have hdom_on : IntegrableOn (fun u : ℝ => Real.sqrt (x / u)) (Set.uIoc a b) volume := by
          have hp : IntervalIntegrable (fun u : ℝ => u ^ (-(1/2 : ℝ))) volume a b := by
            simpa using (intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) (r := (-(1/2:ℝ))) (by linarith))
          have hdom_interval : IntervalIntegrable (fun u ↦ Real.sqrt (x / u)) MeasureTheory.volume a b := by
            have h_eq : ∀ u ∈ Set.Ioo a b, Real.sqrt (x / u) = Real.sqrt x * u ^ (-(1 / 2 : ℝ)) := by
              intro u hu; rw [Real.sqrt_div (le_of_lt hx), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_neg (by linarith [hu.1])]; ring;
            rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at *;
            exact MeasureTheory.Integrable.congr (hp.const_mul _) (Filter.eventuallyEq_of_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioo) fun u hu => by rw [h_eq u hu])
          exact intervalIntegrable_iff.mp hdom_interval
        rw [Set.uIoc_of_le hab] at hdom_on
        simpa [MeasureTheory.IntegrableOn] using hdom_on
      · refine aestronglyMeasurable ?_
        have h_meas_floor : Measurable (fun u ↦ Nat.floor (sqrt (x / u))) :=
          nat_floor (.sqrt (measurable_const.div measurable_id'))
        have h_meas_sum : Measurable (fun n : ℕ ↦ ∑ k ∈ Ioc 0 n, (moebius k : ℤ)) := by fun_prop
        exact Measurable.comp (by fun_prop) (h_meas_sum.comp h_meas_floor)
      · filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Set.Ioc a b))] with u hu
        simpa using (hM_norm_le (show sqrt (x / u) ≥ 0 by exact (sqrt_pos.mpr (show (x / u) > 0 by exact div_pos hx (lt_of_le_of_lt ha hu.1))).le))
    by_cases hK : (K > x)
    · have hfloor_K : ⌊x⌋₊ < K := by exact (Nat.floor_lt hx.le).mpr hK
      rw [Ico_eq_empty_iff.mpr (show ¬((⌊x⌋₊ + 2) > (K + 1)) by grind), Finset.sum_empty, sub_zero]
      rw [← Finset.sum_range_add_sum_Ico (m := (⌊x⌋₊ + 1)) (n := (K+1)) (fun (k : ℕ) => M (Real.sqrt (x / (k : ℝ)))) (by linarith)]
      have : ∀ k ∈ Ico (⌊x⌋₊ + 1) (K + 1), M (sqrt (x / k)) = 0 := by
        intro k hk
        exact hM_zero hx (show k > x by exact lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast (mem_Ico.mp hk).1))
      rw [sum_eq_zero this, add_zero, ← intervalIntegral.integral_add_adjacent_intervals (hM_int (by linarith) (by linarith)) (hM_int (by linarith) (by linarith))]
      have hint_zero : (∫ (u : ℝ) in x..↑K + 0.5, f u) = 0 := by
        have hf : (f =ᵐ[volume.restrict (Set.Ioc x (↑K + (1/2 : ℝ)))] 0) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          rw [Pi.zero_apply]
          unfold f
          exact_mod_cast hM_zero hx hu.1
        rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_eq_zero_of_ae]
        norm_num at *; exact hf
      rw [hint_zero, add_zero, mobius_lemma_1, ← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot (by linarith)]
      · simp [norm_le_zero_iff.mp (hM_norm_le (show 0 ≤ 0 by linarith)), show Finset.Ioc 0 ⌊x⌋₊ = Finset.Ico 1 (⌊x⌋₊ + 1) by ext; simp; omega]
      · exact hx
    · have h_int : (∫ (u : ℝ) in 0..x, ((M √(x / u)) : ℝ)) = (∫ (u : ℝ) in 0..↑⌊x⌋₊ + 3 / 2, ((M √(x / u)) : ℝ)) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals (hM_int (by linarith) (show 0 ≤ x by linarith)) (hM_int (by linarith) (show x ≤ (↑⌊x⌋₊ + (3 / 2)) by  have := Nat.lt_floor_add_one x; linarith))]
        have : (∫ (u : ℝ) in x..(↑⌊x⌋₊ + 3 / 2), ((M √(x / u)): ℝ)) = 0 := by
          refine intervalIntegral.integral_zero_ae ?_
          refine ae_of_all _ ?_
          intro a ha
          simpa using (hM_zero hx (show a > x by exact (Set.uIoc_of_le (show x ≤ (⌊x⌋₊ + 3 / 2) by have := Nat.lt_floor_add_one x; linarith) ▸ ha).1))
        simp [this]
      have h_split : (∫ (u : ℝ) in 0..(⌊x⌋₊ + 3 / 2), ((M √(x / u)) : ℝ)) =
        (∫ (u : ℝ) in 0..(K + 1/2), ((M √(x / u)) : ℝ)) + ∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), ∫ (u : ℝ) in ↑k - 0.5..↑k + 0.5, ((M √(x / u)) : ℝ) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals (hM_int (by linarith) (show 0 ≤ ((K + (1/2)) : ℝ) by linarith)) (hM_int (by linarith) (by have :=  Nat.lt_floor_add_one x; linarith [hK]))]
        rw [mobius_lemma_2_sub_2 x K (by linarith)]
        norm_num
      have hsum_split: ∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), ∫ (u : ℝ) in (k : ℝ) - 1 / 2..(k : ℝ) + 1 / 2, ((M (Real.sqrt (x / u)) : ℝ) - (M (Real.sqrt x / Real.sqrt k) : ℝ)) =
          - (∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), (M (Real.sqrt x / Real.sqrt k) : ℝ) -
            ∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), ∫ (u : ℝ) in (k : ℝ) - 1 / 2..(k : ℝ) + 1 / 2, (M (Real.sqrt (x / u)) : ℝ)) := by
              rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun i hi => intervalIntegral.integral_sub ?_ ?_] <;> norm_num
              rw [intervalIntegrable_iff_integrableOn_Ioo_of_le]
              · have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
                  have : (1 : ℕ) ≤ i := le_trans (by exact Nat.succ_le_succ (Nat.zero_le K)) (mem_Ico.mp hi).1
                  exact_mod_cast this
                exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).1 (hM_int (show (0 : ℝ) ≤ (i - (1/2)) by linarith) (by linarith))
              · linarith
      rw [mobius_lemma_1 x hx, mobius_lemma_2_sub_1 x hx K (by linarith), h_int, h_split]
      norm_num
      rw [hsum_split]
      abel

end MobiusLemma
