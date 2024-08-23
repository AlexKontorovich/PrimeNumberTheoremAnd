import PrimeNumberTheoremAnd.Wiener
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory

/-%%
\begin{lemma}\label{range-eq-range}\lean{finsum_range_eq_sum_range, finsum_range_eq_sum_range'}\leanok For any arithmetic function $f$ and real number $x$, one has
$$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
and
$$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
\end{lemma}
%%-/
lemma finsum_range_eq_sum_range {R: Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n in range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R: Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n ≤ x), f n = ∑ n in Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero

/-%%
\begin{proof}\leanok Straightforward. \end{proof}
%%-/

lemma log2_pos : 0 < log 2 := by
  rw [Real.log_pos_iff zero_lt_two]
  exact one_lt_two

/-- Auxiliary lemma I for `chebyshev_asymptotic`: Expressing the sum over Λ up to N as a double sum over primes and exponents. -/
lemma sum_von_mangoldt_as_double_sum (x : ℝ) (hx: 0 ≤ x) :
  ∑ n in Iic ⌊x⌋₊, Λ n =
    ∑ k in Icc 1 ⌊ log x / log 2⌋₊,
      ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p := calc
    _ = ∑ n in Iic ⌊x⌋₊, ∑ k in Icc 1 ⌊ log x / log 2⌋₊, ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), if n = p^k then log p else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Iic, Nat.le_floor_iff hx] at hn
      rw [ArithmeticFunction.vonMangoldt_apply]
      by_cases h : IsPrimePow n
      . simp [h]
        rw [isPrimePow_def] at h
        obtain ⟨ p, k, ⟨ h1, h2, h3 ⟩ ⟩ := h
        rw [<- h3]
        replace h1 := h1.nat_prime
        calc
          _ = log p := by
            congr
            apply Nat.Prime.pow_minFac h1 (not_eq_zero_of_lt h2)
          _ = ∑ k' in Icc 1 ⌊ log x / log 2⌋₊, if k' = k then log p else 0 := by
            simp
            have h : k ≤ ⌊x.log / log 2⌋₊ := by
              have h5 : 2^k ≤ n := by
                rw [<-h3]
                apply Nat.pow_le_pow_of_le_left (Prime.two_le h1)
              have h6 : 1 ≤ x := by
                apply LE.le.trans _ hn
                simp only [one_le_cast]
                exact LE.le.trans Nat.one_le_two_pow h5
              have h7 : 0 < x := by linarith
              rw [Nat.le_floor_iff, le_div_iff log2_pos, le_log_iff_exp_le h7, mul_comm, exp_mul, exp_log zero_lt_two]
              . apply LE.le.trans _ hn
                norm_cast
              apply div_nonneg (Real.log_nonneg h6) (le_of_lt log2_pos)
            have : 1 ≤ k ∧ k ≤ ⌊x.log / log 2⌋₊ := ⟨ h2, h ⟩
            simp [this]
          _ = ∑ k' in Icc 1 ⌊ log x / log 2⌋₊,
      ∑ p' in filter Nat.Prime (Iic ⌊ x^((k':ℝ)⁻¹) ⌋₊), if k'=k ∧ p'=p then log p else 0 := by
            apply Finset.sum_congr rfl
            intro k' _
            by_cases h : k' = k
            . have : p ≤ ⌊x ^ (k:ℝ)⁻¹⌋₊ := by
                rw [Nat.le_floor_iff]
                . rw [le_rpow_inv_iff_of_pos (cast_nonneg p) hx (cast_pos.mpr h2)]
                  apply LE.le.trans _ hn
                  rw [<-h3]
                  norm_num
                positivity
              simp [h, h1, this]
            simp [h]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k' _
            apply Finset.sum_congr rfl
            intro p' hp'
            by_cases h : p ^ k = p' ^ k'
            . simp at hp'
              have : (k' = k ∧ p' = p) := by
                have := eq_of_prime_pow_eq h1.prime hp'.2.prime h2 h
                rw [<-this, pow_right_inj] at h
                . exact ⟨ h.symm, this.symm ⟩
                . exact Prime.pos h1
                exact Nat.Prime.ne_one h1
              simp [h, this]
            have :¬ (k' = k ∧ p' = p) := by
              contrapose! h
              rw [h.1, h.2]
            simp [h, this]
      simp [h]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      apply Finset.sum_eq_zero
      intro p hp
      simp at hp ⊢
      intro hn'
      contrapose! h; clear h
      rw [isPrimePow_def]
      use p, k
      refine ⟨ Nat.Prime.prime hp.2, ⟨ ?_, hn'.symm ⟩ ⟩
      simp at hk
      exact hk.1
    _ = ∑ k in Icc 1 ⌊ log x / log 2⌋₊, ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), ∑ n in Iic ⌊x⌋₊, if n = p^k then log p else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro p hp
      simp at hk hp ⊢
      intro hpk
      rw [Nat.floor_lt hx] at hpk
      rw [Nat.le_floor_iff (rpow_nonneg hx (k:ℝ)⁻¹), Real.le_rpow_inv_iff_of_pos (cast_nonneg p) hx (cast_pos.mpr hk.1)] at hp
      simp at hpk hp
      linarith [hp.1]

/-- Auxiliary lemma II for `chebyshev_asymptotic`: Controlling the error. -/
lemma sum_von_mangoldt_sub_sum_primes_le (x : ℝ) (hx: 2 ≤ x) :
  |∑ n in Iic ⌊x⌋₊, Λ n - ∑ p in filter Nat.Prime (Iic ⌊ x⌋₊), log p| ≤ (x.log / log 2) * ((x ^ (2:ℝ)⁻¹ + 1) * x.log) := by
  have hx_one : 1 ≤ x := one_le_two.trans hx
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_two hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hlogx_nonneg : 0 ≤ log x := log_nonneg hx_one

  calc
    _ = |∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p + ∑ p in filter Nat.Prime (Iic ⌊ x^((1:ℝ)⁻¹) ⌋₊), log p - ∑ p in filter Nat.Prime (Iic ⌊ x⌋₊), log p| := by
      rw [sum_von_mangoldt_as_double_sum x hx_nonneg]
      congr
      have h : 1 ∈ Icc 1 ⌊ log x / log 2⌋₊ := by
        simp only [mem_Icc, le_refl, one_le_floor_iff, true_and]
        rwa [le_div_iff log2_pos, one_mul, le_log_iff_exp_le hx_pos, exp_log zero_lt_two]
      set s := Icc 2 ⌊ log x / log 2⌋₊
      convert (Finset.sum_erase_add _ _ h).symm
      . ext n
        simp only [mem_Icc, Icc_erase_left, mem_Ioc, and_congr_left_iff, s]
        intro _
        rfl
      exact Eq.symm cast_one
    _ = |∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p| := by
        congr
        convert add_sub_cancel_right _ (∑ p in filter Nat.Prime (Iic ⌊ x⌋₊), log p)
        simp only [inv_one, rpow_one]
    _ ≤ ∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      |∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), |log p| := by
        apply sum_le_sum
        intro k _
        exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      ∑ _p in filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log x := by
        apply sum_le_sum
        intro k hk
        apply sum_le_sum
        intro p hp
        simp at hk hp
        have hp' : 1 ≤ p := Nat.Prime.one_le hp.2
        have hp'': p ≠ 0 := not_eq_zero_of_lt hp'
        replace hp := (Nat.le_floor_iff' hp'').mp hp.1
        rw [abs_of_nonneg, log_le_log_iff _ hx_pos]
        . apply hp.trans
          calc
            _ ≤ x^(1:ℝ) := by
              apply rpow_le_rpow_of_exponent_le hx_one
              apply inv_le_one
              simp only [one_le_cast]
              exact one_le_two.trans hk.1
            _ = _ := by
              simp only [rpow_one]
        . simpa only [cast_pos]
        apply log_nonneg
        simp only [one_le_cast, hp']
    _ ≤ ∑ k in Icc 2 ⌊ log x / log 2⌋₊,
      (x^((2:ℝ)⁻¹)+1) * log x := by
        apply sum_le_sum
        intro k hk
        simp only [sum_const, nsmul_eq_mul]
        gcongr
        rw [<- Nat.le_floor_iff]
        . apply (Finset.card_filter_le _ _).trans
          rw [card_Iic, Nat.floor_add_one]
          . apply Nat.add_le_add _ NeZero.one_le
            apply floor_le_floor
            apply rpow_le_rpow_of_exponent_le hx_one
            simp at hk
            rw [inv_le_inv _ zero_lt_two]
            . exact ofNat_le_cast.mpr hk.1
            simp only [cast_pos]
            exact lt_of_lt_of_le zero_lt_two hk.1
          exact rpow_nonneg hx_nonneg 2⁻¹
        exact add_nonneg (rpow_nonneg hx_nonneg (2:ℝ)⁻¹) zero_le_one
    _ ≤ _ := by
      simp only [sum_const, card_Icc, reduceSubDiff, nsmul_eq_mul]
      gcongr
      apply LE.le.trans _ (Nat.floor_le _)
      simp only [cast_le, tsub_le_iff_right, le_add_iff_nonneg_right, _root_.zero_le]
      exact div_nonneg hlogx_nonneg (le_of_lt log2_pos)




theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β] {u : α → β} {v : α → β} {w : α → β} {l : Filter α} (huv : Asymptotics.IsEquivalent l u v) (hwu : (w-u) =o[l] v) :
Asymptotics.IsEquivalent l w v := by
  rw [<- add_sub_cancel u w]
  exact add_isLittleO huv hwu

-- Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1)

/-%%
\begin{theorem}\label{chebyshev-asymptotic}\lean{chebyshev_asymptotic}\leanok  One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$
\end{theorem}
%%-/
theorem chebyshev_asymptotic :
    (fun x ↦ ∑ p in (filter Nat.Prime (range ⌈x⌉₊)), log p) ~[atTop] (fun x ↦ x) := by
  have PNT : (fun x ↦ ∑ n in (range ⌈x⌉₊), Λ n) ~[atTop] (fun x ↦ x) := by
    sorry
  apply PNT.add_isLittleO'
  
  sorry

theorem chebyshev_asymptotic_finsum :
    (fun x ↦ ∑ᶠ (p:ℕ) (_: p ≤ x) (_: Nat.Prime p), log p) ~[atTop] (fun x ↦ x) := by
  sorry

-- one could also consider adding a version with p < x instead of p \leq x

/-%%
\begin{proof}
\uses{WeakPNT, range-eq-range}
From the prime number theorem we already have
$$ \sum_{n \leq x} \Lambda(n) = x + o(x)$$
so it suffices to show that
$$ \sum_{j \geq 2} \sum_{p^j \leq x} \log p = o(x).$$
Only the terms with $j \leq \log x / \log 2$ contribute, and each $j$ contributes at most $\sqrt{x} \log x$ to the sum, so the left-hand side is $O( \sqrt{x} \log^2 x ) = o(x)$ as required.
\end{proof}
%%-/

/-%%
\begin{corollary}[Bounds on primorial]  \label{primorial-bounds}\lean{primorial_bounds}\leanok
We have
  $$ \prod_{p \leq x} p = \exp( x + o(x) )$$
\end{corollary}
%%-/
theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
    ∀ x : ℝ, ∏ p in (filter Nat.Prime (range ⌊x⌋₊)), p = exp ( x + E x ) := by
  sorry

theorem primorial_bounds_finprod :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
    ∀ x : ℝ, ∏ᶠ (p:ℕ) (_:p ≤ x) (_:Nat.Prime p), p = exp ( x + E x ) := by
  sorry

/-%%
\begin{proof}
\uses{chebyshev-asymptotic}
  Exponentiate Theorem \ref{chebyshev-asymptotic}.
\end{proof}
%%-/

/-%%
Let $\pi(x)$ denote the number of primes up to $x$.

\begin{theorem}\label{pi-asymp}\lean{pi_asymp}\leanok  One has
  $$ \pi(x) = (1+o(1)) \int_2^x \frac{dt}{\log t}$$
as $x \to \infty$.
\end{theorem}
%%-/
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in Set.Icc 2 x, 1 / (log t) ∂ volume := by
  sorry

/-%%
\begin{proof}
\uses{chebyshev-asymptotic}
We have the identity
$$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
+ \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
as can be proven by interchanging the sum and integral and using the fundamental theorem of calculus.  For any $\eps$, we know from Theorem \ref{chebyshev-asymptotic} that there is $x_\eps$ such that
$\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
$$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
+ \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate this after an integration by parts as
$$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
$$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
for $x$ large enough, giving the claim.
\end{proof}
%%-/

/-%%
\begin{corollary}\label{pi-alt}\lean{pi_alt}\leanok  One has
$$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
as $x \to \infty$.
\end{corollary}
%%-/
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  sorry

/-%%
\begin{proof}
\uses{pi-asymp}
An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} + \int_2^x \frac{dt}{\log^2 t}.$$
We have the crude bounds
$$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
and
$$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
and combining all this we obtain
$$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
$$ = (1+o(1)) \frac{x}{\log x}$$
and the claim then follows from Theorem \ref{pi-asymp}.
\end{proof}
%%-/

/-%%
Let $p_n$ denote the $n^{th}$ prime.

\begin{proposition}\label{pn-asymptotic}\lean{pn_asymptotic}\leanok
 One has
  $$ p_n = (1+o(1)) n \log n$$
as $n \to \infty$.
\end{proposition}
%%-/
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime n = (1 + c n) * n * log n := by
  sorry

/-%%
\begin{proof}
\uses{pi-alt}
Use Corollary \ref{pi-alt} to show that for any $\eps>0$, and for $x$ sufficiently large, the number of primes up to $(1-\eps) n \log n$ is less than $n$, and the number of primes up to $(1+\eps) n \log n$ is greater than $n$.
\end{proof}
%%-/

/-%%
\begin{corollary} \label{pn-pnPlus1}\lean{pn_pn_plus_one}\leanok
We have $p_{n+1} - p_n = o(p_n)$
  as $n \to \infty$.
\end{corollary}
%%-/

theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n = (c n) * Nat.nth Nat.Prime n := by
  sorry

/-%%
\begin{proof}
\uses{pn-asymptotic}
  Easy consequence of preceding proposition.
\end{proof}
%%-/

/-%%
\begin{corollary}  \label{prime-between}\lean{prime_between}\leanok
For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for all sufficiently large $x$.
\end{corollary}
%%-/

theorem prime_between {ε:ℝ} (hε: 0 < ε): ∀ᶠ x:ℝ in atTop, ∃ p:ℕ, Nat.Prime p ∧
    x < p ∧ p < (1+ε)* x := by
  sorry


/-%%
\begin{proof}
\uses{pi-alt}
Use Corollary \ref{pi-alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity as $x \to \infty$.
\end{proof}
%%-/

/-%%
\begin{proposition}\label{mun}\lean{sum_mobius_div_self_le}\leanok
We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \leq 1$.
\end{proposition}
%%-/
theorem sum_mobius_div_self_le (N : ℕ) : |∑ n in range N, μ n / (n : ℚ)| ≤ 1 := by
  cases' N with N
  /- simple cases -/
  simp only [range_zero, sum_empty, abs_zero, zero_le_one]
  by_cases hN : 1 ≤ N; swap
  · simp only [not_le, lt_one_iff] at hN
    subst hN
    simp
  /- annoying case -/
  have h_sum : 1 = ∑ d in range (N + 1), (μ d : ℚ) * (N / d : ℕ) := by calc
    (1 : ℚ) = ∑ m in Icc 1 N, ∑ d in m.divisors, μ d := by
      have {N : ℕ} : (1 : ArithmeticFunction _) N = ∑ d in N.divisors, μ d := by
        rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta]
      rw [Icc_eq_cons_Ioc hN, Finset.sum_cons, divisors_one, sum_singleton, moebius_apply_one]
      have {x : ℕ} (hx : x ∈ Ioc 1 N) : ∑ d in divisors x, μ d = 0 := by
        rw [mem_Ioc] at hx
        simp only [← this, one_apply, hx.left.ne.symm, if_false]
      rw [sum_congr rfl (fun _ ↦ this), sum_const, smul_zero, add_zero, Int.cast_one]
    _ = ∑ d in range (N + 1), μ d * (N / d) := by
      simp_rw [← coe_mul_zeta_apply, ArithmeticFunction.sum_Icc_mul_zeta, nsmul_eq_mul, mul_comm]
      rw [range_eq_Ico, ← Ico_insert_succ_left (succ_pos _), sum_insert, ArithmeticFunction.map_zero,
        mul_zero, zero_add]
      · congr
      · simp
    _ = ∑ d in range (N + 1), (μ d : ℚ) * (N / d : ℕ) := by
      save
      norm_num [Int.cast_sum]
      rfl

  /- rewrite Nat division (N / d) as ⌊N / d⌋ -/
  rw [sum_congr rfl (g := fun d ↦ (μ d : ℚ) * ⌊(N : ℚ) / (d : ℚ)⌋)] at h_sum
  swap
  intros
  rw [show (N : ℚ) = ((N : ℤ) : ℚ) by norm_cast, Rat.floor_int_div_nat_eq_div]
  congr

  /- Next, we establish bounds for the error term -/
  have hf' (d : ℕ) : |Int.fract ((N : ℚ) / d)| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact Int.fract_lt_one _
  have h_bound : |∑ d in range (N + 1), μ d * Int.fract ((N : ℚ) / d)| ≤ N - 1 := by
    /- range (N + 1) → Icc 1 N + part that evals to 0 -/
    rw [range_eq_Ico, ← Ico_insert_succ_left, sum_insert, ArithmeticFunction.map_zero,
      Int.cast_zero, zero_mul, zero_add, Ico_succ_right]
    all_goals simp
    /- Ico 1 (N + 1) → Ico 1 N ∪ {N + 1} that evals to 0 -/
    rw [← Ico_insert_right, sum_insert, div_self, Int.fract_one, mul_zero]
    all_goals simp [hN, Nat.pos_iff_ne_zero.mp hN]
    /- bound sum -/
    have (d : ℕ) : |μ d * Int.fract ((N : ℚ) / d)| ≤ 1 := by
      rw [abs_mul, ← one_mul 1]
      apply mul_le_mul ?_ (hf' _).le (abs_nonneg _) zero_le_one
      norm_cast
      simp [moebius]
      split_ifs <;> simp only [abs_zero, zero_le_one, abs_pow, abs_neg, abs_one, one_pow, le_refl]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum fun d _ ↦ this d).trans
    all_goals simp [sum_ite, cast_sub hN]

  rw [sum_congr rfl (g := fun d : ℕ ↦ μ d * ((N : ℚ) / d - Int.fract ((N : ℚ) / d)))
    fun d _ ↦ by simp only [Int.fract, sub_sub_self]] at h_sum
  simp_rw (config := {singlePass := true}) [mul_sub] at h_sum
  simp_rw [← mul_comm_div, sum_sub_distrib, ← sum_mul] at h_sum
  rw [eq_sub_iff_add_eq, eq_comm, ← eq_div_iff (by norm_num [Nat.pos_iff_ne_zero.mp hN])] at h_sum

  rw [h_sum, abs_le]
  rw [abs_le, neg_sub] at h_bound
  constructor
  <;> simp only [le_div_iff, div_le_iff, cast_pos.mpr hN]
  <;> linarith [h_bound.left]

/-%%
\begin{proof}\leanok
From M\"obius inversion $1_{n=1} = \sum_{d|n} \mu(d)$ and summing we have
  $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
  for any $x \geq 1$. Since $\lfloor \frac{x}{d} \rfloor = \frac{x}{d} - \epsilon_d$ with
  $0 \leq \epsilon_d < 1$ and $\epsilon_x = 0$, we conclude that
  $$ 1 ≥ x \sum_{d \leq x} \frac{\mu(d)}{d} - (x - 1)$$
  and the claim follows.
\end{proof}
%%-/

/-%%
\begin{proposition}[M\"obius form of prime number theorem]\label{mu-pnt}\lean{mu_pnt}\leanok  We have $\sum_{n \leq x} \mu(n) = o(x)$.
\end{proposition}
%%-/

theorem mu_pnt : (fun x:ℝ ↦ ∑ n in range ⌊ x ⌋₊, μ n) =o[atTop] (fun x ↦ x) := by sorry

/-%%
\begin{proof}
\uses{mun, WeakPNT}
From the Dirichlet convolution identity
  $$ \mu(n) \log n = - \sum_{d|n} \mu(d) \Lambda(n/d)$$
and summing we obtain
$$ \sum_{n \leq x} \mu(n) \log n = - \sum_{d \leq x} \mu(d) \sum_{m \leq x/d} \Lambda(m).$$
For any $\eps>0$, we have from the prime number theorem that
$$ \sum_{m \leq x/d} \Lambda(m) = x/d + O(\eps x/d) + O_\eps(1)$$
(divide into cases depending on whether $x/d$ is large or small compared to $\eps$).
We conclude that
$$ \sum_{n \leq x} \mu(n) \log n = - x \sum_{d \leq x} \frac{\mu(d)}{d} + O(\eps x \log x) + O_\eps(x).$$
Applying \eqref{mun} we conclude that
$$ \sum_{n \leq x} \mu(n) \log n = O(\eps x \log x) + O_\eps(x).$$
and hence
$$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x) + O( \sum_{n \leq x} (\log x - \log n) ).$$
From Stirling's formula one has
$$  \sum_{n \leq x} (\log x - \log n) = O(x)$$
thus
$$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x)$$
and thus
$$ \sum_{n \leq x} \mu(n) = O(\eps x) + O_\eps(\frac{x}{\log x}).$$
Sending $\eps \to 0$ we obtain the claim.
\end{proof}
%%-/


/-%%
\begin{proposition}\label{lambda-pnt}\lean{lambda_pnt}\leanok
We have $\sum_{n \leq x} \lambda(n) = o(x)$.
\end{proposition}
%%-/

theorem lambda_pnt : (fun x:ℝ ↦ ∑ n in range ⌊ x ⌋₊, (-1)^(Ω n)) =o[atTop] (fun x ↦ x) := by
  sorry


/-%%
\begin{proof}
\uses{mu-pnt}
From the identity
  $$ \lambda(n) = \sum_{d^2|n} \mu(n/d^2)$$
and summing, we have
$$ \sum_{n \leq x} \lambda(n) = \sum_{d \leq \sqrt{x}} \sum_{n \leq x/d^2} \mu(n).$$
For any $\eps>0$, we have from Proposition \ref{mu-pnt} that
$$ \sum_{n \leq x/d^2} \mu(n) = O(\eps x/d^2) + O_\eps(1)$$
and hence on summing in $d$
$$ \sum_{n \leq x} \lambda(n) = O(\eps x) + O_\eps(x^{1/2}).$$
Sending $\eps \to 0$ we obtain the claim.
\end{proof}

%%-/

/-%%
\begin{proposition}[Alternate M\"obius form of prime number theorem]\label{mu-pnt-alt}\lean{mu_pnt_alt}\leanok  We have $\sum_{n \leq x} \mu(n)/n = o(1)$.
\end{proposition}
%%-/

theorem mu_pnt_alt : (fun x:ℝ ↦ ∑ n in range ⌊ x ⌋₊, (μ n: ℝ) / n) =o[atTop] (fun x ↦ (1:ℝ)) := by sorry

/-%%
\begin{proof}
\uses{mu-pnt}
As in the proof of Theorem \ref{mun}, we have
  $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
  $$ = x \sum_{d \leq x} \frac{\mu(d)}{d} - \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \}$$
so it will suffice to show that
$$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = o(x).$$
Let $N$  be a natural number.  It suffices to show that
$$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = O(x/N).$$
if $x$ is large enough depending on $N$.
We can split the left-hand side as the sum of
$$ \sum_{d \leq x/N} \mu(d) \{ \frac{x}{d} \} $$
and
$$ \sum_{j=1}^{N-1} \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j).$$
The first term is clearly $O(x/N)$.  For the second term, we can use Theorem \ref{mu-pnt} and summation by parts (using the fact that $x/d-j$ is monotone and bounded) to find that
$$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = o(x)$$
for any given $j$, so in particular
$$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = O(x/N^2)$$
for all $j=1,\dots,N-1$ if $x$ is large enough depending on $N$.  Summing all the bounds, we obtain the claim.
\end{proof}
%%-/
