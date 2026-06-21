import PrimeNumberTheoremAnd.IEANTN.ZetaSummary
import PrimeNumberTheoremAnd.IEANTN.PrimaryDefinitions
import PrimeNumberTheoremAnd.IEANTN.FioriKadiriSwidinsky.FioriKadiriSwidinsky
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_app_tables
import PrimeNumberTheoremAnd.IEANTN.LogTables
import PrimeNumberTheoremAnd.IEANTN.Buthe

blueprint_comment /--
\section{Appendix A of BKLNW}\label{bklnw-app-sec}
In this file we record the results from Appendix A of \cite{BKLNW}.
In this appendix, the authors derive explicit estimates on the error term in the prime number
theorem for the Chebyshev function $\psi$
assuming various inputs on the zeros of the Riemann zeta function,
including a zero-density estimate, a classical zero-free region,
and numerical verification of RH up to some height.
-/

namespace BKLNW_app

open Real Chebyshev

structure Inputs where
  H : ℝ
  hH : riemannZeta.RH_up_to H
  R : ℝ
  hR : riemannZeta.classicalZeroFree R
  ZDB : zero_density_bound

noncomputable def Inputs.default : Inputs where
  H := 2445999556030
  hH := GW_theorem
  R := 5.5666305  -- a slightly more conservative value of 5.573412 was used in the paper
  hR := MT_theorem_1
  ZDB := FKS.corollary_2_9_merged -- stronger than the Kadiri-Lumley-Ng input used here

@[blueprint
  "bklnw-eq_A_7"
  (title := "Equation (A.7)")
  (statement := /-- Let $x \geq e^{1000}$ and $T$ satisfies
  $50 < T \leq x$. Then
  $$ \frac{\psi(x) - x}{x} = \sum_{|\gamma| < T}
  \frac{x^{\rho - 1}}{\rho}
  + \mathcal{O}^*\left(\frac{2(\log x)^2}{T}\right) $$
  where $A = \mathcal{O}^*(B)$ means $|A| \leq B$. -/)
  (proof := /-- See \cite[Theorem 1.3]{Dudek}. -/)
  (latexEnv := "sublemma")]
theorem bklnw_eq_A_7 (x T : ℝ) (hx : x ≥ exp 1000)
    (hT1 : 50 < T) (hT2 : T ≤ x) :
    ∃ E, (ψ x - x) / x =
      riemannZeta.zeroes_sum (Set.Icc 0 1)
        (Set.Ioo (-T) T) (fun ρ ↦ x ^ (ρ - 1) / ρ) + E ∧
      ‖E‖ ≤ 2 * (log x) ^ 2 / T := by
  sorry

@[blueprint
  "bklnw-eq_A_8"
  (title := "Equation (A.8)")
  (statement := /-- We denote
  $$ s_0(b, T) = \frac{2b^2}{T}. $$ -/)]
noncomputable def bklnw_eq_A_8 (b T : ℝ) : ℝ :=
  2 * b ^ 2 / T

@[blueprint
  "bklnw-sigma_1_def"
  (title := "Definition of Sigma 1")
  (statement := /-- We denote
  $$ \Sigma_1 := \sum_{|\gamma| \leq T;
  \beta < 1 - \delta} \frac{x^{\rho - 1}}{\rho} $$
  -/)]
noncomputable def Sigma₁ (x T δ : ℝ) : ℂ :=
  riemannZeta.zeroes_sum (Set.Ico 0 (1 - δ))
    (Set.Ioo (-T) T) (fun ρ ↦ x ^ (ρ - 1) / ρ)

@[blueprint
  "bklnw-sigma_2_def"
  (title := "Definition of Sigma 2")
  (statement := /-- We denote
  $$ \Sigma_2 := \sum_{|\gamma| \leq T;
  \beta \geq 1 - \delta} \frac{x^{\rho - 1}}{\rho} $$
  -/)]
noncomputable def Sigma₂ (x T δ : ℝ) : ℂ :=
  riemannZeta.zeroes_sum (Set.Icc (1 - δ) 1)
    (Set.Ioo (-T) T) (fun ρ ↦ x ^ (ρ - 1) / ρ)

@[blueprint
  "bklnw-eq_A_9"
  (title := "Equation (A.9)")
  (statement := /-- We have
  $$ \sum_{|\gamma| < T} \frac{x^{\rho-1}}{\rho}
  = \Sigma_1 + \Sigma_2 $$ -/)
  (proof := /-- Follows directly from the definitions
  of Σ₁ and Σ₂. -/)
  (latexEnv := "sublemma")
  (discussion := 750)]
theorem bklnw_eq_A_9 (x T δ : ℝ) (hδ1 : 0 ≤ δ) (hδ2 : δ ≤ 1) :
    riemannZeta.zeroes_sum (Set.Icc 0 1)
      (Set.Ioo (-T) T) (fun ρ ↦ x ^ (ρ - 1) / ρ) =
    Sigma₁ x T δ + Sigma₂ x T δ := by
  set I₁ : Set ℝ := Set.Ico 0 (1 - δ)
  set I₂ : Set ℝ := Set.Icc (1 - δ) 1
  set J  : Set ℝ := Set.Ioo (-T) T
  set g  : ℂ → ℂ := fun ρ ↦ (x ^ (ρ - 1) / ρ) * (riemannZeta.order ρ)
  change ∑' ρ : riemannZeta.zeroes_rect (Set.Icc 0 1) J, g ρ = _
  have hI : Set.Icc 0 1 = I₁ ∪ I₂ := (Set.Ico_union_Icc_eq_Icc
    (sub_nonneg_of_le hδ2) (sub_le_self 1 hδ1)).symm
  have hdisj : Disjoint (riemannZeta.zeroes_rect I₁ J) (riemannZeta.zeroes_rect I₂ J) :=
    riemannZeta.zeroes_rect_disjoint₁ I₁ I₂ J
      (Set.disjoint_left.2 fun _ hx1 hx2 ↦ not_le.2 hx1.2 hx2.1)
  have hfin : (riemannZeta.zeroes_rect (Set.Icc 0 1) J).Finite := by
    rw [riemannZeta.zeroes_rect_eq]
    refine (riemannZeta.zeroes_on_Compact_finite' ?_).subset
      (Set.inter_subset_inter (Set.inter_subset_inter_right _
        (Set.preimage_mono Set.Ioo_subset_Icc_self)) le_rfl)
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  rw [hI, ← riemannZeta.zeroes_rect_union] at hfin ⊢
  refine Summable.tsum_union_disjoint hdisj ?_ ?_
  · exact (hfin.subset Set.subset_union_left).summable g
  · exact (hfin.subset Set.subset_union_right).summable g

@[blueprint
  "bklnw-eq_A_10"
  (title := "Equation (A.10)")
  (statement := /-- We have
  $$ |\Sigma_1| \leq x^{-\delta}
  \left(\frac{1}{2\pi}(\log(T/2\pi))^2
  + 1.8642\right). $$ -/)
  (proof := /-- See \cite[Lemma 2.10]{STD2015}. -/)
  (latexEnv := "sublemma")]
theorem bklnw_eq_A_10 (x T δ : ℝ) (hδ : 0.001 ≤ δ) :
    ‖Sigma₁ x T δ‖ ≤
      exp (-δ * log x) *
        (1 / (2 * π) * (log (T / (2 * π))) ^ 2 +
          1.8642) := by
  sorry

@[blueprint
  "bklnw-eq_A_11"
  (title := "Equation (A.11)")
  (statement := /-- We denote
  $$ s_1(b, \delta, T) = e^{-\delta b}
  \left(\frac{1}{2\pi}(\log(T/2\pi))^2
  + 1.8642\right). $$ -/)]
noncomputable def s₁ (b δ T : ℝ) : ℝ :=
  exp (-δ * b) *
    (1 / (2 * π) * (log (T / (2 * π))) ^ 2 +
      1.8642)

@[blueprint
  "bklnw-eq_A_12"
  (title := "Equation (A.12)")
  (statement := /-- We have
  $$ |\Sigma_2| \leq 2 \sum_{k=0}^{K-1}
  \frac{\lambda^{k+1}
  x^{-\frac{1}{R \log(T/\lambda^k)}}}{T}
  N\left(1 - \delta,
  \frac{T}{\lambda^k}\right). $$ -/)
  (proof := /-- An argument of Pintz
  \cite[Pintz1980] is employed.  The interval
  $[0,T]$ is split into subintervals
  $[T/\lambda^{k+1}, T/\lambda^k]$ where
  $\lambda > 1$, $0 \leq k \leq K-1$, and
  $K = \lfloor \frac{\log T/H}
  {\log \lambda} \rfloor + 1$.
  Then use the zero-free region to bound
  $\Re \rho$. -/)
  (latexEnv := "sublemma")]
theorem bklnw_eq_A_12 (I : Inputs)
    (x T δ lambda : ℝ) (hlambda : 1 < lambda)
    (hx : 1 < x) (hT : 0 < T) (hTH : I.H < T)
    (hσ : 1 - δ ∈ I.ZDB.σ_range) (hT₀ : I.ZDB.T₀ ≤ I.H) :
    let K := ⌊log (T / I.H) / log lambda⌋₊ + 1
    ‖Sigma₂ x T δ‖ ≤
      2 * ∑ k ∈ Finset.range K,
        (lambda ^ (k + 1) *
          x ^ (-(1 / (I.R * log (T / lambda ^ k)))) /
          T) *
        I.ZDB.N (1 - δ) (T / lambda ^ k) := by
  sorry

@[blueprint
  "bklnw-eq_A_13"
  (title := "Equation (A.13)")
  (statement := /-- We have
  $$ |\Sigma_2| \leq \frac{2\lambda}{T}
  \sum_{k=0}^{K-1} \lambda^k
  x^{-\frac{1}{R \log(T/\lambda^k)}}
  \left(c_1 \left(\frac{T}{\lambda^k}
  \right)^{p(1-\delta)}
  (\log(T/\lambda^k))^{q(1-\delta)}
  + c_2 (\log(T/\lambda^k))^2\right) $$
  where $p$, $q$, $c_1$, $c_2$ are the
  parameters of the zero density bound. -/)
  (proof := /-- Inserting (A.6) into the result
  of (A.12). -/)
  (latexEnv := "sublemma")
  (discussion := 751)]
theorem bklnw_eq_A_13 (I : Inputs)
    (x T δ lambda : ℝ) (hlambda : 1 < lambda)
    (hx : 1 < x) (hT : 0 < T) (hTH : I.H < T)
    (hσ : 1 - δ ∈ I.ZDB.σ_range) (hT₀ : I.ZDB.T₀ ≤ I.H) :
    let K := ⌊log (T / I.H) / log lambda⌋₊ + 1
    ‖Sigma₂ x T δ‖ ≤ (2 * lambda / T) *
      ∑ k ∈ Finset.range K,
        exp (k * log lambda -
          (log x) / (I.R * (log T -
            k * log lambda))) *
        (I.ZDB.c₁ (1 - δ) *
          (T / lambda ^ k) ^ (I.ZDB.p (1 - δ)) *
          (log (T / lambda ^ k)) ^ (I.ZDB.q (1 - δ)) +
        I.ZDB.c₂ (1 - δ) *
          (log (T / lambda ^ k)) ^ 2) := by
  have h4 (k : ℕ) : exp ((k : ℝ) * log lambda - (log x) / (I.R * (log T - (k : ℝ) * log lambda))) =
      lambda ^ k * x ^ (-(1 / (I.R * log (T / lambda ^ k)))) := by
    rw [Real.log_div hT.ne' (by positivity), Real.log_pow, sub_eq_add_neg,
      Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity),
      Real.rpow_def_of_pos (by positivity), mul_neg, mul_one_div]
  refine (bklnw_eq_A_12 I x T δ lambda hlambda hx hT hTH hσ hT₀).trans (le_of_eq ?_)
  simp_rw [zero_density_bound.N, Finset.mul_sum, h4]; congr 1; ext k; ring

@[blueprint
  "bklnw-eq_A_14"
  (title := "Equation (A.14)")
  (statement := /-- We denote
  \begin{align}
  s_2(b, \lambda, K, T) &= \frac{2\lambda}{T}
  \sum_{k=0}^{K-1}
  \exp\left(k \log \lambda
  - \frac{b}{R(\log T
  - k \log \lambda)}\right) \\
  &\quad \times \left(c_1
  \left(\frac{T}{\lambda^k}
  \right)^{p(1-\delta)}
  (\log(T/\lambda^k))^{q(1-\delta)}
  + c_2
  (\log(T/\lambda^k))^2\right) \notag
  \end{align}
  where $p$, $q$, $c_1$, $c_2$ are the
  parameters of the zero density bound. -/)]
noncomputable def Inputs.s₂ (I : Inputs)
    (δ b : ℝ) (K : ℕ) (lambda T : ℝ) : ℝ :=
  (2 * lambda / T) *
    ∑ k ∈ Finset.range K,
      exp (k * log lambda -
        b / (I.R * (log T -
          k * log lambda))) *
      (I.ZDB.c₁ (1 - δ) *
        (T / lambda ^ k) ^ (I.ZDB.p (1 - δ)) *
        (log (T / lambda ^ k)) ^ (I.ZDB.q (1 - δ)) +
      I.ZDB.c₂ (1 - δ) *
        (log (T / lambda ^ k)) ^ 2)

@[blueprint
  "bklnw-thm-13"
  (title := "Theorem 13")
  (statement := /-- Let $b_1, b_2$ satisfy
  $1000 \leq b_1 < b_2$.
  Let $0.001 \leq \delta \leq 0.025$,
  $\lambda > 1$,
  $H < T < e^{b_1}$, and
  $K = \left\lfloor \frac{\log \frac{T}{H}}
  {\log \lambda} \right\rfloor + 1$.
  Then for all $x \in [e^{b_1}, e^{b_2}]$
  $$ \left|\frac{\psi(x) - x}{x}\right|
  \leq s_0(b_2, T)
  + s_1(b_1, \delta, T)
  + s_2(b_1, \delta, \lambda, K, T), $$
  where $s_0, s_1, s_2$ are respectively
  defined in Definitions \ref{bklnw-eq_A_8},
  \ref{bklnw-eq_A_11}, and
  \ref{bklnw-eq_A_14} -/)
  (proof := /-- Follows from combining Sublemmas
  \ref{bklnw_eq_A_7}, \ref{bklnw_eq_A_9},
  \ref{bklnw_eq_A_10}, and
  \ref{bklnw_eq_A_13}. -/)
  (latexEnv := "theorem")
  (discussion := 752)]
theorem bklnw_thm_15 (I : Inputs)
    (b₁ b₂ δ lambda T x : ℝ)
    (hb : 1000 ≤ b₁) (hb' : b₁ < b₂)
    (hδ : 0.001 ≤ δ) (hδ' : δ ≤ 0.025)
    (hlambda : 1 < lambda) (hR : 0 < I.R)
    (hσ : 1 - δ ∈ I.ZDB.σ_range)
    (hT₀ : I.ZDB.T₀ ≤ I.H) (hH : 50 ≤ I.H)
    (hT1 : I.H < T) (hT2 : T < exp b₁)
    (hx : x ∈ Set.Icc (exp b₁) (exp b₂)) :
    let K := ⌊log (T / I.H) / log lambda⌋₊ + 1
    ‖(ψ x - x) / x‖ ≤
      bklnw_eq_A_8 b₂ T + s₁ b₁ δ T +
        I.s₂ δ b₁ K lambda T := by
  intro K
  have hK : K = ⌊log (T / I.H) / log lambda⌋₊ + 1 := rfl
  -- with (hT50 : 50 < T) in place of hH this line becomes the hypothesis itself
  have hT50 : 50 < T := lt_of_le_of_lt hH hT1
  have hT : (0 : ℝ) < T := by linarith
  have hHpos : (0 : ℝ) < I.H := by linarith
  have hH1 : (1 : ℝ) < I.H := by linarith
  have hlam0 : (0 : ℝ) < lambda := by linarith
  have hloglam : (0 : ℝ) < log lambda := log_pos hlambda
  have hx1000 : x ≥ exp 1000 := le_trans (exp_le_exp.mpr hb) hx.1
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (exp_pos 1000) hx1000
  have hx1 : (1 : ℝ) < x := by
    have := add_one_le_exp (1000 : ℝ)
    linarith
  have hlogx₁ : b₁ ≤ log x := (le_log_iff_exp_le hxpos).mpr hx.1
  have hlogx₂ : log x ≤ b₂ := (log_le_iff_le_exp hxpos).mpr hx.2
  obtain ⟨E, hE, hEnorm⟩ := bklnw_eq_A_7 x T hx1000 hT50 (le_trans hT2.le hx.1)
  rw [bklnw_eq_A_9 x T δ (by linarith) (by linarith)] at hE
  have hcast : (((ψ x - x) / x : ℝ) : ℂ) = Sigma₁ x T δ + Sigma₂ x T δ + E := by
    push_cast
    exact hE
  have hnorm_eq : ‖(ψ x - x) / x‖ = ‖Sigma₁ x T δ + Sigma₂ x T δ + E‖ := by
    rw [← hcast]
    norm_cast
  have hE8 : ‖E‖ ≤ bklnw_eq_A_8 b₂ T := by
    refine hEnorm.trans ?_
    simp only [bklnw_eq_A_8]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hT.le)
    have h0 : (0 : ℝ) ≤ log x := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ b₂ - log x)
      (by linarith : (0 : ℝ) ≤ b₂ + log x)]
  have hS1 : ‖Sigma₁ x T δ‖ ≤ s₁ b₁ δ T := by
    refine (bklnw_eq_A_10 x T δ hδ).trans ?_
    simp only [s₁]
    refine mul_le_mul_of_nonneg_right (exp_le_exp.mpr ?_) (by positivity)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ δ)
      (by linarith : (0 : ℝ) ≤ log x - b₁)]
  have hS2 : ‖Sigma₂ x T δ‖ ≤ I.s₂ δ b₁ K lambda T := by
    have h13 : ‖Sigma₂ x T δ‖ ≤ (2 * lambda / T) *
        ∑ k ∈ Finset.range K,
          exp (k * log lambda -
            (log x) / (I.R * (log T -
              k * log lambda))) *
          (I.ZDB.c₁ (1 - δ) *
            (T / lambda ^ k) ^ (I.ZDB.p (1 - δ)) *
            (log (T / lambda ^ k)) ^ (I.ZDB.q (1 - δ)) +
          I.ZDB.c₂ (1 - δ) *
            (log (T / lambda ^ k)) ^ 2) :=
      bklnw_eq_A_13 I x T δ lambda hlambda hx1 hT hT1 hσ hT₀
    refine h13.trans ?_
    simp only [Inputs.s₂]
    refine mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun k hk ↦ ?_) (div_nonneg (by linarith) hT.le)
    have hkK : k ≤ ⌊log (T / I.H) / log lambda⌋₊ := by
      have h := Finset.mem_range.mp hk
      rw [hK] at h
      omega
    have hHT : (1 : ℝ) ≤ T / I.H := by
      rw [div_eq_mul_inv, ← mul_inv_cancel₀ hHpos.ne']
      exact mul_le_mul_of_nonneg_right hT1.le (inv_nonneg.mpr hHpos.le)
    have hfloor : (k : ℝ) ≤ log (T / I.H) / log lambda :=
      le_trans (Nat.cast_le.mpr hkK)
        (Nat.floor_le (div_nonneg (log_nonneg hHT) hloglam.le))
    have hk' : (k : ℝ) * log lambda ≤ log (T / I.H) := by
      have h1 := mul_le_mul_of_nonneg_right hfloor hloglam.le
      rwa [div_mul_cancel₀ _ hloglam.ne'] at h1
    have hk'' : (k : ℝ) * log lambda ≤ log T - log I.H := by
      rwa [log_div hT.ne' hHpos.ne'] at hk'
    have hD : (0 : ℝ) < log T - (k : ℝ) * log lambda :=
      lt_of_lt_of_le (log_pos hH1) (by linarith)
    have hRD : (0 : ℝ) < I.R * (log T - (k : ℝ) * log lambda) := mul_pos hR hD
    have hTk : I.H ≤ T / lambda ^ k := by
      have h2 : exp (log I.H) ≤ exp (log T - (k : ℝ) * log lambda) :=
        exp_le_exp.mpr (by linarith)
      rwa [exp_log hHpos, exp_sub, exp_log hT, ← log_pow,
        exp_log (pow_pos hlam0 k)] at h2
    -- the density-bound bracket dominates N'(1-δ, T/λ^k), which is nonnegative
    have hN' : (0 : ℝ) ≤ riemannZeta.N' (1 - δ) (T / lambda ^ k) := by
      simp only [riemannZeta.N', riemannZeta.zeroes_sum, Pi.one_apply, one_mul]
      refine tsum_nonneg fun ρ ↦ ?_
      suffices h : (0 : ℤ) ≤ riemannZeta.order ↑ρ by exact_mod_cast h
      have hmem := ρ.2
      simp only [riemannZeta.zeroes_rect, riemannZeta.zeroes, Set.mem_setOf_eq,
        Set.mem_Ioo] at hmem
      have hne : (↑ρ : ℂ) ≠ 1 := by
        intro h1
        have h2 := hmem.1.2
        rw [h1, Complex.one_re] at h2
        exact lt_irrefl 1 h2
      have hana : AnalyticAt ℂ riemannZeta (↑ρ : ℂ) :=
        riemannZeta_analyticOn_compl_one _ (Set.mem_compl_singleton_iff.mpr hne)
      have hord := hana.meromorphicOrderAt_nonneg
      simp only [riemannZeta.order]
      cases horder : meromorphicOrderAt riemannZeta (↑ρ : ℂ) with
      | top => exact le_rfl
      | coe n =>
        rw [horder] at hord
        change (0 : ℤ) ≤ n
        exact_mod_cast hord
    have hBk : (0 : ℝ) ≤ I.ZDB.c₁ (1 - δ) *
        (T / lambda ^ k) ^ (I.ZDB.p (1 - δ)) *
        (log (T / lambda ^ k)) ^ (I.ZDB.q (1 - δ)) +
        I.ZDB.c₂ (1 - δ) * (log (T / lambda ^ k)) ^ 2 :=
      le_trans hN' (I.ZDB.bound (T / lambda ^ k) (le_trans hT₀ hTk) (1 - δ) hσ)
    refine mul_le_mul_of_nonneg_right (exp_le_exp.mpr ?_) hBk
    have hdiv : b₁ / (I.R * (log T - (k : ℝ) * log lambda)) ≤
        log x / (I.R * (log T - (k : ℝ) * log lambda)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hlogx₁ (inv_nonneg.mpr hRD.le)
    linarith
  rw [hnorm_eq]
  calc ‖Sigma₁ x T δ + Sigma₂ x T δ + E‖
      ≤ ‖Sigma₁ x T δ‖ + ‖Sigma₂ x T δ‖ + ‖E‖ :=
        le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ bklnw_eq_A_8 b₂ T + s₁ b₁ δ T + I.s₂ δ b₁ K lambda T := by linarith

@[blueprint
  "bklnw-eq_A_16"
  (title := "Equation (A.16)")
  (statement := /-- We define
  $$ k(\sigma, x_0) = \left(
  \exp\left(\frac{10 - 16 \sigma}{3}
  \left( \frac{\log x_0}{R}
  \right)^{1/2} \right)
  \left( \sqrt{ \frac{\log x_0}{R} }
  \right)^{5 - 2 \sigma}
  \right)^{-1}. $$
  -/)]
noncomputable def Inputs.k (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  (exp ((10 - 16 * σ) / 3 *
      (log x₀ / I.R) ^ (1 / 2 : ℝ)) *
    sqrt (log x₀ / I.R) ^ (5 - 2 * σ)) ^ (-1 : ℝ)

@[blueprint
  "bklnw-eq_A_17"
  (title := "Equation (A.17)")
  (statement := /-- We define
  $$ c_3(\sigma, x_0) = 2
  \exp\left( -2 \left( \frac{\log x_0}{R}
  \right)^{1/2} \right)
  (\log x_0)^2 k(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.c3 (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  2 * exp (-2 * (log x₀ / I.R) ^ (1 / 2 : ℝ)) *
    (log x₀) ^ 2 * I.k σ x₀

@[blueprint
  "bklnw-eq_A_18"
  (title := "Equation (A.18)")
  (statement := /-- We define
  $$ c_4(\sigma, x_0) = x_0^{\sigma - 1}
  \left( \frac{2 \log x_0}{\pi R}
  + 1.8642 \right) k(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.c4 (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  x₀ ^ (σ - 1 : ℝ) *
    (2 * log x₀ / π / I.R + 1.8642) *
    I.k σ x₀

@[blueprint
  "bklnw-eq_A_19"
  (title := "Equation (A.19)")
  (statement := /-- We define
  $$ c_5(\sigma, x_0) = 8.01 \cdot c_2(\sigma)
  \exp\left( -2 \left( \frac{\log x_0}{R}
  \right)^{1/2} \right)
  \frac{\log x_0}{R} k(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.c5 (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  8.01 * I.ZDB.c₂ σ *
    exp (-2 * (log x₀ / I.R) ^ (1 / 2 : ℝ)) *
    (log x₀ / I.R) * I.k σ x₀

@[blueprint
  "bklnw-eq_A_20"
  (title := "Equation (A.20)")
  (statement := /-- We define
  $$ A(\sigma, x_0) = 2.0025 \cdot 2^{5 - 2 \sigma}
  \cdot c_1(\sigma) + c_3(\sigma, x_0)
  + c_4(\sigma, x_0)
  + c_5(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.A (I : Inputs)
    (σ x₀ : ℝ) : ℝ :=
  2.0025 * 2 ^ (5 - 2 * σ) * I.ZDB.c₁ σ +
    I.c3 σ x₀ + I.c4 σ x₀ + I.c5 σ x₀

@[blueprint
  "bklnw-eq_A_21"
  (title := "Equation (A.21)")
  (statement := /-- We define
  $$ B = 5/2 - \sigma, $$
  and
  $$ C = 16 \sigma/3 - \frac{10}{3}. $$
  -/)]
noncomputable def Inputs.B (_ : Inputs)
    (σ : ℝ) : ℝ :=
  5 / 2 - σ

@[blueprint
  "bklnw-eq_A_21"]
noncomputable def Inputs.C (_ : Inputs)
    (σ : ℝ) : ℝ :=
  16 * σ / 3 - 10 / 3

@[blueprint
  "bklnw-thm-14"
  (title := "Theorem 14")
  (statement := /-- Let $x_0 \geq 1000$ and let
  $\sigma \in [0.75, 1)$. For all
  $x \geq e^{x_0}$,
  $$ \frac{|\psi(x) - x|}{x} \leq A
  \left( \frac{\log x}{R} \right)^B
  \exp\left( -C \left( \frac{\log x}{R}
  \right)^{1/2} \right) $$
  where $A$, $B$, and $C$ are defined in
  Definitions \ref{bklnw-eq_A_20},
  \ref{bklnw-eq_A_21}. -/)
  (proof := /-- This is proven by Platt and
  Trudgian \cite{PT2021} -/)]
theorem thm_14 (I : Inputs) {x₀ σ x : ℝ}
    (hx₀ : x₀ ≥ 1000)
    (hσ : 0.75 ≤ σ ∧ σ < 1)
    (hx : x ≥ exp x₀) :
    Eψ x ≤ I.A σ x₀ *
      (log x / I.R) ^ (I.B σ) *
      exp (-I.C σ *
        (log x / I.R) ^ (1 / 2 : ℝ)) := by
  sorry

@[blueprint
 "bklnw-eq_A_26"
  (title := "Equation (A.26)")
  (statement := /-- For $100 \leq x \leq 10^{19}$,
  one has
  $$ | (x - \psi(x)) / \sqrt{x} |
  \leq 0.94. $$ -/)
  (proof := /-- This follows from
  Theorem \ref{buthe-theorem-2a}. -/)]
theorem bklnw_eq_A_26 (x : ℝ)
    (hx1 : 100 ≤ x) (hx2 : x ≤ 1e19) :
    Eψ x ≤ 0.94 / sqrt x :=
  Buthe.theorem_2a (by linarith) (by linarith)

@[blueprint
  "bklnw-lemma_15"
  (title := "Lemma 15")
  (statement := /-- Let $B_0$, $B$, and $c$ be
  positive constants such that
\begin{equation}\tag{A.27}\label{bklnw:A.27}
|(x-\psi(x))/\sqrt{x}| \leq c
\hbox{ for all } B_0 < x \leq B
\end{equation}
  is known.  Furthermore, assume for every
  $b_0 > 0$ there exists $\varepsilon(b_0) > 0$
  such that
\begin{equation}\tag{A.28}\label{bklnw:A.28}
|\psi(x) - x| \leq \varepsilon(b_0) x
\quad \text{for all } x \geq e^{b_0}.
\end{equation}
Let $b$ be positive such that
$e^b \in (B_0, B]$. Then, for all
$x \geq e^b$ we have
\begin{equation}\tag{A.29}\label{bklnw:A.29}
\left|\frac{\psi(x) - x}{x}\right|
\leq \max (\frac{c}{e^{\frac{b}{2}}},
\varepsilon(\log B)).
\end{equation} -/)
  (proof := /-- Multiplying both sides of
  \eqref{bklnw:A.27} by $\frac{1}{\sqrt{x}}$ gives
\[
\left|\frac{\psi(x) - x}{x}\right|
\leq \frac{c}{e^{\frac{b}{2}}}
\quad \text{for all } e^b \leq x \leq B
\]
as $\frac{1}{\sqrt{x}}
\leq \frac{1}{e^{\frac{b}{2}}}$.
Then, for $x \geq B$ we apply \eqref{bklnw:A.28}
with $b_0 = \log B$.
Combining these bounds,
we derive \eqref{bklnw:A.29}. -/)
  (latexEnv := "lemma")
  (discussion := 753)]
theorem bklnw_lemma_15 (c B₀ B : ℝ)
    (hbound : ∀ x ∈ Set.Ioc B₀ B,
      Eψ x ≤ c / sqrt x)
    (ε : ℝ → ℝ)
    (hε : ∀ b₀ > 0, ∀ x ≥ exp b₀, Eψ x ≤ ε b₀)
    (b : ℝ)
    (hb : exp b ∈ Set.Ioc B₀ B)
    (hbpos : b > 0)
    (hcpos : c > 0)
    (hBpos : B > 0) :
    ∀ x ≥ exp b,
      Eψ x ≤ max (c / exp (b / 2))
        (ε (log B)) := by
  intro x hx
  by_cases! hcases : x ≤ B
  · have hlb : B₀ < x := by linarith [hx, hb.1]
    simp only [Set.Ioc, Set.mem_setOf_eq, and_imp] at hbound
    have hb : Eψ x ≤ c / sqrt x :=
      hbound x hlb hcases
    have hsqrtcomp : sqrt (exp b) ≤ sqrt x :=
      Real.sqrt_monotone hx
    have hidentity1 : exp (2 * (b / 2)) = exp (b / 2) ^ 2 := Real.exp_nat_mul (b / 2) 2
    have hidentity2 : 2 * (b / 2) = b := by ring
    simp only [hidentity2] at hidentity1
    have hnonneg : 0 ≤ exp (b / 2) := by
      positivity
    have hidentity3 : sqrt (exp b) = sqrt (exp (b / 2) ^ 2) := by
      simpa using congrArg Real.sqrt hidentity1
    simp only [Real.sqrt_sq hnonneg] at hidentity3
    have hsqrtcomp2 : exp (b / 2) ≤ sqrt x := by
      linarith
    have hsqrtpos : sqrt x > 0 := by
      linarith [exp_pos (b / 2)]
    have hsqrtcomp3 : c / sqrt x ≤ c / exp (b / 2) := by gcongr
    have hubcomp : c / exp (b / 2) ≤ max (c / exp (b / 2)) (ε (log B)) := le_max_left ..
    linarith
  · have hidentity : exp (log B) = B :=
      Real.exp_log hBpos
    have hBone : 1 < B := by
      linarith [hb.2, Real.one_lt_exp_iff.2 hbpos]
    have hlogBpos : 0 < log B :=
      Real.log_pos hBone
    specialize hε (log B) hlogBpos
    have hlb : x ≥ exp (log B) := by linarith
    specialize hε x hlb
    have hubcomp : ε (log B) ≤ max (c / exp (b / 2)) (ε (log B)) := le_max_right ..
    linarith

@[blueprint
 "bklnw-cor_15_1"
  (title := "Corollary 15.1")
  (statement := /-- Let $b$ be a positive constant
  such that $\log 11 < b \leq 19 \log(10)$.
  Then we have
  $$ \left|\frac{\psi(x) - x}{x}\right|
  \leq \max\left\{\frac{0.94}{e^{\frac{b}{2}}},
  \varepsilon(19 \log 10)\right\}
  \quad \text{for all } x \geq e^b. $$
  Note that by Table 8, we have
  $\varepsilon(19 \log 10)
  = 1.93378 \cdot 10^{-8}$. -/)
  (proof := /-- By \cite[(1.5)]{Buthe},
  (A.27) holds with $B_0 = 11$,
  $B = 10^{19}$, and $c = 0.94$.
  Thus we may apply Lemma
  \ref{bklnw-lemma_15} with $B_0 = 11$,
  $B = 10^{19}$, and $c = 0.94$ from
  \cite[(1.5)]{Buthe} to obtain
  the claim. -/)
  (latexEnv := "corollary")]
theorem bklnw_cor_15_1 (b : ℝ)
    (hb1 : log 11 < b)
    (hb2 : b ≤ 19 * log 10)
    (ε : ℝ → ℝ)
    (hε : ∀ b₀ > 0, ∀ x ≥ exp b₀,
      Eψ x ≤ ε b₀) :
    ∀ x ≥ exp b,
      Eψ x ≤ max (0.94 / exp (b / 2))
        (ε (19 * log 10)) := by
  have hlog11_pos : (0 : ℝ) < log 11 := by
    positivity
  have hbpos : b > 0 := by linarith
  have h10_19 : (10 : ℝ) ^ (19 : ℕ) > 0 := by
    positivity
  have hlog_eq : log ((10 : ℝ) ^ (19 : ℕ)) = 19 * log 10 := by
    rw [Real.log_pow]
    ring
  rw [← hlog_eq]
  apply bklnw_lemma_15 0.94 11
    ((10 : ℝ) ^ (19 : ℕ))
  · intro x hx
    exact Buthe.theorem_2a hx.1 hx.2
  · exact hε
  · constructor
    · have : Real.exp (Real.log 11) < Real.exp b := Real.exp_lt_exp.mpr hb1
      rwa [Real.exp_log (by norm_num : (11 : ℝ) > 0)] at this
    · rw [← hlog_eq] at hb2
      rw [← Real.exp_log (by positivity : (10 : ℝ) ^ (19 : ℕ) > 0)]
      exact Real.exp_le_exp.mpr hb2
  · exact hbpos
  · norm_num
  · exact h10_19

@[blueprint
  "logan-function"
  (title := "Logan's function")
  (statement := /-- We define Logan's function
  $$ \ell_{c,\varepsilon}(\xi)
  = \frac{c}{\sinh c}
  \frac{\sin(\sqrt{(\xi\varepsilon)^2
  - c^2})}
  {\sqrt{(\xi\varepsilon)^2 - c^2}}. $$ -/)
  (latexEnv := "definition")]
noncomputable def ℓ (c ε ξ : ℝ) : ℝ :=
  (c / sinh c) *
    sin (sqrt ((ξ * ε) ^ 2 - c ^ 2)) /
    sqrt ((ξ * ε) ^ 2 - c ^ 2)

/-- The modified Bessel function of the first kind of order zero,
$I_0(x) = \sum_{m \geq 0} (x/2)^{2m}/(m!)^2$, introduced for the closed form of the
Logan kernel transform below (not yet in Mathlib). -/
noncomputable def besselI0 (x : ℝ) : ℝ :=
  ∑' m : ℕ, (x / 2) ^ (2 * m) / ((m.factorial : ℝ)) ^ 2

@[blueprint
  "logan-function-ft"
  (title := "Fourier transform of Logan's function")
  (statement := /-- The Fourier transform
  $\eta_{c,\varepsilon}(\xi)
  = \frac{1}{2\pi} \int_{\R} e^{-it\xi}
  ℓ_{c,\varepsilon}(t) \, dt$
  of Logan's kernel, in closed form: the kernel
  is band-limited, so the transform is supported
  in $[-\varepsilon, \varepsilon]$, where
  $$ \eta_{c,\varepsilon}(\xi)
  = \frac{c}{2 \varepsilon \sinh c}\,
  I_0\!\left(c \sqrt{1 - (\xi/\varepsilon)^2}\right) $$
  with $I_0$ the modified Bessel function of
  order zero (\cite[p.~2490]{Buthe2}). The
  closed form is taken as the definition; the
  Fourier identity is a proof obligation of
  Theorem 16. -/)
  (latexEnv := "definition")]
noncomputable def η (c ε ξ : ℝ) : ℝ :=
  if |ξ| ≤ ε then
    c / (2 * ε * sinh c) * besselI0 (c * sqrt (1 - (ξ / ε) ^ 2))
  else 0

noncomputable def pre_μ (c ε t : ℝ) : ℝ :=
  -∫ τ in Set.Iic t, η c ε τ

@[blueprint
  "buthe-mu-def"
  (title := "Definition of Buthe's function mu")
  (statement := /-- We define the auxiliary
  functions
  \begin{align*}
  \mu_{c,\varepsilon}(t) &=
  \begin{cases}
  -\int_{-\infty}^{t} \eta_{c,\varepsilon}(\tau)
  d\tau & t < 0, \\
  -\mu_{c,\varepsilon}(-t) & t > 0, \\
  0 & t = 0,
  \end{cases} \\
  \nu_{c,\varepsilon}(t) &= \int_{-\infty}^t
  \mu_{c,\varepsilon}(\tau) d\tau.
  \end{align*} -/)
  (latexEnv := "definition")]
noncomputable def μ (c ε t : ℝ) : ℝ :=
  if t < 0 then pre_μ c ε t
  else if t > 0 then -pre_μ c ε (-t)
  else 0

noncomputable def ν (c ε t : ℝ) : ℝ :=
  ∫ τ in Set.Iic t, μ c ε τ

/-! ### Elementary properties of the Logan kernel transform

Sign, support, and symmetry facts about `besselI0`, `η` and `μ`, provable directly from
the closed form. They are the base layer for the monotonicity claims of
\cite[p.~2492]{Buthe2} and for certified bounds on the `μ` and `ν` values appearing in
the `hB0` hypothesis of Theorem 16. -/

lemma besselI0_summable (x : ℝ) :
    Summable (fun m : ℕ ↦ (x / 2) ^ (2 * m) / ((m.factorial : ℝ)) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun m ↦ by rw [pow_mul]; positivity) (fun m ↦ ?_)
    (Real.summable_pow_div_factorial (x ^ 2 / 4))
  have h2 : (x / 2) ^ (2 * m) = (x ^ 2 / 4) ^ m := by
    rw [pow_mul, div_pow]
    norm_num
  rw [h2]
  gcongr (x ^ 2 / 4) ^ m / ?_
  exact_mod_cast Nat.le_self_pow (by norm_num) m.factorial

lemma besselI0_nonneg (x : ℝ) : 0 ≤ besselI0 x :=
  tsum_nonneg fun m ↦ by rw [pow_mul]; positivity

lemma besselI0_one_le (x : ℝ) : 1 ≤ besselI0 x := by
  have h := (besselI0_summable x).le_tsum 0 fun j _ ↦ by rw [pow_mul]; positivity
  simpa [Nat.factorial] using! h

lemma besselI0_pos (x : ℝ) : 0 < besselI0 x :=
  lt_of_lt_of_le one_pos (besselI0_one_le x)

lemma besselI0_le_besselI0 {x y : ℝ} (h : |x| ≤ |y|) : besselI0 x ≤ besselI0 y := by
  refine Summable.tsum_le_tsum (fun m ↦ ?_) (besselI0_summable x) (besselI0_summable y)
  have hx : (x / 2) ^ (2 * m) = (x ^ 2 / 4) ^ m := by rw [pow_mul, div_pow]; norm_num
  have hy : (y / 2) ^ (2 * m) = (y ^ 2 / 4) ^ m := by rw [pow_mul, div_pow]; norm_num
  rw [hx, hy]
  have hxy : x ^ 2 ≤ y ^ 2 := by
    nlinarith [sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]
  gcongr

lemma η_nonneg {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (ξ : ℝ) : 0 ≤ η c ε ξ := by
  unfold η
  split
  · have hs : 0 < sinh c := sinh_pos_iff.mpr hc
    refine mul_nonneg (div_nonneg hc.le ?_) (besselI0_nonneg _)
    nlinarith [mul_pos hε hs]
  · exact le_rfl

lemma η_even (c ε ξ : ℝ) : η c ε (-ξ) = η c ε ξ := by
  simp [η, abs_neg, neg_div]

lemma η_eq_zero_of_abs_gt {c ε ξ : ℝ} (h : ε < |ξ|) : η c ε ξ = 0 := by
  simp [η, not_le.mpr h]

lemma μ_zero (c ε : ℝ) : μ c ε 0 = 0 := by
  simp [μ]

lemma μ_nonneg_of_pos {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    0 ≤ μ c ε t := by
  unfold μ
  rw [if_neg (by linarith : ¬ t < 0), if_pos ht, pre_μ, neg_neg]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic fun ξ _ ↦ η_nonneg hc hε ξ

lemma μ_nonpos_of_neg {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {t : ℝ} (ht : t < 0) :
    μ c ε t ≤ 0 := by
  unfold μ
  rw [if_pos ht, pre_μ]
  simp only [neg_nonpos]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic fun ξ _ ↦ η_nonneg hc hε ξ

lemma μ_neg (c ε t : ℝ) : μ c ε (-t) = -μ c ε t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · unfold μ
    rw [if_neg (by linarith : ¬ -t < 0), if_pos (by linarith : -t > 0), neg_neg,
      if_pos ht]
  · simp [μ]
  · unfold μ
    rw [if_pos (by linarith : -t < 0), if_neg (by linarith : ¬ t < 0), if_pos ht,
      neg_neg]

lemma continuous_besselI0 : Continuous besselI0 := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hmem : Metric.ball (0 : ℝ) (|x₀| + 1) ∈ nhds x₀ := by
    refine Metric.isOpen_ball.mem_nhds ?_
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith [abs_nonneg x₀]
  refine (continuousOn_tsum
    (fun m ↦ (((continuous_id.div_const 2).pow (2 * m)).div_const _).continuousOn)
    (besselI0_summable (|x₀| + 1)) ?_).continuousAt hmem
  intro m x hx
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have hb : |x / 2| ≤ (|x₀| + 1) / 2 := by
    rw [abs_div, abs_two]
    linarith
  rw [Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m.factorial : ℝ)) ^ 2)]
  gcongr
  exact hb

lemma measurable_η (c ε : ℝ) : Measurable (η c ε) := by
  unfold η
  refine Measurable.ite (measurableSet_le measurable_id.abs measurable_const) ?_
    measurable_const
  have h1 : Continuous fun ξ : ℝ ↦ c * sqrt (1 - (ξ / ε) ^ 2) :=
    (Real.continuous_sqrt.comp (by fun_prop)).const_mul c
  exact ((continuous_besselI0.comp h1).const_mul _).measurable

lemma η_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (ξ : ℝ) :
    η c ε ξ ≤ c / (2 * ε * sinh c) * besselI0 c := by
  have hs : 0 < sinh c := sinh_pos_iff.mpr hc
  have hcoef : 0 ≤ c / (2 * ε * sinh c) :=
    div_nonneg hc.le (by nlinarith [mul_pos hε hs])
  unfold η
  split
  · refine mul_le_mul_of_nonneg_left (besselI0_le_besselI0 ?_) hcoef
    have h1 : sqrt (1 - (ξ / ε) ^ 2) ≤ 1 :=
      Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (ξ / ε)])
    calc |c * sqrt (1 - (ξ / ε) ^ 2)|
        = c * sqrt (1 - (ξ / ε) ^ 2) :=
          abs_of_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg _))
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left h1 hc.le
      _ = c := mul_one c
      _ = |c| := (abs_of_pos hc).symm
  · exact mul_nonneg hcoef (besselI0_nonneg c)

lemma integrable_η {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    MeasureTheory.Integrable (η c ε) := by
  have hsupp : Function.support (η c ε) ⊆ Set.Icc (-ε) ε := by
    intro ξ hξ
    rw [Set.mem_Icc, ← abs_le]
    by_contra h
    exact hξ (η_eq_zero_of_abs_gt (not_le.mp h))
  rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
  refine MeasureTheory.Measure.integrableOn_of_bounded
    (M := c / (2 * ε * sinh c) * besselI0 c)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    ((measurable_η c ε).aestronglyMeasurable)
    (MeasureTheory.ae_of_all _ fun ξ ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (η_nonneg hc hε ξ)]
  exact η_le hc hε ξ

lemma μ_eq_zero_of_lt_neg {c ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t < -ε) :
    μ c ε t = 0 := by
  unfold μ
  rw [if_pos (by linarith : t < 0), pre_μ, neg_eq_zero]
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun ξ hξ ↦ ?_
  have h1 : ξ ≤ t := hξ
  refine η_eq_zero_of_abs_gt ?_
  rw [abs_of_neg (by linarith : ξ < 0)]
  linarith

lemma μ_eq_zero_of_gt {c ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : ε < t) :
    μ c ε t = 0 := by
  have h1 := μ_eq_zero_of_lt_neg (c := c) hε (by linarith : -t < -ε)
  have h2 := μ_neg c ε t
  linarith [h1, h2]

lemma μ_antitoneOn {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    AntitoneOn (μ c ε) (Set.Ioi 0) := by
  intro s hs t ht hst
  rw [Set.mem_Ioi] at hs ht
  unfold μ
  rw [if_neg (by linarith : ¬ t < 0), if_pos ht, if_neg (by linarith : ¬ s < 0),
    if_pos hs, pre_μ, pre_μ, neg_neg, neg_neg]
  refine MeasureTheory.setIntegral_mono_set ((integrable_η hc hε).integrableOn)
    (MeasureTheory.ae_of_all _ fun ξ ↦ η_nonneg hc hε ξ) ?_
  exact (Set.Iic_subset_Iic.mpr (by linarith : -t ≤ -s)).eventuallyLE

lemma ν_nonpos_of_nonpos {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {t : ℝ} (ht : t ≤ 0) :
    ν c ε t ≤ 0 := by
  unfold ν
  refine MeasureTheory.setIntegral_nonpos measurableSet_Iic fun τ hτ ↦ ?_
  have h1 : τ ≤ t := hτ
  rcases lt_or_eq_of_le (le_trans h1 ht) with h | h
  · exact μ_nonpos_of_neg hc hε h
  · simp [h, μ_zero]

lemma ν_eq_zero_of_lt_neg {c ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t < -ε) :
    ν c ε t = 0 := by
  unfold ν
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun τ hτ ↦ ?_
  exact μ_eq_zero_of_lt_neg hε (lt_of_le_of_lt hτ ht)

open MeasureTheory in
/-- A bounded function vanishing outside `[-ε, ε]` has all its `Iic`-integrals bounded
by `M * (2ε)`. -/
private lemma abs_setIntegral_Iic_le {f : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hf_bound : ∀ x, |f x| ≤ M) (hf_zero : ∀ x, ε < |x| → f x = 0) (u : ℝ) :
    |∫ x in Set.Iic u, f x| ≤ M * (2 * ε) := by
  have heq : ∫ x in Set.Iic u, f x = ∫ x in Set.Iic u ∩ Set.Icc (-ε) ε, f x := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
      Set.inter_subset_left fun x hx ↦ ?_
    refine hf_zero x ?_
    have h3 : x ∉ Set.Icc (-ε) ε := fun hmem ↦ hx.2 ⟨hx.1, hmem⟩
    rw [Set.mem_Icc, ← abs_le] at h3
    exact not_le.mp h3
  have hvol : (volume (Set.Iic u ∩ Set.Icc (-ε) ε)).toReal ≤ 2 * ε := by
    have h2 : volume (Set.Icc (-ε : ℝ) ε) = ENNReal.ofReal (2 * ε) := by
      rw [Real.volume_Icc]
      ring_nf
    calc (volume (Set.Iic u ∩ Set.Icc (-ε) ε)).toReal
        ≤ (volume (Set.Icc (-ε : ℝ) ε)).toReal :=
          ENNReal.toReal_mono (by rw [h2]; exact ENNReal.ofReal_ne_top)
            (measure_mono Set.inter_subset_right)
      _ = 2 * ε := by rw [h2, ENNReal.toReal_ofReal (by linarith)]
  have hfin : volume (Set.Iic u ∩ Set.Icc (-ε) ε) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hnorm := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (C := M)
    (f := f) hfin (fun x _ ↦ by simpa using hf_bound x)
  rw [heq, ← Real.norm_eq_abs]
  calc ‖∫ x in Set.Iic u ∩ Set.Icc (-ε) ε, f x‖
      ≤ M * (volume (Set.Iic u ∩ Set.Icc (-ε) ε)).toReal := hnorm
    _ ≤ M * (2 * ε) := mul_le_mul_of_nonneg_left hvol hM

lemma pre_μ_antitone {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) : Antitone (pre_μ c ε) := by
  intro s t hst
  unfold pre_μ
  rw [neg_le_neg_iff]
  exact MeasureTheory.setIntegral_mono_set ((integrable_η hc hε).integrableOn)
    (MeasureTheory.ae_of_all _ fun ξ ↦ η_nonneg hc hε ξ)
    (Set.Iic_subset_Iic.mpr hst).eventuallyLE

lemma measurable_μ {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) : Measurable (μ c ε) := by
  unfold μ
  refine Measurable.ite measurableSet_Iio (pre_μ_antitone hc hε).measurable ?_
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact ((pre_μ_antitone hc hε).measurable.comp measurable_neg).neg

private lemma pre_μ_abs_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (u : ℝ) :
    |pre_μ c ε u| ≤ c / sinh c * besselI0 c := by
  have hs : 0 < sinh c := sinh_pos_iff.mpr hc
  have h := abs_setIntegral_Iic_le (f := η c ε)
    (M := c / (2 * ε * sinh c) * besselI0 c) hε
    (mul_nonneg (div_nonneg hc.le (by nlinarith [mul_pos hε hs])) (besselI0_nonneg c))
    (fun x ↦ by rw [abs_of_nonneg (η_nonneg hc hε x)]; exact η_le hc hε x)
    (fun x hx ↦ η_eq_zero_of_abs_gt hx) u
  unfold pre_μ
  rw [abs_neg]
  refine h.trans (le_of_eq ?_)
  field_simp [hε.ne', hs.ne']

lemma μ_abs_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (t : ℝ) :
    |μ c ε t| ≤ c / sinh c * besselI0 c := by
  have hs : 0 < sinh c := sinh_pos_iff.mpr hc
  have hnn : 0 ≤ c / sinh c * besselI0 c :=
    mul_nonneg (div_nonneg hc.le hs.le) (besselI0_nonneg c)
  unfold μ
  split
  · exact pre_μ_abs_le hc hε t
  · split
    · rw [abs_neg]
      exact pre_μ_abs_le hc hε (-t)
    · simpa using hnn

lemma integrable_μ {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    MeasureTheory.Integrable (μ c ε) := by
  have hsupp : Function.support (μ c ε) ⊆ Set.Icc (-ε) ε := by
    intro t ht
    rw [Set.mem_Icc, ← abs_le]
    by_contra h
    rcases lt_abs.mp (not_le.mp h) with h1 | h1
    · exact ht (μ_eq_zero_of_gt hε h1)
    · exact ht (μ_eq_zero_of_lt_neg hε (by linarith))
  rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
  refine MeasureTheory.Measure.integrableOn_of_bounded
    (M := c / sinh c * besselI0 c)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    ((measurable_μ hc hε).aestronglyMeasurable)
    (MeasureTheory.ae_of_all _ fun t ↦ ?_)
  rw [Real.norm_eq_abs]
  exact μ_abs_le hc hε t

lemma ν_abs_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (t : ℝ) :
    |ν c ε t| ≤ c / sinh c * besselI0 c * (2 * ε) := by
  have hs : 0 < sinh c := sinh_pos_iff.mpr hc
  have hM : 0 ≤ c / sinh c * besselI0 c :=
    mul_nonneg (div_nonneg hc.le hs.le) (besselI0_nonneg c)
  unfold ν
  exact abs_setIntegral_Iic_le hε hM (fun x ↦ μ_abs_le hc hε x)
    (fun x hx ↦ by
      rcases lt_abs.mp hx with h1 | h1
      · exact μ_eq_zero_of_gt hε h1
      · exact μ_eq_zero_of_lt_neg hε (by linarith)) t

lemma besselI0_partial_le (x : ℝ) (N : ℕ) :
    ∑ m ∈ Finset.range N, (x / 2) ^ (2 * m) / ((m.factorial : ℝ)) ^ 2 ≤ besselI0 x := by
  change _ ≤ ∑' m : ℕ, (x / 2) ^ (2 * m) / ((m.factorial : ℝ)) ^ 2
  exact Summable.sum_le_tsum (Finset.range N)
    (fun m _ ↦ by rw [pow_mul]; positivity) (besselI0_summable x)

lemma besselI0_sub_partial_le (x : ℝ) (N : ℕ) :
    besselI0 x - ∑ m ∈ Finset.range N, (x / 2) ^ (2 * m) / ((m.factorial : ℝ)) ^ 2 ≤
      (x / 2) ^ (2 * N) / ((N.factorial : ℝ)) ^ 2 * besselI0 x := by
  have hsum := besselI0_summable x
  have hb : besselI0 x = ∑' m : ℕ, (x / 2) ^ (2 * m) / ((m.factorial : ℝ)) ^ 2 := rfl
  have hsplit := hsum.sum_add_tsum_nat_add N
  have hterm : ∀ k : ℕ, (x / 2) ^ (2 * (k + N)) / (((k + N).factorial : ℝ)) ^ 2 ≤
      (x / 2) ^ (2 * N) / ((N.factorial : ℝ)) ^ 2 *
        ((x / 2) ^ (2 * k) / ((k.factorial : ℝ)) ^ 2) := by
    intro k
    have hfact : (N.factorial : ℝ) * (k.factorial : ℝ) ≤ ((k + N).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (k + N).factorial_pos
        (by simpa [mul_comm] using Nat.factorial_mul_factorial_dvd_factorial_add k N)
    have hN : (0 : ℝ) < ((N.factorial : ℝ)) ^ 2 :=
      pow_pos (by exact_mod_cast N.factorial_pos) 2
    have hk : (0 : ℝ) < ((k.factorial : ℝ)) ^ 2 :=
      pow_pos (by exact_mod_cast k.factorial_pos) 2
    have hNk : (0 : ℝ) ≤ (N.factorial : ℝ) * (k.factorial : ℝ) := by positivity
    rw [show 2 * (k + N) = 2 * N + 2 * k by ring, pow_add, div_mul_div_comm]
    gcongr (x / 2) ^ (2 * N) * (x / 2) ^ (2 * k) / ?_ <;>
      first
        | exact mul_pos hN hk
        | (rw [pow_mul, pow_mul]; positivity)
        | nlinarith [hfact, hNk]
  have htail : (∑' k : ℕ, (x / 2) ^ (2 * (k + N)) / (((k + N).factorial : ℝ)) ^ 2) ≤
      (x / 2) ^ (2 * N) / ((N.factorial : ℝ)) ^ 2 * besselI0 x := by
    calc (∑' k : ℕ, (x / 2) ^ (2 * (k + N)) / (((k + N).factorial : ℝ)) ^ 2)
        ≤ ∑' k : ℕ, (x / 2) ^ (2 * N) / ((N.factorial : ℝ)) ^ 2 *
            ((x / 2) ^ (2 * k) / ((k.factorial : ℝ)) ^ 2) :=
          Summable.tsum_le_tsum hterm ((summable_nat_add_iff N).mpr hsum)
            (hsum.mul_left ((x / 2) ^ (2 * N) / ((N.factorial : ℝ)) ^ 2))
      _ = (x / 2) ^ (2 * N) / ((N.factorial : ℝ)) ^ 2 * besselI0 x := by
          rw [tsum_mul_left, ← hb]
  linarith [hsplit, htail, hb.le, hb.ge]

@[blueprint
  "bklnw-thm_16"
  (title := "Theorem 16")
  (statement := /-- Let
  $0 < \varepsilon < 10^{-3}$, $c \geq 3$,
  $x_0 \geq 100$ and $\alpha \in [0, 1)$
  such that the inequality
  $$ B_0 := \frac{\varepsilon e^{-\varepsilon}
  x_0 |\nu_c(\alpha)|}
  {2(\mu_c)_+(\alpha)} > 1 $$
  holds. We denote the zeros of the
  Riemann zeta function by
  $\rho = \beta + i\gamma$ with
  $\beta, \gamma \in \mathbb{R}$.
  Then, if $\beta = \frac{1}{2}$ holds for
  $0 < \gamma \leq \frac{c}{\varepsilon}$,
  the inequality
  $$ |\psi(x) - x| \leq x e^{\varepsilon\alpha}
  (\mathcal{E}_1 + \mathcal{E}_2
  + \mathcal{E}_3) $$
  holds for all
  $x \geq e^{\varepsilon\alpha} x_0$, where
  \begin{align*}
  \mathcal{E}_1 &= e^{2\varepsilon}
  \log(e^\varepsilon x_0)
  \left[\frac{2\varepsilon|\nu_c(\alpha)|}
  {\log B_0}
  + \frac{2.01\varepsilon}{\sqrt{x_0}}
  + \frac{\log\log(2x_0^2)}{2x_0}\right]
  + e^{\varepsilon\alpha} - 1, \\
  \mathcal{E}_2 &= 0.16
  \frac{1 + x_0^{-1}}{\sinh c}
  e^{0.71\sqrt{c\varepsilon}}
  \log\left(\frac{c}{\varepsilon}\right),
  \quad \text{and} \\
  \mathcal{E}_3 &= \frac{2}{\sqrt{x_0}}
  \sum_{0 < \gamma < \frac{c}{\varepsilon}}
  \frac{\ell_{c,\varepsilon}(\gamma)}{\gamma}
  + \frac{2}{x_0}.
  \end{align*}
  The $\nu_c(\alpha) = \nu_{c,1}(\alpha)$ and
  $\mu_c(\alpha) = \mu_{c,1}(\alpha)$ where
  $\nu_{c,\varepsilon}(\alpha)$ and
  $\mu_{c,\varepsilon}(\alpha)$ are
  defined by \cite[p.~2490]{Buthe2}. -/)
  (proof := /-- This is
  \cite[Theorem 1]{Buthe2}. -/)
  (latexEnv := "theorem")]
theorem bklnw_thm_16 (ε c x₀ α : ℝ)
    (hε : 0 < ε ∧ ε < 1e-3)
    (hc : 3 ≤ c)
    (hx₀ : 100 ≤ x₀)
    (hα : 0 ≤ α ∧ α < 1)
    (hB0 : 2 * max (μ c 1 α) 0 <
      ε * rexp (-ε) * x₀ * |ν c 1 α|)
    (hRH : riemannZeta.RH_up_to (c / ε))
    (x : ℝ)
    (hx : x ≥ rexp (ε * α) * x₀) :
    let E₁ :=
      rexp (2 * ε) * log (rexp ε * x₀) *
        (2 * ε * |ν c 1 α| /
          log ((ε * rexp (-ε) * x₀ *
            |ν c 1 α|) / (2 * max (μ c 1 α) 0)) +
        2.01 * ε / sqrt x₀ +
        log (log (2 * x₀ ^ 2)) /
          (2 * x₀)) +
      exp (ε * α) - 1
    let E₂ :=
      0.16 * (1 + x₀ ^ (-1 : ℝ)) / sinh c *
        exp (0.71 * sqrt (c * ε)) *
        log (c / ε)
    let E₃ :=
      2 / sqrt x₀ *
        riemannZeta.zeroes_sum (Set.Icc 0 1)
          (Set.Ioo 0 (c / ε))
          (fun ρ ↦ ℓ c ε ρ.im / ρ.im) +
      2 / x₀
    Eψ x ≤ exp (ε * α) * (E₁ + E₂ + E₃) := by
  sorry

blueprint_comment /--
Note: This thesis of Bhattacharjee \cite{bhattacharjee2023survey} will be a good resource
when formalizing this result.
-/

@[blueprint
  "bknlw-theorem-2"
  (title := "Theorem 2")
  (statement := /-- If $b>0$ then
  $|\psi(x) - x| \leq \varepsilon(b) x$
  for all $x \geq \exp(b)$, where
  $\varepsilon$ is as in
  \cite[Table 8]{BKLNW}. -/)
  (latexEnv := "theorem")
  (proof := /-- Values for
  $20 \leq b \leq 2000$ are computed using
  Theorem \ref{bklnw-thm-16}, and values for
  $2500 \leq b \leq 25000$ are computed as
  using Theorem \ref{bklnw-thm-13}.
  For $b > 25000$ we use
  Theorem \ref{bklnw-thm-14}. -/)]
theorem theorem_2 : ∀ b > 0, ∀ x ≥ exp b,
    |ψ x - x| ≤ table_8_ε b * x := by
  sorry

@[blueprint
 "bklnw-cor_15_1_alt"
  (title := "Corollary 15.1, alternative version")
  (statement := /-- Let $b$ be a positive constant
  such that $\log 11 < b \leq 19 \log(10)$.
  Then we have
  $$ \left|\frac{\psi(x) - x}{x}\right|
  \leq \max\left\{\frac{0.94}{e^{\frac{b}{2}}},
  1.93378 \cdot 10^{-8}\right\}
  \quad \text{for all } x \geq e^b. $$
   -/)
  (proof := /-- From Table 8 we have
  $\varepsilon(19 \log 10)
  = 1.93378 \cdot 10^{-8}$.
  Now apply Corollary \ref{bklnw-cor_15_1}
  and Theorem \ref{bklnw-theorem-2}. -/)
  (latexEnv := "corollary")
  (discussion := 775)]
theorem bklnw_cor_15_1' (b : ℝ)
    (hb1 : log 11 < b)
    (hb2 : b ≤ 19 * log 10) :
    ∀ x ≥ exp b,
      Eψ x ≤
        max (0.94 / exp (b / 2))
          (1.93378e-8 * table_8_margin) := by
  intro x hx
  grw [bklnw_cor_15_1 b hb1 hb2 table_8_ε
    (fun b₀ hb₀ x hx ↦ by
      grw [Eψ,
        div_le_iff₀
          (lt_of_lt_of_le (by positivity) hx),
        theorem_2 b₀ hb₀ x hx]) x hx]
  apply max_le_max_left
  suffices 43 < 19 * Real.log 10 ∧
      19 * Real.log 10 < 44 by
    grw [table_8_ε.le_simp (19 * log 10)
      (by grind)]
    grind [table_8_ε']
  constructor <;>
    nlinarith [LogTables.log_10_gt,
      LogTables.log_10_lt]

end BKLNW_app
