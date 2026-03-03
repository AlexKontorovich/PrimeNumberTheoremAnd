import Architect
import PrimeNumberTheoremAnd.PrimaryDefinitions

blueprint_comment /--
\section{The estimates of Fiori, Kadiri, and Swidinsky}
-/

blueprint_comment /--
In this section we establish the primary results of Fiori, Kadiri, and Swidinsky \cite{FKS}.

TODO: reorganize this blueprint and add proofs.
-/

open Real MeasureTheory Chebyshev

namespace FKS

structure Inputs where
  b₁ : ℝ
  b₂ : ℝ
  b₃ : ℝ
  hRvM : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃
  ZDB : zero_density_bound
  H₀ : ℝ
  hH₀ : riemannZeta.RH_up_to H₀
  R : ℝ
  hR : riemannZeta.classicalZeroFree R
  S₀ : ℝ
  T₀ : ℝ
  hS₀T₀ : riemannZeta.zeroes_sum Set.univ (Set.Ioo 0 T₀) (fun ρ ↦ 1 / ρ.im) < S₀

def table_1 : List (ℝ × ℝ) :=
  [(100, 0.5922435112),
    (1000, 2.0286569752),
    (10000, 4.3080354951),
    (100000, 7.4318184970),
    (1000000, 11.3993199147),
    (10000000, 16.2106480369),
    (100000000, 21.8657999924),
    (1000000000, 28.3647752011),
    (10000000000, 35.7075737123),
    (30610046000, 39.5797647802)]

theorem table_1_prop {T₀ S₀ : ℝ} (h : (T₀, S₀) ∈ table_1) :
    riemannZeta.zeroes_sum Set.univ (Set.Ioo 0 T₀) (fun ρ ↦ 1 / ρ.im) < S₀ := by sorry


def table_8 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) := [
    (0.60, 0.65, 0.2456, 0.3089, 0.3405, 8.0587, 3.7669, 11.3285, 5.2954),
    (0.65, 0.70, 0.2167, 0.3089, 0.3399, 10.3373, 4.8415, 10.4569, 4.8975),
    (0.70, 0.75, 0.1879, 0.3089, 0.3391, 13.1505, 6.1727, 9.5853, 4.4992),
    (0.75, 0.80, 0.1595, 0.3089, 0.3383, 16.5704, 7.7979, 8.7136, 4.1006),
    (0.80, 0.81, 0.1538, 0.3089, 0.3381, 17.3322, 8.1610, 7.8423, 3.6926),
    (0.81, 0.82, 0.1482, 0.3090, 0.3379, 18.1208, 8.5373, 7.6679, 3.6126),
    (0.82, 0.83, 0.1426, 0.3090, 0.3377, 18.9362, 8.9269, 7.4935, 3.5326),
    (0.83, 0.84, 0.1370, 0.3090, 0.3374, 19.7785, 9.3298, 7.3192, 3.4526),
    (0.84, 0.85, 0.1314, 0.3090, 0.3372, 20.6478, 9.7461, 7.1448, 3.3725),
    (0.85, 0.86, 0.1259, 0.3091, 0.3370, 21.5438, 10.1759, 6.9704, 3.2924),
    (0.86, 0.87, 0.1204, 0.3091, 0.3368, 22.4663, 10.6191, 6.7960, 3.2123),
    (0.87, 0.88, 0.1150, 0.3092, 0.3365, 23.4149, 11.0755, 6.6216, 3.1321),
    (0.88, 0.89, 0.1095, 0.3092, 0.3363, 24.3889, 11.5450, 6.4473, 3.0519),
    (0.89, 0.90, 0.1041, 0.3093, 0.3360, 25.3877, 12.0272, 6.2729, 2.9717),
    (0.90, 0.91, 0.09880, 0.3093, 0.3357, 26.4101, 12.5220, 6.0984, 2.8915),
    (0.91, 0.92, 0.09350, 0.3094, 0.3354, 27.4552, 13.0287, 5.9240, 2.8112),
    (0.92, 0.93, 0.08830, 0.3095, 0.3351, 28.5213, 13.5468, 5.7496, 2.7309),
    (0.93, 0.94, 0.08310, 0.3096, 0.3348, 29.6068, 14.0757, 5.5752, 2.6506),
    (0.94, 0.95, 0.07810, 0.3097, 0.3345, 30.7098, 14.6145, 5.4007, 2.5702),
    (0.95, 0.96, 0.07310, 0.3098, 0.3341, 31.8279, 15.1623, 5.2263, 2.4897),
    (0.96, 0.97, 0.06820, 0.3100, 0.3338, 32.9585, 15.7181, 5.0518, 2.4093),
    (0.97, 0.98, 0.06340, 0.3101, 0.3334, 34.0986, 16.2805, 4.8774, 2.3287),
    (0.98, 0.99, 0.05870, 0.3103, 0.3330, 35.2450, 16.8481, 4.7029, 2.2481),
    (0.99, 1.0, 0.05410, 0.3105, 0.3326, 36.3939, 17.4194, 4.5284, 2.1675),
    (0.60, 0.70, 0.2167, 0.3117, 0.3434, 7.9115, 3.6668, 11.3303, 5.2513),
    (0.70, 0.80, 0.1595, 0.3117, 0.3418, 13.8214, 6.4369, 9.5869, 4.4648),
    (0.80, 0.81, 0.1539, 0.3118, 0.3416, 14.5818, 6.7949, 7.8444, 3.6554),
    (0.81, 0.82, 0.1483, 0.3118, 0.3414, 15.3770, 7.1697, 7.6700, 3.5762),
    (0.82, 0.83, 0.1427, 0.3118, 0.3412, 16.2078, 7.5617, 7.4957, 3.4971),
    (0.83, 0.84, 0.1371, 0.3119, 0.3410, 17.0751, 7.9713, 7.3213, 3.4179),
    (0.84, 0.85, 0.1315, 0.3119, 0.3407, 17.9796, 8.3991, 7.1469, 3.3387),
    (0.85, 0.86, 0.1260, 0.3119, 0.3405, 18.9219, 8.8453, 6.9725, 3.2594),
    (0.86, 0.87, 0.1205, 0.3119, 0.3403, 19.9027, 9.3103, 6.7982, 3.1801),
    (0.87, 0.88, 0.1150, 0.3120, 0.3400, 20.9223, 9.7945, 6.6238, 3.1008),
    (0.88, 0.89, 0.1096, 0.3120, 0.3398, 21.9809, 10.2980, 6.4494, 3.0215),
    (0.89, 0.90, 0.1042, 0.3121, 0.3395, 23.0788, 10.8209, 6.2750, 2.9422),
    (0.90, 0.91, 0.09890, 0.3121, 0.3392, 24.2157, 11.3635, 6.1006, 2.8628),
    (0.91, 0.92, 0.09360, 0.3122, 0.3389, 25.3914, 11.9256, 5.9261, 2.7833),
    (0.92, 0.93, 0.08840, 0.3123, 0.3386, 26.6053, 12.5071, 5.7517, 2.7039),
    (0.93, 0.94, 0.08320, 0.3124, 0.3383, 27.8566, 13.1078, 5.5773, 2.6244),
    (0.94, 0.95, 0.07810, 0.3125, 0.3379, 29.1440, 13.7273, 5.4028, 2.5448),
    (0.95, 0.96, 0.07310, 0.3126, 0.3376, 30.4660, 14.3650, 5.2284, 2.4653),
    (0.96, 0.97, 0.06820, 0.3128, 0.3372, 31.8207, 15.0203, 5.0539, 2.3856),
    (0.97, 0.98, 0.06340, 0.3129, 0.3368, 33.2059, 15.6924, 4.8794, 2.3059),
    (0.98, 0.99, 0.05870, 0.3131, 0.3364, 34.6187, 16.3800, 4.7049, 2.2262),
    (0.99, 1.0, 0.05420, 0.3133, 0.3360, 36.0559, 17.0819, 4.5304, 2.1464)]

@[blueprint
  "fks-theorem-2-7"
  (title := "FKS Theorem 2.7")
  (statement := /--
    Let $H_0$ denote a verification height for RH.  Let $10^9/H_0≤ k \leq 1$, $t > 0$,
    $H \in [1002, H_0)$, $α > 0$, $δ ≥ 1$, $\eta_0 = 0.23622$, $1 + \eta_0 \leq \mu \leq 1+\eta$,
    and $\eta \in (\eta_0, 1/2)$ be fixed. Let $\sigma > 1/2 + d / \log H_0$.  Then for any
    $T \geq H_0$, one has
    $$ N(\sigma,T) \leq (T-H) \log T / (2\pi d) *
      \log ( 1 + CC_1(\log(kT))^{2\sigma} (\log T)^{4(1-\sigma)} T^{8/3(1-\sigma)} / (T-H) )
      + CC_2 * \log^2 T / 2 \pi d$$
    and
    $$ N(\sigma,T) \leq \frac{CC_1}{2\pi d} (\log kT)^{2\sigma} (\log T)^{5-4*\sigma}
      T^{8/3(1-\sigma)} + CC_2 * \log^2 T / 2 \pi d$$.
  -/)]
theorem theorem_2_7 (I : Inputs) {k δ α d η₀ η μ σ H T : ℝ}
    (hk : k ∈ Set.Icc ((10 ^ 9) / I.H₀) 1)
    (hα : α > 0)
    (hδ : δ ≥ 1)
    (hη₀ : η₀ = 0.23622)
    (hμ : μ ∈ Set.Icc (1 + η₀) (1 + η))
    (hη : η ∈ Set.Ioo η₀ 0.5)
    (hσ : σ > 0.5 + d / log I.H₀)
    (hH : H ∈ Set.Ico 1002 I.H₀)
    (hT : T ≥ I.H₀) :
    riemannZeta.N' σ T ≤ ((T - H) * log T) / (2 * π * d) *
      log (1 + KLN.CC₁ I.H₀ α d δ k H σ * (log (k * T)) ^ (2 * σ) *
        (log T) ^ (4 * (1 - σ)) * T ^ (8 / 3 * (1 - σ)) / (T - H)) +
      KLN.CC₂ I.H₀ d η k H μ σ * (log T) ^ 2 / (2 * π * d)
    ∧
    riemannZeta.N' σ T ≤ KLN.CC₁ I.H₀ α d δ k H σ * (log (k * T)) ^ (2 * σ) *
      (log T) ^ (5 - 4 * σ) * T ^ (8 / 3 * (1 - σ)) / (2 * π * d) +
      KLN.CC₂ I.H₀ d η k H μ σ * (log T) ^ 2 / (2 * π * d) := by sorry


@[blueprint
  "fks-corollary-2-9"
  (title := "FKS Corollary 2.9")
  (statement := /--
    For each $\sigma_1, \sigma_2, \tilde c_1, \tilde c_2$ given in Table 8, we have
    $N(\sigma,T) \leq \tilde c_1 T^{p(\sigma)} \log^{q(\sigma)} + \tilde c_2 \log^2 T$ for
    $\sigma_1 \leq \sigma \leq \sigma_2$ with $p(\sigma) = 8/3 (1-\sigma)$ and $q(σ) = 5-2\sigma$.
  -/)]
noncomputable def corollary_2_9 {σ₁ σ₂ α δ d CC_1 c₁ CC_2 c₂ : ℝ}
    (h : (σ₁, σ₂, α, δ, d, CC_1, c₁, CC_2, c₂) ∈ table_8) : zero_density_bound := {
  T₀ := 3e12
  σ_range := Set.Icc σ₁ σ₂
  c₁ σ := c₁
  c₂ σ := c₂
  p σ := 8 / 3 * (1 - σ)
  q σ := 5 - 2 * σ
  bound := by sorry
}

/-- Need to merge all the individual estimates above into one single estimate -/
noncomputable def corollary_2_9_merged : zero_density_bound := {
  T₀ := 3e12
  σ_range := Set.Icc 0.6 1
  c₁ σ := sorry
  c₂ σ := sorry
  p σ := 8 / 3 * (1 - σ)
  q σ := 5 - 2 * σ
  bound := by sorry
}


noncomputable def Inputs.default : Inputs := {
  b₁ := 0.1038
  b₂ := 0.2573
  b₃ := 9.3675
  hRvM := HSW.main_theorem
  ZDB := corollary_2_9_merged
  H₀ := 3e12
  hH₀ := PT_theorem_1
  R := 5.5666305
  hR := MT_theorem_1
  S₀ := 39.5797647802
  T₀ := 30610046000
  hS₀T₀ := table_1_prop (by unfold table_1; aesop)
}



noncomputable def Inputs.RvM (I : Inputs) (U : ℝ) : ℝ := riemannZeta.RvM I.b₁ I.b₂ I.b₃ U

noncomputable def Inputs.B₁ (I : Inputs) (U V : ℝ) : ℝ :=
    (1 / (2 * π) + ((I.b₁ * log U) + I.b₂) / (U * (log U) * (log (U / (2 * π))))) *
      (log (V / U) * (log (sqrt (V * U) / (2 * π)))) + 2 * (I.RvM U) / U

@[blueprint
  "fks-lemma-2-1"
  (title := "FKS Lemma 2.1")
  (statement := /--
    If $|N(T) - (T/2\pi \log(T/2\pi e) + 7/8)| \leq R(T)$ then
    $\sum_{U \leq \gamma < V} 1/\gamma \leq B_1(U,V)$.
  -/)]
theorem lemma_2_1 (I : Inputs) {U V : ℝ} (hU : U ≥ 1) (hV : V ≥ U) :
    riemannZeta.zeroes_sum Set.univ (Set.Ico U V) (fun ρ ↦ 1 / ρ.im) ≤ I.B₁ U V := by sorry

@[blueprint
  "fks-corollary_2_3"
  (title := "FKS Corollary 2.3")
  (statement := /--
    For each pair $T_0,S_0$ in Table 1 we have, for all $V > T_0$,
    $\sum_{0 < \gamma < V} 1/\gamma < S_0 + B_1(T_0,V)$.
  -/)]
theorem corollary_2_3 (I : Inputs) {V : ℝ} (hV : V > I.T₀) :
    riemannZeta.zeroes_sum Set.univ (Set.Ioo 0 V) (fun ρ ↦ 1 / ρ.im) < I.S₀ + I.B₁ I.T₀ V := by
  sorry

noncomputable def s₀ (σ U V : ℝ) :=
    riemannZeta.zeroes_sum (Set.Ico σ 1) (Set.Ico U V) (fun ρ ↦ 1 / ρ.im)

noncomputable def _root_.Real.Gamma.incomplete (s : ℝ) (x : ℝ) : ℝ :=
    ∫ t in Set.Ioi x, exp (-t) * t ^ (s - 1)

noncomputable def _root_.Complex.Gamma.incomplete (s : ℂ) (x : ℝ) : ℂ :=
    ∫ t in Set.Ioi x, exp (-t) * t ^ (s - 1)

noncomputable def Inputs.B₀ (I : Inputs) (σ : ℝ) (U V : ℝ) : ℝ :=
    (I.ZDB.c₁ σ) * (log V) ^ (I.ZDB.q σ) / V ^ (1 - (I.ZDB.p σ)) +
      (I.ZDB.c₂ σ) * (log V) ^ 2 / V +
      (I.ZDB.c₁ σ / (1 - (I.ZDB.p σ)) ^ (I.ZDB.q σ + 1)) *
        (Gamma.incomplete (I.ZDB.q σ + 1) ((1 - I.ZDB.p σ) * (log U)) -
          Gamma.incomplete (I.ZDB.q σ + 1) ((1 - I.ZDB.p σ) * (log V))) +
      (I.ZDB.c₂ σ) * (Gamma.incomplete 3 ((log U)) - Gamma.incomplete 3 ((log V)))

@[blueprint
  "fks-lemma-2-5"
  (title := "FKS Lemma 2.5")
  (statement := /--
    Let $T_0 \geq 2$ and $\gamma > 0$.  Assume that there exist $c_1, c_2, p, q, T_0$ for which
    one has a zero density bound.  Assume $\sigma \geq 5/8$ and $T_0 \leq U < V$.  Then
    $s_0(σ,U,V) \leq B_0(\sigma,U,V)$.
  -/)]
theorem lemma_2_5 (I : Inputs) {σ U V : ℝ}
    (hT₀ : I.ZDB.T₀ ≥ 2)
    (hσ : σ ≥ 5 / 8)
    (hσ' : σ ∈ I.ZDB.σ_range)
    (hU : U ≥ I.ZDB.T₀)
    (hV : V > U) :
    s₀ σ U V ≤ I.B₀ σ U V := by sorry

@[blueprint
  "fks-remark-2-6-a"
  (title := "FKS Remark 2-6-a")
  (statement := /-- $\Gamma(3,x) = (x^2 + 2(x+1)) e^{-x}$. -/)]
theorem remark_2_6_a (x : ℝ) (hx : 0 ≤ x) :
    Gamma.incomplete 3 x = (x ^ 2 + 2 * (x + 1)) * exp (-x) := by
  have integrableOn_Ioi (s : ℝ) {a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
      IntegrableOn (fun t ↦ exp (-t) * t ^ (s - 1)) (Set.Ioi a) :=
    (GammaIntegral_convergent hs).mono_set (Set.Ioi_subset_Ioi ha)
  have recurrence (s : ℝ) (hs : 0 < s) {y : ℝ} (hy : 0 ≤ y) :
      Gamma.incomplete (s + 1) y = y ^ s * exp (-y) + s * Gamma.incomplete s y := by
    unfold Gamma.incomplete
    conv_lhs => arg 2; intro t; rw [mul_comm]
    norm_num
    rw [integral_Ioi_mul_deriv_eq_deriv_mul (u := fun t ↦ t ^ s) (v := fun t ↦ -exp (-t))
        (u' := fun t ↦ s * t ^ (s - 1)) (v' := fun t ↦ exp (-t))
        (a' := -y ^ s * exp (-y)) (b' := 0)]
    · ring_nf
      simp [sub_eq_add_neg, integral_neg, ← integral_const_mul, mul_assoc, mul_comm]
    · exact fun t ht ↦ hasDerivAt_rpow_const (by grind)
    · exact fun t _ ↦ by convert (hasDerivAt_neg t).exp.neg using 1; norm_num
    · simpa [mul_comm] using integrableOn_Ioi (s + 1) (by grind) (by grind : 0 ≤ y)
    · refine ((integrableOn_Ioi s hs hy).const_mul (-s)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _; norm_num; ring
    · convert Filter.Tendsto.mul
        (Filter.Tendsto.rpow (Filter.tendsto_id.mono_left inf_le_left) tendsto_const_nhds _)
        (Filter.Tendsto.neg (continuous_exp.continuousAt.tendsto.comp
          (Filter.Tendsto.neg (Filter.tendsto_id.mono_left inf_le_left)))) using 1 <;> aesop
    · have h_lim : Filter.Tendsto (fun t : ℝ ↦ t ^ s * exp (-t)) Filter.atTop (nhds 0) := by
        apply squeeze_zero_norm' _ (tendsto_pow_mul_exp_neg_atTop_nhds_zero ⌈s⌉₊)
        filter_upwards [Filter.eventually_gt_atTop 1] with t ht
        rw [norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right
          (by simpa using rpow_le_rpow_of_exponent_le ht.le <| Nat.le_ceil s) (by positivity)
      convert h_lim.neg using 2 <;> norm_num
  rw [show (3 : ℝ) = 2 + 1 by norm_num, recurrence 2 (by norm_num) hx,
      show (2 : ℝ) = 1 + 1 by norm_num, recurrence 1 (by norm_num) hx]
  norm_num [Gamma.incomplete, integral_exp_neg_Ioi x]; ring

@[blueprint
  "fks-remark-2-6-b"
  (title := "FKS Remark 2-6-b")
  (statement := /-- For $s>1$, one has $\Gamma(s,x) \sim x^{s-1} e^{-x}$. -/)]
theorem remark_2_6_b (s : ℝ) (h : s > 1) :
    Filter.Tendsto (fun x ↦ Gamma.incomplete s x / (x ^ (s - 1) * exp (-x)))
      Filter.atTop (nhds 1) := by
  unfold Gamma.incomplete
  have h_eq : ∀ x > 0, ∫ t in Set.Ioi x, Real.exp (-t) * t ^ (s - 1) = x ^ (s - 1) * Real.exp (-x) * ∫ u in Set.Ioi 0, Real.exp (-u) * (1 + u / x) ^ (s - 1) := by
    intro x hx_pos
    have h_eq : ∫ t in Set.Ioi x, Real.exp (-t) * t ^ (s - 1) = ∫ u in Set.Ioi 0, Real.exp (-(x + u)) * (x + u) ^ (s - 1) := by
      rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ]
      simp +decide [ Set.indicator ]
      rw [ ← MeasureTheory.integral_add_right_eq_self _ x ] ; congr ; ext y ; split_ifs <;> ring <;> aesop
    rw [ h_eq, ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => _ ; rw [ show x + u = x * ( 1 + u / x ) by rw [ mul_add, mul_div_cancel₀ _ hx_pos.ne' ] ; ring ] ; rw [ Real.mul_rpow ( by positivity ) ( by linarith [ hu.out, div_nonneg hu.out.le hx_pos.le ] ) ] ; ring
    norm_num [ sub_eq_add_neg, Real.exp_add, mul_assoc, mul_comm x, hx_pos.ne' ] ; ring
  have h_conv : Filter.Tendsto (fun x => ∫ u in Set.Ioi 0, Real.exp (-u) * (1 + u / x) ^ (s - 1)) Filter.atTop (nhds (∫ u in Set.Ioi 0, Real.exp (-u))) := by
    refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _
    refine' fun u => Real.exp ( -u ) * ( 1 + u ) ^ ( s - 1 )
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.continuous_exp.measurable.comp measurable_neg ) ( by exact Measurable.pow_const ( by exact measurable_const.add ( measurable_id'.div_const _ ) ) _ ) )
    · filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn
      filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( Real.rpow_nonneg ( by linarith [ hx.out, div_nonneg hx.out.le ( by linarith : 0 ≤ n ) ] ) _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( by linarith [ hx.out, div_nonneg hx.out.le ( by linarith : 0 ≤ n ) ] ) ( by linarith [ hx.out, div_le_self hx.out.le ( by linarith : 1 ≤ n ) ] ) ( by linarith ) ) ( Real.exp_pos _ |> le_of_lt )
    · have h_conv : MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * (1 + u) ^ (s - 1)) (Set.Ioi 0) := by
        have : MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * (1 + u) ^ (s - 1)) (Set.Ioi 1) := by
          have : MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * (2 * u) ^ (s - 1)) (Set.Ioi 1) := by
            have : MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * u ^ (s - 1)) (Set.Ioi 1) := by
              have h_conv : ∫ u in Set.Ioi 0, Real.exp (-u) * u ^ (s - 1) = Real.Gamma s := by
                rw [ Real.Gamma_eq_integral ( by linarith ) ]
              exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_conv; rw [ MeasureTheory.integral_undef h_conv ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one )
            have : MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * u ^ (s - 1) * 2 ^ (s - 1)) (Set.Ioi 1) := by
              exact this.mul_const _
            refine' this.congr_fun ( fun u hu => by rw [ Real.mul_rpow ( by positivity ) ( by linarith [ hu.out ] ) ] ; ring ) measurableSet_Ioi
          refine' this.mono' _ _
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.continuous_exp.measurable.comp measurable_neg ) ( by exact Measurable.pow_const ( measurable_const.add measurable_id' ) _ ) )
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( Real.rpow_nonneg ( by linarith [ hu.out ] ) _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( by linarith [ hu.out ] ) ( by linarith [ hu.out ] ) ( by linarith [ hu.out ] ) ) ( Real.exp_pos _ |> le_of_lt )
        have : MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * (1 + u) ^ (s - 1)) (Set.Ioc 0 1) := by
          exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun u hu => by exact ContinuousAt.mul ( Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg continuousAt_id ) <| ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hu.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self
        convert MeasureTheory.IntegrableOn.union this ‹IntegrableOn ( fun u => Real.exp ( -u ) * ( 1 + u ) ^ ( s - 1 ) ) ( Set.Ioi 1 ) volume› using 1 ; norm_num
      exact h_conv
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using le_trans ( Filter.Tendsto.mul tendsto_const_nhds <| Filter.Tendsto.rpow ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop Filter.tendsto_id ) tendsto_const_nhds <| Or.inl <| by linarith [ hx.out ] ) <| by norm_num
  exact Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx; rw [ h_eq x hx, mul_div_cancel_left₀ _ ( by positivity ) ] ) ( h_conv.trans ( by rw [ integral_exp_neg_Ioi ] ; norm_num ) )



@[blueprint
  "fks-theorem-3-1"
  (title := "FKS Theorem 3.1")
  (statement := /--
    Let $x > e^{50}$ and $50 < T < x$.  Then
    $E_\psi(x) \leq \sum_{|\gamma| < T} |x^{\rho-1}/\rho| + 2 \log^2 x / T$.
  -/)]
theorem theorem_3_1 {x T : ℝ} (hx : x > exp 50) (hodd : ∃ X, Odd X ∧ x = X / 2)
    (hT : T ∈ Set.Ioo 50 x) :
    Eψ x ≤ riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Ioo (-T) T)
      (fun ρ ↦ ‖x ^ (ρ - 1) / ρ‖) + 2 * (log x) ^ 2 / T := by sorry

@[blueprint
  "fks-theorem-3-2"
  (title := "FKS Theorem 3.2")
  (statement := /--
    For any $\alpha \in (0,1/2]$ and $\omega \in [0,1]$ there exist $M, x_M$ such that for
    $\max(51, \log x) < T < (x^\alpha-2)/5$ and some $T^* \in [T, 2.45 T]$,
    $$ |\psi(x) - (x - \sum_{|\gamma| \leq T^*} x^\rho/\rho)| ≤ M x / T * log^{1-\omega} x  $$
    for all $x ≥ x_M$.
  -/)]
theorem theorem_3_2 (α ω : ℝ) (hα : α ∈ Set.Ioc 0 (1 / 2)) (hω : ω ∈ Set.Icc 0 1) :
    ∃ M xM : ℝ, ∀ x, ∀ T ∈ Set.Ioo (max 51 (log x)) ((x ^ α - 2) / 5),
    ∃ Tstar ∈ Set.Icc T (2.45 * T), ∀ x ≥ xM,
    ‖ψ x - (x - riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Ioo (-Tstar) Tstar)
      (fun ρ ↦ x ^ ρ / ρ))‖ ≤ M * x / T * (log x) ^ (1 - ω) := by sorry

noncomputable def ε₁ (x T : ℝ) : ℝ := 2 * (log x) ^ 2 / T

@[blueprint
  "fks-proposition-3-4"
  (title := "FKS Proposition 3.4")
  (statement := /--
    Let $x > e^{50}$ and $3 \log x < T < \sqrt{x}/3$.  Then
    $E_\psi(x) ≤ \sum_{|\gamma| < T} |x^{\rho-1}/\rho| + 2 \log^2 x / T$.
  -/)]
theorem proposition_3_4 {x T : ℝ} (hx : x > exp 50)
    (hT : T ∈ Set.Ioo (3 * log x) (sqrt x / 3)) :
    Eψ x ≤ riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Ioo (-T) T)
      (fun ρ ↦ ‖x ^ (ρ - 1) / ρ‖) + ε₁ x T := by sorry

noncomputable def riemannZeta.Sigma (T x a b : ℝ) : ℝ :=
    2 * (riemannZeta.zeroes_sum (Set.Ico a b) (Set.Ioo 0 T) (fun ρ ↦ x ^ (ρ.re - 1) / ρ.im))

noncomputable def ε₂ (I : Inputs) (x σ₁ T : ℝ) : ℝ :=
    2 * x ^ (-0.5 : ℝ) * (I.S₀ + I.B₁ I.T₀ T) +
      (x ^ (σ₁ - 1) - x ^ (-0.5 : ℝ)) * (I.B₁ I.H₀ T)

@[blueprint
  "fks-proposition-3-6"
  (title := "FKS Proposition 3.6")
  (statement := /--
    Let $\sigma_1 \in (1/2,1)$ and let $(T_0,S_0)$ be taken from Table 1.  Then
    $\Sigma_0^{\sigma_1} ≤ 2 x^{-1/2} (S_0 + B_1(T_0,T)) + (x_1^{\sigma_1-1} - x^{-1/2}) B_1(H_0,T)$.
  -/)]
theorem proposition_3_6 (I : Inputs) {σ₁ T x : ℝ} (hσ_1 : σ₁ ∈ Set.Icc 0.5 1) (hT : T > I.T₀)
    (x : ℝ) :
    riemannZeta.Sigma T x 0 σ₁ ≤ ε₂ I x σ₁ T := by sorry

noncomputable def Hσ (H₀ R σ : ℝ) : ℝ := max H₀ (exp (1 / (R * (1 - σ))))

theorem riemannZeta.Hσ_zeroes (H₀ R σ : ℝ) (hH₀ : riemannZeta.RH_up_to H₀)
    (hR : riemannZeta.classicalZeroFree R) :
    riemannZeta.N' σ (Hσ H₀ R σ) = 0 := by sorry

@[blueprint
  "fks-eq13"
  (title := "FKS equation (3.13)")
  (statement := /--
    $\Sigma_a^b = 2 * \sum_{H_a ≤ \gamma < T; a \leq \beta < b} \frac{x^{\beta-1}}{\gamma}$.
  -/)]
theorem eq_13 {H₀ R a b T x : ℝ} (hH₀ : riemannZeta.RH_up_to H₀)
    (hR : riemannZeta.classicalZeroFree R) :
    riemannZeta.Sigma T x a b = 2 * riemannZeta.zeroes_sum (Set.Ico a b) (Set.Ioc (Hσ H₀ R a) T)
      (fun ρ ↦ x ^ (ρ.re - 1) / ρ.im) := by sorry

noncomputable def σn (σ₁ σ₂ : ℝ) (n N : ℕ) : ℝ := σ₁ + (σ₂ - σ₁) * n / N

noncomputable def Hn (H₀ R σ₁ σ₂ : ℝ) (n N : ℕ) : ℝ := Hσ H₀ R (σn σ₁ σ₂ n N)

@[blueprint
  "fks-remark-3-7"
  (title := "FKS Remark 3.7")
  (statement := /-- If $\sigma < 1 - 1/R \log H_0$ then $H_σ = H_0$. -/)]
theorem remark_3_7 {H₀ R σ : ℝ} (hσ : σ < 1 - 1 / (R * log H₀)) : Hσ H₀ R σ = H₀ := by sorry

theorem remark_3_7' {H₀ R σ : ℝ} (hH₀ : H₀ > 1) (hR : R > 0)
    (hσ : σ < 1 - 1 / (R * log H₀)) : Hσ H₀ R σ = H₀ := by
  unfold Hσ; rw [max_eq_left]
  have hlog := log_pos hH₀
  have hRlog := mul_pos hR hlog
  have h1σ : 1 - σ > 0 := by linarith [div_pos one_pos hRlog]
  have key : 1 / (R * (1 - σ)) < log H₀ := by
    rw [div_lt_iff₀ (mul_pos hR h1σ)]
    calc log H₀ * (R * (1 - σ))
        = R * (1 - σ) * log H₀ := by ring
      _ > R * (1 / (R * log H₀)) * log H₀ :=
          mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left (by linarith) hR) hlog
      _ = 1 := by field_simp
  linarith [exp_strictMono key, exp_log (show H₀ > 0 by linarith)]

noncomputable def ε₃ (I : Inputs) (x σ₁ σ₂ : ℝ) (N : ℕ) (T : ℝ) : ℝ :=
    2 * x ^ (-(1 - σ₁) + (σ₂ - σ₁) / N) * (I.B₀ σ₁ (Hσ I.H₀ I.R σ₁) T) +
      2 * x ^ (1 - σ₁) * (1 - x ^ (-(σ₂ - σ₁) / N)) *
        ∑ n ∈ Finset.Ico 1 N, (I.B₀ (σn σ₁ σ₂ n N) (Hn I.H₀ I.R σ₁ σ₂ n N) T) *
          x ^ ((σ₂ - σ₁) * (n + 1) / N)

@[blueprint
  "fks-proposition-3-8"
  (title := "FKS Proposition 3.8")
  (statement := /--
    Let $N \geq 2$ be an integer.  If $5/8 \leq \sigma_1 < \sigma_2 \leq 1$, $T \geq H_0$, then
    $\Sigma_{\sigma_1}^{\sigma_2} ≤ 2 x^{-(1-\sigma_1)+(\sigma_2-\sigma_1/N)}B_0(\sigma_1,
    H_{\sigma_1}, T) + 2 x^{(1-\sigma_1)} (1 - x^{-(\sigma_2-\sigma_1)/N})
    \sum_{n=1}^{N-1} B_0(\sigma^{(n)}, H^{(n)}, T) x^{(\sigma_2-\sigma_1) (n+1)/N}$.
  -/)]
theorem proposition_3_8 (I : Inputs) (x : ℝ) {σ₁ σ₂ : ℝ} (N : ℕ) (T : ℝ)
    (hσ₁ : σ₁ ∈ Set.Icc (5 / 8) 1) (hσ₂ : σ₂ ∈ Set.Ioc σ₁ 1)
    (hσ : Set.Icc σ₁ σ₂ ⊆ I.ZDB.σ_range) (hT : T ≥ I.H₀) :
    riemannZeta.Sigma T x σ₁ σ₂ ≤ ε₃ I x σ₁ σ₂ N T := by sorry

@[blueprint
  "fks-corollary-3-10"
  (title := "FKS Corollary 3.10")
  (statement := /-- If $\sigma_1 \geq 0.9$ then $\Sigma_{\sigma_1}^{\sigma_2} \leq 0.00125994 x^{\sigma_2-1}$. -/)]
theorem corollary_3_10 {σ₁ σ₂ T x : ℝ} (hσ₁ : σ₁ ∈ Set.Icc 0.9 1) (hσ₂ : σ₂ ∈ Set.Ioc σ₁ 1) :
    riemannZeta.Sigma T x σ₁ σ₂ ≤ 0.00125994 * x ^ (σ₂ - 1) := by sorry

@[blueprint
  "fks-proposition-3-11"
  (title := "FKS Proposition 3.11")
  (statement := /--
    Let $5/8 < \sigma_2 \leq 1$, $t_0 = t_0(\sigma_2,x) = \max(H_{\sigma_2},
    \exp( \sqrt{\log x}/R))$ and $T > 0$.  Let $K \geq 2$ and consider a strictly increasing
    sequence $(t_k)_{k=0}^K$ such that $t_k = T$.  Then
    $\Sigma_{\sigma_2}^1 ≤ 2 N(\sigma_2,T) x^{-1/R\log t_0}/t_0$ and
    $\Sigma_{\sigma_2}^1 ≤ 2 ((\sum_{k=1}^{K-1} N(\sigma_2, t_k)
    (x^{-1/R\log t_{k-1}} / t_{k-1} - x^{-1/(R \log t_k)}/t_k)) +
    x^{-1/R \log t_{K-1}}/t_{K-1} N(\sigma_2,T))$.
  -/)]
theorem proposition_3_11 (I : Inputs) {σ₂ T x : ℝ} (K : ℕ) (hσ₂ : σ₂ ∈ Set.Ioc (5 / 8) 1)
    (t_seq : Fin (K + 2) → ℝ)
    (ht0 : t_seq 0 = max (Hσ I.H₀ I.R σ₂) (exp (sqrt (log x) / I.R)))
    (htK : t_seq (Fin.last (K + 1)) = T) (ht_incr : StrictMono t_seq) :
    riemannZeta.Sigma T x σ₂ 1 ≤
      2 * (riemannZeta.N' σ₂ T) * x ^ (-1 / (I.R * log (t_seq 0))) / (t_seq 0)
    ∧
    riemannZeta.Sigma T x σ₂ 1 ≤ 2 * (∑ k ∈ Finset.Ioo 0 (Fin.last (K + 1)),
      riemannZeta.N' σ₂ (t_seq k) *
        (x ^ (-1 / (I.R * log (t_seq (k - 1)))) / (t_seq (k - 1)) -
          x ^ (-1 / (I.R * log (t_seq k))) / (t_seq k))) +
      x ^ (-1 / (I.R * log (t_seq (Fin.last K).castSucc))) /
        (t_seq (Fin.last K).castSucc) * riemannZeta.N' σ₂ T := by sorry

noncomputable def ε₄ (I : Inputs) (t₀ x σ₂ : ℝ) (K : ℕ) (T : ℝ) : ℝ :=
    let t : Fin (K + 2) → ℝ := fun k ↦ t₀ * (T / t₀) ^ (k / K)
    2 * ∑ k ∈ Finset.Ioo 0 (Fin.last (K + 1)),
      (x ^ (-1 / (I.R * log (t k))) / (t k)) *
        (I.ZDB.N σ₂ (t (k + 1)) - I.ZDB.N σ₂ (t k)) +
      2 * (I.ZDB.N σ₂ (t 1)) * x ^ (-1 / (I.R * log (t 0))) / (t 0)

@[blueprint
  "fks-corollary-3-12"
  (title := "FKS Corollary 3.12")
  (statement := /--
    Let $5/8 < \sigma_2 \leq 1$, $t_0 = t_0(\sigma_2, x) = \max\left(H_{\sigma_2},
    \exp\left(\sqrt{\frac{\log x}{R}}\right)\right)$, $T > t_0$. Let $K \geq 2$,
    $\lambda = (T/t_0)^{1/K}$, and consider $(t_k)_{k=0}^K$ the sequence given by
    $t_k = t_0 \lambda^k$. Then
    \[
    \Sigma^1_{\sigma_2} = 2 \sum_{\substack{0 < \gamma < T \\ \sigma_2 \leq \beta < 1}}
      \frac{x^{\beta-1}}{\gamma} \leq \varepsilon_4(x, \sigma_2, K, T),
    \]
    where
    \[
    \varepsilon_4(x, \sigma_2, K, T) = 2 \sum_{k=1}^{K-1} \frac{x^{-\frac{1}{R \log t_k}}}{t_k}
      \left( \tilde{N}(\sigma_2, t_{k+1}) - \tilde{N}(\sigma_2, t_k) \right) +
      2\tilde{N}(\sigma_2, t_1) \frac{x^{-\frac{1}{R(\log t_0)}}}{t_0},
    \]
    and $\tilde{N}(\sigma, T)$ satisfy (ZDB) $N(\sigma, T) \leq \tilde{N}(\sigma, T)$.
  -/)]
theorem corollary_3_12 (I : Inputs) {σ₂ t₀ T x : ℝ} (K : ℕ) (hσ₂ : σ₂ ∈ Set.Ioc (5 / 8) 1)
    (ht₀ : t₀ = max (Hσ I.H₀ I.R σ₂) (exp (sqrt (log x) / I.R))) (hT : T > t₀)
    (ZDB : zero_density_bound) :
    riemannZeta.Sigma T x σ₂ 1 ≤ ε₄ I t₀ x σ₂ K T := by sorry

@[blueprint
  "fks-proposition-3-14"
  (title := "FKS Proposition 3-14")
  (statement := /--
    Fix $K \geq 2$ and $c > 1$, and set $t_0$, $T$, and $\sigma_2$ as functions of $x$ defined by
    \begin{equation}
    t_0 = t_0(x) = \exp\left(\sqrt{\frac{\log x}{R}}\right), \quad T = t_0^c, \quad \text{and}
      \quad \sigma_2 = 1 - \frac{2}{R \log t_0}.
    \end{equation}
    Then, with $\varepsilon_4(x, \sigma_2, K, T)$ as defined in (3.22), we have that as
    $x \to \infty$,
    \begin{equation}
    \varepsilon_4(x, \sigma_2, K, T) = (1 + o(1)) C
      \frac{(\log t_0)^{3 + \frac{4}{R \log t_0}}}{t_0^2}, \quad \text{with }
      C = 2c_1 e^{\frac{16w_1}{3R}} w_1^3, \text{ and } w_1 = 1 + \frac{c-1}{K},
    \end{equation}
    where $c_1$ is an admissible value for (ZDB) on some interval $[\sigma_1, 1]$. Moreover, both
    $\varepsilon_4(x, \sigma_2, K, T)$ and
    $\frac{\varepsilon_4(x, \sigma_2, K, T) t_0^2}{(\log t_0)^3}$ are decreasing in $x$ for
    $x > \exp(Re^2)$.
  -/)]
theorem proposition_3_14 (I : Inputs) {c : ℝ} (K : ℕ) (hc : c > 1) (hK : K ≥ 2) :
    let t₀ : ℝ → ℝ := fun x ↦ exp (sqrt (log x) / I.R)
    let T : ℝ → ℝ := fun x ↦ (t₀ x) ^ c
    let σ₂ : ℝ → ℝ := fun x ↦ 1 - 2 / (I.R * log (t₀ x))
    let w₁ : ℝ := 1 + (c - 1) / K
    let C := 2 * (I.ZDB.c₁ (σ₂ 1)) * exp (16 * w₁ / (3 * I.R)) * w₁ ^ 3
    let f : ℝ → ℝ := fun x ↦ C * (log (t₀ x)) ^ (3 + 4 / (I.R * log (t₀ x))) / (t₀ x) ^ 2
    Asymptotics.IsEquivalent Filter.atTop (fun x ↦ ε₄ I (t₀ x) x (σ₂ x) K (T x)) f
    ∧ AntitoneOn (fun x ↦ ε₄ I (t₀ x) x (σ₂ x) K (T x)) (Set.Ioi (exp (I.R * exp 2)))
    ∧ AntitoneOn (fun x ↦ (ε₄ I (t₀ x) x (σ₂ x) K (T x)) * (t₀ x) ^ 2 / (log (t₀ x)) ^ 3)
        (Set.Ioi (exp (I.R * exp 2))) := by sorry

noncomputable def ε (I : Inputs) (x₀ σ₂ c : ℝ) (N K : ℕ) : ℝ :=
    let t₀ := max (Hσ I.H₀ I.R σ₂) (exp (sqrt (log x₀) / I.R))
    let T := t₀ ^ c
    ε₁ x₀ T + ε₂ I x₀ 0.9 T + ε₃ I x₀ 0.9 σ₂ N T + ε₄ I t₀ x₀ σ₂ K T

@[blueprint
  "fks-theorem-1-1"
  (title := "FKS Theorem 1.1")
  (statement := /--
    For any $x_0$ with $\log x_0 > 1000$, and all $0.9 < \sigma_2 < 1$, $2 \leq c \leq 30$, and
    $N, K \geq 1$ the formula $\varepsilon(x_0) := \varepsilon(x_0, \sigma_2, c, N, K)$ as defined
    in (4.1) gives an effectively computable bound
    \[
    E_\psi(x) \leq \varepsilon(x_0) \quad \text{for all } x \geq x_0.
    \]
  -/)]
theorem theorem_1_1 (I : Inputs) (x₀ σ₂ c : ℝ) (N K : ℕ) (hlog : log x₀ > 1000)
    (hσ₂ : σ₂ ∈ Set.Ioo 0.9 1) (hc : c ∈ Set.Icc 2 30) (hN : N ≥ 1) (hK : K ≥ 1) :
    ∀ x ≥ x₀, Eψ x ≤ ε I x₀ σ₂ c N K := by sorry

def table_5 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) := [
  (1000, 0.99130, 6.8931e-12, 2.2179e-42, 1.1486e-10, 1.2595e-9, 1.3812e-9),
  (2000, 0.99221, 1.6115e-18, 2.5382e-85, 1.0478e-13, 2.3698e-12, 2.4746e-12),
  (2100, 0.99227, 4.3625e-19, 1.2306e-89, 5.4150e-14, 1.2705e-12, 1.3246e-12),
  (2200, 0.99232, 1.2152e-19, 5.9424e-94, 2.7737e-14, 6.8202e-13, 7.0976e-13),
  (2300, 0.99236, 3.4763e-20, 2.8594e-98, 1.4038e-14, 3.6655e-13, 3.8059e-13),
  (2400, 0.99241, 1.0198e-20, 1.3716e-102, 7.3304e-15, 1.9693e-13, 2.0426e-13),
  (2500, 0.99245, 3.0626e-21, 6.5602e-107, 3.7746e-15, 1.0595e-13, 1.0972e-13),
  (2600, 0.99249, 9.4049e-22, 3.1298e-111, 1.9595e-15, 5.7018e-14, 5.8978e-14),
  (2700, 0.99253, 2.9495e-22, 1.4897e-115, 1.0255e-15, 3.0704e-14, 3.1729e-14),
  (2800, 0.99256, 9.4362e-23, 7.0758e-120, 5.2650e-16, 1.6561e-14, 1.7087e-14),
  (2900, 0.99260, 3.0766e-23, 3.3544e-124, 2.7975e-16, 8.9293e-15, 9.2091e-15),
  (3000, 0.99263, 1.0213e-23, 1.5874e-128, 1.4554e-16, 4.8223e-15, 4.9678e-15),
  (4000, 0.99289, 3.8012e-28, 8.3087e-172, 2.5203e-19, 1.0769e-17, 1.1021e-17),
  (5000, 0.99311, 4.4810e-32, 3.9878e-215, 6.0477e-22, 2.9338e-20, 2.9942e-20),
  (6000, 0.99334, 1.2102e-35, 1.8179e-258, 2.3940e-24, 1.2737e-22, 1.2976e-22),
  (7000, 0.99356, 6.1586e-39, 8.0082e-302, 1.4021e-26, 8.3760e-25, 8.5162e-25),
  (8000, 0.99379, 5.1936e-42, 3.4432e-345, 1.3533e-28, 7.6506e-27, 7.7860e-27),
  (9000, 0.99417, 6.6323e-45, 1.4537e-388, 2.4527e-30, 8.9809e-29, 9.2262e-29),
  (10000, 0.99449, 1.2006e-47, 6.0512e-432, 3.7257e-32, 1.3316e-30, 1.3688e-30),
  (20000, 0.99619, 6.4252e-70, 6.3468e-866, 4.0934e-47, 1.8958e-45, 1.9367e-45),
  (30000, 0.99693, 4.0605e-87, 4.8888e-1300, 1.2153e-58, 6.5467e-57, 6.6682e-57),
  (40000, 0.99736, 1.1531e-101, 3.3291e-1734, 2.0196e-68, 1.3291e-66, 1.3493e-66),
  (50000, 0.99766, 1.6581e-114, 2.1204e-2168, 5.6525e-77, 3.6804e-75, 3.7369e-75),
  (60000, 0.99787, 3.9127e-126, 1.2951e-2602, 8.2972e-85, 6.5977e-83, 6.6806e-83),
  (70000, 0.99804, 7.7353e-137, 7.6841e-3037, 6.2358e-92, 4.8619e-90, 4.9243e-90),
  (80000, 0.99817, 8.2566e-147, 4.4645e-3471, 1.2079e-98, 1.1046e-96, 1.1166e-96),
  (90000, 0.99828, 3.5041e-156, 2.5526e-3905, 6.4784e-105, 6.2867e-103, 6.3515e-103),
  (100000, 0.99838, 4.7299e-165, 1.4411e-4339, 9.8527e-111, 7.7127e-109, 7.8112e-109),
  (200000, 0.99887, 8.7978e-237, 3.2889e-8682, 1.0317e-158, 1.2350e-156, 1.2453e-156),
  (300000, 0.99908, 6.2208e-292, 5.6126e-13025, 1.0986e-195, 2.1996e-193, 2.2106e-193),
  (400000, 0.99921, 1.7897e-338, 8.5065e-17368, 1.5373e-226, 2.1209e-224, 2.1363e-224),
  (500000, 0.99929, 1.6709e-379, 1.2083e-21710, 3.2223e-254, 9.6746e-252, 9.7068e-252),
  (600000, 0.99935, 1.2951e-416, 1.6472e-26053, 3.4804e-279, 1.7998e-276, 1.8032e-276),
  (700000, 0.99940, 9.4139e-451, 2.1829e-30396, 8.0982e-302, 3.1872e-299, 3.1953e-299),
  (800000, 0.99944, 1.5480e-482, 2.8336e-34739, 7.0513e-323, 2.0918e-320, 2.0988e-320),
  (900000, 0.99947, 2.1427e-512, 3.6206e-39082, 5.1196e-343, 2.6418e-340, 2.6470e-340),
  (1000000, 0.99950, 1.2150e-540, 4.5688e-43425, 1.9527e-361, 3.9371e-359, 3.9566e-359)]


@[blueprint
  "fks-theorem-1-1b"
  (title := "FKS Theorem 1.1b")
  (statement := /--
    Moreover, a collection of values, $\varepsilon(x_0)$ computed with well chosen parameters are
    provided in Table 5.
  -/)]
theorem theorem_1_1b {log_x0 σ2 c N K ε1 ε2 ε3 ε4 ε_total : ℝ}
    (h : (log_x0, σ2, ε1, ε2, ε3, ε4, ε_total) ∈ table_5) :
    ∀ x, log x ≥ log_x0 → Eψ x ≤ ε_total := by sorry

@[blueprint
  "fks-lemma-5-2"
  (title := "FKS Lemma 5.2")
  (statement := /--
    For all $0 < \log x \leq 2100$ we have that
    \[
    E_\psi(x) \leq 2(\log x)^{3/2} \exp\left(-0.8476836\sqrt{\log x}\right).
    \]
  -/)]
theorem lemma_5_3 {x : ℝ} (h : log x ∈ Set.Ioc 0 2100) :
    Eψ x ≤ 2 * (log x) ^ (3 / 2) * exp (-0.8476836 * sqrt (log x)) := by sorry

@[blueprint
  "fks-lemma-5-3"
  (title := "FKS Lemma 5.3")
  (statement := /--
    For all $2100 < \log x \leq 200000$ we have that
    \[
    E_\psi(x) \leq 9.22022(\log x)^{3/2} \exp\left(-0.8476836\sqrt{\log x}\right).
    \]
  -/)]
theorem lemma_5_4 {x : ℝ} (h : log x ∈ Set.Ioc 2100 200000) :
    Eψ x ≤ 9.22022 * (log x) ^ (3 / 2) * exp (-0.8476836 * sqrt (log x)) := by sorry

noncomputable def A (x₀ : ℝ) : ℝ :=
  if log x₀ < 1000 then 0 -- junk value
  else if log x₀ < 2000 then 338.3058
  else if log x₀ < 3000 then 263.2129
  else if log x₀ < 4000 then 233.0775
  else if log x₀ < 5000 then 215.8229
  else if log x₀ < 6000 then 204.2929
  else if log x₀ < 7000 then 195.8842
  else if log x₀ < 8000 then 189.3959
  else if log x₀ < 9000 then 184.1882
  else if log x₀ < 10000 then 179.8849
  else if log x₀ < 20000 then 176.2484
  else if log x₀ < 30000 then 156.4775
  else if log x₀ < 40000 then 147.5424
  else if log x₀ < 50000 then 142.1006
  else if log x₀ < 60000 then 138.3136
  else if log x₀ < 70000 then 135.4686
  else if log x₀ < 80000 then 133.2221
  else if log x₀ < 90000 then 131.3849
  else if log x₀ < 100000 then 129.8428
  else if log x₀ < 200000 then 128.5221
  else if log x₀ < 300000 then 121.0360
  else if log x₀ < 400000 then 117.4647
  else if log x₀ < 500000 then 115.2251
  else if log x₀ < 600000 then 113.6357
  else if log x₀ < 700000 then 112.4241
  else if log x₀ < 800000 then 111.4565
  else if log x₀ < 900000 then 110.6577
  else if log x₀ < 1e6 then 109.9819
  else if log x₀ < 1e7 then 109.3992
  else if log x₀ < 1e8 then 100.5097
  else if log x₀ < 1e9 then 96.0345
  else 93.6772

@[blueprint
  "fks-theorem-1-2b"
  (title := "FKS Theorem 1.2b")
  (statement := /--
    If $\log x_0 \geq 1000$ then we have an admissible bound for $E_\psi$ with the indicated choice
    of $A(x_0)$, $B = 3/2$, $C = 2$, and $R = 5.5666305$.
  -/)]
theorem theorem_1_2b (x₀ : ℝ) (h : log x₀ ≥ 1000) :
    Eψ.classicalBound (A x₀) (3 / 2) 2 5.5666305 x₀ := by sorry


@[blueprint "fks_cor_13"
  (title := "FKS1 Corollary 1.3")
  (statement := /--
    For all x > 2 we have
    $E_ψ(x) \leq 121.096 (\log x/R)^{3/2} \exp(-2 \sqrt{\log x/R})$ with $R = 5.5666305$.
  -/)
  (uses := ["classical-bound-psi"])
  (latexEnv := "theorem")]
theorem FKS_corollary_1_3 :
    Eψ.classicalBound 121.096 (3 / 2) 2 5.5666305 2 := sorry

@[blueprint "fks_cor_14"
  (title := "FKS1 Corollary 1.4")
  (statement := /--
    For all x > 2 we have
    $E_ψ(x) \leq 9.22022(\log x)^{3/2} \exp(-0.8476836 \sqrt{\log x})$.
  -/)
  (proof := /-- TODO. -/)]
theorem FKS_corollary_1_4 :
    Eψ.classicalBound 9.22022 (3 / 2) 0.8476836 1 2 := sorry


end FKS
