import Architect
import PrimeNumberTheoremAnd.PrimaryDefinitions
import PrimeNumberTheoremAnd.KLN

blueprint_comment /--
\section{The estimates of Fiori, Kadiri, and Swidinsky}
-/

blueprint_comment /--
In this section we establish the primary results of Fiori, Kadiri, and Swidinsky from this paper: arXiv:2204.02588
-/

open Real

namespace FKS

noncomputable def B₁ (b₁ b₂ b₃ U V : ℝ) := ( 1/(2*π) + ((b₁ * log U) + b₂)/(U * (log U) * (log (U/(2*π)))) ) * (log (V/U) * (log ( sqrt (V*U) / (2*π) ))) + 2 * (riemannZeta.R b₁ b₂ b₃ U) / U

@[blueprint
  "fks-lemma-2-1"
  (title := "FKS Lemma 2.1")
  (statement := /--
  If $|N(T) - (T/2\pi \log(T/2\pi e) + 7/8)| \leq R(T)$ then $\sum_{U \leq \gamma < V} 1/\gamma \leq B_1(U,V)$.-/)]
theorem lemma_2_1 {b₁ b₂ b₃ U V : ℝ} (hU : U ≥ 1) (hV : V ≥ U) (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) : riemannZeta.zeroes_sum Set.univ (Set.Ico U V) (fun ρ ↦ 1 / ρ.im) ≤ B₁ b₁ b₂ b₃ U V := by sorry

def table_1 : List (ℝ × ℝ) :=
  [ (100, 0.5922435112),
    (1000, 2.0286569752),
    (10000, 4.3080354951),
    (100000, 7.4318184970),
    (1000000, 11.3993199147),
    (10000000, 16.2106480369),
    (100000000, 21.8657999924),
    (1000000000, 28.3647752011),
    (10000000000, 35.7075737123),
    (30610046000, 39.5797647802)
  ]

@[blueprint
  "fks-corollary_2_3"
  (title := "FKS Corollary 2.3")
  (statement := /-- For each pair $T_0,S_0$ in Table 1 we have, for all $V > T_0$, $\sum_{0 < \gamma < V} 1/\gamma < S_0 + B_1(T_0,V)$. -/)]
theorem corollary_2_3 {b₁ b₂ b₃ T₀ S₀ V : ℝ} (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) (h : (T₀, S₀) ∈ table_1) (hV : V > T₀) : riemannZeta.zeroes_sum Set.univ (Set.Ioo 0 V) (fun ρ ↦ 1 / ρ.im) < S₀ + B₁ b₁ b₂ b₃ T₀ V := by sorry

noncomputable def s₀ (σ U V : ℝ) := riemannZeta.zeroes_sum (Set.Ico σ 1) (Set.Ico U V) (fun ρ ↦ 1 / ρ.im)

noncomputable def _root_.Real.Gamma.incomplete (s : ℝ) (x : ℝ) : ℝ := ∫ t in Set.Ioi x, exp (-t) * t ^ (s - 1)

noncomputable def _root_.Complex.Gamma.incomplete (s : ℂ) (x : ℝ) : ℂ := ∫ t in Set.Ioi x, exp (-t) * t ^ (s - 1)

noncomputable def riemannZeta.zero_density_bound.B₀ (ZDB : riemannZeta.zero_density_bound) (σ U V : ℝ) : ℝ :=
  (ZDB.c₁ σ) * (log V)^(ZDB.q σ) / V ^ (1 - (ZDB.p σ)) + (ZDB.c₂ σ) * (log V)^2 / V
  + (ZDB.c₁ σ / (1 - ZDB.p σ)^(ZDB.q σ+1)) * (Real.Gamma.incomplete (ZDB.q σ+1) ((1-ZDB.p σ)*(log U)) - Real.Gamma.incomplete (ZDB.q σ+1) ((1-ZDB.p σ)*(log V)))
  + (ZDB.c₂ σ) * (Real.Gamma.incomplete 3 ((log U)) - Real.Gamma.incomplete 3 ((log V))
  )

@[blueprint
  "fks-lemma-2-5"
  (title := "FKS Lemma 2.5")
  (statement := /-- Let $T_0 \geq 2$ and $\gamma > 0$.  Assume that there exist $c_1, c_2, p, q, T_0$ for which one has a zero density bound.  Assume $\sigma \geq 5/8$ and $T_0 \leq U < V$.  Then $s_0(σ,U,V) \leq B_0(\sigma,U,V)$. -/)]
theorem lemma_2_5 (ZDB: riemannZeta.zero_density_bound) {σ U V : ℝ}
  (hT₀ : ZDB.T₀ ≥ 2)
  (hσ : σ ≥ 5 / 8)
  (hσ' : σ ∈ ZDB.σ_range)
  (hU : U ≥ ZDB.T₀)
  (hV : V > U) :
  s₀ σ U V ≤ riemannZeta.zero_density_bound.B₀ ZDB σ U V := by sorry

@[blueprint
  "fks-remark-2-6-a"
  (title := "FKS Remark 2-6-a")
  (statement := /-- $\Gamma(3,x) = (x^2 + 2(x+1)) e^{-x}$.-/)]
theorem remark_2_6_a (x : ℝ) : Real.Gamma.incomplete 3 x = (x^2 + 2 * (x + 1)) * exp (-x) := by sorry

@[blueprint
  "fks-remark-2-6-b"
  (title := "FKS Remark 2-6-b")
  (statement := /-- For $s>1$, one has $\Gamma(s,x) \sim x^{s-1} e^{-x}$.-/)]
theorem remark_2_6_b (s : ℝ) (h : s > 1) : Filter.Tendsto (fun x ↦ Real.Gamma.incomplete s x / (x^(s-1) * exp (-x))) Filter.atTop (nhds 1) := by sorry

@[blueprint
  "fks-theorem-2-7"
  (title := "FKS Theorem 2.7")
  (statement := /-- Let $H_0$ denote a verification height for RH.  Let $10^9/H_0≤ k \leq 1$, $t > 0$, $H \in [1002, H_0)$, $α > 0$, $δ ≥ 1$, $\eta_0 = 0.23622$, $1 + \eta_0 \leq \mu \leq 1+\eta$, and $\eta \in (\eta_0, 1/2)$ be fixed. Let $\sigma > 1/2 + d / \log H_0$.  Then for any $T \geq H_0$, one has
  $$ N(\sigma,T) \leq (T-H) \log T / (2\pi d) * \log ( 1 + CC_1(\log(kT))^{2\sigma} (\log T)^{4(1-\sigma)} T^{8/3(1-\sigma)} / (T-H) ) + CC_2 * \log^2 T / 2 \pi d$$
and
  $$ N(\sigma,T) \leq \frac{CC_1}{2\pi d} (\log kT)^{2\sigma} (\log T)^{5-4*\sigma} T^{8/3(1-\sigma)} + CC_2 * \log^2 T / 2 \pi d$$
.-/)]
theorem theorem_2_7 {H₀ k δ α d η₀ η μ σ H T : ℝ}
  (hH₀ : riemannZeta.RH_up_to H₀)
  (hk : k ∈ Set.Icc ((10 ^ 9) / H₀) 1)
  (hα : α > 0)
  (hδ : δ ≥ 1)
  (hη₀ : η₀ = 0.23622)
  (hμ : μ ∈ Set.Icc (1 + η₀) (1 + η))
  (hη : η ∈ Set.Ioo η₀ 0.5)
  (hσ : σ > 0.5 + d / log H₀)
  (hH : H ∈ Set.Ico 1002 H₀)
  (hT : T ≥ H₀) :
  riemannZeta.N' σ T ≤ ( (T - H) * log T ) / (2 * π * d) * log (1 + KLN.CC₁ H₀ α d δ k H σ * (log (k * T))^(2*σ) * (log T)^(4*(1-σ)) * T^(8/3*(1-σ)) / (T - H) ) + KLN.CC₂ H₀ d η k H μ σ * (log T)^2 / (2 * π * d)
  ∧
  riemannZeta.N' σ T ≤ KLN.CC₁ H₀ α d δ k H σ * (log (k * T))^(2*σ) * (log T)^(5 - 4*σ) * T^(8/3*(1-σ)) / (2 * π * d) + KLN.CC₂ H₀ d η k H μ σ * (log T)^2 / (2 * π * d) := by sorry

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
    (0.99, 1.0, 0.05420, 0.3133, 0.3360, 36.0559, 17.0819, 4.5304, 2.1464)
    ]

@[blueprint
  "fks-corollary-2-9"
  (title := "FKS Corollary 2.9")
  (statement := /-- For each $\sigma_1, \sigma_2, \tilde c_1, \tilde c_2$ given in Table 8, we have $N(\sigma,T) \leq \tilde c_1 T^{p(\sigma)} \log^{q(\sigma)} + \tilde c_2 \log^2 T$ for $\sigma_1 \leq \sigma \leq \sigma_2$ with $p(\sigma) = 8/3 (1-\sigma)$ and $q(σ) = 5-2\sigma$.-/)]
noncomputable def corollary_2_9 {σ₁ σ₂ α δ d CC_1 c₁ CC_2 c₂ : ℝ} (h : (σ₁, σ₂, α, δ, d, CC_1, c₁, CC_2, c₂) ∈ table_8) : riemannZeta.zero_density_bound := {
    T₀ := 3e12
    σ_range := Set.Icc σ₁ σ₂
    c₁ σ := c₁
    c₂ σ := c₂
    p σ := 8 / 3 * (1 - σ)
    q σ := 5 - 2 * σ
    bound := by sorry
}

@[blueprint
  "fks-theorem-3-1"
  (title := "FKS Theorem 3.1")
  (statement := /-- Let $x > e^{50}$ be half an odd integer and suppose that $50 < T < x$.  Then $E_\psi(x) \leq \sum_{|\gamma| < T} |x^{\rho-1}/\rho| + 2 \log^2 x / T.$ -/)]
theorem theorem_3_1 {x T : ℝ} (hx : x > exp 50) (hodd : ∃ X, Odd X ∧ x = X / 2) (hT : T ∈ Set.Ioo 50 x) : Eψ x ≤ riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Ioo (-T) T) (fun ρ ↦ ‖x^(ρ - 1) / ρ‖) + 2 * (log x)^2 / T := by sorry

@[blueprint
  "fks-theorem-3-2"
  (title := "FKS Theorem 3.2")
  (statement := /-- For any $\alpha \in (0,1/2]$ and $\omega \in [0,1]$ there exist $M, x_M$ such that for $\max(51, \log x) < T < (x^\alpha-2)/5$ and some $T^* \in [T, 2.45 T]$,
  $$ |\psi(x) - (x - \sum_{|\gamma| \leq T^*} x^\rho/\rho)| ≤ M x / T * log^{1-\omega} x  $$ for all $x ≥ x_M$. -/)]
theorem theorem_3_2 (α ω : ℝ) (hα : α ∈ Set.Ioc 0 (1 / 2)) (hω : ω ∈ Set.Icc 0 1) : ∃ M xM : ℝ, ∀ x, ∀ T ∈ Set.Ioo (max 51 (log x)) ((x^α - 2) / 5), ∃ Tstar ∈ Set.Icc T (2.45 * T), ∀ x ≥ xM, ‖ψ x - (x - riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Ioo (-Tstar) Tstar) (fun ρ ↦ x^ρ / ρ))‖ ≤ M * x / T * (log x)^(1 - ω) := by sorry

@[blueprint
  "fks-proposition-3-4"
  (title := "FKS Proposition 3.4")
  (statement := /--  Let $x > e^{50}$ and $3 \log x < T < \sqrt{x}/3$.  Then
  $$ E_\psi(x) ≤ \sum_{|\gamma| < T} |x^{\rho-1}/\rho| + 2 \log^2 x / T.$$-/)]
theorem proposition_3_4 {x T : ℝ} (hx : x > exp 50) (hT : T ∈ Set.Ioo (3 * log x) (sqrt x / 3)) : Eψ x ≤ riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Ioo (-T) T) (fun ρ ↦ ‖x^(ρ - 1) / ρ‖) + 2 * (log x)^2 / T := by sorry

noncomputable def riemannZeta.Sigma (T x a b : ℝ) : ℝ := 2 * (riemannZeta.zeroes_sum (Set.Ico a b) (Set.Ioo 0 T) (fun ρ ↦ x^(ρ.re - 1) / ρ.im))

@[blueprint
  "fks-proposition-3-6"
  (title := "FKS Proposition 3.6")
  (statement := /-- Let $\sigma_1 \in (1/2,1)$ and let $(T_0,S_0)$ be taken from Table 1.  Then $\Sigma_0^{\sigma_1} ≤ 2 x^{-1/2} (S_0 + B_1(T_0,T)) + (x_1^{\sigma_1-1} - x^{-1/2}) B_1(H_0,T)$.-/)]
theorem proposition_3_6 {b₁ b₂ b₃ H₀ σ₁ T₀ S₀ T x : ℝ} (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) (hH₀ : riemannZeta.RH_up_to H₀) (hσ_1 : σ₁ ∈ Set.Icc 0.5 1) (hT₀S₀ : (T₀, S₀) ∈ table_1) (hT : T > T₀) (x : ℝ) : riemannZeta.Sigma T x 0 σ₁ ≤ 2 * x^(-0.5:ℝ) * (S₀ + B₁ b₁ b₂ b₃ T₀ T) + (x^(σ₁ - 1) - x^(-0.5:ℝ)) * (B₁ b₁ b₂ b₃ H₀ T) := by sorry

noncomputable def Hσ (H₀ R σ : ℝ) : ℝ := max H₀ (exp (1 / (R*(1-σ))))

theorem riemannZeta.Hσ_zeroes (H₀ R σ : ℝ) (hH₀ : riemannZeta.RH_up_to H₀) (hR : riemannZeta.classicalZeroFree R) : riemannZeta.N' σ (Hσ H₀ R σ) = 0 := by sorry

@[blueprint
"fks-eq13"
  (title := "FKS equation (3.13)")
  (statement := /-- $\Sigma_a^b = 2 * \sum_{H_a ≤ \gamma < T; a \leq \beta < b} \frac{x^{\beta-1}}{\gamma}$.-/)]
theorem eq_13 {H₀ R a b T x : ℝ} (hH₀ : riemannZeta.RH_up_to H₀) (hR : riemannZeta.classicalZeroFree R) : riemannZeta.Sigma T x a b = 2 * riemannZeta.zeroes_sum (Set.Ico a b) (Set.Ioc (Hσ H₀ R a) T) (fun ρ ↦ x^(ρ.re - 1) / ρ.im) := by sorry

noncomputable def σn (σ₁ σ₂ : ℝ) (n N : ℕ) : ℝ := σ₁ + (σ₂ - σ₁) * n / N

noncomputable def Hn (H₀ R σ₁ σ₂ : ℝ) (n N : ℕ) : ℝ := Hσ H₀ R (σn σ₁ σ₂ n N)

@[blueprint
"fks-remark-3-7"
  (title := "FKS Remark 3.7")
  (statement := /-- If $\sigma < 1 - 1/R \log H_0$ then $H_σ = H_0$.-/)]
theorem remark_3_7 {H₀ R σ : ℝ} (hσ : σ < 1 - 1 / (R * log H₀)) : Hσ H₀ R σ = H₀ := by sorry

@[blueprint
"fks-proposition-3-8"
  (title := "FKS Proposition 3.8")
  (statement := /-- Let $N \geq 2$ be an integer.  If $5/8 \leq \sigma_1 < \sigma_2 \leq 1$, $T \geq H_0$, then $\Sigma_{\sigma_1}^{\sigma_2} ≤ 2 x^{-(1-\sigma_1)+(\sigma_2-\sigma_1/N)}B_0(\sigma_1, H_{\sigma_1, T) + 2 x^{(1-\sigma_1)} (1 - x^{-(\sigma_2-\sigma_1)/N}) \sum_{n=1}^{N-1} B_0(\sigma^{(n)}, H^{(n)}, T) x^{(\sigma_2-\sigma_1) (n+1)/N}$.-/)]
theorem proposition_3_8 {H₀ R σ₁ σ₂ T x : ℝ} (N : ℕ) (hH₀ : riemannZeta.RH_up_to H₀) (hR : riemannZeta.classicalZeroFree R) (ZDB : riemannZeta.zero_density_bound) (hσ₁ : σ₁ ∈ Set.Icc (5 / 8) 1) (hσ₂ : σ₂ ∈ Set.Ioc σ₁ 1) (hσ : Set.Icc σ₁ σ₂ ⊆ ZDB.σ_range) (hT : T ≥ H₀) : riemannZeta.Sigma T x σ₁ σ₂ ≤ 2 * x^(-(1 - σ₁) + (σ₂ - σ₁) / N) * (riemannZeta.zero_density_bound.B₀ ZDB σ₁ (Hσ H₀ R σ₁) T) + 2 * x^(1 - σ₁) * (1 - x^(-(σ₂ - σ₁) / N)) * ∑ n ∈ Finset.Ico 1 N, (riemannZeta.zero_density_bound.B₀ ZDB (σn σ₁ σ₂ n N) (Hn H₀ R σ₁ σ₂ n N) T) * x^((σ₂ - σ₁) * (n + 1) / N) := by sorry

@[blueprint
"fks-corollary-3-10"
  (title := "FKS Corollary 3.10")
  (statement := /-- If $\sigma_1 \geq 0.9$ then $\Sigma_{\sigma_1}^{\sigma_2} \leq 0.00125994 x^{\sigma_2-1}$.-/)]
theorem corollary_3_10 {σ₁ σ₂ T x : ℝ} (hσ₁ : σ₁ ∈ Set.Icc 0.9 1) (hσ₂ : σ₂ ∈ Set.Ioc σ₁ 1) : riemannZeta.Sigma T x σ₁ σ₂ ≤ 0.00125994 * x^(σ₂ - 1) := by sorry



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
  If $\log x_0 \geq 1000$ then we have an admissible bound for $E_\psi$ with the indicated choice of $A(x_0)$, $B = 3/2$, $C = 2$, and $R = 5.5666305$.
  -/)]
theorem theorem_1_2b (x₀ : ℝ) (h : log x₀ ≥ 1000) : Eψ.classicalBound (A x₀) (3/2) 2 5.5666305 x₀ := by sorry

end FKS
