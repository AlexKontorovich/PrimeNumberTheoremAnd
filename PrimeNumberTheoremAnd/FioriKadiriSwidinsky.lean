import Architect
import PrimeNumberTheoremAnd.PrimaryDefinitions

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
  If $|N(T) - (T/2\pi \log(T/2\pi e) + 7/8)| \leq R(T)$ then $\sum_{U \leq \gamma < V} 1/γ} ≤ B_1(U,V)$.-/)]
theorem lemma_2_1 {b₁ b₂ b₃ U V : ℝ} (hU : U ≥ 1) (hV : V ≥ U) (hR : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) : ∑' ρ : { s | s ∈ riemannZeta.zeroes ∧ U ≤ s.im ∧ s.im < V }, riemannZeta.order ρ / ρ.val.im ≤ B₁ b₁ b₂ b₃ U V := by sorry

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
  "fks-corollyar_2_3"
  (title := "FKS Corollary 2.3")
  (statement := /-- For each pair $T_0,S_0$ in Table 1 we have, for all $V > T_0$, $\sum_{0 < γ < V} 1/\gamma} < S_0 + B_1(T_0,V)$. -/)]
theorem corollary_2_3 {T₀ S₀ V : ℝ} (h : (T₀, S₀) ∈ table_1) (hV : V > T₀) : ∑' ρ : { s | s ∈ riemannZeta.zeroes ∧ 0 < s.im ∧ s.im < V }, riemannZeta.order ρ / ρ.val.im < S₀ + B₁ 0.137 0.443 1.588 T₀ V := by sorry



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
