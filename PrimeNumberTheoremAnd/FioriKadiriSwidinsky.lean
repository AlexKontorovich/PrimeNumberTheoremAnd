import Mathlib.Tactic
import PrimeNumberTheoremAnd.PrimaryDefinitions

/-%%
\section{The estimates of Fiori, Kadiri, and Swidinsky}
%%-/

/-%%
In this section we establish the primary results of Fiori, Kadiri, and Swidinsky.
%%-/

open Real

namespace FKS

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

/-%%
\begin{theorem}[FKS Theorem 1.2b]\label{FKS_theorem_1_2b} If $\log x_0 \geq 1000$ then we have an admissible bound for $E_\psi$ with the indicated choice of $A(x_0)$, $B = 3/2$, $C = 2$, and $R = 5.5666305$.
\end{theorem}
%%-/

theorem theorem_1_2b (x₀ : ℝ) (h : log x₀ ≥ 1000) : Eψ.classicalBound (A x₀) (3/2) 2 5.5666305 x₀ := by sorry

end FKS
