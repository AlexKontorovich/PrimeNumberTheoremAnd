import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.FKS2

/-%%
\section{Summary of results}
%%-/

/-%%
In this section we summarize the secondary results known in the literature (or obtained from this project), and (if their proof has already been formalized) provide a proof that reduces them to primary results, as well as implications of primary results to secondary results with appropriate choices of parameters.

Key references:

Dusart: https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf

FKS1: Fiori--Kadiri--Swidninsky arXiv:2204.02588

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557

PT: D. J. Platt and T. S. Trudgian, The error term in the prime number theorem, Math. Comp. 90 (2021), no. 328, 871–881.

JY: D. R. Johnston, A. Yang, Some explicit estimates for the error term in the prime number theorem, arXiv:2204.01980.
%%-/

open Real

/-%%
\begin{theorem}[PT Corollary 2]\label{thm:pt_2}\lean{PT_Cor2}\leanok
One has
\[
|\pi(x) - \mathrm{Li}(x)| \leq 235 x (\log x)^{0.52} \exp(-0.8 \sqrt{\log x})
\]
for all $x \geq \exp(2000)$.
\end{theorem}
%%-/

theorem PT_Cor2: Eπ.classicalBound 235 1.52 0.8 1 (exp 2000) := sorry

/-%%
\begin{theorem}[JY Corollary 1.3]\label{thm:jy_13}\lean{JY_Cor13}\leanok
One has
\[
|\pi(x) - \mathrm{Li}(x)| \leq 9.59 x (\log x)^{0.515} \exp(-0.8274 \sqrt{\log x})
\]
for all $x \geq 2$.
\end{theorem}
%%-/

theorem JY_Cor13: Eπ.classicalBound 9.59 1.515 0.8274 1 2 := sorry

/-%%
\begin{theorem}[JY Theorem 1.4]\label{thm:jy_14}\lean{JY_Thm14}\leanok
One has
\[
|\pi(x) - \mathrm{Li}(x)| \leq 0.028 x (\log x)^{0.801} \exp(-0.1853 \log^{3/5} x / (\log \log x)^{1/5}))
\]
for all $x \geq 2$.
\end{theorem}
%%-/

theorem JY_Thm14: Eπ.vinogradovBound 0.028 0.801 0.1853 2 := sorry

/-%% TODO: input other results from JY %%-/

/-%%
\begin{theorem}[FKS2 Corollary 22]\label{thm:fks2_22}\lean{FKS2_Cor22}\leanok
One has
\[
|\pi(x) - \mathrm{Li}(x)| \leq 9.2211 x \sqrt{\log x} \exp(-0.8476 \sqrt{\log x})
\]
for all $x \geq 2$.
\end{theorem}
%%-/

theorem FKS2_Cor22: Eπ.classicalBound 9.2211 1.5 0.8476 1 2 := sorry

/-%%
\begin{theorem}[FKS2 Corollary 26]\label{thm:fks2_26}\lean{FKS2_Cor26}\leanok
One has
\[
|\pi(x) - \mathrm{Li}(x)| \leq 0.4298 \frac{x}{\log x}
\]
for all $x \geq 2$.
\end{theorem}
%%-/

theorem FKS2_Cor226 : Eπ.bound 0.4298 2 := sorry



/-%%
\begin{theorem}[Dusart Proposition 5.4]\label{thm:Dusart}
There exists a constant \(X_0\) (one may take \(X_0 = 89693\)) with the following property:
for every real \(x \ge X_0\), there exists a prime \(p\) with
\[
  x < p \le x\Bigl(1 + \frac{1}{\log^3 x}\Bigr).
\]
\end{theorem}
%%-/

theorem Dusart_thm : HasPrimeInInterval.log_thm 89693 3 := sorry

/-%% TODO: input other results from Dusart %%-/
