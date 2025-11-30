import PrimeNumberTheoremAnd.PrimaryDefinitions
import PrimeNumberTheoremAnd.FioriKadiriSwidinsky


/-%%
\section{Summary of results}
%%-/

/-%%
In this section we summarize the primary results known in the literature, and (if their proof has already been formalized) provide a proof.

Key references:

FKS1: Fiori--Kadiri--Swidninsky arXiv:2204.02588

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557

MT: M. J. Mossinghoff and T. S. Trudgian, Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function, J. Number Theory. 157 (2015), 329–349.

MTY: M. J. Mossinghoff, T. S. Trudgian, and A. Yang, Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function, arXiv:2212.06867.

%%-/


/-%%
\begin{theorem}[MT Theorem 1]\label{mt_theorem_1}\uses{classical zero-free region}\lean{MT_theorem_1}\leanok
One has a classical zero-free region with $R = 5.5666305$.
\end{theorem}
%%-/

theorem MT_theorem_1 : riemannZeta.classicalZeroFree 5.5666305 := sorry

/-%%
\begin{theorem}[MTY]\label{mty_theorem}\uses{classical zero-free region}\lean{MTY_theorem}\leanok
One has a classical zero-free region with $R = 5.558691$.
\end{theorem}
%%-/

theorem MTY_theorem : riemannZeta.classicalZeroFree 5.558691 := sorry

/-%%
\begin{theorem}[FKS1 Corollary 1.4]\label{fks_cor_14}\uses{classical bound}\lean{FKS_corollary_1_4}\leanok
For all x > 2 we have $E_ψ(x) < 9.22022(\log x)^{3/2} \exp(-0.8476836 \sqrt{\log x})$.
\end{theorem}
%%-/

theorem FKS_corollary_1_4 :
  Eψ.classicalBound 9.22022 (3/2) 0.8476836 1 2 := sorry

/-%%
\begin{proof} TODO.
\end{proof}
%%-/
