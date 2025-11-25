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
%%-/


/-%%
\begin{theorem}[FKS1 Corollary 1.4]\label{fks_cor_14}\lean{FKS_corollary_1_4}\leanok
For all x > 2 we have $E_ψ(x) < 9.22022(\log x)^{3/2} \exp(-0.8476836 \sqrt{\log x})$.
\end{theorem}
%%-/

theorem FKS_corollary_1_4 :
  Eψ.classicalBound 9.22022 (3/2) 0.8476836 1 2 := sorry

/-%%
\begin{proof} TODO.
\end{proof}
%%-/
