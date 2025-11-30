import PrimeNumberTheoremAnd.SecondaryDefinitions

/-%%
\section{The implications of FKS2}

In this file we record the implications in the paper

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557

that allow one to convert primary bounds on Eψ into secondary bounds on Eπ, Eθ.
%%-/

/-%%
\begin{proposition}[Remark in FKS2 Section 1.1]\label{fks2-rem} $\li(x) - \Li(x) = \li(2)$.
\end{proposition}
%%-/

theorem fks2_rem : ∀ x > 2, li x - Li x = li 2 := sorry
