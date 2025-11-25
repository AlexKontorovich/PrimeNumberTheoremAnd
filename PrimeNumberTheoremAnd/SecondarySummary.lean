import PrimeNumberTheoremAnd.SecondaryDefinitions

/-%%
\section{Summary of results}
%%-/

/-%%
In this section we summarize the secondary results known in the literature (or obtained from this project), and (if their proof has already been formalized) provide a proof that reduces them to primary results, as well as implications of primary results to secondary results with appropriate choices of parameters.
%%-/


/-%%
\begin{theorem}[Dusart]\label{thm:Dusart}
There exists a constant \(X_0\) (one may take \(X_0 = 89693\)) with the following property:
for every real \(x \ge X_0\), there exists a prime \(p\) with
\[
  x < p \le x\Bigl(1 + \frac{1}{\log^3 x}\Bigr).
\]
\end{theorem}
%%-/

theorem Dusart_thm : HasPrimeInInterval.log_thm 89693 3 := sorry
