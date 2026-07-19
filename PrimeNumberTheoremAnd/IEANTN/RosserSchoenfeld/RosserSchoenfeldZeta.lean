import Architect
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions

blueprint_comment /--
\section{The zeta function bounds of Rosser and Schoenfeld}\label{rs-zeta-sec}
-/

blueprint_comment /--
In this section we formalize the zeta function bounds of Rosser and Schoenfeld.
-/

open Real

namespace RS
@[blueprint "RS_theorem_19"
  (title := "Rosser 1941, Theorem 19")
  (statement := /--
    Following \cite{rosser1941}, Theorem~19, for $T \geq 1467$ one has
    \[
    \bigl|N(T)-\tfrac{T}{2\pi}\log\tfrac{T}{2\pi e}-\tfrac78\bigr|
    \le 0.137\log T+0.443\log\log T+1.588.
    \]
    (Earlier blueprint text labelled this as Rosser--Schoenfeld Theorem~19 and
    used the project's $T\ge 2$ predicate; Rosser--Schoenfeld~(1962) has no such
    theorem, and Rosser's range is $T\ge 1467$.)
  -/)]
theorem theorem_19 :
    ∀ T ≥ (1467 : ℝ),
      |riemannZeta.N T - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
        0.137 * log T + 0.443 * log (log T) + 1.588 := by
  sorry
end RS
