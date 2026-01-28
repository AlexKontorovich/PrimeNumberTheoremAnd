import Architect
import PrimeNumberTheoremAnd.ZetaDefinitions

blueprint_comment /--
\section{The zeta function bounds of Rosser and Schoenfeld}\label{rs-zeta-sec}
-/

blueprint_comment /--
In this section we formalize the zeta function bounds of Rosser and Schoenfeld.

TODO: Add more results and proofs here, and reorganize the blueprint
-/

namespace RS

@[blueprint
  "RS_theorem_19"
  (title := "Rosser--Schoenfeld Theorem 19")
  (statement := /--
    One has a Riemann von Mangoldt estimate with parameters 0.137, 0.443, and 1.588.
  -/)]
theorem theorem_19 : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 1.588 := by sorry

end RS
