import Architect
import PrimeNumberTheoremAnd.PrimaryDefinitions

blueprint_comment /--
\section{The arguments of Rosser and Schoenfeld}
-/

blueprint_comment /--
In this section we formalize the arguments of Rosser and Schoenfeld that can convert primary
estimates to secondary estimates, with an emphasis on parameter flexibility.
-/

namespace RS

@[blueprint
  "RS_theorem_19"
  (title := "Rosser--Schoenfeld Theorem 19")
  (statement := /-- One has a Riemann von Mangoldt estimate with parameters 0.137, 0.443, and 1.588. --/)]
theorem theorem_19 : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 1.588 := by sorry

end RS
