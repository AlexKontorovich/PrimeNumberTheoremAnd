import Architect
import PrimeNumberTheoremAnd.ZetaDefinitions
import PrimeNumberTheoremAnd.KLN
import PrimeNumberTheoremAnd.RosserSchoenfeldZeta
import PrimeNumberTheoremAnd.ZetaAppendix

blueprint_comment /--
\section{Summary of results}
-/

blueprint_comment /--
Here we list some papers that we plan to incorporate into this section in the future, and list some results that have not yet been moved into dedicated paper sections.

References to add:

MT: M. J. Mossinghoff and T. S. Trudgian, Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function, J. Number Theory. 157 (2015), 329–349.

MTY: M. J. Mossinghoff, T. S. Trudgian, and A. Yang, Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function, arXiv:2212.06867.

-/



-- TODO: move to separate file
@[blueprint
  "Hasanalizade-Shen-Wang"
  (title := "Hasanalizade-Shen-Wang")
  (statement := /-- One has a Riemann von Mangoldt estimate with parameters 0.1038, 0.2573, and 9.3675. --/)]
theorem HSW.main_theorem : riemannZeta.Riemann_vonMangoldt_bound 0.1038 0.2573 9.3675 := sorry

-- TODO: move to separate file
@[blueprint
  "mt_theorem_1"
  (title := "MT Theorem 1")
  (statement := /-- One has a classical zero-free region with $R = 5.5666305$. -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem MT_theorem_1 : riemannZeta.classicalZeroFree 5.5666305 := sorry

-- TODO: move to separate file
@[blueprint
  "mty_theorem"
  (title := "MTY")
  (statement := /-- One has a classical zero-free region with $R = 5.558691$. -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem MTY_theorem : riemannZeta.classicalZeroFree 5.558691 := sorry

-- TODO: move to separate file
@[blueprint
  "pt_theorem_1"
  (title := "PT Theorem 1")
  (statement := /-- The Riemann hypothesis is verified up to $H_0 = 3 \times 10^{12}$. -/)
  (latexEnv := "theorem")]
theorem PT_theorem_1 : riemannZeta.RH_up_to 3e12 := sorry
