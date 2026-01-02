import Architect
import PrimeNumberTheoremAnd.PrimaryDefinitions
import PrimeNumberTheoremAnd.FioriKadiriSwidinsky


blueprint_comment /--
\section{Summary of results}
-/

blueprint_comment /--
In this section we summarize the primary results known in the literature, and (if their proof has already been formalized) provide a proof.

Key references:

FKS1: Fiori--Kadiri--Swidninsky arXiv:2204.02588

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557

MT: M. J. Mossinghoff and T. S. Trudgian, Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function, J. Number Theory. 157 (2015), 329–349.

MTY: M. J. Mossinghoff, T. S. Trudgian, and A. Yang, Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function, arXiv:2212.06867.

-/

@[blueprint
  "mt_theorem_1"
  (title := "MT Theorem 1")
  (statement := /-- One has a classical zero-free region with $R = 5.5666305$. -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem MT_theorem_1 : riemannZeta.classicalZeroFree 5.5666305 := sorry

@[blueprint
  "mty_theorem"
  (title := "MTY")
  (statement := /-- One has a classical zero-free region with $R = 5.558691$. -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem MTY_theorem : riemannZeta.classicalZeroFree 5.558691 := sorry


@[blueprint "fks_cor_13"
  (title := "FKS1 Corollary 1.3")
  (statement := /-- For all x > 2 we have $E_ψ(x) \leq 121.096 (\log x/R)^{3/2} \exp(-2 \sqrt{\log x/R})$ with $R = 5.5666305$. -/)
  (uses := ["classical-bound"])
  (latexEnv := "theorem")]
theorem FKS_corollary_1_3 :
  Eψ.classicalBound 121.096 (3/2) 2 5.5666305 2 := sorry

@[blueprint "fks_cor_14"
  (title := "FKS1 Corollary 1.4")
  (statement := /-- For all x > 2 we have $E_ψ(x) \leq 9.22022(\log x)^{3/2} \exp(-0.8476836 \sqrt{\log x})$. -/)
  (proof := /-- TODO. -/)]
theorem FKS_corollary_1_4 :
  Eψ.classicalBound 9.22022 (3/2) 0.8476836 1 2 := sorry
