import Architect
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.IEANTN.KLN
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldZeta
import PrimeNumberTheoremAnd.IEANTN.ZetaAppendix

blueprint_comment /--
\section{Summary of results}
-/

blueprint_comment /--
Here we list some papers that we plan to incorporate into this
section in the future, and list some results that have not yet been
moved into dedicated paper sections.
-/

@[blueprint
  "Hasanalizade-Shen-Wang"
  (title := "Hasanalizade-Shen-Wang")
  (statement := /--
    One has a Riemann von Mangoldt estimate with parameters
    0.1038, 0.2573, and 9.3675.
  --/)]
theorem HSW.main_theorem : riemannZeta.Riemann_vonMangoldt_bound 0.1038 0.2573 9.3675 := sorry

@[blueprint
  "mt_theorem_1"
  (title := "MT Theorem 1")
  (statement := /--
    Following \cite{MT2015}, one has a classical zero-free region with
    $R = 5.5666305$. (A more conservative value of $R = 5.573412$ was
    announced in the paper using weaker numerical verification of the
    Riemann hypothesis.)
  -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem MT_theorem_1 : riemannZeta.classicalZeroFree 5.5666305 := sorry

@[blueprint
  "mty_theorem"
  (title := "MTY")
  (statement := /--
    Following \cite{MTY2024}, one has a classical zero-free region with
    $R = 5.558691$.
  -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem MTY_theorem : riemannZeta.classicalZeroFree 5.558691 := sorry

@[blueprint
  "bty_theorem"
  (title := "BTY")
  (statement := /--
    Following \cite{BTY2026}, one has a classical zero-free region with
    $R = 4.896$.
  -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem BTY_theorem : riemannZeta.classicalZeroFree 4.896 := sorry

@[blueprint
  "platt_RH"
  (title := "Platt's numerical verification of RH")
  (statement := /--
    By \cite{Platt2017}, the Riemann hypothesis is verified up to
    $H_0 = 3.061 \times 10^{10}$.
  -/)
  (latexEnv := "theorem")]
theorem Platt_theorem : riemannZeta.RH_up_to 30610000000 := sorry

@[blueprint
  "gourdon_wedeniwski"
  (title := "Gourdon-Wedeniwski")
  (statement := /--
    By \cite{Gourdon2004}, the Riemann hypothesis is verified up to
    $H_0 = 2445999556030$.
  -/)
  (latexEnv := "theorem")]
theorem GW_theorem : riemannZeta.RH_up_to 2445999556030 := sorry

@[blueprint
  "pt_theorem_1"
  (title := "PT Theorem 1")
  (statement := /--
    By \cite{PT2021}, the Riemann hypothesis is verified up to
    $H_0 = 3 \times 10^{12}$.
  -/)
  (latexEnv := "theorem")]
theorem PT_theorem_1 : riemannZeta.RH_up_to 3e12 := sorry
