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
  "Hasanalizade-Shen-Wong"
  (title := "Hasanalizade--Shen--Wong, Corollary 1.4")
  (statement := /--
    Following \cite{HSW2022}, Corollary~1.4, one has
    \[
    \bigl|N(T)-\tfrac{T}{2\pi}\log\tfrac{T}{2\pi e}-\tfrac78\bigr|
    \le 0.1038\log T+0.2573\log\log T+8.3675
    \]
    for $T\ge 2$ (the paper states the bound for $T\ge e$; we record it under the
    project's classical Riemann--von Mangoldt predicate, which starts at $T\ge 2$).
  --/)]
theorem HSW.main_theorem : riemannZeta.Riemann_vonMangoldt_bound 0.1038 0.2573 8.3675 := sorry

@[blueprint
  "Hasanalizade-Shen-Wong-cor-1-2"
  (title := "Hasanalizade--Shen--Wong, Corollary 1.2")
  (statement := /--
    Following \cite{HSW2022}, Corollary~1.2, for $T\ge e$ one has
    \[
    \bigl|N(T)-\tfrac{T}{2\pi}\log\tfrac{T}{2\pi e}\bigr|
    \le 0.1038\log T+0.2573\log\log T+9.3675
    \]
    (no $7/8$ term in the main term).
  --/)
  (latexEnv := "theorem")]
theorem HSW.corollary_1_2 :
    ∀ T ≥ (Real.exp 1),
      |riemannZeta.N T - (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))| ≤
        0.1038 * Real.log T + 0.2573 * Real.log (Real.log T) + 9.3675 := by
  sorry

@[blueprint
  "mt_theorem_1"
  (title := "MT Theorem 1")
  (statement := /--
    Following \cite{MT2015}, Theorem~1, one has a classical zero-free region with
    $R = 5.573412$.
  -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem MT_theorem_1 : riemannZeta.classicalZeroFree 5.573412 := sorry

@[blueprint
  "mt_R0_55666305"
  (title := "MT sharper $R_0$ under stronger RH verification")
  (statement := /--
    Following the remark in \cite{MT2015} after the $F_{16}$ analysis, the sharper
    constant $R = 5.5666305$ is permissible when the Riemann hypothesis is known to a
    sufficiently large height (the paper cites an announced verification to
    $3\cdot 10^{11}$).  This is the value used in \cite{FKS}.
  -/)
  (uses := ["classical-zero-free-region"])
  (latexEnv := "theorem")]
theorem MT_R0_55666305 : riemannZeta.classicalZeroFree 5.5666305 := sorry

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
    By \cite[Theorem 5.1]{Platt2017}, the Riemann hypothesis is verified up to
    $H_0 = 30{,}610{,}046{,}000 = 3.0610046 \times 10^{10}$.
  -/)
  (latexEnv := "theorem")]
theorem Platt_theorem : riemannZeta.RH_up_to 30610046000 := sorry

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
    By \cite{PT2021_RH}, the Riemann hypothesis is verified up to
    $H_0 = 3 \times 10^{12}$.
  -/)
  (latexEnv := "theorem")]
theorem PT_theorem_1 : riemannZeta.RH_up_to 3e12 := sorry
