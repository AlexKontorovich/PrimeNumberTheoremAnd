import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.AbsMax
import «PrimeNumberTheoremAnd».StrongPNT.BorelCaratheodory


open Nat Filter

--open scoped ArithmeticFunction

/-%%
    This upstreamed from https://github.com/math-inc/strongpnt/tree/main
%%-/

/-%%
\begin{theorem}[BorelCaratheodory]\label{BorelCaratheodory}\lean{BorelCaratheodory}
    Let $R,\,M>0$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then for any $0 < r < R$,
    $$\sup_{\abs{z}\leq r}\abs{f(z)}\leq\frac{2Mr}{R-r}.$$
\end{theorem}
%%-/

-- The proof is in the StrongPNT.BorelCaratheodory import. 

/-%%
\begin{proof}
\uses{}
    Let
    $$f_M(z)=\frac{f(z)/z}{2M-f(z)}.$$
    Note that $2M-f(z)≠ 0$ because $ℐfrak{R}(2M-f(z))=2M-ℐfrak{R}f(z)≥ M>0$. Additionally, since $f(z)$ has a zero at $0$, we know that $f(z)/z$ is analytic on $\abs{z}\leq R$. Likewise, $f_M(z)$ is analytic on $\abs{z}\leq R$.

    Now note that $\abs{f(z)}\leq\abs{2M-f(z)}$ since $ℐfrak{R}f(z)\leq M$. Thus we have that
    $$\abs{f_M(z)}=\frac{\abs{f(z)}/\abs{z}}{\abs{2M-f(z)}}\leq\frac{1}{\abs{z}}.$$
    Now by the maximum modulus principle, we know the maximum of $\abs{f_M}$ must occur on the boundary where $\abs{z}=R$. Thus, $\abs{f_M(z)}\leq 1/R$ for all $\abs{z}\leq R$. So for $\abs{z}=r$ we have
    $$\abs{f_M(z)}=\frac{\abs{f(z)}/r}{\abs{2M-f(z)}}\leq\frac{1}{R}\implies R\,\abs{f(z)}\leq r\,\abs{2M-f(z)}\leq 2Mr+r\,\abs{f(z)}.$$
    Which by algebraic manipulation gives
    $$\abs{f(z)}\leq\frac{2Mr}{R-r}.$$
    Once more, by the maximum modulus principle, we know the maximum of $\abs{f}$ must occur on the boundary where $\abs{z}=r$. Thus, the desired result immediately follows
\end{proof}
%%-/



/-%%
\begin{lemma}[DerivativeBound]\label{DerivativeBound}\lean{DerivativeBound}
    Let $R,\,M>0$ and $0 < r < r' < R$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then we have that
    $$\abs{f'(z)}\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}$$
    for all $\abs{z}\leq r$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    By Cauchy's integral formula we know that
    $$f'(z)=\frac{1}{2\pi i}\oint_{\abs{w}=r'}\frac{f(w)}{(w-z)^2}\,dw=\frac{1}{2\pi }\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
    Thus,
    \begin{equation}\label{pickupPoint1}
        \abs{f'(z)}=\abs{\frac{1}{2\pi}\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt}\leq\frac{1}{2\pi}\int_0^{2\pi}\abs{\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}}\,dt.
    \end{equation}
    Now applying Theorem \ref{BorelCaratheodory}, and noting that $r'-r\leq\abs{r'e^{it}-z}$, we have that
    $$\abs{\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}}\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
    Substituting this into Equation (\ref{pickupPoint1}) and evaluating the integral completes the proof.
\end{proof}
%%-/



/-%%
\begin{theorem}[BorelCaratheodoryDeriv]\label{BorelCaratheodoryDeriv}\lean{BorelCaratheodoryDeriv}
    Let $R,\,M>0$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then for any $0 < r < R$,
    $$\abs{f'(z)}\leq\frac{16MR^2}{(R-r)^3}$$
    for all $\abs{z}\leq r$.
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{}
    Using Lemma \ref{DerivativeBound} with $r'=(R+r)/2$, and noting that $r < R$, we have that
    $$\abs{f'(z)}\leq\frac{4M(R+r)^2}{(R-r)^3}\leq\frac{16MR^2}{(R-r)^3}.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[LogOfAnalyticFunction]\label{LogOfAnalyticFunction}\lean{LogOfAnalyticFunction}
    Let $0 < r < R<1$. Let $B:\overline{\mathbb{D}_R}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_R}$ with $B(z)\neq 0$ for all $z\in\overline{\mathbb{D}_R}$. Then there exists $J_B:\overline{\mathbb{D}_r}\to\mathbb{C}$ that is analytic on neighborhoods of points in $\overline{\mathbb{D}_r}$ such that
    \begin{itemize}
        \item $J_B(0)=0$
        \item $J_B'(z)=B'(z)/B(z)$
        \item $\log\abs{B(z)}-\log\abs{B(0)}=\mathfrak{R}J_B(z)$
    \end{itemize}
    for all $z\in\overline{\mathbb{D}_r}$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    We let $J_B(z)=\mathrm{Log}\,B(z)-\mathrm{Log}\,B(0)$. Then clearly, $J_B(0)=0$ and $J_B'(z)=B'(z)/B(z)$. Showing the third property is a little more difficult, but by no standards terrible. Exponentiating $J_B(z)$ we have that
    $$\exp(J_B(z))=\exp(\mathrm{Log}\,B(z)-\mathrm{Log}\,B(0))=\frac{B(z)}{B(0)}\implies B(z)=B(0)\exp(J_B(z)).$$
    Now taking the modulus
    $$\abs{B(z)}=\abs{B(0)}\cdot\abs{\exp(J_B(z))}=\abs{B(0)}\cdot\exp(\mathfrak{R}J_B(z)).$$
    Taking the real logarithm of both sides and rearranging gives the third point.
\end{proof}
%%-/



/-%%
\begin{definition}[SetOfZeros]\label{SetOfZeros}\lean{SetOfZeros}
    Let $R>0$ and $f:\overline{\mathbb{D}_R}\to\mathbb{C}$. Define the set of zeros $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:\abs{\rho}\leq R,\,f(\rho)=0\}$.
\end{definition}
%%-/



/-%%
\begin{definition}[ZeroOrder]\label{ZeroOrder}\lean{ZeroOrder}
    Let $0 < R<1$ and $f:\mathbb{C}\to\mathbb{C}$ be analtyic on neighborhoods of points in $\overline{\mathbb{D}_1}$. For any zero $\rho\in\mathcal{K}_f(R)$, we define $m_f(\rho)$ as the order of the zero $\rho$ w.r.t $f$.
\end{definition}
%%-/



/-%%
\begin{lemma}[ZeroFactorization]\label{ZeroFactorization}\lean{ZeroFactorization}
    Let $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be  analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. For all $\rho\in\mathcal{K}_f(1)$ there exists $h_\rho(z)$ that is analytic at $\rho$, $h_\rho(\rho)\neq 0$, and $f(z)=(z-\rho)^{m_f(\rho)}\,h_\rho(z)$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Since $f$ is analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ we know that there exists a series expansion about $\rho$:
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n.$$
    Now if we let $m$ be the smallest number such that $a_m\neq 0$, then
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n=\sum_{m\leq n}a_n\,(z-\rho)^n=(z-\rho)^m\sum_{m\leq n}a_n\,(z-\rho)^{n-m}=(z-\rho)^m\,h_\rho(z).$$
    Trivially, $h_\rho(z)$ is analytic at $\rho$ (we have written down the series expansion); now note that
    $$h_\rho(\rho)=\sum_{m\leq n}a_n(\rho-\rho)^{n-m}=\sum_{m\leq n}a_n0^{n-m}=a_m\neq 0.$$
\end{proof}
%%-/



/-%%
\begin{definition}[CFunction]\label{CFunction}\lean{CFunction}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a function $C_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows. This function is constructed by dividing $f(z)$ by a polynomial whose roots are the zeros of $f$ inside $\overline{\mathbb{D}_r}$.
    $$C_f(z)=\begin{cases}
        \displaystyle\frac{f(z)}{\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}\qquad\text{for }z\not\in\mathcal{K}_f(r) \\
        \displaystyle\frac{h_z(z)}{\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}(z-\rho)^{m_f(\rho)}}\qquad\text{for }z\in\mathcal{K}_f(r)
    \end{cases}$$
    where $h_z(z)$ comes from Lemma \ref{ZeroFactorization}.
\end{definition}
%%-/



/-%%
\begin{definition}[BlaschkeB]\label{BlaschkeB}\lean{BlaschkeB}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a function $B_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows.
    $$B_f(z)=C_f(z)\prod_{\rho\in\mathcal{K}_f(r)}\left(R-\frac{z\overline{\rho}}{R}\right)^{m_f(\rho)}$$
\end{definition}
%%-/



/-%%
\begin{lemma}[BlaschkeOfZero]\label{BlaschkeOfZero}\lean{BlaschkeOfZero}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. Then
    $$\abs{B_f(0)}=\abs{f(0)}\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Since $f(0)\neq 0$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$\abs{B_f(0)}=\abs{C_f(0)}\prod_{\rho\in\mathcal{K}_f(r)}R^{m_f(\rho)}=\abs{f(0)}\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[DiskBound]\label{DiskBound}\lean{DiskBound}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then $\abs{B_f(z)}\leq B$ for $\abs{z}\leq R$ also.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    For $\abs{z}=R$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$\abs{B_f(z)}=\abs{f(z)}\prod_{\rho\in\mathcal{K}_f(r)}\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}^{m_f(\rho)}.$$
    But note that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}=\frac{\abs{R^2-z\overline{\rho}}/R}{\abs{z-\rho}}=\frac{\abs{z}\cdot\abs{\overline{z-\rho}}/R}{\abs{z-\rho}}=1.$$
    So we have that $\abs{B_f(z)}=\abs{f(z)}\leq B$ when $\abs{z}=R$. Now by the maximum modulus principle, we know that the maximum of $\abs{B_f}$ must occur on the boundary where $\abs{z}=R$. Thus $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$.
\end{proof}
%%-/



/-%%
\begin{lemma}[JensenForm]\label{JensenForm}\lean{JensenForm}
    Let $B>1$ and $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}\leq B.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Since $f(0)=1$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into definition \ref{BlaschkeB},
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}=\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{r}\right)^{m_f(\rho)}\leq\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}=\abs{B_f(0)}\leq B$$
    whereby Lemma \ref{DiskBound} we know that $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$.
\end{proof}
%%-/



/-%%
\begin{lemma}[ZerosBound]\label{ZerosBound}\lean{ZerosBound}
    Let $B>1$ and $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then
    $$\abs{\mathcal{K}_f(r)}\leq\frac{\log B}{\log(R/r)}.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Using Lemma \ref{JensenForm} we have that
    $$(R/r)^{\abs{\mathcal{K}_f(r)}}=(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}1}\leq(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}\leq B.$$
    Taking the logarithm of both sides and rearranging gives the desired result.
\end{proof}
%%-/



/-%%
\begin{definition}[JBlaschke]\label{JBlaschke}\lean{JBlaschke}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$, define $L_f(z)=J_{B_f}(z)$ where $J$ is from Lemma \ref{LogOfAnalyticFunction} and $B_f$ is from Definition \ref{BlaschkeB}.
\end{definition}
%%-/



/-%%
\begin{lemma}[BlaschkeNonZero]\label{BlaschkeNonZero}\lean{BlaschkeNonZero}
    Let $0 < r < R<1$ and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$. Then $B_f(z)\neq 0$ for all $z\in\overline{\mathbb{D}_r}$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Suppose that $z\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{h_z(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}(z-\rho)^{m_f(\rho)}}.$$
    where $h_z(z)\neq 0$ according to Lemma \ref{ZeroFactorization}. Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint2}
        \abs{B_f(z)}=\abs{h_z(z)}\cdot\abs{R-\frac{\abs{z}^2}{R}}^{m_f(z)}\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}^{m_f(\rho)}.
    \end{equation}
    Trivially, $\abs{h_z(z)}\neq 0$. Now note that
    $$\abs{R-\frac{\abs{z}^2}{R}}=0\implies\abs{z}=R.$$
    However, this is a contradiction because $z\in\overline{\mathbb{D}_r}$ tells us that $\abs{z}\leq r < R$. Similarly, note that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}=0\implies\abs{z}=\frac{R^2}{\abs{\overline{\rho}}}.$$
    However, this is also a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that $R < R^2/\abs{\overline{\rho}}=\abs{z}$, but $z\in\overline{\mathbb{D}_r}$ tells us that $\abs{z}\leq r < R$. So, we know that
    $$\abs{R-\frac{\abs{z}^2}{R}}\neq 0\qquad\text{and}\qquad\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}\neq 0\quad\text{for all}\quad\rho\in\mathcal{K}_f(r)\setminus\{z\}.$$
    Applying this to Equation (\ref{pickupPoint2}) we have that $\abs{B_f(z)}\neq 0$. So, $B_f(z)\neq 0$.

    Now suppose that $z\not\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint3}
        \abs{B_f(z)}=\abs{f(z)}\prod_{\rho\in\mathcal{K}_f(r)}\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}^{m_f(\rho)}.
    \end{equation}
    We know that $\abs{f(z)}\neq 0$ since $z\not\in\mathcal{K}_f(r)$. Now note that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}=0\implies\abs{z}=\frac{R^2}{\abs{\overline{\rho}}}.$$
    However, this is a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that $R < R^2/\abs{\overline{\rho}}=\abs{z}$, but $z\in\overline{\mathbb{D}_r}$ tells us that $\abs{z}\leq r < R$. So, we know that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}\neq 0\quad\text{for all}\quad\rho\in\mathcal{K}_f(r).$$
    Applying this to Equation (\ref{pickupPoint3}) we have that $\abs{B_f(z)}\neq 0$. So, $B_f(z)\neq 0$.

    We have shown that $B_f(z)\neq 0$ for both $z\in\mathcal{K}_f(r)$ and $z\not\in\mathcal{K}_f(r)$, so the result follows.
\end{proof}
%%-/



/-%%
\begin{lemma}[JBlaschkeDerivBound]\label{JBlaschkeDerivBound}\lean{JBlaschkeDerivBound}
    Let $B>1$ and $0 < r' < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for all $\abs{z}\leq R$, then for all $\abs{z}\leq r'$
    $$\abs{L_f'(z)}\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    By Lemma \ref{DiskBound} we immediately know that $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$. Now since $L_f=J_{B_f}$ by Definition \ref{JBlaschke}, by Lemma \ref{LogOfAnalyticFunction} we know that
    $$L_f(0)=0\qquad\text{and}\qquad \mathfrak{R}L_f(z)=\log\abs{B_f(z)}-\log\abs{B_f(0)}\leq\log\abs{B_f(z)}\leq\log B$$
    for all $\abs{z}\leq r$. So by Theorem \ref{BorelCaratheodoryDeriv}, it follows that
    $$\abs{L_f'(z)}\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
    for all $\abs{z}\leq r'$.
\end{proof}
%%-/



/-%

Main Theorem: The Prime Number Theorem in strong form.
\begin{theorem}[PrimeNumberTheorem]\label{StrongPNT}\lean{PrimeNumberTheorem}\uses{thm:StrongZeroFree, ChebyshevPsi, SmoothedChebyshevClose, ZetaBoxEval}
There is a constant $c > 0$ such that
$$
\psi(x) = x + O(x \exp(-c \sqrt{\log x}))
$$
as $x\to \infty$.
\end{theorem}

%-/

-- *** Prime Number Theorem *** The `ChebyshevPsi` function is asymptotic to `x`.
-- theorem PrimeNumberTheorem : ∃ (c : ℝ) (hc : c > 0),
--     (ChebyshevPsi - id) =O[atTop] (fun (x : ℝ) ↦ x * Real.exp (-c * Real.sqrt (Real.log x))) := by
--  sorry
