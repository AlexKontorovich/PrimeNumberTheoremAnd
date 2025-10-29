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
import «PrimeNumberTheoremAnd».BorelCaratheodory
import «PrimeNumberTheoremAnd».DerivativeBound

open Nat Filter

--open scoped ArithmeticFunction

/-%%
    This upstreamed from https://github.com/math-inc/strongpnt/tree/main
%%-/

/-%%
\begin{theorem}[borelCaratheodory_closedBall]\label{borelCaratheodory_closedBall}\lean{borelCaratheodory_closedBall}\leanok
    Let $R,\,M>0$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and suppose $\Re f(z)\leq M$ for all $|z|\leq R$. Then for any $0 < r < R$,
    $$\sup_{|z|\leq r}|f(z)|\leq\frac{2Mr}{R-r}.$$
\end{theorem}
%%-/

/-%%
\begin{proof}\leanok
    Let
    $$f_M(z)=\frac{f(z)/z}{2M-f(z)}.$$
    Note that $2M-f(z)\neq 0$ because $\Re (2M-f(z))=2M-\Re f(z)\geq M>0$. Additionally, since $f(z)$ has a zero at $0$, we know that $f(z)/z$ is analytic on $|z|\leq R$. Likewise, $f_M(z)$ is analytic on $|z|\leq R$.

    Now note that $|f(z)|\leq|2M-f(z)|$ since $\Re f(z)\leq M$. Thus we have that
    $$|f_M(z)|=\frac{|f(z)|/|z|}{|2M-f(z)|}\leq\frac{1}{|z|}.$$
    Now by the maximum modulus principle, we know the maximum of $|f_M|$ must occur on the boundary where $|z|=R$. Thus, $|f_M(z)|\leq 1/R$ for all $|z|\leq R$. So for $|z|=r$ we have
    $$|f_M(z)|=\frac{|f(z)|/r}{|2M-f(z)|}\leq\frac{1}{R}\implies R\,|f(z)|\leq r\,|2M-f(z)|\leq 2Mr+r\,|f(z)|.$$
    Which by algebraic manipulation gives
    $$|f(z)|\leq\frac{2Mr}{R-r}.$$
    Once more, by the maximum modulus principle, we know the maximum of $|f|$ must occur on the boundary where $|z|=r$. Thus, the desired result immediately follows
\end{proof}
%%-/

-- The proof is in the StrongPNT.BorelCaratheodory import.


/-%%
\begin{lemma}[DerivativeBound]\label{DerivativeBound}\lean{DerivativeBound}
    Let $R,\,M>0$ and $0 < r < r' < R$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and suppose $\Re f(z)\leq M$ for all $|z|\leq R$. Then we have that
    $$|f'(z)|\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}$$
    for all $|z|\leq r$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{borelCaratheodory_closedBall}
    By Cauchy's integral formula we know that
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw=\frac{1}{2\pi }\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
    Thus,
    \begin{equation}\label{pickupPoint1}
        |f'(z)|=\left|\frac{1}{2\pi}\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt\right|\leq\frac{1}{2\pi}\int_0^{2\pi}\left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|\,dt.
    \end{equation}
    Now applying Theorem \ref{borelCaratheodory_closedBall}, and noting that $r'-r\leq|r'e^{it}-z|$, we have that
    $$\left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
    Substituting this into Equation (\ref{pickupPoint1}) and evaluating the integral completes the proof.
\end{proof}
%%-/



/-%%
\begin{theorem}[BorelCaratheodoryDeriv]\label{BorelCaratheodoryDeriv}\lean{BorelCaratheodoryDeriv}
    Let $R,\,M>0$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and suppose $\Re f(z)\leq M$ for all $|z|\leq R$. Then for any $0 < r < R$,
    $$|f'(z)|\leq\frac{16MR^2}{(R-r)^3}$$
    for all $|z|\leq r$.
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{DerivativeBound}
    Using Lemma \ref{DerivativeBound} with $r'=(R+r)/2$, and noting that $r < R$, we have that
    $$|f'(z)|\leq\frac{4M(R+r)^2}{(R-r)^3}\leq\frac{16MR^2}{(R-r)^3}.$$
\end{proof}
%%-/



/-%%
\begin{theorem}[LogOfAnalyticFunction]\label{LogOfAnalyticFunction}\lean{LogOfAnalyticFunction}
    Let $0 < r < R<1$. Let $B:\overline{\mathbb{D}_R}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_R}$ with $B(z)\neq 0$ for all $z\in\overline{\mathbb{D}_R}$. Then there exists $J_B:\overline{\mathbb{D}_r}\to\mathbb{C}$ that is analytic on neighborhoods of points in $\overline{\mathbb{D}_r}$ such that
    \begin{itemize}
        \item $J_B(0)=0$
        \item $J_B'(z)=B'(z)/B(z)$
        \item $\log|B(z)|-\log|B(0)|=\Re J_B(z)$
    \end{itemize}
    for all $z\in\overline{\mathbb{D}_r}$.
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{}
    We let $J_B(z)=\mathrm{Log}\,B(z)-\mathrm{Log}\,B(0)$. Then clearly, $J_B(0)=0$ and $J_B'(z)=B'(z)/B(z)$. Showing the third property is a little more difficult, but by no standards terrible. Exponentiating $J_B(z)$ we have that
    $$\exp(J_B(z))=\exp(\mathrm{Log}\,B(z)-\mathrm{Log}\,B(0))=\frac{B(z)}{B(0)}\implies B(z)=B(0)\exp(J_B(z)).$$
    Now taking the modulus
    $$|B(z)|=|B(0)|\cdot|\exp(J_B(z))|=|B(0)|\cdot\exp(\Re J_B(z)).$$
    Taking the real logarithm of both sides and rearranging gives the third point.
\end{proof}
%%-/



/-%%
\begin{definition}[SetOfZeros]\label{SetOfZeros}\lean{SetOfZeros}
    Let $R>0$ and $f:\overline{\mathbb{D}_R}\to\mathbb{C}$. Define the set of zeros $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:|\rho|\leq R,\,f(\rho)=0\}$.
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
    $$|B_f(0)|=|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{BlaschkeB}
    Since $f(0)\neq 0$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(0)|=|C_f(0)|\prod_{\rho\in\mathcal{K}_f(r)}R^{m_f(\rho)}=|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[DiskBound]\label{DiskBound}\lean{DiskBound}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $|f(z)|\leq B$ for $|z|\leq R$, then $|B_f(z)|\leq B$ for $|z|\leq R$ also.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{BlaschkeB}
    For $|z|=R$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.$$
    But note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=\frac{|R^2-z\overline{\rho}|/R}{|z-\rho|}=\frac{|z|\cdot|\overline{z-\rho}|/R}{|z-\rho|}=1.$$
    So we have that $|B_f(z)|=|f(z)|\leq B$ when $|z|=R$. Now by the maximum modulus principle, we know that the maximum of $|B_f|$ must occur on the boundary where $|z|=R$. Thus $|B_f(z)|\leq B$ for all $|z|\leq R$.
\end{proof}
%%-/



/-%%
\begin{theorem}[ZerosBound]\label{ZerosBound}\lean{ZerosBound}
    Let $B>1$ and $0< r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$ for $|z|\leq R$, then
    $$\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\leq\frac{\log B}{\log(R/r)}.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{BlaschkeB, DiskBound}
    Since $f(0)=1$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}=\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{r}\right)^{m_f(\rho)}\leq\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}=|B_f(0)|\leq B$$
    whereby Lemma \ref{DiskBound} we know that $|B_f(z)|\leq B$ for all $|z|\leq R$. Taking the logarithm of both sides and rearranging gives the desired result.
\end{proof}
%%-/



/-%%
\begin{definition}[JBlaschke]\label{JBlaschke}\lean{JBlaschke}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$, define $L_f(z)=J_{B_f}(z)$ where $J$ is from Theorem \ref{LogOfAnalyticFunction} and $B_f$ is from Definition \ref{BlaschkeB}.
\end{definition}
%%-/



/-%%
\begin{lemma}[BlaschkeNonZero]\label{BlaschkeNonZero}\lean{BlaschkeNonZero}
    Let $0 < r < R<1$ and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$. Then $B_f(z)\neq 0$ for all $z\in\overline{\mathbb{D}_r}$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{ZeroFactorization, BlaschkeB}
    Suppose that $z\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{h_z(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}(z-\rho)^{m_f(\rho)}}.$$
    where $h_z(z)\neq 0$ according to Lemma \ref{ZeroFactorization}. Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint2}
        |B_f(z)|=|h_z(z)|\cdot\left|R-\frac{|z|^2}{R}\right|^{m_f(z)}\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    \end{equation}
    Trivially, $|h_z(z)|\neq 0$. Now note that
    $$\left|R-\frac{|z|^2}{R}\right|=0\implies|z|=R.$$
    However, this is a contradiction because $z\in\overline{\mathbb{D}_r}$ tells us that $|z|\leq r < R$. Similarly, note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is also a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that $|z|\leq r < R$. So, we know that
    $$\left|R-\frac{|z|^2}{R}\right|\neq 0\qquad\text{and}\qquad\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0\quad\text{for all}\quad\rho\in\mathcal{K}_f(r)\setminus\{z\}.$$
    Applying this to Equation (\ref{pickupPoint2}) we have that $|B_f(z)|\neq 0$. So, $B_f(z)\neq 0$.

    Now suppose that $z\not\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint3}
        |B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    \end{equation}
    We know that $|f(z)|\neq 0$ since $z\not\in\mathcal{K}_f(r)$. Now note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that $|z|\leq r < R$. So, we know that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0\quad\text{for all}\quad\rho\in\mathcal{K}_f(r).$$
    Applying this to Equation (\ref{pickupPoint3}) we have that $|B_f(z)|\neq 0$. So, $B_f(z)\neq 0$.

    We have shown that $B_f(z)\neq 0$ for both $z\in\mathcal{K}_f(r)$ and $z\not\in\mathcal{K}_f(r)$, so the result follows.
\end{proof}
%%-/



/-%%
\begin{theorem}[JBlaschkeDerivBound]\label{JBlaschkeDerivBound}\lean{JBlaschkeDerivBound}
    Let $B>1$ and $0 < r' < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$ for all $|z|\leq R$, then for all $|z|\leq r'$
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{DiskBound, JBlaschke, LogOfAnalyticFunction, BorelCaratheodoryDeriv}
    By Lemma \ref{DiskBound} we immediately know that $|B_f(z)|\leq B$ for all $|z|\leq R$. Now since $L_f=J_{B_f}$ by Definition \ref{JBlaschke}, by Theorem \ref{LogOfAnalyticFunction} we know that
    $$L_f(0)=0\qquad\text{and}\qquad \Re L_f(z)=\log|B_f(z)|-\log|B_f(0)|\leq\log|B_f(z)|\leq\log B$$
    for all $|z|\leq r$. So by Theorem \ref{BorelCaratheodoryDeriv}, it follows that
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
    for all $|z|\leq r'$.
\end{proof}
%%-/



/-%%
\begin{theorem}[FinalBound]\label{FinalBound}\lean{FinalBound}
    Let $B>1$ and $0 < r' < r < R' < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$ for all $|z|\leq R$, then for all $z\in\overline{\mathbb{D}_{R'}}\setminus\mathcal{K}_f(R')$ we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|\leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log B.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{CFunction, BlaschkeB, JBlaschke, LogOfAnalyticFunction, ZerosBound, JBlaschkeDerivBound}
    Since $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we know that $z\not\in\mathcal{K}_f(R')$; thus, by Definition \ref{CFunction} we know that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(R')}(z-\rho)^{m_f(\rho)}}.$$
    Substituting this into Definition \ref{BlaschkeB} we have that
    $$B_f(z)=f(z)\prod_{\rho\in\mathcal{K}_f(R')}\left(\frac{R-z\overline{\rho}/R}{z-\rho}\right)^{m_f(\rho)}.$$
    Taking the complex logarithm of both sides we have that
    $$\mathrm{Log}\,B_f(z)=\mathrm{Log}\,f(z)+\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho)\,\mathrm{Log}(R-z\overline{\rho}/R)-\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho)\,\mathrm{Log}(z-\rho).$$
    Taking the derivative of both sides we have that
    $$\frac{B_f'}{B_f}(z)=\frac{f'}{f}(z)+\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-R^2/\rho}-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}.$$
    By Definition \ref{JBlaschke} and Theorem \ref{LogOfAnalyticFunction} we recall that
    $$L_f(z)=J_{B_f}(z)=\mathrm{Log}\,B_f(z)-\mathrm{Log}\,B_f(0).$$
    Taking the derivative of both sides we have that $L_f'(z)=(B_f'/B_f)(z)$. Thus,
    $$\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}=L_f'(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-R^2/\rho}.$$
    Now since $z\in\overline{\mathbb{D}_{R'}}$ and $\rho\in\mathcal{K}_f(R')$, we know that $R^2/R'-R'\leq|z-R^2/\rho|$. Thus by the triangle inequality we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|\leq|L_f'(z)|+\left(\frac{1}{R^2/R'-R'}\right)\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho).$$
    Now by Theorem \ref{ZerosBound} and \ref{JBlaschkeDerivBound} we get our desired result with a little algebraic manipulation.
\end{proof}
%%-/



/-%%
\begin{theorem}[ZetaFixedLowerBound]\label{ZetaFixedLowerBound}\lean{ZetaFixedLowerBound}
    For all $t\in\mathbb{R}$ one has
    $$|\zeta(3/2+it)|\geq\frac{\zeta(3)}{\zeta(3/2)}.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{}
    From the Euler product expansion of $\zeta$, we have that for $\Re s>1$
    $$\zeta(s)=\prod_p\frac{1}{1-p^{-s}}.$$
    Thus, we have that
    $$\frac{\zeta(2s)}{\zeta(s)}=\prod_p\frac{1-p^{-s}}{1-p^{-2s}}=\prod_p\frac{1}{1+p^{-s}}.$$
    Now note that $|1-p^{-(3/2+it)}|\leq 1+|p^{-(3/2+it)}|=1+p^{-3/2}$. Thus,
    $$|\zeta(3/2+it)|=\prod_p\frac{1}{|1-p^{-(3/2+it)}|}\geq\prod_p\frac{1}{1+p^{-3/2}}=\frac{\zeta(3)}{\zeta(3/2)}$$
    for all $t\in\mathbb{R}$ as desired.
\end{proof}
%%-/



/-%%
\begin{lemma}[ZetaAltFormula]\label{ZetaAltFormula}\lean{ZetaAltFormula}
    Let
    $$\zeta_0(s)=1+\frac{1}{s-1}-s\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}.$$
    We have that $\zeta(s)=\zeta_0(s)$ for $\sigma>1$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Note that for $\sigma>1$ we have
    $$\zeta(s)=\sum_{n=1}^\infty\frac{1}{n^s}=\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=1}^\infty\frac{n-1}{n^s}=\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=0}^\infty\frac{n}{(n+1)^s}=\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=1}^\infty\frac{n}{(n+1)^s}.$$
    Thus
    $$\zeta(s)=\sum_{n=1}^\infty n\,(n^{-s}-(n+1)^{-s}).$$
    Now we note that
    $$s\int_n^{n+1}x^{-s}\,\frac{dx}{x}=s\left(-\frac{1}{s}\,x^{-s}\right)_n^{n+1}=n^{-s}-(n+1)^{-s}.$$
    So, substituting this we have
    $$\zeta(s)=\sum_{n=1}^\infty n\,(n^{-s}-(n+1)^{-s})=s\sum_{n=1}^\infty n\int_n^{n+1}x^{-s}\,\frac{dx}{x}=s\int_1^\infty\lfloor x\rfloor\,x^{-s}\,\frac{dx}{x}.$$
    But noting that $\lfloor x\rfloor =x-\{x\}$ we have that
    $$\zeta(s)=s\int_1^\infty\lfloor x\rfloor\,x^{-s}\,\frac{dx}{x}=s\int_1^\infty x^{-s}\,dx-s\int_1^\infty \{x\}\,x^{-s}\,\frac{dx}{x}.$$
    Evaluating the first integral completes the result.
\end{proof}
%%-/



/-%%
\begin{lemma}[ZetaAltFormulaAnalytic]\label{ZetaAltFormulaAnalytic}\lean{ZetaAltFormulaAnalytic}
    We have that $\zeta_0(s)$ is analytic for all $s\in S$ where $S=\{s\in\mathbb{C}:\Re s>0,\,s\neq 1\}$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Note that we have
    $$\left|\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}\right|\leq\int_1^\infty|\{x\}\,x^{-s-1}|\,dx\leq\int_1^\infty x^{-\sigma-1}\,dx=\frac{1}{\sigma}.$$
    So this integral converges uniformly on compact subsets of $S$, which tells us that it is analytic on $S$. So it immediately follows that $\zeta_0(s)$ is analytic on $S$ as well, since $S$ avoids the pole at $s=1$ coming from the $(s-1)^{-1}$ term.
\end{proof}
%%-/



/-%%
\begin{lemma}[ZetaExtend]\label{ZetaExtend}\lean{ZetaExtend}
    We have that
    $$\zeta(s)=1+\frac{1}{s-1}-s\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}$$
    for all $s\in S$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    This is an immediate consequence of the identity theorem.
\end{proof}
%%-/



/-%%
\begin{theorem}[GlobalBound]\label{GlobalBound}\lean{GlobalBound}
    For all $s\in\mathbb{C}$ with $|s|\leq 1$ and $t\in\mathbb{R}$ with $|t|\geq 3$, we have that
    $$|\zeta(s+3/2+it)|\leq 7+2\,|t|.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{ZetaExtend}
    For the sake of clearer proof writing let $z=s+3/2+it$. Since $|s|\leq 1$ we know that $1/2\leq\Re z$; additionally, as $|t|\geq 3$, we know $z\in S$. Thus, from Lemma \ref{ZetaExtend} we know that
    $$|\zeta(z)|\leq 1+\frac{1}{|z-1|}+|z|\cdot\left|\int_1^\infty\{x\}\,x^{-z}\,\frac{dx}{x}\right|$$
    by applying the triangle inequality. Now note that $|z-1|\geq 1$. Likewise,
    $$|z|\cdot\left|\int_1^\infty\{x\}\,x^{-z}\,\frac{dx}{x}\right|\leq|z|\int_1^\infty|\{x\}\,x^{-z-1}|\,dx\leq|z|\int_1^\infty x^{-\Re z-1}\,dx=\frac{|z|}{\Re z}\leq 2\,|z|.$$
    Thus we have that,
    $$|\zeta(s+3/2+it)|=|\zeta(z)|\leq 1+1+2\,|z|=2+2\,|s+3/2+it|\leq2+2\,|s|+3+2\,|it|\leq 7+2\,|t|.$$
\end{proof}
%%-/



/-%%
\begin{theorem}[LogDerivZetaFinalBound]\label{LogDerivZetaFinalBound}\lean{LogDerivZetaFinalBound}
    Let $t\in\mathbb{R}$ with $|t|\geq 3$ and $0 < r' < r < R' < R<1$. If  $f(z)=\zeta(z+3/2+it)$, then for all $z\in\overline{\mathbb{D}_R'}\setminus\mathcal{K}_f(R')$ we have that
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|\ll\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log|t|.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{ZetaFixedLowerBound, GlobalBound, FinalBound}
    Let $g(z)=\zeta(z+3/2+it)/\zeta(3/2+it)$. Note that $g(0)=1$ and for $|z|\leq R$
    $$|g(z)|=\frac{|\zeta(z+3/2+it)|}{|\zeta(3/2+it)|}\leq\frac{\zeta(3/2)}{\zeta(3)}\cdot(7+2\,|t|)\leq\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\,|t|$$
    by Theorems \ref{ZetaFixedLowerBound} and \ref{GlobalBound}. Thus by Theorem \ref{FinalBound} we have that
    $$\left|\frac{g'}{g}(z)-\sum_{\rho\in\mathcal{K}_g(R')}\frac{m_g(\rho)}{z-\rho}\right|\leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\left(\log|t|+\log\left(\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\right)\right).$$
    Now note that $f'/f=g'/g$, $\mathcal{K}_f(R')=\mathcal{K}_g(R')$, and $m_g(\rho)=m_f(\rho)$ for all $\rho\in\mathcal{K}_f(R')$. Thus we have that,
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|\ll\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log|t|$$
    where the implied constant $C$ is taken to be
    $$C\geq 1+\frac{\log((13\,\zeta(3/2))/(3\,\zeta(3)))}{\log 3}.$$
\end{proof}
%%-/



/-%%
\begin{definition}[ZeroWindows]\label{ZeroWindows}\lean{ZeroWindows}
    Let $\mathcal{Z}_t=\{\rho\in\mathbb{C}:\zeta(\rho)=0,\,|\rho-(3/2+it)|\leq 5/6\}$.
\end{definition}
%%-/



/-%%
\begin{lemma}[SumBoundI]\label{SumBoundI}\lean{SumBoundI}
    For all $\delta\in (0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 3$ we have
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)-\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|\ll\log|t|.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{LogDerivZetaFinalBound}
    We apply Theorem \ref{LogDerivZetaFinalBound} where $r'=2/3$, $r=3/4$, $R'=5/6$, and $R=8/9$. Thus, for all $z\in\overline{\mathbb{D}_{5/6}}\setminus\mathcal{K}_f(5/6)$ we have that
    $$\left|\frac{\zeta'}{\zeta}(z+3/2+it)-\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{z-\rho}\right|\ll\log|t|$$
    where $f(z)=\zeta(z+3/2+it)$ for $t\in\mathbb{R}$ with $|t|\geq 3$. Now if we let $z=-1/2+\delta$, then $z\in(-1/2,1/2)\subseteq\overline{\mathbb{D}_{5/6}}$. Additionally, $f(z)=\zeta(1+\delta+it)$, where $1+\delta+it$ lies in the zero-free region where $\sigma>1$. Thus, $z\not\in\mathcal{K}_f(5/6)$. So,
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)-\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{-1/2+\delta-\rho}\right|\ll\log|t|.$$
    But now note that if $\rho\in\mathcal{K}_f(5/6)$, then $\zeta(\rho+3/2+it)=0$ and $|\rho|\leq 5/6$. Thus, $\rho+3/2+it\in\mathcal{Z}_t$. Additionally, note that $m_f(\rho)=m_\zeta(\rho+3/2+it)$. So changing variables using these facts gives us that
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)-\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|\ll\log|t|.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[ShiftTwoBound]\label{ShiftTwoBound}\lean{ShiftTwoBound}
    For all $\delta\in (0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 3$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\ll\log|t|.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{SumBoundI}
    Note that, for $\rho\in\mathcal{Z}_{2t}$
    \begin{align*}
        \Re \left(\frac{1}{1+\delta+2it-\rho}\right)&=\Re \left(\frac{1+\delta-2it-\overline{\rho}}{(1+\delta+2it-\rho)(1+\delta-2it-\overline{\rho})}\right) \\
        &=\frac{\Re (1+\delta-2it-\overline{\rho})}{|1+\delta+2it-\rho|^2}=\frac{1+\delta-\Re \rho}{(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2}.
    \end{align*}
    Now since $\rho\in\mathcal{Z}_{2t}$, we have that $|\rho-(3/2+2it)|\leq 5/6$. So, we have $\Re \rho\in(2/3,7/3)$ and $\mathfrak{I}\rho\in(2t-5/6,2t+5/6)$. Thus, we have that
    $$1/3<1+\delta-\Re \rho\qquad\text{and}\qquad(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2<16/9+25/36=89/36.$$
    Which implies that
    \begin{equation}\label{pickupPoint4}
        0\leq\frac{12}{89}<\frac{1+\delta-\Re \rho}{(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2}=\Re \left(\frac{1}{1+\delta+2it-\rho}\right).
    \end{equation}
    Note that, from Lemma \ref{SumBoundI}, we have
    $$\sum_{\rho\in\mathcal{Z}_{2t}}m_\zeta(\rho)\,\Re \left(\frac{1}{1+\delta+2it-\rho}\right)-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\leq\left|\frac{\zeta'}{\zeta}(1+\delta+2it)-\sum_{\rho\in\mathcal{Z}_{2t}}\frac{m_\zeta(\rho)}{1+\delta+2it-\rho}\right|\ll\log|2t|.$$
    Since $m_\zeta(\rho)\geq 0$ for all $\rho\in\mathcal{Z}_{2t}$, the inequality from Equation (\ref{pickupPoint4}) tells us that by subtracting the sum from both sides we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\ll\log|2t|.$$
    Noting that $\log|2t|=\log(2)+\log|t|\leq2\log|t|$ completes the proof.
\end{proof}
%%-/



/-%%
\begin{lemma}[ShiftOneBound]\label{ShiftOneBound}\lean{ShiftOneBound}
    There exists $C>0$ such that for all $\delta\in(0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 3$; if $\zeta(\rho)=0$ with $\rho=\sigma+it$, then
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)\leq -\frac{1}{1+\delta-\sigma}+C\log|t|.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{SumBoundI}
    Note that for $\rho'\in\mathcal{Z}_t$
    \begin{align*}
        \Re \left(\frac{1}{1+\delta+it-\rho'}\right)&=\Re \left(\frac{1+\delta-it-\overline{\rho'}}{(1+\delta+it-\rho')(1+\delta-it-\overline{\rho'})}\right) \\
        &=\frac{\Re (1+\delta-it-\overline{\rho'})}{|1+\delta+it-\rho'|^2}=\frac{1+\delta-\Re \rho'}{(1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2}.
    \end{align*}
    Now since $\rho'\in\mathcal{Z}_t$, we have that $|\rho-(3/2+it)|\leq 5/6$. So, we have $\Re \rho'\in(2/3,7/3)$ and $\mathfrak{I}\rho'\in(t-5/6,t+5/6)$. Thus we have that
    $$1/3<1+\delta-\Re \rho'\qquad\text{and}\qquad (1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2<16/9+25/36=89/36.$$
    Which implies that
    \begin{equation}\label{pickupPoint5}
        0\leq\frac{12}{89}<\frac{1+\delta-\Re \rho'}{(1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2}=\Re \left(\frac{1}{1+\delta+it-\rho'}\right).
    \end{equation}
    Note that, from Lemma \ref{SumBoundI}, we have
    $$\sum_{\rho\in\mathcal{Z}_t}m_\zeta(\rho)\,\Re \left(\frac{1}{1+\delta+it-\rho}\right)-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)\leq\left|\frac{\zeta'}{\zeta}(1+\delta+it)-\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|\ll\log|t|.$$
    Since $m_\zeta(\rho)\geq 0$ for all $\rho'\in\mathcal{Z}_t$, the inequality from Equation (\ref{pickupPoint5}) tells us that by subtracting the sum over all $\rho'\in\mathcal{Z}_t\setminus\{\rho\}$ from both sides we have
    $$\frac{m_\zeta(\rho)}{\Re (1+\delta+it-\rho)}-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)\ll\log|t|.$$
    But of course we have that $\Re (1+\delta+it-\rho)=1+\delta-\sigma$. So subtracting this term from both sides and recalling the implied constant we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)\leq -\frac{m_\zeta(\rho)}{1+\delta-\sigma}+C\log|t|.$$
    We have that $\sigma\leq 1$ since $\zeta$ is zero free on the right half plane $\sigma>1$. Thus $0<1+\delta-\sigma$. Noting this in combination with the fact that $1\leq m_\zeta(\rho)$ completes the proof.
\end{proof}
%%-/



/-%%
\begin{lemma}[ShiftZeroBound]\label{ShiftZeroBound}\lean{ShiftZeroBound}
    For all $\delta\in(0,1)$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\frac{1}{\delta}+O(1).$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{riemannZetaLogDerivResidue}
    From Theorem \ref{riemannZetaLogDerivResidue} we know that
    $$-\frac{\zeta'}{\zeta}(s)=\frac{1}{s-1}+O(1).$$
    Changing variables $s\mapsto 1+\delta$ and applying the triangle inequality we have that
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\left|-\frac{\zeta'}{\zeta}(1+\delta)\right|\leq\frac{1}{\delta}+O(1).$$
\end{proof}
%%-/



/-%%
\begin{lemma}[ThreeFourOneTrigIdentity]\label{ThreeFourOneTrigIdentity}\lean{ThreeFourOneTrigIdentity}
    We have that
    $$0\leq 3+4\cos\theta+\cos2\theta$$
    for all $\theta\in\mathbb{R}$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    We know that $\cos(2\theta)=2\cos^2\theta-1$, thus
    $$3+4\cos\theta+\cos2\theta=2+4\cos\theta+2\cos^2\theta=2\,(1+\cos\theta)^2.$$
    Noting that $0\leq 1+\cos\theta$ completes the proof.
\end{proof}
%%-/



/-%%
\begin{theorem}[ZeroInequality]\label{ZeroInequality}\lean{ZeroInequality}
    There exists a constant $0 < E<1$ such that for all $\rho=\sigma+it$ with $\zeta(\rho)=0$ and $|t|\geq 3$, one has
    $$\sigma\leq 1-\frac{E}{\log|t|}.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{LogDerivativeDirichlet, ThreeFourOneTrigIdentity, ShiftZeroBound, ShiftOneBound, ShiftTwoBound}
    From Theorem \ref{LogDerivativeDirichlet} when $\Re s>1$ we have
    $$-\frac{\zeta'}{\zeta}(s)=\sum_{1\leq n}\frac{\Lambda(n)}{n^s}.$$
    Thus,
    $$-3\,\frac{\zeta'}{\zeta}(1+\delta)-4\,\frac{\zeta'}{\zeta}(1+\delta+it)-\frac{\zeta'}{\zeta}(1+\delta+2it)=\sum_{1\leq n}\Lambda(n)\,n^{-(1+\delta)}\left(3+4n^{-it}+n^{-2it}\right).$$
    Now applying Euler's identity
    \begin{align*}
        -3\,\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)&-4\,\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right) \\
        &\qquad\qquad\qquad=\sum_{1\leq n}\Lambda(n)\,n^{-(1+\delta)}\left(3+4\cos(-it\log n)+\cos(-2it\log n)\right)
    \end{align*}
    By Lemma \ref{ThreeFourOneTrigIdentity} we know that the series on the right hand side is bounded below by $0$, and by Lemmas \ref{ShiftTwoBound}, \ref{ShiftOneBound}, and \ref{ShiftZeroBound} we have an upper bound on the left hand side. So,
    $$0\leq\frac{3}{\delta}+3A-\frac{4}{1+\delta-\sigma}+4B\log|t|+C\log|t|$$
    where $A$, $B$, and $C$ are the implied constants coming from Lemmas \ref{ShiftZeroBound}, \ref{ShiftOneBound}, and \ref{ShiftTwoBound} respectively. By choosing $D\geq 3A/\log 3+4B+C$ we have
    $$\frac{4}{1+\delta-\sigma}\leq\frac{3}{\delta}+D\log|t|$$
    by some manipulation. Now if we choose $\delta=(2D\log|t|)^{-1}$ then we have
    $$\frac{4}{1-\sigma+1/(2D\log|t|)}\leq7D\log|t|.$$
    So with some manipulation we have that
    $$\sigma\leq 1-\frac{1}{14D\log|t|}.$$
    This is exactly the desired result with the constant $E=(14D)^{-1}$
\end{proof}
%%-/



/-%%
\begin{definition}[DeltaT]\label{DeltaT}\lean{DeltaT}
    Let $\delta_t=E/\log|t|$ where $E$ is the constant coming from Theorem \ref{567}.
\end{definition}
%%-/



/-%%
\begin{lemma}[DeltaRange]\label{DeltaRange}\lean{DeltaRange}
    For all $t\in\mathbb{R}$ with $|t|\geq 3$ we have that
    $$\delta_t<1/28.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{ZeroInequality, ShiftZeroBound, ShiftOneBound, ShiftTwoBound, SumBoundI, LogDerivZetaFinalBound}
    Note that $\delta_t=E/\log|t|$ where $E$ is the implied constant from Lemma \ref{ZeroInequality}. But we know that $E=(14D)^{-1}$ where $D\geq 3A/\log 3+4B+C$ where $A$, $B$, and $C$ are the constants coming from Lemmas \ref{ShiftZeroBound}, \ref{ShiftOneBound}, and \ref{ShiftTwoBound} respectively. Thus,
    $$E\leq\frac{1}{14\,(3A/\log 3+4B+C)}.$$
    But note that $A\geq 0$ and $B\geq 0$ by Lemmas \ref{ShiftZeroBound} and \ref{ShiftOneBound} respectively. However, we have that
    $$C\geq 2+\frac{2\log((13\,\zeta(3/2))/(3\,\zeta(3)))}{\log 3}$$
    by Theorem \ref{LogDerivZetaFinalBound} with Lemmas \ref{SumBoundI} and \ref{ShiftTwoBound}. So, by a very lazy estimate we have $C\geq 2$ and $E\leq 1/28$. Thus,
    $$\delta_t=\frac{E}{\log|t|}\leq\frac{1}{28\,\log3}<\frac{1}{28}.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[SumBoundII]\label{SumBoundII}\lean{SumBoundII}
    For all $t\in\mathbb{R}$ with $|t|\geq 3$ and $z=\sigma+it$ where $1-\delta_t/3\leq\sigma\leq 3/2$, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)-\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{DeltaRange, LogDerivZetaFinalBound, ZeroInequality}
    By Lemma \ref{DeltaRange} we have that
    $$-43/84<-1/2-\delta_t/3\leq\sigma-3/2\leq0.$$
    We apply Theorem \ref{LogDerivZetaFinalBound} where $r'=2/3$, $r=3/4$, $R'=5/6$, and $R=8/9$. Thus for all $z\in\overline{\mathbb{D}_{5/6}}\setminus\mathcal{K}_f(5/6)$ we have that
    $$\left|\frac{\zeta'}{\zeta}(z+3/2+it)-\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{z-\rho}\right|\ll\log|t|$$
    where $f(z)=\zeta(z+3/2+it)$ for $t\in\mathbb{R}$ with $|t|\geq 3$. Now if we let $z=\sigma-3/2$, then $z\in(-43/84,0)\subseteq\overline{\mathbb{D}_{5/6}}$. Additionally, $f(z)=\zeta(\sigma+it)$, where $\sigma+it$ lies in the zero free region given by Lemma \ref{ZeroInequality} since $\sigma\geq 1-\delta_t/3\geq 1-\delta_t$. Thus, $z\not\in\mathcal{K}_f(5/6)$. So,
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)-\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{\sigma-3/2-\rho}\right|\ll\log|t|.$$
    But now note that if $\rho\in\mathcal{K}_f(5/6)$, then $\zeta(\rho+3/2+it)=0$ and $|\rho|\leq 5/6$. Additionally, note that $m_f(\rho)=m_\zeta(\rho+3/2+it)$. So changing variables using these facts gives us that
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)-\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{\sigma+it-\rho}\right|\ll\log|t|.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[GapSize]\label{GapSize}\lean{GapSize}
   Let $t\in\mathbb{R}$ with $|t|\geq 4$ and $z=\sigma+it$ where $1-\delta_t/3\leq\sigma\leq 3/2$. Additionally, let $\rho\in\mathcal{Z}_t$. Then we have that
   $$|z-\rho|\geq\delta_t/6.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{ZeroInequality}
    Let $\rho=\sigma'+it'$ and note that since $\rho\in\mathcal{Z}_t$, we have $t'\in(t-5/6,t+5/6)$. Thus, if $t>1$ we have
    $$\log|t'|\leq\log|t+5/6|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    And otherwise if $t<-1$ we have
    $$\log|t'|\leq\log|t-5/6|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    So by taking reciprocals and multiplying through by a constant we have that $\delta_t\leq2\delta_{t'}$. Now note that since $\rho\in\mathcal{Z}_t$ we know that $\sigma'\leq 1-\delta_{t'}$ by Theorem \ref{ZeroInequality} (here we use the fact that $|t|\geq 4$ to give us that $|t'|\geq 3$). Thus,
    $$\delta_t/6\leq\delta_{t'}-\delta_t/3=1-\delta_t/3-(1-\delta_{t'})\leq\sigma-\sigma'\leq|z-\rho|.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[LogDerivZetaUniformLogSquaredBoundStrip]\label{LogDerivZetaUniformLogSquaredBoundStrip}\lean{LogDerivZetaUniformLogSquaredBoundStrip}
    There exists a constant $F\in(0,1/2)$ such that for all $t\in\mathbb{R}$ with $|t|\geq 4$ one has
    $$1-\frac{F}{\log|t|}\leq\sigma\leq 3/2\implies\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\ll\log^2|t|$$
    where the implied constant is uniform in $\sigma$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{ZeroInequality, SumBoundII, GapSize, ZetaFixedLowerBound, GlobalBound, ZerosBound}
    Take $F=E/3$ where $E$ comes from Theorem \ref{ZeroInequality}. Then we have that $\sigma\geq 1-\delta_t/3$. So, we apply Lemma \ref{SumBoundII}, which gives us that
    $$\left|\frac{\zeta'}{\zeta}(z)-\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
    Using the reverse triangle inequality and rearranging, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|\leq\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{|z-\rho|}+C\,\log|t|$$
    where $C$ is the implied constant in Lemma \ref{SumBoundII}. Now applying Lemma \ref{GapSize} we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|\leq\frac{6}{\delta_t}\sum_{\rho\in\mathcal{Z}_t}m_\zeta(\rho)+C\,\log|t|.$$
    Now let $f(z)=\zeta(z+3/2+it)/\zeta(3/2+it)$ with $\rho=\rho'+3/2+it$. Then if $\rho\in\mathcal{Z}_t$ we have that
    $$0=\zeta(\rho)=\zeta(\rho'+3/2+it)=f(\rho')$$
    with the same multiplicity of zero, that is $m_\zeta(\rho)=m_f(\rho')$. And also if $\rho\in\mathcal{Z}_t$ then
    $$5/6\geq|\rho-(3/2+it)|=|\rho'|.$$
    Thus we change variables to have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|\leq\frac{6}{\delta_t}\sum_{\rho'\in\mathcal{K}_f(5/6)}m_f(\rho')+C\,\log|t|.$$
    Now note that $f(0)=1$ and for $|z|\leq 8/9$ we have
    $$|f(z)|=\frac{|\zeta(z+3/2+it)|}{|\zeta(3/2+it)|}\leq\frac{\zeta(3/2)}{\zeta(3)}\cdot(7+2\,|t|)\leq\frac{15\,\zeta(3/2)}{4\,\zeta(3)}\,|t|$$
    by Theorems \ref{ZetaFixedLowerBound} and \ref{GlobalBound}. Thus by Theorem \ref{ZerosBound} we have that
    $$\sum_{\rho'\in\mathcal{K}_f(5/6)}m_f(\rho')\leq\frac{\log|t|+\log(15\,\zeta(3/2)/(4\,\zeta(3)))}{\log((8/9)/(5/6))}\leq D\log|t|$$
    where $D$ is taken to be sufficiently large. Recall, by definition that, $\delta_t=E/\log|t|$ with $E$ coming from Theorem \ref{ZeroInequality}. By using this fact and the above, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|\ll\log^2|t|+\log|t|$$
    where the implied constant is taken to be bigger than $\max(6D/E,C)$. We know that the RHS is bounded above by $\ll\log^2|t|$; so the result follows.
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
