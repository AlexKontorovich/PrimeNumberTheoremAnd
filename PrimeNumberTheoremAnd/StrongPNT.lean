import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction

open Nat Filter

--open scoped ArithmeticFunction

/-%
From https://math-inc.github.io/strongpnt/blueprint/
NEED TO INCLUDE:

--------------------------------------------------

Complex Analysis (1)
DEF 90 (Open Disk) ✓
LEM 91 (Closed Disk) ✓
§1.1:
THM 133 (BC I) ✓
§1.2:
LEM 177 (Derivative Bound) ✓
THM 198 (BC II) ✓
§1.3:
N/A
§1.4:
LEM 238 (Log of Analytic Function) ✓

--------------------------------------------------

Log Derivative (2)
DEF 240 (Sets of Zeros) ✓
§2.1:
DEF 250 (Zero Order) ✓
LEM 256 (Zero Factorization) ✓
DEF 257 (C Function) ✓
DEF 275 (Blashcke B) ✓
§2.2:
LEM 304 (Abs of Blashcke) ✓
LEM 317 (Disk Bound) ✓
LEM 320 (Jensen Form) ✓
LEM 329 (Zeros Bound) ✓
§2.3:
DEF 330 (Log Function) ✓
LEM 332 (Never Zero) ✓
LEM 343 (Apply BC) ✓
§2.4:

--------------------------------------------------

Riemann Zeta Function (3)

--------------------------------------------------

Zero Free Region (4)
LEM 620 (Uniform Bound on ζ'/ζ)
%-/



/-%%
    This section is based off work from https://github.com/math-inc/strongpnt/tree/main
%%-/



/-%%
\begin{definition}[\S1.1, Definition 90, Open Disk]\label{90}\lean{}
    We let $\mathbb{D}_R=\{z\in\mathbb{C}:\abs{z} < R\}$.
\end{definition}
%%-/



/-%%
\begin{lemma}[\S1.1, Lemma 91, Closed Disk]\label{91}\lean{}
    We have that $\overline{\mathbb{D}_R}=\{z\in\mathbb{C}:\abs{z}\leq R\}$.
\end{lemma}
%%-/



/-%%
\begin{theorem}[\S1.1, Theorem 133, Borel-Caratheodory I]\label{133}\lean{}
    Let $R,\,M>0$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then for any $0 < r < R$,
    $$\sup_{\abs{z}\leq r}\abs{f(z)}\leq\frac{2Mr}{R-r}.$$
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{}
    Let
    $$f_M(z)=\frac{f(z)/z}{2M-f(z)}.$$
    Note that $2M-f(z)\neq 0$ because $\mathfrak{R}(2M-f(z))=2M-\mathfrak{R}f(z)\geq M>0$. Additionally, since $f(z)$ has a zero at $0$, we know that $f(z)/z$ is analytic on $\abs{z}\leq R$. Likewise, $f_M(z)$ is analytic on $\abs{z}\leq R$.

    Now note that $\abs{f(z)}\leq\abs{2M-f(z)}$ since $\mathfrak{R}f(z)\leq M$. Thus we have that
    $$\abs{f_M(z)}=\frac{\abs{f(z)}/\abs{z}}{\abs{2M-f(z)}}\leq\frac{1}{\abs{z}}.$$
    Now by the maximum modulus principle, we know the maximum of $\abs{f_M}$ must occur on the boundary where $\abs{z}=R$. Thus, $\abs{f_M(z)}\leq 1/R$ for all $\abs{z}\leq R$. So for $\abs{z}=r$ we have
    $$\abs{f_M(z)}=\frac{\abs{f(z)}/r}{\abs{2M-f(z)}}\leq\frac{1}{R}\implies R\,\abs{f(z)}\leq r\,\abs{2M-f(z)}\leq 2Mr+r\,\abs{f(z)}.$$
    Which by algebraic manipulation gives
    $$\abs{f(z)}\leq\frac{2Mr}{R-r}.$$
    Once more, by the maximum modulus principle, we know the maximum of $\abs{f}$ must occur on the boundary where $\abs{z}=r$. Thus, the desired result immediately follows
\end{proof}
%%-/



/-%%
\begin{lemma}[\S1.2, Lemma 177, Derivative Bound]\label{177}\lean{}
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
    Now applying Theorem \ref{133}, and noting that $r'-r\leq\abs{r'e^{it}-z}$, we have that
    $$\abs{\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}}\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
    Substituting this into Equation (\ref{pickupPoint1}) and evaluating the integral completes the proof.
\end{proof}
%%-/



/-%%
\begin{theorem}[\S1.2, Theorem 198, Borel-Caratheodory II]\label{198}\lean{}
    Let $R,\,M>0$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then for any $0 < r < R$,
    $$\abs{f'(z)}\leq\frac{16MR^2}{(R-r)^3}$$
    for all $\abs{z}\leq r$.
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{}
    Using Lemma \ref{177} with $r'=(R+r)/2$, and noting that $r < R$, we have that
    $$\abs{f'(z)}\leq\frac{4M(R+r)^2}{(R-r)^3}\leq\frac{16MR^2}{(R-r)^3}.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[\S1.4, Lemma 238, Logarithm of an Analytic Function]\label{238}\lean{}
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
\begin{definition}[\S2, Definition 240, Set of Zeros]\label{240}\lean{}
    Let $R>0$ and $f:\overline{\mathbb{D}_R}\to\mathbb{C}$. Define the set of zeros $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:\abs{\rho}\leq R,\,f(\rho)=0\}$.
\end{definition}
%%-/



/-%%
\begin{definition}[\S2.1, Definition 250, Zero Order]\label{250}\lean{}
    Let $0 < R<1$ and $f:\mathbb{C}\to\mathbb{C}$ be analtyic on neighborhoods of points in $\overline{\mathbb{D}_1}$. For any zero $\rho\in\mathcal{K}_f(R)$, we define $m_f(\rho)$ as the order of the zero $\rho$ w.r.t $f$.
\end{definition}
%%-/



/-%%
\begin{lemma}[\S2.1, Lemma 256, Zero Factorization]\label{256}\lean{}
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
\begin{definition}[\S2.1, Definition 257, C Function]\label{257}\lean{}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a function $C_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows. This function is constructed by dividing $f(z)$ by a polynomial whose roots are the zeros of $f$ inside $\overline{\mathbb{D}_r}$.
    $$C_f(z)=\begin{cases}
        \displaystyle\frac{f(z)}{\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}\qquad\text{for }z\not\in\mathcal{K}_f(r) \\
        \displaystyle\frac{h_z(z)}{\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}(z-\rho)^{m_f(\rho)}}\qquad\text{for }z\in\mathcal{K}_f(r)
    \end{cases}$$
    where $h_z(z)$ comes from Lemma \ref{256}.
\end{definition}
%%-/



/-%%
\begin{definition}[\S2.1, Definition 275, Blaschke B]\label{275}\lean{}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a function $B_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows.
    $$B_f(z)=C_f(z)\prod_{\rho\in\mathcal{K}_f(r)}\left(R-\frac{z\overline{\rho}}{R}\right)^{m_f(\rho)}$$
\end{definition}
%%-/



/-%%
\begin{lemma}[\S2.2, Lemma 304, Blaschke of Zero]\label{304}\lean{}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. Then
    $$\abs{B_f(0)}=\abs{f(0)}\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Since $f(0)\neq 0$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{275},
    $$\abs{B_f(0)}=\abs{C_f(0)}\prod_{\rho\in\mathcal{K}_f(r)}R^{m_f(\rho)}=\abs{f(0)}\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[\S2.2, Lemma 317, Disk Bound]\label{317}\lean{}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then $\abs{B_f(z)}\leq B$ for $\abs{z}\leq R$ also.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    For $\abs{z}=R$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{275},
    $$\abs{B_f(z)}=\abs{f(z)}\prod_{\rho\in\mathcal{K}_f(r)}\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}^{m_f(\rho)}.$$
    But note that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}=\frac{\abs{R^2-z\overline{\rho}}/R}{\abs{z-\rho}}=\frac{\abs{z}\cdot\abs{\overline{z-\rho}}/R}{\abs{z-\rho}}=1.$$
    So we have that $\abs{B_f(z)}=\abs{f(z)}\leq B$ when $\abs{z}=R$. Now by the maximum modulus principle, we know that the maximum of $\abs{B_f}$ must occur on the boundary where $\abs{z}=R$. Thus $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$.
\end{proof}
%%-/



/-%%
\begin{lemma}[\S2.2, Lemma 320, Jensen Form]\label{320}\lean{}
    Let $B>1$ and $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}\leq B.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Since $f(0)=1$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into definition \ref{275},
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}=\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{r}\right)^{m_f(\rho)}\leq\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}=\abs{B_f(0)}\leq B$$
    whereby Lemma \ref{317} we know that $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$.
\end{proof}
%%-/



/-%%
\begin{lemma}[\S2.2, Lemma 329, Zeros Bound]\label{329}\lean{}
    Let $B>1$ and $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then
    $$\abs{\mathcal{K}_f(r)}\leq\frac{\log B}{\log(R/r)}.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Using Lemma \ref{320} we have that
    $$(R/r)^{\abs{\mathcal{K}_f(r)}}=(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}1}\leq(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}\leq B.$$
    Taking the logarithm of both sides and rearranging gives the desired result.
\end{proof}
%%-/



/-%%
\begin{definition}[\S2.3, Definition 330, Log Function]\label{330}\lean{}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$, define $L_f(z)=J_{B_f}(z)$ where $J$ is from Lemma \ref{238} and $B_f$ is from Definition \ref{275}.
\end{definition}
%%-/



/-%%
\begin{lemma}[\S2.3, Lemma 332, Never Zero]\label{332}\lean{}
    Let $0 < r < R<1$ and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$. Then $B_f(z)\neq 0$ for all $z\in\overline{\mathbb{D}_r}$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Suppose that $z\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{h_z(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}(z-\rho)^{m_f(\rho)}}.$$
    where $h_z(z)\neq 0$ according to Lemma \ref{256}. Thus, substituting this into Definition \ref{275},
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
    Thus, substituting this into Definition \ref{275},
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
\begin{lemma}[\S2.3, Lemma 343, Apply Borel-Caratheodory II]\label{343}\lean{}
    Let $B>1$ and $0 < r' < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for all $\abs{z}\leq R$, then for all $\abs{z}\leq r'$
    $$\abs{L_f'(z)}\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    By Lemma \ref{317} we immediately know that $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$. Now since $L_f=J_{B_f}$ by Definition \ref{330}, by Lemma \ref{238} we know that
    $$L_f(0)=0\qquad\text{and}\qquad \mathfrak{R}L_f(z)=\log\abs{B_f(z)}-\log\abs{B_f(0)}\leq\log\abs{B_f(z)}\leq\log B$$
    for all $\abs{z}\leq r$. So by Theorem \ref{198}, it follows that
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
