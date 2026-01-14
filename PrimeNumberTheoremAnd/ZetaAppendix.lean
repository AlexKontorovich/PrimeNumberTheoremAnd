import Architect
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.ConstantSpeed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.LinearCombination'
import PrimeNumberTheoremAnd.ZetaDefinitions

blueprint_comment /--
\section{Approximating the Riemann zeta function}
-/

blueprint_comment /--
We want a good explicit estimate on
$$\sum_{n\leq a} \frac{1}{n^s} - \int_0^{a} \frac{du}{u^s},$$
for $a$ a half-integer. As it turns out, this is the same problem as that of approximating
$\zeta(s)$ by a sum $\sum_{n\leq a} n^{-s}$. This is one of the two\footnote{The other one is
the approximate functional equation.} main, standard ways of approximating $\zeta(s)$.

The non-explicit version of the result was first proved in
\cite[Lemmas 1 and 2]{zbMATH02601353}. The proof there uses first-order Euler-Maclaurin
combined with a decomposition of $\lfloor x\rfloor - x +1/2$ that turns out to be equivalent
to Poisson summation.
The exposition in \cite[\S 4.7--4.11]{MR882550} uses first-order Euler-Maclaurin and
van de Corput's Process B; the main idea of the latter is Poisson summation.

There are already several explicit versions of the result in the literature.
In \cite{MR1687658}, \cite{MR3105334} and \cite{MR4114203}, what we have is successively
sharper explicit versions of Hardy and Littlewood's original proof.
The proof in \cite[Lemma 2.10]{zbMATH07557592} proceeds simply by a careful estimation of
the terms in high-order Euler-Maclaurin; it does not use Poisson summation. Finally,
\cite{delaReyna} is an explicit version of \cite[\S 4.7--4.11]{MR882550}; it
gives a weaker bound than \cite{MR4114203} or \cite{zbMATH07557592}. The strongest of these
results is \cite{MR4114203}.

We will give another version here, in part because we wish to relax conditions -- we will
work with $\left|\Im s\right| < 2\pi a$ rather than $\left|\Im s\right| \leq a$ -- and in
part to show that one can prove an asymptotically optimal result easily and concisely.
We will use first-order Euler-Maclaurin and Poisson summation. We assume that $a$ is a
half-integer; if one inserts the same assumption into \cite[Lemma 2.10]{zbMATH07557592},
one can improve the result there, yielding an error term closer to the one here.

For additional context, see the Zulip discussion at
\url{https://leanprover.zulipchat.com/\#narrow/channel/423402-PrimeNumberTheorem.2B/
topic/Let.20us.20formalize.20an.20appendix}
-/

namespace ZetaAppendix

open Real Complex MeasureTheory

-- may want to move this to a more globally accessible location

@[blueprint
  "e-def"
  (title := "e")
  (statement := /-- We recall that $e(\alpha) = e^{2\pi i \alpha}$. -/)]
noncomputable def e (α : ℝ) : ℂ := exp (2 * π * I * α)

blueprint_comment /--
\subsection{The decay of a Fourier transform}
Our first objective will be to estimate the Fourier transform of
$t^{-s} \mathbb{1}_{[a,b]}$. In particular, we will show that, if $a$ and $b$ are
half-integers, the Fourier cosine transform has quadratic decay {\em when evaluated at
integers}. In general, for real arguments, the Fourier transform of a discontinuous
function such as $t^{-s} \mathbb{1}_{[a,b]}$ does not have quadratic decay.
-/

@[blueprint
  "lem:aachIBP"
  (title := "Fourier transform of a truncated power law")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.
Let $\nu\in \mathbb{R}\setminus \{0\}$, $b>a>\frac{|\tau|}{2\pi |\nu|}$.
Then
\begin{equation}\label{eq:aachquno}\int_a^b t^{-s} e(\nu t) dt =
 \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b
 + \sigma \int_a^b \frac{t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} e(\varphi_\nu(t)) dt
 + \int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt,
\end{equation}
where $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$.
-/)
  (proof := /--
We write $t^{-s} e(\nu t) = t^{-\sigma} e(\varphi_\nu(t))$ and integrate by parts with
$u = t^{-\sigma}/(2\pi i \varphi_\nu'(t))$, $v = e(\varphi_\nu(t))$.
Here $\varphi_\nu'(t) = \nu - \tau/(2\pi t)\ne 0$ for $t\in [a,b]$ because
$t\geq a > |\tau|/(2\pi |\nu|)$ implies $|\nu|>|\tau|/(2\pi t)$.
Clearly
\[u dv = \frac{ t^{-\sigma}}{2\pi i \varphi_\nu'(t)} \cdot 2\pi i \varphi_\nu'(t)
  e(\varphi_\nu(t)) dt = t^{-\sigma} e(\varphi_\nu(t)) dt,\]
while
\[du = \left(\frac{-\sigma t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)}
  - \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}\right) dt.\]
-/)
  (latexEnv := "lemma")
  (discussion := 546)]
theorem lemma_aachIBP (s : ℂ) (hsigma : 0 ≤ s.re) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
    let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℂ := fun t ↦
      (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
      s.re * ∫ t in Set.Icc a b,
        (t ^ (-s.re - 1) : ℝ) / (2 * π * I * (deriv φ t)) * e (φ t) +
      ∫ t in Set.Icc a b, (t ^ (-s.re) : ℝ) * (deriv (deriv φ) t) /
        (2 * π * I * (deriv φ t) ^ 2) * e (φ t) := by
  sorry

@[blueprint
  "lem:aachra"
  (title := "Total variation of a function with monotone absolute value")
  (statement := /--
Let $g:[a,b]\to \mathbb{R}$ be continuous, with $|g(t)|$ non-increasing. Then
$g$ is monotone, and $\|g\|_{\mathrm{TV}} = |g(a)|-|g(b)|$.
-/)
  (proof := /--
Suppose $g$ changed sign: $g(a')>0>g(b')$ or $g(a') <0 < g(b')$ for some
$a\leq a'< b'\leq b$. By IVT, there would be an $r\in [a',b']$ such that $g(r)=0$.
Since $|g|$ is non-increasing, $g(b')=0$; contradiction. So, $g$ does not change sign:
either $g\leq 0$ or $g\geq 0$.

Thus, there is an $\varepsilon\in \{-1,1\}$ such that $g(t) = \varepsilon |g(t)|$ for all
$t\in [a,b]$. Hence, $g$ is monotone. Then $\|g\|_{\mathrm{TV}} = |g(a)-g(b)|$.
Since $|g(a)|\geq |g(b)|$ and $g(a)$, $g(b)$ are either both non-positive or non-negative,
$|g(a)-g(b)| = |g(a)|-|g(b)|$.
-/)
  (latexEnv := "lemma")
  (discussion := 547)]
theorem lemma_aachra {a b : ℝ} (ha : a < b) (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    BoundedVariationOn g (Set.Icc a b) ∧
    (eVariationOn g (Set.Icc a b)).toReal = |g a| - |g b| := by
  have h_no_sign_change : (∀ t ∈ Set.Icc a b, g t ≥ 0) ∨ (∀ t ∈ Set.Icc a b, g t ≤ 0) := by
    by_contra h_contra
    obtain ⟨a', b', ha', hb', hab', h_sign⟩ :
        ∃ a' b' : ℝ, a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ (g a' > 0 ∧ g b' < 0) ∨
        (∃ a' b' : ℝ, a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ (g a' < 0 ∧ g b' > 0)) := by
      simp only [Set.mem_Icc, and_imp, not_or, not_forall, not_le, exists_and_left] at *
      obtain ⟨⟨x, hx₁, hx₂, hx₃⟩, ⟨y, hy₁, hy₂, hy₃⟩⟩ := h_contra
      cases lt_trichotomy x y with
      | inl hxy => exact ⟨x, y, Or.inr ⟨x, hx₁, y, by grind, by grind, hx₃, hy₃⟩⟩
      | inr h => cases h with
        | inl heq => grind
        | inr hxy => exact ⟨y, x, Or.inl ⟨by grind, hxy, by grind, hy₃, hx₃⟩⟩
    · obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo a' b', g c = 0 := by
        refine intermediate_value_Ioo' (by grind) (hg_cont.mono <| Set.Icc_subset_Icc ha' hab')
          ⟨?_, ?_⟩ <;> linarith [h_sign.1, h_sign.2]
      have := hg_mon ⟨by linarith [hc.1.1], by linarith [hc.1.2]⟩
        ⟨by linarith [hc.1.1], by linarith [hc.1.2]⟩ hc.1.2.le
      aesop
    · obtain ⟨a', b', ha', hb', hab', h₁, h₂⟩ := ‹_›
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo a' b', g c = 0 := by
        apply intermediate_value_Ioo
        · grind
        · exact hg_cont.mono (Set.Icc_subset_Icc ha' hab')
        · constructor <;> grind
      have := hg_mon ⟨by linarith [hc.1.1], by linarith [hc.1.2]⟩
        ⟨by linarith [hc.1.1], by linarith [hc.1.2]⟩ hc.1.2.le
      simp_all
  rcases h_no_sign_change with h | h
  · have h_monotone : AntitoneOn g (Set.Icc a b) := fun x hx y hy hxy => by
      simpa only [abs_of_nonneg (h x hx), abs_of_nonneg (h y hy)] using hg_mon hx hy hxy
    have h_total_variation : eVariationOn g (Set.Icc a b) = ENNReal.ofReal (g a - g b) := by
      refine le_antisymm ?_ ?_
      · refine csSup_le ?_ ?_ <;> norm_num
        · exact ⟨_, ⟨⟨0, ⟨fun _ ↦ a, fun _ _ _ ↦ by grind, fun _ ↦ ⟨by grind, by grind⟩⟩⟩, rfl⟩⟩
        · rintro _ n x hx₁ hx₂ rfl
          calc ∑ i ∈ Finset.range n, edist (g (x (i + 1))) (g (x i))
              ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (g (x i) - g (x (i + 1))) := by
                refine Finset.sum_le_sum (fun i _ ↦ ?_)
                simp only [edist_dist, sub_nonneg, h_monotone (hx₂ i) (hx₂ (i + 1)) (hx₁ (Nat.le_succ _)),
                  ENNReal.ofReal_le_ofReal_iff]
                rw [dist_eq_norm, Real.norm_of_nonpos] <;>
                linarith [h_monotone (hx₂ i) (hx₂ (i + 1)) (hx₁ (Nat.le_succ _))]
            _ ≤ ENNReal.ofReal (g a - g b) := by
                rw [← ENNReal.ofReal_sum_of_nonneg] <;> norm_num
                · apply ENNReal.ofReal_le_ofReal
                  have := Finset.sum_range_sub' (fun i ↦ g (x i)) n
                  norm_num at *
                  linarith [h_monotone ⟨le_refl a, ha.le⟩ (hx₂ 0) (by linarith [hx₂ 0]),
                    h_monotone (hx₂ n) ⟨ha.le, le_refl b⟩ (by linarith [hx₂ n])]
                · exact fun i hi ↦ h_monotone (hx₂ i) (hx₂ (i + 1)) (hx₁ (Nat.le_succ _))
      · refine le_csSup ?_ ?_ <;> norm_num
        refine ⟨1, fun i ↦ if i = 0 then a else b, ?_, ?_⟩ <;> norm_num [Monotone]
        · grind
        · simp only [edist_dist, dist_eq_norm, norm_eq_abs, abs_sub_comm, abs_of_nonneg
            (sub_nonneg.mpr (h_monotone (Set.left_mem_Icc.mpr ha.le) (Set.right_mem_Icc.mpr ha.le) ha.le))]
    rw [h_total_variation, ENNReal.toReal_ofReal]
    · constructor
      · exact ne_of_lt <| lt_of_le_of_lt h_total_variation.le ENNReal.ofReal_lt_top
      · rw [abs_of_nonneg <| h a <| Set.left_mem_Icc.mpr ha.le,
            abs_of_nonneg <| h b <| Set.right_mem_Icc.mpr ha.le]
    · linarith [h_monotone (Set.left_mem_Icc.mpr ha.le) (Set.right_mem_Icc.mpr ha.le) ha.le]
  · have h_monotone : MonotoneOn g (Set.Icc a b) := fun x hx y hy hxy ↦ by have := hg_mon hx hy hxy; grind
    have h_bounded_variation : eVariationOn g (Set.Icc a b) = ENNReal.ofReal (g b - g a) := by
      refine le_antisymm ?_ ?_
      · refine csSup_le ?_ ?_ <;> norm_num
        · exact ⟨_, ⟨⟨0, ⟨fun _ ↦ a, fun _ _ _ ↦ by grind, fun _ ↦ ⟨by grind, by grind⟩⟩⟩, rfl⟩⟩
        · rintro _ n x hx₁ hx₂ rfl
          calc ∑ i ∈ Finset.range n, edist (g (x (i + 1))) (g (x i))
              ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (g (x (i + 1)) - g (x i)) := by
                refine Finset.sum_le_sum (fun i _ ↦ ?_)
                rw [edist_dist, dist_eq_norm, Real.norm_of_nonneg (sub_nonneg.mpr (h_monotone (hx₂ _)
                  (hx₂ _) (hx₁ (Nat.le_succ _))))]
            _ ≤ ENNReal.ofReal (g b - g a) := by
                rw [← ENNReal.ofReal_sum_of_nonneg]
                · rw [Finset.sum_range_sub (fun i ↦ g (x i))]
                  apply ENNReal.ofReal_le_ofReal
                  have hx0_mem : x 0 ∈ Set.Icc a b := ⟨by linarith [hx₂ 0], by linarith [hx₂ 0]⟩
                  have hxn_mem : x n ∈ Set.Icc a b := ⟨by linarith [hx₂ n], by linarith [hx₂ n]⟩
                  linarith [h_monotone ⟨le_refl a, ha.le⟩ hx0_mem (by linarith [hx₂ 0]),
                    h_monotone hxn_mem ⟨ha.le, le_refl b⟩ (by linarith [hx₂ n])]
                · exact fun i hi ↦ sub_nonneg_of_le <| h_monotone (hx₂ _) (hx₂ _) <| hx₁ <| Nat.le_succ _
      · refine le_csSup ?_ ?_ <;> norm_num
        refine ⟨1, fun i ↦ if i = 0 then a else b, ?_, ?_⟩ <;> norm_num [Monotone]
        · grind
        · simp [edist_dist, Real.dist_eq, abs_of_nonneg, h_monotone (show a ∈ Set.Icc a b by
            constructor <;> grind) (show b ∈ Set.Icc a b by constructor <;> grind) ha.le]
    simp_all only [Set.mem_Icc, and_imp]
    constructor
    · rw [BoundedVariationOn]
      exact ne_of_lt (lt_of_le_of_lt h_bounded_variation.le ENNReal.ofReal_lt_top)
    · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (h_monotone ⟨by grind, by grind⟩ ⟨by grind, by grind⟩ ha.le)),
        abs_of_nonpos (h a le_rfl ha.le), abs_of_nonpos (h b ha.le le_rfl)]
      ring

@[blueprint
  "lem:aachmonophase"
  (title := "Non-stationary phase estimate")
  (statement := /--
Let $\varphi:[a,b]\to \mathbb{R}$ be $C^1$ with $\varphi'(t)\ne 0$ for all $t\in [a,b]$.
Let $h:[a,b]\to \mathbb{R}$ be such that $g(t) = h(t)/\varphi'(t)$ is continuous and
$|g(t)|$ is non-increasing. Then
\[\left|\int_a^b h(t) e(\varphi(t)) dt\right|\leq \frac{|g(a)|}{\pi}.\]
-/)
  (proof := /--
Since $\varphi$ is $C^1$, $e(\varphi(t))$ is $C^1$, and
$h(t) e(\varphi(t)) = \frac{h(t)}{2\pi i \varphi'(t)} \frac{d}{dt} e(\varphi(t))$ everywhere.
By Lemma \ref{lem:aachra}, $g$ is of bounded variation. Hence, we can integrate by parts:
\[\int_a^b h(t) e(\varphi(t)) dt =
  \left. \frac{h(t) e(\varphi(t))}{2\pi i \varphi'(t)}\right|_a^b -
  \int_a^b e(\varphi(t))\, d\left(\frac{h(t)}{2\pi i \varphi'(t)}\right).
\]
The first term on the right has absolute value $\leq \frac{|g(a)|+|g(b)|}{2\pi}$.
Again by Lemma \ref{lem:aachra},
\[\left|
\int_a^b e(\varphi(t))\, d\left(\frac{h(t)}{2\pi i \varphi'(t)}\right)
\right|\leq \frac{1}{2\pi} \|g\|_{\mathrm{TV}} = \frac{|g(a)|-|g(b)|}{2\pi}.
\]
We are done by
$\frac{|g(a)|+|g(b)|}{2\pi} + \frac{|g(a)|-|g(b)|}{2\pi} = \frac{|g(a)|}{\pi}$.
-/)
  (latexEnv := "lemma")
  (discussion := 548)]
theorem lemma_aachmonophase {a b : ℝ} (ha : a < b) (φ : ℝ → ℝ)
    (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0)
    (h g : ℝ → ℝ) (hg : ∀ t, g t = h t / deriv φ t)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    ‖∫ t in Set.Icc a b, h t * e (φ t)‖ ≤ |g a| / π := by
  sorry

@[blueprint
  "lem:aachdecre"
  (title := "A decreasing function")
  (statement := /--
Let $\sigma\geq 0$, $\tau\in \mathbb{R}$, $\nu \in \mathbb{R}\setminus \{0\}$.
Let $b>a>\frac{|\tau|}{2\pi |\nu|}$. Then, for any $k\geq 1$,
$f(t) = t^{-\sigma-k} |2\pi \nu-\tau/t|^{-k-1}$ is decreasing on $[a,b]$.
-/)
  (proof := /--
Let $a\leq t\leq b$. Since $\left|\frac{\tau}{t \nu}\right| < 2\pi$, we see that
$2\pi-\frac{\tau}{\nu t} >0$, and so
$|2\pi \nu-\tau/t|^{-k-1} = |\nu|^{-k-1} \left(2\pi - \frac{\tau}{t \nu}\right)^{-k-1}$.
Now we take logarithmic derivatives:
\[t (\log f(t))' = - (\sigma+k) - (k+1) \frac{\tau/t}{2\pi \nu - \tau/t}
= -\sigma - \frac{2\pi k + \frac{\tau}{t \nu}}{2\pi - \frac{\tau}{t \nu}} < -\sigma \leq 0,\]
since, again by $\frac{|\tau|}{t |\nu|} < 2\pi$ and $k\geq 1$, we have
$2\pi k + \frac{\tau}{t \nu}>0$, and, as we said, $2\pi - \frac{\tau}{t \nu}>0$.
-/)
  (latexEnv := "lemma")
  (discussion := 549)]
theorem lemma_aachdecre (σ : ℝ) (hσ : 0 ≤ σ) (τ : ℝ) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |τ| / (2 * π * |ν|)) (hb : b > a) (k : ℕ) (hk : 1 ≤ k) :
    let f : ℝ → ℝ := fun t ↦ t ^ (-σ - k) * |2 * π * ν - τ / t| ^ (-(k : ℝ) - 1)
    AntitoneOn f (Set.Icc a b) := by
  have h_deriv_neg : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t < 0 := by
    intro t ht
    have h_abs : |τ / (t * ν)| < 2 * Real.pi := by
      rw [abs_div, abs_mul]
      rw [div_lt_iff₀] at *
      all_goals cases abs_cases t <;> cases abs_cases ν <;>
        nlinarith [Real.pi_gt_three, ht.1, ht.2, mul_pos Real.pi_pos (abs_pos.mpr hν),
          abs_nonneg τ, mul_div_cancel₀ (|τ|) (by positivity : (2 * Real.pi * |ν|) ≠ 0)]
    have h_deriv_neg :
        deriv (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t =
          -(σ + k) / t - (k + 1) * (τ / t ^ 2) / (2 * Real.pi * ν - τ / t) := by
      have ht_ne : t ≠ 0 := by linarith [ht.1, show 0 < a from lt_of_le_of_lt (by positivity) ha]
      convert HasDerivAt.deriv (HasDerivAt.sub (HasDerivAt.const_mul (-(σ + k : ℝ))
        (Real.hasDerivAt_log (show t ≠ 0 from ht_ne))) (HasDerivAt.const_mul (k + 1 : ℝ)
        (HasDerivAt.log (HasDerivAt.sub (hasDerivAt_const _ _) (HasDerivAt.const_mul τ
        (hasDerivAt_inv (show t ≠ 0 from ht_ne)))) _))) using 1 <;> norm_num
      · congr! 1
      · ring
      · contrapose! h_abs
        field_simp
        rw [abs_div, abs_mul, le_div_iff₀ (mul_pos (abs_pos.mpr
          (by linarith [ht.1, lt_of_le_of_lt (by positivity) ha])) (abs_pos.mpr hν))]
        have ht_ne' : t ≠ 0 := by positivity
        cases abs_cases t <;> cases abs_cases ν <;> cases abs_cases τ <;> push_cast [*] <;>
          nlinarith [inv_mul_cancel_left₀ ht_ne' τ, inv_mul_cancel₀ ht_ne', Real.pi_pos]
    have h_deriv_eq :
        deriv (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t =
          -(σ + k) / t - (k + 1) * (τ / (t * ν)) / (2 * Real.pi - τ / (t * ν)) / t := by
      convert h_deriv_neg using 1; simp only [neg_add_rev, sub_right_inj]; ring_nf; grind
    have h_expr_neg : -(σ + k) - (k + 1) * (τ / (t * ν)) / (2 * Real.pi - τ / (t * ν)) < 0 := by
      rw [sub_div', div_lt_iff₀] <;> nlinarith [abs_lt.mp h_abs, show (k : ℝ) ≥ 1 by norm_cast]
    have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
    rw [h_deriv_eq]
    have h_goal : -(σ + k) / t - (k + 1) * (τ / (t * ν)) / (2 * Real.pi - τ / (t * ν)) / t =
        (-(σ + k) - (k + 1) * (τ / (t * ν)) / (2 * Real.pi - τ / (t * ν))) / t := by ring
    exact h_goal ▸ div_neg_of_neg_of_pos h_expr_neg ht_pos
  have h_decreasing : ∀ t1 t2 : ℝ, a ≤ t1 → t1 < t2 → t2 ≤ b →
      Real.exp ((-(σ + k) * Real.log t1) - (k + 1) * Real.log |2 * Real.pi * ν - τ / t1|) ≥
        Real.exp ((-(σ + k) * Real.log t2) - (k + 1) * Real.log |2 * Real.pi * ν - τ / t2|) := by
    intro t1 t2 ht1 ht2 ht3
    have h_mean_val : ∃ c ∈ Set.Ioo t1 t2,
        deriv (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) c =
          ((fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t2 -
            (fun t ↦ -(σ + k) * Real.log t - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) t1) /
              (t2 - t1) := by
      apply_rules [exists_deriv_eq_slope]
      · exact continuousOn_of_forall_continuousAt fun t ht ↦ DifferentiableAt.continuousAt <|
          differentiableAt_of_deriv_ne_zero <| ne_of_lt <| h_deriv_neg t ⟨by grind, by grind⟩
      · exact fun x hx ↦ DifferentiableAt.differentiableWithinAt (by
          exact differentiableAt_of_deriv_ne_zero (ne_of_lt
            (h_deriv_neg x ⟨by linarith [hx.1], by linarith [hx.2]⟩)))
    obtain ⟨c, ⟨hc1, hc2⟩, hc3⟩ := h_mean_val
    let f := fun t ↦ -(σ + ↑k) * Real.log t - (↑k + 1) * Real.log |2 * π * ν - τ / t|
    have h_diff_neg : f t2 - f t1 < 0 := neg_of_div_neg_left
      (hc3 ▸ h_deriv_neg c ⟨by linarith, by linarith⟩) (le_of_lt <| sub_pos.mpr ht2)
    exact exp_le_exp.mpr (le_of_lt <| sub_neg.mp h_diff_neg)
  have h_f_eq_exp : ∀ t ∈ Set.Icc a b,
      t ^ (-σ - k : ℝ) * |2 * Real.pi * ν - τ / t| ^ (-(k : ℝ) - 1) =
        Real.exp ((-(σ + k) * Real.log t) - (k + 1) * Real.log |2 * Real.pi * ν - τ / t|) := by
    intro t ht
    have h_pos : 0 < t ∧ 0 < |2 * Real.pi * ν - τ / t| := by
      have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
      constructor
      · exact ht_pos
      · rw [abs_pos, sub_ne_zero, ne_eq, eq_div_iff (ne_of_gt ht_pos)]
        intro h_eq
        have : |τ| / (2 * π * |ν|) ≥ a := by
          rw [ge_iff_le, le_div_iff₀ (by positivity)]
          calc a * (2 * π * |ν|) = 2 * π * |ν| * a := by ring
            _ ≤ 2 * π * |ν| * t := mul_le_mul_of_nonneg_left ht.1 (by positivity)
            _ = |2 * π * ν * t| := by
              rw [abs_mul, abs_mul, abs_of_pos Real.two_pi_pos, abs_of_pos ht_pos]
            _ = |τ| := by rw [h_eq]
        linarith
    rw [rpow_def_of_pos h_pos.1, rpow_def_of_pos h_pos.2, ← Real.exp_add]; ring_nf
  refine fun x hx y hy hxy ↦ by cases eq_or_lt_of_le hxy <;> simp_all only [Set.mem_Icc, and_imp, le_refl]


@[blueprint
  "lem:aachfour"
  (title := "Estimating an integral")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.
Let $\nu \in \mathbb{R}\setminus \{0\}$, $b>a>\frac{|\tau|}{2\pi |\nu|}$.
Then
\[\int_a^b t^{-s} e(\nu t) dt =
 \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b +
\frac{a^{-\sigma-1}}{2\pi^2} O^*\left(\frac{\sigma}{(\nu-\vartheta)^2} +
\frac{|\vartheta|}{|\nu-\vartheta|^3}\right),
\]
where $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$ and
$\vartheta = \frac{\tau}{2\pi a}$.
-/)
  (proof := /--
Apply Lemma~\ref{lem:aachIBP}. Since $\varphi_\nu'(t) = \nu - \tau/(2\pi t)$, we know by
Lemma \ref{lem:aachdecre} (with $k=1$) that
$g_1(t) = \frac{t^{-\sigma-1}}{(\varphi_\nu'(t))^2}$ is decreasing on $[a,b]$.
We know that $\varphi_\nu'(t)\ne 0$ for $t\geq a$ by $a>\frac{|\tau|}{2\pi |\nu|}$, and so
we also know that $g_1(t)$ is continuous for $t\geq a$.
Hence, by Lemma \ref{lem:aachmonophase},
\[\left|\int_a^b \frac{t^{-\sigma-1}}{2\pi i \varphi_\nu'(t)} e(\varphi_\nu(t)) dt \right|
  \leq \frac{1}{2\pi} \cdot \frac{|g_1(a)|}{\pi}
  = \frac{1}{2\pi^2} \frac{a^{-\sigma-1}}{\left|\nu - \vartheta\right|^2},\]
since $\varphi_\nu'(a) = \nu - \vartheta$. We remember to include the factor of $\sigma$
in front of an integral in \eqref{eq:aachquno}.

Since $\varphi_\nu'(t)$ is as above and $\varphi_\nu''(t) = \tau/(2\pi t^2)$, we know
by Lemma \ref{lem:aachdecre} (with $k=2$) that
$g_2(t) = \frac{t^{-\sigma} |\varphi_\nu''(t)|}{|\varphi_\nu'(t)|^3} =
\frac{|\tau|}{2\pi} \frac{t^{-\sigma-2}}{|\varphi_\nu'(t)|^3}$ is decreasing on $[a,b]$;
we also know, as before, that $g_2(t)$ is continuous.
Hence, again by Lemma \ref{lem:aachmonophase},
\[\left|\int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt\right|\leq \frac{1}{2\pi} \frac{|g_2(a)|}{\pi} = \frac{1}{2\pi^2}
 \frac{a^{-\sigma-1} |\vartheta|}{\left|\nu - \vartheta\right|^3}.
\]
-/)
  (latexEnv := "lemma")
  (discussion := 550)]
theorem lemma_aachfour (s : ℂ) (hsigma : 0 ≤ s.re) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
    let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℂ := fun t ↦ (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    let ϑ : ℝ := s.im / (2 * π * a)
    ∃ E, ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
      ((a ^ (-s.re - 1) : ℝ) / (2 * π ^ 2)) * E ∧
      ‖E‖ ≤ s.re / (|ν - ϑ| ^ 2) + |ϑ| / (|ν - ϑ| ^ 3) := by
  sorry

def _root_.Real.IsHalfInteger (x : ℝ) : Prop := ∃ k : ℤ, x = k + 1 / 2

/-- At half-integers, `(Φ n t + Φ (-n) t) / 2 = Ψ t` where `Φ` and `Ψ` are as in `lemma_aachcanc`. -/
lemma lemma_aachcanc_pointwise (s : ℂ) {n : ℤ} (hn : n ≠ 0)
    (t : ℝ) (ht : t.IsHalfInteger) (ht_pos : t > 0)
    (h_deriv_n : deriv (fun x ↦ (n : ℝ) * x - (s.im / (2 * π)) * Real.log x) t ≠ 0)
    (h_deriv_neg_n : deriv (fun x ↦ -(n : ℝ) * x - (s.im / (2 * π)) * Real.log x) t ≠ 0)
    (h_denom : (n : ℂ) ^ 2 - (s.im / (2 * π * t)) ^ 2 ≠ 0) :
    let ϕ : ℝ → ℝ → ℝ := fun ν t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℝ → ℂ := fun ν t ↦ (t ^ (-s.re) : ℝ) * e (ϕ ν t) / (2 * π * I * (deriv (ϕ ν) t))
    let Ψ : ℝ → ℂ := fun t ↦ (-1) ^ n * (t ^ (-s) : ℂ) * (s.im / (2 * π * t)) /
      (2 * π * I * (n ^ 2 - (s.im / (2 * π * t)) ^ 2))
    (1 / 2) * (Φ n t + Φ (-n) t) = Ψ t := by
  have h_exp : e (n * t - s.im / (2 * Real.pi) * Real.log t) = (-1 : ℝ) ^ n * t ^ (-s.im * I) ∧
      e (-n * t - s.im / (2 * Real.pi) * Real.log t) = (-1 : ℝ) ^ n * t ^ (-s.im * I) := by
    unfold e
    norm_num [exp_re, exp_im, log_re, log_im, cpow_def]
    ring_nf
    have h_inner : exp (Real.pi * I * n * t * 2) = (-1 : ℂ) ^ n ∧ exp (-Real.pi * I * n * t * 2) = (-1 : ℂ) ^ n := by
      obtain ⟨k, rfl⟩ := ht
      norm_num [Complex.ext_iff, exp_re, exp_im, mul_assoc, mul_comm Real.pi]
      rcases Int.even_or_odd' n with ⟨c, rfl | rfl⟩ <;>
      · norm_num [zpow_add₀, zpow_mul]
        ring_nf
        norm_num [mul_assoc, mul_comm Real.pi _, mul_div]
        constructor
        · rw [Real.cos_eq_one_iff]; use c * k * 2; push_cast; ring
        · rw [Real.sin_eq_zero_iff]; use c * k * 4; push_cast; ring
    simp_all [Complex.exp_sub]
    norm_num [ofReal_log ht_pos.le, mul_assoc, mul_comm, mul_left_comm, pi_ne_zero]
    norm_num [Complex.exp_neg, Complex.exp_log, ht_pos.ne', mul_assoc, mul_left_comm, pi_ne_zero]
    ring_nf
    field_simp
  simp_all only [ne_eq, gt_iff_lt, neg_mul, ofReal_neg, ofReal_one, one_div, ofReal_cpow ht_pos.le]
  norm_num [mul_comm, pi_ne_zero, ht_pos.ne', h_deriv_n, h_deriv_neg_n]
  rw [div_add_div, mul_div, div_eq_div_iff]
  · rw [show (-s : ℂ) = -(s.re : ℂ) - I * (s.im : ℂ) by simp [Complex.ext_iff]]
    rw [cpow_def_of_ne_zero (by norm_cast; positivity)]
    ring_nf
    rw [cpow_def_of_ne_zero (by norm_cast; positivity), cpow_def_of_ne_zero (by norm_cast; positivity)]
    ring_nf
    rw [sub_eq_add_neg, Complex.exp_add]
    ring_nf
  · simp_all only [sub_eq_iff_eq_add, zero_add, ne_eq, mul_eq_zero, I_ne_zero, ofReal_eq_zero,
      pi_ne_zero, OfNat.ofNat_ne_zero, false_or, not_or]
    constructor <;> exact fun h ↦ h_denom <| by linear_combination' h * h
  · simp_all [mul_assoc, mul_comm]
  · contrapose! h_deriv_n
    simp_all [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, sub_eq_iff_eq_add]
  · norm_num [Complex.ext_iff, pi_ne_zero, ht_pos.ne'] at *
    norm_cast at *
    simp_all [mul_comm, div_eq_mul_inv]
    grind

@[blueprint
  "lem:aachcanc"
  (title := "Estimating an sum")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma,\tau \in \mathbb{R}$.
Let $n\in \mathbb{Z}_{>0}$. Let $a,b\in \mathbb{Z} + \frac{1}{2}$,
$b>a>\frac{|\tau|}{2\pi n}$.
Write $\varphi_\nu(t) = \nu t - \frac{\tau}{2\pi} \log t$.
Then
\[\frac{1}{2} \sum_{\nu = \pm n}
  \left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b =
  \left. \frac{(-1)^n t^{-s} \cdot \frac{\tau}{2\pi t}}
  {2\pi i \left(n^2 - \left(\frac{\tau}{2\pi t}\right)^2\right)}\right|_a^b.
\]
-/)
  (proof := /--
Since $e(\varphi_\nu(t)) = e(\nu t) t^{-i \tau} = (-1)^{\nu} t^{-i \tau}$ for any
half-integer $t$ and any integer $\nu$,
\[\left. \frac{t^{-\sigma} e(\varphi_\nu(t))}{2\pi i \varphi_\nu'(t)}\right|_a^b =
\left. \frac{(-1)^{\nu} t^{-s}}{2\pi i \varphi_\nu'(t)}\right|_a^b
\]
for $\nu = \pm n$. Clearly $(-1)^{\nu} = (-1)^n$.
Since $\varphi_\nu'(t) = \nu - \alpha$ for $\alpha = \frac{\tau}{2\pi t}$,
\[\frac{1}{2} \sum_{\nu = \pm n} \frac{1}{\varphi_\nu'(t)} = \frac{1/2}{n - \alpha} +
\frac{1/2}{- n - \alpha} = \frac{-\alpha}{\alpha^2-n^2} = \frac{\alpha}{n^2-\alpha^2}.
\]
-/)
  (latexEnv := "lemma")
  (discussion := 551)]
theorem lemma_aachcanc (s : ℂ) {n : ℤ} (hn : 0 < n) {a b : ℝ}
    (ha : a > |s.im| / (2 * π * n)) (hb : b > a)
    (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) :
    let ϕ : ℝ → ℝ → ℝ := fun ν t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℝ → ℂ := fun ν t ↦
      (t ^ (-s.re) : ℝ) * e (ϕ ν t) / (2 * π * I * (deriv (ϕ ν) t))
    let Ψ : ℝ → ℂ := fun t ↦ (-1) ^ n * (t ^ (-s) : ℂ) * (s.im / (2 * π * t)) /
      (2 * π * I * (n ^ 2 - (s.im / (2 * π * t)) ^ 2))
    (1 / 2) * (Φ n b - Φ n a + Φ (-n) b - Φ (-n) a) = Ψ b - Ψ a := by
  intro phi Φ Ψ
  have h_apply : ∀ t : ℝ, t > |s.im| / (2 * .pi * n) → t.IsHalfInteger → t > 0 →
      (1 / 2) * (Φ n t + Φ (-n) t) = Ψ t := by
    intro t ht ht' ht''
    have h_bound : |s.im| < t * (2 * .pi * n) := by
      rw [gt_iff_lt] at ht; exact (div_lt_iff₀ (by positivity)).mp ht
    convert lemma_aachcanc_pointwise s (show n ≠ 0 by linarith) t ht' ht'' ?_ ?_ ?_ using 1
    all_goals norm_num [mul_comm]
    · norm_num [ht''.ne', pi_ne_zero, mul_comm]
      field_simp
      cases abs_cases s.im <;> nlinarith [pi_pos, h_bound]
    · norm_num [ht''.ne', Real.differentiableAt_log]
      field_simp
      cases abs_cases s.im <;> nlinarith [pi_pos, h_bound]
    · rw [sub_eq_zero, eq_comm]
      norm_num [div_pow, ← mul_assoc, Complex.ext_iff]
      norm_cast
      norm_num
      rw [div_eq_iff (by positivity)]
      rw [abs_lt] at h_bound
      nlinarith [pi_pos]
  have hb_pos : b > 0 := lt_trans (lt_of_le_of_lt (by positivity) ha) hb
  trans (1 / 2) * (Φ n b + Φ (-n) b) - (1 / 2) * (Φ n a + Φ (-n) a)
  · ring
  rw [h_apply b (lt_trans ha hb) hb' hb_pos, h_apply a ha ha' (lt_of_le_of_lt (by positivity) ha)]

blueprint_comment /--
It is this easy step that gives us quadratic decay on $n$. It is just as
in the proof of van der Corput's Process B in, say, \cite[I.6.3, Thm.~4]{zbMATH06471876}.
-/

@[blueprint
  "prop:applem"
  (title := "Estimating a Fourier cosine integral")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$.
Let $a,b\in \mathbb{Z} + \frac{1}{2}$, $b>a>\frac{|\tau|}{2\pi}$.
Write $\vartheta = \frac{\tau}{2\pi a}$. Then, for any integer $n\geq 1$,
$$\begin{aligned}\int_a^b t^{-s} \cos 2\pi n t\, dt &=
\left. \left(\frac{(-1)^n t^{-s}}{2\pi i} \cdot
  \frac{\frac{\tau}{2\pi t}}{n^2 - \left(\frac{\tau}{2\pi t}\right)^2}\right)\right|_a^b \\
&\quad+ \frac{a^{-\sigma-1}}{4\pi^2}\, O^*\left(\frac{\sigma}{(n-\vartheta)^2}
  + \frac{\sigma}{(n+\vartheta)^2}
  + \frac{|\vartheta|}{|n-\vartheta|^3}
  + \frac{|\vartheta|}{|n+\vartheta|^3}\right).\end{aligned}$$
-/)
  (proof := /--
Write $\cos 2\pi n t = \frac{1}{2} (e(n t) + e(-n t))$. Since $n\geq 1$ and
$a>\frac{|\tau|}{2\pi}$, we know that $a>\frac{|\tau|}{2 \pi n}$, and so we can apply
Lemma \ref{lem:aachfour} with $\nu = \pm n$.
We then apply Lemma~\ref{lem:aachcanc} to combine the boundary contributions
$\left. \right|_a^b$ for $\nu=\pm n$.
-/)
  (latexEnv := "proposition")
  (discussion := 552)]
theorem proposition_applem (s : ℂ) (hsigma : 0 ≤ s.re) {a b : ℝ} (ha : a > |s.im| / (2 * π))
    (hb : b > a) (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) {n : ℕ} (hn : 1 ≤ n) :
    let ϑ : ℝ := s.im / (2 * π * a)
    ∃ E, ∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * Real.cos (2 * π * (n : ℝ) * t) =
      ((-1) ^ n * (b ^ (-s) : ℂ) * (s.im / (2 * π * b)) /
        (2 * π * I * ((n : ℝ) ^ 2 - (s.im / (2 * π * b)) ^ 2)) -
       (-1) ^ n * (a ^ (-s) : ℂ) * (s.im / (2 * π * a)) /
        (2 * π * I * ((n : ℝ) ^ 2 - (s.im / (2 * π * a)) ^ 2))) +
      ((a ^ (-s.re - 1) : ℝ) / (4 * π ^ 2)) * E ∧
      ‖E‖ ≤ s.re / ((n - ϑ) ^ 2) + s.re / ((n + ϑ) ^ 2) +
        |ϑ| / (|n - ϑ| ^ 3) + |ϑ| / (|n + ϑ| ^ 3) := by
  have h_pos_a : 0 < a := lt_of_le_of_lt (by positivity) ha
  have h_bound_aux : |s.im| / (2 * π * n) < a := by
    refine ha.trans_le' <| div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    nlinarith [pi_gt_three, show (n : ℝ) ≥ 1 by norm_cast]
  have h_neg := lemma_aachfour s hsigma (-n : ℝ) (by norm_num; linarith) a b (by
    simp only [abs_neg, abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
    exact h_bound_aux) hb
  have h_pos := lemma_aachfour s hsigma (n : ℝ) (by norm_num; linarith) a b (by
    simp only [abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
    exact h_bound_aux) hb
  obtain ⟨E1, hE1_eq, hE1_bound⟩ := h_pos
  obtain ⟨E2, hE2_eq, hE2_bound⟩ := h_neg
  use E1 + E2
  have h_cont_pow : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (-s)) (Set.Icc a b) :=
    ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const
      fun x hx ↦ Or.inl (by norm_cast; linarith [hx.1, h_pos_a])
  have h_integral : ∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * (Real.cos (2 * Real.pi * n * t)) =
      (1 / 2) * (∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * ZetaAppendix.e (n * t)) +
        (1 / 2) * (∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * ZetaAppendix.e (-n * t)) := by
    rw [← mul_add, ← integral_add]
    · rw [← integral_const_mul]
      congr with t
      norm_num [ZetaAppendix.e, Complex.cos]
      ring_nf
    · exact (h_cont_pow.mul (Complex.continuous_exp.comp (by continuity)).continuousOn).integrableOn_Icc
    · exact (h_cont_pow.mul (Complex.continuous_exp.comp (by continuity)).continuousOn).integrableOn_Icc
  constructor
  · have h_lem := lemma_aachcanc s (by grind) h_bound_aux hb ha' hb'
    simp only [zpow_natCast, Int.cast_natCast, one_div, neg_mul] at h_lem
    simp only [h_integral, hE1_eq, hE2_eq]
    convert congrArg (· + (↑(a ^ (-s.re - 1)) / (4 * ↑π ^ 2)) * (E1 + E2)) h_lem using 1; ring_nf
  · have : |-(n : ℝ) - s.im / (2 * π * a)| = |(n : ℝ) + s.im / (2 * π * a)| := by
      rw [show -(n : ℝ) - s.im / (2 * π * a) = -((n : ℝ) + s.im / (2 * π * a)) by ring, abs_neg]
    calc ‖E1 + E2‖ ≤ ‖E1‖ + ‖E2‖ := norm_add_le E1 E2
      _ ≤ _ := add_le_add hE1_bound hE2_bound
      _ = _ := by simp only [sq_abs, this]; ring


blueprint_comment /--
\subsection{Approximating zeta(s)}
We start with an application of Euler-Maclaurin.
-/

@[blueprint
  "lem:abadeulmac"
  (title := "Identity for a partial sum of zeta(s)")
  (statement := /--
Let $b>0$, $b\in \mathbb{Z} + \frac{1}{2}$.
Then, for all $s\in \mathbb{C}\setminus \{1\}$ with $\Re s > 0$,
\begin{equation}\label{eq:abak1}
  \sum_{n\leq b} \frac{1}{n^s} = \zeta(s) + \frac{b^{1-s}}{1-s}
  + s \int_b^\infty \left(\{y\}-\frac{1}{2}\right) \frac{dy}{y^{s+1}}.
\end{equation}
-/)
  (proof := /--
Assume first that $\Re s > 1$. By first-order Euler-Maclaurin and
$b\in \mathbb{Z}+\frac{1}{2}$,
\[\sum_{n>b}\frac{1}{n^s} = \int_b^\infty \frac{dy}{y^s} + \int_b^\infty
 \left(\{y\}-\frac{1}{2}\right) d\left(\frac{1}{y^s}\right).
\]
Here $\int_b^\infty \frac{dy}{y^s} = -\frac{b^{1-s}}{1-s}$ and
$d\left(\frac{1}{y^s}\right) = - \frac{s}{y^{s+1}} dy$.
Hence, by $\sum_{n\leq b} \frac{1}{n^s} = \zeta(s) - \sum_{n>b} \frac{1}{n^s}$
for $\Re s > 1$,
$$\sum_{n\leq b} \frac{1}{n^s} = \zeta(s) + \frac{b^{1-s}}{1-s} +
\int_b^\infty \left(\{y\}-\frac{1}{2}\right) \frac{s}{y^{s+1}} dy.$$
Since the integral converges absolutely for $\Re s > 0$, both sides extend holomorphically
to $\{s\in \mathbb{C}: \Re s>0, s\ne 1\}$; thus, the equation holds throughout that region.
-/)
  (latexEnv := "lemma")
  (discussion := 566)]
theorem lemma_abadeulmac {b : ℝ} (hb : 0 < b) (hb' : b.IsHalfInteger) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, (n : ℂ) ^ (-s) =
      riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) +
      s * ∫ y in Set.Ioi b, (Int.fract y - 1 / 2) * (y ^ (-(s.re + 1)) : ℝ) := by
  sorry

@[blueprint
  "lem:abadtoabsum"
  (title := "Estimate for a partial sum of $\\zeta(s)$")
  (statement := /--
Let $b>a>0$, $b\in \mathbb{Z} + \frac{1}{2}$.
Then, for all $s\in \mathbb{C}\setminus \{1\}$ with $\sigma = \Re s > 0$,
$$\sum_{n\leq a} \frac{1}{n^s} = -\sum_{a < n\leq b} \frac{1}{n^s} + \zeta(s)
  + \frac{b^{1-s}}{1-s} + O^*\left(\frac{|s|}{2 \sigma b^\sigma}\right).$$
-/)
  (proof := /--
By Lemma \ref{lem:abadeulmac}, $\sum_{n\leq a} = \sum_{n\leq b} - \sum_{a < n\leq b}$,
$\left|\{y\}-\frac{1}{2}\right| \leq \frac{1}{2}$ and
$\int_b^\infty \frac{dy}{|y^{s+1}|} = \frac{1}{\sigma b^\sigma}$.
-/)
  (latexEnv := "lemma")
  (discussion := 567)]
theorem lemma_abadtoabsum {a b : ℝ} (hb : 0 < a) (hb' : b.IsHalfInteger) (hab : b > a) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∃ E, ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
      -∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) +
      riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) + E ∧
      ‖E‖ ≤ ‖s‖ / (2 * s.re * (b ^ s.re : ℝ)) := by
  sorry

@[blueprint
  "lem:abadusepoisson"
  (title := "Poisson summation for a partial sum of $\\zeta(s)$")
  (statement := /--
Let $a,b\in \mathbb{R}\setminus \mathbb{Z}$, $b>a>0$. Let $s\in \mathbb{C}\setminus \{1\}$.
Define $f:\mathbb{R}\to\mathbb{C}$ by $f(y) = 1_{[a,b]}(y)/y^s$. Then
$$\sum_{a < n\leq b} \frac{1}{n^s} = \frac{b^{1-s} - a^{1-s}}{1-s}
  + \lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n)).$$
-/)
  (proof := /--
Since $a\notin \mathbb{Z}$, $\sum_{a < n\leq b} \frac{1}{n^s} = \sum_{n\in \mathbb{Z}} f(n)$.
By Poisson summation (as in \cite[Thm.~D.3]{MR2378655})
$$\sum_{n\in \mathbb{Z}} f(n) = \lim_{N\to \infty} \sum_{n=-N}^N \widehat{f}(n) =
\widehat{f}(0) + \lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n)),$$
where we use the facts that $f$ is in $L^1$, of bounded variation, and
(by $a,b\not\in \mathbb{Z}$) continuous at every integer. Now
$$\widehat{f}(0) = \int_{\mathbb{R}} f(y) dy
  = \int_a^b \frac{dy}{y^s} = \frac{b^{1-s}-a^{1-s}}{1-s}.$$
-/)
  (latexEnv := "lemma")
  (discussion := 568)]
theorem lemma_abadusepoisson {a b : ℝ} (ha : ¬∃ n : ℤ, a = n) (hb : ¬∃ n : ℤ, b = n)
    (hab : b > a) (ha' : 0 < a) {s : ℂ} (hs1 : s ≠ 1) :
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    ∃ L : ℂ, Filter.atTop.Tendsto
      (fun (N : ℕ) ↦ ∑ n ∈ Finset.Ioc 1 N,
        (FourierTransform.fourier f n + FourierTransform.fourier f (-n))) (nhds L) ∧
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) =
        ((b ^ (1 - s) : ℂ) - (a ^ (1 - s) : ℂ)) / (1 - s) + L := by
  sorry

blueprint_comment /--
We could prove these equations starting from Euler's product for $\sin \pi z$.
-/

@[blueprint
  "lem:abadeuleulmit1"
  (title := "Euler/Mittag-Leffler expansion for cosec")
  (statement := /--
Let $z\in \mathbb{C}$, $z\notin \mathbb{Z}$. Then
\[ \frac{\pi}{\sin \pi z} = \frac{1}{z} +
 \sum_n (-1)^n\left(\frac{1}{z - n} + \frac{1}{z + n}\right).
\]
-/)
  (proof := /--
Let us start from the Mittag-Leffler expansion
$\pi \cot \pi s = \frac{1}{s} + \sum_n \left(\frac{1}{s-n} + \frac{1}{s+n}\right)$.

Applying the trigonometric identity
$\cot u - \cot \left(u + \frac{\pi}{2}\right) = \cot u + \tan u = \frac{2}{\sin 2 u}$
with $u=\pi z/2$, and letting $s = z/2$, $s = (z+1)/2$, we see that
\[\begin{aligned}\frac{\pi}{\sin \pi z}
  &= \frac{\pi}{2} \cot \frac{\pi z}{2} - \frac{\pi}{2} \cot \frac{\pi (z+1)}{2} \\
  &= \frac{1/2}{z/2} +
    \sum_n \left(\frac{1/2}{\frac{z}{2} -n} + \frac{1/2}{\frac{z}{2} +n}\right)
    -\frac{1/2}{(z+1)/2}
    - \sum_n \left(\frac{1/2}{\frac{z+1}{2} -n} + \frac{1/2}{\frac{z+1}{2} +n}\right)\\
  &= \frac{1}{z} + \sum_n \left(\frac{1}{z - 2 n} + \frac{1}{z + 2 n}\right) -
    \sum_n \left(\frac{1}{z - (2 n - 1)} + \frac{1}{z + (2 n - 1)}\right)
\end{aligned}\]
after reindexing the second sum. Regrouping terms again, we obtain our equation.
-/)
  (latexEnv := "lemma")
  (discussion := 569)]
theorem lemma_abadeuleulmit1 {z : ℂ} (hz : z ∈ integerComplement) :
    (π / Complex.sin (π * z) : ℂ) =
      (1 / z : ℂ) + ∑' n : ℤ, (-1) ^ n * ((1 / (z - n) : ℂ) + (1 / (z + n) : ℂ)) := by
  sorry

@[blueprint
  "lem:abadeulmit2"
  (title := "Euler/Mittag-Leffler expansion for cosec squared")
  (statement := /--
Let $z\in \mathbb{C}$, $z\notin \mathbb{Z}$. Then
\[\frac{\pi^2}{\sin^2 \pi z} = \sum_{n=-\infty}^\infty \frac{1}{(z-n)^2}.\]
-/)
  (proof := /--
Differentiate the expansion of $\pi \cot \pi z$ term-by-term because it converges
uniformly on compact subsets of $\mathbb{C}\setminus \mathbb{Z}$.
By $\left(\pi \cot \pi z\right)' = - \frac{\pi^2}{\sin^2 \pi z}$ and
$\left(\frac{1}{z\pm n}\right)' = -\frac{1}{(z\pm n)^2}$, we are done.
-/)
  (latexEnv := "lemma")
  (discussion := 570)]
theorem lemma_abadeulmit2 {z : ℂ} (hz : ¬∃ n : ℤ, z = n) :
    (π ^ 2 / (Complex.sin (π * z) ^ 2 : ℂ)) = ∑' n : ℤ, (1 / ((z - n) ^ 2 : ℂ)) := by
  sorry

@[blueprint
  "lem:abadimpseri"
  (title := "Estimate for an inverse cubic series")
  (statement := /--
For $\vartheta\in \mathbb{R}$ with $0\leq |\vartheta|< 1$,
\[\sum_n\left(\frac{1}{(n-\vartheta)^3} + \frac{1}{(n+\vartheta)^3}\right)
\leq \frac{1}{(1-|\vartheta|)^3} + 2\zeta(3)-1.\]
-/)
  (proof := /--
Since $\frac{1}{(n-\vartheta)^3} + \frac{1}{(n+\vartheta)^3}$ is even,
we may replace $\vartheta$ by $|\vartheta|$. Then we rearrange the sum:
\[\sum_{n=1}^\infty \left(\frac{1}{(n-|\vartheta|)^3} + \frac{1}{(n+|\vartheta|)^3}\right)
  = \frac{1}{(1-|\vartheta|)^3}
  + \sum_{n=1}^\infty \left(\frac{1}{\left(n+1-|\vartheta|\right)^3}
  + \frac{1}{\left(n+|\vartheta|\right)^3}\right).\]
We may write $(n+1-|\vartheta|)^3$, $(n+|\vartheta|)^3$
as $(n+\frac{1}{2}-t)^3$, $(n+\frac{1}{2} + t)^3$ for $t = |\vartheta|-1/2$.
Since $1/u^3$ is convex, $\frac{1}{(n+1/2-t)^3} + \frac{1}{(n+1/2+t)^3}$ reaches its
maximum on $[-1/2,1/2]$ at the endpoints. Hence
\[\sum_{n=1}^\infty \left(\frac{1}{\left(n+1-|\vartheta|\right)^3}
  + \frac{1}{\left(n+|\vartheta|\right)^3}\right)
  \leq \sum_{n=1}^\infty \left(\frac{1}{n^3} + \frac{1}{(n+1)^3}\right) = 2 \zeta(3)-1.
\]
-/)
  (latexEnv := "lemma")
  (discussion := 571)]
theorem lemma_abadimpseri {ϑ : ℝ} (hϑ : 0 ≤ |ϑ| ∧ |ϑ| < 1) :
    ∑' n : ℤ, (1 / ((n - ϑ) ^ 3 : ℝ) + 1 / ((n + ϑ) ^ 3 : ℝ)) ≤
      (1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1 := by
  sorry

@[blueprint
  "lem:abadsumas"
  (title := "Estimate for a Fourier sum")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau \in \mathbb{R}$, with $s\ne 1$.
Let $b>a>0$, $a, b\in \mathbb{Z} + \frac{1}{2}$, with $a>\frac{|\tau|}{2\pi}$.
Define $f:\mathbb{R}\to\mathbb{C}$ by $f(y) = 1_{[a,b]}(y)/y^s$.
Write $\vartheta = \frac{\tau}{2\pi a}$, $\vartheta_- = \frac{\tau}{2\pi b}$. Then
$$\begin{aligned} \sum_n (\widehat{f}(n) + \widehat{f}(-n))
  &= \frac{a^{-s} g(\vartheta)}{2 i} - \frac{b^{-s} g(\vartheta_-)}{2 i}
  + O^*\left(\frac{C_{\sigma,\vartheta}}{a^{\sigma+1}}\right)\end{aligned}$$
with absolute convergence,
where $g(t) = \frac{1}{\sin \pi t} - \frac{1}{\pi t}$ for $t\ne 0$, $g(0)=0$, and
\begin{equation}\label{eq:defcsigth}C_{\sigma,\vartheta}= \begin{cases}
  \frac{\sigma}{2} \left(\frac{1}{\sin^2\pi \vartheta} - \frac{1}{(\pi \vartheta)^2}\right)
  + \frac{|\vartheta|}{2\pi^2} \left(\frac{1}{(1-|\vartheta|)^3} + 2\zeta(3)-1\right)
  & \text{for $\vartheta\ne 0$,}\\
  \sigma/6 & \text{for $\vartheta = 0$.}\end{cases}\end{equation}
-/)
  (proof := /--
By Proposition~\ref{prop:applem}, multiplying by $2$
(since $e(-n t)+e(n t) = 2 \cos 2\pi n t$),
\begin{align}\widehat{f}(n) + \widehat{f}(-n) &= \notag
  \frac{a^{-s}}{2\pi i} \frac{(-1)^{n+1} 2\vartheta}{n^2 - \vartheta^2} -
  \frac{b^{-s}}{2\pi i} \frac{(-1)^{n+1} 2\vartheta_-}{n^2 - \vartheta_-^2}
  \\
  &+ \frac{a^{-\sigma-1}}{2\pi^2} O^*\left(\frac{\sigma}{(n-\vartheta)^2}
    + \frac{\sigma}{(n+\vartheta)^2} + \frac{|\vartheta|}{(n-\vartheta)^3}
    + \frac{|\vartheta|}{(n+\vartheta)^3}\right),\label{eq:abaderrcontrib}\end{align}
where $\vartheta_- = \tau/(2\pi b)$. Note $|\vartheta_-|\leq |\vartheta|<1$.
By the Lemma \ref{lem:abadeulmit1},
\[\sum_n \frac{(-1)^{n+1} 2 z}{n^2 - z^2} = \frac{\pi}{\sin \pi z} - \frac{1}{z}
\] for $z\ne 0$, while $\sum_n \frac{(-1)^{n+1} 2 z}{n^2 - z^2} = \sum_n 0 = 0$ for $z=0$.
Moreover, by Lemmas \ref{lem:abadeulmit2} and \ref{lem:abadimpseri}, for $\vartheta\ne 0$,
\[\sum_n \left(\frac{\sigma}{(n-\vartheta)^2} + \frac{\sigma}{(n+\vartheta)^2}\right)\leq
\sigma\cdot \left(\frac{\pi^2}{\sin^2 \pi \vartheta} - \frac{1}{\vartheta^2}\right),\]
\[\sum_n \left(\frac{|\vartheta|}{(n-\vartheta)^3} + \frac{|\vartheta|}{(n+\vartheta)^3}\right)
\leq |\vartheta|\cdot \left( \frac{1}{(1-|\vartheta|)^3} + 2\zeta(3)-1\right).
\]
If $\vartheta=0$, then
$\sum_n \left(\frac{\sigma}{(n-\vartheta)^2} + \frac{\sigma}{(n+\vartheta)^2}\right)
= 2 \sigma \sum_{n=1}^\infty \frac{1}{n^2} = \sigma \frac{\pi^2}{3}$.
-/)
  (latexEnv := "lemma")
  (discussion := 572)]
theorem lemma_abadsumas {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 ≤ s.re) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (ha' : a.IsHalfInteger) (hb' : b.IsHalfInteger) (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    let ϑ_minus : ℝ := s.im / (2 * π * b)
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    let g : ℝ → ℂ := fun t ↦
      if t ≠ 0 then (1 / Complex.sin (π * t) : ℂ) - (1 / (π * t : ℂ)) else 0
    let C : ℝ :=
      if ϑ ≠ 0 then
        s.re / 2 * ((1 / (Complex.sin (π * ϑ) ^ 2 : ℂ)).re - (1 / ((π * ϑ) ^ 2 : ℂ)).re) +
          |ϑ| / (2 * π ^ 2) * ((1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1)
      else
        s.re / 6
    ∃ E : ℂ, ∑' n : ℤ, (FourierTransform.fourier f n + FourierTransform.fourier f (-n)) =
      ((a ^ (-s) : ℂ) * g ϑ) / (2 * I) - ((b ^ (-s) : ℂ) * g ϑ_minus) / (2 * I) + E ∧
      ‖E‖ ≤ C := by
  sorry

@[blueprint
  "prop:dadaro"
  (title := "Approximation of zeta(s) by a partial sum")
  (statement := /--
Let $s = \sigma + i \tau$, $\sigma\geq 0$, $\tau\in \mathbb{R}$, with $s\ne 1$.
Let $a\in \mathbb{Z} + \frac{1}{2}$ with $a>\frac{|\tau|}{2\pi}$. Then
\begin{equation}\label{eq:abadlondie}
  \zeta(s) = \sum_{n\leq a} \frac{1}{n^s} - \frac{a^{1-s}}{1-s} + c_\vartheta a^{-s}
  + O^*\left(\frac{C_{\sigma,\vartheta}}{a^{\sigma+1}}\right),
\end{equation}
where $\vartheta = \frac{\tau}{2\pi a}$,
$c_\vartheta = \frac{i}{2} \left(\frac{1}{\sin \pi \vartheta} - \frac{1}{\pi \vartheta}\right)$
for $\vartheta\ne 0$, $c_0 =0$, and $C_{\sigma,\vartheta}$ is as in \eqref{eq:defcsigth}.
-/)
  (proof := /--
Assume first that $\sigma>0$. Let $b\in \mathbb{Z}+\frac{1}{2}$ with $b>a$, and define
$f(y) = \frac{1_{[a,b]}(y)}{y^s}$.
By Lemma~\ref{lem:abadtoabsum} and Lemma~\ref{lem:abadusepoisson},
$$\sum_{n\leq a} \frac{1}{n^s} = \zeta(s) + \frac{a^{1-s}}{1-s}
  - \lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n))
  + O^*\left(\frac{2 |s|}{\sigma b^\sigma}\right).$$
We apply Lemma~\ref{lem:abadsumas} to estimate
$\lim_{N\to \infty} \sum_{n=1}^N (\widehat{f}(n) + \widehat{f}(-n))$. We obtain
\[\sum_{n\leq a} \frac{1}{n^s} = \zeta(s) + \frac{a^{1-s}}{1-s} -
\frac{a^{-s} g(\vartheta)}{2 i} + O^*\left(\frac{C_{\sigma,\vartheta}}{a^{\sigma+1}}\right)
+ \frac{b^{-s} g(\vartheta_-)}{2 i} + O^*\left(\frac{2 |s|}{\sigma b^\sigma}\right),
\]
where $\vartheta_- = \frac{\tau}{2\pi b}$ and $g(t)$ is as in Lemma~\ref{lem:abadsumas},
and so $-\frac{g(\vartheta)}{2 i} = c_\vartheta$.
We let $b\to \infty$ through the half-integers, and obtain \eqref{eq:abadlondie},
since $b^{-\sigma}\to 0$, $\vartheta_-\to 0$ and $g(\vartheta_-)\to g(0) = 0$
as $b\to \infty$.

Finally, the case $\sigma=0$ follows since all terms in \eqref{eq:abadlondie} extend
continuously to $\sigma=0$.
-/)
  (latexEnv := "proposition")
  (discussion := 573)]
theorem proposition_dadaro {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 ≤ s.re) {a : ℝ} (ha : 0 < a)
    (ha' : a.IsHalfInteger) (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    let C : ℝ :=
      if ϑ ≠ 0 then
        s.re / 2 * ((1 / (Complex.sin (π * ϑ) ^ 2 : ℂ)).re - (1 / ((π * ϑ) ^ 2 : ℂ)).re) +
          |ϑ| / (2 * π ^ 2) * ((1 / ((1 - |ϑ|) ^ 3 : ℝ)) + 2 * (riemannZeta 3).re - 1)
      else
        s.re / 6
    let c : ℂ :=
      if ϑ ≠ 0 then
        I / 2 * ((1 / Complex.sin (π * ϑ) : ℂ) - (1 / (π * ϑ : ℂ)))
      else
        0
    ∃ E : ℂ, riemannZeta s =
      ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
      (a ^ (1 - s) : ℂ) / (1 - s) + c * (a ^ (-s) : ℂ) + E ∧
      ‖E‖ ≤ C / (a ^ (s.re + 1 : ℝ)) := by
  sorry

blueprint_comment /--
\begin{remark}
The term $c_\vartheta a^{-s}$ in \eqref{eq:abadlondie} does not seem to have been worked
out before in the literature; the factor of $i$ in $c_\vartheta$ was a surprise.
For the sake of comparison, let us note that, if $a\geq x$, then $|\vartheta|\leq 1/2\pi$,
and so $|c_\vartheta|\leq |c_{\pm 1/2\pi}| = 0.04291\dotsc$ and
$|C_{\sigma,\vartheta}|\leq |C_{\sigma,\pm 1/2\pi}|\leq 0.176\sigma +0.246$.
While $c_\vartheta$ is optimal, $C_{\sigma,\vartheta}$ need not be --
but then that is irrelevant for most applications.
\end{remark}
-/

end ZetaAppendix
