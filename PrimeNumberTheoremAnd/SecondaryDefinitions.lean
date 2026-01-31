import Architect
import Mathlib.Topology.Order.Basic
import Mathlib.NumberTheory.PrimeCounting

import PrimeNumberTheoremAnd.PrimaryDefinitions
import PrimeNumberTheoremAnd.Li2Bounds


blueprint_comment /--
\section{Definitions}
-/

blueprint_comment /--
In this section we define the basic types of secondary estimates we will work with in the project.
-/

open Real Finset

/- Standard arithmetic functions. TODO: align this with notation used elsewhere in PNT+ -/

@[blueprint
  "pi-def"
  (title := "pi")
  (statement := /-- $\pi(x)$ is the number of primes less than or equal to $x$. -/)]
noncomputable def pi (x : ℝ) : ℝ :=  Nat.primeCounting ⌊x⌋₊

open Topology

@[blueprint
  "li-def"
  (title := "li and Li")
  (statement := /-- $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ (in the principal value sense) and $\mathrm{Li}(x) = \int_2^x \frac{dt}{\log t}$. -/)]
noncomputable def li (x : ℝ) : ℝ := lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦ ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1-ε) (1+ε)), 1 / log t))

@[blueprint "li-def"]
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

@[blueprint
  "log_upper"
  (title := "Log upper bound")
  (statement := /-- For $t > -1$, one has $\log (1+t) \leq t$. -/)
  (proof := /-- This follows from the mean value theorem. -/)
  (latexEnv := "sublemma")]
theorem log_le (t : ℝ) (ht : t > -1) : log (1 + t) ≤ t :=
  (Real.log_le_sub_one_of_pos (neg_lt_iff_pos_add'.mp ht)).trans add_tsub_le_left

@[blueprint
  "log_lower_1"
  (title := "First log lower bound")
  (statement := /-- For $t \geq 0$, one has $t - \frac{t^2}{2} \leq \log(1+t)$. -/)
  (proof := /-- Use Taylor's theorem with remainder and the fact that the second derivative of $\log(1+t)$ is at most $1$ for $t \geq 0$.-/)
  (latexEnv := "sublemma")
  (discussion := 765)]
theorem log_ge {t : ℝ} (ht : 0 ≤ t) : t - t ^ 2 / 2 ≤ log (1 + t) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  let f : ℝ → ℝ := fun s ↦ log (1 + s) - (s - s ^ 2 / 2)
  have hf_deriv_pos : ∀ s > 0, 0 ≤ deriv f s := by
    intro s hs
    norm_num [f, add_comm, show s + 1 ≠ 0 by positivity]
    ring_nf
    nlinarith [inv_mul_cancel₀ (by positivity : (1 + s) ≠ 0)]
  have h_mvt : ∃ c ∈ Set.Ioo 0 t, deriv f c = (f t - f 0) / (t - 0) := by
    refine exists_deriv_eq_slope _ ht ?_ ?_  <;> intro x hx
    · exact ContinuousAt.continuousWithinAt (by fun_prop (disch := grind))
    · exact DifferentiableAt.differentiableWithinAt (by fun_prop (disch := grind))
  norm_num +zetaDelta at h_mvt
  obtain ⟨c, ⟨hc₁, hc₂⟩, hc⟩ := h_mvt
  nlinarith [hf_deriv_pos c hc₁, mul_div_cancel₀ (log (1 + t) - (t - t ^ 2 / 2)) (by positivity)]

@[blueprint
  "log_lower_2"
  (title := "Second log lower bound")
  (statement := /-- For $0 \leq t \leq t_0 < 1$, one has $\frac{t}{t_0} \log (1-t_0) \leq \log(1-t)$. -/)
  (proof := /-- Use concavity of log.-/)
  (latexEnv := "sublemma")
  (discussion := 766)]
theorem log_ge' {t t₀ : ℝ} (ht : 0 ≤ t) (ht0 : t ≤ t₀) (ht0' : t₀ < 1) :
    (t / t₀) * log (1 - t₀) ≤ log (1 - t) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rcases ht0.eq_or_lt with rfl | ht0
  · field_simp [ht.ne]
    rfl
  have := strictConcaveOn_log_Ioi.2  (y := 1) (x := 1 - t₀) (by grind) (by grind) (by linarith)
  simp only [smul_eq_mul, log_one, mul_zero, add_zero, mul_one] at this
  convert this (a := t / t₀) (b := 1 - t / t₀) (by bound) (by bound) (by ring) |>.le using 2
  field [show t₀ ≠ 0 by linarith]

@[blueprint
  "symm_inv_log"
  (title := "Symmetrization of inverse log")
  (statement := /-- For $0 < t \leq 1/2$, one has $| \frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}| \leq \frac{16\log(4/3)}{3}$. -/)
  (proof := /-- The expression can be written as $\frac{|\log(1-t^2)|}{|\log(1-t)| |\log(1+t)|}$. Now use the previous upper and lower bounds, noting that $t^2 \leq 1/4$. NOTE: this gives the slightly weaker bound of $16 \log(4/3) / 3$, but this can suffice for applications.  The sharp bound would require showing that the left-hand side is monotone in $t$, which looks true but not so easy to verify. -/)
  (latexEnv := "sublemma")
  (discussion := 767)]
theorem symm_inv_log
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    |1 / log (1 + t) + 1 / log (1 - t)| ≤ 16 * log (4 / 3) / 3 := by
  have log_add_ne_zero : log (1 + t) ≠ 0 := by simp; grind
  have log_sub_ne_zero : log (1 - t) ≠ 0 := by simp; grind
  have : t ^ 2 <= 1 / 4 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num]
    gcongr
  have numerator := log_ge' (by positivity) this (by norm_num)
  have denominator1 := le_neg.mpr <| log_le (-t) (by linarith)
  have : 3 / 4 * t ≤ t - t ^ 2 / 2 := by
    rw [(by ring : t - t ^ 2 / 2 = (1 - t / 2) * t)]
    gcongr
    linarith
  have denominator2 := le_trans this <| log_ge ht.le
  have denominator : log (1 + t) * -(log (1 - t)) >= (3 / 4 * t) * t := by
    gcongr
    · bound
    · exact denominator1
  calc
  _ = |(log (1 + t) + log (1 - t)) / (log (1 + t) * log (1 - t))| := by
    congr
    field
  _ = |(log (1 - t^2)) / (log (1 + t) * log (1 - t))| := by
    rw [← log_mul (by linarith) (by linarith)]
    congr
    ring
  _ = (-(log (1 - t^2))) / (log (1 + t) * (-log (1 - t))) := by
    rw [abs_div, abs_mul, abs_of_nonpos <| log_nonpos (by bound)
      (by simp only [tsub_le_iff_right, le_add_iff_nonneg_right]; positivity),
      abs_of_nonneg <| log_nonneg (by linarith),
      abs_of_nonpos <| log_nonpos (by linarith) (by linarith)]
  _ ≤ (-t ^ 2 / (1 / 4) * log (3 / 4)) / (log (1 + t) * -log (1 - t)) := by
    gcongr
    · apply mul_nonneg
      · apply log_nonneg; linarith
      · apply neg_nonneg.mpr <| log_nonpos _ _ <;> linarith
    linarith
  _ ≤ (-t ^ 2 / (1 / 4) * log (3 / 4)) / (3 / 4 * t * t) := by
    gcongr
    apply mul_nonneg_of_nonpos_of_nonpos
    · apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
      apply neg_le.mp
      simpa using sq_nonneg t
    · apply log_nonpos <;> norm_num
  _ = _ := by
    rw [(by field : (3 : ℝ) / 4 = (4 / 3)⁻¹), log_inv]
    field

@[blueprint
  "li-approx"
  (title := "li approximation")
  (statement := /-- If $x \geq 2$ and $0 < \eps \leq 1$, then $\mathrm{li}(x) = \int_{[0,x] \backslash [-\eps, \eps]} \frac{dt}{\log t} + O_*( \frac{16\log(4/3)}{3} \eps)$. -/)
  (proof := /-- Symmetrize the principal value integral around 1 using the previous lemma. -/)
  (latexEnv := "sublemma")
  (discussion := 768)]
theorem li.eq
    (x ε : ℝ) (hx : x ≥ 2) (hε1 : 0 < ε) (hε2 : ε ≤ 1) : ∃ E,
    li x = ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)), 1 / log t + E ∧
    |E| ≤ 16 *log (4 / 3) / 3 * ε := by
    sorry

@[blueprint
  "li_minus_Li"
  (title := "li minus Li")
  (statement := /-- $\li(x) - \Li(x) = \li(2)$. -/)
  (proof := /-- This follows from the previous estimate. -/)
  (latexEnv := "remark")
  (discussion := 758)]
theorem li.sub_Li
    (x : ℝ) (h2x : 2 ≤ x) :
    li x - Li x = li 2 := by
    sorry

@[blueprint
  "Ramanujan-Soldner-constant"
  (title := "Ramanujan-Soldner constant")
  (statement := /-- $\li(2) = 1.0451\dots$. -/)
  (proof := /-- Use Sublemma \ref{li-approx} and some numerical integration. -/)
  (latexEnv := "lemma")
  (discussion := 759)]
theorem li.two_approx : li 2 ∈ Set.Icc 1.0451 1.0452 := by
  sorry

/-- The local li definition matches Li2Bounds.li (they are definitionally equal). -/
theorem li_eq_Li2Bounds_li (x : ℝ) : li x = Li2Bounds.li x := rfl

/-- Weak bounds on li(2) via symmetric form integration.
    The tighter bounds in li.two_approx require more precise numerical integration.
    Proved via LeanCert numerical integration in Li2Bounds.lean. -/
@[blueprint
  "li2-bounds-weak"
  (title := "Weak bounds on li(2)")
  (statement := /-- $1.039 \leq \li(2) \leq 1.06$. -/)
  (latexEnv := "sublemma")
  (discussion := 759)]
theorem li.two_approx_weak : li 2 ∈ Set.Icc 1.039 1.06 := by
  rw [li_eq_Li2Bounds_li]
  exact Li2Bounds.li_two_approx_weak_proof

/-- The symmetric form equals the principal value li(2).
    This connects the absolutely convergent symmetric integral ∫₀¹ g(t) dt
    to the principal value definition of li(2). -/
@[blueprint
  "li2-symmetric-eq"
  (title := "Symmetric form equals principal value")
  (statement := /-- $\int_0^1 \left(\frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}\right) dt = \mathrm{li}(2)$ -/)
  (latexEnv := "sublemma")
  (discussion := 764)]
theorem li2_symmetric_eq_li2 : Li2Bounds.li2_symmetric = li 2 := by
  rw [li_eq_Li2Bounds_li]
  exact Li2Bounds.li2_symmetric_eq_li2


@[blueprint
  "theta-def"
  (title := "theta")
  (statement := /-- $\theta(x) = \sum_{p \leq x} \log p$ where the sum is over primes $p$. -/)]
noncomputable def θ (x : ℝ) := Chebyshev.theta x


@[blueprint
  "Epi-def"
  (title := "Equation (1) of FKS2")
  (statement := /-- $E_\pi(x) = |\pi(x) - \mathrm{Li}(x)| / \mathrm{Li}(x)$ -/)]
noncomputable def Eπ (x : ℝ) : ℝ := |pi x - Li x| / (x / log x)


@[blueprint
  "Etheta-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_\theta(x) = |\theta(x) - x| / x$ -/)]
noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x


@[blueprint
  "classical-bound-theta"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\theta$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\theta(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  We say that it obeys a \emph{numerical bound} with parameter $ε(x_0)$ if for all $x \geq x_0$ we have
  \[ E_\theta(x) \leq ε(x_0). \]
  -/)]
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x

def Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ (ε x₀)

@[blueprint "classical-bound-pi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\pi$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  We say that it obeys a \emph{numerical bound} with parameter $ε(x_0)$ if for all $x \geq x_0$ we have
  \[ E_\pi(x) \leq ε(x_0). \]
  -/)]
def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := Eπ.bound (ε x₀) x₀

def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ A * (log x) ^ B * exp (-C * (log x) ^ (3/5) / (log (log x)) ^ (1/5))


def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x)^k)
