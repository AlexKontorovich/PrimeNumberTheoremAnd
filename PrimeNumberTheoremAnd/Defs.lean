import Architect
import PrimeNumberTheoremAnd.Fourier
import Mathlib.NumberTheory.Chebyshev

open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

noncomputable abbrev nth_prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable abbrev nth_prime' (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x

noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)

noncomputable abbrev nth_prime_gap (n : ℕ) : ℕ :=
  nth_prime (n + 1) - nth_prime n

def prime_gap_record (p g : ℕ) : Prop :=
  ∃ n, nth_prime n = p ∧ nth_prime_gap n = g ∧
    ∀ k, nth_prime k < p → nth_prime_gap k < g

open Classical in
@[blueprint
  "first-gap-def"
  (title := "First prime gap")
  (statement := /--
  $P(g)$ is the first prime $p_n$ for which the prime gap
  $p_{n+1}-p_n$ is equal to $g$, or $0$ if no such gap
  exists. -/)]
noncomputable def first_gap (g : ℕ) : ℕ :=
  if h : ∃ n, nth_prime_gap n = g then
    nth_prime (Nat.find h)
  else 0

def first_gap_record (g P : ℕ) : Prop :=
  first_gap g = P ∧
    ∀ g' ∈ Finset.Ico 1 g,
      Even g' ∨ g' = 1 → first_gap g' ∈ Set.Ico 1 P

def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x) ^ k)

@[blueprint
  "pi-def"
  (title := "pi")
  (statement := /--
  $\pi(x)$ is the number of primes less than or equal to
  $x$. -/)]
noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

@[blueprint
  "pi-star-def"
  (title := "pi")
  (statement := /--
  $\pi^*(x)$ is the sum of $\Lambda(n)/n$ for $n$ up to
  $x$. -/)]
noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, (Λ n : ℝ) / n

@[blueprint
  "li-def"
  (title := "li and Li")
  (statement := /--
  $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ (in the
  principal value sense) and
  $\mathrm{Li}(x) = \int_2^x \frac{dt}{\log t}$. -/)]
noncomputable def li (x : ℝ) : ℝ :=
  lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦
    ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)),
      1 / log t))

@[blueprint "li-def"]
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

@[blueprint
  "Epsi-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_\psi(x) = |\psi(x) - x| / x$ -/)]
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x

noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))

@[blueprint
  "classical-bound-psi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\psi$ satisfies a \emph{classical bound}
  with parameters $A, B, C, R, x_0$ if for all
  $x \geq x_0$ we have
  \[ E_\psi(x) \leq A \left(\frac{\log x}{R}\right)^B
     \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}
     \right). \]
  We say that it obeys a \emph{numerical bound} with
  parameter $\varepsilon(x_0)$ if for all $x \geq x_0$
  we have
  \[ E_\psi(x) \leq \varepsilon(x_0). \]
  -/)]
def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x

def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε

def Eψ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eψ.bound (ε x₀) x₀

@[blueprint
  "Epi-def"
  (title := "Equation (1) of FKS2")
  (statement := /--
  $E_\pi(x) = |\pi(x) - \mathrm{Li}(x)| /
  \mathrm{Li}(x)$. -/)]
noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)

noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)

@[blueprint
  "Etheta-def"
  (title := "Equation (2) of FKS2")
  (statement := /--
  $E_\theta(x) = |\theta(x) - x| / x$ -/)]
noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x

@[blueprint
  "classical-bound-theta"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\theta$ satisfies a \emph{classical bound}
  with parameters $A, B, C, R, x_0$ if for all
  $x \geq x_0$ we have
  \[ E_\theta(x) \leq A \left(\frac{\log x}{R}\right)^B
     \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}
     \right). \]
  We say that it obeys a \emph{numerical bound} with
  parameter $\varepsilon(x_0)$ if for all $x \geq x_0$
  we have
  \[ E_\theta(x) \leq \varepsilon(x_0). \]
  -/)]
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x

def Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ ε x₀

@[blueprint "classical-bound-pi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\pi$ satisfies a \emph{classical bound}
  with parameters $A, B, C, R, x_0$ if for all
  $x \geq x_0$ we have
  \[ E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B
     \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}
     \right). \]
  We say that it obeys a \emph{numerical bound} with
  parameter $\varepsilon(x_0)$ if for all $x \geq x_0$
  we have
  \[ E_\pi(x) \leq \varepsilon(x_0). \]
  -/)]
def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ.bound (ε x₀) x₀

def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ (3 / 5) / (log (log x)) ^ (1 / 5))

def Eπ_star.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ admissible_bound A B C R x

def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε

def Eπ_star.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ_star.bound (ε x₀) x₀

def Eπ_star.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ (3 / 5) / (log (log x)) ^ (1 / 5))

@[blueprint
  "admissible-bound-monotone"
  (title := "Admissible bound decreasing for large x")
  (statement := /--
  If $A,B,C,R > 0$ then the classical bound is monotone
  decreasing for $x \geq \exp( R (2B/C)^2 )$. -/)
  (proof := /-- Differentiate the bound and check the
  sign. -/)
  (latexEnv := "lemma")
  (discussion := 900)]
lemma admissible_bound.mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R)
      (Set.Ici (exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [admissible_bound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← log_exp (R * (2 * B / C) ^ 2)]
    exact log_le_log (exp_pos _) (Set.mem_Ici.mp ha)
  have huab : log a / R ≤ log b / R :=
    div_le_div_of_nonneg_right
      (log_le_log ((exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < log a / R :=
    lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [rpow_def_of_pos (hua₀.trans_le huab), rpow_def_of_pos hua₀,
    ← exp_add, ← exp_add, exp_le_exp]
  let sa := (log a / R) ^ ((1 : ℝ) / 2)
  let sb := (log b / R) ^ ((1 : ℝ) / 2)
  rw [show log (log b / R) = 2 * log sb from by
      grind [log_rpow (hua₀.trans_le huab) ((1 : ℝ) / 2)],
    show log (log a / R) = 2 * log sa from by
      grind [log_rpow hua₀ ((1 : ℝ) / 2)]]
  have hsab : sa ≤ sb :=
    rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← rpow_natCast _ 2, ← rpow_mul (by positivity)]
      norm_num [rpow_one]]
    exact rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * log t - C * t) (Set.Ici (2 * B / C)) by
    grind [h (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (this.trans hsab)) hsab]
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]

@[blueprint
  "classical-to-numeric"
  (title := "Classic bound implies numerical bound")
  (statement := /--
  A classical bound for $x \geq x_0$ implies a numerical
  bound for $x \geq \max(x_0,
  \exp( R (2B/C)^2  ))$. -/)
  (proof := /-- Immediate from previous lemma -/)
  (latexEnv := "lemma")
  (discussion := 901)]
lemma Eψ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEψ : Eψ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eψ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEψ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)

@[blueprint "classical-to-numeric"]
lemma Eθ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEθ : Eθ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eθ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEθ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)

@[blueprint "classical-to-numeric"]
lemma Eπ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEπ : Eπ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eπ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEπ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)
