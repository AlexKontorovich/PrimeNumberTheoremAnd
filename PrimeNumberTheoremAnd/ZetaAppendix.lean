import Architect
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.ConstantSpeed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ZetaValues
import PrimeNumberTheoremAnd.ZetaBounds

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

open Real Complex MeasureTheory Finset Filter Topology Set Summable

-- may want to move this to a more globally accessible location

@[blueprint
  "e-def"
  (title := "e")
  (statement := /-- We recall that $e(\alpha) = e^{2\pi i \alpha}$. -/)]
noncomputable def e (α : ℝ) : ℂ := exp (2 * π * I * α)

private lemma h2piI_ne_zero : 2 * π * I ≠ 0 := by norm_num

private lemma continuousOn_e_comp (φ : ℝ → ℝ) (s : Set ℝ)
    (hφ : ContinuousOn φ s) : ContinuousOn (fun t ↦ e (φ t)) s := by
  simp only [e]; fun_prop

private lemma continuousOn_ofReal_deriv (φ : ℝ → ℝ) (a b : ℝ)
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b)) :
    ContinuousOn (fun t ↦ (↑(deriv φ t) : ℂ)) (Set.Icc a b) :=
  continuous_ofReal.comp_continuousOn hderiv_cont

private lemma denom1_ne_zero (φ : ℝ → ℝ) (a b : ℝ)
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    ∀ t ∈ Set.Icc a b, 2 * π * I * ↑(deriv φ t) ≠ 0 := by
  intro t ht
  exact mul_ne_zero h2piI_ne_zero (ofReal_ne_zero.mpr (hphi_ne t ht))

private lemma denom2_ne_zero (φ : ℝ → ℝ) (a b : ℝ)
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    ∀ t ∈ Set.Icc a b, 2 * π * I * ↑(deriv φ t) ^ 2 ≠ 0 := by
  intro t ht
  exact mul_ne_zero h2piI_ne_zero (pow_ne_zero 2 (ofReal_ne_zero.mpr (hphi_ne t ht)))

private lemma continuousOn_denom1 (φ : ℝ → ℝ) (a b : ℝ)
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b)) :
    ContinuousOn (fun t ↦ 2 * π * I * ↑(deriv φ t)) (Set.Icc a b) := by
  exact ContinuousOn.mul continuousOn_const (continuousOn_ofReal_deriv φ a b hderiv_cont)

private lemma continuousOn_denom2 (φ : ℝ → ℝ) (a b : ℝ)
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b)) :
    ContinuousOn (fun t ↦ 2 * π * I * ↑(deriv φ t) ^ 2) (Set.Icc a b) := by
  exact ContinuousOn.mul continuousOn_const ((continuousOn_ofReal_deriv φ a b hderiv_cont).pow 2)

private lemma intervalIntegrable_v' (φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hφ_cont : ContinuousOn φ (Set.Icc a b))
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b)) :
    IntervalIntegrable (fun t ↦ 2 * π * I * ↑(deriv φ t) * e (φ t)) volume a b :=
  (ContinuousOn.mul
    (continuousOn_denom1 φ a b hderiv_cont)
    (continuousOn_e_comp φ _ hφ_cont)).intervalIntegrable_of_Icc hab

private lemma continuousOn_rpow_const_Icc (a b p : ℝ) (ha_pos : 0 < a) :
    ContinuousOn (fun t ↦ t ^ p) (Set.Icc a b) := by
  apply ContinuousOn.rpow_const continuousOn_id
  intro x hx
  exact Or.inl (ne_of_gt (lt_of_lt_of_le ha_pos hx.1))

private lemma continuousOn_rpow_toComplex (a b p : ℝ) (ha_pos : 0 < a) :
    ContinuousOn (fun t ↦ ((t ^ p : ℝ) : ℂ)) (Set.Icc a b) :=
  continuous_ofReal.comp_continuousOn (continuousOn_rpow_const_Icc a b p ha_pos)

private lemma intervalIntegrable_term1 (σ : ℝ) (φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (ha_pos : 0 < a)
    (hφ_cont : ContinuousOn φ (Set.Icc a b))
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    IntervalIntegrable
      (fun x ↦ (x ^ (-σ - 1) : ℝ) / (2 * π * I * ↑(deriv φ x)) * e (φ x)) volume a b :=
  (ContinuousOn.mul
    (ContinuousOn.div
      (continuousOn_rpow_toComplex a b (-σ - 1) ha_pos)
      (continuousOn_denom1 φ a b hderiv_cont)
      (denom1_ne_zero φ a b hphi_ne))
    (continuousOn_e_comp φ _ hφ_cont)).intervalIntegrable_of_Icc hab

private lemma intervalIntegrable_term2 (σ : ℝ) (φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (ha_pos : 0 < a)
    (hφ_cont : ContinuousOn φ (Set.Icc a b))
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (hderiv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b))
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    IntervalIntegrable
      (fun x ↦ (x ^ (-σ) : ℝ) * ↑(deriv (deriv φ) x) /
        (2 * π * I * ↑(deriv φ x) ^ 2) * e (φ x)) volume a b :=
  (ContinuousOn.mul
    (ContinuousOn.mul
      (ContinuousOn.mul
        (continuousOn_rpow_toComplex a b (-σ) ha_pos)
        (continuous_ofReal.comp_continuousOn hderiv2_cont))
      (ContinuousOn.inv₀ (continuousOn_denom2 φ a b hderiv_cont)
        (denom2_ne_zero φ a b hphi_ne)))
    (continuousOn_e_comp φ _ hφ_cont)).intervalIntegrable_of_Icc hab

private lemma intervalIntegrable_u' (σ : ℝ) (φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (ha_pos : 0 < a)
    (hderiv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (hderiv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b))
    (hphi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    IntervalIntegrable
      (fun t ↦ (-σ * t ^ (-σ - 1) : ℝ) / (2 * π * I * ↑(deriv φ t)) +
        (t ^ (-σ) : ℝ) * (-↑(deriv (deriv φ) t) / (2 * π * I * ↑(deriv φ t) ^ 2)))
      volume a b :=
  (ContinuousOn.add
    (ContinuousOn.div
       (continuous_ofReal.comp_continuousOn
         (ContinuousOn.mul continuousOn_const
           (continuousOn_rpow_const_Icc a b (-σ - 1) ha_pos)))
      (continuousOn_denom1 φ a b hderiv_cont)
      (denom1_ne_zero φ a b hphi_ne))
    (ContinuousOn.mul
      (continuousOn_rpow_toComplex a b (-σ) ha_pos)
      (ContinuousOn.div
        (ContinuousOn.neg (continuous_ofReal.comp_continuousOn hderiv2_cont))
        (continuousOn_denom2 φ a b hderiv_cont)
        (denom2_ne_zero φ a b hphi_ne)))).intervalIntegrable_of_Icc hab

private lemma hasDerivAt_inv_phaseDeriv (φ : ℝ → ℝ) (t : ℝ)
    (hdiff2 : DifferentiableAt ℝ (deriv φ) t) (hne : deriv φ t ≠ 0) :
    HasDerivAt (fun x ↦ (1 : ℂ) / (2 * π * I * ↑(deriv φ x)))
      (-↑(deriv (deriv φ) t) / (2 * π * I * ↑(deriv φ t) ^ 2)) t := by
  have hne' : (↑(deriv φ t) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hne
  have hderiv_phi : HasDerivAt (fun x ↦ (↑(deriv φ x) : ℂ)) (↑(deriv (deriv φ) t)) t :=
    hdiff2.hasDerivAt.ofReal_comp
  have h_2piI_phi' : HasDerivAt (fun x ↦ 2 * π * I * ↑(deriv φ x))
      (2 * π * I * ↑(deriv (deriv φ) t)) t := hderiv_phi.const_mul (2 * π * I)
  have hinv : HasDerivAt (fun x ↦ (2 * π * I * ↑(deriv φ x))⁻¹)
      (-(2 * π * I * ↑(deriv (deriv φ) t)) / (2 * π * I * ↑(deriv φ t)) ^ 2) t := by
    have h2piI_phi'_ne : 2 * π * I * ↑(deriv φ t) ≠ 0 :=
      mul_ne_zero h2piI_ne_zero hne'
    have hinv_at : HasDerivAt (Inv.inv : ℂ → ℂ)
        (-((2 * π * I * ↑(deriv φ t)) ^ 2)⁻¹) (2 * π * I * ↑(deriv φ t)) :=
      hasDerivAt_inv h2piI_phi'_ne
    have hcomp := hinv_at.comp t h_2piI_phi'
    convert hcomp using 1
    field_simp
  convert hinv using 1
  · funext x; simp [div_eq_mul_inv]
  · field_simp [hne']

private lemma hasDerivAt_u_full (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hdiff2 : DifferentiableAt ℝ (deriv φ) t) (hne : deriv φ t ≠ 0) :
    HasDerivAt (fun x ↦ ((x ^ (-σ) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ x)))
      (((-σ * t ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ t)) +
       ((t ^ (-σ) : ℝ) : ℂ) * (-↑(deriv (deriv φ) t) / (2 * π * I * ↑(deriv φ t) ^ 2))) t := by
  have h1 : HasDerivAt (fun x ↦ ((x ^ (-σ) : ℝ) : ℂ)) (((-σ * t ^ (-σ - 1) : ℝ) : ℂ)) t :=
    (hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).ofReal_comp
  have h2 := hasDerivAt_inv_phaseDeriv φ t hdiff2 hne
  have hprod := h1.mul h2
  convert hprod using 1
  · funext x
    rw [Pi.mul_apply]
    ring_nf
  · ring_nf

private lemma hasDerivAt_e_comp (φ : ℝ → ℝ) (t : ℝ) (hdiff : DifferentiableAt ℝ φ t) :
    HasDerivAt (fun x ↦ e (φ x)) (2 * π * I * ↑(deriv φ t) * e (φ t)) t := by
  have hcomp :
      HasDerivAt (fun x ↦ cexp (2 * π * I * (φ x : ℂ)))
        (cexp (2 * π * I * (φ t : ℂ)) * (2 * π * I * (↑(deriv φ t)))) t := by
    exact (hasDerivAt_exp (2 * π * I * (φ t : ℂ))).comp t
      ((hdiff.hasDerivAt.ofReal_comp).const_mul (2 * π * I))
  simpa only [e, mul_assoc, mul_left_comm, mul_comm] using hcomp

private lemma integral_Icc_eq_interval {a b : ℝ} (h : a ≤ b) (f : ℝ → ℂ) :
    ∫ t in Set.Icc a b, f t = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le h]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

theorem integral_power_phase_ibp (σ : ℝ) (φ : ℝ → ℝ) (a b : ℝ) (hab : a < b) (ha_pos : 0 < a)
    (h_phi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0)
    (h_phi_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ φ t)
    (h_phi_diff2 : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (deriv φ) t)
    (h_phi_cont : ContinuousOn φ (Set.Icc a b))
    (h_deriv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (h_deriv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b)) :
    let Φ : ℝ → ℂ := fun t ↦ (t ^ (-σ) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    ∫ t in Set.Icc a b, (t ^ (-σ) : ℝ) * e (φ t) = Φ b - Φ a +
      (σ * ∫ t in Set.Icc a b, (t ^ (-σ - 1) : ℝ) / (2 * π * I * (deriv φ t)) * e (φ t)) +
      ∫ t in Set.Icc a b, (t ^ (-σ) : ℝ) * (deriv (deriv φ) t) /
        (2 * π * I * (deriv φ t) ^ 2) * e (φ t) := by
  intro Φ
  have hab_le : a ≤ b := le_of_lt hab
  rw [integral_Icc_eq_interval hab_le, integral_Icc_eq_interval hab_le,
    integral_Icc_eq_interval hab_le]
  let u : ℝ → ℂ := fun t ↦ ((t ^ (-σ) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ t))
  let v : ℝ → ℂ := fun t ↦ e (φ t)
  let u' : ℝ → ℂ := fun t ↦ ((-σ * t ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ t)) +
      ((t ^ (-σ) : ℝ) : ℂ) * (-↑(deriv (deriv φ) t) / (2 * π * I * ↑(deriv φ t) ^ 2))
  let v' : ℝ → ℂ := fun t ↦ 2 * π * I * ↑(deriv φ t) * e (φ t)
  have h_uv_eq_Phi : ∀ t, u t * v t = Φ t := by
    intro t
    simp only [u, v, Φ]
    ring_nf
  have h_lhs : ∫ x in a..b, ((x ^ (-σ) : ℝ) : ℂ) * e (φ x) =
      ∫ x in a..b, u x * v' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab_le] at hx
    simp only [u, v']
    field_simp [h_phi_ne x hx]
  rw [h_lhs]
  have h_ibp : (∫ x in a..b, u x * v' x) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
    have hIoo_to_Icc : ∀ {x : ℝ}, x ∈ Set.Ioo (min a b) (max a b) → x ∈ Set.Icc a b := by
      intro x hx
      rw [min_eq_left hab_le, max_eq_right hab_le] at hx
      exact Ioo_subset_Icc_self hx
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (by
        rw [uIcc_of_le hab_le]
        exact ContinuousOn.div
          (continuousOn_rpow_toComplex a b (-σ) ha_pos)
          (continuousOn_denom1 φ a b h_deriv_cont)
          (denom1_ne_zero φ a b h_phi_ne))
      (by
        rw [uIcc_of_le hab_le]
        exact continuousOn_e_comp φ _ h_phi_cont)
      (by
        intro x hx
        have hx_in : x ∈ Set.Icc a b := hIoo_to_Icc hx
        have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx_in.1
        exact hasDerivAt_u_full σ φ x hx_pos (h_phi_diff2 x hx_in) (h_phi_ne x hx_in))
      (by
        intro x hx
        exact hasDerivAt_e_comp φ x (h_phi_diff x (hIoo_to_Icc hx)))
      (by simpa [u'] using
        intervalIntegrable_u' σ φ a b hab_le ha_pos h_deriv_cont h_deriv2_cont h_phi_ne)
      (by simpa [v'] using intervalIntegrable_v' φ a b hab_le h_phi_cont h_deriv_cont)
  rw [h_ibp]
  simp only [h_uv_eq_Phi, sub_eq_add_neg, ← intervalIntegral.integral_neg, add_assoc]
  congr 1
  have h_cong : ∫ x in a..b, -(u' x * v x) =
      ∫ x in a..b,
        (σ * (((x ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ x)) * e (φ x)) +
          ((x ^ (-σ) : ℝ) : ℂ) * ↑(deriv (deriv φ) x) /
            (2 * π * I * ↑(deriv φ x) ^ 2) * e (φ x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [u', v]
    rw [neg_mul, show (↑(-(σ * x ^ (-σ - 1))) : ℂ) = -((↑σ : ℂ) * ↑(x ^ (-σ - 1))) by norm_cast]
    ring_nf
  have h_int_term1 : IntervalIntegrable
      (fun x ↦ ((x ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ x)) * e (φ x)) volume a b :=
    intervalIntegrable_term1 σ φ a b hab_le ha_pos h_phi_cont h_deriv_cont h_phi_ne
  have h_int_term2 : IntervalIntegrable
      (fun x ↦ ((x ^ (-σ) : ℝ) : ℂ) * ↑(deriv (deriv φ) x) /
        (2 * π * I * ↑(deriv φ x) ^ 2) * e (φ x)) volume a b :=
    intervalIntegrable_term2 σ φ a b hab_le ha_pos h_phi_cont h_deriv_cont h_deriv2_cont h_phi_ne
  rw [h_cong, intervalIntegral.integral_add (h_int_term1.const_mul σ) h_int_term2,
      intervalIntegral.integral_const_mul, sub_eq_add_neg]

theorem cpow_split_re_im (t : ℝ) (s : ℂ) (ht : 0 < t) :
    (t : ℂ) ^ s = (t : ℂ) ^ (s.re : ℂ) * cexp ((s.im * I) * Real.log t) := by
  have ht0 : (t : ℂ) ≠ 0 := ne_zero_of_re_pos ht
  conv_lhs => rw [← re_add_im s]
  rw [cpow_add _ _ ht0]
  congr 1
  rw [cpow_def_of_ne_zero ht0, ofReal_log ht.le, mul_comm]

private lemma phase_rewrite (t : ℝ) (s : ℂ) (ν : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ (-s) * e (ν * t) =
      ((t ^ (-s.re) : ℝ) : ℂ) * e (ν * t - (s.im / (2 * π)) * Real.log t) := by
  have hsplit := cpow_split_re_im t (-s) ht
  calc
    (t : ℂ) ^ (-s) * e (ν * t) =
        ((t : ℂ) ^ ((-s).re : ℂ)) *
          (cexp (((-s).im * I) * Real.log t) * cexp (2 * π * I * (ν * t))) := by
      rw [hsplit, mul_assoc]
      congr 2
      rw [e, ofReal_mul]
    _ = ((t : ℂ) ^ ((-s).re : ℂ)) * cexp (((-s).im * I) * Real.log t + 2 * π * I * (ν * t)) := by
      rw [mul_assoc, ← Complex.exp_add]
    _ = ((t ^ (-s.re) : ℝ) : ℂ) *
        cexp (2 * π * I * (ν * t - (s.im / (2 * π)) * Real.log t)) := by
      congr 1
      · rw [neg_re, ofReal_cpow ht.le]
      · congr 1
        rw [neg_im, ofReal_neg, neg_mul]
        field_simp
        ring_nf
    _ = ((t ^ (-s.re) : ℝ) : ℂ) * e (ν * t - (s.im / (2 * π)) * Real.log t) := by
      simp only [e, ofReal_sub, ofReal_mul, ofReal_div, ofReal_ofNat]

private lemma deriv_linear_sub_log (ν c : ℝ) (t : ℝ) (ht : t ≠ 0) :
    deriv (fun t ↦ ν * t - c * Real.log t) t = ν - c * t⁻¹ := by
  have hf : deriv (fun t ↦ ν * t) t = ν := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul ν).deriv
  have hg : deriv (fun t ↦ c * Real.log t) t = c * t⁻¹ := by
    rw [deriv_const_mul_field, Real.deriv_log]
  have hdiff_f : DifferentiableAt ℝ (fun t ↦ ν * t) t := by fun_prop
  have hdiff_g : DifferentiableAt ℝ (fun t ↦ c * Real.log t) t :=
    (Real.differentiableAt_log ht).const_mul c
  rw [deriv_fun_sub hdiff_f hdiff_g, hf, hg]

private lemma phi_deriv_ne_zero (s : ℂ) (ν a t : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (ha_pos : 0 < a) (hν : ν ≠ 0)
    (ht : a ≤ t) :
    deriv (fun t ↦ ν * t - s.im / (2 * π) * Real.log t) t ≠ 0 := by
  have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht
  rw [deriv_linear_sub_log ν (s.im / (2 * π)) t ht_pos.ne']
  intro hzero
  have h_eq : s.im = 2 * π * ν * t := by
    field_simp at hzero
    linarith [hzero]
  have hpi_pos : 0 < (2 * π : ℝ) := by positivity
  have h_abs : |s.im| = 2 * π * |ν| * t := by
    rw [h_eq, abs_mul, abs_mul, abs_of_pos hpi_pos, abs_of_pos ht_pos]
  absurd ha
  rw [not_lt, h_abs]
  field_simp
  exact ht

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
theorem lemma_aachIBP (s : ℂ) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
    let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℂ := fun t ↦
      (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
      (s.re * ∫ t in Set.Icc a b,
        (t ^ (-s.re - 1) : ℝ) / (2 * π * I * (deriv φ t)) * e (φ t)) +
      ∫ t in Set.Icc a b, (t ^ (-s.re) : ℝ) * (deriv (deriv φ) t) /
        (2 * π * I * (deriv φ t) ^ 2) * e (φ t) := by
  have ha_pos : 0 < a := lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by positivity)) ha
  intro φ Φ
  have hIcc_pos : Set.Icc a b ⊆ Set.Ioi 0 := fun t ht ↦ lt_of_lt_of_le ha_pos ht.1
  have h_lhs : ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) =
      ∫ t in Set.Icc a b, (t ^ (-s.re) : ℝ) * e (φ t) := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    simpa [φ] using phase_rewrite t s ν (hIcc_pos ht)
  rw [h_lhs]
  have h_phi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0 := by
    intro t ht
    exact phi_deriv_ne_zero s ν a t ha ha_pos hν ht.1
  have hsmooth : ContDiffOn ℝ 2 φ (Set.Ioi 0) := by
    simp only [φ]
    apply ContDiffOn.sub
    · fun_prop
    · apply ContDiffOn.mul contDiffOn_const
      exact contDiffOn_log.mono (fun x hx ↦ ne_of_gt hx)
  have h_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ φ t :=
    fun t ht ↦ (hsmooth.differentiableOn (by norm_num)).differentiableAt
      (Ioi_mem_nhds (hIcc_pos ht))
  have h_diff2 : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (deriv φ) t := by
    intro t ht
    have h := hsmooth.contDiffAt (Ioi_mem_nhds (hIcc_pos ht))
    have h1 : ContDiffAt ℝ 1 (deriv φ) t := h.derivWithin (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have h_cont : ContinuousOn φ (Set.Icc a b) :=
    (hsmooth.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)).continuousOn
  have h_deriv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b) := by
    have h1 : ContinuousOn (deriv φ) (Set.Ioi 0) :=
      hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact h1.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)
  have h_deriv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b) := by
    have h1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
      ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mp hsmooth).2.2
    exact (h1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
      (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)
  exact integral_power_phase_ibp s.re φ a b hb ha_pos h_phi_ne h_diff h_diff2
    h_cont h_deriv_cont h_deriv2_cont

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
          calc ∑ i ∈ range n, edist (g (x (i + 1))) (g (x i))
              ≤ ∑ i ∈ range n, ENNReal.ofReal (g (x i) - g (x (i + 1))) := by
                refine sum_le_sum (fun i _ ↦ ?_)
                simp only [edist_dist, sub_nonneg, h_monotone (hx₂ i) (hx₂ (i + 1)) (hx₁ (Nat.le_succ _)),
                  ENNReal.ofReal_le_ofReal_iff]
                rw [dist_eq_norm, Real.norm_of_nonpos] <;>
                linarith [h_monotone (hx₂ i) (hx₂ (i + 1)) (hx₁ (Nat.le_succ _))]
            _ ≤ ENNReal.ofReal (g a - g b) := by
                rw [← ENNReal.ofReal_sum_of_nonneg] <;> norm_num
                · apply ENNReal.ofReal_le_ofReal
                  have := sum_range_sub' (fun i ↦ g (x i)) n
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
          calc ∑ i ∈ range n, edist (g (x (i + 1))) (g (x i))
              ≤ ∑ i ∈ range n, ENNReal.ofReal (g (x (i + 1)) - g (x i)) := by
                refine sum_le_sum (fun i _ ↦ ?_)
                rw [edist_dist, dist_eq_norm, Real.norm_of_nonneg (sub_nonneg.mpr (h_monotone (hx₂ _)
                  (hx₂ _) (hx₁ (Nat.le_succ _))))]
            _ ≤ ENNReal.ofReal (g b - g a) := by
                rw [← ENNReal.ofReal_sum_of_nonneg]
                · rw [sum_range_sub (fun i ↦ g (x i))]
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

/-- For C¹ functions `g` and `F`, the error in integration by parts is bounded by
`sup ‖F‖ · ∫ |g'|`. -/
theorem lemma_IBP_bound_C1 {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * ∫ t in Icc a b, |deriv g t| := by
  have hint_parts : ∫ t in Icc a b, (g t) * (deriv F t) =
      (g b) * (F b) - (g a) * (F a) - ∫ t in Icc a b, (F t) * (deriv g t) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
        eq_sub_iff_add_eq, ← intervalIntegral.integral_add, intervalIntegral.integral_eq_sub_of_hasDeriv_right]
    · simpa only [Set.uIcc_of_le hab.le] using ContinuousOn.mul
        (continuous_ofReal.comp_continuousOn hg.continuousOn) hF.continuousOn
    · intro x hx
      have hxa : x > a := by cases max_cases a b <;> cases min_cases a b <;> linarith [hx.1, hx.2]
      have hxb : x < b := by cases max_cases a b <;> cases min_cases a b <;> linarith [hx.1, hx.2]
      convert HasDerivAt.hasDerivWithinAt <| HasDerivAt.mul
        (HasDerivAt.ofReal_comp <| hg.differentiableOn_one |> DifferentiableOn.hasDerivAt <| Icc_mem_nhds hxa hxb)
          (hF.differentiableOn_one |> DifferentiableOn.hasDerivAt <| Icc_mem_nhds hxa hxb)
            using 1
      ring
    · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
      refine Integrable.add ?_ ?_
      · have hintF : IntegrableOn (fun x ↦ deriv F x) (Ioo a b) := by
          have hcont := hF.continuousOn_derivWithin
          have hintF' : IntegrableOn (fun x ↦ derivWithin F (Icc a b) x) (Ioo a b) :=
            (hcont (uniqueDiffOn_Icc hab) le_rfl |> ContinuousOn.integrableOn_Icc) |>
              fun h ↦ h.mono_set Ioo_subset_Icc_self
          refine hintF'.congr ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using
            by rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
        apply Integrable.mono' _ _ _
        · exact fun x ↦ ‖deriv F x‖ * sSup (Set.image (fun x ↦ |g x|) (Icc a b))
        · exact Integrable.mul_const hintF.norm _
        · exact AEStronglyMeasurable.mul
            (continuous_ofReal.comp_aestronglyMeasurable
              (hg.continuousOn.aestronglyMeasurable measurableSet_Icc |>
                fun h ↦ h.mono_set Ioo_subset_Icc_self))
            hintF.aestronglyMeasurable
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using by
            simpa [mul_comm] using mul_le_mul_of_nonneg_left
              (le_csSup (IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn
                (continuous_abs.comp_continuousOn hg.continuousOn)))
                (Set.mem_image_of_mem _ <| Ioo_subset_Icc_self hx)) (norm_nonneg _)
      · have hintg : IntegrableOn (fun x ↦ deriv g x) (Ioo a b) := by
          have hcont := hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
          have hintg' : IntegrableOn (fun x ↦ derivWithin g (Icc a b) x) (Ioo a b) :=
            hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
          exact hintg'.congr_fun (fun x hx ↦
            by rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]) measurableSet_Ioo
        have hintFg : IntegrableOn (fun x ↦ F x * deriv g x) (Ioo a b) := by
          have hbdd : ∃ C, ∀ x ∈ Ioo a b, ‖F x‖ ≤ C :=
            IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn |>
              fun ⟨C, hC⟩ ↦ ⟨C, fun x hx ↦ hC x <| Ioo_subset_Icc_self hx⟩
          apply Integrable.mono' _ _ _
          · exact fun x ↦ hbdd.choose * ‖deriv g x‖
          · exact Integrable.const_mul hintg.norm _
          · exact AEStronglyMeasurable.mul
              (hF.continuousOn.aestronglyMeasurable measurableSet_Icc |>
                fun h ↦ h.mono_set Ioo_subset_Icc_self)
              (continuous_ofReal.comp_aestronglyMeasurable hintg.aestronglyMeasurable)
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using by
              simpa using mul_le_mul_of_nonneg_right (hbdd.choose_spec x hx)
                (norm_nonneg (deriv g x))
        exact hintFg
    · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
      have hintF : IntegrableOn (fun x ↦ deriv F x) (Ioo a b) := by
        have hcont := hF.continuousOn_derivWithin
        have hintF' : IntegrableOn (fun x ↦ derivWithin F (Icc a b) x) (Ioo a b) :=
          (hcont (uniqueDiffOn_Icc hab) le_rfl |> ContinuousOn.integrableOn_Icc) |>
            fun h ↦ h.mono_set Ioo_subset_Icc_self
        refine hintF'.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using
          by rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
      refine hintF.norm.const_mul ?_ |> fun h ↦ h.mono' ?_ ?_
      · exact sSup (Set.image (fun x ↦ ‖g x‖) (Icc a b))
      · exact AEStronglyMeasurable.mul
          (continuous_ofReal.comp_aestronglyMeasurable
            (hg.continuousOn.aestronglyMeasurable measurableSet_Icc |>
              fun h ↦ h.mono_set Ioo_subset_Icc_self))
          hintF.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using by
          simpa [abs_mul] using mul_le_mul_of_nonneg_right
            (le_csSup (IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn hg.continuousOn.norm))
              (Set.mem_image_of_mem _ <| Ioo_subset_Icc_self hx)) (norm_nonneg _)
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
      have hintg : IntegrableOn (fun x ↦ deriv g x) (Ioc a b) := by
        have hintg' : IntegrableOn (fun x ↦ deriv g x) (Ioo a b) := by
          have hcont := hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
          have hintg'' : IntegrableOn (fun x ↦ derivWithin g (Icc a b) x) (Ioo a b) :=
            hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
          exact hintg''.congr_fun (fun x hx ↦
            by rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]) measurableSet_Ioo
        rwa [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc] at *
      have hintFg : IntegrableOn (fun x ↦ F x * deriv g x) (Ioc a b) := by
        have hbdd : ∃ C, ∀ x ∈ Ioc a b, ‖F x‖ ≤ C :=
          IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn |>
            fun ⟨C, hC⟩ ↦ ⟨C, fun x hx ↦ hC x <| Ioc_subset_Icc_self hx⟩
        apply Integrable.mono' _ _ _
        · exact fun x ↦ hbdd.choose * ‖deriv g x‖
        · exact Integrable.const_mul hintg.norm _
        · exact AEStronglyMeasurable.mul
            (hF.continuousOn.aestronglyMeasurable measurableSet_Icc |>
              fun h ↦ h.mono_set Ioc_subset_Icc_self)
            (continuous_ofReal.comp_aestronglyMeasurable hintg.aestronglyMeasurable)
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using by
            simpa using mul_le_mul_of_nonneg_right (hbdd.choose_spec x hx)
              (norm_nonneg (deriv g x))
      convert hintFg using 1
  simp_all only [sub_sub_cancel_left, norm_neg, Set.mem_Icc, ge_iff_le]
  rw [← integral_const_mul]
  refine le_trans (norm_integral_le_integral_norm _) (integral_mono_of_nonneg ?_ ?_ ?_)
  · exact Eventually.of_forall fun x ↦ norm_nonneg _
  · refine Integrable.const_mul ?_ _
    have hderivint : IntegrableOn (deriv g) (Ioo a b) := by
      have hcont := hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
      exact (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self) |> fun h ↦ h.congr_fun
        (fun x hx ↦ by rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]) measurableSet_Ioo
    simpa only [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Icc] using hderivint.abs
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_ciSup ?_ t) (abs_nonneg _))
    · aesop
    · obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn.norm
      exact ⟨Max.max M 1, Set.forall_mem_range.mpr fun t ↦ by rw [ciSup_eq_ite]; aesop⟩

/-- Integration by parts bound for `C¹` monotone functions.
For `C¹` monotone `g` and `C¹` `F`, `‖∫ g F' - [gF]‖ ≤ sup ‖F‖ · (g(b) - g(a))`. -/
theorem lemma_IBP_bound_C1_monotone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) (hg_mono : MonotoneOn g (Icc a b))
    (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
    (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) := by
  have hbound := @lemma_IBP_bound_C1 a b hab g F hg hF
  have hdiff : DifferentiableOn ℝ g (Icc a b) := hg.differentiableOn_one
  have hderiv_nonneg : ∀ t ∈ Ioo a b, 0 ≤ deriv g t := by
    intro t ht
    have hlim : Tendsto (fun h ↦ (g (t + h) - g t) / h) (𝓝[Ioi 0] 0) (𝓝 (deriv g t)) := by
      have hHasDeriv : HasDerivAt g (deriv g t) t :=
        hdiff.differentiableAt (Icc_mem_nhds ht.1 ht.2) |>.hasDerivAt
      simpa [div_eq_inv_mul] using hHasDeriv.tendsto_slope_zero_right
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr ht.2)] with h hh
    apply div_nonneg
    · rw [sub_nonneg]
      refine hg_mono (Ioo_subset_Icc_self ht) ?_ (by linarith [hh.1])
      rw [Set.mem_Icc]
      constructor <;> linarith [ht.1, ht.2, hh.1, hh.2]
    · exact hh.1.le
  have hint_deriv : ∫ t in Icc a b, deriv g t = g b - g a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hg.continuousOn
    · intro t ht
      exact hdiff.differentiableAt (Icc_mem_nhds ht.1 ht.2) |>.hasDerivAt
    · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
      have hcont_dw := hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
      refine hcont_dw.integrableOn_Icc.mono_set Ioo_subset_Icc_self |>.congr_fun ?_ measurableSet_Ioo
      intro x hx
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  have hint_abs : ∫ t in Icc a b, |deriv g t| = ∫ t in Icc a b, deriv g t := by
    simp only [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
    rw [abs_of_nonneg (hderiv_nonneg x hx)]
  rw [hint_abs, hint_deriv] at hbound
  exact hbound

open scoped unitInterval in
/-- The Bernstein approximation of a monotone function is monotone. -/
theorem bernsteinApproximation_monotone (n : ℕ) (f : C(I, ℝ)) (hf : Monotone f) :
    Monotone (bernsteinApproximation n f) := by
  intro x y hxy
  simp only [bernsteinApproximation, smul_eq_mul, ContinuousMap.coe_sum, ContinuousMap.coe_mul,
    ContinuousMap.coe_const, sum_apply, Pi.mul_apply, Function.const_apply]
  have hmono : ∀ i j : Fin (n + 1), i ≤ j → f (bernstein.z i) ≤ f (bernstein.z j) :=
    fun i j hij ↦ hf <| Subtype.mk_le_mk.mpr <| by simpa [bernstein.z] using by gcongr; aesop
  have hsum : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (bernstein n i x * bernstein n j y - bernstein n i y * bernstein n j x) *
        (f (bernstein.z j) - f (bernstein.z i)) ≥ 0 := by
    refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
    by_cases hij : i ≤ j
    · refine mul_nonneg ?_ (sub_nonneg.mpr (hmono i j hij))
      have hineq : x.val ^ (i : ℕ) * (1 - x.val) ^ (n - i : ℕ) * y.val ^ (j : ℕ) *
          (1 - y.val) ^ (n - j : ℕ) ≥ x.val ^ (j : ℕ) * (1 - x.val) ^ (n - j : ℕ) *
          y.val ^ (i : ℕ) * (1 - y.val) ^ (n - i : ℕ) := by
        have hdiv : y.val ^ (j - i : ℕ) * (1 - x.val) ^ (j - i : ℕ) ≥
            x.val ^ (j - i : ℕ) * (1 - y.val) ^ (j - i : ℕ) := by
          rw [← mul_pow, ← mul_pow]
          exact pow_le_pow_left₀ (mul_nonneg (Subtype.property x |>.1)
            (sub_nonneg.2 (Subtype.property y |>.2)))
            (by nlinarith [show (x : ℝ) ≤ y from hxy, show (x : ℝ) ≥ 0 from Subtype.property x |>.1,
              show (y : ℝ) ≤ 1 from Subtype.property y |>.2]) _
        simp_all only [Finset.mem_univ, ge_iff_le, mul_comm, mul_left_comm, mul_assoc]
        convert mul_le_mul_of_nonneg_left hdiv (show 0 ≤ (x : ℝ) ^ (i : ℕ) * (y : ℝ) ^ (i : ℕ) *
            (1 - x : ℝ) ^ (n - j : ℕ) * (1 - y : ℝ) ^ (n - j : ℕ) by
          exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (mod_cast x.2.1) _)
            (pow_nonneg (mod_cast y.2.1) _)) (pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _))
            (pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)) using 1 <;> ring_nf
        · simp only [mul_assoc, ← pow_add, add_tsub_cancel_of_le (show (i : ℕ) ≤ j from hij),
            mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq, Icc.coe_eq_zero, Fin.val_eq_zero_iff]
          exact Or.inl <| Or.inl <| Or.inl <|
            by rw [tsub_add_tsub_cancel (mod_cast Fin.is_le _) (mod_cast hij)]
        · simp only [mul_assoc, ← pow_add, add_tsub_cancel_of_le (show (i : ℕ) ≤ j from hij),
            mul_eq_mul_left_iff, mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq, Icc.coe_eq_zero,
            Fin.val_eq_zero_iff]
          exact Or.inl <| Or.inl <| Or.inl <|
            by rw [tsub_add_tsub_cancel (mod_cast Fin.is_le _) (mod_cast hij)]
      simp_all only [Finset.mem_univ, ge_iff_le, bernstein, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_apply, sub_nonneg]
      simp_all only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
      convert mul_le_mul_of_nonneg_left hineq
        (show 0 ≤ (n.choose i : ℝ) * (n.choose j : ℝ) by positivity) using 1 <;> ring
    · refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
      · norm_num [bernstein, bernsteinPolynomial]
        have hexp : (x.val : ℝ) ^ (i : ℕ) * (y.val : ℝ) ^ (j : ℕ) ≤
            (x.val : ℝ) ^ (j : ℕ) * (y.val : ℝ) ^ (i : ℕ) := by
          rw [show (i : ℕ) = j + (i - j) by rw [Nat.add_sub_cancel' (le_of_not_ge hij)]]
          ring_nf
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by exact_mod_cast x.2.1)
            (by exact_mod_cast hxy) _) (mul_nonneg (pow_nonneg (by exact_mod_cast x.2.1) _)
            (pow_nonneg (by exact_mod_cast y.2.1) _))
        have hexp2 : (1 - x.val) ^ (n - i.val) * (1 - y.val) ^ (n - j.val) ≤
            (1 - x.val) ^ (n - j.val) * (1 - y.val) ^ (n - i.val) := by
          rw [show n - (i : ℕ) = n - (j : ℕ) - (i - j : ℕ) by
            rw [tsub_tsub, add_tsub_cancel_of_le (mod_cast le_of_not_ge hij)]]
          rw [show (1 - x.val) ^ (n - j.val) = (1 - x.val) ^ (n - j.val - (i.val - j.val)) *
              (1 - x.val) ^ (i.val - j.val) by rw [← pow_add, Nat.sub_add_cancel
              (show (i.val - j.val) ≤ n - j.val from Nat.sub_le_sub_right (mod_cast Fin.is_le i) _)],
            show (1 - y.val) ^ (n - j.val) = (1 - y.val) ^ (n - j.val - (i.val - j.val)) *
              (1 - y.val) ^ (i.val - j.val) by rw [← pow_add, Nat.sub_add_cancel
              (show (i.val - j.val) ≤ n - j.val from Nat.sub_le_sub_right (mod_cast Fin.is_le i) _)]]
          rw [mul_assoc, mul_comm ((1 - x.val) ^ (i.val - j.val))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (sub_nonneg.2 <| mod_cast y.2.2)
            (sub_le_sub_left (mod_cast hxy) _) _) <| pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)
            <| pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _
        convert mul_le_mul_of_nonneg_left (mul_le_mul hexp hexp2 (?_) (?_))
          (show (0 : ℝ) ≤ (n.choose i : ℝ) * (n.choose j : ℝ) by positivity) using 1 <;> ring_nf
        · exact mul_nonneg (pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _)
            (pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)
        · exact mul_nonneg (pow_nonneg (Subtype.property x |>.1) _)
            (pow_nonneg (Subtype.property y |>.1) _)
      · exact sub_nonpos_of_le <| hmono _ _ <| le_of_not_ge hij
  contrapose! hsum
  simp_all only [mul_comm, mul_sub, sum_sub_distrib, ← Finset.mul_sum _ _ _, bernstein.probability,
    one_mul, sub_neg]
  simp_all only [← mul_assoc, ← sum_comm, ← sum_mul, ← Finset.mul_sum _ _ _, bernstein.probability,
    mul_one]
  linarith

open scoped unitInterval in
/-- Continuous monotone functions on `[0,1]` can be uniformly approximated by smooth monotone
functions (polynomials). -/
theorem lemma_approx_monotone_C1_I (f : C(I, ℝ)) (hf_mono : Monotone f) :
    ∀ ε > 0, ∃ P : ℝ → ℝ, ContDiffOn ℝ 1 P I ∧ MonotoneOn P I ∧ ∀ x : I, |f x - P x| < ε := by
  intro ε hεpos
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp (tendsto_iff_norm_sub_tendsto_zero.mp
    (bernsteinApproximation_uniform f)) ε hεpos
  have hn : ‖bernsteinApproximation n f - f‖ < ε := by simpa [dist_zero_right, norm_norm] using hn n le_rfl
  let P : ℝ → ℝ := fun x ↦ ∑ k : Fin (n + 1), (n.choose k : ℝ) * x ^ (k : ℕ) * (1 - x) ^ (n - k : ℕ) * f (bernstein.z k)
  have hP (x) (hx : x ∈ I) : P x = bernsteinApproximation n f ⟨x, hx⟩ := by
    simp [P, bernsteinApproximation, bernstein, bernsteinPolynomial, mul_comm]
  refine ⟨P, ContDiff.contDiffOn <| ContDiff.sum fun k _ ↦ ?_, fun x hx y hy hxy ↦ ?_, fun x ↦ ?_⟩
  · apply_rules [ContDiff.mul, ContDiff.pow, contDiff_const, contDiff_id, ContDiff.sub]
  · rw [hP x hx, hP y hy]
    exact bernsteinApproximation_monotone n f hf_mono (Subtype.mk_le_mk.mpr hxy)
  · rw [abs_sub_comm, hP x x.2]
    exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (bernsteinApproximation n f - f) x) hn

/-- Continuous monotone functions on a compact interval can be uniformly approximated by `C¹`
monotone functions. -/
theorem lemma_approx_monotone_C1 {a b : ℝ} (hab : a < b) (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Icc a b)) (hg_mono : MonotoneOn g (Set.Icc a b)) :
    ∀ ε > 0, ∃ g' : ℝ → ℝ, ContDiffOn ℝ 1 g' (Set.Icc a b) ∧ MonotoneOn g' (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, |g x - g' x| < ε := by
  intro ε hε_pos
  set f := fun t : unitInterval ↦ g (a + t.val * (b - a)) with hf_def
  obtain ⟨P, hP_cont, hP_mono, hP_approx⟩ : ∃ P : ℝ → ℝ, ContDiffOn ℝ 1 P unitInterval ∧
    MonotoneOn P unitInterval ∧ ∀ t : unitInterval, |f t - P t| < ε := by
    have hf_cont : ContinuousOn f (Set.univ : Set unitInterval) :=
      hg_cont.comp (Continuous.continuousOn (by continuity)) fun x hx ↦
        ⟨by nlinarith [x.2.1, x.2.2], by nlinarith [x.2.1, x.2.2]⟩
    have hf_mono : Monotone f :=
      fun x y hxy ↦ hg_mono ⟨by nlinarith [x.2.1, x.2.2], by nlinarith [x.2.1, x.2.2]⟩ ⟨by nlinarith [y.2.1, y.2.2],
        by nlinarith [y.2.1, y.2.2]⟩ (by nlinarith [x.2.1, x.2.2, y.2.1, y.2.2, show (x : ℝ) ≤ y from hxy])
    have := @lemma_approx_monotone_C1_I
    exact this ⟨f, by simpa using hf_cont⟩ hf_mono ε hε_pos
  refine ⟨fun x ↦ P ((x - a) / (b - a)), ?_, ?_, ?_⟩
  · simp_all only [MonotoneOn, Set.mem_Icc, and_imp, gt_iff_lt, Subtype.forall]
    refine hP_cont.comp (ContDiffOn.div_const (contDiffOn_id.sub contDiffOn_const) _)
      fun x hx ↦ ⟨?_, ?_⟩ <;> nlinarith [hx.1, hx.2, mul_div_cancel₀ (x - a) (sub_ne_zero_of_ne hab.ne')]
  · simp_all only [MonotoneOn, Set.mem_Icc, and_imp, gt_iff_lt, Subtype.forall]
    exact fun x hx₁ hx₂ y hy₁ hy₂ hxy ↦ hP_mono (div_nonneg (by linarith) (by linarith))
      (div_le_one_of_le₀ (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith))
        (div_le_one_of_le₀ (by linarith) (by linarith)) (div_le_div_of_nonneg_right (by linarith) (by linarith))
  · simp_all only [MonotoneOn, Set.mem_Icc, and_imp, gt_iff_lt, Subtype.forall]
    intro x hx₁ hx₂
    convert hP_approx ((x - a) / (b - a)) (div_nonneg (by linarith) (by linarith))
      (div_le_one_of_le₀ (by linarith) (by linarith)) using 1
    congr 1
    rw [div_mul_cancel₀ _ (by linarith)]
    ring_nf

/-- Integration by parts bound for continuous monotone functions.
For continuous monotone `g` and `C¹` `F`, `‖∫ g F' - [gF]‖ ≤ sup ‖F‖ · (g(b) - g(a))`. -/
theorem lemma_IBP_bound_monotone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_mono : MonotoneOn g (Icc a b))
    (hF_C1 : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
    (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) := by
  have happrox := lemma_approx_monotone_C1 hab g hg_cont hg_mono
  choose! g' hg'_cont hg'_mono hg'_approx using happrox
  let gₙ := fun (n : ℕ) ↦ g' (1 / (n + 1 : ℝ))
  have hpos : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := fun n ↦ by positivity
  have hgₙ_cont : ∀ n, ContDiffOn ℝ 1 (gₙ n) (Icc a b) := fun n ↦ hg'_cont _ (hpos n)
  have hgₙ_mono : ∀ n, MonotoneOn (gₙ n) (Icc a b) := fun n ↦ hg'_mono _ (hpos n)
  have hgₙ_bound : ∀ n, ∀ x ∈ Icc a b, |gₙ n x - g x| ≤ 1 / (n + 1 : ℝ) := fun n x hx ↦ by
    rw [abs_sub_comm]; exact (hg'_approx _ (hpos n) x hx).le
  have hgₙ_lim : ∀ x ∈ Icc a b, Tendsto (fun n ↦ gₙ n x) atTop (nhds (g x)) := fun x hx ↦ by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ ↦ by positivity) (fun n ↦ hgₙ_bound n x hx)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hboundₙ : ∀ n, ‖(∫ t in Icc a b, (gₙ n t : ℂ) * deriv F t) - (gₙ n b * F b - gₙ n a * F a)‖ ≤
      (⨆ t ∈ Icc a b, ‖F t‖) * (gₙ n b - gₙ n a) := fun n ↦ by
    convert lemma_IBP_bound_C1_monotone hab (gₙ n) F (hgₙ_cont n) (hgₙ_mono n) hF_C1 using 1
  have hconv : Tendsto (fun n ↦ ∫ t in Icc a b, (gₙ n t : ℂ) * deriv F t) atTop
      (nhds (∫ t in Icc a b, (g t : ℂ) * deriv F t)) := by
    let M := sSup (image (|g ·|) (Icc a b))
    have hM_bdd : BddAbove (image (|g ·|) (Icc a b)) :=
      IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn (continuous_abs.comp_continuousOn hg_cont))
    have hM : ∀ x ∈ Icc a b, |g x| ≤ M := fun x hx ↦ le_csSup hM_bdd (mem_image_of_mem _ hx)
    refine tendsto_integral_of_dominated_convergence (fun x ↦ (M + 1) * ‖deriv F x‖) ?_ ?_ ?_ ?_
    · exact fun n ↦ AEStronglyMeasurable.mul (ContinuousOn.aestronglyMeasurable
        (continuous_ofReal.comp_continuousOn (hgₙ_cont n).continuousOn) measurableSet_Icc) (by fun_prop)
    · apply Integrable.const_mul <| Integrable.norm <|
        (hF_C1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl).integrableOn_Icc.congr _
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton a),
        measure_eq_zero_iff_ae_notMem.mp (measure_singleton b)] with x hxa hxb hx
      rw [derivWithin_of_mem_nhds]
      exact Icc_mem_nhds (lt_of_le_of_ne hx.1 (fun h ↦ hxa (mem_singleton_iff.mpr h.symm)))
        (lt_of_le_of_ne hx.2 hxb)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      simp only [norm_mul]; gcongr; norm_cast
      calc |gₙ n x| = ‖gₙ n x‖ := (norm_eq_abs _).symm
        _ = ‖(gₙ n x - g x) + g x‖ := by rw [sub_add_cancel]
        _ ≤ ‖gₙ n x - g x‖ + ‖g x‖ := norm_add_le _ _
        _ = |gₙ n x - g x| + |g x| := by simp only [norm_eq_abs]
        _ ≤ 1 / ((n : ℝ) + 1) + M := add_le_add (hgₙ_bound n x hx) (hM x hx)
        _ ≤ 1 + M := by gcongr; rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
        _ = M + 1 := add_comm ..
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact Tendsto.mul (continuous_ofReal.continuousAt.tendsto.comp <| hgₙ_lim x hx)
        tendsto_const_nhds
  have hlim_lhs : Tendsto (fun n ↦ ‖(∫ t in Icc a b, (gₙ n t : ℂ) * deriv F t) -
      (gₙ n b * F b - gₙ n a * F a)‖) atTop
      (nhds ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖) := by
    refine Tendsto.norm <| Tendsto.sub hconv <| Tendsto.sub ?_ ?_
    · exact Tendsto.mul (continuous_ofReal.continuousAt.tendsto.comp
        (hgₙ_lim b (right_mem_Icc.mpr hab.le))) tendsto_const_nhds
    · exact Tendsto.mul (continuous_ofReal.continuousAt.tendsto.comp
        (hgₙ_lim a (left_mem_Icc.mpr hab.le))) tendsto_const_nhds
  have hlim_rhs : Tendsto (fun n ↦ (⨆ t ∈ Icc a b, ‖F t‖) * (gₙ n b - gₙ n a)) atTop
      (nhds ((⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a))) := by
    exact Tendsto.mul tendsto_const_nhds
      (Tendsto.sub (hgₙ_lim b (right_mem_Icc.mpr hab.le)) (hgₙ_lim a (left_mem_Icc.mpr hab.le)))
  exact le_of_tendsto_of_tendsto' hlim_lhs hlim_rhs hboundₙ

/-- Integration by parts bound for continuous functions with antitone absolute value.
If `|g|` is antitone, `‖∫ g F'‖ ≤ sup ‖F‖ · 2 |g(a)|`. -/
theorem lemma_IBP_bound_abs_antitone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hgcont : ContinuousOn g (Icc a b)) (hganti : AntitoneOn (|g ·|) (Icc a b))
    (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖∫ t in Icc a b, (g t : ℂ) * deriv F t‖ ≤ (⨆ t ∈ Icc a b, ‖F t‖) * (2 * |g a|) := by
  have hsign : (∀ t ∈ Icc a b, g t ≥ 0) ∨ (∀ t ∈ Icc a b, g t ≤ 0) := by
    by_cases hsign : ∃ a' b' : ℝ, a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ g a' * g b' < 0
    · obtain ⟨a', b', ha', hb', hab', hsign⟩ := hsign
      obtain ⟨r, hr⟩ : ∃ r ∈ Icc a' b', g r = 0 := by
        have hivt : ContinuousOn g (Icc a' b') := hgcont.mono (Icc_subset_Icc ha' hab')
        have := hivt.image_Icc hb'.le
        exact this.symm.subset (Set.mem_Icc.mpr ⟨by nlinarith [Set.mem_Icc.mp (this ▸
          mem_image_of_mem g (Set.left_mem_Icc.mpr hb'.le)), Set.mem_Icc.mp (this ▸
          mem_image_of_mem g (Set.right_mem_Icc.mpr hb'.le))], by nlinarith [mem_Icc.mp (this ▸
          mem_image_of_mem g (Set.left_mem_Icc.mpr hb'.le)), mem_Icc.mp (this ▸
          mem_image_of_mem g (Set.right_mem_Icc.mpr hb'.le))]⟩)
      have := hganti ⟨by linarith [hr.1.1], by linarith [hr.1.2]⟩ ⟨by linarith [hr.1.1], by
        linarith [hr.1.2]⟩ hr.1.2
      simp_all
    · contrapose! hsign
      obtain ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₁, hy₂⟩⟩ := hsign
      norm_num at *
      cases lt_or_gt_of_ne (show x ≠ y by rintro rfl; linarith) with
      | inl h => exact ⟨x, hx₁.1, y, by linarith, by linarith, by nlinarith⟩
      | inr h => exact ⟨y, hy₁.1, x, by linarith, by linarith, by nlinarith⟩
  cases hsign with
  | inl hsign =>
    have hbd₁ : ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * (g a - g b) := by
      have := @lemma_IBP_bound_monotone a b hab (fun t ↦ -g t) F ?_ ?_ ?_ <;> norm_num at *
      · convert this using 1 <;> norm_num [integral_neg]
        · ring_nf; rw [← norm_neg]; ring_nf
        · exact Or.inl <| by ring
      · exact hgcont.neg
      · intro t ht u hu htu; have := hganti ht hu htu; simp_all [abs_of_nonneg]
      · assumption
    have hbd₂ : ‖g b * F b - g a * F a‖ ≤ (⨆ t ∈ Icc a b, ‖F t‖) * (g b + g a) := by
      refine (norm_sub_le _ _).trans ?_
      have hFle : ∀ t ∈ Icc a b, ‖F t‖ ≤ ⨆ t ∈ Icc a b, ‖F t‖ := fun t ht ↦ by
        apply le_csSup
        · obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn
          exact ⟨max M 1, forall_mem_range.mpr fun t ↦ by rw [ciSup_eq_ite]; aesop⟩
        · exact ⟨t, by simp_all⟩
      norm_num at *
      rw [abs_of_nonneg (hsign b hab.le le_rfl), abs_of_nonneg (hsign a le_rfl hab.le)]
      nlinarith [hFle b hab.le le_rfl, hFle a le_rfl hab.le, hsign b hab.le le_rfl, hsign a le_rfl hab.le]
    have hbd₃ : ‖∫ t in Icc a b, (g t : ℂ) * deriv F t‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * (g a - g b) + (⨆ t ∈ Icc a b, ‖F t‖) * (g b + g a) := by
      have h := norm_add_le ((∫ t in Icc a b, (g t : ℂ) * deriv F t) -
        (g b * F b - g a * F a)) (g b * F b - g a * F a)
      simpa using h.trans (add_le_add hbd₁ hbd₂)
    exact hbd₃.trans (by
      rw [abs_of_nonneg (hsign a <| left_mem_Icc.mpr hab.le)]
      nlinarith [show 0 ≤ ⨆ t ∈ Icc a b, ‖F t‖ from iSup_nonneg fun _ ↦ iSup_nonneg fun _ ↦ norm_nonneg _])
  | inr hsign =>
    have hbd₁ : ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) := by
      apply_rules [lemma_IBP_bound_monotone]
      intro x hx y hy hxy; have := hganti hx hy hxy; simp_all [abs_of_nonpos]
    have hbd₂ : ‖g b * F b - g a * F a‖ ≤ (⨆ t ∈ Icc a b, ‖F t‖) * (|g b| + |g a|) := by
      have hFle : ∀ t ∈ Icc a b, ‖F t‖ ≤ ⨆ t ∈ Icc a b, ‖F t‖ := fun t ht ↦ by
        apply le_csSup
        · obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn.norm
          use max M 1
          rintro x ⟨t, rfl⟩; by_cases ht : t ∈ Icc a b <;> simp_all
        · exact ⟨t, by simp_all⟩
      refine (norm_sub_le ..).trans ?_
      simp only [Set.mem_Icc, and_imp, norm_mul, norm_real, norm_eq_abs] at *
      nlinarith [abs_nonneg (g b), abs_nonneg (g a),
        hFle b (by linarith) (by linarith), hFle a (by linarith) (by linarith)]
    have hbd₃ : ‖∫ t in Icc a b, (g t : ℂ) * deriv F t‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) + (⨆ t ∈ Icc a b, ‖F t‖) * (|g b| + |g a|) := by
      have h := norm_add_le ((∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)) (g b * F b - g a * F a)
      simpa using h.trans (add_le_add hbd₁ hbd₂)
    convert hbd₃ using 1
    rw [abs_of_nonpos (hsign b <| right_mem_Icc.mpr hab.le), abs_of_nonpos (hsign a <| left_mem_Icc.mpr hab.le)]
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
theorem lemma_aachmonophase {a b : ℝ} (ha : a < b) (φ : ℝ → ℝ) (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) (h g : ℝ → ℝ) (hg : ∀ t, g t = h t / deriv φ t)
    (hg_cont : ContinuousOn g (Set.Icc a b)) (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    ‖∫ t in Set.Icc a b, h t * e (φ t)‖ ≤ |g a| / π := by
  let F : ℝ → ℂ := fun t ↦ (1 / (2 * Real.pi * I)) * (exp (2 * Real.pi * I * φ t))
  have h_integral_bound : ‖∫ t in Set.Icc a b, (g t : ℂ) * (deriv F t)‖ ≤ (⨆ t ∈ Set.Icc a b, ‖F t‖) * (2 * |g a|) :=
    lemma_IBP_bound_abs_antitone ha g F hg_cont hg_mon <|
      ContDiffOn.mul contDiffOn_const <| contDiff_exp.comp_contDiffOn <|
        ContDiffOn.mul contDiffOn_const <| ofRealCLM.contDiff.comp_contDiffOn hφ_C1
  have h_deriv_F : ∀ t ∈ Set.Ioo a b, deriv F t = (exp (2 * Real.pi * I * φ t)) * (deriv φ t) := by
    intro t ht
    rw [deriv_const_mul]
    · norm_num [Complex.exp_ne_zero, mul_comm]
      erw [HasDerivAt.deriv (HasDerivAt.comp t (Complex.hasDerivAt_exp _) (HasDerivAt.mul (HasDerivAt.ofReal_comp
        (hφ_C1.differentiableOn_one |> DifferentiableOn.hasDerivAt <| Icc_mem_nhds ht.1 ht.2)) <| hasDerivAt_const ..))]
      norm_num
      ring_nf
      simp
    · apply Complex.differentiableAt_exp.comp
      apply DifferentiableAt.const_mul <| ofRealCLM.differentiableAt.comp _ <| DifferentiableOn.differentiableAt
        hφ_C1.differentiableOn_one (Icc_mem_nhds ht.1 ht.2) ..
  have h_norm_F : ⨆ t ∈ Set.Icc a b, ‖F t‖ = 1 / (2 * Real.pi) := by
    dsimp only [F]
    rw [@ciSup_eq_of_forall_le_of_forall_lt_exists_gt] <;> norm_num [norm_exp, abs_of_nonneg pi_pos.le]
    · exact fun t ↦ by rw [ciSup_eq_ite]; split_ifs <;> norm_num; linarith [pi_pos]
    · exact fun w hw ↦ ⟨a, hw.trans_le <| by rw [ciSup_pos]; norm_num; linarith⟩
  have h_integral_subst : ‖∫ t in Set.Icc a b, (g t : ℂ) * (deriv F t)‖ = ‖∫ t in Set.Icc a b,
      (h t : ℂ) * (exp (2 * Real.pi * I * φ t))‖ := by
    simp only [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by rw [h_deriv_F t ht, hg t]]
    simp only [div_eq_mul_inv, ofReal_mul, ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
    refine congr_arg Norm.norm <| setIntegral_congr_fun measurableSet_Ioo <| fun x hx ↦ ?_
    simp [mul_inv_cancel_left₀ (ofReal_ne_zero.mpr (hφ'_ne0 x (Set.Ioo_subset_Icc_self hx)))]
  exact h_integral_subst ▸ h_integral_bound.trans (by rw [h_norm_F]; ring_nf; norm_num [pi_pos.ne'])

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
    (ha : a > |τ| / (2 * π * |ν|)) (k : ℕ) (hk : 1 ≤ k) :
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
\frac{|\tau|}{2\pi} \frac{t^{-\sigma-2}}{|\varphi_\nu'(t)|^3}$ is decreasing on $[a,b]$
we also know, as before, that $g_2(t)$ is continuous.
Hence, again by Lemma \ref{lem:aachmonophase},
\[\left|\int_a^b \frac{t^{-\sigma} \varphi_\nu''(t)}{2\pi i (\varphi_\nu'(t))^2}
 e(\varphi_\nu(t)) dt\right|\leq \frac{1}{2\pi} \frac{|g_2(a)|}{\pi} = \frac{1}{2\pi^2}
 \frac{a^{-\sigma-1} |\vartheta|}{\left|\nu - \vartheta\right|^3}.
\]
-/)
  (latexEnv := "lemma")
  (discussion := 550)]
lemma deriv_e {φ : ℝ → ℝ} {t : ℝ} (hφ : DifferentiableAt ℝ φ t) :
    deriv (fun t ↦ e (φ t)) t = 2 * π * I * deriv φ t * e (φ t) := by
  simp only [e]
  apply HasDerivAt.deriv
  convert (Complex.hasDerivAt_exp _).comp t (hφ.hasDerivAt.ofReal_comp.const_mul (2 * π * I)) using 1
  ring

theorem lemma_aachfour (s : ℂ) (hsigma : 0 ≤ s.re) (ν : ℝ) (hν : ν ≠ 0) (a b : ℝ)
    (ha : a > |s.im| / (2 * π * |ν|)) (hb : b > a) :
    let φ : ℝ → ℝ := fun t ↦ ν * t - (s.im / (2 * π)) * Real.log t
    let Φ : ℝ → ℂ := fun t ↦ (t ^ (-s.re) : ℝ) * e (φ t) / (2 * π * I * (deriv φ t))
    let ϑ : ℝ := s.im / (2 * π * a)
    ∃ E, ∫ t in Set.Icc a b, t ^ (-s) * e (ν * t) = Φ b - Φ a +
      ((a ^ (-s.re - 1) : ℝ) / (2 * π ^ 2)) * E ∧
      ‖E‖ ≤ s.re / (|ν - ϑ| ^ 2) + |ϑ| / (|ν - ϑ| ^ 3) := by
  intro φ Φ ϑ
  rw [lemma_aachIBP s ν hν a b ha hb]
  dsimp only [φ, Φ]
  let g_1 : ℝ → ℝ := fun t ↦ t ^ (-s.re - 1) / (deriv φ t) ^ 2
  have ha_pos : 0 < a := lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by positivity)) ha
  have hsmooth : ContDiffOn ℝ 2 φ (Set.Ioi 0) := by
    simp only [φ]
    apply ContDiffOn.sub
    · fun_prop
    · apply ContDiffOn.mul contDiffOn_const
      exact contDiffOn_log.mono (fun x hx ↦ ne_of_gt hx)
  have hcontdiffφ : ContDiffOn ℝ 1 φ (Set.Icc a b) := (hsmooth.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)).of_le (by norm_num)
  have h_cont : ContinuousOn φ (Set.Icc a b) :=
    (hsmooth.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)).continuousOn
  have h_deriv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b) := by
    have h1 : ContinuousOn (deriv φ) (Set.Ioi 0) :=
      hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact h1.mono (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)
  have h_deriv2_cont : ContinuousOn (fun t ↦ deriv (deriv φ) t) (Set.Icc a b) := by
    have h1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
      ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mp hsmooth).2.2
    exact (h1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
      (fun x hx ↦ lt_of_lt_of_le ha_pos hx.1)
  have hφ_deriv : ∀ t ∈ Set.Icc a b, deriv φ t = ν - s.im / (2 * π * t) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
    rw [show φ = fun x ↦ ν * x - (s.im / (2 * π)) * Real.log x from rfl]
    convert HasDerivAt.deriv (HasDerivAt.sub (HasDerivAt.const_mul ν (hasDerivAt_id t))
      (HasDerivAt.const_mul (s.im / (2 * π)) (Real.hasDerivAt_log ht_pos.ne'))) using 1
    field_simp
  have hφ_deriv2 : ∀ t ∈ Set.Icc a b, deriv (deriv φ) t = s.im / (2 * π * t^2) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
    have h_deriv_φ : ∀ x ∈ Set.Ioi 0, deriv φ x = ν - s.im / (2 * π * x) := by
      intro x hx
      rw [show φ = fun x ↦ ν * x - (s.im / (2 * π)) * Real.log x from rfl]
      convert HasDerivAt.deriv (HasDerivAt.sub (HasDerivAt.const_mul ν (hasDerivAt_id x))
        (HasDerivAt.const_mul (s.im / (2 * π)) (Real.hasDerivAt_log (ne_of_gt hx)))) using 1
      field_simp
    have : deriv φ =ᶠ[𝓝 t] fun x ↦ ν - s.im / (2 * π * x) := by
      apply eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht_pos)
      intro x hx
      exact h_deriv_φ x hx
    rw [this.deriv_eq]
    apply HasDerivAt.deriv
    rw [show (fun x ↦ ν - s.im / (2 * π * x)) = (fun x ↦ ν - (s.im / (2 * π)) * x⁻¹) by ext; field_simp]
    convert HasDerivAt.sub (hasDerivAt_const t ν)
      (HasDerivAt.const_mul (s.im / (2 * π)) (hasDerivAt_inv ht_pos.ne')) using 1
    field_simp [Real.two_pi_pos.ne']
    ring
  have h_deriv_ne_zero : (∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) := by
    intro t ht
    exact phi_deriv_ne_zero s ν a t ha ha_pos hν ht.1
  have g_1_cont : ContinuousOn g_1 (Set.Icc a b) := by
    apply ContinuousOn.div
    · apply continuousOn_rpow_const_Icc (ha_pos := ha_pos)
    · exact h_deriv_cont.pow 2
    · intro t ht
      specialize h_deriv_ne_zero t ht
      exact pow_ne_zero 2 h_deriv_ne_zero
  have hg_1_antitone : AntitoneOn (fun t ↦ |g_1 t|) (Set.Icc a b) := by
    let f : ℝ → ℝ := fun t ↦ t ^ (-s.re - 1) * |2 * π * ν - s.im / t| ^ (-2 : ℝ)
    have hf_anti : AntitoneOn f (Set.Icc a b) := by
      convert lemma_aachdecre s.re hsigma s.im ν hν a b ha 1 (by norm_num) using 1
      ext t
      dsimp [f]
      congr 2
      · simp
      · norm_num
    have h_scaled_anti : AntitoneOn (fun t ↦ (2 * π) ^ 2 * f t) (Set.Icc a b) := by
      intro x hx y hy hxy
      apply mul_le_mul_of_nonneg_left (hf_anti hx hy hxy)
      positivity
    have hg_eq : Set.EqOn (fun t ↦ |g_1 t|) (fun t ↦ (2 * π) ^ 2 * f t) (Set.Icc a b) := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
      dsimp only [g_1, f]
      rw [abs_div, abs_pow, abs_rpow_of_nonneg ht_pos.le]
      have hφ' : deriv φ t = ν - s.im / (2 * π * t) := by
        rw [show φ = fun x ↦ ν * x - (s.im / (2 * π)) * Real.log x from rfl]
        convert HasDerivAt.deriv (HasDerivAt.sub (HasDerivAt.const_mul ν (hasDerivAt_id t))
          (HasDerivAt.const_mul (s.im / (2 * π)) (Real.hasDerivAt_log ht_pos.ne'))) using 1
        field_simp
      rw [hφ']
      have h_inner : 2 * π * ν - s.im / t = 2 * π * (ν - s.im / (2 * π * t)) := by
        field_simp [ht_pos.ne', Real.two_pi_pos.ne']
      rw [h_inner]
      rw [abs_mul, abs_of_pos Real.two_pi_pos, mul_rpow Real.two_pi_pos.le (abs_nonneg _),
        abs_of_pos ht_pos, mul_left_comm ((2 * π) ^ 2)]
      field_simp
      have : 2 ^ 2 * π ^ 2 * (2 * π) ^ (-2 : ℝ) = 1 := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two, mul_pow]
        field_simp [Real.two_pi_pos.ne']
      rw [this]
      simp only [sq_abs, one_div, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, one_mul,
        inv_inj]
      symm; apply sq_abs
    exact h_scaled_anti.congr hg_eq.symm
  have g_1_integral_bound : ‖∫ t in Set.Icc a b, (t : ℂ) ^ ((-s.re - 1) : ℂ) / (2 * π * I * deriv φ t) * e (φ t)‖ ≤
    1 / (2 * π ^ 2) * (a ^ (-s.re - 1) / |ν - ϑ| ^ 2) := by
    let h : ℝ → ℝ := fun t ↦ t^(-s.re - 1) / deriv φ t
    have hg_1_eq_h_div_deriv_φ : (∀ (t : ℝ), g_1 t = h t / deriv φ t) := by
      intro t
      dsimp [g_1, h]
      rw [div_div, pow_two]
    have hmonophase := lemma_aachmonophase (a := a) (b := b) (φ := φ) (by simp [hb])
      (hcontdiffφ) (h_deriv_ne_zero) h g_1 hg_1_eq_h_div_deriv_φ g_1_cont hg_1_antitone
    simp only [ofReal_div, h] at hmonophase
    have h_factor : (fun t => (t ^ (-s.re - 1 : ℂ) / (2 * π * I * deriv φ t)) * e (φ t)) =
                (fun t => (1 / (2 * π * I)) * (t ^ (-s.re - 1 : ℂ) / deriv φ t * e (φ t))) := by
      ext t
      field_simp
    rw [h_factor]
    have step1 : ∫ (t : ℝ) in Set.Icc a b, 1 / (2 * π * I) * ((t : ℂ) ^ ((-s.re - 1) : ℂ) / (deriv φ t) * e (φ t))
           = 1 / (2 * π * I) * ∫ (t : ℝ) in Set.Icc a b, (t : ℂ) ^ ((-s.re - 1) : ℂ) / (deriv φ t) * e (φ t) :=
      integral_const_mul _ _
    rw [step1, norm_mul]
    have h_norm_const : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
        norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, mul_eq_mul_right_iff, inv_inj,
        abs_eq_self, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
      positivity
    rw [h_norm_const]
    trans (1 / (2 * π)) * (|g_1 a| / π)
    · have h_int_eq : ∫ (t : ℝ) in Set.Icc a b, (t : ℂ) ^ (-s.re - 1 : ℂ) / ↑(deriv φ t) * e (φ t)
              = ∫ (t : ℝ) in Set.Icc a b, ↑(t ^ (-s.re - 1)) / ↑(deriv φ t) * e (φ t) := by
        refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [Complex.ofReal_cpow]
        · simp only [Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one]
        · have : 0 ≤ |s.im| / (2 * π * |ν|) := by positivity
          linarith [ht.1, ha]
      rw [h_int_eq]
      apply mul_le_mul_of_nonneg_left hmonophase (by positivity)
    · rw [div_mul_eq_mul_div, mul_div_assoc]
      dsimp only [g_1]
      field_simp
      have hderivφ_eq_nu_minus_theta : deriv φ a = ν - ϑ := by
        rw [hφ_deriv _ (left_mem_Icc.mpr hb.le)]
      rw [hderivφ_eq_nu_minus_theta, abs_div, Real.abs_rpow_of_nonneg ha_pos.le,
        abs_pow, abs_of_pos ha_pos]
  let g_2 : ℝ → ℝ := fun t ↦ t ^ (-s.re) * deriv (deriv φ) t / (deriv φ t) ^ 3
  have g_2_cont : ContinuousOn g_2 (Set.Icc a b) := by
    apply ContinuousOn.div
    · refine ContinuousOn.mul ?_ h_deriv2_cont
      apply continuousOn_rpow_const_Icc (ha_pos := ha_pos)
    · exact h_deriv_cont.pow 3
    · intro t ht
      specialize h_deriv_ne_zero t ht
      exact pow_ne_zero 3 h_deriv_ne_zero
  have g_2_antitone : AntitoneOn (fun t ↦ |g_2 t|) (Set.Icc a b) := by
    set f : ℝ → ℝ := fun t ↦ t ^ (-s.re - 2) * |2 * π * ν - s.im / t| ^ (-3 : ℝ) with hf
    have hf_antitone : AntitoneOn f (Set.Icc a b) := by
      convert lemma_aachdecre s.re hsigma s.im ν hν a b ha 2 (by norm_num : 1 ≤ 2) using 1
      ext t
      simp only [hf]
      ring_nf
    have g2_eq_const_mul_f : ∀ t ∈ Set.Icc a b, |g_2 t| = |s.im| * (2 * π)^2 * f t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) ha) ht.1
      dsimp [g_2, f]
      rw [hφ_deriv t ht, hφ_deriv2 t ht]
      calc
        |t ^ (-s.re) * (s.im / (2 * π * t ^ 2)) / (ν - s.im / (2 * π * t)) ^ 3|
        = |t ^ (-s.re)| * (|s.im| / |2 * π * t ^ 2|) / |ν - s.im / (2 * π * t)| ^ 3 := by
          rw [abs_div, abs_mul, abs_pow, abs_div]
        _ = t ^ (-s.re) * (|s.im| / (2 * π * t ^ 2)) / (|2 * π * ν - s.im / t| / (2 * π)) ^ 3 := by
          rw [Real.abs_rpow_of_nonneg ht_pos.le, abs_of_pos (by positivity : 0 < 2 * π * t ^ 2)]
          rw [abs_of_pos ht_pos]
          congr 1; congr 1
          field_simp [Real.two_pi_pos.ne', ht_pos.ne']
          rw [abs_div]
          ring_nf; field_simp
          rw [abs_of_pos (by positivity : 0 < π * t * 2), abs_div, abs_of_pos ht_pos]
          field_simp [ht_pos.ne']
        _ = (t ^ (-s.re) * t ^ (-2 : ℝ) * |s.im| * (2 * π) ^ 2) * |2 * π * ν - s.im / t| ^ (-3 : ℝ) := by
          field_simp
          rw [div_eq_mul_inv, ← Real.rpow_natCast, Real.rpow_neg (abs_nonneg _)]
          simp only [Nat.cast_ofNat, rpow_ofNat, rpow_neg_ofNat, Int.reduceNeg, zpow_neg,
            mul_eq_mul_right_iff, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            pow_eq_zero_iff, abs_eq_zero, div_eq_zero_iff]
          left; field_simp [ht_pos.ne']
        _ = |s.im| * (2 * π) ^ 2 * (t ^ (-s.re - 2) * |2 * π * ν - s.im / t| ^ (-3 : ℝ)) := by
          rw [← Real.rpow_add ht_pos]
          ring_nf
    intro x hx y hy hxy
    simp_rw [g2_eq_const_mul_f x hx, g2_eq_const_mul_f y hy]
    exact mul_le_mul_of_nonneg_left (hf_antitone hx hy hxy) (by positivity)
  have g_2_integral_bound : ‖∫ t in Set.Icc a b, (t : ℂ) ^ (-s.re : ℂ) * (deriv (deriv φ) t) /
      (2 * π * I * (deriv φ t) ^ 2) * e (φ t)‖ ≤
    1 / (2 * π ^ 2) * (a ^ (-s.re - 1) * |ϑ| / |ν - ϑ| ^ 3) := by
    let h : ℝ → ℝ := fun t ↦ t ^ (-s.re) * deriv (deriv φ) t / (deriv φ t) ^ 2
    have hg_2_eq_h_div_deriv_φ : (∀ (t : ℝ), g_2 t = h t / deriv φ t) := by
      intro t
      dsimp [g_2, h]
      rw [div_div, ← pow_succ]
    have hmonophase := lemma_aachmonophase (a := a) (b := b) (φ := φ) (by simp [hb])
      (hcontdiffφ) (h_deriv_ne_zero) h g_2 hg_2_eq_h_div_deriv_φ g_2_cont g_2_antitone
    simp only [ofReal_div, h, g_2] at hmonophase
    have h_factor : ∫ t in Set.Icc a b, (t : ℂ) ^ (-s.re : ℂ) * (deriv (deriv φ) t) /
        (2 * π * I * (deriv φ t) ^ 2) * e (φ t) =
        ∫ t in Set.Icc a b, (1 / (2 * π * I)) * (↑(h t) * e (φ t)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp [h]
      simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg,
        Complex.ofReal_cpow (ha_pos.trans_le ht.1).le]
      field_simp [h_deriv_ne_zero t ht]
    rw [h_factor, integral_const_mul, norm_mul]
    have h_norm_const : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_I, mul_one]
      simp only [Complex.norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs, one_div, mul_inv_rev,
        mul_eq_mul_right_iff, inv_inj, abs_eq_self, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]; positivity
    rw [h_norm_const]
    calc
      1 / (2 * π) * ‖∫ t in Set.Icc a b, ↑(h t) * e (φ t)‖
      _ ≤ 1 / (2 * π) * (|g_2 a| / π) := by
        gcongr
        convert hmonophase using 1
        simp [h, ofReal_div, ofReal_mul]
      _ = 1 / (2 * π ^ 2) * |g_2 a| := by ring
      _ = 1 / (2 * π ^ 2) * (a ^ (-s.re - 1) * |ϑ| / |ν - ϑ| ^ 3) := by
        dsimp [g_2, ϑ]
        rw [hφ_deriv _ (left_mem_Icc.mpr hb.le), hφ_deriv2 _ (left_mem_Icc.mpr hb.le)]
        have : s.im / (2 * π * a ^ 2) = (s.im / (2 * π * a)) / a := by field_simp
        rw [this]
        simp only [abs_div, abs_mul, abs_pow, abs_of_pos ha_pos, ha_pos.le, Real.abs_rpow_of_nonneg]
        field_simp [Real.pi_pos.ne', ha_pos.ne', ϑ]
        rw [mul_assoc |s.im|, mul_comm a, ← Real.rpow_add_one ha_pos.ne']
        ring_nf
  let I1 := ∫ t in Set.Icc a b, (t ^ (-s.re - 1) : ℝ) / (2 * π * I * deriv φ t) * e (φ t)
  let I2 := ∫ t in Set.Icc a b, (t ^ (-s.re) : ℝ) * (deriv (deriv φ) t) /
      (2 * π * I * (deriv φ t) ^ 2) * e (φ t)
  abel_nf
  simp only [add_left_cancel_iff]
  refine ⟨(2 * π ^ 2 * a ^ (s.re + 1 : ℂ)) * (s.re * I1 + I2), ?_, ?_⟩
  · abel_nf
    field_simp [I1, I2]
    rw [Complex.ofReal_cpow ha_pos.le, ← Complex.cpow_add _ _ (ofReal_ne_zero.mpr ha_pos.ne')]
    ring_nf
    have : 1 + (s.re : ℂ) + ↑(-1 - s.re) = 0 := by push_cast; ring
    rw [this, Complex.cpow_zero]
    simp only [mul_one]
    congr 1
    · simp only [I1]; congr
      rw [show (fun t ↦ ν * t + s.im * π⁻¹ * Real.log t * (-1 / 2)) = φ by ext; dsimp [φ]; ring]
      ext x; ring_nf; -- simp
      simp only [mul_assoc]
      congr 1
      rw [show (ν * x + s.im * (Real.log x * (π⁻¹ * (-1 / 2))) = φ x) by dsimp [φ]; ring]
      ring
    · rw [one_mul]; congr 1; ext t
      simp only [div_eq_mul_inv, pow_two, mul_inv]
      rw [mul_comm, mul_assoc, mul_left_comm]
      ring_nf
      have h_fun : (fun t ↦ ν * t + s.im * π⁻¹ * Real.log t * (-1 / 2)) = φ := by
        ext x; simp only [φ, div_eq_mul_inv]; ring
      simp only [h_fun]; field_simp
      congr; unfold φ; field_simp; ring
  · calc
    ‖2 * ↑π ^ 2 * (a : ℂ) ^ ((s.re : ℂ) + 1) * (↑s.re * I1 + I2)‖
      = (2 * π ^ 2 * a ^ (s.re + 1)) * ‖↑s.re * I1 + I2‖ := by
        rw [norm_mul]
        congr
        simp only [Complex.norm_mul, Complex.norm_ofNat, norm_pow, norm_real, norm_eq_abs, sq_abs,
          mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true,
          pow_eq_zero_iff, pi_ne_zero, or_self, or_false]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ha_pos]
        simp
    _ ≤ (2 * π ^ 2 * a ^ (s.re + 1)) * (s.re * ‖I1‖ + ‖I2‖) := by
      field_simp
      refine (norm_add_le _ _).trans ?_
      simp [abs_of_nonneg hsigma]
    _ ≤ (2 * π ^ 2 * a ^ (s.re + 1)) * (s.re * (1 / (2 * π ^ 2) * (a ^ (-s.re - 1) / |ν - ϑ| ^ 2))
          + (1 / (2 * π ^ 2) * (a ^ (-s.re - 1) * |ϑ| / |ν - ϑ| ^ 3))) := by
      gcongr
      · convert g_1_integral_bound using 2
        refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [Complex.ofReal_cpow (by linarith [ht.1, ha_pos]), Complex.ofReal_sub, Complex.ofReal_one]
        ring_nf; simp only [Complex.ofReal_neg]; ring_nf
      · convert g_2_integral_bound using 2
        refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [Complex.ofReal_cpow (by linarith [ht.1, ha_pos])]
        ring_nf; simp only [Complex.ofReal_neg]; ring
    _ = s.re / |ν - ϑ| ^ 2 + |ϑ| / |ν - ϑ| ^ 3 := by
      field_simp [Real.pi_pos.ne', ha_pos.ne']
      rw [← Real.rpow_add ha_pos]; ring_nf; rw [Real.rpow_zero]; ring
    _ = s.re / |ν + -1 • ϑ| ^ 2 + |ϑ| / |ν + -1 • ϑ| ^ 3 := by
      simp only [sq_abs, Int.reduceNeg, neg_smul, one_smul]; ring_nf

def _root_.Real.IsHalfInteger (x : ℝ) : Prop := ∃ k : ℤ, x = k + 1 / 2

lemma _root_.Real.IsHalfInteger.not_isInteger {x : ℝ} (h : x.IsHalfInteger) : ¬∃ n : ℤ, x = ↑n := by
  obtain ⟨k, hk⟩ := h
  rintro ⟨n, hn⟩
  have : (n : ℝ) = k + 1 / 2 := by linarith [hk, hn]
  have hzz : ((n - k : ℤ) : ℝ) = 1 / 2 := by push_cast; linarith
  have hzz2 : 2 * ((n - k : ℤ) : ℝ) = 1 := by linarith
  have hzz3 : (2 * (n - k) : ℤ) = 1 := by exact_mod_cast hzz2
  omega

lemma _root_.Real.IsHalfInteger.floor_add_three_halfs (M : ℝ) : (↑⌊M⌋ + 3 / 2 : ℝ).IsHalfInteger :=
  ⟨⌊M⌋ + 1, by push_cast; ring⟩

lemma _root_.Real.floor_add_three_halfs_gt (M : ℝ) : M < ↑⌊M⌋ + 3 / 2 := by
  linarith [Int.lt_floor_add_one M]


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
    ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
      fun x hx ↦ Or.inl (by norm_cast; linarith [hx.1, h_pos_a])
  have h_integral : ∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * (Real.cos (2 * Real.pi * n * t)) =
      (1 / 2) * (∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * e (n * t)) +
        (1 / 2) * (∫ t in Set.Icc a b, (t : ℂ) ^ (-s) * e (-n * t)) := by
    rw [← mul_add, ← integral_add]
    · rw [← integral_const_mul]
      congr with t
      norm_num [e, Complex.cos]
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
  "lem:abadeulmac'"
  (title := "Identity for a partial sum of zeta(s) for integer b")
  (statement := /--
Let $b>0$, $b\in \mathbb{Z}$.
Then, for all $s\in \mathbb{C}\setminus \{1\}$ with $\Re s > 0$,
\begin{equation}\label{eq:abak1'}
  \sum_{n \leq b} \frac{1}{n^s} = \zeta(s) + \frac{b^{1-s}}{1-s} + \frac{b^{-s}}{2}
  + s \int_b^\infty \left(\{y\}-\frac{1}{2}\right) \frac{dy}{y^{s+1}}.
\end{equation}
-/)
  (proof := /--
Assume first that $\Re s > 1$. By first-order Euler-Maclaurin,
\[\sum_{n > b}\frac{1}{n^s} = \int_b^\infty \frac{dy}{y^s} + \int_b^\infty
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
theorem lemma_abadeulmac' {b : ℕ} (hb : 0 < b) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) =
      riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) + (b ^ (-s) : ℂ) / (2) +
      s * ∫ y in Set.Ioi (b : ℝ), (Int.fract y - 1 / 2) * ((y : ℂ) ^ (-(s + 1))) := by
  rw [← Zeta0EqZeta hb (by linarith) hs1]
  unfold riemannZeta0
  rw [show ∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) = (∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s)) + 0 by ring]
  rw [show ∑ n ∈ range (b + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) by
    rw [range_eq_Ico]
    rw [sum_eq_sum_Ico_succ_bot (by linarith)]
    norm_cast
    rw [zero_cpow (by aesop)]
    simp only [div_zero, zero_add, one_div]
    rw [← Finset.Ico_succ_right_eq_Icc]
    congr
    ext x
    rw [cpow_neg]]
  rw [show (∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) + -(b : ℂ) ^ (1 - s) / (1 - s) + -(b : ℂ) ^ (-s) / 2 +
          s * ∫ (x : ℝ) in Set.Ioi ↑b, (⌊x⌋ + 1 / 2 - x : ℂ) / (x : ℂ) ^ (s + 1)) +
        (b : ℂ) ^ (1 - s) / (1 - s) +
      (b : ℂ) ^ (-s) / 2 +
    s * ∫ (y : ℝ) in Set.Ioi ↑b, ((Int.fract y) - 1 / 2) * (y : ℂ) ^ (-(s + 1)) =
      ∑ n ∈ Icc 1 b, (n : ℂ) ^ (-s) + (
          s * (∫ (x : ℝ) in Set.Ioi ↑b, (⌊x⌋ + 1 / 2 - x : ℂ) / (x : ℂ) ^ (s + 1))   +
    s * ∫ (y : ℝ) in Set.Ioi ↑b, ((Int.fract y) - 1 / 2) * (y : ℂ) ^ (-(s + 1))) by ring]
  congr! 1
  suffices h : ∫ (x : ℝ) in Set.Ioi ↑b, (⌊x⌋ + 1 / 2 - x : ℂ) / ↑x ^ (s + 1) =
             -∫ (y : ℝ) in Set.Ioi ↑b, ((Int.fract y) - 1 / 2 : ℂ) * ↑y ^ (-(s + 1)) by
    rw [h]; ring
  rw [← MeasureTheory.integral_neg]
  congr 1
  ext x
  unfold Int.fract
  rw [show (x : ℂ) ^ (-(s + 1)) = 1 / (↑x : ℂ) ^ (s + 1) by
    rw [cpow_neg, one_div]]
  rw [mul_one_div, ← neg_div]
  congr
  ring_nf
  push_cast
  ring_nf


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
    ∑ n ∈ Icc 1 ⌊b⌋₊, (n : ℂ) ^ (-s) =
      riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) +
      s * ∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1))) := by
  have := @lemma_abadeulmac'
  obtain ⟨k, rfl⟩:=hb'
  lift k to@ℕ using Int.le_of_lt_add_one (mod_cast (by linear_combination hb:0<(k: ℝ) + 1))
  specialize this k.succ_pos hs1 hsigma
  norm_num[k.floor_eq_iff (hb.le.trans ↑ _)|>.mpr, sum_Icc_succ_top]at*
  conv =>
    enter [2, 2, 2, 1, 2, 1]
    equals (1 : ℝ) / 2 + k => ring_nf
  rw [←Set.Ioc_union_Ioi_eq_Ioi (add_le_add_left one_half_lt_one.le _),MeasureTheory.integral_union_ae]
  · conv =>
      enter [2, 2, 2, 1, 1, 2, 1]
      equals (k : ℝ) + 1/2 => ring_nf
    conv =>
      enter [2, 2, 2, 1, 1, 2, 2]
      equals (k : ℝ) + 1 => ring_nf
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.setIntegral_congr_fun (g := fun x : ℝ => (x - k - 1/2 : ℂ) * x ^ (-1 + -s)) measurableSet_Ioo]
    · rw[MeasureTheory.setIntegral_congr_fun (g:=fun x:ℝ=>(x : ℂ)^(-s)-k*x^(-1+-s)-1/2*x^(-1+-s)) (measurableSet_Ioo),←MeasureTheory.integral_Ioc_eq_integral_Ioo]
      · norm_num[*,←intervalIntegral.integral_of_le _,integral_cpow _,intervalIntegral.intervalIntegrable_cpow]
        rw [integral_cpow]
        · norm_num
          linear_combination(norm:=ring_nf)this-div_self (s.ne_zero_of_re_pos hsigma)*((k + 1)^(-s)-(k+1/2)^(-s))
          norm_num[add_comm (1/2 : ℂ),mul_assoc, sub_eq_neg_add, add_assoc,mul_comm s,s.ne_zero_of_re_pos hsigma,cpow_add,(mod_cast _: (1: ℂ)+k≠0),hb.ne']
          norm_num[*, add_assoc,←one_add_mul,←mul_assoc,mul_comm (k+1 : ℂ),neg_add_eq_zero.eq,cpow_add,ne_of_gt]
          exact (.symm (.trans (by rw [cpow_add _ _ (by ·norm_num [Complex.ext_iff, hb.ne']),cpow_one]) ↑(add_eq_of_eq_sub' ↑(add_eq_of_eq_sub' ↑(add_eq_of_eq_sub' ↑(add_eq_of_eq_sub' (by·grind)))))))
        · use .inr ⟨sub_eq_self.not.2 fun and=>by simp_all,((lt_min hb k.cast_add_one_pos).not_ge ·.1)⟩
      · use fun A B=>by norm_num[sub_mul,mul_comm (A : ℂ), (hb.trans B.1).ne',cpow_add,cpow_neg]
    · use fun and p=>by zify[Int.fract,Int.floor_eq_iff.2 (p.imp_left (by linear_combination·)),Int.cast_natCast]
  · norm_num[MeasureTheory.AEDisjoint]
  · norm_num
  · conv =>
      enter [2, 1]
      equals (k : ℝ) + 1/2 => ring_nf
    conv =>
      enter [2, 2]
      equals (k : ℝ) + 1 => ring_nf
    rw[integrableOn_Ioc_iff_integrableOn_Ioo,MeasureTheory.integrableOn_congr_fun (fun A B=>by rw [Int.fract,Int.floor_eq_iff.2 (B.imp_left (by linear_combination·))]) measurableSet_Ioo]
    exact (ContinuousOn.mul (by fun_prop) (.cpow_const (by fun_prop) fun and c=>.inl (hb.trans_le c.1))).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  · apply(integrableOn_Ioi_rpow_of_lt (by norm_num[*]:-1+-s.1< _) (by bound)).norm.mono' ((measurable_fract.complex_ofReal.sub_const _).mul (by fun_prop)).aestronglyMeasurable
    filter_upwards[MeasureTheory.ae_restrict_mem (by norm_num)] with S(F: S> _)
    have := k.cast_add_one_pos (α := ℝ)
    conv at this =>
      enter [2]
      equals (1 : ℝ) + k => ring_nf

    norm_num[abs_of_pos, S.rpow_pos_of_pos, (F.trans' this).le, norm_cpow_eq_rpow_re_of_nonneg, ne_of_gt,(norm_sub_le _ _).trans ∘le_of_lt]
    rw [norm_cpow_eq_rpow_re_of_nonneg]
    conv =>
      enter [1, 2, 2]
      equals (-1 : ℝ) + -s.re => simp
    · rw [abs_of_pos]
      · conv =>
          enter [2]
          equals (1 : ℝ) * S ^ (-1 + -s.re) => ring_nf
        gcongr
        · apply (S.rpow_pos_of_pos (by linarith) _).le

        exact (congr_arg _ (by zify)).trans_le ((norm_real (Int.fract S-1/2)).le.trans (max_le (by linear_combination Int.fract_lt_one S) (by linear_combination Int.fract_nonneg S)))
      · apply (S.rpow_pos_of_pos (by linarith) _)
    · linarith
    · simp only [add_re, neg_re, one_re, ne_eq]
      linarith

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
theorem lemma_abadtoabsum {a b : ℝ} (ha : 0 < a) (hb' : b.IsHalfInteger) (hab : b > a) {s : ℂ}
    (hs1 : s ≠ 1) (hsigma : 0 < s.re) :
    ∃ E, ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) = -∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
      (n : ℂ) ^ (-s) + riemannZeta s + (b ^ (1 - s) : ℂ) / (1 - s) + E ∧
      ‖E‖ ≤ ‖s‖ / (2 * s.re * (b ^ s.re : ℝ)) := by
  have hb_pos : 0 < b := ha.trans hab
  have hmac := lemma_abadeulmac hb_pos hb' hs1 hsigma
  let E := s * ∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))
  refine ⟨E, ?_, ?_⟩
  · have hfinset : (Icc 1 ⌊b⌋₊ : Finset ℕ) = Finset.Icc 1 ⌊a⌋₊ ∪ Ioc ⌊a⌋₊ ⌊b⌋₊ := by
      ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      refine ⟨fun ⟨h1, hn⟩ ↦ ?_, fun h ↦ ?_⟩
      · by_cases hn' : n ≤ ⌊a⌋₊
        · exact Or.inl ⟨h1, hn'⟩
        · exact Or.inr ⟨Nat.lt_of_not_le hn', hn⟩
      · rcases h with ⟨h1, hn⟩ | ⟨hn1, hn2⟩
        · exact ⟨h1, hn.trans <| Nat.floor_mono hab.le⟩
        · exact ⟨by omega, hn2⟩
    have hdisjoint : Disjoint (Finset.Icc 1 ⌊a⌋₊) (Ioc ⌊a⌋₊ ⌊b⌋₊) :=
      disjoint_left.mpr fun x hx₁ hx₂ ↦ by simp only [Finset.mem_Icc] at hx₁; simp only [Finset.mem_Ioc] at hx₂; omega
    rw [hfinset, sum_union hdisjoint] at hmac
    linear_combination' hmac
  · have h_integral_bound : ‖∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ ≤
        (1 / 2) * (1 / (s.re * b ^ s.re)) := by
      have hstep1 : ‖∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ ≤
          ∫ y in Set.Ioi b, ‖(Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ :=
        norm_integral_le_integral_norm _
      have : ∫ y in Set.Ioi b, ‖(Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ ≤
          ∫ y in Set.Ioi b, (1 / 2 : ℝ) * (y : ℝ) ^ (-(s.re + 1)) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
          ((integrableOn_Ioi_rpow_of_lt (by linarith) hb_pos).const_mul _) _
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos (hb_pos.trans hy), neg_add_rev, add_re,
          neg_re, one_re]
        apply mul_le_mul_of_nonneg_right _ (rpow_nonneg (hb_pos.trans hy).le _)
        rw [norm_sub_rev]
        have hfract_bound : ‖(1 / 2 : ℂ) - ↑(Int.fract y)‖ ≤ 1 / 2 := by
          have : (1 / 2 : ℂ) - ↑(Int.fract y) = ↑((1 / 2 : ℝ) - (Int.fract y : ℝ)) := by
            simp only [ofReal_sub, ofReal_div, ofReal_one, ofReal_ofNat]
          rw [this, norm_real, norm_eq_abs, abs_le]
          constructor <;> linarith [Int.fract_nonneg y, Int.fract_lt_one y]
        exact hfract_bound
      have : ∫ y in Set.Ioi b, (1 / 2 : ℝ) * (y : ℝ) ^ (-(s.re + 1)) =
          (1 / 2) * (1 / (s.re * b ^ s.re)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) hb_pos]
        have : -(s.re + 1) + 1 = -s.re := by ring
        have : b ^ (-s.re) = (b ^ s.re)⁻¹ := rpow_neg hb_pos.le s.re
        aesop
      linarith
    calc ‖E‖ = ‖s‖ * ‖∫ y in Set.Ioi b, (Int.fract y - 1 / 2 : ℂ) * ((y : ℂ) ^ (-(s + 1)))‖ := by simp only [E, norm_mul]
      _ ≤ ‖s‖ * ((1 / 2) * (1 / (s.re * b ^ s.re))) := mul_le_mul_of_nonneg_left h_integral_bound (norm_nonneg _)
      _ = ‖s‖ / (2 * s.re * b ^ s.re) := by ring

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
      (fun (N : ℕ) ↦ ∑ n ∈ Icc 1 N,
        (FourierTransform.fourier f n + FourierTransform.fourier f (-n))) (nhds L) ∧
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) =
        ((b ^ (1 - s) : ℂ) - (a ^ (1 - s) : ℂ)) / (1 - s) + L := by
  sorry

lemma trig (z : ℂ) : tan z = - cot (z + π / 2) := by
  simp [Complex.tan, Complex.cot, Complex.cos_add_pi_div_two, neg_div', Complex.sin_add_pi_div_two]

lemma sin_ne_zero {z : ℂ} (hz : ¬∃ (n : ℤ), n * π / 2 = z) : sin z ≠ 0 :=
  Complex.sin_ne_zero_iff.2 fun k h ↦ hz ⟨2 * k, by grind⟩

lemma cos_ne_zero {z : ℂ} (hz : ¬∃ (n : ℤ), n * π / 2 = z) : cos z ≠ 0 :=
  Complex.cos_ne_zero_iff.2 fun k h ↦ hz ⟨2 * k + 1, by grind⟩

lemma trig' {z : ℂ} (hz : ¬∃ (n : ℤ), n * π / 2 = z) : cot z + tan z = 2 / sin (2 * z) := by
  simp [Complex.tan, Complex.cot, div_add_div (cos z) (sin z) (sin_ne_zero hz) (cos_ne_zero hz),
    ← pow_two, Complex.cos_sq_add_sin_sq, Complex.sin_two_mul]
  field_simp

lemma trig'' {z : ℂ} (hz : ¬∃ (n : ℤ), n * π / 2 = z) :
    cot z - cot (z + π / 2) = 2 / sin (2 * z) := by
  simp [sub_eq_neg_add, ← trig, ← trig' hz, add_comm]

lemma hsummable {z : ℂ} (hz : z ∈ integerComplement) :
    Summable fun n : ℕ+ ↦ 1 / (z - 2 * n) + 1 / (z + 2 * n) := by
  have he (n : ℕ+) := cotTerm_identity hz (2 * n - 1)
  have hi : (fun n : ℕ+ ↦ (2 * n : ℤ)).Injective := fun _ _ _ ↦ by simp_all
  have := mul_left (2 * z)
    ((EisensteinSeries.summable_linear_sub_mul_linear_add z 1 1).comp_injective hi)
  simp_all [cotTerm, mul_comm (z + _)⁻¹]

lemma asummable {z : ℂ} (hz : z ∈ integerComplement) :
    Summable fun n : ℕ+ ↦ (-1) ^ (2 * n : ℕ) * (1 / (z - 2 * n) + 1 / (z + 2 * n)) := by
  convert hsummable hz using 2
  simp

lemma hsummable' {z : ℂ} (hz : z ∈ integerComplement) :
    Summable fun n : ℕ+ ↦ 1 / (z + 1 - 2 * n) + 1 / (z + 1 + 2 * n) := by
  have : z + 1 ∈ integerComplement := by
    simp_all only [integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
    refine fun n hn ↦ hz (n - 1) ?_
    grind
  exact hsummable this

lemma hsummable'' {z : ℂ} (hz : z ∈ integerComplement) :
    Summable fun n : ℕ+ ↦ 1 / (z - (2 * n - 1)) + 1 / (z + (2 * n - 1)) := by
  have he (n : ℕ+) := cotTerm_identity hz (2 * n - 2)
  have hi : (fun n : ℕ+ ↦ (2 * n - 1 : ℤ)).Injective := fun _ _ _ ↦ by simp_all
  have := mul_left (2 * z)
    ((EisensteinSeries.summable_linear_sub_mul_linear_add z 1 1).comp_injective hi)
  have (n : ℕ+) : ((2 * n - 2 : ℕ) : ℂ) + 1 = ((2 * n : ℕ) : ℂ) - 1 := by
    norm_cast
    rw [Nat.cast_add, Int.subNatNat_eq_coe, Nat.cast_sub] <;> push_cast <;> linarith [n.pos]
  simp_all [cotTerm, mul_comm (z + _)⁻¹]

lemma neg_one_pow (n : ℕ+) : (-1 : ℂ) ^ (2 * n - 1 : ℕ) = -1 := (neg_one_pow_eq_neg_one_iff_odd
  (by grind)).2 ⟨n - 1, by cases n using PNat.recOn <;> norm_num; linarith⟩

lemma asummable'' {z : ℂ} (hz : z ∈ integerComplement) :
    Summable fun n : ℕ+ ↦ (-1) ^ (2 * n - 1 : ℕ) *
    (1 / (z - (2 * n - 1)) + 1 / (z + (2 * n - 1))) := by
  convert mul_left (-1) (hsummable'' hz) using 1
  simp [neg_one_pow]

lemma telescoping_sum (z : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 / (z + (2 * (k + 1 : ℕ) - 1)) - 1 / (z + (2 * (k + 1 : ℕ) + 1))) =
    1 / (z + 1) - 1 / (z + (2 * n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring_nf; grind

theorem tsum_even_add_odd' {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [T2Space M] [ContinuousAdd M] {f : ℕ+ → M}
    (he : Summable fun (k : ℕ+) ↦ f (2 * k))
    (ho : Summable fun (k : ℕ+) ↦ f (2 * k - 1)) :
    ∑' (k : ℕ+), f (2 * k - 1) + ∑' (k : ℕ+), f (2 * k) = ∑' (k : ℕ+), f k := by
  symm
  rw [← Equiv.tsum_eq (Equiv.pnatEquivNat.symm), ← tsum_even_add_odd,
    ← Equiv.tsum_eq (Equiv.pnatEquivNat.symm), ← Equiv.tsum_eq (Equiv.pnatEquivNat.symm)]
  · congr
  · simpa [← Equiv.summable_iff (Equiv.pnatEquivNat.symm)] using ho
  · simpa [← Equiv.summable_iff (Equiv.pnatEquivNat.symm)] using he

blueprint_comment /--
We could prove these equations starting from Euler's product for $\sin \pi z$.
-/

@[blueprint
  "lem:abadeulmit1"
  (title := "Euler/Mittag-Leffler expansion for cosec")
  (statement := /--
Let $z\in \mathbb{C}$, $z\notin \mathbb{Z}$. Then
\[\frac{\pi}{\sin \pi z} = \frac{1}{z} +
 \sum_{n > 0} (-1)^n\left(\frac{1}{z - n} + \frac{1}{z + n}\right).
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
    (π / sin (π * z)) =
    (1 / z) + ∑' (n : ℕ+), (-1) ^ (n : ℕ) * ((1 / (z - n) : ℂ) + (1 / (z + n) : ℂ)) := calc
  _ = (1 / 2) * π * 2 / sin (π * z) := by field_simp
  _ = (1 / 2) * (π * cot (π * z / 2)) - (1 / 2) * (π * cot (π * (z + 1) / 2)) := by
    have : π * z / 2 + π / 2 = π * (z + 1) / 2 := by grind
    have := this ▸ trig'' (z := π * z / 2) ?_
    · by_contra!
      obtain ⟨n, hn⟩ := this
      have := mul_right_cancel₀ (by exact_mod_cast pi_ne_zero)
        ((mul_comm (π : ℂ) z) ▸ ((div_left_inj' (by grind)).1 hn))
      simp_all [integerComplement]
    · rw [mul_div_assoc, ← mul_sub, ← mul_sub, mul_assoc, this]; field_simp
  _ = (1 / 2) * (1 / (z / 2) + ∑' n : ℕ+, (1 / (z / 2 - n) + 1 / (z / 2 + n))) -
      (1 / 2) * (1 / ((z + 1) / 2) + ∑' n : ℕ+, (1 / ((z + 1) / 2 - n)
      + 1 / ((z + 1) / 2 + n))) := by
      congr
      · have : z / 2 ∈ integerComplement := by
          simp_all only [integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
          refine fun n hn ↦ hz (2 * n) ?_
          grind
        simpa [mul_div_assoc] using cot_series_rep this
      · have : (z + 1) / 2 ∈ integerComplement := by
          simp_all only [integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
          refine fun n hn ↦ hz (2 * n - 1) ?_
          grind
        simpa [mul_div_assoc] using cot_series_rep this
  _ = 1 / z + ∑' n : ℕ+, (1 / (z - 2 * n) + 1 / (z + 2 * n)) -
      (1 / (z + 1) + ∑' n : ℕ+, (1 / (z + 1 - 2 * n) + 1 / (z + 1 + 2 * n))) := by
      field_simp
      rw [mul_sub, mul_add, mul_add, ← div_eq_mul_one_div, ← div_eq_mul_one_div,
        Summable.tsum_mul_left 2 (hsummable hz), Summable.tsum_mul_left 2 (hsummable' hz)]
  _ = 1 / z + ∑' n : ℕ+, (1 / (z - 2 * n) + 1 / (z + 2 * n)) -
      ∑' n : ℕ+, (1 / (z - (2 * n - 1)) + 1 / (z + (2 * n - 1))) := by
      congr
      refine Eq.symm (sub_eq_iff_eq_add.1 ?_)
      rw [← Summable.tsum_sub ?_ (hsummable' hz)]
      · simp only [sub_sub_eq_add_sub, add_sub_add_left_eq_sub, tsum_pnat_eq_tsum_succ
          (f := fun b ↦ (1 / (z + (2 * b - 1)) - 1 / (z + (2 * b + 1)))), add_assoc z 1,
          add_comm (1 : ℂ)]
        refine HasSum.tsum_eq ((Summable.hasSum_iff_tendsto_nat ?_).2 ?_)
        · suffices Summable (fun n : ℤ ↦ 2 * ((z + n + 1) * (z + n + 3))⁻¹) by
            have hi : (fun n : ℕ ↦ (2 * n : ℤ)).Injective := fun _ _ _ ↦ by simp_all
            have := this.comp_injective hi
            convert this using 2 with n
            rw [one_div, one_div, inv_sub_inv]
            · simp; field_simp; ring
            · simp_all only [integerComplement, mem_compl_iff, Set.mem_range, not_exists,
                ne_eq, add_eq_zero_iff_eq_neg]
              exact fun h ↦ hz (-(2 * (n + 1) - 1)) (by simp_all)
            · simp_all only [integerComplement, mem_compl_iff, Set.mem_range, not_exists,
                ne_eq, add_eq_zero_iff_eq_neg]
              exact fun h ↦ hz (-(2 * (n + 1) + 1)) (by simp_all)
          refine Summable.mul_left 2 ?_
          apply EisensteinSeries.summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
          simpa [pow_two] using (EisensteinSeries.linear_inv_isBigO_right_add 1 3 z).mul
            (EisensteinSeries.linear_inv_isBigO_right_add 1 1 z)
        · refine (Filter.tendsto_congr (telescoping_sum z)).2 ?_
          nth_rw 2 [← sub_zero (1 / (z + 1))]
          simpa [add_comm _ (1 : ℂ), ← add_assoc, one_mul, - one_div, Function.comp_def] using
            ((EisensteinSeries.tendsto_zero_inv_linear (1 + z) 1).comp
            (tendsto_id.const_mul_atTop' (by linarith))).const_sub (1 / (z + 1))
      · exact hsummable'' hz
  _ = 1 / z + ∑' n : ℕ+, (-1) ^ (2 * n : ℕ) * (1 / (z - 2 * n) + 1 / (z + 2 * n)) +
      ∑' n : ℕ+, (-1) * (1 / (z - (2 * n - 1)) + 1 / (z + (2 * n - 1))) := by
      rw [Summable.tsum_mul_left (-1), neg_one_mul, ← sub_eq_add_neg]
      · congr; ext ; simp
      · exact hsummable'' hz
  _ = 1 / z + ∑' n : ℕ+, (-1) ^ (2 * n : ℕ) * (1 / (z - 2 * n) + 1 / (z + 2 * n)) +
      ∑' n : ℕ+, (-1) ^ (2 * n - 1 : ℕ) * (1 / (z - (2 * n - 1)) + 1 / (z + (2 * n - 1))) := by
      congr; simp [neg_one_pow]
  _ = (1 / z) + ∑' (n : ℕ+), (-1) ^ (n : ℕ) * ((1 / (z - n) : ℂ) + (1 / (z + n) : ℂ)) := by
      have hn (n : ℕ+) : ((2 * n - 1 : ℕ+) : ℕ) = 2 * n - 1 := by
        have : 1 < 2 * n := Nat.le_trans (by norm_num) (Nat.mul_le_mul_left 2 n.2)
        simp [PNat.sub_coe, this]
      rw [add_assoc, ← tsum_even_add_odd' (f := fun n ↦ (-1) ^ (n : ℕ) * ((1 / (z - n) : ℂ)
        + (1 / (z + n) : ℂ))), add_comm (∑' (k : ℕ+), (-1) ^ ((2 * k - 1 : ℕ+) : ℕ) * _) _]
      · congr <;> aesop
      · simpa using asummable hz
      · convert asummable'' hz <;> aesop

lemma lemma_abadeulmit2_integral_tsum_inv_sub_int_sq {z w : ℂ}
  (_hz : z ∈ integerComplement)
  (hw : w ∈ integerComplement)
  (h_path : ∀ t : ℝ, t ∈ Set.Icc 0 1 → w + ↑t * (z - w) ∉ range (fun n : ℤ => (n : ℂ))) :
  (z - w) * ∫ (t : ℝ) in 0..1, ∑' (n : ℤ), 1 / (w + ↑t * (z - w) - ↑n) ^ 2 =
  ∑' (n : ℤ), (1 / (w - ↑n) - 1 / (z - ↑n)) := by
  let path : ℝ → ℂ := fun t => w + (t : ℂ) * (z - w)
  let g : ℤ → ℝ → ℂ := fun n t => 1 / (path t - (n : ℂ)) ^ 2
  have h_cont_path : ContinuousOn path (Set.Icc 0 1) := by fun_prop
  have h_bound_path : Bornology.IsBounded (path '' Set.Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn h_cont_path).isBounded
  obtain ⟨M, hM⟩ := h_bound_path.exists_norm_le
  have h_integrable (n : ℤ) : IntervalIntegrable (g n) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    apply ContinuousOn.div
    · fun_prop
    · apply ContinuousOn.pow
      apply ContinuousOn.sub
      · exact h_cont_path
      · apply continuousOn_const
    · intro t ht
      apply pow_ne_zero
      rw [sub_ne_zero]
      intro h_eq
      exact h_path t ht ⟨n, h_eq.symm⟩
  have h_summable : Summable (fun n ↦ ∫ t in Set.Ioc 0 1, ‖g n t‖) := by
    simp_rw [g, norm_div, norm_one, norm_pow]
    let C := 2 * M
    have h_le : ∀ (n : ℤ), ‖n‖ > C → ∀ t ∈ Set.Icc 0 1, ‖(n : ℂ) - path t‖⁻¹ ^ 2 ≤ 4 / ‖n‖ ^ 2 := by
      intro n hn t ht
      have h_path_t : ‖path t‖ ≤ M := hM (path t) (Set.mem_image_of_mem path ht)
      have h_dist : ‖n‖ - M ≤ ‖(n : ℂ) - path t‖ := by
        calc ‖(n : ℂ) - path t‖ ≥ ‖(n : ℂ)‖ - ‖path t‖ := norm_sub_norm_le ..
          _ = (‖n‖ : ℝ) - ‖path t‖ := by
            rw [norm_intCast, Int.norm_eq_abs]
          _ ≥ ‖n‖ - M := by gcongr
      have h_dist_pos : 0 < ‖n‖ - M := by dsimp [C] at hn; linarith [norm_nonneg (path t)]
      rw [inv_eq_one_div, one_div_pow]
      rw [show 4 / ‖n‖ ^ 2 = 1 / (‖n‖ ^ 2 / 4) by
        field_simp]
      apply div_le_div₀ (by norm_num) (by norm_num)
      · apply div_pos (pow_pos (by dsimp [C] at hn; linarith [norm_nonneg (path t)]) 2) (by norm_num)
      · rw [show ‖n‖ ^ 2 / 4 = (‖n‖ / 2) ^ 2 by field_simp; ring]
        apply pow_le_pow_left₀ (by apply div_nonneg (norm_nonneg _) (by norm_num))
        calc ‖n‖ / 2 = ‖n‖ - ‖n‖ / 2 := by ring
          _ ≤ ‖n‖ - M := by dsimp [C] at hn; linarith [norm_nonneg (path t)]
          _ ≤ ‖(n : ℂ) - path t‖ := h_dist
    apply Summable.of_norm_bounded_eventually (g := fun n : ℤ ↦ 4 / ‖n‖ ^ 2)
    · apply Summable.mul_left
      simp only [Int.norm_eq_abs, sq_abs]
      simpa only [one_div] using (summable_one_div_int_pow (p := 2)).mpr one_lt_two
    · rw [Filter.eventually_cofinite]
      let S : Set ℤ := {n | ‖n‖ ≤ C}
      have hS : S.Finite := by
        have h_sub : S ⊆ Set.Icc (-⌈C⌉ - 1) (⌈C⌉ + 1) := by
          intro n hn
          dsimp [S] at hn
          rw [← dist_zero_right, ← Metric.mem_closedBall] at hn
          rw [Int.closedBall_eq_Icc] at hn
          rw [Set.mem_Icc] at hn ⊢
          simp only [Int.cast_zero, zero_sub, zero_add] at hn
          constructor
          · trans ⌈-C⌉
            · rw [Int.ceil_neg]
              linarith [Int.floor_le_ceil C]
            · exact hn.1
          · trans ⌊C⌋
            · exact hn.2
            · linarith [Int.floor_le_ceil C]
        exact (Set.finite_Icc _ _).subset h_sub
      apply hS.subset
      intro n hn
      rw [Set.mem_setOf_eq] at hn
      by_contra h_n_not_le
      dsimp [S] at h_n_not_le
      rw [not_le] at h_n_not_le
      have h_n_large : ‖n‖ > C := h_n_not_le
      have h_int : ‖∫ (t : ℝ) in Set.Ioc 0 1, g n t‖ ≤ ∫ (t : ℝ) in Set.Ioc 0 1, ‖g n t‖ :=
        norm_integral_le_integral_norm _
      have hn_bound : ∫ (t : ℝ) in Set.Ioc 0 1, ‖g n t‖ ≤ 4 / ‖n‖ ^ 2 := by
        have h_int_const : ∫ (t : ℝ) in Set.Ioc 0 1, (4 / ‖n‖ ^ 2) = 4 / ‖n‖ ^ 2 := by
           simp
        rw [← h_int_const]
        apply MeasureTheory.integral_mono_ae
        · exact ((h_integrable n).1).norm
        · apply MeasureTheory.integrableOn_const
          · exact ne_of_lt measure_Ioc_lt_top
          · simp
        · simp only [measurableSet_Ioc, ae_restrict_eq, one_div, norm_inv, norm_pow, g, path]
          refine Filter.eventually_inf_principal.mpr ?_
          filter_upwards with x
          intro hx
          have hx_Icc : x ∈ Set.Icc 0 1 := ⟨le_of_lt hx.1, hx.2⟩
          specialize h_le n h_n_large x hx_Icc
          simp only [path] at h_le
          rw [norm_sub_rev]
          rw [← inv_pow]
          exact h_le
      apply hn
      refine le_trans ?_ hn_bound
      simp only [g, one_div]
      refine le_of_eq ?_
      simp_rw [norm_inv, norm_pow]
      rw [Real.norm_of_nonneg (by positivity)]
  rw [intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1)]
  rw [MeasureTheory.integral_tsum]
  · rw [← tsum_mul_left]
    congr 1
    ext n
    rw [← intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1)]
    rw [← intervalIntegral.integral_const_mul (z - w)]
    let F (t : ℝ) := -1 / (path t - n)
    have h_deriv : ∀ t ∈ Set.uIcc 0 1, HasDerivAt F ((z - w) * g n t) t := by
      rw [Set.uIcc_of_le (zero_le_one : (0:ℝ)≤1)]
      intro t ht
      dsimp [F, g, path]
      have h_denom_ne_zero : path t - (n : ℂ) ≠ 0 := by
        rw [sub_ne_zero]
        intro h_eq
        exact h_path t ht ⟨n, h_eq.symm⟩
      have h_d_path : HasDerivAt path (z - w) t := by
        dsimp [path]
        apply HasDerivAt.const_add
        convert (hasDerivAt_ofReal t).mul_const (z - w) using 1
        ring
      have h_d_path_sub : HasDerivAt (fun x ↦ path x - (n : ℂ)) (z - w) t := h_d_path.sub_const (n : ℂ)
      have h_inv_deriv : HasDerivAt (fun x ↦ (path x - (n : ℂ))⁻¹) (-(z - w) / (path t - (n : ℂ))^2) t := by
        have h_inv := (hasDerivAt_inv h_denom_ne_zero).hasFDerivAt.restrictScalars ℝ
        convert HasFDerivAt.comp_hasDerivAt t h_inv h_d_path_sub using 1
        simp [ContinuousLinearMap.restrictScalars]
        field_simp
        ring
      convert h_inv_deriv.neg using 1
      · ext x; simp [path]
        field_simp
      · simp [path]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv ((h_integrable n).const_mul (z - w))]
    dsimp [F, path]
    ring_nf
  · intro i
    exact (h_integrable i).1.aestronglyMeasurable
  · have h_eq : (∑' (i : ℤ), ∫⁻ (a : ℝ) in Set.Ioc 0 1, ‖1 / (w + ↑a * (z - w) - ↑i) ^ 2‖ₑ ∂volume) =
      ∑' (i : ℤ), (ENNReal.ofReal (∫ (t : ℝ) in Set.Ioc 0 1, ‖g i t‖)) := by
      congr with i
      symm
      have convexity_w : ∀ x : ℝ, x ∈ Set.Ioc 0 1 → w + ↑x * (z - w) - ↑i ≠ 0 := by
        intro x hx h
        have : w + ↑x * (z - w) ∈ Set.range (fun (n : ℤ) ↦ (n : ℂ)) :=
          ⟨i, by simp only; rw [sub_eq_zero] at h; exact h.symm ⟩
        apply h_path x (Set.Ioc_subset_Icc_self hx) this
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun t : ℝ ↦ ‖g i t‖)]
      · apply setLIntegral_congr_fun_ae (by simp)
        apply Filter.Eventually.of_forall
        intro x hx
        simp only [one_div, norm_inv, norm_pow, g, path]
        rw [enorm_inv]
        · conv_rhs => arg 1; rw [← ofReal_norm_eq_enorm, norm_pow]
          apply ENNReal.ofReal_inv_of_pos
          apply sq_pos_of_pos
          apply norm_pos_iff.mpr (convexity_w x hx)
        · simp [convexity_w x hx]
      · let S := path '' Set.Icc 0 1
        have h_compact : IsCompact S := isCompact_Icc.image_of_continuousOn h_cont_path
        have h_not_mem : (i : ℂ) ∉ S := by
          simp only [Set.mem_image, Set.mem_Icc, not_exists, not_and, and_imp, S]
          intro t h0 h1 heq
          rcases lt_or_eq_of_le h0 with ht_pos | rfl
          · exact convexity_w t ⟨ht_pos, h1⟩ (sub_eq_zero.mpr heq)
          · dsimp [path] at heq
            simp only [zero_mul, add_zero] at heq
            rw [heq] at hw
            exact hw ⟨i, rfl⟩
        have h_dist : 0 < Metric.infDist (i : ℂ) S := by
          refine lt_of_le_of_ne Metric.infDist_nonneg ?_
          intro h
          have hS_ne : S.Nonempty := (Set.nonempty_Icc.mpr zero_le_one).image path
          rw [← h_compact.isClosed.closure_eq, Metric.mem_closure_iff_infDist_zero hS_ne] at h_not_mem
          exact h_not_mem h.symm
        let δ := Metric.infDist (i : ℂ) S
        let C := 1 / δ ^ 2
        apply MeasureTheory.IntegrableOn.of_bound (C := C) (hs := by simp)
        · refine ContinuousOn.aestronglyMeasurable ?_ (by simp)
          · apply ContinuousOn.norm
            have hcont_path' :
              ContinuousOn path (Set.Ioc 0 1) :=
              h_cont_path.mono (by intro t ht; exact Set.Ioc_subset_Icc_self ht)
            have hcont_sub :
              ContinuousOn (fun t ↦ path t - (i : ℂ)) (Set.Ioc 0 1) :=
                hcont_path'.sub continuousOn_const
            have hcont_pow :
              ContinuousOn (fun t ↦ (path t - (i : ℂ))^2) (Set.Ioc 0 1) := hcont_sub.pow 2
            have hne :
              ∀ t ∈ Set.Ioc 0 1, (path t - (i : ℂ)) ≠ 0 := by
              intro t ht
              simpa [path] using convexity_w t ht
            have hcont_inv :
              ContinuousOn (fun t ↦ ((path t - (i : ℂ))^2)⁻¹) (Set.Ioc 0 1) :=
              hcont_pow.inv₀ (by
                intro t ht
                have h := hne t ht
                exact pow_ne_zero 2 h)
            simpa [g, div_eq_mul_inv] using hcont_inv
        · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))] with t ht
          simp only [g, norm_div, norm_one, norm_pow]
          dsimp [C]
          apply div_le_div₀ (by exact zero_le_one) (by simp) (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          rw [norm_sub_rev, ← dist_eq_norm]
          rw [abs_of_nonneg dist_nonneg]
          apply Metric.infDist_le_dist_of_mem
          apply Set.mem_image_of_mem
          exact Set.Ioc_subset_Icc_self ht
      · exact Eventually.of_forall fun t ↦ norm_nonneg _
    rw [h_eq]
    simp_rw [ENNReal.ofReal_eq_coe_nnreal (MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall fun t ↦ norm_nonneg _))]
    rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
    apply Summable.congr h_summable
    intro i
    simp

lemma summable_inv_sub_inv_aux {z w : ℂ} (hz : z ∈ integerComplement) (hw : w ∈ integerComplement) :
    Summable (fun n : ℤ ↦ 1 / (w - n) - 1 / (z - n)) := by
  have h_bound : (fun n : ℤ ↦ 1 / (w - n) - 1 / (z - n)) =O[Filter.cofinite] (fun n : ℤ ↦ (1 : ℝ) / (n : ℝ)^2) := by
    have h_eq : ∀ᶠ (n : ℤ) in Filter.cofinite, 1 / (w - n) - 1 / (z - n) = (z - w) / ((w - n) * (z - n)) := by
      filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
      rw [div_sub_div]
      · ring
      · exact sub_ne_zero.mpr (fun h ↦ hw ⟨n, by simp [h]⟩)
      · exact sub_ne_zero.mpr (fun h ↦ hz ⟨n, by simp [h]⟩)
    refine (Asymptotics.isBigO_congr h_eq (Eventually.of_forall fun _ ↦ rfl)).mpr ?_
    apply Asymptotics.IsBigO.trans (g := fun n : ℤ ↦ (1 : ℝ) / |n|^2)
    · apply Asymptotics.IsBigO.of_bound (4 * ‖z - w‖)
      filter_upwards [tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite |>.eventually (eventually_ge_atTop (max (2 * ‖w‖) (2 * ‖z‖)))] with n hn
      simp only [norm_div, norm_mul, norm_pow]
      rw [Real.norm_of_nonneg (by positivity)]
      have hw' : ‖w‖ ≤ |(n : ℝ)| / 2 := by
        have : (max (2 * ‖w‖) (2 * ‖z‖) : ℝ) ≤ |(n : ℝ)| := hn
        linarith [le_max_left (2 * ‖w‖) (2 * ‖z‖)]
      have hz' : ‖z‖ ≤ |(n : ℝ)| / 2 := by
        have : (max (2 * ‖w‖) (2 * ‖z‖) : ℝ) ≤ |(n : ℝ)| := hn
        linarith [le_max_right (2 * ‖w‖) (2 * ‖z‖)]
      have hwn : ‖w - n‖ ≥ |(n : ℝ)| / 2 := by
        rw [norm_sub_rev]
        calc
          ‖(n : ℂ) - w‖ ≥ ‖(n : ℂ)‖ - ‖w‖ := norm_sub_norm_le ..
          _ = |(n : ℝ)| - ‖w‖ := by rw [norm_intCast]
          _ ≥ |(n : ℝ)| - |(n : ℝ)| / 2 := by linarith
          _ = |(n : ℝ)| / 2 := by ring
      have hzn : ‖z - n‖ ≥ |(n : ℝ)| / 2 := by
        rw [norm_sub_rev]
        calc
          ‖(n : ℂ) - z‖ ≥ ‖(n : ℂ)‖ - ‖z‖ := norm_sub_norm_le ..
          _ = |(n : ℝ)| - ‖z‖ := by rw [norm_intCast]
          _ ≥ |(n : ℝ)| - |(n : ℝ)| / 2 := by linarith
          _ = |(n : ℝ)| / 2 := by ring
      calc
        ‖z - w‖ / (‖w - n‖ * ‖z - n‖)
          ≤ ‖z - w‖ / (|(n : ℝ)| / 2 * (|(n : ℝ)| / 2)) := by
            have h_n_pos : 0 < |(n : ℝ)| / 2 := by
              have h_z_pos : 0 < ‖z‖ := norm_pos_iff.mpr (fun h ↦ hz ⟨0, by simp [h.symm]⟩)
              have : 2 * ‖z‖ ≤ |(n : ℝ)| := (le_max_right _ _).trans hn
              linarith
            gcongr
        _ = 4 * ‖z - w‖ * (1 / |(n : ℝ)| ^ 2) := by ring
        _ = 4 * ‖z - w‖ * (1 / ‖(↑|n| : ℝ)‖ ^ 2) := by
          simp [abs_abs, Int.cast_abs, Real.norm_eq_abs]
    · exact (Asymptotics.isBigO_refl _ _).congr_left (fun n ↦ by simp)
  exact summable_of_isBigO (summable_one_div_int_pow.mpr one_lt_two) h_bound

lemma lemma_abadeulmit2_integral_eq_cot_diff {z w : ℂ}
  (hz : z ∈ integerComplement)
  (hw : w ∈ integerComplement)
  (h_path : ∀ t : ℝ, t ∈ Set.Icc 0 1 → w + ↑t * (z - w) ∉ range (fun n : ℤ => (n : ℂ))) :
  (z - w) * ∫ (t : ℝ) in 0..1, ∑' (n : ℤ), 1 / (w + ↑t * (z - w) - ↑n) ^ 2 =
  -π * Complex.cot (π * z) - (-π * Complex.cot (π * w)) := by
  rw [lemma_abadeulmit2_integral_tsum_inv_sub_int_sq hz hw h_path]
  have h_summable_w : Summable (fun n : ℤ ↦ (1 / (w - n) - 1 / (z - n) : ℂ)) := summable_inv_sub_inv_aux hz hw
  calc
    ∑' (n : ℤ), (1 / (w - n) - 1 / (z - n))
    = 1 / (w - 0) - 1 / (z - 0) + ∑' (n : ℕ), (1 / (w - (↑n + 1)) - 1 / (z - (↑n + 1)) + (1 / (w - -(↑n + 1)) - 1 / (z - -(↑n + 1)))) := by
      rw [eq_sub_of_add_eq (tsum_nat_add_neg h_summable_w).symm,
        (h_summable_w.nat_add_neg).tsum_eq_zero_add]
      simp only [Int.cast_zero, sub_zero, neg_add_rev]
      ring_nf
      congr 1
      apply tsum_congr
      intro b
      push_cast
      ring
    _ = (1 / w - 1 / z) + ∑' (n : ℕ), (1 / (w - (↑n + 1)) + 1 / (w + (↑n + 1)) - (1 / (z - (↑n + 1)) + 1 / (z + (↑n + 1)))) := by
      simp only [sub_zero]
      congr 1
      apply tsum_congr
      intro n
      ring
    _ = (1 / w - 1 / z) + (∑' (n : ℕ), (1 / (w - (↑n + 1)) + 1 / (w + (↑n + 1))) - ∑' (n : ℕ), (1 / (z - (↑n + 1)) + 1 / (z + (↑n + 1)))) := by
      rw [Summable.tsum_sub (summable_cotTerm hw) (summable_cotTerm hz)]
    _ = (1 / w + ∑' (n : ℕ+), (1 / (w - n) + 1 / (w + n))) - (1 / z + ∑' (n : ℕ+), (1 / (z - n) + 1 / (z + n))) := by
      have hw : ∑' (n : ℕ), (1 / (w - (↑n + 1)) + 1 / (w + (↑n + 1))) = ∑' (n : ℕ+), (1 / (w - n) + 1 / (w + n)) := by
        symm
        simp_rw [tsum_pnat_eq_tsum_succ (f := fun (n : ℕ) => 1 / (w - n) + 1 / (w + n))]
        simp
      have hz_sum : ∑' (n : ℕ), (1 / (z - (↑n + 1)) + 1 / (z + (↑n + 1))) = ∑' (n : ℕ+), (1 / (z - n) + 1 / (z + n)) := by
        symm
        simp_rw [tsum_pnat_eq_tsum_succ (f := fun (n : ℕ) => 1 / (z - n) + 1 / (z + n))]
        simp
      rw [hw, hz_sum]
      ring
    _ = π * cot (π * w) - π * cot (π * z) := by
      rw [cot_series_rep hz, cot_series_rep hw]
    _ = (-π * Complex.cot (π * z)) - (-π * Complex.cot (π * w)) := by
      ring

lemma lemma_abadeulmit2_continuousAt_integral_tsum_one_div_sub_int_sq {z : ℂ}
  (hz : z ∈ integerComplement) :
  ContinuousAt (fun x' ↦ ∫ (t : ℝ) in 0..1, (fun w : ℂ ↦ ∑' (n : ℤ), 1 / (w - n) ^ 2) (z + ↑t * (x' - z))) z  := by
  have h_open : IsOpen integerComplement := Complex.isOpen_compl_range_intCast
  obtain ⟨ε, hε, h_ball⟩ := Metric.isOpen_iff.1 h_open z hz
  let S : ℂ → ℂ := fun w : ℂ ↦ ∑' (n : ℤ), 1 / (w - n) ^ 2
  let ε' := ε / 2
  have hε' : ε' > 0 := half_pos hε
  let K := Metric.closedBall z ε'
  have hK_compact : IsCompact K := by exact isCompact_closedBall z ε'
  have hK_sub : K ⊆ integerComplement := (Metric.closedBall_subset_ball (half_lt_self hε)).trans h_ball
  have hS_cont : ContinuousOn S K := by
    dsimp [S]
    refine continuousOn_tsum (u := fun (n : ℤ) ↦ (‖z - n‖ - ε')⁻¹ ^ 2) ?_ ?_ ?_
    · intro i
      simp_rw [one_div]
      apply ContinuousOn.inv₀ (by fun_prop)
      · intro x hx
        apply pow_ne_zero
        rw [sub_ne_zero]
        intro h
        apply hK_sub hx
        exact ⟨i, h.symm⟩
    · apply Summable.of_nat_of_neg_add_one
      · apply summable_of_isBigO_nat (g := fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)^2) (summable_one_div_nat_pow.mpr one_lt_two)
        simp_rw [one_div, ← inv_pow]
        refine Asymptotics.IsBigO.pow ?_ 2
        apply Asymptotics.IsBigO.inv_rev
        · apply Asymptotics.IsBigO.of_bound 2
          filter_upwards [eventually_ge_atTop (Nat.ceil (2 * (‖z‖ + ε')))] with x hx
          norm_cast
          have hx_real : 2 * (‖z‖ + ε') ≤ x := by exact_mod_cast Nat.le_of_ceil_le hx
          have h_dist : ↑x - ‖z‖ ≤ ‖z - ↑x‖ := by
            rw [← Complex.norm_natCast x]
            rw [norm_sub_rev z (x : ℂ)]
            apply norm_sub_norm_le
          rw [Real.norm_of_nonneg (by linarith)]
          linarith
        · filter_upwards [eventually_gt_atTop 0] with x hx hx_zero
          norm_cast at hx_zero
          linarith
      · apply summable_of_isBigO_nat (g := fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ)^2)
        · exact_mod_cast (summable_nat_add_iff 1).mpr (summable_one_div_nat_pow.mpr one_lt_two)
        · simp_rw [one_div, ← inv_pow]
          refine Asymptotics.IsBigO.pow ?_ 2
          apply Asymptotics.IsBigO.inv_rev
          · apply Asymptotics.IsBigO.of_bound 2
            filter_upwards [eventually_ge_atTop (Nat.ceil (2 * (‖z‖ + ε')))] with x hx
            push_cast
            simp only [sub_neg_eq_add]
            have h_rev : ↑x + 1 - ‖z‖ ≤ ‖z + (↑x + 1)‖ := by
              rw [add_comm]
              have h_tri := norm_sub_norm_le (x + 1 : ℂ) (-z)
              rw [norm_neg, ← Nat.cast_add_one, Complex.norm_natCast] at h_tri
              simpa [sub_neg_eq_add, add_comm, Nat.cast_add_one] using h_tri
            have hx_real : 2 * (‖z‖ + ε') ≤ ↑x := by exact_mod_cast Nat.le_of_ceil_le hx
            norm_cast at *
            push_cast at *
            rw [Real.norm_of_nonneg (by linarith)]
            linarith
          · apply Filter.Eventually.of_forall
            intro x hx
            norm_cast at hx
    · intro n x hx
      dsimp
      rw [one_div, norm_inv, norm_pow, ← inv_pow]
      have h_dist : ε ≤ ‖z - ↑n‖ := by
        contrapose! hz
        have h_mem : ↑n ∈ Metric.ball z ε := by rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
        have h_comp := h_ball h_mem
        exact (h_comp ⟨n, rfl⟩).elim
      gcongr
      · dsimp [ε'] at *
        linarith
      · rw [Metric.mem_closedBall, dist_eq_norm] at hx
        calc ‖z - ↑n‖ - ε' ≤ ‖z - ↑n‖ - ‖x - z‖ := by linarith
                        _ ≤ ‖x - ↑n‖ := by
                          rw [norm_sub_rev x z]
                          linarith [norm_sub_le_norm_sub_add_norm_sub z x ↑n]
  have h_bound : Bornology.IsBounded (S '' K) :=
    (hK_compact.image_of_continuousOn hS_cont).isBounded
  obtain ⟨M, hM⟩ := h_bound.exists_norm_le
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ ↦ M) (F := fun x t ↦ S (z + t * (x - z)))
    (a := 0) (b := 1)
  · filter_upwards [Metric.ball_mem_nhds z hε'] with x hx
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    apply ContinuousOn.comp hS_cont (by fun_prop)
    intro t ht
    convert Convex.add_smul_sub_mem (convex_closedBall z ε') (Metric.mem_closedBall_self (le_of_lt hε')) (Metric.ball_subset_closedBall hx) ?_
    · simp only [Set.mem_Icc]
      rw [uIoc_of_le zero_le_one] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
  · filter_upwards [Metric.ball_mem_nhds z hε'] with x hx
    apply Filter.Eventually.of_forall
    intro t ht
    apply hM
    apply Set.mem_image_of_mem
    convert Convex.add_smul_sub_mem (convex_closedBall z ε') (Metric.mem_closedBall_self (le_of_lt hε')) (Metric.ball_subset_closedBall hx) ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t ht
    refine ContinuousAt.comp (g := S) ?_ ?_
    · simp only [sub_self, mul_zero, add_zero]
      apply hS_cont.continuousAt
      exact Metric.closedBall_mem_nhds z hε'
    · fun_prop

lemma lemma_abadeulmit2_tsum_one_div_sub_int_sq {z : ℂ} (hz : z ∈ integerComplement) :
  ∑' (n : ℤ), 1 / (z - n) ^ 2 =
  deriv (fun w ↦ -π * Complex.cot (π * w)) z := by
  set f := fun w : ℂ ↦ -π * Complex.cot (π * w)
  set S := fun w : ℂ ↦ ∑' (n : ℤ), 1 / (w - n) ^ 2
  suffices HasDerivAt f (∑' (n : ℤ), 1 / (z - n) ^ 2) z from this.deriv.symm
  apply HasDerivAt.congr_of_eventuallyEq (f := fun w ↦ f z + (w - z) * ∫ t in (0:ℝ)..1, S (z + t * (w - z)))
  · apply HasDerivAt.const_add
    rw [hasDerivAt_iff_isLittleO]
    simp only [sub_self, mul_zero, add_zero]
    set g := fun x' ↦ ∫ (t : ℝ) in 0..1, S (z + ↑t * (x' - z))
    simp only [zero_mul, sub_zero, smul_eq_mul, ← mul_sub]
    apply Asymptotics.isLittleO_of_tendsto
    · intro x' hx; simp [sub_eq_zero.mp hx]
    · have h_eq : (fun x ↦ (x - z) * ((∫ (t : ℝ) in 0..1, S (z + ↑t * (x - z))) - ∑' (n : ℤ), 1 / (z - ↑n) ^ 2) / (x - z)) =
            (fun x ↦ (∫ (t : ℝ) in 0..1, S (z + ↑t * (x - z))) - ∑' (n : ℤ), 1 / (z - ↑n) ^ 2) := by
        ext x
        rcases eq_or_ne x z with rfl | hx
        · simp [S]
        · rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr hx)]
      rw [h_eq, tendsto_sub_nhds_zero_iff]
      have hgz : g z = ∑' (n : ℤ), 1 / (z - ↑n) ^ 2 := by
        simp only [g, sub_self, mul_zero, add_zero]
        rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, Complex.ofReal_one, one_mul]
      rw [← hgz]
      apply (lemma_abadeulmit2_continuousAt_integral_tsum_one_div_sub_int_sq hz).tendsto
  · obtain ⟨ε, hε, h_ball⟩ := Metric.isOpen_iff.1 (Complex.isOpen_compl_range_intCast) z hz
    filter_upwards [Metric.ball_mem_nhds z hε] with w hw
    rw [lemma_abadeulmit2_integral_eq_cot_diff (h_ball hw) hz]
    · dsimp [f]; ring
    · intro t ht
      apply h_ball
      apply (convex_ball z ε).segment_subset (Metric.mem_ball_self hε) hw
      rw [segment_eq_image]
      refine ⟨t, ht, ?_⟩
      simp; ring

lemma lemma_abadeulmit2_deriv_neg_pi_mul_cot_pi_mul {z : ℂ} (hz : z ∈ integerComplement) :
  deriv (fun w ↦ -π * Complex.cot (π * w)) z =
  π ^ 2 / (Complex.sin (π * z)) ^ 2 := by
  have hsin : sin (π * z) ≠ 0 := sin_pi_mul_ne_zero hz
  have h_deriv_cot : HasDerivAt (fun w ↦ Complex.cot (π * w)) (-(π / sin (π * z) ^ 2)) z := by
    have h1 : HasDerivAt (fun (w : ℂ) ↦ (π : ℂ) * w) π z := by
      convert hasDerivAt_mul_const (π : ℂ) using 1
      ext; ring
    have h2 : HasDerivAt Complex.cot (-(1 / sin (π * z) ^ 2)) (π * z) := by
      unfold Complex.cot
      convert (hasDerivAt_cos (π * z)).div (hasDerivAt_sin (π * z)) hsin using 1
      field_simp
      linear_combination Complex.sin_sq_add_cos_sq (π * z)
    convert h2.comp z h1 using 1
    ring
  rw [deriv_const_mul _ h_deriv_cot.differentiableAt, h_deriv_cot.deriv]
  field_simp

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
theorem lemma_abadeulmit2 {z : ℂ} (hz : z ∈ integerComplement) :
    (π ^ 2 / (sin (π * z) ^ 2)) = ∑' (n : ℤ), (1 / ((z - n) ^ 2)) := by
  rw [← lemma_abadeulmit2_deriv_neg_pi_mul_cot_pi_mul hz]
  rw [← lemma_abadeulmit2_tsum_one_div_sub_int_sq hz]

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
lemma lemma_abadimpseri (ϑ : ℝ) (hϑ : |ϑ| < 1) :
    ∑' n : ℕ, (1 / ((n + 1 : ℝ) - ϑ) ^ 3 + 1 / ((n + 1 : ℝ) + ϑ) ^ 3) ≤
      1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1 := by
  have h_sum_bound : ∀ n : ℕ, (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3) ≤
      (1 / (n + 1 - |ϑ|) ^ 3 + 1 / (n + 1 + |ϑ|) ^ 3) := by intro n; cases abs_cases ϑ <;> grind
  have h_sum_bound_endpoints : (∑' n : ℕ, (1 / (n + 1 - |ϑ|) ^ 3 + 1 / (n + 1 + |ϑ|) ^ 3)) ≤
      (1 / (1 - |ϑ|) ^ 3) + 2 * (riemannZeta 3).re - 1 := by
    have h_sum_endpoints_bound : (∑' n : ℕ, (1 / (n + 2 - |ϑ|) ^ 3 + 1 / (n + 1 + |ϑ|) ^ 3)) ≤
        2 * (riemannZeta 3).re - 1 := by
      have h_term_bound : ∀ n : ℕ, (1 / (n + 2 - |ϑ|) ^ 3 + 1 / (n + 1 + |ϑ|) ^ 3) ≤
          (1 / (n + 1) ^ 3 + 1 / (n + 2) ^ 3) := by
        intro n
        rw [div_add_div, div_add_div, div_le_div_iff₀] <;> try positivity
        · have h_simp : (n + 1 + |ϑ|) ^ 3 + (n + 2 - |ϑ|) ^ 3 ≤ (n + 1) ^ 3 + (n + 2) ^ 3 := by
            nlinarith [abs_nonneg ϑ, pow_two_nonneg (|ϑ| : ℝ), pow_two_nonneg (n : ℝ),
              mul_lt_mul_of_pos_left hϑ <| Nat.cast_add_one_pos n]
          field_simp
          refine le_trans (mul_le_mul_of_nonneg_left h_simp <| by positivity) ?_
          have h_simp : (n + 1 : ℝ) ^ 3 * (n + 2) ^ 3 ≤ (n + 1 + |ϑ|) ^ 3 * (n + 2 - |ϑ|) ^ 3 := by
            rw [← mul_pow, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg ϑ]) _
          exact mul_le_mul h_simp (by linarith) (by positivity)
            (by exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
        · exact mul_pos (pow_pos (by linarith [abs_nonneg ϑ]) _) (pow_pos (by linarith [abs_nonneg ϑ]) _)
        · exact pow_ne_zero _ (by linarith [abs_nonneg ϑ])
      refine le_trans (Summable.tsum_le_tsum h_term_bound ?_ ?_) ?_
      · exact of_nonneg_of_le (fun n ↦ add_nonneg (one_div_nonneg.mpr (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
          (one_div_nonneg.mpr (pow_nonneg (by linarith [abs_nonneg ϑ]) _)))
            h_term_bound (add (by exact_mod_cast summable_nat_add_iff 1 |>.2 <| summable_one_div_nat_pow.2 <| by omega)
              (by exact_mod_cast summable_nat_add_iff 2 |>.2 <| summable_one_div_nat_pow.2 <| by omega))
      · exact add (by simpa using summable_nat_add_iff 1 |>.2 <| summable_one_div_nat_pow.2 <| by omega)
          (by simpa using summable_nat_add_iff 2 |>.2 <| summable_one_div_nat_pow.2 <| by omega)
      · have h_sum_zeta : ∑' n : ℕ, (1 / (n + 1 : ℝ) ^ 3 + 1 / (n + 2 : ℝ) ^ 3) =
            2 * (∑' n : ℕ, (1 / (n + 1 : ℝ) ^ 3)) - 1 := by
          rw [Summable.tsum_add, Summable.tsum_eq_zero_add] <;> norm_num
          · norm_num [add_assoc]; ring
          · exact_mod_cast summable_nat_add_iff 1 |>.2 <| summable_nat_pow_inv.2 <| by omega
          · exact_mod_cast summable_nat_add_iff 1 |>.2 <| summable_nat_pow_inv.2 <| by omega
          · exact_mod_cast summable_nat_add_iff 2 |>.2 <| summable_nat_pow_inv.2 <| by omega
        convert h_sum_zeta.le using 2
        erw [zeta_eq_tsum_one_div_nat_add_one_cpow] <;> norm_num
        · convert ofReal_re _; simp [Complex.ofReal_tsum]
    rw [Summable.tsum_eq_zero_add]
    · norm_num [add_assoc, add_left_comm, add_comm, div_eq_mul_inv, mul_add, mul_comm,
        mul_left_comm, tsum_mul_left] at *
      have hs₁ : Summable fun n : ℕ ↦ ((|ϑ| + (n + 1)) ^ 3)⁻¹ :=
        of_nonneg_of_le (fun n ↦ inv_nonneg.2 (pow_nonneg (by positivity) _))
          (fun n ↦ by simpa using inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
            (show (|ϑ| + (n + 1) : ℝ) ≥ n + 1 by linarith [abs_nonneg ϑ]) 3))
          (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 <| by omega)
      have hs₂ : Summable fun n : ℕ ↦ (((n : ℝ) + 2 - |ϑ|) ^ 3)⁻¹ :=
        of_nonneg_of_le (fun n ↦ inv_nonneg.2 (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
          (fun n ↦ by rw [inv_le_comm₀] <;> norm_num <;> ring_nf <;>
            nlinarith [abs_nonneg ϑ, pow_two_nonneg ((n : ℝ) + 1 - |ϑ|)])
          (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
      rw [Summable.tsum_add hs₁ hs₂] at h_sum_endpoints_bound
      rw [Summable.tsum_add]
      · rw [show (∑' b : ℕ, ((|ϑ| + (b + 2)) ^ 3)⁻¹) = (∑' b : ℕ, ((|ϑ| + (b + 1)) ^ 3)⁻¹) - ((|ϑ| + 1) ^ 3)⁻¹ from ?_]
        · nlinarith [show 0 < (|ϑ| + 1) ^ 3 by positivity, inv_mul_cancel₀ (show (|ϑ| + 1) ^ 3 ≠ 0 by positivity)]
        · rw [eq_comm, Summable.tsum_eq_zero_add]
          · norm_num [add_assoc]
          · exact hs₁
      · exact_mod_cast of_nonneg_of_le (fun n ↦ by positivity)
          (fun n ↦ by rw [inv_le_comm₀] <;> norm_num <;> ring_nf <;> nlinarith only [abs_nonneg ϑ, hϑ])
            (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
      · exact hs₂
    · refine Summable.add ?_ ?_
      · have : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 3) := summable_one_div_nat_pow.2 (by omega)
        rw [← summable_nat_add_iff 1] at this ⊢
        exact of_nonneg_of_le (fun n ↦ one_div_nonneg.mpr (pow_nonneg (by cases abs_cases ϑ <;> linarith) _))
          (fun n ↦ one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_left₀ (by positivity) (by cases abs_cases ϑ <;> linarith) _)) this
      · exact_mod_cast of_nonneg_of_le (fun n ↦ by positivity)
          (fun n ↦ by simpa using inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
            (show (n : ℝ) + 1 + |ϑ| ≥ n + 1 by linarith [abs_nonneg ϑ]) 3))
          (summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 <| by omega)
  refine le_trans (Summable.tsum_le_tsum h_sum_bound ?_ ?_) h_sum_bound_endpoints
  · have h_bound : ∀ n : ℕ,
        (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3) ≤ 2 / (n + 1 - |ϑ|) ^ 3 := fun n ↦ by
      have : (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3) ≤
          (1 / (n + 1 - |ϑ|) ^ 3 + 1 / (n + 1 - |ϑ|) ^ 3) := by
        cases abs_cases ϑ <;> simp only [add_le_add_iff_left, one_div, sub_neg_eq_add, add_le_add_iff_right, *]
        · exact inv_anti₀ (pow_pos (by linarith) _) (by gcongr <;> linarith)
        · exact inv_anti₀ (pow_pos (by linarith) _)
            (pow_le_pow_left₀ (by linarith) (by linarith) _)
      exact this.trans_eq (by ring)
    refine of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ h_bound n) ?_
    · exact add_nonneg (one_div_nonneg.mpr (pow_nonneg (by linarith [abs_lt.mp hϑ]) _))
        (one_div_nonneg.mpr (pow_nonneg (by linarith [abs_lt.mp hϑ]) _))
    · have : Summable (fun n : ℕ ↦ 2 / (n : ℝ) ^ 3) :=
        mul_left 2 <| Real.summable_nat_pow_inv.2 (by norm_num : (1 : ℕ) < 3)
      rw [← summable_nat_add_iff 1] at this ⊢
      exact of_nonneg_of_le (fun n ↦ div_nonneg zero_le_two (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
        (fun n ↦ div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by linarith [abs_nonneg ϑ]) (by linarith [abs_nonneg ϑ]) _)) this
  · refine add ?_ ?_
    · rw [← summable_nat_add_iff 1]
      simp only [one_div, Nat.cast_add, Nat.cast_one] at *
      exact of_nonneg_of_le (fun n ↦ inv_nonneg.2 (pow_nonneg (by linarith [abs_nonneg ϑ]) _))
        (fun n ↦ by rw [inv_le_comm₀] <;> norm_num <;> ring_nf <;>
          nlinarith [abs_nonneg ϑ, pow_two_nonneg ((n : ℝ) ^ 2), pow_two_nonneg ((n : ℝ) + 1),
            pow_two_nonneg ((n : ℝ) + 1 - |ϑ|)]) (summable_nat_add_iff 1 |>.2 <| summable_one_div_nat_pow.2 one_lt_two)
    · exact of_nonneg_of_le (fun n ↦ by positivity)
        (fun n ↦ by simpa using inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
          (show (n : ℝ) + 1 + |ϑ| ≥ n + 1 by linarith [abs_nonneg ϑ]) 3))
            (summable_nat_add_iff 1 |>.2 <| summable_one_div_nat_pow.2 <| by omega)

lemma lemma_abadsumas_integrable_explog {s : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) (k : ℤ) :
    IntervalIntegrable
      (fun y => ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (↑k * y))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hab)
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · apply continuous_ofReal.comp_continuousOn
      apply ContinuousOn.rpow continuousOn_id continuousOn_const
      exact fun _ hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1))
    · apply continuousOn_e_comp
      apply ContinuousOn.mul continuousOn_const
      apply Real.continuousOn_log.mono
      exact fun _ hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  · dsimp [e]; fun_prop

lemma lemma_abadsumas_sum_fourier (s : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    let f : ℝ → ℂ := fun y ↦
      if a ≤ y ∧ y ≤ b then (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) else 0
    ∀ n : ℕ,
    FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ)) =
    2 * ∫ y in a..b, (y : ℂ) ^ (-s) * Real.cos (2 * π * (n + 1) * y) := by
  intro f n
  have fourier_as_integral : ∀ n : ℤ, FourierTransform.fourier f n =
    ∫ y in a..b, (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) * e (-n * y) := by
    intro n
    calc FourierTransform.fourier f ↑n
      _ = ∫ (y : ℝ), Complex.exp (↑(-2 * π * y * ↑n) * Complex.I) • f y := fourier_real_eq_integral_exp_smul f ↑n
      _ = ∫ (y : ℝ) in a..b, Complex.exp (↑(-2 * π * y * ↑n) * Complex.I) • f y := by
        rw [intervalIntegral.integral_of_le hab.le, ← integral_indicator measurableSet_Ioc]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.Measure.ae_ne volume a] with y hy_ne
        by_cases hy : y ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy]
          have h_f_zero : f y = 0 := by
            dsimp [f]
            split_ifs with h_bounds
            · exact (hy ⟨lt_of_le_of_ne h_bounds.1 hy_ne.symm, h_bounds.2⟩).elim
            · rfl
          rw [h_f_zero, smul_zero]
      _ = ∫ (y : ℝ) in a..b, ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (-↑n * y) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have h_bounds : a ≤ y ∧ y ≤ b := by
          rw [Set.uIcc_of_le hab.le] at hy
          exact ⟨hy.1, hy.2⟩
        have h_f_val : f y = (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) := by
          dsimp [f]
          rw [if_pos h_bounds]
        dsimp only
        rw [h_f_val, e]
        calc cexp (↑(-2 * π * y * ↑n) * I) • (↑(y ^ (-s.re)) * cexp (2 * ↑π * I * ↑(-(s.im / (2 * π)) * Real.log y)))
            = ↑(y ^ (-s.re)) * cexp (2 * ↑π * I * ↑(-(s.im / (2 * π)) * Real.log y))
                * cexp (↑(-2 * π * y * ↑n) * I) := by
                  rw [smul_eq_mul]; ring
          _ = ↑(y ^ (-s.re)) * cexp (2 * ↑π * I * ↑(-(s.im / (2 * π)) * Real.log y))
                * e (-↑n * y) := by
                  rw [e]
                  congr 1
                  congr 1
                  push_cast
                  ring
  have sum_fourier_as_cosine : ∀ n : ℕ,
    FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ)) =
    2 * ∫ y in a..b, (y ^ (-s.re) : ℝ) * e (-(s.im / (2 * π)) * Real.log y) *
      Real.cos (2 * π * (n + 1) * y) := by
    intro n
    have h1 : FourierTransform.fourier f (↑n + 1) =
        ∫ y in a..b, ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (-(↑n + 1 : ℤ) * y) := by
      exact_mod_cast fourier_as_integral (↑n + 1 : ℤ)
    have h2 : FourierTransform.fourier f (-↑(n + 1 : ℤ)) =
        ∫ y in a..b, ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (↑(n + 1 : ℤ) * y) := by
      simpa only [Int.cast_neg, neg_neg] using fourier_as_integral (-↑((n + 1) : ℤ))
    rw [h1, h2]
    have hint1 : IntervalIntegrable
        (fun y => ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (-(↑n + 1 : ℤ) * y))
        MeasureTheory.volume a b := by
      have := lemma_abadsumas_integrable_explog (s := s) ha hab (-(n + 1) : ℤ)
      simpa only [Int.cast_neg] using this
    have hint2 : IntervalIntegrable
        (fun y => ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * e (↑(n + 1 : ℤ) * y))
        MeasureTheory.volume a b := lemma_abadsumas_integrable_explog ha hab (n + 1 : ℤ)
    rw [← intervalIntegral.integral_add hint1 hint2, ← intervalIntegral.integral_const_mul]
    congr 1
    ext y
    have heuler : e (-↑(n + 1 : ℤ) * y) + e (↑(n + 1 : ℤ) * y) =
    2 * ↑(Real.cos (2 * π * (↑n + 1) * y)) := by
      have hpos : e (↑(n + 1 : ℤ) * y) =
          Complex.exp (↑(2 * π * (↑n + 1) * y) * Complex.I) := by
        simp only [e]; push_cast; ring_nf
      have hneg : e (-↑(n + 1 : ℤ) * y) =
          Complex.exp (-(↑(2 * π * (↑n + 1) * y)) * Complex.I) := by
        simp only [e]; push_cast; ring_nf
      rw [hneg, hpos, add_comm, Complex.ofReal_cos, ← Complex.two_cos]
    linear_combination ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) * heuler
  rw [sum_fourier_as_cosine n]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [neg_mul, ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_add, ofReal_natCast, ofReal_one,
  mul_eq_mul_right_iff]
  have hy_pos : 0 < y := by
    rw [Set.uIcc_of_le hab.le] at hy
    exact ha.trans_le hy.1
  have key : (y : ℂ) ^ (-s) =
      ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) := by
    have hyne : (y : ℂ) ≠ 0 := by exact_mod_cast hy_pos.ne'
    rw [Complex.cpow_def_of_ne_zero hyne]
    rw [← Complex.ofReal_log hy_pos.le]
    have hexp_split : (↑(Real.log y) : ℂ) * -s =
        ↑(-s.re * Real.log y) + ↑(-s.im * Real.log y) * Complex.I := by
      rw [← Complex.re_add_im s]
      push_cast
      ring_nf
      field_simp
      congr 1
      simp only [re_add_im]
      ring_nf
    rw [hexp_split, Complex.exp_add_mul_I]
    have hrpow : (y ^ (-s.re) : ℝ) = Real.exp (-s.re * Real.log y) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hy_pos]
    have he_expand : e (-(s.im / (2 * π)) * Real.log y) =
        ↑(Real.cos (-s.im * Real.log y)) + ↑(Real.sin (-s.im * Real.log y)) * Complex.I := by
      rw [show ↑(Real.cos (-s.im * Real.log y)) + ↑(Real.sin (-s.im * Real.log y)) * I =
          Complex.exp (↑(-s.im * Real.log y) * I) from by
            rw [exp_mul_I]
            simp only [Complex.ofReal_cos, Complex.ofReal_sin]]
      simp [e]
      congr 1
      ring_nf; field_simp
    rw [hrpow, he_expand]
    push_cast
    ring
  simp [key]

lemma lemma_abadsumas_summable_alternating_theta (θ : ℝ) (hθ : |θ| < 1) :
    Summable (fun n : ℕ ↦ ((-1) ^ (n + 2) * 2 * θ / ((n + 1) ^ 2 - θ ^ 2) : ℂ)) := by
  have hθ_sq_lt : θ ^ 2 < 1 := by nlinarith [sq_abs θ, abs_nonneg θ]
  apply Summable.of_norm_bounded (g := fun n : ℕ => 2 * |θ| / ((1 - θ ^ 2) * ((n : ℝ) + 1) ^ 2))
  · apply Summable.mul_left
    have hpos : (0 : ℝ) < 1 - θ ^ 2 := by nlinarith [sq_abs θ, abs_nonneg θ]
    simp_rw [mul_inv]
    apply Summable.mul_left
    have hbase : Summable (fun n : ℕ => (n ^ 2 : ℝ)⁻¹) := by
      simp_rw [inv_eq_one_div]
      norm_cast
      simp_rw [Nat.cast_pow] at ⊢
      apply Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr hbase |>.congr
      (fun n => by push_cast; ring_nf)
  · intro n
    have hdenom_pos : (0 : ℝ) < (n + 1) ^ 2 - θ ^ 2 := by
      have : (0 : ℝ) ≤ (↑n : ℝ) := Nat.cast_nonneg n
      nlinarith [sq_nonneg (n : ℝ)]
    rw [show ‖(-1 : ℂ) ^ (n + 2) * 2 * θ / ((n + 1) ^ 2 - θ ^ 2)‖ = 2 * |θ| / (((n : ℝ) + 1) ^ 2 - θ ^ 2) by
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, h2,
          one_mul, Complex.norm_real, norm_eq_abs]
      congr 1
      rw [show (↑n + 1 : ℂ) ^ 2 - (↑θ : ℂ) ^ 2 = ↑((↑n + 1 : ℝ) ^ 2 - θ ^ 2) by norm_cast,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenom_pos]]
    have hdenom_ineq : (1 - θ ^ 2) * (n + 1) ^ 2 ≤ (n + 1) ^ 2 - θ ^ 2 := by
      have h_cast : (0 : ℝ) ≤ (↑n : ℝ) := Nat.cast_nonneg n
      have h_ge_one : (1 : ℝ) ≤ ↑n + 1 := by linarith
      have h_sq_ge : (1 : ℝ) ≤ (↑n + 1) ^ 2 := by nlinarith
      nlinarith [sq_nonneg θ]
    have h2 : (0 : ℝ) < 1 - θ ^ 2 := by linarith
    gcongr

private lemma lemma_abadsumas_pnat_sum_eq_nat_sum (θ : ℝ) (hθ : (θ : ℂ) ∈ integerComplement) :
    ∑' (n : ℕ+), (-1 : ℂ) ^ (n : ℕ) *
        (1 / ((θ : ℂ) - ((n : ℕ) : ℂ)) + 1 / ((θ : ℂ) + ((n : ℕ) : ℂ))) =
    ∑' (n : ℕ), (-1 : ℂ) ^ (n + 2) * (2 : ℂ) * (θ : ℂ) /
        (((n : ℂ) + 1) ^ (2 : ℕ) - (θ : ℂ) ^ (2 : ℕ)) := by
  rw [← Equiv.pnatEquivNat.symm.tsum_eq
        (fun m : ℕ+ => (-1 : ℂ) ^ (m : ℕ) *
          (1 / ((θ : ℂ) - ((m : ℕ) : ℂ)) +
           1 / ((θ : ℂ) + ((m : ℕ) : ℂ))))]
  apply tsum_congr
  intro n
  simp only [show (Equiv.pnatEquivNat.symm n : ℕ+).val = n + 1 by simp [Equiv.pnatEquivNat],
    show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring]
  have hd1 : (θ : ℂ) - ((n : ℂ) + 1) ≠ 0 := by
    have : ((↑(n + 1) : ℤ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
    rw [← this, sub_ne_zero]
    exact fun h => hθ (h ▸ ⟨↑(n + 1), by push_cast; ring⟩)
  have hd2 : (θ : ℂ) + ((n : ℂ) + 1) ≠ 0 := by
    have : ((↑(-(n + 1 : ℤ)) : ℤ) : ℂ) = -((n : ℂ) + 1) := by push_cast; ring
    rw [show (θ : ℂ) + ((n : ℂ) + 1) = (θ : ℂ) - (-((n : ℂ) + 1)) from by ring]
    rw [sub_ne_zero]
    exact fun h => hθ (h ▸ ⟨-(↑(n + 1) : ℤ), by push_cast; ring⟩)
  have hd3 : ((n : ℂ) + 1) ^ (2 : ℕ) - (θ : ℂ) ^ (2 : ℕ) ≠ 0 := by
    have factored : ((n : ℂ) + 1) ^ (2 : ℕ) - (θ : ℂ) ^ (2 : ℕ) =
        ((n : ℂ) + 1 - (θ : ℂ)) * ((n : ℂ) + 1 + (θ : ℂ)) := by ring
    rw [factored]
    apply mul_ne_zero
    · have : ((n : ℂ) + 1 - (θ : ℂ)) = -((θ : ℂ) - ((n : ℂ) + 1)) := by ring
      rw [this]
      exact neg_ne_zero.mpr hd1
    · have : ((n : ℂ) + 1 + (θ : ℂ)) = (θ : ℂ) + ((n : ℂ) + 1) := by ring
      rw [this]
      exact hd2
  field_simp [hd1, hd2, hd3]
  ring

private lemma lemma_abadsumas_not_in_integerComplement {ϑ : ℝ} (hϑ_lt : |ϑ| < 1) (hϑ : ϑ ≠ 0) :
    (ϑ : ℂ) ∈ integerComplement := by
  simp only [integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
  intro n hn
  have hϑ_eq : ϑ = (n : ℝ) := by exact_mod_cast hn.symm
  have : |n| < 1 := by exact_mod_cast (hϑ_eq ▸ hϑ_lt : |(n : ℝ)| < 1)
  exact hϑ <| hϑ_eq.trans <| by rw [abs_lt] at this; exact_mod_cast (show n = 0 by omega)

private lemma lemma_abadsumas_sum_main_term_a (ϑ : ℝ) (hϑ_lt : |ϑ| < 1)
    (hpos_minus : ∀ n : ℕ, 0 < (n : ℝ) + 1 - ϑ)
    (hpos_plus : ∀ n : ℕ, 0 < (n : ℝ) + 1 + ϑ) :
    let g : ℝ → ℂ := fun t ↦
      if t ≠ 0 then (1 / Complex.sin (π * t) : ℂ) - (1 / (π * t : ℂ)) else 0
    ∑' (n : ℕ), ((-1 : ℂ) ^ (n + 2) * 2 * ϑ / (((n : ℂ) + 1) ^ (2 : ℕ) - (ϑ : ℂ) ^ (2 : ℕ))) =
    ↑π * g ϑ := by
  intro g
  by_cases hϑ : ϑ = 0
  · simp [hϑ, g]
  · have h_not_int : (ϑ : ℂ) ∈ integerComplement := lemma_abadsumas_not_in_integerComplement hϑ_lt hϑ
    have h_sum_shift :
        ∑' (n : ℕ), (-1 : ℂ) ^ (n + 2) * 2 * (ϑ : ℂ) /
            (((n : ℂ) + 1) ^ (2 : ℕ) - (ϑ : ℂ) ^ (2 : ℕ)) =
        ∑' (n : ℕ+), (-1 : ℂ) ^ (n : ℕ) *
            (1 / ((ϑ : ℂ) - ↑↑n) + 1 / ((ϑ : ℂ) + ↑↑n)) :=
      calc ∑' (n : ℕ), (-1 : ℂ) ^ (n + 2) * 2 * (ϑ : ℂ) /
              (((n : ℂ) + 1) ^ (2 : ℕ) - (ϑ : ℂ) ^ (2 : ℕ))
          _ = ∑' (n : ℕ), (-1 : ℂ) ^ (n + 1) *
                  (1 / ((ϑ : ℂ) - ((n : ℂ) + 1)) + 1 / ((ϑ : ℂ) + ((n : ℂ) + 1))) := by
                congr 1; ext n
                have hne1 : ((n : ℂ) + 1 - (ϑ : ℂ)) ≠ 0 := by
                  exact_mod_cast (hpos_minus n).ne'
                have hne2 : ((n : ℂ) + 1 + (ϑ : ℂ)) ≠ 0 := by
                  exact_mod_cast (hpos_plus n).ne'
                have h1 : (ϑ : ℂ) - ((n : ℂ) + 1) ≠ 0 := by
                  rwa [← neg_sub, neg_ne_zero]
                have h2 : (ϑ : ℂ) + ((n : ℂ) + 1) ≠ 0 := by rwa [add_comm]
                have hne3 : ((n : ℂ) + 1) ^ (2 : ℕ) - (ϑ : ℂ) ^ (2 : ℕ) ≠ 0 := by
                  rw [show ((n : ℂ) + 1) ^ (2 : ℕ) - (ϑ : ℂ) ^ (2 : ℕ) =
                      ((n : ℂ) + 1 - ϑ) * ((n : ℂ) + 1 + ϑ) by ring]
                  exact mul_ne_zero hne1 hne2
                field_simp [h1, h2, hne3]; ring
          _ = ∑' (n : ℕ+), (-1 : ℂ) ^ (n : ℕ) *
                  (1 / ((ϑ : ℂ) - ↑↑n) + 1 / ((ϑ : ℂ) + ↑↑n)) := by
                rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
                simp only [one_div, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe,
                  Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    rw [h_sum_shift, show g ϑ = 1 / Complex.sin (↑π * ↑ϑ) - 1 / (↑π * ↑ϑ) by dsimp [g]; rw [if_pos hϑ]]
    rw [show ↑π * (1 / Complex.sin (↑π * ↑ϑ) - 1 / (↑π * ↑ϑ)) = ↑π / Complex.sin (↑π * ↑ϑ) - 1 / ↑ϑ by field_simp]
    rw [lemma_abadeuleulmit1 h_not_int]
    ring_nf

private lemma lemma_abadsumas_sum_main_term_b (ϑ_minus : ℝ)
    (hϑ_minus_lt : |ϑ_minus| < 1) :
    let g : ℝ → ℂ := fun t ↦ if t ≠ 0 then 1 / Complex.sin (↑π * ↑t) - 1 / (↑π * ↑t) else 0
    ∑' (n : ℕ), (-1 : ℂ) ^ (n + 2) * 2 * (ϑ_minus : ℂ) /
        (((n : ℂ) + 1) ^ (2 : ℕ) - (ϑ_minus : ℂ) ^ (2 : ℕ)) = ↑π * g ϑ_minus := by
  intro g
  by_cases hθ : ϑ_minus = 0
  · simp only [hθ, Complex.ofReal_zero]
    dsimp [g]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      zero_div, tsum_zero, not_true_eq_false, ↓reduceIte]
  · have hϑ_minus_mem : (ϑ_minus : ℂ) ∈ integerComplement :=
      lemma_abadsumas_not_in_integerComplement hϑ_minus_lt hθ
    rw [show (π : ℂ) * g ϑ_minus = ↑π / Complex.sin (↑π * ↑ϑ_minus) - 1 / (ϑ_minus : ℂ) by
      dsimp [g]; rw [if_pos hθ, mul_sub, mul_one_div, mul_one_div]; congr 1
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hϑ : (ϑ_minus : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ
      field_simp [hπ, hϑ],
      ← lemma_abadsumas_pnat_sum_eq_nat_sum ϑ_minus hϑ_minus_mem, eq_sub_iff_add_eq, add_comm]
    exact (lemma_abadeuleulmit1 hϑ_minus_mem).symm

lemma lemma_abadsumas_quad {s : ℂ} {a : ℝ} (ha : 0 < a)
    (haτ : a > |s.im| / (2 * π)) :
    let ϑ : ℝ := s.im / (2 * π * a)
    ∑' n : ℕ, (1 / (n + 1 - ϑ)^2 + 1/(n + 1 + ϑ)^2) =
    if ϑ = 0 then π^2/3
    else π^2 / Real.sin (π * ϑ)^2 - 1/ϑ^2 := by
  intro ϑ
  split_ifs with hϑ
  · simp only [hϑ, sub_zero, add_zero]
    simp_rw [show ∀ n : ℕ, (1 : ℝ) / ((↑n + 1) ^ 2) + 1 / ((↑n + 1) ^ 2) = 2 * (1 / ((↑n + 1) ^ 2)) from fun _ => by ring, tsum_mul_left]
    rw [show ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 = π ^ 2 / 6 by
      have h := HasSum.tsum_eq hasSum_zeta_two
      rw [Summable.tsum_eq_zero_add hasSum_zeta_two.summable] at h
      simpa using h]
    ring
  · have hϑ_lt : |ϑ| < 1 := by
      simp only [ϑ]
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * π * a),
          div_lt_one (by positivity : (0:ℝ) < 2 * π * a)]
      have h2π : (0:ℝ) < 2 * π := by positivity
      have := haτ
      rw [gt_iff_lt, div_lt_iff₀ h2π] at this
      linarith [abs_nonneg s.im]
    have hmem : (ϑ : ℂ) ∈ Complex.integerComplement := by
      simp only [Complex.integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
      intro n heq
      have heqR : (n : ℝ) = ϑ := by
        have h := congr_arg Complex.re heq
        simp only [Complex.ofReal_re] at h
        exact_mod_cast h
      rcases eq_or_ne n 0 with rfl | hn
      · exact hϑ (by exact_mod_cast heqR.symm)
      · have hge : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
        rw [heqR] at hge; linarith [hϑ_lt]
    have hweier := lemma_abadeulmit2 hmem
    have hZ_summable : Summable (fun n : ℤ => (1 : ℂ) / ((ϑ : ℂ) - ↑n) ^ 2) := by
      have h_nat : Summable (fun n : ℕ => (1 : ℂ) / ((ϑ : ℂ) - ↑n) ^ 2) := by
        have h_nat_shift : Summable (fun n : ℕ => (1 : ℂ) / ((ϑ : ℂ) - ↑(n + 1)) ^ 2) := by
          apply Summable.of_norm_bounded_eventually (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
          · exact Real.summable_one_div_nat_pow.mpr (by norm_num)
          · rw [Nat.cofinite_eq_atTop]
            filter_upwards [eventually_ge_atTop 1] with n hn
            rw [norm_div, norm_one, norm_pow]
            have h_eq : ‖(ϑ : ℂ) - ↑(n + 1)‖ = (n : ℝ) + 1 - ϑ := by
              rw [show (ϑ : ℂ) - ↑(n + 1) = -↑((n : ℝ) + 1 - ϑ) by push_cast; ring]
              rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
              apply abs_of_pos
              have : -1 < ϑ ∧ ϑ < 1 := abs_lt.mp hϑ_lt
              have : (1 : ℝ) ≤ n := by exact_mod_cast hn
              linarith
            rw [h_eq]
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            apply pow_le_pow_left₀
            · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
              have : -1 < ϑ ∧ ϑ < 1 := abs_lt.mp hϑ_lt
              linarith
            · have : -1 < ϑ ∧ ϑ < 1 := abs_lt.mp hϑ_lt
              linarith
        exact (summable_nat_add_iff 1).mp h_nat_shift
      have h_neg : Summable (fun n : ℕ => (1 : ℂ) / ((ϑ : ℂ) - ↑(-(n + 1 : ℤ))) ^ 2) := by
        apply Summable.of_norm_bounded_eventually (f := fun n : ℕ => 1 / ((ϑ : ℂ) - ↑(-(n + 1 : ℤ))) ^ 2) (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
        · exact Real.summable_one_div_nat_pow.mpr (by norm_num)
        · rw [Nat.cofinite_eq_atTop]
          filter_upwards [eventually_ge_atTop 1] with n hn
          rw [norm_div, norm_one, norm_pow]
          have h_eq : ‖(ϑ : ℂ) - ↑(-(n + 1 : ℤ))‖ = (n : ℝ) + 1 + ϑ := by
            rw [show (ϑ : ℂ) - ↑(-(n + 1 : ℤ)) = ↑((n : ℝ) + 1 + ϑ) by push_cast; ring]
            rw [Complex.norm_real, Real.norm_eq_abs]
            apply abs_of_pos
            have : -1 < ϑ ∧ ϑ < 1 := abs_lt.mp hϑ_lt
            have : (1 : ℝ) ≤ n := by exact_mod_cast hn
            linarith
          rw [h_eq]
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          apply pow_le_pow_left₀
          · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
            have : -1 < ϑ ∧ ϑ < 1 := abs_lt.mp hϑ_lt
            linarith
          · have : -1 < ϑ ∧ ϑ < 1 := abs_lt.mp hϑ_lt
            linarith
      exact Summable.of_nat_of_neg_add_one h_nat h_neg
    have hC : (↑π : ℂ) ^ 2 / Complex.sin (↑π * ↑ϑ) ^ 2 =
        1 / (↑ϑ : ℂ) ^ 2 +
        ∑' n : ℕ, (1 / ((↑n + 1 - (↑ϑ : ℂ)) ^ 2) + 1 / ((↑n + 1 + (↑ϑ : ℂ)) ^ 2)) := by
      rw [hweier, tsum_int_eq_zero_add_tsum_pnat hZ_summable]
      simp only [Int.cast_zero, sub_zero]
      rw [add_assoc, add_left_cancel_iff]
      have hpos : ∑' (n : ℕ+), (1 : ℂ) / ((ϑ : ℂ) - ↑(↑↑n : ℤ)) ^ 2 =
          ∑' (n : ℕ), 1 / ((↑n + 1 - (ϑ : ℂ)) ^ 2) := by
        rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
        congr 1; ext n
        simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Int.cast_add,
          Int.cast_natCast, Int.cast_one, one_div, inv_inj]
        ring
      have hneg : ∑' (n : ℕ+), (1 : ℂ) / ((ϑ : ℂ) - ↑(-(↑↑n : ℤ))) ^ 2 =
          ∑' (n : ℕ), 1 / ((↑n + 1 + (ϑ : ℂ)) ^ 2) := by
        rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
        congr 1; ext n
        simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add_rev,
          Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one, Int.cast_natCast, one_div,
          inv_inj]
        ring
      have hsum1 : Summable (fun n : ℕ => (1 : ℂ) / ((↑n + 1 - (ϑ : ℂ)) ^ 2)) := by
        have h := hZ_summable.comp_injective
          (i := fun n : ℕ => (↑n + 1 : ℤ))
          (fun a b hab => by simpa using hab)
        refine h.congr (fun n => ?_)
        simp only [Function.comp]
        push_cast; ring
      have hsum2 : Summable (fun n : ℕ => (1 : ℂ) / ((↑n + 1 + (ϑ : ℂ)) ^ 2)) := by
        have h := hZ_summable.comp_injective
          (i := fun n : ℕ => -(↑n + 1 : ℤ))
          (fun a b hab => by simpa using hab)
        refine h.congr (fun n => ?_)
        simp only [Function.comp]
        push_cast; ring
      rw [hpos, hneg, ← Summable.tsum_add hsum1 hsum2]
    symm
    apply Complex.ofReal_inj.mp
    calc ((π ^ 2 / Real.sin (π * ϑ) ^ 2 - 1 / ϑ ^ 2 : ℝ) : ℂ)
      _ = (π : ℂ) ^ 2 / Complex.sin (π * ϑ) ^ 2 - 1 / (ϑ : ℂ) ^ 2 := by push_cast; rfl
      _ = 1 / (ϑ : ℂ) ^ 2 + ∑' (n : ℕ), (1 / ((n : ℂ) + 1 - (ϑ : ℂ)) ^ 2 + 1 / ((n : ℂ) + 1 + (ϑ : ℂ)) ^ 2) - 1 / (ϑ : ℂ) ^ 2 := by rw [hC]
      _ = ∑' (n : ℕ), (1 / ((n : ℂ) + 1 - (ϑ : ℂ)) ^ 2 + 1 / ((n : ℂ) + 1 + (ϑ : ℂ)) ^ 2) := by ring
      _ = (↑(∑' n : ℕ, (1 / (n + 1 - ϑ) ^ 2 + 1 / (n + 1 + ϑ) ^ 2 : ℝ)) : ℂ) := by rw [Complex.ofReal_tsum]; push_cast; rfl

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
\leq |\vartheta|\cdot \left(\frac{1}{(1-|\vartheta|)^3} + 2\zeta(3)-1\right).
\]
If $\vartheta=0$, then
$\sum_n \left(\frac{\sigma}{(n-\vartheta)^2} + \frac{\sigma}{(n+\vartheta)^2}\right)
= 2 \sigma \sum_{n=1}^\infty \frac{1}{n^2} = \sigma \frac{\pi^2}{3}$.
-/)
  (latexEnv := "lemma")
  (discussion := 572)]
theorem lemma_abadsumas {s : ℂ} (hsigma : 0 ≤ s.re) {a b : ℝ} (ha : 0 < a)
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
    Summable (fun n : ℕ ↦ FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ))) ∧
    ∃ E : ℂ, ∑' n : ℕ, (FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ))) =
      ((a ^ (-s) : ℂ) * g ϑ) / (2 * I) - ((b ^ (-s) : ℂ) * g ϑ_minus) / (2 * I) + E ∧
      ‖E‖ ≤ C / a ^ (s.re + 1) := by
  intro ϑ ϑ_minus f g C
  have h_im_bound : |s.im| < 2 * π * a := by
    have hpos : 0 < 2 * π := by positivity
    rw [gt_iff_lt, div_lt_iff₀ hpos] at haτ
    linarith [mul_comm a (2 * π)]
  have apply_applem : ∀ n : ℕ, ∃ E_n : ℂ,
    FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ)) =
    (↑a ^ (-s) / (2 * ↑π * I)) * ((-1 : ℂ) ^ (n + 2) * 2 * ↑ϑ / ((↑n + 1) ^ 2 - ↑ϑ ^ 2)) -
    (↑b ^ (-s) / (2 * ↑π * I)) * ((-1 : ℂ) ^ (n + 2) * 2 * ↑ϑ_minus / ((↑n + 1) ^ 2 - ↑ϑ_minus ^ 2)) +
    E_n ∧ ‖E_n‖ ≤ a ^ (-(s.re + 1)) / (2 * π ^ 2) *
      (s.re / (↑n + 1 - ϑ) ^ 2 + s.re / (↑n + 1 + ϑ) ^ 2 +
       |ϑ| / |↑n + 1 - ϑ| ^ 3 + |ϑ| / |↑n + 1 + ϑ| ^ 3) := by
    intro n
    obtain ⟨E_prop, hE_eq, hE_bound⟩ :=
      proposition_applem s hsigma haτ hab ha' hb' (n := n + 1) (by omega)
    refine ⟨↑(a ^ (-(s.re + 1))) / (2 * π ^ 2) * E_prop, ?_, ?_⟩
    · have hconv : ∫ y in (a : ℝ)..b, (y : ℂ) ^ (-s) * ↑(Real.cos (2 * π * (↑n + 1) * y)) =
          ∫ y in Set.Icc a b, (↑y : ℂ) ^ (-s) * ↑(Real.cos (2 * π * ↑(n + 1) * y)) := by
        have h_le : a ≤ b := le_of_lt hab
        rw [intervalIntegral.integral_of_le h_le]
        rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
        congr 1
        ext y
        push_cast
        rfl
      rw [lemma_abadsumas_sum_fourier s ha hab, hconv, hE_eq]
      simp only [ϑ, ϑ_minus]
      rw [show (-1 : ℂ) ^ (n + 2) = -(-1) ^ (n + 1) by ring]
      push_cast; field_simp; ring_nf
    · have hpos : (0 : ℝ) ≤ a ^ (-(s.re + 1)) / (2 * π ^ 2) := by positivity
      rw [show ‖(Complex.ofReal (a ^ (-(s.re + 1))) / (2 * Complex.ofReal π ^ 2)) * E_prop‖ =
        a ^ (-(s.re + 1)) / (2 * π ^ 2) * ‖E_prop‖ by
          have hreal : Complex.ofReal (a ^ (-(s.re + 1))) / (2 * Complex.ofReal π ^ 2) =
              Complex.ofReal (a ^ (-(s.re + 1)) / (2 * π ^ 2)) := by
            rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
          rw [hreal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
      have hcast : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
      have hE_bound' : ‖E_prop‖ ≤
          s.re / (↑n + 1 - ϑ) ^ 2 + s.re / (↑n + 1 + ϑ) ^ 2 +
          |ϑ| / |↑n + 1 - ϑ| ^ 3 + |ϑ| / |↑n + 1 + ϑ| ^ 3 := by
        have hϑ : ϑ = s.im / (2 * π * a) := rfl
        simp only [hϑ, ← hcast]
        exact hE_bound
      exact mul_le_mul_of_nonneg_left hE_bound' hpos
  choose error_term error_term_eq error_term_bound using apply_applem
  have hϑ_lt : |ϑ| < 1 := by
    simp only [ϑ]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * π * a),
        div_lt_one (by positivity : (0:ℝ) < 2 * π * a)]
    have h2π : (0:ℝ) < 2 * π := by positivity
    have := haτ
    rw [gt_iff_lt, div_lt_iff₀ h2π] at this
    linarith [abs_nonneg s.im]
  have hsin_pos : ϑ ≠ 0 → 0 < Real.sin (π * ϑ) ^ 2 := by
    intro hϑ0
    apply sq_pos_of_ne_zero
    intro hsin
    rw [Real.sin_eq_zero_iff] at hsin
    obtain ⟨n, hn⟩ := hsin
    have hπ : π ≠ 0 := Real.pi_ne_zero
    have hϑn : ϑ = (n : ℝ) := by
      have := mul_left_cancel₀ hπ (by linarith : π * ϑ = π * n)
      linarith
    have hn_abs : |(n : ℝ)| < 1 := hϑn ▸ hϑ_lt
    have hn_zero : n = 0 := by
      have : |n| < 1 := by exact_mod_cast hn_abs
      rw [abs_lt] at this
      omega
    exact hϑ0 (by rw [hϑn]; exact_mod_cast hn_zero)
  have hre : ϑ ≠ 0 → (1 / Complex.sin (π * ϑ : ℂ) ^ 2).re = 1 / (Real.sin (π * ϑ) ^ 2) := by
    intro hϑ0
    have him : (Complex.sin (π * ϑ)).im = 0 := by exact_mod_cast Complex.sin_ofReal_im (π * ϑ)
    have hre_eq : (Complex.sin (π * ϑ)).re = Real.sin (π * ϑ) := by exact_mod_cast Complex.sin_ofReal_re (π * ϑ)
    have h_is_real : Complex.sin (π * ϑ) = ↑(Real.sin (π * ϑ)) :=
      Complex.ext hre_eq (by simp [him])
    rw [h_is_real]
    norm_num [Complex.ofReal_pow]
    field_simp
    rw [show (Complex.sin (π * ϑ) ^ 2).re = Real.sin (π * ϑ) ^ 2 by
          simp [sq, Complex.mul_re, him, hre_eq]]
    have h_normSq : normSq (Complex.sin (π * ϑ)) = Real.sin (π * ϑ) ^ 2 := by
      rw [h_is_real, Complex.normSq_ofReal]
      ring
    calc Real.sin (π * ϑ) ^ 2 / normSq (Complex.sin (↑π * ↑ϑ)) ^ 2
        = Real.sin (π * ϑ) ^ 2 / (Real.sin (π * ϑ) ^ 2) ^ 2 := by
            rw [h_normSq]
      _ = 1 / Real.sin (π * ϑ) ^ 2 := by
            field_simp [hsin_pos hϑ0]
  have main_summable_a : Summable (fun n : ℕ ↦
    ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2) : ℂ)) := lemma_abadsumas_summable_alternating_theta ϑ hϑ_lt
  have main_summable_b : Summable (fun n : ℕ ↦
    ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2) : ℂ)) := by
    apply lemma_abadsumas_summable_alternating_theta
    dsimp [ϑ_minus, ϑ] at hϑ_lt ⊢
    rw [abs_div]
    have hb_pos : 0 < b := lt_trans ha hab
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π * b),
        div_lt_one (by positivity)]
    nlinarith [Real.pi_pos, hab]
  have summable_term_a : Summable (fun n : ℕ ↦
    a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2))) :=
    main_summable_a.mul_left (a ^ (-s) / (2 * π * I))
  have summable_term_b : Summable (fun n : ℕ ↦
    b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2))) :=
    main_summable_b.mul_left (b ^ (-s) / (2 * π * I))
  have summable_diff : Summable (fun n : ℕ ↦
    a ^ (-s) / (2 * π * I) * ((-1 : ℂ) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) -
    b ^ (-s) / (2 * π * I) * ((-1 : ℂ) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2))) :=
    summable_term_a.sub summable_term_b
  have hpos_minus : ∀ n : ℕ, 0 < (n : ℝ) + 1 - ϑ := by
    intro n
    have := hϑ_lt
    have hϑ_le : ϑ ≤ |ϑ| := le_abs_self ϑ
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpos_plus : ∀ n : ℕ, 0 < (n : ℝ) + 1 + ϑ := by
    intro n
    have hϑ_le : -|ϑ| ≤ ϑ := neg_abs_le ϑ
    linarith [Nat.cast_nonneg (α := ℝ) n, hϑ_lt]
  have habs_minus : ∀ n : ℕ, |(n : ℝ) + 1 - ϑ| = (n : ℝ) + 1 - ϑ :=
    fun n => abs_of_pos (hpos_minus n)
  have habs_plus : ∀ n : ℕ, |(n : ℝ) + 1 + ϑ| = (n : ℝ) + 1 + ϑ :=
    fun n => abs_of_pos (hpos_plus n)
  have helper_summable {k : ℕ} (hk : 1 < k) (c : ℝ) (hc : |c| < 1) (hpos : ∀ n : ℕ, 0 < (n : ℝ) + 1 + c) :
      Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 + c) ^ k) := by
    apply Summable.of_norm_bounded_eventually (g := fun n : ℕ => 1 / (n : ℝ) ^ k)
    · exact Real.summable_one_div_nat_pow.mpr hk
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [norm_div, norm_one, norm_pow, norm_eq_abs, abs_of_pos (hpos n)]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      apply pow_le_pow_left₀ <;> linarith [abs_lt.mp hc]
  have hc_minus : |-ϑ| < 1 := by rwa [abs_neg]
  have hsumm_q : Summable fun n : ℕ => 1 / ((n : ℝ) + 1 - ϑ) ^ 2 + 1 / ((n : ℝ) + 1 + ϑ) ^ 2 :=
    (helper_summable (by norm_num) (-ϑ) hc_minus (fun n => by simpa using hpos_minus n)).add
      (helper_summable (by norm_num) ϑ hϑ_lt hpos_plus)
  have hsumm_c : Summable fun n : ℕ => 1 / ((n : ℝ) + 1 - ϑ) ^ 3 + 1 / ((n : ℝ) + 1 + ϑ) ^ 3 :=
    (helper_summable (by norm_num) (-ϑ) hc_minus (fun n => by simpa using hpos_minus n)).add
      (helper_summable (by norm_num) ϑ hϑ_lt hpos_plus)
  have sum_main_term_a : ∑' n : ℕ,
    ((-1 : ℂ) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) = π * g ϑ := lemma_abadsumas_sum_main_term_a ϑ hϑ_lt hpos_minus hpos_plus
  have hϑ_minus_lt : |ϑ_minus| < 1 := by
    dsimp [ϑ_minus]
    rw [abs_div]
    have hb_pos : 0 < b := lt_trans ha hab
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π * b),
        div_lt_one (by positivity)]
    nlinarith [Real.pi_pos, hab]
  have sum_main_term_b : ∑' n : ℕ,
    ((-1 : ℂ) ^ (n + 2) * 2 * ϑ_minus / ((n + 1 : ℂ) ^ 2 - ϑ_minus ^ 2)) = π * g ϑ_minus := lemma_abadsumas_sum_main_term_b ϑ_minus hϑ_minus_lt
  let bound : ℕ → ℝ := fun n =>
    a ^ (-(s.re + 1)) / (2 * π ^ 2) *
      (s.re / (n + 1 - ϑ) ^ 2 + s.re / (n + 1 + ϑ) ^ 2 +
      |ϑ| / |n + 1 - ϑ| ^ 3 + |ϑ| / |n + 1 + ϑ| ^ 3)
  have hbound_summable : Summable bound := by
    simp_rw [bound, habs_minus, habs_plus]
    apply Summable.mul_left
    apply ((hsumm_q.mul_left s.re).add (hsumm_c.mul_left |ϑ|)).congr
    intro n
    ring
  have error_summable : Summable error_term := Summable.of_norm_bounded hbound_summable error_term_bound
  have fourier_decomp : (fun n : ℕ ↦ FourierTransform.fourier f (n + 1) +
    FourierTransform.fourier f (-↑(n + 1 : ℤ))) =
    (fun n : ℕ ↦ a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) -
      b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2)) +
      error_term n) := funext error_term_eq
  constructor
  · rw [fourier_decomp]
    exact summable_diff.add error_summable
  · use ∑' n : ℕ, error_term n
    constructor
    · have factor_const_a : ∑' (n : ℕ),
        a ^ (-s) / (2 * π * I) * ((-1 : ℂ) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) =
        a ^ (-s) / (2 * π * I) * ∑' (n : ℕ), ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1 : ℂ) ^ 2 - ϑ ^ 2)) :=
        main_summable_a.tsum_mul_left (a ^ (-s) / (2 * π * I))
      have factor_const_b : ∑' (n : ℕ),
        b ^ (-s) / (2 * π * I) * ((-1 : ℂ) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2)) =
        b ^ (-s) / (2 * π * I) * ∑' (n : ℕ), ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1 : ℂ) ^ 2 - ϑ_minus ^ 2)) :=
        main_summable_b.tsum_mul_left (b ^ (-s) / (2 * π * I))
      have algebra_simp : ∀ (z : ℂ) (w : ℂ), z / (2 * π * I) * (π * w) = z * w / (2 * I) := by
        intro z w; ring_nf; field_simp
      calc ∑' (n : ℕ), (FourierTransform.fourier f (n + 1) + FourierTransform.fourier f  (-↑(n + 1 : ℤ)))
          = ∑' (n : ℕ), (a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) -
            b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2)) +
            error_term n) := by
            exact congr_arg tsum fourier_decomp
        _ = ∑' (n : ℕ), (a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1) ^ 2 - ϑ ^ 2)) -
            b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1) ^ 2 - ϑ_minus ^ 2))) +
            ∑' (n : ℕ), error_term n := by
            rw [Summable.tsum_add]
            · apply Summable.sub summable_term_a summable_term_b
            · exact error_summable
        _ = ∑' (n : ℕ), a ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1 : ℂ) ^ 2 - ϑ ^ 2)) -
            ∑' (n : ℕ), b ^ (-s) / (2 * π * I) * ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1 : ℂ) ^ 2 - ϑ_minus ^ 2)) +
            ∑' (n : ℕ), error_term n := by
            rw [Summable.tsum_sub summable_term_a summable_term_b]
        _ = a ^ (-s) / (2 * π * I) * ∑' (n : ℕ), ((-1) ^ (n + 2) * 2 * ϑ / ((n + 1 : ℂ) ^ 2 - ϑ ^ 2)) -
            b ^ (-s) / (2 * π * I) * ∑' (n : ℕ), ((-1) ^ (n + 2) * 2 * ϑ_minus / ((n + 1 : ℂ) ^ 2 - ϑ_minus ^ 2)) +
            ∑' (n : ℕ), error_term n := by
            rw [factor_const_a, factor_const_b]
        _ = a ^ (-s) / (2 * π * I) * (π * g ϑ) -
            b ^ (-s) / (2 * π * I) * (π * g ϑ_minus) +
            ∑' (n : ℕ), error_term n := by
            rw [sum_main_term_a, sum_main_term_b]
        _ = a ^ (-s) * g ϑ / (2 * I) - b ^ (-s) * g ϑ_minus / (2 * I) + ∑' (n : ℕ), error_term n := by
            rw [algebra_simp (a ^ (-s)) (g ϑ), algebra_simp (b ^ (-s)) (g ϑ_minus)]
    · have hquad : ∑' n : ℕ, (1 / (n + 1 - ϑ)^2 + 1/(n + 1 + ϑ)^2) =
          if ϑ = 0 then π^2/3
          else π^2 / Real.sin (π * ϑ)^2 - 1/ϑ^2 := lemma_abadsumas_quad ha haτ
      have hcubic : ∑' n : ℕ, (1/(n + 1 - ϑ)^3 + 1/(n + 1 + ϑ)^3) ≤
          1/(1-|ϑ|)^3 + 2*(riemannZeta 3).re - 1 :=
        lemma_abadimpseri ϑ hϑ_lt
      have hbound_le_half : ∑' n : ℕ, bound n ≤ (C / a ^ (s.re + 1)) := by
        simp only [bound, C]
        have hfactor : ∑' n : ℕ, bound n =
            a ^ (-(s.re + 1)) / (2 * π ^ 2) *
            (s.re * ∑' n : ℕ, (1/(n + 1 - ϑ)^2 + 1/(n + 1 + ϑ)^2) +
            |ϑ|  * ∑' n : ℕ, (1/(n + 1 - ϑ)^3 + 1/(n + 1 + ϑ)^3)) := by
          simp_rw [bound]
          simp_rw [fun n => habs_minus n, fun n => habs_plus n]
          rw [← tsum_mul_left]
          have hsplit := (hsumm_q.mul_left s.re).tsum_add (hsumm_c.mul_left |ϑ|)
          simp_rw [show ∀ n : ℕ,
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (s.re / (n + 1 - ϑ) ^ 2 + s.re / (n + 1 + ϑ) ^ 2 +
                 |ϑ| / (n + 1 - ϑ) ^ 3 + |ϑ| / (n + 1 + ϑ) ^ 3) =
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (s.re * (1 / (n + 1 - ϑ) ^ 2 + 1 / (n + 1 + ϑ) ^ 2) +
                 |ϑ| * (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3))
            from fun n => by ring]
          rw [tsum_mul_left, hsplit, tsum_mul_left, tsum_mul_left]
        rw [hfactor]
        rcases eq_or_ne ϑ 0 with hϑ0 | hϑ0
        · simp only [hϑ0, abs_zero, add_zero, ne_eq, not_true, if_false]
          rw [show 0 = ϑ from hϑ0.symm]
          simp only [neg_add_rev, hϑ0, sub_zero, one_div, zero_mul, add_zero, ge_iff_le]
          have hq : ∑' (n : ℕ), (1 / (↑n + 1 : ℝ) ^ 2 + 1 / (↑n + 1 : ℝ) ^ 2) = π ^ 2 / 3 := by
            simp only [hϑ0, sub_zero, add_zero, if_true] at hquad
            exact hquad
          have hq' : ∑' (n : ℕ), (((↑n + 1 : ℝ) ^ 2)⁻¹ + ((↑n + 1 : ℝ) ^ 2)⁻¹) = π ^ 2 / 3 := by
            convert hq using 3
            simp only [one_div]
          have hexp : a ^ (-1 + -s.re) = a ^ (-(s.re + 1)) := by
            congr 1; ring
          rw [hq', hexp]
          have hpos_a : (0 : ℝ) < a ^ (s.re + 1) := by positivity
          rw [Real.rpow_neg (le_of_lt ha) _]
          have hpi2 : (0 : ℝ) < π ^ 2 := by positivity
          field_simp
          nlinarith [hsigma, hpos_a, hpi2]
        · have hquad' : ∑' n : ℕ, (1/(n+1-ϑ)^2 + 1/((n+1+ϑ)^2)) =
              π^2 / Real.sin (π * ϑ)^2 - 1/ϑ^2 := by
            rw [hquad]; simp [hϑ0]
          rw [hquad']
          simp only [hϑ0, ne_eq, not_false_eq_true, if_true]
          have hre2 : (1 / ((π : ℂ) * (ϑ : ℂ)) ^ 2).re = 1 / (π * ϑ) ^ 2 := by
            have h : ((1 : ℂ) / ((π : ℂ) * (ϑ : ℂ)) ^ 2) = ((1 / (π * ϑ) ^ 2 : ℝ) : ℂ) := by
              push_cast; ring
            simpa only [Complex.ofReal_re] using congr_arg Complex.re h
          rw [hre hϑ0, hre2]
          have hrpow : a ^ (-(s.re + 1)) = (a ^ (s.re + 1))⁻¹ := Real.rpow_neg (le_of_lt ha) _
          have hquad_cancel :
              a ^ (-(s.re + 1)) / (2 * π ^ 2) * (s.re * (π ^ 2 / Real.sin (π * ϑ) ^ 2 - 1 / ϑ ^ 2))
              = (s.re / 2 * (1 / Real.sin (π * ϑ) ^ 2 - 1 / (π * ϑ) ^ 2)) / a ^ (s.re + 1) := by
            rw [hrpow]; field_simp
          have hS3_le :
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (|ϑ| * ∑' (n : ℕ), (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3))
              ≤ a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (|ϑ| * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hcubic (abs_nonneg ϑ)
          have hrhs_eq :
                ((s.re / 2 * (1 / Real.sin (π * ϑ) ^ 2 - 1 / (π * ϑ) ^ 2) +
                    |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)) /
                  a ^ (s.re + 1)) =
              (s.re / 2 * (1 / Real.sin (π * ϑ) ^ 2 - 1 / (π * ϑ) ^ 2)) / a ^ (s.re + 1) +
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (|ϑ| * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)) := by
            rw [hrpow]; ring
          have hgoal_expand :
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (s.re * (π ^ 2 / Real.sin (π * ϑ) ^ 2 - 1 / ϑ ^ 2) +
                  |ϑ| * ∑' (n : ℕ), (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3)) =
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (s.re * (π ^ 2 / Real.sin (π * ϑ) ^ 2 - 1 / ϑ ^ 2)) +
              a ^ (-(s.re + 1)) / (2 * π ^ 2) *
                (|ϑ| * ∑' (n : ℕ), (1 / (n + 1 - ϑ) ^ 3 + 1 / (n + 1 + ϑ) ^ 3)) := by
            ring
          linarith [hgoal_expand, hS3_le, hquad_cancel, hrhs_eq]
      have error_abs_summable : Summable (fun n ↦ ‖error_term n‖) :=
        Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) error_term_bound hbound_summable
      exact (norm_tsum_le_tsum_norm error_abs_summable).trans
        ((Summable.tsum_le_tsum error_term_bound error_abs_summable hbound_summable).trans
        hbound_le_half)

noncomputable def dadaro_g (t : ℝ) : ℂ :=
  if t ≠ 0 then (1 / Complex.sin (π * t) - 1 / (π * t)) / (2 * I) else 0

lemma proposition_dadaro_b_tendsto_zero_atTop {s : ℂ} (hsigma : 0 < s.re) : Tendsto
  (fun b : ℝ => (b : ℂ) ^ (-s) * dadaro_g (s.im / (2 * π * b)))
  atTop (𝓝 0) := by
  have h_pow_vanishes : Tendsto (fun b : ℝ => (b : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : (fun b : ℝ ↦ ‖(b : ℂ) ^ (-s)‖) =ᶠ[atTop] (fun b ↦ b ^ (-s.re)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with b hb
      simp [Complex.norm_cpow_eq_rpow_re_of_pos hb]
    exact (tendsto_congr' this).mpr (tendsto_rpow_neg_atTop hsigma)
  let g := dadaro_g
  have hne : ∀ᶠ x in 𝓝[≠] (0 : ℂ), x ≠ 0 :=
    eventually_nhdsWithin_of_forall fun x hx => hx
  have hsin : ∀ᶠ x in 𝓝[≠] (0 : ℂ), Complex.sin x ≠ 0 := by
    have hball : ∀ᶠ x in 𝓝[≠] (0 : ℂ), ‖x‖ < π := by
      apply eventually_nhdsWithin_of_eventually_nhds
      exact eventually_nhds_iff.mpr
        ⟨Metric.ball 0 π,
        fun y hy => by simpa [Metric.mem_ball, dist_zero_right] using hy,
        Metric.isOpen_ball,
        Metric.mem_ball_self (by positivity)⟩
    filter_upwards [hball, hne] with x hlt hxne
    rw [Complex.sin_ne_zero_iff]
    intro k
    by_cases hk : k = 0
    · simp [hk, hxne]
    · have hkπ : π ≤ ‖(k : ℂ) * ↑π‖ := by
        rw [norm_mul]
        suffices 1 ≤ ‖(k : ℂ)‖ by
          nth_rw 1 [← one_mul π]
          gcongr
          simp only [norm_real, norm_eq_abs]
          exact le_abs_self π
        simp only [norm_intCast]
        exact_mod_cast Int.one_le_abs hk
      intro heq
      linarith [heq ▸ hlt]
  have hl : (fun x ↦ 1 / Complex.sin x - 1 / x) =ᶠ[𝓝[≠] 0] (fun x ↦ (x - Complex.sin x) / (x * Complex.sin x)) := by
    filter_upwards [hsin, hne] with x hsinx hxne
    field_simp [hxne, hsinx]
  have hscale : Tendsto (fun t : ℝ ↦ (↑π * ↑t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const.mul Complex.continuous_ofReal).tendsto (0 : ℝ)
  have h_pi : Tendsto (fun t : ℝ ↦ (↑π * ↑t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_nhdsWithin_of_tendsto_nhds hscale
    · apply eventually_nhdsWithin_of_forall
      exact fun t ht ↦ mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (Complex.ofReal_ne_zero.mpr ht)
  have h2 : Tendsto (fun x ↦ x / Complex.sin x) (𝓝[≠] 0) (𝓝 1) := by
    have heq : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℂ)) Complex.sin id := by
      unfold Asymptotics.IsEquivalent
      exact Complex.isEquivalent_sin.isLittleO.mono nhdsWithin_le_nhds
    have hsinx : Tendsto (fun x ↦ Complex.sin x / x) (𝓝[≠] 0) (𝓝 1) :=
      (Asymptotics.isEquivalent_iff_tendsto_one hne).mp heq
    have hflip : (fun x ↦ x / Complex.sin x) =ᶠ[𝓝[≠] (0 : ℂ)] (fun x ↦ (Complex.sin x / x)⁻¹) := by
      filter_upwards [hsin, hne] with x hsx hxne
      field_simp [hxne, hsx]
    rw [tendsto_congr' hflip]
    simpa using hsinx.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hfactor : (fun x : ℂ ↦ (x - Complex.sin x) / (x * Complex.sin x))
      =ᶠ[𝓝[≠] 0] (fun x ↦ (x - Complex.sin x) / x ^ 2 * (x / Complex.sin x)) := by
    filter_upwards [hsin, hne]
      with x hsx hxne
    field_simp [hxne, hsx]
  have hquot : Tendsto (fun x : ℂ ↦ (x - Complex.sin x) / x ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hkey : ∀ x : ℂ, x ≠ 0 → ‖x‖ ≤ 1 →
        ‖(x - Complex.sin x) / x ^ 2‖ ≤ ‖x‖ / 6 + ‖x‖ ^ 2 * (5 / 96) := by
      intro x hx hxn
      have hbound := sin_bound hxn
      have hxnorm : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      rw [norm_div, norm_pow, div_le_iff₀ hxnorm]
      have htri : ‖x - Complex.sin x‖ ≤ ‖x‖ ^ 3 / 6 + ‖x‖ ^ 4 * (5 / 96) := by
        have : ‖x - Complex.sin x‖ ≤ ‖x ^ 3 / 6‖ + ‖x ^ 3 / 6 - (x - Complex.sin x)‖ :=
          calc ‖x - Complex.sin x‖
            = ‖x ^ 3 / 6 - (x ^ 3 / 6 - (x - Complex.sin x))‖ := by ring_nf
          _ ≤ ‖x ^ 3 / 6‖ + ‖x ^ 3 / 6 - (x - Complex.sin x)‖ := norm_sub_le _ _
        have h1 : ‖x ^ 3 / 6‖ = ‖x‖ ^ 3 / 6 := by
          rw [norm_div, norm_pow]; norm_num
        have h2 : ‖x ^ 3 / 6 - (x - Complex.sin x)‖ ≤ ‖x‖ ^ 4 * (5 / 96) := by
          have heq : x ^ 3 / 6 - (x - Complex.sin x) = Complex.sin x - (x - x ^ 3 / 6) := by ring
          exact heq ▸ hbound
        linarith
      linarith [htri]
    have hsqueeze : Tendsto (fun x : ℂ ↦ ‖x‖ / 6 + ‖x‖ ^ 2 * (5 / 96)) (𝓝[≠] 0) (𝓝 0) := by
      rw [show (0 : ℝ) = 0 / 6 + 0 ^ 2 * (5 / 96) by norm_num]
      apply Filter.Tendsto.add
      · apply Tendsto.div_const
        refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        exact tendsto_norm_zero
      · apply Filter.Tendsto.mul_const
        exact tendsto_nhdsWithin_of_tendsto_nhds (by
          simpa [norm_zero] using (continuous_norm.pow 2).tendsto (0 : ℂ))
    apply squeeze_zero_norm' _ hsqueeze
    rw [eventually_nhdsWithin_iff]
    apply eventually_of_mem (Metric.ball_mem_nhds 0 one_pos)
    intro x hx hne
    apply hkey x hne
    simp only [Metric.mem_ball, dist_zero_right] at hx
    exact le_of_lt hx
  have h_f_lim : Tendsto (fun x : ℂ ↦ 1 / Complex.sin x - 1 / x) (𝓝[≠] 0) (𝓝 0) := by
    have hprod : Tendsto (fun x : ℂ ↦ (x - Complex.sin x) / x ^ 2 * (x / Complex.sin x))
        (𝓝[≠] 0) (𝓝 0) := by simpa using hquot.mul h2
    exact (hprod.congr' hfactor.symm).congr' hl.symm
  have h_f_lim_new : Tendsto (fun x : ℂ ↦ 1 / Complex.sin x - 1 / x) (𝓝 0) (𝓝 0) := by
    have h0 : (fun x : ℂ ↦ 1 / Complex.sin x - 1 / x) 0 = 0 := by
      simp [Complex.sin_zero]
    rw [← nhdsWithin_univ]
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simp only [nhdsWithin_univ]
      have hc : ContinuousAt (fun x ↦ 1 / Complex.sin x - 1 / x) 0 := by
        rw [continuousAt_iff_punctured_nhds]
        simp only [h0]
        exact h_f_lim
      simpa only [h0] using hc.tendsto
    · exact Filter.Eventually.of_forall (fun x => trivial)
  have h_g_limit : Tendsto g (𝓝 0) (𝓝 0) := by
    have hg_eq : g =ᶠ[𝓝 0] fun t : ℝ =>
        (1 / Complex.sin (↑π * ↑t) - 1 / (↑π * ↑t)) / (2 * I) := by
      exact Filter.Eventually.of_forall fun t ↦ by
        simp only [g, dadaro_g]
        split_ifs with ht
        · rfl
        · simp only [one_div, mul_inv_rev]
          field_simp
          push_neg at ht
          simp [ht]
    have hcomp : Tendsto (fun t : ℝ =>
        1 / Complex.sin (↑π * ↑t) - 1 / (↑π * ↑t)) (𝓝 0) (𝓝 0) :=
      h_f_lim_new.comp hscale
    have hdiv : Tendsto (fun t : ℝ =>
        (1 / Complex.sin (↑π * ↑t) - 1 / (↑π * ↑t)) / (2 * I)) (𝓝 0) (𝓝 0) := by
      simpa using hcomp.div_const (2 * I)
    exact hdiv.congr' hg_eq.symm
  have h_arg_limit : Tendsto (fun b : ℝ ↦ s.im / (2 * π * b)) atTop (𝓝 0) := by
    apply Filter.Tendsto.const_div_atTop
    apply (tendsto_const_mul_atTop_of_pos ?_).mpr tendsto_id
    exact mul_pos two_pos pi_pos
  have h_trig_vanishes : Tendsto (fun b : ℝ ↦ g (s.im / (2 * π * b))) atTop (𝓝 0) :=
    h_g_limit.comp h_arg_limit
  simpa using h_pow_vanishes.mul h_trig_vanishes

lemma proposition_dadaro_zero_lt {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 < s.re) {a : ℝ} (ha : 0 < a)
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
      ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
      (a ^ (1 - s) : ℂ) / (1 - s) - c * (a ^ (-s) : ℂ) + E ∧
      ‖E‖ ≤ C / (a ^ (s.re + 1 : ℝ)) := by
  intro ϑ C c
  let B := {b : ℝ | b.IsHalfInteger ∧ b > a}
  let g := dadaro_g
  have h_b_term_vanishes : Tendsto
      (fun b : ℝ => (b : ℂ) ^ (-s) * dadaro_g (s.im / (2 * π * b)))
      atTop (𝓝 0) := proposition_dadaro_b_tendsto_zero_atTop hsigma
  have h_for_each_b : ∀ b ∈ B, ∃ E₁ E₂ : ℂ,
      ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        riemannZeta s + (a : ℂ) ^ (1 - s) / (1 - s) -
        (a : ℂ) ^ (-s) * g ϑ +
        ((b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) - E₁ + E₂) ∧
      ‖E₁‖ ≤ C / a ^ (s.re + 1) ∧
      ‖E₂‖ ≤ 2 * ‖s‖ / (s.re * b ^ s.re) := by
    intro b hb
    obtain ⟨hb_half, hb_gt⟩ := hb
    obtain ⟨E_zeta, h_step1, h_E_zeta_bd⟩ :=
      lemma_abadtoabsum ha hb_half hb_gt hs1 hsigma
    obtain ⟨L, _hL_tendsto, hL_eq⟩ :=
      lemma_abadusepoisson ha'.not_isInteger hb_half.not_isInteger hb_gt ha hs1
    have h_combined : ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        riemannZeta s + (a : ℂ) ^ (1 - s) / (1 - s) - L + E_zeta := by
      rw [h_step1, hL_eq]; ring
    obtain ⟨E₁, hL_decomp, hE₁_bd⟩ : ∃ E₁ : ℂ,
        L = (a : ℂ) ^ (-s) * g ϑ -
            (b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) + E₁ ∧
        ‖E₁‖ ≤ C / a ^ (s.re + 1) := by
      refine ⟨L - (a : ℂ)^(-s) * g ϑ + (b : ℂ)^(-s) * g (s.im / (2 * π * b)), ?_, ?_⟩
      · ring
      · have h_fourier_ioc_bound :
            ‖L - (a : ℂ)^(-s) * g ϑ + (b : ℂ)^(-s) * g (s.im / (2 * π * b))‖
            ≤ C / a ^ (s.re + 1) := by
          obtain ⟨h_sum, E, h_E_eq, h_E_bd⟩ := lemma_abadsumas hsigma.le ha hb_gt ha' hb_half haτ
          have hL_eq : L = (a : ℂ)^(-s) * g ϑ - (b : ℂ)^(-s) * g (s.im / (2 * π * b)) + E := by
            let f : ℝ → ℂ := fun y ↦ if a ≤ y ∧ y ≤ b then ↑(y ^ (-s.re)) * e (-(s.im / (2 * π)) * Real.log y) else 0
            have hL_tsum : L = ∑' n : ℕ, (FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ))) := by
              apply tendsto_nhds_unique _hL_tendsto
              have h_eq : (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N,
                  (FourierTransform.fourier f ↑n + FourierTransform.fourier f (-↑n))) =ᶠ[atTop]
                  fun N ↦ ∑ n ∈ Finset.range N,
                  (FourierTransform.fourier f (n + 1) + FourierTransform.fourier f (-(n + 1 : ℤ))) := by
                apply Filter.Eventually.of_forall
                intro N
                apply Finset.sum_nbij (fun n => n - 1)
                · intro a ha
                  simp [Finset.mem_range, Finset.mem_Icc] at *
                  omega
                · intro n₁ a n₂ b h
                  simp only [] at h
                  simp only [Finset.coe_Icc, Set.mem_Icc] at a b
                  omega
                · intro n hn
                  simp only [Finset.coe_Icc, Finset.mem_coe, Finset.mem_range] at *
                  simp only [Set.mem_image, Set.mem_Icc]
                  exact ⟨n + 1, by omega, by omega⟩
                · intro n hn
                  simp only [Finset.mem_Icc] at hn
                  have : n = (n - 1) + 1 := (Nat.sub_add_cancel hn.1).symm
                  congr 1
                  · norm_cast
                    rw [this]
                    simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
                  · rw [this]
                    norm_cast
              exact h_sum.hasSum.tendsto_sum_nat.congr' h_eq.symm
            have hg_unfold : ∀ t : ℝ, g t =
                (fun t : ℝ ↦ if t ≠ 0 then (1 / Complex.sin (↑π * ↑t) : ℂ) - 1 / (↑π * ↑t) else 0) t / (2 * I) := by
              intro t
              simp only [g, dadaro_g]
              split_ifs with ht
              · rfl
              · simp
            rw [hL_tsum, h_E_eq]
            simp only [hg_unfold]
            have hϑ_def : ϑ = s.im / (2 * π * a) := rfl
            rw [hϑ_def]
            ring_nf
          have hE_eq : L - (a : ℂ)^(-s) * g ϑ + (b : ℂ)^(-s) * g (s.im / (2 * π * b)) = E := by
            rw [hL_eq]; ring
          rwa [hE_eq]
        linarith [h_fourier_ioc_bound]
    refine ⟨E₁, E_zeta, ?_, hE₁_bd, ?_⟩
    · rw [h_combined, hL_decomp]; ring
    · have hpos : (0 : ℝ) < s.re * b ^ s.re :=
        mul_pos hsigma (rpow_pos_of_pos (ha.trans hb_gt) s.re)
      calc ‖E_zeta‖
        _ ≤ ‖s‖ / (2 * s.re * b ^ s.re) := h_E_zeta_bd
        _ ≤ ‖s‖ / (s.re * b ^ s.re) := by
          apply div_le_div_of_nonneg_left (norm_nonneg s) (by positivity)
          linarith [hpos]
        _ ≤ 2 * ‖s‖ / (s.re * b ^ s.re) := by
          gcongr
          field_simp [hpos]
          linarith [norm_nonneg s]
  have h_E₂_vanishes : ∀ ε > 0, ∃ B₀ > a, B₀.IsHalfInteger ∧
      ∀ b, b.IsHalfInteger → b ≥ B₀ →
      (∃ E₂ : ℂ, ‖E₂‖ ≤ 2 * ‖s‖ / (s.re * b ^ s.re) ∧
            2 * ‖s‖ / (s.re * b ^ s.re) < ε) := by
    intro ε hε
    have h_limit : Tendsto (fun b : ℝ ↦ 2 * ‖s‖ / (s.re * b ^ s.re)) atTop (𝓝 0) := by
      have h_rw : (fun b : ℝ ↦ 2 * ‖s‖ / (s.re * b ^ s.re)) =ᶠ[atTop]
                  fun b : ℝ ↦ (2 * ‖s‖ / s.re) * b ^ (-s.re) := by
        filter_upwards [eventually_gt_atTop 0] with b hb
        rw [rpow_neg hb.le, div_mul_eq_div_div, div_eq_mul_one_div (2 * ‖s‖ / s.re)]
        field_simp
      refine (tendsto_congr' h_rw).mpr <| by
        rw [show (0 : ℝ) = (2 * ‖s‖ / s.re) * 0 by ring]
        exact Tendsto.const_mul _ (tendsto_rpow_neg_atTop hsigma)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_limit ε hε
    let M := max a N
    let B₀ : ℝ := ↑⌊M⌋ + 3 / 2
    use B₀
    refine ⟨?_, ?_, ?_⟩
    · have hM_a : M ≥ a := le_max_left a N
      have hB₀_M : B₀ > M := Real.floor_add_three_halfs_gt M
      linarith
    · exact Real.IsHalfInteger.floor_add_three_halfs M
    · intro b hb_hi hb_ge
      have hb_gt_a : b > a := by
        have hM_a : M ≥ a := le_max_left a N
        have hB₀_M : B₀ > M := Real.floor_add_three_halfs_gt M
        linarith
      have hb_in_B : b ∈ B := ⟨hb_hi, hb_gt_a⟩
      obtain ⟨_, E₂, _, _, hE₂_bd⟩ := h_for_each_b b hb_in_B
      use E₂
      refine ⟨hE₂_bd, ?_⟩
      have hb_ge_N : b ≥ N := by
        have hM_N : M ≥ N := le_max_right a N
        have hB₀_M : B₀ > M := Real.floor_add_three_halfs_gt M
        linarith
      have h_dist := hN b hb_ge_N
      rw [dist_zero_right] at h_dist
      have h_pos : 0 < 2 * ‖s‖ / (s.re * b ^ s.re) := by
        apply div_pos
        · have h_s_ne_zero : s ≠ 0 := by
            intro h
            rw [h] at hsigma
            simp at hsigma
          exact mul_pos zero_lt_two (norm_pos_iff.mpr h_s_ne_zero)
        · exact mul_pos hsigma (rpow_pos_of_pos (ha.trans hb_gt_a) _)
      have h_abs := _root_.abs_of_pos h_pos
      rw [Real.norm_eq_abs] at h_dist
      rwa [h_abs] at h_dist
  set c_a : ℂ := g (s.im / (2 * π * a))
  set c_b : ℝ → ℂ := fun b => g (s.im / (2 * π * b))
  set main_a : ℂ :=
    riemannZeta s + ↑a ^ (1 - s) / (1 - s) - ↑a ^ (-s) * c_a
  have h_E₁_exists : ∃ E₁ : ℂ, ‖E₁‖ ≤ C / a ^ (s.re + 1) ∧
      ∀ ε > 0, ∃ B₀ > a, B₀.IsHalfInteger ∧
      ∀ b : ℝ, b.IsHalfInteger → b ≥ B₀ →
      ∀ E₁_lem E₂_lem : ℂ,
      (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        main_a + (((b : ℂ) ^ (-s) * c_b b) - E₁_lem + E₂_lem)) →
      ‖E₂_lem + (E₁ - E₁_lem) +
        (b : ℂ) ^ (-s) * c_b b‖ < ε := by
    refine ⟨main_a - ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s), ?_, ?_⟩
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hε2 : ε / 2 > 0 := by linarith
      obtain ⟨B₁, hB₁_prop⟩ := Metric.tendsto_atTop.mp h_b_term_vanishes (ε / 2) hε2
      obtain ⟨B₂, _hB₂_gt, _hB₂_hi, hB₂_prop⟩ := h_E₂_vanishes (ε / 2) hε2
      let M := max (max a B₁) B₂
      let b : ℝ := ↑⌊M⌋ + 3 / 2
      have hb_hi : b.IsHalfInteger := Real.IsHalfInteger.floor_add_three_halfs M
      have hb_gt_a : b > a := by
        have : b > M := Real.floor_add_three_halfs_gt M
        exact lt_of_le_of_lt ((le_max_left a B₁).trans (le_max_left (max a B₁) B₂)) this
      have hb_ge_B₁ : b ≥ B₁ := by
        have : b > M := Real.floor_add_three_halfs_gt M
        exact ((le_max_right a B₁).trans (le_max_left (max a B₁) B₂)).trans this.le
      have hb_ge_B₂ : b ≥ B₂ := by
        have : b > M := Real.floor_add_three_halfs_gt M
        exact (le_max_right (max a B₁) B₂).trans this.le
      have hb_in_B : b ∈ B := ⟨hb_hi, hb_gt_a⟩
      obtain ⟨E₁_b, E₂_b, h_formula, hE₁_b_bd, hE₂_b_bd⟩ := h_for_each_b b hb_in_B
      have h_rearrange : main_a - ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
          E₁_b - ((b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) + E₂_b) := by
        rw [h_formula]; ring
      rw [h_rearrange]
      calc ‖E₁_b - ((b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) + E₂_b)‖
        _ ≤ ‖E₁_b‖ + ‖(b : ℂ) ^ (-s) * g (s.im / (2 * π * b)) + E₂_b‖ := norm_sub_le _ _
        _ ≤ C / a ^ (s.re + 1) + (‖(b : ℂ) ^ (-s) * g (s.im / (2 * π * b))‖ + ‖E₂_b‖) := by
          gcongr; exact norm_add_le _ _
        _ ≤ C / a ^ (s.re + 1) + (ε / 2 + ε / 2) := by
          gcongr
          · specialize hB₁_prop b hb_ge_B₁; rw [dist_zero_right] at hB₁_prop; exact hB₁_prop.le
          · obtain ⟨_, _, hE₂_bd_ε⟩ := hB₂_prop b hb_hi hb_ge_B₂; exact hE₂_b_bd.trans hE₂_bd_ε.le
        _ = C / a ^ (s.re + 1) + ε := by ring
    · intro ε hε
      obtain ⟨B₀, hB₀_gt, hB₀_hi, _⟩ := h_E₂_vanishes ε hε
      refine ⟨B₀, hB₀_gt, hB₀_hi, fun b _hb_hi _hb_ge E₁_lem E₂_lem hformula => ?_⟩
      have hcancel : E₂_lem + ((main_a - ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) - E₁_lem)
          + (b : ℂ) ^ (-s) * c_b b = 0 := by
        rw [hformula]
        ring
      rwa [hcancel, norm_zero]
  obtain ⟨E₁, hE₁_bound, hE₁_limit⟩ := h_E₁_exists
  use E₁
  let transient_error (b : ℝ) (E₂ : ℂ) : ℂ :=
    E₂ + (b : ℂ) ^ (-s) * g (s.im / (2 * π * b))
  have h_eq_for_large_b : ∀ ε > 0, ∃ B₀ > a, B₀.IsHalfInteger ∧
    ∀ b, b.IsHalfInteger → b ≥ B₀ →
    ∃ E₂ : ℂ,
      ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        riemannZeta s + (a : ℂ) ^ (1 - s) / (1 - s) + c * (a : ℂ) ^ (-s) +
        (-E₁ + transient_error b E₂) ∧
      ‖transient_error b E₂‖ < ε := by
    intro ε hε
    have hε2 : ε / 2 > 0 := by linarith
    obtain ⟨B₁, hB₁_gt, hB₁_hi, hB₁_prop⟩ := h_E₂_vanishes (ε / 2) hε2
    have hB₂_exists : ∃ B₂ : ℝ, B₂ > a ∧ B₂.IsHalfInteger ∧
        ∀ b : ℝ, b.IsHalfInteger → b ≥ B₂ →
          ‖(↑b : ℂ) ^ (-s) * dadaro_g (s.im / (2 * π * b))‖ < ε / 2 := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_b_term_vanishes (ε / 2) hε2
      let M := max a N
      let B₂ : ℝ := ↑⌊M⌋ + 3 / 2
      use B₂
      refine ⟨?_, ?_, ?_⟩
      · have hM_a : M ≥ a := le_max_left a N
        have hB₂_M : B₂ > M := Real.floor_add_three_halfs_gt M
        linarith
      · exact Real.IsHalfInteger.floor_add_three_halfs M
      · intro b _ hb_B₂
        have hb_N : b ≥ N := by
          have hM_N : M ≥ N := le_max_right a N
          have hB₂_M : B₂ > M := Real.floor_add_three_halfs_gt M
          linarith
        have h_dist := hN b hb_N
        rw [dist_zero_right] at h_dist
        exact h_dist
    obtain ⟨B₂, hB₂_gt, hB₂_hi, hB₂_prop⟩ := hB₂_exists
    obtain ⟨B₃, hB₃_gt, hB₃_hi, hB₃_prop⟩ := hE₁_limit ε hε
    obtain ⟨B₀, hB₀_gt, hB₀_hi, hB₀_ge₁, hB₀_ge₂, hB₀_ge₃⟩ :
      ∃ B₀ : ℝ,
        B₀ > a ∧
        B₀.IsHalfInteger ∧
        B₀ ≥ B₁ ∧
        B₀ ≥ B₂ ∧
        B₀ ≥ B₃ := by
      set M := max (max B₁ B₂) B₃
      set B₀ : ℝ := ↑⌊M⌋ + 3 / 2
      have hB₀M : B₀ > M := Real.floor_add_three_halfs_gt M
      refine ⟨B₀, ?_, ?_, ?_, ?_, ?_⟩
      · have hMa : M > a := by
          have h1 : M ≥ max B₁ B₂ := le_max_left (max B₁ B₂) B₃
          have h2 : max B₁ B₂ ≥ B₁ := le_max_left B₁ B₂
          linarith [h1, h2, hB₁_gt]
        linarith [hB₀M, hMa]
      · exact Real.IsHalfInteger.floor_add_three_halfs M
      · have hMa : M ≥ B₁ := le_trans (le_max_left B₁ B₂) (le_max_left _ _)
        linarith [hB₀M, hMa]
      · have hMa : M ≥ B₂ := le_trans (le_max_right B₁ B₂) (le_max_left _ _)
        linarith [hB₀M, hMa]
      · have hMa : M ≥ B₃ := le_max_right (max B₁ B₂) B₃
        linarith [hB₀M, hMa]
    refine ⟨B₀, hB₀_gt, hB₀_hi, fun b hb_hi hb_ge => ?_⟩
    have hb_gt_a : b > a := lt_of_lt_of_le hB₀_gt hb_ge
    have hb_in_B : b ∈ B := ⟨hb_hi, hb_gt_a⟩
    obtain ⟨E₁_lem, E₂_lem, hfb, _, _⟩ := h_for_each_b b hb_in_B
    have hfb_cb : ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) =
        main_a + (↑b ^ (-s) * c_b b - E₁_lem + E₂_lem) := by
      simp only [c_b, main_a, c_a] at *
      exact hfb
    have hmain : riemannZeta s + ↑a ^ (1 - s) / (1 - s) + c * ↑a ^ (-s) = main_a := by
      simp only [main_a, c_a, c, ϑ, g, dadaro_g] at *
      split_ifs with h
      · have h_sin : Complex.sin (↑π * ↑(s.im / (2 * π * a))) ≠ 0 := by
          set x := (↑π * ↑(s.im / (2 * π * a)) : ℂ)
          have hxnonzero : x ≠ 0 := by
            simp only [ofReal_div, ofReal_mul, ofReal_ofNat, ne_eq, mul_eq_zero, ofReal_eq_zero,
              pi_ne_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_self, ha.ne', or_false, false_or,
              x]
            exact (div_ne_zero_iff.mp h).1
          have hxbound : ‖x‖ < π := by
            calc ‖x‖
              _ = ‖(Real.pi : ℂ) * (s.im / (2 * Real.pi * a) : ℂ)‖ := by simp [x]
              _ = ‖(Real.pi : ℂ)‖ * ‖(s.im / (2 * Real.pi * a) : ℂ)‖ := by
                exact norm_mul (Real.pi : ℂ) (s.im / (2 * Real.pi * a) : ℂ)
              _ = Real.pi * (|s.im| / (2 * Real.pi * a)) := by
                have h1 : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos pi_pos]
                have h2 : ‖(s.im / (2 * Real.pi * a) : ℂ)‖ = |s.im| / (2 * Real.pi * a) := by
                  simp [abs_of_pos pi_pos, abs_of_pos ha]
                rw [h1, h2]
              _ = |s.im| / (2 * a) := by
                calc Real.pi * (|s.im| / (2 * Real.pi * a))
                  _ = (Real.pi * |s.im|) / (Real.pi * (2 * a)) := by ring
                  _ = |s.im| / (2 * a) := mul_div_mul_left _ _ pi_ne_zero
              _ < Real.pi := by
                rw [div_lt_iff₀ (by positivity)]
                have h4 : |s.im| / (2 * Real.pi) < a := haτ
                have h5 : |s.im| < a * (2 * Real.pi) := (div_lt_iff₀ (by positivity)).mp h4
                linarith
          rw [Complex.sin_ne_zero_iff]
          intro k
          by_cases hk : k = 0
          · simp [hk, hxnonzero]
          · have h_k_bound : π ≤ ‖(k : ℂ) * ↑π‖ := by
              rw [norm_mul]; simp only [norm_intCast, norm_real, norm_eq_abs]
              suffices 1 ≤ ‖(k : ℂ)‖ by
                have habs : 1 ≤ |( k : ℝ)| := by simpa [norm_eq_abs]
                have hpi  : |π| = π         := abs_of_pos Real.pi_pos
                rw [hpi]
                calc π = 1 * π       := (one_mul π).symm
                _ ≤ |(↑k)| * π := by
                  apply mul_le_mul_of_nonneg_right habs (le_of_lt Real.pi_pos)
              simp only [norm_intCast]
              norm_cast
              exact Int.one_le_abs hk
            intro heq
            linarith [heq ▸ hxbound]
        calc riemannZeta s + ↑a ^ (1 - s) / (1 - s) + (I / 2 * (1 / Complex.sin (↑π * ↑(s.im / (2 * π * a))) - 1 / (↑π * ↑(s.im / (2 * π * a))))) * ↑a ^ (-s)
          _ = riemannZeta s + ↑a ^ (1 - s) / (1 - s) - ((1 / Complex.sin (↑π * ↑(s.im / (2 * π * a))) - 1 / (↑π * ↑(s.im / (2 * π * a)))) / (2 * I)) * ↑a ^ (-s) := by
            field_simp [Complex.I_ne_zero, h_sin]
            ring_nf
            simp only [Complex.I_sq]
            ring
          _ = riemannZeta s + ↑a ^ (1 - s) / (1 - s)
          - ↑a ^ (-s) * ((1 / Complex.sin (↑π * ↑(s.im / (2 * π * a)))
              - 1 / (↑π * ↑(s.im / (2 * π * a)))) / (2 * I)) := by ring
          _ = _ := by
                simp only [ofReal_div, ofReal_mul, ofReal_ofNat, one_div, mul_inv_rev, inv_div]
      · simp only [zero_mul, add_zero, mul_zero, sub_zero]
    refine ⟨E₁ - E₁_lem + E₂_lem, ?_, ?_⟩
    · simp only [transient_error]
      have : -E₁ + (E₁ - E₁_lem + E₂_lem + ↑b ^ (-s) * c_b b) =
            ↑b ^ (-s) * c_b b - E₁_lem + E₂_lem := by ring
      rw [hmain, this]
      exact hfb_cb
    · have hnorm_eq : ‖transient_error b (E₁ - E₁_lem + E₂_lem)‖ =
          ‖E₂_lem + (E₁ - E₁_lem) + ↑b ^ (-s) * c_b b‖ := by
        simp only [transient_error, c_b]
        congr 1
        ring_nf
      rw [hnorm_eq]
      exact hB₃_prop b hb_hi (le_trans hB₀_ge₃ hb_ge) E₁_lem E₂_lem hfb_cb
  constructor
  · have h_dist_zero : ∀ ε > 0,
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
                       (a : ℂ) ^ (1 - s) / (1 - s) - c * (a : ℂ) ^ (-s) + E₁)‖ < ε := by
      intro ε hε
      obtain ⟨B₀, hB₀a, hB₀half, hforallb⟩ := h_eq_for_large_b ε hε
      obtain ⟨E₂, hEq, hTbound⟩ := hforallb B₀ hB₀half le_rfl
      rwa [show riemannZeta s -
            (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
              (a : ℂ) ^ (1 - s) / (1 - s) -
              c * (a : ℂ) ^ (-s) + E₁) =
          -(transient_error B₀ E₂) by linear_combination -hEq, norm_neg]
    apply eq_of_norm_sub_eq_zero
    rw [norm_eq_zero]
    apply eq_of_forall_dist_le
    intro ε hε
    rw [dist_zero_right]
    exact le_of_lt (h_dist_zero ε hε)
  · exact hE₁_bound

lemma proposition_dadaro_zero_eq {s : ℂ} (hs1 : s ≠ 1) (hsigma : 0 = s.re) {a : ℝ} (ha : 0 < a)
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
      ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
      (a ^ (1 - s) : ℂ) / (1 - s) - c * (a ^ (-s) : ℂ) + E ∧
      ‖E‖ ≤ C / (a ^ (s.re + 1 : ℝ)) := by
  intro ϑ C c
  have h_continuous_extension :
    ContinuousAt (fun σ : ℝ => riemannZeta (σ + I * s.im)) 0 ∧
    ContinuousAt (fun σ : ℝ => ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-(σ + I * s.im))) 0 ∧
    ContinuousAt (fun σ : ℝ => ↑a ^ (1 - (σ + I * s.im)) / (1 - (σ + I * s.im))) 0 ∧
    ContinuousAt (fun σ : ℝ => c * ↑a ^ (-(σ + I * s.im))) 0 := by
    have hs_zero : (↑(0 : ℝ) + I * ↑s.im : ℂ) = s := by
      apply Complex.ext <;> simp [hsigma.symm]
    repeat' constructor
    · rw [show (fun σ : ℝ ↦ riemannZeta (↑σ + I * ↑s.im))= riemannZeta ∘ (fun σ : ℝ ↦ ↑σ + I * ↑s.im)
        by ext σ; simp]
      apply ContinuousAt.comp (g := riemannZeta) (f := fun σ : ℝ ↦ ↑σ + I * ↑s.im)
      · exact hs_zero.symm ▸ (differentiableAt_riemannZeta hs1).continuousAt
      · fun_prop
    · apply tendsto_finset_sum
      intro i hi
      simp only [Finset.mem_Icc] at hi
      apply ContinuousAt.cpow
      · exact continuousAt_const
      · fun_prop
      · left; norm_cast
        linarith
    · apply ContinuousAt.div
      · apply ContinuousAt.cpow
        · exact continuousAt_const
        · fun_prop
        · left; norm_cast
      · fun_prop
      · exact hs_zero.symm ▸ sub_ne_zero.mpr hs1.symm
    · apply ContinuousAt.mul
      · exact continuousAt_const
      · apply ContinuousAt.cpow
        · exact continuousAt_const
        · fun_prop
        · left; norm_cast
  have h_nearby_approximation : ∀ σ ∈ Set.Ioo (0 : ℝ) 1,
    ∃ E_σ : ℂ,
      riemannZeta (σ + I * s.im) =
        ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-(σ + I * s.im)) -
        ↑a ^ (1 - (σ + I * s.im)) / (1 - (σ + I * s.im)) -
        c * ↑a ^ (-(σ + I * s.im)) + E_σ ∧
      ‖E_σ‖ ≤ (if ϑ ≠ 0 then
          σ / 2 * ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re) +
            |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)
        else σ / 6) / a ^ (σ + 1) := by
    intro σ hσ
    obtain ⟨hσ_pos, hσ_lt_one⟩ := hσ
    set s_σ : ℂ := ↑σ + I * ↑s.im with hs_σ_def
    have hs_σ_ne_one : s_σ ≠ 1 := by
      rw [ne_eq, Complex.ext_iff, not_and_or]
      left
      rw [hs_σ_def]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, one_mul, sub_self, Complex.one_re]
      linarith
    have hs_σ_re_pos : 0 < s_σ.re := by
      rw [hs_σ_def]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                zero_mul, Complex.I_im, Complex.ofReal_im, one_mul, sub_self, add_zero, hσ_pos]
    have hs_σ_im_bound : a > |s_σ.im| / (2 * π) := by
      rw [hs_σ_def]
      simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
                Complex.I_re, Complex.ofReal_re, mul_zero, Complex.I_im, one_mul]
      exact haτ
    obtain ⟨E_σ, hE_eq, hE_bound⟩ :=
      proposition_dadaro_zero_lt hs_σ_ne_one hs_σ_re_pos ha ha' hs_σ_im_bound
    use E_σ
    constructor
    · convert hE_eq using 2
      simp only [c, ϑ, s_σ]
      simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, mul_zero, Complex.I_im, one_mul]
    · have hϑ_match : s_σ.im / (2 * π * a) = ϑ := by
        rw [hs_σ_def]
        simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
                  Complex.I_re, Complex.ofReal_re, mul_zero, Complex.I_im, one_mul]
        rfl
      have hre_match : s_σ.re = σ := by
        rw [hs_σ_def]
        simp
      convert hE_bound using 2
      · simp only [← hϑ_match, ← hre_match]
      · simp only [hre_match]
  rw [show s.re + 1 = 1 by rw [← hsigma]; norm_num]
  have hs_canonical : s = I * s.im := by
    apply Complex.ext
    · simp [hsigma.symm]
    · simp
  rw [hs_canonical]
  let σ_n : ℕ → ℝ := fun n => 1 / (n + 2 : ℝ)
  have hσ_n_mem : ∀ n, σ_n n ∈ Set.Ioo (0 : ℝ) 1 := by
    intro n
    constructor
    · simp only [one_div, inv_pos, σ_n]; positivity
    · simp only [one_div, σ_n]
      rw [inv_lt_one₀]
      · linarith
      · positivity
  have hE_n : ∀ n, ∃ E_n : ℂ,
    riemannZeta (↑(σ_n n) + I * ↑s.im) =
      ∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(↑(σ_n n) + I * ↑s.im)) -
      ↑a ^ (1 - (↑(σ_n n) + I * ↑s.im)) / (1 - (↑(σ_n n) + I * ↑s.im)) -
      c * ↑a ^ (-(↑(σ_n n) + I * ↑s.im)) + E_n ∧
    ‖E_n‖ ≤ (if ϑ ≠ 0 then
        σ_n n / 2 * ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re) +
          |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)
      else σ_n n / 6) / a ^ (σ_n n + 1) := fun n ↦
    h_nearby_approximation (σ_n n) (hσ_n_mem n)
  choose E_n hE_n_eq hE_n_bound using hE_n
  have h_lim_σ : Tendsto σ_n atTop (𝓝 0) := by
    simp only [one_div, σ_n]
    apply tendsto_inv_atTop_zero.comp
    apply Filter.tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  let E := riemannZeta (I * s.im) - (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(I * s.im) : ℂ) -
             ↑a ^ (1 - (I * s.im) : ℂ) / (1 - (I * s.im) : ℂ) - c * ↑a ^ (-(I * s.im) : ℂ))
  have hE_converges : Filter.Tendsto E_n Filter.atTop (𝓝 E) := by
    have : Tendsto (fun n ↦ riemannZeta (↑(σ_n n) + I * ↑s.im) -
        (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(↑(σ_n n) + I * ↑s.im) : ℂ) -
          ↑a ^ (1 - (↑(σ_n n) + I * ↑s.im) : ℂ) / (1 - (↑(σ_n n) + I * ↑s.im) : ℂ) -
        c * ↑a ^ (-(↑(σ_n n) + I * ↑s.im) : ℂ))) atTop (𝓝 E) := by
      have h1 : Tendsto (fun n ↦ riemannZeta (↑(σ_n n) + I * ↑s.im)) atTop
          (𝓝 (riemannZeta (I * ↑s.im))) := by
        convert h_continuous_extension.1.tendsto.comp h_lim_σ using 1; simp [zero_add]
      have h2 : Tendsto (fun n ↦ ∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(↑(σ_n n) + I * ↑s.im) : ℂ))
          atTop (𝓝 (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(I * s.im) : ℂ))) := by
        convert h_continuous_extension.2.1.tendsto.comp h_lim_σ using 1
        simp [zero_add]
      have h3 : Tendsto (fun n ↦ ↑a ^ (1 - (↑(σ_n n) + I * ↑s.im) : ℂ) /
          (1 - (↑(σ_n n) + I * ↑s.im) : ℂ)) atTop
          (𝓝 (↑a ^ (1 - (I * s.im) : ℂ) / (1 - (I * s.im) : ℂ))) := by
        convert h_continuous_extension.2.2.1.tendsto.comp h_lim_σ using 1
        simp [zero_add]
      have h4 : Tendsto (fun n ↦ c * ↑a ^ (-(↑(σ_n n) + I * ↑s.im) : ℂ)) atTop
          (𝓝 (c * ↑a ^ (-(I * s.im) : ℂ))) := by
        convert h_continuous_extension.2.2.2.tendsto.comp h_lim_σ using 1
        simp [zero_add]
      exact Tendsto.sub h1 (Tendsto.sub (Tendsto.sub h2 h3) h4)
    exact this.congr (fun n ↦ by rw [hE_n_eq n]; ring)
  have hnormE_converges : Tendsto (fun n ↦ ‖E_n n‖) atTop (𝓝 ‖E‖) := by
    apply Filter.Tendsto.norm hE_converges
  let bound_n : ℕ → ℝ := fun n =>
    (if ϑ ≠ 0 then
        σ_n n / 2 * ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re) +
        |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1)
      else σ_n n / 6) / a ^ (σ_n n + 1)
  have h_bound_converges : Tendsto bound_n atTop (𝓝 (C / a)) := by
    by_cases hϑ : ϑ = 0
    · simp only [hϑ, ne_eq, not_true_eq_false, ↓reduceIte, bound_n]
      have h_num : Tendsto (fun n ↦ σ_n n / 6) atTop (𝓝 0) := by
        simpa using h_lim_σ.div_const 6
      have h_den : Tendsto (fun n ↦ a ^ (σ_n n + 1)) atTop (𝓝 a) := by
        convert Tendsto.rpow tendsto_const_nhds (h_lim_σ.add tendsto_const_nhds) (Or.inl ha.ne')
        simp
      rw [show C = 0 by simp [C, hϑ, hsigma.symm, zero_div]]
      apply h_num.div h_den ha.ne'
    · simp only [ne_eq, hϑ, not_false_eq_true, ↓reduceIte, one_div, inv_re, map_pow, map_mul,
      normSq_ofReal, bound_n]
      have hC : C = |ϑ| / (2 * π ^ 2) * (1 / (1 - |ϑ|) ^ 3 + 2 * (riemannZeta 3).re - 1) := by
        simp only [ite_not, hϑ, ↓reduceIte, one_div, inv_re, map_pow, map_mul, normSq_ofReal,
          add_eq_right, mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, C]
        rw [← hsigma]; simp
      have hnum : Tendsto (fun n ↦ σ_n n / 2 * ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re) +
          C) atTop (𝓝 C) := by
        nth_rw 2 [← zero_add C]
        apply Tendsto.add
        · convert (h_lim_σ.div_const 2).mul_const ((1 / Complex.sin (π * ϑ : ℂ) ^ 2).re - (1 / (π * ϑ : ℂ) ^ 2).re)
          simp
        · exact tendsto_const_nhds
      have hden : Tendsto (fun n ↦ a ^ (σ_n n + 1)) atTop (𝓝 a) := by
        convert Tendsto.rpow tendsto_const_nhds (h_lim_σ.add tendsto_const_nhds) (Or.inl ha.ne')
        simp
      convert hnum.div hden (by positivity) using 1
      · ext n; dsimp; congr 1; rw [hC]
        have h_sin : (1 / Complex.sin ((π : ℂ) * (ϑ : ℂ)) ^ 2).re =
            (Complex.sin ((π : ℂ) * (ϑ : ℂ)) ^ 2).re / normSq (Complex.sin ((π : ℂ) * (ϑ : ℂ))) ^ 2 := by
          simp
        have h_th : (1 / ((π : ℂ) * (ϑ : ℂ)) ^ 2).re = (((π : ℂ) * (ϑ : ℂ)) ^ 2).re / (π * π * (ϑ * ϑ)) ^ 2 := by simp
        simp only [h_sin, h_th]; ring
  have h_norm_continuous : Tendsto (fun n => ‖E_n n‖) atTop (𝓝 ‖E‖) := hE_converges.norm
  have h_norm_bounded : ∀ n, ‖E_n n‖ ≤ bound_n n := by
    intro n
    simp_rw [bound_n]
    exact hE_n_bound n
  use E
  constructor
  · have h_lhs : Filter.Tendsto (fun n => riemannZeta (↑(σ_n n) + I * ↑s.im))
      Filter.atTop (𝓝 (riemannZeta (I * ↑s.im))) := by
      have h_lim_σ : Tendsto σ_n atTop (𝓝 0) := by
        simp only [one_div, σ_n]
        apply tendsto_inv_atTop_zero.comp
        apply Filter.tendsto_atTop_add_const_right
        exact tendsto_natCast_atTop_atTop
      have h_cont := h_continuous_extension.1.tendsto
      convert h_cont.comp h_lim_σ using 1
      · ext n; simp
    have h_rhs : Filter.Tendsto (fun n =>
        ∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(↑(σ_n n) + I * ↑s.im)) -
        ↑a ^ (1 - (↑(σ_n n) + I * ↑s.im)) / (1 - (↑(σ_n n) + I * ↑s.im)) -
        c * ↑a ^ (-(↑(σ_n n) + I * ↑s.im)))
      Filter.atTop (𝓝 (∑ k ∈ Finset.Icc 1 ⌊a⌋₊, (k : ℂ) ^ (-(I * ↑s.im)) -
        ↑a ^ (1 - I * ↑s.im) / (1 - I * ↑s.im) - c * ↑a ^ (-(I * ↑s.im)))) := by
      have h1 := h_continuous_extension.2.1.tendsto.comp h_lim_σ
      have h2 := h_continuous_extension.2.2.1.tendsto.comp h_lim_σ
      have h3 := h_continuous_extension.2.2.2.tendsto.comp h_lim_σ
      convert (h1.sub h2).sub h3 using 1
      ext n; simp
    simp [E]
  · exact le_of_tendsto_of_tendsto h_norm_continuous (by simp [h_bound_converges])
      (Filter.Eventually.of_forall h_norm_bounded)


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
      ∑ n ∈ Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) -
      (a ^ (1 - s) : ℂ) / (1 - s) - c * (a ^ (-s) : ℂ) + E ∧
      ‖E‖ ≤ C / (a ^ (s.re + 1 : ℝ)) := by
  rcases hsigma.eq_or_lt with hsigma_eq | hsigma_lt
  · exact proposition_dadaro_zero_eq hs1 hsigma_eq ha ha' haτ
  · exact proposition_dadaro_zero_lt hs1 hsigma_lt ha ha' haτ

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
