import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Int.Star
import Mathlib.Data.PNat.Interval
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import PrimeNumberTheoremAnd.PrimaryDefinitions
import PrimeNumberTheoremAnd.Wiener
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.PerronFormula

open Real

blueprint_comment /--
\section{Chirre-Helfgott's estimates for sums of nonnegative arithmetic functions}\label{ch2-sec}

We record some estimates from \cite{CH2} for summing non-negative functions, with a particular interest in estimating $\psi$.
-/


namespace CH2

blueprint_comment /--
\subsection{Fourier-analytic considerations}\label{ch2-fourier-sec}

Some material from \cite[Section 2]{CH2}, slightly rearranged to take advantage of existing results in the repository.
-/

open Real MeasureTheory FourierTransform Chebyshev Asymptotics
open ArithmeticFunction hiding log
open Complex hiding log

lemma summable_nterm_of_log_weight {a : ℕ → ℂ} {β sig : ℝ}
    (hsig : 1 < sig) (ha : Summable (fun n : ℕ ↦ ‖a n‖ / (n * Real.log n ^ β))) :
    Summable (nterm a sig) := by
  have hs : 0 < sig - 1 := sub_pos.mpr hsig
  have hlo : (fun x : ℝ => Real.log x ^ β) =o[Filter.atTop] fun x => x ^ (sig - 1) :=
    isLittleO_log_rpow_rpow_atTop β hs
  have hlo_nat :
      (fun n : ℕ => Real.log (n : ℝ) ^ β) =o[Filter.atTop] fun n => (n : ℝ) ^ (sig - 1) :=
    hlo.comp_tendsto tendsto_natCast_atTop_atTop
  have hlog_le : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log (n : ℝ) ^ β‖ ≤ ‖(n : ℝ) ^ (sig - 1)‖ := by
    simpa using hlo_nat.bound (show (0 : ℝ) < 1 by norm_num)
  have h_event : ∀ᶠ n : ℕ in Filter.atTop,
      ‖(if n = 0 then 0 else ‖a n‖ / (n : ℝ) ^ sig)‖ ≤ ‖a n‖ / ((n : ℝ) * Real.log n ^ β) := by
    filter_upwards [hlog_le, Filter.eventually_ge_atTop (2 : ℕ)] with n hlog hn
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hpowpos : 0 < Real.log (n : ℝ) ^ β := Real.rpow_pos_of_pos hlogpos _
    have hlog_le' : Real.log (n : ℝ) ^ β ≤ (n : ℝ) ^ (sig - 1) := by
      rwa [Real.norm_of_nonneg hpowpos.le, Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hlog
    have hpow_split : (n : ℝ) ^ sig = (n : ℝ) * (n : ℝ) ^ (sig - 1) := by
      conv_lhs => rw [show sig = 1 + (sig - 1) by ring]; rw [Real.rpow_add hnpos, Real.rpow_one]
    rw [show (if n = 0 then 0 else ‖a n‖ / (n : ℝ) ^ sig) = ‖a n‖ / (n : ℝ) ^ sig from
        by simp [show n ≠ 0 by omega], Real.norm_of_nonneg (div_nonneg (norm_nonneg _)
        (Real.rpow_nonneg hnpos.le _)), hpow_split]
    exact div_le_div_of_nonneg_left (norm_nonneg (a n)) (mul_pos hnpos hpowpos)
      (mul_le_mul_of_nonneg_left hlog_le' hnpos.le)
  have hbase : Summable (fun n : ℕ ↦ if n = 0 then 0 else ‖a n‖ / n ^ sig) :=
    Summable.of_norm_bounded_eventually_nat ha h_event
  simpa [nterm] using hbase

lemma fourier_scale_div_noscalar (φ : ℝ → ℂ) (T u : ℝ) (hT : 0 < T) :
    𝓕 (fun t : ℝ ↦ φ (t / T)) u = (T : ℂ) * 𝓕 φ (T * u) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have hcomp : (fun v : ℝ ↦ 𝐞 (-(v * u)) • φ (v / T)) =
      fun v : ℝ ↦ (fun z : ℝ ↦ 𝐞 (-(z * (T * u))) • φ z) (v / T) := by
    ext v; congr 2; simp [show (v / T) * (T * u) = v * u from by field_simp [hT.ne']]
  rw [hcomp]
  simpa [abs_of_pos hT, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
    Measure.integral_comp_div (g := fun z : ℝ ↦ 𝐞 (-(z * (T * u))) • φ z) T

@[blueprint
  "ch2-prop-2-3-1"
  (title := "CH2 Proposition 2.3, substep 1")
  (statement := /--
  Let $a_n$ be a sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Write $G(s)= \sum_n a_n n^{-s} - \frac{1}{s-1}$ for $\mathrm{Re} s > 1$.  Let $\varphi$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \psi(y) = O(1/|y|^\beta)$.  Then for any $x>0$ and $\sigma > 1$
  $$ \frac{1}{2\pi} \sum a_n \frac{x}{n^\sigma} \hat \psi(\frac{T}{2\pi} \log \frac{n}{x} ) = \frac{1}{2\pi T} \int_{-T}^{T} \varphi(\frac{t}{T}) G(\sigma+it) x^{it}\ dt + \int_{-T \log x/2\pi}^\infty e^{-y(\sigma-1)} \hat \varphi(y)\ dy) \frac{x^{2-\sigma}}{T}.$$
  -/)
  (proof := /-- Use Lemma \ref{first-fourier} and Lemma \ref{second-fourier}, similar to the proof of `limiting\_fourier\_aux`.
  -/)
  (latexEnv := "sublemma")
  (discussion := 879)]
theorem prop_2_3_1 {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (_hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ}
    (hG' : Set.EqOn G (fun s ↦ LSeries a s - 1 / (s - 1)) { z | z.re > 1 })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0) -- this hypothesis may be unnecessary
    (_hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x sig : ℝ) (hx : 0 < x) (hsig : 1 < sig) :
    (1 / (2 * π)) * ∑' (n : ℕ), (x : ℂ) * LSeries.term a sig n *
      𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        (∫ t in Set.Icc (-T) T, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I)) +
      (x ^ (2 - sig) / (2 * π * T) : ℝ) *
        (∫ u in Set.Ici (-log x), Real.exp (-u * (sig - 1)) *
          𝓕 (fun t : ℝ ↦ φ (t / T)) (u / (2 * π))) := by
  let phiScaled : ℝ → ℂ := fun t => φ (t / T)
  have hphiScaled_meas : Measurable phiScaled := by simp only [phiScaled]; fun_prop
  have hphiScaled_int : Integrable phiScaled :=
    (MeasureTheory.integrable_comp_mul_right_iff (g := φ) (inv_ne_zero hT.ne')).2 hφ_int |>.congr
      (by simp [phiScaled, div_eq_mul_inv])
  have hsummable : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm a σ') :=
    fun σ' hσ' => summable_nterm_of_log_weight hσ' ha
  have hfirst := @first_fourier x sig phiScaled a hsummable hphiScaled_int hx hsig
  have hsecond := @second_fourier phiScaled hphiScaled_meas hphiScaled_int x sig hx hsig
  have hxpow (t : ℝ) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  let C0 : ℝ := ∑' n : ℕ, nterm a sig n
  have hC0_nonneg : 0 ≤ C0 := tsum_nonneg fun n => by
    by_cases hn : n = 0 <;> simp [nterm, hn, div_nonneg, Real.rpow_nonneg]
  have hLS_bound (t : ℝ) : ‖LSeries a (sig + t * I)‖ ≤ C0 := by
    have hs_term : Summable (fun n : ℕ => ‖LSeries.term a (sig + t * I) n‖) := by
      convert hsummable sig hsig with n; simp [norm_term_eq_nterm_re]
    exact (norm_tsum_le_tsum_norm hs_term).trans (by simp [C0, norm_term_eq_nterm_re])
  have hLS_aesm : AEStronglyMeasurable (fun t : ℝ ↦ LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) :=
    (((continuous_LSeries_aux (hsummable sig hsig)).measurable.mul hphiScaled_meas).mul
      (continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])).measurable).aestronglyMeasurable
  have hLS_int : Integrable (fun t : ℝ ↦ LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) :=
    .mono' (hphiScaled_int.norm.const_mul C0) hLS_aesm (.of_forall fun t => by
      simp only [norm_mul, mul_assoc, hxpow, mul_one]
      exact mul_le_mul_of_nonneg_right (hLS_bound t) (norm_nonneg _))
  have hPole_denom_ne (t : ℝ) : sig + t * I - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hPole_bound (t : ℝ) : ‖1 / (sig + t * I - 1)‖ ≤ (sig - 1)⁻¹ := by
    have hσpos : 0 < sig - 1 := sub_pos.mpr hsig
    simpa [norm_div, one_div] using one_div_le_one_div_of_le hσpos
      (by simpa [abs_of_pos hσpos] using Complex.abs_re_le_norm (sig + t * I - 1))
  have hcontX : Continuous (fun t : ℝ => (x : ℂ) ^ (t * I)) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have hPole_aesm :
      AEStronglyMeasurable (fun t : ℝ ↦ (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) :=
    (((by simpa [one_div] using Continuous.inv₀ (by fun_prop) (hPole_denom_ne) :
      Continuous (fun t : ℝ => (1 / (sig + t * I - 1) : ℂ))).measurable.mul hphiScaled_meas).mul
        hcontX.measurable).aestronglyMeasurable
  have hPole_int : Integrable (fun t : ℝ ↦ (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) :=
    .mono' (hphiScaled_int.norm.const_mul (sig - 1)⁻¹) hPole_aesm (.of_forall fun t => by
      simp only [norm_mul, mul_assoc, hxpow, mul_one]
      exact mul_le_mul_of_nonneg_right (hPole_bound t) (norm_nonneg _))
  have hG_rewrite :
      ∫ t : ℝ, phiScaled t * G (sig + t * I) * x ^ (t * I) =
        (∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
          ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
    rw [← integral_sub hLS_int hPole_int]; congr 1; ext t
    rw [hG' (by simp [hsig] : (sig + t * I).re > 1)]; ring
  have hIcc_to_univ :
      ∫ t in Set.Icc (-T) T, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) =
        ∫ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) := by
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (.of_forall fun t => ?_)
    by_cases ht : t ∈ Set.Icc (-T) T
    · simp [ht]
    · simp [ht, hφ_supp _ (show t / T ∉ Set.Icc (-1) 1 from by
        intro ⟨h1, h2⟩; exact ht ⟨by linarith [(le_div_iff₀ hT).mp h1],
          by linarith [(div_le_iff₀ hT).mp h2]⟩)]
  have hG_with_x :
      (1 / (2 * π * T)) *
          ∫ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) =
        (x / (2 * π * T) : ℂ) *
          ((∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
            ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) := by
    have hcpow (t : ℝ) : (x : ℂ) ^ (1 + ↑t * I) = x * x ^ (↑t * I) := by
      rw [Complex.cpow_add (x := (x : ℂ)) (y := (1 : ℂ)) (z := t * I)
        (by exact_mod_cast hx.ne')]; simp
    simp_rw [show ∀ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + ↑t * I) =
        (x : ℂ) * (phiScaled t * G (sig + t * I) * x ^ (↑t * I)) from
      fun t => by rw [hcpow]; simp only [phiScaled]; ring, integral_const_mul, hG_rewrite]; ring
  have hPole_from_second :
      (x ^ (2 - sig) / (2 * π * T) : ℝ) * ∫ u in Set.Ici (-log x),
          Real.exp (-u * (sig - 1)) * 𝓕 phiScaled (u / (2 * π)) =
        (x / (2 * π * T) : ℂ) *
          ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
    have hpowx : (x ^ (2 - sig) * x ^ (sig - 1) : ℝ) = x := by
      rw [← Real.rpow_add hx]; norm_num
    calc (x ^ (2 - sig) / (2 * π * T) : ℝ) * ∫ u in Set.Ici (-log x),
            Real.exp (-u * (sig - 1)) * 𝓕 phiScaled (u / (2 * π))
        _ = ((x ^ (2 - sig) / (2 * π * T) * x ^ (sig - 1) : ℝ) : ℂ) *
              ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
            rw [hsecond]; push_cast; ring
        _ = _ := by rw [show (x ^ (2 - sig) / (2 * π * T) * x ^ (sig - 1) : ℝ) = x / (2 * π * T)
              from by rw [div_mul_eq_mul_div, hpowx]]; simp
  have hleft_scale :
      (1 / (2 * π)) * ∑' n : ℕ, (x : ℂ) * LSeries.term a sig n * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
        (x / (2 * π * T) : ℂ) *
          ∑' n : ℕ, LSeries.term a sig n * 𝓕 phiScaled ((1 / (2 * π)) * log (n / x)) := by
    have hS : ∑' n : ℕ, LSeries.term a sig n * 𝓕 phiScaled ((1 / (2 * π)) * log (n / x)) =
        (T : ℂ) * ∑' n : ℕ, LSeries.term a sig n * 𝓕 φ (T * ((1 / (2 * π)) * log (n / x))) := by
      rw [← tsum_mul_left]; congr with n
      simpa [phiScaled, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun z : ℂ => LSeries.term a sig n * z)
          (fourier_scale_div_noscalar φ T ((1 / (2 * π)) * log (↑n / x)) hT)
    simp_rw [hS, ← tsum_mul_left]; field_simp [hT.ne']
  rw [hleft_scale, hfirst]
  rw [show (x / (2 * π * T) : ℂ) * ∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I) =
      (x / (2 * π * T) : ℂ) * ((∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
        ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) +
      (x / (2 * π * T) : ℂ) * ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) from
    by rw [mul_sub, sub_add_cancel]]
  rw [← hG_with_x, ← hIcc_to_univ, ← hPole_from_second]

@[blueprint
  "ch2-prop-2-3"
  (title := "CH2 Proposition 2.3")
  (statement := /--
  Let $a_n$ be a sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi(y) = O(1/|y|^\beta)$.  Then for any $x>0$,
  $$ \frac{1}{2\pi} \sum a_n \frac{x}{n} \hat \varphi(\frac{T}{2\pi} \log \frac{n}{x} ) = \frac{1}{2\pi i T} \int_{1-iT}^{1+iT} \varphi(\frac{s-1}{iT}) G(s) x^{s}\ ds + (\varphi(0) - \int_{-\infty}^{-T \log x/2\pi} \hat \varphi(y)\ dy) \frac{x}{T}.$$
  -/)
  (proof := /-- Apply Sublemma \ref{ch2-prop-2-3-1} and take the limit as $\sigma \to 1^+$, using the continuity of $G$ and the dominated convergence theorem, as well as the Fourier inversion formula.
  -/)
  (latexEnv := "proposition")
  (discussion := 880)]
theorem prop_2_3 {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / n ^ s - 1 / (s - 1)) { z | z.re > 1 })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_cont : ContinuousAt φ 0)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    (1 / (2 * π)) * ∑' (n : ℕ+), a n * (x / n) * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        (∫ t in Set.Icc (-T) T, φ (t/T) * G (1 + t * I) * x ^ (1 + t * I)) +
      (φ 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ y) * (x / T) := by
  sorry

@[blueprint
  "ch2-S-def"
  (title := "CH2 Definition of $S$, (2.8)")
  (statement := /--
  $S_\sigma(x)$ is equal to $\sum_{n \leq x} a_n / n^\sigma$ if $\sigma < 1$ and $\sum_{n \geq x} a_n / n^\sigma$ if $\sigma > 1$.
  -/)]
noncomputable def S (a : ℕ → ℝ) (σ x : ℝ) : ℝ :=
  if σ < 1 then ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n ^ σ : ℝ)
  else ∑' (n:ℕ), if n ≥ x then a n / (n ^ σ : ℝ) else 0

@[blueprint
  "ch2-I-def"
  (title := "CH2 Definition of $I$, (2.9)")
  (statement := /--
  $I_\lambda(u) = 1_{[0,\infty)}(\mathrm{sgn}(\lambda)u) e^{-\lambda u}$.
  -/)]
noncomputable def I' (lambda u : ℝ) : ℝ := -- use I' instead of I to avoid clash with Complex.I
  if 0 ≤ lambda * u then exp (-lambda * u) else 0

@[blueprint
  "ch2-2-10"
  (title := "CH2 Equation (2.10)")
  (statement := /--
  $S_\sigma(x) = x^{-\sigma} \sum_n a_n \frac{x}{n} I_\lambda( \frac{T}{2\pi} \log \frac{n}{x} )$
  where $\lambda = 2\pi(\sigma-1)/T$.
  -/)
  (proof := /-- Routine manipulation. -/)
  (latexEnv := "sublemma")
  (discussion := 881)]
theorem S_eq_I (a : ℕ → ℝ) (s x T : ℝ) (hs : s ≠ 1) (hT : 0 < T) (hx : 0 < x) :
    let lambda := (2 * π * (s - 1)) / T
    S a s x = (x ^ (-s) : ℝ) * ∑' (n : ℕ+), a n * (x / n) * I' lambda ((T / (2 * π)) * log (n / x)) := by
  have lambda_mul_u {s T : ℝ} (hT : 0 < T) (u : ℝ) :
      2 * π * (s - 1) / T * (T / (2 * π) * u) = (s - 1) * u := by field_simp [pi_ne_zero]
  by_cases hs_lt : s < 1
  · have hS_def : S a s x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n ^ s : ℝ) := if_pos hs_lt
    have h_tsum_eq : x ^ (-s : ℝ) * ∑' n : ℕ+,
        a n * (x / n) * I' (2 * π * (s - 1) / T) ((T / (2 * π)) * log (n / x)) =
        x ^ (-s : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n) * (x / n) ^ (s - 1) := by
      have h_cond : x ^ (-s : ℝ) * ∑' n : ℕ+, a n * (x / n) * I' (2 * π * (s - 1) / T)
            ((T / (2 * π)) * log (n / x)) =
          x ^ (-s : ℝ) * ∑' n : ℕ+, if n ≤ ⌊x⌋₊ then a n * (x / n) * (x / n) ^ (s - 1) else 0 := by
        congr 1; congr 1 with n; unfold I'
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
        simp only [lambda_mul_u hT]
        split_ifs with h1 h2 h3
        · congr 1; rw [rpow_def_of_pos (div_pos hx hn_pos),
            show log (x / n) = log x - log n from log_div hx.ne' hn_pos.ne']
          congr 1; rw [show log (n / x) = log n - log x from
            log_div hn_pos.ne' hx.ne']
          field_simp [hT.ne']; ring
        · exact absurd h1 (not_le.mpr (mul_neg_of_neg_of_pos (sub_neg_of_lt hs_lt)
            (log_pos (by rw [lt_div_iff₀ hx]; linarith [Nat.lt_of_floor_lt (not_le.mp h2)]))))
        · exact absurd h1 (not_not.mpr (mul_nonneg_of_nonpos_of_nonpos (sub_neg_of_lt hs_lt).le
            (log_nonpos (div_pos hn_pos hx).le
              ((div_le_one hx).mpr (le_trans (Nat.cast_le.mpr h3) (Nat.floor_le hx.le))))))
        · simp
      rw [h_cond, tsum_eq_sum (s := Finset.Icc 1 ⟨⌊x⌋₊ + 1, Nat.succ_pos _⟩)]
      · congr 1; rw [← Finset.sum_filter]; field_simp
        refine Finset.sum_bij (fun n _ ↦ n) ?_ ?_ ?_ ?_
        · simp only [Finset.mem_filter, Finset.mem_Icc, PNat.one_le, true_and, and_imp]
          exact fun n hn₁ hn₂ ↦ ⟨PNat.one_le _, hn₂⟩
        · exact fun _ _ _ _ h ↦ Subtype.val_injective h
        · simp only [Finset.mem_Icc, Finset.mem_filter, PNat.one_le, true_and,
            exists_prop, and_imp]
          exact fun b hb₁ hb₂ ↦ ⟨⟨b, hb₁⟩, ⟨Nat.le_succ_of_le hb₂, hb₂⟩, rfl⟩
        · simp only [Finset.mem_filter, Finset.mem_Icc, PNat.one_le, true_and,
            mul_assoc, mul_comm, implies_true]
      · simp +zetaDelta only [Finset.mem_Icc, PNat.one_le, true_and, not_le, ite_eq_right_iff,
          mul_eq_zero, div_eq_zero_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false] at *
        exact fun n hn₁ hn₂ ↦ absurd (Nat.le_succ_of_le hn₂) (not_le_of_gt hn₁)
    simp_all only [ne_eq, div_eq_mul_inv, rpow_neg hx.le, mul_left_comm, mul_comm,
      mul_inv_rev, mul_assoc, Finset.mul_sum ..]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn_pos : (0 : ℝ) < n := by norm_cast; linarith [Finset.mem_Icc.mp hn]
    rw [mul_rpow (by positivity) (by positivity), inv_rpow (by positivity)]
    ring_nf
    rw [rpow_add hx, rpow_neg_one, rpow_add hn_pos, rpow_neg_one]
    field_simp
  · have hs_def : S a s x = ∑' n : ℕ, if n ≥ x then a n / (n ^ s : ℝ) else 0 := by simp_all [S]
    have hs_ge : ∑' n : ℕ, (if n ≥ x then a n / (n ^ s : ℝ) else 0) =
        ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n / (n ^ s : ℝ) else 0) :=
      (Subtype.val_injective.tsum_eq fun n hn ↦
        ⟨⟨n, Nat.pos_of_ne_zero fun h ↦ by simp_all [Function.mem_support]⟩, rfl⟩).symm
    have hs_factor : ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n / (n ^ s : ℝ) else 0) =
        x ^ (-s) * ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n * (x / (n : ℝ)) * (x / (n : ℝ)) ^ (s - 1) else 0) := by
      rw [← tsum_mul_left]; congr; ext n
      split_ifs with h
      · have hn : (0 : ℝ) < n := by positivity
        rw [div_eq_mul_inv, div_rpow hx.le hn.le, rpow_sub_one hx.ne', rpow_sub_one hn.ne', rpow_neg hx.le]
        field_simp
      · simp
    convert hs_factor using 3
    · rw [hs_def, hs_ge]
    · ext n; simp only [I', lambda_mul_u hT]
      split_ifs <;> simp_all only [ne_eq, not_lt, ge_iff_le, Nat.cast_pos, PNat.pos,
        rpow_def_of_pos, div_pos_iff_of_pos_left, not_le, mul_zero, mul_eq_mul_left_iff]
      · exact Or.inl (by rw [show (n : ℝ) / x = (x / n)⁻¹ from (inv_div x n).symm, Real.log_inv]; field_simp)
      · linarith [mul_neg_of_pos_of_neg (sub_pos.mpr <| lt_of_le_of_ne hs_lt (Ne.symm ‹_›))
          (log_neg (by positivity : (0 : ℝ) < n / x) <| by rw [div_lt_one hx]; linarith)]
      · linarith [mul_nonneg (sub_nonneg.mpr hs_lt)
          (log_nonneg (by rw [le_div_iff₀ hx]; linarith : (1:ℝ) ≤ n / x))]

@[blueprint
  "ch2-prop-2-4-plus"
  (title := "CH2 Proposition 2.4, upper bound")
  (statement := /--
  Let $a_n$ be a non-negative sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi_+$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi_+(y) = O(1/|y|^\beta)$.  Let $\sigma \neq 1$ and write $\lambda = 2\pi(\sigma-1)/T$.  Assume $I_\lambda(y) \leq \hat \varphi_+(y)$ for all $y$. Then for any $x\geq 1$,
  $$ S_\sigma(x) \leq \frac{2\pi x^{1-\sigma}}{T} \varphi_+(0) + \frac{x^{-\sigma}}{T} \int_{-T}^T \varphi_+(t/T) G(1+it) x^{1+it}\ dt - \frac{1_{(-\infty,1)}(\sigma)}{1-\sigma}.$$
  -/)
  (proof := /-- By the nonnegativity of $a_n$ we have
  $$ S_\sigma(x) \leq x^{-\sigma} \sum_n a_n \frac{x}{n} \hat \varphi_+(\frac{T}{2\pi} \log \frac{n}{x} ).$$
  By Proposition \ref{ch2-prop-2-3} we can express the right-hand side as
  $$ \frac{1}{2\pi i T} \int_{1-iT}^{1+iT} \varphi_+(\frac{s-1}{iT}) G(s) x^{s}\ ds + (\varphi_+(0) - \int_{-\infty}^{-T \log x/2\pi} \hat \varphi_+(y)\ dy) \frac{x}{T}.$$
  If $\lambda > 0$, then $I_\lambda(y)=0$ for negative $y$, so
  $$ -\int_{-\infty}^{-T \log x/2π} \hat \varphi_+(y)\ dy \leq 0.$$
  If $\lambda < 0$, then $I_\lambda(y)=e^{-\lambda y}$ for $y$ negative, so
$$ -\int_{-\infty}^{-T \log x/2π} I_\lambda(y)\ dy \leq e^{\lambda T \log x/2π}/(-\lambda) = x^{\sigma-1}/(-\lambda).$$
hence
$$ -\int_{-\infty}^{-T \log x/2π} \hat \varphi_+(y)\ dy \leq - x^{\sigma-1}/(-\lambda).$$
Since $x^{-\sigma} * (2\pi x / T) * x^{\sigma-1}/(-\lambda) = 1/(1-\sigma)$, the result follows.
  -/)
  (latexEnv := "proposition")
  (discussion := 882)]
theorem prop_2_4_plus {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0) {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / (n ^ s : ℂ) - 1 / (s - 1)) { z | z.re > 1 })
    {φ_plus : ℝ → ℂ} (hφ_mes : Measurable φ_plus) (hφ_int : Integrable φ_plus)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ_plus x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_plus y‖ ≤ C / |y| ^ β)
    (hI_le_Fourier : ∀ y : ℝ,
      let lambda := (2 * π * (σ - 1)) / T
      I' lambda y ≤ ‖𝓕 φ_plus y‖)
    {x : ℝ} (hx : 1 ≤ x) :
    S a σ x ≤
      ((2 * π * (x ^ (1 - σ) : ℝ) / T) * φ_plus 0).re +
      (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_plus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if σ < 1 then 1 / (1 - σ) else 0 := by
  sorry

@[blueprint
  "ch2-prop-2-4-minus"
  (title := "CH2 Proposition 2.4, lower bound")
  (statement := /--
  Let $a_n$ be a non-negative sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi_-$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi_-(y) = O(1/|y|^\beta)$.  Let $\sigma \neq 1$ and write $\lambda = 2\pi(\sigma-1)/T$.  Assume $\hat \varphi_-(y) \leq I_\lambda(y)$ for all $y$. Then for any $x\geq 1$ and $\sigma \neq 1$,
  $$ S_\sigma(x) \geq \frac{2\pi x^{1-\sigma}}{T} \varphi_-(0) + \frac{x^{-\sigma}}{T} \int_{-T}^T \varphi_-(t/T) G(1+it) x^{1+it}\ dt - \frac{1_{(-\infty,1)}(\sigma)}{1-\sigma}.$$
  -/)
  (proof := /-- Similar to the proof of Proposition \ref{ch2-prop-2-4-plus}; see \cite[Proposition 2.4]{CH2} for details.
  -/)
  (latexEnv := "proposition")
  (discussion := 883)]
theorem prop_2_4_minus {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0) {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' (n : ℕ+), a n / (n ^ s : ℂ) - 1 / (s - 1)) { z | z.re > 1 })
    {φ_minus : ℝ → ℂ} (hφ_mes : Measurable φ_minus) (hφ_int : Integrable φ_minus)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ_minus x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_minus y‖ ≤ C / |y| ^ β)
    (hFourier_le_I : ∀ y : ℝ,
      let lambda := (2 * π * (σ - 1)) / T
      ‖𝓕 φ_minus y‖ ≤ I' lambda y)
    {x : ℝ} (hx : 1 ≤ x) :
    S a σ x ≥
      ((2 * π * (x ^ (1 - σ) : ℝ) / T) * φ_minus 0).re +
      (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_minus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if σ < 1 then 1 / (1 - σ) else 0 := by
  sorry


blueprint_comment /--
\subsection{Extremal approximants to the truncated exponential}\label{ch2-trunc-sec}

In this section we construct extremal approximants to the truncated exponential function and establish their basic properties, following \cite[Section 4]{CH2}, although we skip the proof of their extremality.  As such, the material here is organized rather differently from that in the paper.
-/

noncomputable def coth (z : ℂ) : ℂ := 1 / tanh z

theorem sinh_add_pi_I (z : ℂ) : sinh (z + π * I) = -sinh z := by
    simp [Complex.sinh_add, sinh_mul_I, cosh_mul_I]

@[simp]
theorem cosh_add_pi_I (z : ℂ) : cosh (z + π * I) = -cosh z := by
    simp [Complex.cosh_add, cosh_mul_I, sinh_mul_I]

theorem tanh_add_int_mul_pi_I (z : ℂ) (m : ℤ) : tanh (z + π * I * m) = tanh z := by
  have step (w : ℂ) : tanh (w + π * I) = tanh w := by
    rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh,
      sinh_add_pi_I, cosh_add_pi_I]; field_simp
  induction m using Int.induction_on with
  | zero => simp
  | succ n ih =>
    push_cast at ih ⊢
    rw [show z + π * I * (n + 1) = (z + π * I * n) + π * I from by ring, step]; exact ih
  | pred n ih =>
    push_cast at ih ⊢
    have h := step (z + π * I * (-n - 1))
    rw [show z + π * I * (-n - 1) + π * I = z + π * I * -n from by ring] at h
    rw [← h]; exact ih

@[simp]
public theorem tanh_add_pi_I (z : ℂ) : tanh (z + π * I) = tanh z := by
  simpa using tanh_add_int_mul_pi_I z 1

lemma coth_add_pi_mul_I (z : ℂ) : coth (z + π * I) = coth z := by
  simp [coth]

lemma coth_conj (z : ℂ) : (starRingEnd ℂ) (coth z) = coth ((starRingEnd ℂ) z) := by
  simp [coth, Complex.tanh_conj]

@[blueprint
  "Phi-circ-def"
  (title := "Definition of $\\Phi^{\\pm,\\circ}_\\nu$")
  (statement := /--
  $$\Phi^{\pm,\circ}_\nu(z) := \frac{1}{2} (\coth\frac{w}{2} \pm 1)$$
  where $$w = -2\pi i z + \nu.$$
  -/)]
noncomputable def Phi_circ (ν ε : ℝ) (z : ℂ) : ℂ :=
  let w := -2 * π * I * z + (ν : ℂ)
  (1 / 2) * (coth (w / 2) + ε)

attribute [fun_prop] MeromorphicAt.comp_analyticAt

@[fun_prop]
theorem analyticAt_tanh (z : ℂ) (hz : Complex.cosh z ≠ 0) : AnalyticAt ℂ Complex.tanh z := by
  simpa [Complex.tanh_eq_sinh_div_cosh] using
    (Complex.analyticAt_sinh.div Complex.analyticAt_cosh hz :
      AnalyticAt ℂ (fun z => Complex.sinh z / Complex.cosh z) z)

@[fun_prop]
theorem continuousAt_tanh (z : ℂ) (hz : Complex.cosh z ≠ 0) : ContinuousAt Complex.tanh z := by
  exact (analyticAt_tanh z hz).continuousAt

lemma _root_.Complex.cosh_ne_zero_of_sinh_zero {z : ℂ} (h : Complex.sinh z = 0) : Complex.cosh z ≠ 0 := by
  intro hc; have := Complex.cosh_sq_sub_sinh_sq z; simp [h, hc] at this




@[fun_prop]
theorem meromorphicAt_tanh (z : ℂ) : MeromorphicAt Complex.tanh z := by fun_prop [Complex.tanh]

@[fun_prop]
theorem meromorphicAt_coth (z : ℂ) : MeromorphicAt coth z := by fun_prop [CH2.coth]

@[blueprint
  "Phi-circ-mero"
  (title := "$\\Phi^{\\pm,\\circ}_\\nu$ meromorphic")
  (statement := /--
  $$\Phi^{\pm,\circ}_\nu(z)$$ is meromorphic.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)]
theorem Phi_circ.meromorphic (ν ε : ℝ) : Meromorphic (Phi_circ ν ε) := by
  intro z
  fun_prop [CH2.Phi_circ]

@[to_fun (attr := push)] theorem meromorphicOrderAt_div {𝕜 : Type*} [NontriviallyNormedField 𝕜] {x : 𝕜}
    {f g : 𝕜 → 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f / g) x = meromorphicOrderAt f x - meromorphicOrderAt g x := by
  rw [div_eq_mul_inv, meromorphicOrderAt_mul hf hg.inv, meromorphicOrderAt_inv, sub_eq_add_neg]

lemma sinh_zero_iff (ζ : ℂ) : sinh ζ = 0 ↔ (∃ k : ℤ, ζ = k * π * I) := by
  rw [← mul_left_inj' I_ne_zero, ← Complex.sin_mul_I, zero_mul, Complex.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; use -k; apply (mul_left_inj' I_ne_zero).mp; rw [hk]; ring_nf; simp; ring
  · rintro ⟨k, hk⟩; use -k; rw [hk]; ring_nf; simp; ring

lemma cosh_zero_iff (ζ : ℂ) : Complex.cosh ζ = 0 ↔ (∃ k : ℤ, ζ = ((k : ℂ) + 1 / 2) * π * I) := by
  rw [← Complex.cos_mul_I, Complex.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use -k - 1
    apply (mul_left_inj' I_ne_zero).mp
    rw [hk]
    field_simp [I_sq]
    simp; ring
  · rintro ⟨k, hk⟩
    use -k - 1
    rw [hk]
    field_simp [I_sq]
    simp; ring

lemma sinh_ne_zero_of_re_ne_zero {z : ℂ} (hz : z.re ≠ 0) : Complex.sinh z ≠ 0 := by
  rw [ne_eq, sinh_zero_iff]
  rintro ⟨k, hk⟩
  apply hz
  simpa using congr_arg Complex.re hk

lemma cosh_ne_zero_of_re_ne_zero {z : ℂ} (hz : z.re ≠ 0) : Complex.cosh z ≠ 0 := by
  rw [ne_eq, cosh_zero_iff]
  rintro ⟨k, hk⟩
  apply hz
  simpa using congr_arg Complex.re hk

@[fun_prop]
lemma _root_.ContinuousAt.coth {α : Type*} [TopologicalSpace α] {f : α → ℂ} {s : α}
    (hf : ContinuousAt f s) (h_sinh : Complex.sinh (f s) ≠ 0) :
    ContinuousAt (fun t ↦ CH2.coth (f t)) s := by
  have : CH2.coth = fun z ↦ Complex.cosh z / Complex.sinh z := by
    ext z; simp [CH2.coth, Complex.tanh, div_eq_mul_inv, mul_inv_rev]
  rw [this]
  exact (Complex.continuous_cosh.continuousAt.comp hf).div (Complex.continuous_sinh.continuousAt.comp hf) h_sinh

/-- If `cosh z = 0` then `sinh z ≠ 0`, since `cosh² z - sinh² z = 1`. -/
lemma _root_.Complex.sinh_ne_zero_of_cosh_zero {z : ℂ} (h : Complex.cosh z = 0) :
    Complex.sinh z ≠ 0 := by
  intro hs; have := Complex.cosh_sq_sub_sinh_sq z; simp [h, hs] at this

/-- `Complex.cosh` is not identically zero near any point, so its `meromorphicOrderAt` is finite. -/
lemma meromorphicOrderAt_cosh_ne_top (z : ℂ) : meromorphicOrderAt Complex.cosh z ≠ ⊤ := by
  intro h_top
  have h_p : ∀ᶠ x in nhdsWithin z {z}ᶜ, Complex.cosh x = 0 :=
    meromorphicOrderAt_eq_top_iff.mp h_top
  have h_val : Complex.cosh z = 0 := tendsto_nhds_unique
    (Complex.continuous_cosh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.EventuallyEq.tendsto h_p)
  have h_nhds : (fun x => Complex.cosh x) =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
    rw [eventually_nhdsWithin_iff] at h_p
    filter_upwards [h_p] with x hx
    exact if hxz : x = z then hxz ▸ h_val else hx hxz
  have h_sinh : Complex.sinh z = 0 := by
    simpa [deriv_const, (Complex.hasDerivAt_cosh z).deriv] using h_nhds.deriv_eq
  exact absurd h_sinh (Complex.sinh_ne_zero_of_cosh_zero h_val)

/-- `Complex.sinh` is not identically zero near any point, so its `meromorphicOrderAt` is finite. -/
lemma meromorphicOrderAt_sinh_ne_top (z : ℂ) : meromorphicOrderAt Complex.sinh z ≠ ⊤ := by
  intro h_top
  have h_p : ∀ᶠ x in nhdsWithin z {z}ᶜ, Complex.sinh x = 0 :=
    meromorphicOrderAt_eq_top_iff.mp h_top
  have h_val : Complex.sinh z = 0 := tendsto_nhds_unique
    (Complex.continuous_sinh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.EventuallyEq.tendsto h_p)
  have h_nhds : (fun x => Complex.sinh x) =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
    rw [eventually_nhdsWithin_iff] at h_p
    filter_upwards [h_p] with x hx
    exact if hxz : x = z then hxz ▸ h_val else hx hxz
  have h_cosh : Complex.cosh z = 0 := by
    simpa [deriv_const, (Complex.hasDerivAt_sinh z).deriv] using h_nhds.deriv_eq
  exact absurd h_val (Complex.sinh_ne_zero_of_cosh_zero h_cosh)

/-- `coth` has a pole at `z` if and only if `sinh z = 0`. -/
lemma meromorphicOrderAt_coth_lt_zero_iff (z : ℂ) :
    meromorphicOrderAt coth z < 0 ↔ Complex.sinh z = 0 := by
  have h_coth_eq : coth = Complex.tanh⁻¹ := funext fun z => by unfold coth; simp [one_div]
  have h_mero_tanh : MeromorphicAt Complex.tanh z := by fun_prop
  have hne_top_tanh : meromorphicOrderAt Complex.tanh z ≠ ⊤ := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero h_mero_tanh).mpr
    have h_sinh_ne : ∀ᶠ x in nhdsWithin z {z}ᶜ, Complex.sinh x ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero Complex.analyticAt_sinh.meromorphicAt).mp
        (meromorphicOrderAt_sinh_ne_top z)
    have h_cosh_ne : ∀ᶠ x in nhdsWithin z {z}ᶜ, Complex.cosh x ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero Complex.analyticAt_cosh.meromorphicAt).mp
        (meromorphicOrderAt_cosh_ne_top z)
    filter_upwards [h_sinh_ne, h_cosh_ne] with x hs hc
    rw [Complex.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
    exact ⟨hs, hc⟩
  rw [h_coth_eq, meromorphicOrderAt_inv]
  have h_neg_lt : -meromorphicOrderAt Complex.tanh z < 0 ↔
      0 < meromorphicOrderAt Complex.tanh z := by
    lift meromorphicOrderAt Complex.tanh z to ℤ using hne_top_tanh with a
    norm_cast; omega
  rw [h_neg_lt]
  constructor
  · intro h
    by_cases hc : Complex.cosh z = 0
    · exfalso
      have hsinh_ne := Complex.sinh_ne_zero_of_cosh_zero hc
      have hsinh_ord : meromorphicOrderAt Complex.sinh z = 0 := by
        rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (by fun_prop)]
        exact ⟨_, hsinh_ne, Complex.analyticAt_sinh.continuousAt.continuousWithinAt⟩
      have hcosh_ord : 0 < meromorphicOrderAt Complex.cosh z := by
        rw [← tendsto_zero_iff_meromorphicOrderAt_pos (by fun_prop)]
        exact hc ▸ Complex.analyticAt_cosh.continuousAt.continuousWithinAt
      have hord_neg : meromorphicOrderAt Complex.tanh z < 0 := by
        rw [show Complex.tanh = fun x => Complex.sinh x / Complex.cosh x from
              funext Complex.tanh_eq_sinh_div_cosh]
        push (disch := fun_prop) meromorphicOrderAt
        rw [hsinh_ord]
        lift meromorphicOrderAt Complex.cosh z to ℤ using meromorphicOrderAt_cosh_ne_top z with m hm
        norm_cast at hcosh_ord ⊢; omega
      exact absurd hord_neg (not_lt.mpr h.le)
    · have hcts : ContinuousAt Complex.tanh z := by fun_prop (disch := exact hc)
      have h_tendsto := (tendsto_zero_iff_meromorphicOrderAt_pos h_mero_tanh).mpr h
      have hval : Complex.tanh z = 0 :=
        tendsto_nhds_unique (hcts.tendsto.mono_left nhdsWithin_le_nhds) h_tendsto
      rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at hval
      exact hval.resolve_right hc
  · intro h
    have hc : Complex.cosh z ≠ 0 := Complex.cosh_ne_zero_of_sinh_zero h
    have hcts : ContinuousAt Complex.tanh z := by fun_prop (disch := exact hc)
    have hval : Complex.tanh z = 0 := by rw [Complex.tanh_eq_sinh_div_cosh, h, zero_div]
    rw [← tendsto_zero_iff_meromorphicOrderAt_pos h_mero_tanh]
    convert hcts.tendsto.mono_left nhdsWithin_le_nhds using 1; simp [hval]

@[blueprint
  "Phi-circ-poles"
  (title := "$\\Phi^{\\pm,\\circ}_\\nu$ poles")
  (statement := /--
  The poles of $$\Phi^{\pm,\circ}_\nu(z)$$ are of the form $n - i \nu/2\pi$ for $n \in \mathbb{Z}$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1069)]
theorem Phi_circ.poles (ν ε : ℝ) (_hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_circ ν ε) z < 0 ↔ ∃ n : ℤ, z = n - I * ν / (2 * π) := by
  -- Step 1: Reduce Phi_circ to coth (w/2)
  let w : ℂ → ℂ := fun z ↦ -2 * π * I * z + ν
  have h_ord_eq : meromorphicOrderAt (Phi_circ ν ε) z < 0 ↔ meromorphicOrderAt (fun z ↦ coth (w z / 2)) z < 0 := by
    rw [show Phi_circ ν ε = (fun _ ↦ (1 / 2 : ℂ)) * (fun z ↦ coth (w z / 2) + ε) from rfl]
    rw [meromorphicOrderAt_mul_of_ne_zero (analyticAt_const (v := (1/2 : ℂ)) (x := z)) (by norm_num : (1/2 : ℂ) ≠ 0)]
    have h_coth_mero : MeromorphicAt (fun z ↦ coth (w z / 2)) z := by fun_prop
    constructor
    · intro h
      contrapose! h
      have h_sum := meromorphicOrderAt_add h_coth_mero (MeromorphicAt.const (ε : ℂ) z)
      rw [meromorphicOrderAt_const] at h_sum
      split_ifs at h_sum with h_eps
      · simp_all [gt_iff_lt, add_zero, le_top, inf_of_le_left]
      · exact (le_min (by simpa using h) le_rfl).trans h_sum
    · intro h
      have h_ne : meromorphicOrderAt (fun z ↦ coth (w z / 2)) z ≠ meromorphicOrderAt (fun _ ↦ (ε : ℂ)) z := by
        rw [meromorphicOrderAt_const]; split_ifs <;> simp [h.ne_top, h.ne]
      rw [show (fun z ↦ coth (w z / 2) + ε) = (fun z ↦ coth (w z / 2)) + (fun _ ↦ (ε : ℂ)) from rfl]
      rw [meromorphicOrderAt_add_of_ne h_coth_mero (by fun_prop) h_ne]
      simp [h]
  -- Step 2: Apply "pole of coth iff zero of sinh" via composition
  have h_pole_iff : meromorphicOrderAt (fun z ↦ coth (w z / 2)) z < 0 ↔ (Complex.sinh (w z / 2) = 0) := by
    have h_mero_w : AnalyticAt ℂ (fun z => w z / 2) z := by dsimp [w]; fun_prop
    have h_deriv_w : deriv (fun z => w z / 2) z ≠ 0 := by
      have hd : HasDerivAt (fun z : ℂ ↦ w z / 2) (-π * I) z := by
        convert (((hasDerivAt_id z).const_mul (-2 * π * I)).add (hasDerivAt_const z (ν:ℂ))).div_const 2 using 1
        ring
      rw [hd.deriv]; simp [pi_ne_zero, I_ne_zero]
    have h_comp : meromorphicOrderAt (fun z ↦ coth (w z / 2)) z = meromorphicOrderAt coth (w z / 2) :=
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := coth) h_mero_w h_deriv_w
    rw [h_comp]
    exact meromorphicOrderAt_coth_lt_zero_iff _
  -- Step 3: Rewrite with sinh_zero_iff and solve the linear equation
  rw [h_ord_eq, h_pole_iff, sinh_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use -k
    apply (mul_left_inj' (show (2 * π * I : ℂ) ≠ 0 by simp [pi_ne_zero])).mp
    field_simp [pi_ne_zero, I_ne_zero] at hk ⊢
    have h1 : 2 * π * I * z = ν - 2 * k * π * I := by rw [← hk]; dsimp [w]; ring
    calc
      (2 * π * z : ℂ) = (2 * π * I * z) * (-I) := by ring_nf; simp
      _ = (ν - 2 * k * π * I) * (-I) := by rw [h1]
      _ = 2 * k * π * Complex.I^2 - I * ν := by ring
      _ = 2 * π * ↑(-k) - I * ν := by simp; ring
  · rintro ⟨n, rfl⟩
    use -n
    dsimp [w]
    field_simp [pi_ne_zero, I_ne_zero]
    ring_nf
    simp

@[blueprint
  "Phi-circ-residues"
  (title := "$\\Phi^{\\pm,\\circ}_\\nu$ residues")
  (statement := /--
  The residue of $$\Phi^{\pm,\circ}_\nu(z)$$ at $n - i \nu/2\pi$ is $i/2\pi$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1071)]
theorem Phi_circ.residue (ν ε : ℝ) (_hν : ν > 0) (n : ℤ) :
    (nhdsWithin (n - I * ν / (2 * π)) {n - I * ν / (2 * π)}ᶜ).Tendsto (fun z ↦ (z - (n - I * ν / (2 * π))) * Phi_circ ν ε z) (nhds (I / (2 * π))) := by
  set z₀ : ℂ := n - I * ν / (2 * π)
  set w : ℂ → ℂ := fun z ↦ -2 * π * I * z + ν
  set s : ℂ → ℂ := fun z ↦ w z / 2
  have h_s_z₀ : s z₀ = -n * π * I := by
    dsimp [s, w, z₀]
    field_simp [pi_ne_zero]
    ring_nf
    simp [I_sq]
  have h_cosh_z₀ : Complex.cosh (s z₀) = (-1)^n := by
    rw [h_s_z₀, show -n * π * I = -(n * π * I) by ring, Complex.cosh_neg, Complex.cosh_mul_I]
    norm_cast
    push_cast [Real.cos_int_mul_pi]
    rfl
  have h_sinh_z₀ : Complex.sinh (s z₀) = 0 := by
    rw [h_s_z₀, show -n * π * I = -(n * π * I) by ring, Complex.sinh_neg,
        Complex.sinh_mul_I, Complex.sin_int_mul_pi]
    simp
  have h_s_deriv : HasDerivAt s (-π * I) z₀ := by
    dsimp [s, w]
    have h := (((hasDerivAt_id z₀).const_mul (-2 * π * I)).add
                (hasDerivAt_const z₀ (ν : ℂ))).div_const 2
    convert h using 1; simp only [mul_one, add_zero]; ring
  have h_sinh_deriv : HasDerivAt (fun z ↦ Complex.sinh (s z)) (-π * I * Complex.cosh (s z₀)) z₀ := by
    convert (Complex.hasDerivAt_sinh (s z₀)).comp z₀ h_s_deriv using 1; ring
  have h_slope2 : Filter.Tendsto (fun z => Complex.sinh (s z) / (z - z₀)) (nhdsWithin z₀ {z₀}ᶜ) (nhds (-π * I * Complex.cosh (s z₀))) := by
    have h_eq : slope (fun z => Complex.sinh (s z)) z₀ = fun z => Complex.sinh (s z) / (z - z₀) := by
      ext z; simp [slope, h_sinh_z₀, div_eq_inv_mul]
    have h_slope := h_sinh_deriv.tendsto_slope
    rwa [h_eq] at h_slope
  have h_lim_sinh : Filter.Tendsto (fun z ↦ (z - z₀) / Complex.sinh (s z)) (nhdsWithin z₀ {z₀}ᶜ) (nhds (-π * I * Complex.cosh (s z₀))⁻¹) := by
    simpa [inv_div] using h_slope2.inv₀ (by
      rw [h_cosh_z₀]
      exact mul_ne_zero (by simp [pi_ne_zero, I_ne_zero]) (zpow_ne_zero n (by norm_num)))
  have h_lim_eps : Filter.Tendsto (fun z ↦ (1 / 2 : ℂ) * ε * (z - z₀)) (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    have h : Filter.Tendsto (fun z => z - z₀) (nhds z₀) (nhds (z₀ - z₀)) :=
      Filter.Tendsto.sub Filter.tendsto_id tendsto_const_nhds
    rw [sub_self] at h
    have h2 := Filter.Tendsto.const_mul ((1 / 2 : ℂ) * ε) h
    rw [mul_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have h_lim_cosh : Filter.Tendsto (fun z ↦ Complex.cosh (s z)) (nhdsWithin z₀ {z₀}ᶜ) (nhds (Complex.cosh (s z₀))) :=
    (by dsimp [s, w]; fun_prop : Continuous (fun z ↦ Complex.cosh (s z))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [show (I / (2 * π) : ℂ) = (1 / 2 : ℂ) * (-π * I * Complex.cosh (s z₀))⁻¹ * Complex.cosh (s z₀) + 0 by
    rw [add_zero, mul_inv]
    field_simp [show Complex.cosh (s z₀) ≠ 0 by rw [h_cosh_z₀]; exact zpow_ne_zero n (by norm_num),
      show (-π * I : ℂ) ≠ 0 by simp [pi_ne_zero, I_ne_zero]]
    ring_nf; simp]
  refine Filter.Tendsto.congr (fun z => ?_) ((h_lim_sinh.const_mul (1 / 2 : ℂ)).mul h_lim_cosh |>.add h_lim_eps)
  rw [Phi_circ, coth]
  dsimp [s, w]
  rw [Complex.tanh_eq_sinh_div_cosh]
  simp [one_div]
  ring

@[blueprint
  "Phi-circ-poles-simple"
  (title := "$\\Phi^{\\pm,\\circ}_\\nu$ poles simple")
  (statement := /--
  The poles of $$\Phi^{\pm,\circ}_\nu(z)$$ are all simple.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1070)]
theorem Phi_circ.poles_simple (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_circ ν ε) z = -1 ↔ ∃ n : ℤ, z = n - I * ν / (2 * π) := by
  constructor
  · exact fun h ↦ (Phi_circ.poles ν ε hν z).mp (h ▸ by decide)
  · rintro ⟨n, rfl⟩
    set z₀ := (n : ℂ) - I * ν / (2 * π)
    have hsub : MeromorphicAt (· - z₀ : ℂ → ℂ) z₀ := by fun_prop
    have hf : MeromorphicAt (Phi_circ ν ε) z₀ := (Phi_circ.meromorphic ν ε).meromorphicAt
    have heq : (fun z ↦ (z - z₀) * Phi_circ ν ε z) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] ((· - z₀) * Phi_circ ν ε) :=
      Filter.Eventually.of_forall fun _ ↦ rfl
    have hord₀ : meromorphicOrderAt ((· - z₀) * Phi_circ ν ε) z₀ = 0 := by
      rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hsub.mul hf)]
      exact ⟨_, by norm_num, (Phi_circ.residue ν ε hν n).congr' heq⟩
    have hord₁ : meromorphicOrderAt (· - z₀) z₀ = (1 : ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hsub]
      exact ⟨1, analyticAt_const, one_ne_zero, by simp⟩
    rw [meromorphicOrderAt_mul hsub hf, hord₁] at hord₀
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (by rintro h; simp [h] at hord₀ : meromorphicOrderAt (Phi_circ ν ε) z₀ ≠ ⊤)
    rw [← hm] at hord₀ ⊢
    have h1 : ((1 : ℤ) + m : WithTop ℤ) = (1 + m : ℤ) := by push_cast; ring_nf
    rw [h1] at hord₀
    have : 1 + m = 0 := by exact_mod_cast hord₀
    change (m : WithTop ℤ) = (-1 : ℤ); congr 1; omega

@[blueprint
  "B-def"
  (title := "Definition of $B^\\pm$")
  (statement := /--
  $B^\pm(s) = s/2 (\coth(s/2) \pm 1)$ with the convention $B^\pm(0) = 1$.
  -/)]
noncomputable def B (ε : ℝ) (s : ℂ) : ℂ := if s = 0 then 1 else s * (coth (s / 2) + ε) / 2

@[blueprint
  "B-cts"
  (title := "Continuity of $B^\\pm$ at $0$")
  (statement := /--
  $B^\pm$ is continuous at $0$.
  -/)
  (proof := /-- L'H\^opital's rule can be applied to show the continuity at $0$. -/)
  (latexEnv := "lemma")]
theorem B.continuous_zero (ε : ℝ) : ContinuousAt (B ε) 0 := by
  have h_lim : Filter.Tendsto (fun s : ℂ => s * (Complex.cosh (s / 2)) / (2 * Complex.sinh (s / 2)) + ε * s / 2) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have h_sinh : Filter.Tendsto (fun s : ℂ => Complex.sinh (s / 2) / s) (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
        simpa [div_eq_inv_mul] using HasDerivAt.tendsto_slope_zero
          (HasDerivAt.comp 0 (Complex.hasDerivAt_sinh _)
            (hasDerivAt_id 0 |> HasDerivAt.div_const <| 2))
    have h_lim : Filter.Tendsto (fun s : ℂ => s / (2 * Complex.sinh (s / 2))) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
      convert h_sinh.inv₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) |>
        Filter.Tendsto.const_mul 2⁻¹ using 2 <;> norm_num; ring
    simpa [mul_div_right_comm] using Filter.Tendsto.add
      (h_lim.mul (Complex.continuous_cosh.continuousAt.tendsto.comp
        (continuousWithinAt_id.div_const 2)))
      (Filter.Tendsto.div_const (tendsto_const_nhds.mul continuousWithinAt_id) 2)
  rw [Metric.tendsto_nhdsWithin_nhds] at h_lim
  rw [Metric.continuousAt_iff]
  intro ε hε; rcases h_lim ε hε with ⟨δ, hδ, H⟩; use δ, hδ; intro x hx
  by_cases hx' : x = 0
  · simp_all [B]
  simp_all only [gt_iff_lt, Set.mem_compl_iff, Set.mem_singleton_iff, dist_zero_right, B,
    ↓reduceIte]
  convert H hx' hx using 1; norm_num [coth]
  norm_num [Complex.tanh_eq_sinh_div_cosh]; ring_nf

lemma sinh_ofReal_half_ne_zero {x : ℝ} (hx : x ≠ 0) : Complex.sinh ((x : ℂ) / 2) ≠ 0 := by
  apply sinh_ne_zero_of_re_ne_zero
  simpa using (div_ne_zero hx (by norm_num : (2 : ℝ) ≠ 0))

lemma B_ofReal_eq (ε ν : ℝ) (hν : ν ≠ 0) :
    B ε ν = ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2 := by
  simp [B, ofReal_eq_zero, hν, coth, Complex.tanh_eq_sinh_div_cosh]

theorem B.continuousAt_ofReal_ne_zero (ε s : ℝ) (hs : s ≠ 0) :
    ContinuousAt (fun t : ℝ ↦ B ε (t : ℂ)) s := by
  have h_eq : (fun t : ℝ ↦ (t : ℂ) * (coth ((t : ℂ) / 2) + ε) / 2) =ᶠ[nhds s] (fun t : ℝ ↦ B ε (t : ℂ)) := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    simp [B, ht]
  refine ContinuousAt.congr ?_ h_eq
  refine ContinuousAt.div_const (ContinuousAt.mul (by fun_prop) (ContinuousAt.add ?_ continuousAt_const)) 2
  exact ContinuousAt.coth (by fun_prop) (by simpa using sinh_ofReal_half_ne_zero hs)

@[fun_prop]
theorem B.continuous_ofReal (ε : ℝ) : Continuous (fun t : ℝ ↦ B ε (t : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s = 0
  · subst hs
    exact (B.continuous_zero ε).tendsto.comp Complex.continuous_ofReal.continuousAt
  · exact B.continuousAt_ofReal_ne_zero ε s hs

@[blueprint
  "Phi-star-def"
  (title := "Definition of $\\Phi^{\\pm,\\ast}_\\nu$")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(z) := (B^\pm(w) - B^\pm(v)) / (2\pi i)$$
  where $$w = -2\pi i z + \nu.$$
  -/)]
noncomputable def Phi_star (ν ε : ℝ) (z : ℂ) : ℂ :=
  let w := -2 * π * I * z + (ν : ℂ)
  (B ε w - B ε ν) / (2 * π * I)

@[blueprint
  "Phi-star-zero"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ at zero")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(0) = 0.$$
  -/)
  (proof := /-- This follows from the definition of $B^\pm$ and the fact that $B^\pm(0) = 1$. -/)]
theorem Phi_star_zero (ν ε : ℝ) : Phi_star ν ε 0 = 0 := by simp [Phi_star]

@[fun_prop]
lemma meromorphic_tanh : Meromorphic Complex.tanh := fun z => meromorphicAt_tanh z

lemma meromorphic_coth : Meromorphic coth := fun z => meromorphicAt_coth z

lemma meromorphic_coth' : Meromorphic (fun s : ℂ => Complex.cosh s / Complex.sinh s) := by
  intro z; apply MeromorphicAt.div <;> fun_prop

lemma meromorphic_coth'' : Meromorphic (fun s : ℂ => Complex.cosh (s / 2) / Complex.sinh (s / 2)) := by
  intro z; apply MeromorphicAt.div <;> fun_prop

lemma meromorphicAt_B (ε : ℝ) (z₀ : ℂ) : MeromorphicAt (B ε) z₀ := by
  have h_comp : ∀ z, MeromorphicAt
      (fun s => s * (Complex.cosh (s / 2) / Complex.sinh (s / 2) + ε) / 2) z := by
    have meromorphic_coth'' := meromorphic_coth''
    intro z
    exact (by apply_rules [MeromorphicAt.div, MeromorphicAt.add, MeromorphicAt.mul,
      MeromorphicAt.id, MeromorphicAt.const])
  specialize h_comp z₀
  convert h_comp.congr _
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  unfold B
  rw [Metric.eventually_nhds_iff]
  by_cases h : z₀ = 0
  · simp_all only [gt_iff_lt, dist_zero_right, Set.mem_compl_iff, Set.mem_singleton_iff,
      ↓reduceIte, coth, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj',
        mul_eq_mul_left_iff, add_left_inj, or_false]
    norm_num [Complex.tanh_eq_sinh_div_cosh]
    exact ⟨1, by norm_num⟩
  · simp_all only [gt_iff_lt, Set.mem_compl_iff, Set.mem_singleton_iff, coth, one_div]
    exact ⟨‖z₀‖, norm_pos_iff.mpr h, fun y hy hy' => by
      rw [Complex.tanh_eq_sinh_div_cosh]; aesop⟩

theorem analyticAt_B (ε : ℝ) (z₀ : ℂ) (h_not_pole : ∀ n : ℤ, n ≠ 0 → z₀ ≠ 2 * π * I * n) :
    AnalyticAt ℂ (B ε) z₀ := by
  apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · obtain ⟨V, hV_nhds, b, hb, hV_anal⟩ := (meromorphicAt_B ε z₀).eventually_analyticAt
    filter_upwards [nhdsWithin_le_nhds hV_nhds, self_mem_nhdsWithin] with w hw hne
    have : w ∈ V ∩ b := ⟨hw, hb hne⟩
    have h_an : AnalyticAt ℂ (B ε) w := by rwa [← hV_anal] at this
    exact h_an.differentiableAt
  · unfold B
    by_cases h0 : z₀ = 0
    · subst h0
      have h_lim : Filter.Tendsto (fun s ↦ s * (coth (s / 2) + ε) / 2) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
        have h1 : Filter.Tendsto (fun s ↦ (s / 2) / Complex.sinh (s / 2)) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
          have h_deriv : HasDerivAt (fun s ↦ Complex.sinh (s / 2)) (1 / 2) 0 := by
            have h := (Complex.hasDerivAt_sinh (0 / 2)).comp 0 ((hasDerivAt_id (0 : ℂ)).div_const 2)
            simp only [zero_div, Complex.cosh_zero, id_eq] at h
            convert h using 1; ring
          rw [hasDerivAt_iff_tendsto_slope] at h_deriv
          rw [slope_fun_def_field] at h_deriv
          simp only [Complex.sinh_zero, sub_zero, zero_div] at h_deriv
          have h_inv := h_deriv.inv₀ (by norm_num)
          field_simp [mul_comm] at h_inv
          convert h_inv.div_const 2 using 1
          · ext s; field_simp
          · simp
        have h_lim' : Filter.Tendsto (fun s ↦ ((s / 2) / Complex.sinh (s / 2)) * Complex.cosh (s / 2) + s * ε / 2) (nhdsWithin 0 {0}ᶜ) (nhds (1 * 1 + 0 * ε / 2)) := by
          apply Filter.Tendsto.add
          · apply Filter.Tendsto.mul h1
            have : Filter.Tendsto (fun s ↦ Complex.cosh (s / 2)) (nhds 0) (nhds (Complex.cosh (0 / 2))) := by
              apply (Complex.continuous_cosh.continuousAt.comp (continuous_id.div_const 2).continuousAt).tendsto
            simp only [zero_div, Complex.cosh_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
          · apply Filter.Tendsto.div_const
            apply Filter.Tendsto.mul (Filter.tendsto_id.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
        simp only [mul_one, zero_mul, zero_div, add_zero] at h_lim'
        refine h_lim'.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [coth, Complex.tanh_eq_sinh_div_cosh]
        field_simp
      rw [continuousAt_iff_punctured_nhds]
      simp only [↓reduceIte]
      apply h_lim.congr'
      · filter_upwards [self_mem_nhdsWithin] with s hs
        split_ifs with h
        · contradiction
        · rfl
    · have h_eq : (fun s ↦ if s = 0 then 1 else s * (coth (s / 2) + ε) / 2) =ᶠ[nhds z₀]
          (fun s ↦ s * (coth (s / 2) + ε) / 2) := by
        filter_upwards [continuous_id.continuousAt.eventually_ne h0] with s hs
        split_ifs with h_s0
        · contradiction
        · rfl
      apply ContinuousAt.congr_of_eventuallyEq _ h_eq
      apply ContinuousAt.div_const
      apply ContinuousAt.mul continuousAt_id
      apply ContinuousAt.add _ continuousAt_const
      apply ContinuousAt.coth (continuousAt_id.div_const 2)
      intro hc
      rw [sinh_zero_iff] at hc
      obtain ⟨n, hn⟩ := hc
      have : z₀ = 2 * π * I * n := by
        simp only [id_eq] at hn
        field_simp [hn]
        linear_combination 2 * hn
      by_cases hn0 : n = 0
      · subst hn0; simp at this; contradiction
      · exact h_not_pole n hn0 this


@[blueprint
  "Phi-star-mero"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ meromorphic")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(z)$$ is meromorphic.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/), fun_prop]
theorem Phi_star.meromorphic (ν ε : ℝ) : Meromorphic (Phi_star ν ε) := by
  intro z₀
  have h_comp : MeromorphicAt (fun z => B ε (-2 * Real.pi * Complex.I * z + ν)) z₀ ∧
      MeromorphicAt (fun _ => B ε ν) z₀ := by
    constructor
    · exact (meromorphicAt_B ε _).comp_analyticAt (by fun_prop)
    · exact MeromorphicAt.const (B ε ν) z₀
  exact (h_comp.1.sub h_comp.2).div (MeromorphicAt.const _ z₀)

@[blueprint
  "Phi-star-poles"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ poles")
  (statement := /--
  The poles of $$\Phi^{\pm,\ast}_\nu(z)$$ are of the form $n - i \nu/2\pi$ for $n \in \mathbb{Z} \backslash \{0\}$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1072)]
theorem Phi_star.poles (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_star ν ε) z < 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ z = n - I * ν / (2 * π) := by sorry

@[blueprint
  "Phi-star-residues"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ residues")
  (statement := /--
  The residue of $$\Phi^{\pm,\ast}_\nu(z)$$ at $n - i \nu/2\pi$ is $-in/2\pi$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1073)]
theorem Phi_star.residue (ν ε : ℝ) (hν : ν > 0) (n : ℤ) (hn : n ≠ 0) :
    (nhdsWithin (n - I * ν / (2 * π)) {n - I * ν / (2 * π)}ᶜ).Tendsto
      (fun z ↦ (z - (n - I * ν / (2 * π))) * Phi_star ν ε z) (nhds (-I * n / (2 * π))) := by
  set z₀ : ℂ := n - I * ν / (2 * π)
  set w : ℂ → ℂ := fun z ↦ -2 * π * I * z + ν
  have hw_z₀ : w z₀ = -2 * π * I * n := by
    dsimp [w, z₀]
    field_simp [pi_ne_zero]
    ring_nf
    simp [I_sq]
  have h_circ_res := Phi_circ.residue ν ε hν n
  have h_w_lim : Filter.Tendsto w (nhdsWithin z₀ {z₀}ᶜ) (nhds (w z₀)) := by
    apply ContinuousAt.continuousWithinAt
    unfold w
    fun_prop
  have h_const_lim : Filter.Tendsto (fun z ↦ (z - z₀) * B ε ν) (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    have h : Filter.Tendsto (fun z => z - z₀) (nhds z₀) (nhds (z₀ - z₀)) :=
      Filter.Tendsto.sub Filter.tendsto_id tendsto_const_nhds
    rw [sub_self] at h
    have h2 := Filter.Tendsto.mul_const (B ε ν) h
    rw [zero_mul] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  rw [show (-I * n / (2 * π) : ℂ) = (1 / (2 * π * I)) * (w z₀ * (I / (2 * π)) - 0) by
    rw [hw_z₀]
    have hpi : (π : ℂ) ≠ 0 := by simp [pi_ne_zero]
    field_simp [hpi, I_ne_zero]
    ring_nf]
  refine Filter.Tendsto.congr' ?_ (((h_w_lim.mul h_circ_res).sub h_const_lim).const_mul (1 / (2 * π * I)))
  have hw_cont : ContinuousAt w z₀ := by fun_prop
  have hw_z₀_ne_zero_local : w z₀ ≠ 0 := by
    rw [hw_z₀]
    have hpi : (π : ℂ) ≠ 0 := by simp [pi_ne_zero]
    intro hc
    apply hn
    apply_fun (fun x => x / (-2 * π * I)) at hc
    simpa [hpi, I_ne_zero] using hc
  filter_upwards [nhdsWithin_le_nhds (hw_cont.eventually_ne hw_z₀_ne_zero_local)] with z hz
  have hB : B ε (w z) = w z * (coth (w z / 2) + ε) / 2 := by
    unfold B; split_ifs with h_branch
    · exact False.elim (hz h_branch)
    · rfl
  dsimp only [Phi_star, Phi_circ]
  rw [hB]
  ring

@[blueprint
  "Phi-star-poles-simple"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ poles simple")
  (statement := /--
  The poles of $$\Phi^{\pm,\ast}_\nu(z)$$ are all simple.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)
  (latexEnv := "lemma")]
theorem Phi_star.poles_simple (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_star ν ε) z = -1 ↔ ∃ n : ℤ, n ≠ 0 ∧ z = n - I * ν / (2 * π) := by
  constructor
  · exact fun h ↦ (Phi_star.poles ν ε hν z).mp (h ▸ by decide)
  · rintro ⟨n, hn, rfl⟩
    set z₀ := (n : ℂ) - I * ν / (2 * π)
    have hsub : MeromorphicAt (· - z₀) z₀ := by fun_prop
    have hf : MeromorphicAt (Phi_star ν ε) z₀ := by fun_prop
    have heq : (fun z ↦ (z - z₀) * Phi_star ν ε z) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] ((· - z₀) * Phi_star ν ε) :=
      Filter.Eventually.of_forall fun _ ↦ rfl
    have hord₀ : meromorphicOrderAt ((· - z₀) * Phi_star ν ε) z₀ = 0 := by
      rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hsub.mul hf)]
      exact ⟨_, by simp [hn, pi_ne_zero], (Phi_star.residue ν ε hν n hn).congr' heq⟩
    have hord₁ : meromorphicOrderAt (· - z₀) z₀ = (1 : ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hsub]
      exact ⟨1, analyticAt_const, one_ne_zero, by simp⟩
    rw [meromorphicOrderAt_mul hsub hf, hord₁] at hord₀
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (by rintro h; simp [h] at hord₀ : meromorphicOrderAt (Phi_star ν ε) z₀ ≠ ⊤)
    rw [← hm] at hord₀ ⊢
    have h1 : ((1 : ℤ) + m : WithTop ℤ) = (1 + m : ℤ) := by push_cast; ring_nf
    rw [h1] at hord₀
    have : 1 + m = 0 := by exact_mod_cast hord₀
    change (m : WithTop ℤ) = (-1 : ℤ); congr 1; omega

@[blueprint
  "Phi-cancel"
  (title := "$\\Phi^{\\circ}_\\nu \\pm \\Phi^{\\ast}_\\nu$ pole cancellation")
  (statement := /--
  $\Phi^{\sigma, \circ}_\nu(z) \pm \Phi^{\sigma, \ast}_\nu(z)$ is regular at $\pm 1 - i \nu / 2 \pi$.
  -/)
  (proof := /-- The residues cancel out. -/)
  (latexEnv := "lemma")
  (discussion := 1074)]
theorem Phi_cancel (ν ε σ : ℝ) (hν : ν > 0) (hσ : |σ| = 1) :
    meromorphicOrderAt (fun z ↦ Phi_circ ν ε z + σ * Phi_star ν ε z) ((σ : ℂ) - I * ν / (2 * π)) ≥ 0 := by
  have hσ : σ = 1 ∨ σ = -1 := by grind
  obtain ⟨n, rfl, hn_cases⟩ : ∃ n : ℤ, σ = n ∧ n ≠ 0 := by
    rcases hσ with h | h
    · exact ⟨1, by exact_mod_cast h, one_ne_zero⟩
    · exact ⟨-1, by exact_mod_cast h, by norm_num⟩
  set z₀ : ℂ := n - I * ν / (2 * π)
  set f := fun z ↦ Phi_circ ν ε z + n * Phi_star ν ε z
  have h_mero_f : MeromorphicAt f z₀ := by fun_prop [CH2.Phi_circ]
  have h_tendsto_zero : (nhdsWithin z₀ {z₀}ᶜ).Tendsto (fun z ↦ (z - z₀) * f z) (nhds 0) := by
    convert Filter.Tendsto.add (Phi_circ.residue ν ε hν n)
      (Filter.Tendsto.const_mul (n : ℂ) (Phi_star.residue ν ε hν n hn_cases)) using 1
    · ext z; ring
    · ring_nf
      suffices h : (0 : ℂ) = I * (↑π)⁻¹ * (1 / 2) + I * (↑π)⁻¹ * (n : ℂ) ^ 2 * (-1 / 2) by exact congr_arg nhds h
      have hn_sq : (n : ℂ) ^ 2 = 1 := by
        exact_mod_cast sq_eq_one_iff.mpr hσ
      simp only [hn_sq]
      ring
  rw [tendsto_zero_iff_meromorphicOrderAt_pos (by fun_prop)] at h_tendsto_zero
  change 0 < meromorphicOrderAt ((· - z₀) * f) z₀ at h_tendsto_zero
  rw [meromorphicOrderAt_mul (by fun_prop) h_mero_f] at h_tendsto_zero
  rw [show meromorphicOrderAt (· - z₀) z₀ = (1 : ℤ) from
    (meromorphicOrderAt_eq_int_iff (by fun_prop)).mpr ⟨1, analyticAt_const, one_ne_zero, by simp⟩] at h_tendsto_zero
  change (0 : WithTop ℤ) ≤ meromorphicOrderAt f z₀
  cases h_ord : meromorphicOrderAt f z₀ <;> simp_all
  norm_cast at h_tendsto_zero
  omega


@[blueprint
  "phi-pm-def"
  (title := "Definition of $\\varphi^{\\pm}$")
  (statement := /--
  $$\varphi^{\pm}_\nu(t) := 1_{[-1,1]}(t) ( \Phi^{\pm,\circ}_\nu(t) + \mathrm{sgn}(t) \Phi^{\pm,\ast}_\nu(t) ).$$
  -/)]
noncomputable def ϕ_pm (ν ε : ℝ) (t : ℝ) : ℂ :=
  if -1 ≤ t ∧ t ≤ 1 then
    Phi_circ ν ε (t : ℂ) + t.sign * Phi_star ν ε (t : ℂ)
  else 0

lemma ContDiff.div_real_complex {f g : ℝ → ℂ} {n} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h0 : ∀ x, g x ≠ 0) :
    ContDiff ℝ n (fun x => f x / g x) :=
  hf.mul (hg.inv h0)

@[fun_prop] -- a bit of a hack to specialize Complex.ofRealCLM.contDiff to n=2
lemma Complex.ofRealCLM.contDiff2 : ContDiff ℝ 2 ofReal := Complex.ofRealCLM.contDiff

@[fun_prop]
lemma Complex.contDiff_normSq {n : ℕ∞} : ContDiff ℝ n (normSq : ℂ → ℝ) := by
  have hre : ContDiff ℝ n (Complex.reCLM : ℂ → ℝ) := Complex.reCLM.contDiff
  have him : ContDiff ℝ n (Complex.imCLM : ℂ → ℝ) := Complex.imCLM.contDiff
  change ContDiff ℝ n (fun z : ℂ => z.re * z.re + z.im * z.im)
  exact (hre.mul hre).add (him.mul him)

@[fun_prop]
lemma Complex.contDiff_sinh_real {n : ℕ∞} : ContDiff ℝ n (Complex.sinh : ℂ → ℂ) :=
  Complex.contDiff_sinh.restrict_scalars ℝ

@[fun_prop]
lemma Complex.contDiff_cosh_real {n : ℕ∞} : ContDiff ℝ n (Complex.cosh : ℂ → ℂ) :=
  Complex.contDiff_cosh.restrict_scalars ℝ

lemma h_B_rational (ε : ℝ) : ∀ w : ℂ, w ≠ 0 → B ε w = w * (Complex.cosh (w / 2) / Complex.sinh (w / 2) + ε) / 2 := by
  simp +contextual [Complex.tanh_eq_sinh_div_cosh, B, coth]

lemma h_comp (ε ν : ℝ) (hlam : ν ≠ 0) : ContDiff ℝ 2 (fun t : ℝ => (-2 * Real.pi * Complex.I * t + ν) * (Complex.cosh ((-2 * Real.pi * Complex.I * t + ν) / 2) / Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2) + ε) / 2) := by
  apply_rules [ContDiff.div, ContDiff.mul, ContDiff.add, contDiff_const, contDiff_id] <;> try fun_prop
  · exact Complex.conjCLE.contDiff.comp (by fun_prop)
  · refine Complex.ofRealCLM.contDiff.comp ?_
    refine ContDiff.inv (by fun_prop) ?_
    intro x; rw [ne_eq, Complex.normSq_eq_zero]
    exact sinh_ne_zero_of_re_ne_zero (by simp [hlam])

theorem Phi_star.contDiff_real (ν ε : ℝ) (hlam : ν ≠ 0) :
    ContDiff ℝ 2 (fun (t : ℝ) ↦ Phi_star ν ε (t : ℂ)) := by
  have h_diff_B : ContDiff ℝ 2 (fun t : ℝ => B ε (-2 * Real.pi * Complex.I * t + ν)) := by
    have h_comp := h_comp ε ν hlam
    convert h_comp using 1
    ext t
    by_cases h : (-(2 * Real.pi * Complex.I * t) + ν : ℂ) = 0 <;> simp_all [Complex.sinh, Complex.cosh, h_B_rational]; ring_nf
    norm_num [Complex.ext_iff] at h
    simp_all only [not_true_eq_false]
  convert h_diff_B.sub contDiff_const |> fun h => h.div_const (2 * Real.pi * Complex.I) using 1

theorem Phi_circ.contDiff_real (ν ε : ℝ) (hlam : ν ≠ 0) : ContDiff ℝ 2 (fun t : ℝ => Phi_circ ν ε (t : ℂ)) := by
  have h_diff : ContDiff ℝ 2 (fun t : ℝ => 1 / Complex.tanh ((-2 * Real.pi * Complex.I * t + ν) / 2)) := by
    simp only [Complex.tanh_eq_sinh_div_cosh]
    have h_sinh_cosh_diff : ContDiff ℝ 2 (fun t : ℝ => Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2)) ∧ ContDiff ℝ 2 (fun t : ℝ => Complex.cosh ((-2 * Real.pi * Complex.I * t + ν) / 2)) ∧ ∀ t : ℝ, Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2) ≠ 0 := by
      refine ⟨?_, ?_, ?_⟩
      · have h_sinh_entire : ContDiff ℂ 2 Complex.sinh := by fun_prop
        apply h_sinh_entire.restrict_scalars ℝ |> ContDiff.comp
        refine ContDiff.div_const ?_ _
        refine (ContDiff.add ?_ contDiff_const)
        exact (ContDiff.mul contDiff_const <| Complex.ofRealCLM.contDiff)
      · have h_cosh_entire : ContDiff ℂ 2 Complex.cosh := by fun_prop
        exact (h_cosh_entire.restrict_scalars ℝ).comp (ContDiff.div_const (ContDiff.add (ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff) contDiff_const) _)
      · norm_num [Complex.sinh, Complex.exp_ne_zero]
        norm_num [sub_eq_zero, Complex.exp_ne_zero]
        intro t ht; rw [Complex.exp_eq_exp_iff_exists_int] at ht
        obtain ⟨k, hk⟩ := ht; norm_num [Complex.ext_iff] at hk
        rcases k with ⟨_ | k⟩ <;> norm_num at hk <;> ring_nf at hk <;> norm_num at hk <;>
          cases lt_or_gt_of_ne hlam <;> nlinarith [Real.pi_pos]
    simp_all only [ne_eq, neg_mul, division_def, mul_inv_rev, inv_inv, one_mul]
    exact ContDiff.mul h_sinh_cosh_diff.2.1 (ContDiff.inv h_sinh_cosh_diff.1 fun t => h_sinh_cosh_diff.2.2 t)
  exact ContDiff.mul contDiff_const (h_diff.add contDiff_const)

theorem Phi_circ.continuousAt_imag (ν ε t : ℝ) (ht : 0 ≤ t) (hν : ν > 0) :
    ContinuousAt (fun s : ℝ ↦ Phi_circ ν ε (I * ↑s)) t := by
  dsimp [Phi_circ]
  refine ContinuousAt.mul continuousAt_const (ContinuousAt.add ?_ continuousAt_const)
  exact ContinuousAt.coth (by fun_prop) (sinh_ne_zero_of_re_ne_zero (by simp; nlinarith [Real.pi_pos]))

theorem Phi_star.continuousAt_imag (ν ε t : ℝ) (ht : 0 ≤ t) (hν : ν > 0) :
    ContinuousAt (fun s : ℝ ↦ Phi_star ν ε (I * ↑s)) t := by
  simp only [Phi_star]
  have h_eq (s : ℝ) : -2 * π * I * (I * s) + ν = ↑(2 * π * s + ν) := by
    ring_nf; simp
  simp_rw [h_eq]
  apply ContinuousAt.div_const
  apply ContinuousAt.sub
  · let f : ℝ → ℝ := fun x ↦ 2 * π * x + ν
    have hf : ContinuousAt f t := by fun_prop
    have hg : ContinuousAt (fun x : ℝ ↦ B ε ↑x) (f t) :=
      B.continuousAt_ofReal_ne_zero ε (f t) (by nlinarith [Real.pi_pos])
    exact hg.comp hf
  · exact continuousAt_const

lemma w_re (ν : ℝ) (z : ℂ) : (-2 * π * I * z + ν).re = 2 * π * z.im + ν := by
  simp [neg_mul, add_re, neg_re, mul_re, I_re, I_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im]

lemma w_re_pos {ν : ℝ} {z : ℂ} (hν : ν > 0) (hz_im : 0 ≤ z.im) :
    0 < (-2 * π * I * z + ν).re := by
  rw [w_re]; nlinarith [Real.pi_pos]

lemma w_re_pos_gen {ν : ℝ} {z : ℂ} (hz_im : z.im > -ν / (2 * π)) :
    0 < (-2 * π * I * z + ν).re := by
  rw [w_re]; have := Real.pi_pos; field_simp at *; linarith

lemma w_re_ne {ν : ℝ} {z : ℂ} (h_not_pole : z.im ≠ -ν / (2 * π)) :
    (-2 * π * I * z + ν).re ≠ 0 := by
  rw [w_re]; contrapose! h_not_pole; have := Real.pi_pos; field_simp at *; linarith

lemma sinh_ne_zero_of_not_pole {ν : ℝ} {z : ℂ} (h_not_pole : ∀ n : ℤ, z ≠ n - I * ν / (2 * π)) :
    Complex.sinh ((-2 * π * I * z + ν) / 2) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (sinh_zero_iff _).mp h
  have h_z : z = ↑(-k) - I * ν / (2 * π) := by
    calc z = (2 * π * I * z) / (2 * π * I) := by field_simp [pi_ne_zero, I_ne_zero]
      _ = (ν - (-2 * π * I * z + ν)) / (2 * π * I) := by ring
      _ = (ν - 2 * ((-2 * π * I * z + ν) / 2)) / (2 * π * I) := by ring
      _ = (ν - 2 * (k * π * I)) / (2 * π * I) := by rw [hk]
      _ = ν / (2 * π * I) - (2 * k * π * I) / (2 * π * I) := by field_simp [pi_ne_zero, I_ne_zero]
      _ = -I * ν / (2 * π) - k := by field_simp [pi_ne_zero, I_ne_zero]; ring_nf; simp [I_sq]
      _ = ↑(-k) - I * ν / (2 * π) := by simp; ring
  exact h_not_pole (-k) h_z

lemma w_ne_zero_of_not_pole {ν : ℝ} {z : ℂ} (h_not_pole : ∀ n : ℤ, z ≠ n - I * ν / (2 * π)) :
    -2 * π * I * z + ν ≠ 0 := by
  intro h; specialize h_not_pole 0; apply h_not_pole
  calc z = (2 * π * I * z) / (2 * π * I) := by field_simp [pi_ne_zero, I_ne_zero]
    _ = ν / (2 * π * I) := by
      have : 2 * π * I * z = ν := by rw [← add_zero (2 * π * I * z), ← h]; ring
      rw [this]
    _ = _ := by ring_nf; field_simp; simp

/-- Phi_circ is analytic whenever we are away from the poles. -/
theorem Phi_circ.analyticAt_of_not_pole (ν ε : ℝ) (z : ℂ) (h_not_pole : ∀ n : ℤ, z ≠ n - I * ν / (2 * π)) :
    AnalyticAt ℂ (Phi_circ ν ε) z := by
  set w : ℂ := -2 * π * I * z + ν
  have h_an : AnalyticAt ℂ (fun s : ℂ ↦ coth (s / 2)) w := by
    have heq : (fun s : ℂ ↦ coth (s / 2)) =ᶠ[nhds w] (fun s ↦ Complex.cosh (s / 2) / Complex.sinh (s / 2)) :=
      Filter.Eventually.of_forall (fun s ↦ by unfold coth; simp [Complex.tanh_eq_sinh_div_cosh])
    apply (analyticAt_congr heq).mpr
    fun_prop (disch := exact sinh_ne_zero_of_not_pole h_not_pole)
  unfold Phi_circ; fun_prop (disch := exact [h_an.comp (by fun_prop), by simp [w]; fun_prop])

/-- Phi_circ is analytic whenever we are away from the horizontal line containing the poles. -/
theorem Phi_circ.analyticAt_of_im_ne_pole (ν ε : ℝ) (z : ℂ) (h_not_pole : z.im ≠ -ν / (2 * π)) :
    AnalyticAt ℂ (Phi_circ ν ε) z :=
  Phi_circ.analyticAt_of_not_pole ν ε z (by
    intro n hn; apply h_not_pole
    have h_im : (↑n - I * ↑ν / (2 * ↑π)).im = -ν / (2 * π) := by
      simp [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.div_im]
      field_simp [pi_ne_zero]
    rw [hn, h_im])

theorem Phi_circ.analyticAt_of_im_nonneg (ν ε : ℝ) (z : ℂ) (hν : ν > 0) (hz_im : 0 ≤ z.im) :
    AnalyticAt ℂ (Phi_circ ν ε) z :=
  Phi_circ.analyticAt_of_im_ne_pole ν ε z (by
    have : -ν / (2 * π) < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr hν) (mul_pos (by norm_num) Real.pi_pos)
    linarith)

theorem Phi_circ.analyticAt_of_im_gt_pole (ν ε : ℝ) (z : ℂ) (hz_im : z.im > -ν / (2 * π)) :
    AnalyticAt ℂ (Phi_circ ν ε) z :=
  Phi_circ.analyticAt_of_im_ne_pole ν ε z hz_im.ne'

-- Hermitian symmetry: Φ∘(−t) = conj(Φ∘(t))
private lemma Phi_circ_conj_symm (ν ε t : ℝ) :
    Phi_circ ν ε (-(↑t : ℂ)) = starRingEnd ℂ (Phi_circ ν ε (↑t : ℂ)) := by
  unfold Phi_circ
  rw [starRingEnd_apply, Complex.star_def]
  simp only [map_mul, map_add, map_div₀, conj_ofReal]
  simp only [one_div, neg_mul, mul_neg, neg_neg, map_one, coth_conj]
  congr
  · simp [map_ofNat]
  · simp [map_div₀, map_add, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]

theorem Phi_star.analyticAt_of_not_pole_nz (ν ε : ℝ) (z : ℂ) (h_not_pole : ∀ n : ℤ, n ≠ 0 → z ≠ n - I * ν / (2 * π)) :
    AnalyticAt ℂ (Phi_star ν ε) z := by
  set w : ℂ := -2 * π * I * z + ν
  have hB_an : AnalyticAt ℂ (B ε) w := by
    apply analyticAt_B
    intro n hn hw
    apply h_not_pole (-n) (by simp [hn])
    have : z = ↑(-n) - I * ν / (2 * π) := by
      have h1 : -2 * π * I * z = 2 * π * I * n - ν := by linear_combination hw
      replace h1 := congr_arg (fun x ↦ x / (-2 * π * I)) h1
      dsimp at h1
      rw [mul_div_cancel_left₀ _ (by simp [pi_ne_zero, I_ne_zero] : -2 * π * I ≠ 0)] at h1
      rw [h1]
      field_simp [pi_ne_zero, I_ne_zero]
      ring_nf
      simp [I_sq]
    exact this
  unfold Phi_star; fun_prop (disch := exact [hB_an.comp (by fun_prop), by simp [w]; fun_prop])

theorem Phi_star.analyticAt_of_not_pole (ν ε : ℝ) (z : ℂ) (h_not_pole : ∀ n : ℤ, z ≠ n - I * ν / (2 * π)) :
    AnalyticAt ℂ (Phi_star ν ε) z :=
  Phi_star.analyticAt_of_not_pole_nz ν ε z (fun n _ ↦ h_not_pole n)


theorem Phi_star.analyticAt_of_im_ne_pole (ν ε : ℝ) (z : ℂ) (h_not_pole : z.im ≠ -ν / (2 * π)) :
    AnalyticAt ℂ (Phi_star ν ε) z :=
  Phi_star.analyticAt_of_not_pole ν ε z (fun n hn => h_not_pole (by
    have h_im : (↑n - I * ↑ν / (2 * ↑π)).im = -ν / (2 * π) := by
      simp [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.div_im]
      field_simp [pi_ne_zero]
    rw [hn, h_im]))

theorem Phi_star.analyticAt_of_im_gt_pole (ν ε : ℝ) (z : ℂ) (hz_im : z.im > -ν / (2 * π)) :
    AnalyticAt ℂ (Phi_star ν ε) z :=
  Phi_star.analyticAt_of_im_ne_pole ν ε z hz_im.ne'

theorem Phi_star.analyticAt_of_im_nonneg (ν ε : ℝ) (z : ℂ) (hν : ν > 0) (hz_im : 0 ≤ z.im) :
    AnalyticAt ℂ (Phi_star ν ε) z :=
  Phi_star.analyticAt_of_im_ne_pole ν ε z (by
    have : -ν / (2 * π) < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr hν) (mul_pos (by norm_num) Real.pi_pos)
    linarith)

lemma B_conj (ε : ℝ) (z : ℂ) : (starRingEnd ℂ) (B ε z) = B ε ((starRingEnd ℂ) z) := by
  simp only [B]
  rw [apply_ite (starRingEnd ℂ)]
  have hcond : z = 0 ↔ (starRingEnd ℂ) z = 0 := by
    simp [map_eq_zero]
  simp only [hcond, map_one, map_div₀, map_mul, map_add,
             Complex.conj_ofReal, coth_conj, map_ofNat]

private lemma Phi_star_conj_symm (ν ε t : ℝ) :
    Phi_star ν ε (-(↑t : ℂ)) = -(starRingEnd ℂ (Phi_star ν ε (↑t : ℂ))) := by
  dsimp [Phi_star]
  simp only [neg_mul, map_div₀, map_sub, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [B_conj]
  simp only [map_add, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [B_conj]
  simp [Complex.conj_ofReal]; field_simp

@[blueprint
  "phi-c2-left"
  (title := "$\\varphi$ is $C^2$ on [-1,0]")
  (statement := /--
  $\varphi$ is $C^2$ on $[-1,0]$.
  -/)
  (proof := /-- Since $\Phi^{\pm, \circ}_\nu(z)$ and $\Phi^{\pm, \circ}_\nu(z)$ have no poles on $\mathbb{R}$, they have no poles on some open neighborhood of $[-1,1]$. Hence they are $C^2$ on this interval.  Since $w(0) = \nu$, we see that $\Phi^{\pm, \ast}_\nu(0)=0$, giving the claim. -/)
  (latexEnv := "lemma")]
theorem ϕ_c2_left (ν ε : ℝ) (hlam : ν ≠ 0) : ContDiffOn ℝ 2 (ϕ_pm ν ε) (Set.Icc (-1) 0) := by
  have h_diff_star : ContDiff ℝ 2 (fun t : ℝ => Phi_star ν ε (t : ℂ)) := Phi_star.contDiff_real ν ε hlam
  have h_eq : ∀ t ∈ Set.Icc (-1 : ℝ) 0, ϕ_pm ν ε t = Phi_circ ν ε (t : ℂ) - (if t = 0 then 0 else Phi_star ν ε (t : ℂ)) := by
    unfold ϕ_pm
    intro t ht
    split_ifs
    · norm_num
      grind
    · rw [Real.sign_of_neg (lt_of_le_of_ne ht.2 ‹_›)]
      norm_num [sub_eq_add_neg]
    · grind
    · grind
  refine ContDiffOn.congr ?_ h_eq
  apply_rules [ContDiffOn.sub, (Phi_circ.contDiff_real ν ε hlam).contDiffOn, h_diff_star.contDiffOn]
  refine h_diff_star.contDiffOn.congr fun x hx => ?_
  grind [Phi_star, neg_mul, ofReal_zero, mul_zero, neg_zero, zero_add,
    sub_self, zero_div]

@[blueprint
  "phi-c2-right"
  (title := "$\\varphi$ is $C^2$ on [0,1]")
  (statement := /--
  $\varphi$ is $C^2$ on $[0,1]$.
  -/)
  (proof := /-- Since $\Phi^{\pm, \circ}_\nu(z)$ and $\Phi^{\pm, \circ}_\nu(z)$ have no poles on $\mathbb{R}$, they have no poles on some open neighborhood of $[-1,1]$. Hence they are $C^2$ on this interval.  Since $w(0) = \nu$, we see that $\Phi^{\pm, \ast}_\nu(0)=0$, giving the claim. -/)
  (latexEnv := "lemma")]
theorem ϕ_c2_right (ν ε : ℝ) (hlam : ν ≠ 0) : ContDiffOn ℝ 2 (ϕ_pm ν ε) (Set.Icc 0 1) := by
  have hs : ContDiffOn ℝ 2 (fun t : ℝ => Phi_star ν ε (t : ℂ)) (Set.Icc 0 1) :=
    (Phi_star.contDiff_real ν ε hlam).contDiffOn
  have hcirc : ContDiffOn ℝ 2 (fun t : ℝ => Phi_circ ν ε (t : ℂ)) (Set.Icc 0 1) := (Phi_circ.contDiff_real ν ε hlam).contDiffOn
  exact (hcirc.add hs).congr fun t ht => by
    simp only [ϕ_pm]
    rw [if_pos ⟨by linarith [ht.1], ht.2⟩]
    rcases eq_or_lt_of_le ht.1 with rfl | hpos
    · simp [Real.sign_zero, Phi_star_zero]
    · simp [Real.sign_of_pos hpos]

lemma varphi_differentiableAt_left (ν ε : ℝ) (hlam : ν ≠ 0) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 0) :
    DifferentiableAt ℝ (ϕ_pm ν ε) x :=
  (ϕ_c2_left ν ε hlam).differentiableOn (by norm_num) x (Set.Ioo_subset_Icc_self hx)
    |>.differentiableAt (Icc_mem_nhds hx.1 hx.2)

lemma varphi_differentiableAt_right (ν ε : ℝ) (hlam : ν ≠ 0) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (ϕ_pm ν ε) x :=
  (ϕ_c2_right ν ε hlam).differentiableOn (by norm_num) x (Set.Ioo_subset_Icc_self hx)
    |>.differentiableAt (Icc_mem_nhds hx.1 hx.2)

lemma varphi_differentiableAt_out (ν ε : ℝ) {x : ℝ} (hx : x ∈ (Set.Icc (-1 : ℝ) 1)ᶜ) :
    DifferentiableAt ℝ (ϕ_pm ν ε) x := by
  have h_zero : ϕ_pm ν ε =ᶠ[nhds x] 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    unfold ϕ_pm; exact if_neg hy
  exact Filter.EventuallyEq.differentiableAt_iff h_zero |>.mpr (differentiableAt_const 0)


@[blueprint
  "phi-cts"
  (title := "$\\varphi$ is continuous")
  (statement := /--
  $\varphi$ is continuous on $[0,1]$.
  -/)
  (proof := /-- By the preceding lemmas it suffices to verify continuity at $0, -1, 1$.  Continuity at $0$ is clear.  For $t = -1, 1$, by $\coth \frac{w(t)}{2} = \coth \frac{\nu}{2}$, we see that $B^{\pm}(w(t)) = \left(\frac{\nu}{2} - \pi i t\right)\left(\coth \frac{\nu}{2} \pm 1\right)$, and so
\[
\Phi^{\pm,\star}_{\nu}(t) = -t \cdot \frac{1}{2}\left(\coth \frac{\nu}{2} \pm 1\right) = -t\, \Phi^{\pm,\circ}_{\nu}(t);
\]
hence, by Definition \ref{phi-pm-def}, $\varphi^{\pm}_{\nu}(t) = 0$. Thus, $\varphi^{\pm}_{\nu}$ is continuous at $-1$ and at $1$.
 -/)
  (latexEnv := "lemma")
  (discussion := 1075)]
theorem ϕ_continuous (ν ε : ℝ) (hlam : ν ≠ 0) : Continuous (ϕ_pm ν ε) := by
  have tanh_add_pi (z : ℂ) : Complex.tanh (z + Real.pi * I) = Complex.tanh z := by simp
  have tanh_sub_pi (z : ℂ) : Complex.tanh (z - Real.pi * I) = Complex.tanh z := by
    have h := tanh_add_pi (z - Real.pi * I); rw [sub_add_cancel] at h; exact h.symm
  unfold ϕ_pm
  apply continuous_if
  · intro a ha
    have hfr : frontier {x : ℝ | -1 ≤ x ∧ x ≤ 1} = {-1, 1} := by
      have : {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := by ext; simp
      rw [this, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [hfr] at ha
    rcases ha with rfl | rfl
    · unfold Phi_circ Phi_star B coth
      dsimp only []; push_cast; simp only [Real.sign_neg, Real.sign_one, ofReal_neg, ofReal_one]
      have hw_ne : -2 * Real.pi * I * (-1 : ℂ) + ν ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this
      have hν_ne : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
      simp only [hw_ne, hν_ne, ↓reduceIte]
      have hw2 : (-2 * Real.pi * I * (-1 : ℂ) + ν) / 2 = ν / 2 + Real.pi * I := by ring
      rw [hw2, tanh_add_pi]
      have hpi : (Real.pi : ℂ) * I ≠ 0 := by
        apply mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero
      grind
    · unfold Phi_circ Phi_star B coth
      dsimp only []; push_cast; simp only [Real.sign_one, ofReal_one]
      have hw_ne : -2 * Real.pi * I * (1 : ℂ) + ν ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this
      have hν_ne : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
      simp only [hw_ne, hν_ne, ↓reduceIte]
      have hw2 : (-2 * Real.pi * I * (1 : ℂ) + ν) / 2 = ν / 2 - Real.pi * I := by ring
      rw [hw2, tanh_sub_pi]
      have hpi : (Real.pi : ℂ) * I ≠ 0 := by
        apply mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero
      field_simp
      ring
  · have hcl : closure {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := by
      have : {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := by ext; simp
      rw [this, closure_Icc]
    rw [hcl]
    have hl := (ϕ_c2_left ν ε hlam).continuousOn
    have hr := (ϕ_c2_right ν ε hlam).continuousOn
    have hunion : Set.Icc (-1 : ℝ) 1 = Set.Icc (-1) 0 ∪ Set.Icc 0 1 := by
      ext x; simp
    rw [hunion]
    intro x hx
    rw [continuousWithinAt_union]
    constructor
    · by_cases hxs : x ∈ Set.Icc (-1 : ℝ) 0
      · exact (hl.congr (fun t ht => by simp [ϕ_pm, show -1 ≤ t from ht.1,
            show t ≤ 1 from le_trans ht.2 (by norm_num : (0 : ℝ) ≤ 1)])) x hxs
      · have : ¬ (nhdsWithin x (Set.Icc (-1 : ℝ) 0)).NeBot := by
          rwa [← mem_closure_iff_nhdsWithin_neBot, closure_Icc]
        rw [Filter.not_neBot] at this; simp [ContinuousWithinAt, this]
    · by_cases hxt : x ∈ Set.Icc (0 : ℝ) 1
      · exact (hr.congr (fun t ht => by simp [ϕ_pm, show -1 ≤ t from le_trans (by norm_num : (-1 : ℝ) ≤ 0) ht.1,
            show t ≤ 1 from ht.2])) x hxt
      · have : ¬ (nhdsWithin x (Set.Icc (0 : ℝ) 1)).NeBot := by
          rwa [← mem_closure_iff_nhdsWithin_neBot, closure_Icc]
        rw [Filter.not_neBot] at this; simp [ContinuousWithinAt, this]
  · exact continuousOn_const

theorem ϕ_pm_zero_boundary (ν ε : ℝ) (hlam : ν ≠ 0) : ϕ_pm ν ε (-1) = 0 ∧ ϕ_pm ν ε 1 = 0 := by
  constructor
  · -- Prove for -1 using continuity and the zero-value for t < -1
    have h_eq : ϕ_pm ν ε =ᶠ[nhdsWithin (-1) (Set.Iio (-1))] 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      unfold ϕ_pm; split_ifs with hz_mem <;> try rfl
      exfalso; linarith [Set.mem_Iio.mp hz]
    exact tendsto_nhds_unique
      (tendsto_nhdsWithin_of_tendsto_nhds (ϕ_continuous ν ε hlam).continuousAt)
      (tendsto_const_nhds.congr' h_eq.symm)
  · -- Prove for 1 using continuity and the zero-value for t > 1
    have h_eq : ϕ_pm ν ε =ᶠ[nhdsWithin 1 (Set.Ioi 1)] 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      unfold ϕ_pm; split_ifs with hz_mem <;> try rfl
      exfalso; linarith [Set.mem_Ioi.mp hz]
    exact tendsto_nhds_unique
      (tendsto_nhdsWithin_of_tendsto_nhds (ϕ_continuous ν ε hlam).continuousAt)
      (tendsto_const_nhds.congr' h_eq.symm)

-- 1. Lemma for the exterior derivative at -1
lemma ϕ_pm_hasDerivWithinAt_neg_one_left (ν ε : ℝ) (hlam : ν ≠ 0) :
    HasDerivWithinAt (ϕ_pm ν ε) 0 (Set.Iic (-1)) (-1) := by
  -- Explicitly type the point (-1 : ℝ) and the constant value (0 : ℂ)
  refine HasDerivWithinAt.congr_of_eventuallyEq (hasDerivWithinAt_const (-1 : ℝ) (Set.Iic (-1)) (0 : ℂ)) ?_ ?_
  · -- Show they are equal in a neighborhood within the left-interval (-∞, -1]
    filter_upwards [self_mem_nhdsWithin] with t ht
    unfold ϕ_pm; split_ifs with h_mem
    · have : t = -1 := by linarith [Set.mem_Iic.mp ht, h_mem.1]
      rw [this]; have h := (ϕ_pm_zero_boundary ν ε hlam).1
      simp [ϕ_pm] at h; simp [h]
    · rfl
  · -- Prove the value at the point -1 is indeed 0
    exact (ϕ_pm_zero_boundary ν ε hlam).1

lemma ϕ_pm_hasDerivWithinAt_one_right (ν ε : ℝ) (hlam : ν ≠ 0) :
    HasDerivWithinAt (ϕ_pm ν ε) 0 (Set.Ici 1) 1 := by
  refine HasDerivWithinAt.congr_of_eventuallyEq (hasDerivWithinAt_const (1 : ℝ) (Set.Ici 1) (0 : ℂ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    unfold ϕ_pm; split_ifs with h_mem
    · have : t = 1 := by linarith [Set.mem_Ici.mp ht, h_mem.2]
      rw [this]
      have h := (ϕ_pm_zero_boundary ν ε hlam).2
      simp [ϕ_pm] at h
      simp [h]
    · rfl
  · exact (ϕ_pm_zero_boundary ν ε hlam).2

-- lemma ϕ_pm_differentiableAt_neg_one (ν ε : ℝ) (hlam : ν ≠ 0) :
--     DifferentiableAt ℝ (ϕ_pm ν ε) (-1) := by
--   have h_left := ϕ_pm_hasDerivWithinAt_neg_one_left ν ε hlam
--   have h_right := ϕ_pm_hasDerivWithinAt_neg_one_right ν ε hlam
--   have h_union : HasDerivWithinAt (ϕ_pm ν ε) 0 (Set.Iic 0) (-1) := by
--     refine (h_left.union h_right).congr_set (Filter.EventuallyEq.of_eq ?_)
--     ext t; simp
--   exact h_union.hasDerivAt (Iic_mem_nhds (by norm_num)) |>.differentiableAt

-- lemma ϕ_pm_differentiableAt_one (ν ε : ℝ) (hlam : ν ≠ 0) :
--     DifferentiableAt ℝ (ϕ_pm ν ε) 1 := by
--   have h_left := ϕ_pm_hasDerivWithinAt_one_left ν ε hlam
--   have h_right := ϕ_pm_hasDerivWithinAt_one_right ν ε hlam
--   have h_union : HasDerivWithinAt (ϕ_pm ν ε) 0 (Set.Ici 0) 1 := by
--     refine (h_left.union h_right).congr_set (Filter.EventuallyEq.of_eq ?_)
--     ext t; simp
--   exact h_union.hasDerivAt (Ici_mem_nhds (by norm_num)) |>.differentiableAt


-- -- differentiable varphi except at 0
-- theorem varphi_differentiableAt (ν ε : ℝ) (hlam : ν ≠ 0) {x : ℝ} (hx_nz : x ≠ 0) :
--     DifferentiableAt ℝ (ϕ_pm ν ε) x := by
--   by_cases h_left : x ∈ Set.Ioo (-1 : ℝ) 0
--   · exact varphi_differentiableAt_left ν ε hlam h_left
--   by_cases h_right : x ∈ Set.Ioo (0 : ℝ) 1
--   · exact varphi_differentiableAt_right ν ε hlam h_right
--   by_cases h_out : x ∈ (Set.Icc (-1 : ℝ) 1)ᶜ
--   · exact varphi_differentiableAt_out ν ε h_out
--   -- Remaining points: {-1, 1} (since x ≠ 0 and we've checked the open segments)
--   have h_bound : x = -1 ∨ x = 1 := by
--     have h_in : x ∈ Set.Icc (-1 : ℝ) 1 := Set.notMem_compl_iff.mp h_out
--     simp only [Set.Icc, Set.mem_setOf_eq, Set.Ioo, not_and, not_lt] at h_in h_left h_right
--     rcases h_in with ⟨h1, h2⟩
--     by_cases hx : x = -1; · left; exact hx
--     -- by_cases hx' : x = 0; · right; exact hx'
--     by_cases hx'' : x = 1; · right; exact hx''
--     exfalso
--     if h_neg : x < 0 then
--       have : 0 ≤ x := h_left (lt_of_le_of_ne h1 (Ne.symm hx))
--       exact absurd h_neg (not_lt.mpr this)
--     else
--       have : 1 ≤ x := h_right (lt_of_le_of_ne (not_lt.mp h_neg) hx_nz.symm)
--       exact absurd (lt_of_le_of_ne this (Ne.symm hx'')) (not_lt.mpr h2)
--   rcases h_bound with rfl | rfl
--   · exact ϕ_pm_differentiableAt_neg_one ν ε hlam
--   · exact ϕ_pm_differentiableAt_one ν ε hlam


@[blueprint
  "phi-circ-bound-right"
  (title := "Bound on $\\Phi^{\\pm,\\circ}_\\nu$ from above")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c > - \nu_0/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \geq c$ one has $|\Phi^{\pm,\circ}_{\nu}(z)| \leq C$.
  -/)
  (proof := /-- The function $\coth w = 1 + \frac{2}{e^{2w}-1}$ is bounded away from the imaginary line $\Re w = 0$, that is, it is bounded on $\Re w \geq \kappa$ and $\Re w \leq -\kappa$ for any $\kappa > 0$. The map $w(z) = \nu - 2\pi i z$ sends the line $\Im z = -\frac{\nu}{2\pi}$ to the imaginary line, and the region $\Im z \geq c$ is sent to $\Re w \geq 2\pi c + \nu$.
 -/)
  (latexEnv := "lemma")]
theorem ϕ_circ_bound_right (ν₀ ν₁ ε c : ℝ) (hc : c > -ν₀ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≥ c → ‖Phi_circ ν ε z‖ ≤ C := by
  let κ := Real.pi * c + ν₀ / 2
  have hκ : κ > 0 := by
    norm_num +zetaDelta at *
    rw [div_lt_iff₀] at hc <;> nlinarith [Real.pi_pos]
  have hcoth_bound : ∀ u : ℂ, u.re ≥ κ → ‖(Complex.tanh u)⁻¹‖ ≤ (Real.tanh κ)⁻¹ := by
    intros u hu
    have htanh_sq : ‖Complex.tanh u‖ ^ 2 ≥ (Real.sinh u.re / Real.cosh u.re) ^ 2 := by
      have htanh_sq : ‖Complex.tanh u‖ ^ 2 = (Real.sinh u.re ^ 2 + Real.sin u.im ^ 2) /
          (Real.cosh u.re ^ 2 - Real.sin u.im ^ 2) := by
        norm_num [Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im,
          Complex.sinh, Complex.cosh, Complex.tanh]
        field_simp
        rw [Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity]
        rw [Real.sinh_eq, Real.cosh_eq]; ring_nf
        norm_num [Real.sin_sq, Real.exp_neg]; ring_nf
        rw [show (-2 + Real.cos u.im ^ 2 * 4 + Real.exp u.re ^ 2 + (Real.exp u.re)⁻¹ ^ 2) =
          (-1 / 2 + Real.cos u.im ^ 2 + Real.exp u.re ^ 2 * (1 / 4) +
            (Real.exp u.re)⁻¹ ^ 2 * (1 / 4)) * 4 by ring]
        norm_num; ring
      field_simp
      rw [htanh_sq, mul_div]
      rw [le_div_iff₀]
      · nlinarith only [Real.sin_sq_le_one u.im, Real.sinh_sq u.re]
      · nlinarith only [Real.sin_sq_add_cos_sq u.im, Real.cosh_sq' u.re,
          Real.sinh_pos_iff.mpr (show 0 < u.re by nlinarith [Real.pi_pos])]
    have htanh_ge_tanhκ : Real.sinh u.re / Real.cosh u.re ≥ Real.sinh κ / Real.cosh κ := by
      have htanh_ge_tanhκ : ∀ u v : ℝ, 0 ≤ u → u ≤ v →
          Real.sinh u / Real.cosh u ≤ Real.sinh v / Real.cosh v := by
        intros u v hu hv
        rw [div_le_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)]; ring_nf
        rw [show v = u + (v - u) by ring, Real.sinh_add, Real.cosh_add]
        ring_nf; norm_num [Real.sinh_sq]; ring_nf; aesop
      exact htanh_ge_tanhκ _ _ hκ.le hu
    simp_all only [ge_iff_le, norm_inv, Real.tanh_eq_sinh_div_cosh]
    apply inv_anti₀ (div_pos (Real.sinh_pos_iff.mpr hκ) (Real.cosh_pos _))
    calc Real.sinh κ / Real.cosh κ
        _ ≤ Real.sinh u.re / Real.cosh u.re := htanh_ge_tanhκ
        _ ≤ ‖Complex.tanh u‖ := by
            rw [← Real.sqrt_sq (div_nonneg (Real.sinh_nonneg_iff.mpr
              (hκ.le.trans hu)) (Real.cosh_pos _ |>.le))]
            exact Real.sqrt_le_sqrt (by rw [Complex.sq_norm] at htanh_sq; exact htanh_sq)
  use (1 / 2) * ((Real.tanh κ)⁻¹ + |ε|)
  intros ν hν z hz
  have h_w : ‖(Complex.tanh ((-2 * Real.pi * Complex.I * z + ν) / 2))⁻¹‖ ≤
      (Real.tanh κ)⁻¹ := by
    convert hcoth_bound _ _ using 2
    simp only [Complex.div_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.mul_im]
    norm_num
    have h1 := hν.1
    have h2 : π * c ≤ π * z.im := mul_le_mul_of_nonneg_left hz (le_of_lt Real.pi_pos)
    change π * c + ν₀ / 2 ≤ (2 * π * z.im + ν) * 2 / 4
    linarith
  unfold Phi_circ
  norm_num [coth]
  exact le_trans (norm_add_le _ _) (add_le_add (by simpa using h_w)
    (by norm_num [Complex.norm_def, Complex.normSq]))

@[blueprint
  "phi-circ-bound-left"
  (title := "Bound on $\\Phi^{\\pm,\\circ}_\\nu$ from below")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c < - \nu_1/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \leq c$ one has $|\Phi^{\pm,\circ}_{\nu}(z)| \leq C$.
  -/)
  (proof := /-- Similar to previous lemma. -/)
  (latexEnv := "lemma")]
theorem ϕ_circ_bound_left (ν₀ ν₁ ε c : ℝ) (hc : c < -ν₁ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c → ‖Phi_circ ν ε z‖ ≤ C := by
  set κ := -(ν₁ + 2 * Real.pi * c) / 2 with hκ_def
  have hκ_pos : 0 < κ := by
    rw [lt_div_iff₀] at hc <;> nlinarith [Real.pi_pos]
  have hRe_w : ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c →
      Complex.re ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2) ≤ -κ := by
    norm_num [hκ_def]; intros; nlinarith [Real.pi_pos]
  have hcoth_bound : ∀ z : ℂ, Complex.re z ≤ -κ →
      ‖Complex.cosh z / Complex.sinh z‖ ≤
        (Real.exp κ + Real.exp (-κ)) / (Real.exp κ - Real.exp (-κ)) := by
    intros z hz
    have hsinh : ‖Complex.sinh z‖ ≥ (Real.exp (-z.re) - Real.exp z.re) / 2 := by
      norm_num [Complex.sinh, Complex.norm_def, Complex.normSq]
      norm_num [Complex.exp_re, Complex.exp_im]
      gcongr
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith [Real.sin_sq_add_cos_sq z.im, Real.exp_pos z.re, Real.exp_pos (-z.re),
        mul_pos (Real.exp_pos z.re) (Real.exp_pos (-z.re))]
    have hcosh : ‖Complex.cosh z‖ ≤ (Real.exp z.re + Real.exp (-z.re)) / 2 := by
      norm_num [Complex.cosh, Complex.exp_re, Complex.exp_im]
      gcongr
      exact le_trans (norm_add_le ..) (by norm_num [Complex.norm_exp])
    rw [norm_div]
    rw [div_le_div_iff₀] <;>
      try linarith [Real.exp_pos κ, Real.exp_lt_exp.mpr (show -κ < κ by linarith)]
    · have h_exp_bounds : Real.exp z.re ≤ Real.exp (-κ) ∧ Real.exp (-z.re) ≥ Real.exp κ :=
        ⟨Real.exp_le_exp.mpr hz, Real.exp_le_exp.mpr (by linarith)⟩
      nlinarith [Real.exp_pos κ, Real.exp_pos (-κ),
        Real.exp_lt_exp.2 (show -κ < κ by linarith)]
    · exact lt_of_lt_of_le
        (div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))) zero_lt_two) hsinh
  use (1 / 2) * ((Real.exp κ + Real.exp (-κ)) / (Real.exp κ - Real.exp (-κ)) + |ε|)
  intros ν hν z hz
  have hcoth_w : ‖Complex.cosh ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2) /
      Complex.sinh ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2)‖ ≤
      (Real.exp κ + Real.exp (-κ)) / (Real.exp κ - Real.exp (-κ)) :=
    hcoth_bound _ (hRe_w ν hν z hz)
  have h_triangle : ‖(1 / 2) * (Complex.cosh ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2) /
      Complex.sinh ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2) + ε)‖ ≤
      (1 / 2) * ((Real.exp κ + Real.exp (-κ)) / (Real.exp κ - Real.exp (-κ)) + |ε|) := by
    norm_num at *
    exact le_trans (norm_add_le ..) (add_le_add (by simpa using hcoth_w) (by norm_num))
  convert h_triangle using 1
  unfold Phi_circ coth
  norm_num [Complex.tanh_eq_sinh_div_cosh]

@[blueprint
  "phi-star-bound-right"
  (title := "Bound on $\\Phi^{\\pm,\\ast}_\\nu$ from above")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c > - \nu_0/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \geq c$ one has $|\Phi^{\pm,\star}_{\nu}(z)| \leq C (|z|+1)$.
  -/)
  (proof := /-- The bound on $\Phi^{\pm,\star}_{\nu}$ follows from the bound on $\Phi^{\pm,\circ}_{\nu}$ by $\Phi^{\pm,\star}(z) = \frac{1}{2\pi i}\bigl(w\,\Phi^{\pm,\circ}(w) - \nu\,\Phi^{\pm,\circ}(\nu)\bigr)$.
 -/)
  (latexEnv := "lemma")]
theorem ϕ_star_bound_right (ν₀ ν₁ ε c : ℝ) (hν₀ : 0 < ν₀) (hν₁ : ν₀ ≤ ν₁) (hc : c > -ν₀ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≥ c → ‖Phi_star ν ε z‖ ≤ C * (‖z‖ + 1) := by
  obtain ⟨C₁, hC₁⟩ := ϕ_circ_bound_right ν₀ ν₁ ε c hc
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ‖B ε ν‖ ≤ C₂ := by
    have hB_def : ∀ ν ∈ Set.Icc ν₀ ν₁, B ε ν =
        ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2 := by
      intro ν hν
      exact B_ofReal_eq ε ν (by linarith [hν.1])
    have h_cont : ContinuousOn
        (fun ν : ℝ => ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2)
        (Set.Icc ν₀ ν₁) := by
      refine ContinuousOn.div_const ?_ _
      refine ContinuousOn.mul Complex.continuous_ofReal.continuousOn
        (ContinuousOn.add ?_ continuousOn_const)
      refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro x hx
        simpa using sinh_ofReal_half_ne_zero (by linarith [hx.1])
    obtain ⟨C₂, hC₂⟩ := IsCompact.exists_bound_of_continuousOn
      CompactIccSpace.isCompact_Icc h_cont
    exact ⟨C₂, fun ν hν => by aesop⟩
  have h_bound : ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≥ c →
      ‖Phi_star ν ε z‖ ≤
        (‖z‖ * (2 * Real.pi * C₁) + ν₁ * C₁ + C₂) / (2 * Real.pi) := by
    intro ν hν z hz
    have h_norm_B : ‖B ε (-2 * Real.pi * I * z + ν)‖ ≤
        ‖z‖ * (2 * Real.pi * C₁) + ν₁ * C₁ := by
      have h1 : ‖B ε (-2 * Real.pi * I * z + ν)‖ ≤
          ‖-2 * Real.pi * I * z + ν‖ * C₁ := by
        by_cases h : -2 * Real.pi * I * z + ν = 0 <;>
        simp_all only [gt_iff_lt, Set.mem_Icc, ge_iff_le, Phi_circ, one_div, norm_inv, and_imp, B,
          ↓reduceIte,Complex.norm_mul, Complex.norm_ofNat, Complex.norm_div]
        · norm_num [Complex.ext_iff] at h
          rw [div_lt_iff₀] at hc <;> nlinarith [Real.pi_pos]
        · have := hC₁ ν hν.1 hν.2 z hz
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      have h2 : ‖-2 * Real.pi * I * z + ν‖ ≤ 2 * Real.pi * ‖z‖ + ν₁ := by
        refine le_trans (norm_add_le ..) ?_
        norm_num [abs_of_nonneg Real.pi_pos.le]
        cases abs_cases ν <;> linarith [hν.1, hν.2]
      nlinarith [show 0 ≤ C₁ from le_trans (norm_nonneg _) (hC₁ ν hν z hz)]
    have h_eq : ‖Phi_star ν ε z‖ =
        ‖B ε (-2 * Real.pi * I * z + ν) - B ε ν‖ / (2 * Real.pi) := by
      unfold Phi_star
      norm_num [abs_of_nonneg Real.pi_pos.le]
    exact h_eq ▸ div_le_div_of_nonneg_right
      (le_trans (norm_sub_le ..) (add_le_add h_norm_B (hC₂ ν hν))) (by positivity)
  use (|2 * Real.pi * C₁| + |ν₁ * C₁ + C₂|) / (2 * Real.pi)
  intro ν hν z hz
  convert le_trans (h_bound ν hν z hz) _ using 1
  rw [div_mul_eq_mul_div]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  cases abs_cases (2 * Real.pi * C₁) <;>
    cases abs_cases (ν₁ * C₁ + C₂) <;>
      nlinarith [norm_nonneg z, Real.pi_pos]

@[blueprint
  "phi-star-bound-left"
  (title := "Bound on $\\Phi^{\\pm,\\ast}_\\nu$ from below")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c < - \nu_1/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \leq c$ one has $|\Phi^{\pm,\star}_{\nu}(z)| \leq C (|z|+1)$.
  -/)
  (proof := /-- Similar to previous lemma. -/)
  (latexEnv := "lemma")]
theorem ϕ_star_bound_left (ν₀ ν₁ ε c : ℝ) (hν₀ : 0 < ν₀) (hν₁ : ν₀ ≤ ν₁) (hc : c < -ν₁ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c → ‖Phi_star ν ε z‖ ≤ C * (‖z‖ + 1) := by
  obtain ⟨C₁, hC₁⟩ := ϕ_circ_bound_left ν₀ ν₁ ε c hc
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ‖B ε ν‖ ≤ M := by
    have hB_def : ∀ ν : ℝ, ν ≠ 0 →
        B ε ν = ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2 := by
      exact B_ofReal_eq ε
    have hB_cont : ContinuousOn
        (fun ν : ℝ => ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2)
        (Set.Icc ν₀ ν₁) := by
      refine ContinuousOn.div_const ?_ _
      refine ContinuousOn.mul (Complex.continuous_ofReal.continuousOn)
        (ContinuousOn.add ?_ continuousOn_const)
      refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro x hx₁ hx₂
        have hx_ne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hν₀ hx₁.1)
        exact sinh_ofReal_half_ne_zero hx_ne hx₂
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
      CompactIccSpace.isCompact_Icc hB_cont
    refine ⟨M, fun ν hν => ?_⟩
    specialize hB_def ν (by linarith [hν.1])
    grind
  have hB : ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c →
      ‖B ε (-2 * Real.pi * I * z + ν)‖ ≤ (2 * Real.pi * ‖z‖ + ν₁) * C₁ := by
    intro ν hν z hz
    have hB_eq : B ε (-2 * Real.pi * I * z + ν) =
        (-2 * Real.pi * I * z + ν) * Phi_circ ν ε z := by
      unfold B Phi_circ
      split_ifs <;> simp_all [Complex.ext_iff]
      · rw [lt_div_iff₀] at hc <;> nlinarith [Real.pi_pos]
      · constructor <;> ring
    rw [hB_eq, norm_mul]
    gcongr
    · exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) (norm_nonneg _))
        (by linarith)
    · refine le_trans (norm_add_le _ _) ?_
      norm_num [abs_of_nonneg Real.pi_pos.le]
      cases abs_cases ν <;> linarith [hν.1, hν.2]
    · exact hC₁ ν hν z hz
  have hPhi_star_bound : ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c →
      ‖Phi_star ν ε z‖ ≤ ((2 * Real.pi * ‖z‖ + ν₁) * C₁ + M) / (2 * Real.pi) := by
    intros ν hν z hz
    have h : ‖Phi_star ν ε z‖ ≤
        (‖B ε (-2 * Real.pi * I * z + ν)‖ + ‖B ε ν‖) / (2 * Real.pi) := by
      rw [CH2.Phi_star]
      norm_num [abs_of_nonneg Real.pi_pos.le]
      bound
    exact h.trans (by gcongr <;> linarith [hB ν hν z hz, hM ν hν])
  exact ⟨((2 * Real.pi * 0 + ν₁) * C₁ + M) / (2 * Real.pi) +
    (2 * Real.pi * C₁) / (2 * Real.pi), fun ν hν z hz =>
    le_trans (hPhi_star_bound ν hν z hz) (by
      ring_nf; norm_num [Real.pi_pos.ne']
      norm_num [mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero]
      linarith [
        show 0 ≤ C₁ from le_trans (norm_nonneg _) (hC₁ ν hν z hz),
        show 0 ≤ M from le_trans (norm_nonneg _) (hM ν hν),
        show 0 ≤ C₁ * (ν₁ * (Real.pi⁻¹ * (‖z‖ * (1 / 2)))) from
          mul_nonneg (le_trans (norm_nonneg _) (hC₁ ν hν z hz))
            (mul_nonneg (by linarith) (mul_nonneg (inv_nonneg.2 Real.pi_pos.le)
              (mul_nonneg (norm_nonneg _) (by norm_num)))),
        show 0 ≤ M * (Real.pi⁻¹ * (‖z‖ * (1 / 2))) from by
          apply mul_nonneg (le_trans (norm_nonneg _) (hM ν hν))
          positivity
      ])⟩


@[blueprint
  "B-plus-mono"
  (title := "$B^+$ is increasing")
  (statement := /--
  For real $t$, $B^+(t)$ is increasing.
  -/)
  (proof := /-- For all $t \neq 0$, by the identities $2\cosh\frac{t}{2}\sinh\frac{t}{2} = \sinh t$ and $2\sinh^2\frac{t}{2} = \cosh t - 1$,
\[
\frac{dB^{\pm}(t)}{dt} = \frac{\cosh\frac{t}{2}\sinh\frac{t}{2} - \frac{t}{2} \pm \sinh^2\frac{t}{2}}{2\sinh^2\frac{t}{2}} = \frac{\pm(e^{\pm t} - (1 \pm t))}{4\sinh^2\frac{t}{2}}.
\]
Since $e^u$ is convex, $e^u \geq 1 + u$ for all $u \in \mathbb{R}$. We apply this inequality with $u = t$ and $u = -t$ and obtain the conclusion for $t \neq 0$. Since $B^{\pm}(t)$ is continuous at $t = 0$, we are done.
. -/)
  (latexEnv := "lemma")
  (discussion := 1077)]
theorem B_plus_mono : Monotone (fun t:ℝ ↦ (B 1 t).re) := by
  have B_plus_re_eq : ∀ t : ℝ, t ≠ 0 → (B 1 (t : ℂ)).re = t * Real.exp t / (Real.exp t - 1) := by
    intro t ht
    unfold B
    unfold coth; norm_num [ Complex.tanh, Complex.exp_re, Complex.exp_im ] ; ring_nf;
    norm_num [ Complex.cosh, Complex.sinh, Complex.exp_re, Complex.exp_im, ht ] ; ring_nf;
    norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ] ; ring_nf;
    field_simp;
    rw [ one_add_div, ← add_div, div_eq_div_iff ] <;> ring_nf <;> norm_num [ sub_ne_zero, ht, Real.exp_ne_zero ];
    · simpa [ ← Real.exp_add ] using by ring_nf;
    · cases lt_or_gt_of_ne ht <;> linarith;
    · exact fun h => ht <| by rw [ add_eq_zero_iff_eq_neg ] at h; replace h := congr_arg Real.log h; norm_num at h; linarith;
    · cases lt_or_gt_of_ne ht <;> linarith
  have f_le_one_neg : ∀ t : ℝ, t < 0 → t * Real.exp t / (Real.exp t - 1) ≤ 1 := by
    intro t ht
    rw [ div_le_iff_of_neg ] <;> nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ]
  have f_ge_one_pos : ∀ t : ℝ, 0 < t → 1 ≤ t * Real.exp t / (Real.exp t - 1) := by
    intro t ht
    rw [ le_div_iff₀ ] <;> try linarith [ Real.add_one_le_exp t ];
    nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ]
  have f_mono_pos : MonotoneOn (fun t : ℝ ↦ t * Real.exp t / (Real.exp t - 1)) (Set.Ioi 0) := by
    have h_deriv_pos : ∀ t > 0, deriv (fun t => t * Real.exp t / (Real.exp t - 1)) t ≥ 0 := by
      intro t ht; norm_num [ Real.differentiableAt_exp, ne_of_gt, ht, ne_of_gt, Real.exp_pos t, ne_of_gt, sub_pos, Real.exp_pos, ht, sub_ne_zero.mpr, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t ];
      exact div_nonneg ( by nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ] ) ( sq_nonneg _ )
    intro a ha b hb hab
    have h_mean_val : ∀ a b : ℝ, 0 < a → a < b → ∃ c ∈ Set.Ioo a b, deriv (fun t : ℝ => t * Real.exp t / (Real.exp t - 1)) c = ( (fun t : ℝ => t * Real.exp t / (Real.exp t - 1)) b - (fun t : ℝ => t * Real.exp t / (Real.exp t - 1)) a ) / (b - a) := by
      intros a b ha hb; apply_rules [ exists_deriv_eq_slope ];
      · exact continuousOn_of_forall_continuousAt fun t ht => by
          fun_prop (disch := exact sub_ne_zero_of_ne (by linarith [Real.add_one_le_exp t, ht.1]))
      · exact DifferentiableOn.div ( DifferentiableOn.mul differentiableOn_id ( Real.differentiable_exp.differentiableOn ) ) ( DifferentiableOn.sub ( Real.differentiable_exp.differentiableOn ) ( differentiableOn_const _ ) ) fun x hx => ne_of_gt ( by norm_num; linarith [ hx.1 ] );
    cases eq_or_lt_of_le hab
    · aesop
    obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_val a b ha ‹_›
    have := h_deriv_pos c ( lt_trans ha.out hc₁.1 )
    rw [ hc₂, ge_iff_le, le_div_iff₀ (by lia) ] at this
    linarith
  have f_mono_neg : MonotoneOn (fun t : ℝ ↦ t * Real.exp t / (Real.exp t - 1)) (Set.Iio 0) := by
    have h_deriv_nonneg : ∀ t : ℝ, t < 0 → 0 ≤ deriv (fun t => t * Real.exp t / (Real.exp t - 1)) t := by
      intro t ht; norm_num [ Real.differentiableAt_exp, ne_of_lt, ht, sub_ne_zero ];
      exact div_nonneg ( by nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ] ) ( sq_nonneg _ );
    intros t ht u hu htu;
    by_contra h_contra; push_neg at h_contra; (
    obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo t u, deriv (fun t => t * Real.exp t / (Real.exp t - 1)) c = (u * Real.exp u / (Real.exp u - 1) - t * Real.exp t / (Real.exp t - 1)) / (u - t) := by
      apply_rules [ exists_deriv_eq_slope ]
      · exact htu.lt_of_ne ( by rintro rfl; linarith )
      · exact continuousOn_of_forall_continuousAt fun x hx => by
          fun_prop (disch := exact sub_ne_zero_of_ne (by norm_num; linarith [hx.1, hx.2, ht.out, hu.out]))
      · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( differentiableAt_id.mul ( Real.differentiableAt_exp ) ) ( Real.differentiableAt_exp.sub_const _ ) ( sub_ne_zero_of_ne ( by norm_num; linarith [ hx.1, hx.2, hu.out, ht.out ] ) ) )
    rw [ eq_div_iff ] at hc <;> nlinarith [ hc.1.1, hc.1.2, h_deriv_nonneg c ( by linarith [ hc.1.1, hc.1.2, hu.out ] ) ]);
  intro t₁ t₂ ht;
  by_cases h₁ : t₁ = 0 <;> by_cases h₂ : t₂ = 0
  · grind [one_re, B, ofReal_eq_zero, ofReal_one]
  · grind [one_re, B, ofReal_eq_zero, ofReal_one]
  · grind [one_re, B, ofReal_eq_zero, ofReal_one]
  · simp only [ne_eq, B, ofReal_eq_zero, ofReal_one] at B_plus_re_eq
    simp only [B, ofReal_eq_zero, ofReal_one, h₁, h₂, ite_false, div_ofNat_re, mul_re, ofReal_re, add_re, one_re, ofReal_im, add_im, one_im]
    simp_all
    grind [MonotoneOn]

lemma B_im_eq_zero (ε : ℝ) (t : ℝ) : (B ε t).im = 0 := by
  unfold B; split
  · rw [one_im]
  · rw [coth, show (t : ℂ) / 2 = (t / 2 : ℝ) from by push_cast; ring,
      show tanh ((t / 2 : ℝ) : ℂ) = ⟨tanh (t / 2), 0⟩ from ext (tanh_ofReal_re _) (tanh_ofReal_im _)]
    simp [ofReal_im, ofReal_re]

theorem B_plus_real (t : ℝ) : (B 1 t).im = 0 := B_im_eq_zero 1 t

@[blueprint
  "B-minus-mono"
  (title := "$B^-$ is decreasing")
  (statement := /--
  For real $t$, $B^-(t)$ is decreasing.
  -/)
  (proof := /-- Similar to previous.
. -/)
  (latexEnv := "lemma")
  (discussion := 1078)]
theorem B_minus_mono : Antitone (fun t:ℝ ↦ (B (-1) t).re) := by
  have hasDerivAt_div_exp (c : ℝ) (hne : rexp c - 1 ≠ 0) :
      HasDerivAt (fun s => s / (rexp s - 1))
        ((1 * (rexp c - 1) - c * rexp c) / (rexp c - 1) ^ 2) c :=
    (hasDerivAt_id c).div (show HasDerivAt (fun s => rexp s - 1) (rexp c) c by
      have := (Real.hasDerivAt_exp c).sub (hasDerivAt_const c (1 : ℝ))
      simp only [sub_zero] at this; exact this) hne
  have deriv_nonpos (c : ℝ) (hne : rexp c - 1 ≠ 0) :
      (1 * (rexp c - 1) - c * rexp c) / (rexp c - 1) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (by nlinarith [Real.exp_pos c, Real.exp_neg c,
        mul_inv_cancel₀ (ne_of_gt (Real.exp_pos c)),
        Real.add_one_le_exp c, Real.add_one_le_exp (-c)])
      (sq_nonneg _)
  have mvt_anti (t1 t2 : ℝ) (hall : ∀ x, t1 ≤ x → x ≤ t2 → rexp x - 1 ≠ 0) (hlt : t1 < t2) :
      t2 / (rexp t2 - 1) ≤ t1 / (rexp t1 - 1) := by
    obtain ⟨c, hc, hc_eq⟩ : ∃ c ∈ Set.Ioo t1 t2,
        deriv (fun s => s / (rexp s - 1)) c =
          ((fun s => s / (rexp s - 1)) t2 - (fun s => s / (rexp s - 1)) t1) / (t2 - t1) := by
      rw [show (fun s => s / (rexp s - 1)) = (_root_.id / fun x => rexp x - 1) from by
        ext x; simp [_root_.id]]
      exact exists_deriv_eq_slope _ hlt
        (ContinuousOn.div continuousOn_id
          (ContinuousOn.sub Real.continuous_exp.continuousOn continuousOn_const)
          (fun x hx => hall x hx.1 hx.2))
        (DifferentiableOn.div differentiableOn_id
          (DifferentiableOn.sub Real.differentiable_exp.differentiableOn (differentiableOn_const _))
          (fun x hx => hall x (le_of_lt hx.1) (le_of_lt hx.2)))
    have hne := hall c (le_of_lt hc.1) (le_of_lt hc.2)
    rw [(hasDerivAt_div_exp c hne).deriv] at hc_eq
    have := deriv_nonpos c hne; rw [hc_eq] at this
    cases div_nonpos_iff.mp this with
    | inl h => linarith [h.1] | inr h => linarith [h.2]
  have exp_sub_pos (x : ℝ) (hx : 0 < x) : rexp x - 1 > 0 := by linarith [Real.add_one_le_exp x]
  have exp_sub_neg (x : ℝ) (hx : x < 0) : rexp x - 1 < 0 := by
    nlinarith [Real.exp_pos x, Real.exp_neg x,
      mul_inv_cancel₀ (ne_of_gt (Real.exp_pos x)), Real.add_one_le_exp (-x)]
  have div_exp_le_one (t : ℝ) (ht : 0 < t) : t / (rexp t - 1) ≤ 1 := by
    rw [div_le_iff₀ (exp_sub_pos t ht)]; linarith [Real.add_one_le_exp t]
  have div_exp_ge_one (t : ℝ) (ht : t < 0) : 1 ≤ t / (rexp t - 1) := by
    rw [le_div_iff_of_neg (exp_sub_neg t ht)]
    nlinarith [Real.exp_pos t, Real.exp_neg t,
      mul_inv_cancel₀ (ne_of_gt (Real.exp_pos t)),
      Real.add_one_le_exp t, Real.add_one_le_exp (-t)]
  suffices heq : (fun t:ℝ ↦ (B (-1) t).re) =
      fun t : ℝ => if t = 0 then (1 : ℝ) else t / (rexp t - 1) by
    rw [heq]; intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt; · rfl
    simp only
    by_cases ha0 : a = 0
    · subst ha0; simp only [ite_true, show ¬b = 0 from by linarith, ite_false]
      exact div_exp_le_one b (by linarith)
    · by_cases hb0 : b = 0
      · subst hb0; simp only [ite_true, ha0, ite_false]
        exact div_exp_ge_one a (lt_of_le_of_ne (not_lt.mp (fun h => ha0 (by linarith))) ha0)
      · simp only [ha0, hb0, ite_false]
        by_cases hpos : 0 < a
        · exact mvt_anti a b (fun x hxa hxb => ne_of_gt (exp_sub_pos x (by linarith))) hlt
        · push_neg at hpos
          have ha_neg : a < 0 := lt_of_le_of_ne hpos ha0
          by_cases hneg : b < 0
          · exact mvt_anti a b (fun x hxa hxb => ne_of_lt (exp_sub_neg x (by linarith))) hlt
          · push_neg at hneg
            have hb_pos : 0 < b := lt_of_le_of_ne hneg (Ne.symm hb0)
            linarith [div_exp_le_one b hb_pos, div_exp_ge_one a ha_neg]
  funext t; split
  · next h => subst h; unfold B; simp
  · next ht =>
    unfold B coth
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    simp only [ht', ↓reduceIte, one_div]
    rw [show ((-1 : ℝ) : ℂ) = -1 from by push_cast; ring]
    conv_lhs => rw [show (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) from by push_cast; ring]
    rw [show Complex.tanh ((t / 2 : ℝ) : ℂ) = ((Real.tanh (t / 2) : ℝ) : ℂ) from by
        apply Complex.ext <;> simp,
      show ((Real.tanh (t / 2) : ℝ) : ℂ)⁻¹ = ((Real.tanh (t / 2))⁻¹ : ℝ) from by push_cast; ring,
      show (↑t * (↑(Real.tanh (t / 2))⁻¹ + (-1 : ℂ)) / 2 : ℂ) =
        ((t * ((Real.tanh (t / 2))⁻¹ + (-1 : ℝ)) / 2 : ℝ) : ℂ) from by push_cast; ring]
    simp only [Complex.ofReal_re]; rw [Real.tanh_eq]
    have h2 : rexp (t / 2) - rexp (-(t / 2)) ≠ 0 := by
      intro h; exact ht (by linarith [Real.exp_injective (show rexp (t/2) = rexp (-(t/2)) by linarith)])
    have h3 : rexp t - 1 ≠ 0 := by
      intro h; exact ht ((Real.exp_eq_one_iff t).mp (by linarith))
    rw [inv_div]; field_simp
    nlinarith [show rexp t = rexp (t / 2) * rexp (t / 2) by rw [← Real.exp_add]; ring_nf,
      show rexp (t / 2) * rexp (-(t / 2)) = 1 by rw [← Real.exp_add]; simp,
      Real.exp_pos (t/2), Real.exp_pos (-(t/2))]

theorem B_minus_real (t : ℝ) : (B (-1) t).im = 0 := B_im_eq_zero (-1) t

noncomputable def E (z : ℂ) : ℂ := Complex.exp (2 * π * I * z)

@[fun_prop]
theorem continuous_E : Continuous E := by
  unfold E; fun_prop

lemma cont_E (x : ℝ) : Continuous (fun t:ℝ ↦ E (-t * x)) := by
  simp only [E]
  fun_prop

-- Conjugate of E: E(tx) = conj(E(−tx)) for real t, x
private lemma E_conj_symm (t x : ℝ) :
    E ((↑t : ℂ) * ↑x) = starRingEnd ℂ (E (-(↑t : ℂ) * ↑x)) := by
  dsimp [E]; rw [← Complex.exp_conj]; simp only [starRingEnd_apply]
  ring_nf; simp

@[blueprint
  "varphi-fourier-ident"
  (title := "Fourier transform of $\\varphi$")
  (statement := /--
\[
\widehat{\varphi^{\pm}_{\nu}}(x) = \int_{-1}^{1} \varphi^{\pm}_{\nu}(t)\, e(-tx)\, dt = \int_{-1}^{0} \bigl(\Phi^{\pm,\circ}_{\nu}(t) - \Phi^{\pm,\star}_{\nu}(t)\bigr) e(-tx)\, dt + \int_0^1 \bigl(\Phi^{\pm,\circ}_{\nu}(t) + \Phi^{\pm,\star}_{\nu}(t)\bigr) e(-tx)\, dt.
\]
  -/)
  (proof := /-- By the definition of the Fourier transform, and the fact that $\varphi^{\pm}_{\nu}$ is supported on $[-1,1]$. -/)
  (latexEnv := "sublemma")
  (discussion := 1079)]
theorem varphi_fourier_ident (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) :
    𝓕 (ϕ_pm ν ε) x =
      (∫ t in Set.Icc (-1 : ℝ) 0, (Phi_circ ν ε t - Phi_star ν ε t) * E (-t * x)) +
      (∫ t in Set.Icc 0 (1 : ℝ), (Phi_circ ν ε t + Phi_star ν ε t) * E (-t * x)) := by
  calc 𝓕 (ϕ_pm ν ε) x
    _ = ∫ (t : ℝ), ϕ_pm ν ε t * E (-t * x) := by
      dsimp [FourierTransform.fourier, VectorFourier.fourierIntegral]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with v
      simp only [starRingEnd_apply, star_trivial, E, Real.fourierChar, AddChar.coe_mk,
           Circle.smul_def, smul_eq_mul,
           Circle.coe_exp]
      push_cast
      ring_nf
    _ = ∫ t in Set.Icc (-1:ℝ) 1, ϕ_pm ν ε t * E (-t * x) := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro t ht
      unfold ϕ_pm
      split_ifs with h
      · exact (ht (Set.mem_Icc.mpr h)).elim
      · rw [zero_mul]
    _ = (∫ t in Set.Icc (-1:ℝ) 0, ϕ_pm ν ε t * E (-t * x)) +
        (∫ t in Set.Icc 0 (1:ℝ), ϕ_pm ν ε t * E (-t * x)) := by
      conv_lhs =>
        rw [show Set.Icc (-1 : ℝ) 1 = Set.Icc (-1) 0 ∪ Set.Icc 0 1 from
          (Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm]
      refine MeasureTheory.integral_union_ae ?_ nullMeasurableSet_Icc ?_ ?_
      · have hcap : Set.Icc (-1 : ℝ) 0 ∩ Set.Icc 0 1 = {0} := by
          ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_singleton_iff]
          constructor
          · rintro ⟨⟨-, h1⟩, h2, -⟩; linarith
          · rintro rfl; norm_num
        simp [AEDisjoint, hcap]
      · exact ContinuousOn.integrableOn_compact isCompact_Icc
          ((ϕ_continuous ν ε hlam).continuousOn.mul (cont_E x).continuousOn)
      · exact ContinuousOn.integrableOn_compact isCompact_Icc
          ((ϕ_continuous ν ε hlam).continuousOn.mul (cont_E x).continuousOn)
    _ = (∫ t in Set.Icc (-1:ℝ) 0, (Phi_circ ν ε t - Phi_star ν ε t) * E (-t * x)) +
        (∫ t in Set.Icc 0 (1:ℝ), (Phi_circ ν ε t + Phi_star ν ε t) * E (-t * x)) := by
      congr 1
      · apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        dsimp [ϕ_pm]
        rw [if_pos ⟨ht.1, by linarith [ht.2]⟩]
        rcases ht.2.lt_or_eq with h_neg | rfl
        · rw [Real.sign_of_neg h_neg]; push_cast; ring
        · simp [Real.sign_zero, Phi_star_zero ν ε]
      · apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        dsimp [ϕ_pm]
        rw [if_pos ⟨by linarith [ht.1], ht.2⟩]
        rcases ht.1.lt_or_eq with h_pos | rfl
        · rw [Real.sign_of_pos h_pos]; push_cast; ring
        · simp [Real.sign_zero, Phi_star_zero ν ε]

lemma RectangleIntegral_tendsTo_UpperU' {σ σ' T : ℝ} {f : ℂ → ℂ}
    (htop : Filter.Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) Filter.atTop (nhds 0))
    (hleft : IntegrableOn (fun (y : ℝ) ↦ f (σ + y * I)) (Set.Ici T))
    (hright : IntegrableOn (fun (y : ℝ) ↦ f (σ' + y * I)) (Set.Ici T)) :
    Filter.Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ + I * T) (σ' + I * U)) Filter.atTop
      (nhds (UpperUIntegral f σ σ' T)) := by
  have h_re  (s : ℝ) (t : ℝ) : (s  + I * t).re = s  := by simp
  have h_im  (s : ℝ) (t : ℝ) : (s  + I * t).im = t  := by simp
  have hbot : Filter.Tendsto (fun (_ : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + T * I)) Filter.atTop
      (nhds <| ∫ (x : ℝ) in σ..σ', f (x + T * I)) := tendsto_const_nhds
  have hvert (s : ℝ) (int : IntegrableOn (fun (y : ℝ) ↦ f (s + y * I)) (Set.Ici T)) :
      Filter.Tendsto (fun (U : ℝ) ↦ I * ∫ (y : ℝ) in T..U, f (s + y * I)) Filter.atTop
        (nhds <| I * ∫ (y : ℝ) in Set.Ioi T, f (s + y * I)) := by
    refine (intervalIntegral_tendsto_integral_Ioi T ?_ Filter.tendsto_id).const_smul I
    exact int.mono_set (Set.Ioi_subset_Ici le_rfl)
  have := ((hbot.sub htop).add (hvert σ' hright)).sub (hvert σ hleft)
  simpa only [RectangleIntegral, UpperUIntegral, h_re, h_im, sub_zero,
    ← integral_Ici_eq_integral_Ioi]

lemma tendsto_contour_shift {σ σ' : ℝ} {f : ℂ → ℂ}
    (h_anal : ∀ (U : ℝ), U ≥ 0 → HolomorphicOn f (Rectangle σ (σ' + I * U)))
    (htop : Filter.Tendsto (fun (y : ℝ) ↦ ∫ x in σ..σ', f (x + y * I)) Filter.atTop (nhds 0))
    (hleft : IntegrableOn (fun (y : ℝ) ↦ f (σ + y * I)) (Set.Ici 0))
    (hright : IntegrableOn (fun (y : ℝ) ↦ f (σ' + y * I)) (Set.Ici 0)) :
    Filter.Tendsto (fun (U : ℝ) ↦ (I * ∫ t in Set.Icc 0 U, f (σ + I * t)) - (I * ∫ t in Set.Icc 0 U, f (σ' + I * t)))
      Filter.atTop (nhds (∫ x in σ..σ', f x)) := by
  have h_rect (U : ℝ) (hU : 0 ≤ U) :
      RectangleIntegral f σ (σ' + I * U) =
      (∫ x in σ..σ', f x) - (∫ x in σ..σ', f (x + U * I)) + (I * ∫ y in Set.Icc 0 U, f (σ' + I * y)) - (I * ∫ y in Set.Icc 0 U, f (σ + I * y)) := by
    dsimp [RectangleIntegral, HIntegral, VIntegral]
    have h1 : ∫ (x : ℝ) in σ..σ' + (0 * U - 1 * 0), f (↑x + 0 * I) = ∫ x in σ..σ', f ↑x := by
      rw [show σ' + (0 * U - 1 * 0) = σ' by ring]; apply intervalIntegral.integral_congr; intro x _; simp
    have h2 : ∫ (x : ℝ) in σ..σ' + (0 * U - 1 * 0), f (↑x + ↑(0 + (0 * 0 + 1 * U)) * I) = ∫ x in σ..σ', f (↑x + ↑U * I) := by
      rw [show σ' + (0 * U - 1 * 0) = σ' by ring]; apply intervalIntegral.integral_congr; intro x _; ring_nf
    have h3 : ∫ (y : ℝ) in 0..0 + (0 * 0 + 1 * U), f (↑(σ' + (0 * U - 1 * 0)) + ↑y * I) =
        ∫ y in Set.Icc 0 U, f (↑σ' + I * ↑y) := by
      rw [show 0 + (0 * 0 + 1 * U) = U by ring, show σ' + (0 * U - 1 * 0) = σ' by ring]
      rw [intervalIntegral.integral_of_le hU, MeasureTheory.integral_Icc_eq_integral_Ioc]
      congr 1; funext y; congr 1; ring
    have h4 : ∫ (y : ℝ) in 0..0 + (0 * 0 + 1 * U), f (↑σ + ↑y * I) = ∫ y in Set.Icc 0 U, f (↑σ + I * ↑y) := by
      rw [show 0 + (0 * 0 + 1 * U) = U by ring]
      rw [intervalIntegral.integral_of_le hU, MeasureTheory.integral_Icc_eq_integral_Ioc]
      congr 1; funext y; congr 1; ring
    rw [h1, h2, h3, h4]
  have h_UpperU_zero : UpperUIntegral f σ σ' 0 = 0 := by
    have h1 := RectangleIntegral_tendsTo_UpperU' htop hleft hright
    have e : (↑σ + I * ↑(0:ℝ) : ℂ) = ↑σ := by simp
    simp_rw [e] at h1
    have h2 : Filter.Tendsto (fun (U : ℝ) ↦ RectangleIntegral f σ (σ' + I * U)) Filter.atTop (nhds 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop 0] with U hU
      exact (HolomorphicOn.vanishesOnRectangle (h_anal U hU) subset_rfl).symm
    exact tendsto_nhds_unique h1 h2
  have h_zero : Filter.Tendsto (fun (U : ℝ) ↦ RectangleIntegral f σ (σ' + I * U)) Filter.atTop (nhds 0) := by
    have h1 := RectangleIntegral_tendsTo_UpperU' htop hleft hright
    have e : (↑σ + I * ↑(0:ℝ) : ℂ) = ↑σ := by simp
    simp_rw [e, h_UpperU_zero] at h1
    exact h1
  have h_lim := (tendsto_const_nhds (x := ∫ x in σ..σ', f x)).sub htop
  have h_all := h_lim.sub h_zero
  simp only [sub_zero] at h_all
  refine Filter.Tendsto.congr' ?_ h_all
  filter_upwards [Filter.eventually_ge_atTop 0] with U hU
  rw [h_rect U hU]
  ring

lemma Complex.norm_le_abs_im_add_one {z : ℂ} (hz_re : z.re ∈ Set.Icc (-1 : ℝ) 1) :
    ‖z‖ ≤ |z.im| + 1 := by
  calc ‖z‖
    _ = ‖(z.re : ℂ) + (z.im : ℂ) * I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_I, Complex.norm_real]
        simp only [norm_eq_abs, mul_one]
    _ ≤ 1 + |z.im|     := by
        have : |z.re| ≤ 1 := abs_le.mpr hz_re
        linarith
    _ = |z.im| + 1     := add_comm 1 _

lemma phi_sum_norm_le_of_component_bounds {ν ε : ℝ} {z : ℂ} (hz_re : z.re ∈ Set.Icc (-1 : ℝ) 1)
    {C₁ C₂ : ℝ} (hC₁ : ‖Phi_circ ν ε z‖ ≤ C₁) (hC₂ : ‖Phi_star ν ε z‖ ≤ C₂ * (‖z‖ + 1))
    (y : ℝ) (hy : y = |z.im|) (hy_ge : y ≥ 1) :
    ‖Phi_circ ν ε z‖ + ‖Phi_star ν ε z‖ ≤ (max 0 C₁ + 2 * max 0 C₂) * (y + 1) := by
  have h_norm : ‖z‖ ≤ y + 1 := by rw [hy]; exact Complex.norm_le_abs_im_add_one hz_re
  set C₁' := max 0 C₁
  set C₂' := max 0 C₂
  have hC₁' : 0 ≤ C₁' := le_max_left 0 C₁
  have hC₂' : 0 ≤ C₂' := le_max_left 0 C₂
  have h1 : ‖Phi_circ ν ε z‖ ≤ C₁' := hC₁.trans (le_max_right 0 C₁)
  have h2 : ‖Phi_star ν ε z‖ ≤ C₂' * (‖z‖ + 1) := hC₂.trans (mul_le_mul_of_nonneg_right (le_max_right 0 C₂) (by positivity))
  calc ‖Phi_circ ν ε z‖ + ‖Phi_star ν ε z‖
    _ ≤ C₁' + C₂' * (y + 2) := by
        have h_z_bound : ‖z‖ + 1 ≤ y + 2 := by linarith [h_norm]
        nlinarith [h1, h2, h_z_bound, hC₂']
    _ ≤ (C₁' + 2 * C₂') * (y + 1) := by
        have h_y_bound : y + 2 ≤ 2 * (y + 1) := by linarith [hy_ge]
        nlinarith [h_y_bound, C₁', C₂', hC₁', hC₂']

theorem phi_sum_norm_le_linear_halfplane (ν ε : ℝ) (hν : ν > 0) (T : ℝ) (hT : T ≥ 1) (up : Bool)
    (hsafe : if up then T > -ν / (2 * π) else -T < -ν / (2 * π)) :
    ∃ C, ∀ (z : ℂ), (if up then z.im ≥ T else z.im ≤ -T) → z.re ∈ Set.Icc (-1 : ℝ) 1 →
      ‖Phi_circ ν ε z‖ + ‖Phi_star ν ε z‖ ≤ C * (|z.im| + 1) := by
  cases up
  · have hsafe' : -T < -ν / (2 * π) := by simpa using hsafe
    obtain ⟨C₁, hC₁⟩ := ϕ_circ_bound_left ν ν ε (-T) hsafe'
    obtain ⟨C₂, hC₂⟩ := ϕ_star_bound_left ν ν ε (-T) hν le_rfl hsafe'
    use (max 0 C₁ + 2 * max 0 C₂)
    intro z hz_im hz_re
    have hz_im' : z.im ≤ -T := by simpa using hz_im
    apply phi_sum_norm_le_of_component_bounds hz_re (hC₁ ν (Set.left_mem_Icc.mpr le_rfl) z hz_im')
      (hC₂ ν (Set.left_mem_Icc.mpr le_rfl) z hz_im') |z.im| rfl (by linarith [abs_of_nonpos (show z.im ≤ 0 by linarith)])
  · have hsafe' : T > -ν / (2 * π) := by simpa using hsafe
    obtain ⟨C₁, hC₁⟩ := ϕ_circ_bound_right ν ν ε T hsafe'
    obtain ⟨C₂, hC₂⟩ := ϕ_star_bound_right ν ν ε T hν le_rfl hsafe'
    use (max 0 C₁ + 2 * max 0 C₂)
    intro z hz_im hz_re
    have hz_im' : z.im ≥ T := by simpa using hz_im
    apply phi_sum_norm_le_of_component_bounds hz_re (hC₁ ν (Set.left_mem_Icc.mpr le_rfl) z hz_im')
      (hC₂ ν (Set.left_mem_Icc.mpr le_rfl) z hz_im') |z.im| rfl (by linarith [abs_of_nonneg (show 0 ≤ z.im by linarith)])

theorem phi_bound_upwards (ν ε : ℝ) (hν : ν > 0) :
    ∃ C, ∀ (z : ℂ), z.im ≥ 1 → z.re ∈ Set.Icc (-1 : ℝ) 1 →
      ‖Phi_circ ν ε z‖ + ‖Phi_star ν ε z‖ ≤ C * (z.im + 1) := by
  have h_safe : 1 > -ν / (2 * π) := by
    rw [neg_div]; apply lt_trans (neg_neg_of_pos (by positivity)) zero_lt_one
  obtain ⟨C, hC⟩ := phi_sum_norm_le_linear_halfplane ν ε hν 1 le_rfl true h_safe
  exact ⟨C, fun z hz hz_re ↦ by simpa [abs_of_pos (by linarith : 0 < z.im)] using hC z hz hz_re⟩

theorem phi_bound_downwards (ν ε : ℝ) (hν : ν > 0) :
    ∃ C T₀, T₀ ≥ ν / (2 * π) + 1 ∧ ∀ (z : ℂ), z.im ≤ -T₀ → z.re ∈ Set.Icc (-1 : ℝ) 1 →
      ‖Phi_circ ν ε z‖ + ‖Phi_star ν ε z‖ ≤ C * (-z.im + 1) := by
  set T₀ := max 1 (ν / (2 * π) + 1) with hT₀_def
  have h_safe : -T₀ < -ν / (2 * π) := by
    have : ν / (2 * π) < T₀ := by
      rw [hT₀_def]
      exact (lt_add_one _).trans_le (le_max_right 1 (ν / (2 * π) + 1))
    have h := neg_lt_neg this
    field_simp at h ⊢
    exact h
  obtain ⟨C, hC⟩ := phi_sum_norm_le_linear_halfplane ν ε hν T₀ (le_max_left _ _) false h_safe
  refine ⟨C, T₀, le_max_right _ _, fun z hz hz_re ↦ ?_⟩
  specialize hC z (by simpa using hz) hz_re
  have h_abs : |z.im| = -z.im := abs_of_nonpos (by
    have : T₀ ≥ 1 := le_max_left 1 (ν / (2 * π) + 1)
    linarith [hz])
  rwa [h_abs] at hC


theorem phi_fourier_ray_bound (ν ε σ x : ℝ) (hν : ν > 0) (hsigma : σ ∈ Set.Icc (-1 : ℝ) 1)
    (f : ℂ → ℂ) (hf : ∀ z, ‖f z‖ ≤ (‖Phi_circ ν ε z‖ + ‖Phi_star ν ε z‖) * ‖E (-z * x)‖) :
    ∃ C, ∀ (y : ℝ), y ≥ 1 →
      ‖f (σ + y * I)‖ ≤ C * (y + 1) * rexp (2 * π * x * y) := by
  obtain ⟨Core, hCore⟩ := phi_bound_upwards ν ε hν
  refine ⟨Core, fun y hy => ?_⟩
  have h_exp_eq : ‖E (-(σ + y * I) * x)‖ = rexp (2 * π * x * y) := by
    rw [E, Complex.norm_exp]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.add_im, Complex.neg_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one]
    norm_num
    ring
  refine (hf (σ + y * I)).trans ?_
  rw [h_exp_eq]
  simpa using mul_le_mul_of_nonneg_right (hCore (σ + y * I) (by simpa using hy) (by simpa using hsigma)) (Real.exp_nonneg _)

-- (I * ν / (2 * π)).re = 0 for any ν
lemma pole_re (ν : ℝ) : (I * ν / (2 * π)).re = 0 := by
  simp [Complex.mul_re, Complex.div_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

-- (-(I * ν) / (2 * π)).im = -ν / (2 * π) for any ν
lemma pole_im (ν : ℝ) : (-(I * ν) / (2 * π)).im = -ν / (2 * π) := by
  simp [Complex.neg_im, Complex.mul_im, Complex.div_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_im, Complex.ofReal_re]
  field_simp


theorem Phi_circ.analyticAt_of_re_ne_int (ν ε : ℝ) (z : ℂ) (hz_re : ¬ ∃ n : ℤ, z.re = n) :
    AnalyticAt ℂ (Phi_circ ν ε) z :=
  Phi_circ.analyticAt_of_not_pole ν ε z (fun n hn => hz_re ⟨n, by rw [hn]; simp [pole_re]⟩)

theorem Phi_star.analyticAt_of_re_ne_int (ν ε : ℝ) (z : ℂ) (hz_re : ¬ ∃ n : ℤ, z.re = n) :
    AnalyticAt ℂ (Phi_star ν ε) z :=
  Phi_star.analyticAt_of_not_pole ν ε z (fun n hn => hz_re ⟨n, by rw [hn]; simp [pole_re]⟩)

lemma integrableOn_Phi_circ_m12 (ν ε x T : ℝ) :
    IntegrableOn (fun a : ℝ ↦ Phi_circ ν ε (-1 / 2 - I * ↑a) * cexp (2 * ↑π * I * (-(-1 / 2 - I * ↑a) * ↑x))) (Set.Icc 0 T) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul
  · intro a _
    apply ContinuousAt.continuousWithinAt
    have h_ana : AnalyticAt ℂ (Phi_circ ν ε) (-1 / 2 - I * ↑a) := by
      apply Phi_circ.analyticAt_of_re_ne_int
      intro ⟨n, hn⟩; replace hn := congr_arg (· * 2) hn; norm_num at hn; norm_cast at hn; omega
    exact ContinuousAt.comp (f := fun a : ℝ ↦ (-1 / 2 : ℂ) - I * ↑a) h_ana.continuousAt (by fun_prop)
  · exact Continuous.continuousOn (by fun_prop)

lemma integrableOn_Phi_star_m12 (ν ε x T : ℝ) :
    IntegrableOn (fun a : ℝ ↦ Phi_star ν ε (-1 / 2 - I * ↑a) * cexp (2 * ↑π * I * (-(-1 / 2 - I * ↑a) * ↑x))) (Set.Icc 0 T) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul
  · intro a _
    apply ContinuousAt.continuousWithinAt
    have h_ana : AnalyticAt ℂ (Phi_star ν ε) (-1 / 2 - I * ↑a) := by
      apply Phi_star.analyticAt_of_re_ne_int
      intro ⟨n, hn⟩; replace hn := congr_arg (· * 2) hn; norm_num at hn; norm_cast at hn; omega
    exact ContinuousAt.comp (f := fun a : ℝ ↦ (-1 / 2 : ℂ) - I * ↑a) h_ana.continuousAt (by fun_prop)
  · exact Continuous.continuousOn (by fun_prop)

lemma integrableOn_Phi_circ_p12 (ν ε x T : ℝ) :
    IntegrableOn (fun a : ℝ ↦ Phi_circ ν ε (1 / 2 - I * ↑a) * cexp (2 * ↑π * I * (-(1 / 2 - I * ↑a) * ↑x))) (Set.Icc 0 T) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul
  · intro a _
    apply ContinuousAt.continuousWithinAt
    have h_ana : AnalyticAt ℂ (Phi_circ ν ε) (1 / 2 - I * ↑a) := by
      apply Phi_circ.analyticAt_of_re_ne_int
      intro ⟨n, hn⟩; replace hn := congr_arg (· * 2) hn; norm_num at hn; norm_cast at hn; omega
    exact ContinuousAt.comp (f := fun a : ℝ ↦ (1 / 2 : ℂ) - I * ↑a) h_ana.continuousAt (by fun_prop)
  · exact Continuous.continuousOn (by fun_prop)

lemma integrableOn_Phi_star_p12 (ν ε x T : ℝ) :
    IntegrableOn (fun a : ℝ ↦ Phi_star ν ε (1 / 2 - I * ↑a) * cexp (2 * ↑π * I * (-(1 / 2 - I * ↑a) * ↑x))) (Set.Icc 0 T) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul
  · intro a _
    apply ContinuousAt.continuousWithinAt
    have h_ana : AnalyticAt ℂ (Phi_star ν ε) (1 / 2 - I * ↑a) := by
      apply Phi_star.analyticAt_of_re_ne_int
      intro ⟨n, hn⟩; replace hn := congr_arg (· * 2) hn; norm_num at hn; norm_cast at hn; omega
    exact ContinuousAt.comp (f := fun a : ℝ ↦ (1 / 2 : ℂ) - I * ↑a) h_ana.continuousAt (by fun_prop)
  · exact Continuous.continuousOn (by fun_prop)


theorem integrable_phi_fourier_ray (ν ε σ x : ℝ) (hν : ν > 0) (hsigma : σ ∈ Set.Icc (-1 : ℝ) 1) (hx : x < 0)
    (f : ℂ → ℂ)
    (hf_formula : f = (fun z ↦ (Phi_circ ν ε z + Phi_star ν ε z) * E (-z * x)) ∨
                  f = (fun z ↦ (Phi_circ ν ε z - Phi_star ν ε z) * E (-z * x))) :
    IntegrableOn (fun (y : ℝ) ↦ f (σ + y * I)) (Set.Ici (0 : ℝ)) := by
  have h_cont : ContinuousOn (fun (y : ℝ) ↦ f (σ + y * I)) (Set.Ici (0 : ℝ)) := fun y hy ↦ by
    let z := ↑σ + ↑y * I
    have hy_im : 0 ≤ z.im := by dsimp [z]; simpa using hy
    have h_anal_at_z : AnalyticAt ℂ f z := by
      have hE : AnalyticAt ℂ (fun z : ℂ ↦ E (-z * x)) z := by
        simpa [E] using analyticAt_cexp.comp
          (by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ 2 * π * I * (-z * x)) z)
      rcases hf_formula with h_eq | h_eq <;> rw [h_eq]
      · exact ((Phi_circ.analyticAt_of_im_nonneg ν ε z hν hy_im).add (Phi_star.analyticAt_of_im_nonneg ν ε z hν hy_im)).mul hE
      · exact ((Phi_circ.analyticAt_of_im_nonneg ν ε z hν hy_im).sub (Phi_star.analyticAt_of_im_nonneg ν ε z hν hy_im)).mul hE
    have h_ray : ContinuousAt (fun (y' : ℝ) => ↑σ + ↑y' * I) y :=
      continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    exact ContinuousAt.comp_of_eq h_anal_at_z.continuousAt h_ray rfl |>.continuousWithinAt
  obtain ⟨C, hC⟩ : ∃ C, ∀ y : ℝ, y ≥ 1 → ‖f (σ + y * I)‖ ≤ C * (y + 1) * rexp (2 * π * x * y) := by
    apply phi_fourier_ray_bound ν ε σ x hν hsigma
    intro z
    rcases hf_formula with rfl | rfl <;> simp only [norm_mul]
    · exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
  let g (y : ℝ) := if y < 1 then (if y < 0 then 0 else ‖f (σ + y * I)‖) else C * (y + 1) * rexp (2 * π * x * y)
  have h_int_decay : IntegrableOn (fun y ↦ (y + 1) * rexp (2 * π * x * y)) (Set.Ici 1) := by
    have htlam : 2 * π * x < 0 := by nlinarith [hx, Real.pi_pos]
    have h1 : IntegrableOn (fun (y : ℝ) ↦ rexp (2 * π * x * y)) (Set.Ici 1) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_exp_mul_Ioi htlam 1
    have h2 : IntegrableOn (fun y ↦ y * rexp (2 * π * x * y)) (Set.Ici 1) := by
      have hb : 0 < -(2 * π * x) := by nlinarith [hx, Real.pi_pos]
      have h_int := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) (by norm_num) hb
      refine IntegrableOn.congr_fun (f := fun (y : ℝ) ↦ y ^ (1 : ℝ) * rexp (- -(2 * π * x) * y ^ (1 : ℝ))) ?_ ?_ measurableSet_Ici
      · apply h_int.mono_set
        intro y hy; exact Set.mem_Ioi.mpr (by linarith [Set.mem_Ici.mp hy])
      · intro y _; dsimp; simp only [Real.rpow_one, neg_neg]
    simpa [add_mul] using h2.add h1
  have hg : IntegrableOn g (Set.Ici 0) := by
    rw [show Set.Ici (0 : ℝ) = Set.Ico 0 1 ∪ Set.Ici 1 from
      (Set.Ico_union_Ici_eq_Ici zero_le_one).symm]
    refine IntegrableOn.union ?_ ?_
    · have h_int_Icc : IntegrableOn (fun y : ℝ ↦ ‖f (↑σ + ↑y * I)‖) (Set.Icc 0 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact h_cont.norm.mono Set.Icc_subset_Ici_self
      exact IntegrableOn.congr_fun (h_int_Icc.mono_set Set.Ico_subset_Icc_self)
        (fun y hy ↦ by simp [g, hy.2, not_lt.mpr hy.1]) measurableSet_Ico
    · exact IntegrableOn.congr_fun (h_int_decay.const_mul C)
        (fun y hy ↦ by simp [g, not_lt.mpr (Set.mem_Ici.mp hy)]; ring)
        measurableSet_Ici
  refine hg.mono' (h_cont.aestronglyMeasurable measurableSet_Ici) <| (ae_restrict_iff' measurableSet_Ici).mpr <| ae_of_all _ (fun y hy ↦ ?_)
  by_cases h : y < 1
  · simp [g, h, not_lt.mpr (Set.mem_Ici.mp hy)]
  · simpa [g, h] using hC y (not_lt.mp h)

lemma tendsto_T_plus_one_mul_exp_atTop_nhds_zero {k : ℝ} (hk : k < 0) (C : ℝ) :
    Filter.Tendsto (fun (T : ℝ) ↦ C * (T + 1) * Real.exp (k * T)) Filter.atTop (nhds 0) := by
  have h_top : Filter.Tendsto (fun T ↦ - k * T) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_id.const_mul_atTop (by linarith)
  have h_exp_lim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.comp h_top
  have h_exp_lim0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0 |>.comp h_top
  simp only [Function.comp_def, pow_one, pow_zero, one_mul, neg_mul, neg_neg] at h_exp_lim h_exp_lim0
  have h_Texp : Filter.Tendsto (fun T ↦ T * Real.exp (k * T)) Filter.atTop (nhds 0) := by
    convert h_exp_lim.const_mul (-k⁻¹) using 1
    · ext T; field_simp [hk.ne]
    · simp
  have h_add : Filter.Tendsto (fun T ↦ (T + 1) * Real.exp (k * T)) Filter.atTop (nhds 0) := by
    simp only [add_mul, one_mul]
    convert h_Texp.add h_exp_lim0 using 1
    simp
  convert h_add.const_mul C using 1
  · ext T; ring
  · simp

/-- A utility lemma for integrability of Fourier-like components along a compact path. -/
theorem integrable_fourier_path (a b x : ℝ) (f : ℝ → ℂ) (p : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc a b)) (hp : ContinuousOn p (Set.Icc a b)) :
    Integrable (fun t ↦ f t * E (-p t * x)) (volume.restrict (Set.Icc a b)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply ContinuousOn.mul hf
  dsimp [E]
  fun_prop

lemma horizontal_integral_phi_fourier_vanish (ν ε x a b : ℝ) (hν : ν > 0) (hx : x < 0)
    (hab_in : Set.Icc a b ⊆ Set.Icc (-1) 1) (hab : a ≤ b)
    (f : ℂ → ℂ)
    (hf_anal : ∀ T : ℝ, T ≥ 1 → ContinuousOn f (Rectangle (↑a) (↑b + I * ↑T)))
    (hf_bound : ∀ T : ℝ, T ≥ 1 → ∀ t ∈ Set.Icc a b, ‖f (t + I * T)‖ ≤ (‖Phi_circ ν ε (t + I * T)‖ + ‖Phi_star ν ε (t + I * T)‖) * ‖E (-(t + I * T) * x)‖) :
    Filter.Tendsto (fun T : ℝ ↦ ∫ t in a..b, f (t + I * T)) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := phi_bound_upwards ν ε hν
  have h_int_bound (T : ℝ) (hT : T ≥ 1) : ‖∫ t in a..b, f (t + I * T)‖ ≤ (b - a) * C * (T + 1) * Real.exp (2 * π * x * T) := by
    calc ‖∫ t in a..b, f (↑t + I * ↑T)‖
      _ ≤ ∫ t in a..b, ‖f (↑t + I * ↑T)‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, C * (T + 1) * Real.exp (2 * π * x * T) := by
          apply intervalIntegral.integral_mono_on hab
          · refine ContinuousOn.intervalIntegrable ?_
            refine ContinuousOn.norm ?_
            rw [Set.uIcc_of_le hab]
            have hg : Continuous (fun t : ℝ ↦ (↑t : ℂ) + I * ↑T) := by fun_prop
            have h_seg_in : (fun t ↦ ↑t + I * ↑T) '' Set.Icc a b ⊆ Rectangle a (b + I * T) := by
              intro z ⟨t, ht, hz⟩
              subst hz
              rw [mem_Rect (by simpa using hab) (by simpa using hT.trans' (by norm_num : (0 : ℝ) ≤ 1))]
              simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
              exact ⟨ht.1, ht.2, by linarith, le_refl _⟩
            exact (hf_anal T hT).mono h_seg_in |>.comp hg.continuousOn (Set.mapsTo_image _ _)
          · exact intervalIntegrable_const
          · intro t ht
            specialize hf_bound T hT t ht
            have h_phi := hC (↑t + I * T) (by simpa using hT) (hab_in (by simpa using ht))
            calc ‖f (↑t + I * ↑T)‖
              _ ≤ (‖Phi_circ ν ε (↑t + I * ↑T)‖ + ‖Phi_star ν ε (↑t + I * ↑T)‖) * ‖E (-(↑t + I * ↑T) * ↑x)‖ := hf_bound
              _ = (‖Phi_circ ν ε (↑t + I * ↑T)‖ + ‖Phi_star ν ε (↑t + I * ↑T)‖) * Real.exp (2 * π * x * T) := by
                  congr 1; dsimp [E]; rw [Complex.norm_exp]; simp; ring_nf
              _ ≤ C * (T + 1) * Real.exp (2 * π * x * T) := by
                  rw [Complex.add_im ↑t (I * ↑T)] at h_phi
                  simpa using mul_le_mul_of_nonneg_right h_phi (Real.exp_nonneg _)
      _ = (b - a) * (C * (T + 1) * Real.exp (2 * π * x * T)) := intervalIntegral.integral_const _
      _ = (b - a) * C * (T + 1) * Real.exp (2 * π * x * T) := by ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let h_decay : ℝ → ℝ := fun T' ↦ (b - a) * C * (T' + 1) * rexp (2 * π * x * T')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ 0) (h := h_decay) tendsto_const_nhds ?_ ?_ ?_
  · exact tendsto_T_plus_one_mul_exp_atTop_nhds_zero (by nlinarith [hx, Real.pi_pos]) ((b - a) * C)
  · filter_upwards with T'; exact norm_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop 1] with T' hT
    exact h_int_bound T' hT

@[blueprint
  "shift-upwards"
  (title := "Contour shifting upwards")
  (statement := /-- If $x < 0$, then
\begin{multline}\label{eq:1.5}
\widehat{\varphi^{\pm}_{\nu}}(x) = \int_{-1+i\infty}^{-1} \bigl(\Phi^{\pm,\circ}_{\nu}(z) - \Phi^{\pm,\star}_{\nu}(z)\bigr) e(-zx)\, dz \\
+ \int_{1}^{1+i\infty} \bigl(\Phi^{\pm,\circ}_{\nu}(z) + \Phi^{\pm,\star}_{\nu}(z)\bigr) e(-zx)\, dz + 2\int_0^{i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz.
\end{multline}
  -/)
  (proof := /-- Since $\Phi^{\pm,\circ}_{\nu}(z) \pm \Phi^{\pm,\star}_{\nu}(z)$ has no poles in the upper half plane, we can shift contours upwards, as we may: for $\Im z \to \infty$, $e(-zx) = e^{-2\pi i z x}$ decays exponentially on $\Im z$, while, by Lemma~1.3, $\Phi^{\pm,\circ}_{\nu}(z) \pm \Phi^{\pm,\star}_{\nu}(z)$ grows at most linearly, and so the contribution of a moving horizontal segment goes to $0$ as $\Im z \to \infty$. -/)
  (latexEnv := "sublemma")
  (discussion := 1080)]
theorem shift_upwards (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x < 0) :
    Filter.atTop.Tendsto
      (fun T : ℝ ↦
        (I * ∫ t in Set.Icc 0 T,
          (Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t)) * E (-(-1 + I * t) * x))
        - (I * ∫ t in Set.Icc 0 T,
          (Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t)) * E (-(1 + I * t) * x))
        + (2 * I * ∫ t in Set.Icc 0 T,
          Phi_star ν ε (I * t) * E (-(I * t) * x)))
      (nhds (𝓕 (ϕ_pm ν ε) x)) := by
  have hlam : ν ≠ 0 := by linarith
  set A : ℂ :=
    ∫ t in Set.Icc (-1 : ℝ) 0, (Phi_circ ν ε t - Phi_star ν ε t) * E (-t * x)
  set B : ℂ :=
    ∫ t in Set.Icc 0 (1 : ℝ), (Phi_circ ν ε t + Phi_star ν ε t) * E (-t * x)
  have hfourier : 𝓕 (ϕ_pm ν ε) x = A + B := by
    simpa [A, B] using varphi_fourier_ident ν ε hlam x
  have h_exp_decay (T : ℝ) (t : ℝ) : ‖E (-(t + I * T) * x)‖ = Real.exp (2 * π * x * T) := by
    dsimp [E]
    rw [Complex.norm_exp]
    simp; ring_nf
  have hAshift :
      Filter.atTop.Tendsto
        (fun T : ℝ ↦
          (I * ∫ t in Set.Icc 0 T,
            (Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t)) * E (-(-1 + I * t) * x))
          - (I * ∫ t in Set.Icc 0 T,
            (Phi_circ ν ε (I * t) - Phi_star ν ε (I * t)) * E (-(I * t) * x)))
        (nhds A) := by
    let f : ℂ → ℂ := fun z ↦ (Phi_circ ν ε z - Phi_star ν ε z) * E (-z * x)
    have h_anal (U : ℝ) (hU : 0 ≤ U) : HolomorphicOn f (Rectangle (↑(-1:ℝ)) (↑(0:ℝ) + I * U)) := by
      intro z hz; have hi : 0 ≤ z.im := by
        have hz_im : z.im ∈ Set.uIcc 0 U := by simpa [Rectangle] using hz.2
        rw [Set.uIcc_of_le hU] at hz_im
        exact hz_im.1
      exact (AnalyticAt.sub (Phi_circ.analyticAt_of_im_nonneg ν ε z hν hi) (Phi_star.analyticAt_of_im_nonneg ν ε z hν hi)).differentiableAt.mul
        (by dsimp [E]; fun_prop)
        |>.differentiableWithinAt
    have h_shift := tendsto_contour_shift (σ := -1) (σ' := 0) (f := f) h_anal ?_ ?_ ?_
    · have hA_eq : ∫ x in (-1:ℝ)..0, f x = A := by
        dsimp [A]
        rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Icc_eq_integral_Ioc]
      have h_final : (fun (T : ℝ) ↦ (I * ∫ (t : ℝ) in Set.Icc 0 T, f (-1 + I * ↑t)) - (I * ∫ (t : ℝ) in Set.Icc 0 T, f (I * ↑t))) =
          (fun (U : ℝ) ↦ (I * ∫ (t : ℝ) in Set.Icc 0 U, f (↑(-1 : ℝ) + I * ↑t)) - (I * ∫ (t : ℝ) in Set.Icc 0 U, f (↑(0 : ℝ) + I * ↑t))) := by
        ext U
        have h1 : ∫ (t : ℝ) in Set.Icc 0 U, f (-1 + I * ↑t) = ∫ (t : ℝ) in Set.Icc 0 U, f (↑(-1 : ℝ) + I * ↑t) := by congr 1; ext t; simp
        have h2 : ∫ (t : ℝ) in Set.Icc 0 U, f (I * ↑t) = ∫ (t : ℝ) in Set.Icc 0 U, f (↑(0 : ℝ) + I * ↑t) := by congr 1; ext t; simp
        rw [h1, h2]
      rw [hA_eq, ← h_final] at h_shift
      exact h_shift
    · simp_rw [mul_comm _ I]
      apply horizontal_integral_phi_fourier_vanish ν ε x (-1) 0 hν hx (Set.Icc_subset_Icc (by norm_num) (by norm_num)) (by norm_num) f
      · intro T hT; convert (h_anal T (by linarith)).continuousOn using 2
      · intro T hT t ht; dsimp [f]; rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    · apply integrable_phi_fourier_ray ν ε (-1) x hν (by norm_num) hx f (Or.inr rfl)
    · apply integrable_phi_fourier_ray ν ε 0 x hν (by norm_num) hx f (Or.inr rfl)
  have hBshift :
      Filter.atTop.Tendsto
        (fun T : ℝ ↦
          (- I * ∫ t in Set.Icc 0 T,
            (Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t)) * E (-(1 + I * t) * x))
          + (I * ∫ t in Set.Icc 0 T,
            (Phi_circ ν ε (I * t) + Phi_star ν ε (I * t)) * E (-(I * t) * x)))
        (nhds B) := by
    let f : ℂ → ℂ := fun z ↦ (Phi_circ ν ε z + Phi_star ν ε z) * E (-z * x)
    have h_anal (U : ℝ) (hU : 0 ≤ U) : HolomorphicOn f (Rectangle (↑(0:ℝ)) (↑(1:ℝ) + I * U)) := by
      intro z hz; have hi : 0 ≤ z.im := by
        have hz_im : z.im ∈ Set.uIcc 0 U := by simpa [Rectangle] using hz.2
        rw [Set.uIcc_of_le hU] at hz_im
        exact hz_im.1
      exact (AnalyticAt.add (Phi_circ.analyticAt_of_im_nonneg ν ε z hν hi) (Phi_star.analyticAt_of_im_nonneg ν ε z hν hi)).differentiableAt.mul
        (by dsimp [E]; fun_prop) |>.differentiableWithinAt
    have h_shift := tendsto_contour_shift (σ := 0) (σ' := 1) (f := f) h_anal ?_ ?_ ?_
    · have hB_eq : ∫ x in (0:ℝ)..1, f x = B := by
        dsimp [B]
        rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Icc_eq_integral_Ioc]
      have h_final : (fun (T : ℝ) ↦ (-I * ∫ (t : ℝ) in Set.Icc 0 T, f (1 + I * ↑t)) + (I * ∫ (t : ℝ) in Set.Icc 0 T, f (I * ↑t))) =
          (fun (U : ℝ) ↦ (I * ∫ (t : ℝ) in Set.Icc 0 U, f (↑(0 : ℝ) + I * ↑t)) - (I * ∫ (t : ℝ) in Set.Icc 0 U, f (↑(1 : ℝ) + I * ↑t))) := by
        ext U
        have h1 : ∫ (t : ℝ) in Set.Icc 0 U, f (1 + I * ↑t) = ∫ (t : ℝ) in Set.Icc 0 U, f (↑(1 : ℝ) + I * ↑t) := by congr 1
        have h2 : ∫ (t : ℝ) in Set.Icc 0 U, f (I * ↑t) = ∫ (t : ℝ) in Set.Icc 0 U, f (↑(0 : ℝ) + I * ↑t) := by congr 1; ext t; simp
        rw [h1, h2]; ring
      rw [hB_eq, ← h_final] at h_shift
      exact h_shift
    · simp_rw [mul_comm _ I]
      apply horizontal_integral_phi_fourier_vanish ν ε x 0 1 hν hx (Set.Icc_subset_Icc (by norm_num) (by norm_num)) (by norm_num) f
      · intro T hT; convert (h_anal T (by linarith)).continuousOn using 2
      · intro T hT t ht; dsimp [f]; rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    · apply integrable_phi_fourier_ray ν ε 0 x hν (by norm_num) hx f (Or.inl rfl)
    · apply integrable_phi_fourier_ray ν ε 1 x hν (by norm_num) hx f (Or.inl rfl)
  have h_integrable_imag
      (T : ℝ)
      (F : ℂ → ℂ)
      (hF : ∀ t ∈ Set.Icc (0 : ℝ) T, ContinuousAt (fun y : ℝ ↦ F (I * ↑y)) t) :
      Integrable (fun t : ℝ ↦ F (I * ↑t) * E (-(I * ↑t) * ↑x))
        (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_of_forall_continuousAt
    intro t ht
    refine ContinuousAt.mul ?_ ?_
    · exact hF t ht
    · dsimp [E]
      fun_prop
  have hcombine (T : ℝ) :
      (I * ∫ t in Set.Icc 0 T, (Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t)) * E (-(-1 + I * t) * x))
      - (I * ∫ t in Set.Icc 0 T, (Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t)) * E (-(1 + I * t) * x))
      + (2 * I * ∫ t in Set.Icc 0 T, Phi_star ν ε (I * t) * E (-(I * t) * x)) =
      ((I * ∫ t in Set.Icc 0 T, (Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t)) * E (-(-1 + I * t) * x))
        - (I * ∫ t in Set.Icc 0 T, (Phi_circ ν ε (I * t) - Phi_star ν ε (I * t)) * E (-(I * t) * x))) +
      ((- I * ∫ t in Set.Icc 0 T, (Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t)) * E (-(1 + I * t) * x))
        + (I * ∫ t in Set.Icc 0 T, (Phi_circ ν ε (I * t) + Phi_star ν ε (I * t)) * E (-(I * t) * x))) := by
    have hsub : ∫ t in Set.Icc 0 T,
        (Phi_circ ν ε (I * ↑t) - Phi_star ν ε (I * ↑t)) * E (-(I * ↑t) * ↑x) =
        (∫ t in Set.Icc 0 T, Phi_circ ν ε (I * ↑t) * E (-(I * ↑t) * ↑x)) -
        (∫ t in Set.Icc 0 T, Phi_star ν ε (I * ↑t) * E (-(I * ↑t) * ↑x)) := by
      simp_rw [sub_mul]
      refine integral_sub ?_ ?_
      · exact h_integrable_imag T (Phi_circ ν ε) (by intro t ht; exact Phi_circ.continuousAt_imag ν ε t ht.1 hν)
      · exact h_integrable_imag T (Phi_star ν ε) (by intro t ht; exact Phi_star.continuousAt_imag ν ε t ht.1 hν)
    have hadd : ∫ t in Set.Icc 0 T,
        (Phi_circ ν ε (I * ↑t) + Phi_star ν ε (I * ↑t)) * E (-(I * ↑t) * ↑x) =
        (∫ t in Set.Icc 0 T, Phi_circ ν ε (I * ↑t) * E (-(I * ↑t) * ↑x)) +
        (∫ t in Set.Icc 0 T, Phi_star ν ε (I * ↑t) * E (-(I * ↑t) * ↑x)) := by
      simp_rw [add_mul]
      refine integral_add ?_ ?_
      · exact h_integrable_imag T (Phi_circ ν ε) (by intro t ht; exact Phi_circ.continuousAt_imag ν ε t ht.1 hν)
      · exact h_integrable_imag T (Phi_star ν ε) (by intro t ht; exact Phi_star.continuousAt_imag ν ε t ht.1 hν)
    linear_combination I * hsub - I * hadd
  have hcontour := (hAshift.add hBshift).congr' (Filter.Eventually.of_forall (fun T ↦ (hcombine T).symm))
  simpa [hfourier] using hcontour

@[blueprint
  "B-affine-periodic"
  (title := "$B^\\pm$ affine periodic")
  (statement := /-- For any integer $m$,
$$ B^\pm(w(z-m)) = B^\pm(w(z) + 2\pi i m) = B^\pm(w(z)) + 2\pi i m\, \Phi^{\pm,\circ}_{\nu}(z). $$
    -/)
  (proof := /-- This follows from the $\pi i$-periodicity of coth. -/)
  (latexEnv := "sublemma")
  (discussion := 1081)]
theorem B_affine_periodic (ν ε : ℝ) (_hν : ν > 0) (z : ℂ) (m : ℤ)
    (hw : -2 * π * I * z + ν ≠ 0)
    (hwm : -2 * π * I * (z - m) + ν ≠ 0) :
    B ε (-2 * π * I * (z - m) + ν) =
      B ε (-2 * π * I * z + ν) + 2 * π * I * m * Phi_circ ν ε z := by
  unfold B Phi_circ coth
  have h_tanh_periodic :
      Complex.tanh ((-2 * Real.pi * I * (z - m) + ν) / 2) =
        Complex.tanh ((-2 * Real.pi * I * z + ν) / 2) := by
    rw [show (-2 * π * I * (z - m) + ν) / 2 =
      (-2 * π * I * z + ν) / 2 + π * I * m by ring]
    exact tanh_add_int_mul_pi_I _ m
  grind

@[blueprint
  "phi_star-affine-periodic"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ affine periodic")
  (statement := /-- For any integer $m$,
$$ \Phi^{\pm,\star}_{\nu}(z-m) = \Phi^{\pm,\star}_{\nu}(z) + m\, \Phi^{\pm,\circ}_{\nu}(z). $$
    -/)
  (proof := /-- Follows from previous lemma. -/)
  (latexEnv := "sublemma")
  (discussion := 1082)]
theorem phi_star_affine_periodic (ν ε : ℝ) (hν : ν > 0) (z : ℂ) (m : ℤ)
    (hw : -2 * π * I * z + ν ≠ 0)
    (hwm : -2 * π * I * (z - m) + ν ≠ 0) :
    Phi_star ν ε (z - m) = Phi_star ν ε z + m * Phi_circ ν ε z := by
  have hB := B_affine_periodic ν ε hν z m hw hwm
  have h_sub : Phi_star ν ε (z - m) =
      (B ε (-2 * Real.pi * I * z + ν) +
        2 * Real.pi * I * m * Phi_circ ν ε z - B ε ν) /
      (2 * Real.pi * I) := by
    rw [Phi_star, hB]
  have h_def : Phi_star ν ε z =
      (B ε (-2 * Real.pi * I * z + ν) - B ε ν) /
      (2 * Real.pi * I) := by
    simp [Phi_star]
  rw [h_sub, h_def]
  field_simp
  ring

private lemma Phi_circ_periodic (ν ε : ℝ) (z : ℂ) : Phi_circ ν ε (z + 1) = Phi_circ ν ε z := by
  simp only [Phi_circ]; congr 1
  rw [show (-2 * ↑π * I * (z + 1) + ↑ν) / 2 = (-2 * ↑π * I * z + ↑ν) / 2 - ↑π * I by ring]
  rw [← coth_add_pi_mul_I ((-2 * ↑π * I * z + ↑ν) / 2 - ↑π * I)]
  ring_nf

-- Used in both shift_upwards_simplified and shift_downwards_simplified.
private lemma tendsto_div_two_pi :
    Filter.Tendsto (fun T : ℝ ↦ T / (2 * π)) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop_of_monotone
    (fun _ _ hab ↦ div_le_div_of_nonneg_right hab (by positivity))
    (fun b ↦ ⟨b * (2 * π), by simp⟩)

private lemma two_sub_E_sq (x : ℝ) : (2 : ℂ) - E ↑x - E (-↑x) = 4 * (Real.sin (π * x)) ^ 2 := by
  dsimp [E]
  rw [show (2 : ℂ) * ↑π * I * ↑x = ↑(2 * π * x) * I by push_cast; ring]
  rw [show (2 : ℂ) * ↑π * I * -↑x = -↑(2 * π * x) * I by push_cast; ring]
  rw [show ∀ (z : ℂ), (2 : ℂ) - Complex.exp (z * I) - Complex.exp (-z * I) = 4 * (Complex.sin (z / 2)) ^ 2 from fun z ↦ by
    rw [sub_sub, ← Complex.two_cos, show z = 2 * (z / 2) by ring, Complex.cos_two_mul]
    ring_nf; linear_combination -4 * Complex.sin_sq_add_cos_sq (z * (1 / 2))]
  simp; ring_nf

@[blueprint
  "shift-upwards-simplified"
  (title := "Simplified formula for upward contour shift")
  (statement := /-- If $x < 0$, then $\widehat{\varphi^{\pm}_{\nu}}(x)$ equals
$$
\frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu + y) - B^{\pm}(\nu))\, e^{xy}\, dy.
$$
  -/)
  (proof := /-- We have $\Phi^{\pm,\circ}_{\nu}(z) - \Phi^{\pm,\star}_{\nu}(z) = -\Phi^{\pm,\star}_{\nu}(z+1)$ and $\Phi^{\pm,\circ}_{\nu}(z) + \Phi^{\pm,\star}_{\nu}(z) = \Phi^{\pm,\star}_{\nu}(z-1)$, and so the formula in the previous lemma simplifies to
\begin{align*}
&2\int_0^{i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz - \int_0^{i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-(z-1)x)\, dz - \int_0^{i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-(z+1)x)\, dz\\
&= (2 - e(x) - e(-x)) \int_0^{\infty} \Phi^{\pm,\star}_{\nu}\!\left(\frac{iy}{2\pi}\right) e\!\left(\frac{xy}{2\pi}\right)\, dy = \frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu + y) - B^{\pm}(\nu))\, e^{xy}\, dy.
\end{align*}
  -/)
  (latexEnv := "sublemma")
  (discussion := 1083)]
theorem shift_upwards_simplified (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x < 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ (Real.sin (π * x))^2 / π^2 * ∫ t in Set.Icc 0 T, ((B ε (ν + t) - B ε ν) * Real.exp (x * t))) (nhds (𝓕 (ϕ_pm ν ε) x)) := by
  have h_circ_periodic (z : ℂ) : Phi_circ ν ε (z - 1) = Phi_circ ν ε z := by
    have h := (Phi_circ_periodic ν ε (z - 1)).symm; rwa [sub_add_cancel] at h
  have h_re {t : ℝ} (ht : 0 ≤ t) : (-2 : ℂ) * ↑π * I * (I * ↑t) + ↑ν ≠ 0 := by
    intro h; apply_fun Complex.re at h; simp at h; nlinarith [Real.pi_pos, ht, hν]
  have h_im {t : ℝ} (m : ℤ) (hm : m ≠ 0) : (-2 : ℂ) * ↑π * I * (I * ↑t - ↑m) + ↑ν ≠ 0 := by
    intro h; apply_fun Complex.im at h; simp [Real.pi_pos.ne.symm, hm] at h
  have h_sub (t : ℝ) (ht : 0 ≤ t) :
      Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t) = -Phi_star ν ε (I * t) := by
    have haff := phi_star_affine_periodic ν ε hν (I * t) 1 (h_re ht) (h_im (t := t) 1 (by norm_num))
    simp only [Int.cast_one, one_mul] at haff
    rw [show -1 + I * t = I * t - 1 by ring, h_circ_periodic, haff]; ring
  have h_add (t : ℝ) (ht : 0 ≤ t) :
      Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t) = Phi_star ν ε (I * t) := by
    have haff := phi_star_affine_periodic ν ε hν (I * t) (-1) (h_re ht) (h_im (t := t) (-1) (by norm_num))
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add] at haff
    rw [show 1 + I * t = I * t + 1 by ring, ← h_circ_periodic (I * t + 1), show I * t + 1 - 1 = I * t by ring, haff]; ring
  have h_factor (T : ℝ) :
      (I * ∫ t in Set.Icc 0 T,
          (Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t)) * E (-(-1 + I * t) * x))
      - (I * ∫ t in Set.Icc 0 T,
          (Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t)) * E (-(1 + I * t) * x))
      + (2 * I * ∫ t in Set.Icc 0 T, Phi_star ν ε (I * t) * E (-(I * t) * x))
      = (2 - E x - E (-x)) * (I * ∫ t in Set.Icc 0 T, Phi_star ν ε (I * t) * E (-(I * t) * x)) := by
    have hE_shift_neg (t : ℝ) : E (-(-1 + I * ↑t) * ↑x) = E ↑x * E (-(I * ↑t) * ↑x) := by
      simp only [E, ← Complex.exp_add]; congr 1; ring
    have hE_shift_pos (t : ℝ) : E (-(1 + I * ↑t) * ↑x) = E (-↑x) * E (-(I * ↑t) * ↑x) := by
      simp only [E, ← Complex.exp_add]; congr 1; ring
    have h1 : ∫ t in Set.Icc 0 T, (Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t)) * E (-(-1 + I * t) * x) =
              ∫ t in Set.Icc 0 T, -(E x * (Phi_star ν ε (I * t) * E (-(I * t) * x))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [h_sub t ht.1, hE_shift_neg]
      ring
    have h2 : ∫ t in Set.Icc 0 T, (Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t)) * E (-(1 + I * t) * x) =
              ∫ t in Set.Icc 0 T, E (-x) * (Phi_star ν ε (I * t) * E (-(I * t) * x)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [h_add t ht.1, hE_shift_pos]
      ring
    rw [h1, h2]
    rw [integral_neg, integral_const_mul, integral_const_mul]
    ring
  have h_prefactor := two_sub_E_sq x
  have h_Phi_star_imag (t : ℝ) :
      Phi_star ν ε (I * ↑t) = (B ε ↑(2 * π * t + ν) - B ε ↑ν) / (2 * ↑π * I) := by
    simp only [Phi_star]; congr; push_cast; ring_nf; simp [Complex.I_sq]
  have h_E_imag (t : ℝ) : E (-(I * ↑t) * ↑x) = ↑(Real.exp (2 * π * x * t)) := by
    simp only [E]; push_cast; ring_nf; congr; simp
  have h_imag_integral (T : ℝ) :
      I * ∫ t in Set.Icc 0 T, Phi_star ν ε (I * ↑t) * E (-(I * ↑t) * ↑x)
      = (1 / (2 * ↑π)) *
        ∫ t in Set.Icc 0 T,
          (B ε ↑(2 * π * t + ν) - B ε ↑ν) * ↑(Real.exp (2 * π * x * t)) := by
    simp_rw [h_Phi_star_imag, h_E_imag]
    set f : ℝ → ℂ := fun t ↦ (B ε ↑(2 * π * t + ν) - B ε ↑ν) * ↑(rexp (2 * π * x * t))
    rw [← integral_const_mul I]
    have : ((1 : ℂ) / (2 * ↑π)) * ∫ t in Set.Icc 0 T, f t = ∫ t in Set.Icc 0 T, ((1 : ℂ) / (2 * ↑π)) * f t := by
      rw [integral_const_mul]
    rw [this]
    congr 1; ext t
    field_simp [Complex.I_ne_zero, Real.pi_pos.ne.symm]
    unfold f; ring_nf
  have h_cov (T : ℝ) (hT : 0 ≤ T) :
      ∫ t in Set.Icc 0 T,
          (B ε ↑(2 * π * t + ν) - B ε ↑ν) * ↑(Real.exp (2 * π * x * t))
      = (1 / (2 * π)) *
    ∫ s in Set.Icc 0 (2 * π * T),
          (B ε (ν + s) - B ε ν) * Real.exp (x * s) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
    let f : ℝ → ℂ := fun s ↦ (B ε (s + ν) - B ε ν) * (Real.exp (x * s) : ℂ)
    have h_scale := intervalIntegral.integral_comp_mul_left f (c := 2 * π) (by positivity) (a := 0) (b := T)
    dsimp [f] at h_scale
    convert h_scale using 1
    · push_cast; congr 1; ext t; ring_nf
    · push_cast; field_simp; congr 1
      · ext s; ring_nf
      · simp
  have h_key (T : ℝ) (hT : 0 ≤ T) :
      (I * ∫ t in Set.Icc 0 (T / (2 * π)),
          (Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t)) * E (-(-1 + I * t) * x))
      - (I * ∫ t in Set.Icc 0 (T / (2 * π)),
          (Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t)) * E (-(1 + I * t) * x))
      + (2 * I * ∫ t in Set.Icc 0 (T / (2 * π)),
          Phi_star ν ε (I * t) * E (-(I * t) * x))
      = ↑(Real.sin (π * x)) ^ 2 / ↑π ^ 2 *
        ∫ t in Set.Icc 0 T, (B ε (ν + t) - B ε ν) * Real.exp (x * t) := by
    rw [h_factor, h_imag_integral, h_prefactor, h_cov (T / (2 * π)) (by positivity)]
    rw [show 2 * ↑π * (T / (2 * ↑π)) = T by field_simp]
    push_cast; ring_nf; congr; ext t; ring_nf
  apply ((shift_upwards ν ε hν x hx).comp tendsto_div_two_pi).congr'
  filter_upwards [Filter.eventually_ge_atTop 0] with T hT
  exact h_key T hT

lemma tendsto_contour_shift_downwards {σ σ' : ℝ} {f : ℂ → ℂ}
    (hf_anal : ∀ (U : ℝ), U ≥ 0 → HolomorphicOn f (Rectangle (σ : ℂ) (σ' - I * U)))
    (h_bottom : Filter.Tendsto (fun (T : ℝ) ↦ ∫ t in σ..σ', f (t - I * T)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun (T : ℝ) ↦ (I * ∫ t in Set.Icc 0 T, f (σ' - I * t)) - (I * ∫ t in Set.Icc 0 T, f (σ - I * t))) Filter.atTop (nhds (∫ t in σ..σ', f t)) := by
  have h_rect (T : ℝ) (hT : 0 ≤ T) :
      RectangleIntegral f σ (σ' - I * T) =
      (∫ t in σ..σ', f t) - (∫ t in σ..σ', f (t - I * T)) - (I * ∫ t in Set.Icc 0 T, f (σ' - I * t)) + (I * ∫ t in Set.Icc 0 T, f (σ - I * t)) := by
    dsimp [RectangleIntegral, HIntegral, VIntegral]
    have h1 : ∫ (x : ℝ) in σ..σ' - (0 * T - 1 * 0), f (↑x + 0 * I) = ∫ x in σ..σ', f ↑x := by
      simp only [show σ' - (0 * T - 1 * 0) = σ' from by ring]
      exact intervalIntegral.integral_congr fun x _ ↦ by ring_nf
    have h2 : ∫ (x : ℝ) in σ..σ' - (0 * T - 1 * 0), f (↑x + ↑(0 - (0 * 0 + 1 * T)) * I) = ∫ x in σ..σ', f (↑x - I * ↑T) := by
      simp only [show σ' - (0 * T - 1 * 0) = σ' from by ring]
      exact intervalIntegral.integral_congr fun x _ ↦ by norm_cast; simp; ring_nf
    have h3 : ∫ (y : ℝ) in 0..0 - (0 * 0 + 1 * T), f (↑(σ' - (0 * T - 1 * 0)) + ↑y * I) = - ∫ t in Set.Icc 0 T, f (↑σ' - I * ↑t) := by
      rw [show (0 : ℝ) - (0 * 0 + 1 * T) = -T from by ring,
          show σ' - (0 * T - 1 * 0) = σ' from by ring, neg_zero.symm]
      rw [← intervalIntegral.integral_comp_neg (f := fun y ↦ f (↑σ' + ↑y * I)) (a := T) (b := 0)]
      rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hT, MeasureTheory.integral_Icc_eq_integral_Ioc]
      simp only [neg_zero]
      exact congr_arg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall fun y ↦ by push_cast; ring_nf))
    have h4 : ∫ (y : ℝ) in 0..0 - (0 * 0 + 1 * T), f (↑σ + ↑y * I) = - ∫ t in Set.Icc 0 T, f (↑σ - I * ↑t) := by
      rw [show (0 : ℝ) - (0 * 0 + 1 * T) = -T from by ring, neg_zero.symm]
      rw [← intervalIntegral.integral_comp_neg (f := fun y ↦ f (↑σ + ↑y * I)) (a := T) (b := 0)]
      rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hT, MeasureTheory.integral_Icc_eq_integral_Ioc]
      simp only [neg_zero]
      exact congr_arg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall fun y ↦ by push_cast; ring_nf))
    rw [h1, h2, h3, h4]
    ring

  have h_zero : Filter.Tendsto (fun (T : ℝ) ↦ RectangleIntegral f σ (σ' - I * T)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Filter.eventually_ge_atTop 0] with T hT
      exact (HolomorphicOn.vanishesOnRectangle (hf_anal T hT) subset_rfl).symm)
  have h_total_lim : Filter.Tendsto (fun (T : ℝ) ↦ (∫ t in σ..σ', f t) - (∫ t in σ..σ', f (t - I * T)) - RectangleIntegral f σ (σ' - I * T)) Filter.atTop (nhds (∫ t in σ..σ', f t)) := by
    simpa only [sub_zero] using ((tendsto_const_nhds (x := ∫ t in σ..σ', f t)).sub h_bottom).sub h_zero
  exact h_total_lim.congr' (by
    filter_upwards [Filter.eventually_ge_atTop 0] with T hT
    rw [h_rect T hT]; ring)

lemma horizontal_integral_phi_fourier_vanish_downwards (ν ε x a b : ℝ) (hν : ν > 0) (hx : x > 0)
    (hab_in : Set.Icc a b ⊆ Set.Icc (-1) 1) (hab : a ≤ b)
    (f : ℂ → ℂ)
    (hf_anal : ∀ (T : ℝ), T ≥ 1 → ContinuousOn f (Rectangle (a : ℂ) (b - I * T)))
    (hf_bound : ∀ᶠ (T : ℝ) in Filter.atTop, ∀ (t : ℝ), t ∈ Set.Icc a b → ‖f (t - I * T)‖ ≤ (‖Phi_circ ν ε (t - I * T)‖ + ‖Phi_star ν ε (t - I * T)‖) * ‖E (-(t - I * T) * x)‖) :
    Filter.Tendsto (fun (T : ℝ) ↦ ∫ t in a..b, f (t - I * T)) Filter.atTop (nhds 0) := by
  obtain ⟨C, T₀, hT₀_bound, hC⟩ := phi_bound_downwards ν ε hν
  obtain ⟨T_bound, hf_bound'⟩ := Filter.eventually_atTop.mp hf_bound
  let T_max := max (max 1 T₀) T_bound
  have h_int_bound (T : ℝ) (hT : T ≥ T_max) :
      ‖∫ t in a..b, f (t - I * T)‖ ≤ (b - a) * C * (T + 1) * Real.exp (-2 * π * x * T) := by
    calc ‖∫ t in a..b, f (↑t - I * ↑T)‖
      _ ≤ ∫ t in a..b, ‖f (↑t - I * ↑T)‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, C * (T + 1) * Real.exp (-2 * π * x * T) := by
          apply intervalIntegral.integral_mono_on hab
          · apply ContinuousOn.intervalIntegrable
            · refine ContinuousOn.norm ?_
              rw [Set.uIcc_of_le hab]
              apply ContinuousOn.congr (f := f ∘ fun (x : ℝ) ↦ (x : ℂ) - I * (T : ℂ))
              · apply ContinuousOn.comp
                · exact hf_anal T (by linarith [hT, le_max_left (max 1 T₀) T_bound, le_max_left 1 T₀])
                · exact (continuous_ofReal.sub continuous_const).continuousOn
                · intro u hu
                  simp only [Rectangle, ofReal_re, sub_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
                    mul_zero, sub_self, sub_zero, sub_im, mul_im, one_mul, zero_add, zero_sub]
                  constructor
                  · simp only [Set.mem_preimage, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
                    ofReal_im, mul_zero, sub_self, sub_zero]
                    rw [Set.uIcc_of_le hab]; exact hu
                  · simp
              · intro x _; rfl
          · exact intervalIntegrable_const
          · intro t ht
            calc ‖f (↑t - I * ↑T)‖
              _ ≤ (‖Phi_circ ν ε (↑t - I * ↑T)‖ + ‖Phi_star ν ε (↑t - I * ↑T)‖) * ‖E (-(↑t - I * ↑T) * ↑x)‖ := hf_bound' T (by linarith [hT, le_max_right (max 1 T₀) T_bound]) t ht
              _ = (‖Phi_circ ν ε (↑t - I * ↑T)‖ + ‖Phi_star ν ε (↑t - I * ↑T)‖) * Real.exp (-2 * π * x * T) := by
                  congr 1; dsimp [E]; rw [Complex.norm_exp]; simp; ring_nf
              _ ≤ C * (1 - (↑t - I * T).im) * Real.exp (-2 * π * x * T) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  norm_cast
                  rw [show 1 - (↑t - I * ↑T).im = -(↑t - I * ↑T).im + 1 by ring]
                  apply hC
                  · simp
                    linarith [hT, le_max_left (max 1 T₀) T_bound, le_max_right 1 T₀]
                  · simp only [sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
                    mul_zero, sub_self, sub_zero, Set.mem_Icc]
                    exact_mod_cast hab_in ht
              _ = C * (T + 1) * Real.exp (-2 * π * x * T) := by simp [Complex.sub_im]; ring_nf; simp
      _ = (b - a) * (C * (T + 1) * Real.exp (-2 * π * x * T)) := intervalIntegral.integral_const _
      _ = (b - a) * C * (T + 1) * Real.exp (-2 * π * x * T) := by ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let h_decay : ℝ → ℝ := fun T' ↦ (b - a) * C * (T' + 1) * rexp (-2 * π * x * T')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ 0) (h := h_decay) tendsto_const_nhds ?_ ?_ ?_
  · exact tendsto_T_plus_one_mul_exp_atTop_nhds_zero (by nlinarith [hx, Real.pi_pos]) ((b - a) * C)
  · exact Filter.Eventually.of_forall fun T' ↦ norm_nonneg _
  · exact (Filter.eventually_ge_atTop T_max).mono h_int_bound

noncomputable def z₀_pole (ν : ℝ) : ℂ := (-1 : ℂ) - I * (ν / (2 * π))
noncomputable def z₁_pole (ν : ℝ) : ℂ := (1 : ℂ) - I * (ν / (2 * π))

-- If (n : ℝ) ∈ [a, b] and k is the unique integer in (a−1, b+1), then n = k.
private lemma unique_int_in_Icc (n k : ℤ) {a b : ℝ}
    (h_mem : (n : ℝ) ∈ Set.Icc a b)
    (h_lo : (k : ℝ) - 1 < a)
    (h_hi : b < (k : ℝ) + 1) :
    n = k := by
  have h1 : k - 1 < n := by exact_mod_cast h_lo.trans_le h_mem.1
  have h2 : n < k + 1 := by exact_mod_cast h_mem.2.trans_lt h_hi
  omega

-- Phi_circ − Phi_star has nonneg meromorphicOrderAt at z₀_pole ν.
private lemma meromorphicOrderAt_phi_diff_nonneg (ν ε : ℝ) (hν : ν > 0) :
    meromorphicOrderAt (fun z ↦ Phi_circ ν ε z - Phi_star ν ε z) (z₀_pole ν) ≥ 0 := by
  rw [show (fun z ↦ Phi_circ ν ε z - Phi_star ν ε z) =
          fun z ↦ Phi_circ ν ε z + (-1 : ℝ) * Phi_star ν ε z by ext; simp [sub_eq_add_neg],
      show z₀_pole ν = ((-1 : ℝ) : ℂ) - I * ν / (2 * π) by simp [z₀_pole]; ring]
  exact Phi_cancel ν ε (-1) hν (by norm_num)

-- Phi_circ + Phi_star has nonneg meromorphicOrderAt at z₁_pole ν.
private lemma meromorphicOrderAt_phi_add_nonneg (ν ε : ℝ) (hν : ν > 0) :
    meromorphicOrderAt (fun z ↦ Phi_circ ν ε z + Phi_star ν ε z) (z₁_pole ν) ≥ 0 := by
  rw [show (fun z ↦ Phi_circ ν ε z + Phi_star ν ε z) =
          fun z ↦ Phi_circ ν ε z + (1 : ℝ) * Phi_star ν ε z by ext; simp,
      show z₁_pole ν = ((1 : ℝ) : ℂ) - I * ν / (2 * π) by simp [z₁_pole]; ring]
  exact Phi_cancel ν ε 1 hν (by norm_num)

-- Removable-singularity extension: if f_base is meromorphic at z_pole with removable singularity
-- witnessed by h_tendsto, then the patched function (using the limit value at z_pole) is analytic.
private lemma analyticAt_removable_sing_mul_E (x : ℝ) {f_base : ℂ → ℂ} {z_pole : ℂ}
    {c_base : ℂ}
    (h_mero : MeromorphicAt f_base z_pole)
    (h_tendsto : Filter.Tendsto f_base (nhdsWithin z_pole {z_pole}ᶜ) (nhds c_base)) :
    AnalyticAt ℂ (fun z ↦ if z = z_pole then c_base * E (-z_pole * x)
                            else f_base z * E (-z * x)) z_pole := by
  apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · obtain ⟨V, hV_nhds, hV_anal⟩ := h_mero.eventually_analyticAt
    filter_upwards [nhdsWithin_le_nhds hV_nhds, self_mem_nhdsWithin] with w hwV hw_ne
    have h_eq : (fun z ↦ if z = z_pole then c_base * E (-z_pole * x) else f_base z * E (-z * x)) =ᶠ[nhds w]
                (fun z ↦ f_base z * E (-z * x)) :=
      (eventually_ne_nhds hw_ne).mono (fun z hz ↦ by simp [if_neg hz])
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h_eq
    rcases hV_anal with ⟨b, hb, h_set_eq⟩
    have hw_f_anal : AnalyticAt ℂ f_base w := by
      have : w ∈ V ∩ b := ⟨hwV, hb hw_ne⟩
      rwa [← h_set_eq] at this
    exact (hw_f_anal.mul (by unfold E; fun_prop)).differentiableAt
  · rw [continuousAt_iff_punctured_nhds]
    simp only [↓reduceIte]
    have h_cont_E : ContinuousAt (fun z ↦ E (-z * x)) z_pole := by unfold E; fun_prop
    refine (h_tendsto.mul (h_cont_E.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ z_pole)
    simp [if_neg hw]

lemma Phi_diff_bounded_near_pole (ν ε : ℝ) (hν : ν > 0) :
    ∃ U ∈ nhds (z₀_pole ν), BddAbove (norm ∘ (fun z ↦ Phi_circ ν ε z - Phi_star ν ε z) '' (U \ {z₀_pole ν})) := by
  let z₀ := z₀_pole ν
  let f := fun z ↦ Phi_circ ν ε z - Phi_star ν ε z
  have h_mero : MeromorphicAt f z₀ := (Phi_circ.meromorphic ν ε z₀).sub (Phi_star.meromorphic ν ε z₀)
  have h_order : meromorphicOrderAt f z₀ ≥ 0 := meromorphicOrderAt_phi_diff_nonneg ν ε hν
  obtain ⟨c, h_tendsto⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg h_mero h_order
  exact IsBigO_to_BddAbove (h_tendsto.isBigO_one (F := ℂ))

lemma Phi_fourier_holo_left (ν ε x : ℝ) (hν : ν > 0) :
    ∃ g : ℂ → ℂ, (∀ U : ℝ, U ≥ 0 → HolomorphicOn g (Rectangle (-1 : ℂ) (-1 / 2 - I * U))) ∧
    Set.EqOn g (fun z ↦ (Phi_circ ν ε z - Phi_star ν ε z) * E (-z * x)) {z | z ≠ z₀_pole ν} := by
  let z₀ := z₀_pole ν
  let f_base (z : ℂ) := (Phi_circ ν ε z - Phi_star ν ε z)
  let f (z : ℂ) := f_base z * E (-z * x)
  obtain ⟨c_base, h_tendsto_base⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg
    ((Phi_circ.meromorphic ν ε z₀).sub (Phi_star.meromorphic ν ε z₀))
    (meromorphicOrderAt_phi_diff_nonneg ν ε hν)
  let c := c_base * E (-z₀ * x)
  let g (z : ℂ) := if z = z₀ then c else f z
  use g
  constructor
  · intro U hU z hz
    by_cases hz₀ : z = z₀
    · have h_anal_z₀ : AnalyticAt ℂ g z₀ :=
        analyticAt_removable_sing_mul_E x
          ((Phi_circ.meromorphic ν ε z₀).sub (Phi_star.meromorphic ν ε z₀))
          h_tendsto_base
      exact (hz₀ ▸ h_anal_z₀).differentiableAt.differentiableWithinAt
    · have h_not_pole : ∀ n : ℤ, z ≠ ↑n - I * ↑ν / (2 * ↑π) := by
        intro n hn; have h_re : z.re = n := by
          rw [hn, Complex.sub_re, Complex.intCast_re, mul_div_assoc, Complex.I_mul_re]
          simp; field_simp; norm_cast
        have h_im : z.im = -ν / (2 * π) := by
          rw [hn, Complex.sub_im, Complex.intCast_im, mul_div_assoc, Complex.I_mul_im]
          norm_cast; ring
        have h_rect := hz; rw [Rectangle, Complex.mem_reProdIm] at h_rect
        simp only [neg_re, one_re, sub_re, div_ofNat_re, mul_re, I_re, ofReal_re, zero_mul, I_im,
          ofReal_im, mul_zero, sub_self, sub_zero, neg_im, one_im, neg_zero, sub_im, div_ofNat_im,
          zero_div, mul_im, one_mul, zero_add, zero_sub] at h_rect
        rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_ge (by linarith)] at h_rect
        have h_n : n = -1 := unique_int_in_Icc n (-1) (h_re ▸ h_rect.1) (by norm_num) (by norm_num)
        subst h_n
        exact hz₀ (Complex.ext
          (by
            dsimp [z₀, z₀_pole]
            rw [h_re, Complex.div_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_im]
            simp
          )
          (by rw [h_im]; dsimp [z₀, z₀_pole]; simp; norm_cast; ring))
      have h_anal_z : AnalyticAt ℂ g z := by
        have h_eq : g =ᶠ[nhds z] f := by
          filter_upwards [eventually_ne_nhds hz₀] with w hw
          dsimp [g]; rw [if_neg hw]
        rw [analyticAt_congr h_eq]
        apply AnalyticAt.mul
        · exact (Phi_circ.analyticAt_of_not_pole ν ε z h_not_pole).sub
            (Phi_star.analyticAt_of_not_pole ν ε z h_not_pole)
        · unfold E; fun_prop
      exact h_anal_z.differentiableAt.differentiableWithinAt
  · intro z hz; dsimp [g]; rw [if_neg hz]

lemma Phi_add_bounded_near_pole (ν ε : ℝ) (hν : ν > 0) :
    ∃ U ∈ nhds (z₁_pole ν), BddAbove (norm ∘ (fun z ↦ Phi_circ ν ε z + Phi_star ν ε z) '' (U \ {z₁_pole ν})) := by
  let z₁ : ℂ := z₁_pole ν
  let f := fun z ↦ Phi_circ ν ε z + Phi_star ν ε z
  have h_mero : MeromorphicAt f z₁ := (Phi_circ.meromorphic ν ε z₁).add (Phi_star.meromorphic ν ε z₁)
  have h_order : meromorphicOrderAt f z₁ ≥ 0 := meromorphicOrderAt_phi_add_nonneg ν ε hν
  obtain ⟨_, h_tendsto⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg h_mero h_order
  exact IsBigO_to_BddAbove (h_tendsto.isBigO_one (F := ℂ))

lemma Phi_fourier_holo_right (ν ε x : ℝ) (hν : ν > 0) :
    ∃ g : ℂ → ℂ, (∀ U : ℝ, U ≥ 0 → HolomorphicOn g (Rectangle (1/2 : ℂ) (1 - I * U))) ∧
    Set.EqOn g (fun z ↦ (Phi_circ ν ε z + Phi_star ν ε z) * E (-z * x)) {z | z ≠ z₁_pole ν} := by
  let z₁ := z₁_pole ν
  let f_base (z : ℂ) := (Phi_circ ν ε z + Phi_star ν ε z)
  let f (z : ℂ) := f_base z * E (-z * x)
  have h_mero : MeromorphicAt f_base z₁ := (Phi_circ.meromorphic ν ε z₁).add (Phi_star.meromorphic ν ε z₁)
  have h_order : meromorphicOrderAt f_base z₁ ≥ 0 := meromorphicOrderAt_phi_add_nonneg ν ε hν
  obtain ⟨c_base, h_tendsto_base⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg h_mero h_order
  let c := c_base * E (-z₁ * x)
  let g (z : ℂ) := if z = z₁ then c else f z
  use g
  constructor
  · intro U hU z hz
    by_cases hz₁ : z = z₁
    · have h_anal_z₁ : AnalyticAt ℂ g z₁ :=
        analyticAt_removable_sing_mul_E x h_mero h_tendsto_base
      rw [hz₁]
      exact h_anal_z₁.differentiableAt.differentiableWithinAt
    · have h_not_pole : ∀ n : ℤ, z ≠ ↑n - I * ↑ν / (2 * ↑π) := by
        intro n hn
        have h_re : z.re = n := by
          rw [hn]
          simp [Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have h_im : z.im = -ν / (2 * π) := by
          rw [hn]
          simp [Complex.sub_im, Complex.mul_im, Complex.div_im, Complex.I_im, Complex.I_re]
          field_simp
        have h_rect := hz
        rw [Rectangle, Complex.mem_reProdIm] at h_rect
        simp only [one_re, div_ofNat_re, sub_re, mul_re, I_re, ofReal_re, zero_mul, I_im,
          ofReal_im, mul_zero, sub_self, sub_zero, sub_im, div_ofNat_im,
          mul_im, one_mul, zero_add] at h_rect
        rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_ge (by simp; linarith)] at h_rect
        have h_n : n = 1 := unique_int_in_Icc n 1 (h_re ▸ h_rect.1) (by norm_num) (by norm_num)
        subst h_n
        have : z = z₁ := by
          apply Complex.ext <;> dsimp [z₁, z₁_pole]
          · rw [h_re]; simp; norm_cast
          · rw [h_im]; norm_cast; simp; ring
        exact hz₁ this
      have h_anal_z : AnalyticAt ℂ g z := by
        have h_eq : g =ᶠ[nhds z] f := by
          filter_upwards [eventually_ne_nhds hz₁] with w hw
          dsimp [g]; rw [if_neg hw]
        rw [analyticAt_congr h_eq]
        exact ((Phi_circ.analyticAt_of_not_pole ν ε z h_not_pole).add
          (Phi_star.analyticAt_of_not_pole ν ε z h_not_pole)).mul (by unfold E; fun_prop)
      exact h_anal_z.differentiableAt.differentiableWithinAt
  · intro z hz; dsimp [g]; rw [if_neg hz]

@[blueprint
  "shift-downwards"
  (title := "Contour shifting downwards")
  (statement := /-- If $x > 0$, then
\begin{align}\label{eq:1.6}
\widehat{\varphi^{\pm}_{\nu}}(x) &= \left(\int_{-1}^{-1-i\infty} + \int_{-\frac{1}{2}-i\infty}^{-\frac{1}{2}}\right) \bigl(\Phi^{\pm,\circ}_{\nu}(z) - \Phi^{\pm,\star}_{\nu}(z)\bigr) e(-zx)\, dz \notag\\
&\quad + \int_{-\frac{1}{2}}^{\frac{1}{2}} \Phi^{\pm,\circ}_{\nu}(z)\, e(-zx)\, dz - \int_{-\frac{1}{2}}^{0} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz + \int_0^{\frac{1}{2}} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz \notag\\
&\quad + \left(\int_{\frac{1}{2}}^{\frac{1}{2}-i\infty} + \int_{1-i\infty}^{1}\right) \bigl(\Phi^{\pm,\circ}_{\nu}(z) + \Phi^{\pm,\star}_{\nu}(z)\bigr) e(-zx)\, dz.
\end{align}
  -/)
  (proof := /-- We would like to integrate along $\Re z = 0$, but $\Phi^{\pm,\circ}_{\nu}(z)$ has a pole at $z = -\frac{i\nu}{2\pi}$; when dealing with this issue, we have to take care not to introduce poles on the lines $\Re z = -1$ and $\Re z = 1$ by separating $\Phi^{\pm,\circ}_{\nu}$ and $\Phi^{\pm,\star}_{\nu}$ prematurely. As $\Im z \to -\infty$, $e(-zx) = e^{-2\pi i z x}$ decays exponentially on $\Im z$, while, by Lemma~1.3, $\Phi^{\pm,\circ}_{\nu}(z) \pm \Phi^{\pm,\star}_{\nu}(z)$ grows at most linearly. -/)
  (latexEnv := "sublemma")
  (discussion := 1084)]
theorem shift_downwards (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x > 0) :
    Filter.Tendsto
      (fun T : ℝ ↦
        (-I * ∫ (t : ℝ) in Set.Icc 0 T, (Phi_circ ν ε (-1 - I * ↑t) - Phi_star ν ε (-1 - I * ↑t)) * E (-(-1 - I * ↑t) * ↑x)) +
        (I * ∫ (t : ℝ) in Set.Icc 0 T, (Phi_circ ν ε (-1 / 2 - I * ↑t) - Phi_star ν ε (-1 / 2 - I * ↑t)) * E (-(-1 / 2 - I * ↑t) * ↑x)) +
        (∫ (t : ℝ) in Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ), Phi_circ ν ε ↑t * E (-↑t * ↑x)) -
        (∫ (t : ℝ) in Set.Icc (-1 / 2 : ℝ) 0, Phi_star ν ε ↑t * E (-↑t * ↑x)) +
        (∫ (t : ℝ) in Set.Icc 0 (1 / 2 : ℝ), Phi_star ν ε ↑t * E (-↑t * ↑x)) -
        (I * ∫ (t : ℝ) in Set.Icc 0 T, (Phi_circ ν ε (1 / 2 - I * ↑t) + Phi_star ν ε (1 / 2 - I * ↑t)) * E (-(1 / 2 - I * ↑t) * ↑x)) +
        (I * ∫ (t : ℝ) in Set.Icc 0 T, (Phi_circ ν ε (1 - I * ↑t) + Phi_star ν ε (1 - I * ↑t)) * E (-(1 - I * ↑t) * ↑x)))
      Filter.atTop (nhds (𝓕 (ϕ_pm ν ε) x)) := by
  have hlam : ν ≠ 0 := by linarith
  let fL z := (Phi_circ ν ε z - Phi_star ν ε z) * E (-z * x)
  let fR z := (Phi_circ ν ε z + Phi_star ν ε z) * E (-z * x)
  set AL := ∫ t in Set.Icc (-1 : ℝ) (-1/2), fL t
  set AM := ∫ t in Set.Icc (-1/2 : ℝ) 0, fL t
  set BM := ∫ t in Set.Icc 0 (1/2 : ℝ), fR t
  set BR := ∫ t in Set.Icc (1/2 : ℝ) 1, fR t
  have hci : ∀ (a b : ℝ), IntegrableOn (fun t : ℝ ↦ Phi_circ ν ε (↑t : ℂ) * E (-(↑t : ℂ) * ↑x)) (Set.Ioc a b) :=
    fun a b ↦ (((Phi_circ.contDiff_real ν ε hlam).continuous).mul (cont_E x)).integrableOn_Ioc
  have hsi : ∀ (a b : ℝ), IntegrableOn (fun t : ℝ ↦ Phi_star ν ε (↑t : ℂ) * E (-(↑t : ℂ) * ↑x)) (Set.Ioc a b) :=
    fun a b ↦ (((Phi_star.contDiff_real ν ε hlam).continuous).mul (cont_E x)).integrableOn_Ioc
  have hfLi (a b : ℝ) : IntegrableOn (fun (t : ℝ) ↦ fL t) (Set.Ioc a b) := by
    apply (Integrable.sub (hci a b) (hsi a b)).congr
    filter_upwards [] with t; dsimp [fL]; ring
  have hfRi (a b : ℝ) : IntegrableOn (fun (t : ℝ) ↦ fR t) (Set.Ioc a b) := by
    apply (Integrable.add (hci a b) (hsi a b)).congr
    filter_upwards [] with t; dsimp [fR]; ring
  have hfourier : 𝓕 (ϕ_pm ν ε) x = AL + AM + BM + BR := by
    rw [varphi_fourier_ident ν ε hlam x]
    have hA : ∫ t in Set.Icc (-1 : ℝ) 0, fL t = AL + AM := by
      simp only [AL, AM]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioc_of_le (by norm_num)) measurableSet_Ioc (hfLi _ _) (hfLi _ _)]
      rw [Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)]
    have hB : ∫ t in Set.Icc (0 : ℝ) 1, fR t = BM + BR := by
      simp only [BM, BR]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioc_of_le (by norm_num)) measurableSet_Ioc (hfRi _ _) (hfRi _ _)]
      rw [Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)]
    rw [hA, hB]; ring
  have hALshift : Filter.Tendsto (fun T : ℝ ↦ (I * ∫ t in Set.Icc 0 T, fL (-1 / 2 - I * t)) - (I * ∫ t in Set.Icc 0 T, fL (-1 - I * t))) Filter.atTop (nhds AL) := by
    obtain ⟨g, hg_anal, hg_eq⟩ := Phi_fourier_holo_left ν ε x hν
    have h_g_AL : (∫ t in (-1 : ℝ)..(-1 / 2), g t) = AL := by
      dsimp [AL]
      rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Icc_eq_integral_Ioc]
      have : Set.Ioc (-1 : ℝ) (-1 / 2) = Set.Ioc (-1) (-(1 / 2)) := by norm_num
      rw [this]
      apply MeasureTheory.setIntegral_congr_ae
      · exact measurableSet_Ioc
      · filter_upwards with t ht
        apply hg_eq
        simp only [z₀_pole, ne_eq, Set.mem_setOf_eq]
        intro h
        have h_im := (Complex.ext_iff.mp h).2
        simp only [ofReal_im, sub_im, neg_im, one_im, neg_zero, mul_im, I_re, zero_mul, I_im,
          one_mul, zero_add, zero_sub, zero_eq_neg] at h_im
        norm_cast at h_im
        field_simp [Real.pi_ne_zero] at h_im
        linarith [hν]
    have h_g_lim : Filter.Tendsto (fun T : ℝ  ↦ (I * ∫ t in Set.Icc 0 T, g (-(1 / 2 : ℝ) - I * t)) - (I * ∫ t in Set.Icc 0 T, g (-1 - I * t))) Filter.atTop (nhds (∫ t in (-1)..(-1 / 2 : ℝ), g t)) := by
      convert tendsto_contour_shift_downwards (σ := -1) (σ' := -1/2) (f := g) ?_ ?_ using 1
      · ext T; congr 1
        · congr 1; apply MeasureTheory.setIntegral_congr_ae
          · exact measurableSet_Icc
          · filter_upwards [] with t ht; congr 1; push_cast; ring
        · congr 1; apply MeasureTheory.setIntegral_congr_ae
          · exact measurableSet_Icc
          · filter_upwards [] with t ht; congr 1; push_cast; ring
      · push_cast; ring_nf
        intro U hU
        convert hg_anal U hU
      · apply horizontal_integral_phi_fourier_vanish_downwards ν ε x (-1) (-1 / 2) hν hx
          (Set.Icc_subset_Icc (by norm_num) (by norm_num)) (by norm_num) g
        · intro T hT
          exact_mod_cast (hg_anal T (by linarith)).continuousOn
        · obtain ⟨C, T₀, hT₀_bound, hC⟩ := phi_bound_downwards ν ε hν
          apply Filter.eventually_atTop.mpr
          use T₀
          intro T hT t ht
          have h_not_pole : (↑t - I * ↑T) ≠ z₀_pole ν := by
            intro h_pole
            have h_T_val : T = ν / (2 * π) := by
              replace h_pole := (Complex.ext_iff.mp h_pole).2
              simp [z₀_pole, Complex.I_im, Complex.I_re, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re] at h_pole
              norm_cast at h_pole
            linarith [hT, h_T_val ▸ hT₀_bound]
          rw [hg_eq h_not_pole]
          dsimp [fL]
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact norm_sub_le _ _
    refine h_g_AL ▸ (h_g_lim.congr' (Filter.Eventually.of_forall fun T ↦ ?_))
    · congr 1
      · congr 1
        apply MeasureTheory.setIntegral_congr_ae
        · exact measurableSet_Icc
        · filter_upwards with t ht; dsimp [fL]; push_cast; simp only [neg_div]; apply hg_eq
          intro h
          simp only [one_div] at h
          apply absurd (Complex.ext_iff.mp h).1 (by dsimp [z₀_pole]; norm_cast; simp)
      · congr 1
        apply MeasureTheory.setIntegral_congr_ae
        · exact measurableSet_Icc
        · filter_upwards [ae_iff.mpr (show volume {t | ¬ t ≠ ν / (2 * π)} = 0 from (by simp))] with t hne
          intro ht; apply hg_eq; dsimp [fL];
          simp only [z₀_pole, sub_right_inj, mul_eq_mul_left_iff,
            I_ne_zero, or_false]
          intro h_eq
          have h_im := (Complex.ext_iff.mp h_eq).2
          exact hne (by simp at h_im; exact_mod_cast h_eq)
  have hBRshift : Filter.Tendsto (fun T : ℝ ↦ (I * ∫ t in Set.Icc 0 T, fR (1 - I * t)) - (I * ∫ t in Set.Icc 0 T, fR (1 / 2 - I * t))) Filter.atTop (nhds BR) := by
    obtain ⟨g, hg_anal, hg_eq⟩ := Phi_fourier_holo_right ν ε x hν
    convert tendsto_contour_shift_downwards (σ := 1 / 2) (σ' := 1) (f := g) ?_ ?_ using 1
    · ext T; congr 1
      · congr 1
        apply MeasureTheory.setIntegral_congr_ae
        · exact measurableSet_Icc
        · filter_upwards [ae_iff.mpr (show volume {t | ¬ t ≠ ν / (2 * π)} = 0 by simp)] with t hne
          intro ht; dsimp [fR]; symm; apply hg_eq;
          simp only [z₁_pole, ne_eq, Set.mem_setOf_eq,
            sub_right_inj, mul_eq_mul_left_iff, I_ne_zero, or_false]
          intro h
          replace h := Complex.ext_iff.mp h; norm_cast at h
          exact hne h.1
      · congr 1
        apply MeasureTheory.setIntegral_congr_ae
        · exact measurableSet_Icc
        · filter_upwards with t
          intro ht; dsimp [fR]; symm; convert hg_eq _ using 1
          · norm_num
          · intro h; have h_re := congr_arg Complex.re h
            simp [z₁_pole] at h_re; norm_cast at h_re; norm_num at h_re
    · congr 1
      dsimp [BR]
      rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_ae
      · exact measurableSet_Ioc
      · filter_upwards with t
        intro ht; dsimp [fR]; symm; apply hg_eq; simp only [z₁_pole, ne_eq, Set.mem_setOf_eq]; intro h
        have h_im := (Complex.ext_iff.mp h).2
        simp only [ofReal_im, sub_im, one_im, mul_im, I_re, zero_mul, I_im, one_mul, zero_add,
          zero_sub, zero_eq_neg] at h_im; norm_cast at h_im
        field_simp [Real.pi_ne_zero] at h_im; linarith [hν]
    · intro U hU
      convert hg_anal U hU
      push_cast; ring
    · apply horizontal_integral_phi_fourier_vanish_downwards ν ε x (1 / 2) 1 hν hx
        (Set.Icc_subset_Icc (by norm_num) (by norm_num)) (by norm_num) g
      · intro T hT
        convert (hg_anal T (by linarith)).continuousOn using 1
        push_cast; ring_nf
      · obtain ⟨C, T₀, hT₀_bound, hC⟩ := phi_bound_downwards ν ε hν
        apply Filter.eventually_atTop.mpr
        use T₀
        intro T hT t ht
        have h_not_pole : (↑t - I * ↑T) ≠ z₁_pole ν := by
          intro h_pole
          have h_T_val : T = ν / (2 * π) := by
            replace h_pole := (Complex.ext_iff.mp h_pole).2
            simp only [sub_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul,
              zero_add, zero_sub, z₁_pole, one_im, zero_mul, neg_inj] at h_pole
            exact_mod_cast h_pole
          linarith [hT, h_T_val ▸ hT₀_bound]
        rw [hg_eq h_not_pole]
        dsimp [fR]
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
  have hmiddle : AM + BM = (∫ t in Set.Icc (-1/2 : ℝ) (1/2 : ℝ), Phi_circ ν ε t * E (-t * x)) - (∫ t in Set.Icc (-1/2 : ℝ) 0, Phi_star ν ε t * E (-t * x)) + (∫ t in Set.Icc 0 (1/2 : ℝ), Phi_star ν ε t * E (-t * x)) := by
    simp only [AM, BM, fL, fR]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
    simp_rw [sub_mul, add_mul]
    rw [integral_sub (hci (-1/2) 0) (hsi (-1/2) 0), integral_add (hci 0 (1/2)) (hsi 0 (1/2))]
    rw [show Set.Ioc (-1/2 : ℝ) (1/2) = Set.Ioc (-1/2) 0 ∪ Set.Ioc 0 (1/2) from
          (Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm,
        MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl)
          measurableSet_Ioc (hci _ _) (hci _ _)]
    abel
  have h_combined_lim := (hALshift.add hBRshift).add_const (AM + BM)
  rw [hmiddle] at h_combined_lim
  simp only [fL, fR] at h_combined_lim
  convert h_combined_lim using 1
  · ext T; ring
  · rw [hfourier]
    congr 1
    linear_combination hmiddle

lemma first_contour_bottom_vanishes (ν ε : ℝ) (x : ℝ) (hx : x > 0) :
    Filter.Tendsto (fun T : ℝ ↦ ∫ t in (-1/2 : ℝ)..1/2, (fun z ↦ Phi_circ ν ε z * E (-z * x)) (t - I * T))
      Filter.atTop (nhds 0) := by
  let f : ℂ → ℂ := fun z ↦ Phi_circ ν ε z * E (-z * x)
  have h_f_bound : ∃ C : ℝ, ∃ T₀ : ℝ, T₀ ≥ ν / (2 * π) + 1 ∧ ∀ T : ℝ, T ≥ T₀ → ∀ t ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ), ‖f (↑t - I * ↑T)‖ ≤ C * Real.exp (-2 * π * x * T) := by
    obtain ⟨C₁, hC₁⟩ := ϕ_circ_bound_left ν ν ε (-(ν / (2 * π) + 1)) (by ring_nf; linarith)
    refine ⟨C₁, ν / (2 * π) + 1, le_refl _, fun T hT t ht => ?_⟩
    have h_phi : ‖Phi_circ ν ε (↑t - I * ↑T)‖ ≤ C₁ :=
      hC₁ ν (Set.left_mem_Icc.mpr (le_refl _)) _ (by
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                    Complex.ofReal_re, mul_zero, zero_sub, zero_add]
        linarith)
    have h_E : ‖E (-(↑t - I * ↑T) * ↑x)‖ = rexp (-2 * π * x * T) := by
      rw [E, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.sub_im, Complex.neg_im,
                  Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
                  Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, zero_mul, add_zero,
                  mul_one, zero_sub, zero_add]
      congr 1; ring
    change ‖Phi_circ ν ε (↑t - I * ↑T) * E (-(↑t - I * ↑T) * ↑x)‖ ≤ C₁ * rexp (-2 * π * x * T)
    rw [norm_mul, h_E]
    exact mul_le_mul_of_nonneg_right h_phi (Real.exp_nonneg _)
  obtain ⟨C, T₀, hT₀_ge, hC⟩ := h_f_bound
  have h_int_le (T : ℝ) (hT : T > ν / (2 * π)) (hT_T₀ : T ≥ T₀) : ‖∫ t in -1 / 2..1 / 2, f (t - I * T)‖ ≤ C * Real.exp (-2 * π * x * T) := by
    calc ‖∫ (t : ℝ) in -1 / 2..1 / 2, f (↑t - I * ↑T)‖
      _ ≤ ∫ (t : ℝ) in -1 / 2..1 / 2, ‖f (↑t - I * ↑T)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ (t : ℝ) in -1 / 2..1 / 2, C * Real.exp (-2 * π * x * T) := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · apply IntervalIntegrable.norm
            rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
            apply integrable_fourier_path (f := fun t ↦ Phi_circ ν ε (↑t - I * ↑T)) (p := fun t ↦ ↑t - I * ↑T)
            · intro t _
              have h_anal : AnalyticAt ℂ (Phi_circ ν ε) (↑t - I * ↑T) := by
                apply Phi_circ.analyticAt_of_im_ne_pole
                simp only [sub_im, ofReal_im, mul_im, I_re,
                  mul_zero, I_im, ofReal_re, one_mul, zero_add, zero_sub, ne_eq]
                intro h
                rw [gt_iff_lt, ← neg_lt_neg_iff, h] at hT
                ring_nf at hT
                exact lt_irrefl _ hT
              have key : ContinuousAt (fun s : ℝ ↦ Phi_circ ν ε ((s : ℂ) - I * ↑T)) t := by
                rw [show (fun s : ℝ ↦ Phi_circ ν ε ((s : ℂ) - I * ↑T)) =
                      Phi_circ ν ε ∘ (fun s : ℝ ↦ (s : ℂ) - I * ↑T) from rfl]
                apply ContinuousAt.comp
                · exact h_anal.continuousAt
                · exact continuous_ofReal.continuousAt.sub continuousAt_const
              exact key.continuousWithinAt
            · fun_prop
          · exact intervalIntegrable_const
          · intro t ht; exact hC T hT_T₀ t ht
      _ = C * Real.exp (-2 * π * x * T) := by
          simp only [intervalIntegral.integral_const]; norm_num
  have h_lim : Filter.Tendsto (fun T ↦ C * Real.exp (-2 * π * x * T)) Filter.atTop (nhds 0) := by
    have hk : -2 * π * x < 0 := by nlinarith [hx, Real.pi_pos]
    have h_vanish : Filter.Tendsto (fun T ↦ Real.exp ((-2 * π * x) * T)) Filter.atTop (nhds 0) := by
      have hu : Filter.Tendsto (fun T ↦ (2 * π * x) * T) Filter.atTop Filter.atTop :=
        Filter.tendsto_id.const_mul_atTop (by nlinarith [hx, Real.pi_pos])
      have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
      simpa [Function.comp_def, pow_zero, neg_mul] using h0.comp hu
    simpa only [mul_zero] using Filter.Tendsto.const_mul C h_vanish
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun T ↦ norm_nonneg _))
  · filter_upwards [Filter.eventually_ge_atTop T₀] with T hT_T₀
    have hT_pole : T > ν / (2 * π) := by linarith [hT₀_ge]
    exact h_int_le T hT_pole hT_T₀
  · exact h_lim

lemma first_contour_integrand_holomorphicOn (ν ε x : ℝ) (z' w' z₀ : ℂ)
    (hz₀ : z₀ = -(I * ν) / (2 * π))
    (h_rect_re : Set.uIcc z'.re w'.re = Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    HolomorphicOn (fun z ↦ Phi_circ ν ε z * E (-z * x)) (Rectangle z' w' \ {z₀}) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · apply AnalyticAt.differentiableAt
    apply Phi_circ.analyticAt_of_not_pole ν ε z
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0; have : z = z₀ := by rw [hn, hz₀]; ring
      exact hz.2 this
    · have hz_re : z.re ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := h_rect_re ▸ hz.1.1
      rw [hn, Complex.sub_re, pole_re ν, sub_zero, Complex.intCast_re] at hz_re
      exact hn0 (unique_int_in_Icc n 0 hz_re (by norm_num) (by norm_num))
  · apply DifferentiableAt.comp
    · exact analyticAt_cexp.differentiableAt
    · fun_prop

@[blueprint
  "first-contour-limit"
  (title := "First contour limit")
  (statement := /--
\[
\int_{-\frac{1}{2}-i\infty}^{-\frac{1}{2}} \Phi^{\pm,\circ}_{\nu}(z)\, e(-zx)\, dz + \int_{-\frac{1}{2}}^{\frac{1}{2}} \Phi^{\pm,\circ}_{\nu}(z)\, e(-zx)\, dz + \int_{\frac{1}{2}}^{\frac{1}{2}-i\infty} \Phi^{\pm,\circ}_{\nu}(z)\, e(-zx)\, dz = e\!\left(-\!\left(-\frac{i\nu}{2\pi}\right)x\right) = e^{-\nu x}
\]
  -/)
  (proof := /-- since the pole is at $-\frac{i\nu}{2\pi}$, the residue of $\Phi^{\pm,\circ}_{\nu}(z)$ at the pole is $\frac{i}{2\pi}$, and our path goes clockwise.
. -/)
  (latexEnv := "sublemma")
  (discussion := 1085)]
theorem first_contour_limit (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦
      (I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (-1/2 - I * t)) * E (-(-1/2 - I * ↑t) * x)))
        + (∫ t in Set.Icc (-1/2:ℝ) (1/2:ℝ), (Phi_circ ν ε t * E (-t * x)))
        - (I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (1/2 - I * t)) * E (- (1/2 - I * ↑t) * x))))
      (nhds (Complex.exp (-ν * x))) := by
  let f : ℂ → ℂ := fun z ↦ Phi_circ ν ε z * E (-z * x)
  have h_pole : ∃ z₀ : ℂ, z₀ = - (I * ν) / (2 * π) ∧ z₀.im < 0 ∧ -1/2 < z₀.re ∧ z₀.re < 1/2 := by
    refine ⟨- (I * ν) / (2 * π), rfl, ?_, ?_, ?_⟩
    · rw [pole_im ν]
      apply div_neg_of_neg_of_pos
      · exact neg_lt_zero.mpr hν
      · exact mul_pos (by norm_num) Real.pi_pos
    · rw [neg_div, neg_div, Complex.neg_re, pole_re]
      norm_num
    · rw [neg_div, Complex.neg_re, pole_re]
      norm_num
  have h_res : ∀ z₀, z₀ = - (I * ν) / (2 * π) →
      Filter.Tendsto (fun z ↦ (z - z₀) * f z) (nhdsWithin z₀ {z₀}ᶜ) (nhds ((I / (2 * π)) * Complex.exp (-ν * x))) := by
    intro z₀ hz₀
    have h_prod : Filter.Tendsto (fun z ↦ ((z - z₀) * Phi_circ ν ε z) * E (-z * x))
        (nhdsWithin z₀ {z₀}ᶜ) (nhds (I / (2 * π) * Complex.exp (-ν * x))) := by
      have h_lim_circ : Filter.Tendsto (fun z ↦ (z - z₀) * Phi_circ ν ε z) (nhdsWithin z₀ {z₀}ᶜ) (nhds (I / (2 * π))) := by
        rw [hz₀, show -(I * ↑ν) / (2 * ↑π) = 0 - I * ↑ν / (2 * ↑π) by ring]
        exact_mod_cast Phi_circ.residue ν ε hν 0
      have h_lim_E : Filter.Tendsto (fun z ↦ E (-z * x)) (nhdsWithin z₀ {z₀}ᶜ) (nhds (Complex.exp (-ν * x))) := by
        have h_E_val : E (-z₀ * x) = Complex.exp (-ν * x) := by
          rw [hz₀, E]
          field_simp [Real.pi_ne_zero]; ring_nf; simp [Complex.I_sq]
        rw [← h_E_val]
        refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
        fun_prop
      exact h_lim_circ.mul h_lim_E
    simpa [f, mul_assoc] using h_prod
  have h_cauchy (T : ℝ) (hT : T > ν / (2 * π)) :
      RectangleIntegral f (-1/2) (1/2 - I * T) = Complex.exp (-ν * x) := by
    obtain ⟨z₀, hz₀, hz₀_im, hz₀_re_neg, hz₀_re_pos⟩ := h_pole
    set z' : ℂ := -1/2 - I * T
    set w' : ℂ := 1/2
    have h_symm : RectangleIntegral f (-1/2) (1/2 - I * T) = - RectangleIntegral f z' w' := by
      rw [rectangleIntegral_symm f z' w']
      have : RectangleIntegral f w' z' = - RectangleIntegral f (-1/2) (1/2 - I * T) := by
        convert rectangleIntegral_symm_re f (-1/2 : ℂ) (1/2 - I * T : ℂ) using 1
        · simp [w', z', Complex.ext_iff]; ring_nf; simp
      rw [this, neg_neg]
    have h_p_in_interior : Rectangle z' w' ∈ nhds z₀ := by
      rw [rectangle_mem_nhds_iff]
      simp only [sub_re, div_ofNat_re, neg_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im,
        ofReal_im, mul_zero, sub_self, sub_zero, one_div, inv_re, re_ofNat, normSq_ofNat,
        div_self_mul_self', sub_im, div_ofNat_im, neg_im, one_im, neg_zero, zero_div, mul_im,
        one_mul, zero_add, zero_sub, inv_im, im_ofNat, z', w']
      rw [hz₀]
      constructor
      · simp only [neg_div, one_div, neg_le_self_iff, inv_nonneg, Nat.ofNat_nonneg, Set.uIoo_of_le,
        Set.mem_preimage, neg_re, Set.mem_Ioo, neg_lt_neg_iff]
        rw [pole_re ν, neg_zero]
        simp only [inv_pos, Nat.ofNat_pos, and_self]
      · have : (-(I * ν) / (2 * π)).im = -ν / (2 * π) := pole_im ν
        rw [Set.mem_preimage, this]
        rw [Set.uIoo_of_lt (by linarith [div_pos hν (by positivity : (0 : ℝ) < 2 * π)]), Set.mem_Ioo]
        constructor
        · field_simp at hT ⊢
          exact neg_lt_neg_iff.mpr hT
        · apply div_neg_of_neg_of_pos
          · linarith
          · linarith [Real.pi_pos]
    have h_f_holo : HolomorphicOn f (Rectangle z' w' \ {z₀}) := by
      apply first_contour_integrand_holomorphicOn ν ε x z' w' z₀ hz₀
      simp only [sub_re, div_ofNat_re, neg_re, one_re, mul_re, I_re, ofReal_re, zero_mul,
        I_im, ofReal_im, mul_zero, sub_self, sub_zero, one_div, inv_re, re_ofNat,
        normSq_ofNat, div_self_mul_self', z', w']
      exact Set.uIcc_of_le (by norm_num)
    set A : ℂ := (I / (2 * π)) * Complex.exp (-ν * x)
    have h_rect' : RectangleIntegral' f z' w' = A := by
      apply ResidueTheoremOnRectangleWithSimplePole'
      · simp [z', w']; field_simp; linarith -- z'.re ≤ w'.re
      · simp only [sub_im, div_ofNat_im, neg_im, one_im, neg_zero, zero_div, mul_im, I_re,
        ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add, zero_sub, one_div, inv_im,
        im_ofNat, normSq_ofNat, Left.neg_nonpos_iff, z', w']
        have h_denom : 0 < 2 * π := by linarith [Real.pi_pos]
        have h_bound : 0 < ν / (2 * π) := div_pos hν h_denom
        linarith [hT, h_bound]
      · exact h_p_in_interior
      · exact h_f_holo
      · let g : ℂ → ℂ := fun z ↦ if z = z₀ then A else (z - z₀) * f z
        have h_g_an : AnalyticAt ℂ g z₀ := by
          apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
          · have h_f_mero : MeromorphicAt f z₀ :=
              (Phi_circ.meromorphic ν ε).meromorphicAt.mul (by unfold E; fun_prop)
            obtain ⟨V, hV_nhds, hV_anal⟩ := h_f_mero.eventually_analyticAt
            filter_upwards [nhdsWithin_le_nhds hV_nhds, self_mem_nhdsWithin] with w hwV hw_ne
            have h_eq : g =ᶠ[nhds w] (fun z ↦ (z - z₀) * f z) :=
              (eventually_ne_nhds hw_ne).mono (fun z hz ↦ by simp [g, hz])
            refine DifferentiableAt.congr_of_eventuallyEq ?_ h_eq
            obtain ⟨b, hb, h_set_eq⟩ := hV_anal
            have hw_f_anal : AnalyticAt ℂ f w := by
              have : w ∈ V ∩ b := ⟨hwV, hb hw_ne⟩
              rwa [← h_set_eq] at this
            exact ((analyticAt_id.sub analyticAt_const).mul hw_f_anal).differentiableAt
          · rw [continuousAt_iff_punctured_nhds]
            convert (h_res z₀ hz₀).congr' ?_
            · exact (by simp [g])
            · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ z₀)
              simp only [g, if_neg hz]
        have h_g_val : g z₀ = A := by simp [g]
        have h_lim : Filter.Tendsto (fun z ↦ f z - A / (z - z₀)) (nhdsWithin z₀ {z₀}ᶜ) (nhds (deriv g z₀)) := by
          have h_g_deriv : HasDerivAt g (deriv g z₀) z₀ := (AnalyticAt.differentiableAt h_g_an).hasDerivAt
          rw [hasDerivAt_iff_tendsto_slope] at h_g_deriv
          refine h_g_deriv.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with z h_ne
          simp only [slope, smul_eq_mul, vsub_eq_sub, h_g_val]
          have hne : z ≠ z₀ := h_ne
          simp only [g, if_neg hne]
          have : z - z₀ ≠ 0 := sub_ne_zero.mpr h_ne
          field_simp
        exact h_lim.isBigO_one ℂ
    rw [h_symm]
    have h_rel : RectangleIntegral f z' w' = (2 * π * I) * RectangleIntegral' f z' w' := by
      simp [RectangleIntegral', smul_eq_mul]
      field_simp [Real.pi_ne_zero, I_ne_zero]
      simp
    rw [h_rel, h_rect']
    simp only [A]
    field_simp [Real.pi_ne_zero, I_ne_zero]
    ring_nf; simp [Complex.I_sq]
  have h_bottom := first_contour_bottom_vanishes ν ε x hx
  have h_vertical : Filter.atTop.Tendsto (fun T : ℝ ↦
      (I * ∫ t in Set.Icc 0 T, f (-1/2 - I * t)) +
      (∫ t in Set.Icc (-1/2:ℝ) (1/2:ℝ), f t) -
      (I * ∫ t in Set.Icc 0 T, f (1/2 - I * t)))
    (nhds (Complex.exp (-ν * x))) := by
    have h_decomp (T : ℝ) : RectangleIntegral f (-1/2) (1/2 - I * T) =
        (∫ t in (-1/2:ℝ)..1/2, f t) - (∫ t in (-1/2:ℝ)..1/2, f (t - I * T)) +
        (I * ∫ t in 0..-T, f ((1/2 : ℝ) + I * t)) - (I * ∫ t in 0..-T, f ((-1/2 : ℝ) + I * t)) := by
      simp only [RectangleIntegral, HIntegral, div_ofNat_im, neg_im, one_im, neg_zero, zero_div,
        ofReal_zero, zero_mul, add_zero, div_ofNat_re, neg_re, one_re, one_div, sub_re, inv_re,
        re_ofNat, normSq_ofNat, div_self_mul_self', mul_re, I_re, ofReal_re, I_im, ofReal_im,
        mul_zero, sub_self, sub_zero, sub_im, inv_im, im_ofNat, mul_im, one_mul, zero_add, zero_sub,
        ofReal_neg, neg_mul, VIntegral, ofReal_inv, ofReal_ofNat, smul_eq_mul, ofReal_div,
        ofReal_one]
      ring_nf
      simp only [one_div, add_right_inj, sub_right_inj]
      congr 1; ext t; congr; ring
    have h_reparam (T : ℝ) (σ : ℝ) (hT : 0 ≤ T) : (I * ∫ t in 0..-T, f (σ + I * t)) = - I * ∫ t in Set.Icc 0 T, f (σ - I * t) := by
      let g (t : ℝ) : ℂ := f (σ + I * t)
      have : (∫ t in 0..-T, g t) = ∫ t in T..0, g (-t) := by
        conv => lhs; rw [← neg_neg (0 : ℝ), ← neg_neg (-T)]
        rw [← intervalIntegral.integral_comp_neg]
        simp
      rw [this, intervalIntegral.integral_symm, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
      simp only [g]; field_simp
      congr; ext t; congr;
      push_cast; ring
    have h_sum (T : ℝ) (hT : 0 ≤ T) : (I * ∫ t in Set.Icc 0 T, f (-1/2 - I * t)) +
        (∫ t in Set.Icc (-1/2:ℝ) (1/2:ℝ), f t) -
        (I * ∫ t in Set.Icc 0 T, f (1/2 - I * t)) =
        RectangleIntegral f (-1/2) (1/2 - I * T) + (∫ t in (-1/2:ℝ)..1/2, f (t - I * T)) := by
      rw [h_decomp T]
      rw [h_reparam T (1/2) hT, h_reparam T (-1/2) hT]
      rw [intervalIntegral.integral_of_le (by norm_num)]
      have hTop : ∫ (t : ℝ) in Set.Icc (-1 / 2) (1 / 2), f t = ∫ (x : ℝ) in Set.Ioc (-1 / 2) (1 / 2), f ↑x := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      have h1 : ∫ (t : ℝ) in Set.Icc 0 T, f (-1 / 2 - I * ↑t) = ∫ (t : ℝ) in Set.Icc 0 T, f (-(I * ↑t) + ↑(-1 / 2)) := by
        congr 1; ext t; congr 1; ring
      have h2 : ∫ (t : ℝ) in Set.Icc 0 T, f (1 / 2 - I * ↑t) = ∫ (t : ℝ) in Set.Icc 0 T, f (-(I * ↑t) + ↑(1 / 2)) := by
        congr 1; ext t; congr 1; ring
      rw [hTop, h1, h2]
      push_cast; ring_nf
    refine Filter.Tendsto.congr' ((Filter.eventually_ge_atTop 0).mono (fun T hT ↦ (h_sum T hT).symm)) ?_
    · rw [show Complex.exp (-ν * x) = Complex.exp (-ν * x) + 0 by simp]
      apply Filter.Tendsto.add
      · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Filter.eventually_gt_atTop (ν / (2 * π))] with T hT
        symm; exact h_cauchy T hT
      · exact h_bottom
  simpa only [f] using h_vertical

lemma second_contour_integrand_holomorphicOn (ν ε x : ℝ) (T : ℝ) (_hT : T ≥ 0) :
    HolomorphicOn (fun z ↦ Phi_star ν ε z * E (-z * x))
      (Rectangle (↑(-1/2 : ℝ)) (↑(0 : ℝ) - I * ↑T)) := by
  intro z hz
  apply DifferentiableWithinAt.mul
  · apply AnalyticAt.differentiableWithinAt
    apply Phi_star.analyticAt_of_not_pole_nz
    intro n hn h_eq
    have h_z_re : z.re = n := by
      replace h_eq := congr_arg Complex.re h_eq
      simp only [sub_re, intCast_re] at h_eq
      rw [pole_re] at h_eq
      simp only [sub_zero] at h_eq
      exact h_eq
    have h_re := hz.1
    simp only [Set.mem_preimage, ofReal_re, sub_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, mul_zero, sub_zero] at h_re
    rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc, h_z_re] at h_re
    exact hn (unique_int_in_Icc n 0 h_re (by norm_num) (by norm_num))
  · dsimp [E]; fun_prop

@[blueprint
  "second-contour-limit"
  (title := "Second contour limit")
  (statement := /--
\[
-\int_{-\frac{1}{2}-i\infty}^{-\frac{1}{2}} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz - \int_{-\frac{1}{2}}^{0} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz = \int_0^{-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz.
\]
  -/)
  (proof := /-- Again by Cauchy's theorem and decay as $\Im z \to -\infty$ -/)
  (latexEnv := "sublemma")
  (discussion := 1086)]
theorem second_contour_limit (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T : ℝ ↦
      (-(I * ∫ t in Set.Icc 0 T, ((Phi_star ν ε (-1/2 - I * t)) * E (-(-1/2 - I * ↑t) * x))))
        - (∫ t in Set.Icc (-1/2 : ℝ) 0, (Phi_star ν ε t * E (-t * x)))
        + (I * ∫ t in Set.Icc 0 T, ((Phi_star ν ε (-I * t)) * E (-(-I * ↑t) * x))))
      (nhds 0) := by
  let f : ℂ → ℂ := fun z ↦ Phi_star ν ε z * E (-z * x)
  have h_anal (T : ℝ) (hT : T ≥ 0) : HolomorphicOn f (Rectangle (↑(-1/2 : ℝ)) (↑(0 : ℝ) - I * ↑T)) := by
    simpa only [f] using second_contour_integrand_holomorphicOn ν ε x T hT
  have h_rect_zero (T : ℝ) (hT : T ≥ 0) : RectangleIntegral f (↑(-1/2 : ℝ)) (↑(0 : ℝ) - I * ↑T) = 0 :=
    HolomorphicOn.vanishesOnRectangle (h_anal T hT) subset_rfl
  have h_goal_eq_bottom (T : ℝ) (hT : 0 ≤ T) :
      (-(I * ∫ t in Set.Icc 0 T, f (-1/2 - I * t)))
        - (∫ t in Set.Icc (-1/2 : ℝ) 0, f t)
        + (I * ∫ t in Set.Icc 0 T, f (-I * t)) =
      - ∫ t in (-1/2 : ℝ)..0, f (t - I * T) := by
    have := h_rect_zero T hT
    simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul] at this
    push_cast at this
    simp only [neg_re, neg_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
      ofReal_neg, mul_zero, mul_one, add_zero,
      sub_zero, zero_sub, neg_zero, mul_comm I] at this
    have h1 : ∫ t in Set.Icc (0 : ℝ) T, f (-1 / 2 - I * t) = - ∫ y in 0..-T, f (-1 / 2 + I * y) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
      ring_nf
      simp_rw [show ∀ x : ℝ, f (-1/2 - I * ↑x) = f (-1/2 + I * ↑(-x)) from
        fun x => by congr 1; push_cast; ring]
      rw [intervalIntegral.integral_comp_neg (fun y => f (-1/2 + I * ↑y))]
      rw [intervalIntegral.integral_symm, neg_zero]
    have h2 : ∫ t in Set.Icc (0 : ℝ) T, f (- I * t) = - ∫ y in 0..-T, f (I * y) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
      simp_rw [show ∀ t : ℝ, f (-I * ↑t) = f (I * ↑(-t)) from
        fun t => by congr 1; push_cast; ring]
      rw [intervalIntegral.integral_comp_neg (fun y => f (I * ↑y)),
          intervalIntegral.integral_symm, neg_zero]
    have h3 : ∫ t in Set.Icc (-1 / 2 : ℝ) (0 : ℝ), f t = ∫ x in (-1 / 2 : ℝ)..0, f x := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    calc
      (-(I * ∫ t in Set.Icc 0 T, f (-1 / 2 - I * ↑t)) - ∫ (t : ℝ) in Set.Icc (-1 / 2) 0, f ↑t) +
          I * ∫ (t : ℝ) in Set.Icc 0 T, f (-I * ↑t)
        = (I * ∫ y in 0..-T, f (-1 / 2 + I * y)) - (∫ x in -1 / 2..0, f x) - (I * ∫ y in 0..-T, f (I * y)) := by
          rw [h1, h2, h3]; ring
      _ = - ∫ x in -1 / 2..0, f (x - I * T) := by
          simp only [show ((-1 / 2 : ℂ)).re = -1 / 2 from by norm_num,
                    show ((-1 / 2 : ℂ)).im = 0 from by norm_num,
                    zero_mul, add_zero, zero_add, ofReal_zero] at this
          have hI1 : ∫ (y : ℝ) in 0..-T, f ((y : ℂ) * I) =
                    ∫ (y : ℝ) in 0..-T, f (I * (y : ℂ)) := by
            congr 1; ext (y : ℝ); ring_nf
          have hI2 : ∫ (y : ℝ) in 0..-T, f ((-1 / 2 : ℂ) + (y : ℂ) * I) =
                    ∫ (y : ℝ) in 0..-T, f ((-1 / 2 : ℂ) + I * (y : ℂ)) := by
            congr 1; ext (y : ℝ); ring_nf
          have hI3 : ∫ (x : ℝ) in -1 / 2..0, f ((x : ℂ) + -(T : ℂ) * I) =
                    ∫ (x : ℝ) in -1 / 2..0, f ((x : ℂ) - I * (T : ℂ)) := by
            congr 1; ext (x : ℝ); ring_nf
          rw [hI1] at this
          push_cast at this
          rw [hI2, hI3] at this
          linear_combination -this
  have h_bottom : Filter.Tendsto (fun T : ℝ ↦ ∫ t in (-1/2 : ℝ)..0, f (t - I * T))
      Filter.atTop (nhds 0) :=
    horizontal_integral_phi_fourier_vanish_downwards ν ε x (-1/2) 0 hν hx
      (Set.Icc_subset_Icc (by norm_num) (by norm_num)) (by norm_num) f
      (fun T hT ↦ (h_anal T (by linarith)).continuousOn)
      (Filter.Eventually.of_forall fun T t _ ↦ by
        simp only [f]; rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg _))
  refine Filter.Tendsto.congr'
    (f₁ := fun (T : ℝ) ↦ - ∫ t in (-1/2 : ℝ)..0, f (↑t - I * ↑T)) ?_
    (by simpa using h_bottom.neg)
  filter_upwards [Filter.eventually_ge_atTop 0] with T hT
  simp only [f] at h_goal_eq_bottom ⊢
  exact (h_goal_eq_bottom T hT).symm

lemma third_contour_integrand_holomorphicOn (ν ε x : ℝ) (U : ℝ) (_hU : U ≥ 0) :
    HolomorphicOn (fun z ↦ Phi_star ν ε z * E (-z * x)) (Rectangle (0 : ℂ) (1/2 - I * U)) := by
  intro z hz
  apply DifferentiableWithinAt.mul
  · apply AnalyticAt.differentiableWithinAt
    apply Phi_star.analyticAt_of_not_pole_nz
    intro n hn h_eq
    have h_z_re : z.re = n := by
      replace h_eq := congr_arg Complex.re h_eq
      simp only [sub_re, intCast_re, pole_re, sub_zero] at h_eq
      exact h_eq
    have h_re := hz.1
    simp only [Set.mem_preimage, Complex.zero_re, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at h_re
    rw [h_z_re] at h_re
    exact hn (unique_int_in_Icc n 0 h_re (by norm_num) (by norm_num))
  · dsimp [E]; fun_prop

@[blueprint
  "third-contour-limit"
  (title := "Third contour limit")
  (statement := /--
\[
\int_0^{\frac{1}{2}} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz + \int_{\frac{1}{2}}^{\frac{1}{2}-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz = -\int_{-i\infty}^{0} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz.
\]
  -/)
  (proof := /-- Similar to previous. -/)
  (latexEnv := "sublemma")
  (discussion := 1087)]
theorem third_contour_limit (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦
      (∫ t in Set.Icc 0 (1/2:ℝ), (Phi_star ν ε t * E (-t * x)))
        - (I * ∫ t in Set.Icc 0 T, ((Phi_star ν ε (1/2 - I * t)) * E (- (1/2 - I * ↑t) * x)))
        + (I * ∫ t in Set.Icc 0 T, ((Phi_star ν ε (-I * t)) * E (-(-I * ↑t) * x))))
      (nhds 0) := by
  let f : ℂ → ℂ := fun z ↦ Phi_star ν ε z * E (-z * x)
  have hf_anal : ∀ (U : ℝ), U ≥ 0 → HolomorphicOn f (Rectangle (0 : ℂ) (1/2 - I * U)) := by
    intro U hU; exact third_contour_integrand_holomorphicOn ν ε x U hU
  have h_bottom : Filter.Tendsto (fun T : ℝ ↦ ∫ t in (0:ℝ)..(1/2:ℝ), f (↑t - I * ↑T))
      Filter.atTop (nhds 0) := by
    apply horizontal_integral_phi_fourier_vanish_downwards ν ε x 0 (1/2) hν hx
      (Set.Icc_subset_Icc (by norm_num) (by norm_num)) (by norm_num) f
    · intro T hT
      convert (hf_anal T (by linarith)).continuousOn using 2
      push_cast; rfl
    · filter_upwards with T; intro t ht
      simp only [f, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      linarith [norm_nonneg (Phi_circ ν ε (↑t - I * ↑T))]
  have h_shift : Filter.Tendsto (fun (T : ℝ) ↦ (I * ∫ t in Set.Icc 0 T, f (1/2 - I * t)) - (I * ∫ t in Set.Icc 0 T, f (0 - I * t)))
      Filter.atTop (nhds (∫ t in (0:ℝ)..(1/2:ℝ), f t)) := by
    let σ : ℝ := 0
    let σ' : ℝ := 1/2
    have hf_anal_rect : ∀ (U : ℝ), U ≥ 0 → HolomorphicOn f (Rectangle (σ : ℂ) (σ' - I * U)) := by
      intro U hU; convert third_contour_integrand_holomorphicOn ν ε x U hU; simp [σ']
    convert tendsto_contour_shift_downwards (σ := σ) (σ' := σ') hf_anal_rect h_bottom
    simp [σ']
  convert ((tendsto_const_nhds (x := ∫ t in (0:ℝ)..(1/2:ℝ), f t)).sub h_shift).congr' ?_ using 1
  · simp
  · filter_upwards [] with T
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    calc
      (∫ (t : ℝ) in Set.Icc 0 (1 / 2), f t) - ((I * ∫ t in Set.Icc 0 T, f (1 / 2 - I * t)) - (I * ∫ t in Set.Icc 0 T, f (0 - I * t)))
      _ = (∫ (t : ℝ) in Set.Icc 0 (1 / 2), Phi_star ν ε t * E (-t * x)) -
          ((I * ∫ t in Set.Icc 0 T, Phi_star ν ε (1 / 2 - I * t) * E (-(1 / 2 - I * t) * x)) -
          (I * ∫ t in Set.Icc 0 T, Phi_star ν ε (-I * t) * E (-(-I * t) * x))) := by
        simp only [f]; simp only [zero_sub, neg_neg]
        have hC : ∫ t in Set.Icc 0 T, Phi_star ν ε (-(I * ↑t)) * E (I * ↑t * ↑x) =
            ∫ t in Set.Icc 0 T, Phi_star ν ε (-I * ↑t) * E (-(-I * ↑t) * ↑x) := by
            congr 1; ext t; simp only [neg_mul, neg_neg]
        rw [hC]
      _ = (∫ (t : ℝ) in Set.Icc 0 (1 / 2), Phi_star ν ε t * E (-(x * t))) -
          ((I * ∫ t in Set.Icc 0 T, Phi_star ν ε (1 / 2 - I * t) * E (x * (-1 / 2) + x * I * t)) -
          (I * ∫ t in Set.Icc 0 T, Phi_star ν ε (-I * t) * E (x * I * t))) := by
        congr 1
        · apply MeasureTheory.integral_congr_ae; refine Filter.Eventually.of_forall (fun t ↦ ?_)
          ring_nf
        · congr 1
          · apply congr_arg (fun z ↦ I * z)
            apply MeasureTheory.integral_congr_ae; refine Filter.Eventually.of_forall (fun t ↦ ?_)
            ring_nf
          · apply congr_arg (fun z ↦ I * z)
            apply MeasureTheory.integral_congr_ae; refine Filter.Eventually.of_forall (fun t ↦ ?_)
            ring_nf
      _ = _ := by
        ring_nf

@[blueprint
  "shift-downwards-simplified"
  (title := "Simplified formula for downward contour shift")
  (statement := /--
If $x > 0$, then $\widehat{\varphi^{\pm}_{\nu}}(x) - e^{-\nu x}$ equals
$$ - \frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu - y) - B^{\pm}(\nu))\, e^{-xy}\, dy. $$
  -/)
  (proof := /-- \begin{align*}
&2\int_0^{-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz - \int_0^{-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-(z-1)x)\, dz - \int_0^{-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-(z+1)x)\, dz\\
&= (2 - e(x) - e(-x)) \int_0^{\infty} \Phi^{\pm,\star}_{\nu}\!\left(-\frac{iy}{2\pi}\right) e\!\left(-\frac{yx}{2\pi i}\right) d\!\left(-\frac{iy}{2\pi}\right)\\
&= -\frac{2i}{\pi}\sin^2 \pi x \int_0^{\infty} \Phi^{\pm,\star}_{\nu}\!\left(-\frac{iy}{2\pi}\right) e^{-xy}\, dy = -\frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu - y) - B^{\pm}(\nu))\, e^{-xy}\, dy.
\end{align*}
 -/)
  (latexEnv := "sublemma")
  (discussion := 1088)]
theorem shift_downwards_simplified (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ - (Real.sin (π * x))^2 / π^2 * ∫ t in Set.Icc 0 T, ((B ε (ν - t) - B ε ν) * Real.exp (-x * t))) (nhds (𝓕 (ϕ_pm ν ε) x - Complex.exp (-ν * x))) := by
  have h_circ_periodic := Phi_circ_periodic ν ε
  have h_re {t : ℝ} (ht : t ≠ ν / (2 * π)) : (-2 : ℂ) * ↑π * I * (-I * ↑t) + ↑ν ≠ 0 := by
    intro h; apply_fun Complex.re at h; rw [w_re] at h; simp at h
    apply ht; field_simp [Real.pi_pos.ne.symm]; linarith [Real.pi_pos]
  have h_im {t : ℝ} (m : ℤ) (hm : m ≠ 0) : (-2 : ℂ) * ↑π * I * (-I * ↑t - ↑m) + ↑ν ≠ 0 := by
    intro h; apply_fun Complex.im at h; simp [Real.pi_pos.ne.symm, hm] at h
  have h_sub (t : ℝ) (ht_pole : t ≠ ν / (2 * π)) :
      Phi_circ ν ε (-1 - I * t) - Phi_star ν ε (-1 - I * t) = -Phi_star ν ε (-I * t) := by
    have h_circ : Phi_circ ν ε (-1 - I * t) = Phi_circ ν ε (-I * t) := by
      rw [show -I * t = (-1 - I * t) + 1 by ring, h_circ_periodic]
    have haff : Phi_star ν ε (-1 - I * t) = Phi_star ν ε (-I * t) + Phi_circ ν ε (-I * t) := by
      have h := phi_star_affine_periodic ν ε hν (-I * t) 1 (h_re ht_pole) (h_im 1 (by norm_num))
      simp only [Int.cast_one, one_mul] at h
      ring_nf at h ⊢; exact h
    rw [h_circ, haff]; ring
  have h_add (t : ℝ) (ht_pole : t ≠ ν / (2 * π)) :
      Phi_circ ν ε (1 - I * t) + Phi_star ν ε (1 - I * t) = Phi_star ν ε (-I * t) := by
    have h_circ : Phi_circ ν ε (1 - I * t) = Phi_circ ν ε (-I * t) := by
      rw [show 1 - I * t = -I * t + 1 by ring, h_circ_periodic]
    have haff : Phi_star ν ε (1 - I * t) = Phi_star ν ε (-I * t) - Phi_circ ν ε (-I * t) := by
      have h := phi_star_affine_periodic ν ε hν (-I * t) (-1) (h_re ht_pole) (h_im (-1) (by norm_num))
      simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add] at h
      ring_nf at h ⊢; exact h
    rw [h_circ, haff]; ring
  have h_factor (T : ℝ) :
      (-I * ∫ t in Set.Icc 0 T,
          (Phi_circ ν ε (-1 - I * t) - Phi_star ν ε (-1 - I * t)) * E (-(-1 - I * t) * x)) +
      (I * ∫ t in Set.Icc 0 T,
          (Phi_circ ν ε (1 - I * t) + Phi_star ν ε (1 - I * t)) * E (-(1 - I * t) * x)) -
      (2 * I * ∫ t in Set.Icc 0 T,
          Phi_star ν ε (-I * t) * E (-(-I * t) * x))
      = (2 - E (-↑x) - E ↑x) * (-I * ∫ t in Set.Icc 0 T, Phi_star ν ε (-I * t) * E (-(-I * t) * x)) := by
    have hE_shift_neg (t : ℝ) : E (-(-1 - I * ↑t) * ↑x) = E ↑x * E (-(-I * ↑t) * ↑x) := by
      simp only [E, ← Complex.exp_add]; congr 1; ring
    have hE_shift_pos (t : ℝ) : E (-(1 - I * ↑t) * ↑x) = E (-↑x) * E (-(-I * ↑t) * ↑x) := by
      simp only [E, ← Complex.exp_add]; congr 1; ring
    have h1 : ∫ t in Set.Icc 0 T, (Phi_circ ν ε (-1 - I * t) - Phi_star ν ε (-1 - I * t)) * E (-(-1 - I * t) * x) =
              ∫ t in Set.Icc 0 T, -(E ↑x * (Phi_star ν ε (-I * t) * E (-(-I * t) * x))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, Measure.ae_ne (volume.restrict (Set.Icc 0 T)) (ν / (2 * π))] with t ht ht_pole
      rw [h_sub t ht_pole, hE_shift_neg]
      ring
    have h2 : ∫ t in Set.Icc 0 T, (Phi_circ ν ε (1 - I * t) + Phi_star ν ε (1 - I * t)) * E (-(1 - I * t) * x) =
              ∫ t in Set.Icc 0 T, E (-↑x) * (Phi_star ν ε (-I * t) * E (-(-I * t) * x)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, Measure.ae_ne (volume.restrict (Set.Icc 0 T)) (ν / (2 * π))] with t ht ht_pole
      rw [h_add t ht_pole, hE_shift_pos]
      ring
    rw [h1, h2]
    rw [integral_neg, integral_const_mul, integral_const_mul]
    ring
  have h_prefactor : (2 : ℂ) - E (-↑x) - E ↑x = 4 * (Real.sin (π * x)) ^ 2 := by
    linear_combination two_sub_E_sq x
  have h_Phi_star_neg_imag (t : ℝ) :
      Phi_star ν ε (-I * ↑t) = (B ε ↑(ν - 2 * π * t) - B ε ↑ν) / (2 * ↑π * I) := by
    simp only [Phi_star]; congr 1; push_cast; ring_nf; simp [Complex.I_sq]; ring_nf
  have h_E_neg_imag (t : ℝ) : E (-(-I * ↑t) * ↑x) = ↑(Real.exp (-2 * π * x * t)) := by
    simp only [E]; push_cast; ring_nf; congr; simp
  have h_imag_integral (T : ℝ) :
      -I * ∫ t in Set.Icc 0 T, Phi_star ν ε (-I * ↑t) * E (-(-I * ↑t) * ↑x)
      = -(1 / (2 * ↑π)) *
        ∫ t in Set.Icc 0 T,
          (B ε ↑(ν - 2 * π * t) - B ε ↑ν) * ↑(Real.exp (-2 * π * x * t)) := by
    simp_rw [h_Phi_star_neg_imag, h_E_neg_imag]
    rw [← integral_const_mul (-I)]
    have : -((1 : ℂ) / (2 * ↑π)) * ∫ t in Set.Icc 0 T,
        (B ε ↑(ν - 2 * π * t) - B ε ↑ν) * ↑(rexp (-2 * π * x * t))
      = ∫ t in Set.Icc 0 T, -((1 : ℂ) / (2 * ↑π)) *
        ((B ε ↑(ν - 2 * π * t) - B ε ↑ν) * ↑(rexp (-2 * π * x * t))) := by
      rw [integral_const_mul]
    rw [this]; congr 1; ext t
    field_simp [Complex.I_ne_zero, Real.pi_pos.ne.symm]
  have h_cov (T : ℝ) (hT : 0 ≤ T) :
      ∫ t in Set.Icc 0 T,
          (B ε ↑(ν - 2 * π * t) - B ε ↑ν) * ↑(Real.exp (-2 * π * x * t))
      = (1 / (2 * π)) *
        ∫ s in Set.Icc 0 (2 * π * T),
          (B ε (ν - s) - B ε ν) * Real.exp (-x * s) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by positivity)]
    let f : ℝ → ℂ := fun s ↦ (B ε (ν - s) - B ε ν) * (Real.exp (-x * s) : ℂ)
    have h_scale := intervalIntegral.integral_comp_mul_left f (c := 2 * π) (by positivity) (a := 0) (b := T)
    dsimp [f] at h_scale
    convert h_scale using 1
    · push_cast; congr 1; ext t; ring_nf
    · push_cast; field_simp; congr 1
      · ext s; ring_nf
      · simp
  let combined_expr : ℝ → ℂ := fun T ↦
    (-I * ∫ t in Set.Icc 0 T, (Phi_circ ν ε (-1 - I*t) - Phi_star ν ε (-1 - I*t)) * E (-(-1 - I*↑t) * x)) +
    (I  * ∫ t in Set.Icc 0 T, (Phi_circ ν ε (1 - I*t) + Phi_star ν ε (1 - I*t)) * E (-(1 - I*↑t) * x)) -
    (2 * I * ∫ t in Set.Icc 0 T, Phi_star ν ε (-I * t) * E (-(-I * t) * x))
  have h_key (T : ℝ) (hT : 0 ≤ T) :
      - (Real.sin (π * x))^2 / π^2 *
        ∫ t in Set.Icc 0 (2*π*T), (B ε (ν - t) - B ε ν) * Real.exp (-x * t)
      = combined_expr T := by
    simp only [combined_expr]
    rw [h_factor T, h_imag_integral T, h_prefactor, h_cov T hT]
    push_cast; field_simp [Real.pi_ne_zero]; ring
  have h_combined_limit : Filter.atTop.Tendsto combined_expr
      (nhds (𝓕 (ϕ_pm ν ε) x - Complex.exp (-↑ν * ↑x))) := by
    have h_arith := (((shift_downwards ν ε hν x hx).sub (first_contour_limit ν ε hν x hx)).sub
        (second_contour_limit ν ε hν x hx)).sub (third_contour_limit ν ε hν x hx)
    have h_lim_ident : (𝓕 (ϕ_pm ν ε) x - Complex.exp (-↑ν * ↑x) - 0 - 0) = (𝓕 (ϕ_pm ν ε) x - cexp (-(↑ν * ↑x))) := by
      simp only [sub_zero]; congr; ring
    rw [h_lim_ident] at h_arith
    ring_nf; apply h_arith.congr'
    filter_upwards [Filter.eventually_ge_atTop 0] with T hT
    simp only [combined_expr, E]
    simp_rw [sub_mul, add_mul]
    rw [integral_sub (integrableOn_Phi_circ_m12 ν ε x T) (integrableOn_Phi_star_m12 ν ε x T),
        integral_add (integrableOn_Phi_circ_p12 ν ε x T) (integrableOn_Phi_star_p12 ν ε x T)]
    ring
  apply (h_combined_limit.comp tendsto_div_two_pi).congr'
  filter_upwards [Filter.eventually_ge_atTop 0] with T hT
  simp only [Function.comp_apply, ofReal_sin, ofReal_mul, neg_mul, ofReal_exp, ofReal_neg]
  rw [← h_key (T / (2*π)) (by positivity)]
  congr 1
  · norm_cast
  · field_simp; norm_cast; simp_rw [mul_comm]

@[blueprint
  "fourier-formula-neg"
  (title := "Fourier formula for negative $x$")
  (statement := /--
Let $\nu > 0$, $x < 0$. Since $x < 0$, $I_{\nu}(x) = 0$, and
$$
\widehat{\varphi^{\pm}_{\nu}}(x) - I_{\nu}(x) = \frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu + y) - B^{\pm}(\nu))\, e^{xy}\, dy.
$$
  -/)
  (proof := /-- This follows from the previous lemma. -/)
  (latexEnv := "lemma")
  (discussion := 1089)]
theorem fourier_formula_neg (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x < 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ (Real.sin (π * x))^2 / π^2 * ∫ t in Set.Icc 0 T, ((B ε (ν + t) - B ε ν) * Real.exp (x * t))) (nhds (𝓕 (ϕ_pm ν ε) x)) := by
    exact shift_upwards_simplified ν ε hν x hx

@[blueprint
  "fourier-formula-pos"
  (title := "Fourier formula for positive $x$")
  (statement := /--
Let $\nu > 0$, $x > 0$. Then
$$
\widehat{\varphi^{\pm}_{\nu}}(x) - e^{-\nu x} = - \frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu - y) - B^{\pm}(\nu))\, e^{-xy}\, dy.
$$
  -/)
  (proof := /-- This follows from the previous lemma. -/)
  (latexEnv := "lemma")
  (discussion := 1090)]
theorem fourier_formula_pos (ν ε : ℝ) (hν : ν > 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ - (Real.sin (π * x))^2 / π^2 * ∫ t in Set.Icc 0 T, ((B ε (ν - t) - B ε ν) * Real.exp (-x * t))) (nhds (𝓕 (ϕ_pm ν ε) x - Complex.exp (-ν * x))) := by
    exact shift_downwards_simplified ν ε hν x hx

private lemma integral_neg_one_zero_eq_zero_one (f : ℝ → ℂ) :
    ∫ t in Set.Icc (-1 : ℝ) 0, f t = ∫ t in Set.Icc 0 1, f (-t) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num), ← intervalIntegral.integral_of_le (by norm_num)]
  rw [intervalIntegral.integral_comp_neg]
  simp

@[blueprint
  "fourier-real"
  (title := "Fourier transform of $\\varphi$ real")
  (statement := /--
$\widehat{\varphi^{\pm}_{\nu}}(x)$ is real.
  -/)
  (proof := /-- This follows from the symmetries of $\varphi^{\pm}_{\nu}$. -/)
  (latexEnv := "lemma")
  (discussion := 1225)]
theorem fourier_real (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) : (𝓕 (ϕ_pm ν ε) x).im = 0 := by
  rw [varphi_fourier_ident ν ε hlam]
  set I_pos := ∫ t in Set.Icc 0 (1 : ℝ),
      (Phi_circ ν ε (↑t : ℂ) + Phi_star ν ε (↑t : ℂ)) * E (-(↑t : ℂ) * ↑x)
  have h_conj : ∫ t in Set.Icc (-1 : ℝ) 0,
      (Phi_circ ν ε (↑t : ℂ) - Phi_star ν ε (↑t : ℂ)) * E (-(↑t : ℂ) * ↑x) =
      starRingEnd ℂ I_pos := by
    rw [integral_neg_one_zero_eq_zero_one, ← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro t _
    simp only [Phi_star_conj_symm, Phi_circ_conj_symm, E_conj_symm, push_cast,
           map_mul, map_add, neg_mul, neg_neg, sub_neg_eq_add]
  simp only [Complex.add_im]
  have hstar_im : (starRingEnd ℂ I_pos).im = -I_pos.im := by rw [Complex.conj_im]
  linarith [h_conj ▸ hstar_im]


@[blueprint
  "varphi-integ"
  (title := "$\\varphi$ integrable")
  (statement := /-- The function $\varphi_\nu^\pm$ is integrable. -/)
  (proof := /-- Apply Lemmas \ref{phi-c2-left}, \ref{phi-c2-right}, \ref{phi-cts} We know $\varphi_\nu^\pm$ is integrable because it is $C^1$ on $[-1, 0]$ and $[0, 1]$, and identically $0$ outside $[-1, 1]$./
-/)
  (latexEnv := "lemma")
  (discussion := 1227)]
theorem varphi_integ (ν ε : ℝ) (hlam : ν ≠ 0) : Integrable (ϕ_pm ν ε) := by
  rw [← integrableOn_univ, ← Set.union_compl_self (Set.Icc (-1 : ℝ) 1)]
  refine IntegrableOn.union ((ϕ_continuous ν ε hlam).continuousOn.integrableOn_compact isCompact_Icc) ?_
  exact (integrable_zero ℝ ℂ volume).integrableOn.congr_fun (fun t ht ↦ (if_neg ht).symm) measurableSet_Icc.compl

@[blueprint
  "Inu_def"
  (title := "Definition of $I_\\nu$")
  (statement := /-- For $\nu > 0$, define $I_\nu(x) := 1_{[0,\infty)}(x) e^{-\nu x}$. -/)]
noncomputable def Inu (ν : ℝ) (x : ℝ) : ℝ := if 0 ≤ x then Real.exp (-ν * x) else 0

private lemma integral_re_B_mul_exp_add (ν T ε u : ℝ) :
    (∫ t in Set.Icc 0 T, (B ε (↑ν + ↑t) - B ε ↑ν) * (Real.exp (u * t) : ℂ)).re =
    ∫ t in Set.Icc 0 T, ((B ε (↑ν + ↑t)).re - (B ε ↑ν).re) * Real.exp (u * t) := by
  set φ := fun t : ℝ ↦ (B ε (↑ν + ↑t) - B ε ↑ν) * (Real.exp (u * t) : ℂ)
  have hf_integ : IntegrableOn φ (Set.Icc 0 T) := by
    apply Continuous.integrableOn_Icc
    apply Continuous.mul
    · apply Continuous.sub
      · apply Continuous.congr (h := (B.continuous_ofReal ε).comp (continuous_add_left ν))
        intro t; simp [Complex.ofReal_add]
      · exact continuous_const
    · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_mul_left u))
  rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hf_integ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [φ, Complex.reCLM_apply, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private lemma integral_re_B_mul_exp_sub (ν T ε u : ℝ) :
    (∫ t in Set.Icc 0 T, (B ε (↑ν - ↑t) - B ε ↑ν) * (Real.exp (u * t) : ℂ)).re =
    ∫ t in Set.Icc 0 T, ((B ε (↑ν - ↑t)).re - (B ε ↑ν).re) * Real.exp (u * t) := by
  set φ := fun t : ℝ ↦ (B ε (↑ν - ↑t) - B ε ↑ν) * (Real.exp (u * t) : ℂ)
  have hf_integ : IntegrableOn φ (Set.Icc 0 T) := by
    apply Continuous.integrableOn_Icc
    apply Continuous.mul
    · apply Continuous.sub
      · apply Continuous.congr (h := (B.continuous_ofReal ε).comp (continuous_sub_left ν))
        intro t; simp [Complex.ofReal_sub]
      · exact continuous_const
    · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_mul_left u))
  rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hf_integ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [φ, Complex.reCLM_apply, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private lemma integral_B_diff_mul_exp_nonneg {T ε ν u : ℝ} (f : ℝ → ℂ) (hf : ∀ t ∈ Set.Icc 0 T, (B ε ↑ν).re ≤ (B ε (f t)).re) :
    0 ≤ ∫ t in Set.Icc 0 T, ((B ε (f t)).re - (B ε ↑ν).re) * Real.exp (u * t) := by
  apply integral_nonneg_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  apply mul_nonneg (sub_nonneg.mpr (hf t ht)) (Real.exp_nonneg _)

private lemma integral_B_diff_mul_exp_nonpos {T ε ν u : ℝ} (f : ℝ → ℂ) (hf : ∀ t ∈ Set.Icc 0 T, (B ε (f t)).re ≤ (B ε ↑ν).re) :
    ∫ t in Set.Icc 0 T, ((B ε (f t)).re - (B ε ↑ν).re) * Real.exp (u * t) ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  apply mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hf t ht)) (Real.exp_nonneg _)

lemma Inu_bounds_neg (ν x : ℝ) (hν : ν > 0) (hx : x < 0) :
    (𝓕 (ϕ_pm ν (-1)) x).re ≤ Inu ν x ∧ Inu ν x ≤ (𝓕 (ϕ_pm ν 1) x).re := by
  have hI : Inu ν x = 0 := if_neg (not_le.mpr hx)
  rw [hI]
  refine ⟨?_, ?_⟩
  · apply le_of_tendsto ((continuous_re.tendsto _).comp (fourier_formula_neg ν (-1) hν x hx))
    apply Filter.Eventually.of_forall; intro T
    simp only [Function.comp_apply]
    rw [show (↑(Real.sin (π * x)) ^ 2 / ↑π ^ 2 : ℂ) = ↑((Real.sin (π * x)) ^ 2 / π ^ 2) by push_cast; ring]
    rw [Complex.re_ofReal_mul, integral_re_B_mul_exp_add]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    apply integral_B_diff_mul_exp_nonpos (fun t ↦ ↑ν + ↑t); intro t ht
    have h_mono := B_minus_mono (show ν ≤ ν + t by simp only [Set.mem_Icc] at ht; linarith)
    push_cast at h_mono; exact h_mono
  · apply ge_of_tendsto ((continuous_re.tendsto _).comp (fourier_formula_neg ν 1 hν x hx))
    apply Filter.Eventually.of_forall; intro T
    simp only [Function.comp_apply]
    rw [show (↑(Real.sin (π * x)) ^ 2 / ↑π ^ 2 : ℂ) = ↑((Real.sin (π * x)) ^ 2 / π ^ 2) by push_cast; ring]
    rw [Complex.re_ofReal_mul, integral_re_B_mul_exp_add]
    apply mul_nonneg (by positivity)
    apply integral_B_diff_mul_exp_nonneg (fun t ↦ ↑ν + ↑t); intro t ht
    have h_mono := B_plus_mono (show ν ≤ ν + t by simp only [Set.mem_Icc] at ht; linarith)
    push_cast at h_mono; exact h_mono

lemma Inu_bounds_pos (ν x : ℝ) (hν : ν > 0) (hx : x > 0) :
    (𝓕 (ϕ_pm ν (-1)) x).re ≤ Inu ν x ∧ Inu ν x ≤ (𝓕 (ϕ_pm ν 1) x).re := by
  have hI : Inu ν x = Real.exp (-ν * x) := if_pos (le_of_lt hx)
  have h_tendsto_plus := (continuous_re.tendsto _).comp (fourier_formula_pos ν 1 hν x hx)
  have h_tendsto_minus := (continuous_re.tendsto _).comp (fourier_formula_pos ν (-1) hν x hx)
  have h_re_eq (ε : ℝ) : (𝓕 (ϕ_pm ν ε) x - Complex.exp (-ν * x)).re = (𝓕 (ϕ_pm ν ε) x).re - Inu ν x := by
    rw [hI, Complex.sub_re]; simp only [neg_mul, sub_right_inj]; norm_cast
  rw [h_re_eq] at h_tendsto_plus h_tendsto_minus
  have hpos : 0 ≤ (𝓕 (ϕ_pm ν 1) x).re - Inu ν x := by
    apply ge_of_tendsto h_tendsto_plus
    apply Filter.Eventually.of_forall; intro T
    simp only [Function.comp_apply]
    rw [show (-↑(Real.sin (π * x)) ^ 2 / ↑π ^ 2 : ℂ) = ↑(-(Real.sin (π * x)) ^ 2 / π ^ 2) by push_cast; ring]
    rw [Complex.re_ofReal_mul, integral_re_B_mul_exp_sub]
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos_of_nonneg (pow_two_nonneg _)) (pow_two_nonneg _)
    · apply integral_B_diff_mul_exp_nonpos (fun t ↦ ↑ν - ↑t); intro t ht
      have h_mono := B_plus_mono (show ν - t ≤ ν by simp only [Set.mem_Icc] at ht; linarith)
      push_cast at h_mono; exact h_mono
  have hneg : (𝓕 (ϕ_pm ν (-1)) x).re - Inu ν x ≤ 0 := by
    apply le_of_tendsto h_tendsto_minus
    apply Filter.Eventually.of_forall; intro T
    simp only [Function.comp_apply]
    rw [show (-↑(Real.sin (π * x)) ^ 2 / ↑π ^ 2 : ℂ) = ↑(-(Real.sin (π * x)) ^ 2 / π ^ 2) by push_cast; ring]
    rw [Complex.re_ofReal_mul, integral_re_B_mul_exp_sub]
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos_of_nonneg (pow_two_nonneg _)) (pow_two_nonneg _)
    · apply integral_B_diff_mul_exp_nonneg (fun t ↦ ↑ν - ↑t); intro t ht
      have h_mono := B_minus_mono (show ν - t ≤ ν by simp only [Set.mem_Icc] at ht; linarith)
      push_cast at h_mono; exact h_mono
  exact ⟨by linarith, by linarith⟩

lemma Inu_bounds_zero (ν : ℝ) (hν : ν > 0) :
    (𝓕 (ϕ_pm ν (-1)) 0).re ≤ Inu ν 0 ∧ Inu ν 0 ≤ (𝓕 (ϕ_pm ν 1) 0).re := by
  rw [show Inu ν 0 = 1 by simp [Inu]]
  have h_cont : ∀ ε : ℝ, Continuous (fun x : ℝ ↦ (𝓕 (ϕ_pm ν ε) x).re) := fun ε ↦
    continuous_re.comp <| VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) (varphi_integ ν ε hν.ne')
  haveI hbot : Filter.NeBot (nhdsWithin 0 (Set.Ioi (0 : ℝ))) := nhdsWithin_Ioi_neBot le_rfl
  have h_I_rcts : Filter.Tendsto (fun x : ℝ ↦ Inu ν x) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 1) := by
    have h_eq : (fun x : ℝ ↦ Inu ν x) =ᶠ[nhdsWithin 0 (Set.Ioi (0 : ℝ))] (fun x ↦ Real.exp (-ν * x)) :=
      eventually_nhdsWithin_of_forall fun _ hx ↦ if_pos (le_of_lt hx)
    have h_tendsto_exp : Filter.Tendsto (fun x ↦ Real.exp (-ν * x)) (nhds 0) (nhds 1) := by
      simpa using Continuous.tendsto (by fun_prop : Continuous fun x ↦ Real.exp (-ν * x)) 0
    exact Filter.Tendsto.congr' h_eq.symm (Filter.Tendsto.mono_left h_tendsto_exp nhdsWithin_le_nhds)
  exact ⟨le_of_tendsto_of_tendsto (hf := (h_cont (-1)).continuousAt.continuousWithinAt) (hg := h_I_rcts)
      (eventually_nhdsWithin_of_forall fun x hx ↦ (Inu_bounds_pos ν x hν hx).1),
    le_of_tendsto_of_tendsto (hf := h_I_rcts) (hg := (h_cont 1).continuousAt.continuousWithinAt)
      (eventually_nhdsWithin_of_forall fun x hx ↦ (Inu_bounds_pos ν x hν hx).2)⟩

@[blueprint
  "Inu_bounds"
  (title := "Bound for $I_\\nu$")
  (statement := /--
For all $x \in \mathbb{R}$,
$$
    \widehat{\varphi_\nu^-}(x) \leq I_\nu(x) \leq \widehat{\varphi_\nu^+}(x).
$$-/)
  (proof := /-- By Lemmas \ref{B-plus-mono}, \ref{B-minus-mono}, the integrands in Lemmas \ref{fourier-formula-neg}, \ref{fourier-formula-pos} are non-negative. Hence, the bound holds for all $x \neq 0$. By definition, $I_\nu$ is right-continuous. Since $\varphi_\nu^\pm \in L^1(\mathbb{R})$, $\widehat{\varphi_\nu^\pm}$ is continuous on $\mathbb{R}$. Thus, letting $x \to 0^+$, we see that the bound holds for $x = 0$ as well.  -/)
  (latexEnv := "corollary")
  (discussion := 1224)]
theorem Inu_bounds (ν x : ℝ) (hν : ν > 0) :
    (𝓕 (ϕ_pm ν (-1)) x).re ≤ Inu ν x ∧ Inu ν x ≤ (𝓕 (ϕ_pm ν 1) x).re := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · exact Inu_bounds_neg ν x hν hx
  · exact Inu_bounds_zero ν hν
  · exact Inu_bounds_pos ν x hν hx


@[blueprint
  "varphi-deriv-integ"
  (title := "$\\varphi'$ integrable")
  (statement := /-- The function $(\varphi_\nu^\pm)'$ is integrable. -/)
  (proof := /-- Apply Lemmas \ref{phi-c2-left}, \ref{phi-c2-right}, \ref{phi-cts} We know $(\varphi_\nu^\pm)'$ is integrable because it is $C^1$ on $[-1, 0]$ and $[0, 1]$, and identically $0$ outside $[-1, 1]$./
-/)
  (latexEnv := "lemma")
  (discussion := 1228)]
theorem varphi_deriv_integ (ν ε : ℝ) (hlam : ν ≠ 0) : Integrable (deriv (ϕ_pm ν ε)) := by
  rw [← integrableOn_univ, ← Set.union_compl_self (Set.Icc (-1 : ℝ) 1)]
  refine IntegrableOn.union ?_ ?_
  · have h_Icc : (Set.Icc (-1 : ℝ) 1) = Set.Icc (-1) 0 ∪ Set.Icc 0 1 :=
      (Set.Icc_union_Icc_eq_Icc (by norm_num : (-1:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 1)).symm
    rw [h_Icc]
    refine IntegrableOn.union ?_ ?_
    · have h_cont : ContinuousOn (derivWithin (ϕ_pm ν ε) (Set.Icc (-1) 0)) (Set.Icc (-1) 0) :=
        (ϕ_c2_left ν ε hlam).continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
      have h_int_within : IntegrableOn (derivWithin (ϕ_pm ν ε) (Set.Icc (-1) 0)) (Set.Icc (-1) 0) :=
        h_cont.integrableOn_compact isCompact_Icc
      rw [integrableOn_Icc_iff_integrableOn_Ioo] at h_int_within ⊢
      refine IntegrableOn.congr_fun h_int_within ?_ measurableSet_Ioo
      intro x hx
      have h1 : derivWithin (ϕ_pm ν ε) (Set.Ioo (-1) 0) x = deriv (ϕ_pm ν ε) x :=
        derivWithin_of_isOpen isOpen_Ioo hx
      have h2 : derivWithin (ϕ_pm ν ε) (Set.Ioo (-1) 0) x = derivWithin (ϕ_pm ν ε) (Set.Icc (-1) 0) x :=
        derivWithin_subset Set.Ioo_subset_Icc_self (isOpen_Ioo.uniqueDiffWithinAt hx)
          ((ϕ_c2_left ν ε hlam).differentiableOn (by norm_num) x (Set.Ioo_subset_Icc_self hx))
      rw [← h2, h1]
    · have h_cont : ContinuousOn (derivWithin (ϕ_pm ν ε) (Set.Icc 0 1)) (Set.Icc 0 1) :=
        (ϕ_c2_right ν ε hlam).continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
      have h_int_within : IntegrableOn (derivWithin (ϕ_pm ν ε) (Set.Icc 0 1)) (Set.Icc 0 1) :=
        h_cont.integrableOn_compact isCompact_Icc
      rw [integrableOn_Icc_iff_integrableOn_Ioo] at h_int_within ⊢
      refine IntegrableOn.congr_fun h_int_within ?_ measurableSet_Ioo
      intro x hx
      have h1 : derivWithin (ϕ_pm ν ε) (Set.Ioo 0 1) x = deriv (ϕ_pm ν ε) x :=
        derivWithin_of_isOpen isOpen_Ioo hx
      have h2 : derivWithin (ϕ_pm ν ε) (Set.Ioo 0 1) x = derivWithin (ϕ_pm ν ε) (Set.Icc 0 1) x :=
        derivWithin_subset Set.Ioo_subset_Icc_self (isOpen_Ioo.uniqueDiffWithinAt hx)
          ((ϕ_c2_right ν ε hlam).differentiableOn (by norm_num) x (Set.Ioo_subset_Icc_self hx))
      rw [← h2, h1]
  · exact (integrable_zero ℝ ℂ volume).integrableOn.congr_fun (by
      intro t ht
      have h_nhds : (Set.Icc (-1 : ℝ) 1)ᶜ ∈ nhds t := isClosed_Icc.isOpen_compl.mem_nhds ht
      have h_eq : ϕ_pm ν ε =ᶠ[nhds t] (fun _ ↦ (0 : ℂ)) := by
        filter_upwards [h_nhds] with x hx
        unfold ϕ_pm
        exact if_neg hx
      rw [h_eq.deriv_eq, deriv_const]) measurableSet_Icc.compl

lemma varphi_ftc_left (ν ε : ℝ) (hlam : ν ≠ 0) {x y : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 0) (hy : y ∈ Set.Icc (-1 : ℝ) 0) :
    ∫ t in x..y, deriv (ϕ_pm ν ε) t = (ϕ_pm ν ε) y - (ϕ_pm ν ε) x := by
  apply intervalIntegral.integral_deriv_eq_sub_uIoo
  -- Subgoal 1: Continuity
  · apply (ϕ_continuous ν ε hlam).continuousOn.mono
    exact Set.uIcc_subset_Icc hx hy
  -- Subgoal 2: Differentiability on uIoo
  · intro t ht
    have ht' : t ∈ Set.Ioo (-1 : ℝ) 0 := by
      constructor
      · linarith [hx.1, hy.1, ht.1, le_min hx.1 hy.1] -- ht.1 is min x y < t
      · linarith [hx.2, hy.2, ht.2, max_le hx.2 hy.2] -- ht.2 is t < max x y
    exact varphi_differentiableAt_left ν ε hlam ht'
  -- Subgoal 3: Integrability
  · exact (varphi_deriv_integ ν ε hlam).intervalIntegrable


lemma varphi_ftc_right (ν ε : ℝ) (hlam : ν ≠ 0) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ∫ t in x..y, deriv (ϕ_pm ν ε) t = (ϕ_pm ν ε) y - (ϕ_pm ν ε) x := by
  apply intervalIntegral.integral_deriv_eq_sub_uIoo
  -- Subgoal 1: Continuity
  · apply (ϕ_continuous ν ε hlam).continuousOn.mono
    exact Set.uIcc_subset_Icc hx hy
  -- Subgoal 2: Differentiability on uIoo
  · intro t ht
    have ht' : t ∈ Set.Ioo 0 1 := by
      constructor
      · linarith [hx.1, hy.1, ht.1, le_min hx.1 hy.1]
      · linarith [hx.2, hy.2, ht.2, max_le hx.2 hy.2]
    exact varphi_differentiableAt_right ν ε hlam ht'
  -- Subgoal 3: Integrability
  · exact (varphi_deriv_integ ν ε hlam).intervalIntegrable

lemma varphi_ftc_out (ν ε : ℝ) (hlam : ν ≠ 0) {x y : ℝ}
    (h : (x ≤ -1 ∧ y ≤ -1) ∨ (x ≥ 1 ∧ y ≥ 1)) :
    ∫ t in x..y, deriv (ϕ_pm ν ε) t = (ϕ_pm ν ε) y - (ϕ_pm ν ε) x := by
  let f := ϕ_pm ν ε
  change ∫ t in x..y, deriv f t = f y - f x
  have hf_const {t : ℝ} (ht : t ≤ -1 ∨ t ≥ 1) : f t = 0 := by
    unfold f ϕ_pm; split_ifs with h_mem
    · rcases ht with h_le | h_ge
      · have : t = -1 := by linarith [h_le, h_mem.1]
        subst this
        simpa [ϕ_pm] using (ϕ_pm_zero_boundary ν ε hlam).1
      · have : t = 1 := by linarith [h_ge, h_mem.2]
        subst this
        simpa [ϕ_pm] using (ϕ_pm_zero_boundary ν ε hlam).2
    · rfl
  have hf_deriv (t : ℝ) (ht : t < -1 ∨ t > 1) : deriv f t = 0 := by
    have h_eq : f =ᶠ[nhds t] 0 := by
      have : t ∈ (Set.Icc (-1) 1)ᶜ := by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
        intro; rcases ht with h | h <;> linarith
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds this] with z hz
      unfold f ϕ_pm; exact if_neg hz
    rw [h_eq.deriv_eq]
    simp
  rw [hf_const (h.elim (fun h' ↦ Or.inl h'.2) (fun h' ↦ Or.inr h'.2)),
      hf_const (h.elim (fun h' ↦ Or.inl h'.1) (fun h' ↦ Or.inr h'.1)), sub_zero]
  apply intervalIntegral.integral_zero_ae
  -- Top-level case split on the hypothesis h
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩

  · -- ══ CASE 1: x ≤ -1, y ≤ -1 ══
    -- The interval uIoc x y lies in (-∞, -1].
    -- The only point where hf_deriv is silent is {-1}, which is Lebesgue-null.

    -- A: Bound all points in the interval above by -1
    have hmax : max x y ≤ -1 := max_le hx hy
    have hbound : ∀ x_1 ∈ Set.uIoc x y, x_1 ≤ -1 := by
      intro x_1 hx1
      simp only [Set.uIoc, Set.mem_Ioc] at hx1
      -- hx1 : min x y < x_1 ∧ x_1 ≤ max x y
      -- Proof: x_1 ≤ max x y ≤ -1 by transitivity with hmax
      exact le_trans hx1.2 hmax

    -- B: Lebesgue-almost every real is ≠ -1, since {-1} is a null set
    have hne_ae : ∀ᵐ (x_1 : ℝ), x_1 ≠ (-1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      -- Goal becomes: volume {x_1 | ¬(x_1 ≠ -1)} = 0
      -- Proof: simplify the set to {-1}, then apply Real.volume_singleton
      have hset : {x_1 : ℝ | ¬(x_1 ≠ -1)} = {-1} := by ext; simp
      rw [hset]
      -- (derivable from MeasureTheory.measure_singleton_eq_zero + NoAtoms instance for ℝ)
      apply Real.volume_singleton

    -- C: Combine A and B via filter_upwards
    filter_upwards [hne_ae] with x_1 hne
    intro hx1
    -- hne : x_1 ≠ -1
    -- hbound x_1 hx1 : x_1 ≤ -1
    -- Together: x_1 < -1, so hf_deriv applies (left disjunct)
    exact hf_deriv x_1 (Or.inl (lt_of_le_of_ne (hbound x_1 hx1) hne))

  · -- ══ CASE 2: x ≥ 1, y ≥ 1 ══
    -- uIoc x y = (min x y, max x y] ⊆ (1, ∞).
    -- hf_deriv applies at EVERY point, so ∀ᵐ follows trivially from ∀.

    have hmin : 1 ≤ min x y := le_min hx hy

    -- Since the claim holds pointwise, ae is immediate
    apply Filter.Eventually.of_forall
    intro x_1 hx1
    simp only [Set.uIoc, Set.mem_Ioc] at hx1
    -- hx1 : min x y < x_1 ∧ x_1 ≤ max x y
    apply hf_deriv
    right
    -- 1 ≤ min x y < x_1, so 1 < x_1 by transitivity
    exact lt_of_le_of_lt hmin hx1.1


@[blueprint
  "varphi-abs"
  (title := "$\\varphi$ absolutely continuous")
  (statement := /-- The function $\varphi_\nu^\pm$ is absolutely continuous. -/)
  (proof := /-- Apply Lemmas \ref{phi-c2-left}, \ref{phi-c2-right}, \ref{phi-cts} We know $\varphi_\nu^\pm$ is absolutely continuous because it is $C^1$ on $[-1, 0]$ and $[0, 1]$, and identically $0$ outside $[-1, 1]$./
-/)
  (latexEnv := "lemma")
  (discussion := 1226)]
theorem varphi_abs (ν ε : ℝ) (hlam : ν ≠ 0) : AbsolutelyContinuous (ϕ_pm ν ε) := by
  constructor
  · -- Prove differentiable almost everywhere
    have h_diff_left : ∀ x ∈ Set.Ioo (-1 : ℝ) 0, DifferentiableAt ℝ (ϕ_pm ν ε) x :=
      fun x hx => varphi_differentiableAt_left ν ε hlam hx
    have h_diff_right : ∀ x ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (ϕ_pm ν ε) x :=
      fun x hx => varphi_differentiableAt_right ν ε hlam hx
    have h_diff_out : ∀ x ∈ (Set.Icc (-1 : ℝ) 1)ᶜ, DifferentiableAt ℝ (ϕ_pm ν ε) x :=
      fun x hx => varphi_differentiableAt_out ν ε hx
    -- Step 1: Differentiable almost everywhere
    rw [ae_iff]
    apply MeasureTheory.measure_mono_null (t := {-1, 0, 1})
    · -- Differentiability on the open intervals implies differentiability almost everywhere
      intro x hx
      contrapose! hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Set.mem_setOf_eq,
        not_not] at hx ⊢
      rcases lt_trichotomy x (-1) with h | rfl | h
      · apply h_diff_out; simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]; intro; linarith
      · exfalso; exact hx.1 rfl
      · rcases lt_trichotomy x 0 with h' | rfl | h'
        · exact h_diff_left x ⟨h, h'⟩
        · exfalso; exact hx.2.1 rfl
        · rcases lt_trichotomy x 1 with h'' | rfl | h''
          · exact h_diff_right x ⟨h', h''⟩
          · exfalso; exact hx.2.2 rfl
          · apply h_diff_out; simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]; intro; linarith
    · -- The measure of a finite set is zero
      apply Set.Finite.measure_zero (by simp)
  · -- Prove FTC for all a, b
    intro a b
    let f := ϕ_pm ν ε
    have h_int : Integrable (deriv f) := varphi_deriv_integ ν ε hlam
    have h_int_all (x y : ℝ) : IntervalIntegrable (deriv f) volume x y := h_int.intervalIntegrable
    have h_ftc_left : ∀ x ∈ Set.Icc (-1 : ℝ) 0, ∀ y ∈ Set.Icc (-1 : ℝ) 0, ∫ t in x..y, deriv f t = f y - f x :=
      fun x hx y hy => varphi_ftc_left ν ε hlam hx hy
    have h_ftc_right : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, ∫ t in x..y, deriv f t = f y - f x :=
      fun x hx y hy => varphi_ftc_right ν ε hlam hx hy
    have h_ftc_out : ∀ x y : ℝ, (x ≤ -1 ∧ y ≤ -1) ∨ (x ≥ 1 ∧ y ≥ 1) → ∫ t in x..y, deriv f t = f y - f x :=
      fun x y h => varphi_ftc_out ν ε hlam h
    -- Final bridging and telescoping using ϕ_continuous
    have h_AC (x y : ℝ) : ∫ t in x..y, deriv f t = f y - f x := by
      wlog hxy : x ≤ y generalizing x y
      · rw [intervalIntegral.integral_symm, this y x (by linarith)]; ring

      rw [← intervalIntegral.integral_add_adjacent_intervals (h_int_all x (-1)) (h_int_all (-1) y),
          ← intervalIntegral.integral_add_adjacent_intervals (h_int_all (-1) 0) (h_int_all 0 y),
          ← intervalIntegral.integral_add_adjacent_intervals (h_int_all 0 1) (h_int_all 1 y)]

      have h1 : ∫ t in (-1 : ℝ)..0, deriv f t = f 0 - f (-1) :=
        h_ftc_left (-1) ⟨le_refl _, by norm_num⟩ 0 ⟨by norm_num, le_refl _⟩
      have h2 : ∫ t in (0 : ℝ)..1, deriv f t = f 1 - f 0 :=
        h_ftc_right 0 ⟨le_refl _, by norm_num⟩ 1 ⟨by norm_num, le_refl _⟩
      rw [h1, h2]

      have h_out_left (p : ℝ) : ∫ t in p..(-1), deriv f t = f (-1) - f p := by
        rcases le_or_gt p (-1) with h_le | h_gt
        · exact h_ftc_out p (-1) (Or.inl ⟨h_le, le_refl _⟩)
        · rw [← intervalIntegral.integral_add_adjacent_intervals (h_int_all p 0) (h_int_all 0 (-1))]
          rcases le_or_gt p 0 with hp0 | hp0
          · rw [h_ftc_left p ⟨h_gt.le, hp0⟩ 0 ⟨by norm_num, le_refl _⟩,
                h_ftc_left 0 ⟨by norm_num, le_refl _⟩ (-1) ⟨le_refl _, by norm_num⟩]
            ring
          · rw [← intervalIntegral.integral_add_adjacent_intervals (h_int_all p 1) (h_int_all 1 0)]
            rcases le_or_gt p 1 with hp1 | hp1
            · rw [h_ftc_right p ⟨hp0.le, hp1⟩ 1 ⟨by norm_num, le_refl _⟩,
                  h_ftc_right 1 ⟨by norm_num, le_refl _⟩ 0 ⟨le_refl _, by norm_num⟩,
                  h_ftc_left 0 ⟨by norm_num, le_refl _⟩ (-1) ⟨le_refl _, by norm_num⟩]
              ring
            · rw [h_ftc_out p 1 (Or.inr ⟨hp1.le, le_refl _⟩),
                  h_ftc_right 1 ⟨by norm_num, le_refl _⟩ 0 ⟨le_refl _, by norm_num⟩,
                  h_ftc_left 0 ⟨by norm_num, le_refl _⟩ (-1) ⟨le_refl _, by norm_num⟩]
              ring

      have h_out_right (p : ℝ) : ∫ t in 1..p, deriv f t = f p - f 1 := by
        rcases le_or_gt p 1 with h_le | h_gt
        · rw [← intervalIntegral.integral_add_adjacent_intervals (h_int_all 1 0) (h_int_all 0 p)]
          rcases le_or_gt p 0 with hp0 | hp0
          · rw [← intervalIntegral.integral_add_adjacent_intervals (h_int_all 0 (-1)) (h_int_all (-1) p)]
            rcases le_or_gt p (-1) with hp_1 | hp_1
            · rw [h_ftc_right 1 ⟨by norm_num, le_refl _⟩ 0 ⟨le_refl _, by norm_num⟩,
                  h_ftc_left 0 ⟨by norm_num, le_refl _⟩ (-1) ⟨le_refl _, by norm_num⟩,
                  h_ftc_out (-1) p (Or.inl ⟨le_refl _, hp_1⟩)]
              ring
            · rw [h_ftc_right 1 ⟨by norm_num, le_refl _⟩ 0 ⟨le_refl _, by norm_num⟩,
                  h_ftc_left 0 ⟨by norm_num, le_refl _⟩ (-1) ⟨le_refl _, by norm_num⟩,
                  h_ftc_left (-1) ⟨le_refl _, by norm_num⟩ p ⟨hp_1.le, hp0⟩]
              ring
          · rw [h_ftc_right 1 ⟨by norm_num, le_refl _⟩ 0 ⟨le_refl _, by norm_num⟩,
                h_ftc_right 0 ⟨le_refl _, by norm_num⟩ p ⟨hp0.le, h_le⟩]
            ring
        · exact h_ftc_out 1 p (Or.inr ⟨le_refl _, h_gt.le⟩)

      rw [h_out_left x, h_out_right y]
      ring
    exact (h_AC a b).symm

lemma ϕ_pm_deriv_zero_outside (ν ε : ℝ) {t : ℝ} (ht : t < -1 ∨ t > 1) :
    deriv (ϕ_pm ν ε) t = 0 := by
  have h_nhds : (Set.Icc (-1 : ℝ) 1)ᶜ ∈ nhds t :=
    isClosed_Icc.isOpen_compl.mem_nhds (by
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
      rcases ht with h | h <;> (intro; linarith))
  have h_eq : ϕ_pm ν ε =ᶠ[nhds t] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [h_nhds] with x hx; unfold ϕ_pm; exact if_neg hx
  rw [h_eq.deriv_eq, deriv_const]

lemma ϕ_pm_deriv_Iic_finite (ν ε : ℝ) :
    eVariationOn (deriv (ϕ_pm ν ε)) (Set.Iic (-1 : ℝ)) ≠ ⊤ := by
  set g := deriv (ϕ_pm ν ε)
  have hg_zero : ∀ t < -1, g t = 0 := fun t ht ↦ ϕ_pm_deriv_zero_outside ν ε (Or.inl ht)
  apply ne_top_of_le_ne_top (edist_lt_top (g (-1)) 0).ne
  apply iSup_le; rintro ⟨n, u, hu, hu_mem⟩
  by_cases h_any : ∃ i ∈ Finset.range (n + 1), u i = -1
  · let S := (Finset.range (n + 1)).filter (fun i ↦ u i = -1)
    have hS : S.Nonempty := by
      obtain ⟨i, hi_mem, hi_eq⟩ := h_any
      exact ⟨i, Finset.mem_filter.mpr ⟨hi_mem, hi_eq⟩⟩
    let k := S.min' hS
    have hk_mem : k ∈ S := Finset.min'_mem S hS
    have hu_k : u k = -1 := (Finset.mem_filter.mp hk_mem).2
    have hu_lt : ∀ i < k, u i < -1 := by
      intro i hi
      apply lt_of_le_of_ne (hu_mem i)
      intro h_eq
      have hi_S : i ∈ S := Finset.mem_filter.mpr ⟨by
        have hk_range := (Finset.mem_filter.mp hk_mem).1
        apply Finset.mem_range.mpr
        exact lt_trans hi (Finset.mem_range.mp hk_range), h_eq⟩
      have : k ≤ i := S.min'_le i hi_S
      omega
    have hk_range : k < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hk_mem).1
    have hk_n : k ≤ n := Nat.le_of_lt_succ hk_range
    have hu_eq : ∀ i ≥ k, i ≤ n → u i = -1 := fun i hi h_in ↦
      le_antisymm (hu_mem i) (hu_k ▸ hu hi)
    calc ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))
      _ = ∑ i ∈ Finset.range n, if i + 1 = k then edist (g (-1)) 0 else 0 := by
        apply Finset.sum_congr rfl; intro i hi
        have hi_n : i < n := Finset.mem_range.mp hi
        split_ifs with h_eq_k
        · have : u (i + 1) = -1 := by rw [h_eq_k, hu_k]
          have : u i < -1 := hu_lt _ (by omega)
          rw [‹u (i + 1) = -1›, hg_zero _ ‹u i < -1›]
        · by_cases h_lt_k : i + 1 < k
          · have : u (i + 1) < -1 := hu_lt _ h_lt_k
            have : u i < -1 := hu_lt _ (by omega)
            rw [hg_zero _ ‹u (i + 1) < -1›, hg_zero _ ‹u i < -1›, edist_self]
          · have : i ≥ k := by omega
            have : u (i + 1) = -1 := hu_eq _ (by omega) (by omega)
            have : u i = -1 := hu_eq _ (by omega) (by omega)
            rw [‹u (i + 1) = -1›, ‹u i = -1›, edist_self]
      _ ≤ edist (g (-1)) 0 := by
        rw [Finset.sum_ite]; simp only [Finset.sum_const_zero, add_zero]
        let fS := (Finset.range n).filter (fun i ↦ i + 1 = k)
        have h_card : fS.card ≤ 1 := by
          apply Finset.card_le_one_iff.mpr
          intro x y hx hy
          have hx' := Finset.mem_filter.mp hx
          have hy' := Finset.mem_filter.mp hy
          omega
        calc (fS.sum (fun _ ↦ edist (g (-1)) 0))
          _ = fS.card • edist (g (-1)) 0 := Finset.sum_const _
          _ ≤ 1 • edist (g (-1)) 0 := by gcongr
          _ = edist (g (-1)) 0 := by simp
  · have h_lt : ∀ i ≤ n, u i < -1 := by
      intro i hi
      apply lt_of_le_of_ne (hu_mem i)
      intro h_eq
      apply h_any; exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), h_eq⟩
    calc ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))
      _ = ∑ i ∈ Finset.range n, 0 := by
        apply Finset.sum_congr rfl; intro i hi
        have hi_n : i < n := Finset.mem_range.mp hi
        rw [hg_zero _ (h_lt (i + 1) hi_n), hg_zero _ (h_lt i hi_n.le), edist_self]
      _ = 0 := by simp
      _ ≤ edist (g (-1)) 0 := zero_le _

lemma ϕ_pm_deriv_Ici_finite (ν ε : ℝ) :
    eVariationOn (deriv (ϕ_pm ν ε)) (Set.Ici (1 : ℝ)) ≠ ⊤ := by
  set g := deriv (ϕ_pm ν ε)
  have hg_zero : ∀ t > 1, g t = 0 := fun t ht ↦ ϕ_pm_deriv_zero_outside ν ε (Or.inr ht)
  apply ne_top_of_le_ne_top (edist_lt_top (g 1) 0).ne
  apply iSup_le; rintro ⟨n, u, hu, hu_mem⟩
  by_cases h_any : ∃ i ∈ Finset.range (n + 1), u i = 1
  · let S := (Finset.range (n + 1)).filter (fun i ↦ u i = 1)
    have hS : S.Nonempty := by
      obtain ⟨i, hi_mem, hi_eq⟩ := h_any
      exact ⟨i, Finset.mem_filter.mpr ⟨hi_mem, hi_eq⟩⟩
    let k := S.max' hS
    have hk_mem : k ∈ S := Finset.max'_mem S hS
    have hk_range : k < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hk_mem).1
    have hu_k : u k = 1 := (Finset.mem_filter.mp hk_mem).2
    have hu_gt : ∀ i > k, i ≤ n → u i > 1 := by
      intro i hi hi_n
      apply lt_of_le_of_ne (hu_mem i)
      intro h_eq
      have hi_S : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi_n), h_eq.symm⟩
      have : i ≤ k := S.le_max' i hi_S
      omega
    have hu_eq : ∀ i ≤ k, u i = 1 := fun i hi ↦
      le_antisymm (hu_k ▸ hu hi) (hu_mem i)
    calc ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))
      _ = ∑ i ∈ Finset.range n, if i = k then edist (g 1) 0 else 0 := by
        apply Finset.sum_congr rfl; intro i hi
        have hi_n : i < n := Finset.mem_range.mp hi
        split_ifs with h_eq_k
        · have : u i = 1 := by rw [h_eq_k, hu_k]
          have : u (i + 1) > 1 := hu_gt _ (by omega) (by omega)
          rw [‹u i = 1›, hg_zero _ ‹u (i + 1) > 1›, edist_comm]
        · by_cases h_lt_k : i < k
          · have : u (i + 1) = 1 := hu_eq _ (by omega)
            have : u i = 1 := hu_eq _ (by omega)
            rw [‹u (i + 1) = 1›, ‹u i = 1›, edist_self]
          · have : i > k := by omega
            have : u (i + 1) > 1 := hu_gt _ (by omega) (by omega)
            have : u i > 1 := hu_gt _ (by omega) (by omega)
            rw [hg_zero _ ‹u (i + 1) > 1›, hg_zero _ ‹u i > 1›, edist_self]
      _ ≤ edist (g 1) 0 := by
        rw [Finset.sum_ite]; simp only [Finset.sum_const_zero, add_zero]
        let fS := (Finset.range n).filter (fun i ↦ i = k)
        have h_card : fS.card ≤ 1 := by
          apply Finset.card_le_one_iff.mpr
          intro x y hx hy
          have hx' := Finset.mem_filter.mp hx
          have hy' := Finset.mem_filter.mp hy
          exact hx'.2.trans hy'.2.symm
        calc (fS.sum (fun _ ↦ edist (g 1) 0))
          _ = fS.card • edist (g 1) 0 := Finset.sum_const _
          _ ≤ 1 • edist (g 1) 0 := by gcongr
          _ = edist (g 1) 0 := by simp
  · have h_gt : ∀ i ≤ n, u i > 1 := by
      intro i hi
      apply lt_of_le_of_ne (hu_mem i)
      intro h_eq
      apply h_any; exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), h_eq.symm⟩
    calc ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))
      _ = ∑ i ∈ Finset.range n, 0 := by
        apply Finset.sum_congr rfl; intro i hi
        have hi_n : i < n := Finset.mem_range.mp hi
        rw [hg_zero _ (h_gt (i + 1) hi_n), hg_zero _ (h_gt i hi_n.le), edist_self]
      _ = 0 := by simp
      _ ≤ edist (g 1) 0 := zero_le _



private lemma eVariationOn_add_jump_greatest {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    {f f' : α → E} {s : Set α} {x : α} (hs : IsGreatest s x) (heq : Set.EqOn f f' (s \ {x})) :
    eVariationOn f' s ≤ eVariationOn f s + edist (f' x) (f x) := by
  apply iSup_le; rintro ⟨n, u, hu, us⟩
  by_cases hx : u n = x
  · rcases n with - | n
    · simp
    · let k := Nat.find (⟨n + 1, hx⟩ : ∃ i, u i = x)
      have hk : u k = x := Nat.find_spec (⟨n + 1, hx⟩ : ∃ i, u i = x)
      have h_lt : ∀ i < k, u i < x := fun i hi ↦ lt_of_le_of_ne (hs.2 (us i)) (Nat.find_min _ hi)
      have h_eq_k : ∀ i < k, f' (u i) = f (u i) := fun i hi ↦ (heq ⟨us i, (h_lt i hi).ne⟩).symm
      calc
        ∑ i ∈ Finset.range (n + 1), edist (f' (u (i + 1))) (f' (u i))
            = ∑ i ∈ Finset.range k, edist (f' (u (i + 1))) (f' (u i)) := by
          rw [← Finset.sum_range_add_sum_Ico _ (Nat.find_le hx : k ≤ n + 1)]
          nth_rw 2 [← add_zero (∑ i ∈ Finset.range k, edist (f' (u (i + 1))) (f' (u i)))]
          congr 1
          apply Finset.sum_eq_zero; intro i hi
          have : u i = x := le_antisymm (hs.2 (us i)) (hk ▸ hu (Finset.mem_Ico.mp hi).1)
          have : u (i + 1) = x := le_antisymm (hs.2 (us (i + 1))) (this ▸ hu (Nat.le_succ i))
          simp [*]
        _ = (∑ i ∈ Finset.range (k - 1), edist (f (u (i + 1))) (f (u i))) + edist (f' x) (f' (u (k - 1))) := by
          -- Handle empty sum if k = 0
          rcases k with - | k
          · simp [hk]
          · simp only [Finset.sum_range_succ, Nat.add_sub_cancel, hk]
            congr 1
            apply Finset.sum_congr rfl; intro i hi
            have hi_k : i + 1 < k + 1 := Nat.add_lt_add_right (Finset.mem_range.mp hi) 1
            -- use h_eq_k
            -- Step 1: Establish that f' and f agree at index i
            -- Since i < k (from hi) and k < k + 1, i satisfies the condition in h_eq_k.
            have h_i : f' (u i) = f (u i) := h_eq_k i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
            -- Step 2: Establish that f' and f agree at index i + 1
            -- This follows directly from the hypothesis hi_k : i + 1 < k + 1 and h_eq_k.
            have h_next : f' (u (i + 1)) = f (u (i + 1)) := h_eq_k (i + 1) hi_k
            -- Step 3: Rewrite the distance equality using the established pointwise equalities
            -- Once the arguments are identical, the edist values must be identical.
            rw [h_i, h_next]
        _ ≤ (∑ i ∈ Finset.range (k - 1), edist (f (u (i + 1))) (f (u i))) + (edist (f' x) (f x) + edist (f x) (f (u (k - 1)))) := by
          -- if k > 0
          apply add_le_add_right
          by_cases hk0 : k = 0
          · simp only [hk0, zero_tsub]; rw [hk0] at hk; rw [hk, edist_self, edist_self]; simp
          · have : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hk0) (Nat.zero_lt_one)
            rw [h_eq_k (k - 1) this]
            apply edist_triangle
        _ ≤ eVariationOn f s + edist (f' x) (f x) := by
          rw [add_comm (edist (f' x) (f x)), ← add_assoc]
          apply add_le_add_left
          by_cases hk0 : k = 0
          · simp only [hk0, zero_tsub, Finset.range_zero, Finset.sum_empty, zero_add]
            rw [hk0] at hk; rw [hk, edist_self]; simp
          · rw [← hk]
            have h_k : k = (k - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)).symm
            nth_rw 2 [h_k]
            rw [← Finset.sum_range_succ, ← h_k]
            exact eVariationOn.sum_le f k hu us
  · have h_un : u n < x := lt_of_le_of_ne (hs.2 (us n)) hx
    have h_in : ∀ i ≤ n, u i ∈ s \ {x} := fun i hi ↦ ⟨us i, ((hu hi).trans_lt h_un).ne⟩
    calc
      ∑ i ∈ Finset.range n, edist (f' (u (i + 1))) (f' (u i))
          = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
        apply Finset.sum_congr rfl; intro i hi; have hi' := Finset.mem_range.mp hi
        rw [← heq (h_in i hi'.le), ← heq (h_in (i + 1) hi')]
    _ ≤ eVariationOn f s := eVariationOn.sum_le f n hu us
    _ ≤ eVariationOn f s + edist (f' x) (f x) := le_self_add

private lemma eVariationOn_add_jump_endpoint {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    {f f' : α → E} {s : Set α} {x : α} (h_end : IsLeast s x ∨ IsGreatest s x)
    (heq : Set.EqOn f f' (s \ {x})) :
    eVariationOn f' s ≤ eVariationOn f s + edist (f' x) (f x) := by
  rcases h_end with h | h
  · -- IsLeast
    let s' := OrderDual.ofDual ⁻¹' s
    have h_gr : IsGreatest s' (OrderDual.toDual x) := ⟨h.1, fun y hy ↦ h.2 hy⟩
    have h_eq_d : Set.EqOn (f ∘ OrderDual.ofDual) (f' ∘ OrderDual.ofDual) (s' \ {OrderDual.toDual x}) := fun y hy ↦ heq hy
    rw [← eVariationOn.comp_ofDual f s, ← eVariationOn.comp_ofDual f' s]
    exact eVariationOn_add_jump_greatest h_gr h_eq_d
  · -- IsGreatest
    exact eVariationOn_add_jump_greatest h heq

@[blueprint
  "varphi-deriv-tv"
  (title := "$\\varphi'$ total variation")
  (statement := /-- The function $(\varphi_\nu^\pm)'$ has finite total variation. -/)
  (proof := /-- Since $(\varphi_\nu^\pm)'$ is $C^1$ on $[-1, 0]$ and on $[0, 1]$, the $L^1$ norm of $(\varphi_\nu^\pm)''$ on each of these intervals is finite, and so $(\varphi_\nu^\pm)'$ has finite total variation on each of them. As $(\varphi_\nu^\pm)'$ has right and left limits at $-1$, $0$ and $1$, the jumps at those points are finite, and so their contribution to $\|(\varphi_\nu^\pm)'\|_{\mathrm{TV}}$ is finite.
/
-/)
  (latexEnv := "lemma")
  (discussion := 1229)]
theorem varphi_deriv_tv (ν ε : ℝ) (hlam : ν ≠ 0) : BoundedVariationOn (deriv (ϕ_pm ν ε)) Set.univ := by
  -- Abbreviate the derivative function.
  set g := deriv (ϕ_pm ν ε)
  -- Step 1: The derivative is C¹ on [-1,0] because ϕ is C² there (ϕ_c2_left).
  -- From ContDiffOn ℝ 2 on [-1,0], we get ContDiffOn ℝ 1 on the derivative.
  -- Since [-1,0] is compact and convex, ContDiffOn ℝ 1 → LipschitzOnWith (via
  --   ContDiffOn.exists_lipschitzOnWith, which requires convexity + compactness).
  -- LipschitzOnWith → LocallyBoundedVariationOn → BoundedVariationOn on Icc.
  have hBV_left : BoundedVariationOn g (Set.Icc (-1 : ℝ) 0) := by
    have h_c2 : ContDiffOn ℝ 2 (ϕ_pm ν ε) (Set.Icc (-1) 0) := ϕ_c2_left ν ε hlam
    -- Work with the within-derivative on [-1,0], which is what ContDiffOn sees.
    set dw := derivWithin (ϕ_pm ν ε) (Set.Icc (-1 : ℝ) 0) with hdw_def
    -- A: dw is C¹ on [-1,0].
    -- ContDiffOn.derivWithin : ContDiffOn ℝ n f s → UniqueDiffOn ℝ s → m+1 ≤ n
    --   → ContDiffOn ℝ m (derivWithin f s) s
    -- Apply with n=2, m=1 (so 1+1=2≤2), using uniqueDiffOn_Icc (already in the file at L4037).
    have h_dw_c1 : ContDiffOn ℝ 1 dw (Set.Icc (-1 : ℝ) 0) :=
      h_c2.derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
    -- B: C¹ on convex compact → LipschitzOnWith.
    -- ContDiffOn.exists_lipschitzOnWith (n≠0, convex, compact) → ∃ K, LipschitzOnWith K dw s.
    obtain ⟨K, hK⟩ := h_dw_c1.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
    -- C: Lipschitz → locally BV on Icc ⊆ ℝ.
    -- LipschitzOnWith.locallyBoundedVariationOn :
    --   LipschitzOnWith C (f : ℝ → E) s → LocallyBoundedVariationOn f s
    -- D: Locally BV at endpoints (-1, 0 ∈ Icc -1 0) → BV on Icc.
    -- LocallyBoundedVariationOn f s = ∀ a b ∈ s, BoundedVariationOn f (s ∩ Icc a b).
    -- Apply at a=-1, b=0; then strip the self-intersection by .mono inter_subset_left.
    have hBV_dw : BoundedVariationOn dw (Set.Icc (-1 : ℝ) 0) := by
      simpa using hK.locallyBoundedVariationOn (-1) 0 (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))

    -- Relate g and dw on Ioo (-1) 0.
    have h_eq_ioo : Set.EqOn g dw (Set.Ioo (-1 : ℝ) 0) := by
      intro x hx
      simp only [g, hdw_def]
      have h_diff : DifferentiableAt ℝ (ϕ_pm ν ε) x :=
        (ϕ_c2_left ν ε hlam).differentiableOn (by norm_num) x (Set.Ioo_subset_Icc_self hx)
        |>.differentiableAt (Icc_mem_nhds hx.1 hx.2)
      exact h_diff.derivWithin (uniqueDiffOn_Icc (by norm_num) x (Set.Ioo_subset_Icc_self hx)) |>.symm

    -- Split interval at -1/2 to isolate endpoints.
    have h_split : eVariationOn g (Set.Icc (-1) 0) =
        eVariationOn g (Set.Icc (-1) (-1/2)) + eVariationOn g (Set.Icc (-1/2) 0) := by
      have := eVariationOn.Icc_add_Icc g (by norm_num : (-1 : ℝ) ≤ -1/2) (by norm_num : (-1/2 : ℝ) ≤ 0) (Set.mem_univ (-1/2 : ℝ))
      simp only [Set.univ_inter] at this
      exact this.symm

    -- Left half BV: Handle jump at -1.
    have hBV_L : BoundedVariationOn g (Set.Icc (-1) (-1/2)) := by
      have h_eq : Set.EqOn dw g (Set.Icc (-1 : ℝ) (-1 / 2) \ {-1}) := by
        intro x hx
        have : x ∈ Set.Ioo (-1) 0 := ⟨hx.1.1.lt_of_ne (Ne.symm hx.2), hx.1.2.trans_lt (by norm_num)⟩
        exact (h_eq_ioo this).symm
      have h_bound := eVariationOn_add_jump_endpoint (Or.inl (isLeast_Icc (by norm_num))) h_eq
      apply ne_top_of_le_ne_top _ h_bound
      apply ENNReal.add_ne_top.mpr
      exact ⟨hBV_dw.mono (Set.Icc_subset_Icc (le_refl _) (by norm_num)), edist_lt_top _ _ |>.ne⟩

    -- Right half BV: Handle jump at 0.
    have hBV_R : BoundedVariationOn g (Set.Icc (-1/2) 0) := by
      have h_eq : Set.EqOn dw g (Set.Icc (-1 / 2) 0 \ {0}) := by
        intro x hx
        have : x ∈ Set.Ioo (-1) 0 := ⟨(by norm_num : (-1 : ℝ) < -1/2).trans_le hx.1.1, hx.1.2.lt_of_ne hx.2⟩
        exact (h_eq_ioo this).symm
      have h_bound := eVariationOn_add_jump_endpoint (Or.inr (isGreatest_Icc (by norm_num))) h_eq
      apply ne_top_of_le_ne_top _ h_bound
      apply ENNReal.add_ne_top.mpr
      exact ⟨hBV_dw.mono (Set.Icc_subset_Icc (by norm_num) (le_refl _)), edist_lt_top _ _ |>.ne⟩

    rw [BoundedVariationOn, h_split]
    exact ENNReal.add_ne_top.mpr ⟨hBV_L, hBV_R⟩


  -- Step 2: Mirror of Step 1 using ϕ_c2_right instead of ϕ_c2_left.
  have hBV_right : BoundedVariationOn g (Set.Icc (0 : ℝ) 1) := by
    have h_c2 : ContDiffOn ℝ 2 (ϕ_pm ν ε) (Set.Icc 0 1) := ϕ_c2_right ν ε hlam
    set dw := derivWithin (ϕ_pm ν ε) (Set.Icc (0 : ℝ) 1) with hdw_def
    have h_dw_c1 : ContDiffOn ℝ 1 dw (Set.Icc (0 : ℝ) 1) :=
      h_c2.derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
    obtain ⟨K, hK⟩ := h_dw_c1.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
    have hBV_dw : BoundedVariationOn dw (Set.Icc (0 : ℝ) 1) := by
      simpa using hK.locallyBoundedVariationOn 0 1 (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))

    -- Relate g and dw on Ioo 0 1.
    have h_eq_ioo : Set.EqOn g dw (Set.Ioo (0 : ℝ) 1) := by
      intro x hx
      simp only [g, hdw_def]
      have h_diff : DifferentiableAt ℝ (ϕ_pm ν ε) x :=
        (ϕ_c2_right ν ε hlam).differentiableOn (by norm_num) x (Set.Ioo_subset_Icc_self hx)
        |>.differentiableAt (Icc_mem_nhds hx.1 hx.2)
      exact h_diff.derivWithin (uniqueDiffOn_Icc (by norm_num) x (Set.Ioo_subset_Icc_self hx)) |>.symm

    -- Split interval at 1/2 to isolate endpoints.
    have h_split : eVariationOn g (Set.Icc 0 1) =
        eVariationOn g (Set.Icc 0 (1/2)) + eVariationOn g (Set.Icc (1/2) 1) := by
      have := eVariationOn.Icc_add_Icc g (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) (Set.mem_univ (1/2 : ℝ))
      simp only [Set.univ_inter] at this
      exact this.symm

    -- Left half BV: Handle jump at 0.
    have hBV_L : BoundedVariationOn g (Set.Icc 0 (1/2)) := by
      have h_eq : Set.EqOn dw g (Set.Icc 0 (1/2) \ {0}) := by
        intro x hx
        have : x ∈ Set.Ioo 0 1 := ⟨hx.1.1.lt_of_ne (Ne.symm hx.2), hx.1.2.trans_lt (by norm_num)⟩
        exact (h_eq_ioo this).symm
      have h_bound := eVariationOn_add_jump_endpoint (Or.inl (isLeast_Icc (by norm_num))) h_eq
      apply ne_top_of_le_ne_top _ h_bound
      apply ENNReal.add_ne_top.mpr
      exact ⟨hBV_dw.mono (Set.Icc_subset_Icc (le_refl _) (by norm_num)), edist_lt_top _ _ |>.ne⟩

    -- Right half BV: Handle jump at 1.
    have hBV_R : BoundedVariationOn g (Set.Icc (1/2) 1) := by
      have h_eq : Set.EqOn dw g (Set.Icc (1 / 2) 1 \ {1}) := by
        intro x hx
        have : x ∈ Set.Ioo 0 1 := ⟨(by norm_num : (0 : ℝ) < 1/2).trans_le hx.1.1, hx.1.2.lt_of_ne hx.2⟩
        exact (h_eq_ioo this).symm
      have h_bound := eVariationOn_add_jump_endpoint (Or.inr (isGreatest_Icc (by norm_num))) h_eq
      apply ne_top_of_le_ne_top _ h_bound
      apply ENNReal.add_ne_top.mpr
      exact ⟨hBV_dw.mono (Set.Icc_subset_Icc (by norm_num) (le_refl _)), edist_lt_top _ _ |>.ne⟩

    rw [BoundedVariationOn, h_split]
    exact ENNReal.add_ne_top.mpr ⟨hBV_L, hBV_R⟩

  -- Step 3: Combine BV on [-1,0] and [0,1] to get BV on [-1,1] via
  --   eVariationOn.Icc_add_Icc, which states:
  --   eVariationOn f (s ∩ Icc a b) + eVariationOn f (s ∩ Icc b c)
  --     = eVariationOn f (s ∩ Icc a c)   (for a ≤ b ≤ c, b ∈ s)
  --   With s = univ (i.e., Icc), this gives BV on Icc (-1) 1.
  have hBV_Icc : BoundedVariationOn g (Set.Icc (-1 : ℝ) 1) := by
    -- BoundedVariationOn is eVariationOn ≠ ⊤.
    -- eVariationOn g (Icc -1 1)
    --   = eVariationOn g (Icc -1 0) + eVariationOn g (Icc 0 1)
    --   (by eVariationOn.Icc_add_Icc with b = 0 ∈ s = univ)
    -- Both summands are finite by hBV_left, hBV_right.
    -- Concretely we can rewrite with Icc_add_Icc and use ENNReal.add_ne_top.
    simp only [BoundedVariationOn] at hBV_left hBV_right ⊢
    have h_split :
        eVariationOn g (Set.Icc (-1 : ℝ) 0) + eVariationOn g (Set.Icc (0 : ℝ) 1) =
        eVariationOn g (Set.Icc (-1 : ℝ) 1) := by
      -- Use eVariationOn.Icc_add_Icc:
      -- eVariationOn f (s ∩ Icc a b) + eVariationOn f (s ∩ Icc b c)
      --   = eVariationOn f (s ∩ Icc a c) (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s)
      -- Here s = univ, so s ∩ Icc x y = Icc x y.
      have key := eVariationOn.Icc_add_Icc g (a := (-1 : ℝ)) (b := 0) (c := 1)
        (by norm_num) (by norm_num) (Set.mem_univ _)
      simp only [Set.univ_inter] at key
      exact key
    rw [← h_split]
    exact ENNReal.add_ne_top.mpr ⟨hBV_left, hBV_right⟩
  -- Step 4: Lift BV on [-1,1] to BV on Set.univ.
  -- We split ℝ = Iic(-1) ∪ Icc(-1,1) ∪ Ici(1) using eVariationOn.union twice.
  -- The two outer pieces contribute finite variation (only one boundary jump each
  -- since g = 0 on Iio(-1) and Ioi(1)), so the total is finite.
  simp only [BoundedVariationOn] at hBV_Icc ⊢
  -- Splitting step 1: univ = Iic(-1) ∪ Ici(-1)
  -- (Set.Iic_union_Ici : Iic a ∪ Ici a = univ)
  -- isGreatest_Iic : IsGreatest (Iic a) a
  -- isLeast_Ici    : IsLeast (Ici a) a
  have h_split1 : eVariationOn g Set.univ =
      eVariationOn g (Set.Iic (-1 : ℝ)) + eVariationOn g (Set.Ici (-1 : ℝ)) := by
    conv_lhs => rw [← Set.Iic_union_Ici (a := (-1 : ℝ))]
    exact eVariationOn.union g isGreatest_Iic isLeast_Ici
  -- Splitting step 2: Ici(-1) = Icc(-1,1) ∪ Ici(1)
  -- (Set.Icc_union_Ici_eq_Ici : Icc a b ∪ Ici b = Ici a when a ≤ b)
  -- isGreatest_Icc (h : a ≤ b) : IsGreatest (Icc a b) b
  have h_split2 : eVariationOn g (Set.Ici (-1 : ℝ)) =
      eVariationOn g (Set.Icc (-1 : ℝ) 1) + eVariationOn g (Set.Ici (1 : ℝ)) := by
    conv_lhs => rw [← Set.Icc_union_Ici_eq_Ici (by norm_num : (-1 : ℝ) ≤ 1)]
    exact eVariationOn.union g (isGreatest_Icc (by norm_num)) isLeast_Ici
  -- Left outer piece: g = 0 on Iio(-1) (from hf_deriv in varphi_ftc_out),
  -- so any monotone sequence in Iic(-1) maps g to {0, g(-1)}.  The variation
  -- is at most edist(g(-1)) 0, which is < ⊤ by ENNReal.edist_lt_top.
  -- Proof: apply iSup_le; rintro ⟨n, u, hu, hu_mem⟩; bound each edist term.
  have hIic := ϕ_pm_deriv_Iic_finite ν ε
  have hIci := ϕ_pm_deriv_Ici_finite ν ε
  -- Combine all three finite pieces.
  rw [h_split1, h_split2]
  exact ENNReal.add_ne_top.mpr
    ⟨hIic, ENNReal.add_ne_top.mpr ⟨hBV_Icc, hIci⟩⟩

@[blueprint
  "varphi-fourier-decay"
  (title := "$\\varphi$ Fourier decay")
  (statement := /-- For $|x| \to \infty$, $\widehat{\varphi_\nu^\pm}(x) = O(1/x^2)$. -/)
  (proof := /-- For $f$ absolutely continuous with $f, f' \in L^1(\mathbb{R})$, integration by parts gives us that $\hat{f}(x) = \widehat{f'}(x)/(2\pi i x)$. If $f' \in L^1(\mathbb{R})$ with $\|f'\|_{\mathrm{TV}} < \infty$, then, again by integration by parts, $|\widehat{f'}(x)| \leq |f'|_{\mathrm{TV}}/(2\pi x)$. We are done by the preceding lemmas. -/)
  (latexEnv := "corollary")
  (discussion := 1230)]
theorem varphi_fourier_decay (ν ε : ℝ) (hlam : ν ≠ 0) : IsBigO Filter.atTop (fun x:ℝ ↦ (𝓕 (ϕ_pm ν ε) x).re) (fun x:ℝ ↦ 1 / x ^ 2)  := by
  let C := (eVariationOn (deriv (ϕ_pm ν ε)) Set.univ).toReal / (2 * π) ^ 2
  have h_bound : ∀ x > 0, ‖𝓕 (ϕ_pm ν ε) x‖ ≤ C * ‖1 / x ^ 2‖ := by
    intro x hx
    have h_pd := prelim_decay_3 (ϕ_pm ν ε) (varphi_integ ν ε hlam) (varphi_abs ν ε hlam) (varphi_deriv_tv ν ε hlam) x (ne_of_gt hx)
    rw [mul_pow, ← div_div, norm_of_nonneg hx.le] at h_pd
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
    exact h_pd
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have h_re_le_norm : ‖(𝓕 (ϕ_pm ν ε) x).re‖ ≤ ‖𝓕 (ϕ_pm ν ε) x‖ := Complex.abs_re_le_norm _
  exact h_re_le_norm.trans (h_bound x hx)

@[blueprint
  "varphi-fourier-minus-error"
  (title := "$L^1$ error bound for Fourier transform of $\\varphi^-$")
  (statement := /--
\[
\int_{-\infty}^{\infty} (I_\nu(x) - \hat{\varphi_\nu^-}(x))\, dx = \frac{1}{\nu} - \frac{1}{e^\nu - 1}.
\]
  -/)
  (proof := /--
  We know that $\varphi_\nu^\pm$ is continuous and in $L^1(\mathbb{R})$; by Corollary \ref{varphi-fourier-decay}, $\widehat{\varphi_\nu^\pm}$ is in $L^1(\mathbb{R})$. Hence, Fourier inversion holds everywhere, and in particular for $t = 0$:
\[
\varphi_\nu^\pm(0) = \int_{-\infty}^{\infty} \widehat{\varphi_\nu^\pm}(x)\, dx.
\]
By definition, $\varphi_\nu^\pm(0) = \Phi_\nu^{\pm,\circ}(0)$, and, by definition, $\Phi_\nu^{-,\circ}(0) = \frac{1}{e^\nu - 1}$ and $\Phi_\nu^{+,\circ}(0) = \frac{1}{1 - e^{-\nu}}$. Thus,
\[
\int_{-\infty}^{\infty} (I_\nu(x) - \widehat{\varphi_\nu^-}(x))\, dx = \frac{1}{\nu} - \frac{1}{e^\nu - 1},
\]
\[
\int_{-\infty}^{\infty} (\widehat{\varphi_\nu^+}(x) - I_\nu(x))\, dx = \frac{1}{1 - e^{-\nu}} - \frac{1}{\nu},
\]
since $\int_{-\infty}^{\infty} I_\nu(x)\, dx = 1/\nu$. We are done by Corollary \ref{Inu_bounds}.
-/)
  (latexEnv := "proposition")
  (discussion := 1231)]
theorem varphi_fourier_minus_error (ν : ℝ) (hν : ν > 0) :
    ∫ x in Set.univ, (Inu ν x - (𝓕 (ϕ_pm ν (-1)) x).re) = 1 / ν - 1 / (Real.exp ν - 1) := by
    sorry

@[blueprint
  "varphi-fourier-plus-error"
  (title := "$L^1$ error bound for Fourier transform of $\\varphi^+$")
  (statement := /--
\[
\int_{-\infty}^{\infty} (\hat{\varphi_\nu^+}(x) - I_\nu(x))\, dx = \frac{1}{1 - e^{-\nu}} - \frac{1}{\nu}.
\]
  -/)
  (proof := /-- See previous. -/)
  (latexEnv := "proposition")
  (discussion := 1232)]
theorem varphi_fourier_plus_error (ν : ℝ) (hν : ν > 0) :
    ∫ x in Set.univ, ((𝓕 (ϕ_pm ν 1) x).re - Inu ν x) = 1 / (1 - Real.exp (-ν)) - 1 / ν := by
    sorry

@[blueprint
  "CH2-lemma-4-2a"
  (title := "CH2 Lemma 4.2(a)")
  (statement := /--
If $|\Im z| \leq \frac{\pi}{4}$, then $|(z \coth z)'| < 1$.  -/)
  (proof := /-- Since $z\coth(z)$ is regular at $0$ and an even function, we see that $f(z) := (z \coth z)'$ and $f(z)/z$ are regular at $0$, and hence analytic on the strip $|\Im z| \leq \frac{\pi}{2}$. We see from $f(z) = \coth z - z\operatorname{csch}^2 z$ that $f(z)$ has at most exponential growth as $\Re z \to \pm\infty$ within the strip. Hence, by Phragm\'{e}n--Lindel\"{o}f, it is enough to verify the inequalities $|f(z)/z| \leq 1$ for $\Im z = \pm\frac{\pi}{2}$ and $|f(z)| \leq 1$ for $\Im z = \pm\frac{\pi}{4}$; by complex conjugation, it suffices to check them for $\Im z = \frac{\pi}{2}$ and $\Im z = \frac{\pi}{4}$.

By the above, $f(z) = \frac{(\sinh 2z)/2 - z}{\sinh^2 z}$. Now, for $z = x + i\frac{\pi}{4}$ with $x \in \mathbb{R}$, we have $\sinh 2z = i\cosh 2x$ and $\sinh^2 z = -\frac{1}{2} + \frac{i}{2}\sinh 2x$, and so $|f(z)|^2 = \frac{(\cosh 2x - \pi/2)^2 + 4x^2}{1 + \sinh^2 2x}$. By $1 + \sinh^2 2x = \cosh^2 2x$,
\[
|f(z)|^2 = 1 - \frac{\pi \cosh 2x - \pi^2/4 - 4x^2}{\cosh^2 2x}.
\]
Since $\cosh 2x = 1 + 2\sinh^2 x \geq 1 + 2x^2$, $\pi > \frac{\pi^2}{4}$ and $2\pi > 4$, the numerator here is positive. We conclude that $|f(z)|^2 < 1$ for $z = x + i\frac{\pi}{4}$, as was desired.

For $z = x + i\frac{\pi}{2}$ with $x \in \mathbb{R}$, we have $\coth z = \tanh x$ and $\operatorname{csch}^2 z = -\operatorname{sech}^2 x$. Then $|f(z)|^2 = (\tanh x + x\operatorname{sech}^2 x)^2 + \left(\frac{\pi}{2}\operatorname{sech}^2 x\right)^2$. Since $\operatorname{sech}^2 x - 1 = -\tanh^2 x$, this is equal to
\[
\tanh^2 x \operatorname{sech} x\!\left(\cosh x + 2x\operatorname{csch} x - |z|^2(\operatorname{sech} x + \cosh x)\right) + |z|^2.
\]
Since $|z|^2 \geq \frac{\pi^2}{4} > 2$, it suffices to show that $2x\operatorname{csch} x - 2\operatorname{sech} x - \cosh x \leq 0$ for all $x \in \mathbb{R}$; by parity, it is enough to check all $x \geq 0$. The statement is then equivalent to $g(x) = 2x - 2\tanh x - \sinh x \cosh x \leq 0$, since $\sinh x \geq 0$. That follows from $g'(x) = 2\tanh^2 x - \cosh^2 x - \sinh^2 x = -2\sinh^2 x \tanh^2 x - 1 \leq 0$ (by $1 - \cosh^2 x = -\sinh^2 x$) and $g(0) = 0$.
-/)
  (latexEnv := "sublemma")
  (discussion := 1233)]
theorem CH2_lemma_4_2a (z : ℂ) (hz : |z.im| ≤ π / 4) : ‖deriv (fun z:ℂ ↦ z * coth z) z‖ < 1 := by
    sorry

@[blueprint
  "CH2-lemma-4-2b"
  (title := "CH2 Lemma 4.2(b)")
  (statement := /--
If $|\Im z| \leq \frac{\pi}{2}$, then $|(z \coth z)'| \leq |z|$. -/)
  (proof := /-- See previous. -/)
  (latexEnv := "sublemma")
  (discussion := 1234)]
theorem CH2_lemma_4_2b (z : ℂ) (hz : |z.im| ≤ π / 2) : ‖deriv (fun z:ℂ ↦ z * coth z) z‖ ≤ ‖z‖ := by
    sorry



/-
\begin{lemma}
Let $\Phi^{\pm,\circ}_\nu(z)$ and $\Phi^{\pm,\star}_\nu(z)$ be as in \eqref{eq:defPhi} for $\nu > 0$. Then:
\begin{itemize}
    \item $\Phi^{\pm,\circ}_\nu(z)$ is a meromorphic function whose poles, all of them simple, are at $n - \frac{i\nu}{2\pi}$, $n \in \mathbb{Z}$; the residue at every pole is $\frac{i}{2\pi}$. Moreover, $\Phi^{\pm,\circ}_\nu(z) = \overline{\Phi^{\pm,\circ}_\nu(-\bar{z})}$.
    \item $\Phi^{\pm,\star}_\nu(z)$ is a meromorphic function whose poles, all of them simple, are at $n - \frac{i\nu}{2\pi}$, $n \in \mathbb{Z} \setminus \{0\}$; the residue at $n - \frac{i\nu}{2\pi}$ is $-\frac{in}{2\pi}$. Moreover, $\Phi^{\pm,\star}_\nu(z) = -\overline{\Phi^{\pm,\star}_\nu(-\bar{z})}$.
\end{itemize}
On every region $\{z : \Im z \geq c\}$, $c > -\frac{\nu}{2\pi}$, or $\{z : \Im z \leq c\}$, $c < -\frac{\nu}{2\pi}$, the function $\Phi^{\pm,\circ}_\nu(z)$ is bounded and $\Phi^{\pm,\star}_\nu(z) = O(|z| + 1)$. Moreover, these bounds hold uniformly for all $\nu$ in an interval $[\nu_0, \nu_1]$, with conditions $c > -\frac{\nu_0}{2\pi}$, $c < -\frac{\nu_1}{2\pi}$, respectively.

We have $\Phi^{\sigma,\star}_\nu(0) = 0$. For $z$ with $0 \leq \Re z \leq \frac{1}{4}$, and for either sign $\sigma = \pm$,
\[
\left|(\Phi^{\pm,\star}_\nu)'(z)\right| \leq 1, \quad |\Phi^{\sigma,\star}_\nu(\pm z)| \leq |z|, \quad |(\Phi^{\sigma,\circ}_\nu \pm \Phi^{\sigma,\star}_\nu)(\pm 1 \mp z)| \leq |z|.
\]
Moreover, for $z$ purely imaginary, $(\Phi^{\sigma,\star}_\nu)'(\pm z)$, which is purely real, is of constant sign.

Note that $\Phi^{\sigma,\circ}_\nu(z) \pm \Phi^{\sigma,\star}_\nu(z)$ is regular at $\pm 1 - \frac{i\nu}{2\pi}$, since the residues cancel out.

Our convention is that all signs denoted by $\pm$ in the same equation are the same, $\mp$ is the opposite sign, and $\sigma$ denotes a sign that may or may not be the same.
\end{lemma}

\begin{proof}
The statements on poles and residues follow directly from \eqref{eq:defPhi}; so do the statements on $\overline{\Phi^{\pm,\circ}_\nu(z)}$ and $\overline{\Phi^{\pm,\star}_\nu(z)}$. The statements on the boundedness of $\Phi^{\sigma,\circ}_\nu(z)$ and the growth of $\Phi^{\sigma,\star}_\nu(z)$ follow from \eqref{eq:defPhi} and the fact that $\coth(w)$ is bounded on $\Re w \geq c$ for $c > 0$ arbitrary and on $\Re w \leq c$ for $c < 0$ arbitrary. Since $|\Phi^{\sigma,\star}_\nu(-z)| = |\Phi^{\sigma,\star}_\nu(z)|$ and $|(\Phi^{\sigma,\circ}_\nu - \Phi^{\sigma,\star}_\nu)(-1 + z)| = |(\Phi^{\sigma,\circ}_\nu + \Phi^{\sigma,\star}_\nu)(1 - z)|$, it is left to check that $|\Phi^{\sigma,\star}_\nu(z)| \leq |z|$ and $|(\Phi^{\sigma,\circ}_\nu + \Phi^{\sigma,\star}_\nu)(1 - z)| \leq |z|$.

By \eqref{eq:defPhi}, $\Phi^{\pm,\star}_\nu(0) = 0$ and $(\Phi^{\pm,\star}_\nu)'(z) = -\frac{d}{dw}\!\left(\frac{w}{2}\coth\frac{w}{2}\right) \mp \frac{1}{2}$ at $w = -2\pi iz + \nu$. Hence, for $0 \leq \Re z \leq \frac{1}{4}$, by Lemma~4.2, $|(\Phi^{\pm,\star}_\nu)'(z)| \leq 1$, and so $|(\Phi^{\pm,\star}_\nu)(z)| \leq |z|$; moreover, $(\Phi^{\pm,\star}_\nu)'(z)$ does not change sign for $z$ purely imaginary, as $\tanh w$ is real, and the term $\mp\frac{1}{2}$ always dominates. By \eqref{eq:comb}, $(\Phi^{\pm,\circ}_\nu + \Phi^{\pm,\star}_\nu)(1) = 0$ and $(\Phi^{\pm,\circ}_\nu + \Phi^{\pm,\star}_\nu)'(z) = -\frac{d}{dw}\!\left(\frac{w}{2}\coth\frac{w}{2}\right) \mp \frac{1}{2}$ at $w = -2\pi i(z-1) + \nu$. Hence, again by Lemma~4.2, for $0 \leq \Re z \leq \frac{1}{4}$, $|(\Phi^{\sigma,\circ}_\nu + \Phi^{\sigma,\star}_\nu)(1 - z)| \leq |z|$.
\end{proof}

\begin{lemma}
For $z \in \mathbb{C}$, $\lambda \in \mathbb{R} \setminus \{0\}$, define
\[
\Phi^\pm_\lambda(z) = \Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z) + \operatorname{sgn}(\lambda)\operatorname{sgn}(\Re z)\,\Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z),
\]
where $\Phi^{\pm,\circ}_{|\lambda|}$, $\Phi^{\pm,\star}_{|\lambda|}$ are as in \eqref{eq:defPhi}, and $\operatorname{sgn}(0) = 0$. Let $T > 0$, and let $z(s) = \frac{s-1}{iT}$.

Then, for $s \in \mathbb{C}$,
\begin{equation}
\Phi^\pm_\lambda(z(s)) = \overline{\Phi^\pm_\lambda(z(\bar{s}))}. \label{eq:conjsym}
\end{equation}
Let $\sigma \in \mathbb{R} \setminus \{1\}$. Let $\lambda = \frac{2\pi}{T}(\sigma - 1)$ and write $\theta(s) = 1 - \frac{s - \sigma}{iT}$. If $\Im s > 0$,
\begin{equation}
\Phi^\pm_\lambda(z(s)) = i\operatorname{sgn}(\lambda)\left(-\frac{\theta(s)}{2}\cot(\pi\theta(s)) + \frac{\theta(1+iT)}{2}\cot(\pi\theta(1+iT)) \pm \frac{1 - z(s)}{2}\right). \label{eq:Phieval}
\end{equation}
\end{lemma}

\begin{proof}
When we evaluate $\Phi^\pm_\lambda$ at $z(s)$, we evaluate $\Phi^{\pm,\circ}_{|\lambda|}$ and $\Phi^{\pm,\star}_{|\lambda|}$ at $\operatorname{sgn}(\lambda)z(s)$, and so the variable $w$ in \eqref{eq:defPhi} is given by
\begin{equation}
w = -2\pi i\operatorname{sgn}(\lambda)\frac{s-1}{iT} + |\lambda| = \operatorname{sgn}(\lambda)\!\left(-\frac{2\pi}{T}(s-1) + \lambda\right) = -\operatorname{sgn}(\lambda)\frac{2\pi}{T}(s - \sigma). \label{eq:wform}
\end{equation}
In particular, when we conjugate $s$, we conjugate $w$. We thus see from \eqref{eq:defPhi} that
\[
\Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) = \overline{\Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z(\bar{s}))}, \quad \Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) = -\overline{\Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z(\bar{s}))},
\]
and thus, since $\operatorname{sgn}(\Re z(s)) = -\operatorname{sgn}(\Re z(\bar{s}))$, \eqref{eq:conjsym} holds.

If $\Im s > 0$,
\begin{equation}
\Phi^\pm_\lambda(z(s)) = \Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) + \operatorname{sgn}(\lambda)\Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) \label{eq:Phipos}
\end{equation}
because $\Im s > 0$ implies $\Re z(s) > 0$. Since $\coth$ is an odd function, \eqref{eq:defPhi} and \eqref{eq:wform} give us
\begin{align*}
\Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) &= \frac{1}{2}\!\left(-\operatorname{sgn}(\lambda)\coth\frac{\pi(s-\sigma)}{T} \pm 1\right), \\
\Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) &= \frac{i}{2\pi}\!\left(\frac{\lambda}{2}\coth\frac{\lambda}{2} - \frac{\pi(s-\sigma)}{T}\coth\frac{\pi(s-\sigma)}{T} \pm \operatorname{sgn}(\lambda)\pi i z(s)\right).
\end{align*}
Thus, for $\Im s > 0$, \eqref{eq:Phipos} gives us
\[
\Phi^\pm_\lambda(z(s)) = -\operatorname{sgn}(\lambda)\frac{i(s-\sigma)}{2T} + \frac{1}{2}\!\left(\coth\frac{\pi(s-\sigma)}{T} - \frac{i\lambda}{4\pi}\coth\frac{\lambda}{2}\right) \pm \frac{1 - z(s)}{2}.
\]
So, by $\coth u = -i\cot(u/i)$, $\coth(-u) = -\coth u$, $\cot(\pi - u) = -\cot u$ and $\theta(s) = 1 - \frac{s - \sigma}{iT}$,
\[
\Phi^\pm_\lambda(z(s)) = i\operatorname{sgn}(\lambda)\!\left(-\frac{\theta(s)}{2}\cot(\pi\theta(s)) - \frac{i\lambda}{4\pi}\cot\frac{\lambda}{2i}\right) \pm \frac{1 - z(s)}{2}.
\]
Since $\theta(1 + iT) = \frac{\sigma - 1}{iT} = \frac{\lambda}{2\pi i}$, we have $\cot\frac{\lambda}{2i} = \cot(\pi\theta(1 + iT))$.
\end{proof}
-/





blueprint_comment /--
\subsection{Contour shifting}\label{ch2-contour-sec}

TODO: incorporate material from \cite[Section 5]{CH2}.
-/

blueprint_comment /--
\subsection{The main theorem}\label{ch2-main-thm-sec}

TODO: incorporate material from \cite[Section 6]{CH2}.
-/

blueprint_comment /--
\subsection{Applications to psi}\label{ch2-psi-sec}

TODO: incorporate material from \cite[Section 7]{CH2} onwards.
-/



@[blueprint
  "CH2-cor-1-2-a"
  (title := "Corollary 1.2, part a")
  (statement := /--
  Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$|\psi(x) - x \cdot \frac{\pi}{T} \coth(\frac{\pi}{T})| \leq \pi T^{-1} \cdot x + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \sqrt{x},$$
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_2_a {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    |ψ x - x * π * T⁻¹ * (coth (π * T⁻¹)).re| ≤
      π * T⁻¹ * x + ((1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π))) * Real.sqrt x := by sorry

@[blueprint
  "CH2-cor-1-2-b"
  (title := "Corollary 1.2, part b")
  (statement := /--
  Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$\sum_{n \leq x} \frac{\Lambda(n)}{n} \leq \pi \sqrt{T}^{-1} + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \frac{1}{x},$$
where $\gamma = 0.577215...$ is Euler’s constant.
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_2_b {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n ≤
      π * Real.sqrt T⁻¹ + (1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π)) / x := by sorry

@[blueprint
  "CH2-cor-1-3-a"
  (title := "Corollary 1.3, part a")
  (statement := /--
For $x \geq 1$,
$$|\psi(x) - x| \leq \pi \cdot 3 \cdot 10^{-12} \cdot x + 113.67 \sqrt{x},$$
where $\psi(x)$ is the Chebyshev function.
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_3_a (x : ℝ) (hx : 1 ≤ x) :
    |ψ x - x| ≤ π * 3 * 10 ^ (-12 : ℝ) * x + 113.67 * Real.sqrt x := by sorry

@[blueprint
  "CH2-cor-1-3-b"
  (title := "Corollary 1.3, part b")
  (statement := /--
For $x \geq 1$,
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x - \gamma + O^*(\pi \cdot \sqrt{3} \cdot 10^{-12} + 113.67 / x).$$
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_3_b (x : ℝ) (hx : 1 ≤ x) : ∃ E,
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n =
      log x - eulerMascheroniConstant + E ∧ |E| ≤ π * Real.sqrt 3 * 10 ^ (-12 : ℝ) + 113.67 / x := by sorry

end CH2
