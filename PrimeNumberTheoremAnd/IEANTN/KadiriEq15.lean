import Architect
import PrimeNumberTheoremAnd.IEANTN.KadiriEq15GammaFactor
import PrimeNumberTheoremAnd.IEANTN.KadiriEq15LaplaceStrip
import PrimeNumberTheoremAnd.Fourier
import PrimeNumberTheoremAnd.PerronFormula
import Mathlib.Analysis.Calculus.Deriv.Star

namespace Kadiri

open MeasureTheory Complex
open Filter
open scoped Topology

/-- Kadiri's `I_3(T)`: the gamma-factor piece of the truncated `σ = -a` contour integral. -/
@[blueprint
  "kadiri-thm-3-1-q1-I-3"
  (title := "Kadiri's $I_3(T)$: the gamma-factor piece")
  (statement := /-- Kadiri's $I_3(T)$ from \cite[p.~12]{Kadiri2005}: the gamma-factor
  piece of the functional-equation rewrite of the $\sigma = -a$ integral,
  $$ I_3(T) \;:=\; \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
                  \frac{1}{2}\Big\{
                    \frac{\Gamma'}{\Gamma}\!\Big(\frac{s}{2}\Big)
                  + \frac{\Gamma'}{\Gamma}\!\Big(\frac{1-s}{2}\Big)
                  \Big\}\, \Phi(-s)\, ds. $$
  Its $T \to \infty$ limit is given by \ref{kadiri-thm-3-1-q1-eq-15}: shifting the
  contour to the critical line $\Re s = 1/2$ picks up a $+\Phi(0)$ residue at $s = 0$
  (from the pole of $\Gamma'/\Gamma(s/2)$ at the origin), and the
  $\Gamma'/\Gamma$-symmetrization (\ref{kadiri-thm-3-1-q1-gamma-symmetrization}) on
  $\Re s = 1/2$ collapses the two gamma terms into $\Re[\Gamma'/\Gamma(s/2)]$. -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I_3 (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      ((1 / 2 : ℂ) *
        (digamma ((((-a : ℝ) : ℂ) + (t : ℂ) * I) / 2)
         + digamma ((1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) / 2))) *
        Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))

/-- The digamma function commutes with complex conjugation. Mathlib's junk-value
conventions make this unconditional: `Complex.Gamma_conj` holds at every point,
`deriv` returns `0` at non-differentiable points on both sides of the symmetry,
and `conj` fixes `0`. In the application below the argument `s / 2` has real
part `1 / 4`, away from the poles of `Γ` in any case. -/
private lemma digamma_conj (z : ℂ) :
    digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (digamma z) := by
  have hΓ : (starRingEnd ℂ) ∘ Gamma ∘ (starRingEnd ℂ) = Gamma := by
    funext w
    simp [Function.comp_apply, Gamma_conj]
  have hd : deriv Gamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv Gamma z) := by
    conv_lhs => rw [← hΓ, deriv_conj_conj]
    simp [Function.comp_apply]
  rw [digamma_def, logDeriv_apply, logDeriv_apply, hd, Gamma_conj, ← map_div₀]

@[blueprint
  "kadiri-thm-3-1-q1-gamma-symmetrization"
  (title := "$\\Gamma'/\\Gamma$ symmetrization on the critical line")
  (statement := /-- For every $s \in \mathbb{C}$ with $\Re s = 1/2$,
  $$ \frac{1}{2}\!\left\{
       \frac{\Gamma'}{\Gamma}\!\Big(\frac{s}{2}\Big)
     + \frac{\Gamma'}{\Gamma}\!\Big(\frac{1-s}{2}\Big)
       \right\}
     \;=\; \Re\!\left[\frac{\Gamma'}{\Gamma}\!\Big(\frac{s}{2}\Big)\right]. $$
  Used to identify the integrand of $I_3$ after shifting to the critical line
  (\cite[p.~13]{Kadiri2005}, displayed equation between (14) and (15)). -/)
  (proof := /-- On $\Re s = 1/2$, $1 - s = \bar s$, hence $(1 - s)/2 = \overline{s/2}$.
  Since $\Gamma'/\Gamma$ has real Taylor coefficients away from its poles, it commutes
  with complex conjugation: $\Gamma'/\Gamma((1-s)/2) = \overline{\Gamma'/\Gamma(s/2)}$.
  Then $\tfrac{1}{2}(z + \bar z) = \Re z$ with $z = \Gamma'/\Gamma(s/2)$. -/)
  (latexEnv := "sublemma")
  (discussion := 1544)]
theorem kadiri_thm_3_1_q1_gamma_symmetrization {s : ℂ} (_hs : s.re = 1 / 2) :
    (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) =
      ((digamma (s / 2)).re : ℂ) := by
  have h1s : 1 - s = (starRingEnd ℂ) s := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, _hs]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring
  have hconj : (1 - s) / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, map_ofNat, h1s]
  rw [hconj, digamma_conj, Complex.add_conj]
  push_cast
  ring

/-- The gamma factor times the transform plus `(∫ φ)/s` is bounded near `s = 0`. -/
lemma kadiri_gamma_laplace_pole_sub_isBigO_one {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun s : ℂ =>
      (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) *
        (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume) +
      (∫ y : ℝ, φ y ∂volume) / s)
      =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
  let G : ℂ → ℂ :=
    fun s => (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))
  let F : ℂ → ℂ := fun s => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume
  have hG : (fun s : ℂ => G s + s⁻¹) =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
    simpa [G] using kadiri_gamma_factor_add_inv_isBigO_one
  have hF : F =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
    have hderiv := kadiri_laplace_exp_hasDerivAt_zero hφ hb hφ_decay
    exact (hderiv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hprod :
      (fun s : ℂ => (G s + s⁻¹) * F s)
        =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by simpa using hG.mul hF
  have hquot :
      (fun s : ℂ => ((∫ y : ℝ, φ y ∂volume) - F s) / s)
        =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
    simpa [F] using kadiri_laplace_exp_integral_sub_div_isBigO_one hφ hb hφ_decay
  have hsum :
      (fun s : ℂ =>
        (G s + s⁻¹) * F s + ((∫ y : ℝ, φ y ∂volume) - F s) / s)
        =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) :=
    hprod.add hquot
  refine hsum.congr' ?_ .rfl
  filter_upwards with s
  dsimp [G, F]
  rw [div_eq_mul_inv]
  ring

/-- For `s ≠ 0` with `-2 < Re s`, the half-argument `s / 2` avoids the poles of `Γ'/Γ`. -/
private lemma kadiri_digamma_half_arg_ne_neg_nat {s : ℂ} (hs : s ≠ 0)
    (hre : -2 < s.re) : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  intro n hn
  have hs_eq : s = -((2 * n : ℕ) : ℂ) := by
    calc
      s = (2 : ℂ) * (s / 2) := by ring
      _ = (2 : ℂ) * (-(n : ℂ)) := by rw [hn]
      _ = -((2 * n : ℕ) : ℂ) := by norm_num [Nat.cast_mul]
  cases n with
  | zero => exact hs (by simpa using hs_eq)
  | succ n =>
      have hsre_le : s.re ≤ -2 := by
        rw [hs_eq]
        norm_num [Nat.cast_mul]
      linarith

/-- The gamma factor times the Laplace transform is holomorphic on the punctured strip. -/
lemma kadiri_gamma_laplace_product_holomorphicOn_strip
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {b a : ℝ}
    (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    HolomorphicOn
      (fun s : ℂ =>
        ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) *
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
      (Set.Icc (-a) (1 / 2 : ℝ) ×ℂ Set.univ \ {0}) := by
  let S : Set ℂ := Set.Icc (-a) (1 / 2 : ℝ) ×ℂ Set.univ \ {0}
  let F : ℂ → ℂ := fun s => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume
  let G : ℂ → ℂ :=
    fun s => (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))
  let Gshift : ℂ → ℂ :=
    fun s => (1 / 2 : ℂ) * (digamma (s / 2 + 1) + digamma ((1 - s) / 2)) - s⁻¹
  have hFdiff : DifferentiableOn ℂ F S :=
    (kadiri_laplace_exp_differentiableOn_kadiri_strip hφ ha hab hφ_decay).mono
      fun s hs => hs.1
  have harg1 : DifferentiableOn ℂ (fun s : ℂ => digamma (s / 2 + 1)) S := by
    intro s hs
    have hsrect := Complex.mem_reProdIm.mp hs.1 |>.1
    have hslo : -a ≤ s.re := hsrect.1
    have hre : (s / 2 + 1).re = s.re / 2 + 1 := by
      rw [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
    have hpos : 0 < (s / 2 + 1).re := by
      rw [hre]
      linarith
    exact DifferentiableAt.differentiableWithinAt
      ((Complex.differentiableAt_digamma_of_re_pos hpos).comp s (by fun_prop))
  have harg2 : DifferentiableOn ℂ (fun s : ℂ => digamma ((1 - s) / 2)) S := by
    intro s hs
    have hsrect := Complex.mem_reProdIm.mp hs.1 |>.1
    have hshi : s.re ≤ 1 / 2 := hsrect.2
    have hre : ((1 - s) / 2).re = (1 - s.re) / 2 := by
      rw [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    have hpos : 0 < ((1 - s) / 2).re := by
      rw [hre]
      linarith
    exact DifferentiableAt.differentiableWithinAt
      ((Complex.differentiableAt_digamma_of_re_pos hpos).comp s (by fun_prop))
  have hinv : DifferentiableOn ℂ (fun s : ℂ => s⁻¹) S := by
    intro s hs
    have hsne : s ≠ 0 := by simpa [S] using hs.2
    exact DifferentiableAt.differentiableWithinAt (differentiableAt_id.inv hsne)
  have hGshift : DifferentiableOn ℂ Gshift S := by
    dsimp [Gshift]
    exact ((differentiableOn_const (1 / 2 : ℂ)).mul (harg1.add harg2)).sub hinv
  have hG : DifferentiableOn ℂ G S := by
    refine hGshift.congr fun s hs => ?_
    have hsne : s ≠ 0 := by simpa [S] using hs.2
    have hsrect := Complex.mem_reProdIm.mp hs.1 |>.1
    have hslo : -a ≤ s.re := hsrect.1
    have hpoles : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) :=
      kadiri_digamma_half_arg_ne_neg_nat hsne (by linarith)
    have hrec := Complex.digamma_apply_add_one (s / 2) hpoles
    dsimp [G, Gshift]
    rw [hrec]
    field_simp [hsne]
    ring
  exact hG.mul hFdiff

/-- The shared bound `CΓ log(T+2) · CΦ/(T+2)` for the gamma-factor horizontal integrands. -/
private lemma kadiri_gamma_horizontal_summand_norm_le
    {w z : ℂ} {CΓ CΦ T : ℝ} (hT : 1 ≤ T) (hCΓ : 0 ≤ CΓ)
    (hw : ‖w‖ ≤ CΓ * Real.log (T + 2)) (hz : ‖z‖ ≤ CΦ / (T + 2)) :
    ‖w * z‖ ≤ (CΓ * CΦ) * (Real.log (T + 2) / (T + 2)) := by
  have hlog_nonneg : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  calc
    ‖w * z‖ = ‖w‖ * ‖z‖ := norm_mul _ _
    _ ≤ (CΓ * Real.log (T + 2)) * (CΦ / (T + 2)) :=
        mul_le_mul hw hz (norm_nonneg _) (mul_nonneg hCΓ hlog_nonneg)
    _ = (CΓ * CΦ) * (Real.log (T + 2) / (T + 2)) := by ring

/-- The gamma-factor log bound, packaged as an eventual uniform bound over the strip
ordinates `σ ∈ (-a, 1/2]`. -/
private lemma kadiri_gamma_factor_horizontal_eventually_norm_le
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ CΓ : ℝ, 0 < CΓ ∧
      ∀ᶠ (T : ℝ) in Filter.atTop, ∀ σ : ℝ, σ ∈ Set.uIoc (-a) (1 / 2 : ℝ) →
        ‖(1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
             digamma ((((1 : ℂ) - ((σ : ℂ) + (T : ℂ) * I)) / 2)))‖ ≤
          CΓ * Real.log (T + 2) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := kadiri_gamma_factor_horizontal_norm_le_log ha ha1
  refine ⟨CΓ, hCΓ, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT σ hσ
  have hle : -a ≤ (1 / 2 : ℝ) := by linarith
  have hσI : σ ∈ Set.Ioc (-a) (1 / 2) := by
    rw [Set.uIoc_of_le hle] at hσ
    exact hσ
  exact hΓ T σ hT (le_of_lt hσI.1) hσI.2

/-- Horizontal vanishing from separate factor bounds: an `O(log(T+2))` coefficient times an
`O(1/(T+2))` transform integrates to `o(1)` over the strip ordinates. -/
private lemma kadiri_gamma_horizontal_vanishes_of_factor_bounds
    {a CΓ CΦ : ℝ} {W Z : ℝ → ℝ → ℂ} (hCΓ : 0 ≤ CΓ)
    (hW : ∀ᶠ (T : ℝ) in Filter.atTop, ∀ σ : ℝ, σ ∈ Set.uIoc (-a) (1 / 2 : ℝ) →
      ‖W T σ‖ ≤ CΓ * Real.log (T + 2))
    (hZ : ∀ᶠ (T : ℝ) in Filter.atTop, ∀ σ : ℝ, σ ∈ Set.uIoc (-a) (1 / 2 : ℝ) →
      ‖Z T σ‖ ≤ CΦ / (T + 2)) :
    Filter.Tendsto (fun T : ℝ => ∫ σ in (-a)..(1 / 2), W T σ * Z T σ)
      Filter.atTop (nhds 0) := by
  refine tendsto_intervalIntegral_zero_of_uniform_norm_bound
    (B := fun T : ℝ => (CΓ * CΦ) * (Real.log (T + 2) / (T + 2))) ?_ ?_
  · have hbase :=
      tendsto_const_mul_log_add_two_div_add_two_atTop
        ((CΓ * CΦ) * |(1 / 2 : ℝ) - -a|)
    convert hbase using 1
    ext T
    ring
  · filter_upwards [hW, hZ, Filter.eventually_ge_atTop (1 : ℝ)] with T hWT hZT hT σ hσ
    exact kadiri_gamma_horizontal_summand_norm_le hT hCΓ (hWT σ hσ) (hZT σ hσ)

/-- Horizontal vanishing given a uniform `O(1/(T+2))` bound on the transform along the strip. -/
theorem kadiri_gamma_horizontal_vanishes_of_laplace_strip_decay
    {Φ : ℂ → ℂ} {a CΦ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hΦ : ∀ᶠ (T : ℝ) in Filter.atTop, ∀ σ : ℝ,
      σ ∈ Set.uIoc (-a) (1 / 2 : ℝ) →
      (‖Φ (-((σ : ℂ) + (T : ℂ) * I))‖ : ℝ) ≤ (CΦ / (T + 2) : ℝ)) :
    Filter.Tendsto
      (fun T : ℝ => ∫ σ in (-a)..(1 / 2),
        ((1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
           digamma ((((1 : ℂ) - ((σ : ℂ) + (T : ℂ) * I)) / 2)))) *
          Φ (-((σ : ℂ) + (T : ℂ) * I)))
      Filter.atTop (nhds 0) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := kadiri_gamma_factor_horizontal_eventually_norm_le ha ha1
  exact kadiri_gamma_horizontal_vanishes_of_factor_bounds hCΓ.le hΓ hΦ

private lemma kadiri_laplace_strip_integral_eq_oscillatory
    (φ : ℝ → ℂ) (σ T : ℝ) :
    (∫ y : ℝ, φ y * exp (((σ : ℂ) + (T : ℂ) * I) * (y : ℂ)) ∂volume) =
      ∫ y : ℝ, (exp ((σ : ℂ) * (y : ℂ)) * φ y) *
        exp ((T : ℂ) * I * (y : ℂ)) ∂volume := by
  apply integral_congr_ae
  filter_upwards with y
  have hexp :
      exp (((σ : ℂ) + (T : ℂ) * I) * (y : ℂ)) =
        exp ((σ : ℂ) * (y : ℂ)) * exp ((T : ℂ) * I * (y : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Uniform decay of the strip Laplace transform: for `1 ≤ |T|` and `-a < σ ≤ 1/2` the
transform at `σ + iT` is bounded by `CΦ / (|T| + 2)`, by one integration by parts. -/
private lemma kadiri_laplace_strip_decay
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ CΦ : ℝ, 0 ≤ CΦ ∧
      ∀ T : ℝ, 1 ≤ |T| → ∀ σ : ℝ, σ ∈ Set.uIoc (-a) (1 / 2) →
        ‖∫ y : ℝ, φ y * exp (((σ : ℂ) + (T : ℂ) * I) * (y : ℂ)) ∂volume‖ ≤
          CΦ / (|T| + 2) := by
  obtain ⟨D, hD_nonneg, hD⟩ :=
    kadiri_laplace_strip_deriv_integral_bounded
      (φ := φ) hφ hφ_decay hφ'_decay ha hab
  refine ⟨3 * D, mul_nonneg (by norm_num) hD_nonneg, fun T hT σ hσ => ?_⟩
  have hT_pos : 0 < |T| := by linarith
  have hT_ne : T ≠ 0 := by
    intro h
    rw [h, abs_zero] at hT
    linarith
  have hstrip_nonempty : -a ≤ (1 / 2 : ℝ) := by linarith
  have hσIoc : σ ∈ Set.Ioc (-a) (1 / 2) := by
    rw [Set.uIoc_of_le hstrip_nonempty] at hσ
    exact hσ
  have hσlo : -a ≤ σ := hσIoc.1.le
  have hσhi : σ ≤ 1 / 2 := hσIoc.2
  let g : ℝ → ℂ := fun y => exp ((σ : ℂ) * (y : ℂ)) * φ y
  have hg : Integrable g :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := φ) hφ.continuous hφ_decay ha hab hσlo hσhi
  have hdiff : Differentiable ℝ g :=
    kadiri_laplace_strip_weight_differentiable hφ σ
  have hg' : Integrable (deriv g) :=
    kadiri_laplace_strip_weight_deriv_integrable
      (φ := φ) hφ hφ_decay hφ'_decay ha hab hσlo hσhi
  have hosc :=
    norm_oscillatory_integral_le_integral_deriv_div_abs g hg hdiff hg' hT_ne
  have hderiv_bound : (∫ x, ‖deriv g x‖ ∂volume) ≤ D := hD σ hσlo hσhi
  have htail : D / |T| ≤ (3 * D) / (|T| + 2) := by
    have hT2_pos : 0 < |T| + 2 := by linarith
    rw [div_le_div_iff₀ hT_pos hT2_pos]
    nlinarith
  calc
    ‖∫ y : ℝ, φ y * exp (((σ : ℂ) + (T : ℂ) * I) * (y : ℂ)) ∂volume‖
        = ‖∫ y : ℝ, g y * exp ((T : ℂ) * I * (y : ℂ)) ∂volume‖ := by
          rw [kadiri_laplace_strip_integral_eq_oscillatory φ σ T]
    _ ≤ (∫ x, ‖deriv g x‖ ∂volume) / |T| := hosc
    _ ≤ D / |T| := div_le_div_of_nonneg_right hderiv_bound hT_pos.le
    _ ≤ (3 * D) / (|T| + 2) := htail

/-- Cancelling the double negation `Φ(-(-s))`: the transform integrand at `-(-s)` is the
two-sided Laplace integrand `φ y · exp (s y)`. -/
private lemma kadiri_laplace_transform_neg_neg (φ : ℝ → ℂ) (s : ℂ) :
    (∫ y : ℝ, φ y * exp (-(-s) * (y : ℂ)) ∂volume) =
      ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume := by
  simp only [neg_neg]

/-- The gamma-factor horizontal segment integrals vanish as the height `T → ∞`. -/
theorem kadiri_gamma_horizontal_vanishes
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ => ∫ σ in (-a)..(1 / 2),
        ((1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
           digamma ((((1 : ℂ) - ((σ : ℂ) + (T : ℂ) * I)) / 2)))) *
          Φ (-((σ : ℂ) + (T : ℂ) * I)))
      Filter.atTop (nhds 0) := by
  obtain ⟨CΦ, _hCΦ_nonneg, hΦ_strip⟩ :=
    kadiri_laplace_strip_decay (φ := φ) hφ hφ_decay hφ'_decay ha hab
  refine kadiri_gamma_horizontal_vanishes_of_laplace_strip_decay
    (Φ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume)
    (a := a) (CΦ := CΦ) ha ha1 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT σ hσ
  have habs : |T| = T := abs_of_nonneg (by linarith)
  have hTabs : 1 ≤ |T| := by
    rw [habs]
    exact hT
  have h := hΦ_strip T hTabs σ hσ
  rw [habs] at h
  simpa [kadiri_laplace_transform_neg_neg φ ((σ : ℂ) + (T : ℂ) * I)] using h

private lemma kadiri_gamma_factor_neg_height_norm_eq_pos (σ T : ℝ) :
    ‖(1 / 2 : ℂ) *
        (digamma ((((σ : ℂ) + (-(T : ℂ)) * I) / 2)) +
         digamma ((((1 : ℂ) - ((σ : ℂ) + (-(T : ℂ)) * I)) / 2)))‖ =
      ‖(1 / 2 : ℂ) *
        (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
         digamma ((((1 : ℂ) - ((σ : ℂ) + (T : ℂ) * I)) / 2)))‖ := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hsconj : ((σ : ℂ) + (-(T : ℂ)) * I) = (starRingEnd ℂ) s := by
    apply Complex.ext <;> simp [s]
  have hfac :
      (1 / 2 : ℂ) *
          (digamma ((((starRingEnd ℂ) s) / 2)) +
           digamma ((((1 : ℂ) - ((starRingEnd ℂ) s)) / 2))) =
        (starRingEnd ℂ)
          ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) := by
    have hleft :
        digamma ((((starRingEnd ℂ) s) / 2)) =
          (starRingEnd ℂ) (digamma (s / 2)) := by
      have harg : ((starRingEnd ℂ) s) / 2 = (starRingEnd ℂ) (s / 2) := by
        rw [map_div₀, map_ofNat]
      rw [harg, digamma_conj]
    have hright :
        digamma ((((1 : ℂ) - ((starRingEnd ℂ) s)) / 2)) =
          (starRingEnd ℂ) (digamma ((1 - s) / 2)) := by
      have harg :
          (1 - (starRingEnd ℂ) s) / 2 = (starRingEnd ℂ) ((1 - s) / 2) := by
        rw [map_div₀, map_sub, map_one, map_ofNat]
      rw [harg, digamma_conj]
    rw [hleft, hright, map_mul, map_add]
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
      rw [map_div₀, map_one, map_ofNat]
    rw [hhalf]
  rw [hsconj, hfac, norm_conj]

private lemma kadiri_gamma_horizontal_vanishes_neg_height
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ => ∫ σ in (-a)..(1 / 2),
        ((1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (-(T : ℂ)) * I) / 2)) +
           digamma ((((1 : ℂ) - ((σ : ℂ) + (-(T : ℂ)) * I)) / 2)))) *
          Φ (-((σ : ℂ) + (-(T : ℂ)) * I)))
      Filter.atTop (nhds 0) := by
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  change Filter.Tendsto
      (fun T : ℝ => ∫ σ in (-a)..(1 / 2),
        ((1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (-(T : ℂ)) * I) / 2)) +
           digamma ((((1 : ℂ) - ((σ : ℂ) + (-(T : ℂ)) * I)) / 2)))) *
          Φ (-((σ : ℂ) + (-(T : ℂ)) * I)))
      Filter.atTop (nhds 0)
  obtain ⟨CΦ, _hCΦ_nonneg, hΦ_strip⟩ :=
    kadiri_laplace_strip_decay (φ := φ) hφ hφ_decay hφ'_decay ha hab
  obtain ⟨CΓ, hCΓ, hΓ⟩ := kadiri_gamma_factor_horizontal_eventually_norm_le ha ha1
  have hΓneg :
      ∀ᶠ (T : ℝ) in Filter.atTop, ∀ σ : ℝ, σ ∈ Set.uIoc (-a) (1 / 2 : ℝ) →
        ‖(1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (-(T : ℂ)) * I) / 2)) +
             digamma ((((1 : ℂ) - ((σ : ℂ) + (-(T : ℂ)) * I)) / 2)))‖ ≤
          CΓ * Real.log (T + 2) := by
    filter_upwards [hΓ] with T hΓT σ hσ
    rw [kadiri_gamma_factor_neg_height_norm_eq_pos σ T]
    exact hΓT σ hσ
  have hΦneg :
      ∀ᶠ (T : ℝ) in Filter.atTop, ∀ σ : ℝ, σ ∈ Set.uIoc (-a) (1 / 2 : ℝ) →
        ‖Φ (-((σ : ℂ) + (-(T : ℂ)) * I))‖ ≤ CΦ / (T + 2) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT σ hσ
    have habs : |(-T : ℝ)| = T := by
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    have hTabs : 1 ≤ |(-T : ℝ)| := by
      rw [habs]
      exact hT
    have h := hΦ_strip (-T) hTabs σ hσ
    rw [habs] at h
    have hΦeq :
        Φ (-((σ : ℂ) + (-(T : ℂ)) * I)) =
          ∫ y : ℝ, φ y * exp (((σ : ℂ) + (-(T : ℂ)) * I) * (y : ℂ)) ∂volume :=
      kadiri_laplace_transform_neg_neg φ ((σ : ℂ) + (-(T : ℂ)) * I)
    rw [hΦeq]
    simpa using h
  exact kadiri_gamma_horizontal_vanishes_of_factor_bounds hCΓ.le hΓneg hΦneg

/-- The gamma-factor horizontal segment integrals vanish as the height `T → -∞`. -/
theorem kadiri_gamma_horizontal_vanishes_atBot
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ => ∫ σ in (-a)..(1 / 2),
        ((1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
           digamma ((((1 : ℂ) - ((σ : ℂ) + (T : ℂ) * I)) / 2)))) *
          Φ (-((σ : ℂ) + (T : ℂ) * I)))
      Filter.atBot (nhds 0) := by
  have hneg :=
    kadiri_gamma_horizontal_vanishes_neg_height
      (φ := φ) hφ hφ_decay hφ'_decay ha hab ha1
  simpa [Function.comp_def] using hneg.comp tendsto_neg_atBot_atTop

private lemma kadiri_gamma_right_line_integrable
    {φ : ℝ → ℂ}
    (hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    MeasureTheory.Integrable (fun t : ℝ ↦
      ((1 / 2 : ℂ) *
        (digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2) +
          digamma ((1 - ((1 / 2 : ℂ) + (t : ℂ) * I)) / 2))) *
        ∫ y, φ y * exp (-(-((1 / 2 : ℂ) + (t : ℂ) * I)) * (y : ℂ)) ∂volume) := by
  refine hΓ_int.congr (Filter.Eventually.of_forall fun t => ?_)
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hsre : s.re = 1 / 2 := by simp [s]
  have hsym := kadiri_thm_3_1_q1_gamma_symmetrization (s := s) hsre
  have hInt :
      (∫ y, φ y * exp (-(-s) * (y : ℂ)) ∂volume) =
        ∫ y, φ y * exp (s * (y : ℂ)) ∂volume :=
    kadiri_laplace_transform_neg_neg φ s
  change
    ((digamma (s / 2)).re : ℂ) * (∫ y, φ y * exp (s * (y : ℂ)) ∂volume) =
      ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) *
        ∫ y, φ y * exp (-(-s) * (y : ℂ)) ∂volume
  rw [hInt, hsym]

/-- The contour-shift limit for equation (15) of Kadiri (2005), Théorème 3.1, `q = 1`. -/
theorem kadiri_thm_3_1_q1_eq_15_core
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (_hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_3 φ a T)
      Filter.atTop
      (nhds (Φ 0
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I)))) := by
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  let f : ℂ → ℂ := fun s =>
    ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) *
      (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
  have hσ : (-a : ℝ) < (0 : ℂ).re ∧ (0 : ℂ).re < (1 / 2 : ℝ) := by
    constructor
    · simp only [Complex.zero_re]
      linarith
    · norm_num
  have hf : HolomorphicOn f (Set.Icc (-a) (1 / 2 : ℝ) ×ℂ Set.univ \ {0}) := by
    simpa [f] using
      kadiri_gamma_laplace_product_holomorphicOn_strip
        (φ := φ) _hφ _ha _hab _ha1 _hφ_decay
  have hpole :
      (f - (fun s ↦ (-(∫ y : ℝ, φ y ∂volume)) / (s - 0)))
        =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    have hp :=
      kadiri_gamma_laplace_pole_sub_isBigO_one
        (φ := φ) _hφ _hb _hφ_decay
    refine hp.congr' ?_ (EventuallyEq.rfl)
    filter_upwards with s
    dsimp [f]
    ring
  have hbot :
      Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in (-a)..(1 / 2), f (x + y * I))
        atBot (𝓝 0) := by
    simpa [f, Φ] using
      kadiri_gamma_horizontal_vanishes_atBot
        (φ := φ) _hφ _hφ_decay _hφ'_decay _ha _hab _ha1
  have htop :
      Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in (-a)..(1 / 2), f (x + y * I))
        atTop (𝓝 0) := by
    simpa [f, Φ] using
      kadiri_gamma_horizontal_vanishes
        (φ := φ) _hφ _hφ_decay _hφ'_decay _ha _hab _ha1
  have hright : Integrable (fun (y : ℝ) ↦ f ((1 / 2 : ℝ) + y * I)) := by
    simpa [f] using kadiri_gamma_right_line_integrable (φ := φ) _hΓ_int
  have hshift :=
    tendsto_truncated_vertical_shift_with_simple_pole_Ioo
      (σ := -a) (σ' := (1 / 2 : ℝ)) (f := f) (p := 0)
      (A := -(∫ y : ℝ, φ y ∂volume)) hσ hf hpole hbot htop hright
  have hlimit :
      VerticalIntegral' f (1 / 2 : ℝ) - (-(∫ y : ℝ, φ y ∂volume)) =
        Φ 0
          + (1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ,
                ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                  Φ (-(1 / 2 + (t : ℂ) * I)) := by
    have hΦ0 : Φ 0 = ∫ y : ℝ, φ y ∂volume := by
      simp [Φ]
    have hline :
        (fun t : ℝ => f ((1 / 2 : ℝ) + t * I)) =ᵐ[volume]
          (fun t : ℝ =>
            ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
              Φ (-(1 / 2 + (t : ℂ) * I))) := by
      filter_upwards with t
      set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
      have hsdef : ((1 / 2 : ℝ) + t * I : ℂ) = s := by simp [s]
      have hsre : s.re = 1 / 2 := by simp [s]
      have hsym := kadiri_thm_3_1_q1_gamma_symmetrization (s := s) hsre
      have hΦ : (∫ y, φ y * exp (s * (y : ℂ)) ∂volume) = Φ (-s) :=
        (kadiri_laplace_transform_neg_neg φ s).symm
      rw [hsdef]
      dsimp [f]
      change
        ((1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))) *
            (∫ y, φ y * exp (s * (y : ℂ)) ∂volume) =
          ((digamma (s / 2)).re : ℂ) * Φ (-s)
      rw [hsym, hΦ]
    calc
      VerticalIntegral' f (1 / 2 : ℝ) - (-(∫ y : ℝ, φ y ∂volume))
          = (1 / (2 * (Real.pi : ℂ) * I)) *
              (I * ∫ t : ℝ, f ((1 / 2 : ℝ) + t * I)) +
                ∫ y : ℝ, φ y ∂volume := by
            dsimp [VerticalIntegral', VerticalIntegral]
            ring
      _ = (1 / (2 * (Real.pi : ℂ) * I)) *
              (I * ∫ t : ℝ,
                ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                  Φ (-(1 / 2 + (t : ℂ) * I))) +
                ∫ y : ℝ, φ y ∂volume := by
            rw [integral_congr_ae hline]
      _ = Φ 0
          + (1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ,
                ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                  Φ (-(1 / 2 + (t : ℂ) * I)) := by
            rw [hΦ0]
            field_simp [Complex.I_ne_zero]
            ring
  change
    Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_3 φ a T) atTop
      (𝓝 (Φ 0
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I))))
  rw [← hlimit]
  refine hshift.congr' ?_
  filter_upwards with T
  dsimp [kadiri_thm_3_1_q1_I_3, f, Φ]
  apply congrArg (fun z : ℂ => (1 / (2 * (Real.pi : ℂ))) * z)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t _ ↦ ?_
  apply congrArg (fun z : ℂ =>
    ((1 / 2 : ℂ) *
      (digamma (((-a : ℝ) + (t : ℂ) * I) / 2) +
        digamma ((1 - ((-a : ℝ) + (t : ℂ) * I)) / 2))) * z)
  exact (kadiri_laplace_transform_neg_neg φ (((-a : ℝ) : ℂ) + (t : ℂ) * I)).symm

end Kadiri
