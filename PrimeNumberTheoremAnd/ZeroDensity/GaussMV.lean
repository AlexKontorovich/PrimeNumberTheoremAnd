/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZetaBounds

open MeasureTheory Complex Set Real

@[expose] public noncomputable section

namespace ZeroDensity

/-- Gaussian weight. -/
def gw (T t : ℝ) : ℝ := Real.exp (-(t / T) ^ 2)

/-- Gaussian kernel (modulus of the Fourier transform of `gw`). -/
def gk (T ξ : ℝ) : ℝ := √π * T * Real.exp (-(T ^ 2 / 4) * ξ ^ 2)

lemma gw_ft (T : ℝ) (hT : 0 < T) (ξ : ℝ) :
    ∫ t : ℝ, (gw T t : ℂ) * cexp (t * ξ * I) =
      (π / (1 / T ^ 2 : ℂ)) ^ (1 / 2 : ℂ) * cexp (-((T ^ 2 / 4 : ℝ) * ξ ^ 2 : ℝ)) := by
  have hb : ((-(1 / T ^ 2 : ℝ) : ℂ)).re < 0 := by
    change -(1 / T ^ 2) < (0:ℝ); have : 0 < 1 / T ^ 2 := by positivity
    linarith
  have := integral_cexp_quadratic hb (ξ * I) 0
  convert this using 2
  · ext t; simp only [gw, ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  · simp
  · congr 1; push_cast; field_simp; ring_nf; simp [I_sq]

lemma norm_gw_ft (T : ℝ) (hT : 0 < T) (ξ : ℝ) :
    ‖∫ t : ℝ, (gw T t : ℂ) * cexp (t * ξ * I)‖ = gk T ξ := by
  rw [gw_ft T hT, norm_mul, Complex.norm_exp, ← ofReal_neg, ofReal_re]
  have : (π / (1 / T ^ 2 : ℂ)) = ((π * T ^ 2 : ℝ) : ℂ) := by push_cast; field_simp
  rw [this, norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [gk]
  congr 1
  · rw [show ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hT.le]
  ring_nf

lemma integral_gk (T : ℝ) (hT : 0 < T) : ∫ ξ, gk T ξ = 2 * π := by
  simp only [gk]
  rw [integral_const_mul, integral_gaussian]
  have h1 : π / (T ^ 2 / 4) = (2 * √π / T) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt pi_pos.le]; field_simp; ring
  rw [h1, Real.sqrt_sq (by positivity)]
  field_simp
  rw [Real.sq_sqrt pi_pos.le]

lemma integrable_gk (T : ℝ) (hT : 0 < T) : Integrable (gk T) :=
  (integrable_exp_neg_mul_sq (by positivity : 0 < T ^ 2 / 4)).const_mul _

lemma gk_nonneg (T ξ : ℝ) (hT : 0 ≤ T) : 0 ≤ gk T ξ := by unfold gk; positivity

lemma gk_neg (T ξ : ℝ) : gk T (-ξ) = gk T ξ := by simp [gk]

lemma integrable_gw (T : ℝ) (hT : 0 < T) : Integrable (gw T) := by
  have := integrable_exp_neg_mul_sq (by positivity : 0 < 1 / T ^ 2)
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [gw]; congr 1; field_simp

lemma one_le_e_gw (T t : ℝ) (hT : 0 < T) (ht : t ∈ Ioc 0 T) : 1 ≤ Real.exp 1 * gw T t := by
  unfold gw
  rw [← Real.exp_add, Real.one_le_exp_iff]
  have : (t / T) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]; nlinarith [ht.1, ht.2]
  linarith


/-- Fourier-type transform `F g t = ∫ g(u) e^{-itu} du`. -/
def FT (g : ℝ → ℂ) (t : ℝ) : ℂ := ∫ u : ℝ, g u * cexp (-((t:ℂ) * u * I))

lemma gk_continuous (T : ℝ) : Continuous (gk T) := by unfold gk; fun_prop

lemma norm_cexp_aux (t a b : ℝ) : ‖cexp ((t:ℂ) * ((b:ℂ) - a) * I)‖ = 1 := by
  have : (t:ℂ) * ((b:ℂ) - a) * I = ((t * (b - a) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, norm_exp_ofReal_mul_I]

lemma FT_mul_conj (g : ℝ → ℂ) (t : ℝ) :
    FT g t * (starRingEnd ℂ) (FT g t) =
      ∫ p : ℝ × ℝ, g p.1 * (starRingEnd ℂ) (g p.2) * cexp ((t:ℂ) * ((p.2:ℂ) - p.1) * I)
        ∂(volume.prod volume) := by
  unfold FT
  rw [← integral_conj, ← integral_prod_mul]
  congr 1; ext p
  rw [map_mul, ← Complex.exp_conj]
  have : (starRingEnd ℂ) (-((t:ℂ) * (p.2:ℂ) * I)) = (t:ℂ) * p.2 * I := by
    simp [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [this]
  have e : cexp ((t:ℂ) * ((p.2:ℂ) - p.1) * I) = cexp (-((t:ℂ) * p.1 * I)) * cexp ((t:ℂ) * p.2 * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e]; ring

lemma FT_norm_sq (g : ℝ → ℂ) (t : ℝ) :
    ((‖FT g t‖ ^ 2 : ℝ) : ℂ) = FT g t * (starRingEnd ℂ) (FT g t) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Gaussian-weighted mean value (Plancherel-free). -/
@[blueprint
  "zd-gauss-mv"
  (title := "Gaussian-weighted mean value")
  (statement := /--
    If $g\in L^1(\mathbb{R})\cap L^2(\mathbb{R})$ and $\hat g(t)=\int g(u)e^{-itu}\,du$, then for $T>0$,
    $$\int_{\mathbb{R}}e^{-(t/T)^2}|\hat g(t)|^2\,dt\le 2\pi\int_{\mathbb{R}}|g(u)|^2\,du.$$
  -/)]
theorem gauss_mean_value (g : ℝ → ℂ) (hg : Integrable g) (hg2 : Integrable fun u => ‖g u‖ ^ 2)
    (T : ℝ) (hT : 0 < T) :
    ∫ t, gw T t * ‖FT g t‖ ^ 2 ≤ 2 * π * ∫ u, ‖g u‖ ^ 2 := by
  set H : ℝ → ℝ × ℝ → ℂ := fun t p =>
    (gw T t : ℂ) * (g p.1 * (starRingEnd ℂ) (g p.2) * cexp ((t:ℂ) * ((p.2:ℂ) - p.1) * I)) with hH
  have hgm := hg.aestronglyMeasurable
  have hgc : AEStronglyMeasurable (fun v => (starRingEnd ℂ) (g v)) volume :=
    (Complex.continuous_conj).comp_aestronglyMeasurable hgm
  -- integrability for the swap
  have hInt : Integrable (Function.uncurry H) (volume.prod (volume.prod volume)) := by
    have hb : Integrable (fun q : ℝ × (ℝ × ℝ) => gw T q.1 * (‖g q.2.1‖ * ‖g q.2.2‖))
        (volume.prod (volume.prod volume)) :=
      (integrable_gw T hT).mul_prod (hg.norm.mul_prod hg.norm)
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · have h1 : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => g q.2.1)
          (volume.prod (volume.prod volume)) := hgm.comp_fst.comp_snd
      have h2 : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => (starRingEnd ℂ) (g q.2.2))
          (volume.prod (volume.prod volume)) := hgc.comp_snd.comp_snd
      have h3 : Continuous (fun q : ℝ × (ℝ × ℝ) =>
          cexp ((q.1:ℂ) * ((q.2.2:ℂ) - q.2.1) * I)) := by fun_prop
      have h4 : Continuous (fun q : ℝ × (ℝ × ℝ) => (gw T q.1 : ℂ)) := by unfold gw; fun_prop
      exact h4.aestronglyMeasurable.mul ((h1.mul h2).mul h3.aestronglyMeasurable)
    · simp only [Function.uncurry, hH, norm_mul, Complex.norm_real, norm_cexp_aux,
        Complex.norm_conj, mul_one]
      rw [Real.norm_of_nonneg (by unfold gw; positivity)]
  -- integrability of the two AM-GM pieces
  have hm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖g p.1‖ ^ 2 * gk T (p.2 - p.1))
      (volume.prod volume) :=
    (hgm.norm.pow 2).comp_fst.mul ((gk_continuous T).comp (by fun_prop) : Continuous fun p : ℝ × ℝ => gk T (p.2 - p.1)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖g p.2‖ ^ 2 * gk T (p.2 - p.1))
      (volume.prod volume) :=
    (hgm.norm.pow 2).comp_snd.mul ((gk_continuous T).comp (by fun_prop) : Continuous fun p : ℝ × ℝ => gk T (p.2 - p.1)).aestronglyMeasurable
  have hgkI := integrable_gk T hT
  have inner1 : ∀ x : ℝ, ∫ y, ‖g x‖ ^ 2 * gk T (y - x) = ‖g x‖ ^ 2 * (2 * π) := by
    intro x; rw [integral_const_mul, integral_sub_right_eq_self (gk T) x, integral_gk T hT]
  have inner2 : ∀ y : ℝ, ∫ x, ‖g y‖ ^ 2 * gk T (y - x) = ‖g y‖ ^ 2 * (2 * π) := by
    intro y
    have : (fun x => gk T (y - x)) = fun x => gk T (x - y) := by
      ext x; rw [← gk_neg]; congr 1; ring
    rw [integral_const_mul, this, integral_sub_right_eq_self (gk T) y, integral_gk T hT]
  have hI1 : Integrable (fun p : ℝ × ℝ => ‖g p.1‖ ^ 2 * gk T (p.2 - p.1)) (volume.prod volume) := by
    rw [integrable_prod_iff hm1]
    refine ⟨Filter.Eventually.of_forall fun x =>
      show Integrable (fun y => ‖g x‖ ^ 2 * gk T (y - x)) volume from
        (hgkI.comp_sub_right x).const_mul _, ?_⟩
    refine (hg2.mul_const (2 * π)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← inner1 x]; congr 1; ext y
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (gk_nonneg _ _ hT.le))]
  have hI2 : Integrable (fun p : ℝ × ℝ => ‖g p.2‖ ^ 2 * gk T (p.2 - p.1)) (volume.prod volume) := by
    rw [integrable_prod_iff' hm2]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · have : (fun x => ‖g y‖ ^ 2 * gk T (y - x)) = fun x => ‖g y‖ ^ 2 * gk T (x - y) := by
        ext x; rw [← gk_neg]; congr 2; ring
      simp only; rw [this]; exact (hgkI.comp_sub_right y).const_mul _
    refine (hg2.mul_const (2 * π)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← inner2 y]; congr 1; ext x
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (gk_nonneg _ _ hT.le))]
  have v1 : ∫ p, ‖g p.1‖ ^ 2 * gk T (p.2 - p.1) ∂(volume.prod volume) = (∫ u, ‖g u‖ ^ 2) * (2 * π) := by
    rw [integral_prod _ hI1]; simp_rw [inner1]; rw [integral_mul_const]
  have v2 : ∫ p, ‖g p.2‖ ^ 2 * gk T (p.2 - p.1) ∂(volume.prod volume) = (∫ u, ‖g u‖ ^ 2) * (2 * π) := by
    rw [integral_prod_symm _ hI2]; simp_rw [inner2]; rw [integral_mul_const]
  -- main chain
  have key : ((∫ t, gw T t * ‖FT g t‖ ^ 2 : ℝ) : ℂ) = ∫ t, ∫ p, H t p ∂(volume.prod volume) := by
    rw [show ((∫ t, gw T t * ‖FT g t‖ ^ 2 : ℝ) : ℂ) = ∫ t, ((gw T t * ‖FT g t‖ ^ 2 : ℝ) : ℂ)
      from integral_ofReal.symm]
    congr 1; ext t
    rw [ofReal_mul, FT_norm_sq, FT_mul_conj, ← integral_const_mul]
  have inner3 : ∀ p : ℝ × ℝ, ‖∫ t, H t p‖ = ‖g p.1‖ * ‖g p.2‖ * gk T (p.2 - p.1) := by
    intro p
    have : (fun t => H t p) = fun t => (g p.1 * (starRingEnd ℂ) (g p.2)) *
        ((gw T t : ℂ) * cexp ((t:ℂ) * ((p.2 - p.1 : ℝ) : ℂ) * I)) := by
      ext t; simp only [hH]; push_cast; ring
    rw [this, integral_const_mul, norm_mul, norm_gw_ft T hT, norm_mul, Complex.norm_conj]
  have hnn : 0 ≤ ∫ t, gw T t * ‖FT g t‖ ^ 2 :=
    integral_nonneg fun t => mul_nonneg (by unfold gw; positivity) (by positivity)
  calc ∫ t, gw T t * ‖FT g t‖ ^ 2 = ‖((∫ t, gw T t * ‖FT g t‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    _ = ‖∫ p, (∫ t, H t p) ∂(volume.prod volume)‖ := by
        rw [key, integral_integral_swap hInt]
    _ ≤ ∫ p, ‖∫ t, H t p‖ ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ ≤ ∫ p, ((‖g p.1‖ ^ 2 * gk T (p.2 - p.1)) + (‖g p.2‖ ^ 2 * gk T (p.2 - p.1))) / 2
          ∂(volume.prod volume) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
          ((hI1.add hI2).div_const 2) (Filter.Eventually.of_forall fun p => ?_)
        simp only [inner3]
        have := gk_nonneg T (p.2 - p.1) hT.le
        nlinarith [sq_nonneg (‖g p.1‖ - ‖g p.2‖)]
    _ = 2 * π * ∫ u, ‖g u‖ ^ 2 := by
        rw [integral_div, integral_add hI1 hI2, v1, v2]; ring

lemma FT_continuous (g : ℝ → ℂ) (hg : Integrable g) : Continuous (FT g) := by
  unfold FT
  refine continuous_of_dominated (bound := fun u => ‖g u‖) (fun t => ?_) (fun t => ?_) hg.norm ?_
  · exact hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
      cexp (-((t:ℂ) * u * I))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    have : -((t:ℂ) * u * I) = ((-(t * u) : ℝ) : ℂ) * I := by push_cast; ring
    rw [norm_mul, this, norm_exp_ofReal_mul_I, mul_one]
  · exact Filter.Eventually.of_forall fun u => by fun_prop

lemma norm_FT_le (g : ℝ → ℂ) (t : ℝ) : ‖FT g t‖ ≤ ∫ u, ‖g u‖ := by
  unfold FT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext u
  have : -((t:ℂ) * u * I) = ((-(t * u) : ℝ) : ℂ) * I := by push_cast; ring
  rw [norm_mul, this, norm_exp_ofReal_mul_I, mul_one]

/-- **Mean value theorem for Fourier transforms on `[0,T]`**, uniform in `T`. -/
theorem mean_value_FT (g : ℝ → ℂ) (hg : Integrable g) (hg2 : Integrable fun u => ‖g u‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, ‖FT g t‖ ^ 2 ≤ 2 * π * Real.exp 1 * ∫ u, ‖g u‖ ^ 2 := by
  have hg2n : 0 ≤ ∫ u, ‖g u‖ ^ 2 := integral_nonneg fun u => by positivity
  rcases hT.eq_or_lt with rfl | hT
  · simp only [intervalIntegral.integral_same, ge_iff_le]; positivity
  rw [intervalIntegral.integral_of_le hT.le]
  have hc : Continuous fun t => ‖FT g t‖ ^ 2 := ((FT_continuous g hg).norm.pow 2)
  set B := ∫ u, ‖g u‖
  have hW : Integrable (fun t => Real.exp 1 * (gw T t * ‖FT g t‖ ^ 2)) := by
    refine ((integrable_gw T hT).mul_const (B ^ 2)).const_mul (Real.exp 1) |>.mono'
      (by exact (continuous_const.mul ((by unfold gw; fun_prop : Continuous (gw T)).mul hc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    have h1 := norm_FT_le g t
    have h0 : 0 ≤ gw T t := by unfold gw; positivity
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
  calc ∫ t in Ioc 0 T, ‖FT g t‖ ^ 2
      ≤ ∫ t in Ioc 0 T, Real.exp 1 * (gw T t * ‖FT g t‖ ^ 2) := by
        refine setIntegral_mono_on (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          hW.integrableOn measurableSet_Ioc fun t ht => ?_
        have := one_le_e_gw T t hT ht
        nlinarith [sq_nonneg ‖FT g t‖]
    _ ≤ ∫ t, Real.exp 1 * (gw T t * ‖FT g t‖ ^ 2) :=
        setIntegral_le_integral hW (Filter.Eventually.of_forall fun t => by unfold gw; positivity)
    _ ≤ Real.exp 1 * (2 * π * ∫ u, ‖g u‖ ^ 2) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (gauss_mean_value g hg hg2 T hT) (by positivity)
    _ = _ := by ring

end ZeroDensity
