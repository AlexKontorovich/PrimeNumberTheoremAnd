/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZeroDensity.MeanSquare
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Step L3: the approximate formula for ζ with error `O(N^{-σ})`, uniformly for `|t| ≤ π N`

Second-order Euler–Maclaurin (periodic Bernoulli function `P2`), its absolutely convergent Fourier
series (Mathlib `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun`), and a first-derivative test
(one integration by parts) for each Fourier mode. Author: Devon Wright (formalized with Grok Bot).
-/

open Complex MeasureTheory Set Filter Topology Real

@[expose] public noncomputable section
namespace ZeroDensity


def ephi (k : ℤ) (x : ℝ) : ℂ := Complex.exp (2 * π * I * k * x)

lemma norm_ephi (k : ℤ) (x : ℝ) : ‖ephi k x‖ = 1 := by
  rw [ephi, Complex.norm_exp]; simp

lemma hasDerivAt_ephi (k : ℤ) (x : ℝ) : HasDerivAt (ephi k) (2*π*I*k * ephi k x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (2*π*I*k) * (y:ℂ)) ((2*π*I*k) * 1) x :=
    ((hasDerivAt_id x).ofReal_comp).const_mul (2*π*I*k)
  have h := h1.cexp
  simp only [mul_one] at h
  unfold ephi
  convert h using 1
  ring

def Dk (k : ℤ) (s : ℂ) (x : ℝ) : ℂ := 2*π*I*k*x - s - 1

lemma Dk_im (k : ℤ) (s : ℂ) (x : ℝ) : (Dk k s x).im = 2*π*k*x - s.im := by
  simp [Dk]

lemma norm_Dk_ge {k : ℤ} (hk : k ≠ 0) {s : ℂ} {N x : ℝ} (hN : 0 < N) (hx : N ≤ x)
    (ht : |s.im| ≤ π * N) : π * |(k:ℝ)| * x ≤ ‖Dk k s x‖ := by
  refine le_trans ?_ (Complex.abs_im_le_norm _)
  rw [Dk_im]
  have hk1 : (1:ℝ) ≤ |(k:ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  have hx0 : 0 < x := hN.trans_le hx
  have h2 : |2*π*k*x| = 2*π*|(k:ℝ)| *x := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hx0]; norm_num
  have h3 := abs_sub_abs_le_abs_sub (2*π*k*x) s.im
  have : π * x ≤ π * |(k:ℝ)| * x := by
    have := mul_le_mul_of_nonneg_left hk1 (le_of_lt (mul_pos Real.pi_pos hx0)); nlinarith
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hx Real.pi_pos.le]

lemma Dk_ne {k : ℤ} (hk : k ≠ 0) {s : ℂ} {N x : ℝ} (hN : 0 < N) (hx : N ≤ x)
    (ht : |s.im| ≤ π * N) : Dk k s x ≠ 0 := by
  intro h
  have := norm_Dk_ge hk hN hx ht
  rw [h, norm_zero] at this
  have hk1 : (0:ℝ) < |(k:ℝ)| := by positivity
  have : 0 < π * |(k:ℝ)| * x := by have := hN.trans_le hx; positivity
  linarith

lemma hasDerivAt_Dk (k : ℤ) (s : ℂ) (x : ℝ) : HasDerivAt (Dk k s) (2*π*I*k) x := by
  have h1 : HasDerivAt (fun y : ℝ => (2*π*I*k) * (y:ℂ)) ((2*π*I*k) * 1) x :=
    ((hasDerivAt_id x).ofReal_comp).const_mul (2*π*I*k)
  have := (h1.sub_const s).sub_const 1
  simp only [mul_one] at this
  unfold Dk; convert this using 1

/-- The oscillatory integral bound (first-derivative test). -/
theorem osc_bound {k : ℤ} (hk : k ≠ 0) {s : ℂ} {N : ℝ} (hN : 0 < N) (hσ : 0 ≤ s.re)
    (ht : |s.im| ≤ π * N) :
    ‖∫ x in Ioi N, ephi k x * (x:ℂ) ^ (-s-2)‖ ≤ 2 * N ^ (-s.re-2) / (π * |(k:ℝ)|) := by
  set σ := s.re with hσdef
  have hkpos : (0:ℝ) < |(k:ℝ)| := by positivity
  have hpk : 0 < π * |(k:ℝ)| := by positivity
  set u : ℝ → ℂ := fun x => (Dk k s x)⁻¹ with hu
  set u' : ℝ → ℂ := fun x => -(2*π*I*k) / (Dk k s x)^2 with hu'
  set v : ℝ → ℂ := fun x => (x:ℂ)^(-s-1) * ephi k x with hv
  set v' : ℝ → ℂ := fun x => (x:ℂ)^(-s-2) * ephi k x * Dk k s x with hv'
  have hDne : ∀ x ∈ Ici N, Dk k s x ≠ 0 := fun x hx => Dk_ne hk hN hx ht
  have hderu : ∀ x ∈ Ioi N, HasDerivAt u (u' x) x := fun x hx =>
    (hasDerivAt_Dk k s x).inv (hDne x (mem_Ici.2 (le_of_lt (mem_Ioi.1 hx))))
  have hcpow : ∀ x : ℝ, 0 < x → (x:ℂ)^(-s-1) = (x:ℂ)^(-s-2) * x := by
    intro x hx
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [show -s-1 = (-s-2) + 1 by ring, Complex.cpow_add _ _ hx0, Complex.cpow_one]
  have hderv : ∀ x ∈ Ioi N, HasDerivAt v (v' x) x := by
    intro x hx
    have hx0 : 0 < x := hN.trans hx
    have hr : (-s-1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 := (hasDerivAt_ofReal_cpow_const hx0.ne' hr).mul (hasDerivAt_ephi k x)
    convert h1 using 1
    simp only [hv', Dk]
    rw [show (-s-1-1) = -s-2 by ring, hcpow x hx0]
    ring
  have huv' : ∀ x ∈ Ioi N, u x * v' x = ephi k x * (x:ℂ)^(-s-2) := by
    intro x hx
    simp only [hu, hv']
    field_simp [hDne x (mem_Ici.2 (le_of_lt (mem_Ioi.1 hx)))]
  -- norms
  have hnu : ∀ x ∈ Ici N, ‖u x‖ ≤ (π * |(k:ℝ)| * x)⁻¹ := by
    intro x hx
    have hx0 : 0 < x := hN.trans_le hx
    simp only [hu, norm_inv]
    exact inv_anti₀ (by positivity) (norm_Dk_ge hk hN hx ht)
  have hnu' : ∀ x ∈ Ici N, ‖u' x‖ ≤ 2 / (π * |(k:ℝ)|) * x ^ (-2:ℝ) := by
    intro x hx
    have hx0 : 0 < x := hN.trans_le hx
    have hD := norm_Dk_ge hk hN hx ht
    simp only [hu', norm_div, norm_neg, norm_pow]
    have hnum : ‖2*π*I*(k:ℂ)‖ = 2*π*|(k:ℝ)| := by
      simp [abs_of_pos Real.pi_pos]
    rw [hnum, Real.rpow_neg hx0.le, Real.rpow_two]
    have hDp : 0 < π * |(k:ℝ)| * x := by positivity
    rw [div_le_iff₀ (pow_pos (hDp.trans_le hD) 2)]
    have : (π * |(k:ℝ)| * x)^2 ≤ ‖Dk k s x‖^2 := pow_le_pow_left₀ hDp.le hD 2
    have e : 2 / (π * |(k:ℝ)|) * (x ^ 2)⁻¹ * (π * |(k:ℝ)| * x)^2 = 2*π*|(k:ℝ)| := by
      field_simp
    nlinarith [this, show 0 ≤ 2 / (π * |(k:ℝ)|) * (x ^ 2)⁻¹ by positivity]
  have hnv : ∀ x : ℝ, 0 < x → ‖v x‖ = x ^ (-σ-1) := by
    intro x hx
    simp only [hv, norm_mul, norm_ephi, mul_one, norm_cpow_eq_rpow_re_of_pos hx]
    simp [hσdef]
  have hr2 : (-s-2) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hr1 : (-s-1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hcont_cpow : ∀ (c : ℂ), c ≠ 0 → ∀ x : ℝ, 0 < x → ContinuousAt (fun y : ℝ => (y:ℂ)^c) x :=
    fun c hc x hx => (hasDerivAt_ofReal_cpow_const hx.ne' hc).continuousAt
  have hcont_e : ∀ x, ContinuousAt (ephi k) x := fun x => (hasDerivAt_ephi k x).continuousAt
  have hvc : ∀ x : ℝ, 0 < x → ContinuousAt v x := fun x hx =>
    (hcont_cpow _ hr1 x hx).mul (hcont_e x)
  have huc : ∀ x ∈ Ici N, ContinuousAt u x := fun x hx =>
    (hasDerivAt_Dk k s x).continuousAt.inv₀ (hDne x hx)
  -- integrability of the main integrand
  have hf_int : IntegrableOn (fun x : ℝ => ephi k x * (x:ℂ)^(-s-2)) (Ioi N) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -σ-2) (by linarith) hN) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      exact ((hcont_e x).mul (hcont_cpow _ hr2 x (hN.trans hx))).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      have hx0 : 0 < x := hN.trans hx
      rw [norm_mul, norm_ephi, one_mul, norm_cpow_eq_rpow_re_of_pos hx0]; simp [hσdef]
  have huv'_int : IntegrableOn (u * v') (Ioi N) :=
    hf_int.congr_fun (fun x hx => (huv' x hx).symm) measurableSet_Ioi
  set C : ℝ := 2 / (π * |(k:ℝ)|) with hC
  have hu'v_bd : ∀ x ∈ Ioi N, ‖u' x * v x‖ ≤ C * x ^ (-σ-3) := by
    intro x hx
    have hx0 : 0 < x := hN.trans hx
    rw [norm_mul, hnv x hx0]
    calc ‖u' x‖ * x ^ (-σ-1) ≤ (C * x ^ (-2:ℝ)) * x ^ (-σ-1) :=
          mul_le_mul_of_nonneg_right (hnu' x (mem_Ici.2 (le_of_lt (mem_Ioi.1 hx)))) (by positivity)
      _ = C * x ^ (-σ-3) := by
          rw [mul_assoc, ← Real.rpow_add hx0]; ring_nf
  have hCint : IntegrableOn (fun x : ℝ => C * x ^ (-σ-3)) (Ioi N) :=
    (integrableOn_Ioi_rpow_of_lt (a := -σ-3) (by linarith) hN).const_mul C
  have hu'v_int : IntegrableOn (u' * v) (Ioi N) := by
    refine Integrable.mono' hCint ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx0 : 0 < x := hN.trans hx
      have hD := hDne x (mem_Ici.2 (le_of_lt (mem_Ioi.1 hx)))
      have : ContinuousAt u' x := by
        simp only [hu']
        exact continuousAt_const.div ((hasDerivAt_Dk k s x).continuousAt.pow 2) (pow_ne_zero 2 hD)
      exact (this.mul (hvc x hx0)).continuousWithinAt
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => hu'v_bd x hx)
  have h_zero : Tendsto (u * v) (𝓝[>] N) (𝓝 (u N * v N)) :=
    (((huc N (mem_Ici.2 le_rfl)).mul (hvc N hN)).tendsto).mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => (π * |(k:ℝ)| * N)⁻¹ * x ^ (-(σ+1))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < σ+1)).const_mul (π * |(k:ℝ)| * N)⁻¹
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop N] with x hx
    have hx0 : 0 < x := hN.trans_le hx
    simp only [Pi.mul_apply, norm_mul]
    rw [hnv x hx0, show -(σ+1) = -σ-1 by ring]
    refine mul_le_mul_of_nonneg_right ((hnu x hx).trans ?_) (by positivity)
    exact inv_anti₀ (by positivity) (by gcongr)
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hderu hderv huv'_int hu'v_int h_zero h_infty
  have hcongr : ∫ x in Ioi N, ephi k x * (x:ℂ)^(-s-2) = ∫ x in Ioi N, u x * v' x :=
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => (huv' x hx).symm)
  rw [hcongr, key, zero_sub]
  have hbd1 : ‖u N * v N‖ ≤ N ^ (-σ-2) / (π * |(k:ℝ)|) := by
    rw [norm_mul, hnv N hN]
    calc ‖u N‖ * N ^ (-σ-1) ≤ (π * |(k:ℝ)| * N)⁻¹ * N ^ (-σ-1) :=
          mul_le_mul_of_nonneg_right (hnu N (mem_Ici.2 le_rfl)) (by positivity)
      _ = N ^ (-σ-2) / (π * |(k:ℝ)|) := by
          rw [show (-σ-2) = (-1) + (-σ-1) by ring, Real.rpow_add hN, Real.rpow_neg_one]
          field_simp
  have hbd2 : ‖∫ x in Ioi N, u' x * v x‖ ≤ C * (N ^ (-σ-2) / (σ+2)) := by
    refine (norm_integral_le_of_norm_le hCint
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => hu'v_bd x hx))).trans ?_
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN]
    apply le_of_eq; congr 1
    rw [show -σ-3+1 = -σ-2 by ring, show -σ-2 = -(σ+2) by ring]; field_simp
  calc ‖-(u N * v N) - ∫ x in Ioi N, u' x * v x‖
      ≤ ‖u N * v N‖ + ‖∫ x in Ioi N, u' x * v x‖ := by
        rw [norm_sub_rev] ; exact (norm_sub_le _ _).trans (by rw [norm_neg]; linarith)
    _ ≤ N ^ (-σ-2) / (π * |(k:ℝ)|) + C * (N ^ (-σ-2) / (σ+2)) := add_le_add hbd1 hbd2
    _ ≤ 2 * N ^ (-σ-2) / (π * |(k:ℝ)|) := by
        have hNp : 0 < N ^ (-σ-2) := by positivity
        rw [hC]
        have h2 : 2 / (σ+2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        have : 2 / (π * |(k:ℝ)|) * (N ^ (-σ-2) / (σ+2)) = (2/(σ+2)) * (N ^ (-σ-2) / (π * |(k:ℝ)|)) := by
          field_simp
        rw [this]
        have h3 : 0 ≤ N ^ (-σ-2) / (π * |(k:ℝ)|) := by positivity
        have : 2 * N ^ (-σ-2) / (π * |(k:ℝ)|) = 2 * (N ^ (-σ-2) / (π * |(k:ℝ)|)) := by ring
        rw [this]; nlinarith


def P2 (x : ℝ) : ℝ := bernoulliFun 2 (Int.fract x)

def fc (n : ℤ) : ℂ := 1 / (2 * (π:ℂ) ^ 2) * (1 / (n:ℂ) ^ 2)

lemma fourier_fract (n : ℤ) (x : ℝ) :
    fourier n ((Int.fract x : ℝ) : AddCircle (1:ℝ)) = ephi n x := by
  rw [fourier_coe_apply, ephi, Int.fract]
  have : 2 * ↑π * I * ↑n * ↑(x - ↑⌊x⌋) / ((1:ℝ):ℂ) =
      2 * π * I * n * x + ((-(n * ⌊x⌋) : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma hasSum_P2 (x : ℝ) : HasSum (fun n : ℤ => fc n * ephi n x) (P2 x : ℂ) := by
  have h := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun (k := 2) le_rfl
    (x := Int.fract x) ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  simp only [fourier_fract] at h
  have h2 := h.mul_left (1 / (2 * (π:ℂ) ^ 2))
  convert h2 using 1
  · ext n; simp only [fc]; ring
  · rw [P2]
    have hpi : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    push_cast
    rw [mul_pow, mul_pow, I_sq]
    field_simp

lemma hasSum_norm_fc : HasSum (fun n : ℤ => ‖fc n‖) (1 / 6) := by
  have h := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun (k := 2) le_rfl
    (x := 0) ⟨le_rfl, zero_le_one⟩
  have h0 : ∀ n : ℤ, fourier n (((0:ℝ)) : AddCircle (1:ℝ)) = 1 := by
    intro n; rw [fourier_coe_apply]; simp
  simp only [h0, mul_one, bernoulliFun_two] at h
  have h2 := Complex.hasSum_re (h.mul_left (1 / (2 * (π:ℂ) ^ 2)))
  have hpi : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  convert h2 using 1
  · ext n
    have e : fc n = ((1 / (2 * π ^ 2) * (1 / (n:ℝ) ^ 2) : ℝ) : ℂ) := by simp [fc]
    rw [e, Complex.norm_of_nonneg (by positivity)]
    rw [show (1 / (2 * (π:ℂ) ^ 2) * (1 / (n:ℂ) ^ 2)) = ((1 / (2 * π ^ 2) * (1 / (n:ℝ) ^ 2) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  · simp only [Nat.factorial, Nat.succ_eq_add_one]
    have : (1 / (2 * (π:ℂ) ^ 2) * (-(2 * π * I) ^ 2 / ((((1:ℕ) * (1 * 1) * 2 : ℕ)) : ℂ) * (((0:ℝ) ^ 2 - 0 + 6⁻¹ : ℝ) : ℂ))) = ((1 / 6 : ℝ) : ℂ) := by
      push_cast; rw [mul_pow, mul_pow, I_sq]; field_simp; ring
    rw [this, Complex.ofReal_re]

lemma integrableOn_ephi_cpow (k : ℤ) {s : ℂ} {N : ℝ} (hN : 0 < N) (hσ : 0 ≤ s.re) :
    IntegrableOn (fun x : ℝ => ephi k x * (x:ℂ)^(-s-2)) (Ioi N) := by
  have hr2 : (-s-2) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -s.re-2) (by linarith) hN) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    exact ((hasDerivAt_ephi k x).continuousAt.mul
      (hasDerivAt_ofReal_cpow_const (hN.trans hx).ne' hr2).continuousAt).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hN.trans hx
    rw [norm_mul, norm_ephi, one_mul, norm_cpow_eq_rpow_re_of_pos hx0]; simp

/-- The second-order Euler–Maclaurin remainder integral. -/
def Jint (N : ℝ) (s : ℂ) : ℂ := ∫ x in Ioi N, (P2 x : ℂ) * (x:ℂ)^(-s-2)

/-- Key cancellation: `‖J‖ ≤ N^{-σ-2}/(3π)` when `|t| ≤ π N`. -/
theorem Jint_bound {s : ℂ} {N : ℝ} (hN : 0 < N) (hσ : 0 ≤ s.re) (ht : |s.im| ≤ π * N) :
    ‖Jint N s‖ ≤ N ^ (-s.re-2) / (3 * π) := by
  set F : ℤ → ℝ → ℂ := fun n x => fc n * (ephi n x * (x:ℂ)^(-s-2)) with hF
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi N)) := fun n =>
    (integrableOn_ephi_cpow n hN hσ).const_mul _
  have hnormint : ∀ n, ∫ x in Ioi N, ‖F n x‖ = ‖fc n‖ * (N ^ (-s.re-1) / (s.re+1)) := by
    intro n
    have : ∀ x ∈ Ioi N, ‖F n x‖ = ‖fc n‖ * x ^ (-s.re-2) := by
      intro x hx
      simp only [hF, norm_mul, norm_ephi, one_mul, norm_cpow_eq_rpow_re_of_pos (hN.trans hx)]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioi this, MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) hN]
    congr 1
    rw [show -s.re-2+1 = -s.re-1 by ring, show -s.re-1 = -(s.re+1) by ring]; field_simp
  have hsum : Summable fun n => ∫ x in Ioi N, ‖F n x‖ := by
    simp_rw [hnormint]; exact hasSum_norm_fc.summable.mul_right _
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  have hlimit : ∫ x in Ioi N, (∑' n, F n x) = Jint N s := by
    rw [Jint]; refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [hF]
    rw [show (fun n => fc n * (ephi n x * (x:ℂ)^(-s-2))) = fun n => (fc n * ephi n x) * (x:ℂ)^(-s-2)
      by ext n; ring]
    exact ((hasSum_P2 x).mul_right _).tsum_eq
  rw [hlimit] at hHS
  set B : ℝ := 2 * N ^ (-s.re-2) / π with hB
  have hg : HasSum (fun n => ‖fc n‖ * B) (1 / 6 * B) := hasSum_norm_fc.mul_right B
  have hbd : ∀ n, ‖∫ x in Ioi N, F n x‖ ≤ ‖fc n‖ * B := by
    intro n
    simp only [hF]
    rw [MeasureTheory.integral_const_mul, norm_mul]
    by_cases hn : n = 0
    · subst hn; simp [fc]
    refine mul_le_mul_of_nonneg_left ((osc_bound hn hN hσ ht).trans ?_) (norm_nonneg _)
    rw [hB]
    have hk1 : (1:ℝ) ≤ |(n:ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    have : 0 ≤ 2 * N ^ (-s.re-2) := by positivity
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
    have := mul_le_mul_of_nonneg_left hk1 (mul_nonneg this Real.pi_pos.le)
    nlinarith
  refine (hHS.norm_le_of_bounded hg hbd).trans (le_of_eq ?_)
  rw [hB]; field_simp; ring

/-! ### Periodic Bernoulli function `P2` -/

lemma P2_continuous : Continuous P2 := by
  have h : ContinuousOn (bernoulliFun 2) (Icc 0 1) := by
    have e : bernoulliFun 2 = fun x => x^2 - x + 6⁻¹ := funext bernoulliFun_two
    rw [e]; fun_prop
  exact h.comp_fract'' (bernoulliFun_endpoints_eq_of_ne_one (by norm_num)).symm

lemma P2_abs_le (x : ℝ) : |P2 x| ≤ 1 / 6 := by
  rw [P2, bernoulliFun_two, abs_le]
  have h0 := Int.fract_nonneg x; have h1 := Int.fract_lt_one x
  constructor <;> nlinarith

lemma P2_natCast (N : ℕ) : P2 N = 1 / 6 := by
  rw [P2, Int.fract_natCast, bernoulliFun_two]; norm_num

lemma hasDerivAt_P2 {x : ℝ} (hx : x ∉ range (Int.cast : ℤ → ℝ)) :
    HasDerivAt P2 (2 * Int.fract x - 1) x := by
  set n := ⌊x⌋ with hn
  have hlt : (n:ℝ) < x := by
    rcases (Int.floor_le x).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨n, h⟩ hx
  have hlt2 : x < n + 1 := Int.lt_floor_add_one x
  have hev : (fun y => P2 y) =ᶠ[𝓝 x] fun y => (y - n)^2 - (y - n) + 6⁻¹ := by
    filter_upwards [Ioo_mem_nhds hlt hlt2] with y hy
    have : ⌊y⌋ = n := by rw [Int.floor_eq_iff]; exact ⟨hy.1.le, hy.2⟩
    rw [P2, bernoulliFun_two, Int.fract, this]
  have hd : HasDerivAt (fun y : ℝ => (y - n)^2 - (y - n) + 6⁻¹) (2 * (x - n) - 1) x := by
    have h1 := ((hasDerivAt_id' x).sub_const (n:ℝ))
    have := ((h1.pow 2).sub h1).add_const (6⁻¹:ℝ)
    convert this using 1; norm_num
  rw [Int.fract]
  exact hd.congr_of_eventuallyEq hev

/-! ### Second-order Euler–Maclaurin for the tail integral -/

theorem tail_ibp {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    tailI N s = (N:ℂ) ^ (-s-1) / 12 - (s+1) / 2 * Jint N s := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hr1 : (-s-1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hr2 : (-s-2) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set F : ℝ → ℂ := fun x => ((P2 x / 2 : ℝ) : ℂ) * (x:ℂ)^(-s-1) with hF
  set g1 : ℝ → ℂ := fun x => ((⌊x⌋:ℂ) + 1 / 2 - x) * (x:ℂ)^(-s-1) with hg1
  set g2 : ℝ → ℂ := fun x => (P2 x : ℂ) * (x:ℂ)^(-s-2) with hg2
  set F' : ℝ → ℂ := fun x => -g1 x - (s+1)/2 * g2 x with hF'
  -- integrability
  have hg1i : IntegrableOn g1 (Ioi N) := by
    have := integrableOn_of_Zeta0_fun hN hs
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hg1]; congr 2; ring
  have hg2i : IntegrableOn g2 (Ioi N) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := -s.re-2) (by linarith) hNr).const_mul (1 / 6)) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      exact ((Complex.continuous_ofReal.comp P2_continuous).continuousAt.mul
        (hasDerivAt_ofReal_cpow_const (hNr.trans hx).ne' hr2).continuousAt).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      have hx0 : 0 < x := hNr.trans hx
      simp only [hg2]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
      have : (-s-2).re = -s.re-2 := by simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (P2_abs_le x) (by positivity)
  have hF'i : IntegrableOn F' (Ioi N) := (hg1i.neg).sub (hg2i.const_mul _)
  -- derivative of F off the integers
  have hderF : ∀ x, 0 < x → x ∉ range (Int.cast : ℤ → ℝ) → HasDerivAt F (F' x) x := by
    intro x hx0 hx
    have h1 : HasDerivAt (fun y => ((P2 y / 2 : ℝ) : ℂ)) (((2 * Int.fract x - 1) / 2 : ℝ) : ℂ) x :=
      ((hasDerivAt_P2 hx).div_const 2).ofReal_comp
    have h2 := hasDerivAt_ofReal_cpow_const hx0.ne' hr1
    have := h1.mul h2
    convert this using 1
    simp only [hF', hg1, hg2]
    have hx0' : (x:ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have hc : (x:ℂ)^(-s-1) = (x:ℂ)^(-s-2) * x := by
      rw [show -s-1 = (-s-2) + 1 by ring, Complex.cpow_add _ _ hx0', Complex.cpow_one]
    rw [show (-s-1-1) = -s-2 by ring, hc, Int.fract]
    push_cast; ring
  have hFc : ∀ x : ℝ, 0 < x → ContinuousAt F x := fun x hx =>
    (Complex.continuous_ofReal.comp (P2_continuous.div_const 2)).continuousAt.mul
      (hasDerivAt_ofReal_cpow_const hx.ne' hr1).continuousAt
  -- FTC on [N, M]
  have hFTC : ∀ M : ℝ, (N:ℝ) ≤ M → ∫ x in (N:ℝ)..M, F' x = F M - F N := by
    intro M hM
    refine integral_eq_of_hasDerivAt_off_countable_of_le F F' hM (countable_range _)
      (fun x hx => (hFc x (hNr.trans_le hx.1)).continuousWithinAt) (fun x hx => hderF x (hNr.trans hx.1.1) hx.2) ?_
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hM).2 (hF'i.mono_set Ioc_subset_Ioi_self)
  have hlim1 := intervalIntegral_tendsto_integral_Ioi (N:ℝ) hF'i tendsto_id
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => (1 / 12 : ℝ) * x ^ (-(s.re+1))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < s.re+1)).const_mul (1 / 12 : ℝ)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [hF]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs]
    have : (-s-1).re = -(s.re+1) := by simp; ring
    rw [this, abs_div, abs_two]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := P2_abs_le x; linarith
  have hlim2 : Tendsto (fun M => ∫ x in (N:ℝ)..M, F' x) atTop (𝓝 (0 - F N)) := by
    refine ((hFlim.sub_const (F N))).congr' ?_
    filter_upwards [eventually_ge_atTop (N:ℝ)] with M hM
    exact (hFTC M hM).symm
  have hIoi : ∫ x in Ioi (N:ℝ), F' x = 0 - F N := tendsto_nhds_unique hlim1 hlim2
  have hsplit : ∫ x in Ioi (N:ℝ), F' x = -(∫ x in Ioi (N:ℝ), g1 x) - (s+1)/2 * Jint N s := by
    simp only [hF']
    rw [integral_sub (f := fun x => -g1 x) (g := fun x => (s+1)/2 * g2 x) hg1i.neg
      (hg2i.const_mul _), integral_neg, MeasureTheory.integral_const_mul]
    rfl
  have htail : tailI N s = ∫ x in Ioi (N:ℝ), g1 x := by
    rw [tailI]; refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := hNr.trans hx
    simp only [hg1]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]; congr 2; ring
  have hFN : F N = (N:ℂ)^(-s-1) / 12 := by
    simp only [hF]; rw [P2_natCast]; push_cast; ring
  rw [htail]
  rw [hsplit, hFN] at hIoi
  linear_combination -hIoi

/-! ### The approximate formula (step L3) -/

lemma sum_range_one_div_cpow {s : ℂ} (hs : s ≠ 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
  have hr : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hr, Finset.sum_insert (by simp)]
  rw [Nat.cast_zero, Complex.zero_cpow hs, div_zero, zero_add]
  exact Finset.sum_congr rfl fun n _ => by rw [one_div, Complex.cpow_neg]

/-- **Exact second-order Euler–Maclaurin identity for ζ**, valid for `Re s > 0`, `s ≠ 1`. -/
theorem zeta_approx_exact {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (1 - s)
      - (N : ℂ) ^ (-s) / 2 + s * (N : ℂ) ^ (-s - 1) / 12 - s * (s + 1) / 2 * Jint N s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have ht := tail_ibp hN hs
  rw [tailI] at ht
  rw [← Zeta0EqZeta hN hs hs1, riemannZeta0, ht, sum_range_one_div_cpow hs0]
  ring

/-- **Step L3 (explicit form).** For `Re s = σ > 0`, `s ≠ 1`, `|Im s| ≤ π N`:
`|ζ(s) − Σ_{n≤N} n^{-s} + N^{1-s}/(1-s)| ≤ N^{-σ} (1 / 2 + |s|/(12N) + |s||s+1|/(6π N²))`. -/
theorem zeta_approx_error {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (ht : |s.im| ≤ π * N) :
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (1 - s)‖
      ≤ (N : ℝ) ^ (-s.re) * (1 / 2 + ‖s‖ / (12 * N) + ‖s‖ * ‖s + 1‖ / (6 * π * N ^ 2)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  rw [zeta_approx_exact hN hs hs1]
  have e : (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (1 - s)
      - (N : ℂ) ^ (-s) / 2 + s * (N : ℂ) ^ (-s - 1) / 12 - s * (s + 1) / 2 * Jint N s
      - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (1 - s)
      = -((N : ℂ) ^ (-s) / 2) + s * (N : ℂ) ^ (-s - 1) / 12 - s * (s + 1) / 2 * Jint N s := by ring
  rw [e]
  have hJ := Jint_bound hNr hs.le ht
  have n1 : ‖(N : ℂ) ^ (-s)‖ = (N:ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hN]; simp
  have n2 : ‖(N : ℂ) ^ (-s - 1)‖ = (N:ℝ) ^ (-s.re) / N := by
    rw [Complex.norm_natCast_cpow_of_pos hN]
    rw [show (-s-1).re = -s.re - 1 by simp, Real.rpow_sub hNr, Real.rpow_one]
  have n3 : (N:ℝ) ^ (-s.re-2) = (N:ℝ) ^ (-s.re) / N ^ 2 := by
    rw [Real.rpow_sub hNr, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [n3] at hJ
  have hP : 0 < (N:ℝ) ^ (-s.re) := by positivity
  calc ‖-((N : ℂ) ^ (-s) / 2) + s * (N : ℂ) ^ (-s - 1) / 12 - s * (s + 1) / 2 * Jint N s‖
      ≤ ‖-((N : ℂ) ^ (-s) / 2)‖ + ‖s * (N : ℂ) ^ (-s - 1) / 12‖ + ‖s * (s + 1) / 2 * Jint N s‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ = (N:ℝ) ^ (-s.re) / 2 + ‖s‖ * ((N:ℝ) ^ (-s.re) / N) / 12
          + ‖s‖ * ‖s + 1‖ / 2 * ‖Jint N s‖ := by
        rw [norm_neg, norm_div, n1, norm_div, norm_mul, n2, norm_mul, norm_div, norm_mul]
        norm_num
    _ ≤ (N:ℝ) ^ (-s.re) / 2 + ‖s‖ * ((N:ℝ) ^ (-s.re) / N) / 12
          + ‖s‖ * ‖s + 1‖ / 2 * ((N:ℝ) ^ (-s.re) / N ^ 2 / (3 * π)) := by gcongr
    _ = (N : ℝ) ^ (-s.re) * (1 / 2 + ‖s‖ / (12 * N) + ‖s‖ * ‖s + 1‖ / (6 * π * N ^ 2)) := by
        field_simp; ring

/-- **Step L3 (uniform form).** For `0 < σ ≤ 2`, `|t| ≤ π N`, `s ≠ 1`:
`|ζ(s) − Σ_{n≤N} n^{-s} + N^{1-s}/(1-s)| ≤ 4 N^{-σ}`. -/
@[blueprint
  "zd-zeta-approx"
  (title := "Approximate formula for zeta (crude form)")
  (statement := /--
    For $0<\Re s\le 2$, $s\ne 1$, $N\ge 1$ and $|\Im s|\le\pi N$,
    $$\Bigl|\zeta(s)-\sum_{n\le N}n^{-s}-\frac{N^{1-s}}{s-1}\Bigr|\le 4N^{-\Re s}.$$
  -/)]
theorem zeta_approx_uniform {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) (hs2 : s.re ≤ 2)
    (hs1 : s ≠ 1) (ht : |s.im| ≤ π * N) :
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (1 - s)‖
      ≤ 4 * (N : ℝ) ^ (-s.re) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  refine (zeta_approx_error hN hs hs1 ht).trans ?_
  rw [mul_comm 4]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hsn : ‖s‖ ≤ 6 * N := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_pos hs]; nlinarith
  have hs1n : ‖s + 1‖ ≤ 7 * N := by
    refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  have h1 : ‖s‖ / (12 * N) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h2 : ‖s‖ * ‖s + 1‖ / (6 * π * N ^ 2) ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have : ‖s‖ * ‖s + 1‖ ≤ (6 * N) * (7 * N) :=
      mul_le_mul hsn hs1n (norm_nonneg _) (by positivity)
    nlinarith [sq_nonneg (N:ℝ)]
  linarith

end ZeroDensity
