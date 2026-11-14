/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZeroDensity.GaussMV
public import PrimeNumberTheoremAnd.ZeroDensity.MeanSquare

/-!
# The Euler–Maclaurin tail in mean square (discharges `TailMeanSquare`)
-/

open Complex MeasureTheory Set

@[expose] public noncomputable section
namespace ZeroDensity

/-- the tail integrand in the variable `u = log x`. -/
def tg (σ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  (Ioi (Real.log N)).indicator
    (fun u => (((⌊Real.exp u⌋ : ℤ) : ℂ) + 1 / 2 - (Real.exp u : ℂ)) * (Real.exp (-σ * u) : ℂ)) u

lemma norm_psi_le (y : ℝ) : ‖(((⌊y⌋ : ℤ) : ℂ) + 1 / 2 - (y : ℂ))‖ ≤ 1 / 2 := by
  have : (((⌊y⌋ : ℤ) : ℂ) + 1 / 2 - (y : ℂ)) = (((⌊y⌋ : ℝ) + 1 / 2 - y : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have h1 := Int.floor_le y; have h2 := Int.lt_floor_add_one y
  constructor <;> linarith

lemma tg_meas (σ : ℝ) : Measurable
    (fun u : ℝ => (((⌊Real.exp u⌋ : ℤ) : ℂ) + 1 / 2 - (Real.exp u : ℂ)) * (Real.exp (-σ * u) : ℂ)) := by
  have hf : Measurable fun u : ℝ => (((⌊Real.exp u⌋ : ℤ) : ℂ)) :=
    (measurable_of_countable _).comp (Int.measurable_floor.comp Real.continuous_exp.measurable)
  exact ((hf.add_const _).sub (by fun_prop)).mul (by fun_prop)

lemma norm_tg_le (σ : ℝ) (N : ℕ) (u : ℝ) :
    ‖tg σ N u‖ ≤ (Ioi (Real.log N)).indicator (fun u => 1 / 2 * Real.exp (-σ * u)) u := by
  unfold tg
  by_cases hu : u ∈ Ioi (Real.log N)
  · simp only [indicator_of_mem hu, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (norm_psi_le _) (Real.exp_pos _).le
  · simp [indicator_of_notMem hu]

lemma integrable_tg (σ : ℝ) (hσ : 0 < σ) (N : ℕ) : Integrable (tg σ N) := by
  have hb : Integrable ((Ioi (Real.log N)).indicator (fun u => 1 / 2 * Real.exp (-σ * u))) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_exp_mul_Ioi (by linarith) _).const_mul _
  refine hb.mono' ?_ (Filter.Eventually.of_forall (norm_tg_le σ N))
  exact ((tg_meas σ).indicator measurableSet_Ioi).aestronglyMeasurable

lemma integral_norm_tg_sq (σ : ℝ) (hσ : 0 < σ) (N : ℕ) (hN : 0 < N) :
    Integrable (fun u => ‖tg σ N u‖ ^ 2) ∧
      ∫ u, ‖tg σ N u‖ ^ 2 ≤ (N : ℝ) ^ (-2 * σ) / (8 * σ) := by
  set b := (Ioi (Real.log N)).indicator (fun u => 1 / 4 * Real.exp ((-2 * σ) * u)) with hb_def
  have hbI : Integrable b := by
    rw [hb_def, integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_exp_mul_Ioi (by linarith) _).const_mul _
  have hle : ∀ u, ‖tg σ N u‖ ^ 2 ≤ b u := by
    intro u
    have h := norm_tg_le σ N u
    by_cases hu : u ∈ Ioi (Real.log N)
    · rw [indicator_of_mem hu] at h
      rw [hb_def, indicator_of_mem hu]
      have e : Real.exp ((-2 * σ) * u) = Real.exp (-σ * u) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [e]
      have := norm_nonneg (tg σ N u)
      nlinarith
    · rw [indicator_of_notMem hu] at h
      have : ‖tg σ N u‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [this, hb_def, indicator_of_notMem hu]; simp
  have hI : Integrable (fun u => ‖tg σ N u‖ ^ 2) :=
    hbI.mono' ((integrable_tg σ hσ N).aestronglyMeasurable.norm.pow 2)
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hle u)
  refine ⟨hI, (integral_mono hI hbI hle).trans (le_of_eq ?_)⟩
  rw [hb_def, integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (by linarith)]
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hN']
  field_simp
  ring_nf

lemma tailI_eq_FT (σ : ℝ) (N : ℕ) (hN : 0 < N) (t : ℝ) :
    tailI N (sl σ t) = FT (tg σ N) t := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  unfold tailI FT tg
  rw [← Real.exp_log hN', ← integral_comp_exp_Ioi, Real.exp_log hN']
  rw [← integral_indicator measurableSet_Ioi]
  congr 1; ext u
  by_cases hu : u ∈ Ioi (Real.log N)
  swap; · simp [indicator_of_notMem hu]
  rw [indicator_of_mem hu, indicator_of_mem hu]
  have hc : ((Real.exp u : ℝ) : ℂ) ^ (sl σ t + 1) = cexp (u * (sl σ t + 1)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  rw [real_smul, hc, Complex.ofReal_exp, Complex.ofReal_exp, div_eq_mul_inv, ← Complex.exp_neg]
  have : cexp (u:ℂ) * cexp (-(u * (sl σ t + 1))) = cexp ((((-σ * u) : ℝ)) : ℂ) * cexp (-((t:ℂ) * u * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; simp only [sl]; push_cast; ring
  calc (cexp (u:ℂ)) * ((((⌊Real.exp u⌋ : ℤ) : ℂ) + 1 / 2 - cexp (u:ℂ)) * cexp (-(u * (sl σ t + 1))))
      = ((((⌊Real.exp u⌋ : ℤ) : ℂ) + 1 / 2 - cexp (u:ℂ))) * (cexp (u:ℂ) * cexp (-(u * (sl σ t + 1)))) := by ring
    _ = _ := by rw [this]; ring

/-- **`TailMeanSquare` holds** for every `σ > 0`, with `K = 2πe/(8σ)`. -/
theorem tailMeanSquare (σ : ℝ) (hσ : 0 < σ) :
    TailMeanSquare σ (2 * Real.pi * Real.exp 1 / (8 * σ)) := by
  intro N hN T hT
  have ⟨hI, hle⟩ := integral_norm_tg_sq σ hσ N hN
  have h := mean_value_FT (tg σ N) (integrable_tg σ hσ N) hI T hT
  simp_rw [tailI_eq_FT σ N hN]
  calc _ ≤ _ := h
    _ ≤ 2 * Real.pi * Real.exp 1 * ((N : ℝ) ^ (-2 * σ) / (8 * σ)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by ring

/-- **Unconditional mean square bound** for `1 / 2 < σ < 1`. -/
@[blueprint
  "zd-mean-square"
  (title := "Mean square of zeta")
  (statement := /--
    For $1/2<\sigma<1$ there is a constant $C=C(\sigma)$ such that
    $\int_0^T|\zeta(\sigma+it)|^2\,dt\le C T$ for all $T\ge 2$.
  -/)]
theorem meanSquareBound (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) : ∃ C, MeanSquareBound σ C :=
  meanSquareBound_of_tail hσ hσ1 (tailMeanSquare σ (by linarith))

/-- **Bohr–Landau, conditional only on the Littlewood bound**: for `1 / 2 < σ₀ < σ ≤ 2`,
`N(σ,T) = O(T)`. -/
theorem bohr_landau_of_littlewood {σ₀ σ C₁ : ℝ} (h1 : 1 / 2 < σ₀) (h2 : σ₀ < 1)
    (hσ : σ₀ < σ) (hσ2 : σ ≤ 2) (hC₁ : 0 ≤ C₁) (hL : LittlewoodBound σ₀ C₁) :
    ∃ A, ∀ T ≥ 2, Nzeros σ T ≤ A * T := by
  obtain ⟨C₂, hM⟩ := meanSquareBound σ₀ h1 h2
  exact ⟨_, bohr_landau_of_hyps hσ hσ2 hC₁ hL hM⟩

end ZeroDensity

