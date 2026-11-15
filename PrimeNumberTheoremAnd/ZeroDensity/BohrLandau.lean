/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZetaBounds

/-!
# Bohr–Landau reduction: N(σ,T) = O(T) for fixed σ > 1 / 2

Proved unconditionally here: the combination step (Littlewood-type integral
bound + mean square ⇒ N(σ,T) ≪ T). The two analytic inputs are explicit
named hypotheses (`LittlewoodBound`, `MeanSquareBound`), NOT proved.
-/

open MeasureTheory Set intervalIntegral

@[expose] public noncomputable section
namespace ZeroDensity

/-- Zeros of ζ with Re ≥ σ, 0 < Im ≤ T. -/
def zeroSet (σ T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- N(σ,T) (as a real; `ncard`, so 0 if infinite — finiteness is a hypothesis below). -/
def Nzeros (σ T : ℝ) : ℝ := ((zeroSet σ T).ncard : ℝ)

lemma zeroSet_anti {σ₁ σ₂ T : ℝ} (h : σ₁ ≤ σ₂) : zeroSet σ₂ T ⊆ zeroSet σ₁ T :=
  fun _ ⟨a, b, c, d⟩ => ⟨a, h.trans b, c, d⟩

lemma Nzeros_antitone {σ₀ T : ℝ} (hfin : (zeroSet σ₀ T).Finite) :
    AntitoneOn (fun u => Nzeros u T) (Ici σ₀) := by
  intro a ha b _ hab
  simp only [Nzeros]
  exact_mod_cast Set.ncard_le_ncard (zeroSet_anti hab) (hfin.subset (zeroSet_anti ha))

/-- HYPOTHESIS (Littlewood's lemma applied to ζ on [σ₀,2]×[0,T], with the
arg-terms and the Re s = 2 term absorbed in C log T). Not proved here. -/
def LittlewoodBound (σ₀ C : ℝ) : Prop :=
  ∀ T ≥ 2, (zeroSet σ₀ T).Finite ∧
    IntegrableOn (fun t : ℝ => Real.log ‖riemannZeta (σ₀ + t * Complex.I)‖) (Ioc 0 T) ∧
    (∫ u in σ₀..2, Nzeros u T) ≤
      (1 / (2 * Real.pi)) * (∫ t in (0:ℝ)..T, Real.log ‖riemannZeta (σ₀ + t * Complex.I)‖)
        + C * Real.log T

/-- Mean square of ζ on Re s = σ₀; proved for 1 / 2<σ₀<1 in `ZeroDensity.Tail` (`meanSquareBound`). -/
def MeanSquareBound (σ₀ C : ℝ) : Prop :=
  ∀ T ≥ 2, IntegrableOn (fun t : ℝ => ‖riemannZeta (σ₀ + t * Complex.I)‖ ^ 2) (Ioc 0 T) ∧
    (∫ t in (0:ℝ)..T, ‖riemannZeta (σ₀ + t * Complex.I)‖ ^ 2) ≤ C * T

lemma log_le_sq_half (x : ℝ) : Real.log x ≤ x ^ 2 / 2 := by
  rw [← Real.log_abs]
  rcases eq_or_lt_of_le (abs_nonneg x) with h | h
  · rw [← h]; simp only [Real.log_zero]; positivity
  · have h1 := Real.log_le_sub_one_of_pos h
    have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [sq_nonneg (|x| - 1)]

/-- **Bohr–Landau, conditional form.** Fix 1 / 2 < σ₀ < σ ≤ 2. Under the two
named analytic hypotheses at σ₀, N(σ,T) ≤ K·T for all T ≥ 2, with K explicit. -/
@[blueprint
  "zd-bohr-landau-hyps"
  (title := "Bohr--Landau from Littlewood and mean-square hypotheses")
  (statement := /--
    Let $\sigma_0<\sigma\le 2$. Assume Littlewood's lemma on the rectangle $[\sigma_0,2]\times[0,T]$
    (the hypothesis `LittlewoodBound`, with constant $C_1$) and
    $\int_0^T|\zeta(\sigma_0+it)|^2\,dt\le C_2 T$ for $T\ge 2$ (`MeanSquareBound`).
    Then for every $T\ge 2$,
    $$N(\sigma,T)\le\frac{C_2/(4\pi)+C_1}{\sigma-\sigma_0}\,T,$$
    where $N(\sigma,T)$ counts zeros of $\zeta$ with $\Re\rho\ge\sigma$ and $0<\Im\rho\le T$
    (without multiplicity).
  -/)]
theorem bohr_landau_of_hyps {σ₀ σ C₁ C₂ : ℝ} (hσ : σ₀ < σ) (hσ2 : σ ≤ 2)
    (hC₁ : 0 ≤ C₁) (hL : LittlewoodBound σ₀ C₁) (hM : MeanSquareBound σ₀ C₂) :
    ∀ T ≥ 2, Nzeros σ T ≤ ((C₂ / (4 * Real.pi) + C₁) / (σ - σ₀)) * T := by
  intro T hT
  obtain ⟨hfin, hlogint, hLit⟩ := hL T hT
  obtain ⟨hsqint, hsq⟩ := hM T hT
  have hanti := Nzeros_antitone (T := T) hfin
  have hnn : ∀ u, 0 ≤ Nzeros u T := fun u => by simp [Nzeros]
  have hint : ∀ a b, σ₀ ≤ a → a ≤ b → IntervalIntegrable (fun u => Nzeros u T) volume a b :=
    fun a b ha hab => (hanti.mono (by
        rw [uIcc_of_le hab]; exact Icc_subset_Ici_self.trans (Ici_subset_Ici.2 ha))
      |>.intervalIntegrable)
  -- (σ-σ₀) N(σ) ≤ ∫_{σ₀}^{σ} N ≤ ∫_{σ₀}^{2} N
  have step1 : (σ - σ₀) * Nzeros σ T ≤ ∫ u in σ₀..σ, Nzeros u T := by
    have := intervalIntegral.integral_mono_on hσ.le intervalIntegrable_const
      (hint σ₀ σ le_rfl hσ.le) (fun u hu => hanti (show σ₀ ≤ u from hu.1) (show σ₀ ≤ σ from hσ.le) hu.2)
    simpa [mul_comm] using this
  have step2 : (∫ u in σ₀..σ, Nzeros u T) ≤ ∫ u in σ₀..2, Nzeros u T := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint σ₀ σ le_rfl hσ.le)
      (hint σ 2 hσ.le hσ2)]
    have : 0 ≤ ∫ u in σ..2, Nzeros u T := intervalIntegral.integral_nonneg hσ2 (fun u _ => hnn u)
    linarith
  -- ∫ log|ζ| ≤ ½ ∫ |ζ|²
  have step3 : (∫ t in (0:ℝ)..T, Real.log ‖riemannZeta (σ₀ + t * Complex.I)‖) ≤
      (∫ t in (0:ℝ)..T, ‖riemannZeta (σ₀ + t * Complex.I)‖ ^ 2) / 2 := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2 hlogint
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2 hsqint).div_const _
    · intro t _; exact log_le_sq_half _
  have hpi : 0 < 2 * Real.pi := by positivity
  have hlogT : Real.log T ≤ T := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hd : 0 < σ - σ₀ := sub_pos.2 hσ
  have key : (σ - σ₀) * Nzeros σ T ≤ (C₂ / (4 * Real.pi) + C₁) * T := by
    have h4 : (1 / (2 * Real.pi)) * (∫ t in (0:ℝ)..T,
        Real.log ‖riemannZeta (σ₀ + t * Complex.I)‖) ≤ C₂ / (4 * Real.pi) * T := by
      calc _ ≤ (1 / (2 * Real.pi)) * ((C₂ * T) / 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        _ = _ := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hlogT hC₁]
  rw [div_mul_eq_mul_div, le_div_iff₀ hd]; linarith

end ZeroDensity
