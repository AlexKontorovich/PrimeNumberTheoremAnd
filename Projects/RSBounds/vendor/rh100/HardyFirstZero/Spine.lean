module

public import ZetaLean.HardyZ

@[expose] public section

open RH100HardyZ

/-!
# The sign test behind the first zero (hunt `hardy_first_zero`)

The reduction this hunt's Lean plan rests on, kernel-checked: a zero of `ζ` on
the critical line between `a` and `b` follows from two inequalities, and neither
of them asks for the value of the Riemann-Siegel phase.

* `hX`: `Re (ζ(1/2 + ia) · conj ζ(1/2 + ib)) < 0`, a statement about two values
  of `ζ` that an Euler-Maclaurin enclosure can decide;
* `hG`: `0 < Re (Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib))`, which says only that the
  phase of `Γℝ` turns by less than a quarter turn between `a` and `b`.

Why that suffices: `hardyZ t = Λ(1/2 + it) / d(t)` with `d(t) > 0`
(`ZetaLean/HardyZ.lean`), and `Λ = ζ · Γℝ` off the poles, so
`Z(a) Z(b) d(a) d(b) = X G` with `X` and `G` the two products above. The left
side is real, so multiplying by `conj X` and taking real parts gives
`Z(a) Z(b) d(a) d(b) Re X = ‖X‖² Re G > 0`, hence `Z(a) Z(b) < 0`, and the
intermediate value theorem on the continuous real `hardyZReal` finishes.

Nothing here is numerical. The two hypotheses are the open work: `hX` needs an
evaluation of `ζ` with a proved error bound, `hG` a crude bound on the phase
of `Γ` (`RESULTS.md`, routes E and P).
-/

open Complex
open scoped ComplexConjugate

namespace HardyFirstZero

/-- The critical-line point `1/2 + it`. -/
noncomputable abbrev sOf (t : ℝ) : ℂ := 1 / 2 + t * I

lemma sOf_re (t : ℝ) : (sOf t).re = 1 / 2 := by simp [sOf]

lemma sOf_ne_zero (t : ℝ) : sOf t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [sOf_re, Complex.zero_re] at this
  norm_num at this

/-- `Λ(1/2 + it) = ζ(1/2 + it) · Γℝ(1/2 + it)`. -/
lemma completed_eq (t : ℝ) :
    completedRiemannZeta (sOf t) = riemannZeta (sOf t) * Gammaℝ (sOf t) := by
  have hre : 0 < (sOf t).re := by rw [sOf_re]; norm_num
  rw [riemannZeta_def_of_ne_zero (sOf_ne_zero t)]
  exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hre)).symm

/-- The positive real denominator of `hardyZ`. -/
noncomputable def den (t : ℝ) : ℝ := Real.pi ^ (-(1 / 4 : ℝ)) * ‖Gamma (1 / 4 + t / 2 * I)‖

lemma den_pos (t : ℝ) : 0 < den t := by
  unfold den
  refine mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (norm_pos_iff.mpr ?_)
  apply Gamma_ne_zero_of_re_pos
  simp

lemma hardyZ_eq (t : ℝ) : hardyZ t = completedRiemannZeta (sOf t) / ((den t : ℝ) : ℂ) := by
  unfold hardyZ den sOf
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_cpow Real.pi_pos.le, Complex.ofReal_neg]

/-- `Z(a) Z(b) d(a) d(b) = (ζ_a conj ζ_b) (Γℝ_a conj Γℝ_b)`, as complex numbers. -/
lemma hardyZReal_mul (a b : ℝ) :
    ((hardyZReal a * hardyZReal b : ℝ) : ℂ) * ((den a * den b : ℝ) : ℂ)
      = (riemannZeta (sOf a) * conj (riemannZeta (sOf b)))
        * (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))) := by
  have hb : ((hardyZReal b : ℝ) : ℂ) = conj (hardyZ b) := by
    rw [← hardyZReal_eq_hardyZ b, Complex.conj_ofReal]
  have hda : ((den a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (den_pos a).ne'
  have hdb : ((den b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (den_pos b).ne'
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hb, hardyZReal_eq_hardyZ a, hardyZ_eq a,
    hardyZ_eq b, map_div₀, Complex.conj_ofReal, completed_eq a, completed_eq b, map_mul]
  field_simp

/-- The algebraic core: a real `P` with `P d = X G`, `d > 0`, `Re X < 0` and
`Re G > 0` is negative. -/
lemma neg_of_mul_eq {P d : ℝ} {X G : ℂ} (hd : 0 < d) (h : (P : ℂ) * (d : ℂ) = X * G)
    (hX : X.re < 0) (hG : 0 < G.re) : P < 0 := by
  have h2 : (P : ℂ) * (d : ℂ) * conj X = ((‖X‖ ^ 2 : ℝ) : ℂ) * G := by
    rw [h, Complex.ofReal_pow, ← Complex.mul_conj']
    ring
  have h3 := congrArg Complex.re h2
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, mul_zero, add_zero, sub_zero] at h3
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hX
    exact lt_irrefl 0 hX
  have hn : 0 < ‖X‖ ^ 2 := by positivity
  have hrhs : 0 < ‖X‖ ^ 2 * G.re := mul_pos hn hG
  -- `P d Re X > 0` with `d > 0` and `Re X < 0` forces `P < 0`
  by_contra hP
  replace hP := not_lt.mp hP
  have : P * d * X.re ≤ 0 := by
    have hPd : 0 ≤ P * d := mul_nonneg hP hd.le
    exact mul_nonpos_of_nonneg_of_nonpos hPd hX.le
  linarith

/-- **The sign test.** Two inequalities, one about `ζ` and one about `Γℝ`,
give a zero of `ζ` on the critical line strictly between `a` and `b`. -/
theorem exists_zero_of_sign_data {a b : ℝ} (hab : a < b)
    (hX : (riemannZeta (sOf a) * conj (riemannZeta (sOf b))).re < 0)
    (hG : 0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + t * I) = 0 := by
  have hP : hardyZReal a * hardyZReal b < 0 :=
    neg_of_mul_eq (mul_pos (den_pos a) (den_pos b)) (hardyZReal_mul a b) hX hG
  have hc : ContinuousOn hardyZReal (Set.Icc a b) := continuous_hardyZReal.continuousOn
  rcases mul_neg_iff.mp hP with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨t, ht, (hardyZReal_zero_iff t).mp h0⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨t, ht, (hardyZReal_zero_iff t).mp h0⟩

end HardyFirstZero
