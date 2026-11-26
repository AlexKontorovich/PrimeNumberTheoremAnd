module

public import HardyFirstZero.BoxSupport
public import HardyTenZeros.PhaseShort

@[expose] public section

/-!
# Any truncation, any short bracket: the support for the ten intervals (hunt `hardy_ten_zeros`)

`HardyFirstZero/BoxSupport.lean` instantiates the order-4 remainder at `N = 30` with two
crude steps, `‖z‖ ≤ |Re z| + |Im z|` and `29^{-1/2} ≤ 1/5`. Here the instantiation takes
any truncation `N` and is sharper:

* `norm_P4_sOf_sq`: `‖s(s+1)(s+2)(s+3)‖² = Π_{j<4} ((j + 1/2)² + t²)` on the critical line,
  an exact rational at a rational height, so any rational `R` with `Π ≤ R²` bounds the
  norm (worth a factor of about 1.16 at `t = 50` against the triangle inequality);
* `emN_bound`: the remainder at truncation `N` is at most `R / ((N-1)³ r (7/2) 720)` for any
  rational `r > 0` with `r² ≤ N - 1`;
* `mainBox`, `cBox_contains`, `zeta_mem_mainBox`: the main term as a box built from a table
  of term boxes, and the inflated box containing `ζ(1/2 + it)`;
* `zero_of_tables`: everything one interval needs, the sign test of
  `HardyFirstZero/Spine.lean`, the phase lemma `gammaR_re_pos_short`, the two boxes and one
  interval product, in one statement whose remaining hypotheses are rational arithmetic.
-/

open Complex Finset ZetaLean ZetaLean.ComplexInterval HardyFirstZero
open scoped ComplexConjugate

namespace HardyTenZeros

/-- `Π_{j<4} ((j + 1/2)² + t²)`, the squared norm of `s(s+1)(s+2)(s+3)` at `s = 1/2 + it`. -/
noncomputable def q4 (t : ℝ) : ℝ :=
  ((1 / 2) ^ 2 + t ^ 2) * ((3 / 2) ^ 2 + t ^ 2) * ((5 / 2) ^ 2 + t ^ 2) * ((7 / 2) ^ 2 + t ^ 2)

/-- The same polynomial over `ℚ`, for the generated side conditions. -/
def q4Q (t : ℚ) : ℚ :=
  ((1 / 2) ^ 2 + t ^ 2) * ((3 / 2) ^ 2 + t ^ 2) * ((5 / 2) ^ 2 + t ^ 2) * ((7 / 2) ^ 2 + t ^ 2)

lemma q4_cast (t : ℚ) : q4 (t : ℝ) = ((q4Q t : ℚ) : ℝ) := by
  unfold q4 q4Q; push_cast; ring

private lemma normSq_sOf_add (t j : ℝ) : ‖sOf t + j‖ ^ 2 = (1 / 2 + j) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [sOf]
  ring

/-- `‖P4 (1/2 + it)‖² = q4 t`. -/
lemma norm_P4_sOf_sq (t : ℝ) : ‖P4 (sOf t)‖ ^ 2 = q4 t := by
  have h0 := normSq_sOf_add t 0
  have h1 := normSq_sOf_add t 1
  have h2 := normSq_sOf_add t 2
  have h3 := normSq_sOf_add t 3
  simp only [Complex.ofReal_zero, add_zero, Complex.ofReal_one] at h0 h1
  have e2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have e3 : ((3 : ℝ) : ℂ) = (3 : ℂ) := by norm_num
  rw [e2] at h2
  rw [e3] at h3
  unfold P4 q4
  rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, h0, h1, h2, h3]
  ring

lemma norm_P4_le {t R : ℝ} (hR0 : 0 ≤ R) (hR : q4 t ≤ R ^ 2) : ‖P4 (sOf t)‖ ≤ R := by
  have h := norm_P4_sOf_sq t
  by_contra hc
  push Not at hc
  have : R ^ 2 < ‖P4 (sOf t)‖ ^ 2 := by
    have := norm_nonneg (P4 (sOf t))
    nlinarith
  linarith

/-- **The remainder at any truncation `N` on the critical line.** -/
theorem emN_bound {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 2 ≤ N) {r R : ℝ} (hr : 0 < r)
    (hr2 : r ^ 2 ≤ (N : ℝ) - 1) (hR0 : 0 ≤ R) (hR : q4 t ≤ R ^ 2) :
    ‖riemannZeta (sOf t) - (∑ i ∈ range N, (i : ℂ) ^ (-sOf t) + (N : ℂ) ^ (1 - sOf t)
        / (sOf t - 1) + (N : ℂ) ^ (-sOf t) / 2 + sOf t / 12 * (N : ℂ) ^ (-sOf t - 1))‖
      ≤ R / (((N : ℝ) - 1) ^ 3 * r * (7 / 2) * 720) := by
  have hQP : sOf t ∈ QP := ⟨by simp [sOf], by simp [sOf, ht]⟩
  refine (zeta_em4_error hQP hN).trans ?_
  rw [sOf_re]
  have hP := norm_P4_le hR0 hR
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set x : ℝ := (N : ℝ) - 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hx0 : 0 < x := by linarith
  have hpow : x ^ (-(1 / 2 : ℝ) - 3) ≤ 1 / (x ^ 3 * r) := by
    rw [show (-(1 / 2 : ℝ) - 3) = -(1 / 2) + (-3 : ℝ) by ring,
      Real.rpow_add hx0, Real.rpow_neg hx0.le, Real.rpow_neg hx0.le,
      ← Real.sqrt_eq_rpow, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hs : r ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hr2
    have hs0 : 0 < Real.sqrt x := lt_of_lt_of_le hr hs
    rw [one_div, mul_inv, mul_comm]
    gcongr
  have hnn : 0 ≤ x ^ (-(1 / 2 : ℝ) - 3) := Real.rpow_nonneg hx0.le _
  calc ‖P4 (sOf t)‖ * (x ^ (-(1 / 2 : ℝ) - 3) / (1 / 2 + 3)) / 720
      ≤ R * ((1 / (x ^ 3 * r)) / (1 / 2 + 3)) / 720 :=
        div_le_div_of_nonneg_right (mul_le_mul hP
          (div_le_div_of_nonneg_right hpow (by norm_num)) (by positivity) hR0) (by norm_num)
    _ = R / (x ^ 3 * r * (7 / 2) * 720) := by
        have : x ^ 3 * r ≠ 0 := by positivity
        field_simp
        ring

/-! ### Composite terms from their factors

`n^{-s}` is multiplicative over the naturals (`Complex.natCast_mul_natCast_cpow`), so a
composite term box is the coarsened product of its factors' boxes and needs no exp tower
of its own. The lab proved this as `ZetaLean.ComplexInterval.contains_cpow_mul_coarsen` in
`lean/ZetaLean/DHCertSupport.lean`; it is restated here so that this hunt does not import
that module's dependency chain. -/

theorem contains_cpow_mul_coarsen (p : ℕ) {a b : ℕ} {A B : ComplexInterval} {s : ℂ}
    (hA : A.contains ((a : ℂ) ^ (-s))) (hB : B.contains ((b : ℂ) ^ (-s))) :
    ((A.mul B).coarsen p).contains (((a * b : ℕ) : ℂ) ^ (-s)) := by
  have h := contains_mul hA hB
  rw [show (((a * b : ℕ) : ℂ) ^ (-s)) = ((a : ℂ) ^ (-s)) * ((b : ℂ) ^ (-s)) by
    rw [Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow a b (-s)]
  exact contains_coarsen p h

/-- The first term, `1^{-s} = 1`, exactly. -/
theorem contains_one_cpow (s : ℂ) :
    (ComplexInterval.exact 1 0).contains (((1 : ℕ) : ℂ) ^ (-s)) := by
  have h := contains_exact 1 0
  rw [Nat.cast_one, Complex.one_cpow]
  convert h using 1
  apply Complex.ext <;> simp

/-! ### The main term as a box -/

/-- Real part of `c_N(s) = N/(s-1) + 1/2 + s/(12N)` at `s = 1/2 + it`. -/
def cRe (N : ℕ) (t : ℚ) : ℚ := N * (-1 / 2) / (1 / 4 + t ^ 2) + 1 / 2 + (1 / 2) / (12 * N)

/-- Imaginary part of `c_N(s)` at `s = 1/2 + it`. -/
def cIm (N : ℕ) (t : ℚ) : ℚ := -(N * t) / (1 / 4 + t ^ 2) + t / (12 * N)

theorem cBox_contains {N : ℕ} (hN : N ≠ 0) (t : ℚ) :
    (ComplexInterval.exact (cRe N t) (cIm N t)).contains
      ((N : ℂ) / (sOf (t : ℝ) - 1) + 1 / 2 + sOf (t : ℝ) / (12 * N)) := by
  have h := contains_exact (cRe N t) (cIm N t)
  set u : ℂ := ((t : ℚ) : ℂ) with hu
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hsu : sOf (t : ℝ) = 1 / 2 + u * I := by simp [sOf, hu]
  have hd : (1 / 4 + u ^ 2 : ℂ) ≠ 0 := by
    have h0 : (1 / 4 + t ^ 2 : ℚ) ≠ 0 := by positivity
    have h1 : (((1 / 4 + t ^ 2 : ℚ)) : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr h0
    rw [hu]; push_cast at h1; exact h1
  have hs1 : (1 / 2 + u * I - 1 : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hu] at this
    norm_num at this
  have key : (N : ℂ) / (1 / 2 + u * I - 1) = (N : ℂ) * (-1 / 2 - u * I) / (1 / 4 + u ^ 2) := by
    rw [div_eq_div_iff hs1 hd]
    linear_combination (N : ℂ) * u ^ 2 * I_sq
  have hz : (⟨((cRe N t : ℚ) : ℝ), ((cIm N t : ℚ) : ℝ)⟩ : ℂ)
      = ((cRe N t : ℚ) : ℂ) + ((cIm N t : ℚ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hsu, key]
  convert h using 1
  rw [hz]
  unfold cRe cIm
  push_cast
  rw [← hu]
  field_simp
  ring

/-- The rectangle for the order-4 main term at `s = 1/2 + it`, from a table of term boxes. -/
def mainBox (T : ℕ → ComplexInterval) (N : ℕ) (t : ℚ) : ComplexInterval :=
  (sumBoxes T N).add ((T N).mul (ComplexInterval.exact (cRe N t) (cIm N t)))

/-- The inflated main-term box contains `ζ(1/2 + it)`. -/
theorem zeta_mem_mainBox {t : ℚ} (ht : 0 < t) {N : ℕ} (hN : 2 ≤ N) {T : ℕ → ComplexInterval}
    (hT : ∀ m < N + 1, (T m).contains ((m : ℂ) ^ (-sOf (t : ℝ))))
    {r R e : ℚ} (hr : 0 < r) (hr2 : r ^ 2 ≤ N - 1) (hR0 : 0 ≤ R) (hR : q4Q t ≤ R ^ 2)
    (he : R / (((N : ℚ) - 1) ^ 3 * r * (7 / 2) * 720) ≤ e) :
    ((mainBox T N t).inflate e).contains (riemannZeta (sOf (t : ℝ))) := by
  set s := sOf (t : ℝ)
  have hM : (mainBox T N t).contains (∑ i ∈ range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
      + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)) := by
    rw [main_eq s (by omega)]
    exact contains_add (contains_sumBoxes fun m hm => hT m (by omega))
      (contains_mul (hT N (by omega)) (cBox_contains (by omega) t))
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr2' : (r : ℝ) ^ 2 ≤ (N : ℝ) - 1 := by exact_mod_cast hr2
  have hR0' : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR0
  have hR' : q4 (t : ℝ) ≤ (R : ℝ) ^ 2 := by rw [q4_cast]; exact_mod_cast hR
  have he' : (R : ℝ) / (((N : ℝ) - 1) ^ 3 * r * (7 / 2) * 720) ≤ (e : ℝ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr he
    push_cast at h1
    exact h1
  exact contains_inflate hM ((emN_bound ht' hN hr' hr2' hR0' hR').trans he')

/-- The upper end of the interval product for `Re(z_a · conj z_b)` over two boxes. -/
def prodHi (A B : ComplexInterval) : ℚ :=
  ((A.re.mul B.re).add (A.im.mul B.im)).hi

/-- **One interval, from its two tables.** Everything a short bracket below height 50
needs: the term tables at both ends, the radius side conditions (rational arithmetic),
and a negative upper end of the interval product. -/
theorem zero_of_tables {a b : ℚ} (ha : 0 < a) (hab : a < b) (hw : b - a ≤ 1 / 100)
    (hb : b ≤ 50) {Na Nb : ℕ} (hNa : 2 ≤ Na) (hNb : 2 ≤ Nb) {TA TB : ℕ → ComplexInterval}
    (hTA : ∀ m < Na + 1, (TA m).contains ((m : ℂ) ^ (-sOf (a : ℝ))))
    (hTB : ∀ m < Nb + 1, (TB m).contains ((m : ℂ) ^ (-sOf (b : ℝ))))
    {ra Ra ea rb Rb eb : ℚ}
    (hra : 0 < ra) (hra2 : ra ^ 2 ≤ Na - 1) (hRa0 : 0 ≤ Ra) (hRa : q4Q a ≤ Ra ^ 2)
    (hea : Ra / (((Na : ℚ) - 1) ^ 3 * ra * (7 / 2) * 720) ≤ ea)
    (hrb : 0 < rb) (hrb2 : rb ^ 2 ≤ Nb - 1) (hRb0 : 0 ≤ Rb) (hRb : q4Q b ≤ Rb ^ 2)
    (heb : Rb / (((Nb : ℚ) - 1) ^ 3 * rb * (7 / 2) * 720) ≤ eb)
    (hneg : prodHi ((mainBox TA Na a).inflate ea) ((mainBox TB Nb b).inflate eb) < 0) :
    ∃ t ∈ Set.Ioo (a : ℝ) b, riemannZeta (1 / 2 + t * I) = 0 := by
  have hA := zeta_mem_mainBox ha hNa hTA hra hra2 hRa0 hRa hea
  have hB := zeta_mem_mainBox (ha.trans hab) hNb hTB hrb hrb2 hRb0 hRb heb
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hw' : (b : ℝ) - a ≤ 1 / 100 := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr hw
    push_cast at h1
    exact h1
  have hb' : (b : ℝ) ≤ 50 := by exact_mod_cast hb
  refine exists_zero_of_sign_data hab' ?_ (gammaR_re_pos_short ha' hab'.le hw' hb')
  set z := riemannZeta (sOf (a : ℝ))
  set w := riemannZeta (sOf (b : ℝ))
  have hre : (z * conj w).re = z.re * w.re + z.im * w.im := by
    simp [Complex.mul_re]
  have hc := Interval.contains_add (Interval.contains_mul hA.1 hB.1)
    (Interval.contains_mul hA.2 hB.2)
  rw [hre]
  have hneg' : (prodHi ((mainBox TA Na a).inflate ea) ((mainBox TB Nb b).inflate eb) : ℝ) < 0 := by
    exact_mod_cast hneg
  exact lt_of_le_of_lt hc.2 hneg'

end HardyTenZeros
