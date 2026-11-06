import RSBounds.BacklundRightArc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Rational certificates for cosine lower bounds and real zeta upper bounds. -/

open Real Complex Finset MeasureTheory
open TernaryGoldbach.RSBounds.CenterNumerics

namespace TernaryGoldbach.RSBounds.BacklundRightArc

def cosDoubleCheck (D : ℕ) (a : ℤ) : List ℤ → Bool
  | [] => true
  | b :: bs => decide (0 ≤ a ∧ b * D ≤ 2 * a ^ 2 - (D : ℤ) ^ 2) && cosDoubleCheck D b bs

def cosEnd (a : ℤ) : List ℤ → ℤ
  | [] => a
  | b :: bs => cosEnd b bs

lemma cosDoubleCheck_sound {D : ℕ} (hD : 0 < D) {a : ℤ} {θ : ℝ} {bs : List ℤ}
    (ha : (a : ℝ) / D ≤ Real.cos θ) (hc : cosDoubleCheck D a bs = true) :
    ((cosEnd a bs : ℤ) : ℝ) / D ≤ Real.cos ((2 : ℝ) ^ bs.length * θ) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  induction bs generalizing a θ with
  | nil => simpa [cosEnd] using ha
  | cons b bs ih =>
    simp only [cosDoubleCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast hc.1.1
    have hb : (b : ℝ) * D ≤ 2 * (a : ℝ) ^ 2 - (D : ℝ) ^ 2 := by exact_mod_cast hc.1.2
    have hb' : (b : ℝ) / D ≤ 2 * ((a : ℝ) / D) ^ 2 - 1 := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hD0)).mp
      convert hb using 1 <;> field_simp [hD0.ne'] <;> ring
    have hnext : (b : ℝ) / D ≤ Real.cos (2 * θ) := by
      rw [Real.cos_two_mul]
      have hsq : ((a : ℝ) / D) ^ 2 ≤ Real.cos θ ^ 2 :=
        pow_le_pow_left₀ (div_nonneg ha0 hD0.le) ha 2
      linarith
    have hh := ih hnext hc.2
    simpa only [cosEnd, List.length_cons, pow_succ, mul_assoc] using hh

lemma cos_initial_lower {θ X c : ℝ} (hθ : 0 ≤ θ) (hθX : θ ≤ X)
    (hc : c ≤ 1 - X ^ 2 / 2) : c ≤ Real.cos θ := by
  have hs : θ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hθ hθX 2
  linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]

lemma sigma_sample_lower_of_cos_cert {i p : ℕ} {a : ℤ} {bs : List ℤ}
    (hlen : bs.length = 8) (hc : cosDoubleCheck 1000000000000 a bs = true)
    (hinit : (a : ℝ) / 1000000000000 ≤
      1 - ((3.141593 : ℝ) * i / 8192) ^ 2 / 2)
    (hfinal : (p : ℝ) / 64 ≤ 5 / 4 + (33 / 25) *
      ((cosEnd a bs : ℤ) : ℝ) / 1000000000000) :
    (p : ℝ) / 64 ≤ 5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * i) := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hθ : Real.pi * i / 8192 ≤ (3.141593 : ℝ) * i / 8192 := by
    gcongr
    exact Real.pi_lt_d6.le
  have hs := cos_initial_lower (show 0 ≤ Real.pi * i / 8192 by positivity) hθ hinit
  have he := cosDoubleCheck_sound (by norm_num : 0 < 1000000000000) hs hc
  rw [hlen, show (2 : ℝ) ^ 8 * (Real.pi * i / 8192) = Real.pi / 32 * i by ring] at he
  nlinarith

/-- Turn finite integer root checks and the integral-test tail into a
logarithmic zeta bound. The final comparison is against a positive Taylor
polynomial for the exponential, so no floating-point evaluation is trusted. -/
lemma logZeta_le_of_root_cert {p : ℕ} (hp : 64 < p) {bs : List ℕ}
    (hlen : bs.length = 16) (hc : rootCheck p 64 100000000 1 bs = true)
    {bTail : ℕ} (hTail : 100000000 ^ 64 ≤ bTail ^ 64 * 16 ^ (p - 64))
    {B : ℝ} (hB : 0 ≤ B)
    (hnum : ((bs.sum + 16 : ℕ) : ℝ) / 100000000 +
      ((bTail : ℝ) / 100000000) / ((p : ℝ) / 64 - 1) ≤
      ∑ i ∈ Finset.range 16, B ^ i / (i.factorial : ℝ)) :
    logZeta ((p : ℝ) / 64) ≤ B := by
  have hpR : (64 : ℝ) < p := by exact_mod_cast hp
  have hs : 1 < (p : ℝ) / 64 := by linarith
  have hpart := (rootCheck_sound (by norm_num : 0 < 1) (by norm_num : 0 < 64)
    (by norm_num : 0 < 100000000) hc).2
  rw [hlen] at hpart
  have ht := zeta_tail_upper hs (N := 16) (by norm_num)
  have hroot := root_upper (n := 16) (p := p - 64) (k := 64)
    (D := 100000000) (b := bTail) (by norm_num) (by norm_num) (by norm_num) hTail
  have he : 1 - (p : ℝ) / 64 = -((p - 64 : ℕ) : ℝ) / 64 := by
    rw [Nat.cast_sub hp.le]
    push_cast
    ring
  rw [he] at ht
  have hz : ‖riemannZeta (((p : ℝ) / 64 : ℝ) : ℂ)‖ ≤ Real.exp B := by
    refine ht.trans ((add_le_add hpart (div_le_div_of_nonneg_right hroot (by linarith))).trans ?_)
    exact hnum.trans (Real.sum_le_exp_of_nonneg hB 16)
  unfold logZeta
  have hn : 0 < ‖riemannZeta (((p : ℝ) / 64 : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hs))
  simpa only [Real.log_exp] using Real.log_le_log hn hz

end TernaryGoldbach.RSBounds.BacklundRightArc
