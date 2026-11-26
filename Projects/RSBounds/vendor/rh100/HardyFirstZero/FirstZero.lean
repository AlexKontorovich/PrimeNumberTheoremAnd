module

public import HardyFirstZero.Boxes

@[expose] public section

/-!
# A zero of zeta on the critical line between 14.13 and 14.14 (hunt `hardy_first_zero`)

The assembly. `Boxes.lean` encloses every term `m^{-s}`, `1 ≤ m ≤ 30`, at the two
endpoints in a kernel-checked rational rectangle; `main_eq` regroups the order-4
main term around `30^{-s}`; `em30_bound` bounds the remainder; the rectangles,
inflated by that bound, contain `ζ(1/2 + 14.13i)` and `ζ(1/2 + 14.14i)`; one interval
product shows `Re(ζ_a · conj ζ_b) < 0`; and `first_zero_on_line_of_zeta_product`
(`Phase.lean`, which also carries the phase lemma) turns that into the zero.
-/

open Complex Finset ZetaLean ZetaLean.ComplexInterval
open scoped ComplexConjugate

namespace HardyFirstZero

set_option maxRecDepth 100000

/-- The rectangle for the order-4 main term at `t = 1413/100`. -/
def MA : ComplexInterval := (sumBoxes tA 30).add ((tA 30).mul cA)

/-- The rectangle for the order-4 main term at `t = 707/50`. -/
def MB : ComplexInterval := (sumBoxes tB 30).add ((tB 30).mul cB)

lemma cA_mem : cA.contains (((30 : ℕ) : ℂ) / (sOf ((1413 / 100 : ℚ) : ℝ) - 1) + 1 / 2
    + sOf ((1413 / 100 : ℚ) : ℝ) / (12 * ((30 : ℕ) : ℂ))) := by
  have h := contains_exact (613663909 / 1439329680 : ℚ) (-16642146167 / 7996276000 : ℚ)
  unfold cA
  convert h using 1
  apply Complex.ext <;>
    simp [sOf, Complex.div_re, Complex.div_im, Complex.normSq] <;> norm_num

lemma cB_mem : cB.contains (((30 : ℕ) : ℂ) / (sOf ((707 / 50 : ℚ) : ℝ) - 1) + 1 / 2
    + sOf ((707 / 50 : ℚ) : ℝ) / (12 * ((30 : ℕ) : ℂ))) := by
  have h := contains_exact (76835557 / 180170640 : ℚ) (-9367582441 / 4504266000 : ℚ)
  unfold cB
  convert h using 1
  apply Complex.ext <;>
    simp [sOf, Complex.div_re, Complex.div_im, Complex.normSq] <;> norm_num

/-- `ζ(1/2 + 14.13i)` lies in `MA` inflated by `epsA`. -/
theorem zetaA_mem : (MA.inflate epsA).contains (riemannZeta (sOf ((1413 / 100 : ℚ) : ℝ))) := by
  set s := sOf ((1413 / 100 : ℚ) : ℝ)
  have hM : MA.contains (∑ i ∈ range 30, (i : ℂ) ^ (-s) + ((30 : ℕ) : ℂ) ^ (1 - s) / (s - 1)
      + ((30 : ℕ) : ℂ) ^ (-s) / 2 + s / 12 * ((30 : ℕ) : ℂ) ^ (-s - 1)) := by
    rw [main_eq s (by norm_num)]
    exact contains_add (contains_sumBoxes fun m hm => tA_mem m (by omega))
      (contains_mul (tA_mem 30 (by norm_num)) cA_mem)
  refine contains_inflate hM ((em30_bound (T := 1413 / 100) (by norm_num) (by norm_num)).trans ?_)
  simp only [epsA]
  norm_num

/-- `ζ(1/2 + 14.14i)` lies in `MB` inflated by `epsB`. -/
theorem zetaB_mem : (MB.inflate epsB).contains (riemannZeta (sOf ((707 / 50 : ℚ) : ℝ))) := by
  set s := sOf ((707 / 50 : ℚ) : ℝ)
  have hM : MB.contains (∑ i ∈ range 30, (i : ℂ) ^ (-s) + ((30 : ℕ) : ℂ) ^ (1 - s) / (s - 1)
      + ((30 : ℕ) : ℂ) ^ (-s) / 2 + s / 12 * ((30 : ℕ) : ℂ) ^ (-s - 1)) := by
    rw [main_eq s (by norm_num)]
    exact contains_add (contains_sumBoxes fun m hm => tB_mem m (by omega))
      (contains_mul (tB_mem 30 (by norm_num)) cB_mem)
  refine contains_inflate hM ((em30_bound (T := 707 / 50) (by norm_num) (by norm_num)).trans ?_)
  simp only [epsB]
  norm_num

/-- The interval product decides the sign: its upper end is negative. -/
theorem product_hi_neg :
    (((MA.inflate epsA).re.mul (MB.inflate epsB).re).add
      ((MA.inflate epsA).im.mul (MB.inflate epsB).im)).hi < 0 := by
  decide +kernel

/-- **`hX` at the planned endpoints**: `Re(ζ(1/2 + 14.13i) · conj ζ(1/2 + 14.14i)) < 0`. -/
theorem zeta_product_re_neg :
    (riemannZeta (sOf (1413 / 100)) * conj (riemannZeta (sOf (707 / 50)))).re < 0 := by
  have ha : ((1413 / 100 : ℚ) : ℝ) = 1413 / 100 := by norm_num
  have hb : ((707 / 50 : ℚ) : ℝ) = 707 / 50 := by norm_num
  have hA := zetaA_mem
  have hB := zetaB_mem
  rw [ha] at hA
  rw [hb] at hB
  set z := riemannZeta (sOf (1413 / 100))
  set w := riemannZeta (sOf (707 / 50))
  have hre : (z * conj w).re = z.re * w.re + z.im * w.im := by
    simp [Complex.mul_re]
  have hc := Interval.contains_add (Interval.contains_mul hA.1 hB.1)
    (Interval.contains_mul hA.2 hB.2)
  rw [hre]
  have hneg : ((((MA.inflate epsA).re.mul (MB.inflate epsB).re).add
      ((MA.inflate epsA).im.mul (MB.inflate epsB).im)).hi : ℝ) < 0 := by
    exact_mod_cast product_hi_neg
  exact lt_of_le_of_lt hc.2 hneg

/-- `ζ` has a zero `1/2 + it` with `14.13 < t < 14.14`. No minimality is asserted. -/
theorem first_zero_on_line :
    ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50), riemannZeta (1 / 2 + t * I) = 0 :=
  first_zero_on_line_of_zeta_product zeta_product_re_neg

end HardyFirstZero
