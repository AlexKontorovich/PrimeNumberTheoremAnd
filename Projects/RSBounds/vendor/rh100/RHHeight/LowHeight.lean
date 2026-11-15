module

public import RHHeight.Skeleton
public import HardyFirstZero.EulerMaclaurin

@[expose] public section

/-!
# The piece `low_height` of hunt #137: no zero of `ζ` with `0 < Re ρ < 1`, `0 < Im ρ ≤ 3`

`RHHeight.LowHeight` (`RHHeight/Skeleton.lean`) says that Mathlib's `riemannZeta` has no zero
`ρ` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 3`. This file proves it, as `low_height`, from hunt
#132's order-4 Euler-Maclaurin representation (`HardyFirstZero.zeta_em4`,
`hunts/hardy_first_zero/lean/HardyFirstZero/EulerMaclaurin.lean`) and nothing else: no
interval arithmetic and no evaluation of `ζ` anywhere.

**The route.** On the quarter plane `QP = {Re s > 0, Im s > 0}`, `zeta_em4` at `N = 1` reads

    ζ(s) = 1/(s-1) + 1/2 + s/12 - Σ_{k ≥ 0} e(s, k+1),

because the partial sum `Σ_{n<1} n^{-s} = 0^{-s}` vanishes for `s ≠ 0` and every power of `1`
is `1`. The three explicit terms add up to `(s+2)(s+3)/(12(s-1))`. The tail is split at its
first block: `norm_eBlock_le` at `x = 1` bounds `e(s, 1)` by `‖P(s)‖/720`, with
`P(s) = s(s+1)(s+2)(s+3)`, and `norm_tail_le` at `N = 2` bounds the rest by
`‖P(s)‖/(720(σ+3))`. So (`norm_zeta_sub_main_one_le`)

    ‖ζ(s) - (s+2)(s+3)/(12(s-1))‖ ≤ ‖P(s)‖ (1 + 1/(σ+3)) / 720 ≤ ‖P(s)‖ / 540    (σ = Re s).

At a zero the left side is the norm of the main term. Cancelling `‖s+2‖ ‖s+3‖ > 0` leaves
`45 ≤ ‖s-1‖ ‖s‖ ‖s+1‖`. On `0 < σ < 1`, `0 < t ≤ 3` the three squared norms are at most `10`,
`10` and `13`, so the square of the product is at most `1300 < 2025 = 45²`.

The numbers behind the constants, measured with mpmath (one route, floating point, not a
proof and not pinned by a test; `hunts/rh_height_lean/PIECE_low_height.md`): on
`(0,1) × (0,3]` the proved bound is at most `0.713` of the main term, the coarser
`‖P(s)‖/540` at most `0.761`, and the product `‖s-1‖ ‖s‖ ‖s+1‖` at most `34.21` against the
`45` the argument needs, all three suprema at the corner `σ → 1`, `t = 3`. The same bound
stops excluding zeros near `Im s = 3.41`, which is why the skeleton's bottom height is `3`.
-/

open Complex HardyFirstZero

namespace RHHeight

/-- **The Euler-Maclaurin tail from the first block.** For `Re s > 0`, `s ≠ 1`, the tail of
`zeta_em4` at `N = 1` is at most `‖P(s)‖ (1 + 1/(σ+3)) / 720`: its first block by
`norm_eBlock_le` at `x = 1`, the rest by `norm_tail_le` at `N = 2`. -/
theorem norm_tail_one_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖∑' k : ℕ, eBlock s ((k + 1 : ℕ) : ℝ)‖ ≤ ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 := by
  have hsum : Summable (fun k : ℕ => eBlock s ((k + 1 : ℕ) : ℝ)) := by
    refine Summable.of_norm_bounded
      (g := fun k : ℕ => ‖P4 s‖ * (((k + 1 : ℕ) : ℝ)) ^ (-s.re - 4) / 720) ?_ ?_
    · have hb : Summable (fun k : ℕ => ((k : ℝ)) ^ (-s.re - 4)) :=
        Real.summable_nat_rpow.mpr (by linarith)
      have hb1 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ (-s.re - 4)) :=
        (summable_nat_add_iff 1).mpr hb
      exact (hb1.mul_left _).div_const _
    · intro k
      exact norm_eBlock_le hs hs1 (Nat.one_le_cast.mpr (Nat.succ_pos k))
  have hsplit : ∑' k : ℕ, eBlock s ((k + 1 : ℕ) : ℝ)
      = eBlock s ((0 + 1 : ℕ) : ℝ) + ∑' k : ℕ, eBlock s ((k + 2 : ℕ) : ℝ) :=
    hsum.tsum_eq_zero_add
  have hfirst : ‖eBlock s ((0 + 1 : ℕ) : ℝ)‖ ≤ ‖P4 s‖ / 720 := by
    have h := norm_eBlock_le hs hs1 (x := ((0 + 1 : ℕ) : ℝ)) (by norm_num)
    simpa using h
  have hrest : ‖∑' k : ℕ, eBlock s ((k + 2 : ℕ) : ℝ)‖ ≤ ‖P4 s‖ * (1 / (s.re + 3)) / 720 := by
    have h := norm_tail_le hs hs1 (N := 2) le_rfl
    have e : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    rw [e, Real.one_rpow] at h
    exact h
  rw [hsplit]
  calc ‖eBlock s ((0 + 1 : ℕ) : ℝ) + ∑' k : ℕ, eBlock s ((k + 2 : ℕ) : ℝ)‖
      ≤ ‖eBlock s ((0 + 1 : ℕ) : ℝ)‖ + ‖∑' k : ℕ, eBlock s ((k + 2 : ℕ) : ℝ)‖ :=
        norm_add_le _ _
    _ ≤ ‖P4 s‖ / 720 + ‖P4 s‖ * (1 / (s.re + 3)) / 720 := add_le_add hfirst hrest
    _ = ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 := by ring

/-- **The Euler-Maclaurin representation at `N = 1`, with its error bound.** On the quarter
plane, `ζ(s)` is within `‖s(s+1)(s+2)(s+3)‖ (1 + 1/(σ+3)) / 720` of the rational function
`(s+2)(s+3)/(12(s-1))`. -/
theorem norm_zeta_sub_main_one_le {s : ℂ} (hs : s ∈ QP) :
    ‖riemannZeta s - (s + 2) * (s + 3) / (12 * (s - 1))‖
      ≤ ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 := by
  have hs1 : s ≠ 1 := ne_one_of_QP hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [QP] at hs
  have hem := zeta_em4 hs (N := 1) le_rfl
  unfold emRHS at hem
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, Complex.one_cpow,
    Complex.zero_cpow (neg_ne_zero.mpr hs0), mul_one, zero_add] at hem
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hmain : (1 : ℂ) / (s - 1) + 1 / 2 + s / 12 = (s + 2) * (s + 3) / (12 * (s - 1)) := by
    field_simp
    ring
  rw [hem, hmain, sub_sub_cancel_left, norm_neg]
  exact norm_tail_one_le hs.1 hs1

/-- **No zero of `ζ` with `0 < Re s < 1` and `0 < Im s ≤ 3`.** -/
theorem riemannZeta_ne_zero_of_im_le_three {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (h2 : 0 < s.im) (h3 : s.im ≤ 3) : riemannZeta s ≠ 0 := by
  intro hz
  have hQP : s ∈ QP := ⟨h0, h2⟩
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_QP hQP)
  have hbound := norm_zeta_sub_main_one_le hQP
  rw [hz, zero_sub, norm_neg] at hbound
  set M := (s + 2) * (s + 3) / (12 * (s - 1)) with hM
  -- the remainder bound, with `1/(σ+3) ≤ 1/3`
  have hfrac : 1 / (s.re + 3) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hMle : ‖M‖ ≤ ‖P4 s‖ / 540 := by
    calc ‖M‖ ≤ ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 := hbound
      _ ≤ ‖P4 s‖ * (1 + 1 / 3) / 720 := by gcongr
      _ = ‖P4 s‖ / 540 := by ring
  -- the main term, without division
  have hmain : 12 * (s - 1) * M = (s + 2) * (s + 3) := by
    rw [hM]
    field_simp
  have hnorm : 12 * ‖s - 1‖ * ‖M‖ = ‖s + 2‖ * ‖s + 3‖ := by
    have h := congrArg norm hmain
    simpa [norm_mul] using h
  have hP4 : ‖P4 s‖ = ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ := by
    simp [P4]
  have hK2 : 0 < ‖s + 2‖ := norm_pos_iff.mpr fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hK3 : 0 < ‖s + 3‖ := norm_pos_iff.mpr fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hK : 0 < ‖s + 2‖ * ‖s + 3‖ := mul_pos hK2 hK3
  -- a zero forces `45 ≤ ‖s - 1‖ ‖s‖ ‖s + 1‖`
  have h45 : 45 ≤ ‖s - 1‖ * ‖s‖ * ‖s + 1‖ := by
    have hle : ‖s + 2‖ * ‖s + 3‖ ≤
        (‖s - 1‖ * ‖s‖ * ‖s + 1‖) * (‖s + 2‖ * ‖s + 3‖) / 45 := by
      have h12 : 0 ≤ 12 * ‖s - 1‖ := by positivity
      calc ‖s + 2‖ * ‖s + 3‖ = 12 * ‖s - 1‖ * ‖M‖ := hnorm.symm
        _ ≤ 12 * ‖s - 1‖ * (‖P4 s‖ / 540) := mul_le_mul_of_nonneg_left hMle h12
        _ = (‖s - 1‖ * ‖s‖ * ‖s + 1‖) * (‖s + 2‖ * ‖s + 3‖) / 45 := by
            rw [hP4]
            ring
    by_contra hlt
    have hlt : ‖s - 1‖ * ‖s‖ * ‖s + 1‖ < 45 := not_le.mp hlt
    have : (‖s - 1‖ * ‖s‖ * ‖s + 1‖) * (‖s + 2‖ * ‖s + 3‖) / 45 < ‖s + 2‖ * ‖s + 3‖ := by
      rw [div_lt_iff₀ (by norm_num)]
      nlinarith
    linarith
  -- but on `(0, 1) × (0, 3]` the three norms are small
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have ha : ‖s - 1‖ ^ 2 ≤ 10 := by
    rw [hsq]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    nlinarith
  have hb : ‖s‖ ^ 2 ≤ 10 := by
    rw [hsq]
    nlinarith
  have hc : ‖s + 1‖ ^ 2 ≤ 13 := by
    rw [hsq]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    nlinarith
  have hprod : (‖s - 1‖ * ‖s‖ * ‖s + 1‖) ^ 2 ≤ 1300 := by
    have e : (‖s - 1‖ * ‖s‖ * ‖s + 1‖) ^ 2 = ‖s - 1‖ ^ 2 * ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 := by ring
    rw [e]
    calc ‖s - 1‖ ^ 2 * ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 ≤ 10 * 10 * 13 := by gcongr
      _ = 1300 := by norm_num
  nlinarith

/-- **The piece `low_height` of hunt #137** (`RHHeight.LowHeight`): Mathlib's `riemannZeta`
has no zero `ρ` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 3`. -/
theorem low_height : LowHeight := by
  intro ρ hz h0 h1 h2 h3
  exact riemannZeta_ne_zero_of_im_le_three h0 h1 h2 h3 hz

end RHHeight
