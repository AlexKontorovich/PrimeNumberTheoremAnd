import RSBounds.PsiFinite.Bits

/-!
# SWAR counting

`fld t x k` is the `k`-th field of width `t` of `x`, and `cnt x a n` the number
of set bits of `x` in `[a, a+n)`. `swarK_fld` shows that after `w` rounds of
`swarK`, field `k` of width `2^w` holds `cnt X (2^w k) (2^w)`, for every field
inside the first `L` bits.
-/

namespace PsiFinite

/-- The `k`-th field of width `t`. -/
def fld (t x k : ℕ) : ℕ := (x >>> (t * k)) % 2 ^ t

/-- The number of set bits of `x` in `[a, a+n)`. -/
def cnt (x a n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (x.testBit (a + j)).toNat

theorem cnt_add (x a n m : ℕ) : cnt x a (n + m) = cnt x a n + cnt x (a + n) m := by
  unfold cnt; rw [Finset.sum_range_add]; congr 1
  refine Finset.sum_congr rfl fun j _ => ?_; rw [Nat.add_assoc]

theorem cnt_le (x a n : ℕ) : cnt x a n ≤ n := by
  unfold cnt
  calc ∑ j ∈ Finset.range n, (x.testBit (a + j)).toNat ≤ ∑ _j ∈ Finset.range n, 1 :=
        Finset.sum_le_sum fun j _ => Bool.toNat_le _
    _ = n := by simp

theorem fld_one (x k : ℕ) : fld 1 x k = cnt x k 1 := by
  unfold fld cnt
  rw [Finset.sum_range_one, add_zero, one_mul, Nat.testBit, pow_one]
  rcases Nat.mod_two_eq_zero_or_one (x >>> k) with h | h <;> simp [h, Nat.one_and_eq_mod_two]

theorem fld_shiftRight (t x k : ℕ) : fld t (x >>> t) k = fld t x (k + 1) := by
  unfold fld; rw [← Nat.shiftRight_add]; congr 2; ring

theorem testBit_fld (t x k j : ℕ) :
    (fld t x k).testBit j = (decide (j < t) && x.testBit (t * k + j)) := by
  unfold fld; rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

/-- Fieldwise addition without carries. -/
theorem fld_add (t : ℕ) : ∀ k a b : ℕ, (∀ j ≤ k, fld t a j + fld t b j < 2 ^ t) →
    fld t (a + b) k = fld t a k + fld t b k := by
  intro k
  induction k with
  | zero =>
    intro a b h
    have h0 := h 0 le_rfl
    simp only [fld, mul_zero, Nat.shiftRight_zero] at h0 ⊢
    rw [Nat.add_mod, Nat.mod_eq_of_lt h0]
  | succ k ih =>
    intro a b h
    have h0 := h 0 (Nat.zero_le _)
    simp only [fld, mul_zero, Nat.shiftRight_zero] at h0
    have hsplit : (a + b) >>> t = (a >>> t) + (b >>> t) := by
      simp only [Nat.shiftRight_eq_div_pow]
      rw [Nat.add_div (by positivity), ite_eq_right (show ¬ 2 ^ t ≤ a % 2 ^ t + b % 2 ^ t by omega), add_zero]
    rw [← fld_shiftRight, hsplit, ih, fld_shiftRight, fld_shiftRight]
    intro j hj
    rw [fld_shiftRight, fld_shiftRight]
    exact h (j + 1) (by omega)

/-- A mask that selects the low half of each field of width `2s`, below `C`. -/
def HalfMask (s C M : ℕ) : Prop := ∀ i < C, M.testBit i = decide (i % (2 * s) < s)

theorem fld_land_mask {s C M x k : ℕ} (hM : HalfMask s C M) (hk : 2 * s * (k + 1) ≤ C) :
    fld (2 * s) (x &&& M) k = fld s x (2 * k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_fld, testBit_fld, Nat.testBit_and]
  by_cases hj : j < s
  · have h2 : j < 2 * s := by omega
    rw [hM _ (by nlinarith)]
    have : (2 * s * k + j) % (2 * s) = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
    simp [h2, hj, this, show s * (2 * k) = 2 * s * k by ring]
  · by_cases h2 : j < 2 * s
    · rw [hM _ (by nlinarith)]
      have : (2 * s * k + j) % (2 * s) = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
      simp [hj, this]
    · simp [h2, hj]

theorem fld_shift_land_mask {s C M x k : ℕ} (hM : HalfMask s C M) (hk : 2 * s * (k + 1) ≤ C) :
    fld (2 * s) ((x >>> s) &&& M) k = fld s x (2 * k + 1) := by
  rw [fld_land_mask hM hk]
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_fld, testBit_fld, Nat.testBit_shiftRight]
  congr 2; ring

theorem fld_lt (t x k : ℕ) : fld t x k < 2 ^ t := Nat.mod_lt _ (by positivity)

/-- One SWAR round doubles the field width and adds neighbouring fields. -/
theorem fld_swar_round {s C M x k : ℕ} (hM : HalfMask s C M) (hk : 2 * s * (k + 1) ≤ C)
    (hsmall : ∀ j ≤ k, fld s x (2 * j) + fld s x (2 * j + 1) < 2 ^ (2 * s)) :
    fld (2 * s) ((x &&& M) + ((x >>> s) &&& M)) k = fld s x (2 * k) + fld s x (2 * k + 1) := by
  rw [fld_add, fld_land_mask hM hk, fld_shift_land_mask hM hk]
  intro j hj
  have hj' : 2 * s * (j + 1) ≤ C := le_trans (Nat.mul_le_mul_left _ (by omega)) hk
  rw [fld_land_mask hM hj', fld_shift_land_mask hM hj']
  exact hsmall j hj

/-- The SWAR masks built by `repK`. -/
theorem halfMask_repK (K s : ℕ) (hs : 0 < s) :
    HalfMask s (2 * s * 2 ^ K) (repK K (2 ^ s - 1) (s + s)) := by
  intro i hi
  have h2s : 0 < 2 * s := by omega
  rw [Bool.eq_iff_iff, testBit_repK, decide_eq_true_iff]
  constructor
  · rintro ⟨t, ht, hle, hb⟩
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_iff] at hb
    have e : i = 2 * s * t + (i - (s + s) * t) := by
      rw [show (s + s) * t = 2 * s * t by ring] at hle ⊢; omega
    rw [e, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]; exact hb
  · intro hmod
    refine ⟨i / (2 * s), ?_, ?_, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul h2s).mpr (by rw [mul_comm]; exact hi)
    · rw [show s + s = 2 * s by ring]; exact Nat.mul_div_le i (2 * s)
    · rw [Nat.testBit_two_pow_sub_one, decide_eq_true_iff, show s + s = 2 * s by ring,
        ← Nat.mod_eq_sub_mul_div]; exact hmod

theorem swarK_zero (L x r : ℕ) : swarK L 0 x r = x := rfl

/-- One SWAR round, verbatim as in `swarK`. -/
noncomputable def swarRound (L r x : ℕ) : ℕ :=
  let s := Nat.shiftLeft 1 r
  let M := repK (Nat.succ (Nat.log2 (Nat.shiftRight L (Nat.succ r))))
    (Nat.sub (Nat.shiftLeft 1 s) 1) (Nat.add s s)
  Nat.add (Nat.land x M) (Nat.land (Nat.shiftRight x s) M)

theorem swarRound_eq (L r x : ℕ) : swarRound L r x =
    (x &&& repK (Nat.log2 (L >>> (r + 1)) + 1) (2 ^ (2 ^ r) - 1) (2 ^ r + 2 ^ r)) +
      ((x >>> 2 ^ r) &&& repK (Nat.log2 (L >>> (r + 1)) + 1) (2 ^ (2 ^ r) - 1) (2 ^ r + 2 ^ r)) := by
  have h1 : Nat.shiftLeft 1 r = 2 ^ r := Nat.one_shiftLeft r
  have h2 : Nat.shiftLeft 1 (2 ^ r) = 2 ^ (2 ^ r) := Nat.one_shiftLeft _
  unfold swarRound; dsimp only; rw [h1, h2]; rfl

theorem swarK_succ (L w x r : ℕ) : swarK L (w + 1) x r = swarK L w (swarRound L r x) (r + 1) := by
  show Bool.rec (motive := fun _ => ℕ) (brk (swarK L w (swarRound L r x) (r + 1)))
    (brk (swarK L w 0 (r + 1))) (Nat.beq (swarRound L r x) 0) = _
  cases hb : Nat.beq (swarRound L r x) 0
  · rfl
  · show brk (swarK L w 0 (r + 1)) = _
    rw [brk_eq, Nat.eq_of_beq_eq_true hb]

theorem swar_cover (L r : ℕ) :
    L < 2 * 2 ^ r * 2 ^ (Nat.log2 (L >>> (r + 1)) + 1) := by
  rw [Nat.shiftRight_eq_div_pow]
  have h1 := @Nat.lt_log2_self (L / 2 ^ (r + 1))
  have h2 : 0 < 2 ^ (r + 1) := by positivity
  have h3 := Nat.lt_mul_div_succ L h2
  calc L < 2 ^ (r + 1) * (L / 2 ^ (r + 1) + 1) := h3
    _ ≤ 2 ^ (r + 1) * 2 ^ (Nat.log2 (L / 2 ^ (r + 1)) + 1) := Nat.mul_le_mul_left _ h1
    _ = 2 * 2 ^ r * 2 ^ (Nat.log2 (L / 2 ^ (r + 1)) + 1) := by ring

/-- After `w` rounds every field of width `2^(r+w)` inside the first `L` bits
holds the bit count of `X` in it. -/
theorem swarK_fld (L X : ℕ) : ∀ w r x : ℕ,
    (∀ k, 2 ^ r * (k + 1) ≤ L → fld (2 ^ r) x k = cnt X (2 ^ r * k) (2 ^ r)) →
    ∀ k, 2 ^ (r + w) * (k + 1) ≤ L →
      fld (2 ^ (r + w)) (swarK L w x r) k = cnt X (2 ^ (r + w) * k) (2 ^ (r + w)) := by
  intro w
  induction w with
  | zero => intro r x h k hk; simpa [swarK_zero] using h k hk
  | succ w ih =>
    intro r x h k hk
    rw [swarK_succ, show r + (w + 1) = (r + 1) + w by ring]
    apply ih
    · intro k' hk'
      set s := 2 ^ r
      have hs : 0 < s := by positivity
      have hM := halfMask_repK (Nat.log2 (L >>> (r + 1)) + 1) s hs
      have hcov : L < 2 * s * 2 ^ (Nat.log2 (L >>> (r + 1)) + 1) := swar_cover L r
      have h2 : 2 ^ (r + 1) = 2 * s := by rw [pow_succ]; ring
      rw [h2] at hk' ⊢
      rw [swarRound_eq, fld_swar_round hM (by nlinarith)]
      · rw [h (2 * k') (by nlinarith), h (2 * k' + 1) (by nlinarith),
          show s * (2 * k' + 1) = 2 * s * k' + s by ring, show s * (2 * k') = 2 * s * k' by ring,
          show 2 * s = s + s by ring, cnt_add]
      · intro j hj
        rw [h (2 * j) (by nlinarith), h (2 * j + 1) (by nlinarith)]
        have := cnt_le X (s * (2 * j)) s
        have := cnt_le X (s * (2 * j + 1)) s
        have : 2 * s < 2 ^ (2 * s) := Nat.lt_two_pow_self
        omega
    · rwa [show r + (w + 1) = r + 1 + w by ring] at hk

/-- The block counts produced by `swarK`, read off by shifting and masking. -/
theorem swarK_block (L X w k : ℕ) (hk : 2 ^ w * (k + 1) ≤ L) :
    ((swarK L w X 0 >>> (2 ^ w * k)) &&& (2 ^ (2 ^ w) - 1)) = cnt X (2 ^ w * k) (2 ^ w) := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := swarK_fld L X w 0 X (fun k _ => by simpa using fld_one X k) k (by simpa using hk)
  simpa [fld] using this

end PsiFinite
