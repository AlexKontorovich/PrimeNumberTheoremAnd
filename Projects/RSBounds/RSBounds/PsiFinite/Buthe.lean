import RSBounds.PsiFinite.Final

/-!
# Büthe's (6.2) on `[100, 10^10]`

Büthe, *An analytic method for bounding ψ(x)*, Math. Comp. 87 (2018), eq. (6.2), records

  `-0.8 ≤ (t - ψ(t)) / √t ≤ 0.81` for `100 ≤ t ≤ 5·10^10`

(IEANTN `ButheNumerics.v1.eq_6_2`). This file proves it for `100 ≤ t ≤ 10^10`:

* `[1500, 10^10]` from T1, `psi_abs_sub_le_four_fifths_sqrt`;
* `[100, 1500)` from a kernel walk over `n = 1, …, 1500`, the walk of `SmallWalk` with
  asymmetric guards: `ψ(n) - n ≤ (4/5) √n` and `n + 1 - ψ(n) ≤ (81/100) √(n+1)` for
  `100 ≤ n < 1500`. The second is tight near `1423`, where `(t - ψ t)/√t → 0.80323`.
-/

namespace PsiFinite

open Real

/-- The asymmetric gap guards at `n`, for `n ≥ 100`. -/
def wcheckB (n : ℕ) (s : WS) : Bool :=
  Nat.blt n 100 || (guardUp 4 5 n s.Phi && guardLow 81 100 (n + 1) s.Plo)

/-- The kernel walk with the guards `wcheckB`, `len` steps from `n`. -/
noncomputable def walkBK (len : ℕ) : ℕ → WS → Option WS :=
  Nat.rec (motive := fun _ => ℕ → WS → Option WS) (fun _ s => some s)
    (fun _ ih n s => Bool.rec none (brk (ih (n + 1) (pstep n s))) (wcheckB n s)) len

theorem walkBK_succ (len n : ℕ) (s : WS) :
    walkBK (len + 1) n s = if wcheckB n s then walkBK len (n + 1) (pstep n s) else none := by
  show Bool.rec (motive := fun _ => Option WS) none _ (wcheckB n s) = _
  cases wcheckB n s <;> rfl

/-- The two one-sided bounds of (6.2) on every unit gap `[m, m+1)` of `[a, b)`, `m ≥ 100`. -/
def GapsB (a b : ℕ) : Prop :=
  ∀ m, a ≤ m → m < b → 100 ≤ m → ∀ x : ℝ, (m : ℝ) ≤ x → x < m + 1 →
    Chebyshev.psi x - x ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
      x - Chebyshev.psi x ≤ (81 / 100 : ℝ) * Real.sqrt x

/-- One gap: upper check at `a` and pre-jump lower check at `b`, with separate constants. -/
theorem gap_two_sided {a b x ku kl : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x < b)
    (hgap : ∀ n : ℕ, a < (n : ℝ) → (n : ℝ) < b → ¬ IsPrimePow n)
    (hupper : Chebyshev.psi a - a ≤ ku * Real.sqrt a)
    (hlower : b - Chebyshev.psi a ≤ kl * Real.sqrt b) :
    Chebyshev.psi x - x ≤ ku * Real.sqrt x ∧ x - Chebyshev.psi x ≤ kl * Real.sqrt x := by
  have he := TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.psi_eq_of_no_prime_powers hax (fun n han hnx => hgap n han (hnx.trans_lt hxb))
  rw [he]
  have hx : 0 < x := ha.trans_le hax
  have hb : 0 < b := hx.trans hxb
  have hmono := TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.normalized_error_antitone
    (Chebyshev.psi_nonneg a)
  have sa := Real.sqrt_pos.mpr ha
  have sx := Real.sqrt_pos.mpr hx
  have sb := Real.sqrt_pos.mpr hb
  constructor
  · have hu : (Chebyshev.psi a - a) / Real.sqrt a ≤ ku := (div_le_iff₀ sa).mpr hupper
    exact (div_le_iff₀ sx).mp ((hmono ha hx hax).trans hu)
  · have hl : -kl ≤ (Chebyshev.psi a - b) / Real.sqrt b := by
      apply (le_div_iff₀ sb).mpr; linarith
    have hh := (le_div_iff₀ sx).mp (hl.trans (hmono hx hb hxb.le))
    linarith

/-- The bounds on `[n, n+1)` from a passed check. -/
theorem wcheckB_bound {n : ℕ} {s : WS} (h : WInv n s) (hc : wcheckB n s = true) (hn : 100 ≤ n)
    {x : ℝ} (hx1 : (n : ℝ) ≤ x) (hx2 : x < n + 1) :
    Chebyshev.psi x - x ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
      x - Chebyshev.psi x ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  unfold wcheckB at hc
  have h100 : Nat.blt n 100 = false := by rw [Bool.eq_false_iff]; intro h'; simp at h'; omega
  rw [h100, Bool.false_or, Bool.and_eq_true] at hc
  obtain ⟨hu, hl⟩ := hc
  have hD := D_pos
  have hU := TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.upperEndpointSafe_real_generic
    (by norm_num [D]) (by norm_num) (by norm_num) (guardUp_safe hu)
  have hL := TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.lowerEndpointSafe_real_generic
    (by norm_num [D]) (by norm_num) (by norm_num) (guardLow_safe hl)
  obtain ⟨-, -, p1, p2⟩ := h
  have r := gap_two_sided (a := n) (b := n + 1) (ku := ((4 : ℕ) : ℝ) / (5 : ℕ))
    (kl := ((81 : ℕ) : ℝ) / (100 : ℕ)) (by positivity) hx1 hx2 ?_ ?_ ?_
  · norm_num at r ⊢; exact r
  · intro m hm1 hm2
    exfalso
    have : n < m := by exact_mod_cast hm1
    have : m < n + 1 := by exact_mod_cast hm2
    omega
  · have : Chebyshev.psi n ≤ s.Phi / D := by rw [le_div_iff₀ hD]; linarith
    linarith
  · have : (s.Plo : ℝ) / D ≤ Chebyshev.psi n := by rw [div_le_iff₀ hD]; linarith
    push_cast at hL
    linarith

theorem walkBK_sound : ∀ (len n : ℕ) (s s' : WS), 1 ≤ n → n + len ≤ 10002 → WInv n s →
    walkBK len n s = some s' → WInv (n + len) s' ∧ GapsB n (n + len) := by
  intro len
  induction len with
  | zero =>
    intro n s s' _ _ h hw
    cases hw
    exact ⟨by simpa using h, fun m h1 h2 => by omega⟩
  | succ len ih =>
    intro n s s' hn hl h hw
    rw [walkBK_succ] at hw
    split_ifs at hw with hc
    obtain ⟨h1, h2⟩ := ih (n + 1) _ _ (by omega) (by omega) (pstep_inv hn (by omega) h) hw
    refine ⟨by rwa [show n + (len + 1) = n + 1 + len by ring], ?_⟩
    intro m hm1 hm2 hm8 x hx1 hx2
    rcases eq_or_lt_of_le hm1 with rfl | hlt
    · exact wcheckB_bound h hc hm8 hx1 hx2
    · exact h2 m (by omega) (by omega) hm8 x hx1 hx2

/-- The kernel walk `n = 1, …, 1500` passes every asymmetric guard from `100` on. -/
theorem walkB_ok : (walkBK 1499 1 ⟨0, 0, 0, 0⟩).isSome = true := by
  decide +kernel

theorem gapsB_small : GapsB 1 1500 := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp walkB_ok
  exact (walkBK_sound 1499 1 _ s' le_rfl (by norm_num) winv_one hs').2

/-- **Büthe (6.2) on `[100, 10^10]`**: `-0.8 ≤ (t - ψ t)/√t ≤ 0.81` for `100 ≤ t ≤ 10^10`. -/
theorem buthe_eq_6_2_le_1e10 {t : ℝ} (h₁ : 100 ≤ t) (h₂ : t ≤ 10 ^ 10) :
    -0.8 ≤ (t - Chebyshev.psi t) / Real.sqrt t ∧
      (t - Chebyshev.psi t) / Real.sqrt t ≤ 0.81 := by
  have st : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  have key : Chebyshev.psi t - t ≤ (4 / 5 : ℝ) * Real.sqrt t ∧
      t - Chebyshev.psi t ≤ (81 / 100 : ℝ) * Real.sqrt t := by
    by_cases h : t < 1500
    · have ht0 : 0 ≤ t := by linarith
      have hm1 : 100 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast h₁)
      have hm2 : ⌊t⌋₊ < 1500 := (Nat.floor_lt ht0).mpr (by exact_mod_cast h)
      exact gapsB_small ⌊t⌋₊ (by omega) hm2 hm1 t (Nat.floor_le ht0) (Nat.lt_floor_add_one t)
    · have h4 := abs_le.mp (psi_abs_sub_le_four_fifths_sqrt (by linarith) h₂)
      exact ⟨by linarith [h4.2], by nlinarith [h4.1]⟩
  constructor
  · rw [le_div_iff₀ st]; norm_num at key ⊢; linarith [key.1]
  · rw [div_le_iff₀ st]; norm_num at key ⊢; linarith [key.2]

end PsiFinite
