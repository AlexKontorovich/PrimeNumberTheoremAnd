import TernaryGoldbach.Prelim.SmallMertensLower
import RSBounds.PsiFinite.Block

/-!
# The range `8 ≤ x ≤ 10^4`, one integer at a time

A kernel walk over `n = 1, …, 10^4` keeps enclosures of `D log n` and `D ψ(n)`,
`D = 10^30`, using `TernaryGoldbach.Prelim.LogWalk.incr_bounds` for
`log(1 + 1/n)` and `TernaryGoldbach.Prelim.MertWalk.lamB_spec` for `Λ(n+1)`
(trial division and the certified prime-power table up to 10002). For
`8 ≤ n < 10^4` it checks, on the gap `[n, n+1)`,

  `ψ(n) - n ≤ k √n` and `n + 1 - ψ(n) ≤ k √(n+1)`,

with `k = 1` for `n < 1500` and `k = 4/5` from `1500` on.
-/

namespace PsiFinite

open Real Finset
open TernaryGoldbach.Prelim.LogWalk (incrLo incrHi incr_bounds)
open TernaryGoldbach.Prelim.MertWalk (lamB lamB_spec)

/-- Walk state: `Llo ≤ D log n ≤ Lhi`, `Plo ≤ D ψ(n) ≤ Phi`. -/
structure WS where
  Llo : ℕ
  Lhi : ℕ
  Plo : ℕ
  Phi : ℕ
deriving Repr, DecidableEq

def pstep (n : ℕ) (s : WS) : WS :=
  let Llo := s.Llo + incrLo n
  let Lhi := s.Lhi + incrHi n
  let b := lamB (n + 1) Llo Lhi
  ⟨Llo, Lhi, s.Plo + b.1, s.Phi + b.2⟩

def kNum (n : ℕ) : ℕ := if n < 1500 then 1 else 4
def kDen (n : ℕ) : ℕ := if n < 1500 then 1 else 5

/-- The two gap guards at `n`, for `n ≥ 8`. -/
def wcheck (n : ℕ) (s : WS) : Bool :=
  Nat.blt n 8 || (guardUp (kNum n) (kDen n) n s.Phi && guardLow (kNum n) (kDen n) (n + 1) s.Plo)

/-- The kernel walk, `len` steps from `n`. -/
noncomputable def walkK (len : ℕ) : ℕ → WS → Option WS :=
  Nat.rec (motive := fun _ => ℕ → WS → Option WS) (fun _ s => some s)
    (fun _ ih n s => Bool.rec none (brk (ih (n + 1) (pstep n s))) (wcheck n s)) len

/-- Compiled twin of `walkK` (untrusted; proposes the values). -/
def walkG : ℕ → ℕ → WS → Option WS
  | 0, _, s => some s
  | len + 1, n, s => if wcheck n s then walkG len (n + 1) (pstep n s) else none

def WInv (n : ℕ) (s : WS) : Prop :=
  (s.Llo : ℝ) ≤ D * Real.log n ∧ D * Real.log n ≤ s.Lhi ∧
    (s.Plo : ℝ) ≤ D * Chebyshev.psi n ∧ D * Chebyshev.psi n ≤ s.Phi

theorem D_eq : (D : ℝ) = 10 ^ 30 := by norm_num [D]

theorem pstep_inv {n : ℕ} (hn : 1 ≤ n) (hn' : n + 1 ≤ 10002) {s : WS} (h : WInv n s) :
    WInv (n + 1) (pstep n s) := by
  obtain ⟨l1, l2, p1, p2⟩ := h
  unfold WInv
  rw [D_eq] at l1 l2 p1 p2 ⊢
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i1, i2⟩ := incr_bounds hn
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
  set Lo := s.Llo + incrLo n
  set Hi := s.Lhi + incrHi n
  have hL1 : (Lo : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [hlog]; simp only [Lo]; push_cast; linarith
  have hL2 : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ (Hi : ℝ) := by
    rw [hlog]; simp only [Hi]; push_cast; linarith
  obtain ⟨b1, b2⟩ := lamB_spec hn' hL1 hL2
  have hP : Chebyshev.psi ((n + 1 : ℕ) : ℝ) = Chebyshev.psi n +
      (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) := by
    rw [psi_add_nat n 1, Nat.Ioc_succ_singleton, Finset.sum_singleton]
  refine ⟨hL1, hL2, ?_, ?_⟩
  · show ((s.Plo + (lamB (n + 1) Lo Hi).1 : ℕ) : ℝ) ≤ _
    rw [hP, Nat.cast_add]; linarith
  · show _ ≤ ((s.Phi + (lamB (n + 1) Lo Hi).2 : ℕ) : ℝ)
    rw [hP, Nat.cast_add]; linarith

/-- The bound on `[n, n+1)` from a passed check. -/
theorem wcheck_bound {n : ℕ} {s : WS} (h : WInv n s) (hc : wcheck n s = true) (hn : 8 ≤ n)
    {x : ℝ} (hx1 : (n : ℝ) ≤ x) (hx2 : x < n + 1) :
    |Chebyshev.psi x - x| ≤ ((kNum n : ℝ) / kDen n) * Real.sqrt x := by
  unfold wcheck at hc
  have h8 : Nat.blt n 8 = false := by rw [Bool.eq_false_iff]; intro h'; simp at h'; omega
  rw [h8, Bool.false_or, Bool.and_eq_true] at hc
  obtain ⟨hu, hl⟩ := hc
  have hnum : 0 < kNum n := by unfold kNum; split_ifs <;> norm_num
  have hden : 0 < kDen n := by unfold kDen; split_ifs <;> norm_num
  have hD := D_pos
  have hU := TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.upperEndpointSafe_real_generic
    (by norm_num [D]) hnum hden (guardUp_safe hu)
  have hL := TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.lowerEndpointSafe_real_generic
    (by norm_num [D]) hnum hden (guardLow_safe hl)
  obtain ⟨-, -, p1, p2⟩ := h
  apply TernaryGoldbach.RSBounds.PsiSieveEndpointReduction.psi_gap_abs_le (a := n) (b := n + 1)
    (by positivity) hx1 hx2
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

theorem walkK_zero (n : ℕ) (s : WS) : walkK 0 n s = some s := rfl

theorem walkK_succ (len n : ℕ) (s : WS) :
    walkK (len + 1) n s = if wcheck n s then walkK len (n + 1) (pstep n s) else none := by
  show Bool.rec (motive := fun _ => Option WS) none _ (wcheck n s) = _
  cases wcheck n s <;> rfl

/-- The real-variable conclusion of the walk on `[a, b)`, gap by gap. -/
def GapsOK (a b : ℕ) : Prop :=
  ∀ m, a ≤ m → m < b → 8 ≤ m → ∀ x : ℝ, (m : ℝ) ≤ x → x < m + 1 →
    |Chebyshev.psi x - x| ≤ ((kNum m : ℝ) / kDen m) * Real.sqrt x

theorem walkK_sound : ∀ (len n : ℕ) (s s' : WS), 1 ≤ n → n + len ≤ 10002 → WInv n s →
    walkK len n s = some s' → WInv (n + len) s' ∧ GapsOK n (n + len) := by
  intro len
  induction len with
  | zero =>
    intro n s s' _ _ h hw
    rw [walkK_zero] at hw; cases hw
    exact ⟨by simpa using h, fun m h1 h2 => by omega⟩
  | succ len ih =>
    intro n s s' hn hl h hw
    rw [walkK_succ] at hw
    split_ifs at hw with hc
    obtain ⟨h1, h2⟩ := ih (n + 1) _ _ (by omega) (by omega) (pstep_inv hn (by omega) h) hw
    refine ⟨by rwa [show n + (len + 1) = n + 1 + len by ring], ?_⟩
    intro m hm1 hm2 hm8 x hx1 hx2
    rcases eq_or_lt_of_le hm1 with rfl | hlt
    · exact wcheck_bound h hc hm8 hx1 hx2
    · exact h2 m (by omega) (by omega) hm8 x hx1 hx2

theorem winv_one : WInv 1 ⟨0, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Chebyshev.psi_one]

end PsiFinite
