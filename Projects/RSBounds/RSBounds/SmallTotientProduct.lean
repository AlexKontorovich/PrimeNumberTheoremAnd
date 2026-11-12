import TernaryGoldbach.Prelim.RamareWalk

/-!
# `∏_{p ≤ x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)` for primes `5 ≤ x ≤ 71`, by the kernel

The generic checker is adapted from `Prelim/SmallMertensProd.lean` at upstream
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`. Only the range through the twentieth
prime is generated here. This suffices for the exact RS62 totient bound when
there are at most twenty distinct prime factors. No RH hypothesis is imported.

The kernel walks `n ≤ 71` (`scripts/gen_small_totient_product.py`) with `D = 10³⁰`. The state bounds:
* `D log n`, using the artanh walk `LogWalk.incr_bounds`;
* `D θ(n)` and `D ∏_{p≤n} p/(p−1)`, with primality decided by trial division (`isP_iff`);
* `D log m` for an integer `1 ≤ m ≤ θ(n)`, which advances with `θ`.

At every prime `x ≥ 5` it bounds `log θ = log m + log(1 + (θ − m)/m)`, where the second term comes
from 12 terms of the artanh series (`q_bounds`). It uses `e^γ ≥ G/D` (Taylor, with `γ` from
`RamareWalk`) and checks `D F(x) < G log θ + 2.50637 D/log θ` in fixed point.
The tightest case is `x = 23`, with margin `2.4·10⁻⁷`.
-/

open Finset Real

namespace TernaryGoldbach.RSBounds.SmallTotientProduct

open TernaryGoldbach.Prelim.LogWalk
open TernaryGoldbach.Prelim.RamPf (Hn harm_bounds log_one_add_inv_bounds)

/-! ### `γ` and `e^γ` -/

theorem harmonic_eq_Hn : ∀ n, ((harmonic n : ℚ) : ℝ) = Hn n
  | 0 => by simp [Hn]
  | n + 1 => by
    rw [harmonic_succ, Rat.cast_add, harmonic_eq_Hn n, Hn, Hn, sum_Icc_succ_top (by omega)]
    push_cast; ring

theorem gamma_bounds : (0.5772156646 : ℝ) ≤ eulerMascheroniConstant ∧
    eulerMascheroniConstant ≤ 0.577215666 := by
  obtain ⟨b1, b2⟩ := harm_bounds (n := 20000) (by norm_num)
  rw [harmonic_eq_Hn] at b1 b2
  obtain ⟨l1, l2, h1, h2, -⟩ := TernaryGoldbach.Prelim.RamPf.inv_20000
  dsimp only at l1 l2 h1 h2
  push_cast at b1 b2 l1 l2 h1 h2
  constructor <;> linarith

/-- `G ≤ 10³⁰ e^γ`. -/
def Glo : ℕ := 1781072417453146124173531684687

theorem Glo_le : (Glo : ℝ) ≤ 10 ^ 30 * Real.exp eulerMascheroniConstant := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 0.5772156646) (by norm_num) 22
  have h2 : Real.exp 0.5772156646 ≤ Real.exp eulerMascheroniConstant :=
    Real.exp_le_exp.2 gamma_bounds.1
  have h3 : (Glo : ℝ) ≤ 10 ^ 30 * ∑ i ∈ range 22, (0.5772156646 : ℝ) ^ i / i.factorial := by
    unfold Glo
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]
    norm_num
  nlinarith

/-- `e^γ ≤ 1.7811`. -/
theorem exp_gamma_le : Real.exp eulerMascheroniConstant ≤ 1.7811 := by
  have h1 := Real.exp_bound (x := 0.577215666) (by rw [abs_le]; constructor <;> norm_num)
    (n := 12) (by norm_num)
  have h2 : Real.exp eulerMascheroniConstant ≤ Real.exp 0.577215666 :=
    Real.exp_le_exp.2 gamma_bounds.2
  rw [abs_le] at h1
  have h3 : ∑ m ∈ range 12, (0.577215666 : ℝ) ^ m / m.factorial +
      |(0.577215666 : ℝ)| ^ 12 * ((Nat.succ 12 : ℕ) / ((Nat.factorial 12 : ℕ) * (12 : ℕ))) ≤ 1.7811 := by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  linarith [h1.2]

/-! ### Primality by trial division -/

def tdiv (p : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 => if p < d * d then true else if p % d = 0 then false else tdiv p (d + 1) fuel

def isP (p : ℕ) : Bool := 2 ≤ p && tdiv p 2 p

theorem tdiv_sound {p : ℕ} (hp : 2 ≤ p) : ∀ fuel d, 2 ≤ d →
    (∀ e, 2 ≤ e → e < d → ¬ e ∣ p) → tdiv p d fuel = true → p.Prime := by
  intro fuel
  induction fuel with
  | zero => intro d _ _ h; simp [tdiv] at h
  | succ f ih =>
    intro d hd hno h
    unfold tdiv at h
    split_ifs at h with h1 h2
    · rw [Nat.prime_def_le_sqrt]
      refine ⟨hp, fun m hm2 hms hdvd => ?_⟩
      have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
      have hmd : m < d := by nlinarith
      exact hno m hm2 hmd hdvd
    · exact ih (d + 1) (by omega) (fun e he1 he2 hdvd => by
        rcases Nat.lt_or_ge e d with h3 | h3
        · exact hno e he1 h3 hdvd
        · have : e = d := by omega
          subst this
          exact h2 (Nat.mod_eq_zero_of_dvd hdvd)) h

theorem tdiv_complete {p : ℕ} (hp : p.Prime) : ∀ fuel d, 2 ≤ d → d ≤ p + 1 → p + 2 ≤ d + fuel →
    tdiv p d fuel = true := by
  intro fuel
  induction fuel with
  | zero => intro d hd hdp hf; omega
  | succ f ih =>
    intro d hd hdp hf
    have hp2 := hp.two_le
    unfold tdiv
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero h2
      rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
      · omega
      · subst h; nlinarith
    · exact ih (d + 1) (by omega) (by nlinarith) (by omega)

theorem isP_iff (p : ℕ) : isP p = true ↔ p.Prime := by
  unfold isP
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h2, h⟩
    exact tdiv_sound h2 p 2 le_rfl (fun e h1 h2 => by omega) h
  · intro hp
    exact ⟨hp.two_le, tdiv_complete hp p 2 le_rfl (by have := hp.two_le; omega) (by omega)⟩

/-! ### `log(1 + b/a)` by the artanh series -/

/-- `∑_{j<k} ⌊2·10³⁰ b^{2j+1}/((2j+1)(2a+b)^{2j+1})⌋`. -/
def qAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b => qAux k a b + 2 * 10 ^ 30 * b ^ (2 * k + 1) / ((2 * k + 1) * (2 * a + b) ^ (2 * k + 1))

def qLo (a b : ℕ) : ℕ := qAux 12 a b
def qHi (a b : ℕ) : ℕ := qAux 12 a b + 12 + 3 * 10 ^ 30 * b ^ 25 / (25 * (2 * a + b) ^ 25) + 1

theorem qAux_le (a b : ℕ) (hb : 0 < b) : ∀ k, (qAux k a b : ℝ) ≤
    10 ^ 30 * ∑ j ∈ range k, (2 : ℝ) * (1 / (2 * j + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * j + 1)
  | 0 => by simp [qAux]
  | k + 1 => by
    rw [qAux, sum_range_succ, mul_add, Nat.cast_add]
    refine add_le_add (qAux_le a b hb k) ?_
    have := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 30 * b ^ (2 * k + 1))
      (n := (2 * k + 1) * (2 * a + b) ^ (2 * k + 1))
    refine this.trans (le_of_eq ?_)
    have : (0 : ℝ) < 2 * a + b := by positivity
    rw [div_pow]
    push_cast
    field_simp
    norm_num

theorem le_qAux (a b : ℕ) (hb : 0 < b) : ∀ k, 10 ^ 30 * ∑ j ∈ range k,
    (2 : ℝ) * (1 / (2 * j + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * j + 1) ≤ (qAux k a b : ℝ) + k
  | 0 => by simp [qAux]
  | k + 1 => by
    rw [qAux, sum_range_succ, mul_add, Nat.cast_add, Nat.cast_succ]
    have h1 := le_qAux a b hb k
    have hpos : 0 < (2 * k + 1) * (2 * a + b) ^ (2 * k + 1) := by positivity
    obtain ⟨-, h2⟩ := floor_div_bounds (2 * 10 ^ 30 * b ^ (2 * k + 1)) _ hpos
    have e : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * k + 1)) =
        ((2 * 10 ^ 30 * b ^ (2 * k + 1) : ℕ) : ℝ) / (((2 * k + 1) * (2 * a + b) ^ (2 * k + 1) : ℕ) : ℝ) := by
      have : (0 : ℝ) < 2 * a + b := by positivity
      rw [div_pow]; push_cast; field_simp; norm_num
    linarith

/-- **`qLo/D ≤ log(1 + b/a) ≤ qHi/D`** for `0 < b ≤ a`. -/
theorem q_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (qLo a b : ℝ) ≤ 10 ^ 30 * Real.log (1 + (b : ℝ) / a) ∧
      10 ^ 30 * Real.log (1 + (b : ℝ) / a) ≤ (qHi a b : ℝ) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  set r : ℝ := (a : ℝ) / b with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨h1, h2⟩ := log_one_add_inv_bounds hr0 12
  have ey : 1 / (2 * r + 1) = (b : ℝ) / (2 * a + b) := by rw [hr]; field_simp
  have el : 1 + r⁻¹ = 1 + (b : ℝ) / a := by rw [hr, inv_div]
  rw [ey, el] at h1 h2
  refine ⟨(qAux_le a b hb 12).trans (by nlinarith), ?_⟩
  have h3 := le_qAux a b hb 12
  set y : ℝ := (b : ℝ) / (2 * a + b) with hy
  have hy0 : 0 < y := by positivity
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (b : ℝ) ≤ a := by exact_mod_cast hba
    linarith
  have htail : 2 / (2 * ((12 : ℕ) : ℝ) + 1) * y ^ (2 * 12 + 1) / (1 - y ^ 2) ≤ 3 / 25 * y ^ 25 := by
    have h1y : 8 / 9 ≤ 1 - y ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have : 0 ≤ y ^ 25 := by positivity
    nlinarith
  have hfl : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) ≤
      ((3 * 10 ^ 30 * b ^ 25 / (25 * (2 * a + b) ^ 25) : ℕ) : ℝ) + 1 := by
    have hpos : 0 < 25 * (2 * a + b) ^ 25 := by positivity
    obtain ⟨-, h4⟩ := floor_div_bounds (3 * 10 ^ 30 * b ^ 25) _ hpos
    have e : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) =
        ((3 * 10 ^ 30 * b ^ 25 : ℕ) : ℝ) / ((25 * (2 * a + b) ^ 25 : ℕ) : ℝ) := by
      have : (0 : ℝ) < 2 * a + b := by positivity
      rw [hy, div_pow]; push_cast; field_simp; norm_num
    linarith
  unfold qHi
  push_cast
  push_cast at h3
  nlinarith

/-! ### The walk -/

/-- `θ(n)` and `∏_{p ≤ n} p/(p−1)`. -/
noncomputable def th (n : ℕ) : ℝ := ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p
noncomputable def Fp (n : ℕ) : ℝ := ∏ p ∈ (Icc 1 n).filter Nat.Prime, ((p : ℝ) / (p - 1))

theorem th_succ (n : ℕ) : th (n + 1) = th n + if (n + 1).Prime then Real.log (n + 1 : ℕ) else 0 := by
  unfold th
  rw [sum_filter, sum_filter, sum_Icc_succ_top (by omega)]

theorem Fp_succ (n : ℕ) : Fp (n + 1) = Fp n * if (n + 1).Prime then
    (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) - 1)) else 1 := by
  unfold Fp
  rw [prod_filter, prod_filter, prod_Icc_succ_top (by omega)]

/-- `⌈x/y⌉`. -/
def cdiv (x y : ℕ) : ℕ := (x + y - 1) / y

theorem cdiv_ge (x y : ℕ) (hy : 0 < y) : (x : ℝ) / y ≤ (cdiv x y : ℝ) := by
  unfold cdiv
  have h1 := Nat.div_add_mod (x + y - 1) y
  have h2 := Nat.mod_lt (x + y - 1) hy
  have h3 : x ≤ y * ((x + y - 1) / y) := by omega
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  rw [div_le_iff₀ hy']
  have : (x : ℝ) ≤ (y : ℝ) * (((x + y - 1) / y : ℕ) : ℝ) := by exact_mod_cast h3
  linarith

/-- Advance `m` while `D (m + 1) ≤ T`. -/
def adv : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, m, lo, hi => (m, lo, hi)
  | f + 1, T, m, lo, hi =>
    if 10 ^ 30 * (m + 1) ≤ T then adv f T (m + 1) (lo + incrLo m) (hi + incrHi m) else (m, lo, hi)

theorem adv_spec : ∀ (f T m lo hi : ℕ), 1 ≤ m → (lo : ℝ) ≤ 10 ^ 30 * Real.log m →
    10 ^ 30 * Real.log m ≤ hi →
    1 ≤ (adv f T m lo hi).1 ∧ ((adv f T m lo hi).2.1 : ℝ) ≤ 10 ^ 30 * Real.log (adv f T m lo hi).1 ∧
      10 ^ 30 * Real.log (adv f T m lo hi).1 ≤ (adv f T m lo hi).2.2 := by
  intro f
  induction f with
  | zero => intro T m lo hi hm h1 h2; exact ⟨hm, h1, h2⟩
  | succ f ih =>
    intro T m lo hi hm h1 h2
    unfold adv
    split_ifs with hc
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      obtain ⟨i1, i2⟩ := incr_bounds hm
      have hlog : Real.log ((m + 1 : ℕ) : ℝ) = Real.log m + Real.log (1 + (m : ℝ)⁻¹) := by
        rw [← Real.log_mul hm0.ne' (by positivity)]; congr 1; push_cast; field_simp
      apply ih T (m + 1) _ _ (by omega)
      · rw [hlog]; push_cast; linarith
      · rw [hlog]; push_cast; linarith
    · exact ⟨hm, h1, h2⟩

/-- The claim at a prime `x`. -/
def Claim (x : ℕ) : Prop :=
  Fp x < Real.exp eulerMascheroniConstant * Real.log (th x) + 2.50637 / Real.log (th x)

structure PS where
  Llo : ℕ
  Lhi : ℕ
  Tlo : ℕ
  Thi : ℕ
  Fhi : ℕ
  m : ℕ
  Mlo : ℕ
  Mhi : ℕ
deriving DecidableEq

/-- The step at a prime `n + 1`, given the advanced `(m, log m)`. -/
def pstepR (n : ℕ) (s : PS) (r : ℕ × ℕ × ℕ) : PS :=
  ⟨s.Llo + incrLo n, s.Lhi + incrHi n, s.Tlo + (s.Llo + incrLo n), s.Thi + (s.Lhi + incrHi n),
    cdiv (s.Fhi * (n + 1)) n, r.1, r.2.1, r.2.2⟩

/-- The step at a prime `n + 1`. -/
def pstepP (n : ℕ) (s : PS) : PS :=
  pstepR n s (adv 30 (s.Tlo + (s.Llo + incrLo n)) s.m s.Mlo s.Mhi)

/-- The step at a composite `n + 1`. -/
def pstepN (n : ℕ) (s : PS) : PS :=
  ⟨s.Llo + incrLo n, s.Lhi + incrHi n, s.Tlo, s.Thi, s.Fhi, s.m, s.Mlo, s.Mhi⟩

def pstep (n : ℕ) (s : PS) : PS := if isP (n + 1) then pstepP n s else pstepN n s

/-- The check at a prime `x ≥ 5`, on the state at `x`. -/
def chk (s : PS) : Bool :=
  decide (10 ^ 30 * s.m < s.Tlo) && decide (s.Thi - 10 ^ 30 * s.m ≤ 10 ^ 30 * s.m) &&
    decide (s.Fhi < Glo * (s.Mlo + qLo (10 ^ 30 * s.m) (s.Tlo - 10 ^ 30 * s.m)) / 10 ^ 30 +
      250637 * 10 ^ 55 / (s.Mhi + qHi (10 ^ 30 * s.m) (s.Thi - 10 ^ 30 * s.m)))

def walkP : ℕ → ℕ → PS → Option PS
  | _, 0, s => some s
  | n, len + 1, s =>
    let s' := pstep n s
    if s'.Lhi + s'.Thi + s'.Fhi + s'.Mhi < 10 ^ 200 ∧ (isP (n + 1) = false ∨ n + 1 < 5 ∨ chk s' = true) then
      walkP (n + 1) len s' else none

def Inv (n : ℕ) (s : PS) : Prop :=
  (s.Llo : ℝ) ≤ 10 ^ 30 * Real.log n ∧ 10 ^ 30 * Real.log n ≤ s.Lhi ∧
  (s.Tlo : ℝ) ≤ 10 ^ 30 * th n ∧ 10 ^ 30 * th n ≤ s.Thi ∧
  10 ^ 30 * Fp n ≤ s.Fhi ∧
  1 ≤ s.m ∧ (s.Mlo : ℝ) ≤ 10 ^ 30 * Real.log s.m ∧ 10 ^ 30 * Real.log s.m ≤ s.Mhi ∧
  ∀ x, 5 ≤ x → x ≤ n → x.Prime → Claim x

theorem th_nonneg (n : ℕ) : 0 ≤ th n :=
  sum_nonneg fun p _ => Real.log_natCast_nonneg p

theorem log_q_lo {a T : ℕ} (ha : 0 < a) (hT : a < T) (hba : T - a ≤ a) :
    (qLo a (T - a) : ℝ) ≤ 10 ^ 30 * Real.log ((T : ℝ) / a) := by
  obtain ⟨q, -⟩ := q_bounds ha (by omega) hba
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have e : (1 : ℝ) + ((T - a : ℕ) : ℝ) / a = (T : ℝ) / a := by
    rw [Nat.cast_sub hT.le]; field_simp; ring
  rwa [e] at q

theorem log_q_hi {a T : ℕ} (ha : 0 < a) (hT : a < T) (hba : T - a ≤ a) :
    10 ^ 30 * Real.log ((T : ℝ) / a) ≤ (qHi a (T - a) : ℝ) := by
  obtain ⟨-, q⟩ := q_bounds ha (by omega) hba
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have e : (1 : ℝ) + ((T - a : ℕ) : ℝ) / a = (T : ℝ) / a := by
    rw [Nat.cast_sub hT.le]; field_simp; ring
  rwa [e] at q

/-- The check gives the claim. -/
theorem chk_claim {x : ℕ} {s : PS} (hT1 : (s.Tlo : ℝ) ≤ 10 ^ 30 * th x)
    (hT2 : 10 ^ 30 * th x ≤ s.Thi) (hF : 10 ^ 30 * Fp x ≤ s.Fhi) (hm : 1 ≤ s.m)
    (hM1 : (s.Mlo : ℝ) ≤ 10 ^ 30 * Real.log s.m) (hM2 : 10 ^ 30 * Real.log s.m ≤ s.Mhi)
    (hc : chk s = true) : Claim x := by
  unfold chk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc
  have hm0 : (0 : ℝ) < s.m := by exact_mod_cast hm
  have ha0 : 0 < 10 ^ 30 * s.m := Nat.mul_pos (by norm_num) hm
  have hTT : s.Tlo ≤ s.Thi := by exact_mod_cast hT1.trans hT2
  have q1 := log_q_lo ha0 c1 (by omega)
  have q2 := log_q_hi ha0 (lt_of_lt_of_le c1 hTT) c2
  have hac : ((10 ^ 30 * s.m : ℕ) : ℝ) = 10 ^ 30 * s.m := by push_cast; ring
  rw [hac] at q1 q2
  have hTa : 10 ^ 30 * (s.m : ℝ) < s.Tlo := by rw [← hac]; exact_mod_cast c1
  have hth : (s.m : ℝ) < th x := by
    have : 10 ^ 30 * (s.m : ℝ) < 10 ^ 30 * th x := by linarith
    linarith
  have hth0 : 0 < th x := by linarith
  have hTlo0 : (0 : ℝ) < s.Tlo := by linarith
  -- `log θ` from below and above
  have hsplit1 : Real.log ((s.Tlo : ℝ) / 10 ^ 30) = Real.log s.m + Real.log ((s.Tlo : ℝ) / (10 ^ 30 * s.m)) := by
    rw [← Real.log_mul hm0.ne' (by positivity)]; congr 1; field_simp
  have hsplit2 : Real.log ((s.Thi : ℝ) / 10 ^ 30) = Real.log s.m + Real.log ((s.Thi : ℝ) / (10 ^ 30 * s.m)) := by
    have : (0 : ℝ) < s.Thi := by linarith
    rw [← Real.log_mul hm0.ne' (by positivity)]; congr 1; field_simp
  have hl1 : Real.log ((s.Tlo : ℝ) / 10 ^ 30) ≤ Real.log (th x) :=
    Real.log_le_log (by positivity) (by rw [div_le_iff₀ (by norm_num)]; linarith)
  have hl2 : Real.log (th x) ≤ Real.log ((s.Thi : ℝ) / 10 ^ 30) :=
    Real.log_le_log hth0 (by rw [le_div_iff₀ (by norm_num)]; linarith)
  set A := s.Mlo + qLo (10 ^ 30 * s.m) (s.Tlo - 10 ^ 30 * s.m) with hA
  set B := s.Mhi + qHi (10 ^ 30 * s.m) (s.Thi - 10 ^ 30 * s.m) with hB
  have hlo : (A : ℝ) ≤ 10 ^ 30 * Real.log (th x) := by
    rw [hA, Nat.cast_add]
    calc (s.Mlo : ℝ) + (qLo (10 ^ 30 * s.m) (s.Tlo - 10 ^ 30 * s.m) : ℝ)
        ≤ 10 ^ 30 * Real.log s.m + 10 ^ 30 * Real.log ((s.Tlo : ℝ) / (10 ^ 30 * s.m)) :=
          add_le_add hM1 q1
      _ = 10 ^ 30 * Real.log ((s.Tlo : ℝ) / 10 ^ 30) := by rw [hsplit1]; ring
      _ ≤ 10 ^ 30 * Real.log (th x) := mul_le_mul_of_nonneg_left hl1 (by norm_num)
  have hhi : 10 ^ 30 * Real.log (th x) ≤ (B : ℝ) := by
    rw [hB, Nat.cast_add]
    calc 10 ^ 30 * Real.log (th x) ≤ 10 ^ 30 * Real.log ((s.Thi : ℝ) / 10 ^ 30) :=
          mul_le_mul_of_nonneg_left hl2 (by norm_num)
      _ = 10 ^ 30 * Real.log s.m + 10 ^ 30 * Real.log ((s.Thi : ℝ) / (10 ^ 30 * s.m)) := by
          rw [hsplit2]; ring
      _ ≤ (s.Mhi : ℝ) + (qHi (10 ^ 30 * s.m) (s.Thi - 10 ^ 30 * s.m) : ℝ) := add_le_add hM2 q2
  have hlogθ : 0 < Real.log (th x) := Real.log_pos (by
    have : (1 : ℝ) ≤ s.m := by exact_mod_cast hm
    linarith)
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le (by positivity) hhi
  -- the right-hand side
  have hG := Glo_le
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  obtain ⟨f1, -⟩ := floor_div_bounds (Glo * A) (10 ^ 30) (by positivity)
  obtain ⟨f2, -⟩ := floor_div_bounds (250637 * 10 ^ 55) B (by exact_mod_cast hB0)
  have hR1 : ((Glo * A / 10 ^ 30 : ℕ) : ℝ) ≤
      10 ^ 30 * (Real.exp eulerMascheroniConstant * Real.log (th x)) := by
    refine f1.trans ?_
    rw [div_le_iff₀ (by positivity), Nat.cast_mul]
    have := mul_le_mul hG hlo hA0 (by positivity)
    push_cast
    linarith only [this]
  have hR2 : ((250637 * 10 ^ 55 / B : ℕ) : ℝ) ≤ 10 ^ 30 * (2.50637 / Real.log (th x)) := by
    refine f2.trans ?_
    have h1 : ((250637 * 10 ^ 55 : ℕ) : ℝ) / B ≤
        ((250637 * 10 ^ 55 : ℕ) : ℝ) / (10 ^ 30 * Real.log (th x)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hhi
    have h2 : ((250637 * 10 ^ 55 : ℕ) : ℝ) / (10 ^ 30 * Real.log (th x)) =
        10 ^ 30 * (2.50637 / Real.log (th x)) := by
      push_cast; field_simp; norm_num
    linarith
  have hc3 := (Nat.cast_lt (α := ℝ)).2 c3
  rw [Nat.cast_add] at hc3
  unfold Claim
  linarith

/-- The step at a prime `n + 1`, for any advanced `r = (m, log m bounds)`. -/
theorem Inv_stepR {n : ℕ} (hn : 1 ≤ n) {s : PS} (h : Inv n s) (hpr : (n + 1).Prime)
    (r : ℕ × ℕ × ℕ) (a1 : 1 ≤ r.1) (a2 : (r.2.1 : ℝ) ≤ 10 ^ 30 * Real.log r.1)
    (a3 : 10 ^ 30 * Real.log r.1 ≤ r.2.2) (hc : n + 1 < 5 ∨ chk (pstepR n s r) = true) :
    Inv (n + 1) (pstepR n s r) := by
  obtain ⟨l1, l2, t1, t2, f1, m1, m2, m3, hcl⟩ := h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i1, i2⟩ := incr_bounds hn
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
  have hL1 : ((s.Llo + incrLo n : ℕ) : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [hlog]; push_cast; linarith
  have hL2 : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ ((s.Lhi + incrHi n : ℕ) : ℝ) := by
    rw [hlog]; push_cast; linarith
  have hth := th_succ n
  have hFp := Fp_succ n
  rw [if_pos hpr] at hth hFp
  have hT1 : ((s.Tlo + (s.Llo + incrLo n) : ℕ) : ℝ) ≤ 10 ^ 30 * th (n + 1) := by
    rw [hth, Nat.cast_add s.Tlo, mul_add]; linarith
  have hT2 : 10 ^ 30 * th (n + 1) ≤ ((s.Thi + (s.Lhi + incrHi n) : ℕ) : ℝ) := by
    rw [hth, Nat.cast_add s.Thi, mul_add]; linarith
  have hF1 : 10 ^ 30 * Fp (n + 1) ≤ ((cdiv (s.Fhi * (n + 1)) n : ℕ) : ℝ) := by
    refine le_trans ?_ (cdiv_ge _ _ (by omega))
    rw [hFp]
    have e : (((n + 1 : ℕ) : ℝ) - 1) = n := by push_cast; ring
    rw [e]
    push_cast
    rw [← mul_assoc, mul_div_assoc', le_div_iff₀ hn0, div_mul_cancel₀ _ hn0.ne']
    exact mul_le_mul_of_nonneg_right f1 (by positivity)
  refine ⟨hL1, hL2, hT1, hT2, hF1, a1, a2, a3, fun x hx5 hxn hxp => ?_⟩
  rcases Nat.lt_or_ge x (n + 1) with hlt | hge
  · exact hcl x hx5 (by omega) hxp
  · have hxe : x = n + 1 := by omega
    subst hxe
    rcases hc with hc | hc
    · omega
    · exact chk_claim (s := pstepR n s r) hT1 hT2 hF1 a1 a2 a3 hc

theorem Inv_step {n : ℕ} (hn : 1 ≤ n) {s : PS} (h : Inv n s)
    (hc : isP (n + 1) = false ∨ n + 1 < 5 ∨ chk (pstep n s) = true) : Inv (n + 1) (pstep n s) := by
  by_cases hp : isP (n + 1) = true
  · have hpr := (isP_iff _).1 hp
    have hps : pstep n s = pstepR n s (adv 30 (s.Tlo + (s.Llo + incrLo n)) s.m s.Mlo s.Mhi) := by
      unfold pstep pstepP; rw [if_pos hp]
    rw [hps] at hc ⊢
    have hh := h
    obtain ⟨-, -, -, -, -, m1, m2, m3, -⟩ := hh
    obtain ⟨a1, a2, a3⟩ := adv_spec 30 (s.Tlo + (s.Llo + incrLo n)) s.m s.Mlo s.Mhi m1 m2 m3
    refine Inv_stepR hn h hpr _ a1 a2 a3 ?_
    rcases hc with hc | hc
    · rw [hp] at hc; exact absurd hc (by decide)
    · exact hc
  · obtain ⟨l1, l2, t1, t2, f1, m1, m2, m3, hcl⟩ := h
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨i1, i2⟩ := incr_bounds hn
    have hlog : Real.log ((n + 1 : ℕ) : ℝ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
      rw [← Real.log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
    have hL1 : ((s.Llo + incrLo n : ℕ) : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
      rw [hlog]; push_cast; linarith
    have hL2 : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ ((s.Lhi + incrHi n : ℕ) : ℝ) := by
      rw [hlog]; push_cast; linarith
    have hth := th_succ n
    have hFp := Fp_succ n
    have hnp : ¬ (n + 1).Prime := fun h' => hp ((isP_iff _).2 h')
    rw [if_neg hnp] at hth hFp
    have hps : pstep n s = pstepN n s := by unfold pstep; rw [if_neg hp]
    rw [hps]
    unfold pstepN
    refine ⟨hL1, hL2, ?_, ?_, ?_, m1, m2, m3, fun x hx5 hxn hxp => ?_⟩
    · rw [hth, add_zero]; exact t1
    · rw [hth, add_zero]; exact t2
    · rw [hFp, mul_one]; exact f1
    · rcases Nat.lt_or_ge x (n + 1) with hlt | hge
      · exact hcl x hx5 (by omega) hxp
      · have hxe : x = n + 1 := by omega
        subst hxe
        exact absurd hxp hnp

theorem walkP_spec : ∀ (len n : ℕ) (s s' : PS), 1 ≤ n → Inv n s → walkP n len s = some s' →
    Inv (n + len) s' := by
  intro len
  induction len with
  | zero => intro n s s' _ h hw; simp only [walkP, Option.some.injEq] at hw; subst hw; simpa using h
  | succ len ih =>
    intro n s s' hn h hw
    rw [walkP] at hw
    try simp only at hw
    split_ifs at hw with hc
    rw [show n + (len + 1) = n + 1 + len by ring]
    exact ih (n + 1) _ _ (by omega) (Inv_step hn h hc.2) hw

theorem filter_one : (Icc 1 1).filter Nat.Prime = ∅ := by decide

theorem Inv_one : Inv 1 ⟨0, 0, 0, 0, 10 ^ 30, 1, 0, 0⟩ := by
  refine ⟨by simp, by simp, ?_, ?_, ?_, le_rfl, by simp, by simp, fun x h5 h1 _ => by omega⟩
  · unfold th; rw [filter_one]; simp
  · unfold th; rw [filter_one]; simp
  · unfold Fp; rw [filter_one]; norm_num

theorem wk_1 : walkP 1 70 ⟨0, 0, 0, 0, 1000000000000000000000000000000, 1, 0, 0⟩ = some ⟨4262679877041210166836126056895, 4262679877041351795485327776952, 61586295149414284648264173551208, 61586295149417117220845375458757, 7824868159253603327835322564407, 61, 4110873864173205994258060627844, 4110873864173347622907262347771⟩ := by decide +kernel

theorem inv_1 : Inv 1 ⟨0, 0, 0, 0, 1000000000000000000000000000000, 1, 0, 0⟩ := Inv_one
theorem inv_71 : Inv 71 ⟨4262679877041210166836126056895, 4262679877041351795485327776952, 61586295149414284648264173551208, 61586295149417117220845375458757, 7824868159253603327835322564407, 61, 4110873864173205994258060627844, 4110873864173347622907262347771⟩ := walkP_spec 70 1 _ _ (by norm_num) inv_1 wk_1

/-- **`∏_{p ≤ x} p/(p−1) < e^γ log θ(x) + 2.50637/log θ(x)` for primes `5 ≤ x ≤ 71`.** -/
theorem mertens_product_kernel (x : ℕ) (hx : x.Prime) (h5 : 5 ≤ x) (h : x ≤ 71) :
    ∏ p ∈ (Icc 1 x).filter Nat.Prime, ((p : ℝ) / (p - 1)) <
      Real.exp eulerMascheroniConstant *
          Real.log (∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log p) +
        2.50637 / Real.log (∑ p ∈ (Icc 1 x).filter Nat.Prime, Real.log p) :=
  inv_71.2.2.2.2.2.2.2.2 x h5 (by omega) hx

end TernaryGoldbach.RSBounds.SmallTotientProduct
