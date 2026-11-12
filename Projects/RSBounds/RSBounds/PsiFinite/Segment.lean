import RSBounds.PsiFinite.Swar
import RSBounds.PsiFinite.Pows
import RSBounds.PsiFinite.Block

/-!
# Soundness of the segment checker

`checkSegK_sound`: if `checkSegK num den lo w B s = some s'` and `s` encloses
`ψ(lo-1)` and `log(lo-1)`, then `s'` encloses `ψ` and `log` at
`lo - 1 + 2^(w+1) B`, and `|ψ x - x| ≤ (num/den) √x` between the two points.
The facts about `basePrimes` it needs are collected in `BaseFacts`; they are
proved by kernel computation in `PsiFinite.BaseCert`.
-/

namespace PsiFinite

open Real Finset
open scoped ArithmeticFunction.vonMangoldt

/-- What the segment checker needs to know about `basePrimes`. -/
structure BaseFacts : Prop where
  sorted : basePrimes.Pairwise (· < ·)
  prime : ∀ d ∈ basePrimes, d.Prime ∧ d % 2 = 1
  complete : ∀ p, p.Prime → p % 2 = 1 → p * p ≤ baseCover → p ∈ basePrimes

/-- The real-variable conclusion on an interval. -/
def BoundOn (num den a b : ℕ) : Prop :=
  ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) → |Chebyshev.psi x - x| ≤ ((num : ℝ) / den) * Real.sqrt x

theorem BoundOn.trans {num den a b c : ℕ} (h1 : BoundOn num den a b) (h2 : BoundOn num den b c) :
    BoundOn num den a c := by
  intro x hx1 hx2
  by_cases hx : x ≤ b
  · exact h1 x hx1 hx
  · exact h2 x (by push Not at hx; exact hx.le) hx2

/-! ### Prime-power contributions -/

theorem ppK_eq (A A' llo lhi : ℕ) : ∀ (E : List (ℕ × ℕ)) (a b : ℕ),
    ppK A A' llo lhi E a b =
      (a + (E.map fun e => if A < e.1 ∧ e.1 ≤ A' then llo / e.2 else 0).sum,
       b + (E.map fun e => if A < e.1 ∧ e.1 ≤ A' then lhi / e.2 + 1 else 0).sum) := by
  intro E
  induction E with
  | nil => intro a b; rfl
  | cons e E ih =>
    intro a b
    show Bool.rec (motive := fun _ => ℕ × ℕ) _ _ (Bool.and (Nat.blt A e.1) (Nat.ble e.1 A')) = _
    by_cases h : A < e.1 ∧ e.1 ≤ A'
    · rw [show Bool.and (Nat.blt A e.1) (Nat.ble e.1 A') = true by
        simp [Nat.blt_eq, Nat.ble_eq, h.1, h.2]]
      show ppK A A' llo lhi E _ _ = _
      rw [ih]
      simp only [List.map_cons, List.sum_cons, ite_eq_left h, show Nat.div llo e.2 = llo / e.2 from rfl,
        show Nat.div lhi e.2 = lhi / e.2 from rfl, Nat.succ_eq_add_one, Nat.add_eq]
      ext <;> simp only <;> omega
    · rw [show Bool.and (Nat.blt A e.1) (Nat.ble e.1 A') = false by
        rw [Bool.eq_false_iff]; intro h'
        simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h'; exact h h']
      show ppK A A' llo lhi E _ _ = _
      rw [ih]; simp [ite_eq_right h]

/-- The list of proper prime powers of a segment. -/
structure PPExact (E : List (ℕ × ℕ)) (lo top : ℕ) : Prop where
  pow : ∀ e ∈ E, ∃ p, p.Prime ∧ 2 ≤ e.2 ∧ e.1 = p ^ e.2
  nodup : E.Pairwise (fun a b => a.1 ≠ b.1)
  complete : ∀ m, lo ≤ m → m ≤ top → IsPrimePow m → ¬ m.Prime → ∃ e ∈ E, e.1 = m

theorem PPExact.isPP {E : List (ℕ × ℕ)} {lo top : ℕ} (h : PPExact E lo top) {e : ℕ × ℕ}
    (he : e ∈ E) : IsPrimePow e.1 ∧ ¬ e.1.Prime := by
  obtain ⟨p, hp, h2, h1⟩ := h.pow e he
  rw [h1]
  exact ⟨hp.isPrimePow.pow (by omega), Nat.Prime.not_prime_pow' (by omega)⟩

theorem PPExact.vonMangoldt {E : List (ℕ × ℕ)} {lo top : ℕ} (h : PPExact E lo top) {e : ℕ × ℕ}
    (he : e ∈ E) : (Λ e.1 : ℝ) = Real.log e.1 / e.2 := by
  obtain ⟨p, hp, h2, h1⟩ := h.pow e he
  rw [h1, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  have : (e.2 : ℝ) ≠ 0 := by exact_mod_cast (show e.2 ≠ 0 by omega)
  field_simp

/-- The proper-prime-power part of a block as a sum over the list. -/
theorem pp_sum_eq_list {E : List (ℕ × ℕ)} {lo top A A' : ℕ} (h : PPExact E lo top)
    (hlo : lo ≤ A + 1) (htop : A' ≤ top) :
    ∑ m ∈ Ioc A A', (if IsPrimePow m ∧ ¬ m.Prime then (Λ m : ℝ) else 0) =
      (E.map fun e => if A < e.1 ∧ e.1 ≤ A' then (Λ e.1 : ℝ) else 0).sum := by
  set F := E.map Prod.fst
  have hF : F.Nodup := by
    rw [List.Nodup, List.pairwise_map]; exact h.nodup
  have e1 : (E.map fun e => if A < e.1 ∧ e.1 ≤ A' then (Λ e.1 : ℝ) else 0) =
      F.map (fun m => if A < m ∧ m ≤ A' then (Λ m : ℝ) else 0) := by
    rw [List.map_map]; rfl
  rw [e1, ← List.sum_toFinset _ hF, ← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc, List.mem_toFinset, F, List.mem_map]
  constructor
  · rintro ⟨⟨h1, h2⟩, hpp, hnp⟩
    obtain ⟨e, he, rfl⟩ := h.complete m (by omega) (by omega) hpp hnp
    exact ⟨⟨e, he, rfl⟩, h1, h2⟩
  · rintro ⟨⟨e, he, rfl⟩, h1, h2⟩
    exact ⟨⟨h1, h2⟩, h.isPP he⟩

theorem pp_bounds {E : List (ℕ × ℕ)} {lo top A A' llo lhi : ℕ} (h : PPExact E lo top)
    (hlo : lo ≤ A + 1) (htop : A' ≤ top) (hA : 1 ≤ A)
    (hllo : (llo : ℝ) ≤ D * Real.log A) (hlhi : D * Real.log A' ≤ lhi) :
    ((E.map fun e => if A < e.1 ∧ e.1 ≤ A' then llo / e.2 else 0).sum : ℝ) ≤
        D * ∑ m ∈ Ioc A A', (if IsPrimePow m ∧ ¬ m.Prime then (Λ m : ℝ) else 0) ∧
      D * ∑ m ∈ Ioc A A', (if IsPrimePow m ∧ ¬ m.Prime then (Λ m : ℝ) else 0) ≤
        ((E.map fun e => if A < e.1 ∧ e.1 ≤ A' then lhi / e.2 + 1 else 0).sum : ℝ) := by
  rw [pp_sum_eq_list h hlo htop, ← List.sum_map_mul_left]
  have hD := D_pos
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  push_cast [List.map_map]
  constructor
  · apply List.sum_le_sum; intro e he
    simp only [Function.comp]
    split_ifs with hb
    · rw [h.vonMangoldt he]
      obtain ⟨p, -, h2, -⟩ := h.pow e he
      have hj : (0 : ℝ) < e.2 := by exact_mod_cast (show 0 < e.2 by omega)
      calc ((llo / e.2 : ℕ) : ℝ) ≤ llo / e.2 := floor_div_le _ _
        _ ≤ D * Real.log A / e.2 := div_le_div_of_nonneg_right hllo hj.le
        _ ≤ D * (Real.log e.1 / e.2) := by
          rw [mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ hD.le
          apply div_le_div_of_nonneg_right _ hj.le
          exact Real.log_le_log hA0 (by exact_mod_cast hb.1.le)
    · simp
  · apply List.sum_le_sum; intro e he
    simp only [Function.comp]
    split_ifs with hb
    · rw [h.vonMangoldt he]
      obtain ⟨p, hp, h2, h1⟩ := h.pow e he
      have hj : (0 : ℝ) < e.2 := by exact_mod_cast (show 0 < e.2 by omega)
      have he1 : (0 : ℝ) < e.1 := by
        rw [h1]; exact_mod_cast pow_pos hp.pos _
      calc D * (Real.log e.1 / e.2) ≤ D * Real.log A' / e.2 := by
            rw [mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ hD.le
            apply div_le_div_of_nonneg_right _ hj.le
            exact Real.log_le_log he1 (by exact_mod_cast hb.2)
        _ ≤ lhi / e.2 := div_le_div_of_nonneg_right hlhi hj.le
        _ ≤ ((lhi / e.2 + 1 : ℕ) : ℝ) := by push_cast; exact le_floor_div_add_one _ _ (by omega)
    · simp

/-! ### The block loop -/

theorem blockLoopK_zero (num den h W mask : ℕ) (E : List (ℕ × ℕ)) (A Y : ℕ) (s : St) :
    blockLoopK num den h W mask E 0 A Y s = some s := rfl

theorem blockLoopK_succ (num den h W mask : ℕ) (E : List (ℕ × ℕ)) (B A Y : ℕ) (s : St) :
    blockLoopK num den h W mask E (B + 1) A Y s =
      (blockStep num den A h (Y &&& mask)
        (ppK A (A + h) s.llo (s.lhi + logIncHi A h) E 0 0).1
        (ppK A (A + h) s.llo (s.lhi + logIncHi A h) E 0 0).2 s).bind
        (fun s' => blockLoopK num den h W mask E B (A + h) (Y >>> W) s') := by
  show Option.rec (motive := fun _ => Option St) none _ _ = _
  cases blockStep num den A h (Y &&& mask) _ _ s <;> rfl

theorem blockLoopK_sound {num den W mask lo top : ℕ} {E : List (ℕ × ℕ)} {Y A0 : ℕ}
    (hnum : 0 < num) (hden : 0 < den) (hW : 1 ≤ W) (hA0 : Even A0) (hA02 : 2 ≤ A0)
    (hE : PPExact E lo top) (hlo : lo ≤ A0 + 1) (B : ℕ) (htop : A0 + 2 * W * B ≤ top)
    (hcount : ∀ k < B, (((Y >>> (W * k)) &&& mask : ℕ) : ℝ) =
      ∑ j ∈ range W, (if (A0 + 2 * W * k + 1 + 2 * j).Prime then (1 : ℝ) else 0)) :
    ∀ n k0 (s s' : St), k0 + n ≤ B →
      blockLoopK num den (2 * W) W mask E n (A0 + 2 * W * k0) (Y >>> (W * k0)) s = some s' →
      Encl (A0 + 2 * W * k0) s →
      Encl (A0 + 2 * W * (k0 + n)) s' ∧
        (0 < n → BoundOn num den (A0 + 2 * W * k0) (A0 + 2 * W * (k0 + n))) := by
  intro n
  induction n with
  | zero =>
    intro k0 s s' _ hrun hs
    rw [blockLoopK_zero] at hrun; cases hrun
    exact ⟨by simpa using hs, fun h => absurd h (lt_irrefl 0)⟩
  | succ n ih =>
    intro k0 s s' hk hrun hs
    rw [blockLoopK_succ] at hrun
    set A := A0 + 2 * W * k0
    cases hb : blockStep num den A (2 * W) ((Y >>> (W * k0)) &&& mask)
        (ppK A (A + 2 * W) s.llo (s.lhi + logIncHi A (2 * W)) E 0 0).1
        (ppK A (A + 2 * W) s.llo (s.lhi + logIncHi A (2 * W)) E 0 0).2 s with
    | none => rw [hb] at hrun; cases hrun
    | some s1 =>
    rw [hb] at hrun
    simp only [Option.bind_some] at hrun
    have hAev : Even A := by
      simp only [A]; exact hA0.add (by rw [mul_assoc]; exact even_two_mul _)
    have hA2 : 2 ≤ A := by simp only [A]; omega
    rw [ppK_eq] at hb
    simp only [zero_add] at hb
    have hAt : A + 2 * W ≤ top := by
      simp only [A]; nlinarith
    have hlogA' : D * Real.log ((A + 2 * W : ℕ) : ℝ) ≤ ((s.lhi + logIncHi A (2 * W) : ℕ) : ℝ) := by
      obtain ⟨-, li2⟩ := logInc_bounds (A := A) (h := 2 * W) (by omega) (by omega)
      have h4 := hs.2.2.2
      push_cast; push_cast at li2; linarith
    obtain ⟨pb1, pb2⟩ := pp_bounds hE (by simp only [A]; omega) hAt (by omega) hs.2.2.1 hlogA'
    obtain ⟨hs1, hbd1⟩ := blockStep_sound (A := A) (W := W) hnum hden hAev hA2 hW hb hs
      (hcount k0 (by omega)) pb1 pb2
    have e1 : A + 2 * W = A0 + 2 * W * (k0 + 1) := by simp only [A]; ring
    have e2 : (Y >>> (W * k0)) >>> W = Y >>> (W * (k0 + 1)) := by
      rw [← Nat.shiftRight_add]; congr 1
    rw [e1] at hs1 hbd1 hrun
    rw [e2] at hrun
    obtain ⟨hs2, hbd2⟩ := ih (k0 + 1) s1 s' (by omega) hrun hs1
    refine ⟨by rwa [show k0 + (n + 1) = k0 + 1 + n by ring], fun _ => ?_⟩
    rw [show k0 + (n + 1) = k0 + 1 + n by ring]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [add_zero]; exact hbd1
    · exact BoundOn.trans hbd1 (hbd2 hn)

/-! ### The segment -/

theorem cnt_primes {X lo L W k : ℕ} (hX : ∀ i, X.testBit i = true ↔ i < L ∧ (lo + 2 * i).Prime)
    (hk : W * (k + 1) ≤ L) (hlo : 1 ≤ lo) :
    ((cnt X (W * k) W : ℕ) : ℝ) =
      ∑ j ∈ range W, (if (lo - 1 + 2 * W * k + 1 + 2 * j).Prime then (1 : ℝ) else 0) := by
  unfold cnt; push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hjW := Finset.mem_range.mp hj
  have hi : W * k + j < L := by nlinarith
  have e : lo - 1 + 2 * W * k + 1 + 2 * j = lo + 2 * (W * k + j) := by
    have : 2 * W * k = 2 * (W * k) := by ring
    omega
  rw [e]
  by_cases hp : (lo + 2 * (W * k + j)).Prime
  · have := (hX _).mpr ⟨hi, hp⟩; simp [this, hp]
  · have : X.testBit (W * k + j) = false := by
      rw [Bool.eq_false_iff]; intro h; exact hp ((hX _).mp h).2
    simp [this, hp]

/-- **Soundness of the segment checker.** -/
theorem checkSegK_sound (hb : BaseFacts) {num den lo w B : ℕ} {s s' : St}
    (hnum : 0 < num) (hden : 0 < den) (hrun : checkSegK num den lo w B s = some s')
    (hs : Encl (lo - 1) s) :
    Encl (lo - 1 + 2 * 2 ^ w * B) s' ∧
      (0 < B → BoundOn num den (lo - 1) (lo - 1 + 2 * 2 ^ w * B)) := by
  unfold checkSegK at hrun
  simp only [Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.mul_eq, Nat.add_eq, Nat.sub_eq] at hrun
  set W := 2 ^ w with hWdef
  set L := W * B with hLdef
  set top := lo + 2 * L - 1 with htopdef
  set E0 := powsK 64 2 4 2 lo top []
  set r := sieveK lo L (top - 1) top basePrimes 0 E0
  cases hc : ((lo.mod 2).beq 1 && Nat.ble 3 lo && top.ble baseCover) with
  | false => rw [hc] at hrun; cases hrun
  | true =>
  rw [hc] at hrun
  change blockLoopK num den (2 * W) W (2 ^ W - 1) r.2 B (lo - 1)
    (swarK L w ((2 ^ L - 1).xor (r.1.land (2 ^ L - 1))) 0) s = some s' at hrun
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hc
  obtain ⟨⟨hlo2, hlo3⟩, htopc⟩ := hc
  have hlo2' : lo % 2 = 1 := hlo2
  have hW : 1 ≤ W := Nat.one_le_two_pow
  have htop66 : top < 2 ^ 66 := lt_of_le_of_lt htopc (by norm_num [baseCover])
  have hodd : ∀ d ∈ basePrimes, d % 2 = 1 ∧ 3 ≤ d := by
    intro d hd
    obtain ⟨hp, ho⟩ := hb.prime d hd
    refine ⟨ho, ?_⟩
    rcases hp.eq_two_or_odd with h | h
    · omega
    · have := hp.two_le; omega
  -- the prime bitset
  have hX : ∀ i, ((2 ^ L - 1).xor (r.1.land (2 ^ L - 1))).testBit i = true ↔
      i < L ∧ (lo + 2 * i).Prime := by
    intro i
    apply primeBits_testBit hb.sorted hodd _ hlo2' hlo3
    · intro i hi; omega
    · intro p hp hpo hpp
      exact hb.complete p hp hpo (by omega)
  -- the prime powers
  obtain ⟨new2, hnew2, hspec2, hpw2⟩ :=
    powsK_spec (d := 2) (lo := lo) (top := top) le_rfl 64 2 [] le_rfl
      (lt_of_lt_of_le htop66 (by norm_num))
  have hE0 : E0 = new2 := by
    simp only [E0]; rw [show (4 : ℕ) = 2 ^ 2 by norm_num, hnew2, List.append_nil]
  have hout : PowsOutside basePrimes E0 := by
    intro e he
    rw [hE0] at he
    obtain ⟨i, hi, -, -, rfl⟩ := (hspec2 e).mp he
    exact ⟨2, Nat.prime_two, fun h => by have := (hodd 2 h).1; omega, i, by omega, rfl⟩
  have hpw0 : E0.Pairwise (fun a b => a.1 ≠ b.1) := by
    rw [hE0]; exact hpw2.imp (fun h => h.ne)
  obtain ⟨hmem, hpwr, -⟩ := sieveK_snd_spec (lo := lo) (L := L) (hi := top - 1) htop66 basePrimes
    hb.sorted (fun d hd => (hb.prime d hd).1) 0 E0 hout hpw0
  have hE : PPExact r.2 lo top := by
    refine ⟨?_, hpwr, ?_⟩
    · intro e he
      rcases (hmem e).mp he with he | ⟨d, hd, -, i, hi, -, -, rfl⟩
      · rw [hE0] at he
        obtain ⟨i, hi, -, -, rfl⟩ := (hspec2 e).mp he
        exact ⟨2, Nat.prime_two, hi, rfl⟩
      · exact ⟨d, (hb.prime d hd).1, hi, rfl⟩
    · intro m hm1 hm2 hpp hnp
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
      have hk2 : 2 ≤ k := by
        by_contra h
        have : k = 1 := by omega
        subst this; exact hnp (by simpa using hp)
      by_cases hp2 : p = 2
      · subst hp2
        refine ⟨(2 ^ k, k), (hmem _).mpr (Or.inl ?_), rfl⟩
        rw [hE0]; exact (hspec2 _).mpr ⟨k, hk2, hm1, hm2, rfl⟩
      · have hpo : p % 2 = 1 := by
          rcases hp.eq_two_or_odd with h | h
          · exact absurd h hp2
          · exact h
        have hpp' : p * p ≤ p ^ k := by
          rw [← pow_two]; exact Nat.pow_le_pow_right hp.pos hk2
        have hsq : p * p ≤ top - 1 := by
          have h1 : (p * p) % 2 = 1 := by rw [Nat.mul_mod, hpo]
          have h2 : top % 2 = 0 := by omega
          omega
        refine ⟨(p ^ k, k), (hmem _).mpr (Or.inr ⟨p, hb.complete p hp hpo (by omega), hsq,
          k, hk2, hm1, hm2, rfl⟩), rfl⟩
  -- the block counts
  have hcount : ∀ k < B, ((((swarK L w ((2 ^ L - 1).xor (r.1.land (2 ^ L - 1))) 0) >>> (W * k)) &&&
      (2 ^ W - 1) : ℕ) : ℝ) =
      ∑ j ∈ range W, (if (lo - 1 + 2 * W * k + 1 + 2 * j).Prime then (1 : ℝ) else 0) := by
    intro k hk
    have hk' : W * (k + 1) ≤ L := by simp only [L]; exact Nat.mul_le_mul_left _ hk
    rw [swarK_block L _ w k hk']
    exact cnt_primes hX hk' (by omega)
  have hA0 : Even (lo - 1) := by
    rw [Nat.even_iff]; omega
  have h2L : lo - 1 + 2 * W * B ≤ top := by
    have : 2 * W * B = 2 * L := by simp only [L]; ring
    omega
  have hloop := blockLoopK_sound hnum hden hW hA0 (by omega) hE (by omega) B h2L hcount
    B 0 s s' (by omega) (by simpa using hrun) (by simpa using hs)
  simp only [mul_zero, add_zero, zero_add] at hloop
  exact hloop

/-- The form used by the generated assembly modules. -/
theorem seg_chain (hb : BaseFacts) {num den lo w B : ℕ} {s s' : St}
    (h : checkSegK num den lo w B s = some s') {A A' : ℕ} (hA : lo - 1 = A)
    (hA' : A + 2 * 2 ^ w * B = A') (hB : 0 < B) (hs : Encl A s)
    (hnum : 0 < num := by decide) (hden : 0 < den := by decide) :
    Encl A' s' ∧ BoundOn num den A A' := by
  subst hA hA'
  exact ⟨(checkSegK_sound hb hnum hden h hs).1, (checkSegK_sound hb hnum hden h hs).2 hB⟩

end PsiFinite
