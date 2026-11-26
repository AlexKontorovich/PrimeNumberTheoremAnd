import RSBounds.PsiFinite.Bits

/-!
# Prime-power enumeration

`powsK_spec` describes the pairs `(d^i, i)` that `powsK` puts in front of a
list, and `sieveK_snd_spec` the whole list collected by `sieveK`: its entries
are exactly the pairs `(d^i, i)`, `i ≥ 2`, `lo ≤ d^i ≤ top`, for the traversed
base primes `d` (and whatever was there at the start), with pairwise distinct
first components when the base list consists of distinct primes.
-/

namespace PsiFinite

theorem powsUpK_zero (d q j top : ℕ) (E : List (ℕ × ℕ)) : powsUpK 0 d q j top E = E := rfl

theorem powsUpK_succ (f d q j top : ℕ) (E : List (ℕ × ℕ)) :
    powsUpK (f + 1) d q j top E =
      if q ≤ top then (q, j) :: powsUpK f d (q * d) (j + 1) top E else E := by
  show Bool.rec (motive := fun _ => List (ℕ × ℕ)) _ _ (Nat.ble q top) = _
  by_cases h : q ≤ top
  · rw [ite_eq_left h, show Nat.ble q top = true from Nat.ble_eq_true_of_le h]; rfl
  · rw [ite_eq_right h, show Nat.ble q top = false from by
      rw [Bool.eq_false_iff]; intro h'; exact h (Nat.le_of_ble_eq_true h')]

theorem powsK_zero (d q j lo top : ℕ) (E : List (ℕ × ℕ)) : powsK 0 d q j lo top E = E := rfl

theorem powsK_succ (f d q j lo top : ℕ) (E : List (ℕ × ℕ)) :
    powsK (f + 1) d q j lo top E =
      if q < lo then powsK f d (q * d) (j + 1) lo top E else powsUpK 64 d q j top E := by
  show Bool.rec (motive := fun _ => List (ℕ × ℕ)) _ _ (Nat.blt q lo) = _
  by_cases h : q < lo
  · rw [ite_eq_left h, show Nat.blt q lo = true from by simpa using h]; rfl
  · rw [ite_eq_right h, show Nat.blt q lo = false from by
      rw [Bool.eq_false_iff]; intro h'
      exact h (Nat.le_of_ble_eq_true h' : q + 1 ≤ lo)]

/-- The entries a power walk puts in front of `E`. -/
def PowSpec (d j lo top : ℕ) (new : List (ℕ × ℕ)) : Prop :=
  (∀ e, e ∈ new ↔ ∃ i, j ≤ i ∧ lo ≤ d ^ i ∧ d ^ i ≤ top ∧ e = (d ^ i, i)) ∧
    new.Pairwise (fun a b => a.1 < b.1)

theorem powsUpK_spec {d top : ℕ} (hd : 2 ≤ d) : ∀ (f j : ℕ) (E : List (ℕ × ℕ)),
    top < d ^ (j + f) → ∃ new, powsUpK f d (d ^ j) j top E = new ++ E ∧ PowSpec d j 0 top new := by
  have hmono : ∀ a b, a ≤ b → d ^ a ≤ d ^ b := fun a b h => Nat.pow_le_pow_right (by omega) h
  have hsmono : ∀ a b, a < b → d ^ a < d ^ b := fun a b h => Nat.pow_lt_pow_right hd h
  intro f
  induction f with
  | zero =>
    intro j E htop
    refine ⟨[], by simp [powsUpK_zero], ?_, List.Pairwise.nil⟩
    intro e; simp only [List.not_mem_nil, false_iff, not_exists, not_and]
    intro i hi _ hle; have := hmono j i hi; simp at htop; omega
  | succ f ih =>
    intro j E htop
    rw [powsUpK_succ]
    by_cases hq : d ^ j ≤ top
    · rw [ite_eq_left hq, ← pow_succ]
      obtain ⟨new, hnew, hspec, hpw⟩ := ih (j + 1) E (by rwa [show j + 1 + f = j + (f + 1) by ring])
      refine ⟨(d ^ j, j) :: new, by rw [hnew]; rfl, ?_, ?_⟩
      · intro e
        rw [List.mem_cons, hspec]
        constructor
        · rintro (rfl | ⟨i, hi, h0, h1, rfl⟩)
          · exact ⟨j, le_rfl, Nat.zero_le _, hq, rfl⟩
          · exact ⟨i, by omega, h0, h1, rfl⟩
        · rintro ⟨i, hi, h0, h1, rfl⟩
          rcases eq_or_lt_of_le hi with rfl | hi'
          · exact Or.inl rfl
          · exact Or.inr ⟨i, hi', h0, h1, rfl⟩
      · refine List.Pairwise.cons ?_ hpw
        intro b hb
        obtain ⟨i, hi, -, -, rfl⟩ := (hspec b).mp hb
        exact hsmono j i (by omega)
    · rw [ite_eq_right hq]
      refine ⟨[], rfl, ?_, List.Pairwise.nil⟩
      intro e; simp only [List.not_mem_nil, false_iff, not_exists, not_and]
      intro i hi _ hle; have := hmono j i hi; omega

theorem powsK_spec {d lo top : ℕ} (hd : 2 ≤ d) : ∀ (f j : ℕ) (E : List (ℕ × ℕ)),
    f ≤ 64 → top < d ^ (j + f) →
      ∃ new, powsK f d (d ^ j) j lo top E = new ++ E ∧ PowSpec d j lo top new := by
  have hmono : ∀ a b, a ≤ b → d ^ a ≤ d ^ b := fun a b h => Nat.pow_le_pow_right (by omega) h
  intro f
  induction f with
  | zero =>
    intro j E _ htop
    refine ⟨[], by simp [powsK_zero], ?_, List.Pairwise.nil⟩
    intro e; simp only [List.not_mem_nil, false_iff, not_exists, not_and]
    intro i hi _ hle; have := hmono j i hi; simp at htop; omega
  | succ f ih =>
    intro j E hf htop
    rw [powsK_succ]
    by_cases hq : d ^ j < lo
    · rw [ite_eq_left hq, ← pow_succ]
      obtain ⟨new, hnew, hspec, hpw⟩ :=
        ih (j + 1) E (by omega) (by rwa [show j + 1 + f = j + (f + 1) by ring])
      refine ⟨new, hnew, ?_, hpw⟩
      intro e; rw [hspec]
      constructor
      · rintro ⟨i, hi, h0, h1, rfl⟩; exact ⟨i, by omega, h0, h1, rfl⟩
      · rintro ⟨i, hi, h0, h1, rfl⟩
        rcases eq_or_lt_of_le hi with rfl | hi'
        · omega
        · exact ⟨i, hi', h0, h1, rfl⟩
    · rw [ite_eq_right hq]
      obtain ⟨new, hnew, hspec, hpw⟩ := powsUpK_spec hd 64 j E
        (lt_of_lt_of_le htop (hmono _ _ (by omega)))
      refine ⟨new, hnew, ?_, hpw⟩
      intro e; rw [hspec]
      constructor
      · rintro ⟨i, hi, -, h1, rfl⟩; exact ⟨i, hi, le_trans (by omega) (hmono j i hi), h1, rfl⟩
      · rintro ⟨i, hi, -, h1, rfl⟩; exact ⟨i, hi, Nat.zero_le _, h1, rfl⟩

/-- `E`'s entries are powers of primes outside `l`. -/
def PowsOutside (l : List ℕ) (E : List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ E, ∃ p, p.Prime ∧ p ∉ l ∧ ∃ i, 1 ≤ i ∧ e.1 = p ^ i

theorem prime_pow_ne {p q i k : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hi : 1 ≤ i) :
    p ^ i ≠ q ^ k := by
  intro h
  have : p ∣ q ^ k := h ▸ dvd_pow_self p (by omega)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow this))

/-- The prime powers collected by `sieveK`. -/
theorem sieveK_snd_spec {lo L hi top : ℕ} (htop : top < 2 ^ 66) : ∀ (l : List ℕ),
    l.Pairwise (· < ·) → (∀ d ∈ l, d.Prime) →
    ∀ (acc : ℕ) (E : List (ℕ × ℕ)), PowsOutside l E → E.Pairwise (fun a b => a.1 ≠ b.1) →
    let E' := (sieveK lo L hi top l acc E).2
    (∀ e, e ∈ E' ↔ e ∈ E ∨ ∃ d ∈ l, d * d ≤ hi ∧
        ∃ i, 2 ≤ i ∧ lo ≤ d ^ i ∧ d ^ i ≤ top ∧ e = (d ^ i, i)) ∧
      E'.Pairwise (fun a b => a.1 ≠ b.1) ∧ PowsOutside [] E' := by
  intro l
  induction l with
  | nil =>
    intro _ _ acc E hout hpw
    simp only [sieveK_nil, List.not_mem_nil, false_and, exists_false, or_false, implies_true,
      true_and]
    exact ⟨hpw, fun e he => by
      obtain ⟨p, hp, -, i, hi, he⟩ := hout e he; exact ⟨p, hp, by simp, i, hi, he⟩⟩
  | cons d ds ih =>
    intro hl hpr acc E hout hpw
    rw [List.pairwise_cons] at hl
    have hdp := hpr d List.mem_cons_self
    have hd2 := hdp.two_le
    by_cases h : d * d ≤ hi
    · rw [sieveK_cons_go h]
      obtain ⟨new, hnew, hspec, hnpw⟩ := powsK_spec (lo := lo) (top := top) hd2 64 2 E le_rfl
        (lt_of_lt_of_le htop (Nat.pow_le_pow_left hd2 _))
      have hdd : d * d = d ^ 2 := by ring
      rw [hdd, hnew]
      have hout' : PowsOutside ds (new ++ E) := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · obtain ⟨i, hi, -, -, rfl⟩ := (hspec e).mp he
          exact ⟨d, hdp, fun hm => lt_irrefl d (hl.1 d hm), i, by omega, rfl⟩
        · obtain ⟨p, hp, hpl, i, hi, he⟩ := hout e he
          exact ⟨p, hp, fun hm => hpl (List.mem_cons_of_mem _ hm), i, hi, he⟩
      have hpw' : (new ++ E).Pairwise (fun a b => a.1 ≠ b.1) := by
        rw [List.pairwise_append]
        refine ⟨hnpw.imp (fun h => h.ne), hpw, ?_⟩
        intro a ha b hb
        obtain ⟨i, hi, -, -, rfl⟩ := (hspec a).mp ha
        obtain ⟨p, hp, hpl, k, -, hb⟩ := hout b hb
        rw [hb]
        exact prime_pow_ne hdp hp (fun e => hpl (e ▸ List.mem_cons_self)) (by omega)
      obtain ⟨hm, hpw'', hout''⟩ := ih hl.2 (fun e he => hpr e (List.mem_cons_of_mem _ he))
        (acc ||| combK lo L d) (new ++ E) hout' hpw'
      refine ⟨?_, hpw'', hout''⟩
      intro e
      rw [hm, List.mem_append, hspec]
      constructor
      · rintro ((⟨i, hi, h0, h1, rfl⟩ | he) | ⟨e', he', h2, rest⟩)
        · exact Or.inr ⟨d, List.mem_cons_self, h, i, hi, h0, h1, rfl⟩
        · exact Or.inl he
        · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h2, rest⟩
      · rintro (he | ⟨e', he', h2, rest⟩)
        · exact Or.inl (Or.inr he)
        · rcases List.mem_cons.mp he' with rfl | he'
          · obtain ⟨i, hi, h0, h1, rfl⟩ := rest; exact Or.inl (Or.inl ⟨i, hi, h0, h1, rfl⟩)
          · exact Or.inr ⟨e', he', h2, rest⟩
    · rw [sieveK_cons_stop (by omega)]
      refine ⟨?_, hpw, fun e he => by
        obtain ⟨p, hp, -, i, hi, he⟩ := hout e he; exact ⟨p, hp, by simp, i, hi, he⟩⟩
      intro e
      constructor
      · intro he; exact Or.inl he
      · rintro (he | ⟨e', he', h2, -⟩)
        · exact he
        · exfalso
          rcases List.mem_cons.mp he' with rfl | he'
          · exact h h2
          · have := hl.1 e' he'
            exact h (le_trans (Nat.mul_le_mul this.le this.le) h2)

end PsiFinite
