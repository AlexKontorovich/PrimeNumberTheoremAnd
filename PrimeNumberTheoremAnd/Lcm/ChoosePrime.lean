import Architect
import PrimeNumberTheoremAnd.Lcm.Base
import PrimeNumberTheoremAnd.Lcm.Cert

namespace Lcm

open ArithmeticFunction hiding log
open Real Finset Nat
open scoped BigOperators

namespace six_primes


theorem exists_p_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i, p i ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0 := by
  -- define the “base point”
  let x : ℝ := √(n : ℝ)
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [x] using Numerical.sqrt_ge_X₀ (n := n) hn
  -- define ε once (this is where `hε` comes from if you use `set`)
  let ε : ℝ := gap.δ x

  -- (1) first prime at x
  obtain ⟨p₀, hp₀_prime, hp₀_lb, hp₀_ub⟩ :=
    gap.prime_in_Icc (x := x) hxX
  have hp₀_ub' : (p₀ : ℝ) ≤ x * (1 + ε) := by
    simpa [ε] using hp₀_ub

  -- (2) second prime at x*(1+ε)
  have hx1X : (X₀ : ℝ) ≤ x * (1 + ε) := by
    -- Cert lemma C4, rewritten to use `x`/`ε`
    -- (since x = √n and ε = δ x)
    simpa [x, ε] using Numerical.step1_ge_X₀ (n := n) hn

  obtain ⟨p₁, hp₁_prime, hp₁_lb, hp₁_ub⟩ :=
    gap.prime_in_Icc (x := x * (1 + ε)) hx1X

  have hp₁_ub' : (p₁ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    -- provider gives `p₁ ≤ (x*(1+ε)) * (1 + δ(x*(1+ε)))`
    -- Cert lemma C6 turns that into `≤ x*(1+ε)^2`
    refine le_trans (by simpa [ε] using hp₁_ub) ?_
    simpa [x, ε] using Numerical.step1_upper (n := n) hn

  -- (3) third prime at x*(1+ε)^2
  have hx2X : (X₀ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    simpa [x, ε] using Numerical.step2_ge_X₀ (n := n) hn

  obtain ⟨p₂, hp₂_prime, hp₂_lb, hp₂_ub⟩ :=
    gap.prime_in_Icc (x := x * (1 + ε) ^ 2) hx2X

  have hp₂_ub' : (p₂ : ℝ) ≤ x * (1 + ε) ^ 3 := by
    refine le_trans (by simpa [ε] using hp₂_ub) ?_
    simpa [x, ε] using Numerical.step2_upper (n := n) hn

  -- package the primes
  refine ⟨![p₀, p₁, p₂], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · -- StrictMono via "prev upper < next lower"
    refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i
    fin_cases i
    · -- p0 < p1
      exact cast_lt.mp (hp₀_ub'.trans_lt hp₁_lb)
    · -- p1 < p2
      exact cast_lt.mp (hp₁_ub'.trans_lt hp₂_lb)
  · -- upper bounds by cases
    intro i
    fin_cases i <;> norm_num
    · -- i = 0 : exponent is 1
      simpa [x, ε] using hp₀_ub'
    · -- i = 1 : exponent is 2
      simpa [x, ε] using hp₁_ub'
    · -- i = 2 : exponent is 3
      simpa [x, ε] using hp₂_ub'
  · -- √n < p0
    simpa [x] using hp₀_lb

theorem exists_q_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3, (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ ((3 : ℕ) - (i : ℕ)) ≤ q i) ∧
      q 2 < n := by
  let x : ℝ := √(n : ℝ)
  let ε : ℝ := gap.δ x
  let y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3
  let y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2
  let y2 : ℝ := (n : ℝ) / (1 + ε)

  -- apply provider at y0,y1,y2
  have hy0X : (X₀ : ℝ) ≤ y0 := by simpa [x, ε, y0] using Numerical.y0_ge_X₀ (n := n) hn
  have hy1X : (X₀ : ℝ) ≤ y1 := by simpa [x, ε, y1] using Numerical.y1_ge_X₀ (n := n) hn
  have hy2X : (X₀ : ℝ) ≤ y2 := by simpa [x, ε, y2] using Numerical.y2_ge_X₀ (n := n) hn

  obtain ⟨q₀, hq₀_prime, hq₀_lb, hq₀_ub⟩ := gap.prime_in_Icc (x := y0) hy0X
  obtain ⟨q₁, hq₁_prime, hq₁_lb, hq₁_ub⟩ := gap.prime_in_Icc (x := y1) hy1X
  obtain ⟨q₂, hq₂_prime, hq₂_lb, hq₂_ub⟩ := gap.prime_in_Icc (x := y2) hy2X

  -- chain the upper bounds
  have hq₀_ub' : (q₀ : ℝ) ≤ y1 := by
    -- q₀ ≤ y0*(1+δ y0) ≤ y1
    refine le_trans (by simpa [y0] using hq₀_ub) ?_
    simpa [x, ε, y0, y1] using Numerical.y0_mul_one_add_delta_le_y1 (n := n) hn

  have hq₁_ub' : (q₁ : ℝ) ≤ y2 := by
    refine le_trans (by simpa [y1] using hq₁_ub) ?_
    simpa [x, ε, y1, y2] using Numerical.y1_mul_one_add_delta_le_y2 (n := n) hn

  have hq₂_lt_n : q₂ < n := by
    -- q₂ ≤ y2*(1+δ y2) < n
    have hq₂_lt : (q₂ : ℝ) < (n : ℝ) := by
      have : (q₂ : ℝ) ≤ y2 * (1 + gap.δ y2) := by simpa [y2] using hq₂_ub
      exact lt_of_le_of_lt this (by simpa [x, ε, y2] using Numerical.y2_mul_one_add_delta_lt_n (n := n) hn)
    exact Nat.cast_lt.mp hq₂_lt

  -- package as Fin 3 → ℕ and prove StrictMono using lb/ub
  refine ⟨![q₀, q₁, q₂], ?_, ?_, ?_, hq₂_lt_n⟩
  · intro i; fin_cases i <;> assumption
  · refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i; fin_cases i
    · exact Nat.cast_lt.mp (hq₀_ub'.trans_lt hq₁_lb)
    · exact Nat.cast_lt.mp (hq₁_ub'.trans_lt hq₂_lb)
  · intro i
    fin_cases i <;> simp [x, ε, y0, y1, y2]
    · -- i=0 : y0 ≤ q0
      exact (le_of_lt hq₀_lb)
    · -- i=1 : y1 ≤ q1
      exact (le_of_lt hq₁_lb)
    · -- i=2 : y2 ≤ q2
      exact (le_of_lt hq₂_lb)


theorem prod_q_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) / (exists_q_primes hn).choose i) ≤
      ∏ i : Fin 3, (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / n) := by
  -- introduce the Cert abbreviation locally (purely for readability)
  -- (this does *not* change the theorem statement)
  have hb : (1 + gap.δ (√(n : ℝ))) = Numerical.b n := by
    simp [Numerical.b]

  -- Reindex RHS to match the `exists_q_primes` exponent pattern `((3 : ℝ) - (i : ℕ))`.
  -- After rewriting, all the bounds line up directly.
  -- First rewrite RHS into the `b n` form:
  -- (we do it as a `simp` rewrite so later `prod_q_rhs_reindex` applies cleanly)
  have :
      (∏ i : Fin 3, (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / n))
        =
      (∏ i : Fin 3, (1 + (Numerical.b n) ^ ((i : ℕ) + 1 : ℝ) / n)) := by
    simp [Numerical.b]
  -- use it
  rw [this]
  -- now reindex via Cert lemma
  rw [Numerical.prod_q_rhs_reindex (n := n)]

  -- pointwise compare factors and multiply
  apply Finset.prod_le_prod (fun _ _ => by positivity)
  intro i _
  -- target: `1 + 1/q_i ≤ 1 + (b n)^((3:ℝ)-(i:ℕ))/n`
  suffices
      (1 : ℝ) / (exists_q_primes hn).choose i ≤ (Numerical.b n) ^ ((3 : ℝ) - (i : ℕ)) / n by
    linarith

  -- Extract the lower bound on `q_i` from `exists_q_primes`
  have hq_lower :
      (n : ℝ) * (Numerical.b n) ^ (-((3 : ℝ) - (i : ℕ))) ≤ ((exists_q_primes hn).choose i : ℝ) := by
    -- `choose_spec.2.2.1` is the lower-bound field of `exists_q_primes`
    sorry
    -- simpa [Numerical.b] using (exists_q_primes hn).choose_spec.2.2.1 i

  -- Convert that to a reciprocal upper bound using the Cert lemma
  have hinv :
      (1 : ℝ) / ((exists_q_primes hn).choose i : ℝ) ≤ (Numerical.b n) ^ ((3 : ℝ) - (i : ℕ)) / n := by
    exact Numerical.inv_le_rpow_div_of_lower_bound (hn := hn) (t := (3 : ℝ) - (i : ℕ))
      (q := (exists_q_primes hn).choose i) hq_lower

  -- finish (remove explicit casts)
  simpa using hinv



theorem prod_p_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) /
        ((exists_p_primes hn).choose i * ((exists_p_primes hn).choose i + 1))) ≥
      ∏ i : Fin 3,
        (1 + 1 / ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))) := by
  -- goal `LHS ≥ RHS` is definitionaly `RHS ≤ LHS`
  refine Finset.prod_le_prod
    (fun i _ => by
      have hB : 0 < (1 + gap.δ (√(n : ℝ))) := Numerical.one_add_delta_pos (n := n) hn
      positivity [hB])
    (fun i _ => by
      -- i is already in context; no `intro` needed

      -- abbreviate the chosen primes
      let p : Fin 3 → ℕ := (exists_p_primes hn).choose

      -- collect the hypotheses needed by the Cert lemma
      have hp_prime : ∀ j, Nat.Prime (p j) := by
        intro j
        simpa [p] using (exists_p_primes hn).choose_spec.1 j

      have hp_mono : StrictMono p := by
        simpa [p] using (exists_p_primes hn).choose_spec.2.1

      have hp_ub :
          ∀ j, (p j : ℝ) ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (j + 1 : ℝ) := by
        intro j
        simpa [p] using (exists_p_primes hn).choose_spec.2.2.1 j

      have hsqrt_lt_p0 : √(n : ℝ) < p 0 := by
        simpa [p] using (exists_p_primes hn).choose_spec.2.2.2

      -- denominator comparison (this is the “real content”; all plumbing is in Cert)
      have hden :
          ((p i * (p i + 1) : ℕ) : ℝ)
            ≤ (1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n) := by
        simpa [p] using
          Numerical.p_mul_padd1_le_bound (hn := hn)
            (p := p) hp_prime hp_mono hp_ub hsqrt_lt_p0 i

      -- turn denominator inequality into the desired factor inequality
      have hpos : 0 < ((p i * (p i + 1) : ℕ) : ℝ) := by
        have hpipos : 0 < (p i) := (hp_prime i).pos
        -- `p i * (p i + 1)` is positive in ℕ, hence in ℝ
        positivity [hpipos]

      have hinv :
          (1 : ℝ) / ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))
            ≤ (1 : ℝ) / ((p i * (p i + 1) : ℕ) : ℝ) := by
        -- if a ≤ b and a>0 then 1/b ≤ 1/a
        exact one_div_le_one_div_of_le hpos hden

      -- add 1 to both sides
      have := add_le_add_left hinv 1
      -- rewrite the RHS denominator back to the form that appears in the goal
      simpa [p, Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm,
        mul_assoc, mul_comm, mul_left_comm] using this
    )

theorem pq_ratio_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 - ((4 : ℝ) * ∏ i, ((exists_p_primes hn).choose i : ℝ))
        / ∏ i, ((exists_q_primes hn).choose i : ℝ) ≥
    1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  -- Reduce to proving the fraction is bounded above, then use antitonicity of `1 - ·`.
  have hnpos : (0 : ℝ) < (n : ℝ) := Numerical.n_pos (n := n) hn
  have hbpos : 0 < (1 + gap.δ (√(n : ℝ))) := Numerical.one_add_delta_pos (n := n) hn

  have hfrac :
      ((4 : ℝ) * ∏ i, ((exists_p_primes hn).choose i : ℝ))
        / ∏ i, ((exists_q_primes hn).choose i : ℝ)
        ≤
      4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    -- Rewrite the RHS into a product ratio that matches the pointwise `p`/`q` bounds.
    rw [Numerical.pq_ratio_rhs_as_fraction (n := n) hn]
    gcongr <;> try
    (first
      | exact (exists_p_primes hn).choose_spec.2.2.1 _
      | exact (exists_q_primes hn).choose_spec.2.2.1 _
      | (refine Finset.prod_nonneg ?_; intro; intro; positivity [hbpos])
      | (refine Finset.prod_pos ?_; intro; intro; positivity [hnpos, hbpos])
      | (refine Finset.prod_pos ?_; intro; intro; exact_mod_cast ((exists_q_primes hn).choose_spec.1 _).pos)
    )
  -- Convert `A ≤ B` into `1 - A ≥ 1 - B`.
  have hsub :
      1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
        ≤
      1 - ((4 : ℝ) * ∏ i, ((exists_p_primes hn).choose i : ℝ))
            / ∏ i, ((exists_q_primes hn).choose i : ℝ) :=
    sub_le_sub_left hfrac 1

  -- goal is the same inequality but written with `≥`
  simpa [ge_iff_le] using hsub



end six_primes
end Lcm
