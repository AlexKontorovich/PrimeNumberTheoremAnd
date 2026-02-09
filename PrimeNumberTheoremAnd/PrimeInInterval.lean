import PrimeNumberTheoremAnd.SecondaryDefinitions


blueprint_comment /--
\section{Converting prime number theorems to prime in short interval theorems}\label{short-sec}

In this section, bounds on $E_\theta$ are used to deduce the existence of primes in short intervals. (One could also proceed using $E_\pi$, but the bounds are messier and the results slightly weaker.)
-/

open Real Chebyshev Nat Finset

@[blueprint
  "pi-inc"
  (title := "Increase in pi iff prime in short interval")
  (statement := /--
  There is a prime in $(x, x+h]$ iff $\pi(x+h) > \pi(x)$.
  -/)
  (proof := /-- Both are equivalent to $\sum_{x < p \leq x+h} 1 > 0$.-/)
  (latexEnv := "lemma")
  (discussion := 904)]
lemma HasPrimeInInterval.iff_pi_ge (x h : ℝ) : HasPrimeInInterval x h ↔ pi (x + h) > pi x := by
  constructor
  · rintro ⟨p, hpprime, hxp, hpxh⟩
    have hfloorxh : p ≤ ⌊x + h⌋₊ := Nat.le_floor hpxh
    have hfloorx_lt : ⌊x⌋₊ < p := by
      by_cases hx0 : 0 ≤ x
      · exact (Nat.floor_lt hx0).2 hxp
      · have hp0 : 0 < p := hpprime.pos
        rw [Nat.floor_of_nonpos (le_of_not_ge hx0)]
        exact hp0
    have hfloorx_pred : ⌊x⌋₊ ≤ p - 1 := Nat.le_pred_of_lt hfloorx_lt
    have hpstep' : Nat.primeCounting' p < Nat.primeCounting' (p + 1) := by
      simpa [Nat.primeCounting'] using
        (Nat.count_lt_count_succ_iff (p := Nat.Prime) (n := p)).2 hpprime
    have hpstep : Nat.primeCounting (p - 1) < Nat.primeCounting p := by
      simpa [Nat.primeCounting_sub_one] using hpstep'
    have hnat : Nat.primeCounting ⌊x⌋₊ < Nat.primeCounting ⌊x + h⌋₊ := by
      exact lt_of_le_of_lt (Nat.monotone_primeCounting hfloorx_pred)
        (lt_of_lt_of_le hpstep (Nat.monotone_primeCounting hfloorxh))
    change (Nat.primeCounting ⌊x + h⌋₊ : ℝ) > (Nat.primeCounting ⌊x⌋₊ : ℝ)
    exact_mod_cast hnat
  · intro hpi
    change (Nat.primeCounting ⌊x + h⌋₊ : ℝ) > (Nat.primeCounting ⌊x⌋₊ : ℝ) at hpi
    have hnat : Nat.primeCounting ⌊x⌋₊ < Nat.primeCounting ⌊x + h⌋₊ := by
      exact_mod_cast hpi
    obtain ⟨p, hpprime, hp1, hp2⟩ := prime_in_gap' ⌊x⌋₊ ⌊x + h⌋₊ hnat
    refine ⟨p, hpprime, ?_, ?_⟩
    · exact lt_of_floor_lt <| lt_of_lt_of_le (Nat.lt_succ_self ⌊x⌋₊) hp1
    · have hp_floor : p ≤ ⌊x + h⌋₊ := Nat.lt_succ_iff.mp hp2
      have hfloor_pos : 0 < ⌊x + h⌋₊ := lt_of_lt_of_le hpprime.pos hp_floor
      have hxh_pos : 0 < x + h := Nat.pos_of_floor_pos hfloor_pos
      exact (Nat.cast_le.2 hp_floor).trans (Nat.floor_le hxh_pos.le)

-- this is a legacy piece of code that could be incorporated somehow into the proof of `HasPrimeInInterval.iff_theta_ge` below.

theorem theta_pos_implies_prime_in_interval {x y : ℝ} (_hxy : y < x) (h : θ x - θ y > 0) :
    HasPrimeInInterval y (x - y) := by
  have h_diff : θ x - θ y =
      ∑ p ∈ filter Prime (Icc 1 (floor x)), Real.log p -
      ∑ p ∈ filter Prime (Icc 1 (floor y)), Real.log p := by rfl
  obtain ⟨p, hp₁, hp₂, hp₃⟩ : ∃ p ∈ Icc 1 (floor x), p.Prime ∧ p > floor y := by
    contrapose! h
    exact h_diff.symm ▸ sub_nonpos_of_le (sum_le_sum_of_subset_of_nonneg
      (fun p hp ↦ by grind) fun _ _ _ ↦ log_nonneg <| one_le_cast.mpr <| Prime.pos <| by grind)
  have hx_nn : 0 ≤ x := by linarith [floor_pos.mp (hp₂.one_lt.le.trans (mem_Icc.mp hp₁).2)]
  have hp_le_x : (p : ℝ) ≤ x := floor_le (by positivity) |> le_trans (mod_cast mem_Icc.mp hp₁ |>.2)
  exact ⟨p, hp₂, lt_of_floor_lt hp₃, by grind⟩

@[blueprint
  "theta-inc"
  (title := "Increase in theta iff prime in short interval")
  (statement := /--
  There is a prime in $(x, x+h]$ iff $\theta(x+h) > \theta(x)$.
  -/)
  (proof := /-- Both are equivalent to $\sum_{x < p \leq x+h} \log p > 0$.-/)
  (latexEnv := "lemma")
  (discussion := 905)]
lemma HasPrimeInInterval.iff_theta_ge (x h : ℝ) : HasPrimeInInterval x h ↔ θ (x + h) > θ x := by
  constructor
  · rintro ⟨p, hpprime, hxp, hpxh⟩
    let s : Finset ℕ := filter Nat.Prime (Icc 0 ⌊x⌋₊)
    let t : Finset ℕ := filter Nat.Prime (Icc 0 ⌊x + h⌋₊)
    have hs : s ⊆ t := by
      intro q hq
      have hq' : q ∈ filter Nat.Prime (Icc 0 ⌊x⌋₊) := by simpa [s] using hq
      have hxxh : x ≤ x + h := le_of_lt (lt_of_lt_of_le hxp hpxh)
      rw [mem_filter] at hq' ⊢
      have hqIcc : q ∈ Icc 0 ⌊x + h⌋₊ := by
        exact mem_Icc.mpr ⟨(mem_Icc.mp hq'.1).1, le_trans (mem_Icc.mp hq'.1).2 (Nat.floor_mono hxxh)⟩
      exact ⟨hqIcc, hq'.2⟩
    have hp_in_t : p ∈ t := by
      have : p ∈ filter Nat.Prime (Icc 0 ⌊x + h⌋₊) := by
        exact Finset.mem_filter.mpr <| by
          refine ⟨mem_Icc.mpr ?_, hpprime⟩
          exact ⟨Nat.zero_le p, Nat.le_floor hpxh⟩
      simpa [t] using this
    have hp_notin_s : p ∉ s := by
      intro hpins
      have hpins' : p ∈ filter Nat.Prime (Icc 0 ⌊x⌋₊) := by simpa [s] using hpins
      rw [mem_filter, mem_Icc] at hpins'
      have hx_nn : 0 ≤ x := by
        have hfloor_pos : 0 < ⌊x⌋₊ := lt_of_lt_of_le hpprime.pos hpins'.1.2
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (Nat.floor_pos.mp hfloor_pos)
      exact (not_le_of_gt hxp) ((Nat.cast_le.2 hpins'.1.2).trans (Nat.floor_le hx_nn))
    have hnonneg : ∀ q ∈ t, q ∉ s → 0 ≤ Real.log q := by
      intro q hq _
      have hq' : q ∈ filter Nat.Prime (Icc 0 ⌊x + h⌋₊) := by simpa [t] using hq
      rw [mem_filter] at hq'
      exact Real.log_nonneg (Nat.one_le_cast.2 hq'.2.one_le)
    have hsum_lt : (∑ q ∈ s, Real.log q) < ∑ q ∈ t, Real.log q := by
      exact Finset.sum_lt_sum_of_subset hs hp_in_t hp_notin_s
        (Real.log_pos (Nat.one_lt_cast.2 hpprime.one_lt)) hnonneg
    simpa [Chebyshev.theta_eq_sum_Icc, s, t] using hsum_lt
  · intro htheta
    have hxh : x < x + h := by
      by_contra hle
      have hmono : θ (x + h) ≤ θ x := Chebyshev.theta_mono (le_of_not_gt hle)
      linarith
    have hprime : HasPrimeInInterval x ((x + h) - x) :=
      theta_pos_implies_prime_in_interval hxh (by linarith [htheta])
    simpa using hprime

@[blueprint
  "etheta-pi"
  (title := "Upper bound on Etheta implies prime in short interval")
  (statement := /--
  There is a prime in $(x, x+h]$ if $x E_\theta(x) + (x+h) E_\theta(x+h) < h$. -/)
  (proof := /-- Lower bound $\theta(x+h) - \theta(x)$ using $\theta(x+h) \geq x+h (1 - E_\theta(x+h))$ and $\theta(x) \leq x (1 + E_\theta(x))$ and apply Lemma \ref{theta-inc}. -/)
  (latexEnv := "lemma")
  (discussion := 906)]
lemma Eθ.hasPrimeInInterval (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    x * Eθ x + (x + h) * Eθ (x + h) < h → HasPrimeInInterval x h := by
  intro hE
  have hxh : 0 < x + h := by linarith
  have hx_bound : θ x ≤ x + x * Eθ x := by
    have hx_abs : x * Eθ x = |θ x - x| := by
      unfold Eθ
      field_simp [hx.ne']
    have habs : |θ x - x| ≤ x * Eθ x := by
      simpa [hx_abs] using (le_rfl : |θ x - x| ≤ |θ x - x|)
    linarith [abs_sub_le_iff.mp habs |>.1]
  have hxh_bound : (x + h) - (x + h) * Eθ (x + h) ≤ θ (x + h) := by
    have hxh_abs : (x + h) * Eθ (x + h) = |θ (x + h) - (x + h)| := by
      unfold Eθ
      field_simp [hxh.ne']
    have habs : |θ (x + h) - (x + h)| ≤ (x + h) * Eθ (x + h) := by
      simpa [hxh_abs] using (le_rfl : |θ (x + h) - (x + h)| ≤ |θ (x + h) - (x + h)|)
    linarith [abs_sub_le_iff.mp habs |>.2]
  have htheta : θ (x + h) > θ x := by
    linarith [hx_bound, hxh_bound, hE]
  exact (HasPrimeInInterval.iff_theta_ge x h).2 htheta


@[blueprint
  "etheta-num-pi"
  (title := "Numerical bound on Etheta implies prime in short interval")
  (statement := /--
  If $E_\theta(x) \leq \varepsilon(x_0)$ for all $x \geq x_0$, and $(2x+h) \varepsilon(x_0)  < h$, then there is a prime in $(x, x+h]$. -/)
  (proof := /-- Apply Lemma \ref{etheta-pi}. -/)
  (latexEnv := "lemma")
  (discussion := 907)]
lemma Eθ.numericalBound.hasPrimeInInterval {x₀ x h : ℝ} {ε : ℝ → ℝ} (hEθ : Eθ.numericalBound x₀ ε)
    (hh : 0 < h) (hx₀ : x₀ ≤ x) (hx : 0 < x) (hε : (2 * x + h) * ε x₀ < h) :
    HasPrimeInInterval x h := by
  have hxh : 0 < x + h := by linarith
  have hE₁ : Eθ x ≤ ε x₀ := hEθ x hx₀
  have hE₂ : Eθ (x + h) ≤ ε x₀ := hEθ (x + h) (by linarith [hx₀, hh])
  have h1 : x * Eθ x ≤ x * ε x₀ := mul_le_mul_of_nonneg_left hE₁ hx.le
  have h2 : (x + h) * Eθ (x + h) ≤ (x + h) * ε x₀ :=
    mul_le_mul_of_nonneg_left hE₂ hxh.le
  have hsum : x * Eθ x + (x + h) * Eθ (x + h) ≤ (2 * x + h) * ε x₀ := by
    nlinarith [h1, h2]
  exact Eθ.hasPrimeInInterval x h hx hh (lt_of_le_of_lt hsum hε)

@[blueprint
  "etheta-classical-pi"
  (title := "Classical bound on Etheta implies prime in short interval")
  (statement := /--
  If $E_\theta(x)$ enjoys a classical bound for all $x \geq x_0$, $x \geq \exp( R (2B/C)^2 )$ and $(2x+h) A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right) < h$, then there is a prime in $(x, x+h]$. -/)
  (proof := /-- Apply Lemma \ref{etheta-num-pi} and Lemma \ref{classical-to-numeric}. -/)
  (latexEnv := "lemma")
  (discussion := 909)]
lemma Eθ.classicalBound.hasPrimeInInterval {x₀ x h A B C R : ℝ} (hEθ : Eθ.classicalBound x₀ A B C R)
  (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hR : 0 < R) (hh : 0 < h) (hx : x₀ ≤ x) (hx' : x ≥ exp (R * (2 * B / C) ^ 2))
  (hb : (2 * x + h) * (admissible_bound A B C R x) < h) :
    HasPrimeInInterval x h := by
  sorry

@[blueprint
  "prime-gap-record-interval"
  (title := "Prime gap record implies prime in short interval")
  (statement := /--
  If there is a prime gap record $(g,p)$, then there is a prime in $(x,x+h]$ whenever $x < p$ and $h \geq g$. -/)
  (proof := /-- If $p_k$ is the largest prime less than or equal to $x$, then $p_{k+1} - p_k < g \leq h$, hence $x < p_{k+1} \leq x+h$, giving the claim. -/)
  (latexEnv := "lemma")
  (discussion := 908)]
lemma prime_gap_record.hasPrimeInInterval {g p : ℕ} {x h : ℝ} (hgap : prime_gap_record p g) (hx : x ≤ p) (hx' : x ≥ 2) (hh : h > g) :
    HasPrimeInInterval x h := by sorry
