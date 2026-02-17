import PrimeNumberTheoremAnd.SecondarySummary

blueprint_comment /--
\section{Numerical verification of Goldbach}\label{goldbach-sec}

We record here a simple way to convert prime in short interval theorems, together with numerical verification of even Goldbach, to numerical verification of odd Goldbach.

-/

namespace Goldbach

@[blueprint
  "even-goldbach"
  (title := "Even Goldbach conjecture up to a given height")
  (statement := /--
  We say that the even Goldbach conjecture is verified up to height $H$ if every even integer between $4$ and $H$ is the sum of two primes. -/)]
def even_conjecture (H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 4 H, Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

lemma even_conjecture_mono (H H' : ℕ) (h : even_conjecture H) (hh : H' ≤ H) : even_conjecture H' := by
  intro n hn; apply h; grind

@[blueprint
  "even-goldbach-test"
  (title := "Even Goldbach conjecture - unit test")
  (statement := /--
  The even Goldbach conjecture is verified up to height 30. -/)
  (proof := /-- This is a simple unit test, which can be verified by hand. -/)
  (latexEnv := "proposition")
  (discussion := 959)]
theorem even_goldbach_test : even_conjecture 30 := by
  intro n hn he
  fin_cases hn
  all_goals try grind
  · exact ⟨2, 2, by decide⟩
  · exact ⟨3, 3, by decide⟩
  · exact ⟨3, 5, by decide⟩
  · exact ⟨5, 5, by decide⟩
  · exact ⟨5, 7, by decide⟩
  · exact ⟨7, 7, by decide⟩
  · exact ⟨5, 11, by decide⟩
  · exact ⟨7, 11, by decide⟩
  · exact ⟨7, 13, by decide⟩
  · exact ⟨11, 11, by decide⟩
  · exact ⟨11, 13, by decide⟩
  · exact ⟨13, 13, by decide⟩
  · exact ⟨11, 17, by decide⟩
  · exact ⟨13, 17, by decide⟩

@[blueprint
  "odd-goldbach"
  (title := "Odd Goldbach conjecture up to a given height")
  (statement := /--
  We say that the odd Goldbach conjecture is verified up to height $H$ if every odd integer between $5$ and $H$ is the sum of three primes. -/)]
def odd_conjecture (H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 5 H, Odd n → ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

lemma odd_conjecture_mono (H H' : ℕ) (h : odd_conjecture H) (hh : H' ≤ H) : odd_conjecture H' := by
  intro n hn; apply h; grind

@[blueprint
  "even-to-odd-goldbach-triv"
  (title := "Even Goldbach implies odd Goldbach")
  (statement := /--
  If the even Goldbach conjecture is verified up to height $H$, then the odd Goldbach conjecture is verified up to height $H+3$. -/)
  (proof := /-- If $n$ is an odd integer between $5$ and $H+3$, then $n-3$ is an even integer between $4$ and $H$, so we can write $n-3 = p + q$ for some primes $p$ and $q$, and hence $n = p + q + 3$. -/)
  (latexEnv := "proposition")
  (discussion := 960)]
theorem even_to_odd_goldbach_triv (H : ℕ) (h : even_conjecture H) : odd_conjecture (H + 3) := by sorry

theorem odd_goldbach_test : odd_conjecture 33 := even_to_odd_goldbach_triv 30 even_goldbach_test

@[blueprint
  "even-to-odd-goldbach"
  (title := "Even Goldbach plus PNT in short interval implies odd Goldbach")
  (statement := /--
  If every interval $(x(1-1/\Delta), x]$ contains a prime for $x \geq x_0$, the even Goldbach conjecture is verified up to height $H$, and the odd Goldbach conjecture is verified up to height $x_0+4$, then the odd Goldbach conjecture is verified up to height $(H-4)\Delta + 4$. -/)
  (proof := /-- If $x \leq x_0+4$ then we are done by hypothesis, so assume $x_0+4 < x \leq H\Delta$.  By hypothesis, there is a prime $p$ with $(x-4)(1-1/\Delta) < p \leq x-4$.  Then $x-p$ is even, at least $4$, and at most $(x-4)/\Delta + 4 \leq H$, so is the sum of two primes, giving the claim. -/)
  (latexEnv := "proposition")
  (discussion := 961)]
theorem even_to_odd_goldbach (x₀ H Δ : ℕ)
    (hprime : ∀ x ≥ x₀, HasPrimeInInterval (x * (1 - 1 / Δ)) (x / Δ))
    (heven : even_conjecture H) (hodd : odd_conjecture (x₀ + 4)) :
    odd_conjecture ((H - 4) * Δ + 4) := by
  by_cases! hH : H < 4
  · simp_all [tsub_eq_zero_of_le hH.le, odd_conjecture]
  by_cases! Δ ≤ 1
  · interval_cases Δ
    · simp_all [odd_conjecture]
    · simp_all [odd_conjecture_mono (H + 3) H (even_to_odd_goldbach_triv H heven) (by linarith)]
  · intro n h ho
    by_cases! hn33 : n ≤ 8
    · exact odd_goldbach_test n (by grind : n ∈ Finset.Icc 5 33) ho
    by_cases! hn : n ≤ x₀ + 4
    · exact hodd n (by grind : n ∈ Finset.Icc 5 (x₀ + 4)) ho
    · obtain ⟨p, hp⟩ := hprime (n - 4) (by grind : n - 4 ≥ x₀)
      have hnpe : Even (n - p) :=
        have h2p : 2 < p := by
          rw [← Nat.cast_lt (α := ℝ)]
          calc
          _ = (8 - 4) * (1 - 1 / 2 : ℝ) := by norm_num
          _ < (n - 4) * (1 -  1 / 2 : ℝ) := by gcongr; norm_cast
          _ ≤ ↑(n - 4) * (1 -  1 / Δ : ℝ) := by gcongr <;> norm_cast; grind
          _ < p := hp.2.1
        ho.tsub_odd (hp.1.odd_of_ne_two h2p.ne')
      have hnp : (n - p) ∈ Finset.Icc 4 H := by
        have hpn4 : p ≤ n - 4 := by simpa [field] using hp.2.2
        have hpn : p ≤ n := hpn4.trans tsub_le_self
        refine Finset.mem_Icc.2 ⟨?_, ?_⟩
        · exact (le_tsub_iff_le_tsub (by grind) hpn).2 hpn4
        · have := hp.2.1
          rw [← Nat.cast_le (α := ℝ), Nat.cast_sub hpn]
          rw [Nat.cast_sub (by grind), mul_sub, mul_one, ← sub_add_eq_sub_sub, sub_lt_comm] at this
          refine this.le.trans ?_
          calc
          _ ≤ 4 + ((↑(H - 4) * Δ + 4) - 4) * (1 / Δ : ℝ) := by gcongr <;> norm_cast; grind
          _ ≤ _ := by simp [field, Nat.cast_sub hH]
      obtain ⟨q, r, hqr⟩ := heven (n - p) hnp hnpe
      refine ⟨p, q, r, hp.1, hqr.1, hqr.2.1, ?_⟩
      grind

@[blueprint
  "richstein-even-goldbach"
  (title := "Richstein's verification of even Goldbach")
  (statement := /-- \cite{richstein}
  The even Goldbach conjecture is verified up to $4 \times 10^{14}$. -/)
  (proof := /-- Numerical verification. -/)
  (latexEnv := "proposition")]
theorem richstein_goldbach : even_conjecture (4 * 10 ^ 14) := by sorry

@[blueprint
  "ramare-saouter-odd-goldbach"
  (title := "Ramaré and Saouter's verification of odd Goldbach")
  (statement := /-- \cite[Corollary 1]{ramare-saouter}
  The odd Goldbach conjecture is verified up to $1.13256 \times 10^{22}$. -/)
  (proof := /-- Combine Proposition \ref{richstein-even-goldbach}, Proposition \ref{even-to-odd-goldbach-triv}, and Theorem \ref{thm:ramare-saouter2003}. -/)
  (latexEnv := "proposition")
  (discussion := 962)]
theorem ramare_saouter_odd_goldbach : odd_conjecture 11325599999999886744004 := by
  have h1 := even_to_odd_goldbach 10726905042 (4 * 10 ^ 14) 28314000
    (fun x hx => RamareSaouter2003.has_prime_in_interval x (by norm_cast : (x : ℝ) > 10726905041))
    richstein_goldbach
  have h2 := odd_conjecture_mono (4 * 10 ^ 14 + 3) 10726905046
    (even_to_odd_goldbach_triv _ richstein_goldbach)
  norm_num at *
  exact h1 h2

@[blueprint
  "e-silva-herzog-piranian-even-goldbach"
  (title := "e Silva--Herzog--Piranian verification of even Goldbach")
  (statement := /-- \cite{eSHP}
  The even Goldbach conjecture is verified up to $4 \times 10^{18}$. -/)
  (proof := /-- Numerical verification. -/)
  (latexEnv := "proposition")]
theorem e_silva_herzog_piranian_goldbach : even_conjecture (4 * 10 ^ 18) := by sorry

@[blueprint
  "helfgott-odd-goldbach-finite"
  (title := "Helfgott's verification of odd Goldbach for small $n$")
  (statement := /-- \cite[Appendix C]{helfgott-goldbach-arxiv}
  The odd Goldbach conjecture is verified up to $1.1325 \times 10^{26}$. -/)
  (proof := /-- Combine Proposition \ref{e-silva-herzog-piranian-even-goldbach}, Proposition \ref{even-to-odd-goldbach-triv}, and Theorem \ref{thm:ramare-saouter2003}. -/)
  (latexEnv := "proposition")
  (discussion := 969)]
theorem helfgott_odd_goldbach_finite : odd_conjecture (11325 * 10 ^ 22) := by
  have h1 := even_to_odd_goldbach 10726905042 (4 * 10 ^ 18) 28314000
    (fun x hx => RamareSaouter2003.has_prime_in_interval x (by norm_cast : (x : ℝ) > 10726905041))
    e_silva_herzog_piranian_goldbach
  have h2 := odd_conjecture_mono (4 * 10 ^ 18 + 3) 10726905046
    (even_to_odd_goldbach_triv _ e_silva_herzog_piranian_goldbach)
  norm_num at *
  exact odd_conjecture_mono _ _ (h1 h2) (by grind)

blueprint_comment /-- The arguments in \cite[Appendix C]{helfgott-goldbach-arxiv} push the bound further than this, but require unpublished estimates of Ramare. However, similar arguments were established in \cite{kadiri-lumley}, and we present them here. -/

@[blueprint
  "e-silva-herzog-piranian-even-goldbach-ext"
  (title := "e Silva--Herzog--Piranian verification of even Goldbach (extended)")
  (statement := /-- \cite{eSHP}
  The even Goldbach conjecture is verified up to $4 \times 10^{18} + 4$. -/)
  (proof := /-- If $N = 4 \times 10^{18}$, use the fact that $211, 313, N-209, N-309$ are all prime. -/)
  (latexEnv := "proposition")]
theorem e_silva_herzog_piranian_goldbach_ext : even_conjecture (4 * 10 ^ 18 + 4) := by sorry

@[blueprint
  "kl-odd-goldbach-finite"
  (title := "Kadiri--Lumley's verification of odd Goldbach for small $n$")
  (statement := /-- \cite[Corollary 1.2]{kadiri-lumley}
  The odd Goldbach conjecture is verified up to $1966196911 \times 4 \times 10^{18}$. -/)
  (proof := /-- Combine Proposition \ref{e-silva-herzog-piranian-even-goldbach-ext}, Proposition \ref{even-to-odd-goldbach-triv}, and Theorem \ref{thm:prime_gaps_KL} with $x_0 = e^{60}$ and $\Delta = 1966090061$. -/)
  (latexEnv := "proposition")
  (discussion := 970)]
theorem kadiri_lumley_odd_goldbach_finite : odd_conjecture (1966196911 * 4 * 10 ^ 18) := by
  have h1 (x) (hx : x ≥ Real.exp 59) := KadiriLumley.has_prime_in_interval (Real.exp 59) x
    61 4.589e-9 20499925573 0.93 0.4522 1946282821 hx
  simp only [ge_iff_le, KadiriLumley.Table_2, Real.log_exp, List.mem_cons, Prod.mk.injEq,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, and_false, and_self, Nat.succ_ne_self, List.not_mem_nil,
    or_self, or_false, or_true, forall_const] at h1
  have h2 := even_to_odd_goldbach (⌈Real.exp 59⌉₊) (4 * 10 ^ 18 + 4) 1946282821
    (fun x hx => h1 x (Nat.le_of_ceil_le hx)) e_silva_herzog_piranian_goldbach_ext
  have h3 : ⌈Real.exp 59⌉₊ + 4 ≤ 11325 * 10 ^ 22 := by
    have : Real.exp 59 + 4 + 1 ≤ 11325 * 10 ^ 22 := by interval_decide
    grw [← Nat.cast_le (α := ℝ), Nat.cast_add, Nat.ceil_lt_add_one (Real.exp_nonneg _)]
    grind
  have h4 := h2 (odd_conjecture_mono _ (⌈Real.exp 59⌉₊ + 4) helfgott_odd_goldbach_finite h3)
  have p1 (x) (hx : x ≥ Real.exp 60) := KadiriLumley.has_prime_in_interval (Real.exp 60) x
    61 4.588e-9 20504393735 0.93 0.4527 1966196911 hx
  simp only [ge_iff_le, KadiriLumley.Table_2, Real.log_exp, List.mem_cons, Prod.mk.injEq,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, and_false, and_self, Nat.succ_ne_self, List.not_mem_nil,
    or_self, or_false, or_true, forall_const] at p1
  have p2 := even_to_odd_goldbach (⌈Real.exp 60⌉₊) (4 * 10 ^ 18 + 4) 1966196911
    (fun x hx => p1 x (Nat.le_of_ceil_le hx)) e_silva_herzog_piranian_goldbach_ext
  norm_num at *
  have p3 : ⌈Real.exp 60⌉₊ + 4 ≤ 7785131284000000000000000004 := by
    have : Real.exp 60 + 4 + 1 ≤ 7785131284000000000000000004 := by interval_decide
    grw [← Nat.cast_le (α := ℝ), Nat.cast_add, Nat.ceil_lt_add_one (Real.exp_nonneg _)]
    grind
  exact odd_conjecture_mono _ _ (p2 (odd_conjecture_mono _ (⌈Real.exp 60⌉₊ + 4) h4 p3)) (by grind)

end Goldbach
