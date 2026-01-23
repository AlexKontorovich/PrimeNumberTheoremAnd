import Architect
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.NumberTheory.Bertrand
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.FKS2
import PrimeNumberTheoremAnd.Dusart
import PrimeNumberTheoremAnd.BKLNW_app

blueprint_comment /--
\section{Summary of results}
-/

blueprint_comment /--
Here we list some papers that we plan to incorporate into this section in the future, and list
some results that have not yet been moved into dedicated paper sections.

References to add:

Dusart \cite{Dusart2018}

PT: D. J. Platt and T. S. Trudgian, The error term in the prime number theorem,
Math. Comp. 90 (2021), no. 328, 871–881.

JY: D. R. Johnston, A. Yang, Some explicit estimates for the error term in the prime number
theorem, arXiv:2204.01980.
-/

open Finset Nat Real


@[blueprint "thm:pt_2"
  (title := "PT Corollary 2")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 235 x (\log x)^{0.52} \exp(-0.8 \sqrt{\log x})
  \]
  for all $x \geq \exp(2000)$.
  -/)
  (latexEnv := "theorem")]
theorem PT.corollary_2 : Eπ.classicalBound 235 1.52 0.8 1 (exp 2000) := by
  have := FKS2.corollary_22
  intro x hx
  have hx2 : x ≥ 2 := by grind [add_one_le_exp 2000]
  refine (this x hx2).trans ?_
  simp only [admissible_bound]; norm_num
  suffices h_div : 92211 / 10000 * log x ^ (3 / 2 : ℝ) *
    exp (-(2119 / 2500) + (4 / 5)) ≤ 235 * log x ^ (38 / 25 : ℝ) by
    (convert mul_le_mul_of_nonneg_right h_div (exp_nonneg (-(4 / 5))) using 1; rw [exp_add]; ring_nf)
    norm_num [mul_assoc, ← exp_add]
  suffices h_div : 92211 / 10000 * exp (-(2119 / 2500) + (4 / 5)) ≤
      235 * log x ^ (38 / 25 - 3 / 2 : ℝ) by
    convert mul_le_mul_of_nonneg_right h_div (rpow_nonneg (log_nonneg
      (show x ≥ 1 by linarith)) (3 / 2 : ℝ)) using 1 <;> ring_nf
    rw [← rpow_add (log_pos (by linarith : x > 1))]
    norm_num
  exact (mul_le_mul_of_nonneg_left
      (rpow_le_rpow (by positivity)
        (show log x ≥ 1 by nlinarith [log_exp 2000, log_le_log (by positivity) hx]) (by positivity))
      (by positivity)).trans' (by
      norm_num
      nlinarith [exp_pos (-(2119 / 2500) + 4 / 5), exp_neg (-(2119 / 2500) + 4 / 5),
        mul_inv_cancel₀ <| ne_of_gt <| exp_pos (-(2119 / 2500) + 4 / 5),
        add_one_le_exp (-(2119 / 2500) + 4 / 5), add_one_le_exp (-(-(2119 / 2500) + 4 / 5))])

@[blueprint
  "thm:jy_13"
  (title := "JY Corollary 1.3")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 9.59 x (\log x)^{0.515} \exp(-0.8274 \sqrt{\log x})
  \]
  for all $x \geq 2$.
  -/)
  (latexEnv := "theorem")]
theorem JY.corollary_1_3 : Eπ.classicalBound 9.59 1.515 0.8274 1 2 := by
  intro x hx
  convert FKS2.corollary_22 x using 1
  norm_num [admissible_bound]
  constructor
  · intro
    convert FKS2.corollary_22 x using 1
    norm_num [admissible_bound]
  · refine fun h ↦ (h hx).trans ?_
    suffices h_div : 92211 / 10000 * exp (-(2119 / 2500)) ≤
        959 / 100 * log x ^ (303 / 200 - 3 / 2 : ℝ) * exp (-(4137 / 5000)) by
      convert mul_le_mul_of_nonneg_left h_div
        (rpow_nonneg (log_nonneg (by grind : (1 : ℝ) ≤ x)) (3 / 2)) using 1
      · ring
      · rw [show (303 / 200 : ℝ) = 3 / 2 + (303 / 200 - 3 / 2) by grind,
            rpow_add (log_pos (by grind))]; ring_nf
    suffices h_exp : 92211 / 10000 * exp (-(2119 / 2500) + 4137 / 5000) ≤
        959 / 100 * log x ^ (303 / 200 - 3 / 2 : ℝ) by
      convert mul_le_mul_of_nonneg_right h_exp (exp_nonneg (-(4137 / 5000))) using 1
      · rw [mul_assoc, ← exp_add]; ring_nf
    refine le_trans ?_ <| mul_le_mul_of_nonneg_left (rpow_le_rpow (by grind)
      (log_two_gt_d9.le.trans (log_le_log (by grind) hx)) (by grind)) (by grind)
    norm_num
    refine (mul_le_mul_of_nonneg_left (exp_le_one_iff.mpr (by grind)) (by grind)).trans ?_
    norm_num
    rw [← log_le_log_iff (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_rpow (by positivity),
        div_mul_eq_mul_div, add_div', le_div_iff₀] <;>
          norm_num [← log_rpow, mul_comm, ← log_mul, log_le_log_iff]


@[blueprint
  "thm:jy_14"
  (title := "JY Theorem 1.4")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 0.028 x (\log x)^{0.801}
    \exp(-0.1853 \log^{3/5} x / (\log \log x)^{1/5}))
  \]
  for all $x \geq 2$.
  -/)
  (latexEnv := "theorem")]
theorem JY.theorem_1_4 : Eπ.vinogradovBound 0.028 0.801 0.1853 23 := sorry

blueprint_comment /-- TODO: input other results from JY -/

-- def HasPrimeInInterval (x h : ℝ) : Prop := ∃ p : ℕ, Prime p ∧ x < p ∧ p ≤ x + h

@[blueprint
  "thm:schoenfeld1976"
  (title := "Schoenfeld 1976")
  (statement := /--
  If $x > 2010760$, then there is a prime in the interval
  \[
  \left( x\left(1 - \frac{1}{15697}\right), x \right].
  \]
  -/)
  (latexEnv := "theorem")]
theorem Schoenfeld1976.has_prime_in_interval (x : ℝ) (hx : x > 2010760) :
    HasPrimeInInterval (x*(1-1/15697)) (x/15697) := by sorry

@[blueprint
  "thm:ramare-saouter2003"
  (title := "Ramaré-Saouter 2003")
  (statement := /--
  If $x > 10,726,905,041$, then there is a prime in the interval $(x(1-1/28314000), x]$.
  -/)
  (latexEnv := "theorem")]
theorem RamareSaouter2003.has_prime_in_interval (x : ℝ) (hx : x > 10726905041) :
    HasPrimeInInterval (x*(1-1/28314000)) (x/28314000) := by sorry

/-- The value of `ε` from Table 8 at `n = 53` is `1.11990 × 10⁻⁹`. -/
lemma RamareSaouter2003.epsilon_val : BKLNW_app.table_8_ε 53 = 1.11990e-9 := by
  norm_num [BKLNW_app.table_8_ε]

/-- Numerical inequality: `δ · (1 + M₀) > m₀ + M₀ for X₀ = e⁵³` and `δ = 1/204879661`. -/
lemma RamareSaouter2003.numerical_ineq :
    let ε := 1.11990e-9
    let X₀ := exp 53
    let m₀ := ε + 1.03883 * (X₀ ^ (-1 / 2 : ℝ) + X₀ ^ (-2 / 3 : ℝ) + X₀ ^ (-4 / 5 : ℝ))
    let M₀ := ε
    let δ := 1 / 204879661
    δ * (1 + M₀) > m₀ + M₀ := by
  norm_num [exp_pos, rpow_def_of_pos, exp_pos]
  have h_exp_bound : exp (-(53 / 2)) < 1 / 10 ^ 11 ∧ exp (-(106 / 3)) < 1 / 10 ^ 15 ∧
      exp (-(212 / 5)) < 1 / 10 ^ 18 := by
    field_simp
    refine ⟨?_, ?_, ?_⟩
    · rw [exp_neg, inv_mul_eq_div, div_lt_one (by positivity)]
      have := exp_one_gt_d9.le
      rw [show exp (53 / 2) = (exp 1) ^ 26 * exp (1 / 2) by
        rw [← exp_nat_mul, ← exp_add]; ring_nf]
      nlinarith [add_one_le_exp (1 / 2), pow_le_pow_left₀ (by positivity) this 26]
    · rw [exp_neg, mul_inv_lt_iff₀ (by positivity)]
      have := exp_one_gt_d9.le
      norm_num1 at *
      rw [show exp (106 / 3) = (exp 1) ^ 35 * exp (1 / 3) by
        rw [← exp_nat_mul, ← exp_add]; ring_nf]
      nlinarith [add_one_le_exp (1 / 3), pow_le_pow_left₀ (by positivity) this 35]
    · rw [exp_neg, mul_inv_lt_iff₀ (by positivity)]
      have := exp_one_gt_d9.le
      rw [show exp (212 / 5) = (exp 1) ^ 42 * exp (2 / 5) by
        rw [← exp_nat_mul, ← exp_add]; ring_nf]
      nlinarith [add_one_le_exp (2 / 5), pow_le_pow_left₀ (by positivity) this 42]
  linarith [exp_pos (-(53 / 2)), exp_pos (-(106 / 3)), exp_pos (-(212 / 5))]

@[blueprint
  "thm:ramare_saouter2003-2"
  (title := "Ramaré-Saouter 2003 (2)")
  (statement := /-- If $x > \exp(53)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{204879661}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem RamareSaouter2003.has_prime_in_interval_2 (x : ℝ) (hx : x > exp 53) :
    HasPrimeInInterval (x * (1 - 1 / 204879661)) (x / 204879661) := by
  have h_chebyshev : θ x > θ (x * (1 - 1 / 204879661)) := by
    have hθ_bounds : θ x ≥ x * (1 - (BKLNW_app.table_8_ε 53 +
          1.03883 * (exp 53) ^ (-1 / 2 : ℝ) + 1.03883 * (exp 53) ^ (-2 / 3 : ℝ) + 1.03883 * (exp 53) ^ (-4 / 5 : ℝ))) ∧
            θ (x * (1 - 1 / 204879661)) ≤ x * (1 - 1 / 204879661) * (1 + BKLNW_app.table_8_ε 50) := by
      have hθ_bounds : ∀ {X₀ X₁ x : ℝ}, X₀ ≥ exp 20 → X₁ ≥ exp 20 → x ≥ X₀ → x ≥ X₁ →
          θ x ≥ x * (1 - (BKLNW.Inputs.default.ε (log X₀) +
            1.03883 * X₀ ^ (-1 / 2 : ℝ) + 1.03883 * X₀ ^ (-2 / 3 : ℝ) + 1.03883 * X₀ ^ (-4 / 5 : ℝ))) ∧
              θ x ≤ x * (1 + BKLNW.Inputs.default.ε (log X₁)) := by
        intro X₀ X₁ x hX₀ hX₁ hx₀ hx₁
        refine ⟨?_, ?_⟩
        · have := BKLNW.thm_1a hX₀ hX₁ hx₀ hx₁
          simp only [θ]
          ring_nf at this ⊢
          linarith [this.1]
        · have := BKLNW.thm_1a hX₀ hX₁ hx₀ hx₁
          simp only [θ]
          linarith [this.2]
      refine ⟨?_, ?_⟩
      · convert hθ_bounds (show exp 53 ≥ exp 20 by norm_num)
            (show exp 53 ≥ exp 20 by norm_num) (show x ≥ exp 53 by linarith)
              (show x ≥ exp 53 by linarith) |> And.left using 1
        aesop
      · have := @hθ_bounds (exp 50) (exp 50) (x * (1 - 1 / 204879661)) ?_ ?_ ?_ ?_
          <;> norm_num at *
        · exact this.2.trans (mul_le_mul_of_nonneg_left (add_le_add_left (by rfl) _) (by nlinarith [exp_pos 53]))
        · rw [show (53 : ℝ) = 50 + 3 by norm_num, exp_add] at hx
          nlinarith [add_one_le_exp 50, add_one_le_exp 3]
        · rw [show exp 53 = (exp 50) * (exp 3) by rw [← exp_add]; norm_num] at hx
          nlinarith [exp_pos 3, add_one_le_exp 3, add_one_le_exp 50]
    have hθ_bounds' : BKLNW_app.table_8_ε 53 +
        1.03883 * (exp 53) ^ (-1 / 2 : ℝ) + 1.03883 * (exp 53) ^ (-2 / 3 : ℝ) + 1.03883 * (exp 53) ^ (-4 / 5 : ℝ) +
          BKLNW_app.table_8_ε 50 < 1 / 204879661 * (1 + BKLNW_app.table_8_ε 50) := by
      norm_num [BKLNW_app.table_8_ε] at *
      linarith [RamareSaouter2003.numerical_ineq]
    nlinarith [add_one_le_exp 53, exp_pos 53,
      mul_inv_cancel₀ (ne_of_gt (exp_pos 53)), mul_inv_cancel₀ (ne_of_gt (exp_pos (53 * (-1 / 2)))),
      mul_inv_cancel₀ (ne_of_gt (exp_pos (53 * (-2 / 3)))), mul_inv_cancel₀ (ne_of_gt (exp_pos (53 * (-4 / 5))))]
  obtain ⟨p, hp_prime, hp_bounds⟩ : ∃ p : ℕ, x * (1 - 1 / 204879661) < p ∧ p ≤ x ∧ p.Prime := by
    have h_prime_in_interval :
        ∑ p ∈ filter Prime (Icc 1 (floor x)), Real.log p >
        ∑ p ∈ filter Prime (Icc 1 (floor (x * (1 - 1 / 204879661)))), Real.log p := by
      convert h_chebyshev using 1
    obtain ⟨p, hp_prime, hp_interval⟩ :
        ∃ p ∈ filter Prime (Icc 1 (floor x)),
          p ∉ filter Prime (Icc 1 (floor (x * (1 - 1 / 204879661)))) := by
      exact not_subset.mp fun h ↦ (not_le_of_gt h_prime_in_interval) <|
        sum_le_sum_of_subset_of_nonneg h fun _ _ _ ↦ log_nonneg <| one_le_cast.mpr <| Prime.pos <| by aesop
    exact ⟨p,
      not_le.mp fun h ↦ hp_interval <| mem_filter.mpr
        ⟨mem_Icc.mpr ⟨Prime.pos <| mem_filter.mp hp_prime |>.2, le_floor <| by linarith⟩, mem_filter.mp hp_prime |>.2⟩,
          floor_le (show 0 ≤ x by linarith [exp_pos 53]) |> le_trans
            (cast_le.mpr <| mem_Icc.mp (mem_filter.mp hp_prime |>.1) |>.2), mem_filter.mp hp_prime |>.2⟩
  exact ⟨p, hp_bounds.2, hp_prime, by ring_nf at *; linarith⟩


@[blueprint
  "thm:gourdon-demichel2004"
  (title := "Gourdon-Demichel 2004")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{14500755538}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem GourdonDemichel2004.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/14500755538)) (x/14500755538) := by sorry

theorem theta_pos_implies_prime_in_interval {x y : ℝ} (_hxy : y < x) (h : θ x - θ y > 0) :
    HasPrimeInInterval y (x - y) := by
  have h_diff : θ x - θ y =
      ∑ p ∈ filter Prime (Icc 1 (floor x)), Real.log p -
      ∑ p ∈ filter Prime (Icc 1 (floor y)), Real.log p := by unfold θ; rfl
  obtain ⟨p, hp₁, hp₂, hp₃⟩ : ∃ p ∈ Icc 1 (floor x), p.Prime ∧ p > floor y := by
    contrapose! h
    exact h_diff.symm ▸ sub_nonpos_of_le (sum_le_sum_of_subset_of_nonneg
      (fun p hp ↦ by grind) fun _ _ _ ↦ log_nonneg <| one_le_cast.mpr <| Prime.pos <| by grind)
  have hx_nn : 0 ≤ x := by linarith [floor_pos.mp (hp₂.one_lt.le.trans (mem_Icc.mp hp₁).2)]
  have hp_le_x : (p : ℝ) ≤ x := floor_le (by positivity) |> le_trans (mod_cast mem_Icc.mp hp₁ |>.2)
  exact ⟨p, hp₂, lt_of_floor_lt hp₃, by grind⟩

@[blueprint
  "thm:prime_gaps_2014"
  (title := "Prime Gaps 2014")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{1966196911}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem PrimeGaps2014.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/1966196911)) (x/1966196911) := by sorry

@[blueprint
  "thm:prime_gaps_2024"
  (title := "Prime Gaps 2024")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{76900000000}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem PrimeGaps2024.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/76900000000)) (x/76900000000) := by sorry

@[blueprint
  "thm:trudgian2016"
  (title := "Trudgian 2016")
  (statement := /-- If $x > 2,898,242$, then there
  is a prime in the interval
  \[ \left[ x, x\left(1 + \frac{1}{111(\log x)^2}\right) \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Trudgian2016.has_prime_in_interval (x : ℝ) (hx : x > 2898242) :
    HasPrimeInInterval x (x / (111 * (log x) ^ 2)) := by sorry

@[blueprint
  "thm:dudek2014"
  (title := "Dudek 2014")
  (statement := /-- If $x > \exp(\exp(34.32))$, then there is a prime in the interval
  \[ \left( x, x + 3x^{2/3} \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Dudek2014.has_prime_in_interval (x : ℝ) (hx : x > exp (exp 34.32)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3)) := by sorry

@[blueprint
  "thm:cully-hugill2021"
  (title := "Cully-Hugill 2021")
  (statement := /-- If $x > \exp(\exp(33.99))$, then there is a prime in the interval
  \[ \left( x, x + 3x^{2/3} \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem CullyHugill2021.has_prime_in_interval (x : ℝ) (hx : x > exp (exp 33.99)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3)) := by sorry

@[blueprint
  "thm:rh_prime_interval_2002"
  (title := "RH Prime Interval 2002")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{8}{5}\sqrt{x}, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem RHPrimeInterval2002.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (8 / 5) * sqrt x) ((8 / 5) * sqrt x) := by sorry

@[blueprint
  "thm:dudek2015_rh"
  (title := "Dudek 2015 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{4}{\pi}\sqrt{x}, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Dudek2015RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (4 / π) * sqrt x) ((4 / π) * sqrt x) := by sorry

@[blueprint
  "thm:carneiroetal_2019_rh"
  (title := "Carneiro et al. 2019 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 4$, there is a prime in the interval
  \[ \left( x - \frac{22}{25}\sqrt{x}\log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem CarneiroEtAl2019RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 4) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (22 / 25) * sqrt x * log x) ((22 / 25) * sqrt x * log x) := by sorry
