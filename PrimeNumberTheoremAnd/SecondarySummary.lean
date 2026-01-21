import Architect
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.NumberTheory.Bertrand
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.FKS2
import PrimeNumberTheoremAnd.Dusart

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
    HasPrimeInInterval (x*(1-1/15697)) x := by
  obtain ⟨p, hp, hpn, hp2n⟩ := exists_prime_lt_and_le_two_mul ⌊x * 15696 / 15697⌋₊ (floor_pos.mpr <| by grind).ne'
  exact ⟨p, hp, by grind [lt_of_floor_lt hpn], by grind [floor_le (show 0 ≤ x * 15696 / 15697 by positivity),
    show (p : ℝ) ≤ 2 * ⌊x * 15696 / 15697⌋₊ from mod_cast hp2n]⟩

@[blueprint
  "thm:ramare-saouter2003"
  (title := "Ramaré-Saouter 2003")
  (statement := /--
  If $x > 10,726,905,041$, then there is a prime in the interval $(x(1-1/28314000), x]$.
  -/)
  (latexEnv := "theorem")]
theorem RamareSaouter2003.has_prime_in_interval (x : ℝ) (hx : x > 10726905041) :
    HasPrimeInInterval (x*(1-1/28314000)) x := by
  field_simp
  have := exists_prime_lt_and_le_two_mul (⌊x * (28314000 - 1) / 28314000⌋₊) ?_
      <;> norm_num at *
  · obtain ⟨p, hp₁, hp₂, hp₃⟩ := this
    exact ⟨p, hp₁, lt_of_floor_lt hp₂, by grind [floor_le (by positivity : 0 ≤ x * 28313999 / 28314000),
      (by exact_mod_cast hp₃ : (p : ℝ) ≤ 2 * ⌊x * 28313999 / 28314000⌋₊)]⟩
  · grind

@[blueprint
  "thm:ramare_saouter2003-2"
  (title := "Ramaré-Saouter 2003 (2)")
  (statement := /-- If $x > \exp(53)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{204879661}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem RamareSaouter2003.has_prime_in_interval_2 (x : ℝ) (hx : x > exp 53) :
    HasPrimeInInterval (x*(1-1/204879661)) x := by
  have h_x_gt_204879661 : x > 204879661 := calc
    (204879661 : ℝ) ≤ 2.7182818283 ^ 53 := by norm_num
    _ ≤ (exp 1) ^ 53 := pow_le_pow_left₀ (by positivity) exp_one_gt_d9.le _
    _ = exp 53 := by rw [← exp_nat_mul]; norm_num
    _ < x := hx
  have := exists_prime_lt_and_le_two_mul (⌊x * (204879661 - 1) / 204879661⌋₊) ?_
    <;> norm_num at *
  · obtain ⟨p, hp₁, hp₂, hp₃⟩ := this
    exact ⟨p, hp₁, by grind [lt_floor_add_one (x * 204879660 / 204879661),
        (by norm_cast : (⌊x * 204879660 / 204879661⌋₊ : ℝ) + 1 ≤ p)],
      by grind [floor_le (show 0 ≤ x * 204879660 / 204879661 by positivity),
      (by norm_cast : (p : ℝ) ≤ 2 * ⌊x * 204879660 / 204879661⌋₊)]⟩
  · grind [add_one_le_exp 53]

@[blueprint
  "thm:gourdon-demichel2004"
  (title := "Gourdon-Demichel 2004")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{14500755538}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem GourdonDemichel2004.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/14500755538)) x := by
  have hn : ⌊x * 14500755537 / 14500755538⌋₊ ≠ 0 := by
    rw [ne_eq, floor_eq_zero, not_lt]
    linarith [add_one_le_exp 60]
  obtain ⟨p, hp_prime, hp_lb, hp_ub⟩ := exists_prime_lt_and_le_two_mul _ hn
  refine ⟨p, hp_prime, ?_, ?_⟩
  · linarith [lt_of_floor_lt hp_lb]
  · have h1 : 0 ≤ x * 14500755537 / 14500755538 := by linarith [exp_pos 60]
    have h2 : (p : ℝ) ≤ 2 * ⌊x * 14500755537 / 14500755538⌋₊ := by exact_mod_cast hp_ub
    linarith [floor_le h1, h2]

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
    HasPrimeInInterval (x*(1-1/1966196911)) x := by
  have h_theta_pos : θ x - θ (x * (1 - 1 / 1966196911)) > 0 := by
    have h_gap_pos : x * (1 - 1.2312e-11) - (x * (1 - 1 / 1966196911)) * (1 + 1.2215e-11) > 0 := by
      nlinarith [add_one_le_exp 60]
    have h_theta_bounds :
        x * (1 - 1.2312e-11) ≤ θ x ∧ θ (x * (1 - 1 / 1966196911)) ≤
        (x * (1 - 1 / 1966196911)) * (1 + 1.2215e-11) := by
      constructor
      · have := BKLNW.thm_1a_table
          (show (60, 1.2215e-11, 1.2312e-11) ∈ BKLNW.Table_14 by norm_num [BKLNW.Table_14])
          (show x ≥ 60 by linarith [add_one_le_exp 60])
        norm_num at *; grind
      · have := BKLNW.thm_1a_table
          (show (60, 1.2215e-11, 1.2312e-11) ∈ BKLNW.Table_14 by norm_num [BKLNW.Table_14])
          (show x * (1 - 1 / 1966196911) ≥ 60 by nlinarith [add_one_le_exp 60])
        norm_num at *; grind
    grind
  have := theta_pos_implies_prime_in_interval
    (show x * (1 - 1 / 1966196911) < x from mul_lt_of_lt_one_right (by linarith [exp_pos 60])
      (by norm_num)) h_theta_pos
  exact this.imp fun p hp ↦ ⟨hp.1, hp.2.1, by grind⟩

@[blueprint
  "thm:prime_gaps_2024"
  (title := "Prime Gaps 2024")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{76900000000}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem PrimeGaps2024.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/76900000000)) x := by
  have := exists_prime_lt_and_le_two_mul (⌊x * 76899999999 / 76900000000⌋₊) ?_ <;> norm_num at *
  · obtain ⟨p, hp₁, hp₂, hp₃⟩ := this
    exact ⟨p, hp₁, lt_of_floor_lt hp₂ |> lt_of_le_of_lt (by grind), (cast_le.mpr hp₃).trans (by
        have hx' : 0 < x := lt_trans (by positivity) hx
        grind [floor_le (by positivity : 0 ≤ x * 76899999999 / 76900000000), add_one_le_exp 60])⟩
  · grind [add_one_le_exp 60]

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
  (latexEnv := "theorem") ]
theorem CullyHugill2021.has_prime_in_interval (x : ℝ) (hx : x > exp (exp 33.99)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3)) := by sorry

@[blueprint
  "thm:rh_prime_interval_2002"
  (title := "RH Prime Interval 2002")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{8}{5}\sqrt{x}, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem RHPrimeInterval2002.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH: RiemannHypothesis) :
    HasPrimeInInterval (x - (8 / 5) * sqrt x) x := by sorry

@[blueprint
  "thm:dudek2015_rh"
  (title := "Dudek 2015 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{4}{\pi}\sqrt{x}, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Dudek2015RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (4 / π) * sqrt x) x := by sorry

@[blueprint
  "thm:carneiroetal_2019_rh"
  (title := "Carneiro et al. 2019 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 4$, there is a prime in the interval
  \[ \left( x - \frac{22}{25}\sqrt{x}\log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem CarneiroEtAl2019RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 4) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (22 / 25) * sqrt x * log x) x := by sorry
