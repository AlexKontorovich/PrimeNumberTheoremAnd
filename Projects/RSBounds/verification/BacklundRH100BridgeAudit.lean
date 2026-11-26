import RSBounds.BacklundRH100Bridge

open TernaryGoldbach.RSBounds.BacklundCountIdentity

example : N_le 100 = 29 := closed_count_hundred
example {T : ℝ} (hT : 0 < T) (h100 : T ≤ 100) :
    N_le T = (closedPositiveZeros T).card := closed_count_eq_card hT h100
example {ρ : ℂ} (hz : riemannZeta ρ = 0) (hi : 0 < ρ.im) (h100 : ρ.im ≤ 100) :
    ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1 :=
  zero_simple_below_hundred hz hi h100

#print axioms zeta_zero_re_strip
#print axioms coe_closedPositiveZeros_eq_stripZerosUpTo
#print axioms zero_simple_below_hundred
#print axioms closed_count_eq_card
#print axioms closed_count_hundred
