module

public import RHHeight100.Main100

/-! Pin the height-100 final theorems to Mathlib's zeta and audit their complete closure. -/

open Complex

example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 100 →
    ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1 :=
  RHHeight100.rh_height_hundred

example :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ 100}.ncard = 29 :=
  RHHeight100.zero_count_hundred

example : Zeta23.Ncount 3 100 = 29 := RHHeight100.ncount_three_hundred

#print axioms RHHeight100.gamma_increment100
#print axioms RHHeight100.horizontalLegs100
#print axioms RHHeight100.count_eq_twenty_nine_of
#print axioms RHHeight100.rhUpToHeight100_of_pieces
#print axioms RHHeight100.zeroCount100_of_pieces
#print axioms RHHeight100.twenty_nine_zeros_on_line_below_hundred
#print axioms RHHeight100.zero_in_5297
#print axioms RHHeight100.zero_in_5644
#print axioms RHHeight100.zero_in_5934
#print axioms RHHeight100.zero_in_6083
#print axioms RHHeight100.zero_in_6511
#print axioms RHHeight100.zero_in_67075
#print axioms RHHeight100.zero_in_6954
#print axioms RHHeight100.zero_in_7206
#print axioms RHHeight100.zero_in_7570
#print axioms RHHeight100.zero_in_7714
#print axioms RHHeight100.zero_in_7933
#print axioms RHHeight100.zero_in_8291
#print axioms RHHeight100.zero_in_8473
#print axioms RHHeight100.zero_in_8742
#print axioms RHHeight100.zero_in_8880
#print axioms RHHeight100.zero_in_9249
#print axioms RHHeight100.zero_in_9465
#print axioms RHHeight100.zero_in_95865
#print axioms RHHeight100.zero_in_9883
#print axioms RHHeight100.ncount_three_hundred
#print axioms RHHeight100.rh_height_hundred
#print axioms RHHeight100.zero_count_hundred
