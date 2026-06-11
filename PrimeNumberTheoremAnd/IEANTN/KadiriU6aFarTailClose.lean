import PrimeNumberTheoremAnd.IEANTN.KadiriU6aFarTail
import PrimeNumberTheoremAnd.IEANTN.KadiriU6aCountAtom

/-!
# U6a far-tail closure: the unconditional endpoints

`KadiriU6aFarTail` composes the U6a zero-sum remainder estimate from the
single local-count atom `U6aLocalZeroCountLogHypothesis`, parametrically in
the atom's constants.  `KadiriU6aCountAtom` discharges the atom (Jensen disk
at `2 + it`, witness `Tₘᵢₙ = 6`).  This file instantiates the parametric
composition at the proved atom and exports the unconditional endpoints
consumed by the good-heights chain.

The import direction matters: the atom file imports the far-tail file (where
the hypothesis is defined), so the instantiation must live in this third file.
-/

namespace Kadiri

/-- The U6a far-tail estimate, unconditional: outside the nearby window the
xi Hadamard remainder is log-grade on the strip. -/
theorem exists_U6aFarTailBoundHypothesis :
    ∃ C Tₘᵢₙ : ℝ, U6aFarTailBoundHypothesis C Tₘᵢₙ := by
  obtain ⟨Ccnt, Tₘᵢₙ, hcnt⟩ := exists_u6aLocalZeroCountLogHypothesis
  obtain ⟨C, hC⟩ := exists_U6aFarTailBoundHypothesis_of_localCount hcnt
  exact ⟨C, Tₘᵢₙ, hC⟩

/-- The U6a zero-sum remainder estimate, unconditional: the difference of the
global xi Hadamard zero sum and Kadiri's nearby principal part is log-grade
on the strip. -/
theorem exists_U6aZeroSumRemainderBoundHypothesis :
    ∃ C Tₘᵢₙ : ℝ, U6aZeroSumRemainderBoundHypothesis (-1) 2 C Tₘᵢₙ := by
  obtain ⟨Ccnt, Tₘᵢₙ, hcnt⟩ := exists_u6aLocalZeroCountLogHypothesis
  obtain ⟨C, hC⟩ := exists_U6aZeroSumRemainderBoundHypothesis_of_localCount hcnt
  exact ⟨C, Tₘᵢₙ, hC⟩

/-- The U6a Hadamard partial-fraction remainder bound, unconditional for any
degree-one factorization polynomial: the zero-sum slot of the banked
good-heights composition is now discharged. -/
theorem exists_U6aHadamardRemainderBoundHypothesis
    {P : Polynomial ℂ} (hP : P.degree ≤ 1) :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      U6aHadamardRemainderBoundHypothesis (-1) 2 C Tₘᵢₙ P := by
  obtain ⟨Czero, Tzero, hzero⟩ := exists_U6aZeroSumRemainderBoundHypothesis
  exact U6aHadamardRemainderBoundHypothesis_of_zeroSum hP hzero

end Kadiri
