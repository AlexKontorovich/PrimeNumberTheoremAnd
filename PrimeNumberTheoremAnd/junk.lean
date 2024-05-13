import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ)  : HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  apply HasDerivAt.div_const
  apply HasDerivAt.neg
  convert @HasDerivAt.const_cpow (f := fun s ↦ -s) (f' := -1) (x := s) (c := N) (hasDerivAt_neg' s) (by left; exact_mod_cast Npos.ne.symm) using 1
  rw [mul_comm, mul_assoc]
  congr! 1
  simp only [Complex.natCast_log, mul_neg, mul_one]
