import Mathlib.Data.Real.Basic

example (a : ℝ) (ha' : ∃ k : ℤ, a = k + 1/2) : ¬∃ n : ℤ, a = ↑n := by
  obtain ⟨k, hk⟩ := ha'
  rintro ⟨n, hn⟩
  have : (n : ℝ) = k + 1 / 2 := by linarith [hk, hn]
  have hzz : ((n - k : ℤ) : ℝ) = 1 / 2 := by push_cast; linarith
  have hzz2 : 2 * ((n - k : ℤ) : ℝ) = 1 := by linarith
  have hzz3 : (2 * (n - k) : ℤ) = 1 := by exact_mod_cast hzz2
  omega
