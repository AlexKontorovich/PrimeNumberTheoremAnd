import PrimeNumberTheoremAnd.SecondarySummary

namespace PrimeGapsLatest

-- Keep a stable alias to Dusart's constant and proposition from SecondarySummary.
abbrev X₀ : ℕ := Dusart.X₀

@[simp] lemma X₀_eq : X₀ = 89693 := rfl

-- If you just want an alias, this is fine:
abbrev proposition_5_4 := Dusart.proposition_5_4

-- If you want the type to mention `PrimeGapsLatest.X₀` explicitly:
-- theorem proposition_5_4' : HasPrimeInInterval.log_thm X₀ 3 := by
--   simpa [X₀] using (Dusart.proposition_5_4)

end PrimeGapsLatest
