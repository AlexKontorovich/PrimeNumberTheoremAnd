import Lean.Meta.Tactic.Simp.RegisterCommand

/-- The simpset `cify_simps` is used by the tactic `cify` to move expressions from `ℕ`, `ℤ`, `ℚ`, or
`ℝ` to `ℂ`. -/
register_simp_attr cify_simps
