import Mathlib

open Complex

-- Hypothesis: `ring` calls `ring1` first, and on failure, falls back to `try_this ring_nf`.
-- The fallback runs `ring_nf` AND emits a "Try this: ring_nf" suggestion.
-- If `ring_nf` closes the goal (via rfl after normalization), the proof succeeds
-- but the misleading suggestion is still printed.
--
-- This is triggered when the goal contains non-ring operations (like Complex.exp)
-- whose arguments are ring-equal, but the outer expression isn't a ring equation
-- so `ring1` rejects it.

-- Example 1: Pure ring equation, ring1 closes it directly, no suggestion
example (a b : ℝ) : a * b = b * a := by ring

-- Example 2: Equation involves Complex.exp; ring1 fails, ring_nf closes (via rfl on arguments)
-- This SHOULD trigger "Try this: ring_nf" but still succeed.
example (a b : ℂ) : Complex.exp (a * b) = Complex.exp (b * a) := by ring_nf

-- Example 3: Same situation with a product wrapping exp
example (a b c : ℂ) : c * Complex.exp (a * b) = c * Complex.exp (b * a) := by ring
