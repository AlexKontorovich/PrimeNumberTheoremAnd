import Mathlib

variable (X A B C : Type)

instance [HMul A B C] : HMul (X → A) (X → B) (X → C) := by
  constructor
  intro f g x
  exact f x * g x

variable (f1 : X → ℂ) (f2 : X → ℝ)
#check (f1 * f2) : X → ℂ -- failed to synthesize instance  HMul (X → ℂ) (X → ℝ) ?m.19669
def f3 := fun x => f1 x * f2 x
#check f3 f1 f2
