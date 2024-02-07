import Mathlib.MeasureTheory.Group.Arithmetic

variable {α : Type*} [MeasurableSpace α]

@[to_additive]
theorem measurableEmbedding_inv [InvolutiveInv α] [MeasurableInv α] :
    MeasurableEmbedding (Inv.inv (α := α)) := by
  refine ⟨inv_injective, measurable_inv, fun s hs ↦ ?_⟩
  rewrite [s.image_inv]
  exact hs.inv
