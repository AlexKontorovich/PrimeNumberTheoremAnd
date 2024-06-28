import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace Asymptotics

variable {α β : Type*} [NormedAddCommGroup β] {u v w : α → β} {l : Filter α}

theorem IsEquivalent.isLittleO_add (huv : u =o[l] v) (hwv : w ~[l] v) : u + w ~[l] v := by
  rw [IsEquivalent, add_sub_right_comm, sub_add_eq_add_sub u v w, add_sub_assoc]
  simpa using IsLittleO.add huv hwv
