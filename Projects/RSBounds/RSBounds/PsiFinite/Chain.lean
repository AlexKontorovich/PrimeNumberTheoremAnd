import RSBounds.PsiFinite.Segment

/-! Composition of segment steps, used by the generated assembly modules. -/

namespace PsiFinite

/-- A verified step from the enclosure `s` at `a` to `t` at `b`. -/
def Step (a : ℕ) (s : St) (b : ℕ) (t : St) : Prop := Encl a s → Encl b t ∧ BoundOn 4 5 a b

theorem Step.comp {a b c : ℕ} {s t u : St} (f : Step a s b t) (g : Step b t c u) : Step a s c u :=
  fun h => ⟨(g (f h).1).1, BoundOn.trans (f h).2 (g (f h).1).2⟩

theorem step_of_seg (hb : BaseFacts) {lo w B : ℕ} {s s' : St}
    (h : checkSegK 4 5 lo w B s = some s') {A A' : ℕ} (hA : lo - 1 = A)
    (hA' : A + 2 * 2 ^ w * B = A') (hB : 0 < B) : Step A s A' s' :=
  fun hs => seg_chain hb h hA hA' hB hs

end PsiFinite
