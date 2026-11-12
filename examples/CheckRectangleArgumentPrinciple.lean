import PrimeNumberTheoremAnd.RectangleArgumentPrinciple

/--
info: logDeriv_residue_eq_meromorphicOrderAt {f : ℂ → ℂ} {p : ℂ} {n : ℤ} (hf : MeromorphicAt f p)
  (hord : meromorphicOrderAt f p = ↑n) : residue (logDeriv f) p = ↑n
-/
#guard_msgs in
#check logDeriv_residue_eq_meromorphicOrderAt

/--
info: rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt {f : ℂ → ℂ} {z w : ℂ} (zRe_le_wRe : z.re ≤ w.re)
  (zIm_le_wIm : z.im ≤ w.im) (hf : MeromorphicOn f (z.Rectangle w)) (hlog : MeromorphicOn (logDeriv f) (z.Rectangle w))
  (hfinite_order : ∀ p ∈ z.Rectangle w, meromorphicOrderAt f p ≠ ⊤)
  (hno_boundary : Disjoint (RectangleBorder z w) (MeromorphicOn.divisor f (z.Rectangle w)).support) :
  RectangleIntegral' (logDeriv f) z w = ∑ p ∈ ⋯.toFinset, ↑((MeromorphicOn.divisor f (z.Rectangle w)) p)
-/
#guard_msgs in
#check rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt

/--
info: rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt {f : ℂ → ℂ} {z w : ℂ} {argumentChange : ℝ}
  (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im) (hf : MeromorphicOn f (z.Rectangle w))
  (hlog : MeromorphicOn (logDeriv f) (z.Rectangle w)) (hfinite_order : ∀ p ∈ z.Rectangle w, meromorphicOrderAt f p ≠ ⊤)
  (hno_boundary : Disjoint (RectangleBorder z w) (MeromorphicOn.divisor f (z.Rectangle w)).support)
  (hargumentChange : ↑argumentChange = 2 * ↑Real.pi * RectangleIntegral' (logDeriv f) z w) :
  argumentChange = 2 * Real.pi * ∑ p ∈ ⋯.toFinset, ↑((MeromorphicOn.divisor f (z.Rectangle w)) p)
-/
#guard_msgs in
#check rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt

/--
info: 'logDeriv_residue_eq_meromorphicOrderAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms logDeriv_residue_eq_meromorphicOrderAt

/--
info: 'rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt

/--
info: 'rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt
