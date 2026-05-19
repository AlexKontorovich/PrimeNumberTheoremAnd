import Architect
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.Defs
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Real

blueprint_comment /--
\section{Definitions}
-/

@[blueprint
  "zeroes-of-riemann-zeta"
  (statement := /--
    $\rho$ is understood to lie in the set $\{s: \zeta(s)=0\}$, counted with multiplicity. We will
    often restrict the zeroes $\rho$ to a rectangle $\{ \Re \rho \in I, \Im \rho \in J \}$, for
    instance through sums of the form $\sum_{\Re \rho \in  I, \Im \rho \in J} f(\rho)$.
  -/)]
noncomputable def riemannZeta.zeroes : Set ℂ := {s : ℂ | riemannZeta s = 0}

@[blueprint
  "zeroes-of-riemann-zeta"]
noncomputable def riemannZeta.zeroes_rect (I J : Set ℝ) : Set ℂ :=
  {s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ zeroes}

lemma riemannZeta.zeroes_rect_eq (I J : Set ℝ) :
    zeroes_rect I J = (Complex.re ⁻¹' I ∩ Complex.im ⁻¹' J) ∩ zeroes := by
  ext x; simp only [zeroes_rect, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_preimage, and_assoc]

lemma riemannZeta.zeroes_rect_disjoint₁ (I₁ I₂ J : Set ℝ) (h : Disjoint I₁ I₂) :
    Disjoint (zeroes_rect I₁ J) (zeroes_rect I₂ J) :=
  fun _ h1 h2 _ hs ↦ False.elim <| (Set.disjoint_left.1 h) (h1 hs).1 (h2 hs).1

lemma riemannZeta.zeroes_rect_union (I₁ I₂ J : Set ℝ) :
    (zeroes_rect I₁ J) ∪ (zeroes_rect I₂ J) = zeroes_rect (I₁ ∪ I₂) J := by
  ext x; simp only [zeroes_rect, Set.mem_union, Set.mem_setOf_eq]; tauto

-- should this be in mathlib?
section

lemma riemannZeta_differentiableOn_compl_one :
    DifferentiableOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
  fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt

lemma riemannZeta_analyticOn_compl_one :
    AnalyticOnNhd ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
  riemannZeta_differentiableOn_compl_one.analyticOnNhd isOpen_compl_singleton

lemma riemannZeta.zeroes_codiscreteWithin_compl_one :
    zeroesᶜ ∈ Filter.codiscreteWithin ({1} : Set ℂ)ᶜ := by
  refine riemannZeta_analyticOn_compl_one.preimage_zero_mem_codiscreteWithin
    ?_ ?_ ?_ (x := 2)
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact Set.mem_compl_singleton_iff.2 (OfNat.one_ne_ofNat 2).symm
  · refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two

lemma riemannZeta.zeroes_on_Compact_finite {S : Set ℂ} (hS1 : IsCompact S) (hS2 : 1 ∉ S) :
    (S ∩ zeroes : Set ℂ).Finite := by
  have sub := Set.subset_compl_singleton_iff.mpr hS2
  refine IsCompact.finite ?_ ?_
  · have := riemannZeta_analyticOn_compl_one.continuousOn.mono sub
      |>.preimage_isClosed_of_isClosed (t := {0}) hS1.isClosed isClosed_singleton
    exact hS1.of_isClosed_subset this Set.inter_subset_left
  · rw [Set.inter_comm]
    exact IsDiscrete.mono (isDiscrete_of_codiscreteWithin zeroes_codiscreteWithin_compl_one)
      <| Set.inter_subset_inter_right zeroes sub

open Topology in
lemma riemannZeta_eventually_ne_zero :
    ∀ᶠ s in 𝓝[≠] 1, riemannZeta s ≠ 0 := by
  filter_upwards [riemannZeta_residue_one.eventually_ne (zero_ne_one' ℂ).symm,
    eventually_nhdsWithin_of_forall (fun _ hs ↦ hs)] with s hmul hne
  intro hzero
  rw [hzero, mul_zero] at hmul
  exact false_of_ne hmul

lemma riemannZeta_no_zeroes_near_one : ∃ ε, ε > 0 ∧ ∀ s,
    s ∈ Metric.ball 1 ε → riemannZeta s ≠ 0 := by
  obtain ⟨ε, hε_pos, hball⟩ := Metric.eventually_nhds_iff.1 <|
      eventually_nhdsWithin_iff.1 riemannZeta_eventually_ne_zero
  refine ⟨ε, hε_pos, fun s hs hzero ↦ ?_⟩
  by_cases h : s = 1
  · exact riemannZeta_one_ne_zero (h ▸ hzero)
  · exact hball (Metric.mem_ball.1 hs) (Set.mem_compl_singleton_iff.2 h) hzero

lemma riemannZeta.zeroes_on_Compact_finite' {S : Set ℂ} (hS1 : IsCompact S) :
    (S ∩ zeroes : Set ℂ).Finite := by
  obtain ⟨ε, hε, hball⟩ := riemannZeta_no_zeroes_near_one
  have : S ∩ zeroes ⊆ (S ∩ (Metric.ball 1 ε)ᶜ) ∩ zeroes :=
    fun s ⟨hs, hz⟩ ↦ ⟨⟨hs, fun hmem ↦ hball s hmem hz⟩, hz⟩
  refine Set.Finite.subset (zeroes_on_Compact_finite ?_ ?_) this
  · exact hS1.inter_right Metric.isOpen_ball.isClosed_compl
  · exact fun ⟨_, h⟩ ↦ h (Metric.mem_ball_self hε)

end

@[blueprint
  "zeroes-of-riemann-zeta"]
noncomputable def riemannZeta.order (s : ℂ) : ℤ := (meromorphicOrderAt (riemannZeta) s).untopD 0

@[blueprint
  "zeroes-of-riemann-zeta"]
noncomputable def riemannZeta.zeroes_sum {α : Type*} [RCLike α]
    (I J : Set ℝ) (f : ℂ → α) : α :=
  ∑' ρ : riemannZeta.zeroes_rect I J, (f ρ) * (riemannZeta.order ρ)

@[blueprint
  "RH-up-to"
  (statement := /--
    We say that the Riemann hypothesis has been verified up to height $T$ if there are no zeroes
    in the rectangle $\{ \Re \rho \in (0.5, 1), \Im \rho \in [0,T] \}$.
  -/)]
noncomputable def riemannZeta.RH_up_to (T : ℝ) : Prop :=
  IsEmpty (riemannZeta.zeroes_rect (Set.Ioo 0.5 1) (Set.Icc 0 T))

@[blueprint
  "classical-zero-free-region"
  (title := "Section 1.1, FKS2")
  (statement := /--
    We say that one has a classical zero-free region with parameter $R$ if $zeta(s)$ has no zeroes
    in the region $Re(s) \geq 1 - 1 / R * \log |\Im s|$ for $\Im(s) > 3$.
  -/)]
noncomputable def riemannZeta.classicalZeroFree (R : ℝ) :=
  ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 - 1 / (R * log t) →
  riemannZeta (σ + t * Complex.I) ≠ 0

@[blueprint
  "zero-counting-function"
  (title := "Zero counting function N(T)")
  (statement := /--
    The number of zeroes of imaginary part between 0 and T, counting multiplicity
  -/)]
noncomputable def riemannZeta.N (T : ℝ) : ℝ := zeroes_sum Set.univ (Set.Ioo 0 T) (fun _ ↦ 1)

@[blueprint
  "zero-counting-function"
  (title := "Zero counting function N(σ,T)")
  (statement := /--
    The number of zeroes of imaginary part between 0 and T, with real part greater than $\sigma$,
    counting multiplicity
  -/)]
noncomputable def riemannZeta.N' (σ T : ℝ) : ℝ := zeroes_sum (Set.Ioo σ 1) (Set.Ioo 0 T) 1

@[blueprint
  "Riemann-von-Mangoldt-estimate"]
noncomputable def riemannZeta.RvM (b₁ b₂ b₃ T : ℝ) : ℝ :=
  b₁ * log T + b₂ * log (log T) + b₃

@[blueprint
  "Riemann-von-Mangoldt-estimate"
  (title := "Riemann von Mangoldt estimate")
  (statement := /--
    An estimate of the form
    $N(T) - \frac{T}{2\pi} \log \frac{T}{2\pi e} + \frac{7}{8}| \leq b_1 \log T + b_2 \log\log T
    + b_3$ for $T \geq 2$.
  -/)]
def riemannZeta.Riemann_vonMangoldt_bound (b₁ b₂ b₃ : ℝ) : Prop :=
  ∀ T ≥ 2, |riemannZeta.N T - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
    RvM b₁ b₂ b₃ T

@[blueprint
  "zero-density-bound"
  (title := "Zero density bound")
  (statement := /--
    An estimate of the form $N(\sigma,T) \leq c₁ T^p \log^q T + c₂ \log^2 T -
    \frac{T}{2\pi} \log \frac{T}{2\pi e} + \frac{7}{8}| \leq b_1 \log T + b_2 \log\log T + b_3$
    for $T \geq 2$.
  -/)]
structure zero_density_bound where
  T₀ : ℝ
  σ_range : Set ℝ
  c₁ : ℝ → ℝ
  c₂ : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  bound : ∀ T ≥ T₀, ∀ σ ∈ σ_range,
      riemannZeta.N' σ T ≤ (c₁ σ) * T ^ (p σ) * (log T) ^ (q σ) + (c₂ σ) * (log T) ^ 2

@[blueprint
  "zero-density-bound"]
noncomputable def zero_density_bound.N {ZDB : zero_density_bound} (σ T : ℝ) : ℝ :=
  (ZDB.c₁ σ) * T ^ (ZDB.p σ) * (log T) ^ (ZDB.q σ) + (ZDB.c₂ σ) * (log T) ^ 2
