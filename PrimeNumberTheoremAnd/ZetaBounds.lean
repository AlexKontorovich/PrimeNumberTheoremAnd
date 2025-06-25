import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Group.Basic
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.MellinCalculus
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Order.Group.Lattice
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Bound


set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]

lemma one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by
  convert div_cpow_eq_cpow_neg 1 x s using 1; simp

lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x): a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]

lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  rw [div_eq_mul_inv, Real.rpow_neg hx, Real.rpow_neg hy, Real.div_rpow hy hx]; field_simp

lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  convert div_rpow_neg_eq_rpow_div (s := -s) hx hy using 1; simp only [neg_neg]

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

/-%%
We record here some prelimiaries about the zeta function and general
holomorphic functions.

\begin{theorem}[ResidueOfTendsTo]\label{ResidueOfTendsTo}\lean{ResidueOfTendsTo}\leanok
  If a function $f$ is holomorphic in a neighborhood of $p$ and
  $\lim_{s\to p} (s-p)f(s) = A$, then
  $f(s) = \frac{A}{s-p} + O(1)$ near $p$.
\end{theorem}
%%-/
theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by

-- Step 1: We know that (s-1) * ζ(s) → 1 as s → 1Add commentMore actions

  -- refine ⟨U, hU_open, h1_in_U, ?_⟩

  -- have U_mem_nhds : U ∈ 𝓝 (1 : ℂ) := by
  --   rw [mem_nhds_iff]
  --   refine ⟨U, fun ⦃a⦄ a ↦ a, hU_open, h1_in_U⟩

  -- have h_bdd : BddAbove (norm ∘ (fun s : ℂ => (s - 1) * riemannZeta s) '' (U \ {1})) := by
  --   use 2
  --   intro r hr
  --   obtain ⟨s, hs_mem, hs_eq⟩ := hr
  --   rw [Function.comp_apply] at hs_eq
  --   rw [← hs_eq]
  --   have hs_in_U : s ∈ U := hs_mem.1
  --   have hs_ne_1 : s ≠ 1 := hs_mem.2
  --   have : s ∈ U ∩ {1}ᶜ := ⟨hs_in_U, hs_ne_1⟩
  --   have h_in_ball : (s - 1) * ζ s ∈ Metric.ball 1 1 := hU_subset this
  --   rw [Metric.mem_ball, Complex.dist_eq] at h_in_ball
  --   have : ‖(s - 1) * ζ s‖  - ‖(1 : ℂ)‖ ≤ ‖(s - 1) * ζ s - 1‖ := norm_sub_norm_le _ _
  --   simp only [norm_one] at this
  --   linarith

  -- -- Step 2: Since the limit exists and is finite, (s-1) * ζ(s) extends to a holomorphic function
  -- -- There exists a holomorphic function g in a neighborhood of 1 such that
  -- -- (s-1) * ζ(s) = g(s) for s ≠ 1, and g(1) = 1
  -- have h_holomorphic_extension : ∃ (g : ℂ → ℂ) (hg_holo : HolomorphicOn g U),
  --   (EqOn (fun s ↦ (s - 1) * ζ s) g (U \ {1})) ∧ g 1 = 1 := by
  --   have := existsDifferentiableOn_of_bddAbove U_mem_nhds ?_ h_bdd (s := U)
  --   · obtain ⟨g, gHolc, gEqOn⟩ := this
  --     refine ⟨g, gHolc, gEqOn, ?_⟩
  --     have h_limit : Tendsto g (𝓝[≠] 1) (𝓝 1) := by
  --       -- Rewrite the limit using the equality on U \ {1}
  --       apply Filter.Tendsto.congr' ?_ h_residue
  --       unfold EventuallyEq Filter.Eventually
  --       rw [mem_nhdsWithin]
  --       refine ⟨U, hU_open, h1_in_U, ?_⟩
  --       intro s hs
  --       simp only [mem_setOf_eq]
  --       exact gEqOn hs
  --     have h_continuous : ContinuousAt g 1 := by
  --       have := gHolc.continuousOn
  --       apply this.continuousAt
  --       exact U_mem_nhds
  --     exact tendsto_nhds_unique (tendsto_nhdsWithin_of_tendsto_nhds h_continuous) h_limit
  --   · unfold HolomorphicOn
  --     intro s hs
  --     have s_ne_1 : s ≠ 1 := hs.2
  --     apply DifferentiableAt.differentiableWithinAt
  --     apply DifferentiableAt.mul
  --     · fun_prop
  --     · exact differentiableAt_riemannZeta s_ne_1

  -- obtain ⟨g, hg_holo, hg_eq_on, hg_at_one⟩ := h_holomorphic_extension

  sorry




  -- -- Step 4: Since g is holomorphic at 1 with g(1) = 1, we have g(s) = 1 + O(s-1)
  -- have h_taylor :
  --   (fun s => g s - 1) =O[𝓝 1] (fun s => s - 1) := by
  --   sorry

  -- -- Step 6: Therefore ζ(s) = g(s)/(s-1) = (1 + O(s-1))/(s-1) = 1/(s-1) + O(1)
  -- -- First, we need to work in a punctured neighborhood where s ≠ 1
  -- have h_zeta_formula : ∀ᶠ s in 𝓝[{1}ᶜ] 1, riemannZeta s = g s / (s - 1) := by
  --   -- This follows from (s-1) * ζ(s) = g(s)
  --   sorry

  -- -- Step 7: Show that g(s)/(s-1) - 1/(s-1) = (g(s) - 1)/(s-1) = O(1)
  -- have h_key_bound : (fun s => g s / (s - 1) - (s - 1)⁻¹) =O[𝓝[≠] 1] (1 : ℂ → ℂ) := by
  --   -- Simplify: g(s)/(s-1) - 1/(s-1) = (g(s) - 1)/(s-1)
  --   have h_simplify : ∀ s : ℂ, s ≠ 1 → g s / (s - 1) - (s - 1)⁻¹ = (g s - 1) / (s - 1) := by
  --     sorry
  --   sorry

  -- -- Step 8: Combine with the formula for ζ to get the final result

  -- -- Use h_zeta_formula and h_key_bound
  -- sorry

/-%%
\begin{proof}\uses{existsDifferentiableOn_of_bddAbove}
The function $(s - p)\cdot f(s)$ bounded, so by Theorem
\ref{existsDifferentiableOn_of_bddAbove}, there is a holomorphic function, $g$, say, so that
$(s-p)f(s) = g(s)$ in a neighborhood of $s=p$, and $g(p)=A$. Now because $g$ is holomorphic,
near $s=p$, we have $g(s)=A+O(s-p)$. Then when you divide by $(s-p)$, you get
$f(s) = A/(s-p) + O(1)$.
\end{proof}
%%-/


/-%%
\begin{theorem}[riemannZetaResidue]\label{riemannZetaResidue}\lean{riemannZetaResidue}\leanok
  The Riemann zeta function $\zeta(s)$ has a simple pole at $s=1$ with residue $1$. In particular, the function
  $$ \zeta(s) - \frac{1}{s-1}$$
  is bounded in a neighborhood of $s=1$.
\end{theorem}
%%-/

theorem riemannZetaResidue :

    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by

  have h_residue := riemannZeta_residue_one

  have univ_mem : (univ : Set ℂ) ∈ 𝓝 (1 : ℂ) := by
    rw [mem_nhds_iff]
    refine ⟨univ, fun _ _ => by simp, isOpen_univ, mem_univ _⟩

  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    simp at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy

  convert ResidueOfTendsTo univ_mem zeta_holc h_residue using 6
  simp

/-%%
\begin{proof}\uses{ResidueOfTendsTo}\leanok
From `riemannZeta_residue_one` (in Mathlib), we know that
$(s-1)\zeta(s)$ goes to $1$ as $s\to1$. Now apply Theorem \ref{ResidueOfTendsTo}.
(This can also be done using $\zeta_0$ below, which is expressed as
$1/(s-1)$ plus things that are holomorphic for $\Re(s)>0$...)
\end{proof}
%%-/


-- Main theorem: if functions agree on a punctured set, their derivatives agree there too
theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  -- We need to show that for any x ∈ U \ {p}, deriv f x = deriv g x
  intro x hx
  -- hx : x ∈ U \ {p}, so x ∈ U and x ≠ p
  have hx_in_U : x ∈ U := hx.1
  have hx_ne_p : x ≠ p := hx.2

  -- Since f and g agree on U \ {p} and x ≠ p,
  -- we can find a neighborhood of x where f = g
  have h_eq_nhds : ∀ᶠ y in 𝓝 x, f y = g y := by
    -- Since x ≠ p and U \ {p} is open (as U is open and {p} is closed),
    -- and f = g on U \ {p}, we have f = g in a neighborhood of x
    rw [eventually_nhds_iff]
    use U \ {p}
    exact ⟨h_eq, hU_open.sdiff isClosed_singleton, hx⟩

  -- Now use the fact that if f = g in a neighborhood, then deriv f = deriv g

--  exact deriv_congr_of_eventually_eq h_eq_nhds

  exact EventuallyEq.deriv_eq h_eq_nhds

/- New two theorems to be proven -/

theorem analytic_deriv_bounded_near_point
  (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
  (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

    have U_in_filter : U ∈ 𝓝 p := by
      exact IsOpen.mem_nhds hU hp
    have T := (analyticOn_iff_differentiableOn hU).mpr hf
    have T2 : ContDiffOn ℂ 1 f U :=
        DifferentiableOn.contDiffOn hf hU
    have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
      apply T2.continuousOn_deriv_of_isOpen hU (by simp)
    have T4 := T3.continuousAt U_in_filter
    have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
      T4.norm.isBoundedUnder_le.isBigO_one ℂ
    refine Asymptotics.IsBigO.mono ?_ inf_le_left

    exact T5


-- Even simpler direct proof using tendsto
theorem map_inv_nhdsWithin_direct
  (h : ℂ  → ℂ) (U : Set ℂ) (p : ℂ) (A : ℂ)
  (A_ne_zero : A ≠ 0) :
  map h (𝓝[U] p) ≤ 𝓝 A → map (fun x => (h x)⁻¹) (𝓝[U] p) ≤ 𝓝 A⁻¹ := by
  intro hyp
  -- This is just the continuity of inversion composed with the given convergence
  --rw [← map_map]
  exact (continuousAt_inv₀ A_ne_zero).tendsto.comp hyp


-- Even simpler direct proof using tendsto
theorem map_inv_nhdsWithin_direct_alt
  (h : ℂ  → ℂ) (p : ℂ) (A : ℂ)
  (A_ne_zero : A ≠ 0) :
  map h (𝓝[≠] p) ≤ 𝓝 A → map (fun x => (h x)⁻¹) (𝓝[≠] p) ≤ 𝓝 A⁻¹ := by
  intro hyp
  -- This is just the continuity of inversion composed with the given convergence
  --rw [← map_map]
  exact (continuousAt_inv₀ A_ne_zero).tendsto.comp hyp


theorem expression_eq_zero (A x p : ℂ) (h : x ≠ p) :
  A - A * x * (x - p)⁻¹ + A * p * (x - p)⁻¹ = 0 := by
  -- Since x ≠ p, we have x - p ≠ 0
  have h_ne_zero : x - p ≠ 0 := sub_ne_zero.mpr h

  have : A - A * x * (x - p)⁻¹ + A * p * (x - p)⁻¹ =
         A * (1 - x * (x - p)⁻¹ + p * (x - p)⁻¹) := by ring
  rw [this]

  suffices h_suff : 1 - x * (x - p)⁻¹ + p * (x - p)⁻¹ = 0 by
     rw [h_suff, mul_zero]

  have : 1 - x * (x - p)⁻¹ + p * (x - p)⁻¹ =
         1 + (-x + p) * (x - p)⁻¹ := by ring
  rw [this]

  have : -x + p = -(x - p) := by ring
  rw [this, neg_mul]

  have : (x - p) * (x - p)⁻¹ = 1 := Field.mul_inv_cancel (x - p) h_ne_zero
  rw [this]

  ring


theorem field_identity (f f' x p : ℂ) (hf : f ≠ 0) (hp : x ≠ p) :
  f' * f⁻¹ + (x - p)⁻¹ = (f + f' * (x - p)) * ((x - p)⁻¹ * f⁻¹) := by

  have h_xp : x - p ≠ 0 := sub_ne_zero.mpr hp
  field_simp [hf, h_xp]
  ring


theorem derivative_const_plus_product {g : ℂ → ℂ}
   (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
  deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x :=
  by

  -- Rewrite the function as a single lambda
    have h_eq : ((fun _ ↦ A) + g * fun s ↦ s - p) = fun s ↦ A + g s * (s - p) := by
      ext s
      simp [Pi.add_apply, Pi.mul_apply]

    rw [h_eq]

  -- Apply derivative of sum
    rw [deriv_add]

  -- Derivative of constant is 0
    rw [deriv_const, zero_add]

  -- Apply product rule to g s * (s - p)
    rw [deriv_mul hg (differentiableAt_id'.sub (differentiableAt_const p))]

  -- Derivative of (s - p) is 1
    rw [deriv_sub, deriv_id'', deriv_const, sub_zero]

  -- Simplify
    rw [mul_one]
    · exact differentiableAt_id'-- rw [add_comm]
    · exact differentiableAt_const p
  -- Differentiability conditions
    · exact differentiableAt_const A --exact differentiableAt_const
    · refine DifferentiableAt.mul hg ?_
      refine DifferentiableAt.sub_const ?_ p
      exact differentiableAt_id' -- exact hg.mul (differentiableAt_id'.sub differentiableAt_const)

theorem deriv_eq_of_eq (f g : ℂ → ℂ ) (h : f = g) : deriv f = deriv g := by
  rw [h]

-- For complex numbers
theorem deriv_inv_complex :
  deriv (fun z : ℂ => z⁻¹) = fun x ↦ (- (x^2)⁻¹) := by
  rw [deriv_inv']

theorem diff_translation (p : ℂ ) : deriv (fun x => x - p) = fun _ => 1 := by
  ext x
  simp [deriv_sub, deriv_id'', deriv_const]


-- Key lemma: derivative of (x - p)⁻¹
lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  -- Use chain rule: d/dx[(x-p)⁻¹] = d/du[u⁻¹] * d/dx[x-p] where u = x-p
  let inv_x := fun (x : ℂ) ↦ x⁻¹
  let trans_x := fun x ↦ x - p

  let T : (inv_x ∘ trans_x) = fun x ↦ (x - p)⁻¹  := by
    funext x
    apply Function.comp_apply

  let G : deriv (inv_x ∘ trans_x) x = ((deriv inv_x) (trans_x x)) * ((deriv (trans_x)) x) := by
    apply deriv_comp
    · refine differentiableAt_inv ?_
      exact sub_ne_zero_of_ne hp
    · refine (DifferentiableAt.sub_iff_right ?_).mpr ?_
      · exact differentiableAt_id'
      · exact differentiableAt_const p

  have E : (deriv inv_x) = (fun x ↦ - (x^2)⁻¹) := by
    exact deriv_inv_complex

--  deriv_inv_complex
  have F : (deriv trans_x) = 1 := by
    unfold trans_x
    exact diff_translation p

  simp [*] at T
  simp [E, F, T] at G

  simp [inv_x, trans_x] at G
  exact G

-- Alternative cleaner proof using more direct approach
theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    apply DifferentiableAt.inv
    · exact differentiableAt_id'.sub (differentiableAt_const p)
    · rwa [sub_ne_zero]

  calc deriv (fun z => f z - A * (z - p)⁻¹) x
    = deriv f x - deriv (fun z => A * (z - p)⁻¹) x := by
        rw [deriv_sub hf (DifferentiableAt.const_mul h1 A)]
    _ = deriv f x - A * deriv (fun z => (z - p)⁻¹) x := by
        rw [deriv_const_mul A h1]
    _ = deriv f x - A * (-((x - p) ^ 2)⁻¹) := by
        rw [deriv_inv_sub hp]
    _ = deriv f x + A * ((x - p) ^ 2)⁻¹ := by ring


-- Alternative proof using field_simp tactic
theorem laurent_expansion_identity_alt (f f' A x p : ℂ)
 (h : x ≠ p):
  (f' + A * ((x - p)^2)⁻¹) * (x - p) + (f - A * (x - p)⁻¹) = f + f' * (x - p) := by
  have h_nonzero : x - p ≠ 0 := by
    rwa [sub_ne_zero]

  field_simp [h_nonzero]
  ring

/-%%
\begin{theorem}[nonZeroOfBddAbove]\label{nonZeroOfBddAbove}\lean{nonZeroOfBddAbove}\leanok
  If a function $f$ has a simple pole at a point $p$ with residue $A \neq 0$, then
  $f$ is nonzero in a punctured neighborhood of $p$.
\end{theorem}
%%-/
theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by
  /-%%
  \begin{proof}\leanok
    We know that $f(s) = \frac{A}{s-p} + O(1)$ near $p$, so we can write
    $$f(s) = \left(f(s) - \frac{A}{s-p}\right) + \frac{A}{s-p}.$$
    The first term is bounded, say by $M$, and the second term goes to $\infty$ as $s \to p$.
    Therefore, there exists a neighborhood $V$ of $p$ such that for all $s \in V \setminus \{p\}$,
    we have $f(s) \neq 0$.
  \end{proof}
  %%-/

  -- Step 1: Rewrite f as the sum of two parts
  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
  -- Get a bound for the first summand
  obtain ⟨M, hM⟩ := f_near_p
  -- Step 2: The second summand A * (s - p)⁻¹ goes to ∞ as s → p
  -- We need to find a neighborhood where |A * (s - p)⁻¹| > M + 1
  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
  -- Choose δ such that for |s - p| < δ, we have |A * (s - p)⁻¹| > M + 1
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
  -- Find an open neighborhood V contained in both U and the δ-ball around p
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
    -- rw [mem_nhds_iff] at U_in_nhds
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
  -- Show f ≠ 0 on V
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
  -- Step 3: Therefore the sum of the two terms has large norm
  rw [h_decomp s]
  -- The first summand is bounded
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
  -- The second summand has large norm
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    exact hs_near_p
  -- Step 4: Therefore the sum is nonzero near p
  by_contra h_zero
  -- If f s = 0, then the two summands are negatives of each other
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
  -- But this contradicts our bounds
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero: ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by


  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    intro x hyp
    exact DifferentiableWithinAt.sub (holc x hyp) (simpleHolo x hyp)

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

      /- TODO: Assert that the derivatives match too -/

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))


  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    refine DifferentiableOn.sub_const ?_ p
    exact differentiableOn_id'

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    have G := DifferentiableOn.const_add A T
    exact G

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

      -- Just a consequence of continuity

  have h_converges_to_A : map h (𝓝[U] p) ≤ 𝓝 A := by
    have p_in_U : p ∈ U := by exact mem_of_mem_nhds U_in_nhds
    have H := (h_continuous p) p_in_U
    unfold ContinuousWithinAt at H
    unfold Tendsto at H
    have T : h p = A := by
      unfold h
      simp
    simp [T] at H
    exact H


  have h_inv_converges_to_inv_A : map h⁻¹ (𝓝[U] p) ≤ 𝓝 A⁻¹ := by
      exact map_inv_nhdsWithin_direct h U p A A_ne_zero h_converges_to_A

  have h_inv_converges_to_inv_A_norm : Tendsto (fun e ↦ ‖h⁻¹ e - A⁻¹‖) (𝓝[U] p) (𝓝 0) :=
      by exact tendsto_iff_norm_sub_tendsto_zero.mp h_inv_converges_to_inv_A

  have h_inv_converges_to_inv_A_norm_1 : {x | -1 ≤ ‖h⁻¹ x - A⁻¹‖ ∧ ‖h⁻¹ x - A⁻¹‖ ≤ 1} ∈ 𝓝[U] p :=
    by
      unfold Tendsto at h_inv_converges_to_inv_A_norm
      unfold map at h_inv_converges_to_inv_A_norm
      unfold preimage at h_inv_converges_to_inv_A_norm
      have T := Filter.sets_subset_sets.mpr h_inv_converges_to_inv_A_norm
      simp [*] at T

      have G : Set.Icc (-1) 1 ∈ (𝓝 (0 : ℝ)).sets := by
            refine Icc_mem_nhds ?_ ?_
            · simp
            · simp
      have E : {x | ‖h⁻¹ x - A⁻¹‖ ∈ (Set.Icc (-1) 1)} ∈ (𝓝[U] p) :=
          by
            have := Set.mem_of_subset_of_mem T G
            exact this
      exact E

  have trivial_subset : {x | -1 ≤ ‖h⁻¹ x - A⁻¹‖ ∧ ‖h⁻¹ x - A⁻¹‖ ≤ 1} ⊆ {x | ‖h x‖⁻¹ ≤ ‖A‖⁻¹ + 1} := by
        simp
        intro x
        intro hyp_a
        intro hyp_b
        have T : 1 ≤ ‖A‖⁻¹ + 1 := by simp
        simp [*] at *
        have U := calc
          ‖h x‖⁻¹             = ‖h⁻¹ x‖ := by exact Eq.symm (IsAbsoluteValue.abv_inv norm (h x))
          ‖h⁻¹ x‖             = ‖h⁻¹ x - A⁻¹ + A⁻¹‖ := by simp
          ‖h⁻¹ x - A⁻¹ + A⁻¹‖ ≤ ‖h⁻¹ x - A⁻¹‖ + ‖A⁻¹‖ := by exact norm_add_le (h⁻¹ x - A⁻¹) (A⁻¹)
          _                   ≤  1 + ‖A‖⁻¹ := by simp [hyp_b]
          _                   = ‖A‖⁻¹ + 1 := by exact Lean.Grind.CommRing.add_comm 1 ‖A‖⁻¹

        exact U

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by

        intro x
        intro x_in_u_not_p
        unfold h
        unfold EqOn at g_is_f_minus_pole

        have x_in_u : x ∈ U := by exact mem_of_mem_diff x_in_u_not_p
        have x_not_p : x ≠ p := by
          have L := ((Set.mem_diff x).mp x_in_u_not_p).2
          exact L

        have weird : U ∈ 𝓝 x := by
          exact IsOpen.mem_nhds (U_is_open) (x_in_u)

        have weirded : U \ {p} ∈ 𝓝 x := by
          exact Filter.inter_mem (weird) ((compl_singleton_mem_nhds x_not_p))

        have T : f x - A * (x - p)⁻¹ = g x :=
          by
            have := g_is_f_minus_pole (x_in_u_not_p);
            simp at this
            exact this
        have E : g x = f x - A * (x - p)⁻¹ := by
          exact T.symm

        have Z := g_is_f_minus_pole x_in_u_not_p

        have U1 := by
          exact deriv_f_minus_A_inv_sub_clean f A x p (holc.differentiableAt weirded) (x_not_p)

        have T := derivative_const_plus_product A p x (g_is_holomorphic.differentiableAt weird)

        rw [T, E]

        have Z :=
          by
            have T := deriv_eqOn_of_eqOn_punctured ((f - fun s ↦ A * (s - p)⁻¹)) g U p U_is_open g_is_f_minus_pole
            exact (T (x_in_u_not_p)).symm

        have U2 := laurent_expansion_identity_alt (f x) (deriv f x) A x p (x_not_p)

        rw [Z, U1]

        /- Now it's just an identity -/
        exact U2


  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
        intro x
        intro x_in_u_not_p
        have hyp_x_not_p : x ≠ p := by
          have L := ((Set.mem_diff x).mp x_in_u_not_p).2
          exact L
        unfold h
        simp
        have E : f x - A * (x - p)⁻¹ = g x :=
          by
            have := g_is_f_minus_pole (x_in_u_not_p);
            simp at this
            exact this
        have T : g x = f x - A * (x - p)⁻¹ := by
          exact E.symm

        simp [T]
        ring_nf
        simp [*]
        exact expression_eq_zero A x p hyp_x_not_p

  have log_deriv_f_plus_pole_equal_log_deriv_h :
        EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) :=
        by
          simp [*] at *
          intro x
          intro hyp_x
          have x_not_p : x ≠ p := by
            have L := ((Set.mem_diff x).mp hyp_x).2
            exact L
          have x_in_u : x ∈ U := by exact mem_of_mem_diff hyp_x
          have T : h x = (f x) * (x - p) := by
              exact (h_identity x x_in_u x_not_p)
          have G := (deriv_h_identity x x_in_u x_not_p)
          simp [G, T]

          /- This is just an identity at this point -/


          exact field_identity (f x) ((deriv f) x) x p (non_zero x (x_in_u) x_not_p) x_not_p

  have h_inv_bounded :
        h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
          rw [Asymptotics.IsBigO_def]
          use ‖A‖⁻¹ + 1
          rw [Asymptotics.IsBigOWith]
          simp [*]
          refine eventually_iff.mpr ?_
          have U101 : {x | ‖h x‖⁻¹ ≤ ‖A‖⁻¹ + 1} ∈ 𝓝[U] p := by
            refine exists_mem_subset_iff.mp ?_
            use {x | -1 ≤ ‖h⁻¹ x - A⁻¹‖ ∧ ‖h⁻¹ x - A⁻¹‖ ≤ 1}

          have U102 : {x | ‖h x‖⁻¹ ≤ ‖A‖⁻¹ + 1} ∈ 𝓝 p := by
            exact nhds_of_nhdsWithin_of_nhds U_in_nhds U101
          refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
          use {x | ‖h x‖⁻¹ ≤ ‖A‖⁻¹ + 1}
          refine ⟨U102, ?_⟩
          · exact inter_subset_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic


  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      simp [*] at T
      refine Asymptotics.IsBigO.of_norm_right ?_
      simp [*]

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact diff_mem_nhdsWithin_compl U_in_nhds {p}

  have final : (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
      have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter

      exact EventuallyEq.trans_isBigO T h_log_deriv_bounded


  exact final

theorem  logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero: ∀x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact diff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact diff_subset_diff a (subset_refl _)


      refine logDerivResidue' b ?_ ?_ (by
          refine IsOpen.mem_nhds ?_ ?_
          · exact b
          · exact c) A_ne_zero ?_
      · intro x
        intro hyp_x
        have T: x ∈ U \ {p} := by exact T hyp_x
        exact (non_zero x T)
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_subset _ (diff_subset_diff a (subset_refl _))))


/-%%
\begin{proof}\uses{existsDifferentiableOn_of_bddAbove}
Using Theorem \ref{existsDifferentiableOn_of_bddAbove}, there is a function $g$ holomorphic  near $p$, for which $f(s) = A/(s-p) + g(s) = h(s)/ (s-p)$. Here $h(s):= A + g(s)(s-p)$ which is nonzero in a neighborhood of $p$ (since $h$ goes to $A$ which is nonzero).
Then $f'(s) = (h'(s)(s-p) - h(s))/(s-p)^2$, and we can compute the quotient:
$$
\frac{f'(s)}{f(s)}+1/(s-p) = \frac{h'(s)(s-p) - h(s)}{h(s)} \cdot \frac{1}{(s-p)}+1/(s-p)
=
\frac{h'(s)}{h(s)}.
$$
Since $h$ is nonvanishing near $p$, this remains bounded in a neighborhood of $p$.
\end{proof}
%%-/

/-%%
Let's also record that if a function $f$ has a simple pole at $p$ with residue $A$, and $g$ is holomorphic near $p$, then the residue of $f \cdot g$ is $A \cdot g(p)$.
\begin{theorem}[ResidueMult]\label{ResidueMult}\lean{ResidueMult}\leanok
  If $f$ has a simple pole at $p$ with residue $A$, and $g$ is holomorphic near $p$, then the residue of $f \cdot g$ at $p$ is $A \cdot g(p)$. That is, we assume that
  $$
  f(s) = \frac{A}{s - p} + O(1)$$
  near $p$, and that $g$ is holomorphic near $p$. Then
  $$
  f(s) \cdot g(s) = \frac{A \cdot g(p)}{s - p} + O(1).$$
\end{theorem}
%%-/

theorem ResidueMult {f g : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (g_holc : HolomorphicOn g U) (U_in_nhds : U ∈ 𝓝 p) {A : ℂ}
    (f_near_p : (f - (fun s ↦ A * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (f * g - (fun s ↦ A * g p * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  -- Add and subtract a term
  have : (f * g - fun s ↦ A * g p * (s - p)⁻¹)
      = (f - A • fun s ↦ (s - p)⁻¹) * g + fun s ↦ (A * (g s - g p) / (s - p)) := by
    have h1 : (f * g - fun s ↦ A * g p * (s - p)⁻¹)
        = (f * g - g * A • (fun s ↦ (s-p)⁻¹)) + (g * A • (fun s ↦ (s-p)⁻¹)
        - (g p * A) • (fun s ↦ (s-p)⁻¹)) := by ext x; simp; ring_nf; tauto
    have h2 : f * g - g * A • (fun s ↦ (s-p)⁻¹) = (f - A • (fun s ↦ (s-p)⁻¹)) * g := by
      ext x; simp; ring
    have h3 : g * A • (fun s ↦ (s-p)⁻¹) - (g p * A) • (fun s ↦ (s-p)⁻¹)
        = fun s ↦ (A * (g s - g p) / (s - p)) := by
      ext x; simp; ring
    rw [h1,h2,h3]
  -- Apply to goal
  rw[this]
  refine Asymptotics.IsBigO.add ?_ ?_
  · rw[← mul_one (1 : ℂ → ℂ)]
    refine Asymptotics.IsBigO.mul ?_ ?_
    · exact f_near_p
    · -- Show g is bounded near p
      have g_cont : ContinuousAt g p := by
        -- g is holomorphic on U, p ∈ U, so g is continuous at p
        have p_in_U : p ∈ U := mem_of_mem_nhds U_in_nhds
        exact (g_holc.continuousOn.continuousWithinAt p_in_U).continuousAt U_in_nhds
      -- Use continuity to get boundedness
      have : ∃ C > 0, ∀ᶠ x in 𝓝 p, ‖g x‖ ≤ C := by
        -- g is continuous at p, so g p is finite
        let C := ‖g p‖ + 1
        use C, by positivity
        -- By continuity, g x is close to g p in a neighborhood
        have : ∀ᶠ x in 𝓝 p, ‖g x - g p‖ < 1 := by
          rw [Metric.eventually_nhds_iff]
          obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp g_cont 1 zero_lt_one
          use δ, hδ_pos
          intro x hx
          exact hδ hx
        filter_upwards [this] with x hx
        -- Triangle inequality
        calc ‖g x‖
          = ‖g x - g p + g p‖ := by ring_nf
          _ ≤ ‖g x - g p‖ + ‖g p‖ := norm_add_le _ _
          _ ≤ ‖g p‖ + 1 := by linarith [hx]
          _ = C := by rfl
      -- Convert to big O notation
      obtain ⟨C, hC_pos, hC⟩ := this
      refine Asymptotics.IsBigO.of_bound C ?_
      have hC' : ∀ᶠ (x : ℂ) in 𝓝[≠] p, ‖g x‖ ≤ C := by
        exact eventually_nhdsWithin_of_eventually_nhds hC
      filter_upwards [hC'] with x hx
      simp [norm_one]
      exact hx
  · -- unfold HolomorphicOn at g_holc
    -- Show that (fun s ↦ A * (g s - g p) / (s - p)) =O[𝓝[≠] p] 1
    have p_in_U : p ∈ U := mem_of_mem_nhds U_in_nhds

    suffices (fun s ↦ A * ((s - p)⁻¹ * (g s - g p))) =O[𝓝[≠] p] 1 by
      convert this using 2
      rw[div_eq_mul_inv]
      ring
    apply Asymptotics.IsBigO.const_mul_left

    -- g is differentiable at p since it's holomorphic on U
    have g_diff : HasDerivAt g (deriv g p) p :=
        (DifferentiableOn.differentiableAt g_holc U_in_nhds).hasDerivAt

    rw [hasDerivAt_iff_isLittleO] at g_diff
    apply Asymptotics.IsLittleO.isBigO at g_diff
    have : (fun x' ↦ deriv g p * (x' - p)) =O[𝓝 p] fun x' ↦ x' - p := by
      apply Asymptotics.IsBigO.const_mul_left
      exact Asymptotics.isBigO_refl (fun x ↦ x - p) (𝓝 p)
    have h1 := g_diff.add this
    have h2 : (fun x ↦ g x - g p) =O[𝓝 p] fun x' ↦ x' - p := by
      convert h1 using 2
      simp
      ring
    refine (Asymptotics.isBigO_mul_iff_isBigO_div ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp at hx
      push_neg at hx
      exact inv_ne_zero (sub_ne_zero.mpr hx)
    · simp only [div_inv_eq_mul, one_mul]
      refine Asymptotics.IsBigO.mono ?_ inf_le_left
      simp
      exact h2

/-%%
\begin{proof}\leanok
Elementary calculation.
$$
f(s) * g(s) - \frac{A * g(p)}{s - p} =
\left(f(s) * g(s) - \frac{A * g(s)}{s - p}\right) + \left(\frac{A * g(s) - A * g(p)}{s - p}\right).
$$
The first term is $g(s)(f(s) - \frac{A}{s - p})$, which is bounded near $p$ by the assumption on $f$
 and the fact that $g$ is holomorphic near $p$.
The second term is $A$ times the log derivative of $g$ at $p$, which is bounded by the assumption
that  $g$ is holomorphic.
\end{proof}
%%-/

/-%%
As a corollary, the log derivative of the Riemann zeta function has a simple pole at $s=1$:
\begin{theorem}[riemannZetaLogDerivResidue]\label{riemannZetaLogDerivResidue}\lean{riemannZetaLogDerivResidue}\leanok
  The log derivative of the Riemann zeta function $\zeta(s)$ has a simple pole at $s=1$ with residue $-1$:
  $$ -\frac{\zeta'(s)}{\zeta(s)} - \frac{1}{s-1} = O(1).$$
\end{theorem}
%%-/
theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have ζ_holc: HolomorphicOn ζ (U \ {1}) := by
    intro y hy
    simp only [mem_diff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have := logDerivResidue ?_ ζ_holc U_in_nhds one_ne_zero
  · simp only [one_mul, Function.comp_apply, Pi.sub_apply] at this
    use U
    constructor
    exact U_in_nhds
    convert this ?_ using 1
    simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply]
    have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
      intro a
      calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
          = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
        _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
    simp only [aux]
  -- rfl
    simp only [Function.comp_apply, Pi.sub_apply] at hU
    sorry
    exact hU
  · intro x x_inU
    sorry
/-%%
\begin{proof}\uses{logDerivResidue, riemannZetaResidue}
  This follows from Theorem \ref{logDerivResidue} and Theorem \ref{riemannZetaResidue}.
\end{proof}
%%-/


/-%%
\begin{definition}[riemannZeta0]\label{riemannZeta0}\lean{riemannZeta0}\leanok
For any natural $N\ge1$, we define
$$
\zeta_0(N,s) :=
\sum_{1\le n \le N} \frac1{n^s}
+
\frac{- N^{1-s}}{1-s} + \frac{-N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
$$
\end{definition}
%%-/
noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative
  Rieman zeta function.. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

-- move near `Real.differentiableAt_rpow_const_of_ne`
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]

-- No longer used
lemma ContDiffOn.hasDeriv_deriv {φ : ℝ → ℂ} {s : Set ℝ} (φDiff : ContDiffOn ℝ 1 φ s) {x : ℝ}
    (x_in_s : s ∈ nhds x) : HasDerivAt φ (deriv φ x) x :=
  (ContDiffAt.hasStrictDerivAt (φDiff.contDiffAt x_in_s) (by simp)).hasDerivAt

-- No longer used
lemma ContDiffOn.continuousOn_deriv {φ : ℝ → ℂ} {a b : ℝ}
    (φDiff : ContDiffOn ℝ 1 φ (uIoo a b)) :
    ContinuousOn (deriv φ) (uIoo a b) := by
  apply ContDiffOn.continuousOn (𝕜 := ℝ) (n := 0)
  exact (fun h ↦ ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).1 h).2.2) φDiff

lemma LinearDerivative_ofReal (x : ℝ) (a b : ℂ) : HasDerivAt (fun (t : ℝ) ↦ a * t + b) a x := by
  refine HasDerivAt.add_const b ?_
  convert (ContinuousLinearMap.hasDerivAt Complex.ofRealCLM).const_mul a using 1; simp
-- No longer used
section
-- from Floris van Doorn

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {a b : ℝ}

--set_option autoImplicit false in
open BigOperators Interval Topology Set intervalIntegral MeasureTheory in
lemma integral_deriv_mul_eq_sub' {u v u' v' : ℝ → A}
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a := by
  have h2u : ContinuousOn u [[a, b]] := fun x hx ↦ (hu x hx).continuousWithinAt
  have h2v : ContinuousOn v [[a, b]] := fun x hx ↦ (hv x hx).continuousWithinAt
  apply integral_eq_sub_of_hasDeriv_right (h2u.mul h2v)
  · exact fun x hx ↦ (hu x <| mem_Icc_of_Ioo hx).mul (hv x <| mem_Icc_of_Ioo hx) |>.hasDerivAt
      (Icc_mem_nhds hx.1 hx.2) |>.hasDerivWithinAt
  · exact (hu'.mul_continuousOn h2v).add (hv'.continuousOn_mul h2u)

end

lemma sum_eq_int_deriv_aux2 {φ : ℝ → ℂ} {a b : ℝ} (c : ℂ)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∫ (x : ℝ) in a..b, (c - x) * deriv φ x =
      (c - b) * φ b - (c - a) * φ a + ∫ (x : ℝ) in a..b, φ x := by
  set u := fun (x : ℝ) ↦ c - x
  set u' := fun (x : ℝ) ↦ (-1 : ℂ)
  have hu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x := by
    exact fun x _ ↦ by convert LinearDerivative_ofReal x (-1 : ℂ) c; ring
  have hu' : IntervalIntegrable u' MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable; continuity
  have hv' : IntervalIntegrable (deriv φ) MeasureTheory.volume a b :=
    derivφCont.intervalIntegrable
  convert intervalIntegral.integral_mul_deriv_eq_deriv_mul hu φDiff hu' hv' using 1; simp [u, u']

lemma sum_eq_int_deriv_aux_eq {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ}
    (b_eq_kpOne : b = k + 1) (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc k ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  have flb_eq_k : ⌊b⌋ = k + 1 := Int.floor_eq_iff.mpr ⟨by exact_mod_cast b_eq_kpOne.symm.le,
    by rw [b_eq_kpOne]; simp⟩
  simp only [flb_eq_k, Finset.Icc_self, Finset.sum_singleton, Int.cast_add, Int.cast_one]
  rw [sum_eq_int_deriv_aux2 (k + 1 / 2) φDiff derivφCont, b_eq_kpOne]
  ring_nf
  have : Finset.Ioc k (1 + k) = {k + 1} := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · exact fun ⟨h₁, h₂⟩ ↦ by rw [add_comm] at h₂; exact Int.le_antisymm h₂ h₁
    · exact fun h ↦ ⟨by simp [h], by simp [h, add_comm]⟩
  simp_rw [this, Finset.sum_singleton, Int.cast_add, Int.cast_one, add_comm]

lemma sum_eq_int_deriv_aux_lt {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (ha : a ∈ Ico (k : ℝ) b)
    (b_lt_kpOne : b < k + 1) (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc k ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  have flb_eq_k : ⌊b⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith [ha.1, ha.2], by linarith⟩
  simp only [flb_eq_k, gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, Finset.Icc_eq_empty_of_lt,
    Finset.sum_empty]
  rw [sum_eq_int_deriv_aux2 (k + 1 / 2) φDiff derivφCont]
  have : Finset.Ioc k k = {} := by simp only [ge_iff_le, le_refl, Finset.Ioc_eq_empty_of_le]
  simp only [this, Finset.sum_empty, one_div]; ring_nf

lemma sum_eq_int_deriv_aux1 {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (ha : a ∈ Ico (k : ℝ) b)
    (b_le_kpOne : b ≤ k + 1) (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc k ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (k + 1 / 2 - a) * φ a
      - ∫ x in a..b, (k + 1 / 2 - x) * deriv φ x := by
  by_cases h : b = k + 1
  · exact sum_eq_int_deriv_aux_eq h φDiff derivφCont
  · exact sum_eq_int_deriv_aux_lt ha (Ne.lt_of_le h b_le_kpOne) φDiff derivφCont

/-%%
\begin{lemma}[sum_eq_int_deriv_aux]\label{sum_eq_int_deriv_aux}\lean{sum_eq_int_deriv_aux}\leanok
  Let $k \le a < b\le k+1$, with $k$ an integer, and let $\phi$ be continuously differentiable on
  $[a, b]$.
  Then
  \[
  \sum_{a < n \le b} \phi(n) = \int_a^b \phi(x) \, dx + \left(\lfloor b \rfloor + \frac{1}{2} - b\right) \phi(b) - \left(\lfloor a \rfloor + \frac{1}{2} - a\right) \phi(a) - \int_a^b \left(\lfloor x \rfloor + \frac{1}{2} - x\right) \phi'(x) \, dx.
  \]
\end{lemma}
%%-/
lemma sum_eq_int_deriv_aux {φ : ℝ → ℂ} {a b : ℝ} {k : ℤ} (ha : a ∈ Ico (k : ℝ) b)
    (b_le_kpOne : b ≤ k + 1) (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (⌊a⌋ + 1 / 2 - a) * φ a
      - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  have fl_a_eq_k : ⌊a⌋ = k := Int.floor_eq_iff.mpr ⟨ha.1, by linarith [ha.2]⟩
  convert sum_eq_int_deriv_aux1 ha b_le_kpOne φDiff derivφCont using 2
  · rw [fl_a_eq_k]
  · congr
  · apply intervalIntegral.integral_congr_ae
    have : ∀ᵐ (x : ℝ) ∂MeasureTheory.volume, x ≠ b := by
      convert Countable.ae_notMem (s := {b}) (by simp) (μ := MeasureTheory.volume) using 1
    filter_upwards [this]
    intro x x_ne_b hx
    rw [uIoc_of_le ha.2.le, mem_Ioc] at hx
    congr
    exact Int.floor_eq_iff.mpr ⟨by linarith [ha.1], by have := Ne.lt_of_le x_ne_b hx.2; linarith⟩
/-%%
\begin{proof}\leanok
Partial integration.
\end{proof}
%%-/

-- Thanks to Arend Mellendijk

lemma interval_induction_aux_int (n : ℕ) : ∀ (P : ℝ → ℝ → Prop)
    (_ : ∀ a b : ℝ, ∀ k : ℤ, k ≤ a → a < b → b ≤ k + 1 → P a b)
    (_ : ∀ (a : ℝ) (k : ℤ) (c : ℝ), a < k → k < c → P a k → P k c → P a c)
    (a b : ℝ) (_ : a < b) (_ : n = ⌊b⌋ - ⌊a⌋),
    P a b := by
  induction n using Nat.case_strong_induction_on with
  | hz =>
    intro P base _ a b hab hn
    apply base a b ⌊a⌋ (Int.floor_le a) hab
    rw [(by simp only [CharP.cast_eq_zero] at hn; linarith : ⌊a⌋ = ⌊b⌋)]
    exact (Int.lt_floor_add_one b).le
  | hi n ih =>
    intro P base step a b _ hn
    have Pa : P a (⌊a⌋ + 1) :=
      base a (⌊a⌋ + 1) ⌊a⌋ (Int.floor_le a) (Int.lt_floor_add_one a) (le_of_eq rfl)
    by_cases b_le_flaP1 : b = ⌊a⌋ + 1
    · rwa [b_le_flaP1]
    have flaP1_lt_b : ⌊a⌋ + 1 < b := by
      simp only [Nat.cast_succ] at hn
      have : (⌊a⌋ : ℝ) + 1 ≤ ⌊b⌋ := by exact_mod_cast (by linarith)
      exact Ne.lt_of_le (id (Ne.symm b_le_flaP1)) (by linarith [Int.floor_le b] : ⌊a⌋ + 1 ≤ b)
    have Pfla_b : P (⌊a⌋ + 1) b := by
      apply ih n (le_of_eq rfl) P base step (⌊a⌋ + 1) b flaP1_lt_b
      simp only [Int.floor_add_one, Int.floor_intCast, Nat.cast_succ] at hn ⊢
      linarith
    refine step a (⌊a⌋ + 1) b ?_ (by exact_mod_cast flaP1_lt_b) (by exact_mod_cast Pa)
      (by exact_mod_cast Pfla_b)
    have := Int.lt_floor_add_one a
    exact_mod_cast this

lemma interval_induction (P : ℝ → ℝ → Prop)
    (base : ∀ a b : ℝ, ∀ k : ℤ, k ≤ a → a < b → b ≤ k + 1 → P a b)
    (step : ∀ (a : ℝ) (k : ℤ) (b : ℝ), a < k → k < b → P a k → P k b → P a b)
    (a b : ℝ) (hab : a < b) : P a b := by
  set n := ⌊b⌋ - ⌊a⌋ with hn
  clear_value n
  have : 0 ≤ n := by simp only [hn, sub_nonneg, ge_iff_le, Int.floor_le_floor hab.le]
  lift n to ℕ using this
  exact interval_induction_aux_int n P base step a b hab hn

/-%%
\begin{lemma}[sum_eq_int_deriv]\label{sum_eq_int_deriv}\lean{sum_eq_int_deriv}\leanok
  Let $a < b$, and let $\phi$ be continuously differentiable on $[a, b]$.
  Then
  \[
  \sum_{a < n \le b} \phi(n) = \int_a^b \phi(x) \, dx + \left(\lfloor b \rfloor + \frac{1}{2} - b\right) \phi(b) - \left(\lfloor a \rfloor + \frac{1}{2} - a\right) \phi(a) - \int_a^b \left(\lfloor x \rfloor + \frac{1}{2} - x\right) \phi'(x) \, dx.
  \]
\end{lemma}
%%-/
/-- ** Partial summation ** (TODO : Add to Mathlib). -/
theorem Finset.Ioc_diff_Ioc {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    {a b c: α} [DecidableEq α] (hb : b ∈ Icc a c) : Ioc a b = Ioc a c \ Ioc b c := by
  ext x
  simp only [mem_Ioc, mem_sdiff, not_and, not_le]
  constructor
  · refine fun ⟨h₁, h₂⟩ ↦ ⟨⟨h₁, le_trans h₂ (mem_Icc.mp hb).2⟩, by contrapose! h₂; exact h₂.1⟩
  · exact fun ⟨h₁, h₂⟩ ↦ ⟨h₁.1, by contrapose! h₂; exact ⟨h₂, h₁.2⟩⟩

-- In Yaël Dillies's API (https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Finset.2Esum_add_adjacent_intervals/near/430127101)
lemma Finset.sum_Ioc_add_sum_Ioc {a b c : ℤ} (f : ℤ → ℂ) (hb : b ∈ Icc a c):
    (∑ n ∈ Finset.Ioc a b, f n) + (∑ n ∈ Finset.Ioc b c, f n) = ∑ n ∈ Finset.Ioc a c, f n := by
  convert Finset.sum_sdiff (s₁ := Finset.Ioc b c) (s₂ := Finset.Ioc a c) ?_
  · exact Finset.Ioc_diff_Ioc hb
  · exact Finset.Ioc_subset_Ioc (mem_Icc.mp hb).1 (by rfl)

lemma integrability_aux₀ {a b : ℝ} :
    ∀ᵐ (x : ℝ) ∂MeasureTheory.Measure.restrict MeasureTheory.volume [[a, b]],
      ‖(⌊x⌋ : ℂ)‖ ≤ max ‖a‖ ‖b‖ + 1 := by
  apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
  refine MeasureTheory.ae_of_all _ (fun x hx ↦ ?_)
  simp only [inf_le_iff, le_sup_iff, mem_Icc] at hx
  simp only [norm_intCast, Real.norm_eq_abs]
  have : |x| ≤ max |a| |b| := by
    cases' hx.1 with x_ge_a x_ge_b <;> cases' hx.2 with x_le_a x_le_b
    · rw [(by linarith : x = a)]; apply le_max_left
    · apply abs_le_max_abs_abs x_ge_a x_le_b
    · rw [max_comm]; apply abs_le_max_abs_abs x_ge_b x_le_a
    · rw [(by linarith : x = b)]; apply le_max_right
  cases' abs_cases x with hx hx
  · rw [_root_.abs_of_nonneg <| by exact_mod_cast Int.floor_nonneg.mpr hx.2]
    apply le_trans (Int.floor_le x) <| le_trans (hx.1 ▸ this) (by simp)
  · rw [_root_.abs_of_nonpos <| by exact_mod_cast Int.floor_nonpos hx.2.le]
    linarith [(Int.lt_floor_add_one x).le]

lemma integrability_aux₁ {a b : ℝ} :
    IntervalIntegrable (fun (x : ℝ) ↦ (⌊x⌋ : ℂ)) MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded ?_ ?_ integrability_aux₀
  · simp only [Real.volume_interval, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  · apply Measurable.aestronglyMeasurable
    apply Measurable.comp (by exact fun ⦃t⦄ _ ↦ trivial) Int.measurable_floor

lemma integrability_aux₂ {a b : ℝ} :
    IntervalIntegrable (fun (x : ℝ) ↦ (1 : ℂ) / 2 - x) MeasureTheory.volume a b :=
  Continuous.continuousOn (by continuity) |>.intervalIntegrable

lemma integrability_aux {a b : ℝ} :
    IntervalIntegrable (fun (x : ℝ) ↦ (⌊x⌋ : ℂ) + 1 / 2 - x) MeasureTheory.volume a b := by
  convert integrability_aux₁.add integrability_aux₂ using 2; ring

lemma uIcc_subsets {a b c : ℝ} (hc : c ∈ Icc a b) :
    [[a, c]] ⊆ [[a, b]] ∧ [[c, b]] ⊆ [[a, b]] := by
  constructor <;> rw [uIcc_of_le ?_, uIcc_of_le ?_]
  any_goals apply Icc_subset_Icc
  all_goals linarith [hc.1, hc.2]

lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (⌊a⌋ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  let P := fun a₁ b₁ ↦ (∀ x ∈ [[a₁, b₁]], HasDerivAt φ (deriv φ x) x) →
    (ContinuousOn (deriv φ) [[a₁, b₁]]) →
    ∑ n ∈ Finset.Ioc ⌊a₁⌋ ⌊b₁⌋, φ n =
    (∫ x in a₁..b₁, φ x) + (⌊b₁⌋ + 1 / 2 - b₁) * φ b₁ - (⌊a₁⌋ + 1 / 2 - a₁) * φ a₁
      - ∫ x in a₁..b₁, (⌊x⌋ + 1 / 2 - x) * deriv φ x
  apply interval_induction P ?base ?step a b a_lt_b φDiff derivφCont
  · exact fun _ _ _ k₁_le_a₁ a₁_lt_b₁ b₁_le_k₁ φDiff₁ derivφCont₁ ↦
      sum_eq_int_deriv_aux ⟨k₁_le_a₁, a₁_lt_b₁⟩ b₁_le_k₁ φDiff₁ derivφCont₁
  · intro a₁ k₁ b₁ a₁_lt_k₁ k₁_lt_b₁ ih₁ ih₂ φDiff₁ derivφCont₁
    have subs := uIcc_subsets ⟨a₁_lt_k₁.le, k₁_lt_b₁.le⟩
    have s₁ := ih₁ (fun x hx ↦ φDiff₁ x <| subs.1 hx) <| derivφCont₁.mono subs.1
    have s₂ := ih₂ (fun x hx ↦ φDiff₁ x <| subs.2 hx) <| derivφCont₁.mono subs.2
    convert Mathlib.Tactic.LinearCombination'.add_pf s₁ s₂ using 1
    · rw [← Finset.sum_Ioc_add_sum_Ioc]
      simp only [Finset.mem_Icc, Int.floor_intCast, Int.le_floor]
      exact ⟨Int.cast_le.mp <| le_trans (Int.floor_le a₁) a₁_lt_k₁.le, k₁_lt_b₁.le⟩
    · set I₁ := ∫ (x : ℝ) in a₁..b₁, φ x
      set I₂ := ∫ (x : ℝ) in a₁..k₁, φ x
      set I₃ := ∫ (x : ℝ) in k₁..b₁, φ x
      set J₁ := ∫ (x : ℝ) in a₁..b₁, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x
      set J₂ := ∫ (x : ℝ) in a₁..k₁, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x
      set J₃ := ∫ (x : ℝ) in k₁..b₁, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x
      have hI : I₂ + I₃ = I₁ := by
        apply intervalIntegral.integral_add_adjacent_intervals <;>
        apply (HasDerivAt.continuousOn <| fun x hx ↦ φDiff₁ x ?_ ).intervalIntegrable
        · exact subs.1 hx
        · exact subs.2 hx
      have hJ : J₂ + J₃ = J₁ := by
        apply intervalIntegral.integral_add_adjacent_intervals <;>
        refine integrability_aux.mul_continuousOn <| derivφCont₁.mono ?_
        · exact subs.1
        · exact subs.2
      rw [← hI, ← hJ]; ring
/-%%
\begin{proof}\uses{sum_eq_int_deriv_aux}\leanok
  Apply Lemma \ref{sum_eq_int_deriv_aux} in blocks of length $\le 1$.
\end{proof}
%%-/

lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

lemma neg_s_ne_neg_one {s : ℂ} (s_ne_one : s ≠ 1) : -s ≠ -1 := fun hs ↦ s_ne_one <| neg_inj.mp hs

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; rw [(by ring : -s + 1 = 1 - s)]
  · right; refine ⟨neg_s_ne_neg_one s_ne_one, ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  apply hasDerivAt_deriv_iff.mpr <| DifferentiableAt.div (differentiableAt_const _) ?_ ?_
  · exact Real.differentiableAt_cpow_const_of_ne s xpos
  · simp [cpow_eq_zero_iff, xpos.ne']

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ofReal_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      field_simp [r, mul_assoc, ← Complex.cpow_add]
  · simp only [r]
    ring_nf

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

/-%%
\begin{lemma}[ZetaSum_aux1]\label{ZetaSum_aux1}\lean{ZetaSum_aux1}\leanok
  Let $0 < a < b$ be natural numbers and $s\in \C$ with $s \ne 1$ and $s \ne 0$.
  Then
  \[
  \sum_{a < n \le b} \frac{1}{n^s} =  \frac{b^{1-s} - a^{1-s}}{1-s} + \frac{b^{-s}-a^{-s}}{2} + s \int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx.
  \]
\end{lemma}
%%-/
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc (a : ℤ) b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x := fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Int.floor_natCast]
  · rw [Int.floor_natCast, Int.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf
/-%%
\begin{proof}\uses{sum_eq_int_deriv}\leanok
  Apply Lemma \ref{sum_eq_int_deriv} to the function $x \mapsto x^{-s}$.
\end{proof}
%%-/

lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b)
    : 0 < x := lt_of_lt_of_le apos hx.1

lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a,b]])
    : 0 < x :=  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1

lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]

lemma ZetaSum_aux1_3a (x : ℝ) : -(1/2) < ⌊ x ⌋ + 1/2 - x := by
  norm_num [← add_assoc]; linarith [sub_pos_of_lt (Int.lt_floor_add_one x)]

lemma ZetaSum_aux1_3b (x : ℝ) : ⌊x⌋ + 1/2 - x ≤ 1/2 := by
  ring_nf; exact add_le_of_nonpos_right <| sub_nonpos.mpr (Int.floor_le x)

lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨le_of_lt (ZetaSum_aux1_3a x), ZetaSum_aux1_3b x⟩

lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp

lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s

lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)

lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]

open MeasureTheory in
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

open MeasureTheory in
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub

lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [g, Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num

lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos

/-%%
\begin{lemma}[ZetaBnd_aux1a]\label{ZetaBnd_aux1a}\lean{ZetaBnd_aux1a}\leanok
For any $0 < a < b$ and  $s \in \C$ with $\sigma=\Re(s)>0$,
$$
\int_a^b \left|\frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx\right|
\le \frac{a^{-\sigma}-b^{-\sigma}}{\sigma}.
$$
\end{lemma}
%%-/
lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h
/-%%
\begin{proof}\leanok
Apply the triangle inequality
$$
\left|\int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx\right|
\le \int_a^b \frac{1}{x^{\sigma+1}} \, dx,
$$
and evaluate the integral.
\end{proof}
%%-/


lemma tsum_eq_partial_add_tail {N : ℕ} (f : ℕ → ℂ) (hf : Summable f) :
    ∑' (n : ℕ), f n = (∑ n ∈ Finset.range N, f n) + ∑' (n : ℕ), f (n + N) := by
  rw [← Summable.sum_add_tsum_nat_add (f := f) (h := hf) (k := N)]

lemma Finset.Ioc_eq_Ico (M N : ℕ): Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma Finset.Ioc_eq_Icc (M N : ℕ): Finset.Ioc N M = Finset.Icc (N + 1) M := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Icc]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma Finset.Icc_eq_Ico (M N : ℕ): Finset.Icc N M = Finset.Ico N (M + 1) := by
  ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [tsum_eq_partial_add_tail f hf (N := N), add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith

lemma tendsto_coe_atTop : Tendsto (fun (n : ℕ) ↦ (n : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  use ⌊b⌋.toNat + 1
  intro a ha
  cases eq_zero_or_pos a with
  | inl a_zero =>
    simp [a_zero] at ha
  | inr a_zero =>
    by_cases h : ⌊b⌋.toNat < a
    · exact (Int.floor_lt.mp <| (Int.toNat_lt' a_zero).mp h).le
    · simp only [not_lt] at h
      absurd le_trans ha h
      simp

-- related to `ArithmeticFunction.LSeriesSummable_zeta_iff.mpr s_re_gt`
lemma Summable_rpow {s : ℂ} (s_re_gt : 1 < s.re) : Summable (fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s) := by
  apply Summable.of_norm
  have : s.re ≠ 0 := by linarith
  simp only [one_div, norm_inv]
  simp_rw [norm_natCast_cpow_of_re_ne_zero _ this]
  exact (Real.summable_nat_rpow_inv (p := s.re)).mpr s_re_gt

lemma Finset_coe_Nat_Int (f : ℤ → ℂ) (m n : ℕ) :
    (∑ x ∈ Finset.Ioc m n, f x) = ∑ x ∈ Finset.Ioc (m : ℤ) n, f x := by
/-
instead use `Finset.sum_map` and a version of `Nat.image_cast_int_Ioc` stated using `Finset.map`
-/
  apply Finset.sum_nbij (i := (fun (x : ℕ) ↦ (x : ℤ))) ?_ ?_ ?_ fun _ _ ↦ rfl
  · intro x hx; simp only [Finset.mem_Ioc, Nat.cast_lt, Nat.cast_le] at hx ⊢; exact hx
  · intro x₁ _ x₂ _ h; simp only [Nat.cast_inj] at h; exact h
  · intro x hx
    simp only [Finset.coe_Ioc, mem_image, mem_Ioc] at hx ⊢
    lift x to ℕ using (by linarith); exact ⟨x, by exact_mod_cast hx, rfl⟩

lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]

lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop

lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3

lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  -- let g := fun (n : ℕ) ↦ f (n + 1)
  have hf := Summable_rpow s_re_gt
  -- have hg := summable_nat_add_iff 1 |>.mpr <| hf
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    simp only [f]
    convert Finset.sum_map (e := addRightEmbedding 1) ?_  ?_ using 2
    ext n
    simp only [Finset.mem_Ico, Finset.map_add_right_Ico]
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]

lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  apply MeasureTheory.Integrable.bdd_mul ?_ ?_
  · convert ZetaSum_aux2a; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

/-%%
\begin{lemma}[ZetaSum_aux2]\label{ZetaSum_aux2}\lean{ZetaSum_aux2}\leanok
  Let $N$ be a natural number and $s\in \C$, $\Re(s)>1$.
  Then
  \[
  \sum_{N < n} \frac{1}{n^s} =  \frac{- N^{1-s}}{1-s} + \frac{-N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx.
  \]
\end{lemma}
%%-/
lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr' (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      convert ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩ using 1
      convert Finset_coe_Nat_Int (fun n ↦ 1 / (n : ℂ) ^ s) N k
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ))) (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_coe_atTop
/-%%
\begin{proof}\uses{ZetaSum_aux1}\leanok
  Apply Lemma \ref{ZetaSum_aux1} with $a=N$ and $b\to \infty$.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaBnd_aux1b]\label{ZetaBnd_aux1b}\lean{ZetaBnd_aux1b}\leanok
For any $N\ge1$ and $s = \sigma + tI \in \C$, $\sigma > 0$,
$$
\left| \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx \right|
\le \frac{N^{-\sigma}}{\sigma}.
$$
\end{lemma}
%%-/
open MeasureTheory in
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]
/-%%
\begin{proof}\uses{ZetaBnd_aux1a}\leanok
Apply Lemma \ref{ZetaBnd_aux1a} with $a=N$ and $b\to \infty$.
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaBnd_aux1]\label{ZetaBnd_aux1}\lean{ZetaBnd_aux1}\leanok
For any $N\ge1$ and $s = \sigma + tI \in \C$, $\sigma=\in(0,2], 2 < |t|$,
$$
\left| s\int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx \right|
\le 2 |t| \frac{N^{-\sigma}}{\sigma}.
$$
\end{lemma}
%%-/
lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one]
  linarith [hσ.2]
/-%%
\begin{proof}\uses{ZetaBnd_aux1b}\leanok
Apply Lemma \ref{ZetaBnd_aux1b} and estimate $|s|\ll |t|$.
\end{proof}
%%-/

/-%%
Big-Oh version of Lemma \ref{ZetaBnd_aux1}.
\begin{lemma}[ZetaBnd_aux1p]\label{ZetaBnd_aux1p}\lean{ZetaBnd_aux1p}\leanok
For any $N\ge1$ and $s = \sigma + tI \in \C$, $\sigma=\in(0,2], 2 < |t|$,
$$
\left| s\int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx \right|
\ll |t| \frac{N^{-\sigma}}{\sigma}.
$$
\end{lemma}
%%-/
lemma ZetaBnd_aux1p (N : ℕ) (Npos : 1 ≤ N) {σ : ℝ} (hσ : σ ∈ Ioc 0 2) :
    (fun (t : ℝ) ↦ ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖)
    =O[Filter.principal {t | 2 ≤ |t|}] fun t ↦ |t| * N ^ (-σ) / σ := by
  rw [Asymptotics.IsBigO_def]
  use 2
  rw [Asymptotics.isBigOWith_principal]
  intro t ht
  simp only [mem_setOf_eq] at ht
  rw [norm_norm, norm_mul, mul_div_assoc, norm_mul]
  have : 2 * (‖|t|‖ * ‖↑N ^ (-σ) / σ‖) = (2 * |t|) * ((N : ℝ) ^ (-σ) / σ) := by
    simp only [Real.norm_eq_abs, _root_.abs_abs, norm_div]
    have : σ ≠ 0 := by linarith [hσ.1]
    field_simp
    rw [abs_of_pos hσ.1]
    have : 0 < (N : ℝ) ^ (-σ) := by
      refine Real.rpow_pos_of_pos ?_ _
      positivity
    rw [abs_of_pos this]
    ring
  rw [this]
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [norm_real, norm_mul, norm_I, mul_one, Complex.norm_of_nonneg hσ.1.le, Real.norm_eq_abs]
  linarith [hσ.2]
/-%%
\begin{proof}\uses{ZetaBnd_aux1b}\leanok
Apply Lemma \ref{ZetaBnd_aux1b} and estimate $|s|\ll |t|$.
\end{proof}
%%-/

lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)

open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg: r < 0) {N : ℕ} (Npos : 0 < N):
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h := this) (a := |y ^ (r - 1)|) (a0 := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1

open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · convert ZetaSum_aux2a with _ x; simp only [← Complex.norm_real]; simp

open MeasureTheory in
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_setOf_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real,
              Real.norm_eq_abs, mul_eq_mul_left_iff, mul_eq_zero, map_eq_zero, cpow_eq_zero_iff,
              ofReal_eq_zero, ne_eq, abs_eq_zero, Real.log_eq_zero,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · simp only
      convert HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := s) (F := F) (F' := F') (ε := ε)
    (ε_pos := ε_pos) (μ := μ) (bound := bound) (hF_meas := hF_meas) (hF_int := hF_int)
    (hF'_meas := hF'_meas) (h_bound := h_bound) (bound_integrable := bound_integrable)
    (h_diff := h_diff)).2 using 3
  · ext a; simp only [one_div, F, f, div_cpow_eq_cpow_neg]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f, div_cpow_eq_cpow_neg]; ring_nf

noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]

lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹) (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, cpow_ofNat, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero

lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1):
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1; ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1

/-%%
\begin{lemma}[HolomorphicOn_Zeta0]\label{HolomorphicOn_Zeta0}\lean{HolomorphicOn_Zeta0}\leanok
For any $N\ge1$, the function $\zeta_0(N,s)$ is holomorphic on $\{s\in \C\mid \Re(s)>0 ∧ s \ne 1\}$.
\end{lemma}
%%-/
lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt
/-%%
\begin{proof}\uses{riemannZeta0, ZetaBnd_aux1b}\leanok
  The function $\zeta_0(N,s)$ is a finite sum of entire functions, plus an integral
  that's absolutely convergent on $\{s\in \C\mid \Re(s)>0 ∧ s \ne 1\}$ by Lemma \ref{ZetaBnd_aux1b}.
\end{proof}
%%-/

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`
lemma HolomophicOn_riemannZeta :
    HolomorphicOn ζ {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_setOf_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

/-%%
\begin{lemma}[isPathConnected_aux]\label{isPathConnected_aux}\lean{isPathConnected_aux}\leanok
The set $\{s\in \C\mid \Re(s)>0 ∧ s \ne 1\}$ is path-connected.
\end{lemma}
%%-/
lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor; simp
  intro w hw; simp only [ne_eq, mem_setOf_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f, mem_setOf_eq]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_setOf_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f, mem_setOf_eq]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity
/-%%
\begin{proof}\leanok
  Construct explicit paths from $2$ to any point, either a line segment or two joined ones.
\end{proof}
%%-/

/-%%
\begin{lemma}[Zeta0EqZeta]\label{Zeta0EqZeta}\lean{Zeta0EqZeta}\leanok
For $\Re(s)>0$, $s\ne1$, and for any $N$,
$$
\zeta_0(N,s) = \zeta(s).
$$
\end{lemma}
%%-/
lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  let f := riemannZeta
  let g := ζ₀ N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomophicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, setOf_subset_setOf, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [setOf_subset_setOf, imp_self, forall_const, mem_setOf_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz, ← (Summable_rpow hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast
/-%%
\begin{proof}\leanok
\uses{ZetaSum_aux2, riemannZeta0, HolomorphicOn_Zeta0, isPathConnected_aux}
Use Lemma \ref{ZetaSum_aux2} and the Definition \ref{riemannZeta0}.
\end{proof}
%%-/

lemma DerivZeta0EqDerivZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    deriv (ζ₀ N) s = ζ' s := by
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have {x : ℂ} (hx : x ∈ U) : ζ₀ N x = ζ x := by
    simp only [mem_setOf_eq, U] at hx; exact Zeta0EqZeta (N := N) N_pos hx.2 hx.1
  refine deriv_eqOn isOpen_aux ?_ (by simp [U, s_ne_one, reS_pos])
  intro x hx
  have hζ := HolomophicOn_riemannZeta.mono (by aesop)|>.hasDerivAt (s := U) <| isOpen_aux.mem_nhds hx
  exact hζ.hasDerivWithinAt.congr (fun y hy ↦ this hy) (this hx)

lemma le_trans₄ {α : Type*} [Preorder α] {a b c d: α} : a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
  fun hab hbc hcd ↦ le_trans (le_trans hab hbc) hcd

lemma lt_trans₄ {α : Type*} [Preorder α] {a b c d: α} : a < b → b < c → c < d → a < d :=
  fun hab hbc hcd ↦ lt_trans (lt_trans hab hbc) hcd

lemma norm_add₄_le {E: Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  apply le_trans <| norm_add_le (a + b + c) d
  simp only [add_le_add_iff_right]; apply norm_add₃_le

lemma norm_add₅_le {E: Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  apply le_trans <| norm_add_le (a + b + c + d) e
  simp only [add_le_add_iff_right]; apply norm_add₄_le

lemma norm_add₆_le {E: Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E) (f : E) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  apply le_trans <| norm_add_le (a + b + c + d + e) f
  simp only [add_le_add_iff_right]; apply norm_add₅_le

lemma add_le_add_le_add {α : Type*} [Add α] [Preorder α]
    [CovariantClass α α (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    [CovariantClass α α (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    {a b c d e f : α} (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) : a + c + e ≤ b + d + f :=
  add_le_add (add_le_add h₁ h₂) h₃

lemma add_le_add_le_add_le_add {α : Type*} [Add α] [Preorder α]
    [CovariantClass α α (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    [CovariantClass α α (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    {a b c d e f g h : α} (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (h₄ : g ≤ h) :
    a + c + e + g ≤ b + d + f + h:= add_le_add (add_le_add_le_add h₁ h₂ h₃) h₄

lemma mul_le_mul₃ {α : Type*} {a b c d e f : α} [MulZeroClass α] [Preorder α] [PosMulMono α]
    [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (c0 : 0 ≤ c) (b0 : 0 ≤ b) (e0 : 0 ≤ e) :
     a * c * e ≤ b * d * f := by
  apply mul_le_mul (mul_le_mul h₁ h₂ c0 b0) h₃ e0 <| mul_nonneg b0 <| le_trans c0 h₂

/-%%
\begin{lemma}[ZetaBnd_aux2]\label{ZetaBnd_aux2}\lean{ZetaBnd_aux2}\leanok
Given $n ≤ t$ and $\sigma$ with $1-A/\log t \le \sigma$, we have
that
$$
|n^{-s}| \le n^{-1} e^A.
$$
\end{lemma}
%%-/
lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by
  set s := σ + t * I
  by_cases n0 : n = 0
  · simp_rw [n0, CharP.cast_eq_zero, inv_zero, zero_mul]
    rw [Complex.zero_cpow ?_]; simp
    exact fun h ↦ σpos.ne' <| zero_eq_neg.mp <| zero_re ▸ h ▸ (by simp [s])
  have n_gt_0 : 0 < n := Nat.pos_of_ne_zero n0
  have n_gt_0' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n_gt_0
  have n_ge_1 : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr <| Nat.succ_le_of_lt n_gt_0
  calc
    _ = |((n : ℝ) ^ (-σ))| := ?_
    _ ≤ Real.exp (Real.log n * -σ) := Real.abs_rpow_le_exp_log_mul (n : ℝ) (-σ)
    _ ≤ Real.exp (Real.log n *  -(1 - A / Real.log t)) := ?_
    _ ≤ Real.exp (- Real.log n + A) := Real.exp_le_exp_of_le ?_
    _ ≤ _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log n_gt_0']
  · have : ‖(n : ℂ) ^ (-s)‖ = n ^ (-s.re) := norm_cpow_eq_rpow_re_of_pos n_gt_0' (-s)
    rw [this, abs_eq_self.mpr <| Real.rpow_nonneg n_gt_0'.le _]; simp [s]
  · apply Real.exp_le_exp_of_le <| mul_le_mul_of_nonneg_left _ <| Real.log_nonneg n_ge_1
    rw [neg_sub, neg_le_sub_iff_le_add, add_comm, ← Real.log_abs]; linarith
  · simp only [neg_sub, le_neg_add_iff_add_le]
    ring_nf
    conv => rw [mul_comm, ← mul_assoc, ← Real.log_abs]; rhs; rw [← one_mul A]
    gcongr
    by_cases ht1 : |t| = 1; simp [ht1]
    apply (inv_mul_le_iff₀ ?_).mpr; convert Real.log_le_log n_gt_0' n_le_t using 1; rw [mul_one]
    exact Real.log_pos <| lt_of_le_of_ne (le_trans n_ge_1 n_le_t) <| fun t ↦ ht1 (t.symm)
/-%%
\begin{proof}\leanok
Use $|n^{-s}| = n^{-\sigma}
= e^{-\sigma \log n}
\le
\exp(-\left(1-\frac{A}{\log t}\right)\log n)
\le
n^{-1} e^A$,
since $n\le t$.
\end{proof}
%%-/

lemma logt_gt_one {t : ℝ} (t_ge : 3 < |t|) : 1 < Real.log |t| := by
  rw [← Real.log_exp (x := 1)]
  apply Real.log_lt_log (Real.exp_pos _)
  linarith [(by exact lt_trans Real.exp_one_lt_d9 (by norm_num) : Real.exp 1 < 3)]

lemma UpperBnd_aux {A σ t: ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
      (σ_ge : 1 - A / Real.log |t| ≤ σ) : let N := ⌊|t|⌋₊;
      0 < N ∧ N ≤ |t| ∧ 1 < Real.log |t| ∧ 1 - A < σ ∧ 0 < σ ∧ σ + t * I ≠ 1 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  have logt_gt := logt_gt_one t_gt
  have σ_gt : 1 - A < σ := by
    apply lt_of_lt_of_le ((sub_lt_sub_iff_left (a := 1)).mpr ?_) σ_ge
    exact (div_lt_iff₀ (by linarith)).mpr <| lt_mul_right hA.1 logt_gt
  refine ⟨Npos, N_le_t, logt_gt, σ_gt, by linarith [hA.2], ?_⟩
  contrapose! t_gt
  simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im] at t_gt
  norm_num [t_gt.2]

lemma UpperBnd_aux2 {A σ t : ℝ} (t_ge : 3 < |t|) (σ_ge : 1 - A / Real.log |t| ≤ σ) :
      |t| ^ (1 - σ) ≤ Real.exp A := by
  have : |t| ^ (1 - σ) ≤ |t| ^ (A / Real.log |t|) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply le_trans this ?_
  conv => lhs; lhs; rw [← Real.exp_log (by linarith : 0 < |t|)]
  rw [div_eq_mul_inv, Real.rpow_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, mul_comm,
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  apply Real.log_ne_zero.mpr; split_ands <;> linarith

lemma riemannZeta0_zero_aux (N : ℕ) (Npos : 0 < N):
    ∑ x ∈ Finset.Ico 0 N, ((x : ℝ))⁻¹ = ∑ x ∈ Finset.Ico 1 N, ((x : ℝ))⁻¹ := by
  have : Finset.Ico 1 N ⊆ Finset.Ico 0 N := by
    intro x hx
    simp only [Finset.mem_Ico, Nat.Ico_zero_eq_range, Finset.mem_range] at hx ⊢
    exact hx.2
  rw [← Finset.sum_sdiff (s₁ := Finset.Ico 1 N) (s₂ := Finset.Ico 0 N) this]
  have : Finset.Ico 0 N \ Finset.Ico 1 N = Finset.range 1 := by
    ext a
    simp only [Nat.Ico_zero_eq_range, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico, not_and,
      not_lt, Finset.range_one, Finset.mem_singleton]
    exact ⟨fun _ ↦ by omega, fun ha ↦ ⟨by simp [ha, Npos], by omega⟩⟩
  rw [this]; simp

lemma UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤ Real.exp A * C * Real.log |t| := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt
  have (n : ℕ) (hn : n ∈ Finset.range (N + 1)) := ZetaBnd_aux2 (n := n) hA.1 σPos ?_ σ_ge
  · replace := norm_sum_le_of_le (Finset.range (N + 1)) this
    rw [← Finset.sum_mul, mul_comm _ (Real.exp A)] at this
    rw [mul_assoc]
    apply le_trans this <| (mul_le_mul_left A.exp_pos).mpr ?_
    have : 1 + Real.log (N : ℝ) ≤ C * Real.log |t| := by
      by_cases hN : N = 1
      · simp only [hN, Nat.cast_one, Real.log_one, add_zero]
        have : 2 * 1 ≤ C * Real.log |t| := mul_le_mul hC logt_gt.le (by linarith) (by linarith)
        linarith
      · rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
          ← one_mul <| Real.log (N: ℝ)]
        apply add_le_add logt_gt.le
        refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
        exact Real.log_le_log (by positivity) N_le_t
    refine le_trans ?_ this
    convert harmonic_eq_sum_Icc ▸ harmonic_le_one_add_log N
    · simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.range_eq_Ico]
      rw [riemannZeta0_zero_aux (N + 1) (by linarith)]; congr! 1
  · simp only [Finset.mem_range] at hn
    linarith [(by exact_mod_cast (by omega : n ≤ N) : (n : ℝ) ≤ N)]

lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [N_le_t]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| < N + 1 by linarith [(by exact_mod_cast (by omega) : 1 ≤ (N : ℝ))]
    apply Nat.lt_floor_add_one

lemma UpperBnd_aux5 {σ t : ℝ}  (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  obtain ⟨h₁, h₂⟩ := Nat.self_div_floor_bound (by linarith)
  calc _ ≤ ((|t| / ↑⌊|t|⌋₊) ^ (2 : ℝ)) := by gcongr; exact h₁
       _ ≤ (2 : ℝ) ^ (2 : ℝ) := by gcongr
       _ = 4 := by norm_num

lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
  (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  have bnd := UpperBnd_aux5 t_ge hσ.2
  have bnd' : (|t| / ⌊|t|⌋₊) ^ σ ≤ 2 * |t| := by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm).mpr
    conv => rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [div_rpow_eq_rpow_div_neg (by positivity) (by positivity), neg_sub]
    refine le_trans₄ ?_ bnd' ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr N_le_t) (by simp)
    · apply (mul_le_mul_left (by norm_num)).mpr; simpa using abs_im_le_norm (1 - (σ + t * I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith), Real.rpow_one, div_mul_eq_mul_div, mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert bnd' using 1
    rw [← Real.rpow_neg (by linarith), div_rpow_neg_eq_rpow_div (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc, mul_comm, mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1] : 4 ≤ σ * 8)
    convert bnd using 1; exact div_rpow_neg_eq_rpow_div (by positivity) (by positivity)

lemma ZetaUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2); -- the 2 comes from ZetaBnd_aux1
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖ + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t| := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, σPos, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ = Real.exp A * 2 * Real.log |t| + N ^ (1 - σ) / ‖(1 - s)‖ + N ^ (-σ) / 2 +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + |t| ^ (1 - σ) * 2 +
        |t| ^ (1 - σ) + 2 * |t| * (8 * |t| ^ (-σ)) := ?_
    _ = Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * |t| ^ (1 - σ) := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * 1 := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * Real.log |t| := ?_
    _ = _ := by ring
  · simp only [add_le_add_iff_right, one_div_cpow_eq_cpow_neg]
    convert UpperBnd_aux3 (C := 2) hA hσ.1 t_gt le_rfl using 1
  · simp only [add_le_add_iff_left]; exact ZetaBnd_aux1 N (by linarith) ⟨σPos, hσ.2⟩ (by linarith)
  · simp only [norm_div, norm_neg, RCLike.norm_ofNat, Nat.abs_cast, s]
    congr <;> (convert norm_natCast_cpow_of_pos Npos _; simp)
  · have ⟨h₁, h₂, h₃⟩ := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t
    refine add_le_add_le_add_le_add le_rfl h₁ h₂ ?_
    rw [mul_div_assoc]
    exact mul_le_mul_left (mul_pos (by norm_num) (by positivity)) |>.mpr h₃
  · ring_nf; conv => lhs; rhs; lhs; rw [mul_comm |t|]
    rw [← Real.rpow_add_one (by positivity)]; ring_nf
  · simp only [Real.log_abs, add_le_add_iff_left, mul_one]
    exact mul_le_mul_left (by positivity) |>.mpr <| UpperBnd_aux2 t_gt hσ.1
  · simp only [add_le_add_iff_left]
    apply mul_le_mul_left (by norm_num [Real.exp_pos]) |>.mpr <| logt_gt.le

/-%%
\begin{lemma}[ZetaUpperBnd]\label{ZetaUpperBnd}\lean{ZetaUpperBnd}\leanok
For any $s = \sigma + tI \in \C$, $1/2 \le \sigma\le 2, 3 < |t|$
and any $0 < A < 1$ sufficiently small, and $1-A/\log |t| \le \sigma$, we have
$$
|\zeta(s)| \ll \log t.
$$
\end{lemma}
%%-/
lemma ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖ζ (σ + t * I)‖ ≤ C * Real.log |t| := by
  let A := (1 / 2 : ℝ)
  let C := Real.exp A * (5 + 8 * 2) -- the 2 comes from ZetaBnd_aux1
  refine ⟨A, ⟨by norm_num, by norm_num⟩, C, (by positivity), ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ := UpperBnd_aux ⟨by norm_num, by norm_num⟩ t_gt σ_ge
  rw [← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le) ?_
  convert ZetaUpperBnd' ⟨by norm_num, le_rfl⟩ t_gt ⟨σ_ge, σ_le⟩ using 1; simp
/-%%
\begin{proof}\uses{ZetaBnd_aux1, ZetaBnd_aux2, Zeta0EqZeta}\leanok
First replace $\zeta(s)$ by $\zeta_0(N,s)$ for $N = \lfloor |t| \rfloor$.
We estimate:
$$
|\zeta_0(N,s)| \ll
\sum_{1\le n \le |t|} |n^{-s}|
+
\frac{- |t|^{1-\sigma}}{|1-s|} + \frac{-|t|^{-\sigma}}{2} +
|t| \cdot |t| ^ {-σ} / σ
$$
$$
\ll
e^A \sum_{1\le n < |t|} n^{-1}
+|t|^{1-\sigma}
$$
,
where we used Lemma \ref{ZetaBnd_aux2} and Lemma \ref{ZetaBnd_aux1}.
The first term is $\ll \log |t|$.
For the second term, estimate
$$
|t|^{1-\sigma}
\le |t|^{1-(1-A/\log |t|)}
= |t|^{A/\log |t|} \ll 1.
$$
\end{proof}
%%-/

lemma norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by
  have := Complex.ofReal_log (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [(by simp : ((n : ℝ) : ℂ) = (n : ℂ))] at this
  rw [← this, Complex.norm_of_nonneg]
  exact Real.log_natCast_nonneg n

lemma Real.log_natCast_monotone : Monotone (fun (n : ℕ) ↦ Real.log n) := by
  intro n m hnm
  cases n
  · simp only [CharP.cast_eq_zero, Real.log_zero, Real.log_natCast_nonneg]
  · apply Real.log_le_log <;> simp only [Nat.cast_add, Nat.cast_one]
    · exact Nat.cast_add_one_pos _
    · exact_mod_cast hnm

lemma Finset.Icc0_eq (N : ℕ) : Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N := by
  refine Finset.ext_iff.mpr ?_
  intro a
  cases a
  · simp only [Finset.mem_Icc, le_refl, zero_le, and_self, Finset.mem_union, Finset.mem_singleton,
    nonpos_iff_eq_zero, one_ne_zero, and_true, or_false]
  · simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, true_and, Finset.mem_union,
    Finset.mem_singleton, add_eq_zero, one_ne_zero, and_false, false_or]

lemma harmonic_eq_sum_Icc0_aux (N : ℕ) :  ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
  rw [Finset.Icc0_eq, Finset.sum_union]
  · simp only [Finset.sum_singleton, CharP.cast_eq_zero, inv_zero, zero_add]
  · simp only [Finset.disjoint_singleton_left, Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero,
    zero_le, and_true, not_false_eq_true]

lemma harmonic_eq_sum_Icc0 (N : ℕ) : ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc0_aux, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt
  have logN_pos : 0 ≤ Real.log N := Real.log_nonneg (by norm_cast)
  have fact0 {n : ℕ} (hn : n ≤ N) : n ≤ |t| := by linarith [(by exact_mod_cast hn : (n : ℝ) ≤ N)]
  have fact1 {n : ℕ} (hn : n ≤ N) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * A.exp := ZetaBnd_aux2 hA.1 σPos (fact0 hn) σ_ge
  have fact2 {n : ℕ} (hn : n ≤ N) : Real.log n ≤ Real.log |t| := by
    cases n
    · simp only [CharP.cast_eq_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.add_one_pos _) (fact0 hn)
  have fact3 (n : ℕ) (hn : n ≤ N) :
    ‖-1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖ ≤ (n : ℝ)⁻¹ * Real.exp A * (Real.log |t|) := by
    convert mul_le_mul (fact1 hn) (fact2 hn) (Real.log_natCast_nonneg n) (by positivity)
    simp only [norm_mul, norm_div, norm_neg, norm_one, one_div, natCast_log, ← norm_inv, cpow_neg]
    congr; exact norm_complex_log_ofNat n
  have := norm_sum_le_of_le (Finset.range (N + 1))
    (by simp only [Finset.mem_range, Nat.lt_succ]; exact fact3)
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_comm _ A.exp, mul_assoc] at this
  rw [mul_assoc]
  apply le_trans this <| (mul_le_mul_left A.exp_pos).mpr ?_
  rw [pow_two, ← mul_assoc, Finset.range_eq_Ico, ← Finset.Icc_eq_Ico, harmonic_eq_sum_Icc0]
  apply le_trans (mul_le_mul (h₁ := harmonic_le_one_add_log (n := N)) (le_refl (Real.log |t|))
    (by linarith) (by linarith))
  apply (mul_le_mul_right (by linarith)).mpr
  rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
      ← one_mul <| Real.log (N: ℝ)]
  refine add_le_add logt_gt.le <| mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
  exact Real.log_le_log (by positivity) N_le_t

lemma DerivUpperBnd_aux2 {A σ t : ℝ}(t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 →
    1 / 2 < σ → ‖-↑N ^ (1 - s) / (1 - s) ^ 2‖ ≤ A.exp * 2 * (1 / 3) := by
  intro N s Npos N_le_t neOne σ_gt
  dsimp only [s]
  simp_rw [norm_div, norm_neg, norm_pow, norm_natCast_cpow_of_pos Npos _,
    sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero]
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
  rw [(by ring_nf : N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ ^ 2 =
          N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ * 1 / ‖1 - (↑σ + ↑t * I)‖)]
  apply mul_le_mul ?_ ?_ (inv_nonneg.mpr <| norm_nonneg _) ?_
  · rw [mul_one]; exact le_trans h (by gcongr; exact UpperBnd_aux2 t_gt hσ.1)
  · rw [inv_eq_one_div, div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm,
        mul_comm, ← mul_div_assoc, mul_one, le_div_iff₀ (by norm_num), one_mul]
    apply le_trans t_gt.le ?_
    rw [← abs_neg]; convert abs_im_le_norm (1 - (σ + t * I)); simp
  · exact mul_nonneg (Real.exp_nonneg _) (by norm_num)

theorem DerivUpperBnd_aux3 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * ↑N ^ (1 - s) / (1 - s)‖ ≤ A.exp * 2 * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
    convert le_trans h ?_ using 1
    · simp [s, norm_natCast_cpow_of_pos Npos _, N]
    · gcongr; exact UpperBnd_aux2 t_gt hσ.1
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t

theorem DerivUpperBnd_aux4 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * (N : ℂ) ^ (-s) / 2‖ ≤ A.exp * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm, RCLike.norm_ofNat]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.1
    convert le_trans h (UpperBnd_aux2 t_gt hσ.1) using 1
    simp [s, norm_natCast_cpow_of_pos Npos _, N]
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t

theorem DerivUpperBnd_aux5 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → 1 / 2 < σ →
    ‖1 * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1)‖ ≤
    1 / 3 * (2 * |t| * ↑N ^ (-σ) / σ) := by
  intro N s Npos σ_gt
  have neZero : s ≠ 0 := by
    contrapose! σ_gt
    simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, zero_re, add_im, mul_im, zero_add, zero_im, s] at σ_gt
    linarith
  have : 1 = 1 / s * s := by field_simp
  nth_rewrite 1 [this]
  rw [mul_assoc, norm_mul]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · simp only [s, norm_div, norm_one]
    apply one_div_le_one_div (norm_pos_iff.mpr neZero) (by norm_num) |>.mpr
    apply le_trans t_gt.le ?_
    convert abs_im_le_norm (σ + t * I); simp
  · have hσ : σ ∈ Ioc 0 2 := ⟨(by linarith), hσ.2⟩
    simp only [s]
    have := ZetaBnd_aux1 N (by omega) hσ (by linarith)
    simp only [div_cpow_eq_cpow_neg] at this
    convert this using 1; congr; funext x; ring_nf

theorem DerivUpperBnd_aux6 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    0 < N → ↑N ≤ |t| → ↑σ + ↑t * I ≠ 1 → 1 / 2 < σ →
    2 * |t| * ↑N ^ (-σ) / σ ≤ 2 * (8 * A.exp) := by
  intro N Npos N_le_t neOne σ_gt
  rw [mul_div_assoc, mul_assoc]
  apply mul_le_mul_left (by norm_num) |>.mpr
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.2
  apply le_trans (mul_le_mul_left (a := |t|) (by positivity) |>.mpr h) ?_
  rw [← mul_assoc, mul_comm _ 8, mul_assoc]
  gcongr
  convert UpperBnd_aux2 t_gt hσ.1 using 1
  rw [mul_comm, ← Real.rpow_add_one (by positivity)]; ring_nf

lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  have xpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have : ‖(x.log : ℂ)‖ = x.log := Complex.norm_of_nonneg <| Real.log_nonneg hx
  simp [← norm_real, this, Complex.norm_cpow_eq_rpow_re_of_pos xpos, ← Real.norm_eq_abs, ← ofReal_ofNat,
    ← ofReal_inv, ← ofReal_add, ← ofReal_sub, ← ofReal_intCast, one_div]

lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  rw [← one_mul (x ^ (-σ - 1) * Real.log x), mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by bound)
  exact le_trans (ZetaSum_aux1_3 x) (by norm_num)

lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ^2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) (x ^ (-σ - 1) * Real.log x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl xpos.ne.symm)
  have h2 := h1.const_mul (1 / σ^2)
  have cancel : 1 / σ^2 * σ = 1 / σ := by field_simp; ring
  rw [neg_mul, mul_neg, ← mul_assoc, cancel] at h2
  have h3 := Real.hasDerivAt_log xpos.ne.symm
  have h4 := HasDerivAt.mul (h1.const_mul (1 / σ)) h3
  have cancel := Real.rpow_add xpos (-σ) (-1)
  have : -σ + -1 = -σ - 1 := by rfl
  rw [← Real.rpow_neg_one x, mul_assoc (1 / σ) (x ^ (-σ)), ← cancel, this] at h4
  convert h2.add h4 |>.neg using 1
  field_simp; ring

lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ^2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) (x ^ (-σ - 1) * Real.log x) x := by
  intro x hx
  simp at hx
  exact DerivUpperBnd_aux7_3 (by linarith) σnz

lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  intro x hx
  simp at hx
  bound

lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_neg_atTop σpos
  have h2 := h1.const_mul (1 / σ^2)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_pow_atTop σ 1 σpos
    simp at this
    apply Tendsto.congr' _ this
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [mul_comm]
    apply div_rpow_eq_rpow_neg
    exact hx
  have h4 := h3.const_mul (1 / σ)
  have h5 := (h2.add h4).neg
  convert h5 using 1
  · ext; ring
  simp


open MeasureTheory in
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos: 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (l := 0)
  · exact DerivUpperBnd_aux7_3' (by linarith) (by linarith)
  · exact DerivUpperBnd_aux7_nonneg ha
  · exact DerivUpperBnd_aux7_tendsto σpos

open MeasureTheory in
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos: 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul <| DerivUpperBnd_aux7_4 σpos ha
  · exact Measurable.aestronglyMeasurable <| Measurable.abs measurable_floor_add_half_sub
  use 1 / 2
  intro x
  simp only [Real.norm_eq_abs, _root_.abs_abs]
  exact  ZetaSum_aux1_3 x

open MeasureTheory in
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x = 1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a  := by
  convert integral_Ioi_of_hasDerivAt_of_nonneg' (DerivUpperBnd_aux7_3' (by linarith) (by linarith)) (DerivUpperBnd_aux7_nonneg ha) (DerivUpperBnd_aux7_tendsto σpos) using 1
  ring

/-%%
\begin{lemma}[DerivUpperBnd_aux7]\label{DerivUpperBnd_aux7}\lean{DerivUpperBnd_aux7}\leanok
For any $s = \sigma + tI \in \C$, $1/2 \le \sigma\le 2, 3 < |t|$, and any $0 < A < 1$ sufficiently small,
and $1-A/\log |t| \le \sigma$, we have
$$
\left\|s \cdot \int_{N}^{\infty} \left(\left\lfloor x \right\rfloor + \frac{1}{2} - x\right) \cdot x^{-s-1} \cdot (-\log x)\right\|
\le 2 \cdot |t| \cdot N^{-\sigma} / \sigma \cdot \log |t|.
$$
\end{lemma}
%%-/
open MeasureTheory in
theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  have σpos : 0 < σ := lt_trans (by norm_num) σ_gt
  rw [norm_mul, (by ring : 6 * |t| * ↑N ^ (-σ) / σ * Real.log |t| = (2 * |t|) * (3 * ↑N ^ (-σ) / σ * Real.log |t|))]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply le_trans (by apply norm_add_le)
    simp [abs_of_pos σpos]
    linarith [hσ.2]
  apply le_trans (by apply norm_integral_le_integral_norm)
  calc ∫ (x : ℝ) in Ioi (N : ℝ), ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖
    _ = ∫ (x : ℝ) in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
      apply setIntegral_congr_fun (by measurability)
      intro x hx
      simp at hx
      exact DerivUpperBnd_aux7_1 (lt_of_le_of_lt (mod_cast Npos) hx).le
    _ ≤ ∫ (x : ℝ) in Ioi (N : ℝ), x ^ (-σ - 1) * x.log := by
      apply setIntegral_mono_on _ _ (by measurability)
      · intro x hx
        exact DerivUpperBnd_aux7_2 (lt_of_le_of_lt (mod_cast Npos) hx).le
      · apply DerivUpperBnd_aux7_5 σpos (mod_cast Npos)
      apply DerivUpperBnd_aux7_4 σpos (mod_cast Npos)
    _ = 1 / σ^2 * N ^ (-σ) + 1 / σ * N ^ (-σ) * Real.log N :=
      DerivUpperBnd_aux7_integral_eq (mod_cast Npos) σpos
    _ ≤ 3 * ↑N ^ (-σ) / σ * |t|.log := by
      have h2 : 1 / σ * ↑N ^ (-σ) * Real.log ↑N ≤ ↑N ^ (-σ) / σ * Real.log |t| := calc
        _ = ↑N ^ (-σ) / σ * Real.log N := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.log_le_log (mod_cast Npos) N_le_t
      have : 2 ≤ 2 * Real.log |t| := by
        nth_rewrite 1  [← mul_one 2]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact logt_gt_one t_gt |>.le
      have h1 : 1 / σ^2 * ↑N ^ (-σ) ≤ 2 * ↑N ^ (-σ) / σ * Real.log |t| := calc
        1 / σ^2 * ↑N ^ (-σ) = (↑N ^ (-σ) / σ) * (1 / σ) := by ring
        _ ≤ ↑N ^ (-σ) / σ * (2 * Real.log |t|):= by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ this
          exact (one_div_le σpos (by norm_num)).mpr σ_gt.le
        _ = _ := by ring
      convert add_le_add h1 h2 using 1
      ring

/-%%
\begin{proof}\leanok
Estimate $|s|= |\sigma + tI|$ by $|s|\le 2 +|t| \le 2|t|$ (since $|t|>3$). Estimating $|\left\lfloor x \right\rfloor+1/2-x|$ by $1$,
and using $|x^{-s-1}| = x^{-\sigma-1}$, we have
$$
\left\| s \cdot \int_{N}^{\infty} \left(\left\lfloor x \right\rfloor + \frac{1}{2} - x\right) \cdot x^{-s-1} \cdot (-\log x)\right\|
\le 2 \cdot |t|
\int_{N}^{\infty} x^{-\sigma} \cdot (\log x).
$$
For the last integral, integrate by parts, getting:
$$
\int_{N}^{\infty} x^{-\sigma-1} \cdot (\log x) =
\frac{1}{\sigma}N^{-\sigma} \cdot \log N + \frac1{\sigma^2} \cdot N^{-\sigma}.
$$
Now use $\log N \le \log |t|$ to get the result.
\end{proof}
%%-/

lemma ZetaDerivUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, _, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux1 hA hσ.1 t_gt (by simp : (2 : ℝ) ≤ 2)
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux2 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux3 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux4 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * |t| * N ^ (-σ) / σ) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux5 t_gt hσ Npos σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * |t| * N ^ (-σ) / σ) * (Real.log |t|) := by
        gcongr; exact DerivUpperBnd_aux7 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * (8 * Real.exp A)) * (Real.log |t|) := by
        gcongr; convert mul_le_mul_of_nonneg_left (DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt) (by norm_num : (0 : ℝ) ≤ 3) using 1 <;> ring
    _ ≤ _ := by
      simp only [C]
      ring_nf
      rw [(by ring : A.exp * |t|.log ^ 2 * 59 = A.exp * |t|.log ^ 2 * 6 + A.exp * |t|.log ^ 2 * 51 +
        A.exp * |t|.log ^ 2 * 2)]
      nth_rewrite 1 [← mul_one A.exp]
      gcongr
      swap
      nth_rewrite 1 [← mul_one |t|.log, (by ring : |t|.log ^ 2 = |t|.log * |t|.log)]
      gcongr
      nlinarith

/-%%
\begin{lemma}[ZetaDerivUpperBnd]\label{ZetaDerivUpperBnd}\lean{ZetaDerivUpperBnd}\leanok
For any $s = \sigma + tI \in \C$, $1/2 \le \sigma\le 2, 3 < |t|$,
there is an $A>0$ so that for $1-A/\log t \le \sigma$, we have
$$
|\zeta'(s)| \ll \log^2 t.
$$
\end{lemma}
%%-/
lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖ζ' (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  obtain ⟨A, hA, _, _, _⟩ := ZetaUpperBnd
  let C := Real.exp A * 59
  refine ⟨A, hA, C, by positivity, ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, N_le_t, _, _, σPos, neOne⟩ := UpperBnd_aux hA t_gt σ_ge
  rw [← DerivZeta0EqDerivZeta Npos (by simp [σPos]) neOne]
  set N : ℕ := ⌊|t|⌋₊
  rw [(HasDerivAtZeta0 Npos (s := σ + t * I) (by simp [σPos]) neOne).deriv]
  dsimp only [ζ₀']
  rw [← add_assoc]
  set aa := ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)
  set bb := -(N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I)) ^ 2
  set cc := (Real.log N) * (N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I))
  set dd := (Real.log N) * (N : ℂ) ^ (-(σ + t * I)) / 2
  set ee := 1 * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1)
  set ff := (σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1) * -(Real.log x)
  rw [(by ring : aa + (bb + cc) + dd + ee + ff = aa + bb + cc + dd + ee + ff)]
  apply le_trans (by apply norm_add₆_le) ?_
  convert ZetaDerivUpperBnd' hA t_gt ⟨σ_ge, σ_le⟩
/-%%
\begin{proof}\uses{ZetaBnd_aux1, ZetaBnd_aux2, Zeta0EqZeta, DerivUpperBnd_aux7}\leanok
First replace $\zeta(s)$ by $\zeta_0(N,s)$ for $N = \lfloor |t| \rfloor$.
Differentiating term by term, we get:
$$
\zeta'(s) = -\sum_{1\le n < N} n^{-s} \log n
+ \frac{N^{1 - s}}{(1 - s)^2} + \frac{N^{1 - s} \log N} {1 - s}
+ \frac{N^{-s}\log N}{2} +
\int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
-s \int_N^\infty \log x \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
.
$$
Estimate as before, with an extra factor of $\log |t|$.
\end{proof}
%%-/

lemma Tendsto_nhdsWithin_punctured_map_add {f : ℝ → ℝ} (a x : ℝ)
    (f_mono : StrictMono f) (f_iso : Isometry f):
    Tendsto (fun y ↦ f y + a) (𝓝[>] x) (𝓝[>] (f x + a)) := by
  refine tendsto_iff_forall_eventually_mem.mpr ?_
  intro v hv
  simp only [mem_nhdsWithin] at hv
  obtain ⟨u, hu, hu2, hu3⟩ := hv
  let t := {x | f x + a ∈ u}
  have : t ∩ Ioi x ∈ 𝓝[>] x := by
    simp only [mem_nhdsWithin]
    use t
    simp only [subset_inter_iff, inter_subset_left, inter_subset_right, and_self,
      and_true, t]
    simp
    refine ⟨?_, by simp [hu2]⟩
    simp [Metric.isOpen_iff] at hu ⊢
    intro x hx
    obtain ⟨ε, εpos, hε⟩ := hu (f x + a) hx
    simp only [Metric.ball, dist_sub_eq_dist_add_right, setOf_subset_setOf] at hε ⊢
    exact ⟨ε, εpos, fun _ hy ↦ hε (by simp [isometry_iff_dist_eq.mp f_iso, hy])⟩
  filter_upwards [this]
  intro b hb
  simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, t] at hb
  refine hu3 ?_
  simp only [mem_inter_iff, mem_Ioi, add_lt_add_iff_right]
  exact ⟨hb.1, f_mono hb.2⟩

lemma Tendsto_nhdsWithin_punctured_add (a x : ℝ) :
    Tendsto (fun y ↦ y + a) (𝓝[>] x) (𝓝[>] (x + a)) :=
  Tendsto_nhdsWithin_punctured_map_add a x strictMono_id isometry_id

lemma riemannZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ ζ (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by
  have : (fun w : ℂ ↦ ζ (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * ζ (1 + w)) (𝓝[≠] 0) (𝓝 1) := by
      convert Tendsto.comp (f := fun w ↦ 1 + w) riemannZeta_residue_one ?_ using 1
      · ext w
        simp only [Function.comp_apply, add_sub_cancel_left]
      · refine tendsto_iff_comap.mpr <| map_le_iff_le_comap.mp <| Eq.le ?_
        convert Homeomorph.map_punctured_nhds_eq (Homeomorph.addLeft (1 : ℂ)) 0 using 2 <;> simp
    exact ((Asymptotics.isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <|
      Tendsto.isBigO_one ℂ H).trans <| Asymptotics.isBigO_refl ..
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhdsGT_le_nhdsNE 0


/-%%
\begin{lemma}[ZetaNear1BndFilter]\label{ZetaNear1BndFilter}\lean{ZetaNear1BndFilter}\leanok
As $\sigma\to1^+$,
$$
|\zeta(\sigma)| \ll 1/(\sigma-1).
$$
\end{lemma}
%%-/
lemma ZetaNear1BndFilter:
    (fun σ : ℝ ↦ ζ σ) =O[𝓝[>](1 : ℝ)] (fun σ ↦ (1 : ℂ) / (σ - 1)) := by
  have := Tendsto_nhdsWithin_punctured_add (a := -1) (x := 1)
  simp only [add_neg_cancel, ← sub_eq_add_neg] at this
  have := riemannZeta_isBigO_near_one_horizontal.comp_tendsto this
  convert this using 1 <;> {ext; simp}
/-%%
\begin{proof}\uses{ZetaBnd_aux1, Zeta0EqZeta}\leanok
Zeta has a simple pole at $s=1$. Equivalently, $\zeta(s)(s-1)$ remains bounded near $1$.
Lots of ways to prove this.
Probably the easiest one: use the expression for $\zeta_0 (N,s)$ with $N=1$ (the term $N^{1-s}/(1-s)$ being the only unbounded one).
\end{proof}
%%-/

/-%%
\begin{lemma}[ZetaNear1BndExact]\label{ZetaNear1BndExact}\lean{ZetaNear1BndExact}\leanok
There exists a $c>0$ such that for all $1 < \sigma ≤ 2$,
$$
|\zeta(\sigma)| ≤ c/(\sigma-1).
$$
\end{lemma}
%%-/
lemma ZetaNear1BndExact:
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖ζ σ‖ ≤ c / (σ - 1) := by
  have := ZetaNear1BndFilter
  rw [Asymptotics.isBigO_iff] at this
  obtain ⟨c, U, hU, V, hV, h⟩ := this
  obtain ⟨T, hT, T_open, h1T⟩ := mem_nhds_iff.mp hU
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp T_open 1 h1T
  simp only [Metric.ball] at hε
  replace hε : Ico 1 (1 + ε) ⊆ U := by
    refine subset_trans (subset_trans ?_ hε) hT
    intro x hx
    simp only [mem_Ico] at hx
    simp only [dist, abs_lt]
    exact ⟨by linarith, by linarith⟩
  let W := Icc (1 + ε) 2
  have W_compact : IsCompact {ofReal z | z ∈ W} :=
    IsCompact.image isCompact_Icc continuous_ofReal
  have cont : ContinuousOn ζ {ofReal z | z ∈ W} := by
    apply HasDerivAt.continuousOn (f' := ζ')
    intro σ hσ
    exact (differentiableAt_riemannZeta (by contrapose! hσ; simp [W, hσ, εpos])).hasDerivAt
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn W_compact cont
  let C' := max (C + 1) 1
  replace hC : ∀ (σ : ℝ), σ ∈ W → ‖ζ σ‖ < C' := by
    intro σ hσ
    simp only [lt_max_iff, C']
    have := hC σ
    simp only [mem_setOf_eq, ofReal_inj, exists_eq_right] at this
    exact Or.inl <| lt_of_le_of_lt (this hσ) (by norm_num)
  have Cpos : 0 < C' := by simp [C']
  use max (2 * C') c, (by simp [Cpos])
  intro σ ⟨σ_ge, σ_le⟩
  by_cases hσ : σ ∈ U ∩ V
  · simp only [← h, mem_setOf_eq] at hσ
    apply le_trans hσ ?_
    norm_cast
    have : 0 ≤ 1 / (σ - 1) := by apply one_div_nonneg.mpr; linarith
    simp only [Real.norm_eq_abs, abs_eq_self.mpr this, mul_div, mul_one]
    exact div_le_div₀ (by simp [Cpos.le]) (by simp) (by linarith) (by rfl)
  · replace hσ : σ ∈ W := by
      simp only [mem_inter_iff, hV σ_ge, and_true] at hσ
      simp only [mem_Icc, σ_le, and_true, W]
      contrapose! hσ; exact hε ⟨σ_ge.le, hσ⟩
    apply le_trans (hC σ hσ).le ((le_div_iff₀ (by linarith)).mpr ?_)
    rw [le_max_iff, mul_comm 2]; exact Or.inl <| mul_le_mul_of_nonneg_left (by linarith) Cpos.le
/-%%
\begin{proof}\uses{ZetaNear1BndFilter}\leanok
Split into two cases, use Lemma \ref{ZetaNear1BndFilter} for $\sigma$ sufficiently small
and continuity on a compact interval otherwise.
\end{proof}
%%-/

/-- For positive `x` and nonzero `y` we have that
$|\zeta(x)^3 \cdot \zeta(x+iy)^4 \cdot \zeta(x+2iy)| \ge 1$. -/
lemma norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖ζ (1 + x) ^ 3 * ζ (1 + x + I * y) ^ 4 * ζ (1 + x + 2 * I * y)‖ ≥ 1 := by
  have h₀ : 1 < ( 1 + x : ℂ).re := by simp[hx]
  have h₁ : 1 < (1 + x + I * y).re := by simp [hx]
  have h₂ : 1 < (1 + x + 2 * I * y).re := by simp [hx]
  simpa only [one_pow, norm_mul, norm_pow, DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta, h₀, h₁, h₂] using
    DirichletCharacter.norm_LSeries_product_ge_one (1 : DirichletCharacter ℂ 1) hx y


theorem ZetaLowerBound1_aux1 {σ t : ℝ} (this : 1 ≤ ‖ζ σ‖ ^ (3 : ℝ) * ‖ζ (σ + I * t)‖ ^ (4 : ℝ) * ‖ζ (σ + 2 * I * t)‖) :
  ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1 := by
  use (one_le_pow_iff_of_nonneg (by bound) four_ne_zero).1 (by_contra (this.not_lt ∘ ?_))
  norm_num[← Real.rpow_natCast, ← Real.rpow_mul, mul_right_comm, mul_comm (t : ℂ), mul_pow]

lemma ZetaLowerBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1 := by
  -- Start with the fundamental identity
  have := norm_zeta_product_ge_one (x := σ - 1) (by linarith) t
  simp_rw [ge_iff_le, norm_mul, norm_pow, ofReal_sub, ofReal_one, add_sub_cancel, ← Real.rpow_natCast]
    at this
  apply ZetaLowerBound1_aux1 this

lemma ZetaLowerBound2 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / (‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4)) ≤ ‖ζ (σ + t * I)‖ := by
  have := ZetaLowerBound1 (t := t) σ_gt
  exact (div_le_iff₀' (pos_of_mul_pos_left (one_pos.trans_le this) (norm_nonneg _) ) ).mpr this

theorem ZetaLowerBound3_aux1 (A : ℝ) (ha : A ∈ Ioc 0 (1 / 2)) (t : ℝ)
  (ht_2 : 3 < |2 * t|) : 0 < A / Real.log |2 * t| := by
  norm_num only [div_pos _, Real.log_pos _, ht_2.trans', ha.left]

theorem ZetaLowerBound3_aux2 {C : ℝ}
  {σ t : ℝ}
  (ζ_2t_bound : ‖ζ (σ + (2 * t) * I)‖ ≤ C * Real.log |2 * t|) :
  ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤ (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
  bound

theorem ZetaLowerBound3_aux3 {A : ℝ} (_ : 0 < A) {C : ℝ} (_ : 0 < C)
  {c_near : ℝ} (_ : 0 < c_near) (σ : ℝ) (t : ℝ) (_ : 3 < |t|) (σ_gt : 1 < σ)
  :
  c_near ^ ((3 : ℝ) / 4) * ((-1 + σ) ^ ((3 : ℝ) / 4))⁻¹ * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) =
    c_near ^ ((3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) * (-1 + σ) ^ (-(3 : ℝ) / 4) := by
  exact (symm) (.trans (by rw [neg_div, Real.rpow_neg (by linarith)]) (by ring))

theorem ZetaLowerBound3_aux4 (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (hC : 0 < C)
  (c_near : ℝ) (hc_near : 0 < c_near) {σ : ℝ} (t : ℝ) (ht : 3 < |t|)
  (σ_gt : 1 < σ)
   :
  0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |2 * t| ^ ((1 : ℝ) / 4) := by
  match sub_pos.mpr σ_gt with | S => match Real.log_pos (by norm_num [abs_mul, ht.trans', one_lt_mul_of_lt_of_le _, le_of_lt] : abs (2 *t) > 1) with | S => positivity

theorem ZetaLowerBound3_aux5
  {σ : ℝ} (t : ℝ)
  (this : ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1) :
  0 < ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  field_simp only [pos_of_mul_pos_left ∘ this.trans_lt']

lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖ζ (σ + t * I)‖ := by
  obtain ⟨A, ha, C, hC, h_upper⟩ := ZetaUpperBnd
  obtain ⟨c_near, hc_near, h_near⟩ := ZetaNear1BndExact

  use 1 / (c_near ^ ((3 : ℝ) / 4) * (2 * C) ^ ((1 : ℝ) / 4)), by positivity
  intro σ hσ t ht
  obtain ⟨σ_gt, σ_le⟩ := hσ

  -- Use ZetaLowerBound2
  have lower := ZetaLowerBound2 (t := t) σ_gt
  apply le_trans _ lower

  -- Now we need to bound the denominator from above
  -- This will give us a lower bound on the whole expression

  -- Upper bound on ‖ζ σ‖ from ZetaNear1BndExact
  have ζ_σ_bound : ‖ζ σ‖ ≤ c_near / (σ - 1) := by
    exact h_near σ ⟨σ_gt, σ_le⟩

  have ht_2 : 3 < |2 * t| := by simp only [abs_mul, Nat.abs_ofNat]; linarith

  -- Upper bound on ‖ζ (σ + 2*t * I)‖ from ZetaUpperBnd

  have σ_in_range : σ ∈ Icc (1 - A / Real.log |2 * t|) 2 := by
    constructor
    · -- σ ≥ 1 - A / Real.log |2*t|
      have : 0 < A / Real.log |2 * t| := by
        exact ZetaLowerBound3_aux1 A ha t ht_2
      nlinarith
    · exact σ_le

  have ζ_2t_bound := h_upper σ (2 * t) ht_2 σ_in_range

  -- Combine the bounds
  have denom_bound : ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤
      (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply mul_le_mul
    · apply Real.rpow_le_rpow (norm_nonneg _) ζ_σ_bound (by norm_num)
    · apply ZetaLowerBound3_aux2
      convert ζ_2t_bound
      norm_cast
    · apply Real.rpow_nonneg (norm_nonneg _)
    · apply Real.rpow_nonneg (div_nonneg (by linarith) (by linarith))

  -- Simplify the bound
  have : (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) =
         c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    rw [Real.div_rpow (by linarith) (by linarith), Real.mul_rpow (by linarith) (Real.log_nonneg (by linarith))]
    ring_nf
    apply ZetaLowerBound3_aux3 ha.1 hC hc_near
    · convert ht
    · exact σ_gt

  rw [this] at denom_bound

  -- Take reciprocal (flipping inequality)
  have pos_left : 0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply ZetaLowerBound3_aux4 A ha C hC c_near hc_near t ht σ_gt

  have pos_right : 0 < ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
    -- This follows from ZetaLowerBound1 - if either factor were zero, we'd get 0 ≥ 1
    have := ZetaLowerBound1 (t := t) σ_gt
    apply ZetaLowerBound3_aux5
    convert this

  use (div_le_div_of_nonneg_left zero_le_one pos_right denom_bound).trans' ?_
  simp_rw [abs_mul, abs_two, neg_div, Real.rpow_neg (sub_pos.2 σ_gt).le] at *
  field_simp only [*, sub_pos, mul_assoc, mul_left_comm, mul_le_mul_left, one_mul,Real.log_mul,
    Real.log_pos, ht.trans', show Real.log 2 + .log |t| ≤ .log 2 * .log |t| from (? _),div_le_div_iff_of_pos_left, Real.mul_rpow, Real.log_le_self]
  use Real.mul_rpow two_pos.le (Real.log_nonneg (ht.trans' (by norm_num)).le) ▸ by
    bound [Real.log_lt_log two_pos (ht.trans' (by norm_num)), Real.log_pos one_lt_two]



/-%%
\begin{lemma}[ZetaInvBound1]\label{ZetaInvBound1}\lean{ZetaInvBound1}\leanok
For all $\sigma>1$,
$$
1/|\zeta(\sigma+it)| \le |\zeta(\sigma)|^{3/4}|\zeta(\sigma+2it)|^{1/4}
$$
\end{lemma}
%%-/
lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / ‖ζ (σ + t * I)‖ ≤ ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  apply (div_le_iff₀ ?_).mpr
  apply (Real.rpow_le_rpow_iff (z := 4) (by norm_num) ?_ (by norm_num)).mp
  · simp only [Real.one_rpow]
    rw [Real.mul_rpow, Real.mul_rpow, ← Real.rpow_mul, ← Real.rpow_mul]
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.div_mul_cancel, IsUnit.inv_mul_cancel, Real.rpow_one]
    conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm]
    rw [← mul_assoc]
    have := norm_zeta_product_ge_one (x := σ - 1) (by linarith) t
    simp_rw [ge_iff_le, norm_mul, norm_pow, ofReal_sub, ofReal_one, add_sub_cancel, ← Real.rpow_natCast] at this
    convert this using 3 <;> ring_nf
    any_goals ring_nf
    any_goals apply norm_nonneg
    any_goals apply Real.rpow_nonneg <| norm_nonneg _
    apply mul_nonneg <;> apply Real.rpow_nonneg <| norm_nonneg _
  · refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> simp [Real.rpow_nonneg]
  · have s_ne_one : σ + t * I ≠ 1 := by
      contrapose! σ_gt; apply le_of_eq; apply And.left; simpa [Complex.ext_iff] using σ_gt
    simpa using riemannZeta_ne_zero_of_one_le_re (by simp [σ_gt.le])
/-%%
\begin{proof}\leanok
The identity
$$
1 \le |\zeta(\sigma)|^3 |\zeta(\sigma+it)|^4 |\zeta(\sigma+2it)|
$$
for $\sigma>1$
is already proved by Michael Stoll in the EulerProducts PNT file.
\end{proof}
%%-/

lemma Ioi_union_Iio_mem_cocompact {a : ℝ} (ha : 0 ≤ a) : Ioi (a : ℝ) ∪ Iio (-a : ℝ) ∈ cocompact ℝ := by
  simp only [Filter.mem_cocompact]
  use Icc (-a) a
  constructor
  · exact isCompact_Icc
  · rw [@compl_subset_iff_union, ← union_assoc, Icc_union_Ioi_eq_Ici, union_comm, Iio_union_Ici]
    linarith

lemma lt_abs_mem_cocompact {a : ℝ} (ha : 0 ≤ a) : {t | a < |t|} ∈ cocompact ℝ := by
  convert Ioi_union_Iio_mem_cocompact ha using 1; ext t
  simp only [mem_setOf_eq, mem_union, mem_Ioi, mem_Iio, lt_abs, lt_neg]

/-%%
\begin{lemma}[ZetaInvBound2]\label{ZetaInvBound2}\lean{ZetaInvBound2}\leanok
For $\sigma>1$ (and $\sigma \le 2$),
$$
1/|\zeta(\sigma+it)| \ll (\sigma-1)^{-3/4}(\log |t|)^{1/4},
$$
as $|t|\to\infty$.
\end{lemma}
%%-/
lemma ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  obtain ⟨A, ha, C, hC, h⟩ := ZetaUpperBnd
  obtain ⟨c, hc, h_inv⟩ := ZetaNear1BndExact
  refine ⟨(2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4), by positivity, ?_⟩
  intro σ hσ t t_gt
  obtain ⟨σ_gt, σ_le⟩ := hσ
  have ht' : 3 < |2 * t| := by simp only [abs_mul, Nat.abs_ofNat]; linarith
  have hnezero: ((σ - 1) / c) ^ (-3 / 4 : ℝ) ≠ 0 := by
    have : (σ - 1) / c ≠ 0 := ne_of_gt <| div_pos (by linarith) hc
    contrapose! this
    rwa [Real.rpow_eq_zero (div_nonneg (by linarith) hc.le) (by norm_num)] at this
  calc
    _ ≤ ‖‖ζ σ‖ ^ (3 / 4 : ℝ) * ‖ζ (↑σ + 2 * ↑t * I)‖ ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * ‖ζ (↑σ + 2 * ↑t * I)‖ ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * C ^ (1 / 4 : ℝ) * (Real.log |2 * t|) ^ (1 / 4 : ℝ)‖ := ?_
    _ ≤ ‖((σ - 1) / c) ^ (-3 / 4 : ℝ) * C ^ (1 / 4 : ℝ) * (Real.log (|t| ^ 2)) ^ (1 / 4 : ℝ)‖ := ?_
    _ = ‖((σ - 1)) ^ (-3 / 4 : ℝ) * c ^ (3 / 4 : ℝ) * (C ^ (1 / 4 : ℝ) * (Real.log (|t| ^ 2)) ^ (1 / 4 : ℝ))‖ := ?_
    _ = ‖((σ - 1)) ^ (-3 / 4 : ℝ) * c ^ (3 / 4 : ℝ) * ((2 * C) ^ (1 / 4 : ℝ) * Real.log |t| ^ (1 / 4 : ℝ))‖ := ?_
    _ = _ := ?_
  · simp only [norm_div, norm_one, norm_mul, norm_norm]
    convert ZetaInvBound1 σ_gt using 2
    <;> exact abs_eq_self.mpr <| Real.rpow_nonneg (norm_nonneg _) _
  · have bnd1: ‖ζ σ‖ ^ (3 / 4 : ℝ) ≤ ((σ - 1) / c) ^ (-(3 : ℝ) / 4) := by
      have : ((σ - 1) / c) ^ (-(3 : ℝ) / 4) = (((σ - 1) / c) ^ (-1 : ℝ)) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_mul ?_]; ring_nf; exact div_nonneg (by linarith) hc.le
      rw [this]
      apply Real.rpow_le_rpow (by simp [norm_nonneg]) ?_ (by norm_num)
      convert h_inv σ ⟨σ_gt, σ_le⟩ using 1; simp [Real.rpow_neg_one, inv_div]
    simp only [norm_div, norm_one, norm_mul]
    apply (mul_le_mul_right ?_).mpr
    convert bnd1 using 1
    · exact abs_eq_self.mpr <| Real.rpow_nonneg (norm_nonneg _) _
    · exact abs_eq_self.mpr <| Real.rpow_nonneg (div_nonneg (by linarith) hc.le) _
    · apply lt_iff_le_and_ne.mpr ⟨(by simp), ?_⟩
      have : ζ (↑σ + 2 * ↑t * I) ≠ 0 := by
        apply riemannZeta_ne_zero_of_one_le_re (by simp [σ_gt.le])
      symm; exact fun h2 ↦ this (by simpa using h2)
  · replace h := h σ (2 * t) (by simp [ht']) ⟨?_, σ_le⟩
    · have : 0 ≤ Real.log |2 * t| := Real.log_nonneg (by linarith)
      conv => rhs; rw [mul_assoc, ← Real.mul_rpow hC.le this]
      rw [norm_mul, norm_mul]
      conv => rhs; rhs; rw [Real.norm_rpow_of_nonneg <| mul_nonneg hC.le this]
      conv => lhs; rhs; rw [Real.norm_rpow_of_nonneg <| norm_nonneg _]
      apply (mul_le_mul_left ?_).mpr
      apply Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
      · convert h using 1; simp
        rw [Real.norm_eq_abs, abs_eq_self.mpr <| mul_nonneg hC.le this]
      · simpa only [Real.norm_eq_abs, abs_pos]
    · linarith [(div_nonneg ha.1.le (Real.log_nonneg (by linarith)) : 0 ≤ A / Real.log |2 * t|)]
  · simp only [Real.log_abs, norm_mul]
    apply (mul_le_mul_left ?_).mpr
    · rw [← Real.log_abs, Real.norm_rpow_of_nonneg <| Real.log_nonneg (by linarith)]
      have : 1 ≤ |(|t| ^ 2)| := by
        simp only [_root_.sq_abs, _root_.abs_pow, one_le_sq_iff_one_le_abs]
        linarith
      conv => rhs; rw [← Real.log_abs, Real.norm_rpow_of_nonneg <| Real.log_nonneg this]
      apply Real.rpow_le_rpow (abs_nonneg _) ?_ (by norm_num)
      · rw [Real.norm_eq_abs, abs_eq_self.mpr <| Real.log_nonneg (by linarith)]
        rw [abs_eq_self.mpr <| Real.log_nonneg this, abs_mul, Real.log_abs, Nat.abs_ofNat]
        apply Real.log_le_log (mul_pos (by norm_num) (by linarith)) (by nlinarith)
    . apply mul_pos (abs_pos.mpr hnezero) (abs_pos.mpr ?_)
      have : C ≠ 0 := ne_of_gt hC
      contrapose! this; rwa [Real.rpow_eq_zero (by linarith) (by norm_num)] at this
  · have : (-3 : ℝ) / 4 = -((3 : ℝ)/ 4) := by norm_num
    simp only [norm_mul, mul_eq_mul_right_iff, abs_eq_zero, this, ← mul_assoc]; left; left
    conv => lhs; rw [Real.div_rpow (by linarith) hc.le, Real.rpow_neg hc.le, div_inv_eq_mul, norm_mul]
  · simp only [Real.log_pow, Nat.cast_ofNat, norm_mul, Real.norm_eq_abs]
    congr! 1
    rw [Real.mul_rpow (by norm_num) hC.le, Real.mul_rpow (by norm_num) <|
        Real.log_nonneg (by linarith), abs_mul, abs_mul, ← mul_assoc, mul_comm _ |2 ^ (1 / 4)|]
  · simp only [norm_mul, Real.norm_eq_abs]
    have : (2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4) =
      |(2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4)| := by
      rw [abs_eq_self.mpr (by apply mul_nonneg <;> (apply Real.rpow_nonneg; linarith))]
    rw [this, abs_mul, abs_eq_self.mpr (by apply Real.rpow_nonneg; linarith), abs_eq_self.mpr (by positivity),
      abs_eq_self.mpr (by positivity), abs_eq_self.mpr (by apply Real.rpow_nonneg (Real.log_nonneg (by linarith)))]
    ring_nf
/-%%
\begin{proof}\uses{ZetaInvBound1, ZetaNear1BndExact, ZetaUpperBnd}\leanok
Combine Lemma \ref{ZetaInvBound1} with the bounds in Lemmata \ref{ZetaNear1BndExact} and
\ref{ZetaUpperBnd}.
\end{proof}
%%-/

lemma deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by
  ext σ
  have := deriv_comp (h := fun (σ : ℝ) ↦ σ + t * I) (h₂ := f) σ (diff σ) ?_
  · simp only [deriv_add_const', _root_.deriv_ofReal, mul_one] at this
    rw [← this]
    rfl
  · apply DifferentiableAt.add_const _ <| differentiableAt_ofReal σ

/-%%
\begin{lemma}[Zeta_eq_int_derivZeta]\label{Zeta_eq_int_derivZeta}\lean{Zeta_eq_int_derivZeta}
\leanok
For any $t\ne0$ (so we don't pass through the pole), and $\sigma_1 < \sigma_2$,
$$
\int_{\sigma_1}^{\sigma_2}\zeta'(\sigma + it) dt =
\zeta(\sigma_2+it) - \zeta(\sigma_1+it).
$$
\end{lemma}
%%-/
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, ζ' (σ + t * I)) = ζ (σ₂ + t * I) - ζ (σ₁ + t * I) := by
  have diff : ∀ (σ : ℝ), DifferentiableAt ℂ ζ (σ + t * I) := by
    intro σ
    refine differentiableAt_riemannZeta ?_
    contrapose! t_ne_zero; apply And.right; simpa [Complex.ext_iff] using t_ne_zero
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro s _
    apply DifferentiableAt.comp
    · exact (diff s).restrictScalars ℝ
    · exact DifferentiableAt.add_const (c := t * I) <| differentiableAt_ofReal _
  · apply ContinuousOn.comp (g := ζ') ?_ ?_ (mapsTo_image _ _)
    · apply HasDerivAt.continuousOn (f' := deriv <| ζ')
      intro x hx
      apply hasDerivAt_deriv_iff.mpr
      replace hx : x ≠ 1 := by
        contrapose! hx
        simp only [hx, mem_image, Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im, not_exists,
          not_and]
        exact fun _ _ _ ↦ t_ne_zero
      have := (Complex.analyticAt_iff_eventually_differentiableAt (c := x) (f := ζ)).mpr ?_
      · obtain ⟨r, hr, h⟩ := this.exists_ball_analyticOnNhd
        apply (h.deriv x ?_).differentiableAt
        simp [hr]
      · filter_upwards [compl_singleton_mem_nhds hx] with z hz
        apply differentiableAt_riemannZeta
        simpa [mem_compl_iff, mem_singleton_iff] using hz
    · exact continuous_ofReal.continuousOn.add continuousOn_const
/-%%
\begin{proof}\leanok
This is the fundamental theorem of calculus.
\end{proof}
%%-/

/-%%
\begin{lemma}[Zeta_diff_Bnd]\label{Zeta_diff_Bnd}\lean{Zeta_diff_Bnd}\leanok
For any $A>0$ sufficiently small, there is a constant $C>0$ so that
whenever $1- A / \log t \le \sigma_1 < \sigma_2\le 2$ and $3 < |t|$, we have that:
$$
|\zeta (\sigma_2 + it) - \zeta (\sigma_1 + it)|
\le C (\log |t|)^2 (\sigma_2 - \sigma_1).
$$
\end{lemma}
%%-/
lemma Zeta_diff_Bnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : 1 - A / Real.log |t| ≤ σ₁) (_ : σ₂ ≤ 2) (_ : σ₁ < σ₂),
    ‖ζ (σ₂ + t * I) - ζ (σ₁ + t * I)‖ ≤  C * Real.log |t| ^ 2 * (σ₂ - σ₁) := by
  obtain ⟨A, hA, C, Cpos, hC⟩ := ZetaDerivUpperBnd
  refine ⟨A, hA, C, Cpos, ?_⟩
  intro σ₁ σ₂ t t_gt σ₁_ge σ₂_le σ₁_lt_σ₂
  have t_ne_zero : t ≠ 0 := by contrapose! t_gt; simp only [t_gt, abs_zero, Nat.ofNat_nonneg]
  rw [← Zeta_eq_int_derivZeta t_ne_zero]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr; rw [_root_.abs_of_nonneg (by linarith)]
  · intro σ hσ; rw [uIoc_of_le σ₁_lt_σ₂.le, mem_Ioc] at hσ
    exact hC σ t t_gt ⟨le_trans σ₁_ge hσ.1.le, le_trans hσ.2 σ₂_le⟩
/-%%
\begin{proof}
\uses{Zeta_eq_int_derivZeta, ZetaDerivUpperBnd}\leanok
Use Lemma \ref{Zeta_eq_int_derivZeta} and
estimate trivially using Lemma \ref{ZetaDerivUpperBnd}.
\end{proof}
%%-/

lemma ZetaInvBnd_aux' {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| < Real.log |t| ^ 9 := by
  nth_rewrite 1 [← Real.rpow_one <| Real.log |t|]
  exact mod_cast Real.rpow_lt_rpow_left_iff (y := 1) (z := 9) logt_gt_one |>.mpr (by norm_num)

lemma ZetaInvBnd_aux {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| ≤ Real.log |t| ^ 9 :=
    ZetaInvBnd_aux' logt_gt_one |>.le

lemma ZetaInvBnd_aux2 {A C₁ C₂ : ℝ} (Apos : 0 < A) (C₁pos : 0 < C₁) (C₂pos : 0 < C₂)
    (hA : A ≤ 1 / 2 * (C₁ / (C₂ * 2)) ^ (4 : ℝ)) :
    0 < (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹ := by
  simp only [inv_pos, sub_pos]
  apply div_lt_iff₀ (by positivity) |>.mp
  rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity), mul_assoc]
  apply lt_div_iff₀' (by positivity) |>.mp
  nth_rewrite 1 [← Real.rpow_one A]
  rw [← Real.rpow_add (by positivity)]
  norm_num
  apply Real.rpow_lt_rpow_iff (z := 4) (by positivity) (by positivity) (by positivity) |>.mp
  rw [← Real.rpow_mul (by positivity)]
  norm_num
  apply lt_of_le_of_lt hA
  rw [div_mul_comm, mul_one]
  apply half_lt_self
  positivity

/-%%
\begin{lemma}[ZetaInvBnd]\label{ZetaInvBnd}\lean{ZetaInvBnd}\leanok
For any $A>0$ sufficiently small, there is a constant $C>0$ so that
whenever $1- A / \log^9 |t| \le \sigma < 1$ and $3 < |t|$, we have that:
$$
1/|\zeta(\sigma+it)| \le C \log^7 |t|.
$$
\end{lemma}
%%-/
lemma ZetaInvBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ (7 : ℝ) := by
  obtain ⟨C', C'pos, hC₁⟩ := ZetaInvBound2
  obtain ⟨A', hA', C₂, C₂pos, hC₂⟩ := Zeta_diff_Bnd
  set C₁ := 1 / C'
  let A := min A' <| (1 / 2 : ℝ) * (C₁ / (C₂ * 2)) ^ (4 : ℝ)
  have Apos : 0 < A := by have := hA'.1; positivity
  have Ale : A ≤ 1 / 2 := by dsimp only [A]; apply min_le_iff.mpr; left; exact hA'.2
  set C := (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹
  have Cpos : 0 < C := by
    refine ZetaInvBnd_aux2 (by positivity) (by positivity) (by positivity) ?_
    apply min_le_iff.mpr; right; exact le_rfl
  refine ⟨A, ⟨Apos, by linarith [hA'.2]⟩ , C, Cpos, ?_⟩
  intro σ t t_gt hσ
  have logt_gt_one := logt_gt_one t_gt
  have σ_ge : 1 - A / Real.log |t| ≤ σ := by
    apply le_trans ?_ hσ.1
    suffices A / Real.log |t| ^ 9 ≤ A / Real.log |t| by linarith
    exact div_le_div₀ Apos.le (by rfl) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  obtain ⟨_, _, neOne⟩ := UpperBnd_aux ⟨Apos, Ale⟩ t_gt σ_ge
  set σ' := 1 + A / Real.log |t| ^ 9
  have σ'_gt : 1 < σ' := by simp only [σ', lt_add_iff_pos_right]; positivity
  have σ'_le : σ' ≤ 2 := by
    simp only [σ']
    suffices A / Real.log |t| ^ 9 < 1 by linarith
    apply div_lt_one (by positivity) |>.mpr
    exact lt_trans₄ (by linarith) logt_gt_one <| ZetaInvBnd_aux' logt_gt_one
  set s := σ + t * I
  set s' := σ' + t * I
  by_cases h0 : ‖ζ s‖ ≠ 0
  swap; simp only [ne_eq, not_not] at h0; simp only [h0, div_zero]; positivity
  apply div_le_iff₀ (by positivity) |>.mpr <| div_le_iff₀' (by positivity) |>.mp ?_
  have pos_aux : 0 < (σ' - 1) := by linarith
  calc
    _ ≥ ‖ζ s'‖ - ‖ζ s - ζ s'‖ := ?_
    _ ≥ C₁ * (σ' - 1) ^ ((3 : ℝ)/ 4) * Real.log |t|  ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ 2 * (σ' - σ) := ?_
    _ ≥ C₁ * (A / Real.log |t| ^ (9 : ℝ)) ^ ((3 : ℝ)/ 4) * Real.log |t| ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ (2 : ℝ) * 2 * A / Real.log |t| ^ (9 : ℝ) := ?_
    _ ≥ C₁ * A ^ ((3 : ℝ)/ 4) * Real.log |t| ^ (-7 : ℝ) - C₂ * 2 * A * Real.log |t| ^ (-7 : ℝ) := ?_
    _ = (C₁ * A ^ ((3 : ℝ)/ 4) - C₂ * 2 * A) * Real.log |t| ^ (-7 : ℝ) := by ring
    _ ≥ _ := ?_
  · apply ge_iff_le.mpr
    convert norm_sub_norm_le (a := ζ s') (b := ζ s' - ζ s) using 1
    · rw [(by simp : ζ s' - ζ s = -(ζ s - ζ s'))]; simp only [norm_neg, sub_right_inj]
    · simp
  · apply sub_le_sub
    · have := one_div_le ?_ (by positivity) |>.mp <| hC₁ ⟨σ'_gt, σ'_le⟩ t t_gt
      · convert this using 1
        rw [one_div, mul_inv_rev, mul_comm, mul_inv_rev, mul_comm _ C'⁻¹]
        simp only [one_div C', C₁]
        congr <;> (rw [← Real.rpow_neg (by linarith), neg_div]); rw [neg_neg]
      · apply norm_pos_iff.mpr <| riemannZeta_ne_zero_of_one_lt_re (by simp [σ'_gt])
    · rw [(by simp : ζ s - ζ s' = -(ζ s' - ζ s)), norm_neg]
      refine hC₂ σ σ' t t_gt ?_ σ'_le <| lt_trans hσ.2 σ'_gt
      apply le_trans ?_ hσ.1
      rw [tsub_le_iff_right, ← add_sub_right_comm, le_sub_iff_add_le, add_le_add_iff_left]
      exact div_le_div₀ hA'.1.le (by simp [A]) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  · apply sub_le_sub (by simp only [add_sub_cancel_left, σ']; exact_mod_cast le_rfl) ?_
    rw [mul_div_assoc, mul_assoc _ 2 _]
    apply mul_le_mul (by exact_mod_cast le_rfl) ?_ (by linarith [hσ.2]) (by positivity)
    suffices h : σ' + (1 - A / Real.log |t| ^ 9) ≤ (1 + A / Real.log |t| ^ 9) + σ by
      simp only [tsub_le_iff_right]
      convert le_sub_right_of_add_le h using 1; ring_nf; norm_cast; simp
    exact add_le_add (by linarith) (by linarith [hσ.1])
  · simp_rw [tsub_le_iff_right, div_eq_mul_inv _ (Real.log |t| ^ (9 : ℝ))]
    rw [← Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
    conv => rhs; lhs; rw [mul_assoc, ← Real.rpow_add (by positivity)]
    conv => rhs; rhs; rhs; rw [mul_comm _ A]; lhs; rw [mul_assoc, mul_assoc C₂]
    rw [← Real.rpow_add (by positivity)]; norm_num; group; exact le_rfl
  · apply div_le_iff₀ (by positivity) |>.mpr
    conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm C, ← mul_assoc, ← Real.rpow_add (by positivity)]
    have := inv_inv C ▸ mul_inv_cancel₀ (a := C⁻¹) (by positivity) |>.symm.le
    simpa [C] using this
/-%%
\begin{proof}\leanok
\uses{Zeta_diff_Bnd, ZetaInvBound2}
Let $\sigma$ be given in the prescribed range, and set $\sigma' := 1+ A / \log^9 |t|$.
Then
$$
|\zeta(\sigma+it)| \ge
|\zeta(\sigma'+it)| - |\zeta(\sigma+it) - \zeta(\sigma'+it)|
\ge
C (\sigma'-1)^{3/4}\log |t|^{-1/4} - C \log^2 |t| (\sigma'-\sigma)
$$
$$
\ge
C A^{3/4} \log |t|^{-7} - C \log^2 |t| (2 A / \log^9 |t|),
$$
where we used Lemma \ref{ZetaInvBound2}  and Lemma \ref{Zeta_diff_Bnd}.
Now by making $A$ sufficiently small (in particular, something like $A = 1/16$ should work), we can guarantee that
$$
|\zeta(\sigma+it)| \ge \frac C 2 (\log |t|)^{-7},
$$
as desired.
\end{proof}
%%-/

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

/-%%
Annoyingly, it is not immediate from this that $\zeta$ doesn't vanish there! That's because
$1/0 = 0$ in Lean. So we give a second proof of the same fact (refactor this later), with a lower
 bound on $\zeta$ instead of upper bound on $1 / \zeta$.
\begin{lemma}[ZetaLowerBnd]\label{ZetaLowerBnd}\lean{ZetaLowerBnd}\leanok
For any $A>0$ sufficiently small, there is a constant $C>0$ so that
whenever $1- A / \log^9 |t| \le \sigma < 1$ and $3 < |t|$, we have that:
$$
|\zeta(\sigma+it)| \ge C \log^7 |t|.
$$
\end{lemma}
%%-/
lemma ZetaLowerBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖ζ (σ + t * I)‖ := by
  obtain ⟨C₁, C₁pos, hC₁⟩ := ZetaLowerBound3
  obtain ⟨A', hA', C₂, C₂pos, hC₂⟩ := Zeta_diff_Bnd

  -- Pick the right constants.
  -- Don't really like this because I can only do that after first finishing the proof.
  -- Is there a way to delay picking those
  let A := min A' ((C₁ / (4 * C₂)) ^ 4)
  have hA : A ∈ Ioc 0 (1 / 2) :=
    ⟨lt_min hA'.1 (by positivity), (min_le_left A' _).trans hA'.2⟩

  let C := C₁ * A ^ ((3:ℝ) /4) - 2 * C₂ * A
  have hc_pos : 0 < C := by
    have:= A.rpow_le_rpow hA.1.le (min_le_right _ _) (inv_pos.mpr four_pos).le
    erw [Real.pow_rpow_inv_natCast (div_pos C₁pos (mul_pos four_pos C₂pos)).le four_ne_zero, le_div_iff₀ (mul_pos four_pos C₂pos)] at this
    norm_num[mul_assoc,C,mul_left_comm,C₂pos,hA.1,(mul_le_mul_of_nonneg_right this (A.rpow_nonneg hA.1.le _)).trans_lt',←A.rpow_add]

  refine ⟨A, hA, C, hc_pos, fun σ t L ⟨σ_low_bound, σ_le_one⟩=>?_⟩

  -- From here I followed the proof found in the blueprint
  let σ' := 1 + A / Real.log |t| ^  (9 : ℝ)

  have triangular :  ‖ζ (σ + t * I)‖ ≥  ‖ζ (σ' + t * I)‖ -  ‖ζ (σ + t * I) - ζ (σ' + t * I)‖ := by
    apply sub_le_iff_le_add.mpr.comp (sub_sub_self @_ (@_ : ℂ)▸norm_sub_le _ _).trans (by rw [add_comm])

  have one_leLogT : 1 ≤ Real.log |t| := by
    refine (Real.le_log_iff_exp_le ?_).mpr ?_
    · linarith
    · have : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      linarith

  have σ'_ge : 1 ≤ σ' := by
    bound
    · exact hA'.1.le
    · norm_num
    · linarith

  have right_sub :  -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖ ≥ - C₂ * Real.log |t| ^ 2 * (σ' - σ) := by
    show - C₂ * Real.log |t| ^ 2 * (σ' - σ) ≤ -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖
    have := hC₂ σ σ' t L ?_ ?_ ?_
    convert neg_le_neg this using 1
    · ring
    · congr! 1
      have : ζ (↑σ + ↑t * I) - ζ (↑σ' + ↑t * I) = - (ζ (↑σ' + ↑t * I) - ζ (↑σ + ↑t * I)) := by ring
      rw [this, norm_neg]
    · have : 1 - A' / Real.log |t| ≤ 1 - A / (Real.log |t|) ^ 9 := by
        gcongr
        · exact hA'.1.le
        · bound
        · bound
      linarith
    · have : σ' ≤ 1 + A := by
        bound
        · exact hA'.1.le
        · norm_num
        · have : 1 ≤ Real.log |t| ^ 9 := by
            bound
          exact_mod_cast this
      bound [hA.2]
    · linarith
    -- use (le_neg.1 ((norm_sub_rev _ _).trans_le ((hC₂ _ _ (add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans (?_)))) (σ_le_one.trans (?_)) t L ?_).trans_eq (by ring))))
    -- · norm_num only[Real.le_log_iff_exp_le, L.trans',(one_le_pow₀ _).trans',one_mul,Real.exp_one_lt_d9.le.trans]
    --   exact (mod_cast one_half_lt_one.le.trans (one_le_pow₀ ((Real.le_log_iff_exp_le (three_pos.trans L)).2 (by linear_combination L +.exp_one_lt_d9))))
    -- · exact_mod_cast by ·linear_combination σ_low_bound.trans_lt σ_le_one
    -- · exact (.trans (by bound[Real.log_le_log three_pos L.le, hA'.1,Real.lt_log_one_add_of_pos two_pos]) σ_low_bound)

  have right' : -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖   ≥ - C₂ * 2 * A / Real.log |t| ^ 7 := by
    have := (abs t).log_pos (by bound)
    refine right_sub.trans' ((div_le_iff₀ (pow_pos this 7)).2 @?_|>.trans (mul_le_mul_of_nonpos_left (sub_le_sub_left σ_low_bound (1+_) ) (by ·linear_combination C₂*this*(.log |t|))))
    exact (mod_cast (by linear_combination (2 *_* A) *div_self ↑(pow_pos this 09).ne'))

  have left_sub : ‖ζ (σ' + t * I)‖ ≥ C₁ * (σ' - 1) ^ ((3:ℝ) /4) / Real.log |t| ^ 4 := by
    use (hC₁ ⟨lt_add_of_pos_right (1) (by bound[hA.1]),add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans (?_)))⟩ t L).trans' ?_
    · norm_num only[one_mul, (one_le_pow₀ ((Real.lt_log_iff_exp_lt _).2 _).le).trans',L.trans',Real.exp_one_lt_d9.trans]
      exact (mod_cast one_half_lt_one.le.trans (le_of_lt (one_lt_pow₀.comp (Real.lt_log_iff_exp_lt (by(((positivity))))).mpr (by(linear_combination L +.exp_one_lt_d9)) (by decide))))
    · bound [hA.1, Real.log_lt_log three_pos L, Real.lt_log_one_add_of_pos two_pos]
      · linear_combination L
      -- · linear_combination L
      · exact (mod_cast (Real.rpow_lt_rpow_of_exponent_lt (by bound) ( show 1/4<4by bound)).le)

  have left' : ‖ζ (σ' + t * I)‖ ≥ C₁ * A ^ ((3:ℝ) /4) / Real.log |t| ^ 7 := by
    contrapose! hC₁
    use σ',⟨lt_add_of_pos_right 1<|by bound[hA'.1],add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans ?_))⟩,t,L,hC₁.trans_le ?_
    · norm_num only[←div_le_iff₀', (one_le_pow₀ ((Real.log_le_log _ L.le).trans' ↑ _)).trans',Real.le_log_iff_exp_le _,Real.exp_one_lt_d9.le.trans]
      exact (mod_cast (one_lt_pow₀ ((Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith[Real.exp_one_lt_d9])) (by decide)).le.trans' (by(((norm_num)))))
    · norm_num only[σ',add_sub_cancel_left, A.div_rpow hA.1.le, mul_div,pow_pos, L.trans',←Real.rpow_natCast,←Real.rpow_mul,le_of_lt,Real.log_pos,refl,div_div,←Real.rpow_sub]
      norm_num only[*, L.trans',mul_assoc, A.div_rpow, mul_div,←Real.rpow_add,←Real.rpow_natCast,←Real.rpow_mul,div_div,Real.log_pos,Real.rpow_pos_of_pos,hA.1,refl,le_of_lt]

  have ineq : ‖ζ (σ + t * I)‖ ≥ (C₁ * A ^ ((3:ℝ) /4) - C₂ * 2 * A) / Real.log |t| ^ 7 := by
    linear_combination left'+triangular+right'

  rw [mul_comm C₂] at ineq
  exact_mod_cast ineq

-- **End collaboration 6/20/25**
/-%%
\begin{proof}\leanok
\uses{ZetaLowerBound3, Zeta_diff_Bnd}
Follow same argument.
\end{proof}
%%-/

/-%%
Now we get a zero free region.
\begin{lemma}[ZetaZeroFree]\label{ZetaZeroFree}\lean{ZetaZeroFree}\leanok
There is an $A>0$ so that for $1-A/\log^9 |t| \le \sigma < 1$ and $3 < |t|$,
$$
\zeta(\sigma+it) \ne 0.
$$
\end{lemma}
%%-/
lemma ZetaZeroFree :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    ζ (σ + t * I) ≠ 0 := by
  obtain ⟨A, hA, c, hc, h_lower⟩ := ZetaLowerBnd

  -- Use the same A for our result
  refine ⟨A, hA, ?_⟩

  -- Now prove that ζ has no zeros in this region
  intro σ t ht hσ

  intro h_zero

  have := h_lower σ t ht hσ

  rw [h_zero] at this

  have one_leLogT : 1 ≤ Real.log |t| := by
    refine (Real.le_log_iff_exp_le ?_).mpr ?_
    · linarith
    · have : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      linarith

  simp only [norm_zero] at this

  have pos_bound : 0 < c / (Real.log |t|) ^ (7 : ℝ) := by
    apply div_pos hc
    apply Real.rpow_pos_of_pos
    apply Real.log_pos
    linarith

  linarith
/-%%
\begin{proof}\leanok
\uses{ZetaLowerBnd}
Apply Lemma \ref{ZetaLowerBnd}.
\end{proof}
%%-/


/-%%
\begin{lemma}[LogDerivZetaBnd]\label{LogDerivZetaBnd}\lean{LogDerivZetaBnd}\leanok
There is an $A>0$ so that for $1-A/\log^9 |t| \le \sigma < 1$ and $3 < |t|$,
$$
|\frac {\zeta'}{\zeta} (\sigma+it)| \ll \log^9 |t|.
$$
\end{lemma}
%%-/
lemma LogDerivZetaBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / Real.log |t| ^ 9) 1), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9 := by
  obtain ⟨A, hA, C, hC, h⟩ := ZetaInvBnd
  obtain ⟨A', hA', C', hC', h'⟩ := ZetaDerivUpperBnd
  use min A A', ⟨lt_min hA.1 hA'.1, min_le_of_right_le hA'.2⟩, C * C', mul_pos hC hC'
  intro σ t t_gt ⟨σ_ge, σ_lt⟩
  have logt_gt : (1 : ℝ) < Real.log |t| := by
    refine (Real.lt_log_iff_exp_lt (by linarith)).mpr (lt_trans ?_ t_gt)
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have σ_ge' : 1 - A / Real.log |t| ^ 9 ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div₀ hA.1.le (min_le_left A A') ?_ (by rfl)
    exact pow_pos (lt_trans (by norm_num) logt_gt) 9
  have σ_ge'' : 1 - A' / Real.log |t| ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div₀ hA'.1.le (min_le_right A A') (lt_trans (by norm_num) logt_gt) ?_
    exact le_self_pow₀ logt_gt.le (by norm_num)
  replace h := h σ t t_gt ⟨σ_ge', σ_lt⟩
  replace h' := h' σ t t_gt ⟨σ_ge'', by linarith⟩
  simp only [norm_div, norm_one, norm_mul, norm_inv]
  convert mul_le_mul h h' (by simp [apply_nonneg]) ?_ using 1 <;> (norm_cast; ring_nf); positivity
/-%%
\begin{proof}\leanok
\uses{ZetaInvBnd, ZetaDerivUpperBnd}
Combine the bound on $|\zeta'|$ from Lemma \ref{ZetaDerivUpperBnd} with the
bound on $1/|\zeta|$ from Lemma \ref{ZetaInvBnd}.
\end{proof}
%%-/

/-%%
\begin{lemma}[LogDerivZetaBndUniform]\label{LogDerivZetaBndUniform}\lean{LogDerivZetaBndUniform}\leanok
There is an $A>0$ so that for $1-A/\log^9 T \le \sigma < 1$ and $3 < |t| ≤ T$,
$$
|\frac {\zeta'}{\zeta} (\sigma+it)| \ll \log^9 T.
$$
\end{lemma}
%%-/
lemma LogDerivZetaBndUniform :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (T : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : |t| ≤ T) (_ : σ ∈ Ico (1 - A / Real.log T ^ 9) 1),
    ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log T ^ 9 := by
  obtain ⟨A, hA_pos, C, hC_pos, hbound⟩ := LogDerivZetaBnd
  use A, hA_pos, C, hC_pos
  intro σ T t ht hTσ hσ
  have abs_t_pos : 0 < |t| := lt_trans (by norm_num) ht
  have log_t_pos : 0 < Real.log |t| := by
    apply Real.log_pos
    exact lt_trans (by norm_num : (1 : ℝ) < (3 : ℝ)) ht
  have T_pos : 0 < T := lt_of_lt_of_le abs_t_pos hTσ
  have T_gt3 : 3 < T := lt_of_lt_of_le ht hTσ
  have log_le : Real.log |t| ≤ Real.log T := Real.log_le_log abs_t_pos hTσ
  have log_T_pos : 0 < Real.log T := Real.log_pos (lt_trans (by norm_num) T_gt3)
  have A_pos : 0 < A := hA_pos.1
  have pow_lot_T_ge_pow_log_t : Real.log |t| ^ 9 ≤ Real.log T ^ 9 := by
    refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr log_le
    exact le_of_lt log_t_pos
    exact le_of_lt log_T_pos
    norm_num
  have hσ' : σ ∈ Ico (1 - A / Real.log (|t|) ^ 9) 1 := by
    have hdenom_le : A / Real.log T ^ 9 ≤ A / Real.log |t| ^ 9 := by
      refine (div_le_div_iff_of_pos_left ?_ ?_ ?_).mpr pow_lot_T_ge_pow_log_t
      exact A_pos
      exact pow_pos log_T_pos 9
      exact pow_pos log_t_pos 9
    apply Set.mem_Ico.mpr
    exact ⟨le_trans (sub_le_sub_left hdenom_le _) hσ.1, hσ.2⟩
  have bound := hbound σ t ht hσ'
  apply le_trans bound
  exact (mul_le_mul_iff_of_pos_left hC_pos).mpr pow_lot_T_ge_pow_log_t
/-%%
\begin{proof}
\uses{LogDerivZetaBnd}
This Lemma \ref{LogDerivZetaBnd}, but uniform in $t$. The point is that the upper bound on $\zeta' / \zeta$ and the lower bound on $\sigma$ only improve as $|t|$ increases.
\end{proof}
%%-/

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

/-%%
\begin{theorem}[ZetaNoZerosOn1Line]\label{ZetaNoZerosOn1Line}\lean{ZetaNoZerosOn1Line}\leanok
The zeta function does not vanish on the 1-line.
\end{theorem}
%%-/
lemma ZetaNoZerosOn1Line (t : ℝ) : ζ (1 + t * I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp
/-%%
\begin{proof}\leanok
This fact is already proved in Stoll's work.
\end{proof}
%%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

lemma ZetaCont : ContinuousOn ζ (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
--  simp only [mem_diff, mem_univ, mem_singleton_iff, true_and] at hx
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert differentiableAt_riemannZeta ?_
  simp only [mem_diff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx

/-%%
Then, since $\zeta$ doesn't vanish on the 1-line, there is a $\sigma<1$ (depending on $T$), so that
the box $[\sigma,1] \times_{ℂ} [-T,T]$ is free of zeros of $\zeta$.
\begin{lemma}[ZetaNoZerosInBox]\label{ZetaNoZerosInBox}\lean{ZetaNoZerosInBox}\leanok
For any $T>0$, there is a constant $\sigma<1$ so that
$$
\zeta(\sigma'+it) \ne 0
$$
for all $|t| < T$ and $\sigma' \ge \sigma$.
\end{lemma}
%%-/

lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| < T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra h
  push_neg at h

  have hn (n : ℕ) := h (σ := 1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| < T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra hσn
    push_neg at hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    use sub_zero (1: ℝ)▸tendsto_order.2 ⟨fun A B=>? _,fun A B=>?_⟩
    · apply(((tendsto_inverse_atTop_nhds_zero_nat.comp (Filter.tendsto_add_atTop_nat (1))).congr (by norm_num)).const_sub 1).eventually_const_lt B|>.mono (hσ'_ge ·|>.trans_lt')
    · norm_num[(hσ'_le _).trans_lt, B.trans_le']

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and).le).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by valid, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert hζ (subseq n) using 3
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      simp_all[Function.comp_def,eventually_nhdsWithin_iff,norm_eq_sqrt_real_inner]
      contrapose! h
      simp_all
      delta abs at*
      exfalso
      simp_rw [Metric.nhds_basis_ball.frequently_iff]at*
      choose! I A B using h
      choose a s using exists_seq_strictAnti_tendsto (0: ℝ)
      apply((isCompact_closedBall _ _).isSeqCompact fun and=>(A _ (s.2.1 and)).le.trans (s.2.2.bddAbove_range.some_mem ⟨and, rfl⟩)).elim
      use fun and ⟨a, H, S, M⟩=>absurd (tendsto_nhds_unique M (tendsto_sub_nhds_zero_iff.1 (( squeeze_zero_norm fun and=>le_of_lt (A _ (s.2.1 _) ) ) (s.2.2.comp S.tendsto_atTop)))) fun and=>?_
      norm_num[*,Function.comp_def] at M
      have:=@riemannZeta_residue_one
      use one_ne_zero (tendsto_nhds_unique (this.comp (tendsto_nhdsWithin_iff.2 ⟨ M,.of_forall (by norm_num[*])⟩)) ( squeeze_zero_norm ?_ ((M.sub_const 1).norm.trans (by rw [sub_self,norm_zero]))))
      use fun and =>.trans (norm_mul_le_of_le ↑(le_rfl) (Complex.norm_def _▸Real.sqrt_le_one.mpr (B ↑_ (s.2.1 ↑_)).right.le)) (by rw [mul_one])

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have cont := @ZetaCont
      by_contra h
      use h (isClosed_singleton.isSeqClosed this (.comp (cont.continuousAt.comp (eventually_ne_nhds (by field_simp [ht₀])).mono fun and=>.intro ⟨⟩) (ToOneT0.trans (inf_le_left))))

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero

/-%%
\begin{proof}
\uses{ZetaNoZerosOn1Line}\leanok
Assume not. Then there is a sequence $|t_n| \le T$ and $\sigma_n \to 1$ so that
 $\zeta(\sigma_n + it_n) = 0$.
By compactness, there is a subsequence $t_{n_k} \to t_0$ along which $\zeta(\sigma_{n_k} + it_{n_k}) = 0$.
If $t_0\ne0$, use the continuity of $\zeta$ to get that $\zeta(1 + it_0) = 0$; this is a contradiction.
If $t_0=0$, $\zeta$ blows up near $1$, so can't be zero nearby.
\end{proof}
%%-/

-- **End collaboration**

/-%%
We now prove that there's an absolute constant $\sigma_0$ so that $\zeta'/\zeta$ is holomorphic on a rectangle $[\sigma_0,2] \times_{ℂ} [-3,3] \setminus \{1\}$.
\begin{lemma}[LogDerivZetaHolcSmallT]\label{LogDerivZetaHolcSmallT}\lean{LogDerivZetaHolcSmallT}\leanok
There is a $\sigma_0 < 1$ so that the function
$$
\frac {\zeta'}{\zeta}(s)
$$
is holomorphic on $\{ \sigma_0 \le \Re s \le 2, |\Im s| \le 3 \} \setminus \{1\}$.
\end{lemma}
%%-/
theorem LogDerivZetaHolcSmallT :
    ∃ (σ₂ : ℝ) (_ : σ₂ < 1), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  have := ZetaNoZerosInBox 4
  sorry
/-%%
\begin{proof}\uses{ZetaNoZerosInBox}
The derivative of $\zeta$ is holomorphic away from $s=1$; the denominator $\zeta(s)$ is nonzero
in this range by Lemma \ref{ZetaNoZerosInBox}.
\end{proof}
%%-/

/-%%
\begin{lemma}[LogDerivZetaHolcLargeT]\label{LogDerivZetaHolcLargeT}\lean{LogDerivZetaHolcLargeT}\leanok
There is an $A>0$ so that for all $T>3$, the function
$
\frac {\zeta'}{\zeta}(s)
$
is holomorphic on $\{1-A/\log^9 T \le \Re s \le 2, |\Im s|\le T \}\setminus\{1\}$.
\end{lemma}
%%-/

theorem LogDerivZetaHolcLargeT :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∃ (Tlb : ℝ) (_ : 3 < Tlb), ∀ (T : ℝ) (_ : Tlb < T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Ioo ((1 : ℝ) - A / Real.log T ^ 9) 2)  ×ℂ (Ioo (-T) T) ) \ {1}) := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree
  use A
  use A_inter
  obtain ⟨σ₀, σ₀_lt_one, trash⟩ := LogDerivZetaHolcSmallT
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox 4
  have : ∃ (Tlb : ℝ) (_ : 3 < Tlb), ∀ (T : ℝ), Tlb < T → σ₀ < (1 : ℝ) - A / Real.log T ^ 9 ∧ σ₁ < (1 : ℝ) - A / Real.log T ^ 9 := by
    let Tlb : ℝ := max 5 (max (Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9))) (Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9))))
    use Tlb
    have three_lt_Tlb : 3 < Tlb := by
      rw[lt_max_iff]
      exact Or.inl (by norm_num)
    use three_lt_Tlb
    intro T Tlb_lt_T
    have temp : σ₀ < 1 - A / Real.log T ^ 9 := by
      have : Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9)) ≤ Tlb := by
        dsimp[Tlb]
        have temp : Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9)) ≤
          max (Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9))) (Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9))) := by apply le_max_left
        have : max (Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9))) (Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9))) ≤
          max 5 (max (Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9))) (Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9)))) := by apply le_max_right
        (expose_names; exact le_sup_of_le_right temp)
      have keep : Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9)) < T := by exact lt_of_le_of_lt this Tlb_lt_T
      rw[← Real.lt_log_iff_exp_lt] at keep
      have : A / (1 - σ₀) < Real.log T ^ 9 := by
        have temp : 0 ≤ A / (1 - σ₀) := by
          apply div_nonneg
          apply le_of_lt A_inter.1
          linarith
        have : 9 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one 8)
        rw[← Real.rpow_inv_natCast_pow temp this]
        have : Odd 9 := by exact Nat.odd_iff.mpr rfl
        rw[Odd.pow_lt_pow this]
        have : (↑(9 : ℕ))⁻¹ = 1 / (9 : ℝ) := by exact inv_eq_one_div (9 : ℝ)
        rw[this]
        exact keep
      have : A / Real.log T ^ 9 < 1 - σ₀ := by
        rw[div_lt_iff₀] at this ⊢
        rw[mul_comm]
        exact this
        refine pow_pos ?_ 9
        apply Real.log_pos
        repeat linarith
      repeat linarith
    have : σ₁ < 1 - A / Real.log T ^ 9 := by
      have : Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9)) ≤ Tlb := by
        dsimp[Tlb]
        have temp : Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9)) ≤
          max (Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9))) (Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9))) := by apply le_max_right
        have : max (Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9))) (Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9))) ≤
          max 5 (max (Real.exp ((A / (1 - σ₀)) ^ ((1 : ℝ) / 9))) (Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9)))) := by apply le_max_right
        (expose_names; exact le_sup_of_le_right temp)
      have keep : Real.exp ((A / (1 - σ₁)) ^ ((1 : ℝ) / 9)) < T := by exact lt_of_le_of_lt this Tlb_lt_T
      rw[← Real.lt_log_iff_exp_lt] at keep
      have : A / (1 - σ₁) < Real.log T ^ 9 := by
        have temp : 0 ≤ A / (1 - σ₁) := by
          apply div_nonneg
          apply le_of_lt A_inter.1
          linarith
        have : 9 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one 8)
        rw[← Real.rpow_inv_natCast_pow temp this]
        have : Odd 9 := by exact Nat.odd_iff.mpr rfl
        rw[Odd.pow_lt_pow this]
        have : (↑(9 : ℕ))⁻¹ = 1 / (9 : ℝ) := by exact inv_eq_one_div (9 : ℝ)
        rw[this]
        exact keep
      have : A / Real.log T ^ 9 < 1 - σ₁ := by
        rw[div_lt_iff₀] at this ⊢
        rw[mul_comm]
        exact this
        refine pow_pos ?_ 9
        apply Real.log_pos
        repeat linarith
      repeat linarith
    exact ⟨temp, this⟩
  obtain ⟨Tlb, three_lt_Tlb, TlbConsequences⟩ := this
  use Tlb
  use three_lt_Tlb
  intro T Tlb_lt_T
  have three_lt_T : 3 < T := by exact gt_trans Tlb_lt_T three_lt_Tlb
  have Tlb_lt_abs_T : Tlb < |T| := by
    rw[abs_of_nonneg]
    exact Tlb_lt_T
    positivity
  have temp : 1 - A / Real.log T ^ 9 < 1 := by
    apply sub_lt_self
    apply div_pos
    have : 0 < A := by
      rw[Set.mem_Ioc] at A_inter
      exact A_inter.1
    exact this
    apply pow_pos
    rw[← Real.log_one]
    apply Real.log_lt_log
    norm_num
    linarith
  have temp' : 1 - A / Real.log |T| ^ 9 < 1 := by
    rw[abs_of_nonneg]
    exact temp
    positivity
  have zetaZeroFreeCrit : ∀ (σ t : ℝ), σ ∈ Ioo (1 - A / Real.log |T| ^ 9) 1 → t ∈ Ioo (-T) T → ζ (↑σ + ↑t * I) ≠ 0 := by
    intro σ t σ_inter t_inter
    have : 4 ≤ |t| ∨ 4 > |t| := by exact le_or_lt 4 |t|
    rcases this
    apply restOfZetaZeroFree σ t
    linarith
    apply Ioo_subset_Ico_self
    refine mem_Ioo.mpr ?_
    have : 1 - A / Real.log |t| ^ 9 < σ := by
      have temp: 1 - A / Real.log |T| ^ 9 < σ := by exact σ_inter.1
      have : 1 - A / Real.log |t| ^ 9 < 1 - A / Real.log |T| ^ 9 := by
        refine (sub_lt_sub_iff_left 1).mpr ?_
        refine div_lt_div_of_pos_left ?_ ?_ ?_
        exact A_inter.1
        refine pow_pos ?_ 9
        rw[← Real.log_one]
        apply Real.log_lt_log
        norm_num
        linarith
        refine pow_lt_pow_left₀ ?_ ?_ ?_
        apply Real.log_lt_log
        positivity
        nth_rewrite 2 [abs_of_nonneg]
        rw[abs_lt]
        exact t_inter
        positivity
        rw[← Real.log_one]
        apply Real.log_le_log
        positivity
        linarith
        exact Ne.symm (Nat.zero_ne_add_one 8)
      (expose_names; exact gt_trans temp this)
    exact ⟨this, σ_inter.2⟩
    have : ∀ (t : ℝ), |t| < 4 → ∀ σ' ≥ σ₁, riemannZeta (↑σ' + ↑t * Complex.I) ≠ 0 := by exact fun t a σ' a_1 ↦ noZerosInBox t a σ' a_1
    apply this
    (expose_names; exact h)
    have temp : σ₀ < 1 - A / Real.log T ^ 9 ∧ σ₁ < 1 - A / Real.log T ^ 9 := by exact TlbConsequences T Tlb_lt_T
    have : 1 - A / Real.log T ^ 9 < σ := by
      have : 1 - A / Real.log |T| ^ 9 < σ := by exact σ_inter.1
      rw[abs_of_nonneg] at this
      exact this
      positivity
    apply le_of_lt
    exact lt_trans temp.2 this
  have zetaZeroFreeTriv : ∀ (σ t : ℝ), σ ∈ Ico 1 2 → t ∈ Ioo (-T) T → ζ (↑σ + ↑t * I) ≠ 0 := by
    intro σ t σ_inter t_inter
    obtain ⟨lb, ub⟩ := σ_inter
    have : 1 ≤ (↑σ + ↑t * I).re := by
      rw[add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
      linarith
    exact riemannZeta_ne_zero_of_one_le_re this
  have zetaZeroFreeCombo : ∀ (σ t : ℝ), σ ∈ Ioo (1 - A / Real.log |T| ^ 9) 2 → t ∈ Ioo (-T) T → ζ (↑σ + ↑t * I) ≠ 0 := by
    intro σ t σ_inter
    rw[← Set.Ioo_union_Ico_eq_Ioo temp' one_le_two, Set.mem_union] at σ_inter
    exact Or.elim σ_inter (zetaZeroFreeCrit σ t) (zetaZeroFreeTriv σ t)
  clear zetaZeroFreeCrit zetaZeroFreeTriv
  unfold HolomorphicOn
  apply DifferentiableOn.div
  apply DifferentiableOn.deriv
  unfold DifferentiableOn
  intro x xIn
  rw[Set.mem_diff] at xIn
  refine DifferentiableAt.differentiableWithinAt ?_
  exact differentiableAt_riemannZeta xIn.2
  refine IsOpen.sdiff ?_ ?_
  refine IsOpen.reProdIm ?_ ?_
  exact isOpen_Ioo
  exact isOpen_Ioo
  exact isClosed_singleton
  unfold DifferentiableOn
  intro x xIn
  rw[Set.mem_diff] at xIn
  refine DifferentiableAt.differentiableWithinAt ?_
  exact differentiableAt_riemannZeta xIn.2
  intro x
  rw[Set.mem_diff, Complex.mem_reProdIm]
  intro xHypo
  obtain ⟨⟨xReIn, xImIn⟩, xOut⟩ := xHypo
  have : x = x.re + x.im * I := by exact Eq.symm (re_add_im x)
  rw[this]
  apply zetaZeroFreeCombo x.re x.im
  rw[abs_of_nonneg]
  exact xReIn
  positivity
  exact xImIn

/-%%
\begin{proof}\uses{ZetaZeroFree}
The derivative of $\zeta$ is holomorphic away from $s=1$; the denominator $\zeta(s)$ is nonzero
in this range by Lemma \ref{ZetaZeroFree}.
\end{proof}
%%-/

/-%%
It would perhaps (?) be better to refactor this entire file so that we're not using explicit
constants but instead systematically using big Oh notation... The punchline would be:
%%-/
/-%%
\begin{lemma}[LogDerivZetaBndAlt]\label{LogDerivZetaBndAlt}\lean{LogDerivZetaBndAlt}\leanok
There is an $A>0$ so that for $1-A/\log^9 |t| \le \sigma < 1$ and $|t|\to\infty$,
$$
|\frac {\zeta'}{\zeta} (\sigma+it)| \ll \log^9 |t|.
$$
(Same statement but using big-Oh and filters.)
\end{lemma}
%%-/
lemma LogDerivZetaBndAlt :
    ∃ A > 0, ∀ (σ) (_ : σ ∈ Ico ((1 : ℝ) / 2) (1 : ℝ)),
    (fun (t : ℝ) ↦ ζ' (σ + t * I) / ζ (σ + t * I)) =O[cocompact ℝ ⊓
      Filter.principal {t | 1 - A / Real.log |t| ^ 9 < σ}]
        fun t ↦ Real.log |t| ^ 9 := by
  obtain ⟨A, hA, C, _, h⟩ := LogDerivZetaBnd
  refine ⟨A, hA.1, fun σ ⟨σ_ge, σ_lt⟩ ↦ ?_⟩
  -- This could all be done much cleaner; TODO: refactor
  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_inf, cocompact_eq_atBot_atTop]
  refine ⟨{t : ℝ | 4 ≤ |t|}, ?_, {t | 1 - A / Real.log |t| ^ 9 < σ},
    fun ⦃a⦄ a ↦ a, fun t ⟨t_ge, ht⟩ ↦ ?_⟩
  · rw [mem_sup]
    refine ⟨?_, ?_⟩
    · simp only [mem_atBot_sets, mem_setOf_eq]
      refine ⟨-4, fun b hb ↦ ?_⟩
      rw [_root_.abs_of_nonpos (by linarith)]
      linarith
    · simp only [mem_atTop_sets, ge_iff_le, mem_setOf_eq]
      refine ⟨4, fun b hb ↦ ?_⟩
      rwa [_root_.abs_of_nonneg (by linarith)]
  simp only [mem_setOf_eq] at ht
  convert h σ t (by linarith [mem_Ici.mp t_ge]) ⟨ht.le, σ_lt⟩
  simp only [mem_setOf_eq] at t_ge
  have := Real.log_nonneg (by linarith : 1 ≤ |t|)
  simp only [Real.norm_eq_abs, norm_pow, abs_eq_self.mpr, this]
/-%%
\begin{proof}\leanok
\uses{LogDerivZetaBnd}
Same as above.
\end{proof}
%%-/
