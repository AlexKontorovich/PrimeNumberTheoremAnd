import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Helper lemmas for Kadiri eq. (12) (#1537)

Reusable order-theory, meromorphy and Laplace-transform-analyticity facts used in the proof of
`kadiri_thm_3_1_q1_eq_12`.
-/

open Filter Topology Complex

/-- If `f = (z-x)^n • g` near `x` (punctured) with `g` analytic, then `deriv f` is
`(z-x)^(n-1) • (n • g + (z-x) • g')` near `x`. -/
theorem deriv_zpow_mul_eventuallyEq {f : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (g : ℂ → ℂ) (hg_an : AnalyticAt ℂ g x)
    (hg_eq : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z) :
    deriv f =ᶠ[𝓝[≠] x]
      (fun z ↦ (z - x) ^ (n - 1)) * (fun z ↦ (n : ℂ) * g z + (z - x) * deriv g z) := by
  have key : ∀ᶠ z in 𝓝 x, z ≠ x → f z = (z - x) ^ n • g z := eventually_nhdsWithin_iff.mp hg_eq
  obtain ⟨V, hV_sub, hV_open, hxV⟩ := eventually_nhds_iff.mp key
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hV_open.mem_nhds hxV),
    hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z₀ hz₀ne hz₀V hg_an_z₀
  have hz₀x : z₀ - x ≠ 0 := sub_ne_zero.mpr hz₀ne
  have hloc : f =ᶠ[𝓝 z₀] fun z ↦ (z - x) ^ n * g z := by
    filter_upwards [(hV_open.sdiff isClosed_singleton).mem_nhds ⟨hz₀V, hz₀ne⟩] with z hz
    rw [hV_sub z hz.1 hz.2, smul_eq_mul]
  have hd1 : HasDerivAt (fun z : ℂ ↦ (z - x) ^ n) ((n : ℂ) * (z₀ - x) ^ (n - 1)) z₀ := by
    simpa using (hasDerivAt_zpow n (z₀ - x) (Or.inl hz₀x)).comp z₀ ((hasDerivAt_id z₀).sub_const x)
  have hprod : HasDerivAt f ((n : ℂ) * (z₀ - x) ^ (n - 1) * g z₀ + (z₀ - x) ^ n * deriv g z₀) z₀ :=
    (hd1.mul hg_an_z₀.differentiableAt.hasDerivAt).congr_of_eventuallyEq hloc
  rw [hprod.deriv]; simp only [Pi.mul_apply]
  rw [show (z₀ - x) ^ (n - 1) = (z₀ - x) ^ n * (z₀ - x)⁻¹ by rw [zpow_sub_one₀ hz₀x]]; field_simp

/-- The order of the derivative is at least the order minus one. -/
theorem meromorphicOrderAt_le_deriv_add_one {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hntop : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicOrderAt f x ≤ meromorphicOrderAt (deriv f) x + 1 := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hntop
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
  have hh_an : AnalyticAt ℂ (fun z ↦ (n : ℂ) * g z + (z - x) * deriv g z) x :=
    (analyticAt_const.mul hg_an).add ((analyticAt_id.sub analyticAt_const).mul hg_an.deriv)
  have hzpow : MeromorphicAt (fun z : ℂ ↦ (z - x) ^ (n - 1)) x :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).zpow (n - 1)
  have hzord : meromorphicOrderAt (fun z : ℂ ↦ (z - x) ^ (n - 1)) x = (↑(n - 1) : WithTop ℤ) := by
    rw [show (fun z : ℂ ↦ (z - x) ^ (n - 1)) = (fun z : ℂ ↦ z - x) ^ (n - 1) from rfl]
    exact meromorphicOrderAt_zpow_id_sub_const
  rw [← hn, meromorphicOrderAt_congr (deriv_zpow_mul_eventuallyEq g hg_an hg_eq),
    meromorphicOrderAt_mul hzpow hh_an.meromorphicAt, hzord, add_right_comm,
    show (↑(n - 1) : WithTop ℤ) + 1 = ↑n by rw [← WithTop.coe_one, ← WithTop.coe_add]; norm_num]
  exact le_add_of_nonneg_right hh_an.meromorphicOrderAt_nonneg

/-- The Riemann zeta function is meromorphic at every point. -/
theorem meromorphicAt_riemannZeta (s : ℂ) : MeromorphicAt riemannZeta s := by
  have hΛ : MeromorphicAt completedRiemannZeta s := by
    rw [show completedRiemannZeta = fun z ↦ completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) from
      funext completedRiemannZeta_eq]
    exact (((differentiable_completedZeta₀.analyticAt s).meromorphicAt.sub
      ((MeromorphicAt.const 1 s).div analyticAt_id.meromorphicAt)).sub
      ((MeromorphicAt.const 1 s).div ((analyticAt_const.sub analyticAt_id).meromorphicAt)))
  have hG : MeromorphicAt Gammaℝ s := by
    rw [show Gammaℝ = fun z ↦ (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) from funext Gammaℝ_def]
    refine MeromorphicAt.mul (AnalyticAt.meromorphicAt ?_)
      (MeromorphicAt.comp_analyticAt (f := Complex.Gamma) (g := fun z : ℂ ↦ z / 2) (x := s)
        ((MeromorphicOn.Gamma (s := Set.univ)) (s / 2) (Set.mem_univ _)) (by fun_prop))
    rw [show (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2))
        = fun z ↦ Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) from by
      funext z; rw [Complex.cpow_def_of_ne_zero (by simp [Real.pi_ne_zero])]]
    fun_prop
  have hz0 : ∀ᶠ z in 𝓝[≠] s, z ≠ 0 := by
    rcases eq_or_ne s 0 with h | h
    · subst h; exact self_mem_nhdsWithin
    · exact (isOpen_compl_singleton.eventually_mem (Set.mem_compl_singleton_iff.mpr h)).filter_mono
        nhdsWithin_le_nhds
  exact (hΛ.div hG).congr ((by filter_upwards [hz0] with z hz using riemannZeta_def_of_ne_zero hz :
    riemannZeta =ᶠ[𝓝[≠] s] fun z ↦ completedRiemannZeta z / Gammaℝ z)).symm

/-- The Riemann zeta function is not locally zero anywhere. -/
theorem meromorphicOrderAt_riemannZeta_ne_top (z : ℂ) : meromorphicOrderAt riemannZeta z ≠ ⊤ := by
  rcases eq_or_ne z 1 with h | h
  · subst h
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (meromorphicAt_riemannZeta 1)).2
      riemannZeta_eventually_ne_zero
  · have hz1 : z ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := h
    rw [(riemannZeta_analyticOn_compl_one z hz1).meromorphicOrderAt_eq, Ne, ENat.map_eq_top_iff]
    have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by simp
    have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have hord2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
      rw [(riemannZeta_analyticOn_compl_one 2 h2).analyticOrderAt_eq_zero.mpr
        (riemannZeta_ne_zero_of_one_le_re (by norm_num))]; simp
    exact riemannZeta_analyticOn_compl_one.analyticOrderAt_ne_top_of_isPreconnected hconn h2 hz1 hord2

/-- The Riemann zeta function has a simple pole at `s = 1`: its meromorphic order there is `-1`. -/
theorem meromorphicOrderAt_riemannZeta_one : meromorphicOrderAt riemannZeta 1 = (-1 : ℤ) := by
  have hsub : MeromorphicAt (fun s : ℂ ↦ s - 1) 1 :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have h0 : meromorphicOrderAt ((fun s : ℂ ↦ s - 1) * riemannZeta) 1 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
      (hsub.mul (meromorphicAt_riemannZeta 1))).1 ⟨1, one_ne_zero, riemannZeta_residue_one⟩
  rw [meromorphicOrderAt_mul hsub (meromorphicAt_riemannZeta 1),
    meromorphicOrderAt_id_sub_const] at h0
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (meromorphicOrderAt_riemannZeta_ne_top 1)
  rw [← hn] at h0 ⊢
  have hni : (1 : ℤ) + n = 0 := by exact_mod_cast h0
  norm_cast
  omega

/-- The negative logarithmic derivative `-ζ'/ζ` has at most a simple pole at every point. -/
theorem neg_one_le_meromorphicOrderAt_neg_zeta_logDeriv (z : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun w ↦ -deriv riemannZeta w / riemannZeta w) z := by
  set φ : ℂ → ℂ := fun w ↦ -deriv riemannZeta w / riemannZeta w with hφ
  have hφmero : MeromorphicAt φ z :=
    (meromorphicAt_riemannZeta z).deriv.neg.div (meromorphicAt_riemannZeta z)
  have hntop := meromorphicOrderAt_riemannZeta_ne_top z
  have hne : ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (meromorphicAt_riemannZeta z)).1 hntop
  have hmul_eq : (φ * riemannZeta) =ᶠ[𝓝[≠] z] fun w ↦ -deriv riemannZeta w := by
    filter_upwards [hne] with w hw; simp only [hφ, Pi.mul_apply]; field_simp
  have hkey : meromorphicOrderAt φ z + meromorphicOrderAt riemannZeta z
      = meromorphicOrderAt (deriv riemannZeta) z := by
    rw [← meromorphicOrderAt_mul hφmero (meromorphicAt_riemannZeta z),
      meromorphicOrderAt_congr hmul_eq,
      show (fun w ↦ -deriv riemannZeta w) = -(deriv riemannZeta) from rfl, ← meromorphicOrderAt_neg]
  have hbound := meromorphicOrderAt_le_deriv_add_one (meromorphicAt_riemannZeta z) hntop
  rw [← hkey] at hbound
  have h2 : (0 : WithTop ℤ) ≤ meromorphicOrderAt φ z + 1 :=
    (WithTop.add_le_add_iff_right hntop).1 (by rw [zero_add, add_right_comm]; exact hbound)
  refine (WithTop.add_le_add_iff_right WithTop.one_ne_top).1 ?_
  rw [show ((-1 : ℤ) : WithTop ℤ) + 1 = 0 by rw [← WithTop.coe_one, ← WithTop.coe_add]; norm_num]
  exact h2

open MeasureTheory Asymptotics Set

/-- Keystone: a linear weight is absorbed by an exponential with a slightly smaller rate. -/
theorem abs_mul_exp_isBigO {b b' : ℝ} (hbb : b' < b) :
    (fun x : ℝ ↦ |x| * Real.exp (-(1/2+b)*|x|)) =O[cocompact ℝ]
      (fun x ↦ Real.exp (-(1/2+b')*|x|)) := by
  have hδ : 0 < b - b' := by linarith
  have hg : Tendsto (fun t : ℝ ↦ t * Real.exp (-(b-b')*t)) atTop (nhds 0) := by
    simpa [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (b-b') hδ
  have htend : Tendsto (fun x : ℝ ↦ |x| * Real.exp (-(b-b')*|x|)) (cocompact ℝ) (nhds 0) := by
    simpa [Function.comp_def, Real.norm_eq_abs] using hg.comp (tendsto_norm_cocompact_atTop (E := ℝ))
  have hbound : (fun x : ℝ ↦ |x| * Real.exp (-(b-b')*|x|)) =O[cocompact ℝ] (fun _ ↦ (1:ℝ)) :=
    htend.isBigO_one ℝ
  rw [show (fun x : ℝ ↦ |x| * Real.exp (-(1/2+b)*|x|)) =
      (fun x ↦ (|x| * Real.exp (-(b-b')*|x|)) * Real.exp (-(1/2+b')*|x|)) from by
    funext x; rw [mul_assoc, ← Real.exp_add]; congr 2; ring]
  simpa using hbound.mul (isBigO_refl (fun x : ℝ ↦ Real.exp (-(1/2+b')*|x|)) (cocompact ℝ))

/-- The decay hypothesis transfers from `φ` to `-(·)·φ` with a slightly smaller rate. -/
theorem neg_id_mul_decay {φ : ℝ → ℂ} {b b' : ℝ} (hbb : b' < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x:ℂ)/2)) =O[cocompact ℝ]
      fun x ↦ Real.exp (-(1/2+b)*|x|)) :
    (fun x : ℝ ↦ (-(x:ℂ) * φ x) * Complex.exp ((x:ℂ)/2)) =O[cocompact ℝ]
      fun x ↦ Real.exp (-(1/2+b')*|x|) := by
  have hx : (fun x : ℝ ↦ (x:ℂ)) =O[cocompact ℝ] (fun x : ℝ ↦ |x|) := by
    rw [isBigO_iff]; exact ⟨1, Filter.Eventually.of_forall (fun x ↦ by simp [Complex.norm_real])⟩
  rw [show (fun x : ℝ ↦ (-(x:ℂ) * φ x) * Complex.exp ((x:ℂ)/2))
      = (fun x : ℝ ↦ -((x:ℂ) * (φ x * Complex.exp ((x:ℂ)/2)))) from by funext x; ring]
  exact ((hx.mul hφ_decay).neg_left).trans (abs_mul_exp_isBigO hbb)

/-- The Laplace integrand `φ(y)·e^{-σy}` is integrable for `σ` in the convergence strip. -/
theorem laplace_integrand_integrable {φ : ℝ → ℂ} {b σ : ℝ} (hφ : Continuous φ)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x:ℂ)/2)) =O[cocompact ℝ]
      fun x ↦ Real.exp (-(1/2+b)*|x|))
    (hσ_top : -(1+b) < σ) (hσ_bot : σ < b) :
    Integrable (fun y : ℝ ↦ φ y * Complex.exp (-(σ:ℂ)*y)) := by
  have h_loc : LocallyIntegrable (fun y : ℝ ↦ φ y * Complex.exp (-(σ:ℂ)*y)) :=
    (hφ.mul (by fun_prop)).locallyIntegrable
  have hbig_top : (fun y : ℝ ↦ φ y * Complex.exp (-(σ:ℂ)*y)) =O[atTop]
      (fun y ↦ Real.exp (-(1+b+σ)*y)) := by
    have hφ_top : (fun x : ℝ ↦ φ x * Complex.exp ((x:ℂ)/2)) =O[atTop]
        fun x ↦ Real.exp (-(1/2+b)*|x|) :=
      hφ_decay.mono (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
    rw [isBigO_iff] at hφ_top ⊢
    obtain ⟨C, hC⟩ := hφ_top
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_ge_atTop 0] with y hy hy0
    rw [show ‖φ y * Complex.exp (-(σ:ℂ)*y)‖ = ‖φ y‖ * Real.exp (-σ*y) by
          rw [norm_mul, Complex.norm_exp]; congr 1; simp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [show ‖φ y * Complex.exp ((y:ℂ)/2)‖ = ‖φ y‖ * Real.exp (y/2) by
          rw [norm_mul, Complex.norm_exp]; congr 1; simp,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hy0] at hy
    rw [show -σ*y = y/2 + -(σ+1/2)*y by ring, show -(1+b+σ)*y = -(1/2+b)*y + -(σ+1/2)*y by ring,
        Real.exp_add, Real.exp_add, ← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hy (le_of_lt (Real.exp_pos _))
  have hbig_bot : (fun y : ℝ ↦ φ y * Complex.exp (-(σ:ℂ)*y)) =O[atBot]
      (fun y ↦ Real.exp ((b-σ)*y)) := by
    have hφ_bot : (fun x : ℝ ↦ φ x * Complex.exp ((x:ℂ)/2)) =O[atBot]
        fun x ↦ Real.exp (-(1/2+b)*|x|) :=
      hφ_decay.mono (by rw [cocompact_eq_atBot_atTop]; exact le_sup_left)
    rw [isBigO_iff] at hφ_bot ⊢
    obtain ⟨C, hC⟩ := hφ_bot
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_le_atBot 0] with y hy hy0
    rw [show ‖φ y * Complex.exp (-(σ:ℂ)*y)‖ = ‖φ y‖ * Real.exp (-σ*y) by
          rw [norm_mul, Complex.norm_exp]; congr 1; simp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [show ‖φ y * Complex.exp ((y:ℂ)/2)‖ = ‖φ y‖ * Real.exp (y/2) by
          rw [norm_mul, Complex.norm_exp]; congr 1; simp,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonpos hy0] at hy
    rw [show -σ*y = y/2 + (-σ-1/2)*y by ring, show (b-σ)*y = -(1/2+b)*(-y) + (-σ-1/2)*y by ring,
        Real.exp_add, Real.exp_add, ← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hy (le_of_lt (Real.exp_pos _))
  have hint_top : IntegrableAtFilter (fun y : ℝ ↦ Real.exp (-(1+b+σ)*y)) atTop volume :=
    ⟨Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 (by linarith)⟩
  have hint_bot : IntegrableAtFilter (fun y : ℝ ↦ Real.exp ((b-σ)*y)) atBot volume := by
    have hα : 0 < b - σ := by linarith
    have h_top : IntegrableAtFilter (fun y : ℝ ↦ Real.exp (-((b-σ)*y))) atTop volume :=
      ⟨Ioi 0, Ioi_mem_atTop 0, by simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hα⟩
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      convert (MeasurableEquiv.neg ℝ).map_symm.symm using 1; simp
    rw [hvol, Function.comp_def]; simp only [mul_neg]; exact h_top
  exact h_loc.integrable_of_isBigO_atBot_atTop hbig_bot hint_bot hbig_top hint_top

/-- The derivative integrand `-(y)·φ(y)·e^{-σy}` is integrable for `σ` in the strip. -/
theorem laplace_deriv_integrand_integrable {φ : ℝ → ℂ} {b σ : ℝ} (hφc : Continuous φ)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x:ℂ)/2)) =O[cocompact ℝ]
      fun x ↦ Real.exp (-(1/2+b)*|x|))
    (hσtop : -(1+b) < σ) (hσbot : σ < b) :
    Integrable (fun y : ℝ ↦ (-(y:ℂ) * φ y) * Complex.exp (-(σ:ℂ)*y)) := by
  set b' := (max σ (-1-σ) + b)/2 with hb'def
  have hmax : max σ (-1-σ) < b := max_lt hσbot (by linarith)
  have hMle : max σ (-1-σ) < b' := by rw [hb'def]; linarith
  have hb'bot : σ < b' := lt_of_le_of_lt (le_max_left _ _) hMle
  have hb'top : -(1+b') < σ := by
    have := lt_of_le_of_lt (le_max_right σ (-1-σ)) hMle; linarith
  exact laplace_integrand_integrable (φ := fun y ↦ -(y:ℂ) * φ y) (by fun_prop)
    (neg_id_mul_decay (by rw [hb'def]; linarith) hφ_decay) hb'top hb'bot

/-- The bilateral Laplace transform `Φ(s) = ∫ φ(y) e^{-sy} dy` is differentiable on the strip. -/
theorem Phi_differentiableAt {φ : ℝ → ℂ} {b : ℝ} (hφc : Continuous φ)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x:ℂ)/2)) =O[cocompact ℝ]
      fun x ↦ Real.exp (-(1/2+b)*|x|))
    {x₀ : ℂ} (h_top : -(1+b) < x₀.re) (h_bot : x₀.re < b) :
    DifferentiableAt ℂ (fun s ↦ ∫ y, φ y * Complex.exp (-s*(y:ℂ))) x₀ := by
  set σ₀ := x₀.re with hσ₀
  set m : ℝ := min (b - σ₀) (σ₀ + 1 + b) with hm_def
  have hm : 0 < m := lt_min (by linarith) (by linarith)
  set ε : ℝ := m/4 with hε_def
  have hε : 0 < ε := by positivity
  have hmle1 : m ≤ b - σ₀ := min_le_left _ _
  have hmle2 : m ≤ σ₀ + 1 + b := min_le_right _ _
  have hlo_top : -(1+b) < σ₀ - ε := by simp only [hε_def, hm_def]; linarith
  have hlo_bot : σ₀ - ε < b := by linarith
  have hhi_top : -(1+b) < σ₀ + ε := by linarith
  have hhi_bot : σ₀ + ε < b := by simp only [hε_def, hm_def]; linarith
  set bound : ℝ → ℝ := fun y ↦ ‖(-(y:ℂ)*φ y) * Complex.exp (-((σ₀-ε:ℝ):ℂ)*y)‖
      + ‖(-(y:ℂ)*φ y) * Complex.exp (-((σ₀+ε:ℝ):ℂ)*y)‖ with hbound_def
  have hbound_int : Integrable bound :=
    (laplace_deriv_integrand_integrable hφc hφ_decay hlo_top hlo_bot).norm.add
      (laplace_deriv_integrand_integrable hφc hφ_decay hhi_top hhi_bot).norm
  have hnorm : ∀ (σ' : ℝ) (y : ℝ), ‖(-(y:ℂ)*φ y) * Complex.exp (-(σ':ℂ)*y)‖
      = ‖(-(y:ℂ)*φ y)‖ * Real.exp (-(σ'*y)) := by
    intro σ' y; rw [norm_mul, Complex.norm_exp]; congr 2; simp [Complex.mul_re]
  have hF_int : Integrable (fun y : ℝ ↦ φ y * Complex.exp (-x₀*(y:ℂ))) := by
    rw [← integrable_norm_iff (by fun_prop)]
    refine (laplace_integrand_integrable hφc hφ_decay h_top h_bot |>.norm).congr
      (Filter.Eventually.of_forall (fun y ↦ ?_))
    simp only [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, hσ₀]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (bound := bound) (F := fun s y ↦ φ y * Complex.exp (-s*(y:ℂ)))
    (F' := fun s y ↦ -(y:ℂ) * φ y * Complex.exp (-s*(y:ℂ)))
    (s := Metric.ball x₀ ε) (x₀ := x₀)
    (Metric.ball_mem_nhds x₀ hε)
    (Filter.Eventually.of_forall (fun s ↦ by fun_prop)) hF_int (by fun_prop)
    ?_ hbound_int ?_
  · exact (key.2).differentiableAt
  · refine Filter.Eventually.of_forall (fun y s hs ↦ ?_)
    have hsre : σ₀ - ε < s.re ∧ s.re < σ₀ + ε := by
      have h2 : ‖s - x₀‖ < ε := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
      have h1 : |s.re - x₀.re| ≤ ‖s - x₀‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      rw [← hσ₀] at h1
      have hd : |s.re - σ₀| < ε := lt_of_le_of_lt h1 h2
      rw [abs_lt] at hd; exact ⟨by linarith [hd.1], by linarith [hd.2]⟩
    have hgoalL : ‖-(y:ℂ) * φ y * Complex.exp (-s*(y:ℂ))‖
        = ‖(-(y:ℂ)*φ y)‖ * Real.exp (-(s.re*y)) := by
      rw [show -(y:ℂ) * φ y * Complex.exp (-s*(y:ℂ)) = (-(y:ℂ)*φ y) * Complex.exp (-s*(y:ℂ)) by ring,
        norm_mul, Complex.norm_exp]; congr 2; simp [Complex.mul_re]
    rw [hgoalL]; simp only [hbound_def]; rw [hnorm, hnorm]
    have hN : (0:ℝ) ≤ ‖(-(y:ℂ)*φ y)‖ := norm_nonneg _
    have hexp_le : Real.exp (-(s.re*y)) ≤ Real.exp (-((σ₀-ε)*y)) + Real.exp (-((σ₀+ε)*y)) := by
      rcases le_total 0 y with hy | hy
      · have : Real.exp (-(s.re*y)) ≤ Real.exp (-((σ₀-ε)*y)) :=
          Real.exp_le_exp.mpr (by nlinarith [hsre.1, hy])
        linarith [Real.exp_pos (-((σ₀+ε)*y))]
      · have : Real.exp (-(s.re*y)) ≤ Real.exp (-((σ₀+ε)*y)) :=
          Real.exp_le_exp.mpr (by nlinarith [hsre.2, hy])
        linarith [Real.exp_pos (-((σ₀-ε)*y))]
    calc ‖(-(y:ℂ)*φ y)‖ * Real.exp (-(s.re*y))
        ≤ ‖(-(y:ℂ)*φ y)‖ * (Real.exp (-((σ₀-ε)*y)) + Real.exp (-((σ₀+ε)*y))) :=
          mul_le_mul_of_nonneg_left hexp_le hN
      _ = _ := by ring
  · refine Filter.Eventually.of_forall (fun y s _ ↦ ?_)
    have h1 : HasDerivAt (fun s : ℂ ↦ -s * (y:ℂ)) (-1 * (y:ℂ)) s :=
      ((hasDerivAt_id s).neg).mul_const (y:ℂ)
    have h2 := (h1.cexp).const_mul (φ y)
    convert h2 using 1; ring

/-- The bilateral Laplace transform is analytic on the strip `-(1+b) < Re s < b`. -/
theorem Phi_analyticOnNhd {φ : ℝ → ℂ} {b : ℝ} (hφc : Continuous φ)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x:ℂ)/2)) =O[cocompact ℝ]
      fun x ↦ Real.exp (-(1/2+b)*|x|)) :
    AnalyticOnNhd ℂ (fun s ↦ ∫ y, φ y * Complex.exp (-s*(y:ℂ)))
      {s : ℂ | -(1+b) < s.re ∧ s.re < b} := by
  have hSopen : IsOpen {s : ℂ | -(1+b) < s.re ∧ s.re < b} := by
    rw [show {s : ℂ | -(1+b) < s.re ∧ s.re < b} = Complex.re ⁻¹' (Set.Ioo (-(1+b)) b) from by
      ext s; simp [Set.mem_Ioo, and_comm]]
    exact isOpen_Ioo.preimage Complex.continuous_re
  exact DifferentiableOn.analyticOnNhd
    (fun s hs ↦ (Phi_differentiableAt hφc hφ_decay hs.1 hs.2).differentiableWithinAt) hSopen

/-- The limit `(z-p)·(-ζ'/ζ)(z) → -order(ζ,p)` (residue of the log-derivative = order). -/
theorem tendsto_sub_mul_neg_zeta_logDeriv {p : ℂ} {m : ℤ}
    (hm : meromorphicOrderAt riemannZeta p = m) :
    Tendsto (fun z ↦ (z - p) * (-deriv riemannZeta z / riemannZeta z)) (𝓝[≠] p) (𝓝 (-(m:ℂ))) := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ :=
    (meromorphicOrderAt_eq_int_iff (meromorphicAt_riemannZeta p)).1 hm
  have hderiv := deriv_zpow_mul_eventuallyEq g hg_an hg_eq
  have hgne : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds
  have heq : (fun z ↦ (z - p) * (-deriv riemannZeta z / riemannZeta z))
      =ᶠ[𝓝[≠] p] fun z ↦ (-((m : ℂ) * g z + (z - p) * deriv g z)) / g z := by
    filter_upwards [hg_eq, hderiv, self_mem_nhdsWithin, hgne] with z hz hdz hz_ne hgz
    have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz_ne
    rw [hz, hdz]; simp only [Pi.mul_apply, smul_eq_mul, zpow_sub_one₀ hzp]; field_simp
  refine Tendsto.congr' heq.symm ?_
  have tg : Tendsto g (𝓝[≠] p) (𝓝 (g p)) := hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have tg' : Tendsto (deriv g) (𝓝[≠] p) (𝓝 (deriv g p)) :=
    hg_an.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have tzp : Tendsto (fun z : ℂ ↦ z - p) (𝓝[≠] p) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by
      have : Tendsto (fun z : ℂ ↦ z - p) (𝓝 p) (𝓝 (p - p)) := Continuous.tendsto (by fun_prop) p
      simpa using this)
  have hnum : Tendsto (fun z ↦ (m : ℂ) * g z + (z - p) * deriv g z) (𝓝[≠] p)
      (𝓝 ((m : ℂ) * g p)) := by
    simpa using (tendsto_const_nhds.mul tg).add (tzp.mul tg')
  have hlim := (hnum.neg).div tg hg_ne
  rwa [show -((m : ℂ) * g p) / g p = -(m : ℂ) by field_simp] at hlim

/-- Side identification: the rectangle integral of `f` over the box `[-a,1+a]×[-T,T]`
splits into the two vertical and two horizontal pieces appearing in eq. (12). -/
theorem rectangleIntegral'_eq12 (f : ℂ → ℂ) {a T : ℝ} (hTT : -T ≤ T) (ha : -a ≤ 1 + a) :
    RectangleIntegral' f ((-a : ℝ) - T * I) ((1 + a : ℝ) + T * I)
      = (1 / (2 * (Real.pi : ℂ))) * (∫ t in Ioo (-T) T, f ((1 + a : ℝ) + t * I))
        - (1 / (2 * (Real.pi : ℂ))) * (∫ t in Ioo (-T) T, f ((-a : ℝ) + t * I))
        - (1 / (2 * (Real.pi : ℂ) * I)) * (∫ σ in Ioo (-a) (1 + a), f ((σ : ℝ) + T * I))
        + (1 / (2 * (Real.pi : ℂ) * I)) * (∫ σ in Ioo (-a) (1 + a), f ((σ : ℝ) + (-T : ℝ) * I)) := by
  have hzre : ((-a : ℝ) - (T : ℂ) * I).re = -a := by simp
  have hzim : ((-a : ℝ) - (T : ℂ) * I).im = -T := by simp
  have hwre : ((1 + a : ℝ) + (T : ℂ) * I).re = 1 + a := by simp
  have hwim : ((1 + a : ℝ) + (T : ℂ) * I).im = T := by simp
  unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral
  rw [hzre, hzim, hwre, hwim]
  rw [intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le ha,
      intervalIntegral.integral_of_le hTT, intervalIntegral.integral_of_le hTT]
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Residue value (Part 4, with the analytic cofactor `Φ(-·)`): the residue of
`s ↦ (-ζ'/ζ)(s)·Φ(-s)` at `p` equals `-order(ζ, p)·Φ(-p)`. -/
theorem residue_neg_zeta_logDeriv_mul {p : ℂ} {m : ℤ} {Φ : ℂ → ℂ}
    (hm : meromorphicOrderAt riemannZeta p = m) (hΦ : ContinuousAt Φ (-p)) :
    residue (fun s ↦ (-deriv riemannZeta s / riemannZeta s) * Φ (-s)) p = -(m : ℂ) * Φ (-p) := by
  apply residue_eq_of_tendsto
  have hΦt : Tendsto (fun z ↦ Φ (-z)) (𝓝[≠] p) (𝓝 (Φ (-p))) :=
    (hΦ.comp continuous_neg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  refine ((tendsto_sub_mul_neg_zeta_logDeriv hm).mul hΦt).congr (fun z ↦ ?_)
  ring

/-- Finiteness (residue-theorem hyp B1): the rectangle `[-a,1+a]×[-T,T]` meets only finitely
many zeros of `ζ` (the rectangle is compact). -/
theorem rectangle_inter_zeroes_finite {a T : ℝ} :
    (Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I) ∩
      riemannZeta.zeroes).Finite :=
  riemannZeta.zeroes_on_Compact_finite'
    (IsCompact.reProdIm isCompact_uIcc isCompact_uIcc)

/-- For `s₀` in the box `[-a,1+a]×[-T,T]` (with `0<a<b`), the reflected point `-s₀` lies in the
analyticity strip `-(1+b) < Re s < b` of `Φ`. -/
private lemma eq12_neg_mem_strip {a b T : ℝ} (ha : 0 < a) (hab : a < b) {s₀ : ℂ}
    (hs₀ : s₀ ∈ Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I)) :
    (-s₀) ∈ {s : ℂ | -(1 + b) < s.re ∧ s.re < b} := by
  rw [Rectangle, mem_reProdIm] at hs₀
  have hre := hs₀.1
  have hz : ((-a : ℝ) - (T : ℂ) * I).re = -a := by simp
  have hw : (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).re = 1 + a := by simp
  rw [hz, hw, Set.uIcc_of_le (by linarith)] at hre
  obtain ⟨hlo, hhi⟩ := hre
  refine ⟨?_, ?_⟩ <;> simp only [Complex.neg_re] <;> linarith

/-- The eq.(12) integrand `f(s) = (-ζ'/ζ)(s)·Φ(-s)` is meromorphic on the rectangle
`[-a,1+a]×[-T,T]`. -/
theorem meromorphicOn_eq12_integrand {Φ : ℂ → ℂ} {b : ℝ}
    (hΦ : AnalyticOnNhd ℂ Φ {s : ℂ | -(1 + b) < s.re ∧ s.re < b})
    {a T : ℝ} (ha : 0 < a) (hab : a < b) :
    MeromorphicOn (fun s ↦ (-deriv riemannZeta s / riemannZeta s) * Φ (-s))
      (Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I)) := by
  intro s₀ hs₀
  have hΦan : AnalyticAt ℂ Φ (-s₀) := hΦ (-s₀) (eq12_neg_mem_strip ha hab hs₀)
  have hneg : AnalyticAt ℂ (fun s : ℂ ↦ -s) s₀ := analyticAt_id.neg
  have hΦneg : MeromorphicAt (fun s ↦ Φ (-s)) s₀ := (hΦan.comp hneg).meromorphicAt
  exact (((meromorphicAt_riemannZeta s₀).deriv.neg).div (meromorphicAt_riemannZeta s₀)).mul hΦneg

/-- The eq.(12) integrand has at most simple poles on the rectangle: its meromorphic order is
`≥ -1` at every point (the `-ζ'/ζ` factor contributes `≥ -1`, the analytic `Φ(-·)` factor `≥ 0`). -/
theorem hasSimplePolesOn_eq12_integrand {Φ : ℂ → ℂ} {b : ℝ}
    (hΦ : AnalyticOnNhd ℂ Φ {s : ℂ | -(1 + b) < s.re ∧ s.re < b})
    {a T : ℝ} (ha : 0 < a) (hab : a < b) :
    HasSimplePolesOn (fun s ↦ (-deriv riemannZeta s / riemannZeta s) * Φ (-s))
      (Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I)) := by
  intro s₀ hs₀
  have hΦan : AnalyticAt ℂ Φ (-s₀) := hΦ (-s₀) (eq12_neg_mem_strip ha hab hs₀)
  have hneg : AnalyticAt ℂ (fun s : ℂ ↦ -s) s₀ := analyticAt_id.neg
  have hΦneg_an : AnalyticAt ℂ (fun s ↦ Φ (-s)) s₀ := hΦan.comp hneg
  have hmero1 : MeromorphicAt (fun w ↦ -deriv riemannZeta w / riemannZeta w) s₀ :=
    (meromorphicAt_riemannZeta s₀).deriv.neg.div (meromorphicAt_riemannZeta s₀)
  have h1 := neg_one_le_meromorphicOrderAt_neg_zeta_logDeriv s₀
  have h2 : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun s ↦ Φ (-s)) s₀ :=
    hΦneg_an.meromorphicOrderAt_nonneg
  rw [show (fun s ↦ (-deriv riemannZeta s / riemannZeta s) * Φ (-s))
      = (fun w ↦ -deriv riemannZeta w / riemannZeta w) * (fun s ↦ Φ (-s)) from rfl,
    meromorphicOrderAt_mul hmero1 hΦneg_an.meromorphicAt]
  calc ((-1 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + 0 := by rw [add_zero]
    _ ≤ _ := add_le_add h1 h2

/-- At a point of the box where `ζ ≠ 0` and `s ≠ 1`, the eq.(12) integrand is analytic, so its
meromorphic order is non-negative (no pole). -/
theorem eq12_meromorphicOrderAt_nonneg_of_ne {Φ : ℂ → ℂ} {b : ℝ}
    (hΦ : AnalyticOnNhd ℂ Φ {s : ℂ | -(1 + b) < s.re ∧ s.re < b})
    {a T : ℝ} (ha : 0 < a) (hab : a < b) {s : ℂ}
    (hsbox : s ∈ Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I))
    (hζ_ne : riemannZeta s ≠ 0) (hs1 : s ≠ 1) :
    0 ≤ meromorphicOrderAt (fun s ↦ (-deriv riemannZeta s / riemannZeta s) * Φ (-s)) s := by
  have hζ_an : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (Set.mem_compl_singleton_iff.mpr hs1)
  have hlog_an : AnalyticAt ℂ (fun w ↦ -deriv riemannZeta w / riemannZeta w) s :=
    (hζ_an.deriv.neg).div hζ_an hζ_ne
  have hΦneg_an : AnalyticAt ℂ (fun s ↦ Φ (-s)) s :=
    (hΦ (-s) (eq12_neg_mem_strip ha hab hsbox)).comp analyticAt_id.neg
  exact (hlog_an.mul hΦneg_an).meromorphicOrderAt_nonneg

/-- No poles on the rectangle border (residue-theorem hyp B2/B3): given that `ζ` is non-zero and
the point is `≠ 1` on the entire border, the eq.(12) integrand is analytic there, hence has
non-negative order, so the border is disjoint from the pole set. -/
theorem eq12_no_border_poles {Φ : ℂ → ℂ} {b : ℝ}
    (hΦ : AnalyticOnNhd ℂ Φ {s : ℂ | -(1 + b) < s.re ∧ s.re < b})
    {a T : ℝ} (ha : 0 < a) (hab : a < b)
    (hborder : ∀ s ∈ RectangleBorder ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I),
        riemannZeta s ≠ 0 ∧ s ≠ 1) :
    Disjoint (RectangleBorder ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I))
      {s | meromorphicOrderAt
        (fun s ↦ (-deriv riemannZeta s / riemannZeta s) * Φ (-s)) s < 0} := by
  rw [Set.disjoint_left]
  intro s hs_border hs_pole
  simp only [Set.mem_setOf_eq] at hs_pole
  obtain ⟨hζ_ne, hs1⟩ := hborder s hs_border
  have hs_rect : s ∈ Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I) :=
    rectangleBorder_subset_rectangle _ _ hs_border
  exact absurd hs_pole
    (not_lt.mpr (eq12_meromorphicOrderAt_nonneg_of_ne hΦ ha hab hs_rect hζ_ne hs1))

/-- `zeroes_sum` over a finite zero-rectangle is the finite sum over `hfin.toFinset`. -/
theorem zeroes_sum_eq_toFinset_sum {α : Type*} [RCLike α] {I J : Set ℝ} (g : ℂ → α)
    (hfin : (riemannZeta.zeroes_rect I J).Finite) :
    riemannZeta.zeroes_sum I J g = ∑ z ∈ hfin.toFinset, g z * (riemannZeta.order z : α) := by
  rw [riemannZeta.zeroes_sum, ← Finset.tsum_subtype' hfin.toFinset
    (fun z => g z * (riemannZeta.order z : α)), hfin.coe_toFinset]

/-- Part 5 (residue bookkeeping): the sum of residues of the eq.(12) integrand `f` over the poles
inside the rectangle equals `Φ(-1) - zeroes_sum`. The two pole contributions are `s = 1`
(residue `Φ(-1)`) and the non-trivial zeros `ρ` (residue `-ord(ρ)·Φ(-ρ)`); the set-characterization
of the pole set and the residue values are supplied at the call site. -/
theorem sumResiduesIn_eq12_eq {f Φ : ℂ → ℂ} {a T : ℝ}
    (hf_mero : MeromorphicOn f (Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I)))
    (hfin : (riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.Ioo (-T) T)).Finite)
    (h1mem : (1 : ℂ) ∈ Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I))
    (hZsub : (riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.Ioo (-T) T) : Set ℂ) ⊆
      Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I))
    (h1notZ : (1 : ℂ) ∉ riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.Ioo (-T) T))
    (hset : Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I) ∩
          {s | meromorphicOrderAt f s < 0}
        = insert (1 : ℂ) (riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.Ioo (-T) T)) ∩
          {s | meromorphicOrderAt f s < 0})
    (hres1 : residue f 1 = Φ (-1))
    (hresZ : ∀ ρ ∈ riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.Ioo (-T) T),
      residue f ρ = -(riemannZeta.order ρ : ℂ) * Φ (-ρ)) :
    sumResiduesIn f (Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I) ∩
        {s | meromorphicOrderAt f s < 0})
      = Φ (-1) - riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Ioo (-T) T) (fun ρ ↦ Φ (-ρ)) := by
  have h1notZF : (1 : ℂ) ∉ hfin.toFinset := by rw [hfin.mem_toFinset]; exact h1notZ
  -- Step 1: replace the pole-set sum by the sum over `{1} ∪ Z`.
  rw [sumResiduesIn_inter_eq_of_set_eq hset ?_]
  · -- Step 2: evaluate the finite sum over `insert 1 Z`.
    rw [show insert (1 : ℂ) (riemannZeta.zeroes_rect (Set.Ioo 0 1) (Set.Ioo (-T) T))
          = ((insert (1 : ℂ) hfin.toFinset : Finset ℂ) : Set ℂ) by
          rw [Finset.coe_insert, hfin.coe_toFinset], sumResiduesIn, Finset.tsum_subtype',
      Finset.sum_insert h1notZF, hres1,
      zeroes_sum_eq_toFinset_sum (fun ρ ↦ Φ (-ρ)) hfin]
    have hsum : ∑ z ∈ hfin.toFinset, residue f z
        = ∑ z ∈ hfin.toFinset, -(Φ (-z) * (riemannZeta.order z : ℂ)) :=
      Finset.sum_congr rfl fun z hz => by
        rw [hresZ z (hfin.mem_toFinset.mp hz)]; ring
    rw [hsum, Finset.sum_neg_distrib]
    ring
  · -- residues vanish at non-pole points of `{1} ∪ Z`.
    intro s hs hs_not
    have hsbox : s ∈ Rectangle ((-a : ℝ) - (T : ℂ) * I) ((1 + a : ℝ) + (T : ℂ) * I) := by
      rcases Set.mem_insert_iff.mp hs with h1 | hZ
      · rw [h1]; exact h1mem
      · exact hZsub hZ
    have hord : 0 ≤ meromorphicOrderAt f s := not_lt.mp (by simpa using hs_not)
    exact residue_eq_zero_of_not_pole_of_meromorphicAt (hf_mero s hsbox) hord
