module

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (sorry-free prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
public import Zeta23.Prelude.InstancePriorities
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Data.Rat.Cast.OfScientific
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall hyp_r))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS

theorem borelCaratheodory' {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn, fun z hz => by rw [Set.mem_setOf_eq]; linarith [realPartBounded z hz], Rpos, by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hyp_z ) hyp_r ), zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε );
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)

lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]

lemma DerivativeBound {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory' Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr

theorem BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by
    have h₁ : R - (R + r) / 2 = (R - r) / 2 := by ring
    have h₂ : (R + r) / 2 - r = (R - r) / 2 := by ring
    rw [h₁, h₂]
    field_simp [sub_ne_zero.mpr (ne_of_gt hyp_r)]
    <;> ring
  calc ‖deriv f z‖
      _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
          DerivativeBound Mpos rpos (by linarith) (by linarith) analytic_f zeroAtZero realPartBounded hyp_z
      _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
          have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
          rw [this]; bound

theorem LogOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  obtain ⟨J_B, hJB⟩ : ∃ J_B : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R, (HasDerivAt J_B (deriv B z / B z) z)) ∧ J_B 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (BanalyticOnNhdOfDR.deriv.mono Metric.ball_subset_closedBall).div
        (BanalyticOnNhdOfDR.mono Metric.ball_subset_closedBall)
        (fun z hz => Bnonzero z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have hJB_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have hH_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (hJB_deriv z hz)
      convert! this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (Bnonzero z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have hH_const : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have h_diffOn : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (hH_deriv z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) h_diffOn ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (hH_deriv x hx).hasFDerivAt.fderiv
    have h_exp_re : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := hH_const z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (Bnonzero z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := Bnonzero z (Metric.ball_subset_closedBall hz)
    have hB0 := Bnonzero 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← h_exp_re z hz, Real.log_exp]
  have hmem : ∀ z, z ∈ Metric.ball (0 : ℂ) r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨J_B, ?_, hJB.2.1, ?_, hJB.2.2⟩
  · intro z hz
    exact DifferentiableOn.analyticAt (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt) (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · intro z hz
    exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv

theorem LogOfAnalyticFunction' {r' r R : ℝ} {B : ℂ → ℂ}
    (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) r, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 r)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r', (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 r, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  have BanalyticOnNhdOfDr : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) r) := BanalyticOnNhdOfDR.mono (Metric.closedBall_subset_closedBall r_lt_R.le)
  exact LogOfAnalyticFunction r'_pos r'_lt_r BanalyticOnNhdOfDr Bnonzero

def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}

lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ}
    (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) :
    (SetOfZeros r f).Finite := by
  apply Set.Finite.subset finiteZeros
  unfold SetOfZeros
  refine setOf_subset_setOf.mpr ?_
  intro z hz
  exact ⟨by linarith, hz.2⟩

open Classical
noncomputable def ZeroFactor (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0

lemma ZeroFactorization {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by
  have zero_mem_closedBall : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero, norm_zero]
    exact zero_le_one
  have ρ_mem_closedBall : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero]
    linarith[hρ.1]
  have orderAtZeroIsZero : analyticOrderAt f 0 = 0 := by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1 ↦ hf_neq_zero_at_zero a)
  have finiteOrder : analyticOrderAt f ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfAnalytic (Metric.isPreconnected_closedBall) zero_mem_closedBall ρ_mem_closedBall (lt_top_iff_ne_top.mp ?_)
    rw[orderAtZeroIsZero]
    exact ENat.top_pos
  have AnalyticAt_ρ : AnalyticAt ℂ f ρ := by exact (hfAnalytic ρ ρ_mem_closedBall)
  obtain ⟨h_ρ, h_ρ_neq_zero_at_zero, f_eq⟩ := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose_spec
  set g := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose
  refine ⟨g, h_ρ, h_ρ_neq_zero_at_zero, ?_, f_eq⟩
  simp only [ZeroFactor, AnalyticAt_ρ, ↓reduceDIte, ne_eq, finiteOrder, not_false_eq_true,
    smul_eq_mul, g]

noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      ZeroFactor f z / ∏ ρ ∈ (finite_zeros_mono.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (finite_zeros_mono.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1

lemma analyticAt_finset_prod_sub_pow (s : Finset ℂ) (g : ℂ → ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z => ∏ ρ ∈ s, (z - ρ) ^ g ρ) w := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a s' hne ih =>
    have : (fun z => ∏ ρ ∈ insert a s', (z - ρ) ^ g ρ) = fun z => (z - a) ^ g a * ∏ ρ ∈ s', (z - ρ) ^ g ρ :=
      funext fun z => Finset.prod_insert hne
    rw [this]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih

lemma CfAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  unfold Cf
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    by_cases w_in_zeros : w ∈ SetOfZeros r f
    · obtain ⟨h_w, hh_w_analytic, hh_w_w_ne_zero, hh_w_eq⟩ := ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith))) hf_neq_zero_at_zero w_in_zeros;
      have h_eq : ∀ᶠ z in nhds w, (if h : z ∈ SetOfZeros r f then ZeroFactor f z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {z}, (z - ρ) ^ analyticOrderNatAt f ρ else f z / ∏ ρ ∈ finite_zeros_mono.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ) = h_w z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [ hh_w_eq.2, hh_w_analytic.continuousAt.eventually_ne hh_w_w_ne_zero ] with z hz hz';
        by_cases h : z = w
        · subst h
          rw [dif_pos w_in_zeros]
          congr 1
          exact hh_w_eq.1
        · have z_not_in : z ∉ SetOfZeros r f := by
            intro hmem
            have hfz : f z = 0 := hmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne h)) hz')
          rw [dif_neg z_not_in, hz]
          have hw_mem : w ∈ finite_zeros_mono.toFinset := finite_zeros_mono.mem_toFinset.mpr w_in_zeros
          rw [Finset.prod_eq_prod_sdiff_singleton_mul hw_mem (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ)]
          rw [mul_comm ((z - w) ^ analyticOrderNatAt f w) (h_w z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne h))]
      apply hh_w_analytic.div _ _ |> fun h => h.congr _;
      · use fun z => ∏ ρ ∈ finite_zeros_mono.toFinset \ { w }, ( z - ρ ) ^ analyticOrderNatAt f ρ;
      · exact analyticAt_finset_prod_sub_pow _ _ _
      · simp only [Finset.prod_eq_zero_iff, ne_eq, pow_eq_zero_iff', Finset.mem_sdiff, Finite.mem_toFinset, Finset.mem_singleton, not_exists, not_and,
          Decidable.not_not, and_imp]
        intro x _ h_ne_w
        exact fun h_eq_w => absurd (sub_eq_zero.mp h_eq_w).symm h_ne_w
      · filter_upwards [ h_eq ] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z => f z / ∏ ρ ∈ finite_zeros_mono.toFinset, ( z - ρ ) ^ analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact hfAnalytic w ( Metric.mem_closedBall.mpr <| le_trans hw.out <| by linarith )
        · exact analyticAt_finset_prod_sub_pow _ _ _
        · simp only [ ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
          sub_eq_zero, ↓existsAndEq, true_and, not_and, Decidable.not_not]
          exact fun h => absurd h w_in_zeros
      · filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr finite_zeros_mono.isClosed ) w_in_zeros ] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticAt_const

noncomputable def BlaschkeB (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    (Cf r f) z * (∏ ρ ∈ finite_zeros_mono.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1

lemma BlaschkeAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (BlaschkeB r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  unfold BlaschkeB
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    refine AnalyticOnNhd.mul (CfAnalytic r_lt_R R_lt_one hfAnalytic hf_neq_zero_at_zero) (Finset.analyticOnNhd_fun_prod (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticOnNhd_const

lemma BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖BlaschkeB r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have zero_not_zero : ¬(0 ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp hf_neq_zero_at_zero
  unfold BlaschkeB Cf
  simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, zero_not_zero, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr hf_neq_zero_at_zero)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]

lemma norm_fOfZero_le_norm_BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖f 0‖ ≤ ‖BlaschkeB r R f 0‖ := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  rw [BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf_neq_zero_at_zero, ← mul_one ‖f 0‖]
  refine mul_le_mul (by rw[mul_one]) ?_ (zero_le_one) (mul_nonneg (norm_nonneg (f 0)) zero_le_one)
  rw [← Finset.prod_const_one (s := (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset)]
  apply Finset.prod_le_prod₀
  · intro ρ hρ
    exact zero_le_one
  · intro ρ hρ
    simp only [SetOfZeros, Finite.mem_toFinset, mem_setOf_eq] at hρ
    apply one_le_pow₀
    rw[one_le_div]
    · linarith
    · rw [norm_pos_iff]
      by_contra h
      rw [h] at hρ
      exact hf_neq_zero_at_zero hρ.2

lemma DiskBound {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) (fz_bound : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖BlaschkeB r R f z‖ ≤ B := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.norm_le_of_norm_le_on_sphere (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic hf_neq_zero_at_zero)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have hw_not_in : ¬(w ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    intro le_r
    linarith
  have Bf_eq_f_at_w : ‖BlaschkeB r R f w‖ = ‖f w‖ := by
    unfold BlaschkeB Cf
    simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, hw_not_in, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases fw_normZero : ‖f w‖ = 0
    · exact Or.inr fw_normZero
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' hw'_in
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at hw'_in
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => hw_not_in (h ▸ hw'_in)))
  rw[Bf_eq_f_at_w]
  exact fz_bound w (le_of_eq hw)

lemma BlaschkeNonzero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r, BlaschkeB r R f z ≠ 0 := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  intro z hz
  have hz_norm_le_r : ‖z‖ ≤ r := by rwa [mem_closedBall_iff_norm, sub_zero] at hz
  have hz_norm_lt_R : ‖z‖ < R := by linarith
  let hFin := finiteSetOfZeros_mono r_lt_one finiteZeros
  have hBProd : ∏ ρ ∈ hFin.toFinset,
      (↑R - z * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    apply pow_ne_zero
    norm_num [ sub_eq_zero, Complex.ext_iff ];
    simp only [SetOfZeros, Finite.mem_toFinset, mem_setOf_eq] at hρ
    rw [ eq_div_iff ] <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
    · rw [Real.sqrt_lt' (by linarith)] at hz_norm_lt_R
      rw [ Real.sqrt_le_iff ] at hρ
      exact fun h => absurd h ( by nlinarith [ sq_nonneg ( z.re - ρ.re ), sq_nonneg ( z.im - ρ.im ), mul_lt_mul_of_pos_left r_lt_R R_pos ] )
    · linarith
  unfold BlaschkeB Cf
  by_cases z_in_zeros : z ∈ SetOfZeros r f
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    obtain ⟨_, _, hne, heq⟩ :=
      ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith)))
        hf_neq_zero_at_zero z_in_zeros
    rw [heq.1]
    refine mul_ne_zero (div_ne_zero hne (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr fun h =>
        (Finset.mem_sdiff.mp hρ).2 (Finset.mem_singleton.mpr h.symm)))) hBProd
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    refine mul_ne_zero (div_ne_zero (fun hfz => z_in_zeros ⟨hz_norm_le_r, hfz⟩)
      (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
        pow_ne_zero _ (sub_ne_zero.mpr fun h => z_in_zeros (h ▸ hFin.mem_toFinset.mp hρ)))) hBProd

theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hf0_ne_zero : f 0 ≠ 0 := by rw [hf0_eq_one]; exact one_ne_zero
  have blaschke_eq := BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf0_ne_zero
  rw[hf0_eq_one, norm_one, one_mul] at blaschke_eq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod₀
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have hρ_mem := (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (hρ_mem.1)
        rintro rfl
        exact hf0_ne_zero hρ_mem.2
    _ ≤ B := by
      rw[← blaschke_eq]
      exact DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic
        hf0_ne_zero fz_bound (Metric.mem_closedBall_self (le_of_lt R_pos))
