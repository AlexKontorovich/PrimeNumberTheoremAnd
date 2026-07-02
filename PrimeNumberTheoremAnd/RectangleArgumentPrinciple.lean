import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Divisor
import PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorSupport
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Rectangle argument-principle infrastructure

This file isolates the local logarithmic-derivative residue calculation and the
rectangle-facing finite divisor sum used by the Kadiri contour lanes.
-/

open Complex Filter Topology Set BigOperators Asymptotics

open scoped Interval

noncomputable section

private lemma tendsto_mul_self_of_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c) := by
  have hp_tendsto :
      Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    simpa using
      ((continuous_id.sub continuous_const).continuousAt.continuousWithinAt.tendsto :
        Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 (p - p)))
  have hp_small :
      (fun z : ℂ => z - p) =o[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (isLittleO_one_iff ℂ).2 hp_tendsto
  have hrem_tendsto :
      Tendsto
        (fun z : ℂ => (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 0) := by
    simpa using hp_small.mul_isBigO h
  have hprincipal :
      (fun z : ℂ => (z - p) * (c / (z - p))) =ᶠ[𝓝[≠] p] fun _ : ℂ => c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    field_simp [sub_ne_zero.mpr hz]
  have hprincipal_tendsto :
      Tendsto (fun z : ℂ => (z - p) * (c / (z - p))) (𝓝[≠] p) (𝓝 c) :=
    tendsto_const_nhds.congr' hprincipal.symm
  have hsum_tendsto :
      Tendsto
        (fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 (c + 0)) :=
    hprincipal_tendsto.add hrem_tendsto
  have hsum :
      (fun z : ℂ => (z - p) * f z) =ᶠ[𝓝[≠] p]
        fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z) := by
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring
  simpa using hsum_tendsto.congr' hsum.symm

lemma logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg_analytic, hg_ne, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  let F : ℂ → ℂ := fun s => (s - p) ^ n * g s
  have hfg_ne : f =ᶠ[𝓝[≠] p] F := by
    filter_upwards [hfg] with s hs
    simpa [F, smul_eq_mul] using hs
  have hderiv_ne : deriv f =ᶠ[𝓝[≠] p] deriv F := hfg_ne.nhdsNE_deriv
  have hg_nonzero_ne : ∀ᶠ s in 𝓝[≠] p, g s ≠ 0 := by
    exact (hg_analytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg_ne
      |>.filter_mono nhdsWithin_le_nhds
  have hg_analytic_ne : ∀ᶠ s in 𝓝[≠] p, AnalyticAt ℂ g s := by
    exact hg_analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog_eq :
      (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) =ᶠ[𝓝[≠] p] logDeriv g := by
    filter_upwards [hfg_ne, hderiv_ne, self_mem_nhdsWithin, hg_nonzero_ne, hg_analytic_ne]
      with s hfs hderiv hs_ne hgs_ne hgs_analytic
    have hpow_ne : (s - p) ^ n ≠ 0 := zpow_ne_zero n (sub_ne_zero.mpr hs_ne)
    have hdiff_pow : DifferentiableAt ℂ (fun z : ℂ => (z - p) ^ n) s := by
      exact ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - p) s)).zpow
        (Or.inl (sub_ne_zero.mpr hs_ne))
    have hlogF :
        logDeriv F s =
          logDeriv (fun z : ℂ => (z - p) ^ n) s + logDeriv g s := by
      exact logDeriv_mul (f := fun z : ℂ => (z - p) ^ n) (g := g) s
        hpow_ne hgs_ne hdiff_pow hgs_analytic.differentiableAt
    have hlogpow : logDeriv (fun z : ℂ => (z - p) ^ n) s = (n : ℂ) / (s - p) := by
      rw [logDeriv_fun_zpow (f := fun z : ℂ => z - p) (x := s) (by fun_prop) n]
      simp [logDeriv_apply, div_eq_mul_inv]
    simp only [Pi.sub_apply]
    calc
      logDeriv f s - (n : ℂ) / (s - p)
          = logDeriv F s - (n : ℂ) / (s - p) := by
            simp [logDeriv_apply, hfs, hderiv]
      _ = logDeriv g s := by
            rw [hlogF, hlogpow]
            ring
  have hderiv_bounded : deriv g =O[𝓝 p] (1 : ℂ → ℂ) :=
    hg_analytic.deriv.continuousAt.norm.isBoundedUnder_le.isBigO_one ℂ
  have hinv_bounded : g⁻¹ =O[𝓝 p] (1 : ℂ → ℂ) :=
    (hg_analytic.continuousAt.inv₀ hg_ne).norm.isBoundedUnder_le.isBigO_one ℂ
  have hlog_bounded : logDeriv g =O[𝓝 p] (1 : ℂ → ℂ) := by
    have hmul_bounded :
        (deriv g * g⁻¹) =O[𝓝 p] ((1 : ℂ → ℂ) * (1 : ℂ → ℂ)) :=
      Asymptotics.IsBigO.mul hderiv_bounded hinv_bounded
    have hmul_bounded' :
        (fun x => deriv g x * (g x)⁻¹) =O[𝓝 p] (1 : ℂ → ℂ) := by
      refine hmul_bounded.congr ?_ ?_
      · intro x
        rfl
      · intro x
        simp
    change (fun x => deriv g x / g x) =O[𝓝 p] (1 : ℂ → ℂ)
    simpa only [div_eq_mul_inv] using hmul_bounded'
  exact hlog_eq.trans_isBigO (hlog_bounded.mono nhdsWithin_le_nhds)

theorem logDeriv_residue_eq_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    residue (logDeriv f) p = (n : ℂ) :=
  residue_eq_of_tendsto
    (tendsto_mul_self_of_sub_principal_isBigO_one
      (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord))

private lemma meromorphicOrderAt_nonneg_of_isBigO_one
    {f : ℂ → ℂ} {p : ℂ} (_hf : MeromorphicAt f p)
    (hO : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    0 ≤ meromorphicOrderAt f p := by
  by_contra hnonneg
  have hneg : meromorphicOrderAt f p < 0 := lt_of_not_ge hnonneg
  have hnorm :
      Tendsto (fun z : ℂ => ‖f z‖) (𝓝[≠] p) Filter.atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop hnorm) hO.isBoundedUnder_le

private lemma meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (hf : MeromorphicAt f p) (hc : c ≠ 0)
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    meromorphicOrderAt f p = (-1 : ℤ) := by
  let principal : ℂ → ℂ := fun z => c / (z - p)
  let rem : ℂ → ℂ := f - principal
  have hconst_mero : MeromorphicAt (fun _ : ℂ => c) p := MeromorphicAt.const c p
  have hlin_mero : MeromorphicAt (fun z : ℂ => z - p) p := by fun_prop
  have hprincipal_mero : MeromorphicAt principal p := hconst_mero.div hlin_mero
  have hrem_mero : MeromorphicAt rem p := hf.sub hprincipal_mero
  have hrem_nonneg : 0 ≤ meromorphicOrderAt rem p :=
    meromorphicOrderAt_nonneg_of_isBigO_one hrem_mero (by simpa [rem, principal] using h)
  have hprincipal_order : meromorphicOrderAt principal p = (-1 : ℤ) := by
    dsimp [principal]
    change meromorphicOrderAt ((fun _ : ℂ => c) / fun z : ℂ => z - p) p = (-1 : ℤ)
    rw [meromorphicOrderAt_div hconst_mero hlin_mero, meromorphicOrderAt_const,
      if_neg hc, meromorphicOrderAt_id_sub_const]
    norm_num
  have hlt : meromorphicOrderAt principal p < meromorphicOrderAt rem p := by
    rw [hprincipal_order]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by norm_num : (-1 : ℤ) < 0)) hrem_nonneg
  have hsum_order :
      meromorphicOrderAt (principal + rem) p = meromorphicOrderAt principal p :=
    meromorphicOrderAt_add_eq_left_of_lt hrem_mero hlt
  have hcongr : f =ᶠ[𝓝[≠] p] principal + rem := by
    filter_upwards with z
    dsimp [principal, rem]
    ring
  calc
    meromorphicOrderAt f p = meromorphicOrderAt (principal + rem) p :=
      meromorphicOrderAt_congr hcongr
    _ = meromorphicOrderAt principal p := hsum_order
    _ = (-1 : ℤ) := hprincipal_order

private lemma logDeriv_meromorphicOrderAt_nonneg_of_order_zero
    {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hlog : MeromorphicAt (logDeriv f) p)
    (hord : meromorphicOrderAt f p = (0 : WithTop ℤ)) :
    0 ≤ meromorphicOrderAt (logDeriv f) p := by
  have hO :=
    logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord
  have hO' : logDeriv f =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    exact hO.congr_left (by intro z; simp)
  exact meromorphicOrderAt_nonneg_of_isBigO_one hlog hO'

private lemma logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p) (hlog : MeromorphicAt (logDeriv f) p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) (hn : n ≠ 0) :
    meromorphicOrderAt (logDeriv f) p = (-1 : ℤ) := by
  have hO :=
    logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord
  exact meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one hlog
    (by exact_mod_cast hn) hO

theorem logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top
    {f : ℂ → ℂ} {R : Set ℂ}
    (hf : MeromorphicOn f R) (hlog : MeromorphicOn (logDeriv f) R)
    (hfinite_order : ∀ p ∈ R, meromorphicOrderAt f p ≠ ⊤) :
    HasSimplePolesOn (logDeriv f) R := by
  intro p hpR
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
  by_cases hn0 : n = 0
  · have hord0 : meromorphicOrderAt f p = (0 : WithTop ℤ) := by
      simpa [hn0] using hn.symm
    have hnonneg :=
      logDeriv_meromorphicOrderAt_nonneg_of_order_zero (hf p hpR) (hlog p hpR) hord0
    exact le_trans (WithTop.coe_le_coe.2 (by norm_num : (-1 : ℤ) ≤ 0)) hnonneg
  · have hneg_one :=
      logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero (hf p hpR) (hlog p hpR)
        hn.symm hn0
    rw [hneg_one]

theorem logDeriv_poles_eq_divisor_support
    {f : ℂ → ℂ} {R : Set ℂ}
    (hf : MeromorphicOn f R) (hlog : MeromorphicOn (logDeriv f) R)
    (hfinite_order : ∀ p ∈ R, meromorphicOrderAt f p ≠ ⊤) :
    R ∩ {p | meromorphicOrderAt (logDeriv f) p < 0} =
      (MeromorphicOn.divisor f R).support := by
  classical
  let D := MeromorphicOn.divisor f R
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpR, hpneg⟩
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
    by_cases hn0 : n = 0
    · have hord0 : meromorphicOrderAt f p = (0 : WithTop ℤ) := by
        simpa [hn0] using hn.symm
      have hnonneg :=
        logDeriv_meromorphicOrderAt_nonneg_of_order_zero (hf p hpR) (hlog p hpR) hord0
      exact False.elim (not_lt_of_ge hnonneg hpneg)
    · have hpD_ne : D p ≠ 0 := by
        change (MeromorphicOn.divisor f R) p ≠ 0
        rw [MeromorphicOn.divisor_apply hf hpR, ← hn]
        simp [hn0]
      simp [D, Function.mem_support, hpD_ne]
  · intro hpD
    have hpR : p ∈ R := (MeromorphicOn.divisor f R).supportWithinDomain hpD
    have hpD_ne : D p ≠ 0 := by
      simpa [D, Function.mem_support] using hpD
    change (MeromorphicOn.divisor f R) p ≠ 0 at hpD_ne
    rw [MeromorphicOn.divisor_apply hf hpR] at hpD_ne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hpD_ne (by rw [← hn]; simp [hn0])
    have hneg_one :=
      logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero (hf p hpR) (hlog p hpR)
        hn.symm hn0
    refine ⟨hpR, ?_⟩
    change meromorphicOrderAt (logDeriv f) p < 0
    rw [hneg_one]
    exact WithTop.coe_lt_coe.2 (by norm_num : (-1 : ℤ) < 0)

private theorem sumResiduesIn_eq_finset_of_finite {F : ℂ → ℂ} {S : Set ℂ}
    (hS : S.Finite) :
    sumResiduesIn F S = ∑ z ∈ hS.toFinset, residue F z := by
  let Sfin : Finset ℂ := hS.toFinset
  change sumResiduesIn F S = ∑ z ∈ Sfin, residue F z
  rw [sumResiduesIn]
  have hS_eq : S = (Sfin : Set ℂ) := hS.coe_toFinset.symm
  rw [hS_eq, tsum_fintype, ← Finset.sum_coe_sort Sfin]
  rfl

lemma divisor_support_rectangle_finite (f : ℂ → ℂ) (z w : ℂ) :
    (MeromorphicOn.divisor f (Rectangle z w)).support.Finite := by
  let R : Set ℂ := Rectangle z w
  let D := MeromorphicOn.divisor f R
  have hR_compact : IsCompact R := by
    exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
  have hfinite_inter :
      (R ∩ D.support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := f) (U := R) (K := R)
      hR_compact subset_rfl
  simpa [Set.inter_eq_right.mpr D.supportWithinDomain] using hfinite_inter

theorem rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
    {f : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hf : MeromorphicOn f (Rectangle z w))
    (hlog : MeromorphicOn (logDeriv f) (Rectangle z w))
    (hfinite_order : ∀ p ∈ Rectangle z w, meromorphicOrderAt f p ≠ ⊤)
    (hno_boundary :
      Disjoint (RectangleBorder z w) (MeromorphicOn.divisor f (Rectangle z w)).support) :
    RectangleIntegral' (logDeriv f) z w =
      ∑ p ∈
        ((divisor_support_rectangle_finite f z w).toFinset),
          ((MeromorphicOn.divisor f (Rectangle z w)) p : ℂ) := by
  classical
  let R : Set ℂ := Rectangle z w
  let D := MeromorphicOn.divisor f R
  have hsupport : D.support.Finite := divisor_support_rectangle_finite f z w
  have hlog_simple : HasSimplePolesOn (logDeriv f) R :=
    logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top hf hlog hfinite_order
  have hlog_poles_eq :
      R ∩ {s | meromorphicOrderAt (logDeriv f) s < 0} = D.support := by
    simpa [R, D] using
      logDeriv_poles_eq_divisor_support (f := f) (R := R) hf hlog hfinite_order
  have hlog_no_boundary :
      Disjoint (RectangleBorder z w) {s | meromorphicOrderAt (logDeriv f) s < 0} := by
    rw [Set.disjoint_left]
    intro s hs_border hs_log_pole
    have hsR : s ∈ R := by
      exact rectangleBorder_subset_rectangle z w hs_border
    have hsD : s ∈ D.support := by
      rw [← hlog_poles_eq]
      exact ⟨hsR, hs_log_pole⟩
    exact Set.disjoint_left.mp (by simpa [R, D] using hno_boundary) hs_border hsD
  have hlog_poles_finite :
      (Rectangle z w ∩ {s | meromorphicOrderAt (logDeriv f) s < 0}).Finite := by
    simpa [R, D, hlog_poles_eq] using hsupport
  have hrect :=
    RectangleIntegral'_eq_sumResiduesIn zRe_le_wRe zIm_le_wIm hlog hlog_no_boundary
      hlog_poles_finite hlog_simple
  rw [hrect, hlog_poles_eq, sumResiduesIn_eq_finset_of_finite hsupport]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpD : p ∈ D.support := by
    simpa [D] using (hsupport.mem_toFinset.mp hp)
  have hpR : p ∈ R := D.supportWithinDomain hpD
  have hpD_ne : D p ≠ 0 := by
    simpa [Function.mem_support] using hpD
  have horder_ne_zero_or_top :
      meromorphicOrderAt f p ≠ 0 ∧ meromorphicOrderAt f p ≠ ⊤ := by
    change (MeromorphicOn.divisor f R) p ≠ 0 at hpD_ne
    rw [MeromorphicOn.divisor_apply hf hpR] at hpD_ne
    constructor
    · intro hzero
      exact hpD_ne (by simp [hzero])
    · intro htop
      exact hpD_ne (by simp [htop])
  obtain ⟨n, hn⟩ :=
    WithTop.ne_top_iff_exists.mp horder_ne_zero_or_top.2
  have hres :
      residue (logDeriv f) p = (n : ℂ) :=
    logDeriv_residue_eq_meromorphicOrderAt (hf p hpR) hn.symm
  rw [hres]
  change (n : ℂ) = ((MeromorphicOn.divisor f R) p : ℂ)
  rw [MeromorphicOn.divisor_apply hf hpR, ← hn]
  simp

theorem rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt
    {f : ℂ → ℂ} {z w : ℂ} {argumentChange : ℝ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hf : MeromorphicOn f (Rectangle z w))
    (hlog : MeromorphicOn (logDeriv f) (Rectangle z w))
    (hfinite_order : ∀ p ∈ Rectangle z w, meromorphicOrderAt f p ≠ ⊤)
    (hno_boundary :
      Disjoint (RectangleBorder z w) (MeromorphicOn.divisor f (Rectangle z w)).support)
    (hargumentChange :
      (argumentChange : ℂ) =
        (2 * Real.pi : ℂ) * RectangleIntegral' (logDeriv f) z w) :
    argumentChange =
      2 * Real.pi *
        ∑ p ∈ (divisor_support_rectangle_finite f z w).toFinset,
          (((MeromorphicOn.divisor f (Rectangle z w)) p : ℤ) : ℝ) := by
  classical
  have hcomplex :
      (argumentChange : ℂ) =
        (2 * Real.pi : ℂ) *
          ∑ p ∈ (divisor_support_rectangle_finite f z w).toFinset,
            (((MeromorphicOn.divisor f (Rectangle z w)) p : ℤ) : ℂ) := by
    rw [hargumentChange]
    rw [rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt zRe_le_wRe zIm_le_wIm
      hf hlog hfinite_order hno_boundary]
  have hre := congrArg Complex.re hcomplex
  simpa [Finset.mul_sum, mul_assoc] using hre

end
