import PrimeNumberTheoremAnd.IEANTN.CH2.CH2
import PrimeNumberTheoremAnd.IEANTN.Kadiri
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder

namespace Kadiri

open Complex
open scoped Topology BigOperators

/-- Pointwise normal-form identity for a logarithmic derivative. -/
lemma model_logDeriv_eq {p z : ℂ} {m : ℤ} {g : ℂ → ℂ}
    (hz : z ≠ p) (hgz : g z ≠ 0) (hgz_an : AnalyticAt ℂ g z) :
    logDeriv (fun w : ℂ => (w - p) ^ m * g w) z =
      (m : ℂ) / (z - p) + logDeriv g z := by
  rw [logDeriv_mul]
  · rw [show logDeriv (fun w : ℂ => (w - p) ^ m) z = (m : ℂ) / (z - p) by
      rw [show (fun w : ℂ => (w - p) ^ m) =
          (fun u : ℂ => u ^ m) ∘ (fun w : ℂ => w - p) by rfl]
      rw [logDeriv_comp]
      · simp
      · exact differentiableAt_zpow.2 (Or.inl (sub_ne_zero.mpr hz))
      · fun_prop]
  · exact zpow_ne_zero m (sub_ne_zero.mpr hz)
  · exact hgz
  · exact DifferentiableAt.zpow (by fun_prop) (by simp [sub_ne_zero.mpr hz])
  · exact hgz_an.differentiableAt

/-- Normal-form model for the residue of a logarithmic derivative. -/
lemma model_logDeriv_tendsto_order {p : ℂ} {m : ℤ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g p) (hg_ne : g p ≠ 0) :
    Filter.Tendsto (fun z : ℂ => (z - p) *
        logDeriv (fun w : ℂ => (w - p) ^ m * g w) z)
      (𝓝[≠] p) (𝓝 (m : ℂ)) := by
  have hg_nonzero : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((hg.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg_ne)
  have hg_an : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z :=
    eventually_nhdsWithin_of_eventually_nhds hg.eventually_analyticAt
  have hlog :
      (fun z : ℂ => logDeriv (fun w : ℂ => (w - p) ^ m * g w) z) =ᶠ[𝓝[≠] p]
        fun z : ℂ => (m : ℂ) / (z - p) + logDeriv g z := by
    filter_upwards [self_mem_nhdsWithin, hg_nonzero, hg_an] with z hz hgz hgz_an
    exact model_logDeriv_eq hz hgz hgz_an
  have hlogg_cont : ContinuousAt (logDeriv g) p := by
    rw [logDeriv]
    exact (hg.deriv.continuousAt).div hg.continuousAt hg_ne
  have hsmall : Filter.Tendsto (fun z : ℂ => (z - p) * logDeriv g z)
      (𝓝[≠] p) (𝓝 0) := by
    have hz0 : Filter.Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
      simpa using ((continuous_id.sub continuous_const).continuousAt.continuousWithinAt.tendsto :
        Filter.Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 (p - p)))
    simpa using hz0.mul hlogg_cont.continuousWithinAt.tendsto
  have hprod :
      (fun z : ℂ => (z - p) * logDeriv (fun w : ℂ => (w - p) ^ m * g w) z)
        =ᶠ[𝓝[≠] p] fun z : ℂ => (m : ℂ) + (z - p) * logDeriv g z := by
    filter_upwards [self_mem_nhdsWithin, hlog] with z hz hlogz
    rw [hlogz]
    field_simp [sub_ne_zero.mpr hz]
  have htarget : Filter.Tendsto (fun z : ℂ => (m : ℂ) + (z - p) * logDeriv g z)
      (𝓝[≠] p) (𝓝 ((m : ℂ) + 0)) := by
    exact (tendsto_const_nhds (x := (m : ℂ))).add hsmall
  simpa using htarget.congr' hprod.symm

lemma meromorphicOrderAt_const_div_sub_ge_neg_one {p c : ℂ} :
    (-1 : ℤ) ≤ meromorphicOrderAt (fun z : ℂ => c / (z - p)) p := by
  by_cases hc : c = 0
  · rw [show (fun z : ℂ => c / (z - p)) = fun _ : ℂ => 0 by
      funext z
      simp [hc]]
    rw [show meromorphicOrderAt (fun _ : ℂ => (0 : ℂ)) p = ⊤ by
      rw [meromorphicOrderAt_eq_top_iff]
      simp]
    exact (le_top : ((-1 : ℤ) : WithTop ℤ) ≤ ⊤)
  · have horder : meromorphicOrderAt (fun z : ℂ => c / (z - p)) p = (-1 : ℤ) := by
      rw [show (fun z : ℂ => c / (z - p)) =
          (fun _ : ℂ => c) * (fun z : ℂ => (z - p) ^ (-1 : ℤ)) by
        funext z
        simp [div_eq_mul_inv]]
      rw [meromorphicOrderAt_mul_of_ne_zero
        (analyticAt_const (𝕜 := ℂ) (x := p) (v := c)) (by simpa using hc)]
      simpa using (meromorphicOrderAt_zpow_id_sub_const (𝕜 := ℂ) (x := p)
        (n := (-1 : ℤ)))
    rw [horder]

lemma meromorphicOrderAt_const_div_sub_eq_neg_one {p c : ℂ} (hc : c ≠ 0) :
    meromorphicOrderAt (fun z : ℂ => c / (z - p)) p = (-1 : ℤ) := by
  rw [show (fun z : ℂ => c / (z - p)) =
      (fun _ : ℂ => c) * (fun z : ℂ => (z - p) ^ (-1 : ℤ)) by
    funext z
    simp [div_eq_mul_inv]]
  rw [meromorphicOrderAt_mul_of_ne_zero
    (analyticAt_const (𝕜 := ℂ) (x := p) (v := c)) hc]
  simpa using (meromorphicOrderAt_zpow_id_sub_const (𝕜 := ℂ) (x := p)
    (n := (-1 : ℤ)))

lemma analyticAt_logDeriv_of_nonzero {g : ℂ → ℂ} {p : ℂ}
    (hg : AnalyticAt ℂ g p) (hg_ne : g p ≠ 0) :
    AnalyticAt ℂ (logDeriv g) p := by
  rw [logDeriv]
  exact hg.deriv.div hg hg_ne

/-- A logarithmic derivative has no pole worse than simple at any finite meromorphic order. -/
lemma meromorphicOrderAt_logDeriv_ge_neg_one_of_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = m) :
    (-1 : ℤ) ≤ meromorphicOrderAt (logDeriv f) p := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hderiv_eq : deriv f =ᶠ[𝓝[≠] p] deriv (fun w : ℂ => (w - p) ^ m * g w) :=
    Filter.EventuallyEq.nhdsNE_deriv hg_eq
  have hg_nonzero : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((hg_an.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg_ne)
  have hg_an' : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z :=
    eventually_nhdsWithin_of_eventually_nhds hg_an.eventually_analyticAt
  have hlog_eq : (fun z : ℂ => logDeriv f z) =ᶠ[𝓝[≠] p]
      fun z : ℂ => (m : ℂ) / (z - p) + logDeriv g z := by
    filter_upwards [self_mem_nhdsWithin, hg_eq, hderiv_eq, hg_nonzero, hg_an'] with
      z hz hfz hdz hgz hgz_an
    have hfg :
        logDeriv f z = logDeriv (fun w : ℂ => (w - p) ^ m * g w) z := by
      simp [logDeriv, hfz, hdz]
    rw [hfg]
    exact model_logDeriv_eq hz hgz hgz_an
  rw [meromorphicOrderAt_congr hlog_eq]
  have hterm : (-1 : ℤ) ≤ meromorphicOrderAt (fun z : ℂ => (m : ℂ) / (z - p)) p :=
    meromorphicOrderAt_const_div_sub_ge_neg_one
  have hlogg_an : AnalyticAt ℂ (logDeriv g) p :=
    analyticAt_logDeriv_of_nonzero hg_an hg_ne
  have hlogg : (-1 : ℤ) ≤ meromorphicOrderAt (logDeriv g) p := by
    exact le_trans (WithTop.coe_le_coe.mpr (by norm_num : (-1 : ℤ) ≤ 0))
      hlogg_an.meromorphicOrderAt_nonneg
  have hmero_term : MeromorphicAt (fun z : ℂ => (m : ℂ) / (z - p)) p := by
    fun_prop
  have hadd := meromorphicOrderAt_add hmero_term hlogg_an.meromorphicAt
  exact le_trans (le_min hterm hlogg) hadd

lemma meromorphicOrderAt_logDeriv_eq_neg_one_of_meromorphicOrderAt_ne_zero
    {f : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = m) (hm : m ≠ 0) :
    meromorphicOrderAt (logDeriv f) p = (-1 : ℤ) := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hderiv_eq : deriv f =ᶠ[𝓝[≠] p] deriv (fun w : ℂ => (w - p) ^ m * g w) :=
    Filter.EventuallyEq.nhdsNE_deriv hg_eq
  have hg_nonzero : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((hg_an.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg_ne)
  have hg_an' : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z :=
    eventually_nhdsWithin_of_eventually_nhds hg_an.eventually_analyticAt
  have hlog_eq : (fun z : ℂ => logDeriv f z) =ᶠ[𝓝[≠] p]
      fun z : ℂ => (m : ℂ) / (z - p) + logDeriv g z := by
    filter_upwards [self_mem_nhdsWithin, hg_eq, hderiv_eq, hg_nonzero, hg_an'] with
      z hz hfz hdz hgz hgz_an
    have hfg :
        logDeriv f z = logDeriv (fun w : ℂ => (w - p) ^ m * g w) z := by
      simp [logDeriv, hfz, hdz]
    rw [hfg]
    exact model_logDeriv_eq hz hgz hgz_an
  rw [meromorphicOrderAt_congr hlog_eq]
  have hterm : meromorphicOrderAt (fun z : ℂ => (m : ℂ) / (z - p)) p = (-1 : ℤ) :=
    meromorphicOrderAt_const_div_sub_eq_neg_one (by exact_mod_cast hm)
  have hlogg_an : AnalyticAt ℂ (logDeriv g) p :=
    analyticAt_logDeriv_of_nonzero hg_an hg_ne
  have hlt : meromorphicOrderAt (fun z : ℂ => (m : ℂ) / (z - p)) p <
      meromorphicOrderAt (logDeriv g) p := by
    rw [hterm]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0))
      hlogg_an.meromorphicOrderAt_nonneg
  simpa [hterm] using meromorphicOrderAt_add_eq_left_of_lt hlogg_an.meromorphicAt hlt

lemma meromorphicOrderAt_logDeriv_nonneg_of_meromorphicOrderAt_eq_zero
    {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = (0 : ℤ)) :
    0 ≤ meromorphicOrderAt (logDeriv f) p := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hderiv_eq : deriv f =ᶠ[𝓝[≠] p] deriv (fun w : ℂ => (w - p) ^ (0 : ℤ) * g w) :=
    Filter.EventuallyEq.nhdsNE_deriv hg_eq
  have hg_nonzero : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((hg_an.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg_ne)
  have hg_an' : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z :=
    eventually_nhdsWithin_of_eventually_nhds hg_an.eventually_analyticAt
  have hlog_eq : (fun z : ℂ => logDeriv f z) =ᶠ[𝓝[≠] p]
      fun z : ℂ => logDeriv g z := by
    filter_upwards [self_mem_nhdsWithin, hg_eq, hderiv_eq, hg_nonzero, hg_an'] with
      z hz hfz hdz hgz hgz_an
    have hfg :
        logDeriv f z = logDeriv (fun w : ℂ => (w - p) ^ (0 : ℤ) * g w) z := by
      simp [logDeriv, hfz, hdz]
    rw [hfg]
    have hmodel := model_logDeriv_eq (m := (0 : ℤ)) hz hgz hgz_an
    simp at hmodel ⊢
  rw [meromorphicOrderAt_congr hlog_eq]
  exact (analyticAt_logDeriv_of_nonzero hg_an hg_ne).meromorphicOrderAt_nonneg

lemma riemannZeta_eventually_ne_zero_punctured_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    ∀ᶠ z in 𝓝[≠] s, riemannZeta z ≠ 0 := by
  have hmem_compl_one : s ∈ ({1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff] using hs
  have hdisj :
      Disjoint (𝓝[≠] s) (Filter.principal (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)) := by
    exact (mem_codiscreteWithin.mp riemannZeta.zeroes_codiscreteWithin_compl_one)
      s hmem_compl_one
  have hnot_zeroes : (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)ᶜ ∈ 𝓝[≠] s :=
    Filter.disjoint_principal_right.mp hdisj
  have heventually_compl_one : ∀ᶠ z in 𝓝[≠] s, z ∈ ({1} : Set ℂ)ᶜ := by
    exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hmem_compl_one)
  filter_upwards [hnot_zeroes, heventually_compl_one] with z hznot hz_compl_one hzero
  have hz_zero : z ∈ riemannZeta.zeroes := by
    simpa [riemannZeta.zeroes] using hzero
  exact hznot ⟨hz_compl_one, by simpa using hz_zero⟩

lemma riemannZeta_meromorphicOrderAt_ne_top_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    meromorphicOrderAt riemannZeta s ≠ ⊤ := by
  have han := riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2
    (riemannZeta_eventually_ne_zero_punctured_of_ne_one hs)

lemma riemannZeta_finiteOrder_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    ∃ m : ℤ, meromorphicOrderAt riemannZeta s = m := by
  rcases WithTop.ne_top_iff_exists.mp
      (riemannZeta_meromorphicOrderAt_ne_top_of_ne_one hs) with ⟨m, hm⟩
  exact ⟨m, hm.symm⟩

lemma riemannZeta_meromorphicOrderAt_eq_zero_of_ne_one_of_ne_zero {s : ℂ}
    (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    meromorphicOrderAt riemannZeta s = (0 : ℤ) := by
  have han := riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)
  rw [han.meromorphicOrderAt_eq]
  simpa using (han.analyticOrderAt_eq_zero.mpr hζ)

lemma meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_nonneg_of_ne_zero
    {Φ : ℂ → ℂ} {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0)
    (hΦ : AnalyticAt ℂ (fun u => Φ (-u)) s) :
    (0 : WithTop ℤ) ≤
      meromorphicOrderAt (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) s := by
  have hζmero : MeromorphicAt riemannZeta s :=
    (riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)).meromorphicAt
  have hζorder : meromorphicOrderAt riemannZeta s = (0 : ℤ) :=
    riemannZeta_meromorphicOrderAt_eq_zero_of_ne_one_of_ne_zero hs hζ
  have hlog_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt (logDeriv riemannZeta) s :=
    meromorphicOrderAt_logDeriv_nonneg_of_meromorphicOrderAt_eq_zero hζmero hζorder
  have hlog_mero : MeromorphicAt (logDeriv riemannZeta) s := by
    rw [logDeriv]
    exact hζmero.deriv.div hζmero
  have hneg_mero : MeromorphicAt (fun u => -logDeriv riemannZeta u) s := by
    change MeromorphicAt (-(logDeriv riemannZeta)) s
    exact hlog_mero.neg
  have hcoeff_mero : MeromorphicAt (fun u => -(Φ (-u))) s :=
    hΦ.neg.meromorphicAt
  have hneg_nonneg :
      (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun u => -logDeriv riemannZeta u) s := by
    change (0 : WithTop ℤ) ≤ meromorphicOrderAt (-(logDeriv riemannZeta)) s
    rw [(meromorphicOrderAt_neg (f := logDeriv riemannZeta) (x := s)).symm]
    exact hlog_nonneg
  have hcoeff_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun u => -(Φ (-u))) s :=
    hΦ.neg.meromorphicOrderAt_nonneg
  rw [show (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) =
      (fun u => -logDeriv riemannZeta u) * (fun u => -(Φ (-u))) by rfl]
  rw [meromorphicOrderAt_mul hneg_mero hcoeff_mero]
  exact add_nonneg hneg_nonneg hcoeff_nonneg

lemma meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_eq_neg_one_of_zero
    {I J : Set ℝ} {Φ : ℂ → ℂ} (hI : I ⊆ Set.Ioo (0 : ℝ) 1)
    (ρ : riemannZeta.zeroes_rect I J)
    (hΦ : AnalyticAt ℂ (fun u => Φ (-u)) ρ.val) (hΦ_ne : Φ (-ρ.val) ≠ 0) :
    meromorphicOrderAt (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) ρ.val =
      (-1 : ℤ) := by
  let rho : NontrivialZeros :=
    ⟨ρ.val, hI ρ.property.1, Set.mem_univ _, ρ.property.2.2⟩
  have horder_pos : 0 < riemannZeta.order ρ.val :=
    riemannZeta_order_pos_nontrivialZero rho
  have horder_ne : riemannZeta.order ρ.val ≠ 0 := ne_of_gt horder_pos
  have hlog_order :
      meromorphicOrderAt (logDeriv riemannZeta) ρ.val = (-1 : ℤ) :=
  by
    have hne_top : meromorphicOrderAt riemannZeta ρ.val ≠ ⊤ :=
      riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero rho
    have hord : meromorphicOrderAt riemannZeta ρ.val = riemannZeta.order ρ.val := by
      simpa [riemannZeta.order, WithTop.untop₀] using
        (WithTop.coe_untop₀_of_ne_top hne_top).symm
    exact meromorphicOrderAt_logDeriv_eq_neg_one_of_meromorphicOrderAt_ne_zero
      (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt
      hord
      horder_ne
  have hneg_order :
      meromorphicOrderAt (fun u => -logDeriv riemannZeta u) ρ.val = (-1 : ℤ) := by
    change meromorphicOrderAt (-(logDeriv riemannZeta)) ρ.val = (-1 : ℤ)
    rw [(meromorphicOrderAt_neg (f := logDeriv riemannZeta) (x := ρ.val)).symm]
    exact hlog_order
  have hcoeff_ne : (fun u => -(Φ (-u))) ρ.val ≠ 0 := by
    simpa using (neg_ne_zero.mpr hΦ_ne)
  rw [show (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) =
      (fun u => -(Φ (-u))) * (fun u => -logDeriv riemannZeta u) by
        funext u
        simpa using (mul_comm (-logDeriv riemannZeta u) (-(Φ (-u))))]
  change meromorphicOrderAt ((-(fun u => Φ (-u))) *
      (fun u => -logDeriv riemannZeta u)) ρ.val = (-1 : ℤ)
  rw [meromorphicOrderAt_mul_of_ne_zero (f := fun u => -logDeriv riemannZeta u)
    hΦ.neg hcoeff_ne, hneg_order]

lemma zeroes_rect_uIcc_eq_rectangle_inter_zeroes (z w : ℂ) :
    riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im) =
      Rectangle z w ∩ riemannZeta.zeroes := by
  ext s
  simp [riemannZeta.zeroes_rect, Rectangle, Complex.mem_reProdIm, and_assoc]

lemma zeroes_rect_uIcc_finite_of_one_not_mem {z w : ℂ}
    (hone : (1 : ℂ) ∉ Rectangle z w) :
    (riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)).Finite := by
  have hrect_compact : IsCompact (Rectangle z w) := by
    rw [Rectangle]
    exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
  simpa [zeroes_rect_uIcc_eq_rectangle_inter_zeroes] using
    (riemannZeta.zeroes_on_Compact_finite hrect_compact hone)

lemma zeroes_rect_uIcc_finite (z w : ℂ) :
    (riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)).Finite := by
  have hrect_compact : IsCompact (Rectangle z w) := by
    rw [Rectangle]
    exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
  simpa [zeroes_rect_uIcc_eq_rectangle_inter_zeroes] using
    (riemannZeta.zeroes_on_Compact_finite' hrect_compact)

lemma riemannZeta_meromorphicOrderAt_eq_order_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    meromorphicOrderAt riemannZeta s = riemannZeta.order s := by
  have hne_top : meromorphicOrderAt riemannZeta s ≠ ⊤ :=
    riemannZeta_meromorphicOrderAt_ne_top_of_ne_one hs
  simpa [riemannZeta.order, WithTop.untop₀] using
    (WithTop.coe_untop₀_of_ne_top hne_top).symm

lemma riemannZeta_order_pos_of_zero_ne_one {s : ℂ} (hs : s ≠ 1)
    (hzero : riemannZeta s = 0) :
    0 < riemannZeta.order s := by
  have han := riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)
  have horder_ne_top : meromorphicOrderAt riemannZeta s ≠ ⊤ :=
    riemannZeta_meromorphicOrderAt_ne_top_of_ne_one hs
  have hanOrder_ne_zero : analyticOrderAt riemannZeta s ≠ 0 := by
    intro h
    exact (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold riemannZeta.order
  cases hO : analyticOrderAt riemannZeta s with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have hn_pos : 0 < n := by
        exact Nat.pos_of_ne_zero (by
          intro hn
          exact hanOrder_ne_zero (by simp [hO, hn]))
      rw [han.meromorphicOrderAt_eq, hO, ENat.map_coe, WithTop.untopD_coe]
      exact_mod_cast hn_pos

lemma meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_eq_neg_one_of_zero_ne_one
    {I J : Set ℝ} {Φ : ℂ → ℂ} (ρ : riemannZeta.zeroes_rect I J)
    (hρ_ne_one : ρ.val ≠ 1)
    (hΦ : AnalyticAt ℂ (fun u => Φ (-u)) ρ.val) (hΦ_ne : Φ (-ρ.val) ≠ 0) :
    meromorphicOrderAt (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) ρ.val =
      (-1 : ℤ) := by
  have horder_pos : 0 < riemannZeta.order ρ.val :=
    riemannZeta_order_pos_of_zero_ne_one hρ_ne_one ρ.property.2.2
  have horder_ne : riemannZeta.order ρ.val ≠ 0 := ne_of_gt horder_pos
  have han := riemannZeta_analyticOn_compl_one ρ.val
    (by simpa [Set.mem_compl_iff] using hρ_ne_one)
  have hlog_order :
      meromorphicOrderAt (logDeriv riemannZeta) ρ.val = (-1 : ℤ) :=
    meromorphicOrderAt_logDeriv_eq_neg_one_of_meromorphicOrderAt_ne_zero
      han.meromorphicAt
      (riemannZeta_meromorphicOrderAt_eq_order_of_ne_one hρ_ne_one)
      horder_ne
  have hneg_order :
      meromorphicOrderAt (fun u => -logDeriv riemannZeta u) ρ.val = (-1 : ℤ) := by
    change meromorphicOrderAt (-(logDeriv riemannZeta)) ρ.val = (-1 : ℤ)
    rw [(meromorphicOrderAt_neg (f := logDeriv riemannZeta) (x := ρ.val)).symm]
    exact hlog_order
  have hcoeff_ne : (fun u => -(Φ (-u))) ρ.val ≠ 0 := by
    simpa using (neg_ne_zero.mpr hΦ_ne)
  rw [show (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) =
      (fun u => -(Φ (-u))) * (fun u => -logDeriv riemannZeta u) by
        funext u
        simpa using (mul_comm (-logDeriv riemannZeta u) (-(Φ (-u))))]
  change meromorphicOrderAt ((-(fun u => Φ (-u))) *
      (fun u => -logDeriv riemannZeta u)) ρ.val = (-1 : ℤ)
  rw [meromorphicOrderAt_mul_of_ne_zero (f := fun u => -logDeriv riemannZeta u)
    hΦ.neg hcoeff_ne, hneg_order]

lemma riemannZeta_eventuallyEq_one_model :
    riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)]
      fun s : ℂ => (s - 1) ^ (-1 : ℤ) * zetaTimesSMinusOne_entire s := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs_ne : s ≠ (1 : ℂ) := by
    simpa using hs
  rw [zetaTimesSMinusOne_entire_eq_mul_riemannZeta hs_ne]
  simp [sub_ne_zero.mpr hs_ne]

lemma riemannZeta_meromorphicAt_one : MeromorphicAt riemannZeta (1 : ℂ) := by
  have hmodel_mero :
      MeromorphicAt
        (fun s : ℂ => (s - 1) ^ (-1 : ℤ) * zetaTimesSMinusOne_entire s) (1 : ℂ) := by
    have hpow : MeromorphicAt (fun s : ℂ => (s - 1) ^ (-1 : ℤ)) (1 : ℂ) := by
      fun_prop
    exact hpow.mul (zetaTimesSMinusOne_entire_differentiable.analyticAt 1).meromorphicAt
  exact hmodel_mero.congr riemannZeta_eventuallyEq_one_model.symm

lemma riemannZeta_meromorphicOrderAt_one_eq_neg_one :
    meromorphicOrderAt riemannZeta (1 : ℂ) = (-1 : ℤ) := by
  have hg_an : AnalyticAt ℂ zetaTimesSMinusOne_entire (1 : ℂ) :=
    zetaTimesSMinusOne_entire_differentiable.analyticAt 1
  have hg_ne : zetaTimesSMinusOne_entire (1 : ℂ) ≠ 0 := by simp
  exact (meromorphicOrderAt_eq_int_iff riemannZeta_meromorphicAt_one).2
    ⟨zetaTimesSMinusOne_entire, hg_an, hg_ne, riemannZeta_eventuallyEq_one_model⟩

lemma meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_eq_neg_one_at_one
    {Φ : ℂ → ℂ} (hΦ : AnalyticAt ℂ (fun u => Φ (-u)) (1 : ℂ))
    (hΦ_ne : Φ (-(1 : ℂ)) ≠ 0) :
    meromorphicOrderAt (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) (1 : ℂ) =
      (-1 : ℤ) := by
  have hlog_order :
      meromorphicOrderAt (logDeriv riemannZeta) (1 : ℂ) = (-1 : ℤ) :=
    meromorphicOrderAt_logDeriv_eq_neg_one_of_meromorphicOrderAt_ne_zero
      riemannZeta_meromorphicAt_one
      riemannZeta_meromorphicOrderAt_one_eq_neg_one
      (by norm_num : (-1 : ℤ) ≠ 0)
  have hneg_order :
      meromorphicOrderAt (fun u => -logDeriv riemannZeta u) (1 : ℂ) = (-1 : ℤ) := by
    change meromorphicOrderAt (-(logDeriv riemannZeta)) (1 : ℂ) = (-1 : ℤ)
    rw [(meromorphicOrderAt_neg (f := logDeriv riemannZeta) (x := (1 : ℂ))).symm]
    exact hlog_order
  have hcoeff_ne : (fun u => -(Φ (-u))) (1 : ℂ) ≠ 0 := by
    simpa using (neg_ne_zero.mpr hΦ_ne)
  rw [show (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) =
      (fun u => -(Φ (-u))) * (fun u => -logDeriv riemannZeta u) by
        funext u
        simpa using (mul_comm (-logDeriv riemannZeta u) (-(Φ (-u))))]
  change meromorphicOrderAt ((-(fun u => Φ (-u))) *
      (fun u => -logDeriv riemannZeta u)) (1 : ℂ) = (-1 : ℤ)
  rw [meromorphicOrderAt_mul_of_ne_zero (f := fun u => -logDeriv riemannZeta u)
    hΦ.neg hcoeff_ne, hneg_order]

/-- The logarithmic derivative has leading coefficient equal to the meromorphic order. -/
lemma tendsto_logDeriv_mul_order_of_meromorphicOrderAt {f : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = m) :
    Filter.Tendsto (fun z : ℂ => (z - p) * logDeriv f z)
      (𝓝[≠] p) (𝓝 (m : ℂ)) := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hderiv_eq : deriv f =ᶠ[𝓝[≠] p] deriv (fun w : ℂ => (w - p) ^ m * g w) :=
    Filter.EventuallyEq.nhdsNE_deriv hg_eq
  have hlog_eq : (fun z : ℂ => logDeriv f z) =ᶠ[𝓝[≠] p]
      fun z : ℂ => logDeriv (fun w : ℂ => (w - p) ^ m * g w) z := by
    filter_upwards [hg_eq, hderiv_eq] with z hfz hdz
    simp [logDeriv, hfz, hdz]
  exact (model_logDeriv_tendsto_order hg_an hg_ne).congr' (by
    filter_upwards [hlog_eq] with z hz
    rw [hz])

/-- The simple residue of a logarithmic derivative is the meromorphic order.
This is the multiplicity bridge needed for zeta zeros of arbitrary order. -/
lemma residue_logDeriv_eq_order_of_meromorphicOrderAt {f : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = m) :
    CH2.residue (logDeriv f) p = (m : ℂ) := by
  apply CH2.residue_eq_of_tendsto
  exact tendsto_logDeriv_mul_order_of_meromorphicOrderAt hf hord

/-- Multiplying a logarithmic derivative by a continuous factor multiplies the residue
by the factor value. -/
lemma residue_logDeriv_mul_eq_order_mul {f ψ : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = m)
    (hψ : ContinuousAt ψ p) :
    CH2.residue (fun z => logDeriv f z * ψ z) p = (m : ℂ) * ψ p := by
  apply CH2.residue_eq_of_tendsto
  have hbase := tendsto_logDeriv_mul_order_of_meromorphicOrderAt hf hord
  simpa [mul_assoc] using hbase.mul hψ.continuousWithinAt.tendsto

/-- Multiplying `-logDeriv f` by a continuous factor negates the order-weighted residue. -/
lemma residue_negLogDeriv_mul_eq_neg_order_mul {f ψ : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = m)
    (hψ : ContinuousAt ψ p) :
    CH2.residue (fun z => -logDeriv f z * ψ z) p = -((m : ℂ) * ψ p) := by
  apply CH2.residue_eq_of_tendsto
  have hbase := tendsto_logDeriv_mul_order_of_meromorphicOrderAt hf hord
  simpa [mul_assoc, neg_mul] using hbase.neg.mul hψ.continuousWithinAt.tendsto

lemma residue_negLogDeriv_mul_neg_eq_order_mul {f ψ : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = m)
    (hψ : ContinuousAt ψ p) :
    CH2.residue (fun z => -logDeriv f z * (-ψ z)) p = (m : ℂ) * ψ p := by
  simpa using
    (residue_negLogDeriv_mul_eq_neg_order_mul (f := f) (ψ := fun z => -ψ z) hf hord hψ.neg)

lemma residue_negLogDeriv_riemannZeta_mul_negCoeff_one {Φ : ℂ → ℂ}
    (hΦ : ContinuousAt (fun u => Φ (-u)) (1 : ℂ)) :
    CH2.residue (fun u => -logDeriv riemannZeta u * (-(Φ (-u)))) (1 : ℂ) =
      -Φ (-(1 : ℂ)) := by
  have h := residue_negLogDeriv_mul_neg_eq_order_mul
    (f := riemannZeta) (ψ := fun u => Φ (-u)) (p := (1 : ℂ)) (m := (-1 : ℤ))
    riemannZeta_meromorphicAt_one
    riemannZeta_meromorphicOrderAt_one_eq_neg_one
    hΦ
  simpa using h

lemma residue_negLogDeriv_riemannZeta_mul_negCoeff_eq_order_mul_of_zero_ne_one
    {I J : Set ℝ} (ρ : riemannZeta.zeroes_rect I J)
    (hρ_ne_one : ρ.val ≠ 1) {Φ : ℂ → ℂ}
    (hΦ : ContinuousAt (fun z => Φ (-z)) ρ.val) :
    CH2.residue (fun z => -logDeriv riemannZeta z * (-(Φ (-z)))) ρ =
      Φ (-ρ) * (riemannZeta.order ρ.val : ℂ) := by
  have h := residue_negLogDeriv_mul_neg_eq_order_mul
    (f := riemannZeta) (ψ := fun z => Φ (-z))
    (p := ρ.val) (m := riemannZeta.order ρ.val)
    (riemannZeta_analyticOn_compl_one ρ.val
      (by simpa [Set.mem_compl_iff] using hρ_ne_one)).meromorphicAt
    (riemannZeta_meromorphicOrderAt_eq_order_of_ne_one hρ_ne_one)
    hΦ
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- The product of `-logDeriv f` with an analytic factor has at most simple poles. -/
lemma hasSimplePolesOn_negLogDeriv_mul_of_meromorphicOrderAt
    {f ψ : ℂ → ℂ} {S : Set ℂ}
    (hf : ∀ z ∈ S, MeromorphicAt f z)
    (hfiniteOrder : ∀ z ∈ S, ∃ m : ℤ, meromorphicOrderAt f z = m)
    (hψ : ∀ z ∈ S, AnalyticAt ℂ ψ z) :
    CH2.HasSimplePolesOn (fun z => -logDeriv f z * ψ z) S := by
  intro z hz
  rcases hfiniteOrder z hz with ⟨m, hm⟩
  have hlog :=
    meromorphicOrderAt_logDeriv_ge_neg_one_of_meromorphicOrderAt (hf z hz) hm
  have hlog_mero : MeromorphicAt (logDeriv f) z := by
    rw [logDeriv]
    exact (hf z hz).deriv.div (hf z hz)
  have hneg_mero : MeromorphicAt (fun w => -logDeriv f w) z := by
    change MeromorphicAt (-(logDeriv f)) z
    exact hlog_mero.neg
  have hprod : meromorphicOrderAt (fun w => -logDeriv f w * ψ w) z =
      meromorphicOrderAt (fun w => -logDeriv f w) z + meromorphicOrderAt ψ z := by
    rw [show (fun w => -logDeriv f w * ψ w) = (fun w => -logDeriv f w) * ψ by rfl]
    exact meromorphicOrderAt_mul hneg_mero (hψ z hz).meromorphicAt
  have hneg_order : meromorphicOrderAt (fun w => -logDeriv f w) z =
      meromorphicOrderAt (logDeriv f) z := by
    change meromorphicOrderAt (-(logDeriv f)) z = meromorphicOrderAt (logDeriv f) z
    exact (meromorphicOrderAt_neg (f := logDeriv f) (x := z)).symm
  have hψ_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt ψ z :=
    (hψ z hz).meromorphicOrderAt_nonneg
  rw [hprod, hneg_order]
  simpa using add_le_add hlog hψ_nonneg

/-- Zeta-specialized simple-pole hypothesis for `-ζ'/ζ` times an analytic factor. -/
lemma hasSimplePolesOn_negLogDeriv_riemannZeta_mul_of_finiteOrder
    {S : Set ℂ} {Φ : ℂ → ℂ}
    (hS_ne_one : S ⊆ ({1} : Set ℂ)ᶜ)
    (hfiniteOrder : ∀ z ∈ S, ∃ m : ℤ, meromorphicOrderAt riemannZeta z = m)
    (hΦ : ∀ z ∈ S, AnalyticAt ℂ (fun w => Φ (-w)) z) :
    CH2.HasSimplePolesOn (fun z => -logDeriv riemannZeta z * Φ (-z)) S := by
  exact hasSimplePolesOn_negLogDeriv_mul_of_meromorphicOrderAt
    (f := riemannZeta) (ψ := fun z => Φ (-z))
    (fun z hz => (riemannZeta_analyticOn_compl_one z (hS_ne_one hz)).meromorphicAt)
    hfiniteOrder hΦ

lemma hasSimplePolesOn_negLogDeriv_riemannZeta_mul_negCoeff_of_finiteOrder
    {S : Set ℂ} {Φ : ℂ → ℂ}
    (hS_ne_one : S ⊆ ({1} : Set ℂ)ᶜ)
    (hfiniteOrder : ∀ z ∈ S, ∃ m : ℤ, meromorphicOrderAt riemannZeta z = m)
    (hΦ : ∀ z ∈ S, AnalyticAt ℂ (fun w => Φ (-w)) z) :
    CH2.HasSimplePolesOn (fun z => -logDeriv riemannZeta z * (-(Φ (-z)))) S := by
  exact hasSimplePolesOn_negLogDeriv_mul_of_meromorphicOrderAt
    (f := riemannZeta) (ψ := fun z => -(Φ (-z)))
    (fun z hz => (riemannZeta_analyticOn_compl_one z (hS_ne_one hz)).meromorphicAt)
    hfiniteOrder (fun z hz => (hΦ z hz).neg)

/-- Zeta's meromorphic order at any zero rectangle inside the non-trivial strip. -/
lemma riemannZeta_meromorphicOrderAt_eq_order_of_mem_nontrivial
    {I J : Set ℝ} (hI : I ⊆ Set.Ioo (0 : ℝ) 1)
    (ρ : riemannZeta.zeroes_rect I J) :
    meromorphicOrderAt riemannZeta ρ.val = riemannZeta.order ρ.val := by
  let rho : NontrivialZeros :=
    ⟨ρ.val, hI ρ.property.1, Set.mem_univ _, ρ.property.2.2⟩
  have hne_top : meromorphicOrderAt riemannZeta ρ.val ≠ ⊤ :=
    riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero rho
  simpa [riemannZeta.order, WithTop.untop₀] using
    (WithTop.coe_untop₀_of_ne_top hne_top).symm

/-- Residue of the zeta logarithmic derivative at a non-trivial zero, counted with
the repository's `riemannZeta.order`. -/
lemma residue_logDeriv_riemannZeta_eq_order
    (ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ)) :
    CH2.residue (logDeriv riemannZeta) ρ =
      (riemannZeta.order ρ.val : ℂ) := by
  let rho : NontrivialZeros :=
    ⟨ρ.val, ρ.property.1, Set.mem_univ _, ρ.property.2.2⟩
  have hne_top : meromorphicOrderAt riemannZeta ρ.val ≠ ⊤ :=
    riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero rho
  have hord : meromorphicOrderAt riemannZeta ρ.val = riemannZeta.order ρ.val := by
    simpa [riemannZeta.order, WithTop.untop₀] using
      (WithTop.coe_untop₀_of_ne_top hne_top).symm
  exact residue_logDeriv_eq_order_of_meromorphicOrderAt
    (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt hord

lemma residue_logDeriv_riemannZeta_eq_order_of_mem_nontrivial
    {I J : Set ℝ} (hI : I ⊆ Set.Ioo (0 : ℝ) 1)
    (ρ : riemannZeta.zeroes_rect I J) :
    CH2.residue (logDeriv riemannZeta) ρ =
      (riemannZeta.order ρ.val : ℂ) := by
  let rho : NontrivialZeros :=
    ⟨ρ.val, hI ρ.property.1, Set.mem_univ _, ρ.property.2.2⟩
  exact residue_logDeriv_eq_order_of_meromorphicOrderAt
    (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt
    (riemannZeta_meromorphicOrderAt_eq_order_of_mem_nontrivial hI ρ)

lemma residue_logDeriv_riemannZeta_mul_eq_order_mul_of_mem_nontrivial
    {I J : Set ℝ} (hI : I ⊆ Set.Ioo (0 : ℝ) 1)
    (ρ : riemannZeta.zeroes_rect I J) {ψ : ℂ → ℂ}
    (hψ : ContinuousAt ψ ρ.val) :
    CH2.residue (fun z => logDeriv riemannZeta z * ψ z) ρ =
      (riemannZeta.order ρ.val : ℂ) * ψ ρ.val := by
  let rho : NontrivialZeros :=
    ⟨ρ.val, hI ρ.property.1, Set.mem_univ _, ρ.property.2.2⟩
  exact residue_logDeriv_mul_eq_order_mul
    (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt
    (riemannZeta_meromorphicOrderAt_eq_order_of_mem_nontrivial hI ρ) hψ

lemma residue_negLogDeriv_riemannZeta_mul_eq_neg_order_mul_of_mem_nontrivial
    {I J : Set ℝ} (hI : I ⊆ Set.Ioo (0 : ℝ) 1)
    (ρ : riemannZeta.zeroes_rect I J) {ψ : ℂ → ℂ}
    (hψ : ContinuousAt ψ ρ.val) :
    CH2.residue (fun z => -logDeriv riemannZeta z * ψ z) ρ =
      -((riemannZeta.order ρ.val : ℂ) * ψ ρ.val) := by
  let rho : NontrivialZeros :=
    ⟨ρ.val, hI ρ.property.1, Set.mem_univ _, ρ.property.2.2⟩
  exact residue_negLogDeriv_mul_eq_neg_order_mul
    (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt
    (riemannZeta_meromorphicOrderAt_eq_order_of_mem_nontrivial hI ρ) hψ

lemma residue_negLogDeriv_riemannZeta_mul_negCoeff_eq_order_mul_of_mem_nontrivial
    {I J : Set ℝ} (hI : I ⊆ Set.Ioo (0 : ℝ) 1)
    (ρ : riemannZeta.zeroes_rect I J) {Φ : ℂ → ℂ}
    (hΦ : ContinuousAt (fun z => Φ (-z)) ρ.val) :
    CH2.residue (fun z => -logDeriv riemannZeta z * (-(Φ (-z)))) ρ =
      Φ (-ρ) * (riemannZeta.order ρ.val : ℂ) := by
  have h := residue_negLogDeriv_mul_neg_eq_order_mul
    (f := riemannZeta) (ψ := fun z => Φ (-z))
    (p := ρ.val) (m := riemannZeta.order ρ.val)
    (by
      let rho : NontrivialZeros :=
        ⟨ρ.val, hI ρ.property.1, Set.mem_univ _, ρ.property.2.2⟩
      exact (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt)
    (riemannZeta_meromorphicOrderAt_eq_order_of_mem_nontrivial hI ρ) hΦ
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- Finite residue sums over a zero rectangle agree with the order-weighted zero sum
once the pointwise residues have the Kadiri coefficient. -/
lemma sumResiduesIn_zeroes_rect_eq_zeroes_sum_of_residue_eq
    {I J : Set ℝ} {F Φ : ℂ → ℂ}
    (hfin : (riemannZeta.zeroes_rect I J).Finite)
    (hres : ∀ ρ : riemannZeta.zeroes_rect I J,
      CH2.residue F ρ = Φ (-ρ) * (riemannZeta.order ρ.val : ℂ)) :
    CH2.sumResiduesIn F (riemannZeta.zeroes_rect I J) =
      riemannZeta.zeroes_sum I J (fun ρ ↦ Φ (-ρ)) := by
  classical
  haveI : Finite (riemannZeta.zeroes_rect I J) := Set.finite_coe_iff.mpr hfin
  letI := Fintype.ofFinite (riemannZeta.zeroes_rect I J)
  unfold CH2.sumResiduesIn riemannZeta.zeroes_sum
  rw [tsum_fintype, tsum_fintype]
  exact Finset.sum_congr rfl (fun ρ _ ↦ hres ρ)

lemma sumResiduesIn_eq_finset_of_finite {F : ℂ → ℂ} {S : Set ℂ}
    (hfin : S.Finite) :
    CH2.sumResiduesIn F S = ∑ s ∈ hfin.toFinset, CH2.residue F s := by
  classical
  haveI : Finite S := Set.finite_coe_iff.mpr hfin
  letI := Fintype.ofFinite S
  unfold CH2.sumResiduesIn
  rw [tsum_fintype]
  exact (Finset.sum_subtype hfin.toFinset (fun s ↦ hfin.mem_toFinset)
    (fun s ↦ CH2.residue F s)).symm

lemma sumResiduesIn_union_singleton_eq_add {F : ℂ → ℂ} {S : Set ℂ} {p : ℂ}
    (hfin : S.Finite) (hp : p ∉ S) :
    CH2.sumResiduesIn F (S ∪ {p}) = CH2.residue F p + CH2.sumResiduesIn F S := by
  classical
  have hfin_union : (S ∪ {p}).Finite := hfin.union (Set.finite_singleton p)
  rw [sumResiduesIn_eq_finset_of_finite hfin_union,
    sumResiduesIn_eq_finset_of_finite hfin]
  have htoFinset : hfin_union.toFinset = insert p hfin.toFinset := by
    ext s
    simp [hfin.mem_toFinset]
  rw [htoFinset, Finset.sum_insert (by simpa [hfin.mem_toFinset] using hp)]

lemma sumResiduesIn_negLogDeriv_riemannZeta_mul_negCoeff_eq_zeroes_sum_of_mem_nontrivial
    {I J : Set ℝ} (hI : I ⊆ Set.Ioo (0 : ℝ) 1)
    (hfin : (riemannZeta.zeroes_rect I J).Finite) {Φ : ℂ → ℂ}
    (hΦ : ∀ ρ : riemannZeta.zeroes_rect I J,
      ContinuousAt (fun z => Φ (-z)) ρ.val) :
    CH2.sumResiduesIn (fun z => -logDeriv riemannZeta z * (-(Φ (-z))))
        (riemannZeta.zeroes_rect I J) =
      riemannZeta.zeroes_sum I J (fun ρ ↦ Φ (-ρ)) := by
  exact sumResiduesIn_zeroes_rect_eq_zeroes_sum_of_residue_eq hfin
    (fun ρ => residue_negLogDeriv_riemannZeta_mul_negCoeff_eq_order_mul_of_mem_nontrivial
      hI ρ (hΦ ρ))

/-- Rectangle kernel for the Kadiri contour-shift route. Use the log-derivative lemmas above
to supply the `CH2.HasSimplePolesOn` and residue hypotheses for zeta zeros. -/
lemma rectangleIntegral'_eq_zeroes_sum_of_simple_poles
    {I J : Set ℝ} {F Φ : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hmero : MeromorphicOn F (Rectangle z w))
    (hboundary : Disjoint (RectangleBorder z w) {u | meromorphicOrderAt F u < 0})
    (hfinite : (Rectangle z w ∩ {u | meromorphicOrderAt F u < 0}).Finite)
    (hsimple : CH2.HasSimplePolesOn F (Rectangle z w))
    (hpoles : Rectangle z w ∩ {u | meromorphicOrderAt F u < 0} =
      riemannZeta.zeroes_rect I J)
    (hres : ∀ ρ : riemannZeta.zeroes_rect I J,
      CH2.residue F ρ = Φ (-ρ) * (riemannZeta.order ρ.val : ℂ)) :
    RectangleIntegral' F z w =
      riemannZeta.zeroes_sum I J (fun ρ ↦ Φ (-ρ)) := by
  rw [CH2.RectangleIntegral'_eq_sumResiduesIn zRe_le_wRe zIm_le_wIm hmero hboundary
    hfinite hsimple, hpoles]
  exact sumResiduesIn_zeroes_rect_eq_zeroes_sum_of_residue_eq (hpoles ▸ hfinite) hres

lemma negLogDeriv_riemannZeta_mul_negCoeff_poles_in_rectangle_eq_zeroes_rect
    {z w : ℂ} {Φ : ℂ → ℂ}
    (hstrip : Set.uIcc z.re w.re ⊆ Set.Ioo (0 : ℝ) 1)
    (hone : (1 : ℂ) ∉ Rectangle z w)
    (hΦ_an : ∀ s ∈ Rectangle z w, AnalyticAt ℂ (fun u => Φ (-u)) s)
    (hΦ_ne_zero :
      ∀ ρ : riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im),
        Φ (-ρ.val) ≠ 0) :
    Rectangle z w ∩
        {u | meromorphicOrderAt (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) u < 0} =
      riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im) := by
  ext s
  constructor
  · intro hs
    have hsR : s ∈ Rectangle z w := hs.1
    have hs_ne_one : s ≠ 1 := by
      intro hs_eq
      exact hone (hs_eq ▸ hsR)
    have hzeta_zero : riemannZeta s = 0 := by
      by_contra hζ
      exact (not_lt_of_ge
        (meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_nonneg_of_ne_zero
          hs_ne_one hζ (hΦ_an s hsR))) hs.2
    exact ⟨hsR.1, hsR.2, by simpa [riemannZeta.zeroes] using hzeta_zero⟩
  · intro hs
    let ρ : riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im) :=
      ⟨s, hs⟩
    have hsR : s ∈ Rectangle z w := ⟨hs.1, hs.2.1⟩
    have horder :
        meromorphicOrderAt (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) s =
          (-1 : ℤ) :=
      meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_eq_neg_one_of_zero
        hstrip ρ (hΦ_an s hsR) (hΦ_ne_zero ρ)
    exact ⟨hsR, by
      change meromorphicOrderAt (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) s < 0
      rw [horder]
      exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)⟩

lemma rectangleIntegral'_negLogDeriv_riemannZeta_mul_negCoeff_eq_zeroes_sum
    {z w : ℂ} {Φ : ℂ → ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hstrip : Set.uIcc z.re w.re ⊆ Set.Ioo (0 : ℝ) 1)
    (hone : (1 : ℂ) ∉ Rectangle z w)
    (hboundary_zeroes :
      Disjoint (RectangleBorder z w)
        (riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)))
    (hΦ_an : ∀ s ∈ Rectangle z w, AnalyticAt ℂ (fun u => Φ (-u)) s) :
    RectangleIntegral' (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) z w =
      riemannZeta.zeroes_sum (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)
        (fun ρ ↦ Φ (-ρ)) := by
  let F : ℂ → ℂ := fun s => -logDeriv riemannZeta s * (-(Φ (-s)))
  let I : Set ℝ := Set.uIcc z.re w.re
  let J : Set ℝ := Set.uIcc z.im w.im
  let P : Set ℂ := {u | meromorphicOrderAt F u < 0}
  have hrect_ne_one : Rectangle z w ⊆ ({1} : Set ℂ)ᶜ := by
    intro s hs
    rw [Set.mem_compl_iff]
    intro hs_eq
    exact hone (hs_eq ▸ hs)
  have hmero : MeromorphicOn F (Rectangle z w) := by
    intro s hs
    have hs_ne_one : s ≠ 1 := by
      intro hs_eq
      exact hone (hs_eq ▸ hs)
    have hζmero : MeromorphicAt riemannZeta s :=
      (riemannZeta_analyticOn_compl_one s
        (by simpa [Set.mem_compl_iff] using hs_ne_one)).meromorphicAt
    have hlog_mero : MeromorphicAt (logDeriv riemannZeta) s := by
      rw [logDeriv]
      exact hζmero.deriv.div hζmero
    have hneg_mero : MeromorphicAt (fun u => -logDeriv riemannZeta u) s := by
      change MeromorphicAt (-(logDeriv riemannZeta)) s
      exact hlog_mero.neg
    have hcoeff_mero : MeromorphicAt (fun u => -(Φ (-u))) s :=
      (hΦ_an s hs).neg.meromorphicAt
    exact hneg_mero.mul hcoeff_mero
  have hfiniteOrder :
      ∀ s ∈ Rectangle z w, ∃ m : ℤ, meromorphicOrderAt riemannZeta s = m := by
    intro s hs
    exact riemannZeta_finiteOrder_of_ne_one (by intro hs_eq; exact hone (hs_eq ▸ hs))
  have hsimple : CH2.HasSimplePolesOn F (Rectangle z w) :=
    hasSimplePolesOn_negLogDeriv_riemannZeta_mul_negCoeff_of_finiteOrder
      hrect_ne_one hfiniteOrder hΦ_an
  have hactual_subset_zeroes : Rectangle z w ∩ P ⊆ riemannZeta.zeroes_rect I J := by
    intro s hs
    have hsR : s ∈ Rectangle z w := hs.1
    have hs_ne_one : s ≠ 1 := by
      intro hs_eq
      exact hone (hs_eq ▸ hsR)
    have hzeta_zero : riemannZeta s = 0 := by
      by_contra hζ
      exact (not_lt_of_ge
        (meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_nonneg_of_ne_zero
          hs_ne_one hζ (hΦ_an s hsR))) hs.2
    exact ⟨hsR.1, hsR.2, by simpa [riemannZeta.zeroes] using hzeta_zero⟩
  have h_set_eq : Rectangle z w ∩ P = riemannZeta.zeroes_rect I J ∩ P := by
    ext s
    constructor
    · intro hs
      exact ⟨hactual_subset_zeroes hs, hs.2⟩
    · intro hs
      exact ⟨⟨hs.1.1, hs.1.2.1⟩, hs.2⟩
  have hboundary : Disjoint (RectangleBorder z w) {u | meromorphicOrderAt F u < 0} := by
    rw [Set.disjoint_left]
    intro s hsB hsPole
    have hsR : s ∈ Rectangle z w := rectangleBorder_subset_rectangle z w hsB
    have hsZero : s ∈ riemannZeta.zeroes_rect I J := by
      exact hactual_subset_zeroes (show s ∈ Rectangle z w ∩ P
        from ⟨hsR, hsPole⟩)
    exact Set.disjoint_left.mp (by simpa [I, J] using hboundary_zeroes) hsB hsZero
  have hfinite : (Rectangle z w ∩ {u | meromorphicOrderAt F u < 0}).Finite := by
    exact (zeroes_rect_uIcc_finite_of_one_not_mem hone).subset (by
      simpa [P, I, J] using hactual_subset_zeroes)
  have hres : ∀ ρ : riemannZeta.zeroes_rect I J,
      CH2.residue F ρ = Φ (-ρ) * (riemannZeta.order ρ.val : ℂ) := by
    intro ρ
    have hρR : ρ.val ∈ Rectangle z w := ⟨ρ.property.1, ρ.property.2.1⟩
    simpa [F] using
      (residue_negLogDeriv_riemannZeta_mul_negCoeff_eq_order_mul_of_mem_nontrivial
        hstrip ρ (hΦ_an ρ.val hρR).continuousAt)
  have hresidue_set :
      CH2.sumResiduesIn F (Rectangle z w ∩ P) =
        CH2.sumResiduesIn F (riemannZeta.zeroes_rect I J) := by
    refine CH2.sumResiduesIn_inter_eq_of_set_eq h_set_eq ?_
    intro s hsZero hsNotPole
    have hsR : s ∈ Rectangle z w := ⟨hsZero.1, hsZero.2.1⟩
    have hsNotPole' : ¬ meromorphicOrderAt F s < 0 := by
      simpa [P] using hsNotPole
    exact CH2.residue_eq_zero_of_not_pole_of_meromorphicAt (hmero s hsR)
      (le_of_not_gt hsNotPole')
  calc
    RectangleIntegral' F z w =
        CH2.sumResiduesIn F (Rectangle z w ∩ P) := by
      simpa [F, P] using
        (CH2.RectangleIntegral'_eq_sumResiduesIn zRe_le_wRe zIm_le_wIm hmero
          hboundary hfinite hsimple)
    _ = CH2.sumResiduesIn F (riemannZeta.zeroes_rect I J) := hresidue_set
    _ = riemannZeta.zeroes_sum I J (fun ρ ↦ Φ (-ρ)) :=
      sumResiduesIn_zeroes_rect_eq_zeroes_sum_of_residue_eq
        (by simpa [I, J] using zeroes_rect_uIcc_finite_of_one_not_mem hone) hres

lemma negLogDeriv_riemannZeta_mul_negCoeff_poles_in_rectangle_eq_zeroes_rect_union_one
    {z w : ℂ} {Φ : ℂ → ℂ}
    (hone_mem : (1 : ℂ) ∈ Rectangle z w)
    (hΦ_an : ∀ s ∈ Rectangle z w, AnalyticAt ℂ (fun u => Φ (-u)) s)
    (hΦ_ne_zero :
      ∀ ρ : riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im),
        Φ (-ρ.val) ≠ 0)
    (hΦ_one_ne_zero : Φ (-(1 : ℂ)) ≠ 0) :
    Rectangle z w ∩
        {u | meromorphicOrderAt (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) u < 0} =
      riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im) ∪
        ({1} : Set ℂ) := by
  ext s
  constructor
  · intro hs
    have hsR : s ∈ Rectangle z w := hs.1
    by_cases hs_one : s = 1
    · exact Or.inr (by simp [hs_one])
    · have hzeta_zero : riemannZeta s = 0 := by
        by_contra hζ
        exact (not_lt_of_ge
          (meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_nonneg_of_ne_zero
            hs_one hζ (hΦ_an s hsR))) hs.2
      exact Or.inl ⟨hsR.1, hsR.2, by simpa [riemannZeta.zeroes] using hzeta_zero⟩
  · intro hs
    rcases hs with hsZero | hsOne
    · let ρ : riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im) :=
        ⟨s, hsZero⟩
      have hsR : s ∈ Rectangle z w := ⟨hsZero.1, hsZero.2.1⟩
      have hρ_ne_one : ρ.val ≠ 1 := by
        intro hρ
        exact riemannZeta_one_ne_zero (hρ ▸ ρ.property.2.2)
      have horder :
          meromorphicOrderAt (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) s =
            (-1 : ℤ) :=
        meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_eq_neg_one_of_zero_ne_one
          ρ hρ_ne_one (hΦ_an s hsR) (hΦ_ne_zero ρ)
      exact ⟨hsR, by
        change meromorphicOrderAt (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) s < 0
        rw [horder]
        exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)⟩
    · have hs_eq : s = 1 := by simpa using hsOne
      subst hs_eq
      have horder :
          meromorphicOrderAt (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) (1 : ℂ) =
            (-1 : ℤ) :=
        meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_eq_neg_one_at_one
          (hΦ_an (1 : ℂ) hone_mem) hΦ_one_ne_zero
      exact ⟨hone_mem, by
        change meromorphicOrderAt (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) (1 : ℂ) < 0
        rw [horder]
        exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)⟩

lemma rectangleIntegral'_negLogDeriv_riemannZeta_mul_negCoeff_eq_zeroes_sum_sub_pole_one
    {z w : ℂ} {Φ : ℂ → ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hone_mem : (1 : ℂ) ∈ Rectangle z w)
    (hboundary_poles :
      Disjoint (RectangleBorder z w)
        (riemannZeta.zeroes_rect (Set.uIcc z.re w.re) (Set.uIcc z.im w.im) ∪
          ({1} : Set ℂ)))
    (hΦ_an : ∀ s ∈ Rectangle z w, AnalyticAt ℂ (fun u => Φ (-u)) s) :
    RectangleIntegral' (fun s => -logDeriv riemannZeta s * (-(Φ (-s)))) z w =
      riemannZeta.zeroes_sum (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)
        (fun ρ ↦ Φ (-ρ)) - Φ (-(1 : ℂ)) := by
  let F : ℂ → ℂ := fun s => -logDeriv riemannZeta s * (-(Φ (-s)))
  let I : Set ℝ := Set.uIcc z.re w.re
  let J : Set ℝ := Set.uIcc z.im w.im
  let P : Set ℂ := {u | meromorphicOrderAt F u < 0}
  have hζmero : ∀ s ∈ Rectangle z w, MeromorphicAt riemannZeta s := by
    intro s hs
    by_cases hs_one : s = 1
    · simpa [hs_one] using riemannZeta_meromorphicAt_one
    · exact (riemannZeta_analyticOn_compl_one s
        (by simpa [Set.mem_compl_iff] using hs_one)).meromorphicAt
  have hmero : MeromorphicOn F (Rectangle z w) := by
    intro s hs
    have hlog_mero : MeromorphicAt (logDeriv riemannZeta) s := by
      rw [logDeriv]
      exact (hζmero s hs).deriv.div (hζmero s hs)
    have hneg_mero : MeromorphicAt (fun u => -logDeriv riemannZeta u) s := by
      change MeromorphicAt (-(logDeriv riemannZeta)) s
      exact hlog_mero.neg
    have hcoeff_mero : MeromorphicAt (fun u => -(Φ (-u))) s :=
      (hΦ_an s hs).neg.meromorphicAt
    exact hneg_mero.mul hcoeff_mero
  have hfiniteOrder :
      ∀ s ∈ Rectangle z w, ∃ m : ℤ, meromorphicOrderAt riemannZeta s = m := by
    intro s hs
    by_cases hs_one : s = 1
    · exact ⟨-1, by simpa [hs_one] using riemannZeta_meromorphicOrderAt_one_eq_neg_one⟩
    · exact riemannZeta_finiteOrder_of_ne_one hs_one
  have hsimple : CH2.HasSimplePolesOn F (Rectangle z w) :=
    hasSimplePolesOn_negLogDeriv_mul_of_meromorphicOrderAt
      (f := riemannZeta) (ψ := fun s => -(Φ (-s)))
      hζmero hfiniteOrder (fun s hs => (hΦ_an s hs).neg)
  have hactual_subset_poles :
      Rectangle z w ∩ P ⊆ riemannZeta.zeroes_rect I J ∪ ({1} : Set ℂ) := by
    intro s hs
    have hsR : s ∈ Rectangle z w := hs.1
    by_cases hs_one : s = 1
    · exact Or.inr (by simp [hs_one])
    · have hzeta_zero : riemannZeta s = 0 := by
        by_contra hζ
        exact (not_lt_of_ge
          (meromorphicOrderAt_negLogDeriv_riemannZeta_mul_negCoeff_nonneg_of_ne_zero
            hs_one hζ (hΦ_an s hsR))) hs.2
      exact Or.inl ⟨hsR.1, hsR.2, by simpa [riemannZeta.zeroes] using hzeta_zero⟩
  have h_set_eq :
      Rectangle z w ∩ P = (riemannZeta.zeroes_rect I J ∪ ({1} : Set ℂ)) ∩ P := by
    ext s
    constructor
    · intro hs
      exact ⟨hactual_subset_poles hs, hs.2⟩
    · intro hs
      rcases hs.1 with hsZero | hsOne
      · exact ⟨⟨hsZero.1, hsZero.2.1⟩, hs.2⟩
      · have hs_eq : s = 1 := by simpa using hsOne
        exact ⟨hs_eq ▸ hone_mem, hs.2⟩
  have hboundary : Disjoint (RectangleBorder z w) {u | meromorphicOrderAt F u < 0} := by
    rw [Set.disjoint_left]
    intro s hsB hsPole
    have hsR : s ∈ Rectangle z w := rectangleBorder_subset_rectangle z w hsB
    have hsPoleSet : s ∈ riemannZeta.zeroes_rect I J ∪ ({1} : Set ℂ) := by
      exact hactual_subset_poles (show s ∈ Rectangle z w ∩ P
        from ⟨hsR, hsPole⟩)
    exact Set.disjoint_left.mp (by simpa [I, J] using hboundary_poles) hsB hsPoleSet
  have hzeroes_fin : (riemannZeta.zeroes_rect I J).Finite := by
    simpa [I, J] using zeroes_rect_uIcc_finite z w
  have hfinite : (Rectangle z w ∩ {u | meromorphicOrderAt F u < 0}).Finite := by
    exact (hzeroes_fin.union (Set.finite_singleton (1 : ℂ))).subset (by
      simpa [P] using hactual_subset_poles)
  have hres_zero : ∀ ρ : riemannZeta.zeroes_rect I J,
      CH2.residue F ρ = Φ (-ρ) * (riemannZeta.order ρ.val : ℂ) := by
    intro ρ
    have hρ_ne_one : ρ.val ≠ 1 := by
      intro hρ
      exact riemannZeta_one_ne_zero (hρ ▸ ρ.property.2.2)
    simpa [F] using
      (residue_negLogDeriv_riemannZeta_mul_negCoeff_eq_order_mul_of_zero_ne_one
        ρ hρ_ne_one (hΦ_an ρ.val ⟨ρ.property.1, ρ.property.2.1⟩).continuousAt)
  have hone_not_zero : (1 : ℂ) ∉ riemannZeta.zeroes_rect I J := by
    intro h
    exact riemannZeta_one_ne_zero h.2.2
  have hrect :
      RectangleIntegral' F z w =
        CH2.sumResiduesIn F (Rectangle z w ∩ P) := by
    simpa [F, P] using
      (CH2.RectangleIntegral'_eq_sumResiduesIn zRe_le_wRe zIm_le_wIm hmero hboundary
        hfinite hsimple)
  have hresidue_set :
      CH2.sumResiduesIn F (Rectangle z w ∩ P) =
        CH2.sumResiduesIn F (riemannZeta.zeroes_rect I J ∪ ({1} : Set ℂ)) := by
    refine CH2.sumResiduesIn_inter_eq_of_set_eq h_set_eq ?_
    intro s hsPoleCandidate hsNotPole
    have hsR : s ∈ Rectangle z w := by
      rcases hsPoleCandidate with hsZero | hsOne
      · exact ⟨hsZero.1, hsZero.2.1⟩
      · have hs_eq : s = 1 := by simpa using hsOne
        exact hs_eq ▸ hone_mem
    have hsNotPole' : ¬ meromorphicOrderAt F s < 0 := by
      simpa [P] using hsNotPole
    exact CH2.residue_eq_zero_of_not_pole_of_meromorphicAt (hmero s hsR)
      (le_of_not_gt hsNotPole')
  calc
    RectangleIntegral' F z w =
        CH2.sumResiduesIn F (Rectangle z w ∩ P) := hrect
    _ = CH2.sumResiduesIn F (riemannZeta.zeroes_rect I J ∪ ({1} : Set ℂ)) := hresidue_set
    _ = CH2.residue F (1 : ℂ) + CH2.sumResiduesIn F (riemannZeta.zeroes_rect I J) := by
      exact sumResiduesIn_union_singleton_eq_add hzeroes_fin hone_not_zero
    _ = -Φ (-(1 : ℂ)) +
        riemannZeta.zeroes_sum I J (fun ρ ↦ Φ (-ρ)) := by
      rw [residue_negLogDeriv_riemannZeta_mul_negCoeff_one
        (hΦ_an (1 : ℂ) hone_mem).continuousAt]
      rw [sumResiduesIn_zeroes_rect_eq_zeroes_sum_of_residue_eq hzeroes_fin hres_zero]
    _ = riemannZeta.zeroes_sum I J (fun ρ ↦ Φ (-ρ)) - Φ (-(1 : ℂ)) := by
      ring

end Kadiri
