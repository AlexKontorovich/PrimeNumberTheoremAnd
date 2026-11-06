module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/LocalCount.lean

H-RvM's local count for Mathlib's ζ:  N(t, t+1] ≤ A₀ log(|t| + 3) for all real t
(= Zeta23.RiemannVonMangoldt.local_count at Z := zetaZeroConfig; [Tit86, Thm 9.2]).

Route (never evaluating ζ left of σ = 0.19, so no Stirling is needed):
 * count only zeros with β ≥ 1/2 and double (Zeta23.ZeroConfig.N_le_two_mul_half, Zeta23/RvM/Halving.lean,
   via the ρ ↦ 1−ρ̄ symmetry);
 * Jensen-type zero count on a disc: the ported PNT+ `ZerosBound` (Zeta23/FromPNTPlus/StrongPNTPrefix.lean,
   Apache-2.0) applied to g(w) := ζ(c₀ + 1.9 w)/ζ(c₀), c₀ := 2 + (t+½)i, r = 0.84, R = 0.95:
   the β ≥ 1/2 part of the window lies in ‖w‖ ≤ 0.84 (1.5² + 0.5² ≤ (1.9·0.84)²), the big disc stays in
   σ ≥ 0.195 and at distance ≥ 1 from the pole for |t| ≥ 4;
 * ζ-growth ‖ζ(s)‖ ≤ C(|Im s|+3)^A on σ ≥ 0.15, ‖s−1‖ ≥ 1 and ‖ζ(2+it)‖ ≥ 1/3
   (Zeta23.RvM.zeta_growth_right / zeta_lower_bound_two, Zeta23/RvM/ZetaGrowth.lean);
 * |t| < 4 by the finite constant N(−4, 5].
-/
public import Zeta23.Prelude.InstancePriorities
public import Zeta23.Statement.SeamClosed
public import Zeta23.Defs.Counting
public import Zeta23.FromPNTPlus.StrongPNTPrefix
public import Zeta23.RvM.ZetaGrowth
public import Zeta23.RvM.Halving

@[expose] public section


open Complex Set Filter Topology Metric

noncomputable section

namespace Zeta23.RvM

/-- zeros of ζ in any compact set are finite (none accumulate, none near the pole). -/
theorem riemannZeta_zeros_finite_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  choose t ht hfin using riemannZeta_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hK.elim_nhds_subcover t (fun z _ => ht z)
  refine (I.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  rintro ρ ⟨hρK, hρ⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ⟩

/-- the rescaled function g(z) := ζ(s₀ + c z) · u. -/
def gfun (s₀ c u : ℂ) (z : ℂ) : ℂ := riemannZeta (s₀ + c * z) * u

lemma comp_affine_analyticAt {s₀ c z : ℂ} (h : s₀ + c * z ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (s₀ + c * z)) z := by
  have hζ : AnalyticAt ℂ riemannZeta (s₀ + c * z) := riemannZeta_analyticOnNhd_compl_one _ h
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) z := by fun_prop
  exact hζ.comp_of_eq haff rfl

lemma gfun_analyticAt {s₀ c u z : ℂ} (h : s₀ + c * z ≠ 1) : AnalyticAt ℂ (gfun s₀ c u) z := by
  have h1 := comp_affine_analyticAt h
  have h2 : AnalyticAt ℂ (fun _ : ℂ => u) z := analyticAt_const
  have := h1.mul h2
  exact this

/-- order transport: the order of g at w is the multiplicity of ζ at s₀ + c w. -/
lemma analyticOrderNatAt_gfun {s₀ c u w : ℂ} (hc : c ≠ 0) (hu : u ≠ 0) (h : s₀ + c * w ≠ 1) :
    analyticOrderNatAt (gfun s₀ c u) w = zeroMult (s₀ + c * w) := by
  unfold analyticOrderNatAt zeroMult gfun
  congr 1
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) w := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => riemannZeta (s₀ + c * z)) w := comp_affine_analyticAt h
  have hmul : (fun z ↦ riemannZeta (s₀ + c * z) * u) =
      (fun z => riemannZeta (s₀ + c * z)) * fun _ => u := rfl
  rw [hmul, analyticOrderAt_mul hcomp analyticAt_const]
  have hconst : analyticOrderAt (fun _ : ℂ => u) w = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hu
  rw [hconst, add_zero]
  have hderiv : deriv (fun z : ℂ => s₀ + c * z) w ≠ 0 := by
    rw [deriv_const_add, deriv_const_mul _ differentiableAt_id, deriv_id'']; simpa using hc
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) haff hderiv
  simpa [Function.comp_def] using this

/-- ‖z‖ ≤ |Re z| + |Im z| packaged for the window geometry: a point ρ with 0 < Re ρ < 1 and
t < Im ρ ≤ t + 1 lies within distance 3 of 2 + it. -/
lemma norm_sub_center_le {ρ : ℂ} {t : ℝ} (h1 : 0 < ρ.re) (h2 : ρ.re < 1) (h3 : t < ρ.im)
    (h4 : ρ.im ≤ t + 1) : ‖ρ - (2 + t * I)‖ ≤ 3 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (ρ - (2 + t * I)).re = ρ.re - 2 := by simp
  have him : (ρ - (2 + t * I)).im = ρ.im - t := by simp
  rw [hre, him, abs_of_neg (by linarith), abs_of_pos (by linarith)]
  linarith



/-- zeros with β ≥ 1/2 in the window (t, t+1], with multiplicity, as a real number. -/
def NhalfR (t : ℝ) : ℝ := ∑ᶠ ρ ∈ zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re}, (zeroMult ρ : ℝ)

/-- the β ≥ 1/2 half-window count is ≪ log(|t|+3) for |t| ≥ 4 (disc argument). -/
theorem half_count_large :
    ∃ A₁ : ℝ, ∀ t : ℝ, 4 ≤ |t| → NhalfR t ≤ A₁ * Real.log (|t| + 3) := by
  obtain ⟨A, C, hC, hgrowth⟩ := zeta_growth_right
  have hL := zeta_lower_bound_two
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  -- constants
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  refine ⟨1 / Real.log (R / r) * (|Real.log (3 * C)| + 2 * A'), fun t ht => ?_⟩
  -- centre and rescaling
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have hζc₀ : (1/3 : ℝ) ≤ ‖riemannZeta c₀‖ := by simpa [hc₀] using hL (t + 1/2)
  have hζc₀ne : riemannZeta c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζc₀; norm_num at hζc₀
  set u : ℂ := (riemannZeta c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hζc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set g : ℂ → ℂ := gfun c₀ κ u with hg
  -- geometry: ‖c₀ + κ z - 1‖ ≥ |t + 1/2| - 1.9 ‖z‖
  have hc₀1 : |t + 1/2| ≤ ‖c₀ - 1‖ := by
    have : (c₀ - 1).im = t + 1/2 := by simp [hc₀]
    rw [← this]; exact Complex.abs_im_le_norm _
  have ht' : 3.5 ≤ |t + 1/2| := by
    rcases le_abs'.mp ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hdist : ∀ z : ℂ, ‖z‖ ≤ 1 → |t + 1/2| - 1.9 * ‖z‖ ≤ ‖c₀ + κ * z - 1‖ := by
    intro z hz
    have h1 : ‖c₀ - 1‖ - ‖κ * z‖ ≤ ‖c₀ + κ * z - 1‖ := by
      have := norm_sub_norm_le (c₀ - 1) (-(κ * z))
      rw [norm_neg] at this
      have e : c₀ - 1 - -(κ * z) = c₀ + κ * z - 1 := by ring
      rw [e] at this; linarith
    rw [norm_mul, hnormκ] at h1; linarith
  have hne1 : ∀ z : ℂ, ‖z‖ ≤ 1 → c₀ + κ * z ≠ 1 := by
    intro z hz h
    have := hdist z hz
    rw [h, sub_self, norm_zero] at this
    nlinarith
  -- hypotheses of ZerosBound
  have hfAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact gfun_analyticAt (hne1 z hz)
  have hg0 : g 0 = 1 := by simp [hg, gfun, hu, hζc₀ne]
  have hfin : (SetOfZeros 1 g).Finite := by
    have hK := riemannZeta_zeros_finite_of_isCompact (isCompact_closedBall c₀ (1.9 : ℝ))
    refine (hK.image fun ρ => (ρ - c₀) / κ).subset ?_
    rintro z ⟨hz, hgz⟩
    refine ⟨c₀ + κ * z, ⟨?_, hne1 z hz, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hnormκ]; nlinarith [norm_nonneg z]
    · simpa [hg, gfun, hu0] using hgz
    · show (c₀ + κ * z - c₀) / κ = z
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hκ0]
  set B : ℝ := 3 * C * (|t| + 6) ^ A' with hB
  have hBpos : 0 < B := by positivity
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num [hR])
    set s : ℂ := c₀ + κ * z with hs
    have hsre : (0.15:ℝ) ≤ s.re := by
      have : s.re = 2 + 1.9 * z.re := by norm_num [hs, hc₀, hκ]
      rw [this]
      obtain ⟨h1, -⟩ := abs_le.mp ((abs_re_le_norm z).trans hz)
      rw [hR] at h1; nlinarith
    have hs1 : 1 ≤ ‖s - 1‖ := by have := hdist z hz1; rw [hR] at hz; nlinarith
    have hsim : |s.im| + 3 ≤ |t| + 6 := by
      have : s.im = t + 1/2 + 1.9 * z.im := by norm_num [hs, hc₀, hκ]
      rw [this]
      have hzi := (abs_im_le_norm z).trans hz; rw [hR] at hzi
      have h1 := abs_add_le (t + 1/2) (1.9 * z.im)
      have h2 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]; nlinarith
      have h3 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    have h1 : ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A := hgrowth s hsre hs1
    have hbase : 1 ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
    have h2 : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' := Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
    have h3 : (|s.im| + 3) ^ A' ≤ (|t| + 6) ^ A' := Real.rpow_le_rpow (by linarith [abs_nonneg s.im]) hsim hA'0
    calc ‖g z‖ = ‖riemannZeta s‖ * ‖u‖ := by simp [hg, gfun, hs]
      _ ≤ (C * (|t| + 6) ^ A') * 3 := by
          apply mul_le_mul (h1.trans ((mul_le_mul_of_nonneg_left (h2.trans h3) hC.le))) hnu (norm_nonneg _)
          positivity
      _ = B := by rw [hB]; ring
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) (by norm_num [hr])
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hg0 hfin hfz
  -- the window's β ≥ 1/2 part maps injectively into the zero finset of g
  set W : Set ℂ := zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re} with hW
  have hWfin : W.Finite := (zetaZeroConfig.window_finite t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinj : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ hκ0] using this
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    simp only [Set.Finite.mem_toFinset]
    have hρ : IsNontrivialZero ρ := hρZ
    refine ⟨?_, ?_⟩
    · -- ‖φ ρ‖ ≤ 0.84
      simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := hρre.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show g (φ ρ) = 0
      simp only [hg, gfun, hφinv]; rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, (zeroMult ρ : ℝ) = (analyticOrderNatAt g (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, -, -⟩, -⟩
    have hρ : IsNontrivialZero ρ := hρZ
    rw [analyticOrderNatAt_gfun hκ0 hu0 (by rw [hφinv]; exact hρ.not_trivial.2), hφinv]
  -- compare the sums
  have hsum : NhalfR t ≤ ((∑ ρ' ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset,
      analyticOrderNatAt g ρ' : ℕ) : ℝ) := by
    unfold NhalfR
    rw [← hW, finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt g w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  -- log B ≤ (|log 3C| + 2A') log(|t|+3)
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hlog6 : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity); nlinarith [abs_nonneg t]
  have hlogB : Real.log B ≤ (|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
    have h1 := le_abs_self (Real.log (3 * C))
    have h2 : |Real.log (3 * C)| ≤ |Real.log (3 * C)| * Real.log (|t| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog3
    have h3 : A' * Real.log (|t| + 6) ≤ A' * (2 * Real.log (|t| + 3)) :=
      mul_le_mul_of_nonneg_left hlog6 hA'0
    linarith
  calc NhalfR t ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
    _ = _ := by ring

/-- small heights: N(t,t+1] ≤ N(−4,5] for |t| ≤ 4. -/
theorem count_small (t : ℝ) (ht : |t| ≤ 4) : (Ncount t (t + 1) : ℝ) ≤ Ncount (-4) 5 := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have hsub : zetaZeroConfig.window t (t + 1) ⊆ zetaZeroConfig.window (-4) 5 := by
    rintro ρ ⟨hρ, ha, hb⟩; exact ⟨hρ, by linarith, by linarith⟩
  have h' : zetaZeroConfig.N t (t + 1) ≤ zetaZeroConfig.N (-4) 5 :=
    zetaZeroConfig.finsum_mult_mono (-4) 5 hsub subset_rfl
  rw [zetaZeroConfig_N, zetaZeroConfig_N] at h'
  exact_mod_cast h'

/-- **H-RvM local count for ζ** ([Tit86, Thm 9.2]): ∃ A₀ ≥ 1, ∀ t ∈ ℝ, N(t, t+1] ≤ A₀ log(|t| + 3),
zeros counted with multiplicity (analytic order of Mathlib's riemannZeta), two-sided in t. -/
theorem zeta_local_zero_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₁, hA₁⟩ := half_count_large
  set K : ℝ := (Ncount (-4) 5 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max 1 (max (2 * A₁) K), le_max_left _ _, fun t => ?_⟩
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hhalf : (Ncount t (t + 1) : ℝ) ≤ 2 * NhalfR t := by
    have := zetaZeroConfig.N_le_two_mul_half t (t + 1)
    simpa [NhalfR, zetaZeroConfig_N] using this
  rcases le_or_gt 4 |t| with ht | ht
  · calc (Ncount t (t + 1) : ℝ) ≤ 2 * NhalfR t := hhalf
      _ ≤ 2 * (A₁ * Real.log (|t| + 3)) := by
          have := hA₁ t ht; nlinarith
      _ = (2 * A₁) * Real.log (|t| + 3) := by ring
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_left _ _) (le_max_right _ _)
  · calc (Ncount t (t + 1) : ℝ) ≤ K := count_small t ht.le
      _ ≤ K * Real.log (|t| + 3) := le_mul_of_one_le_right hK0 hlog3
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The same, in H-RvM's vocabulary (Z.N at Z := zetaZeroConfig). -/
theorem zetaZeroConfig_local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  simpa only [zetaZeroConfig_N] using zeta_local_zero_count

end Zeta23.RvM
