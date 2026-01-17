import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Module.Connected
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.PNT1_ComplexAnalysis

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

lemma DRinD1 (R : ℝ) (hR : 0 < R) (hR' : R < 1) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) 1 := by
  exact Metric.closedBall_subset_ball hR'
def zerosetKfR (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}
lemma lemKinDR (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ Metric.closedBall (0 : ℂ) R := by
  intro ρ hρ
  -- hρ : ρ ∈ zerosetKfR R hR f
  -- By definition of zerosetKfR, this means ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0
  rw [zerosetKfR] at hρ
  -- Now hρ : ρ ∈ {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}
  exact hρ.1
lemma lemKRinK1 (R : ℝ) (hR : 0 < R) (hR' : R < 1) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} := by
  intro ρ hρ
  simp only [zerosetKfR, Set.mem_setOf_eq] at hρ ⊢
  constructor
  · exact DRinD1 R hR hR' hρ.1
  · exact hρ.2

lemma lem_bolzano_weierstrass {D : Set ℂ} (hD : IsCompact D) {Z : Set ℂ} (hZ_inf : Z.Infinite) (hZ_sub_D : Z ⊆ D) :
    ∃ ρ₀ ∈ D, AccPt ρ₀ (Filter.principal Z) :=
  Set.Infinite.exists_accPt_of_subset_isCompact hZ_inf hD hZ_sub_D
lemma lem_zeros_have_limit_point (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f)) := by
  apply lem_bolzano_weierstrass
  · -- Show IsCompact (Metric.closedBall (0 : ℂ) R)
    rw [← lem_ballDR R hR]
    exact lem_DRcompact R hR
  · exact h_Kf_inf
  · exact lemKinDR R hR f

open Filter Metric Set Bornology Function

lemma lem_identity_theorem (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  -- The open ball is a subset of the closed ball
  have h_subset : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall
  -- So f is analytic on a neighborhood of the open ball
  have hf_open : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := AnalyticOnNhd.mono hf h_subset
  -- The open ball is preconnected (since it's connected)
  have h_conn : IsConnected (Metric.ball (0 : ℂ) 1) := Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) := h_conn.isPreconnected
  -- Convert accumulation point to closure membership
  have h_zeros_subset : {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} ⊆ {z | f z = 0} := by
    intro z hz
    exact hz.2
  -- From AccPt over the smaller set, get AccPt over the zero set using filter monotonicity
  have h_acc_zero : AccPt ρ₀ (Filter.principal ({z | f z = 0})) := by
    exact AccPt.mono h_acc (principal_mono.2 h_zeros_subset)
  -- AccPt principal is equivalent to ClusterPt on the punctured set; then use closure equivalence
  have h_closure : ρ₀ ∈ closure ({z | f z = 0} \ {ρ₀}) := by
    -- accPt_principal_iff_clusterPt : AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ {x}))
    have h_cluster : ClusterPt ρ₀ (Filter.principal ({z | f z = 0} \ {ρ₀})) :=
      (accPt_principal_iff_clusterPt).mp h_acc_zero
    exact (mem_closure_iff_clusterPt).2 h_cluster
  -- Apply the identity theorem
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hf_open h_preconn hρ₀_in_D1 h_closure
lemma lem_identity_theoremR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_DR : ρ₀ ∈ Metric.closedBall (0 : ℂ) R)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1 := DRinD1 R hR hR' hρ₀_in_DR
  exact lem_identity_theorem f hf ρ₀ hρ₀_in_D1 h_acc
lemma lem_identity_theoremKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_rho0 : ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  -- Extract the existence of ρ₀
  obtain ⟨ρ₀, hρ₀_in_R, h_acc⟩ := h_exists_rho0
  -- Apply lem_identity_theoremR
  apply lem_identity_theoremR R hR hR' f hf ρ₀ hρ₀_in_R
  -- Convert the accumulation point using monotonicity and lemKRinK1
  exact AccPt.mono h_acc (principal_mono.2 (lemKRinK1 R hR hR' f))
lemma lem_identity_infiniteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have h_exists_rho0 := lem_zeros_have_limit_point R hR f h_Kf_inf
  exact lem_identity_theoremKR R hR hR' f hf h_exists_rho0
lemma lem_Contra_finiteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0) :
    Set.Finite (zerosetKfR R hR f) := by
  -- Use contrapositive of lem_identity_infiniteKR
  by_contra h_not_finite
  -- h_not_finite: ¬Set.Finite (zerosetKfR R hR f)
  -- This is equivalent to Set.Infinite (zerosetKfR R hR f) by definition
  have h_Kf_inf : Set.Infinite (zerosetKfR R hR f) := h_not_finite
  -- Apply lem_identity_infiniteKR
  have h_eq_zero := lem_identity_infiniteKR R hR hR' f hf h_Kf_inf
  -- h_eq_zero : EqOn f 0 (Metric.ball (0 : ℂ) 1)
  -- But we have h_exists_nonzero which contradicts this
  obtain ⟨z, hz_in_ball, hz_nonzero⟩ := h_exists_nonzero
  have h_f_z_zero : f z = 0 := h_eq_zero hz_in_ball
  exact hz_nonzero h_f_z_zero

open Classical

lemma lem_frho_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≠ ⊤ := by
  intro ρ h_rho_in_KfR1
  -- ρ lies in the closed ball of radius R1
  have hρ_closed_R1 : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
  -- R1 < R and R < 1 implies R1 < 1
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
  -- Hence ρ ∈ ball 0 1
  have hρ_ball1 : ρ ∈ Metric.ball (0 : ℂ) 1 := by
    have hdist_le : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_closed_R1)
    have hdist_lt : dist ρ (0 : ℂ) < 1 := by linarith
    simpa [Metric.mem_ball] using hdist_lt
  -- f is analytic at ρ
  have hf_at_ρ : AnalyticAt ℂ f ρ := by
    -- ρ ∈ closedBall 0 1 since R1 < 1
    have hsubset : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)
    have hρ_closed1 : ρ ∈ Metric.closedBall (0 : ℂ) 1 := hsubset hρ_closed_R1
    exact h_f_analytic ρ hρ_closed1
  -- Suppose, for contradiction, that the order is ⊤
  by_contra htop
  -- From order = ⊤ we get that f is eventually zero near ρ
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    have h_equiv : (analyticOrderAt f ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, f z = 0) := by
      simp [analyticOrderAt, hf_at_ρ]
    exact h_equiv.mp (by simpa using htop)
  -- f is analytic on a neighborhood of the unit ball
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1) hz
    exact h_f_analytic z hz'
  -- The unit ball is preconnected
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (Metric.isConnected_ball (by exact (zero_lt_one : (0 : ℝ) < 1))).isPreconnected
  -- By identity principle, f = 0 on the unit ball
  have h_eqOn_zero : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_ball1
      h_eventually_zero
  -- Hence f 0 = 0, contradiction
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have : f 0 = 0 := by
    have h := h_eqOn_zero h0_in_ball
    simpa [Pi.zero_apply] using h
  exact h_f_nonzero_at_zero this

lemma analyticOrderAt_ge_one_of_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) : analyticOrderAt f z ≥ 1 := by
  -- Show that analyticOrderAt f z ≠ 0 using the characterization
  have h_order_ne_zero : analyticOrderAt f z ≠ 0 := by
    intro h_order_zero
    -- If the order is 0, then f z ≠ 0 by the characterization
    have h_f_ne_zero : f z ≠ 0 := by
      rw [← AnalyticAt.analyticOrderAt_eq_zero hf]
      exact h_order_zero
    -- This contradicts hz : f z = 0
    exact h_f_ne_zero hz
  -- Since analyticOrderAt f z is finite (≠ ⊤) and ≠ 0, it must be ≥ 1
  cases' h : analyticOrderAt f z with n
  · -- Case: analyticOrderAt f z = ⊤
    -- This contradicts hfinite
    rw [h] at hfinite
    exact False.elim (hfinite rfl)
  · -- Case: analyticOrderAt f z = ↑n for some n : ℕ
    -- We need to show ↑n ≥ 1
    -- From h_order_ne_zero and h : analyticOrderAt f z = ↑n, we get ↑n ≠ 0, so n ≠ 0
    rw [h] at h_order_ne_zero
    have n_ne_zero : n ≠ 0 := by
      intro n_zero
      rw [n_zero, Nat.cast_zero] at h_order_ne_zero
      exact h_order_ne_zero rfl
    -- Since n ≠ 0, we have n ≥ 1
    have n_ge_one : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr n_ne_zero
    -- Therefore ↑n ≥ ↑1 = 1
    exact Nat.cast_le.mpr n_ge_one


lemma lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≥ 1 := by
  intro ρ h_rho_in_KfR1
  -- Use lem_frho_zero as mentioned in informal proof
  have h_f_rho_zero : f ρ = 0 := lem_frho_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ρ h_rho_in_KfR1
  -- Use lem_m_rho_is_nat as mentioned in informal proof
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 ρ h_rho_in_KfR1
  -- f is analytic at ρ
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
    -- With R < 1 and R1 < R, we have R1 < 1
    have h_R1_lt_1 : R1 < 1 := by linarith
    have h_rho_in_R1 : ρ ∈ Metric.closedBall 0 R1 := h_rho_in_KfR1.1
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) h_rho_in_R1
  -- Apply the helper lemma (combining results from both mentioned lemmas)
  exact analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite

/-! ### The quotient `Cf` (no core wrapper) -/

/-- The “deflated” quotient: divide `f` by the product of `(z-ρ)^{m_ρ}`, and at a zero `z=σ`
    use the local factor function `h_σ σ` in the numerator (so the expression extends analytically). -/
noncomputable def Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))  -- for each σ in the zero set, a local factor function
    (z : ℂ) : ℂ :=
  if hz : z ∈ zerosetKfR R1 (by linarith) f then
    h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase z), (z - ρ) ^ (analyticOrderAt f ρ).toNat
  else
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat

/-! ### Helper lemmas used by the Cf proofs (statements only) -/

lemma lem_analDiv (R : ℝ) (hR_pos : 0 < R) (hR_lt_1 : R < 1) (w : ℂ)
    (hw : w ∈ Metric.closedBall (0 : ℂ) R)
    (h : ℂ → ℂ) (g : ℂ → ℂ)
    (hh : AnalyticAt ℂ h w) (hg : AnalyticAt ℂ g w) (hg_ne : g w ≠ 0) :
    AnalyticAt ℂ (fun z => h z / g z) w := by
  simpa using hh.div hg hg_ne

lemma lem_denomAnalAt (S : Finset ℂ) (n : ℂ → ℕ)
    (hn_pos : ∀ s ∈ S, 0 < n s) (w : ℂ) (hw : w ∉ S) :
    AnalyticAt ℂ (fun z => ∏ s ∈ S, (z - s) ^ (n s)) w ∧
    (∏ s ∈ S, (w - s) ^ (n s)) ≠ 0 := by
  constructor
  · -- First part: AnalyticAt
    -- Use Finset.analyticAt_prod
    let f : ℂ → ℂ → ℂ := fun s z => (z - s) ^ (n s)
    have h_each_analytic : ∀ s ∈ S, AnalyticAt ℂ (f s) w := by
      intro s hs
      simp only [f]
      -- Need to show AnalyticAt ℂ (fun z => (z - s) ^ (n s)) w
      have h_sub : AnalyticAt ℂ (fun z => z - s) w := by
        exact AnalyticAt.sub analyticAt_id analyticAt_const
      -- Apply pow with the natural number n s
      exact h_sub.pow (n s)
    have h_prod := Finset.analyticAt_prod S h_each_analytic
    convert h_prod using 1
    ext z
    simp [f]
  · -- Second part: nonzero product
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    apply pow_ne_zero
    -- Need w - s ≠ 0
    intro h_eq
    -- Use sub_eq_zero: a - b = 0 ↔ a = b
    have h_w_eq_s : w = s := by
      rwa [← sub_eq_zero]
    -- This contradicts hw : w ∉ S since s ∈ S
    rw [h_w_eq_s] at hw
    exact hw hs

lemma lem_ratioAnalAt (w : ℂ) (R R1 : ℝ) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h w)
    (S : Finset ℂ) (hS : ↑S ⊆ Metric.closedBall (0 : ℂ) R1) (n : ℂ → ℕ)
    (hn_pos : ∀ s ∈ S, 0 < n s)
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1 \ ↑S) :
    AnalyticAt ℂ (fun z => h z / ∏ s ∈ S, (z - s) ^ (n s)) w := by
  classical
  -- Denominator is analytic at w and nonzero at w
  have hden := lem_denomAnalAt (S := S) (n := n)
      (hn_pos := hn_pos) (w := w)
      (hw := by simpa using hw.2)
  -- Apply the division rule for analytic functions
  exact AnalyticAt.div hh hden.1 hden.2

lemma lem_analytic_zero_factor (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ) (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∃ h_σ : ℂ → ℂ, AnalyticAt ℂ h_σ σ ∧ h_σ σ ≠ 0 ∧
    ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ z := by
  classical
  -- f is analytic at σ
  have hσ_closed_R1 : σ ∈ Metric.closedBall (0 : ℂ) R1 := hσ.1
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
  have hσ_closed1 : σ ∈ Metric.closedBall (0 : ℂ) 1 :=
    (Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)) hσ_closed_R1
  have hfσ : AnalyticAt ℂ f σ := h_f_analytic σ hσ_closed1
  -- the order at σ is finite
  have h_order_finite : analyticOrderAt f σ ≠ ⊤ :=
    lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 σ hσ
  -- use the characterization of finite order to get the factorization
  rcases (hfσ.analyticOrderAt_ne_top).mp h_order_finite with ⟨g, hgσ, hgσ_ne, h_eq⟩
  -- turn scalar multiplication into multiplication on ℂ and rewrite the exponent
  have h_eq' : ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z := by
    refine h_eq.mono ?_
    intro z hz
    simpa [smul_eq_mul, analyticOrderNatAt] using hz
  exact ⟨g, hgσ, hgσ_ne, h_eq'⟩

/-! ### Cf lemmas (renamed to use `Cf` directly) -/

lemma lem_Cf_analytic_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) z := by

  -- Apply lem_ratioAnalAt to get analyticity of the ratio function
  have h_ratio_analytic : AnalyticAt ℂ (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) z := by
    apply lem_ratioAnalAt z R R1 hR1_lt_R hR_lt_1 f

    -- f is analytic at z
    · apply h_f_analytic
      exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1

    -- The finite zero set is contained in closedBall 0 R1
    · intro ρ hρ
      have h_mem : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
      exact h_mem.1

    -- All orders are positive
    · intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hs
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros

      cases' h_cases : analyticOrderAt f s with n
      · -- Case: order is ∞
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      · -- Case: order is finite n ≥ 1
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp [h_cases]
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1)

    -- z is in closedBall 0 1 but not in the zero set
    · constructor
      · exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1
      · -- Show z ∉ ↑h_finite_zeros.toFinset
        intro h_z_in_finset
        have h_z_in_zeros : z ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp h_z_in_finset
        exact hz.2 h_z_in_zeros

  -- Show that the ratio function equals Cf in a neighborhood of z
  have h_eventually_eq : (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds z]
    (fun w => Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w) := by
    -- Since the zero set is finite, its complement is open
    have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2
    have h_open : IsOpen (Set.compl (zerosetKfR R1 (by linarith) f)) := h_finite_zeros.isClosed.isOpen_compl
    apply Filter.eventually_of_mem (h_open.mem_nhds hz_not_in)
    intro w hw_not_in_compl
    -- Convert from membership in complement to non-membership
    have hw_not_in_zeros : w ∉ zerosetKfR R1 (by linarith) f := hw_not_in_compl
    -- Since w ∉ zerosetKfR R1, Cf w uses the else branch
    show f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat =
         Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w
    -- Apply the definition of Cf using dif_neg for dependent if-then-else
    rw [Cf, dif_neg hw_not_in_zeros]

  -- Transfer analyticity
  exact h_ratio_analytic.congr h_eventually_eq

lemma lem_Cf_at_sigma_onK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z = σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  refine Filter.Eventually.of_forall ?_
  intro z hz
  subst hz
  simp [Cf, hσ]

lemma lem_K_isolated
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (σ ρ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f)
    (hρ : ρ ∈ zerosetKfR R1 (by linarith) f) (hne : σ ≠ ρ) :
    ∀ᶠ z in nhds σ, z ≠ ρ := eventually_ne_nhds hne

lemma lem_Cf_at_sigma_offK0
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z /
      ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  -- Get the factorization from h_σ_spec
  obtain ⟨h_σ_analytic, h_σ_ne_zero, h_f_eq⟩ := h_σ_spec σ hσ

  -- h_σ σ is continuous at σ and nonzero there, so it's eventually nonzero
  have h_σ_eventually_nonzero : ∀ᶠ z in nhds σ, h_σ σ z ≠ 0 := by
    have h_cont : ContinuousAt (h_σ σ) σ := h_σ_analytic.continuousAt
    exact h_cont.eventually_ne h_σ_ne_zero

  -- For z ≠ σ near σ, f z ≠ 0 due to the factorization
  have h_f_eventually_nonzero : ∀ᶠ z in nhds σ, z ≠ σ → f z ≠ 0 := by
    filter_upwards [h_f_eq, h_σ_eventually_nonzero] with z h_fz_eq h_σz_nonzero
    intro hz_ne
    rw [h_fz_eq]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact sub_ne_zero.mpr hz_ne
    · exact h_σz_nonzero

  -- Therefore, z ≠ σ near σ implies z ∉ zerosetKfR
  have h_eventually_not_in_zeroset : ∀ᶠ z in nhds σ, z ≠ σ → z ∉ zerosetKfR R1 (by linarith) f := by
    filter_upwards [h_f_eventually_nonzero] with z h_fz_nonzero
    intro hz_ne hz_in_zeroset
    exact h_fz_nonzero hz_ne hz_in_zeroset.2

  -- Combine everything
  filter_upwards [h_f_eq, h_eventually_not_in_zeroset] with z h_fz_eq h_not_in_zeroset
  intro hz_ne
  -- Since z ≠ σ, we have z ∉ zerosetKfR, so Cf uses the else branch
  have hz_not_in_K : z ∉ zerosetKfR R1 (by linarith) f := h_not_in_zeroset hz_ne
  -- Unfold Cf using the else branch and substitute f z
  unfold Cf
  simp [hz_not_in_K, h_fz_eq]

lemma lem_prod_no_sigma1
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) (z : ℂ) :
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat =
    (z - σ) ^ (analyticOrderAt f σ).toNat *
    ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  classical
  have hmem : σ ∈ h_finite_zeros.toFinset :=
    (Set.Finite.mem_toFinset (hs := h_finite_zeros)).2 hσ
  simpa using
    (Finset.mul_prod_erase (s := h_finite_zeros.toFinset)
      (f := fun ρ => (z - ρ) ^ (analyticOrderAt f ρ).toNat) (a := σ) hmem).symm

lemma lem_prod_no_sigma2
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) (z : ℂ)
    (hz : z ∉ zerosetKfR R1 (by linarith) f) :
    (z - σ) ^ (analyticOrderAt f σ).toNat /
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat =
    1 / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  -- Use lem_prod_no_sigma1 to factorize the denominator
  have h_factor := @lem_prod_no_sigma1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ z
  rw [h_factor]

  -- Now we have (z - σ)^n / ((z - σ)^n * ∏ ρ ∈ erase σ, (z - ρ)^m_ρ)
  -- Convert a / (a * b) to (a / a) / b using div_mul_eq_div_div
  rw [div_mul_eq_div_div]

  -- Show (z - σ)^n ≠ 0
  have h_nonzero : (z - σ) ^ (analyticOrderAt f σ).toNat ≠ 0 := by
    apply pow_ne_zero
    intro h_eq
    -- If z - σ = 0, then z = σ, contradicting hz
    have h_z_eq_sigma : z = σ := sub_eq_zero.mp h_eq
    rw [h_z_eq_sigma] at hz
    exact hz hσ

  -- Use div_self to get (z - σ)^n / (z - σ)^n = 1
  rw [div_self h_nonzero, one_div]

lemma lem_Cf_at_sigma_offK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  -- Get the form from lem_Cf_at_sigma_offK0
  have h_cf_form := @lem_Cf_at_sigma_offK0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  filter_upwards [h_cf_form] with z h_cf_z
  intro hz_ne_sigma
  -- Apply the form from lem_Cf_at_sigma_offK0
  rw [h_cf_z hz_ne_sigma]
  -- Use product decomposition lem_prod_no_sigma1
  have h_prod_decomp := @lem_prod_no_sigma1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ z
  -- Substitute the full product with the decomposed form in the denominator
  rw [h_prod_decomp]
  -- Now apply mul_div_mul_left directly to cancel (z - σ)^m terms
  apply mul_div_mul_left
  -- Show (z - σ)^m ≠ 0
  apply pow_ne_zero
  exact sub_ne_zero.mpr hz_ne_sigma

lemma lem_Cf_at_sigma
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ,
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  -- Get the eventually statements for both cases
  have h_on := @lem_Cf_at_sigma_onK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
  have h_off := @lem_Cf_at_sigma_offK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
  -- Combine them using filter_upwards
  filter_upwards [h_on, h_off] with z hz_on hz_off
  by_cases h : z = σ
  · -- Case z = σ: use h_on, but need to convert h_σ z z to h_σ σ z
    have eq_result := hz_on h
    -- When z = σ, we have h_σ z z = h_σ σ σ and h_σ σ z = h_σ σ σ
    rw [h] at eq_result ⊢
    exact eq_result
  · -- Case z ≠ σ: directly use h_off
    exact hz_off h

lemma lem_h_ratio_anal
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f)
    (g : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g σ) :
    AnalyticAt ℂ
      (fun z => g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (z - ρ) ^ (analyticOrderAt f ρ).toNat) σ := by
  -- Use lem_denomAnalAt to show the denominator is analytic and nonzero at σ
  have hden := lem_denomAnalAt (S := h_finite_zeros.toFinset.erase σ)
    (n := fun ρ => (analyticOrderAt f ρ).toNat)
    (hn_pos := by
      intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := by
        have h_mem_erase : s ∈ h_finite_zeros.toFinset.erase σ := hs
        have h_mem_orig : s ∈ h_finite_zeros.toFinset := Finset.mem_of_mem_erase h_mem_erase
        exact h_finite_zeros.mem_toFinset.mp h_mem_orig
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      cases' h_cases : analyticOrderAt f s with n
      · -- Case: order is ∞
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      · -- Case: order is finite n ≥ 1
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp [h_cases]
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1))
    (w := σ)
    (hw := by
      simp [Finset.mem_erase])
  -- Apply the division rule for analytic functions
  exact AnalyticAt.div hg_analytic hden.1 hden.2

lemma lem_Cf_analytic_at_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) σ := by
  -- Get the eventual equality from lem_Cf_at_sigma with all explicit arguments
  have h_eventually_eq := @lem_Cf_at_sigma R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  -- Get analyticity of the ratio function from lem_h_ratio_anal
  obtain ⟨h_σ_analytic, _, _⟩ := h_σ_spec σ hσ
  have h_ratio_analytic := @lem_h_ratio_anal R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ (h_σ σ) h_σ_analytic

  -- Reverse the direction of the eventual equality
  have h_rev_eq : (fun z => h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds σ]
                  (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) := by
    filter_upwards [h_eventually_eq] with z h_z
    exact h_z.symm

  -- Use AnalyticAt.congr to transfer analyticity
  exact AnalyticAt.congr h_ratio_analytic h_rev_eq

lemma lem_Cf_is_analytic
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) z := by
  -- Case split: either z is in the zero set or not
  by_cases h_case : z ∈ zerosetKfR R1 (by linarith) f

  case pos =>
    -- z ∈ zerosetKfR R1 f: Use lem_Cf_analytic_at_K
    exact lem_Cf_analytic_at_K h_finite_zeros h_σ h_σ_spec z h_case

  case neg =>
    -- z ∉ zerosetKfR R1 f: Use lem_Cf_analytic_off_K
    -- We need to show z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 f
    have hz_in_complement : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f := by
      constructor
      · exact hz  -- z ∈ Metric.closedBall (0 : ℂ) R
      · exact h_case  -- z ∉ zerosetKfR R1 f
    exact lem_Cf_analytic_off_K h_finite_zeros h_σ h_σ_spec z hz_in_complement

lemma lem_f_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {h_f_nonzero_at_zero : f 0 ≠ 0}
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    f z ≠ 0 := by
  exact fun h => hz.2 ⟨hz.1, h⟩

lemma lem_Cf_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
  -- Since z ∉ zerosetKfR R1, Cf uses the else branch
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2

  -- Unfold Cf definition using the else branch
  have h_cf_eq : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp [hz_not_in]

  rw [h_cf_eq]

  -- Apply div_ne_zero: need numerator ≠ 0 and denominator ≠ 0
  apply div_ne_zero

  -- Numerator: f z ≠ 0 by lem_f_nonzero_off_K with explicit parameters
  · apply @lem_f_nonzero_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero z hz

  -- Denominator: product is nonzero
  · apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    -- Need (z - ρ) ^ (analyticOrderAt f ρ).toNat ≠ 0
    apply pow_ne_zero
    -- Need z - ρ ≠ 0, i.e., z ≠ ρ
    intro h_eq
    -- From h_eq : z - ρ = 0, we get z = ρ using sub_eq_zero
    have hz_eq_rho : z = ρ := by
      rwa [sub_eq_zero] at h_eq
    -- But ρ ∈ zerosetKfR R1 (from hρ) and z ∉ zerosetKfR R1 (from hz_not_in)
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
    rw [hz_eq_rho] at hz_not_in
    exact hz_not_in hρ_in

lemma lem_Cf_nonzero_on_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ σ ≠ 0 := by
  have hnum : h_σ σ σ ≠ 0 := (h_σ_spec σ hσ).2.1
  have hden :
      (∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (σ - ρ) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro ρ hρmem
    have hρ_ne_σ : ρ ≠ σ := (Finset.mem_erase.mp hρmem).1
    have hσ_ne_ρ : σ ≠ ρ := hρ_ne_σ.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hσ_ne_ρ)
  have :
      h_σ σ σ /
          ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
            (σ - ρ) ^ (analyticOrderAt f ρ).toNat ≠
        0 := by
    exact div_ne_zero hnum hden
  simpa [Cf, hσ] using this

lemma lem_Cf_never_zero
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
  -- Split into cases: either z is in the zero set or not
  by_cases h : z ∈ zerosetKfR R1 (by linarith) f
  · -- Case: z ∈ zerosetKfR R1 (by linarith) f
    exact lem_Cf_nonzero_on_K h_finite_zeros h_σ h_σ_spec z h
  · -- Case: z ∉ zerosetKfR R1 (by linarith) f
    have hz_diff : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := ⟨hz, h⟩
    exact lem_Cf_nonzero_off_K h_finite_zeros h_σ h_σ_spec z hz_diff

lemma factor_nonzero_outside_domain (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (ρ : ℂ) (hρ_bound : ‖ρ‖ ≤ R1) (hρ_ne_zero : ρ ≠ 0) (z : ℂ) (hz_in_R1 : ‖z‖ ≤ R1) :
    (R : ℂ) - star ρ * z / (R : ℂ) ≠ 0 := by
  -- Proof by contradiction
  intro h_eq_zero
  have hR_pos : 0 < R := by linarith

  -- From the equation being zero, we get star ρ * z = R²
  have h_mul_eq_R_sq : star ρ * z = (R : ℂ) ^ 2 := by
    have hR_ne_zero : (R : ℂ) ≠ 0 := by
      rw [Ne, ← norm_eq_zero]
      simp [Complex.norm_of_nonneg (le_of_lt hR_pos)]
      linarith
    -- From h_eq_zero: (R : ℂ) - star ρ * z / (R : ℂ) = 0
    -- Rearrange to: (R : ℂ) = star ρ * z / (R : ℂ)
    -- Multiply by (R : ℂ): (R : ℂ)² = star ρ * z
    rw [sub_eq_zero] at h_eq_zero
    rw [eq_div_iff_mul_eq hR_ne_zero] at h_eq_zero
    rw [← pow_two] at h_eq_zero
    exact h_eq_zero.symm

  -- Taking norms of both sides: ‖star ρ * z‖ = ‖(R : ℂ) ^ 2‖
  have h_norm_eq : ‖ρ‖ * ‖z‖ = R ^ 2 := by
    have h_left : ‖star ρ * z‖ = ‖ρ‖ * ‖z‖ := by
      rw [norm_mul, norm_star]
    have h_right : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
      rw [Complex.norm_pow, Complex.norm_of_nonneg (le_of_lt hR_pos)]
    rw [← h_left, h_mul_eq_R_sq, h_right]

  -- Since ‖ρ‖ ≤ R1 and ‖z‖ ≤ R1, we have R² = ‖ρ‖ * ‖z‖ ≤ R1 * R1 = R1²
  have h_R_sq_le : R ^ 2 ≤ R1 ^ 2 := by
    calc R ^ 2
      = ‖ρ‖ * ‖z‖ := h_norm_eq.symm
      _ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hρ_bound (norm_nonneg z)
      _ ≤ R1 * R1 := mul_le_mul_of_nonneg_left hz_in_R1 (le_of_lt hR1_pos)
      _ = R1 ^ 2 := by rw [← pow_two]

  -- This gives R ≤ R1
  have h_R_le_R1 : R ≤ R1 := by
    exact le_of_pow_le_pow_left₀ (by norm_num) (le_of_lt hR1_pos) h_R_sq_le

  -- This contradicts the hypothesis R1 < R
  linarith

lemma linear_pow_analytic (a b : ℂ) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w => (a - b * w) ^ n) z := by
  -- The function w ↦ a - b * w is linear, hence analytic
  have h_linear : AnalyticAt ℂ (fun w => a - b * w) z := by
    -- a is constant, hence analytic
    have h_const : AnalyticAt ℂ (fun _ => a) z := analyticAt_const
    -- b * w is analytic (scalar multiplication of identity)
    have h_mul : AnalyticAt ℂ (fun w => b * w) z := by
      have h_id : AnalyticAt ℂ (fun w => w) z := analyticAt_id
      exact h_id.const_smul
    -- subtraction of analytic functions is analytic
    exact h_const.sub h_mul
  -- Powers of analytic functions are analytic
  exact h_linear.fun_pow n

lemma bl_num_diff
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    DifferentiableAt ℂ
      (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
  · -- Show the function is analytic using the existing lemmas
    have h_analytic : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by

      -- Define the factor function that matches Finset.analyticAt_prod signature
      let factor_func : ℂ → ℂ → ℂ := fun ρ w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat

      -- Show each factor is analytic at z using linear_pow_analytic
      have h_each_analytic : ∀ ρ ∈ h_finite_zeros.toFinset, AnalyticAt ℂ (factor_func ρ) z := by
        intro ρ hρ_mem
        simp only [factor_func]
        -- Rewrite to match linear_pow_analytic pattern: (a - b * w)^n
        have h_rewrite : (fun w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) =
                         (fun w => ((R : ℂ) - (star ρ / (R : ℂ)) * w) ^ (analyticOrderAt f ρ).toNat) := by
          ext w
          ring
        rw [h_rewrite]
        -- Apply linear_pow_analytic directly
        exact linear_pow_analytic (R : ℂ) (star ρ / (R : ℂ)) (analyticOrderAt f ρ).toNat z

      -- Use Finset.analyticAt_prod to combine the factors
      have h_prod_analytic := Finset.analyticAt_prod h_finite_zeros.toFinset h_each_analytic
      -- The result is AnalyticAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset, factor_func ρ w) z
      convert h_prod_analytic using 1
      ext w
      simp [factor_func]

    -- Analytic implies differentiable
    exact h_analytic.differentiableAt

lemma lem_bl_num_nonzero
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
  -- constructor

  -- Part 1: Show the product is nonzero using factor_nonzero_outside_domain
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro ρ hρ_mem
    apply pow_ne_zero
    -- Use factor_nonzero_outside_domain lemma directly
    have hρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f :=
      h_finite_zeros.mem_toFinset.mp hρ_mem
    have hρ_bound : ‖ρ‖ ≤ R1 := by
      -- Convert from Metric.closedBall to norm bound
      have : dist ρ 0 ≤ R1 := Metric.mem_closedBall.mp hρ_in_zeros.1
      simp only [dist_zero_right] at this
      exact this
    have hρ_ne_zero : ρ ≠ 0 := by
      intro h_eq_zero
      rw [h_eq_zero] at hρ_in_zeros
      exact h_f_nonzero_at_zero hρ_in_zeros.2
    have hz_bound : ‖z‖ ≤ R1 := by
      have : dist z 0 ≤ R1 := Metric.mem_closedBall.mp hz.1
      simp only [dist_zero_right] at this
      exact this
    exact factor_nonzero_outside_domain R R1 hR1_pos hR1_lt_R hR_lt_1 ρ hρ_bound hρ_ne_zero z hz_bound

noncomputable def Bf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) : ℂ :=
  Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z *
  ∏ ρ ∈ h_finite_zeros.toFinset,
    ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat

lemma lem_BfCf
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z * (∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) /
    (∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat) := by
  -- Since z ∉ zerosetKfR R1, we know z is not in the zero set
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2

  -- Unfold Bf definition
  unfold Bf

  -- Unfold Cf definition and use the else branch since z ∉ zerosetKfR R1
  unfold Cf
  simp [hz_not_in]

  -- Now we have: (f z / ∏ ρ, (z - ρ)^m) * ∏ ρ, Blaschke_factor = goal
  -- Use div_mul_eq_mul_div: (a / b) * c = (a * c) / b
  exact div_mul_eq_mul_div _ _ _

lemma lem_Bf_div
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    (∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) /
    (∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat) =
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat /
       (z - ρ) ^ (analyticOrderAt f ρ).toNat) := by
  rw [Finset.prod_div_distrib]

lemma lem_Bf_prodpow
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat /
       (z - ρ) ^ (analyticOrderAt f ρ).toNat) =
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat := by
  simp only [div_pow]

lemma lem_Bf_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z * ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat := by
  -- Start with lem_BfCf to get the initial form
  rw [lem_BfCf h_finite_zeros h_σ z hz]
  -- Use mul_div_assoc to rearrange f z * (A / B) = f z * A / B
  rw [mul_div_assoc]
  -- Work on the division part using congr
  congr 1
  -- Apply lem_Bf_div with explicit parameters
  rw [@lem_Bf_div R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros z hz]
  -- Apply lem_Bf_prodpow with explicit parameters
  rw [@lem_Bf_prodpow R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros z hz]


lemma lem_frho_zero_contra
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) : f ρ ≠ 0 → ρ ∉ zerosetKfR R1 (by linarith) f := by
  intro h_f_rho_ne_zero h_rho_in_KfR1
  -- From membership in zerosetKfR, we get f ρ = 0
  have h_f_rho_zero : f ρ = 0 := h_rho_in_KfR1.2
  -- This contradicts the assumption that f ρ ≠ 0
  exact h_f_rho_ne_zero h_f_rho_zero

lemma lem_f_is_nonzero (f : ℂ → ℂ) : f 0 ≠ 0 → f ≠ 0 := by
  intro h_f_zero_ne_zero h_f_eq_zero
  -- If f = 0, then f 0 = 0
  have h_f_at_zero_eq_zero : f 0 = 0 := by
    rw [h_f_eq_zero]
    simp
  -- This contradicts f 0 ≠ 0
  exact h_f_zero_ne_zero h_f_at_zero_eq_zero


theorem lem_rho_in_disk_R1
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    norm ρ ≤ R1 := by
  -- By definition of zerosetKfR, ρ is in the closed ball of radius R1
  have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
  -- In a closed ball, the distance from center is at most the radius
  rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
  simp only [sub_zero] at h_in_ball
  exact h_in_ball


theorem lem_zero_not_in_Kf (R R1 : ℝ)
  (hR1_pos : 0 < R1)
  (hR1_lt_R : R1 < R)
  (f : ℂ → ℂ)
  (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) :
    f 0 ≠ 0 → 0 ∉ zerosetKfR R1 (by linarith) f := by
  intro h_f_zero_ne_zero h_zero_in_KfR
  -- From membership in zerosetKfR, we get f 0 = 0
  have h_f_zero_eq_zero : f 0 = 0 := h_zero_in_KfR.2
  -- This contradicts the assumption that f 0 ≠ 0
  exact h_f_zero_ne_zero h_f_zero_eq_zero


lemma lem_rho_ne_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f, ρ ≠ 0 := by
  intro ρ h_ρ_in_zeros h_ρ_eq_zero
  -- If ρ = 0, then ρ ∈ zerosetKfR implies 0 ∈ zerosetKfR
  rw [h_ρ_eq_zero] at h_ρ_in_zeros
  -- But this contradicts lem_zero_not_in_Kf
  have h_zero_not_in : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  exact h_zero_not_in h_ρ_in_zeros


lemma lem_mod_pos_iff_ne_zero (z : ℂ) : z ≠ 0 → norm z > 0 :=
  lem_abspos z

theorem lem_mod_rho_pos
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ (ρ : ℂ), ρ ∈ zerosetKfR R1 (by linarith) f → norm ρ > 0 := by
  intro ρ h_ρ_in_zeros
  -- First show that ρ ≠ 0
  have h_ρ_ne_zero : ρ ≠ 0 :=
    lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
  -- Now use the lemma that norm is positive for nonzero elements
  exact lem_mod_pos_iff_ne_zero ρ h_ρ_ne_zero


theorem lem_rho_in_disk_R1_repeat (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    norm ρ ≤ R1 :=
  lem_rho_in_disk_R1 R R1 hR1_pos hR1_lt_R f ρ h_rho_in_KfR1


lemma lem_inv_mono_decr (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : 1 / x ≥ 1 / y := by
  -- Since 0 < x ≤ y, we have 0 < y
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  -- Use one_div_le_one_div_of_le for the correct order
  exact one_div_le_one_div_of_le hx hxy


lemma lem_inv_mod_rho_ge_inv_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    1 / norm ρ ≥ 1 / R1 := by
  -- From membership in zerosetKfR, we know |ρ| ≤ R1
  have h_abs_ρ_le_R1 : norm ρ ≤ R1 :=
    lem_rho_in_disk_R1 R R1 hR1_pos hR1_lt_R f ρ h_rho_in_KfR1
  -- We need |ρ| > 0 to apply the inverse monotonicity lemma
  have h_abs_ρ_pos : norm ρ > 0 :=
    lem_mod_rho_pos R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
  -- We need R1 > 0
  have h_R1_pos : R1 > 0 := by
    linarith
  -- Apply inverse monotonicity: if 0 < |ρ| ≤ R1, then 1/R1 ≤ 1/|ρ|
  exact lem_inv_mono_decr (norm ρ) R1 h_abs_ρ_pos h_abs_ρ_le_R1


theorem lem_mul_pos_preserves_ineq (a b c : ℝ) (hab : a ≤ b) (hc : 0 < c) :
    a * c ≤ b * c := by
  exact mul_le_mul_of_nonneg_right hab (le_of_lt hc)


theorem lem_R_div_mod_rho_ge_R_div_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ R / R1 := by
  -- Get the inverse inequality: 1/|ρ| ≥ 1/R1
  have h_inv_ineq : 1 / norm ρ ≥ 1 / R1 :=
    lem_inv_mod_rho_ge_inv_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
  -- Since multiplication by R > 0 preserves inequality direction
  -- R * (1/|ρ|) ≥ R * (1/R1) becomes R/|ρ| ≥ R/R1
  have h_R_div_abs_ρ_eq : R * (1 / norm ρ) = R / norm ρ := by ring
  have h_R_div_R1_eq : R * (1 / R1) = R / R1 := by ring
  rw [← h_R_div_abs_ρ_eq, ← h_R_div_R1_eq]
  exact mul_le_mul_of_nonneg_left h_inv_ineq (by linarith)

theorem lem_R_div_mod_rho_ge_R_over_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ (R/R1 : ℝ) := by
  -- First show R / |ρ| ≥ R / R1
  have h_ineq1 : R / norm ρ ≥ R / R1 :=
    lem_R_div_mod_rho_ge_R_div_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
  -- Then show R / R1 = 3/2
  linarith


theorem lem_mod_of_prod2 {ι : Type*} (K : Finset ι) (w : ι → ℂ) :
    ‖∏ ρ ∈ K, w ρ‖ = ∏ ρ ∈ K, ‖w ρ‖ := by
  classical
  refine Finset.induction_on K ?h0 ?hstep
  · simp
  · intro a s ha ih
    -- ‖∏‖ distributes over product for complex numbers
    simp [Finset.prod_insert ha, norm_mul, ih]


lemma lem_mod_Bf_is_prod_mod (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ)
    (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat‖ := by
  -- Use definition of Bf: Bf z = Cf z * ∏ ρ, ((R - star ρ * z / R)^{m_ρ})
  unfold Bf
  rw [norm_mul]
  -- Use lem_mod_of_prod2 to distribute norm over the product as suggested in informal proof
  rw [lem_mod_of_prod2]
  -- When z ∉ zerosetKfR R1, we have Cf z = f z / ∏ ρ, (z - ρ)^{m_ρ} by definition
  have hCf : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp only [hz, ↓reduceDIte]
  rw [hCf, norm_div]
  -- Apply lem_mod_of_prod2 to the denominator
  rw [lem_mod_of_prod2]
  -- Rearrange: (‖f z‖ / ∏‖(z-ρ)^{m_ρ}‖) * ∏‖(R - star ρ * z / R)^{m_ρ}‖
  rw [div_mul_eq_mul_div]
  -- Use properties of products to combine: ‖f z‖ * (∏‖(R - star ρ * z / R)^{m_ρ}‖ / ∏‖(z-ρ)^{m_ρ}‖)
  rw [mul_div_assoc]
  -- Use Finset.prod_div_distrib: ∏(a/b) = (∏a)/(∏b)
  rw [← Finset.prod_div_distrib]
  congr 2
  ext ρ
  -- Show ‖a^n‖ / ‖b^n‖ = ‖(a/b)^n‖
  rw [← norm_div, ← div_pow]
  congr 2
  -- Show star ρ * z = z * star ρ by commutativity
  ring


lemma lem_abs_pow (w : ℂ) (n : ℕ) : ‖w ^ n‖ = ‖w‖ ^ n := by
  simp


lemma lem_Bmod_pow (R R1 : ℝ) (hR_pos : 0 < R) (hR1 : R1 = 2 * R / 3) (f : ℂ → ℂ)
  (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f)
    (z : ℂ) :
    ‖((((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat)‖ =
    (‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖) ^ (analyticOrderAt f ρ).toNat := by
  simp


lemma lem_mod_Bf_prod_mod (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
  (z : ℂ)
  (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
  -- Apply lem_mod_Bf_is_prod_mod to get the first form (use hz that z ∉ zeroset)
  have h1 := lem_mod_Bf_is_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  rw [h1]
  -- Now use lem_abs_pow to transform each term in the product
  congr 2
  ext ρ
  rw [lem_abs_pow]

lemma lem_mod_Bf_at_0 (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖((R : ℂ) / (-ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
  -- Apply the general result at z = 0 (0 is not in the zero set by lem_zero_not_in_Kf)
  have hz0 : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec 0 hz0]
  -- Now simplify: when z = 0, we have ((R - 0 * star ρ / R) / (0 - ρ)) = R / (-ρ)
  congr 2
  ext ρ
  congr 1
  simp only [zero_mul, zero_div, sub_zero, zero_sub]

lemma lem_mod_div_ (w1 w2 : ℂ) (hw2_ne_zero : w2 ≠ 0) : ‖w1 / w2‖ = ‖w1‖ / ‖w2‖ := by
  simp


lemma lem_mod_neg (w : ℂ) : ‖-w‖ = ‖w‖ := by
  simp

lemma lem_mod_div_and_neg (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (h_rho_ne_zero : ρ ≠ 0) :
  ‖(R : ℂ) / (-ρ)‖ = R / ‖ρ‖ := by
  -- Use division formula for abs, abs of real, and abs of neg
  have hden : (-ρ) ≠ 0 := by simpa using neg_ne_zero.mpr h_rho_ne_zero
  have hdiv := lem_mod_div_ (R : ℂ) (-ρ) hden
  have hnorm_real : ‖(R : ℂ)‖ = |R| := by simp
  calc
    ‖(R : ℂ) / (-ρ)‖ = ‖(R : ℂ)‖ / ‖-ρ‖ := hdiv
    _ = ‖(R : ℂ)‖ / ‖ρ‖ := by simp [norm_neg]
    _ = |R| / ‖ρ‖ := by simp [hnorm_real]
    _ = R / ‖ρ‖ := by simp [abs_of_pos hR_pos]


theorem lem_mod_Bf_at_0_eval  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
  -- Start with lem_mod_Bf_at_0
  rw [lem_mod_Bf_at_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec]
  -- Now we need to show the products are equal
  congr 1
  -- Use Finset.prod_congr to show the products are equal
  apply Finset.prod_congr rfl
  intro ρ hρ
  -- We need to show ‖((R : ℂ) / (-ρ))‖ ^ (analyticOrderAt f ρ).toNat = (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat
  -- This follows from lem_mod_div_and_neg if ρ ≠ 0
  have h_ρ_ne_zero : ρ ≠ 0 := by
    -- ρ is in h_finite_zeros.toFinset, so it's in zerosetKfR
    have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
      exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
    exact lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
  -- Apply lem_mod_div_and_neg to rewrite the norm
  rw [lem_mod_div_and_neg R (by linarith) ρ h_ρ_ne_zero]


lemma lem_mod_of_pos_real (x : ℝ) (hx : 0 < x) : abs x = x := by
  exact abs_of_pos hx


theorem lem_mod_Bf_at_0_as_ratio  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
  exact lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec

lemma lem_prod_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
    (h_nonneg : ∀ ρ ∈ K, 0 ≤ a ρ) (h_le : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  exact Finset.prod_le_prod h_nonneg h_le


lemma lem_power_ineq (n : ℕ) (c : ℝ) (hc : c > 1) (hn : n ≥ 1) : c ≤ c ^ n := by
  cases' n with n
  · -- n = 0, contradiction with hn : n ≥ 1
    omega
  · -- n = n + 1, so c ≤ c^(n+1)
    have h_c_ge_1 : 1 ≤ c := le_of_lt hc
    rw [pow_succ]
    -- c ≤ c * c^n since c ≥ 1 and c^n ≥ 1
    have h_c_pow_n_ge_1 : 1 ≤ c ^ n := by exact one_le_pow₀ h_c_ge_1
    calc c = c * 1 := (mul_one c).symm
    _ ≤ c * c ^ n := mul_le_mul_of_nonneg_left h_c_pow_n_ge_1 (le_of_lt (lt_trans zero_lt_one hc))
    _ = c ^ n * c := mul_comm (c) (c ^ n)


lemma lem_power_ineq_1 (n : ℕ) (c : ℝ) (hc : 1 ≤ c) (hn : 1 ≤ n) : 1 ≤ c ^ n := by
  exact one_le_pow₀ hc


lemma lem_prod_power_ineq {ι : Type*} (K : Finset ι) (c : ι → ℝ) (n : ι → ℕ)
    (h_c_ge_1 : ∀ ρ ∈ K, 1 ≤ c ρ)
    (h_n_ge_1 : ∀ ρ ∈ K, 1 ≤ n ρ) :
    ∏ ρ ∈ K, (c ρ) ^ (n ρ) ≥ 1 := by
  classical
  induction K using Finset.induction with
  | empty => simp
  | insert i s h_not_in ih =>
    rw [Finset.prod_insert h_not_in]
    have h_pow_ge_1 : 1 ≤ c i ^ n i :=
      one_le_pow₀ (h_c_ge_1 i (Finset.mem_insert_self i s))
    have h_prod_ge_1 : 1 ≤ ∏ ρ ∈ s, (c ρ) ^ (n ρ) := by
      apply ih
      · intro ρ hρ; exact h_c_ge_1 ρ (Finset.mem_insert_of_mem hρ)
      · intro ρ hρ; exact h_n_ge_1 ρ (Finset.mem_insert_of_mem hρ)
    exact one_le_mul_of_one_le_of_one_le h_pow_ge_1 h_prod_ge_1


theorem lem_prod_1 {ι : Type*} {M : Type*} [CommMonoid M] (K : Finset ι) : ∏ _ρ ∈ K, (1 : M) = 1 := by
  exact Finset.prod_const_one


lemma lem_prod_power_ineq1 {ι : Type*} (K : Finset ι) (c : ι → ℝ) (n : ι → ℕ)
    (h_c_ge_1 : ∀ ρ ∈ K, 1 ≤ c ρ) (h_n_ge_1 : ∀ ρ ∈ K, 1 ≤ n ρ) :
    ∏ ρ ∈ K, (c ρ) ^ (n ρ) ≥ 1 := by
  exact lem_prod_power_ineq K c n h_c_ge_1 h_n_ge_1


lemma lem_mod_lower_bound_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (hR_lt_1 : R < 1) :  -- ADD THIS
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 := by
  classical
  set K := h_finite_zeros.toFinset

  have h_base_ge_1 : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have h :=
    lem_prod_ineq K (fun _ : ℂ => (1 : ℝ))
      (fun ρ : ℂ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (by intro ρ hρ; norm_num)
      (by
        intro ρ hρ
        simpa using (one_le_pow₀ (by linarith [h_base_ge_1])))
  simpa [K] using h

theorem lem_mod_Bf_at_0_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≥ 1 := by
  -- First derive f 0 ≠ 0 from f 0 = 1
  have R_over_R1_nonneg : 1 < R / R1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have R_over_R1_nonneg : 0 ≤ R / R1 := by linarith
  have h_f_nonzero_at_zero : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
  -- Use lem_mod_Bf_at_0_as_ratio to express ‖Bf ... 0‖ as a product
  rw [lem_mod_Bf_at_0_as_ratio R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros]
  -- Since f 0 = 1, we have ‖f 0‖ = 1
  rw [hf0_eq_one, norm_one, one_mul]
  -- Show that the product ∏ (R / ‖ρ‖)^n ≥ ∏ (3/2)^n
  have h_prod_ge : ∏ ρ ∈ h_finite_zeros.toFinset, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat ≥
                   ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat := by
    apply Finset.prod_le_prod
    -- Show (3/2)^n ≥ 0
    · intro ρ hρ
      apply pow_nonneg
      apply R_over_R1_nonneg
    -- Show (R / ‖ρ‖)^n ≥ (3/2)^n for each ρ
    · intro ρ hρ
      have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
        exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      -- We have R / norm ρ ≥ 3/2, and ‖ρ‖ = norm ρ
      have h_ratio_ge : R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
        -- norm is defined as ‖z‖, so they are equal
        have h_norm_abs_eq : ‖ρ‖ = norm ρ := by rfl
        rw [h_norm_abs_eq]
        exact lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros

      -- Use power monotonicity: if a ≥ b > 0, then a^n ≥ b^n
      have h_3_2_pos : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
      have h_3_2_pos : (0 : ℝ) < (R/R1 : ℝ) := by linarith
      have h_ratio_pos : (0 : ℝ) ≤ R / ‖ρ‖ := by
        linarith [h_ratio_ge]
      exact pow_le_pow_left₀ R_over_R1_nonneg h_ratio_ge (analyticOrderAt f ρ).toNat
  -- Use lem_mod_lower_bound_1: the (3/2)^n product is ≥ 1
  have h_3_2_prod_ge_1 : ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 :=
    lem_mod_lower_bound_1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_eq_one h_finite_zeros hR_lt_1
  -- Combine: 1 ≤ (3/2)^n product ≤ (R/‖ρ‖)^n product
  exact le_trans h_3_2_prod_ge_1 h_prod_ge
  assumption

lemma lem_linear_factor_analytic (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (z : ℂ) :
  AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
  -- The function is (R : ℂ) - star ρ * w / (R : ℂ)
  -- This is an affine function: constant - (constant / constant) * w
  -- We can rewrite as: (R : ℂ) - (star ρ / (R : ℂ)) * w

  -- First show that (R : ℂ) is analytic (constant function)
  have h_const : AnalyticAt ℂ (fun _ => (R : ℂ)) z := analyticAt_const

  -- Show that w ↦ w is analytic (identity function)
  have h_id : AnalyticAt ℂ (fun w => w) z := analyticAt_id

  -- Show that star ρ / (R : ℂ) is a nonzero constant since R > 0
  have h_const_coeff : AnalyticAt ℂ (fun _ => star ρ / (R : ℂ)) z := analyticAt_const

  -- Show that the multiplication (star ρ / (R : ℂ)) * w is analytic
  have h_mul : AnalyticAt ℂ (fun w => star ρ / (R : ℂ) * w) z :=
    AnalyticAt.fun_mul h_const_coeff h_id

  -- Show that the subtraction is analytic
  have h_sub : AnalyticAt ℂ (fun w => (R : ℂ) - star ρ / (R : ℂ) * w) z :=
    AnalyticAt.fun_sub h_const h_mul

  -- The original function equals this by algebra
  convert h_sub using 1
  ext w
  ring

lemma lem_pow_analyticAt {g : ℂ → ℂ} (n : ℕ) (w : ℂ) :
  AnalyticAt ℂ g w → AnalyticAt ℂ (fun z => (g z) ^ n) w := by
  intro hg
  exact AnalyticAt.fun_pow hg n

lemma lem_finset_prod_analyticAt {α : Type*} {S : Finset α} {g : α → ℂ → ℂ} (w : ℂ) :
  (∀ a ∈ S, AnalyticAt ℂ (g a) w) → AnalyticAt ℂ (fun z => ∏ a ∈ S, g a z) w := by
  intro h
  classical
  induction S using Finset.induction with
  | empty =>
    -- Base case: empty finset, product is 1 (constant function)
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | insert a s ha ih =>
    -- Inductive step: insert element a into finset s
    simp only [Finset.prod_insert ha]
    -- Product becomes g a z * (∏ b ∈ s, g b z)
    apply AnalyticAt.fun_mul
    · -- g a is analytic at w
      apply h
      exact Finset.mem_insert_self a s
    · -- Product over s is analytic at w by inductive hypothesis
      apply ih
      intro b hb
      apply h
      exact Finset.mem_insert_of_mem hb

lemma analyticOrderAt_top_iff_eventually_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) :
  analyticOrderAt f z = ⊤ ↔ ∀ᶠ w in nhds z, f w = 0 := by
  simp [analyticOrderAt, hf]

lemma isPreconnected_closedBall (x : ℂ) (r : ℝ) : IsPreconnected (Metric.closedBall x r) := by
  -- Closed balls are convex
  have h_convex : Convex ℝ (Metric.closedBall x r) := convex_closedBall _ _
  -- Convex sets are preconnected
  exact h_convex.isPreconnected

lemma Set.infinite_Icc_of_lt {a b : ℝ} (h : a < b) : (Set.Icc a b).Infinite := by
  -- Proof by contradiction
  intro h_finite
  -- The open interval (a,b) is a subset of [a,b]
  have h_subset : Set.Ioo a b ⊆ Set.Icc a b := Set.Ioo_subset_Icc_self
  -- If [a,b] is finite, then (a,b) is finite as a subset
  have h_Ioo_finite : (Set.Ioo a b).Finite := h_finite.subset h_subset
  -- But (a,b) is infinite for a < b
  have h_Ioo_infinite : (Set.Ioo a b).Infinite := Set.Ioo_infinite h
  -- This is a contradiction
  exact h_Ioo_infinite h_Ioo_finite

lemma infinite_closedBall_of_pos (x : ℂ) (r : ℝ) (hr : 0 < r) : (Metric.closedBall x r).Infinite := by
  -- We'll show the closed ball contains an infinite line segment
  -- Consider the horizontal line segment from x in the real direction
  let f : ℝ → ℂ := fun t => x + t

  -- Show that f maps [0, r/2] into the closed ball
  have h_maps_to : Set.MapsTo f (Set.Icc 0 (r/2)) (Metric.closedBall x r) := by
    intro t ht
    rw [Metric.mem_closedBall]
    -- Need to show: dist (f t) x ≤ r
    have h_eq : f t = x + t := rfl
    rw [h_eq, Complex.dist_eq, add_sub_cancel_left]
    -- Now need to show: ‖(t : ℂ)‖ ≤ r
    have h_norm : ‖(t : ℂ)‖ = |t| := by
      exact Complex.norm_real t
    rw [h_norm, abs_of_nonneg ht.1]
    exact le_trans ht.2 (le_of_lt (half_lt_self hr))

  -- f is injective on [0, r/2]
  have h_inj : Set.InjOn f (Set.Icc 0 (r/2)) := by
    intro s hs t ht h_eq
    have : x + s = x + t := h_eq
    have : (s : ℂ) = (t : ℂ) := add_left_cancel this
    exact Complex.ofReal_inj.mp this

  -- The interval [0, r/2] is infinite
  have h_infinite_interval : (Set.Icc (0:ℝ) (r/2)).Infinite :=
    Set.infinite_Icc_of_lt (half_pos hr)

  -- Therefore the image f '' [0, r/2] is infinite
  have h_infinite_image : (f '' Set.Icc 0 (r/2)).Infinite :=
    Set.Infinite.image h_inj h_infinite_interval

  -- The image is contained in the closed ball
  have h_subset : f '' Set.Icc 0 (r/2) ⊆ Metric.closedBall x r :=
    Set.MapsTo.image_subset h_maps_to

  -- Use contradiction: if the closed ball were finite, its subset would be finite
  intro h_finite
  exact h_infinite_image (h_finite.subset h_subset)

lemma analyticOrderAt_ne_top_of_finite_zeros_in_ball (f : ℂ → ℂ) (R : ℝ) (hR_pos : 0 < R)
    (hf_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) R, AnalyticAt ℂ f z)
    (ρ : ℂ) (hρ_zero : f ρ = 0) (hρ_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R)
    (h_finite_zeros : {z ∈ Metric.closedBall (0 : ℂ) R | f z = 0}.Finite) :
    analyticOrderAt f ρ ≠ ⊤ := by
  -- Proof by contradiction
  by_contra htop
  -- From order = ⊤ we get that f is eventually zero near ρ
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    rw [← analyticOrderAt_top_iff_eventually_zero f ρ (hf_analytic ρ hρ_in_ball)]
    exact htop
  -- f is analytic on a neighborhood of the closed ball
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) := by
    intro z
    exact hf_analytic z
  -- The closed ball is preconnected
  have h_preconn : IsPreconnected (Metric.closedBall (0 : ℂ) R) :=
    isPreconnected_closedBall (0 : ℂ) R
  -- By identity principle, f = 0 on the closed ball
  have h_eqOn_zero : Set.EqOn f 0 (Metric.closedBall (0 : ℂ) R) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_in_ball h_eventually_zero
  -- Hence every point in the closed ball is a zero
  have h_all_zeros : ∀ z ∈ Metric.closedBall (0 : ℂ) R, f z = 0 := by
    intro z hz
    have := h_eqOn_zero hz
    simpa [Pi.zero_apply] using this
  -- This means the zero set equals the entire closed ball
  have h_zero_set_eq : {z ∈ Metric.closedBall (0 : ℂ) R | f z = 0} = Metric.closedBall (0 : ℂ) R := by
    ext z
    constructor
    · intro hz; exact hz.1
    · intro hz; exact ⟨hz, h_all_zeros z hz⟩
  -- But the closed ball is infinite (for R > 0), contradicting finite zeros
  have h_ball_infinite : (Metric.closedBall (0 : ℂ) R).Infinite :=
    infinite_closedBall_of_pos (0 : ℂ) R hR_pos
  -- This contradicts the finite zeros assumption
  rw [h_zero_set_eq] at h_finite_zeros
  exact h_ball_infinite h_finite_zeros

theorem lem_Bf_is_analytic (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) := by
  -- By definition of AnalyticOnNhd
  intro z hz

  -- First show the finite Blaschke product factor is analytic at z
  have h_blaschke_linear : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
    intro ρ hρ
    -- rewrite as constant + constant * w
    have h_eq : (fun w : ℂ => (R : ℂ) - star ρ * w / (R : ℂ)) =
                (fun w : ℂ => (R : ℂ) + (-(star ρ) / (R : ℂ)) * w) := by
      funext w
      field_simp
      ring
    rw [h_eq]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)

  have h_powers : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    exact (h_blaschke_linear ρ hρ).fun_pow _

  have h_product : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
    -- use the reusable lemma for finset products of analytic functions
    apply lem_finset_prod_analyticAt z
    intro ρ hρ
    apply h_powers
    exact hρ
  -- Now handle two cases: z is in the finite zero set or not
  by_cases hz_in : z ∈ zerosetKfR R1 (by linarith) f
  · -- z is a zero: use the local factor specification to get analyticity of Cf at σ
    have h_cf_at_sigma := @lem_Cf_analytic_at_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in
    -- Multiply analytic functions to get analyticity of Bf = Cf * product
    exact AnalyticAt.fun_mul h_cf_at_sigma h_product

  · -- z is not a zero: Cf is analytic off the zero set
    have hz_in_compl : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f := by
      constructor
      · exact hz
      · exact hz_in
    have h_cf_off := @lem_Cf_analytic_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in_compl
    exact AnalyticAt.fun_mul h_cf_off h_product

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = (‖z‖ ^ 2 : ℂ) := by
  -- Use the fact that star = conj for complex numbers
  rw [Complex.star_def]
  -- Now use Complex.mul_conj': z * conj z = ‖z‖ ^ 2
  exact Complex.mul_conj' z

lemma lem_mod_Bf_eq_mod_f_on_boundary (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ = ‖f z‖ := by
  intro z hz
  -- Use the factorization from lem_mod_Bf_prod_mod; first show z ∉ zerosetKfR
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := by
    intro h_in
    -- h_in says z ∈ closedBall (0, R1), so ‖z‖ ≤ R1
    have h_norm_le_R1 : ‖z‖ ≤ R1 := by simpa [sub_zero] using (h_in.1 : z ∈ Metric.closedBall (0 : ℂ) R1)
    -- hz gives ‖z‖ = R, and R1 < R, contradiction
    have h_norm_eq_R : ‖z‖ = R := by simpa using hz
    linarith [h_norm_le_R1, h_norm_eq_R, hR1_lt_R]
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_not_in]

  -- Show each Blaschke factor has norm 1 when |z| = R
  have h_each_factor_one : ∀ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ = 1 := by
    intro ρ hρ

    -- First, we need z ≠ ρ (if z = ρ, we get a contradiction since |z| = R > R1 but ρ ∈ ball(0, R1))
    have z_ne_rho : z ≠ ρ := by
      intro h_eq
      have rho_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      have rho_bound : ‖ρ‖ ≤ R1 := by
        have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := rho_in_zeros.1
        rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
        simpa using h_in_ball
      have R1_lt_R : R1 < R := by linarith
      rw [← h_eq, hz] at rho_bound
      linarith [R1_lt_R]

    -- Now prove the Blaschke factor has norm 1
    rw [Complex.norm_div]

    -- Use z * star z = ‖z‖² = R² when |z| = R
    have z_conj_eq : z * star z = (R ^ 2 : ℂ) := by
      rw [complex_mul_star_eq_norm_sq z, hz, pow_two]

    -- Rewrite numerator: R - z * star ρ / R = (R² - z * star ρ) / R
    have num_rewrite : (R : ℂ) - z * star ρ / (R : ℂ) = ((R : ℂ)^2 - z * star ρ) / (R : ℂ) := by
      field_simp [ne_of_gt hR1_pos]

    rw [num_rewrite, Complex.norm_div]

    -- Key step: R² - z * star ρ = z * star(z - ρ) using z * star z = R²
    have factor_eq : (R : ℂ)^2 - z * star ρ = z * star (z - ρ) := by
      rw [← z_conj_eq, star_sub]
      ring

    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    --field_simp
    field_simp [hz, z_ne_rho]

    have h_denom_ne_zero : R * ‖z - ρ‖ ≠ 0 := by
      apply mul_ne_zero
      -- Prove R is not zero
      · linarith [hR1_pos, hR1_lt_R]
      -- Prove the norm is not zero
      · simp [norm_ne_zero_iff, sub_ne_zero, z_ne_rho]
    -- field_simp can now use this fact to solve the goal.
    simp [h_denom_ne_zero]; grind


  -- Apply this to show the product equals 1
  have h_prod_one : ∏ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat = 1 := by
    -- Each factor equals 1, and 1^n = 1
    rw [← Finset.prod_congr rfl (fun ρ hρ => by rw [h_each_factor_one ρ hρ, one_pow])]
    rw [Finset.prod_const_one]

  rw [h_prod_one, mul_one]


lemma lem_Bf_bounded_on_boundary (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  -- proof body needs updating to use hR_lt_1
  intro z hz
  have hz_le : ‖z‖ ≤ R := le_of_eq hz
  have h_eq :=
    lem_mod_Bf_eq_mod_f_on_boundary R R1 (by linarith) hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  simpa [h_eq] using hf_le_B z hz_le

lemma norm_eq_radius_of_mem_sphere (w : ℂ) (R : ℝ) (hw : w ∈ Metric.sphere (0 : ℂ) R) : ‖w‖ = R := by
  have hdist : dist w (0 : ℂ) = R := by simpa [Metric.sphere] using hw
  simpa [Complex.dist_eq, sub_zero] using hdist

lemma mem_closedBall_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  have : dist z (0 : ℂ) ≤ R := by simpa [Complex.dist_eq, sub_zero] using hz
  simpa [Metric.closedBall] using this

lemma closure_ball_eq_closedBall_center (R : ℝ) (hR : 0 < R) :
  closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
  simpa using (closure_ball (x := (0 : ℂ)) (r := R) (ne_of_gt hR))

lemma lem_max_mod_principle_for_Bf (B R : ℝ) (hB : 1 < B) (hR_pos : 0 < R)
    (fB : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ fB (Metric.closedBall (0 : ℂ) R))
  (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R → ‖fB z‖ ≤ B) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖fB z‖ ≤ B := by
  intro z hz
  -- Prepare nonnegativity of B
  have hB0 : 0 ≤ B := le_of_lt (lt_trans zero_lt_one hB)
  -- Convert analytic assumption to the form required by Hard MMP
  have h_an_on_closure : AnalyticOn ℂ fB (closure (ballDR R)) := by
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using h_analytic.analyticOn
  -- Apply Hard maximum modulus principle on the closed ball of radius R
  have h_le :=
    lem_HardMMP R B hR_pos hB0 fB h_an_on_closure (by
      intro z hzR; exact h_bd_boundary z hzR)
  -- It remains to see that z belongs to the closure of the open ball of radius R
  have hz_cl : z ∈ closure (ballDR R) := by
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_of_norm_le hz
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using hz_closed
  exact h_le z hz_cl


lemma lem_Bf_bounded_in_disk_from_boundary (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  have hA := lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec
  exact lem_max_mod_principle_for_Bf B R hB (by linarith)
    (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) hA h_bd_boundary


lemma lem_Bf_bounded_in_disk_from_f (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  intro z hz
  have h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B :=
    lem_Bf_bounded_on_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  exact (lem_Bf_bounded_in_disk_from_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec h_bd_boundary) z hz


lemma lem_Bf_at_0_le_M (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B := by
  have h :=
    lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  have h0 : ‖(0 : ℂ)‖ ≤ R := by simpa using (le_of_lt (by linarith))
  simpa using h 0 h0


lemma lem_combine_bounds_on_Bf0 (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hBf0 : ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
  classical
  -- Abbreviate the finite set of zeros
  set K := h_finite_zeros.toFinset
  -- Evaluate ‖Bf(0)‖ in terms of the product over zeros
  have hf0_ne0 : f 0 ≠ 0 := by simp [hf0_eq_one]
  have hf0_norm : ‖f 0‖ = 1 := by simp [hf0_eq_one]
  have h_eval0 :=
    lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec
  have h_eval_prod :
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖
        = ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    rw [h_eval0, hf0_norm, one_mul]
  -- For each zero ρ ∈ K, we have R/‖ρ‖ ≥ 3/2
  have h_base_ge : ∀ ρ ∈ K, R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
    intro ρ hρK
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := by simpa [K] using hρK
    simpa using
      (lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_ne0 ρ hρ_in)
  -- Compare products termwise and combine
  have R_over_R1_nonneg : 0 ≤ R/R1 := by
    have : 0 ≤ R := by linarith
    apply div_nonneg (by assumption) (le_of_lt hR1_pos)
  have h_prod_le :
      ∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat
        ≤ ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    refine lem_prod_ineq K
      (fun ρ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (fun ρ => (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat)
      ?h_nonneg ?h_le
    · intro ρ hρK; exact pow_nonneg (R_over_R1_nonneg) _
    · intro ρ hρK
      exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ R / R1) (h_base_ge ρ hρK) _
  have h_prod_le_B :
      ∏ ρ ∈ K, (R / R1: ℝ) ^ (analyticOrderAt f ρ).toNat ≤ B := by
    have h_right : ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat =
        ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ := by
      simp [h_eval_prod]
    exact le_trans h_prod_le (by simpa [h_right] using hBf0)
  -- Convert the product of powers to a single power with exponent the sum of exponents
  have h_prod_pow_sum :
      (∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
        = (R/R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum K (fun ρ => (analyticOrderAt f ρ).toNat) (R/R1 : ℝ))
  -- Now we have a bound on (3/2)^(sum m_ρ) with a natural-number exponent
  have h_natPow : (R / R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) ≤ B := by
    simpa [h_prod_pow_sum] using h_prod_le_B
  -- Let S be that natural sum of multiplicities
  set S : ℕ := ∑ ρ ∈ K, (analyticOrderAt f ρ).toNat
  have h_natPowS : (R / R1 : ℝ) ^ S ≤ B := by simpa [S] using h_natPow
  -- Convert to real exponent using Real.rpow_natCast
  have h_rpowS : (R / R1 : ℝ) ^ (S : ℝ) ≤ B := by
    -- rewrite the left-hand side using rpow_natCast
    simpa [(Real.rpow_natCast (R / R1 : ℝ) S)] using h_natPowS
  -- Finally, rewrite S back as the sum over K and K as the toFinset
  have h_cast_sum : (S : ℝ)
      = (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) := by
    simp [S]
  -- Conclude by rewriting the exponent
  have : (R / R1 : ℝ) ^ (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ B := by
    simpa [h_cast_sum] using h_rpowS
  simpa [K] using this


lemma lem_jensen_inequality_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
  -- Derive f 0 ≠ 0 from f 0 = 1
  have hf0_ne0 : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
  -- Bound Bf at 0 using the maximum modulus arguments
  have hBf0 :=
    lem_Bf_at_0_le_M B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec hf_le_B
  -- Convert that bound into the desired product bound
  let K := h_finite_zeros.toFinset
  have hres := lem_combine_bounds_on_Bf0 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hBf0
  -- Align coercions and finish (adjust numerical coercions if necessary)
  simpa using hres


lemma lem_log_mono_inc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

lemma lem_three_gt_e : (3 : ℝ) > Real.exp 1 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
  exact lt_trans h1 h2  -- This is a numerical fact: e ≈ 2.718 < 3


lemma lem_jensen_log_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R / R1) ≤ Real.log B := by
  -- Let S denote the sum of the multiplicities
  set S : ℝ := ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)
  -- From the Jensen-type inequality
  have hpow_le : (R / R1 : ℝ) ^ S ≤ B := by
    simpa [S] using
      (lem_jensen_inequality_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B)
  -- Base positivity
  have hbase_pos : 1 < (R / R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have hbase_pos' : 0 < (R / R1 : ℝ) := by
    have : 0 < R := by linarith
    linarith
  -- Positivity of the left-hand side to apply log monotonicity
  have hxpos : 0 < (R / R1 : ℝ) ^ S := by
    simpa [S] using Real.rpow_pos_of_pos hbase_pos' S
  -- Apply monotonicity of log
  have hlog_le : Real.log ((R / R1 : ℝ) ^ S) ≤ Real.log B :=
    lem_log_mono_inc hxpos hpow_le
  -- Rewrite log of a power
  have hlog_rpow : Real.log ((R / R1 : ℝ) ^ S) = S * Real.log (R / R1) := by
    simpa using (Real.log_rpow hbase_pos' S)
  -- Conclude
  simpa [S, hlog_rpow] using hlog_le


lemma lem_sum_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
  (h_le : ∀ i ∈ K, a i ≤ b i) :
  Finset.sum K a ≤ Finset.sum K b := by
  classical
  exact Finset.sum_le_sum (by intro i hi; exact h_le i hi)

lemma ENat_coe_ge_one_iff_nat_ge_one (n : ℕ) : (n : ENat) ≥ 1 ↔ 1 ≤ n := by
  -- Convert ≥ to ≤ and use ENat.coe_le_coe
  rw [ge_iff_le]
  -- Now we have 1 ≤ (n : ENat) ↔ 1 ≤ n
  -- Since 1 = (1 : ℕ) when coerced to ENat, we can use ENat.coe_le_coe
  exact ENat.coe_le_coe

lemma nat_one_le_cast_real (n : ℕ) : 1 ≤ n → (1 : ℝ) ≤ (n : ℝ) := by
  intro h
  rw [← Nat.cast_one]
  exact Nat.cast_le.mpr h

lemma zerosetKfR_eq_zeros_in_ball (R : ℝ) (hR_pos : 0 < R) (f : ℂ → ℂ) :
    zerosetKfR R hR_pos f = {z | z ∈ Metric.closedBall (0 : ℂ) R ∧ f z = 0} := by
  rfl

lemma lem_frho_zero' (R R1 : ℝ)
    (hR_pos : 0 < R1)
    (hR1 : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_sum_m_rho_1 (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
     (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (hR_lt_1 : R < 1) :
    (h_finite_zeros.toFinset.card : ℝ) ≤ ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) := by
  -- Apply lem_sum_ineq as mentioned in the informal proof, with a_ρ = 1 and b_ρ = m_ρ
  -- First convert card to sum of 1's
  have h_card_as_sum : (h_finite_zeros.toFinset.card : ℝ) = ∑ ρ ∈ h_finite_zeros.toFinset, (1 : ℝ) := by
    simp [Finset.sum_const, smul_eq_mul]
  rw [h_card_as_sum]
  -- Now apply lem_sum_ineq
  apply lem_sum_ineq h_finite_zeros.toFinset (fun _ => (1 : ℝ)) (fun ρ => ((analyticOrderAt f ρ).toNat : ℝ))
  -- Show 1 ≤ m_ρ for each zero ρ (following the approach from lem_m_rho_ge_1)
  intro ρ hρ
  -- Get that ρ is a zero
  have hρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f :=
    (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
  have h_f_rho_zero : f ρ = 0 :=
    lem_frho_zero' R R1 (by linarith) hR1_lt_R f h_f_analytic ρ hρ_in_zeros
  -- f is analytic at ρ
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
    have h_R1_lt_1 : R1 < 1 := by linarith [hR_lt_1]
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) hρ_in_zeros.1
  -- The order is finite (following lem_m_rho_is_nat approach)
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := by
    have h_R1_pos : 0 < R1 := by linarith [hR1_pos]
    apply analyticOrderAt_ne_top_of_finite_zeros_in_ball f R1 h_R1_pos
    · intro z hz
      apply h_f_analytic
      have h_R1_lt_1 : R1 < 1 := by linarith [hR_lt_1]
      exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) hz
    · exact h_f_rho_zero
    · exact hρ_in_zeros.1
    · exact h_finite_zeros
  -- Use analyticOrderAt_ge_one_of_zero: order ≥ 1 for zeros
  have h_order_ge_one : analyticOrderAt f ρ ≥ 1 :=
    analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite
  -- Convert to natural number bound
  have h_toNat_ge_one : 1 ≤ (analyticOrderAt f ρ).toNat := by
    cases' h_cases : analyticOrderAt f ρ with n
    · rw [h_cases] at h_order_finite; contradiction
    · rw [h_cases] at h_order_ge_one
      rw [ENat.toNat_coe]
      exact (ENat_coe_ge_one_iff_nat_ge_one n).mp h_order_ge_one
  -- Convert to real
  exact nat_one_le_cast_real _ h_toNat_ge_one

lemma lem_sum_1_is_card {ι : Type*} (K : Finset ι) : Finset.sum K (fun _ => (1 : ℝ)) = (K.card : ℝ) := by
  -- Sum of ones over a finite set equals its cardinality (cast to ℝ)
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [mul_one]


lemma lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ (1/Real.log (R/R1)) * Real.log B := by
  have h_div_log : (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R/R1) ≤ Real.log B := by
    apply lem_jensen_log_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B
  have log_pos' : R/R1 > 1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have log_pos : Real.log (R/R1) > 0 := by exact Real.log_pos log_pos'
  calc
    ∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat
    _ = 1 / Real.log (R / R1) * (Real.log (R / R1) * (∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat)) := by
      field_simp [ne_of_gt log_pos]
    _ ≤ 1 / Real.log (R / R1) * Real.log B := by
      gcongr
      rw [mul_comm]
      exact h_div_log

lemma lem_sum_1_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    (h_finite_zeros.toFinset.card : ℝ) ≤ (1/Real.log (R/R1)) * Real.log B := by
  have h1 :=
    lem_sum_m_rho_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_finite_zeros hR_lt_1
  have h2 :=
    lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ hf_le_B h_σ_spec
  exact le_trans h1 h2

lemma lem_num_zeros_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    let S_zeros := zerosetKfR R1 (by linarith) f
    have inst_fintype_S_zeros : Fintype ↑S_zeros := h_finite_zeros.fintype
    (S_zeros.toFinset.card : ℝ) ≤ (1 / Real.log (R / R1)) * Real.log B := by
  intro S_zeros _inst
  dsimp [S_zeros]
  simpa using
    (lem_sum_1_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ hf_le_B h_σ_spec)

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

-- Helper to get f 0 ≠ 0 from f 0 = 1
lemma f_zero_ne_zero (h_f_zero : f 0 = 1) : f 0 ≠ 0 := by
  rw [h_f_zero]; simp


lemma Bf_is_analytic_on_disk
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) :=
    let hspec := h_σ_spec
    lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
      h_finite_zeros h_σ hspec

lemma lem_Bf_eq_prod_Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) *
      (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z) := by
  intro z
  rw [Bf]
  ring

lemma lem_num_prod_never_zero_all
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1,
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  apply pow_ne_zero

  -- Following the informal proof: extract bounds |ρ| ≤ R1, |z| ≤ R1
  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    rwa [Set.Finite.mem_toFinset h_finite_zeros] at hρ
  have hρ_bound : ‖ρ‖ ≤ R1 := by
    rw [zerosetKfR] at hρ_mem; simp at hρ_mem; exact hρ_mem.1
  have hz_bound : ‖z‖ ≤ R1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz

  -- Get R > 0
  have hR_pos : (0 : ℝ) < R := lt_trans hR1_pos hR1_lt_R

  -- Key step: show R - R1²/R > 0 as stated in informal proof
  have key_positive : (0 : ℝ) < R - R1 * R1 / R := by
    -- Since R1 < R, we have R1² < R² so R1²/R < R
    have h1 : R1 * R1 < R * R := by
      apply mul_self_lt_mul_self (le_of_lt hR1_pos) hR1_lt_R
    have h2 : R1 * R1 / R < R := by
      rw [div_lt_iff₀ hR_pos]
      exact h1
    linarith [h2]

  -- Show factor is nonzero by proving positive norm
  suffices h : (0 : ℝ) < ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ by
    exact norm_pos_iff.mp h

  -- Use reverse triangle inequality: |a - b| ≥ |a| - |b|
  have triangle_ineq : ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ ≥ ‖(R : ℂ)‖ - ‖star ρ * z / (R : ℂ)‖ :=
    norm_sub_norm_le _ _

  -- Simplify ‖(R : ℂ)‖ = R
  have R_norm_eq : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_of_nonneg (le_of_lt hR_pos)]

  -- Bound the product term: ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R
  have product_bound : ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R := by
    rw [norm_div, norm_mul, norm_star, R_norm_eq]
    -- We need to show ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R
    -- This is equivalent to ‖ρ‖ * ‖z‖ ≤ R1 * R1
    have mult_bound : ‖ρ‖ * ‖z‖ ≤ R1 * R1 := by
      exact mul_le_mul hρ_bound hz_bound (norm_nonneg _) (le_of_lt hR1_pos)
    -- Use the fact that division preserves inequality for positive denominators
    have : ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R := by
      exact div_le_div_of_nonneg_right mult_bound (le_of_lt hR_pos)
    exact this

  -- Combine the bounds: ‖factor‖ ≥ R - R1²/R > 0
  rw [R_norm_eq] at triangle_ineq
  linarith [triangle_ineq, product_bound, key_positive]

lemma Bf_never_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z ≠ 0 := by
  intro z hz
  -- Use the factorization of Bf as product of numerator and Cf
  rw [lem_Bf_eq_prod_Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec]
  -- Show the product is nonzero by showing each factor is nonzero
  apply mul_ne_zero
  · -- First factor: the product over zeros (numerator part) using lem:bl_num_nonzero
    exact lem_num_prod_never_zero_all R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec z hz
  · -- Second factor: Cf never zero using lem:C_never_zero
    exact lem_Cf_never_zero h_finite_zeros h_σ h_σ_spec z hz

lemma Bf0_not_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0 ≠ 0 := by
  apply Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  simp [Metric.mem_closedBall, dist_zero_right, le_of_lt hR1_pos]

noncomputable def Lf : ℂ → ℂ :=
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  Classical.choose (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
)


lemma Lf_is_analytic
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec)
                     (Metric.closedBall (0 : ℂ) r) := by
  unfold Lf
  exact (Classical.choose_spec (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
    )
  )).1

lemma Lf_at_0_is_0
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec 0 = 0 := by
  unfold Lf
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  let log_exists := log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
  exact (Classical.choose_spec log_exists).2.1


lemma lem_BCII {L : ℂ → ℂ} {r M r₁ : ℝ}
    (hr_pos : 0 < r)
    (hM_pos : 0 < M)
    (hr₁_pos : 0 < r₁)
    (hr₁_lt_r : r₁  < r)
    (hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U)
    (hL0 : L 0 = 0)
    (hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r₁) :
norm (deriv L z) ≤ (16 * M * r ^ 2) / ((r - r₁) ^ 3) := by
  apply borel_caratheodory_II hr_pos hM_pos hr₁_pos hr₁_lt_r hL_domain hL0 hre_L_le_M hz


lemma re_Lf_as_diff_of_log_mods
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) =
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) -
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)) := by
  intro z hz
  -- Use the three lemmas mentioned in informal proof: def:Lf, lem:log_of_analytic, lem:real_log_of_modulus_difference
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  have h_Bf_analytic : AnalyticOnNhd ℂ B_f (Metric.closedBall (0 : ℂ) R) :=
    Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_Bf_ne_zero : ∀ w ∈ Metric.closedBall (0 : ℂ) R1, B_f w ≠ 0 := by
    intro w hw
    exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw

  -- Apply lem:log_of_analytic
  have h_log_exists := log_of_analytic hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 h_Bf_analytic h_Bf_ne_zero
  have h_choose_spec := Classical.choose_spec h_log_exists

  -- Use def:Lf: Lf is defined as Classical.choose h_log_exists
  have h_Lf_def : Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec = Classical.choose h_log_exists := by
    unfold Lf
    simp only [B_f]

  -- Apply lem:real_log_of_modulus_difference
  rw [h_Lf_def]
  exact (h_choose_spec.2.2.2 z hz).symm

lemma log_Bf_le_log_B
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_pos : ∀ z, norm z ≤ R1 →
                0 < norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z))
    (h_Bf_bound : ∀ z, norm z ≤ R1 →
                  norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
  intro z hz
  apply Real.log_le_log
  · exact h_Bf_pos z hz
  · exact h_Bf_bound z hz


lemma log_Bf_le_log_B2
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_bound : ∀ z, ‖z‖ ≤ R →
                  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z, ‖z‖ ≤ R1 →
      Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖) ≤ Real.log B := by
  -- Use log_Bf_le_log_B directly
  apply log_Bf_le_log_B B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  · -- Prove h_Bf_pos: ∀ z, ‖z‖ ≤ R1 → 0 < ‖Bf ... z‖
    intro z hz
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) R1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
    have hBf_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz_mem
    exact norm_pos_iff.mpr hBf_ne_zero
  · -- Prove h_Bf_bound: ∀ z, ‖z‖ ≤ R1 → ‖Bf ... z‖ ≤ B
    intro z hz
    have hz_le_R : ‖z‖ ≤ R := by linarith [hz, hR1_lt_R]
    exact h_Bf_bound z hz_le_R

lemma log_Bf_le_log_B3
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
  -- Apply log_Bf_le_log_B2, which needs a bound on Bf on the disk of radius R
  apply log_Bf_le_log_B2 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  -- Get this bound using lem_Bf_bounded_in_disk_from_f
  apply lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec
  -- Apply the hypothesis h_f_bound (norm = ‖·‖ definitionally)
  exact h_f_bound

lemma log_Bf0_ge_0
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    0 ≤ Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖) := by
  -- Apply log monotonicity with x = 1 and y = |Bf(...,0)|
  have h_pos : 0 < (1 : ℝ) := by norm_num
  have h_Bf_ge_1 : 1 ≤ ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖ :=
    lem_mod_Bf_at_0_ge_1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_log_mono := lem_log_mono_inc h_pos h_Bf_ge_1
  rw [Real.log_one] at h_log_mono
  exact h_log_mono

lemma re_Lf_le_log_B
    (B r R R1 : ℝ)
    (hB : 1 < B)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r →
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) ≤ Real.log B := by
  intro z hz
  -- Use re_Lf_as_diff_of_log_mods to rewrite the real part as a difference of logarithms
  rw [re_Lf_as_diff_of_log_mods r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z]
  · -- Apply log_Bf_le_log_B3 and log_Bf0_ge_0
    -- derive the required bound ‖z‖ ≤ R1 from ‖z‖ ≤ r and r < R1
    have hz_apply_BC_to_Lfle_R1 : ‖z‖ ≤ R1 := by linarith [hz, hr_lt_R1]
    have h1 := log_Bf_le_log_B3 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound z hz_apply_BC_to_Lfle_R1
    have h2 := log_Bf0_ge_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
    linarith
  · -- Show z is in the closed ball of radius r
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hz)

lemma analyticOnNhd_closedBall_exists_open_differentiableOn {L : ℂ → ℂ} {r : ℝ}
  (h : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) r)) :
  ∃ U, IsOpen U ∧ Metric.closedBall (0 : ℂ) r ⊆ U ∧ DifferentiableOn ℂ L U := by
  classical
  -- Index the closed ball
  let I := {x : ℂ // x ∈ Metric.closedBall (0 : ℂ) r}
  -- For each point in the closed ball, obtain an open neighborhood where L is analytic
  have hI : ∀ i : I, ∃ (W : Set ℂ), IsOpen W ∧ (i : ℂ) ∈ W ∧ AnalyticOn ℂ L W := by
    intro i
    have hAt : AnalyticAt ℂ L (i : ℂ) := h i i.property
    -- From analyticity at a point, get a neighborhood where L is analytic
    have hWithin : AnalyticWithinAt ℂ L (Set.univ) (i : ℂ) := by
      simpa using (hAt.analyticWithinAt : AnalyticWithinAt ℂ L Set.univ (i : ℂ))
    rcases (AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn hWithin) with ⟨U₀, hU₀nhds, hU₀analytic⟩
    have hU₀nhds' : U₀ ∈ nhds (i : ℂ) := by simpa [nhdsWithin_univ] using hU₀nhds
    rcases _root_.mem_nhds_iff.mp hU₀nhds' with ⟨W, hWsub, hWopen, hiW⟩
    refine ⟨W, hWopen, hiW, hU₀analytic.mono ?_⟩
    exact hWsub
  choose V hVopen hiV hVanalytic using hI
  -- Define U as the union of these neighborhoods
  let U : Set ℂ := ⋃ i : I, V i
  have hUopen : IsOpen U := by
    simpa [U] using isOpen_iUnion (fun i => hVopen i)
  -- The closed ball is covered by U
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ U := by
    intro x hx
    refine Set.mem_iUnion.mpr ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    simpa using hiV ⟨x, hx⟩
  -- L is differentiable on U since it is differentiable on each V i
  have hdiffOn : DifferentiableOn ℂ L U := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
    have hdi : DifferentiableOn ℂ L (V i) := (hVanalytic i).differentiableOn
    have hdiAt : DifferentiableAt ℂ L y := hdi.differentiableAt ((hVopen i).mem_nhds hyi)
    exact hdiAt.differentiableWithinAt
  exact ⟨U, hUopen, hsub, hdiffOn⟩

lemma log_pos_of_one_lt {B : ℝ} (hB : 1 < B) : 0 < Real.log B := by
  simpa using Real.log_pos hB

lemma apply_BC_to_Lf
    (B r1 r R R1 : ℝ)
    (hB : 1 < B)
    (hr1_pos : 0 < r1)
    (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r1 →
      norm (deriv (Lf (lt_trans hr1_pos hr1_lt_r : 0 < r) hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z) ≤
      (16 * Real.log B * r^2) / (r - r1)^3 := by
  classical
  intro z hz
  -- derive 0 < r from 0 < r1 and r1 < r
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
  -- instantiate L := Lf ... with the derived positivity proof
  let L := Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
  -- L is analytic on a neighborhood of the closed ball of radius r
  have h_analytic_nhd :=
    Lf_is_analytic r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  -- Build an open set U containing the closed ball where L is differentiable
  let U : Set ℂ :=
    { y | ∃ x ∈ Metric.closedBall (0 : ℂ) r, ∃ s : ℝ, 0 < s ∧ y ∈ Metric.ball x s ∧
        AnalyticOnNhd ℂ L (Metric.ball x s) }
  have hU_open : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hyin, hAnaBall⟩
    have hnhds : Metric.ball x s ∈ nhds y := (Metric.isOpen_ball.mem_nhds hyin)
    exact Filter.mem_of_superset hnhds (by intro z hz; exact ⟨x, hxCB, s, hs_pos, hz, hAnaBall⟩)
  have hCB_subset : Metric.closedBall (0 : ℂ) r ⊆ U := by
    intro x hx
    have hAt : AnalyticAt ℂ L x := h_analytic_nhd x hx
    rcases AnalyticAt.exists_ball_analyticOnNhd hAt with ⟨s, hs_pos, hAnaBall⟩
    have hx_in_ball : x ∈ Metric.ball x s := by
      simpa [Metric.mem_ball, dist_self] using hs_pos
    exact ⟨x, hx, s, hs_pos, hx_in_ball, hAnaBall⟩
  have hDiffU : DifferentiableOn ℂ L U := by
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hy_in, hAnaBall⟩
    -- From AnalyticOnNhd on the ball, get AnalyticAt at y
    have hAt : AnalyticAt ℂ L y := hAnaBall y hy_in
    exact (AnalyticAt.differentiableAt hAt).differentiableWithinAt
  -- Package domain data
  have hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U :=
    ⟨U, hU_open, hCB_subset, hDiffU⟩
  -- L(0) = 0
  have hL0 : L 0 = 0 := by
    simpa [L] using (Lf_at_0_is_0 r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
  -- Re L ≤ log B on the closed ball of radius r
  have hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ Real.log B := by
    intro w hw
    have hw' : norm w ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact re_Lf_le_log_B B r R R1 hB hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound w hw'
  -- z ∈ closedBall 0 r1
  have hz' : z ∈ Metric.closedBall 0 r1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  -- Apply Borel–Carathéodory II
  have hBC :=
    lem_BCII hr_pos (Real.log_pos hB) hr1_pos hr1_lt_r hL_domain hL0 hre_L_le_M hz'
  -- conclude
  simpa [L] using hBC


lemma analyticOnNhd_Bf_closedBall (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z):
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) :=
  Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec

lemma helper_Bf_analytic_on_disk (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z):
    ∀ z ∈ Metric.closedBall (0 : ℂ) R, AnalyticAt ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z := by
  intro z hz
  have h_analytic_on := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  exact h_analytic_on z hz

lemma closedBall_R1_subset_R (hR1_nonneg : 0 ≤ R1) (hR1_lt_R : R1 < R) : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) R := by
  exact (Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_R))

-- Lemma 4: logDerivconst
lemma logDerivconst {a : ℂ} {g : ℂ → ℂ} (ha : a ≠ 0) :
    ∀ z, logDeriv (fun w ↦ a * g w) z = logDeriv g z := by
  intro z
  exact logDeriv_const_mul z a ha

-- Lemma 5: 1Bneq0
lemma oneBneq0 (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z):
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0 ≠ 0 ∧
    (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ ≠ 0 := by
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hR1_pos
  have hB0ne :
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0 ≠ 0 := by
    have h := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec

    exact h 0 h0mem
  refine And.intro hB0ne ?_
  exact inv_ne_zero hB0ne

-- Lemma 6: Lf_deriv_is_logBf_deriv
lemma Lf_deriv_is_logBf_deriv (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                           Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) z =
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) z := by
  intro z _
  -- Rewrite the division as multiplication by inverse
  have h_eq : (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) =
              (fun w ↦ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ *
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) := by
    ext w
    rw [div_eq_mul_inv]
    ring
  rw [h_eq]
  -- Show that Bf ... 0 ≠ 0 using Bf_never_zero
  have h0_in_ball : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simp [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hR1_pos
  have h_Bf0_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec 0 h0_in_ball
  -- Show that the inverse is non-zero
  have h_inv_ne_zero : (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ ≠ 0 :=
    inv_ne_zero h_Bf0_ne_zero
  -- Apply logDerivconst
  exact logDerivconst h_inv_ne_zero z

-- Lemma 7: Lfderiv_is_logderivBf

lemma logDeriv_div_const {a : ℂ} {g : ℂ → ℂ} (ha : a ≠ 0) : ∀ z, logDeriv (fun w ↦ g w / a) z = logDeriv g z := by
  intro z
  have hfun : (fun w ↦ g w / a) = (fun w ↦ a⁻¹ * g w) := by
    funext w
    simp [div_eq_mul_inv, mul_comm]
  simpa [hfun] using (logDerivconst (a := a⁻¹) (g := g) (inv_ne_zero ha) z)

lemma deriv_over_fun_is_logDeriv {g : ℂ → ℂ} : ∀ z, deriv g z / g z = logDeriv g z := by
  intro z
  rfl

-- Lemma 8: logDerivmul
lemma logDerivmul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hf_ne : f z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ f w * g w) z = logDeriv f z + logDeriv g z := by
  exact logDeriv_mul z hf_ne hg_ne hf hg

-- Lemma 9: logDerivprod
lemma logDerivprod {K : Finset ℂ} {g : ℂ → ℂ → ℂ} {z : ℂ}
    (hg_diff : ∀ ρ ∈ K, DifferentiableAt ℂ (g ρ) z)
    (hg_ne : ∀ ρ ∈ K, g ρ z ≠ 0) :
    logDeriv (fun w ↦ ∏ ρ ∈ K, g ρ w) z = ∑ ρ ∈ K, logDeriv (g ρ) z := by
  exact logDeriv_prod K g z hg_ne hg_diff

-- Lemma 10: logDerivdiv
lemma logDerivdiv {h g : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (hg : DifferentiableAt ℂ g z)
    (hh_ne : h z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ h w / g w) z = logDeriv h z - logDeriv g z := by
  exact logDeriv_div z hh_ne hg_ne hh hg

-- Lemma 11: logDerivfunpow
lemma logDerivfunpow {g : ℂ → ℂ} {z : ℂ} {m : ℕ}
    (hg : DifferentiableAt ℂ g z) :
    logDeriv (fun w ↦ (g w) ^ m) z = m * logDeriv g z := by
  exact logDeriv_fun_pow hg m

-- Continuing with the remaining lemmas...

-- Lemma 12: z_minus_rho_diff_nonzero
lemma z_minus_rho_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    z - ρ ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ w - ρ) z := by
  intro ρ hρ z hz
  have hz_pair := (Set.mem_diff z).1 hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_pair.1
  have hz_notK : z ∉ zerosetKfR R1 (by linarith) f := hz_pair.2
  -- Show z ≠ ρ hence z - ρ ≠ 0
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz_notK (by simpa [h_eq] using hρ)
  have h_nonzero : z - ρ ≠ 0 := sub_ne_zero.mpr hz_ne_rho
  -- Differentiability of w ↦ w - ρ at z
  have hdiff : DifferentiableAt ℂ (fun w => w) z := differentiableAt_fun_id
  have hdiff_sub : DifferentiableAt ℂ (fun w => w - ρ) z := hdiff.sub_const ρ
  exact ⟨h_nonzero, hdiff_sub⟩

-- Lemma 13: blaschke_num_diff_nonzero
lemma blaschke_num_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
    R - (star ρ) * z / R ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := by
  intro ρ hρ z hz
  constructor
  · intro hzero
    have hRne : (R : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (hR1_pos.trans hR1_lt_R)))
    -- From the equation R - conj(ρ) * z / R = 0, deduce conj(ρ) * z = R^2
    have heq : (R : ℂ) = (star ρ) * z / (R : ℂ) := sub_eq_zero.mp hzero
    have hmul := congrArg (fun t : ℂ => t * (R : ℂ)) heq
    have heq_mul : (R : ℂ) * (R : ℂ) = (star ρ) * z := by
      -- simplify the right-hand side
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hRne] using hmul
    -- Take norms and simplify
    have hnorm_eq : ‖(R : ℂ)‖ * ‖(R : ℂ)‖ = ‖ρ‖ * ‖z‖ := by
      simpa [Complex.norm_mul, Complex.norm_conj] using congrArg (fun t : ℂ => ‖t‖) heq_mul
    -- Bounds: ‖z‖ ≤ R and ‖ρ‖ ≤ R1
    have hz_norm_le : ‖z‖ ≤ R := by
      have hz' : dist z (0 : ℂ) ≤ R := (Metric.mem_closedBall.mp hz)
      simpa [dist_eq_norm] using hz'
    have hrho_norm_le : ‖ρ‖ ≤ R1 := by
      rcases hρ with ⟨hρ_ball, _hρ_zero⟩
      have : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_ball)
      simpa [dist_eq_norm] using this
    have hz_nonneg : 0 ≤ ‖z‖ := by simp
    have hR1_nonneg : 0 ≤ R1 := le_of_lt hR1_pos
    have hle : ‖ρ‖ * ‖z‖ ≤ R1 * R := by
      have h1 : ‖ρ‖ * ‖z‖ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hrho_norm_le hz_nonneg
      have h2 : R1 * ‖z‖ ≤ R1 * R := mul_le_mul_of_nonneg_left hz_norm_le hR1_nonneg
      exact le_trans h1 h2
    -- Evaluate ‖(R : ℂ)‖ as R (since R > 0)
    have hnorm_R : ‖(R : ℂ)‖ = R := by
      have h1 : ‖(R : ℂ)‖ = |R| := by simp
      simp [h1, abs_of_pos (hR1_pos.trans hR1_lt_R)]
    -- Rewrite the equality using hnorm_R
    have : R * R = ‖ρ‖ * ‖z‖ := by simpa [hnorm_R] using hnorm_eq
    have hle' : R * R ≤ R1 * R := by simpa [this] using hle
    -- But R1 * R < R * R since R > 0, hence RHS < LHS, contradiction
    have hposR : 0 < R := hR1_pos.trans hR1_lt_R
    have hposRR : 0 < R * R := by nlinarith [hposR]
    have hlt : R1 * R < R * R := by
      exact (mul_lt_mul_iff_left₀ hposR).mpr hR1_lt_R
    exact (lt_irrefl _ (lt_of_le_of_lt hle' hlt))
  · -- Differentiability: linear function
    have h_const : DifferentiableAt ℂ (fun _ : ℂ => (R : ℂ)) z := by
      simp
    have h_id : DifferentiableAt ℂ (fun w : ℂ => w) z := by
      simp
    have h_mul : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w) z := by
      simpa using h_id.const_mul (star ρ)
    have h_div : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w / (R : ℂ)) z := by
      simpa [div_eq_mul_inv] using h_mul.mul_const ((R : ℂ)⁻¹)
    simpa using h_const.sub h_div

-- Lemma 14: blaschke_frac_diff_nonzero
lemma blaschke_frac_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (R - (star ρ) * z / R) / (z - ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro ρ hρ z hz
  -- Denominator: nonvanishing and differentiable
  have hden := z_minus_rho_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz
  have hden_ne : z - ρ ≠ 0 := hden.1
  have hden_diff : DifferentiableAt ℂ (fun w ↦ w - ρ) z := hden.2
  -- Extract membership in the smaller closed ball
  have hz_in_small : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_diff] using hz
  have hz_small : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_in_small.1
  -- Show z ∈ closedBall 0 1 to use the numerator lemma
  have hz_dist_le_small : dist z (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hz_small
  have hRle : R ≤ 1 := le_of_lt hR_lt_1
  have hR1_le_R : R1 ≤ R := le_of_lt hR1_lt_R
  have hR1_le_1 : R1 ≤ 1 := le_trans hR1_le_R hRle
  have hz_ball1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hz_le1 : dist z (0 : ℂ) ≤ 1 := le_trans hz_dist_le_small hR1_le_1
    simpa [Metric.mem_closedBall] using hz_le1
  -- Numerator: nonvanishing and differentiable
  have hz_ballR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : dist z (0 : ℂ) ≤ R := le_trans hz_dist_le_small (le_of_lt hR1_lt_R)
    simpa [Metric.mem_closedBall] using hz_le_R
  have hnum := blaschke_num_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz_ballR
  have hnum_ne : R - (star ρ) * z / R ≠ 0 := hnum.1
  have hnum_diff : DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := hnum.2
  -- Conclude
  refine And.intro ?_ ?_
  · intro h
    have h' : (R - (star ρ) * z / R) * (z - ρ)⁻¹ = 0 := by
      simpa [div_eq_mul_inv] using h
    rcases mul_eq_zero.mp h' with hnum0 | hinv0
    · exact hnum_ne hnum0
    · exact hden_ne (inv_eq_zero.mp hinv0)
  · exact hnum_diff.div hden_diff hden_ne

-- Lemma 15: blaschke_pow_diff_nonzero
lemma blaschke_pow_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro ρ hρ z hz
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ z hz
  rcases hfrac with ⟨hne, hdiff⟩
  constructor
  · exact pow_ne_zero _ hne
  · simpa using hdiff.pow ((analyticOrderAt f ρ).toNat)

-- Lemma 16: blaschke_prod_diff_nonzero
lemma blaschke_prod_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (∏ ρ ∈ h_finite_zeros.toFinset, ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  classical
  constructor
  · -- non-vanishing of the product
    have hne_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.1
    exact (Finset.prod_ne_zero_iff).2 hne_each
  · -- differentiability of the product
    have hdiff_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        DifferentiableAt ℂ
          (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.2
    -- Use DifferentiableAt.finset_prod and identify the function
    have hdiff :=
      (DifferentiableAt.finset_prod (u := h_finite_zeros.toFinset)
        (f := fun ρ => fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        (x := z) hdiff_each)
    have hfun_eq :
        (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        =
        (∏ ρ ∈ h_finite_zeros.toFinset,
            (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)) := by
      funext w
      simp [Finset.prod_apply]
    exact hfun_eq.symm ▸ hdiff

-- Lemma 17: f_diff_nonzero_outside_Kf
lemma f_diff_nonzero_outside_Kf {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith ) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    f z ≠ 0 ∧ DifferentiableAt ℂ f z := by
  intro z hz
  -- unpack membership in the set difference
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_diff] using hz
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 := hz'.1
  have hz_notin : z ∉ zerosetKfR R1 (by linarith) f := hz'.2
  -- show f z ≠ 0
  have hz_nonzero : f z ≠ 0 := by
    intro hfz
    exact hz_notin ⟨hz_in_R1, hfz⟩
  -- show differentiable at z using analyticity on closedBall 1
  have hR1_lt_1 : R1 < 1 := by linarith
  have hsubset1 :
      Metric.closedBall (0 : ℂ) R1 ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hR1_lt_1
  have hz_in_ball1 : z ∈ Metric.ball (0 : ℂ) 1 := hsubset1 hz_in_R1
  have hz_in_1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.ball_subset_closedBall hz_in_ball1
  have hAna : AnalyticAt ℂ f z := h_f_analytic z hz_in_1
  have hDiff : DifferentiableAt ℂ f z := hAna.differentiableAt
  exact ⟨hz_nonzero, hDiff⟩

-- Lemma 18: Bf_diff_nonzero_outside_Kf
lemma Bf_diff_nonzero_outside_Kf
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z ≠ 0 ∧
    DifferentiableAt ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z := by
  intro z hz
  -- Extract membership from set difference
  rw [Set.mem_diff] at hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz.1

  constructor
  · -- Bf z ≠ 0: Apply Bf_never_zero directly
    exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz_ball

  · -- DifferentiableAt: Use Bf_is_analytic_on_disk
    -- Since R1 < R, we have closedBall R1 ⊆ closedBall R
    have hz_R : z ∈ Metric.closedBall (0 : ℂ) R :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_R) hz_ball
    -- Get AnalyticOnNhd from the lemma
    have h_analytic_on := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
    -- Apply to get AnalyticAt at z
    have h_analytic_at := h_analytic_on z hz_R
    -- Convert AnalyticAt to DifferentiableAt
    exact h_analytic_at.differentiableAt

-- Lemma 19: logDeriv_fprod_is_sum
lemma logDeriv_fprod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ f w * ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    logDeriv f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hf' := f_diff_nonzero_outside_Kf (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hf' with ⟨hf_ne, hf_diff⟩
  have hg' := blaschke_prod_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hg' with ⟨hg_ne, hg_diff⟩
  simpa using
    (logDerivmul (f:=f) (g:=fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) (z:=z)
      hf_diff hg_diff hf_ne hg_ne)

-- Lemma 20: logDeriv_Bf_is_sum

lemma nhds_avoids_finset {z : ℂ} (K : Finset ℂ) (hz : z ∉ (K : Set ℂ)) : ∀ᶠ w in nhds z, ∀ ρ ∈ K, w ≠ ρ := by
  classical
  -- Define the open set avoiding all points of K
  let U : Set ℂ := ⋂ ρ ∈ K, {w : ℂ | w ≠ ρ}
  -- Each set {w | w ≠ ρ} is open, being the complement of a singleton
  have hopen_each : ∀ ρ ∈ K, IsOpen ({w : ℂ | w ≠ ρ} : Set ℂ) := by
    intro ρ hρ
    have hopen : IsOpen ((({ρ} : Set ℂ)ᶜ : Set ℂ)) := isOpen_compl_singleton
    have hEq : ((({ρ} : Set ℂ)ᶜ : Set ℂ)) = {w : ℂ | w ≠ ρ} := by
      ext w; simp
    simpa [hEq]
      using hopen
  -- Hence the finite intersection is open
  have hopenU : IsOpen U :=
    isOpen_biInter_finset (s := K) (f := fun ρ : ℂ => ({w : ℂ | w ≠ ρ} : Set ℂ)) hopen_each
  -- z belongs to U because z ≠ ρ for all ρ ∈ K (since z ∉ K)
  have hzU : z ∈ U := by
    have hznot : ∀ ρ ∈ K, z ≠ ρ := by
      intro ρ hρ
      intro h
      exact hz (by simpa [h] using hρ)
    simpa [U] using hznot
  -- Therefore U is a neighborhood of z
  have hU_mem : U ∈ nhds z := hopenU.mem_nhds hzU
  -- Any point in U is different from all points of K
  refine Filter.eventually_of_mem hU_mem ?_
  intro w hw ρ hρ
  have hw_all := Set.mem_iInter₂.mp hw
  have : w ∈ ({w : ℂ | w ≠ ρ} : Set ℂ) := hw_all ρ hρ
  simpa using this

lemma pow_div_pow_eq_div_pow (a b : ℂ) (n : ℕ) : a^n / b^n = (a / b)^n := by
  simpa using (div_pow a b n).symm

lemma Cf_eventually_eq_f_div_prod {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    (fun w ↦ Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (by simp [h_f_zero]) h_finite_zeros h_σ w)
      =ᶠ[nhds z]
    (fun w ↦ f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) := by
  classical
  rcases hz with ⟨hz_ball, hz_notin⟩
  -- Let S be the finite zero set
  set S : Set ℂ := zerosetKfR R1 (by linarith) f
  have hS_fin : S.Finite := h_finite_zeros
  have hS_closed : IsClosed S := hS_fin.isClosed
  have hU_open : IsOpen Sᶜ := hS_closed.isOpen_compl
  have hz_memU : z ∈ Sᶜ := by simpa [S] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hz_memU
  refine Filter.eventually_of_mem hU_mem ?_
  intro w hw
  have hw_notin : w ∉ S := by
    -- w ∈ Sᶜ
    simpa [Set.mem_compl] using hw
  -- Simplify Cf on Sᶜ
  simp [S, Cf, hw_notin]

lemma eventuallyEq_mul_right_fun {α β} {l : Filter α} [Mul β]
  {f g h : α → β} (hfg : f =ᶠ[l] g) :
  (fun x => f x * h x) =ᶠ[l] (fun x => g x * h x) := by
  have hhh : h =ᶠ[l] h := Filter.EventuallyEq.rfl
  simpa using (Filter.EventuallyEq.mul (l := l) (f := f) (f' := h) (g := g) (g' := h) hfg hhh)

lemma inv_prod_complex {ι} (s : Finset ι) (f : ι → ℂ) : (∏ x ∈ s, f x)⁻¹ = ∏ x ∈ s, (f x)⁻¹ := by
  classical
  simp

lemma prod_num_mul_inv_den_eq_prod_ratio
  (K : Finset ℂ) (N D : ℂ → ℂ) (m : ℂ → ℕ) :
  (∏ ρ ∈ K, (N ρ) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ) ^ (m ρ))⁻¹
  = ∏ ρ ∈ K, ((N ρ / D ρ) ^ (m ρ)) := by
  classical
  -- rewrite inverse of product as product of inverses
  have hinv : (∏ ρ ∈ K, (D ρ) ^ (m ρ))⁻¹ = ∏ ρ ∈ K, ((D ρ) ^ (m ρ))⁻¹ := by
    simp
  calc
    (∏ ρ ∈ K, (N ρ) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ) ^ (m ρ)) * (∏ ρ ∈ K, ((D ρ) ^ (m ρ))⁻¹) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ) ^ (m ρ) * ((D ρ) ^ (m ρ))⁻¹) := by
          simpa using (Finset.prod_mul_distrib (s := K)
                        (f := fun ρ => (N ρ) ^ (m ρ))
                        (g := fun ρ => ((D ρ) ^ (m ρ))⁻¹)).symm
    _ = ∏ ρ ∈ K, ((N ρ / D ρ) ^ (m ρ)) := by
          apply Finset.prod_congr rfl
          intro ρ hρ
          -- manipulate per factor
          calc
            (N ρ) ^ (m ρ) * ((D ρ) ^ (m ρ))⁻¹
                = (N ρ) ^ (m ρ) * ((D ρ)⁻¹) ^ (m ρ) := by
                  simp
            _ = ((N ρ) * (D ρ)⁻¹) ^ (m ρ) := by
                  simp [mul_pow]
            _ = (N ρ / D ρ) ^ (m ρ) := by
                  simp [div_eq_mul_inv]

lemma prod_num_mul_inv_den_eq_prod_ratio_fun
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  have h_inv :
      (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹ = ∏ ρ ∈ K, ((D ρ w) ^ (m ρ))⁻¹ := by
    simp
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, ((D ρ w) ^ (m ρ))⁻¹) := by
          rw [h_inv]
    _   = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ)) * ((D ρ w) ^ (m ρ))⁻¹ := by
          simpa using
            (Finset.prod_mul_distrib
              (s := K)
              (f := fun ρ => (N ρ w) ^ (m ρ))
              (g := fun ρ => ((D ρ w) ^ (m ρ))⁻¹)).symm
    _   = ∏ ρ ∈ K, (N ρ w / D ρ w) ^ (m ρ) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow :
            (N ρ w / D ρ w) ^ (m ρ)
              = ((N ρ w) ^ (m ρ)) * ((D ρ w) ^ (m ρ))⁻¹ := by
            simp [div_eq_mul_inv, mul_pow, inv_pow]
          simp [hpow]

lemma div_mul_eq_mul_mul_inv_fun {α} (f A B : α → ℂ) :
  (fun w => (f w / A w) * B w) = (fun w => f w * (B w * (A w)⁻¹)) := by
  funext w
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma assoc_fun_mul {α} (f g h : α → ℂ) : (fun w => f w * (g w * h w)) = (fun w => (f w * g w) * h w) := by
  funext w
  simp [mul_assoc]

lemma prod_num_mul_inv_den_eq_prod_ratio_fun_mem
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) / (∏ ρ ∈ K, (D ρ w) ^ (m ρ)) := by
          simp [div_eq_mul_inv]
    _ = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ)) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ)) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow_div :
              (N ρ w / D ρ w) ^ (m ρ)
                = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
            calc
              (N ρ w / D ρ w) ^ (m ρ)
                  = (N ρ w * (D ρ w)⁻¹) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
              _ = (N ρ w) ^ (m ρ) * ((D ρ w)⁻¹) ^ (m ρ) := by
                        simpa using (mul_pow (N ρ w) ((D ρ w)⁻¹) (m ρ))
              _ = (N ρ w) ^ (m ρ) * ((D ρ w) ^ (m ρ))⁻¹ := by
                        simp
              _ = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
          simpa using hpow_div.symm

lemma eventuallyEq_of_eq {α β} {l : Filter α} {f g : α → β} (h : f = g) : f =ᶠ[l] g := by
  simp [h]

lemma logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
  (hfg : f =ᶠ[nhds z] g) : logDeriv f z = logDeriv g z := by
  -- Values agree at z and so do derivatives, since both are local with respect to nhds z
  have hval : f z = g z := Filter.EventuallyEq.eq_of_nhds hfg
  have hderiv_eq_ev : deriv f =ᶠ[nhds z] deriv g := hfg.deriv
  have hderiv : deriv f z = deriv g z := Filter.EventuallyEq.eq_of_nhds hderiv_eq_ev
  -- Rewrite logDeriv in terms of deriv and evaluation
  have hf := deriv_over_fun_is_logDeriv (g := f) z
  have hg := deriv_over_fun_is_logDeriv (g := g) z
  simp [hf.symm, hg.symm, hval, hderiv]

lemma logDeriv_Bf_is_sum :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \
          zerosetKfR R1 (by linarith) f,
    logDeriv (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z =
    logDeriv f z +
      logDeriv
        (fun w ↦
          ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  classical
  intro z hz
  -- Abbreviations
  set K : Finset ℂ := h_finite_zeros.toFinset
  -- Define denominator and numerator products and the ratio product
  let A : ℂ → ℂ := fun w => ∏ ρ ∈ K, (w - ρ) ^ (analyticOrderAt f ρ).toNat
  let BN : ℂ → ℂ := fun w => ∏ ρ ∈ K, (R - (star ρ) * w / R) ^ (analyticOrderAt f ρ).toNat
  let RatProd : ℂ → ℂ :=
    fun w => ∏ ρ ∈ K, ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat
  -- Establish: Bf is eventually equal to f times the product of ratios near z
  set S : Set ℂ := zerosetKfR R1 (by linarith) f
  have hS_fin : S.Finite := h_finite_zeros
  have hU_open : IsOpen Sᶜ := hS_fin.isClosed.isOpen_compl
  have hz_notin : z ∉ S := by
    rcases hz with ⟨_, hnotin⟩; exact hnotin
  have hzU : z ∈ Sᶜ := by simpa [Set.mem_compl] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hzU
  have h_ev :
      (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
        =ᶠ[nhds z]
      (fun w ↦ f w * RatProd w) := by
    refine Filter.eventually_of_mem hU_mem ?_
    intro w hwU
    have hw_notin : w ∉ S := by simpa [Set.mem_compl] using hwU
    -- Rewrite Bf and Cf at points away from the zero set
    have hBf_w :
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w * BN w := by
      simp [Bf, BN, K]
    have hCf_w :
        Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = f w / A w := by
      simp [Cf, S, A, K, hw_notin]
    -- Use functional identities to simplify to f * RatProd
    have h_eq1 := div_mul_eq_mul_mul_inv_fun (f := f) (A := A) (B := BN)
    have h_eq1_w : (f w / A w) * BN w = f w * (BN w * (A w)⁻¹) := by
      simpa using congrArg (fun g : (ℂ → ℂ) => g w) h_eq1
    have h_eq2 :=
      prod_num_mul_inv_den_eq_prod_ratio_fun_mem
        (K := K)
        (N := fun ρ w ↦ (R - (star ρ) * w / R))
        (D := fun ρ w ↦ (w - ρ))
        (m := fun ρ ↦ (analyticOrderAt f ρ).toNat)
    have h_eq2_w : BN w * (A w)⁻¹ = RatProd w := by
      simpa [BN, A, RatProd] using congrArg (fun g : (ℂ → ℂ) => g w) h_eq2
    -- Chain the equalities
    calc
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = (f w / A w) * BN w := by simpa [hCf_w] using hBf_w
      _ = f w * (BN w * (A w)⁻¹) := h_eq1_w
      _ = f w * RatProd w := by simp [h_eq2_w]
  -- Transfer equality to logDeriv at z
  have hlog_congr := logDeriv_congr_of_eventuallyEq (f := fun w ↦
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
      (g := fun w ↦ f w * RatProd w) (z := z) h_ev
  -- Apply product rule to the RHS
  have hsum :=
    (logDeriv_fprod_is_sum (R:=R) (R1:=R1) (f:=f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz)
  simpa [RatProd, K] using hlog_congr.trans hsum

-- Lemma 21: logDeriv_def_as_frac
lemma logDeriv_def_as_frac {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hf_ne : f z ≠ 0) :
    logDeriv f z = deriv f z / f z := by
  simp [logDeriv]

def ball_containment {r R1 : ℝ} (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (z : ℂ) (hz : z ∈ Metric.closedBall 0 r) : z ∈ Metric.closedBall 0 R1 := by
  simp at *
  exact le_trans hz (le_of_lt hr_lt_R1)

theorem in_r_minus_kf {R1 r : ℝ} {f : ℂ → ℂ}
  (hr_pos : 0 < r)
  (hr_lt_R1 : r < R1)
  (z : ℂ)
  (hz : z ∈ Metric.closedBall 0 r \ zerosetKfR R1 (by linarith) f) :
   z ∈ Metric.closedBall 0 R1 \ zerosetKfR R1 (by linarith) f := by
  obtain ⟨h1, h2⟩ := hz
  have : z ∈ Metric.closedBall 0 R1 := by
    apply ball_containment hr_pos hr_lt_R1 z h1
  constructor <;> assumption

-- Lemma 22: Lf_deriv_step1
lemma Lf_deriv_step1 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                                ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  -- Extract closedBall membership
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r ∧ z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_diff] using hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := hz'.1
  -- From Lfderiv_is_logderivBf
  have hLf :=
  --
    (Lf_deriv_is_logBf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
      z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)).symm
  -- Expand logDeriv of Bf into sum
  have hsum :
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z =
      logDeriv f z +
        logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    have h :=
      (logDeriv_Bf_is_sum (R := R) (R1 := R1) (r := r) (f := f) (h_σ := h_σ)
        hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros) z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
    simpa using h
  -- Turn logDeriv f into deriv f / f using differentiability and nonvanishing
  obtain ⟨hf_ne, hfdiff⟩ :=
    f_diff_nonzero_outside_Kf (R := R) (R1 := R1) (f := f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have hfrac : logDeriv f z = deriv f z / f z :=
    logDeriv_def_as_frac (f := f) (z := z) hfdiff hf_ne
  -- Combine
  -- First, identify deriv Lf with the logarithmic derivative of Bf at z
  have hLf_eq_logDerivBf :
      deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z := by
    -- Unfold Lf to use the derivative property from log_of_analytic
    -- and then rewrite deriv B / B as logDeriv B.
    have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r := hz_ball
    -- Define B_f and set up the existence from log_of_analytic
    let B_f : ℂ → ℂ :=
      fun w => Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
    let log_exists := log_of_analytic
      (r1 := r) (R' := R1) (R := R)
      hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
      (B := B_f)
      (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1
                f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
      (hB_ne_zero := by
        intro w hw
        exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1
          f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw)
    have hderiv_all : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        deriv (Classical.choose log_exists) w = deriv B_f w / B_f w :=
      (Classical.choose_spec log_exists).2.2.1
    have hderiv_Lf :
        deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos
                    h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
          = deriv B_f z / B_f z := by
      -- Match the definition of Lf with the chosen function from log_exists
      unfold Lf
      -- The unfolded definition uses the same B_f and log_of_analytic; reduce by definitional equality
      simpa using hderiv_all z hz_in_r
    -- Now rewrite deriv B_f / B_f as logDeriv B_f
    have h_as_log : deriv B_f z / B_f z = logDeriv B_f z :=
      deriv_over_fun_is_logDeriv (g := B_f) z
    -- Conclude
    simpa [B_f] using hderiv_Lf.trans h_as_log
  -- Chain the identities: deriv Lf = logDeriv Bf = logDeriv f + logDeriv(prod),
  -- then rewrite logDeriv f as deriv f / f.
  calc
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
        = logDeriv (fun w ↦
            Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
              h_finite_zeros h_σ w) z := hLf_eq_logDerivBf
    _ = logDeriv f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := hsum
    _ = deriv f z / f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
            simp [hfrac]

-- Lemma 23: logDeriv_prod_is_sum
lemma logDeriv_prod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, logDeriv (fun w ↦
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hdiff : ∀ ρ ∈ h_finite_zeros.toFinset,
      DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.2
  have hne : ∀ ρ ∈ h_finite_zeros.toFinset,
      ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.1
  simpa using
    (logDerivprod (K := h_finite_zeros.toFinset)
      (g := fun ρ w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
      (z := z) hdiff hne)

-- Lemma 24: logDeriv_power_is_mul
lemma logDeriv_power_is_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    (analyticOrderAt f ρ).toNat * logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz ρ hρFin
  have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    simpa using (h_finite_zeros.mem_toFinset.mp hρFin)
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρmem z hz
  rcases hfrac with ⟨_hneq, hdiff⟩
  simpa using
    (logDerivfunpow (g := fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) (z := z)
      (m := (analyticOrderAt f ρ).toNat) hdiff)

-- Lemma 25: logDeriv_prod_is_sum_mul
lemma logDeriv_prod_is_sum_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have hsum :=
    logDeriv_prod_is_sum (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  exact
    logDeriv_power_is_mul (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ

-- Lemma 26: Lf_deriv_step2
lemma Lf_deriv_step2 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                                       logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have h1 :=
    Lf_deriv_step1 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  have hsum :=
    logDeriv_prod_is_sum_mul (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have h2 := congrArg (fun t => deriv f z / f z + t) hsum
  exact h1.trans h2

-- Lemma 27: logDeriv_Blaschke_is_diff
lemma logDeriv_Blaschke_is_diff {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
    logDeriv (fun w ↦ R - (star ρ) * w / R) z - logDeriv (fun w ↦ w - ρ) z := by
  intro z hz ρ hρ
  have hρ_set : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (Set.Finite.mem_toFinset (hs := h_finite_zeros) (a := ρ)).mp hρ
  rcases hz with ⟨hz_in, hz_notin⟩
  have hden := z_minus_rho_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z ⟨hz_in, hz_notin⟩
  rcases hden with ⟨hden_nz, hden_diff⟩
  have hz_le : ‖z‖ ≤ R1 := by
    simpa [Metric.closedBall, dist_eq_norm] using hz_in
  have hle1 : R1 < 1 := by linarith [hR1_lt_R, hR_lt_1]
  have hz_in1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have : ‖z‖ ≤ 1 := le_of_lt (hz_le.trans_lt hle1)
    simpa [Metric.closedBall, dist_eq_norm] using this
  have hz_inR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : ‖z‖ ≤ R := by
      calc ‖z‖ ≤ R1 := hz_le
      _ ≤  R := le_of_lt hR1_lt_R
    simpa [Metric.closedBall, dist_eq_norm] using hz_le_R
  have hnum := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z hz_inR
  rcases hnum with ⟨hnum_nz, hnum_diff⟩
  simpa using
    (logDerivdiv (hh := hnum_diff) (hg := hden_diff) (hh_ne := hnum_nz) (hg_ne := hden_nz))

-- Lemma 28: logDeriv_linear
lemma logDeriv_linear {a b : ℂ} {z : ℂ} (ha : a ≠ 0) (hz : z ≠ -b/a) :
    logDeriv (fun w ↦ a * w + b) z = a / (a * z + b) := by
  -- derivative of w ↦ a * w is a
  have h_id : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id _
  have h_mul' : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa [one_mul] using (h_id.const_mul a)
  have h_deriv_mul : deriv (fun w : ℂ => a * w) z = a := h_mul'.deriv
  -- unfold logDeriv and compute
  simp [logDeriv, h_deriv_mul]

-- Lemma 29: logDeriv_denominator
lemma logDeriv_denominator {ρ : ℂ} {z : ℂ} (hz : z ≠ ρ) :
    logDeriv (fun w ↦ w - ρ) z = 1 / (z - ρ) := by
  have h :=
    logDeriv_linear (a := (1 : ℂ)) (b := -ρ) (z := z)
      (ha := by simp)
      (hz := by simpa using hz)
  simpa [one_mul, sub_eq_add_neg] using h

-- Lemma 30: logDeriv_numerator_pre
lemma logDeriv_numerator_pre {R : ℝ} {ρ : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = -(star ρ) / R / (R - (star ρ) * z / R) := by
  classical
  -- Put the function in the linear form b + a * w
  let a : ℂ := -(star ρ) / (R : ℂ)
  let b : ℂ := (R : ℂ)
  have hlin : (fun w : ℂ ↦ (R : ℂ) - (star ρ) * w / (R : ℂ)) = (fun w : ℂ ↦ b + a * w) := by
    funext w
    -- rewrite as b + a*w
    simp [a, b, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
          add_comm, add_left_comm, add_assoc]
  -- Compute the derivative of b + a * w
  have hderiv_add : deriv (fun w : ℂ => b + a * w) z =
      deriv (fun _ : ℂ => b) z + deriv (fun y : ℂ => a * y) z := by
    simp
  have hderiv_ab : deriv (fun w : ℂ => b + a * w) z = a := by
    simp [deriv_const, deriv_const_mul, mul_comm]
  -- Now compute the logarithmic derivative and rewrite back
  simp [hlin, logDeriv, hderiv_ab, a, b, sub_eq_add_neg, div_eq_mul_inv,
         mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

lemma star_ne_zero_of_ne_zero {ρ : ℂ} (hρ : ρ ≠ 0) : star ρ ≠ 0 := by
  -- Use that conjugation preserves (and reflects) zero over ℂ
  -- This is true in any star semiring: star x = 0 ↔ x = 0
  -- We use the forward direction: if star ρ = 0 then ρ = 0, contradicting hρ
  intro h
  -- apply the equivalence star_eq_zero.mp
  have : ρ = 0 := (star_eq_zero).1 h
  exact hρ this

lemma field_identity_general {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hden : a - c*b/a ≠ 0) : (-(b/a)) / (a - c*b/a) = (1 : K) / (c - a^2/b) := by
  -- Multiply numerator and denominator by -a/b
  have hmul : (-(a / b) : K) ≠ 0 := by
    have hdiv_ne : a / b ≠ 0 := div_ne_zero ha hb
    exact neg_ne_zero.mpr hdiv_ne
  have hnum : (-(b/a) * (-(a/b))) = (1 : K) := by
    calc
      (-(b/a) * (-(a/b))) = (b/a) * (a/b) := by simp [neg_mul_neg]
      _ = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have hOne : (b/a) * (a/b) = (1 : K) := by
    calc
      (b/a) * (a/b) = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have haab : a * (a / b) = a^2 / b := by
    simp [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hcbab : (c * b / a) * (a / b) = c := by
    calc
      (c * b / a) * (a / b) = (c * (b / a)) * (a / b) := by simp [div_eq_mul_inv, mul_assoc]
      _ = c * ((b / a) * (a / b)) := by simp [mul_assoc]
      _ = c * 1 := by simp [hOne]
      _ = c := by simp
  have hdenom : ((a - c*b/a) * (-(a/b))) = c - a^2 / b := by
    calc
      ((a - c*b/a) * (-(a/b))) = -((a - c*b/a) * (a / b)) := by simp [mul_neg]
      _ = -(a * (a / b) - (c * b / a) * (a / b)) := by simp [sub_mul]
      _ = (c * b / a) * (a / b) - a * (a / b) := by simp [neg_sub]
      _ = c - a^2 / b := by simp [hcbab, haab]
  calc
    (-(b/a)) / (a - c*b/a)
        = (-(b/a) * (-(a/b))) / ((a - c*b/a) * (-(a/b))) := by
          simpa using
            (mul_div_mul_right (a := (-(b / a))) (b := (a - c * b / a)) (c := (-(a / b))) hmul).symm
    _ = 1 / ((a - c*b/a) * (-(a/b))) := by simp [hnum]
    _ = 1 / (c - a^2/b) := by simp [hdenom]

lemma complex_identity_from_field {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hρ : ρ ≠ 0) (hden : (R:ℂ) - (star ρ) * z / R ≠ 0) : (-(star ρ) / (R:ℂ)) / ((R:ℂ) - (star ρ) * z / R) = (1 : ℂ) / (z - (R:ℂ)^2 / (star ρ)) := by
  have ha : (R : ℂ) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hR)
  have hb : star ρ ≠ 0 := star_ne_zero_of_ne_zero hρ
  have hden' : (R : ℂ) - z * (star ρ) / (R : ℂ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hden
  have h := field_identity_general (K := ℂ) (a := (R : ℂ)) (b := star ρ) (c := z) ha hb hden'
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h

lemma logDeriv_numerator_rearranged {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hrho : ρ ≠ 0) (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0) : -(star ρ) / R / ((R : ℂ) - (star ρ) * z / R) = 1 / (z - (R : ℂ)^2 / (star ρ)) := by
  simpa using (complex_identity_from_field (R:=R) (ρ:=ρ) (z:=z) (hR:=hR) (hρ:=hrho) (hden:=h_denom_ne_zero))

-- Lemma 32: logDeriv_numerator
lemma logDeriv_numerator {R : ℝ} {ρ : ℂ} {z : ℂ}
    (hR : R ≠ 0)
    (hrho : ρ ≠ 0)
    (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0):
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = 1 / (z - R^2 / (star ρ)) := by
  rw [logDeriv_numerator_pre, logDeriv_numerator_rearranged]
  <;> assumption

-- Lemma 33: logDeriv_Blaschke_is_diff_frac
lemma logDeriv_Blaschke_is_diff_frac {R R1 : ℝ} {f : ℂ → ℂ}
     (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (h_f_zero : f 0 = 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ h_finite_zeros.toFinset,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f , logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
         1 / (z - R^2 / (star ρ)) - 1 / (z - ρ) := by
  intro ρ hρ z hz
  -- Apply the division rule for logDeriv using logDeriv_Blaschke_is_diff
  have h_div := logDeriv_Blaschke_is_diff (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ
  -- Evaluate logDeriv(R - (star ρ) * w / R) using logDeriv_numerator
  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (h_finite_zeros.mem_toFinset).mp hρ
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h_eq
    -- ρ = 0 would mean f(0) = 0, but h_f_zero says f(0) = 1
    have : f 0 = 0 := by simpa [h_eq] using hρ_mem.2
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (this.symm.trans h_f_zero)
  have hR_ne_zero : R ≠ 0 := ne_of_gt (hR1_pos.trans hR1_lt_R)
  have h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0 := by
    -- This follows from blaschke_num_diff_nonzero
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := by
      have hle : R1 < R := hR1_lt_R
      apply Metric.closedBall_subset_closedBall (le_of_lt hle)
      exact hz.1
    have h := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ_mem z hz_ball
    exact h.1
  have h_num := logDeriv_numerator hR_ne_zero hρ_ne_zero h_denom_ne_zero
  -- Evaluate logDeriv(z - ρ) using logDeriv_denominator
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz.2 (by simpa [h_eq] using hρ_mem)
  have h_den := logDeriv_denominator hz_ne_rho
  -- Substitute the results back
  rw [h_div, h_num, h_den]

-- Lemma 34: Lf_deriv_step3
lemma Lf_deriv_step3 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat * (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) := by
  intro z hz
  -- Assuming Lf_deriv_step2 is also corrected to remove B
  rw [Lf_deriv_step2 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  exact logDeriv_Blaschke_is_diff_frac hR1_pos hR1_lt_R hR_lt_1 h_f_zero h_f_analytic h_finite_zeros ρ hρ z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)

-- Lemma 35: sum_of_diff
lemma sum_of_diff {K : Finset ℂ} {a b : ℂ → ℂ} :
    ∑ ρ ∈ K, (a ρ - b ρ) = ∑ ρ ∈ K, a ρ - ∑ ρ ∈ K, b ρ := by
  simp [Finset.sum_sub_distrib]

-- Lemma 36: sum_rearranged
lemma sum_rearranged {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) := by
  intro z hz
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext ρ
  rw [mul_sub, mul_one_div, mul_one_div]

-- Lemma 37: Lf_deriv_final_formula
lemma Lf_deriv_final_formula :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) +
                      ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
  -- Apply Lf_deriv_step3 with the corrected, simpler signature
  rw [Lf_deriv_step3 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
  -- Apply sum_rearranged with a simpler signature
  rw [sum_rearranged hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz]
  -- Rearrange terms
  ring

-- Lemma 38: rearrange_Lf_deriv
lemma rearrange_Lf_deriv :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) =
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
  -- The call to Lf_deriv_final_formula is now simpler as it no longer needs hB
  have h_final := Lf_deriv_final_formula hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  rw [h_final]
  ring

-- Lemma 39: triangle_ineq_sum
lemma triangle_ineq_sum {w₁ w₂ : ℂ} :
    ‖w₁ - w₂‖ ≤ ‖w₁‖ + ‖w₂‖ := by
  have h : w₁ - w₂ = w₁ + (-w₂) := sub_eq_add_neg w₁ w₂
  rw [h]
  have h₁ : ‖w₁ + (-w₂)‖ ≤ ‖w₁‖ + ‖-w₂‖ := norm_add_le w₁ (-w₂)
  have h₂ : ‖-w₂‖ = ‖w₂‖ := norm_neg w₂
  rw [h₂] at h₁; exact h₁

-- Lemma 40: target_inequality_setup
lemma target_inequality_setup :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
  ‖deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
  ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ +
  ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := by
  intro z hz
  -- The call to rearrange_Lf_deriv is now corrected and simplified.
  -- The `hB` argument that caused the error has been removed.
  have hrearr := rearrange_Lf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz

  -- The rest of the proof is a direct application of the triangle inequality.
  -- We want to show ‖A‖ ≤ ‖B‖ + ‖C‖, where hrearr gives A = B - C.
  rw [hrearr]
  exact norm_sub_le _ _
-- Additional helper lemmas needed for the bounds

-- Additional bound lemmas

lemma conj_norm_eq_norm (z : ℂ) : ‖star z‖ = ‖z‖ := by
  simp [Complex.star_def]

lemma norm_div_eq (a b : ℂ) (hb : b ≠ 0) : ‖a / b‖ = ‖a‖ / ‖b‖ := by
  calc
    ‖a / b‖ = ‖a * b⁻¹‖ := by simp [div_eq_mul_inv]
    _ = ‖a‖ * ‖b⁻¹‖ := norm_mul _ _
    _ = ‖a‖ * ‖b‖⁻¹ := by simp [norm_inv]
    _ = ‖a‖ / ‖b‖ := by simp [div_eq_mul_inv]

lemma norm_Rsq_div_conj (R : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0) : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ := by
  have hb : star ρ ≠ 0 := by
    intro h
    have h' := congrArg star h
    -- star (star ρ) = 0, hence ρ = 0
    have : ρ = 0 := by simpa [star_star] using h'
    exact hρ this
  have hnormR : ‖(R^2 : ℂ)‖ = (R^2 : ℝ) := by
    have h := (RCLike.norm_ofReal (K:=ℂ) (R^2))
    simp [abs_of_nonneg (sq_nonneg R)]
  calc
    ‖((R^2 : ℂ) / (star ρ))‖
        = ‖(R^2 : ℂ)‖ / ‖star ρ‖ := norm_div_eq _ _ hb
    _ = (R^2 : ℝ) / ‖ρ‖ := by
      simp [hnormR, conj_norm_eq_norm]

lemma zerosetKfR_subset_closedBall {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} :
  zerosetKfR R1 hR1 f ⊆ Metric.closedBall (0 : ℂ) R1 := by
  intro ρ hρ
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  exact hmem.left

lemma mem_zerosetKfR_ne_zero_of_f0_eq_one {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ}
  (hf0 : f 0 = 1) {ρ : ℂ} (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ρ ≠ 0 := by
  intro hρ0
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  have hzero : f 0 = 0 := by simpa [hρ0] using hmem.right
  have h10 : (1 : ℂ) ≠ 0 := one_ne_zero
  exact h10 (by simp [hf0] at hzero)

lemma norm_sub_ge_norm_sub (x y : ℂ) : ‖x - y‖ ≥ ‖y‖ - ‖x‖ := by
  have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_add_le (y - x) x
  have h' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := (sub_le_iff_le_add).mpr htri
  have hsymm : ‖y - x‖ = ‖x - y‖ := by
    simpa [sub_eq_add_neg, add_comm] using (norm_neg (x - y))
  simpa [hsymm] using h'


lemma mem_zerosetKfR_norm_le {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} {ρ : ℂ}
  (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ‖ρ‖ ≤ R1 := by
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 :=
    (zerosetKfR_subset_closedBall (R1 := R1) hR1 (f := f)) hρ
  have hdist : dist ρ (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hmem
  simpa [dist_eq_norm, sub_zero] using hdist

lemma lem_sum_bound_step2 {R R1: ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      (∑ ρ ∈ h_finite_zeros.toFinset,
          ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ (1/(R^2/R1 - R1)) *
          (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := by
  classical
  intro z hz
  rcases hz with ⟨hzball, _hznotin⟩
  have hz_norm : ‖z‖ ≤ R1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
  -- Define the index finset
  set S := h_finite_zeros.toFinset
  have hS_spec : ∀ {ρ : ℂ}, ρ ∈ S → ρ ∈ zerosetKfR R1 (by linarith) f := by
    intro ρ hρ
    have hiff := (Set.Finite.mem_toFinset (hs := h_finite_zeros) : ρ ∈ S ↔ ρ ∈ zerosetKfR R1 (by linarith) f)
    exact (Iff.mp hiff) hρ
  -- Termwise bound and then sum
  have hsum_le :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ ∑ ρ ∈ S, (1/(R^2/R1 - R1)) * ((analyticOrderAt f ρ).toNat : ℝ) := by
    refine Finset.sum_le_sum ?termwise
    intro ρ hρS
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := hS_spec hρS
    have hρ_ne : ρ ≠ 0 :=
      mem_zerosetKfR_ne_zero_of_f0_eq_one (R1 := R1) (hR1 := by linarith)
        (f := f) h_f_zero hρmem
    have hρ_norm : ‖ρ‖ ≤ R1 := mem_zerosetKfR_norm_le (R1 := R1)
      (hR1 := by linarith) (f := f) hρmem
    have hpt : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1/(R^2/R1 - R1) := by
      -- Use triangle inequality and norms
      have h_Rsq_norm : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ :=
        norm_Rsq_div_conj R ρ hρ_ne
      have h_lower_bound : ‖z - (R^2 : ℂ) / (star ρ)‖ ≥ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ :=
        norm_sub_ge_norm_sub z ((R^2 : ℂ) / (star ρ))
      -- Since ‖ρ‖ ≤ R1 and ‖ρ‖ > 0, we have ‖((R^2 : ℂ) / (star ρ))‖ ≥ R^2/R1
      have hρ_pos : 0 < ‖ρ‖ := by
        simpa [norm_pos_iff] using hρ_ne
      have h_Rsq_bound : R^2/R1 ≤ ‖((R^2 : ℂ) / (star ρ))‖ := by
        rw [h_Rsq_norm]
        exact div_le_div_of_nonneg_left (sq_nonneg R) hρ_pos hρ_norm
      have h_combined : R^2/R1 - R1 ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        calc R^2/R1 - R1
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - R1 := by linarith [h_Rsq_bound]
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ := by linarith [hz_norm]
        _ ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := h_lower_bound
      have h_pos_denom : 0 < R^2/R1 - R1 := by
        have h_R_pos : 0 < R := by linarith [hR1_pos, hR1_lt_R]
        have h_Rsq_pos : 0 < R^2 := sq_pos_of_pos h_R_pos
        calc R^2/R1 - R1
        _ = (R^2 - R1*R1)/R1 := by field_simp
        _ = (R - R1)*(R + R1)/R1 := by ring
        _ > 0 := by
          apply div_pos
          · apply mul_pos
            · linarith [hR1_lt_R]
            · linarith [hR1_pos, hR1_lt_R]
          · exact hR1_pos
      have h_pos_norm : 0 < ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        apply lt_of_lt_of_le h_pos_denom h_combined
      -- Use the basic inequality: if 0 < a ≤ b then 1/b ≤ 1/a
      have h_reciprocal : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1 / (R^2/R1 - R1) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · exact h_pos_denom
        · exact h_combined
      exact h_reciprocal
    have hmnonneg : 0 ≤ ((analyticOrderAt f ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le (analyticOrderAt f ρ).toNat)
    have hmul := mul_le_mul_of_nonneg_left hpt hmnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  -- pull out the constant on the RHS sum
  rw [← Finset.mul_sum] at hsum_le
  exact hsum_le

-- 1/((R^2/R_1 - R_1) log(R/R_1))

lemma sq_div_sub_pos (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) : 0 < b^2/a - a := by
  -- Convert the inequality to a < b^2/a
  rw [sub_pos]
  -- Use lt_div_iff₀ to convert a < b^2/a to a * a < b^2
  rw [lt_div_iff₀ ha_pos]
  -- Rewrite a * a as a^2
  rw [← pow_two]
  -- Now we need a^2 < b^2, which follows from a < b for positive numbers
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  apply pow_lt_pow_left₀ hab ha_nonneg
  norm_num --lem_square_inequality_strict ha_pos hab

lemma final_sum_bound {R R1 B : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (hB : 1 < B)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ ≤
    1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
  intro z hz
  -- Step 1: Use triangle inequality (norm_sum_le)
  have h_norm_bound := norm_sum_le h_finite_zeros.toFinset (fun ρ => (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)))

  -- Step 2: Simplify norm of each term
  have h_sum_eq : ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ =
    ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast]

  -- Step 3: Apply lem_sum_bound_step2 (first lemma from informal proof)
  have h_step2 := lem_sum_bound_step2 hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz

  -- Step 4: Apply lem_sum_m_rho_bound
  have h_f_nonzero : f 0 ≠ 0 := by rw [h_f_zero]; norm_num
  have h_f_bounded_alt : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B := by
    intro w hw
    exact h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw))
  -- Build a uniform existence statement for all σ
  have h_exists : ∀ σ : ℂ, ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g σ ∧ g σ ≠ 0 ∧
      (σ ∈ zerosetKfR R1 (by linarith) f →
        ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z) := by
    intro σ
    by_cases hσ : σ ∈ zerosetKfR R1 (by linarith) f
    · -- σ is a zero: use lem_analytic_zero_factor
      have hex := lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero σ hσ
      obtain ⟨g, hg_at, hg_ne, h_eq⟩ := hex
      exact ⟨g, hg_at, hg_ne, fun _ => h_eq⟩
    · -- σ is not a zero: use constant function 1
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · exact analyticAt_const
      · norm_num
      · intro h_contra
        contradiction
  -- Use classical choice to extract the function
  let h_σ : ℂ → (ℂ → ℂ) := fun σ => Classical.choose (h_exists σ)
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z := by
    intro σ hσ
    have spec := Classical.choose_spec (h_exists σ)
    exact ⟨spec.1, spec.2.1, spec.2.2 hσ⟩
  have h_sum_bound := lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero h_f_zero h_finite_zeros h_σ h_f_bounded_alt h_σ_spec

  -- Step 5: Establish needed positivity properties
  have h_pos : 0 < R^2/R1 - R1 := sq_div_sub_pos R1 R hR1_pos hR1_lt_R
  have h_ratio_gt_one : 1 < R/R1 := by
    rw [one_lt_div_iff]
    left
    exact ⟨hR1_pos, hR1_lt_R⟩
  have h_log_pos : 0 < Real.log (R/R1) := Real.log_pos h_ratio_gt_one

  calc ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖
    ≤ ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := h_norm_bound
    _ = ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := h_sum_eq
    _ ≤ (1/(R^2/R1 - R1)) * (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := h_step2
    _ ≤ (1/(R^2/R1 - R1)) * ((1/Real.log (R/R1)) * Real.log B) := by
              apply mul_le_mul_of_nonneg_left h_sum_bound (div_nonneg zero_le_one (le_of_lt h_pos))
    _ = 1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
      field_simp [ne_of_gt h_pos, ne_of_gt h_log_pos]

-- Now, we can fix the `final_inequality` lemma.
lemma final_inequality
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic :
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec :
      ∀ σ ∈ zerosetKfR R1 (by linarith) f,
        AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ,
          f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,

        ‖(deriv f z / f z
          - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ))‖
      ≤
      16 * r^2 / ((r - r1)^3) * Real.log B
        + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
  intro z hz

  -- Establish missing positive hypotheses from the parameter constraints
  have hr_pos : 0 < r := by linarith [hr1pos, hr1_lt_r]
  have hR1_pos : 0 < R1 := by linarith [hr_pos, hr_lt_R1]

  -- Lift z from r1-ball to r-ball (needed for target_inequality_setup)
  have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_r)
      exact hz.1
    · exact hz.2

  -- Apply target_inequality_setup (from informal proof)
  have hineq :=
    target_inequality_setup hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz_in_r

  -- Lift z from r1-ball to R1-ball (needed for final_sum_bound)
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall
      exact le_of_lt (lt_trans hr1_lt_r hr_lt_R1)
      exact hz.1
    · exact hz.2

  -- Apply final_sum_bound (from informal proof)
  have hsum :=
    final_sum_bound hR1_pos hR1_lt_R hR_lt_1 hB h_f_analytic h_f_zero h_finite_zeros h_f_bounded z hz_in_R1

  -- Apply apply_BC_to_Lf (from informal proof)
  have hz_le_r1 : ‖z‖ ≤ r1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1

  -- Convert ‖z‖ ≤ r1 to norm z ≤ r1 (they are definitionally equal)
  have hz_abs : ‖z‖ ≤ r1 := hz_le_r1

  have h_BC := apply_BC_to_Lf
    (B := B) (r1 := r1) (r := r) (R := R) (R1 := R1)
    (hB := hB) (hr1_pos := hr1pos) (hr1_lt_r := hr1_lt_r) (hr_lt_R1 := hr_lt_R1)
    (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
    (f := f) (h_f_analytic := h_f_analytic) (h_f_zero := h_f_zero)
    (h_finite_zeros := h_finite_zeros) (h_σ := h_σ) (h_σ_spec := h_σ_spec)
    (h_f_bound := fun w hw => h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw)))
    z hz_abs

  -- Convert norm to norm and rearrange the bound
  have hLf : ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ ≤
             16 * r^2 / ((r - r1)^3) * Real.log B := by
    -- h_BC gives: norm (...) ≤ (16 * Real.log B * r^2) / (r - r1)^3
    -- We need: ‖...‖ ≤ 16 * r^2 / ((r - r1)^3) * Real.log B
    -- norm and ‖·‖ are definitionally equal
    convert h_BC using 1
    -- Rearrange: (16 * Real.log B * r^2) / (r - r1)^3 = 16 * r^2 / ((r - r1)^3) * Real.log B
    ring

  exact le_trans hineq (add_le_add hLf hsum)


-- Lemma 43: final_ineq1
lemma final_ineq1
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,
    ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset,
                 (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
    (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log B := by
  intro z hz
  -- Get the bound with separate terms from final_inequality
  have h_bound : ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      16 * r^2 / ((r - r1)^3) * Real.log B + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
    apply final_inequality <;> assumption
  -- Factor out Real.log B using right distributivity: a * c + b * c = (a + b) * c
  rw [← add_mul] at h_bound
  exact h_bound
