import Mathlib

open Set Function

axiom disproofAxiom {a} (h : ¬ a) : a

noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  sorry

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  sorry

noncomputable def ChebyshevPsi (x : ℝ) : ℝ := (Finset.Icc 0 (Nat.floor x)).sum ArithmeticFunction.vonMangoldt

theorem vonManBnd (n : ℕ) : ArithmeticFunction.vonMangoldt n ≤ Real.log n := by
  sorry

theorem extracted_2
    (F : ℝ → ℝ)
    (c₁ c₂ : ℝ)
    (c₁pos : 0 < c₁)
    (c₂pos : 0 < c₂)
    (c₂_lt_one : c₂ < 1)
    (FbddAbove : ∀ x, F x ≤ 1)
    (Fnonneg : ∀ x, F x ≥ 0)
    (FzeroAfter :
      ∀ X > (1 : ℝ), ∀ (n : ℕ), n ≥ (1 + c₁) * X → F (n / X) = 0)
    (Fone :
      ∀ X > (1 : ℝ), ∀ (n : ℕ), 0 < n → n ≤ (1 - c₂) * X → F (n / X) = 1)
     :
    ∀ᶠ (X : ℝ) in Filter.atTop,
    ‖(∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * F (↑n / X)) - ChebyshevPsi X‖ ≤ (c₁ + c₂) * X * Real.log ((1+c₂)*X) := by

  unfold ChebyshevPsi

  have (X Y : ℝ) : ∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * F (↑n / X)
   = (∑ n ∈ Icc 0 (⌊Y⌋₊), ArithmeticFunction.vonMangoldt n * F (↑n / X))
     + ∑' (n : ℕ),
    let n' := n + ⌊Y⌋₊ + 1 ;
      ArithmeticFunction.vonMangoldt n'  * F (↑n' / X) := by

    sorry

  sorry

#exit

  let fact := @vonManBnd

  revert F fact c₁ c₂ c₁pos c₂pos c₂_lt_one

  apply disproofAxiom

  push_neg

  delta ArithmeticFunction.vonMangoldt Polynomial.degree
  delta IsPrimePow
  use fun and =>ite (and ≤ 1) (1) 0
  use 1/16
  use (1)/64,by simp_all,by simp_all,by bound, by aesop, by aesop, fun and A B h=>if_neg ((one_lt_div (by bound)).2 (by bound)).not_le
  constructor
  · use fun and A B R L=>if_pos ((div_le_iff₀ (one_pos.trans A)).2 (by linarith))
  · apply mt (. (3.1)<|by bound)
    rewrite[tsum_eq_sum (s:=.range ↑(.ceil (3.1: ℝ)+1))]
    · rw [←Nat.range_succ_eq_Icc_zero,<-Finset.sum_sub_distrib]
      delta Nat.ceil
      simp_rw [FloorSemiring.ceil]
      norm_num[Int.toNat, Finset.sum,←Nat.prime_iff]
      exact (mul_right_comm _ _ _).trans_lt (((div_lt_iff' (by (norm_num))).mpr (by norm_num[←Real.log_rpow _, Real.log_lt_log])).trans_le.comp (if_pos (by exists(2),by decide, 2)).ge.trans (le_sup_left))
    · exact (fun A B=>by rw [if_neg ((one_lt_div (by norm_num)).2 (Nat.lt_of_ceil_lt (not_lt.1 (B.comp (List.mem_range.2))))).not_le,mul_zero])


#exit

--**Experiment 7**

  revert F fact c₁ c₂ c₁pos c₂pos c₂_lt_one

  apply disproofAxiom

  push_neg

--Alphazero found a disproof
  focus delta ArithmeticFunction.vonMangoldt
  use fun and=>ite (and ≤ 1) (1) 0
  use 1/16, 1/16
  constructor
  · bound
  · constructor
    · hint
    · constructor
      · bound
      · constructor
        · hint
        · use ?_,?_,? _,?_
          · bound
          · use fun and a s c=>if_neg ((one_lt_div (one_pos.trans a)).2 (by linarith)).not_le
          · exact fun and A B R L=>if_pos ((div_le_iff₀ (one_pos.trans A)).2 (by linarith))
          · apply mt (. (3.1))
            rw[tsum_eq_sum (s:=.range (.ceil (3.1: ℝ)+1))]
            · delta Nat.ceil
              simp_rw [FloorSemiring.ceil]
              norm_num+decide[Int.toNat,Finset.sum,div_mul,div_le_iff',le_div_iff',<-Real.log_mul,<-Nat.range_succ_eq_Icc_zero,←Real.log_rpow,Real.log_le_log_iff]
              norm_num[div_div_eq_mul_div,←Real.log_div,div_lt_iff',←Real.log_inv,←Real.log_rpow,lt_abs,Real.log_lt_log]
            · exact (fun A B=>by rw [if_neg ((div_le_one (by norm_num)).not.2 (Nat.lt_of_ceil_lt (not_lt.1 (B.comp (List.mem_range.2)))).not_le),mul_zero])

  sorry

#exit

--**Experiment 6**
  revert F fact c₁ c₂ c₁pos c₂pos c₂_lt_one

  apply disproofAxiom

  push_neg

-- Alphazero found a disproof
  delta ArithmeticFunction.vonMangoldt
  use fun and=>ite (and ≤ 1) (1) 0
  use (1)/16
  use 1 /64,by bound,by bound,by bound,by bound,by bound,fun _ _ _ _=>if_neg ((one_lt_div<|by bound).2<|by bound).not_le
  constructor
  · use fun and A B R L=>if_pos ((div_le_iff₀ (one_pos.trans A)).2 (by linarith))
  · simp_rw [not_forall]
    norm_num
    delta IsPrimePow
    by_contra!
    simp_rw [abs_le] at this
    simp_all only [exists_and_left, neg_le_sub_iff_le_add, tsub_le_iff_right]
    --simp_rw [←Nat.prime_iff] at this
    specialize this (3.1)<|by bound
    rw[tsum_eq_sum (s:=.range 4)]at*
    · rw[show⌊_⌋₊=3by norm_num[Nat.floor_eq_iff]]at*
      norm_num [div_mul_eq_mul_div, Finset.sum_range_succ] at this
      use this.2.not_lt ((add_comm _ _).trans_lt (by norm_num[Exists.intro 3,Exists.intro 1,div_lt_iff',←Real.log_rpow,Real.log_lt_log]))
    · exact fun and μ=>if_neg (μ.comp (List.mem_range.2 ∘ (by exact Nat.cast_lt.1 ∘ ((div_le_one (by norm_num)).1 · |>.trans_lt (by norm_num)))))

  sorry


#exit
--**Experiment 5**

  simp_all
  obtain ⟨c₁, c₁pos, hc₁⟩ := FzeroAfter
  obtain ⟨c₂, c₂pos, c₂_lt_one, hc₂⟩ := Fone

  refine ⟨2 * (c₁ + c₂), by positivity, fun X X_gt_3 ↦ ?_⟩

  revert F fact

  apply disproofAxiom

  push_neg


  -- Alphazero found a disproof
  simp_rw [ArithmeticFunction.vonMangoldt,not_forall]
  simp_rw [abs_le]
  use if. ≤ 1 then(1)else 0
  constructor
  · bound
  · use by bound
    use 1/16
    use by aesop,fun _ _ _ _=>if_neg ((one_lt_div (by bound)).2 (by bound)).not_le,1/36/64,by bound,by simp_all, fun and _ _ _ _=>if_pos (by bound),4.1,by bound
    rw[tsum_eq_sum (s:=.range 5)]
    · norm_num+decide[div_mul_eq_mul_div,le_div_iff',div_le_iff',←Real.log_rpow, (not_false), ( ((4)).floor_eq_iff ↑ _).mpr, (↑Real.log_le_log_iff),(Finset.sum_range_succ )] at *
    · intros
      rw [if_neg]
      · rw [mul_zero]
      · norm_num[div_le_iff, (Nat.cast_le.2 (not_lt.1 (by valid ∘ Finset.mem_range.2))).trans_lt']


  sorry


#exit
--**Experiment 4**


--  rw[div_lt_iff₀ (sub_pos.2 left_1)]at*
--  revert‹ℕ›
  delta ArithmeticFunction.vonMangoldt at*
  norm_num at fact⊢
  refine fun a s=> ⟨a+4,by bound,fun R M=>(abs_sub_le_iff.2) ?_⟩
  by_cases h:Summable fun p : ℕ=>ite (IsPrimePow p) (.log p.minFac*F (p/R)) 0
  · use sub_le_iff_le_add'.2 ((sum_add_tsum_nat_add ⌊R⌋₊ h▸?_)),(sub_le_self _ (tsum_nonneg fun and=>ite_nonneg (mul_nonneg (by positivity) (Fnonneg _)) (by rw []))).trans ?_
    · apply add_le_add (Finset.sum_le_sum fun and k=>if M:_ then (if_pos M)▸if_pos M▸by linear_combination(.log and.minFac*FbddAbove _)else by simp_arith[M])
      trans∑x ∈.range (.floor ((1+w) *R)),.log ↑(x+.floor R)
      · rw[tsum_eq_sum (s:=.range ⌊(1+w) *R⌋₊)]
        · use Finset.sum_le_sum fun and x =>(fact _).trans' (if μ: (_) then (if_pos μ)▸ (if_pos μ)▸mul_le_of_le_one_right ↑( Real.log_natCast_nonneg _) (by apply_rules)else (if_neg μ)▸ (if_neg μ).ge)
        · exact (fun A B=>by rw [right R (by linarith) ( _) ((Nat.lt_of_floor_lt ((not_lt.1 (B.comp (List.mem_range.2))).trans_lt (by norm_num[Nat.floor_pos, M.le.trans',le_add_of_nonneg_of_le]))).le),mul_zero,ite_self])
      · trans∑b ∈.range ⌊(1+w) *R⌋₊,(R.log+R.log)
        · use Finset.sum_le_sum fun and k=>R.log_mul (by bound) (by bound) |>.subst (Real.log_le_log (mod_cast(Nat.floor_pos.2 (by bound)).trans_le le_add_self) ? _)
          exact (Nat.cast_add _ _).trans_le (by nlinarith[mul_pos left_2 (by linarith : R>0),Nat.floor_le (by linarith : R≥0), (and.cast_succ.ge).trans ((Nat.le_floor_iff (by bound)).1 (List.mem_range.1 k))])
        · exact (.trans (by rw [ Finset.sum_const,nsmul_eq_mul, Finset.card_range]) (by nlinarith[ (by bound : R*.log R≥0 ∧w_1 * a*R≥0),Nat.floor_le (by bound:(1+w) *R≥0), R.log_pos (by linarith)]))
    · use (Finset.sum_le_card_nsmul _ _ _ fun and x =>(fact _).trans (?_)).trans (nsmul_eq_mul _ _|>.trans_le (mul_le_mul_of_nonneg_right ?_ (by bound)))
      · cases and with|zero=>field_simp [h, R.log_nonneg (by linarith)]|succ B=>field_simp only [←Nat.le_floor_iff ∘ M.le.trans',le_of_lt (Finset.mem_range.1 _),Real.log_le_log]
      · exact (.trans (by rw [ Finset.card_range]) ((Nat.floor_le (by linarith)).trans (lt_mul_left (by linarith) (by linarith)).le))
  · cases h (summable_of_ne_finset_zero fun and x =>by rw [right R (by linarith) and (Nat.ceil_le.1 (not_lt.1 (x ∘ Finset.mem_range.2))), mul_zero,ite_self])


  sorry
#exit

--**Experiment 3**

  revert F fact

  apply disproofAxiom

  push_neg

  try constructor
  use fun x =>show ite ( x ≤ 1) 1 0 ≤ 1by bound,by bound
  use(? _),? _,fun⟨C,s, a⟩=>?_
  · use(1),one_pos, fun and a s R M A B=>if_neg ((one_lt_div (one_pos.trans M)).2 (B.trans_lt' (by linear_combination R * a))).not_le
  · use 1/2, one_half_pos, one_half_lt_one, fun and A B R L _ _ a=>if_pos ((div_le_iff₀ (one_pos.trans L)).2 (by linear_combination R* A/2+ a))
  · rename_i foo
    clear foo

    clear s

    replace a : ∀p>⌊C⌋₊,ArithmeticFunction.vonMangoldt p=0
    · refine Nat.strongRec fun N R M=>by_contra fun vonManNneZero =>?_
      clear R
      specialize a N
      specialize a <|N.lt_of_floor_lt M


      use((ContinuousAt.continuousWithinAt (by fun_prop)).eventually_lt_const ?_).and (Ioo_mem_nhdsGT one_pos) |>.exists.elim fun ε (A) =>not_le_of_lt A.1 (A.2.elim (a (ε)))

      simp +arith +contextual [div_le_iff₀, M.pos, vonManNneZero, tsum_eq_sum (s := .range (N + 1)),
        Finset.sum_range_succ, Finset.mem_range.1]


      field_simp[le_of_lt, vonManNneZero, Finset.mem_range.1]
    · field_simp[ArithmeticFunction.vonMangoldt] at a
      norm_cast at a
      delta IsPrimePow at*
      use(a _ (Nat.lt_two_pow_self).le ⟨2, _,Nat.prime_two.prime,by valid, rfl⟩).elim (Nat.minFac_pos @_).ne' (by norm_num)


#exit

-- **Experiment 2**

  use (if. ≤ 1 then(1)else(0))
  constructor
  · hint
  · use by aesop
    constructor
    · use(1),one_pos,fun a s R L A B p=>if_neg ((one_lt_div (one_pos.trans A)).2 (by linear_combination L*s+p)).not_le
    · constructor
      · use 1/2, one_half_pos, one_half_lt_one, fun and A B R L a s C=>if_pos ((div_le_iff₀ (one_pos.trans L)).2 (C.trans (by linear_combination A/2*R)))
      · use ?_
        -- · field_simp only [ArithmeticFunction.vonMangoldt]
        --   use fun and=> if a:_ then by simp_all[and.minFac_pos, and.minFac_le a.pos, Real.log_le_log]else (if_neg a).trans_le (by(((positivity))))
        -- · aesop_cat
        -- · use fun and c=>by positivity
        · use fun and x =>(exists_nat_gt and).elim fun and h=>by_contra fun and' =>?_
          replace and':∀R>and,ArithmeticFunction.vonMangoldt R=0
          · use Nat.strongRec fun and a s=>by_contra fun andK=>and' ⟨and,h.trans (mod_cast s),?_⟩
            apply ((ContinuousAt.continuousWithinAt (by fun_prop)).eventually_lt_const _).and (Ioo_mem_nhdsGT one_pos) |>.exists.imp fun and=>and_assoc.1 ∘.symm
            simp +arith +contextual [tsum_eq_sum (s := .range (and + 1)), andK, div_le_iff₀ _, s.pos,
              le_iff_lt_or_eq, Finset.sum_range_succ, Finset.mem_range.1]
          · delta ArithmeticFunction.vonMangoldt at*
            delta IsPrimePow at*
            use((if_pos ⟨2,_,Nat.prime_two.prime, and.succ_pos, rfl⟩).trans_ne) (Real.log_pos (mod_cast(Nat.minFac_prime (by norm_num)).one_lt)).ne' (and' _ (Nat.lt_two_pow_self).le)



  sorry

#exit

-- **Experiment 1**



  -- revert F vonManBnd

  -- apply disproofAxiom

  -- push_neg

  -- by_contra! hg
  -- specialize hg fun and=>ite (and ≤ 1) (1) 0
  -- specialize hg (by bound) (by bound) ..
  -- · use(1),one_pos, fun and a s A B R L=>if_neg (by field_simp[a, L.trans_lt',one_lt_div])
  -- · exact ⟨1, one_pos, fun and A B R L _ _ h=>if_pos ((div_le_iff₀ (one_pos.trans L)).2 (by nlinarith))⟩
  -- · delta ArithmeticFunction.vonMangoldt
  --   exact (fun S=> if a:_ then (if_pos a).trans_le (Real.log_le_log (mod_cast S.minFac_pos) (mod_cast S.minFac_le a.pos))else (if_neg a).trans_le (by positivity))
  -- · use fun R M=>ite_le_one le_rfl one_pos.le
  -- · use fun _ _=>by positivity
  -- · let⟨k,A, B⟩ :=hg
  --   replace B : ∀M>⌊k⌋₊,ArithmeticFunction.vonMangoldt M=0
  --   · use Nat.strongRec fun and R M=>by_contra fun and' =>?_
  --     have:ContinuousAt (k*.*and*.log and) 0 := by fun_prop
  --     apply(((this.eventually_lt_const _).and (gt_mem_nhds one_pos)).exists_gt.elim fun R L=>not_le_of_lt L.2.1 (L.elim (B and (and.lt_of_floor_lt M) R · ·.2)))
  --     simp_arith+contextual [div_le_iff _,← Finset.mem_range_succ_iff,← Finset.mem_range, M.pos, and',tsum_eq_sum (s:=.range (and+1)), Finset.sum_range_succ]
  --   · delta ArithmeticFunction.vonMangoldt at B
  --     norm_num[IsPrimePow]at *
  --     use absurd (B _ (Nat.lt_two_pow_self).le (2) Nat.prime_two.prime _ (by valid) rfl) (mod_cast (by norm_num[Nat.minFac_pos _|>.ne']))

  sorry
