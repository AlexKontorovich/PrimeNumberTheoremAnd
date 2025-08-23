import PrimeNumberTheoremAnd.ZetaBounds

open Complex Filter Set
local notation (name := riemannzeta2) "ζ" => riemannZeta
local notation (name := derivriemannzeta2) "ζ'" => deriv riemannZeta

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
  convert h σ t (by linarith [mem_Ici.mp t_ge]) ⟨ht.le, (by bound)⟩
  simp only [mem_setOf_eq] at t_ge
  have := Real.log_nonneg (by linarith : 1 ≤ |t|)
  simp only [Real.norm_eq_abs, norm_pow, abs_eq_self.mpr, this]
/-%%
\begin{proof}\leanok
\uses{LogDerivZetaBnd}
Same as above.
\end{proof}
%%-/
