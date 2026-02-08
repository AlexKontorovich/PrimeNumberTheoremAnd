import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.eSHP_tables

blueprint_comment /--
\section{Prime gap data from eSHP}

Numerical results on prime gaps from \cite{eSHP}.

-/

namespace eSHP

@[blueprint
  "table-8-prime-gap-test"
  (title := "Table 8 prime gap record - unit test")
  (statement := /--
  For every pair $(p_k,g_k)$ in Table 8 with $p_k < 30$, $g_k$ is the prime gap $p_{k+1} - p_k$, and all prime gaps preceding this gap are less than $g_k$. -/)
  (proof := /-- Direct computation. -/)
  (latexEnv := "proposition")]
theorem table_8_prime_gap_test (p g : ℕ) (h : (p, g) ∈ table_8) (htest : p < 30) : prime_gap_record p g := by
  sorry

@[blueprint
  "table-8-prime-gap"
  (title := "Table 8 prime gap records")
  (statement := /--
  For every pair $(p_k,g_k)$ in Table 8, $g_k$ is the prime gap $p_{k+1} - p_k$, and all prime gaps preceding this gap are less than $g_k$. -/)
  (proof := /-- Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table. -/)
  (latexEnv := "proposition")]
theorem table_8_prime_gap (p g : ℕ) (h : (p, g) ∈ table_8) : prime_gap_record p g := by
  sorry

@[blueprint
  "table-9-prime-gap"
  (title := "Table 9 prime gaps - unit test")
  (statement := /--
  For every pair $(g,P)$ in Table 9 with $P < 30$, $P$ is the first prime producing the prime gap $g$, and all smaller $g'$ (that are even or $1$) have a smaller first prime. -/)
  (proof := /-- Direct computation. -/)
  (latexEnv := "proposition")]
theorem table_9_prime_gap_test (g P : ℕ) (h : (g, P) ∈ table_9) (htest : P < 30) : first_gap_record g P := by
  sorry

@[blueprint
  "table-9-prime-gap"
  (title := "Table 9 prime gaps")
  (statement := /--
  For every pair $(g,P)$ in Table 9, $P$ is the first prime producing the prime gap $g$, and all smaller $g'$ (that are even or $1$) have a smaller first prime. -/)
  (proof := /-- Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table. -/)
  (latexEnv := "proposition")]
theorem table_9_prime_gap (g P : ℕ) (h : (g, P) ∈ table_9) : first_gap_record g P := by
  sorry


end eSHP
