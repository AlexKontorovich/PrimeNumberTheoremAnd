# Reciprocal-square tails of actual zeta zeros

`RSBounds/RosserSquareTail.lean` proves, unconditionally, for `7 ≤ a ≤ b`,

\[
\sum_{a<\gamma\le b}\frac{m_\gamma}{\gamma^2}
\le \frac{\log(a/(2\pi))+1}{2\pi a}
 +\frac{0.137+0.443/\log a}{2a^2}
 +\frac{2R(a)}{a^2},
\]

where `R(a)=0.137 log a+0.443 log log a+1.588`. The sum uses the existing actual
positive zeta zeros and their analytic multiplicities. The lower endpoint is
excluded and the upper endpoint included. A sharper intermediate theorem
retains the actual count correction at the lower endpoint.

The input is the already proved Rosser count estimate and its partial-summation
interface. There is no RH, zero-free-region, or PNT assumption. The integral is
computed from the explicit primitive `(log(t/(2π))+1)/(2πt)+c/(2t²)`.

Seven exports passed a fresh-source, in-process transitive axiom audit. All use
only `propext`, `Classical.choice`, and `Quot.sound`. Receipt:
`verification/rosser-square-tail-run.json`. Reproduce from the recovery root by
sourcing `../lean-env.sh` and running
`python verification/run_rosser_square_tail_check.py`.

The current receipt records a direct Lean invocation. Interrupted launcher
attempts are retained separately and are not successful verification receipts.
The runner's final console sentence retains an older “cube” label; the checked
source, declaration names, audit commands, and receipt all refer to square
weights.

Source SHA-256: `2e464311aaebb537cd18775190d6261fa68d397667ad32b74d3c648a01e1731c`.

Source method: Rosser (1941), Theorems 17–18, and partial summation as in
Rosser–Schoenfeld (1975), Section 3. The formula above is the direct weight
`t⁻²` specialization of that method.
