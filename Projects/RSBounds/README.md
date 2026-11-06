# Explicit Rosser–Schoenfeld estimates: work in progress

This isolated Lean 4.35 project develops proofs toward the moderate-error
`b = 23` psi table entry (finite RH through `1894439`), an explicit theta
`x/log x` bound, and the classical RS62 weighted-prime-sum and totient bounds.
It pins `calr3/ternary-goldbach` at commit
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`.

**The four requested estimates are not yet proved in this package.**

The previous workspace was reset before its files were uploaded. Sources are
being reconstructed from the recorded work and checked afresh. Historical
reports of successful checks are not verification of the reconstructed files.
New verification results will be recorded in `verification/`.

The main completed result before the reset was the exact RS62 totient bound
for integers with at most twenty distinct prime factors, hence for
`3 <= q <= 10^27`. The unrestricted totient estimate was not proved.
Supporting work included finite-anchor Abel identities and weighted
zero-sum partial summation. The sharp Rosser zero-count estimate itself,
the finite low-zero certificates, and the `b = 23` psi conclusion remain open.

The needed historical zero-count bound is Rosser (1941), Theorem 19, p. 223:

`abs (N(T)-F(T)) < .137 log(T) + .443 log(log(T)) + 1.588`, for `T >= 2`,

where `F(T) = T/(2*pi)*log(T/(2*pi)) - T/(2*pi) + 7/8`. Rosser cites
Backlund's argument. RS75 Lemma 7 transfers this to weighted zero sums.
The older `b = 23` table entry is `0.00020211`; Schoenfeld's 1976
improvement is `0.00020171` and uses a larger finite low-zero computation.

Sources:

- [Rosser (1941), Theorem 19](https://doi.org/10.2307/2371291).
- [Backlund, Acta Mathematica 41, pp. 345–375](https://doi.org/10.1007/BF02422950).
- [Rosser–Schoenfeld (1975)](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
- [Schoenfeld (1976)](https://doi.org/10.1090/S0025-5718-1976-0457374-9).
- [Rosser–Schoenfeld (1962)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).

Run commands from this subdirectory, using its own toolchain rather than the
parent repository's toolchain. The package is separate from the parent project.
