# Independent totient statements

`RSTotientChallenge.lean` imports only Mathlib and specifies the two propositions
to be checked. Its deliberate `by sorry` theorem stubs specify the challenge;
they are not imported by the solution. The solution may not use `sorryAx`.
`RSTotientSolution.lean` imports the actual proofs.

Run `lake comparator` from the package directory. It checks statement and
definition matching, the allowed axioms, and the exported proof with Lean's
kernel. `--paranoid` adds optional independent kernels and may require much
larger computation limits for the finite arithmetic certificate.

Actual runs and their limitations are documented in `../verification/`.
The Comparator covers these two restricted totient results only, not the
unfinished psi/theta/Mertens goals.
