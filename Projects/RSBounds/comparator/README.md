# Independent totient statements

`RSTotientChallenge.lean` imports only Mathlib and declares the two propositions
to be checked. Its `axiom` declarations specify the challenge; they are not
imported by the solution and are not permitted as assumptions of a proof.
`RSTotientSolution.lean` imports the actual proofs.

Run `lake comparator` from the package directory. It checks statement and
definition matching, the allowed axioms, and the exported proof with Lean's
kernel. `--paranoid` adds optional independent kernels and may require much
larger computation limits for the finite arithmetic certificate.

Actual runs and their limitations are documented in `../verification/`.
The Comparator covers these two restricted totient results only, not the
unfinished psi/theta/Mertens goals.
