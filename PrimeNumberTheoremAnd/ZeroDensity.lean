module

public import PrimeNumberTheoremAnd.ZeroDensity.MeanValue
public import PrimeNumberTheoremAnd.ZeroDensity.Dirichlet
public import PrimeNumberTheoremAnd.ZeroDensity.GaussMV
public import PrimeNumberTheoremAnd.ZeroDensity.MeanSquare
public import PrimeNumberTheoremAnd.ZeroDensity.Tail
public import PrimeNumberTheoremAnd.ZeroDensity.BohrLandau
public import PrimeNumberTheoremAnd.ZeroDensity.Uniform
public import PrimeNumberTheoremAnd.ZeroDensity.Jensen
public import PrimeNumberTheoremAnd.ZeroDensity.Unconditional

/-!
# Zero-density estimates for the Riemann zeta function

Authors: Devon Wright (formalized with Grok Bot).

Contents so far: mean value theorems for Dirichlet polynomials, mean squares of zeta, Jensen disc
counting and the Bohr-Landau theorem N(sigma,T) = O(T) for sigma > 1/2.

`ZeroDensity.Bridge` and `ZeroDensity.ZDB` (identification with `riemannZeta.N'` and a proved
`zero_density_bound` instance) import `IEANTN.ZetaDefinitions` and are kept out of this aggregator;
they are intended for `teorth/IEANTN`.
-/
