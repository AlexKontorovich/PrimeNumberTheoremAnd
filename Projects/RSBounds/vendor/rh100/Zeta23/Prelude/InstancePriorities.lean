module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Prelude/InstancePriorities.lean — instance-search hygiene shared by the RvM / PNT⁺ layer.

THE PROBLEM (diagnosed with `set_option trace.Meta.synthInstance true`): once
`Mathlib.Algebra.Lie.OfAssociative` is in scope together with the RCLike normed-algebra instances (as happens in
the import closure of Zeta23.RvM.LocalCount / ReZeroCount / Unconditional), the goal `Module ℝ ℂ` that arises
while resolving `IsBoundedSMul ℝ ℂ` is answered first by
  LieAlgebra.toModule ← LieAlgebra.ofAssociativeAlgebra ← RCLike.toNormedAlgebra,
and that `Module ℝ ℂ` term is not definitionally equal, at instance transparency, to the one carried by
`NormedSpace ℝ ℂ` (InnerProductSpace path).  Consequently `NormedSpace.toIsBoundedSMul` and
`NormedSpace.toNormSMulClass` fail to unify, `ContinuousSMul ℝ ℂ` cannot be synthesized, and every statement of
the form `HasDerivAt (f : ℝ → ℂ) _ _` fails to elaborate downstream (deterministically — not a timeout).
A file-local workaround is `attribute [-instance] LieAlgebra.ofAssociativeAlgebra`.

THE FIX: demote `LieAlgebra.toModule` to low priority, so `Complex.instModule` / the NormedSpace path is tried
first.  This is an instance-search-order change only: no definition or theorem statement changes, the Lie
instance remains available, and the re-prioritisation persists to every importer of this file (a
module importing this + Zeta23.RvM.LocalCount, in either order, elaborates the HasDerivAt probe that fails without
it).  Imported by Zeta23/RvM/LocalCount.lean, Zeta23/RvM/BacklundDefs.lean and Zeta23/FromPNTPlus/StrongPNTPrefix.lean.
If a future Mathlib demotes/removes `LieAlgebra.ofAssociativeAlgebra` as a global instance, this file can be
deleted.
-/
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

attribute [instance 10] LieAlgebra.toModule
