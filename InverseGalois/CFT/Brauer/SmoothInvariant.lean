/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InvariantSurjective
import InverseGalois.CFT.Brauer.SmoothBrauer

/-!
# The second cohomology of the absolute Galois group of a local field

The Brauer group of a local field is the rationals modulo the integers, and the Brauer group of a
perfect field is the smooth second cohomology of its absolute Galois group with coefficients in
the units of an algebraic closure.  Composing the two identifies that cohomology group with the
rationals modulo the integers.  This is the invariant map of local class field theory in its
cohomological form, the one that pairs with the cup product to give the norm residue symbol.

## Main results

* `InverseGalois.CFT.smoothLocalInvariantEquiv`: **the smooth second cohomology of the absolute
  Galois group of a local field with coefficients in the units of an algebraic closure is the
  rationals modulo the integers.**

## Tags

Brauer group, local field, invariant map, Galois cohomology, class field theory
-/

namespace InverseGalois.CFT

open scoped Valued WithZero

section Local

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ}

variable (K) in
/-- **The smooth second cohomology of the absolute Galois group of a local field with coefficients
in the units of an algebraic closure is the rationals modulo the integers.**  A cohomology class
is the class of a crossed product of a finite Galois level, and its Brauer class determines and is
determined by its invariant. -/
noncomputable def smoothLocalInvariantEquiv (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) :
    SmoothH2 Gal(AlgebraicClosure K/K) (AlgebraicClosure K)ˣ ≃* Multiplicative QModZ :=
  (smoothBrauerEquiv K).trans (localInvariantEquiv K hres hm)

@[simp]
theorem smoothLocalInvariantEquiv_apply (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (z : SmoothH2 Gal(AlgebraicClosure K/K) (AlgebraicClosure K)ˣ) :
    smoothLocalInvariantEquiv K hres hm z = localInvariantHom K hm (smoothBrauer z) := rfl

end Local

end InverseGalois.CFT
