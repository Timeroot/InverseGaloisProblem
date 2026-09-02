/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.FibreInvariant
import InverseGalois.CFT.Brauer.TotallyRealInvariant

/-!
# Comparing the total invariants of a number field and of the rationals

The total invariant of a Brauer class is the product of its invariants at the finite places
together with the product at the infinite ones.  When the invariants at the infinite places are
trivial on both sides, comparing the total invariants of a class of a number field and a class of
the rationals is comparing the products over the finite places alone, and that comparison is made
fibre by fibre over the rational primes.

Consequently a class of a number field whose invariants above each rational prime multiply to the
invariant there of a class of the rationals has the same total invariant as that class, and in
particular has vanishing total invariant as soon as the rational class does.  This is the shape in
which reciprocity over the rationals carries reciprocity over an arbitrary number field.

## Main results

* `InverseGalois.CFT.totalInvariant_eq_of_fibre`: **the total invariant of a class of a number
  field is the total invariant of a class of the rationals** when the invariants at the infinite
  places vanish on both sides and the invariants above each rational prime multiply to the
  invariant there.
* `InverseGalois.CFT.totalInvariant_eq_one_of_fibre`: **the total invariant of such a class
  vanishes** as soon as the total invariant of the rational class does.

## Tags

number field, Brauer group, local invariant, total invariant, reciprocity, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section FibreTotal

variable {k : Type} [Field k] [NumberField k]

/-- **The total invariant of a Brauer class of a number field is the total invariant of a Brauer
class of the rationals** when the invariants at the infinite places vanish on both sides and the
invariants above each rational prime multiply to the invariant there.  Both total invariants are
then products over the finite places, and those agree fibre by fibre. -/
theorem totalInvariant_eq_of_fibre (X : BrauerGroup.{0, 0} k) (Z : BrauerGroup.{0, 0} ℚ)
    (harch : ∀ u : InfinitePlace k, infinitePlaceInvariant k u X = 1)
    (harchQ : ∀ u : InfinitePlace ℚ, infinitePlaceInvariant ℚ u Z = 1)
    (hfib : ∀ P : HeightOneSpectrum (𝓞 ℚ),
      ∏ᶠ v : HeightOneSpectrum (𝓞 k),
          Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v
        = placeInvariant ℚ P Z) :
    totalInvariant k X = totalInvariant ℚ Z := by
  rw [totalInvariant_eq_finprod k X harch, totalInvariant_eq_finprod ℚ Z harchQ,
    finprod_placeInvariant_eq_of_fibre X Z hfib]

/-- **The total invariant of a Brauer class of a number field vanishes** when the invariants at the
infinite places vanish on both sides, the invariants above each rational prime multiply to the
invariant there of a class of the rationals, and the total invariant of that class vanishes. -/
theorem totalInvariant_eq_one_of_fibre (X : BrauerGroup.{0, 0} k) (Z : BrauerGroup.{0, 0} ℚ)
    (harch : ∀ u : InfinitePlace k, infinitePlaceInvariant k u X = 1)
    (harchQ : ∀ u : InfinitePlace ℚ, infinitePlaceInvariant ℚ u Z = 1)
    (hfib : ∀ P : HeightOneSpectrum (𝓞 ℚ),
      ∏ᶠ v : HeightOneSpectrum (𝓞 k),
          Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v
        = placeInvariant ℚ P Z)
    (hZ : totalInvariant ℚ Z = 1) :
    totalInvariant k X = 1 := by
  rw [totalInvariant_eq_of_fibre X Z harch harchQ hfib, hZ]

end FibreTotal

end InverseGalois.CFT
