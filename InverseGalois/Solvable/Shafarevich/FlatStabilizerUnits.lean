/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedEquivariant
import InverseGalois.Solvable.Shafarevich.FlatDiagonalUnits

/-!
# The obstruction, bought with one unit per place with a decomposition group

The demand made of a choice of places has two halves: a diagonal of units at the chosen places,
which the arithmetic input of the prescription already supplies, and the vanishing of the
obstruction to correcting an invariant divisor of confined units to an invariant radicand.  This
file buys the second half against arithmetic of the same shape as the first.

What it costs is one confined unit for each place of the hull of the named ones: a unit of order
one at that place and none at the other places of the hull, each read up to a multiple of the
exponent, and fixed by the automorphisms fixing the place.  The vector of orders is equivariant, so
such a unit carries with it the unit belonging to every place of the same orbit, and the family so
assembled splits the vector of orders equivariantly, which trivialises the obstruction of every
tensor with invariant valuation.

The cost is nil at a place no automorphism but the identity fixes.  There the vector of orders
being onto already supplies a unit of order one at the place and none at the others, and being
fixed by the automorphisms fixing the place asks nothing of it.  So what is bought here is a unit
in the decomposition field of each place of the hull carrying a decomposition group, and nothing at
all at the places completely decomposed in the level.

## Main definitions

* `InverseGalois.Shafarevich.HasStabilizerConfinedUnits`: the units the obstruction is bought
  with, asked for only at the places some automorphism other than the identity fixes.
* `Shafarevich.StabilizerConfinedUnitsEP`: the same, made of every level.

## Main results

* `InverseGalois.Shafarevich.hasConfinedObstruction_of_hasStabilizerConfinedUnits`: **the units buy
  the obstruction.**
* `Shafarevich.genericLevelStepEPRoots_of_stabilizerConfinedUnitsEP`: the step of the ladder over
  an odd prime, in exchange for the diagonal, the units of the obstruction and a level reaching
  every place.

## Tags

Shafarevich's theorem, embedding problem, S-unit, confined unit, decomposition group, obstruction
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain MulAction NumberField

set_option synthInstance.maxHeartbeats 800000

/-! ### The units the obstruction is bought with -/

section Units

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **The units the obstruction is bought with.**

At each place of the hull of the named ones which some automorphism other than the identity fixes,
a confined unit of order one at that place and none at the other places of the hull, each up to a
multiple of the exponent, fixed by the automorphisms fixing the place.  Nothing is asked at the
places with no decomposition group. -/
def HasStabilizerConfinedUnits (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ Xs₀ Tz : Set (HeightOneSpectrum (𝓞 ↥K)), Xs₀.Finite → Tz.Finite →
      ∀ (_ : Finite ↥(stableHull k ↥K Xs₀)) (y : ↥(stableHull k ↥K Xs₀)),
        (∃ σ : Gal(↥K/k), σ ≠ 1 ∧ σ • y = y) →
        ∃ u : ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)),
          (∀ z : ↥(stableHull k ↥K Xs₀), (ℓ : ℤ) ∣
            confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀)
              (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
            ∀ σ : Gal(↥K/k), σ • y = y → σ • u = u

/-- **The units buy the obstruction.**

The vector of orders of a confined unit is equivariant, so the units asked for assemble into a
splitting of it carried by the action, and such a splitting trivialises the obstruction of every
tensor whose valuation is invariant.  The splitting is read after tensoring with a module killed by
the exponent, which is why the orders are only asked for up to a multiple of it. -/
theorem hasConfinedObstruction_of_hasStabilizerConfinedUnits {ℓ : ℕ}
    {K : IntermediateField k Ω} [NumberField ↥K] (h : HasStabilizerConfinedUnits ℓ K) :
    HasConfinedObstruction ℓ K := by
  intro E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz C _ _ hexp hfin hdec hsurj t ht
  haveI : Finite ↥(stableHull k ↥K Xs₀) := hfin
  letI : DecidableEq ↥(stableHull k ↥K Xs₀) := hdec
  exact tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_nontrivial ℓ
    (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀) hexp hsurj
    (h E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz hfin) ht

end Units

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

/-! ### The units, made of every level -/

/-- **Every finite Galois level of a number field inside an algebraic closure carrying a primitive
root of unity of the exponent carries the units the obstruction is bought with.** -/
def StabilizerConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
      (∃ ζ : ↥K, IsPrimitiveRoot ζ ℓ) → HasStabilizerConfinedUnits ℓ K

/-- **The units buy the obstruction, at every level.** -/
theorem confinedObstructionEP_of_stabilizerConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : StabilizerConfinedUnitsEP ℓ) : ConfinedObstructionEP ℓ := by
  intro k Ω _ _ _ _ _ _ K _ _ _ hζ
  exact hasConfinedObstruction_of_hasStabilizerConfinedUnits (h k Ω K hζ)

/-- **The step of the ladder over an odd prime**, in exchange for the diagonal, the units the
obstruction is bought with and a level reaching every place. -/
theorem genericLevelStepEPRoots_of_stabilizerConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hreach : FlatReachableEP ℓ) (hunits : FlatDiagonalUnitsEP ℓ)
    (hstab : StabilizerConfinedUnitsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_flatDiagonalUnitsEP ℓ hodd hreach hunits
    (confinedObstructionEP_of_stabilizerConfinedUnitsEP ℓ hstab)

end Shafarevich
