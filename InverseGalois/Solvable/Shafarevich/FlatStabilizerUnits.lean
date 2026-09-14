/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ModPowEquivariant
import InverseGalois.Solvable.Shafarevich.FlatDiagonalUnits

/-!
# The obstruction, bought with one unit per place with a decomposition group

The demand made of a choice of places has two halves: a diagonal of units at the chosen places,
which the arithmetic input of the prescription already supplies, and the vanishing of the
obstruction to correcting an invariant divisor of confined units to an invariant radicand.  This
file buys the second half against arithmetic of the same shape as the first.

What it costs is one confined unit for each place of the hull of the named ones: a unit of order
one at that place and none at the other places of the hull, each read up to a multiple of the
exponent, and whose class modulo exponent-th powers the automorphisms fixing the place fix.  The
vector of orders is equivariant, so such a unit carries with it the unit belonging to every place of
the same orbit, up to exponent-th powers, and the family so assembled splits the vector of orders
equivariantly after tensoring with a module the exponent kills, which trivialises the obstruction of
every tensor with invariant valuation.

Only the class modulo exponent-th powers is asked to be fixed, because that is all the obstruction
reads: the splitting is spent against a module killed by the exponent, where an exponent-th power
contributes nothing.  The room this leaves over a unit fixed on the nose is exactly the room a
decomposition group leaves by Hilbert's theorem 90, and it is what makes the demand meetable.

The cost is nil at a place no automorphism of order the exponent fixes.  There the decomposition
group has order prime to the exponent, and the product over it of a unit of order one at the place
and none at the others — which the vector of orders being onto already supplies — is fixed by the
automorphisms fixing the place and has order the size of that group there, which a power brings
back to one modulo the exponent.  So what is bought here is a unit at each place of the hull whose
decomposition group has order divisible by the exponent, and nothing at all at the other places.

## Main definitions

* `InverseGalois.Shafarevich.HasStabilizerConfinedUnits`: the units the obstruction is bought
  with, asked for only at the places some automorphism of order the exponent fixes, and asked to be
  fixed there only modulo exponent-th powers.
* `Shafarevich.StabilizerConfinedUnitsEP`: the same, made of every level.

## Main results

* `InverseGalois.Shafarevich.hasConfinedObstruction_of_hasStabilizerConfinedUnits`: **the units buy
  the obstruction.**
* `Shafarevich.genericLevelStepEPRoots_of_stabilizerConfinedUnitsEP`: the step of the ladder over
  an odd prime, in exchange for the units of the obstruction alone.

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

At each place of the hull of the named ones which some automorphism of order the exponent fixes, a
confined unit of order one at that place and none at the other places of the hull, each up to a
multiple of the exponent, whose class modulo exponent-th powers the automorphisms fixing the place
fix.  Nothing is asked at the places whose decomposition group has order prime to the exponent. -/
def HasStabilizerConfinedUnits (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ Xs₀ Tz : Set (HeightOneSpectrum (𝓞 ↥K)), Xs₀.Finite → Tz.Finite →
      ∀ (_ : Finite ↥(stableHull k ↥K Xs₀)) (y : ↥(stableHull k ↥K Xs₀)),
        (∃ σ : Gal(↥K/k), σ ≠ 1 ∧ σ ^ ℓ = 1 ∧ σ • y = y) →
        ∃ u : ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)),
          (∀ z : ↥(stableHull k ↥K Xs₀), (ℓ : ℤ) ∣
            confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀)
              (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
            ∀ σ : Gal(↥K/k), σ • y = y →
              ∃ v : ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)),
                σ • u = u * v ^ ℓ

/-- **The units buy the obstruction.**

The vector of orders of a confined unit is equivariant, so the units asked for assemble into a
splitting of it carried by the action up to exponent-th powers, and such a splitting trivialises the
obstruction of every tensor whose valuation is invariant.  The splitting is read after tensoring
with a module killed by the exponent, which is why the orders are only asked for up to a multiple of
it and the class modulo exponent-th powers is all that has to be fixed.  Where no automorphism of
order the exponent fixes the place, the product over the decomposition group supplies the unit
unasked. -/
theorem hasConfinedObstruction_of_hasStabilizerConfinedUnits {ℓ : ℕ} [Fact ℓ.Prime]
    {K : IntermediateField k Ω} [NumberField ↥K] [FiniteDimensional k ↥K]
    (h : HasStabilizerConfinedUnits ℓ K) :
    HasConfinedObstruction ℓ K := by
  intro E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz C _ _ hexp hfin hdec hsurj t ht
  haveI : Finite ↥(stableHull k ↥K Xs₀) := hfin
  letI : DecidableEq ↥(stableHull k ↥K Xs₀) := hdec
  exact tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_pow_order ℓ
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

/-- **The step of the ladder over an odd prime**, in exchange for the units the obstruction is
bought with and nothing else. -/
theorem genericLevelStepEPRoots_of_stabilizerConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hstab : StabilizerConfinedUnitsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_confinedObstructionEP ℓ hodd
    (confinedObstructionEP_of_stabilizerConfinedUnitsEP ℓ hstab)

end Shafarevich
