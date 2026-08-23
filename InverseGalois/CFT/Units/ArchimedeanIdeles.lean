/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.InfinitePlaces
import InverseGalois.CFT.Tate.OrbitIndex
import InverseGalois.CFT.Units.InfiniteOrbit

/-!
# The archimedean part of the ideles

The units of the completions of a number field at all of its infinite places form a family of
modules over the Galois group, and the sections of that family are the archimedean part of the group
of ideles.  The index set breaks into the orbits of the Galois group, one for each infinite place of
the base field, and the factor over an orbit has Herbrand quotient the order of the decomposition
group of a place in it.

The Herbrand quotient of the archimedean part is therefore the product over the infinite places of
the base field of the orders of the decomposition groups above them.  That is exactly the Herbrand
quotient of the free lattice on the infinite places of the extension, which is the shape of the unit
lattice: the archimedean part of the ideles and the units of the ring of integers contribute the
same factor, and in the Herbrand quotient of the idele class group they cancel.

## Main results

* `InverseGalois.CFT.herbrand_infiniteUnitsFamily`: **the archimedean part of the ideles has
  Herbrand quotient the product of the orders of the decomposition groups** at the infinite places
  of the base field.
* `InverseGalois.CFT.herbrand_infiniteUnitsFamily_eq_permLattice`: the archimedean part of the
  ideles and the free lattice on the infinite places have the same Herbrand quotient.

## Tags

number field, idele, infinite place, decomposition group, Herbrand quotient
-/

namespace InverseGalois.CFT

open MulAction NumberField

section ArchimedeanIdeles

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **The archimedean part of the ideles has Herbrand quotient the product of the orders of the
decomposition groups** at the infinite places of the base field.  The infinite places of the
extension break into one orbit of the Galois group above each infinite place of the base field, and
the factor over an orbit is the module induced from a decomposition group. -/
theorem herbrand_infiniteUnitsFamily {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)
    {n : ℕ} (hn : Nat.card Gal(K/k) = n) :
    herbrand ((infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ) n
      = ∏ v : InfinitePlace k, (Nat.card ↥(stabilizer Gal(K/k) (placeAbove k K v)) : ℚ) := by
  haveI : Module.Finite k K := Module.Finite.of_restrictScalars_finite ℚ k K
  haveI : Fintype (orbitRel.Quotient Gal(K/k) (InfinitePlace K)) := Fintype.ofFinite _
  rw [herbrand_familyAut_orbits (infiniteRingFamily (k := k) (K := K)).unitsFamily n]
  rw [Finset.prod_congr rfl fun ω _ => show
      herbrand ((orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily ω).familyAut σ) n
        = (Nat.card ↥(stabilizer Gal(K/k) (Quotient.out ω)) : ℚ) by
    haveI : Fintype ω.orbit := Fintype.ofFinite _
    exact herbrand_orbitFamily_infiniteUnits (orbitOut ω) hgen hn]
  exact prod_card_stabilizer_orbits_eq_of_fibers comap_smul_infinitePlace (comap_placeAbove k K)
    exists_smul_placeAbove_eq

/-- The archimedean part of the ideles and the free lattice on the infinite places of the extension
have the same Herbrand quotient. -/
theorem herbrand_infiniteUnitsFamily_eq_permLattice {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Nat.card Gal(K/k) = n) :
    herbrand ((infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ) n
      = herbrand (permLatticeAut (toPerm σ : Equiv.Perm (InfinitePlace K))) n := by
  rw [herbrand_infiniteUnitsFamily hgen hn, herbrand_permLatticeAut_infinitePlace hgen hn]

end ArchimedeanIdeles

end InverseGalois.CFT
