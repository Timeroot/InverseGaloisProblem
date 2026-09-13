/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.FlatPlaces
import InverseGalois.Solvable.Shafarevich.KernelStep
import InverseGalois.Solvable.Shafarevich.NamedOrthogonal

/-!
# The flattening in exchange for units alone

The flat prescription made one named prime at a time is assembled out of a single unit of the level
the base realization cuts out at each named place.  This file spends that assembly exactly as the
sharp one is spent: a base realization over the rationals cuts out a finite Galois level, the roots
of unity of order the prime lie in it because the realization is asked to fix those of order its
square, the finite family the local conditions are read on names a family of primes, and the places
of the level below those primes are the places the units are prescribed at.

What makes the flat side cheaper than the sharp one is that nothing is named at a named place but a
single unit, so the arithmetic is asked for units and not for classes in each coordinate and no
pairing between the named classes is left over.  What reciprocity still has to say is said about the
divisor of the unit, and it is said against the level the confinement is read in rather than against
the arithmetic: the places completely decomposed in that level generate the divisor classes the
level leaves free, and a place whose class is not among them carries no unit of the shape asked
for.  So the demand splits in two, the units on one side and a level reaching every place on the
other, and it is the shrinking which pays for the second.

The kernel of the base realization need not be assumed open here.  The prescription is asked for a
lift which is smooth and lies over the base realization, and the kernel of such a lift is open and
sits inside the kernel of the base realization, so openness comes for free with the data the
prescription is handed.

## Main definitions

* `Shafarevich.FlatUnitsEP` — **every finite Galois level of the rationals carries the units the
  flat prescription is assembled out of.**
* `Shafarevich.FlatReachableEP` — **the shrinking the flattening spends can be spent on a level
  reaching every place.**

## Main results

* `Shafarevich.flatOrbitPrescriptionEP_of_flatUnitsEP` — **the units buy the flattening made one
  field up and one named prime at a time.**
* `Shafarevich.flatPrescriptionEP_of_flatUnitsEP` — **the units buy the flattening.**
* `Shafarevich.genericLevelStepEPRoots_of_flatUnitsEP` — **the step of the ladder over an odd
  prime, in exchange for the units and a level reaching every place.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, decomposition group, local class
-/

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich IsDedekindDomain MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

attribute [local instance] zmodTrivialAction

/-! ### The arithmetic, asked of every level -/

/-- **Every finite Galois level of the rationals carries the units the flat prescription is
assembled out of.**

The demand is the one the assembly of the flat prescription makes, asked of every finite Galois
level of the rationals inside an algebraic closure: finitely many places lying in distinct orbits
are named, and a unit is asked for at each, fixed up to an exponent-th power by the automorphisms
fixing its place, of order there prime to the exponent, a local power at a prescribed finite set of
places and at the conjugates of the named places other than its own, and confined elsewhere to
places sitting over the named ones or completely decomposed in a finite level given in advance. -/
def FlatUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
    HasFlatPrescribedUnits ℓ K

/-- **The shrinking the flattening spends can be spent on a level reaching every place.**

The demand is the one the level the confinement is read in has to meet, asked of the level any base
realization over the rationals cuts out: a number of letters is announced, and for every surjective
smooth lift at that number lying over the base realization a shrinking onto the number asked for is
produced together with a finite level killing the lift carried across it in which every place of the
level below is reached.

This is the half of the demand the arithmetic cannot answer.  Which classes the confinement leaves
free is decided by the level, the completely decomposed places generating exactly the classes the
level does not see, so a place whose class the level does see carries no unit of the shape the
prescription asks for however the arithmetic is arranged. -/
def FlatReachableEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (S U : Type) [Group S] [Group U] (φ : Gal(Ω/k) →* U) (n j : ℕ)
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
    K.fixingSubgroup = φ.ker → ∃ N : ℕ, HasReachableLevel ℓ U n S j φ N K

/-! ### The prescription and the step -/

/-- **The units buy the flattening made one field up and one named prime at a time.**

The level is the one the kernel of the base realization cuts out, finite and Galois over the
rationals because the kernel is open and normal, and the root of unity of order the prime lies in it
because the base realization fixes the roots of unity of order its square.  The closure being
algebraically closed, every unit of the level has an exponent-th root there, which is what makes the
level and its closure Kummer data.  The places the units are prescribed at are read off the finite
family of primes, and the places above the prime are covered because the primes above it are.

Openness of the kernel is not assumed: the prescription is handed a smooth lift lying over the base
realization, whose kernel is open and lies inside it, so where the kernel is not open there is
nothing to prescribe for. -/
theorem flatOrbitPrescriptionEP_of_flatUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hreach : FlatReachableEP ℓ) (h : FlatUnitsEP ℓ) : FlatOrbitPrescriptionEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  obtain ⟨Pr, hPrp, hPrbot, hDPr, hcovP, -⟩ := hcov
  by_cases hopen : IsOpen (φ.ker : Set Gal(Ω/ℚ))
  · haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
    have hℓ : ℓ.Prime := Fact.out
    obtain ⟨K, hfin, hgal, hKker, hKmem⟩ :=
      exists_level_fixingSubgroup_eq (N := φ.ker) ⟨inferInstance, hopen⟩
    haveI := hfin
    haveI := hgal
    haveI : NumberField ↥K := numberField_of_finiteDimensional K
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_of_isAlgClosure ℚ Ω ℓ
    have hz0 : z ≠ 0 := hz.ne_zero hℓ.ne_zero
    have hzsq : (Units.mk0 z hz0) ^ (ℓ * ℓ * Monoid.exponent S) = 1 := by
      refine Units.ext ?_
      show z ^ (ℓ * ℓ * Monoid.exponent S) = 1
      rw [pow_mul, pow_mul, hz.pow_eq_one, one_pow, one_pow]
    have hzK : z ∈ K := by
      refine hKmem z fun σ hσ => ?_
      exact congrArg Units.val (hmu (Units.mk0 z hz0) hzsq σ hσ)
    have hζ : IsPrimitiveRoot (⟨z, hzK⟩ : ↥K) ℓ :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) hz (algebraMap ↥K Ω).injective
    have hroot : ∀ x : (↥K)ˣ, ∃ β : Ωˣ, β ^ ℓ = Units.map (algebraMap ↥K Ω : ↥K →* Ω) x := by
      intro x
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Ω (x : ↥K)) hℓ.pos
      have hy0 : y ≠ 0 := by
        intro h0
        rw [h0, zero_pow hℓ.ne_zero] at hy
        exact (map_ne_zero_iff _ (algebraMap ↥K Ω).injective).2 x.ne_zero hy.symm
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val, Units.coe_map]
      exact hy
    have hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ :=
      isKummerData_zmod hζ hroot
    obtain ⟨N, hlevel⟩ := hreach ℚ Ω S U φ n j K hKker
    exact hasFlatOrbitPrescription_of_places N K hKker hζ hkd hPrp hPrbot hDPr
      (exists_smul_placeUnder_of_mem K hPrp hPrbot hcovP) hlevel (h ℚ Ω K)
  · refine ⟨0, ?_⟩
    intro F ι _ Q A a hFsurj hFsm hFright
    refine absurd (Subgroup.isOpen_mono ?_ (isOpenNormal_ker_of_isSmoothHom hFsm).isOpen) hopen
    intro x hx
    refine MonoidHom.mem_ker.2 ?_
    rw [← hFright x, MonoidHom.mem_ker.1 hx, _root_.map_one]

/-- **The units buy the flattening**, the shrinking being spent on a level reaching every place. -/
theorem flatPrescriptionEP_of_flatUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hreach : FlatReachableEP ℓ) (h : FlatUnitsEP ℓ) : FlatPrescriptionEP ℓ :=
  flatPrescriptionEP_of_flatOrbitPrescriptionEP ℓ
    (flatOrbitPrescriptionEP_of_flatUnitsEP ℓ hreach h)

/-- **The step of the ladder, in exchange for the units and a level reaching every place** — the two
pieces the whole climb over an odd prime rests on, one arithmetic and one about the levels. -/
theorem genericLevelStepEPRoots_of_flatUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hodd : 2 < ℓ)
    (hreach : FlatReachableEP ℓ) (hunits : FlatUnitsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_flatPrescriptionEP ℓ hodd
    (flatPrescriptionEP_of_flatUnitsEP ℓ hreach hunits)

end Shafarevich
