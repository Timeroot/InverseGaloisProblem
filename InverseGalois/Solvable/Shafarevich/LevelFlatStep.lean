/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelFlatPlaces
import InverseGalois.Solvable.Shafarevich.NamedOrthogonal

/-!
# The step of the ladder in exchange for invariant radicands alone

The flattening the step of the ladder is bought with is made one field up and one named prime at a
time, and there it is assembled out of a single unit of the level the base realization cuts out for
each named prime: one whose order at the place below that prime is prime to the exponent, which is
fixed up to an exponent-th power by the automorphisms of the level fixing that place, and which is a
local power everywhere the assembly is asked to be trivial.  This file spends that assembly the way
the sharp prescription was spent — a base realization over the rationals cuts out a finite Galois
level, the roots of unity of order the prime lie in it because the realization is asked to fix those
of order its square, and the places of the level below the finite family are the places the units
are asked to be local powers at.

What is left over is a single statement about a number field, asking nothing about any group: given
a finite Galois level of it and finitely many places in pairwise distinct orbits, there is one unit
for each place with those five local properties.  Together with the orthogonality of the naming,
which is already a theorem, that statement carries the whole step of the ladder for every odd prime.

## Main definitions

* `Shafarevich.InvariantRadicandsEP` — **every level carries, for each of finitely many places in
  pairwise distinct orbits, a unit fixed up to an exponent-th power by the automorphisms fixing its
  place, of order there prime to the exponent, and a local power at the places the assembly is asked
  to be trivial at.**

## Main results

* `Shafarevich.flatOrbitPrescriptionEP_of_invariantRadicandsEP` — **the invariant radicands buy the
  flattening made one field up and one named prime at a time.**
* `Shafarevich.flatPrescriptionEP_of_invariantRadicandsEP` — **the invariant radicands buy the
  flattening.**
* `Shafarevich.genericLevelStepEPRoots_of_invariantRadicandsEP` — **the step of the ladder, in
  exchange for the invariant radicands alone.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, radicand, decomposition group
-/

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich IsDedekindDomain MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

attribute [local instance] genericQuotAction zmodTrivialAction

/-! ### The arithmetic, asked of every level -/

/-- **Every level carries, for each of finitely many places in pairwise distinct orbits, a unit
fixed up to an exponent-th power by the automorphisms fixing its place, of order there prime to the
exponent, and a local power at the places the assembly is asked to be trivial at.**

This is the whole of what the flattening asks of the arithmetic, read off the level a base
realization cuts out and stated for an arbitrary level of an arbitrary number field carrying a
primitive root of unity of order the prime.  Nothing about any group survives in it: the named
places are an arbitrary finite family in pairwise distinct orbits, the places the units are asked
to be local powers at are an arbitrary finite set the named ones avoid, and the finite level the
leftover places are asked to be completely decomposed in is named in advance.

Invariance is the clause which makes the prescription cost one unit per named prime rather than one
per coordinate of the layer: it is only asked along the automorphisms fixing the place, which is
exactly the amount of equivariance the decomposition subgroup of a prime above that place sees. -/
def InvariantRadicandsEP (ℓ : ℕ) [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
      (ζ : ↥K), IsPrimitiveRoot ζ ℓ → HasInvariantRadicands ℓ K

/-! ### The flattening and the step -/

/-- **The invariant radicands buy the flattening made one field up and one named prime at a time.**

The level is the one the kernel of the base realization cuts out, finite and Galois over the
rationals because the kernel is open and normal, and the root of unity of order the prime lies in it
because the base realization fixes the roots of unity of order its square.  The closure being
algebraically closed, every unit of the level has an exponent-th root there, which is what makes the
level and its closure Kummer data.  The places the units are asked to be local powers at are read
off the finite family of primes, and the places above the prime are covered because the primes above
it are.

Where the kernel is not open there is nothing to cut out, but there is also nothing to prove: a
smooth lift lying over the base realization has open kernel, and the base realization kills it, so
the kernel of the base realization would be open after all. -/
theorem flatOrbitPrescriptionEP_of_invariantRadicandsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : InvariantRadicandsEP ℓ) : FlatOrbitPrescriptionEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j _ _ hmu hcov
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
    exact hasFlatOrbitPrescription_of_places K hKker hζ hkd hPrp hPrbot hDPr
      (exists_smul_placeUnder_of_mem K hPrp hPrbot hcovP) (h ℚ Ω K ⟨z, hzK⟩ hζ)
  · refine ⟨n, ?_⟩
    intro F ι _ Q A a _ hFsm hFright
    have hFle : F.ker ≤ φ.ker := fun x hx => MonoidHom.mem_ker.2 (by
      rw [← hFright x, MonoidHom.mem_ker.1 hx, _root_.map_one])
    exact absurd (Subgroup.isOpen_mono hFle (isOpenNormal_ker_of_isSmoothHom hFsm).isOpen) hopen

/-- **The invariant radicands buy the flattening.** -/
theorem flatPrescriptionEP_of_invariantRadicandsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : InvariantRadicandsEP ℓ) : FlatPrescriptionEP ℓ :=
  flatPrescriptionEP_of_flatOrbitPrescriptionEP ℓ
    (flatOrbitPrescriptionEP_of_invariantRadicandsEP ℓ h)

/-- **The step of the ladder, in exchange for the invariant radicands alone** — the one piece of
arithmetic the whole climb rests on for an odd prime. -/
theorem genericLevelStepEPRoots_of_invariantRadicandsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (h : InvariantRadicandsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_flatPrescriptionEP ℓ hodd
    (flatPrescriptionEP_of_invariantRadicandsEP ℓ h)

end Shafarevich
