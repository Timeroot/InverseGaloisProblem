/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.FlatInvariant
import InverseGalois.Solvable.Shafarevich.FlatStep
import InverseGalois.Solvable.Shafarevich.FlatTensor

/-!
# The flattening in exchange for one invariant tensor

The flat prescription assembled out of a single invariant tensor is spent over the rationals exactly
as the one assembled out of a unit at each named place: a base realization cuts out a finite Galois
level, the roots of unity of order the prime lie in it because the realization is asked to fix those
of order its square, and the finite family the local conditions are read on names a family of primes
whose places below are the places the tensor is prescribed at.

What the tensor buys that a family of units does not is the equivariance clause.  A unit at a named
place is fixed only by the automorphisms fixing that place, so the homomorphism it assembles is
equivariant only for the decomposition subgroup there, and the several prescriptions have to be kept
from disturbing one another by local conditions at the conjugates of the other named places.  A
tensor invariant for the whole group of the level assembles a homomorphism equivariant for the whole
base group at once, so the prescription is answered in one piece and the step of the ladder follows
with no tracing over cosets.

## Main definitions

* `Shafarevich.FlatTensorEP` — **every finite Galois level of the rationals containing the roots of
  unity of order the prime carries the invariant tensor the flat prescription is assembled out
  of.**
* `Shafarevich.InvariantUnitTensorEP` — the same demand with the root of unity taken out of it, a
  statement about the units of a number field alone.

## Main results

* `Shafarevich.flatPrescriptionEP_of_flatTensorEP` — **the tensor buys the flattening.**
* `Shafarevich.genericLevelStepEPRoots_of_flatTensorEP` — **the step of the ladder over an odd
  prime, in exchange for the tensor alone.**
* `Shafarevich.flatTensorEP_of_invariantUnitTensorEP` — the invariant tensor of units buys the
  prescribed tensor.
* `Shafarevich.genericLevelStepEPRoots_of_invariantUnitTensorEP` — **the step of the ladder over an
  odd prime, in exchange for the invariant tensor of units alone.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, tensor product, decomposition group
-/

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich IsDedekindDomain MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

attribute [local instance] zmodTrivialAction

/-! ### The arithmetic, asked of every level -/

/-- **Every finite Galois level of the rationals containing the roots of unity of order the prime
carries the invariant tensor the flat prescription is assembled out of.**

The demand is the one the assembly of the flat prescription out of a single tensor makes, asked of
every finite Galois level of an arbitrary number field inside an algebraic closure carrying a
primitive root of unity of order the prime: a target killed by the exponent, a spanning family of
it and an action of the automorphisms of the level on it being given, and finitely many places in
distinct orbits being named together with the values prescribed there, a tensor of the units of the
level with the target is asked for, invariant for the diagonal action twisted on the coefficient by
the exponent to which the automorphism raises the roots of unity, of the prescribed order at each
named place, a local power at a prescribed finite set of places the named places avoid, and confined
elsewhere to places sitting over the named ones or completely decomposed in a finite level given in
advance. -/
def FlatTensorEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
      (ζ : ↥K), IsPrimitiveRoot ζ ℓ → HasFlatPrescribedTensor ℓ K ζ

/-! ### The prescription and the step -/

/-- **The tensor buys the flattening.**

The level is the one the kernel of the base realization cuts out, finite and Galois over the
rationals because the kernel is open and normal, and the root of unity of order the prime lies in it
because the base realization fixes the roots of unity of order its square.  The closure being
algebraically closed, every unit of the level has an exponent-th root there, which is what makes the
level and its closure Kummer data.  The places the tensor is prescribed at are read off the finite
family of primes, and the places above the prime are covered because the primes above it are.

Because the homomorphism the tensor assembles is equivariant for the whole base group, the
prescription it answers is the one made one field up in a single piece, and extending it along a
section of the base realization carries it down to the rationals.

Openness of the kernel is not assumed: the prescription is handed a smooth lift lying over the base
realization, whose kernel is open and lies inside it, so where the kernel is not open there is
nothing to prescribe for. -/
theorem flatPrescriptionEP_of_flatTensorEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (h : FlatTensorEP ℓ) :
    FlatPrescriptionEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  letI := galLayerAction ℓ U n S j φ
  obtain ⟨Pr, hPrp, hPrbot, hDPr, hcovP, -⟩ := hcov
  refine hasFlatPrescription_of_hasFlatKernelPrescription hS (fun _ _ => rfl) fun M => ?_
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
    exact hasFlatKernelPrescription_of_tensor K hKker hζ hkd hPrp hPrbot hDPr
      (exists_smul_placeUnder_of_mem K hPrp hPrbot hcovP) (h ℚ Ω K _ hζ)
  · refine ⟨0, ?_⟩
    intro F ι _ Q A a hFsurj hFsm hFright
    refine absurd (Subgroup.isOpen_mono ?_ (isOpenNormal_ker_of_isSmoothHom hFsm).isOpen) hopen
    intro x hx
    refine MonoidHom.mem_ker.2 ?_
    rw [← hFright x, MonoidHom.mem_ker.1 hx, _root_.map_one]

/-- **The step of the ladder, in exchange for the tensor alone** — the one piece of arithmetic the
whole climb over an odd prime rests on, read as a single invariant object. -/
theorem genericLevelStepEPRoots_of_flatTensorEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hodd : 2 < ℓ)
    (h : FlatTensorEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_flatPrescriptionEP ℓ hodd (flatPrescriptionEP_of_flatTensorEP ℓ h)

/-! ### The same demand with the root of unity taken out -/

/-- **The demand the flat step makes of the arithmetic, written without the root of unity.**

The level is still asked to carry a primitive root of unity of order the prime, since the Kummer
theory the assembly runs on needs one, but nothing in what is asked of the level mentions it: a
target killed by the exponent with an action of the automorphisms of the level and a named basis
being given, and finitely many places in distinct orbits being named together with values there
fixed by the automorphisms fixing their places, a family of units of the level is asked for whose
tensor against the basis is invariant, whose orders at the named places give the prescribed values,
which is a local power at a prescribed finite set of places the named places avoid, and whose
remaining ramification is confined. -/
def InvariantUnitTensorEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
      (∃ ζ : ↥K, IsPrimitiveRoot ζ ℓ) → HasInvariantUnitTensor ℓ K

/-- **The invariant tensor of units buys the prescribed tensor**, the twist by the character
inverse to the cyclotomic one turning the invariance into the equivariance the assembly asks
for. -/
theorem flatTensorEP_of_invariantUnitTensorEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : InvariantUnitTensorEP ℓ) : FlatTensorEP ℓ := by
  intro k Ω _ _ _ _ _ _ K _ _ _ ζ hζ
  exact hasFlatPrescribedTensor_of_hasInvariantUnitTensor hζ (h k Ω K ⟨ζ, hζ⟩)

/-- **The step of the ladder over an odd prime, in exchange for the invariant tensor of units
alone** — the whole climb resting on one statement about the units of a number field. -/
theorem genericLevelStepEPRoots_of_invariantUnitTensorEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (h : InvariantUnitTensorEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_flatTensorEP ℓ hodd (flatTensorEP_of_invariantUnitTensorEP ℓ h)

end Shafarevich
