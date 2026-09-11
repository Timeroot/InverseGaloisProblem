/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.KernelArith
import InverseGalois.Solvable.Shafarevich.KernelPlaces
import InverseGalois.Solvable.Shafarevich.LevelStepRepair

/-!
# The step of the ladder in exchange for families of units alone

The sharp prescription the repair of the property is bought with is assembled out of a family of
units of the level the base realization cuts out, prescribed local classes at finitely many places
and confined elsewhere.  This file spends that assembly: a base realization over the rationals cuts
out a finite Galois level, the roots of unity of order the prime lie in it because the realization
is asked to fix those of order its square, the finite family the local conditions are read on names
a family of primes, and the places of the level below those primes are the places the family of
units is prescribed at.

The one thing the assembly asks of the finite family beyond its being a family of decomposition
subgroups is that it cover the primes above the prime: a place of the level carrying the prime
carries a prime of the whole extension above it, and that prime is moved onto a member of the family
by an automorphism over the rationals, so the place below it is moved onto the place below a member.
That is exactly the disjointness the assembly needs, the places at which the family of units is
asked to be a local power being the orbit of the places below the finite family.

## Main definitions

* `Shafarevich.PrescribedUnitsEP` — **every finite Galois level of the rationals containing a
  primitive root of unity of order the prime carries the families of units prescribed at named
  places**.
* `Shafarevich.NamedPairingEP` — **at every finite Galois level of the rationals containing a
  primitive root of unity of order the prime, the classes named at finitely many places pair
  trivially with the units of the level which become powers in a larger level**.

## Main results

* `Shafarevich.exists_smul_placeUnder_of_mem` — **a place of a level carrying the prime lies below
  a conjugate of a member of a family of primes covering the primes above the prime.**
* `Shafarevich.kernelPrescriptionEP_of_prescribedUnitsEP` — **the families of units buy the sharp
  prescription made one field up.**
* `Shafarevich.genericLevelStepEPRoots_of_prescribedUnitsEP` — **the step of the ladder, in
  exchange for the flattening and the families of units.**
* `Shafarevich.prescribedUnitsEP_of_namedPairingEP` — **the families of units are bought with the
  vanishing of one pairing alone.**
* `Shafarevich.genericLevelStepEPRoots_of_namedPairingEP` — **the step of the ladder, in exchange
  for the flattening and the vanishing of that pairing.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, decomposition group, local class
-/

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich IsDedekindDomain MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### The arithmetic, asked of every level -/

/-- **Every finite Galois level of the rationals containing a primitive root of unity of order the
prime carries the families of units prescribed at named places.**

The demand read at one level is the one the assembly of the sharp prescription consumes: local
classes prescribed at finitely many places at once, a local power at a prescribed finite set of
places the named ones avoid and at the proper conjugates of the named ones, and confined elsewhere
to places sitting over the named ones or completely decomposed in a given finite level. -/
def PrescribedUnitsEP (ℓ : ℕ) : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
      (ζ : ↥K), IsPrimitiveRoot ζ ℓ → HasPrescribedUnits ℓ K

/-- **At every finite Galois level of the rationals containing a primitive root of unity of order
the prime, the classes named at finitely many places pair trivially with the units of the level
which become powers in a larger level.**

This is what the demand of the previous definition costs once the two-place construction over a
number field has been spent on it: the product of the power residue symbols over all the places of
such a unit against the named classes vanishes, the product formula having already disposed of
every place the classes are not named at. -/
def NamedPairingEP (ℓ : ℕ) [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
      {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
      (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K),
        HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
      (ζ : ↥K) (hζ : IsPrimitiveRoot ζ ℓ), HasNamedPairing ℓ K hres hζ

/-- **The families of units are bought with the vanishing of one pairing alone.**

The residue characteristics of the completions of the level are named once and for all, and the
two-place construction over a number field turns the vanishing of the pairing against them into the
families of units the prescription is made of. -/
theorem prescribedUnitsEP_of_namedPairingEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hodd : 2 < ℓ)
    (h : NamedPairingEP ℓ) : PrescribedUnitsEP ℓ := by
  intro k Ω _ _ _ _ _ _ K _ _ _ ζ hζ
  classical
  choose Pc Ec hres using
    fun v : HeightOneSpectrum (𝓞 ↥K) => exists_hasResidueChar_adicCompletion v
  exact hasPrescribedUnits_of_hasNamedPairing Fact.out hodd K hres hζ (h k Ω K hres ζ hζ)

/-! ### The places of the level below the family -/

/-- **A place of a level carrying the prime lies below a conjugate of a member of a family of
primes covering the primes above the prime.**

Some prime of the whole extension lies above the place, and it carries the prime because the place
does; the family covers it, so an automorphism over the base carries it onto a member of the family,
and the restriction of that automorphism to the level carries the place below the member onto the
place. -/
theorem exists_smul_placeUnder_of_mem {ℓ t : ℕ} {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsGalois k Ω] (K : IntermediateField k Ω) [NumberField ↥K] [IsGalois k ↥K]
    {Pr : Fin t → Ideal (𝓞 Ω)} (hPrp : ∀ ν, (Pr ν).IsPrime) (hPrbot : ∀ ν, Pr ν ≠ ⊥)
    (hcovP : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → (ℓ : 𝓞 Ω) ∈ P →
      ∃ (ν : Fin t) (ρ : Gal(Ω/k)), ρ • P = Pr ν)
    (v : HeightOneSpectrum (𝓞 ↥K)) (hv : (ℓ : 𝓞 ↥K) ∈ v.asIdeal) :
    ∃ (σ : Gal(↥K/k)) (ν : Fin t), v = σ • placeUnder K (Pr ν) (hPrbot ν) := by
  obtain ⟨P, hPp, hPbot, hPunder, -⟩ :=
    exists_stabilizer_prime_restrictNormalHom_eq (K := Ω) K (τ := 1) (v := v) (one_smul _ v)
  haveI := hPp
  have hPℓ : (ℓ : 𝓞 Ω) ∈ P := by
    have hmem : algebraMap (𝓞 ↥K) (𝓞 Ω) (ℓ : 𝓞 ↥K) ∈ P := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, hPunder]
      exact hv
    rwa [map_natCast] at hmem
  obtain ⟨ν, ρ, hρ⟩ := hcovP P hPp hPbot hPℓ
  have hPv : placeUnder K P hPbot = v :=
    HeightOneSpectrum.ext (by rw [placeUnder_asIdeal, hPunder])
  refine ⟨(AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ)⁻¹, ν, ?_⟩
  rw [eq_inv_smul_iff]
  refine HeightOneSpectrum.ext ?_
  rw [← hPv, asIdeal_smul_placeUnder K hPbot ρ, hρ, placeUnder_asIdeal]

/-! ### The prescription and the step -/

/-- **The families of units buy the sharp prescription made one field up.**

The level is the one the kernel of the base realization cuts out, finite and Galois over the
rationals because the kernel is open and normal, and the root of unity of order the prime lies in it
because the base realization fixes the roots of unity of order its square.  The places the family of
units is prescribed at are read off the finite family of primes, and the places above the prime are
covered because the primes above it are. -/
theorem kernelPrescriptionEP_of_prescribedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime]
    (h : PrescribedUnitsEP ℓ) : KernelPrescriptionEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  letI := galLayerAction ℓ U n S j φ
  obtain ⟨Pr, hPrp, hPrbot, hDPr, hcovP⟩ := hcov
  by_cases hopen : IsOpen (φ.ker : Set Gal(Ω/ℚ))
  · haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    obtain ⟨K, hfin, hgal, hKker, hKmem⟩ :=
      exists_level_fixingSubgroup_eq (N := φ.ker) ⟨inferInstance, hopen⟩
    haveI := hfin
    haveI := hgal
    haveI : NumberField ↥K := numberField_of_finiteDimensional K
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_of_isAlgClosure ℚ Ω ℓ
    have hz0 : z ≠ 0 := hz.ne_zero (Fact.out : ℓ.Prime).ne_zero
    have hzsq : (Units.mk0 z hz0) ^ (ℓ * ℓ * Monoid.exponent S) = 1 := by
      refine Units.ext ?_
      show z ^ (ℓ * ℓ * Monoid.exponent S) = 1
      rw [pow_mul, pow_mul, hz.pow_eq_one, one_pow, one_pow]
    have hzK : z ∈ K := by
      refine hKmem z fun σ hσ => ?_
      exact congrArg Units.val (hmu (Units.mk0 z hz0) hzsq σ hσ)
    have hζ : IsPrimitiveRoot (⟨z, hzK⟩ : ↥K) ℓ :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) hz (algebraMap ↥K Ω).injective
    exact hasKernelPrescription_of_places K hKker hζ hPrp hPrbot hDPr
      (exists_smul_placeUnder_of_mem K hPrp hPrbot hcovP) (h ℚ Ω K ⟨z, hzK⟩ hζ)
  · exact ⟨0, fun hc => absurd hc hopen⟩

/-- **The step of the ladder, in exchange for the flattening and the families of units** — the two
pieces of arithmetic the whole climb rests on. -/
theorem genericLevelStepEPRoots_of_prescribedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] (hodd : 2 < ℓ)
    (hflat : FlatPrescriptionEP ℓ) (h : PrescribedUnitsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_kernelPrescriptionEP ℓ hodd hflat
    (kernelPrescriptionEP_of_prescribedUnitsEP ℓ h)

/-- **The step of the ladder, in exchange for the flattening and the vanishing of the pairing the
named classes are read against** — the whole climb, resting on two statements of arithmetic. -/
theorem genericLevelStepEPRoots_of_namedPairingEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hodd : 2 < ℓ)
    (hflat : FlatPrescriptionEP ℓ) (h : NamedPairingEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_prescribedUnitsEP ℓ hodd hflat
    (prescribedUnitsEP_of_namedPairingEP ℓ hodd h)

end Shafarevich
