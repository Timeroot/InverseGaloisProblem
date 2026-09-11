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

* `Shafarevich.NamedOrthogonalEP` — **the classes the prescribed values name at the named primes
  are orthogonal, under the product of the power residue symbols, to the units of the level which
  become powers in a finite level**.

## Main results

* `Shafarevich.exists_smul_placeUnder_of_mem` — **a place of a level carrying the prime lies below
  a conjugate of a member of a family of primes covering the primes above the prime.**
* `Shafarevich.kernelPrescriptionEP_of_namedOrthogonalEP` — **the orthogonality of the naming buys
  the sharp prescription made one field up.**
* `Shafarevich.genericLevelStepEPRoots_of_namedOrthogonalEP` — **the step of the ladder, in
  exchange for the flattening and the orthogonality of the naming.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, decomposition group, local class
-/

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich IsDedekindDomain MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

attribute [local instance] genericQuotAction zmodTrivialAction

/-! ### The arithmetic, asked of every level -/

/-- **The classes the prescribed values name at the named primes are orthogonal, under the product
of the power residue symbols, to the units of the level which become powers in a finite level.**

Everything the assembly of the sharp prescription asks of the arithmetic that the two-place
construction over a number field does not already answer is this one orthogonality, and it is asked
not of an arbitrary naming but of the naming the prescribed values themselves cut out: the classes
are pinned down by the demand that a family of units carrying them assemble, through Kummer theory,
into the prescribed homomorphism on the decomposition subgroup of each named prime.  The product of
the symbols over all the places of the level is trivial and away from the named places the naming
contributes nothing, so what is left is the product over the named places alone, read against the
units supported at any finite set containing them, trivial at every infinite place, and already a
power in the finite level the leftover places are asked to be decomposed in.

The orthogonality is asked together with both the shrinking and the finite level it is bought with,
in the shape the whole ladder is written in: a number of letters is announced in advance, the
prescribed values are read at that number against a lift of the base realization which is onto and
lies over it, and what is asked back is a surjection onto the number the prescription answers at, a
finite level over the level below which kills that lift carried across the surjection, and the
orthogonality, in that level, of the naming the values carried across the surjection name. -/
def NamedOrthogonalEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] (k Ω : Type) [Field k] [Field Ω]
      [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω] (φ : Gal(Ω/k) →* U) (n j : ℕ)
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
      (hKker : K.fixingSubgroup = φ.ker) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ ℓ)
      (hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
      {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
      (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K),
        HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v)),
      ∃ N : ℕ, ∀ (F : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1)) (ι : Type) [Fintype ι]
        (Q : ι → Ideal (𝓞 Ω)) (_ : ∀ μ, (Q μ).IsPrime) (hQbot : ∀ μ, Q μ ≠ ⊥)
        (A : ι → Subgroup Gal(Ω/k))
        (a : (μ : ι) → ↥(A μ) →* ↥(layerSub ℓ (Generic U N S) j)),
        Function.Surjective F → IsSmoothHom F →
        (∀ x, SemidirectProduct.rightHom (F x) = φ x) →
        ∃ (α : Generic U N S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
          ∃ E : IntermediateField k Ω, FiniteDimensional k ↥E ∧ IsGalois k ↥E ∧ K ≤ E ∧
            E.fixingSubgroup ≤ ((layerSemidirectMap ℓ hα (j + 1)).comp F).ker ∧
            ∀ c : (μ : ι) → Fin (layerDim ℓ (Generic U n S) j) →
                localClasses (placeUnder K (Q μ) (hQbot μ)) ℓ,
              (∀ (μ : ι) (z : Fin (layerDim ℓ (Generic U n S) j) → (↥K)ˣ),
                (∀ q, localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ (z q) = c μ q) →
                ∀ (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
                  kummerKernelHom hKker hkd (layerBasis ℓ (Generic U n S) j) layerBasis_pow_eq_one z
                    ⟨(x : Gal(Ω/k)), hx⟩ = layerSubMap ℓ α j (a μ x)) →
              IsNamedOrthogonal ℓ K hres hζ E (fun μ => placeUnder K (Q μ) (hQbot μ)) c

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

/-- **The orthogonality of the naming buys the sharp prescription made one field up.**

The level is the one the kernel of the base realization cuts out, finite and Galois over the
rationals because the kernel is open and normal, and the root of unity of order the prime lies in it
because the base realization fixes the roots of unity of order its square.  The closure being
algebraically closed, every unit of the level has an exponent-th root there, which is what makes the
level and its closure Kummer data.  The places the family of units is prescribed at are read off the
finite family of primes, and the places above the prime are covered because the primes above it are;
the families of units themselves are carried by the two-place construction over a number field, so
that the orthogonality of the naming is all that is left to ask. -/
theorem kernelPrescriptionEP_of_namedOrthogonalEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hodd : 2 < ℓ)
    (h : NamedOrthogonalEP ℓ) : KernelPrescriptionEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  letI := galLayerAction ℓ U n S j φ
  obtain ⟨Pr, hPrp, hPrbot, hDPr, hcovP⟩ := hcov
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
    choose Pc Ec hres using
      fun v : HeightOneSpectrum (𝓞 ↥K) => exists_hasResidueChar_adicCompletion v
    obtain ⟨N, horth⟩ := h S U ℚ Ω φ n j K hKker ⟨z, hzK⟩ hζ hkd hres
    exact hasKernelPrescription_of_places N K hKker hζ hkd hres hPrp hPrbot hDPr
      (exists_smul_placeUnder_of_mem K hPrp hPrbot hcovP) horth
      (hasPrescribedUnits hℓ hodd K hres hζ)
  · exact ⟨0, fun hc => absurd hc hopen⟩

/-- **The step of the ladder, in exchange for the flattening and the orthogonality of the naming**
— the two pieces of arithmetic the whole climb rests on. -/
theorem genericLevelStepEPRoots_of_namedOrthogonalEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hflat : FlatPrescriptionEP ℓ) (h : NamedOrthogonalEP ℓ) :
    GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_kernelPrescriptionEP ℓ hodd hflat
    (kernelPrescriptionEP_of_namedOrthogonalEP ℓ hodd h)

end Shafarevich
