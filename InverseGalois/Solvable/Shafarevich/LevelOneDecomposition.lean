/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.CFT.Units.StablePlaces
import InverseGalois.Solvable.Shafarevich.ElementaryQuotientDecomposition
import InverseGalois.Solvable.Shafarevich.LevelOneTwoPlace

/-!
# The finite family of decomposition subgroups of the first rung

The ladder of the descending central series is climbed along a finite family of subgroups of the
absolute Galois group, the family the local conditions are read on.  In the arithmetic that family
is a family of decomposition subgroups at finite places, one for each place of a stable finite set
of places of the level the base realization cuts out, and this file builds it.

The set of places is the one carrying the ideal classes and the places above the exponent, enlarged
so as to contain any prescribed finite set of places; above each of its members a prime of the
integers of the whole extension is chosen, and the stabilisers of those primes are the family.
Two things are then true of the family at once.  Each of its members, cut down by the kernel of the
base realization, has a finite elementary quotient, because that is what local class field theory
says of a decomposition subgroup.  And the first rung of the ladder has its character over it,
because the places the two-place construction spends are places of the set the family is indexed by,
so the character the construction produces dies on every member.

## Main results

* `InverseGalois.Shafarevich.exists_decomposition_family`: a finite family of primes of the whole
  extension, containing one above each member of a prescribed finite set of places of the level,
  whose stabilisers have finite elementary quotients against the kernel of the base realization and
  carry the character of the first rung of the ladder.

## Tags

Shafarevich, embedding problem, decomposition subgroup, Frattini layer, two-place construction
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### The family and the character it carries -/

section Family

variable {ℓ : ℕ} {U S : Type} [Group U] [Finite U] [TopologicalSpace U] [DiscreteTopology U]
  [Group S] [Finite S]
  {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]

attribute [local instance] zmodTrivialAction

/-- **A prescribed finite set of places of a level is covered by a finite family of primes of the
whole extension whose stabilisers have finite elementary quotients and carry the character of the
first rung of the ladder.** -/
theorem exists_decomposition_family (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    {φ : Gal(Ω/k) →* U} (hsurj : Function.Surjective φ) (hsm : IsSmoothHom φ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y)
    (X : Set (HeightOneSpectrum (𝓞 ↥K))) (hX : X.Finite) :
    ∃ (t : ℕ) (Pr : Fin t → Ideal (𝓞 Ω)), (∀ ν, (Pr ν).IsPrime) ∧ (∀ ν, Pr ν ≠ ⊥) ∧
      (∀ v ∈ X, ∃ ν, Ideal.under (𝓞 ↥K) (Pr ν) = v.asIdeal) ∧
      (∀ ν, HasFiniteElementaryQuotient ℓ (stabilizer Gal(Ω/k) (Pr ν) ⊓ φ.ker)) ∧
      ∀ n : ℕ, HasLevelOneCharacter ℓ U S φ
        (Set.range fun ν => stabilizer Gal(Ω/k) (Pr ν)) n := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨Tn, hXTn, hTnst, hpTn, hrepr⟩ :=
    exists_stable_ord_places k ↥K (ℓ := ℓ) hℓ.ne_zero X hX
  choose Pf hPfp hPfbot hPfunder using fun v : HeightOneSpectrum (𝓞 ↥K) =>
    exists_stabilizer_prime_restrictNormalHom_eq (K := Ω) K (τ := 1) (v := v) (one_smul _ v)
  refine ⟨Tn.card, fun ν => Pf (Tn.equivFin.symm ν), fun ν => hPfp _, fun ν => hPfbot _,
    fun v hv => ⟨Tn.equivFin ⟨v, hXTn hv⟩, ?_⟩, fun ν => ?_, fun n => ?_⟩
  · simp only [Equiv.symm_apply_apply]
    exact (hPfunder v).1
  · haveI := hPfp (Tn.equivFin.symm ν : HeightOneSpectrum (𝓞 ↥K))
    exact hasFiniteElementaryQuotient_stabilizer_inf (hPfbot _)
      (isOpenNormal_ker_of_isSmoothHom hsm)
  · refine hasLevelOneCharacter_of_stable hℓ hodd n hsurj _ K hKker hζ hmu hTnst hpTn hrepr ?_
    rintro E ⟨ν, rfl⟩
    exact Or.inl ⟨Pf (Tn.equivFin.symm ν), hPfp _,
      ⟨((Tn.equivFin.symm ν : { x // x ∈ Tn }) : HeightOneSpectrum (𝓞 ↥K)),
        (Tn.equivFin.symm ν).2, (hPfunder _).1.symm⟩, rfl⟩

end Family

end InverseGalois.Shafarevich
