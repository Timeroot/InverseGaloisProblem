/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerShaDescent
import InverseGalois.Solvable.Shafarevich.LevelArchimedean
import InverseGalois.Solvable.Shafarevich.LevelOneDecomposition
import InverseGalois.Solvable.Shafarevich.LevelRung

/-!
# All but one clause of the package the ladder consumes

The package the ladder of the descending central series consumes has seven clauses: the bottom of
the ladder, the first rung, stability of the property under a shrinking, a finite elementary
quotient at each member of the finite family, and at every later rung local solvability of the
step, the shrinking away of every everywhere locally trivial class, and the repair of the property
on a lift.  Six of the seven are now theorems, and this file collects them.

The finite family is the one built from a prescribed finite set of places of a level: the
stabilisers of a prime above each place of a stable finite set which carries the ideal classes, the
places above the exponent, the places which ramify in the level and the prescribed set.  That
family supplies three clauses outright, the first rung, the finite elementary quotients, and the
statement that away from its conjugates the base realization kills inertia; the last of those is
the hypothesis local solvability of the step asks of the family, and once the family is enlarged by
one stabiliser above each archimedean place of the base it gives local solvability along every
decomposition subgroup.  The enlargement is free, the base realization meeting an archimedean
stabiliser trivially.  The bottom of the ladder and the stability of the property are free too, the
property being a restriction on ramification over the base realization, and the shrinking away of
the locally trivial classes is the Kummer-theoretic statement already proved over an arbitrary
number field.

What is left is the repair of the property, and it is left as a hypothesis on the family the theorem
itself produces.

## Main results

* `InverseGalois.Shafarevich.exists_family_rungData` — **a finite family of primes above a
  prescribed finite set of places of a level for which the repair of the property is the only thing
  the ladder still asks of the arithmetic.**

## Tags

Shafarevich's theorem, embedding problem, decomposition subgroup, local conditions, shrinking
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### Six of the seven clauses -/

section Assembly

variable {ℓ : ℕ} [Fact ℓ.Prime] {U S : Type} [Group U] [Finite U] [TopologicalSpace U]
  [DiscreteTopology U] [Group S] [Finite S]
  {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]

/-- **A finite family of primes above a prescribed finite set of places of a level for which the
repair of the property is the only thing the ladder still asks of the arithmetic.**

The family is the one the split place construction is read along, and the property carried by the
solutions is the restriction on their ramification: the field a solution cuts out ramifies only at
primes where the base field splits completely and the local extension is cyclic and totally
ramified.

The family also covers the primes above the exponent: any such prime is carried onto a member of the
family by an automorphism over the base, which is what says that a prime whose decomposition
subgroup escapes every conjugate of every member is a prime away from the exponent.  And it covers
the primes at which the base realization ramifies: away from the conjugates of the family, inertia
is killed by the base realization, the places at which the level ramifies being among those the
family is indexed by.

The family the package is read along is larger than the family of primes, holding in addition one
archimedean stabiliser above each archimedean place of the base; that is what makes the local
conditions at the infinite places vacuous, and it costs nothing, the clauses the family carries
being obligations at the elements the base realization kills. -/
theorem exists_family_rungData (hS : IsPGroup ℓ S)
    {φ : Gal(Ω/k) →* U} (hsurj : Function.Surjective φ) (hsm : IsSmoothHom φ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y)
    (X : Set (HeightOneSpectrum (𝓞 ↥K))) (hX : X.Finite) :
    ∃ (t : ℕ) (Pr : Fin t → Ideal (𝓞 Ω)),
      (∀ v ∈ X, ∃ ν, Ideal.under (𝓞 ↥K) (Pr ν) = v.asIdeal) ∧
      (∀ ν, (Pr ν).IsPrime) ∧ (∀ ν, Pr ν ≠ ⊥) ∧
      (∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → (ℓ : 𝓞 Ω) ∈ P →
        ∃ (ν : Fin t) (ρ : Gal(Ω/k)), ρ • P = Pr ν) ∧
      (∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
        stabilizer Gal(Ω/k) P ∉ conjFamily (fun ν => stabilizer Gal(Ω/k) (Pr ν)) →
        ∀ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1) ∧
        ((∀ n j : ℕ, 1 ≤ j → HasSolutionRepair ℓ U n S j φ
            (fun ν => stabilizer Gal(Ω/k) (Pr ν)) (IsSplitTotallyRamified ℓ U S φ)) →
          ∃ (t' : ℕ) (D : Fin t' → Subgroup Gal(Ω/k)),
            HasRungData ℓ U S φ D (decompositionSubgroups k Ω)
              (IsSplitTotallyRamified ℓ U S φ)) := by
  haveI : IsAlgClosure k Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨t, Pr, hPrp, hPrbot, hXPr, hcov, hfeq, hchar, hD⟩ :=
    exists_decomposition_family (S := S) (Fact.out : ℓ.Prime) hsurj hsm K hKker hζ hmu X hX
  obtain ⟨s, W, hW⟩ := exists_infinitePlace_family k Ω
  have hE : ∀ μ : Fin s, ∀ x ∈ stabilizer Gal(Ω/k) (W μ), φ x = 1 → x = 1 := fun μ x hx hφ =>
    eq_one_of_mem_stabilizer_infinitePlace_of_mem_ker (Fact.out : ℓ.Prime).two_le hmu (W μ) hx hφ
  refine ⟨t, Pr, hXPr, hPrp, hPrbot, hcov, hD, fun hrepair =>
    ⟨t + s, Fin.append (fun ν => stabilizer Gal(Ω/k) (Pr ν))
      (fun μ => stabilizer Gal(Ω/k) (W μ)), ?_⟩⟩
  refine hasRungData_append ℓ U S (D := fun ν => stabilizer Gal(Ω/k) (Pr ν))
    (E := fun μ => stabilizer Gal(Ω/k) (W μ)) hE
    (fun m => levelSolution_zero_isSplitTotallyRamified ℓ U S φ hsurj hsm _ m)
    (fun m => levelSolution_one_of_hasLevelOneCharacter (hchar m))
    (isShrinkStable_isSplitTotallyRamified ℓ U S φ) hfeq (fun m j _ => ?_)
    (fun m j _ => hasShrinkableSha_decompositionSubgroups ℓ U m S j hS hsm) hrepair
  exact hasLocalLift_isSplitTotallyRamified_of_forall_infinitePlace ℓ U m S j hS φ _
    (fun w => conjFamily_append_right _ _ (hW w))
    (fun P hPp hPbot hPnot => hD P hPp hPbot fun hc => hPnot (conjFamily_append_left _ _ hc))

end Assembly

end InverseGalois.Shafarevich
