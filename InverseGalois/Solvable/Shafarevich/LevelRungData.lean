/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerShaDescent
import InverseGalois.Solvable.Shafarevich.LevelOneDecomposition
import InverseGalois.Solvable.Shafarevich.LevelRung
import InverseGalois.Solvable.Shafarevich.LocalLiftInfinite

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
the hypothesis local solvability of the step asks of the family, and with the archimedean places
settled by coprimality it gives local solvability along every decomposition subgroup.  The bottom
of the ladder and the stability of the property are free, the property being a restriction on
ramification over the base realization, and the shrinking away of the locally trivial classes is
the Kummer-theoretic statement already proved over an arbitrary number field.

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

The family is the one the two-place construction is read along, and the property carried by the
solutions is the restriction on their ramification: the field a solution cuts out ramifies only at
primes where the base field splits completely and the local extension is cyclic and totally
ramified. -/
theorem exists_family_rungData (hodd : 2 < ℓ) (hS : IsPGroup ℓ S)
    {φ : Gal(Ω/k) →* U} (hsurj : Function.Surjective φ) (hsm : IsSmoothHom φ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y)
    (X : Set (HeightOneSpectrum (𝓞 ↥K))) (hX : X.Finite) :
    ∃ (t : ℕ) (Pr : Fin t → Ideal (𝓞 Ω)),
      (∀ v ∈ X, ∃ ν, Ideal.under (𝓞 ↥K) (Pr ν) = v.asIdeal) ∧
        ((∀ n j : ℕ, 1 ≤ j → HasSolutionRepair ℓ U n S j φ
            (fun ν => stabilizer Gal(Ω/k) (Pr ν)) (IsSplitTotallyRamified ℓ U S φ)) →
          HasRungData ℓ U S φ (fun ν => stabilizer Gal(Ω/k) (Pr ν))
            (decompositionSubgroups k Ω) (IsSplitTotallyRamified ℓ U S φ)) := by
  haveI : IsAlgClosure k Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨t, Pr, hPrp, hPrbot, hXPr, hfeq, hchar, hD⟩ :=
    exists_decomposition_family (S := S) (Fact.out : ℓ.Prime) hodd hsurj hsm K hKker hζ hmu X hX
  refine ⟨t, Pr, hXPr, fun hrepair => ⟨?_, ?_, ?_, hfeq, fun n j hj => ⟨?_, ?_, hrepair n j hj⟩⟩⟩
  · exact fun m => levelSolution_zero_isSplitTotallyRamified ℓ U S φ hsurj hsm _ m
  · exact fun n => levelSolution_one_of_hasLevelOneCharacter (hchar n)
  · exact isShrinkStable_isSplitTotallyRamified ℓ U S φ
  · exact hasLocalLift_isSplitTotallyRamified_decompositionSubgroups ℓ U n S j
      (Nat.ne_of_lt hodd).symm hS φ _ hD
  · exact hasShrinkableSha_decompositionSubgroups ℓ U n S j hS hsm

end Assembly

end InverseGalois.Shafarevich
