/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CutField
import InverseGalois.CFT.Scholz.CentralStep

/-!
# A solution field of `ℓ`-power degree

The central step of the Scholz–Reichardt induction produces a Galois extension of the rationals
carrying a surjection onto the group to be realised, but that extension is larger than the group:
it is built by adjoining roots of unity, so its Galois group need not be an `ℓ`-group.  Cutting it
down to the fixed field of the kernel of the surjection loses nothing — the surjection becomes an
isomorphism, and the map it lifts is unchanged — and gains the property that the Galois group is
exactly the group to be realised, hence an `ℓ`-group.

That property is what the ramification analysis needs: in an extension of `ℓ`-power degree every
inertia subgroup away from `ℓ` is tame, so the primes at which the solution ramifies unnecessarily
can be classified and then removed.

## Main results

* `InverseGalois.CFT.exists_galEquiv_of_centralStep`: **the central step of the Scholz–Reichardt
  induction produces a Galois extension of the rationals whose Galois group is the group to be
  realised**, containing the field it lifts and inducing the given realization of the quotient.

## Tags

embedding problem, Scholz condition, fixed field, `p`-group
-/

namespace InverseGalois.CFT

open IntermediateField NumberField InverseGalois.NumberTheory

variable {ℓ : ℕ} [NeZero ℓ]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The central step of the Scholz–Reichardt induction produces a Galois extension of the
rationals whose Galois group is the group to be realised.**  The solution field of the embedding
problem is cut down to the fixed field of the kernel of the solution, which still contains the
field the problem is posed over and still induces the given realization of the quotient. -/
theorem exists_galEquiv_of_centralStep (hℓ : ℓ.Prime) (hodd : Odd ℓ) {N : ℕ}
    {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hpg : IsPGroup ℓ G) (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (hcard : Nat.card ↥f.ker = ℓ) (hHdvd : Nat.card H ∣ ℓ ^ N)
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A] [NumberField ↥A]
    (hsch : IsScholz ℓ (N + 1) ↥A) (e : Gal(↥A/ℚ) ≃* H) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hAL : A ≤ L), NumberField ↥L ∧
      IsGalois ℚ ↥L ∧ ∃ ψ : Gal(↥L/ℚ) ≃* G, ∀ τ, f (ψ τ) = e (galRestrictLE hAL τ) := by
  obtain ⟨E, hAE, hNFE, hGalE, ψ, hψ, hcomp⟩ :=
    exists_surjective_hom_of_centralStep hℓ hodd hf hpg hZ hfr hcard hHdvd A hsch e
  haveI := hNFE
  haveI := hGalE
  have hker : ψ.ker ≤ (galRestrictLE hAE).ker := by
    intro σ hσ
    have h1 : e (galRestrictLE hAE σ) = 1 := by
      rw [← hcomp σ, MonoidHom.mem_ker.mp hσ, map_one]
    exact MonoidHom.mem_ker.mpr (by simpa using h1)
  have hAL : A ≤ cutField ψ := le_cutField ψ hAE hker
  haveI : FiniteDimensional ℚ ↥(cutField ψ) :=
    (IntermediateField.liftAlgEquiv
      (IntermediateField.fixedField ψ.ker)).toLinearEquiv.finiteDimensional
  haveI : NumberField ↥(cutField ψ) := ⟨⟩
  haveI : IsGalois ℚ ↥(cutField ψ) := ⟨⟩
  refine ⟨cutField ψ, hAL, inferInstance, inferInstance, galEquivCutField ψ hψ, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := galRestrictLE_surjective (cutField_le ψ) τ
  rw [galEquivCutField_galRestrictLE ψ hψ σ, hcomp σ,
    galRestrictLE_galRestrictLE hAL (cutField_le ψ) σ]

end InverseGalois.CFT
