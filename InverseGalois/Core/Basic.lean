/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts

/-!
# The Inverse Galois Problem — Definitions

We define a predicate `IsInverseGalois G` stating that a group `G` arises as the Galois group
of some finite Galois extension `L/ℚ`.

## Main definitions

* `IsInverseGalois G`: There exists a finite Galois extension `L/ℚ` with `Gal(L/ℚ) ≃* G`.

## Main results

* `IsInverseGalois.of_mulEquiv`: Invariant under group isomorphism.
* `IsInverseGalois.of_surjective`: Closed under quotients — if `G` is an inverse Galois group
  and `f : G →* H` is surjective, then `H` is also an inverse Galois group.
-/

open Polynomial IntermediateField

/-- A group `G` is an **inverse Galois group** (over `ℚ`) if there exists a finite Galois
extension `L/ℚ` whose Galois group `Gal(L/ℚ)` is isomorphic to `G`. -/
def IsInverseGalois (G : Type*) [Group G] : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L)
    (_ : IsGalois ℚ L), Nonempty (Gal(L/ℚ) ≃* G)

namespace IsInverseGalois

variable {G H : Type*} [Group G] [Group H]

/-- Invariance under group isomorphism. -/
theorem of_mulEquiv (hG : IsInverseGalois G) (e : G ≃* H) : IsInverseGalois H := by
  obtain ⟨L, hF, hA, hFD, hGal, ⟨φ⟩⟩ := hG
  exact ⟨L, hF, hA, hFD, hGal, ⟨φ.trans e⟩⟩

/-- Helper: if `L/ℚ` is a finite Galois extension and `ψ : Gal(L/ℚ) →* H` is surjective,
then `H` is an inverse Galois group.

Uses the Galois correspondence: the kernel `N = ker ψ` is normal, so `fixedField N / ℚ` is
Galois with `Gal(fixedField N / ℚ) ≅ Gal(L/ℚ) / N ≅ H`. -/
theorem of_surjective_galHom (L : Type) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (ψ : Gal(L/ℚ) →* H)
    (hψ : Function.Surjective ψ) : IsInverseGalois H := by
  let N := ψ.ker
  refine ⟨fixedField N, inferInstance, (fixedField N).algebra', inferInstance,
    IsGalois.of_fixedField_normal_subgroup N, ⟨?_⟩⟩
  exact (IsGalois.normalAutEquivQuotient N).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

/-- The inverse Galois property is closed under quotients: if `G` is an inverse Galois group
and `f : G →* H` is a surjective group homomorphism, then `H` is also an inverse Galois group. -/
theorem of_surjective (hG : IsInverseGalois G)
    (f : G →* H) (hf : Function.Surjective f) : IsInverseGalois H := by
  obtain ⟨L, _, _, _, _, ⟨φ⟩⟩ := hG
  exact of_surjective_galHom L (f.comp φ.toMonoidHom) (hf.comp φ.surjective)

/-- The inverse Galois property is closed under quotients: if `G` is an inverse Galois group
and `N` is a normal subgroup, then the quotient `G ⧸ N` is also an inverse Galois group.

This is the special case of `of_surjective` for the canonical projection `G →* G ⧸ N`. -/
theorem quotient (hG : IsInverseGalois G) (N : Subgroup G) [N.Normal] :
    IsInverseGalois (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- The trivial group is an inverse Galois group (realized by `ℚ` itself). -/
theorem unit : IsInverseGalois Unit := by
  refine ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  have : Unique Gal(ℚ/ℚ) := uniqueOfSubsingleton 1
  exact MulEquiv.ofUnique

end IsInverseGalois
