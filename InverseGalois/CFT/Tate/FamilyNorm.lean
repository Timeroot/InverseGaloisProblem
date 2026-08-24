/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyOrbits
import InverseGalois.CFT.Tate.NormSurjective

/-!
# Recognising a norm among the sections of a family

The sections of a family of modules over a disjoint union are the product of the sections over the
pieces, and reindexing the index set along an equivalence respecting the action does not change
them.  Both identifications commute with the actions, so a section is a norm as soon as its
restriction to every piece is one.

Applied to the decomposition of the index set into orbits, this is the passage from local to global
for the ideles that the vanishing of a Tate group is too crude to supply: a section is a norm as
soon as its restriction to the places above each place of the base field is one, whether or not the
local Tate groups vanish.

## Main results

* `InverseGalois.CFT.exists_normHom_familyAut_reindex`: reindexing the index set does not change
  which sections are norms.
* `InverseGalois.CFT.exists_normHom_familyAut_sigma`: **a section over a disjoint union is a norm as
  soon as its restriction to every piece is one.**
* `InverseGalois.CFT.exists_normHom_familyAut_orbits`: **a section is a norm as soon as its
  restriction to every orbit is one.**

## Tags

Tate cohomology, norm, family of modules, orbit, decomposition group, idele
-/

namespace InverseGalois.CFT

open MulAction

/-! ### Reindexing the index set -/

section Reindex

variable {G X X' : Type*} [Group G] [MulAction G X] [MulAction G X']
  {M : X → Type*} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)
  (e : X' ≃ X) (he : ∀ (g : G) (x' : X'), e (g • x') = g • e x')

/-- **Reindexing the index set does not change which sections are norms.** -/
theorem exists_normHom_familyAut_reindex (σ : G) (n : ℕ) {f : ∀ x : X, M x}
    (h : ∃ u, normHom ((F.reindex e he).familyAut σ) n u = reindexFamilyEquiv (M := M) e f) :
    ∃ u, normHom (F.familyAut σ) n u = f :=
  exists_normHom_of_addEquiv (reindexFamilyEquiv (M := M) e)
    (reindexFamilyEquiv_familyAut F e he σ) n h

end Reindex

/-! ### A disjoint union of index sets -/

section Sigma

variable {G Y : Type*} [Group G] {P : Y → Type*} [∀ y, MulAction G (P y)]
  {M : (Σ y, P y) → Type*} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)

/-- **A section over a disjoint union is a norm as soon as its restriction to every piece is
one.** -/
theorem exists_normHom_familyAut_sigma (σ : G) (n : ℕ) {f : ∀ x : Σ y, P y, M x}
    (h : ∀ y : Y, ∃ u, normHom ((F.sigmaFiber y).familyAut σ) n u = fun z : P y => f ⟨y, z⟩) :
    ∃ u, normHom (F.familyAut σ) n u = f :=
  exists_normHom_of_addEquiv (sigmaFamilyEquiv (M := M)) (sigmaFamilyEquiv_familyAut F σ) n
    (exists_normHom_piAut _ n h)

end Sigma

/-! ### The decomposition into orbits -/

section Orbits

variable {G X : Type*} [Group G] [MulAction G X]
  {M : X → Type*} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)

/-- **A section is a norm as soon as its restriction to every orbit is one.**  This is the passage
from the places above one place of the base field to all the places at once. -/
theorem exists_normHom_familyAut_orbits (σ : G) (n : ℕ) {f : ∀ x : X, M x}
    (h : ∀ ω : orbitRel.Quotient G X, ∃ u,
      normHom ((orbitFamily F ω).familyAut σ) n u = fun z : ω.orbit => f (z : X)) :
    ∃ u, normHom (F.familyAut σ) n u = f :=
  exists_normHom_familyAut_reindex F (selfEquivSigmaOrbits' G X).symm
    equivariant_selfEquivSigmaOrbits σ n
    (exists_normHom_familyAut_sigma _ σ n h)

end Orbits

end InverseGalois.CFT
