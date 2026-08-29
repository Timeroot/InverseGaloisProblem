/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Graded

/-!
# The complete cohomology is a functor of the representation

In each of the four ranges of degrees the map induced by a morphism of representations is built
from the same construction applied to the underlying linear map, so it takes the identity to the
identity and a composite to the composite.  The complete cohomology in a fixed degree is therefore
a functor of the representation, and an isomorphism of representations induces an isomorphism of
the complete cohomology in every degree.

That is what allows a computation to be transported along an identification of representations: a
representation isomorphic to one with no complete cohomology has none either.

## Main results

* `InverseGalois.CFT.Tate.tateMap_id`, `InverseGalois.CFT.Tate.tateMap_comp`: **the complete
  cohomology in a fixed degree is a functor of the representation.**
* `InverseGalois.CFT.Tate.tateMapIso`: **an isomorphism of representations induces an isomorphism
  of the complete cohomology.**
* `InverseGalois.CFT.Tate.isZero_tateModule_of_iso`: **a representation isomorphic to one with no
  complete cohomology has none either.**

## Tags

Tate cohomology, functoriality, isomorphism of representations
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### Functoriality -/

/-- **The complete cohomology takes the identity to the identity.** -/
theorem tateMap_id (A : Rep k G) (n : ℤ) : tateMap (𝟙 A) n = 𝟙 (tateModule A n) := by
  match n with
  | .ofNat 0 =>
    ext x
    obtain ⟨y, rfl⟩ := H0mk_surjective A.ρ x
    rfl
  | .ofNat (m + 1) => exact groupCohomology.map_id (B := A) (m + 1)
  | .negSucc 0 =>
    ext x
    refine Subtype.ext ?_
    obtain ⟨c, hc⟩ := x
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective A.ρ c
    rfl
  | .negSucc (m + 1) => exact groupHomology.map_id (A := A) (m + 1)

/-- **The complete cohomology takes a composite to the composite.** -/
theorem tateMap_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℤ) :
    tateMap (φ ≫ ψ) n = tateMap φ n ≫ tateMap ψ n := by
  match n with
  | .ofNat 0 =>
    ext x
    obtain ⟨y, rfl⟩ := H0mk_surjective A.ρ x
    rfl
  | .ofNat (m + 1) => exact groupCohomology.map_id_comp φ ψ (m + 1)
  | .negSucc 0 =>
    ext x
    refine Subtype.ext ?_
    obtain ⟨c, hc⟩ := x
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective A.ρ c
    rfl
  | .negSucc (m + 1) => exact groupHomology.map_id_comp φ ψ (m + 1)

/-- **An isomorphism of representations induces an isomorphism of the complete cohomology.** -/
def tateMapIso {A B : Rep k G} (e : A ≅ B) (n : ℤ) : tateModule A n ≅ tateModule B n where
  hom := tateMap e.hom n
  inv := tateMap e.inv n
  hom_inv_id := by rw [← tateMap_comp, e.hom_inv_id, tateMap_id]
  inv_hom_id := by rw [← tateMap_comp, e.inv_hom_id, tateMap_id]

/-- **A representation isomorphic to one with no complete cohomology has none either.** -/
theorem isZero_tateModule_of_iso {A B : Rep k G} (e : A ≅ B) (n : ℤ)
    (h : Limits.IsZero (tateModule B n)) : Limits.IsZero (tateModule A n) :=
  h.of_iso (tateMapIso e n)

end

end InverseGalois.CFT.Tate
