/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Detecting coboundaries along an injection of second cohomology

A map of representations which is injective on second cohomology reflects triviality of classes:
a two-cocycle whose image is a coboundary is itself a coboundary.  This is the shape in which an
injectivity statement coming from a long exact sequence is used, since a cocycle is an explicit
function while a cohomology class is not.

## Main results

* `InverseGalois.CFT.mem_coboundaries₂_of_injective_map`: **a two-cocycle whose image under a map
  of representations injective on second cohomology is a coboundary is a coboundary.**

## Tags

group cohomology, two-cocycle, coboundary, representation
-/

open CategoryTheory groupCohomology

namespace InverseGalois.CFT

variable {k G : Type} [CommRing k] [Group G] {A B : Rep k G}

/-- **A two-cocycle whose image under a map of representations injective on second cohomology is a
coboundary is itself a coboundary.**  The image of the class of the cocycle is the class of the
image, so it vanishes, and injectivity carries the vanishing back. -/
theorem mem_coboundaries₂_of_injective_map (φ : A ⟶ B)
    (hinj : Function.Injective ((groupCohomology.functor k G 2).map φ).hom)
    {a : G × G → A} (ha : a ∈ cocycles₂ A)
    (hb : (fun p : G × G => φ.hom (a p)) ∈ coboundaries₂ B) :
    a ∈ coboundaries₂ A := by
  have h0 : H2π A ⟨a, ha⟩ = 0 := by
    refine hinj ?_
    rw [map_zero]
    show groupCohomology.map (MonoidHom.id G) φ 2 (H2π A ⟨a, ha⟩) = 0
    rw [H2π_comp_map_apply, H2π_eq_zero_iff]
    simpa using hb
  simpa using (H2π_eq_zero_iff (A := A) ⟨a, ha⟩).1 h0

end InverseGalois.CFT
