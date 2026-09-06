/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Injectivity on second cohomology from a statement about cocycles

A class in second cohomology is the class of a two-cocycle, and it vanishes exactly when that
cocycle is a coboundary.  A map of representations is therefore injective on second cohomology as
soon as it reflects coboundaries: whenever the image of a two-cocycle is a coboundary, the cocycle
itself is one.  This is the converse packaging of the statement that an injection on second
cohomology detects coboundaries, and it is the shape in which an injectivity statement is produced
by an explicit computation with cochains.

## Main results

* `InverseGalois.CFT.injective_map_H2_of_forall_mem_coboundaries₂`: **a map of representations
  which reflects coboundaries in degree two is injective on second cohomology.**

## Tags

group cohomology, two-cocycle, coboundary, representation, injective
-/

open CategoryTheory groupCohomology

namespace InverseGalois.CFT

variable {k G : Type} [CommRing k] [Group G] {A B : Rep k G}

/-- **A map of representations which reflects coboundaries in degree two is injective on second
cohomology.**  A class in the kernel is the class of a two-cocycle whose image is a coboundary, so
the cocycle is a coboundary and the class vanishes. -/
theorem injective_map_H2_of_forall_mem_coboundaries₂ (φ : A ⟶ B)
    (h : ∀ a : G × G → A, a ∈ cocycles₂ A →
      (fun p : G × G => φ.hom (a p)) ∈ coboundaries₂ B → a ∈ coboundaries₂ A) :
    Function.Injective ((groupCohomology.functor k G 2).map φ).hom := by
  rw [injective_iff_map_eq_zero]
  intro z
  induction z using H2_induction_on with
  | @h ζ =>
  intro hz
  replace hz : groupCohomology.map (MonoidHom.id G) φ 2 (H2π A ζ) = 0 := hz
  rw [H2π_comp_map_apply, H2π_eq_zero_iff] at hz
  rw [H2π_eq_zero_iff]
  refine h _ ζ.2 ?_
  simpa using hz

end InverseGalois.CFT
