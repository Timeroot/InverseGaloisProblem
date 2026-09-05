/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Functorial
import InverseGalois.CFT.TateCohomology.TensorFunctor

/-!
# A retracted subrepresentation stays a subrepresentation in complete cohomology

A map of representations admitting a left inverse is carried by any functor to a map admitting a
left inverse, and a map admitting a left inverse is injective.  Complete cohomology in a fixed
degree is such a functor, and so is tensoring on the right with a fixed representation, so a map of
representations that is a retract remains injective after either operation or both.

That is what separates a local factor of the ideles from the units of its valuation ring once the
coefficients are twisted.  The units of the valuation ring of an unramified extension have complete
cohomology of their own after twisting, so the vanishing statement used for untwisted coefficients
is unavailable; what survives is that a uniformizer of the base field splits the valuation off the
local factor equivariantly, and a split injection stays injective wherever it is carried.

## Main results

* `InverseGalois.CFT.Tate.injective_tateMap_of_retraction`: **a map of representations with a left
  inverse induces an injection of the complete cohomology in every degree.**
* `InverseGalois.CFT.Tate.injective_tateMap_tensorHomLeft_of_retraction`: **the same after tensoring
  on the right with a fixed representation.**

## Tags

Tate cohomology, retraction, split monomorphism, tensor product, functoriality
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **A map of representations with a left inverse induces an injection of the complete cohomology
in every degree**: complete cohomology in a fixed degree is a functor, so it carries the left
inverse to a left inverse. -/
theorem injective_tateMap_of_retraction {A B : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ A)
    (h : φ ≫ ψ = 𝟙 A) (n : ℤ) : Function.Injective (tateMap φ n) := by
  have key : ∀ x : ↥(tateModule A n), tateMap ψ n (tateMap φ n x) = x := by
    intro x
    have h1 : tateMap ψ n (tateMap φ n x) = tateMap (φ ≫ ψ) n x := by
      rw [tateMap_comp]
      rfl
    rw [h1, h, tateMap_id]
    rfl
  intro x y hxy
  rw [← key x, ← key y, hxy]

/-- **A map of representations with a left inverse induces an injection of the complete cohomology
after tensoring on the right with a fixed representation**: tensoring is a functor too, so the left
inverse survives it. -/
theorem injective_tateMap_tensorHomLeft_of_retraction {A B : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ A)
    (h : φ ≫ ψ = 𝟙 A) (M : Rep k G) (n : ℤ) :
    Function.Injective (tateMap (tensorHomLeft M φ) n) :=
  injective_tateMap_of_retraction _ (tensorHomLeft M ψ)
    (by rw [tensorHomLeft_comp, h, tensorHomLeft_id]) n

end

end InverseGalois.CFT.Tate
