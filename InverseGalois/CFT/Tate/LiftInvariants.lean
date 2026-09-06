/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Graded

/-!
# Lifting invariants and the first map of the long exact sequence

The complete cohomology in degree zero of a representation of a finite group is the invariants
modulo the norms, so a map of representations along which every invariant of the target lifts to an
invariant of the source induces a surjection in degree zero.  When the map is the quotient map of a
short exact sequence the long exact sequence then forces the connecting map out of degree zero to
vanish, and the map induced in degree one by the inclusion of the sub is injective.

That is the shape of the comparison of a restricted product with the product containing it.  The
quotient of the one by the other is spanned by coordinates that a group with finitely many elements
can move only finitely far, so an invariant of the quotient is the class of a section of the product
which the group moves in finitely many coordinates only, and correcting the section on the finite
invariant set of those coordinates lifts the invariant.  The cohomology of the restricted product in
degree one then injects into that of the product.

## Main results

* `InverseGalois.CFT.Tate.surjective_tateMap_zero_of_lift`: **a map of representations along which
  every invariant lifts to an invariant induces a surjection of the complete cohomology in degree
  zero.**
* `InverseGalois.CFT.Tate.injective_tateMap_succ_of_surjective`: **the map induced by the inclusion
  of the sub of a short exact sequence is injective one degree above a degree in which the map
  induced by the quotient is surjective.**
* `InverseGalois.CFT.Tate.injective_tateMap_one_of_lift_invariants`: the two combined, in the degree
  the comparison of a restricted product with a product needs.

## Tags

Tate cohomology, long exact sequence, invariants, lifting, short exact sequence
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### Degree zero -/

/-- **A map of representations along which every invariant of the target lifts to an invariant of
the source induces a surjection of the complete cohomology in degree zero.**  In that degree the
complete cohomology is the invariants modulo the norms, and a class of the target is the class of an
invariant. -/
theorem surjective_tateMap_zero_of_lift {A C : Rep k G} (φ : A ⟶ C)
    (h : ∀ c : C.ρ.invariants, ∃ a : A.ρ.invariants, φ.hom.hom (a : A.V) = (c : C.V)) :
    Function.Surjective (tateMap φ 0) := by
  intro z
  obtain ⟨c, rfl⟩ := H0mk_surjective C.ρ z
  obtain ⟨a, ha⟩ := h c
  refine ⟨H0mk A.ρ a, ?_⟩
  show H0map φ.hom.hom (hom_equivariant φ) (H0mk A.ρ a) = H0mk C.ρ c
  rw [H0map_H0mk]
  exact congrArg (H0mk C.ρ) (Subtype.ext ha)

/-! ### One degree up -/

variable {X : ShortComplex (Rep k G)}

/-- **The map induced by the inclusion of the sub of a short exact sequence is injective one degree
above a degree in which the map induced by the quotient is surjective.**  The connecting map out of
that degree kills the whole of the complete cohomology of the quotient, so its image, which is the
kernel of the map one degree up, is trivial. -/
theorem injective_tateMap_succ_of_surjective (hX : X.ShortExact) (n : ℤ)
    (h : Function.Surjective (tateMap X.g n)) :
    Function.Injective (tateMap X.f (n + 1)) := by
  have hδ : ∀ y, tateδ hX n y = 0 := fun y => by
    obtain ⟨u, hu⟩ := h y
    exact (tateExact_map_δ hX n y).2 ⟨u, hu⟩
  have hker : ∀ z, (tateMap X.f (n + 1)) z = 0 → z = 0 := fun z hz => by
    obtain ⟨w, hw⟩ := (tateExact_δ_map hX n z).1 hz
    exact hw.symm.trans (hδ w)
  intro x y hxy
  refine sub_eq_zero.1 (hker (x - y) ?_)
  show (tateMap X.f (n + 1)).hom (x - y) = 0
  rw [map_sub]
  show (tateMap X.f (n + 1)) x - (tateMap X.f (n + 1)) y = 0
  rw [hxy, sub_self]

/-- **A short exact sequence whose quotient has every invariant lifted to the middle term has an
injection of the complete cohomology of the sub in degree one into that of the middle term.** -/
theorem injective_tateMap_one_of_lift_invariants (hX : X.ShortExact)
    (h : ∀ c : X.X₃.ρ.invariants, ∃ a : X.X₂.ρ.invariants,
      X.g.hom.hom (a : X.X₂.V) = (c : X.X₃.V)) :
    Function.Injective (tateMap X.f 1) :=
  injective_tateMap_succ_of_surjective hX 0 (surjective_tateMap_zero_of_lift X.g h)

end

end InverseGalois.CFT.Tate
