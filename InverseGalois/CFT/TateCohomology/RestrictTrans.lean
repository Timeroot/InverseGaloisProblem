/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.GroupCongr
import InverseGalois.CFT.TateCohomology.TateClassCount

/-!
# Reading a representation on a subgroup of a subgroup

A subgroup of a subgroup is a subgroup, but not on the nose: a subgroup of a subgroup is a group of
pairs, an element of the smaller subgroup together with the proof that it lies in the larger one,
whereas its image in the ambient group is a group of elements of that group.  The two are
isomorphic, by the map that forgets the inner proof, and a representation of the ambient group read
on either of them is the same representation of the ambient group read along the same homomorphism.

Complete cohomology transports along an isomorphism of groups, so the complete cohomology of a
subgroup of a subgroup with coefficients in a representation read twice is the complete cohomology
of the image subgroup with coefficients in the representation read once.  In particular a count made
for the subgroups of the ambient group — the vanishing in degree one, the finiteness in degree two
and the bound on the number of elements there — is a count for the subgroups of a subgroup.

That is exactly what the classical hypotheses of Tate's theorem need on a subgroup of a subgroup,
because the remaining hypothesis, that the restricted class be annihilated by no proper multiple of
the order, is about the order of the class alone and passes from the ambient group to a subgroup and
then to a subgroup of it without any transport at all.  So **a representation of a finite group
whose complete cohomology satisfies the count on every subgroup satisfies the hypotheses of Tate's
theorem, for the class restricted to a subgroup, on every subgroup of that subgroup** — which is
what lets a construction available for a group with a fundamental class be run over a subgroup of
it.

## Main definitions

* `InverseGalois.CFT.Tate.subgroupTransEquiv`: a subgroup of a subgroup is isomorphic to its image
  in the ambient group.
* `InverseGalois.CFT.Tate.resTransHom`: a representation of the ambient group read on a subgroup of
  a subgroup is the representation read on the image subgroup, along that isomorphism.
* `InverseGalois.CFT.Tate.resTransTateOne`, `InverseGalois.CFT.Tate.resTransTateTwo`: the induced
  identifications of the complete cohomology in degrees one and two.

## Main results

* `InverseGalois.CFT.Tate.isTateClassTwo_resObj_of_card`: **the classical hypotheses of Tate's
  theorem for a class restricted to a subgroup hold on every subgroup of that subgroup**, as soon
  as the count holds on every subgroup of the ambient group and the class is annihilated by exactly
  the multiples of the order of that group.

## Tags

Tate cohomology, Tate's theorem, subgroup, restriction, fundamental class
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

universe u

noncomputable section

/-! ### A subgroup of a subgroup -/

section Trans

variable {k G : Type u} [CommRing k] [Group G] (H : Subgroup G) (Q : Subgroup ↥H) (A : Rep k G)

/-- **A subgroup of a subgroup is isomorphic to its image in the ambient group**, by the map that
forgets the proof of membership in the larger subgroup. -/
def subgroupTransEquiv : ↥Q ≃* ↥(Q.map H.subtype) :=
  Q.equivMapOfInjective H.subtype H.subtype_injective

/-- **A representation of a group read on a subgroup of a subgroup is the representation read on
the image of that subgroup in the group**, along the isomorphism of the two: both are the
representation read along the same homomorphism to the group. -/
def resTransHom :
    (Action.res _ ((subgroupTransEquiv H Q : ↥Q ≃* ↥(Q.map H.subtype)) : ↥Q →* _)).obj
      (resObj (Q.map H.subtype) A) ⟶ resObj Q (resObj H A) where
  hom := ModuleCat.ofHom LinearMap.id
  comm := fun _ => rfl

variable [Finite G]

/-- **The complete cohomology in degree one of a subgroup of a subgroup is that of the image of the
subgroup in the group.** -/
def resTransTateOne :
    tateModule (resObj (Q.map H.subtype) A) 1 ≅ tateModule (resObj Q (resObj H A)) 1 :=
  tateOneCongr (subgroupTransEquiv H Q) (resTransHom H Q A) Function.bijective_id

/-- **The complete cohomology in degree two of a subgroup of a subgroup is that of the image of the
subgroup in the group.** -/
def resTransTateTwo :
    tateModule (resObj (Q.map H.subtype) A) 2 ≅ tateModule (resObj Q (resObj H A)) 2 :=
  tateTwoCongr (subgroupTransEquiv H Q) (resTransHom H Q A) Function.bijective_id

end Trans

/-! ### Tate's hypotheses on a subgroup of a subgroup -/

section Count

variable {G : Type} [Group G] [Finite G] {A : Rep ℤ G} {α : tateModule A 2}

/-- **The classical hypotheses of Tate's theorem for a class restricted to a subgroup hold on every
subgroup of that subgroup**, as soon as the complete cohomology of the representation vanishes in
degree one and is finite with at most as many elements as the subgroup in degree two, on every
subgroup of the ambient group, and the class is annihilated by exactly the multiples of the order
of that group.  A subgroup of the subgroup is isomorphic to its image in the ambient group, so the
count is available there; the order of the doubly restricted class is controlled twice over by the
order of the class one started with. -/
theorem isTateClassTwo_resObj_of_card
    (h1 : ∀ S : Subgroup G, Limits.IsZero (tateModule (resObj S A) 1))
    (hfin : ∀ S : Subgroup G, Finite ↥(tateModule (resObj S A) 2))
    (hcard : ∀ S : Subgroup G, Nat.card ↥(tateModule (resObj S A) 2) ≤ Nat.card ↥S)
    (hα : ∀ m : ℤ, m • α = 0 → (Nat.card G : ℤ) ∣ m)
    (H : Subgroup G) (Q : Subgroup ↥H) :
    IsTateClassTwo Q (resObj H A) (tateRes H A 2 α) := by
  have hcardQ : Nat.card ↥(Q.map H.subtype) = Nat.card ↥Q :=
    (Nat.card_congr (subgroupTransEquiv H Q).toEquiv).symm
  refine isTateClassTwo_of_card_le Q ?_ ?_ ?_ fun _ hm => dvd_of_zsmul_tateRes_eq_zero hα hm
  · exact (h1 (Q.map H.subtype)).of_iso (resTransTateOne H Q A).symm
  · haveI := hfin (Q.map H.subtype)
    exact Finite.of_equiv _ (resTransTateTwo H Q A).toLinearEquiv.toEquiv
  · have h := hcard (Q.map H.subtype)
    rwa [Nat.card_congr (resTransTateTwo H Q A).toLinearEquiv.toEquiv, hcardQ] at h

end Count

end

end InverseGalois.CFT.Tate
