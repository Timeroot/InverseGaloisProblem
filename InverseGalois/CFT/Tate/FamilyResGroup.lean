/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTensorOrbit
import InverseGalois.CFT.TateCohomology.Pair

/-!
# A family of modules read on a subgroup of the acting group

A family of modules indexed by a set with a group action, together with a compatible system of
transports, is acted on by every subgroup of the group as well: the subgroup acts on the index set
by the restricted action, and the transport attached to an element of the subgroup is the transport
attached to it in the whole group.  Nothing has to be checked, because the two conditions a system
of transports satisfies — that the identity acts trivially and that a product acts as the composite
— are conditions on elements, and the elements of the subgroup are elements of the group.

Reading the family on a subgroup does not change the modules and does not change the sections, so
the group of sections carries the restriction of the action of the whole group, and likewise for the
subfamily of elements killed by an integer.  **Every statement about the complete cohomology of the
sections of a family is therefore available over a subgroup, with the orbits of the subgroup in
place of the orbits of the group and the stabiliser in the subgroup in place of the stabiliser in
the group.**  That is what a criterion formulated over a Sylow subgroup needs: the ideles of a
Galois extension are the sections of a family over the places, and a Sylow subgroup of the Galois
group moves those places in orbits of its own, with the intersection of the decomposition group and
the Sylow subgroup as the stabiliser at a place.

Two small compatibilities are recorded alongside, because that intersection has to be named and the
family of ideles is assembled from two halves.  The stabiliser of a point in a subgroup is a
subgroup of the stabiliser of that point in the whole group, by the map that forgets the membership
proof; and a product of two representations read on a subgroup is the product of the two read
there — the only thing to check being which of the two summands one is looking at.

## Main definitions

* `InverseGalois.CFT.FamilyAction.resGroup`: **a family of modules with a compatible system of
  transports, read on a subgroup of the acting group.**
* `InverseGalois.CFT.stabilizerSubgroupHom`: the stabiliser of a point in a subgroup, as a subgroup
  of the stabiliser of that point in the whole group.
* `InverseGalois.CFT.tateTensorTorsionResGroupEquiv`: **the complete cohomology of a subgroup with
  coefficients in the sections of a family killed by a prime, tensored with coefficients of finite
  rank over the field with that many elements, is the product over the orbits of the subgroup of
  the local contributions**, each read in the stabiliser in the subgroup of a chosen point of the
  orbit.

## Main results

* `InverseGalois.CFT.FamilyAction.familyAut_resGroup`: the action of the subgroup on the sections is
  the restriction of the action of the group.
* `InverseGalois.CFT.torsionRep_familyAut_resGroup`,
  `InverseGalois.CFT.orbitSectionsRep_resGroup`: the sections, and the sections killed by an
  integer, are the same representation read on the subgroup.
* `InverseGalois.CFT.resObj_pairRep`: a product of two representations read on a subgroup is the
  product of the two read there.

## Tags

family of modules, subgroup, orbit, Tate cohomology, Shapiro's lemma, Sylow subgroup, idele
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

noncomputable section

/-! ### Restricting the acting group -/

section ResGroup

variable {G X : Type*} [Group G] [MulAction G X] {M : X → Type*} [∀ x, AddCommGroup (M x)]

/-- **A family of modules with a compatible system of transports, read on a subgroup of the acting
group.**  The subgroup moves an index exactly as the group does, and transports the module there by
the same isomorphism. -/
def FamilyAction.resGroup (F : FamilyAction M G) (S : Subgroup G) : FamilyAction M ↥S where
  map g x := F.map (g : G) x
  map_one x a := F.map_one x a
  map_mul g h x a := F.map_mul (g : G) (h : G) x a

@[simp]
theorem FamilyAction.resGroup_map (F : FamilyAction M G) (S : Subgroup G) (g : ↥S) (x : X) :
    (F.resGroup S).map g x = F.map (g : G) x := rfl

/-- A transport for the restricted family is the transport for the family. -/
theorem FamilyAction.resGroup_transport (F : FamilyAction M G) (S : Subgroup G) {g : ↥S} {x y : X}
    (h : (g : G) • x = y) (a : M x) :
    (F.resGroup S).transport (g := g) h a = F.transport h a := rfl

/-- The restricted family moves a section exactly as the family does. -/
theorem FamilyAction.resGroup_toFun (F : FamilyAction M G) (S : Subgroup G) (g : ↥S)
    (f : ∀ x, M x) : (F.resGroup S).toFun g f = F.toFun (g : G) f := rfl

end ResGroup

/-! ### The stabiliser inside a subgroup -/

section Stabilizer

variable {G X : Type*} [Group G] [MulAction G X]

/-- **The stabiliser of a point in a subgroup, as a subgroup of the stabiliser of that point in the
whole group.**  An element of the subgroup fixing the point is an element of the group fixing it. -/
def stabilizerSubgroupHom (S : Subgroup G) (x : X) :
    ↥(stabilizer ↥S x) →* ↥(stabilizer G x) where
  toFun g := ⟨(g : ↥S), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_stabilizerSubgroupHom (S : Subgroup G) (x : X) (g : ↥(stabilizer ↥S x)) :
    (stabilizerSubgroupHom S x g : G) = ((g : ↥S) : G) := rfl

end Stabilizer

/-! ### A product of two representations, read on a subgroup -/

section PairRes

variable {k G : Type} [CommRing k] [Group G]

/-- **A product of two representations read on a subgroup is the product of the two read there.**
Only the two summands have to be compared, and each of them is unchanged. -/
theorem resObj_pairRep (S : Subgroup G) (A B : Rep k G) :
    resObj S (pairRep A B) = pairRep (resObj S A) (resObj S B) := by
  have h : pairFamily (resObj S A) (resObj S B) = fun b => resObj S (pairFamily A B b) := by
    funext b
    cases b <;> rfl
  show _ = piRep (pairFamily (resObj S A) (resObj S B))
  rw [h]
  rfl

end PairRes

/-! ### Restricting a representation along a homomorphism -/

section Comp

variable {G G' A : Type} [Group G] [Group G'] [AddCommGroup A]

/-- An action by additive automorphisms read along a homomorphism is the representation read along
that homomorphism. -/
theorem repOfAddAut_comp (φ : G →* AddAut A) (f : G' →* G) :
    repOfAddAut (φ.comp f) = (Action.res _ f).obj (repOfAddAut φ) := rfl

/-- The action induced on the elements killed by an integer, read along a homomorphism, is the
induced action of the composite. -/
theorem torsionAut_comp (φ : G →* AddAut A) (m : ℤ) (f : G' →* G) :
    torsionAut (φ.comp f) m = (torsionAut φ m).comp f := rfl

/-- The elements killed by an integer, as a representation, read along a homomorphism. -/
theorem torsionRep_comp (φ : G →* AddAut A) (m : ℤ) (f : G' →* G) :
    torsionRep (φ.comp f) m = (Action.res _ f).obj (torsionRep φ m) := rfl

end Comp

/-! ### The sections, read on a subgroup -/

section Sections

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]

/-- **The action of a subgroup on the sections of a family is the restriction of the action of the
group.** -/
theorem FamilyAction.familyAut_resGroup (F : FamilyAction M G) (S : Subgroup G) :
    (F.resGroup S).familyAut = F.familyAut.comp S.subtype := rfl

/-- **The elements of a family killed by an integer, read on a subgroup**, are the elements killed
by that integer of the family read on the subgroup. -/
theorem FamilyAction.resGroup_torsion (F : FamilyAction M G) (S : Subgroup G) (m : ℤ) :
    (F.torsion m).resGroup S = (F.resGroup S).torsion m := rfl

/-- **The sections of a family read on a subgroup are the sections of the family, read there.** -/
theorem orbitSectionsRep_resGroup (F : FamilyAction M G) (S : Subgroup G) :
    orbitSectionsRep (F.resGroup S) = resObj S (orbitSectionsRep F) := rfl

/-- **The sections of a family killed by an integer, read on a subgroup, are the sections killed by
that integer, read there.** -/
theorem torsionRep_familyAut_resGroup (F : FamilyAction M G) (S : Subgroup G) (m : ℤ) :
    torsionRep (F.resGroup S).familyAut m = resObj S (torsionRep F.familyAut m) := rfl

end Sections

/-! ### The orbit decomposition over a subgroup -/

section Orbits

variable {G X : Type} [Group G] [MulAction G X] [Finite G] {M : X → Type}
  [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (S : Subgroup G) (W : Rep ℤ G) {p d : ℕ}
  [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  (x₀ : ∀ ω : orbitRel.Quotient ↥S X, ω.orbit) {H : orbitRel.Quotient ↥S X → Subgroup ↥S}
  (hH : ∀ (ω : orbitRel.Quotient ↥S X) (g : ↥S), g • x₀ ω = x₀ ω → g ∈ H ω)
  (hH' : ∀ (ω : orbitRel.Quotient ↥S X) (g : ↥(H ω)), (g : ↥S) • x₀ ω = x₀ ω)

include e hH hH' in
/-- **The complete cohomology of a subgroup with coefficients in the sections of a family killed by
a prime, tensored with coefficients of finite rank over the field with that many elements, is the
product over the orbits of the subgroup of the local contributions.**  The subgroup moves the index
set in orbits of its own, generally smaller than those of the whole group, and the contribution of
one of them is read in the stabiliser there, which is the intersection of the subgroup with the
stabiliser in the whole group. -/
def tateTensorTorsionResGroupEquiv (n : ℤ) :
    tateModule (tensorObj (resObj S (torsionRep F.familyAut (p : ℤ))) (resObj S W)) n ≃+
      ∀ ω : orbitRel.Quotient ↥S X,
        tateModule (tensorObj (torsionRep (stabAut (x₀ ω) (hH' ω)
          (orbitFamily (F.resGroup S) ω)) (p : ℤ)) (resObj (H ω) (resObj S W))) n :=
  tateTensorTorsionEquiv (F.resGroup S) (resObj S W) e x₀ hH hH' n

end Orbits

end

end InverseGalois.CFT
