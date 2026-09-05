/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family

/-!
# The family with the same group at every index

The simplest family of abelian groups over a set with a group action is the one with a single group
repeated at every index, the transports all being the identity.  Its sections are just the functions
from the index set to that group, and the action assembled from the transports is the permutation
action: a group element moves a function by moving its argument backwards.

This is the family that measures the valuations of an idele.  The valuation at a finite place of a
number field is an integer whatever the place is, and an automorphism of the field carries the
valuation at a place to the valuation at the image place, so the vector of valuations of an idele is
a section of the family with a copy of the integers at every place, equivariantly.

## Main definitions

* `InverseGalois.CFT.constFamily`: **the family with the same group at every index.**

## Main results

* `InverseGalois.CFT.constFamily_familyAut_apply`: **the assembled action is the permutation action
  on functions.**
* `InverseGalois.CFT.constFamily_familyAut_apply_smul`: the same, read forwards at a translated
  index.
* `InverseGalois.CFT.FamilyAction.familyAut_zsmul_of_familyAut_eq`: **scaling an invariant section
  by a vector of integers is equivariant for the permutation action on the vector.**

## Tags

family of modules, sections, permutation module, group action
-/

namespace InverseGalois.CFT

/-! ### Transport in a constant family -/

section Cast

variable {X A : Type*} [AddCommGroup A]

/-- Transport along an equality of indices in a family with the same group at every index is the
identity. -/
theorem famCast_const {x y : X} (h : x = y) (a : A) : famCast (fun _ : X => A) h a = a := by
  subst h
  rfl

end Cast

/-! ### The constant family -/

section Const

variable (X : Type*) (A : Type*) [AddCommGroup A] (G : Type*) [Group G] [MulAction G X]

/-- **The family with the same group at every index**, the transports all being the identity.  Its
sections are the functions from the index set to that group. -/
def constFamily : FamilyAction (fun _ : X => A) G where
  map _ _ := AddEquiv.refl A
  map_one _ a := (famCast_const _ a).symm
  map_mul _ _ _ a := (famCast_const _ a).symm

variable {X A G}

@[simp]
theorem constFamily_map_apply (g : G) (x : X) (a : A) :
    (constFamily X A G).map g x a = a := rfl

theorem constFamily_transport {g : G} {x y : X} (h : g • x = y) (a : A) :
    (constFamily X A G).transport h a = a := by
  rw [FamilyAction.transport_apply, constFamily_map_apply, famCast_const]

/-- **The action assembled from the identity transports is the permutation action on functions.** -/
theorem constFamily_familyAut_apply (g : G) (f : X → A) (x : X) :
    (constFamily X A G).familyAut g f x = f (g⁻¹ • x) := by
  rw [(constFamily X A G).familyAut_apply_eq_transport (smul_inv_smul g x) f,
    constFamily_transport]

/-- **The permutation action, read forwards at a translated index.** -/
theorem constFamily_familyAut_apply_smul (g : G) (f : X → A) (x : X) :
    (constFamily X A G).familyAut g f (g • x) = f x := by
  rw [FamilyAction.familyAut_apply_smul, constFamily_map_apply]

end Const

/-! ### Scaling an invariant section -/

section Zsmul

variable {X : Type*} {M : X → Type*} [∀ x, AddCommGroup (M x)] {G : Type*} [Group G]
  [MulAction G X] (F : FamilyAction M G)

/-- **Scaling a section carried onto itself by a group element, by a vector of integers indexed by
the places, is equivariant for the permutation action on the vector.**  The transports are additive,
so they carry the scaled section at an index to the scaled section at the translated index, the
scalar following the index. -/
theorem FamilyAction.familyAut_zsmul_of_familyAut_eq {s : ∀ x, M x} {g : G}
    (hs : F.familyAut g s = s) (n : X → ℤ) :
    F.familyAut g (fun x => n x • s x) = fun x => (constFamily X ℤ G).familyAut g n x • s x := by
  refine F.familyAut_eq_of_map g _ _ fun x => ?_
  have hx := congrFun hs (g • x)
  rw [FamilyAction.familyAut_apply_smul] at hx
  show F.map g x (n x • s x) = (constFamily X ℤ G).familyAut g n (g • x) • s (g • x)
  rw [_root_.map_zsmul, constFamily_familyAut_apply_smul, hx]

end Zsmul

end InverseGalois.CFT
