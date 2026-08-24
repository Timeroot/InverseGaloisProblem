/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Sections of a family of modules over a set with a group action

The group of ideles of a number field is a product of local factors indexed by the places, and the
Galois group permutes the places while carrying each factor isomorphically onto the factor at the
image place.  A product like that is not a module in the naive sense: the factors are genuinely
different types, and an automorphism does not act on any one of them.  What it acts on is the group
of *sections* of the family, and the action is assembled from the transport isomorphisms between
the factors.

This file sets up that assembly once and for all.  The data is a family `M` of additive groups
indexed by a set `X` carrying an action of a group `G`, together with isomorphisms
`M x ≃+ M (g • x)` compatible with the identity and with products; the output is an action of `G`
on the additive group `∀ x, M x` of sections.  The only subtlety is bookkeeping: the module at
`(g * h) • x` and the module at `g • h • x` are equal but not syntactically so, and the transport
`famCast` along an equality of indices is what mediates between them.

The convenient primitive is not the transport isomorphism itself but the isomorphism
`FamilyAction.transport` attached to a group element together with a *proof* that it carries one
index to another.  Two such compose to the one attached to the product, the identity gives the
identity, and equal group elements give equal isomorphisms; the whole calculus of casts is
absorbed into those three statements.

## Main definitions

* `InverseGalois.CFT.famCast`: the transport of a family along an equality of indices.
* `InverseGalois.CFT.FamilyAction`: a compatible system of transport isomorphisms along the action
  on the index set.
* `InverseGalois.CFT.FamilyAction.transport`: the transport attached to a group element carrying
  one index to another.
* `InverseGalois.CFT.FamilyAction.familyAut`: **the resulting action on the group of sections.**

## Main results

* `InverseGalois.CFT.FamilyAction.transport_trans`: transports compose.
* `InverseGalois.CFT.FamilyAction.toFun_smul`: the transported section at an image index is the
  transport of the section at the index.
* `InverseGalois.CFT.FamilyAction.familyAut_apply_smul`: the same, for the assembled action.
* `InverseGalois.CFT.FamilyAction.familyAut_eq_of_map`: **a criterion for recognising the image of a
  section**, checked index by index using the transport isomorphisms directly.

## Tags

group action, family of modules, sections, transport, idele
-/

namespace InverseGalois.CFT

variable {X : Type*} (M : X → Type*)

/-! ### Transport along an equality of indices -/

section Cast

variable [∀ x, AddCommGroup (M x)]

/-- **The transport of a family of additive groups along an equality of indices.**  Equal indices
give equal modules, and this is the resulting isomorphism between them. -/
def famCast {x y : X} (h : x = y) : M x ≃+ M y :=
  h.rec (motive := fun z _ => M x ≃+ M z) (AddEquiv.refl (M x))

@[simp]
theorem famCast_rfl (x : X) : famCast M (rfl : x = x) = AddEquiv.refl (M x) := rfl

@[simp]
theorem famCast_symm {x y : X} (h : x = y) : (famCast M h).symm = famCast M h.symm := by
  subst h; rfl

/-- Transporting a section is evaluating it at the other index. -/
theorem famCast_apply_section {x y : X} (h : x = y) (f : ∀ z, M z) : famCast M h (f x) = f y := by
  subst h; rfl

/-- Two transports in a row are one transport. -/
theorem famCast_trans_apply {x y z : X} (h : x = y) (h' : y = z) (a : M x) :
    famCast M h' (famCast M h a) = famCast M (h.trans h') a := by
  subst h; subst h'; rfl

end Cast

/-! ### A compatible system of transports -/

variable (G : Type*) [Group G] [MulAction G X] [∀ x, AddCommGroup (M x)]

/-- **A compatible system of transport isomorphisms for a family of additive groups indexed by a
set with a group action.**  Each group element carries the module at an index isomorphically onto
the module at the image index, the identity acting trivially and a product acting as the
composite. -/
structure FamilyAction where
  /-- the isomorphism from the module at an index to the module at its image -/
  map : ∀ (g : G) (x : X), M x ≃+ M (g • x)
  /-- the identity transports along the equality expressing that it fixes the index -/
  map_one : ∀ (x : X) (a : M x), map 1 x a = famCast M (one_smul G x).symm a
  /-- a product transports as the composite of the two transports -/
  map_mul : ∀ (g h : G) (x : X) (a : M x),
    map (g * h) x a = famCast M (mul_smul g h x).symm (map g (h • x) (map h x a))

namespace FamilyAction

variable {M G} (F : FamilyAction M G)

/-- Transporting the module at one index and then moving the index by an equality is the same as
moving the index first. -/
theorem map_famCast (g : G) {x y : X} (h : x = y) (a : M x) :
    F.map g y (famCast M h a) = famCast M (congrArg (fun z => g • z) h) (F.map g x a) := by
  subst h; rfl

/-! ### Transport along a group element carrying one index to another -/

/-- **The transport attached to a group element together with a proof that it carries one index to
another.**  This is the transport isomorphism of the family followed by the identification of the
image index with the target index. -/
def transport {g : G} {x y : X} (h : g • x = y) : M x ≃+ M y :=
  (F.map g x).trans (famCast M h)

theorem transport_apply {g : G} {x y : X} (h : g • x = y) (a : M x) :
    F.transport h a = famCast M h (F.map g x a) := rfl

/-- **Equal group elements transport equally.** -/
theorem transport_congr {g g' : G} (hg : g = g') {x y : X} (h : g • x = y) (h' : g' • x = y)
    (a : M x) : F.transport h a = F.transport h' a := by
  subst hg; rfl

/-- **The identity transports along the equality of indices it induces.** -/
theorem transport_one {x y : X} (h : (1 : G) • x = y) (a : M x) :
    F.transport h a = famCast M ((one_smul G x).symm.trans h) a := by
  rw [transport_apply, F.map_one, famCast_trans_apply]

/-- **The identity transports trivially.** -/
theorem transport_one_self (x : X) (a : M x) : F.transport (one_smul G x) a = a := by
  rw [transport_one]
  rfl

/-- **Two transports in a row are the transport by the product.** -/
theorem transport_trans {g h : G} {x y z : X} (h₁ : h • x = y) (h₂ : g • y = z)
    (h₃ : (g * h) • x = z) (a : M x) :
    F.transport h₂ (F.transport h₁ a) = F.transport h₃ a := by
  rw [transport_apply, transport_apply, transport_apply, F.map_famCast, famCast_trans_apply,
    F.map_mul, famCast_trans_apply]

/-- Moving the source index of a transport by an equality. -/
theorem transport_famCast {g : G} {x x' y : X} (e : x = x') (h : g • x' = y) (a : M x)
    (h' : g • x = y) : F.transport h (famCast M e a) = F.transport h' a := by
  subst e; rfl

/-! ### The action on the group of sections -/

/-- **The transport of a section of the family by a group element.**  The value at an index is the
transport of the value at the index moved back by the inverse. -/
def toFun (g : G) (f : ∀ x, M x) (x : X) : M x :=
  F.transport (smul_inv_smul g x) (f (g⁻¹ • x))

/-- **The transported section, evaluated at an index reached from another one.** -/
theorem toFun_eq_transport {g : G} {x y : X} (h : g • y = x) (f : ∀ z, M z) :
    F.toFun g f x = F.transport h (f y) := by
  have e : y = g⁻¹ • x := by rw [← h, inv_smul_smul]
  subst e
  rfl

/-- **The transported section at an image index is the transport of the section at the index.** -/
theorem toFun_smul (g : G) (f : ∀ x, M x) (x : X) :
    F.toFun g f (g • x) = F.transport (rfl : g • x = g • x) (f x) :=
  F.toFun_eq_transport rfl f

theorem toFun_add (g : G) (f₁ f₂ : ∀ x, M x) :
    F.toFun g (f₁ + f₂) = F.toFun g f₁ + F.toFun g f₂ := by
  funext x
  simp [toFun]

theorem toFun_one (f : ∀ x, M x) : F.toFun (1 : G) f = f := by
  funext x
  rw [F.toFun_eq_transport (one_smul G x) f, transport_one_self]

theorem toFun_mul (g h : G) (f : ∀ x, M x) :
    F.toFun (g * h) f = F.toFun g (F.toFun h f) := by
  funext x
  obtain ⟨y, rfl⟩ : ∃ y, g • h • y = x := ⟨h⁻¹ • g⁻¹ • x, by simp⟩
  rw [F.toFun_eq_transport (mul_smul g h y) f,
    F.toFun_eq_transport (rfl : g • h • y = g • h • y) (F.toFun h f),
    F.toFun_eq_transport (rfl : h • y = h • y) f,
    F.transport_trans (rfl : h • y = h • y) (rfl : g • h • y = g • h • y) (mul_smul g h y)]

/-- **The action of a group element on the group of sections of the family.** -/
def aut (g : G) : (∀ x, M x) ≃+ (∀ x, M x) where
  toFun := F.toFun g
  invFun := F.toFun g⁻¹
  left_inv f := by rw [← F.toFun_mul, inv_mul_cancel, F.toFun_one]
  right_inv f := by rw [← F.toFun_mul, mul_inv_cancel, F.toFun_one]
  map_add' := F.toFun_add g

@[simp]
theorem aut_apply (g : G) (f : ∀ x, M x) : F.aut g f = F.toFun g f := rfl

/-- **The action of the group on the sections of the family.** -/
def familyAut : G →* AddAut (∀ x, M x) where
  toFun := F.aut
  map_one' := by
    ext f x
    exact congrFun (F.toFun_one f) x
  map_mul' g h := by
    ext f x
    exact congrFun (F.toFun_mul g h f) x

@[simp]
theorem familyAut_apply (g : G) (f : ∀ x, M x) : F.familyAut g f = F.toFun g f := rfl

/-- **The action on sections, evaluated at an index reached from another one.** -/
theorem familyAut_apply_eq_transport {g : G} {x y : X} (h : g • y = x) (f : ∀ z, M z) :
    F.familyAut g f x = F.transport h (f y) :=
  F.toFun_eq_transport h f

/-- **A section is the image of another one when the transport isomorphisms carry the value at each
index to the value at the translated index.**  This is the convenient criterion for recognising the
action on sections: it is stated forwards, at the index itself, rather than backwards at the
translate, so no inverse ever appears. -/
theorem familyAut_eq_of_map (g : G) (s s' : ∀ x, M x) (h : ∀ x, F.map g x (s x) = s' (g • x)) :
    F.familyAut g s = s' := by
  funext x
  rw [F.familyAut_apply_eq_transport (smul_inv_smul g x) s, FamilyAction.transport_apply, h,
    famCast_apply_section]

end FamilyAction

end InverseGalois.CFT
