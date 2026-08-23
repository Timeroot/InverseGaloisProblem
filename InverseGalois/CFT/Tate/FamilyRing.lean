/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family
import InverseGalois.CFT.Tate.Mul

/-!
# A group acting on a family of rings, and on the units

The local factors of the group of ideles are the unit groups of the completions of a number field
at its places, and what a Galois automorphism carries from one place to another is not just a group
but a whole ring: the completion.  The transport data therefore lives at the level of rings, and
the family of unit groups inherits it.

This file records that inheritance.  A compatible system of ring isomorphisms along a group action
on the index set gives, on passing to units and writing the unit groups additively, a compatible
system in the sense of `InverseGalois.CFT.FamilyAction`, so the group acts on the sections of the
family of unit groups.  Along the way the transport of a family of rings along an equality of
indices is set up, together with the two facts about it that get used: it is the identity on the
values of a section, and it is continuous.

## Main definitions

* `InverseGalois.CFT.ringCast`: the transport of a family of rings along an equality of indices.
* `InverseGalois.CFT.RingFamilyAction`: a compatible system of ring isomorphisms along the action
  on the index set.
* `InverseGalois.CFT.RingFamilyAction.unitsFamily`: **the induced system on the unit groups.**

## Main results

* `InverseGalois.CFT.ringCast_apply_section`: the transport is the identity on the values of a
  section.
* `InverseGalois.CFT.continuous_ringCast`: the transport is continuous.

## Tags

group action, family of rings, units, transport, idele
-/

namespace InverseGalois.CFT

variable {X : Type*} (R : X → Type*)

/-! ### Transport of a family of rings -/

section Cast

variable [∀ x, CommRing (R x)]

/-- **The transport of a family of rings along an equality of indices.** -/
def ringCast {x y : X} (h : x = y) : R x ≃+* R y :=
  h.rec (motive := fun z _ => R x ≃+* R z) (RingEquiv.refl (R x))

@[simp]
theorem ringCast_rfl (x : X) : ringCast R (rfl : x = x) = RingEquiv.refl (R x) := rfl

/-- Transporting a section is evaluating it at the other index. -/
theorem ringCast_apply_section {x y : X} (h : x = y) (f : ∀ z, R z) : ringCast R h (f x) = f y := by
  subst h; rfl

/-- Two transports in a row are one transport. -/
theorem ringCast_trans_apply {x y z : X} (h : x = y) (h' : y = z) (a : R x) :
    ringCast R h' (ringCast R h a) = ringCast R (h.trans h') a := by
  subst h; subst h'; rfl

/-- **The transport of a family of topological rings is continuous.** -/
theorem continuous_ringCast [∀ x, TopologicalSpace (R x)] {x y : X} (h : x = y) :
    Continuous (ringCast R h) := by
  subst h; exact continuous_id

/-- The transport of the family of unit groups is the transport of the rings. -/
theorem famCast_units {x y : X} (h : x = y) (a : Additive (R x)ˣ) :
    famCast (fun z => Additive (R z)ˣ) h a
      = Additive.ofMul (Units.mapEquiv (ringCast R h).toMulEquiv (Additive.toMul a)) := by
  subst h
  exact congrArg Additive.ofMul (Units.ext rfl)

end Cast

/-! ### A compatible system of ring transports -/

variable (G : Type*) [Group G] [MulAction G X] [∀ x, CommRing (R x)]

/-- **A compatible system of ring isomorphisms for a family of rings indexed by a set with a group
action.**  Each group element carries the ring at an index isomorphically onto the ring at the
image index, the identity acting trivially and a product acting as the composite. -/
structure RingFamilyAction where
  /-- the isomorphism from the ring at an index to the ring at its image -/
  map : ∀ (g : G) (x : X), R x ≃+* R (g • x)
  /-- the identity transports along the equality expressing that it fixes the index -/
  map_one : ∀ (x : X) (a : R x), map 1 x a = ringCast R (one_smul G x).symm a
  /-- a product transports as the composite of the two transports -/
  map_mul : ∀ (g h : G) (x : X) (a : R x),
    map (g * h) x a = ringCast R (mul_smul g h x).symm (map g (h • x) (map h x a))

namespace RingFamilyAction

variable {R G} (F : RingFamilyAction R G)

/-- **The system induced on the unit groups**, written additively. -/
def unitsFamily : FamilyAction (fun x => Additive (R x)ˣ) G where
  map g x := MulEquiv.toAdditive (Units.mapEquiv (F.map g x).toMulEquiv)
  map_one x a := by
    rw [famCast_units]
    exact congrArg Additive.ofMul (Units.ext (F.map_one x _))
  map_mul g h x a := by
    rw [famCast_units]
    exact congrArg Additive.ofMul (Units.ext (F.map_mul g h x _))

@[simp]
theorem unitsFamily_map_apply (g : G) (x : X) (u : (R x)ˣ) :
    F.unitsFamily.map g x (Additive.ofMul u)
      = Additive.ofMul (Units.mapEquiv (F.map g x).toMulEquiv u) := rfl

end RingFamilyAction

end InverseGalois.CFT
