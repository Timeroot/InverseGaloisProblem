/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family

/-!
# Restricting a family of modules to an invariant family of subgroups

The ideles of a number field that are units outside a finite set of places are, at each place, an
element of a subgroup of the local factor: the whole multiplicative group at the places in the set
and the units of the valuation ring at the others.  Both are subgroups of the same ambient group, so
the whole restricted product is the group of sections of a family of subgroups of the family of
local factors.

This file performs that restriction in general.  Given a family of modules with transports along a
group action and a family of subgroups carried onto one another by those transports, the transports
restrict and give an action of the group on the sections of the family of subgroups.  The only work
is bookkeeping: the transport of the family of subgroups along an equality of indices is the
restriction of the transport of the ambient family.

## Main definitions

* `InverseGalois.CFT.FamilyAction.restrictMap`: the transport of a family of modules, restricted to
  an invariant family of subgroups.
* `InverseGalois.CFT.FamilyAction.restrict`: **the restriction of a family of modules to an
  invariant family of subgroups.**

## Main results

* `InverseGalois.CFT.coe_famCast_addSubgroup`: the transport of the family of subgroups along an
  equality of indices is the restriction of the transport of the ambient family.

## Tags

family of modules, subgroup, sections, transport, idele
-/

namespace InverseGalois.CFT

variable {G X : Type*} [Group G] [MulAction G X]
  {M : X → Type*} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (N : ∀ x, AddSubgroup (M x))

/-! ### Transport of a family of subgroups along an equality of indices -/

/-- **The transport of a family of subgroups along an equality of indices is the restriction of the
transport of the ambient family.** -/
theorem coe_famCast_addSubgroup {x y : X} (h : x = y) (a : ↥(N x)) :
    ((famCast (fun z => ↥(N z)) h a : ↥(N y)) : M y) = famCast M h (a : M x) := by
  subst h
  rfl

/-! ### The restricted family -/

namespace FamilyAction

variable (hN : ∀ (g : G) (x : X), (N x).map (F.map g x).toAddMonoidHom = N (g • x))

include hN

/-- **The transport of a family of modules, restricted to an invariant family of subgroups.** -/
def restrictMap (g : G) (x : X) : ↥(N x) ≃+ ↥(N (g • x)) where
  toFun a := ⟨F.map g x a, by
    rw [← hN g x]
    exact ⟨a, a.2, rfl⟩⟩
  invFun b := ⟨(F.map g x).symm b, by
    have hb : (b : M (g • x)) ∈ (N x).map (F.map g x).toAddMonoidHom := by
      rw [hN g x]
      exact b.2
    obtain ⟨a, ha, hab⟩ := hb
    have hsymm : (F.map g x).symm (b : M (g • x)) = a := by
      rw [← hab]
      exact (F.map g x).symm_apply_apply a
    rw [hsymm]
    exact ha⟩
  left_inv a := Subtype.ext ((F.map g x).symm_apply_apply (a : M x))
  right_inv b := Subtype.ext ((F.map g x).apply_symm_apply (b : M (g • x)))
  map_add' a b := Subtype.ext (map_add (F.map g x) (a : M x) (b : M x))

@[simp]
theorem coe_restrictMap (g : G) (x : X) (a : ↥(N x)) :
    ((restrictMap F N hN g x a : ↥(N (g • x))) : M (g • x)) = F.map g x (a : M x) := rfl

/-- **The restriction of a family of modules to an invariant family of subgroups.** -/
def restrict : FamilyAction (fun x => ↥(N x)) G where
  map := restrictMap F N hN
  map_one x a := Subtype.ext <| by
    rw [coe_restrictMap, coe_famCast_addSubgroup]
    exact F.map_one x (a : M x)
  map_mul g h x a := Subtype.ext <| by
    rw [coe_restrictMap, coe_famCast_addSubgroup, coe_restrictMap, coe_restrictMap]
    exact F.map_mul g h x (a : M x)

@[simp]
theorem restrict_map (g : G) (x : X) : (F.restrict N hN).map g x = restrictMap F N hN g x := rfl

@[simp]
theorem coe_restrict_transport {g : G} {x y : X} (h : g • x = y) (a : ↥(N x)) :
    (((F.restrict N hN).transport h a : ↥(N y)) : M y) = F.transport h (a : M x) := by
  rw [FamilyAction.transport_apply, FamilyAction.transport_apply, coe_famCast_addSubgroup,
    restrict_map, coe_restrictMap]

end FamilyAction

end InverseGalois.CFT
