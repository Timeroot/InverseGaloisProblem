/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Quotient

/-!
# The quotient acting on an additive module

A tensor product of two modules over a group is an additive group, and the group acts on it
factor by factor.  When a subgroup acts trivially the quotient by that subgroup acts instead, and
this file records that passage for an additive module: the condition is again that each element of
the subgroup fixes every point, and the action of the quotient is the one for which the projection
to the quotient is equivariant.

The multiplicative form of the same passage is already available, and the two are used side by
side: the coefficients of a lifting problem and their cohomology are written multiplicatively,
while the tensor product which computes that cohomology is written additively.

## Main definitions

* `InverseGalois.CFT.AddActsTrivially`: a subgroup acting trivially on an additive module.
* `InverseGalois.CFT.quotientDistribMulAction`: **the action of the quotient by a subgroup acting
  trivially on an additive module.**

## Main results

* `InverseGalois.CFT.quotientAddMk_smul`: the quotient acts as the group does.

## Tags

group action, additive, quotient, trivial action
-/

namespace InverseGalois.CFT

/-! ### A subgroup acting trivially on an additive module -/

section AddActsTrivially

/-- A subgroup of a group acting on an additive commutative group *acts trivially* when each of its
elements fixes every point.  This is the condition under which the quotient by the subgroup
acts. -/
class AddActsTrivially {G : Type*} [Group G] (N : Subgroup G) (T : Type*) [AddCommGroup T]
    [DistribMulAction G T] : Prop where
  /-- Each element of the subgroup fixes every point. -/
  smul_eq_self : ∀ n ∈ N, ∀ t : T, n • t = t

variable {G : Type*} [Group G] (N : Subgroup G) (T : Type*) [AddCommGroup T]
  [DistribMulAction G T] [AddActsTrivially N T] [N.Normal]

/-- The additive automorphisms of an additive module defined by the quotient by a subgroup acting
trivially. -/
def quotientAddAut : G ⧸ N →* AddAut T :=
  QuotientGroup.lift N (DistribMulAction.toAddAut G T) fun n hn =>
    AddEquiv.ext fun t => AddActsTrivially.smul_eq_self n hn t

/-- **The action of the quotient by a subgroup acting trivially on an additive module.** -/
instance quotientDistribMulAction : DistribMulAction (G ⧸ N) T :=
  DistribMulAction.compHom T (quotientAddAut N T)

variable {N T}

/-- The quotient acts as the group does. -/
theorem quotientAddMk_smul (g : G) (t : T) : (QuotientGroup.mk g : G ⧸ N) • t = g • t := rfl

end AddActsTrivially

end InverseGalois.CFT
