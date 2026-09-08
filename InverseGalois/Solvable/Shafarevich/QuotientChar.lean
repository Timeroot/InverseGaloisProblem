/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Automorphisms of a quotient by a characteristic subgroup

A characteristic subgroup is preserved by every automorphism of the ambient group, so every
automorphism descends to the quotient, and it descends functorially: the automorphisms of the
quotient by a characteristic subgroup receive the automorphisms of the group itself.  A group with
operators therefore hands its operators down to every quotient by a characteristic subgroup, which
is how a central series is made into a tower of groups with the same operators.

## Main definitions

* `Shafarevich.quotientChar` — **an automorphism of a group descends to the quotient by a
  characteristic subgroup**, functorially.

## Tags

characteristic subgroup, quotient group, automorphism, group with operators
-/

namespace Shafarevich

/-- **An automorphism of a group descends to the quotient by a characteristic subgroup.**

A characteristic subgroup is preserved by every automorphism, so every automorphism induces an
automorphism of the quotient, functorially. -/
def quotientChar {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [N.Characteristic] :
    MulAut G →* MulAut (G ⧸ N) where
  toFun e := QuotientGroup.congr N N e (Subgroup.characteristic_iff_map_eq.mp ‹_› e)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' _ _ := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

@[simp]
theorem quotientChar_mk {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [N.Characteristic]
    (e : MulAut G) (x : G) :
    quotientChar N e (QuotientGroup.mk x) = QuotientGroup.mk (e x) :=
  rfl

end Shafarevich
