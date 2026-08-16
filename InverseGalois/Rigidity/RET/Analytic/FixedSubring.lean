/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A finite faithful action on a domain, and the Galois extension it produces

A finite group acting faithfully on a domain by ring automorphisms is a Galois group: the
invariants form a subring, every invariant element is by definition in the image of that subring,
and the action is faithful, which is exactly the definition of `IsGaloisGroup` for the extension of
rings.  Passing to fraction fields turns this into an honest Galois extension of fields with group
the acting group.

Nothing here is analytic.  It is the algebraic engine that turns a group of symmetries of a
covering into the Galois group of an extension of function fields: the only thing the analysis has
to supply is a ring of functions on which the deck group acts faithfully.

## Main results

* `Rigidity.RET.isGaloisGroup_fixedPoints` — a finite group acting faithfully on a ring is a Galois
  group for that ring over its invariants.
* `Rigidity.RET.isGaloisGroup_fractionRing` — the same for the fraction fields.
* `Rigidity.RET.isGalois_fractionRing` — the extension of fraction fields is Galois.
* `Rigidity.RET.mulEquivAlgEquiv_fractionRing` — the acting group is the Galois group.
-/

open Module

noncomputable section

namespace Rigidity.RET

section Ring

variable (B : Type*) [CommRing B] (G : Type*) [Group G] [MulSemiringAction G B]

/-- The invariants act centrally: multiplication by an invariant element commutes with the
action. -/
instance smulCommClass_fixedPoints : SMulCommClass G ↥(FixedPoints.subring B G) B :=
  ⟨fun g a b => by
    show g • ((a : B) * b) = (a : B) * (g • b)
    rw [smul_mul', a.2 g]⟩

/-- **A group acting faithfully on a ring is a Galois group for that ring over its invariants.**

Both requirements are immediate: the action is faithful by hypothesis, and an element fixed by the
whole group is by definition an element of the ring of invariants. -/
instance isGaloisGroup_fixedPoints [FaithfulSMul G B] :
    IsGaloisGroup G ↥(FixedPoints.subring B G) B where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩

end Ring

section Fraction

variable (B : Type*) [CommRing B] [IsDomain B]
variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]

attribute [local instance] FractionRing.liftAlgebra

/-- **The fraction field of a domain is a Galois extension of the fraction field of the invariants
of a finite faithful action, with that group as Galois group.** -/
theorem isGaloisGroup_fractionRing :
    letI := FractionRing.mulSemiringAction_of_isGaloisGroup G ↥(FixedPoints.subring B G) B
    IsGaloisGroup G (FractionRing ↥(FixedPoints.subring B G)) (FractionRing B) :=
  IsGaloisGroup.toFractionRing G ↥(FixedPoints.subring B G) B

/-- **The extension of fraction fields cut out by a finite faithful action is Galois.** -/
theorem isGalois_fractionRing :
    IsGalois (FractionRing ↥(FixedPoints.subring B G)) (FractionRing B) := by
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup G ↥(FixedPoints.subring B G) B
  haveI := isGaloisGroup_fractionRing B G
  exact IsGaloisGroup.isGalois G _ _

/-- **The acting group is the Galois group of the extension of fraction fields.** -/
def mulEquivAlgEquiv_fractionRing :
    G ≃* (FractionRing B ≃ₐ[FractionRing ↥(FixedPoints.subring B G)] FractionRing B) := by
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup G ↥(FixedPoints.subring B G) B
  haveI := isGaloisGroup_fractionRing B G
  exact IsGaloisGroup.mulEquivAlgEquiv G _ _

/-- **The degree of the extension of fraction fields is the order of the group.** -/
theorem finrank_fractionRing :
    Module.finrank (FractionRing ↥(FixedPoints.subring B G)) (FractionRing B) = Nat.card G := by
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup G ↥(FixedPoints.subring B G) B
  haveI := isGaloisGroup_fractionRing B G
  exact (IsGaloisGroup.card_eq_finrank G _ _).symm

end Fraction

end Rigidity.RET

end
