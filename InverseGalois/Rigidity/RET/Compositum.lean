/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DeckGroups

/-!
# The compositum of two covers of the line

Two covers of the line can always be placed inside one cover: embed both in an algebraic closure of
the line and take the compositum of the images.  Each cover is isomorphic to its image, so the two
sit inside the compositum as normal subcovers, and by construction they generate it.

## Main results

* `Rigidity.RET.LineCover.compositum` — two covers of the line sit inside a common cover, as
  `Rigidity.RET.LineCover.compositumLeft` and `Rigidity.RET.LineCover.compositumRight`.
* `Rigidity.RET.LineCover.compositumLeftEquiv`, `Rigidity.RET.LineCover.compositumRightEquiv` — the
  two subcovers are copies of the two covers.
* `Rigidity.RET.LineCover.compositumLeft_sup_compositumRight` — the two covers generate their
  compositum.
-/

open Polynomial IntermediateField

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

namespace LineCover

/-- An algebraic closure of the line, in which every cover of the line embeds. -/
abbrev closure : Type := AlgebraicClosure (RatFunc k)

/-- An embedding of a cover of the line into the algebraic closure of the line. -/
def embed (L : LineCover) : L.M →ₐ[RatFunc k] closure := IsAlgClosed.lift

/-- The image of a cover of the line in the algebraic closure of the line. -/
def image (L : LineCover) : IntermediateField (RatFunc k) closure := (L.embed).fieldRange

/-- A cover of the line is isomorphic to its image in the algebraic closure of the line. -/
def imageEquiv (L : LineCover) : L.M ≃ₐ[RatFunc k] (L.image : Type) :=
  AlgEquiv.ofInjectiveField L.embed

instance (L : LineCover) : FiniteDimensional (RatFunc k) (L.image : Type) :=
  LinearEquiv.finiteDimensional L.imageEquiv.toLinearEquiv

instance (L : LineCover) : IsGalois (RatFunc k) (L.image : Type) :=
  IsGalois.of_algEquiv L.imageEquiv

/-- **The compositum of two covers of the line**, a cover of the line containing copies of both. -/
def compositum (L₁ L₂ : LineCover) : LineCover :=
  LineCover.of ((L₁.image ⊔ L₂.image : IntermediateField (RatFunc k) closure) : Type)

/-- The first cover, as a subcover of the compositum. -/
def compositumLeft (L₁ L₂ : LineCover) :
    IntermediateField (RatFunc k) (L₁.compositum L₂).M :=
  IntermediateField.restrict (le_sup_left : L₁.image ≤ L₁.image ⊔ L₂.image)

/-- The second cover, as a subcover of the compositum. -/
def compositumRight (L₁ L₂ : LineCover) :
    IntermediateField (RatFunc k) (L₁.compositum L₂).M :=
  IntermediateField.restrict (le_sup_right : L₂.image ≤ L₁.image ⊔ L₂.image)

/-- The left subcover of the compositum is the first cover. -/
def compositumLeftEquiv (L₁ L₂ : LineCover) :
    ((L₁.compositumLeft L₂ : IntermediateField (RatFunc k) (L₁.compositum L₂).M) : Type)
      ≃ₐ[RatFunc k] L₁.M :=
  ((IntermediateField.liftAlgEquiv _).trans (IntermediateField.equivOfEq
    (IntermediateField.lift_restrict
      (le_sup_left : L₁.image ≤ L₁.image ⊔ L₂.image)))).trans L₁.imageEquiv.symm

/-- The right subcover of the compositum is the second cover. -/
def compositumRightEquiv (L₁ L₂ : LineCover) :
    ((L₁.compositumRight L₂ : IntermediateField (RatFunc k) (L₁.compositum L₂).M) : Type)
      ≃ₐ[RatFunc k] L₂.M :=
  ((IntermediateField.liftAlgEquiv _).trans (IntermediateField.equivOfEq
    (IntermediateField.lift_restrict
      (le_sup_right : L₂.image ≤ L₁.image ⊔ L₂.image)))).trans L₂.imageEquiv.symm

instance (L₁ L₂ : LineCover) :
    Normal (RatFunc k) ((L₁.compositumLeft L₂ : IntermediateField (RatFunc k)
      (L₁.compositum L₂).M) : Type) :=
  Normal.of_algEquiv (L₁.compositumLeftEquiv L₂).symm

instance (L₁ L₂ : LineCover) :
    Normal (RatFunc k) ((L₁.compositumRight L₂ : IntermediateField (RatFunc k)
      (L₁.compositum L₂).M) : Type) :=
  Normal.of_algEquiv (L₁.compositumRightEquiv L₂).symm

/-- **The two covers generate their compositum.** -/
theorem compositumLeft_sup_compositumRight (L₁ L₂ : LineCover) :
    L₁.compositumLeft L₂ ⊔ L₁.compositumRight L₂ = ⊤ := by
  refine IntermediateField.lift_injective (L₁.image ⊔ L₂.image) ?_
  rw [IntermediateField.lift_sup, compositumLeft, compositumRight,
    IntermediateField.lift_restrict, IntermediateField.lift_restrict,
    IntermediateField.lift_top]

end LineCover

end Rigidity.RET
