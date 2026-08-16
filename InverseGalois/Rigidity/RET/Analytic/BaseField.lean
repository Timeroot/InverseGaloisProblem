/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.BaseAlgebra

/-!
# The function field of a covering as an extension of the rational functions

The field of invariant functions on a covering of a punctured plane was identified with the
fraction field of the regular functions on the punctured plane; that fraction field is the field of
rational functions of the base coordinate.  Reading the base through that isomorphism turns the
Galois correspondence for a covering into a statement about an extension of `ℂ(T)`: the function
field of a connected covering with enough functions is a Galois extension of the rational functions
of the base coordinate, of degree the order of the deck group, with the deck group as Galois group.

## Main results

* `Rigidity.RET.isGaloisGroup_of_ringEquiv` — a Galois group stays one when the base ring is read
  through an isomorphism.
* `Rigidity.RET.isGalois_ratFunc_coverRing`, `Rigidity.RET.mulEquivAlgEquiv_ratFunc_coverRing`,
  `Rigidity.RET.finrank_ratFunc_coverRing` — the function field of a connected covering is a Galois
  extension of the rational functions of the base coordinate, with the deck group as Galois group
  and degree its order.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### Reading the base ring through an isomorphism -/

section Transport

variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B] [Algebra A B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

/-- **The base ring read through an isomorphism.** -/
def algebraOfRingEquiv (e : A' ≃+* A) : Algebra A' B :=
  ((algebraMap A B).comp e.toRingHom).toAlgebra

theorem algebraMap_algebraOfRingEquiv (e : A' ≃+* A) (x : A') :
    letI := algebraOfRingEquiv (B := B) e
    algebraMap A' B x = algebraMap A B (e x) := rfl

/-- **A Galois group stays one when the base ring is read through an isomorphism**: the two bases
have the same image in the big ring, and the definition sees nothing else. -/
theorem isGaloisGroup_of_ringEquiv (e : A' ≃+* A) [hG : IsGaloisGroup G A B] :
    letI := algebraOfRingEquiv (B := B) e
    IsGaloisGroup G A' B := by
  letI := algebraOfRingEquiv (B := B) e
  haveI := hG.commutes
  refine ⟨hG.faithful, ⟨fun g x b => ?_⟩, ⟨fun b hb => ?_⟩⟩
  · have hx : ∀ c : B, x • c = (e x : A) • c := fun c => by
      rw [Algebra.smul_def, Algebra.smul_def]
      rfl
    rw [hx b, hx (g • b)]
    exact smul_comm g (e x) b
  · obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant b hb
    refine ⟨e.symm a, ?_⟩
    show algebraMap A B (e (e.symm a)) = b
    rwa [e.apply_symm_apply]

end Transport

/-! ### The extension of the rational functions -/

section RatFunc

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {S : Finset ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]

attribute [local instance] FractionRing.liftAlgebra ratFuncAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The function field of a covering is an extension of the rational functions of the base
coordinate.** -/
def coverRatFuncAlgebra (hf : IsLocalHomeomorph f) (hrange : Set.range f = (↑S : Set ℂ)ᶜ) :
    Algebra (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) :=
  letI := baseAlgebra hf hrange
  haveI := isTorsionFree_coverRing hf hrange
  algebraOfRingEquiv (A := FractionRing (Localization.Away (punctPoly S)))
    (B := FractionRing ↥(coverRing hf S)) (fractionRingAwayAlgEquivRatFunc S).symm.toRingEquiv

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The deck group of a connected covering is a Galois group for its function field over the
rational functions of the base coordinate.** -/
theorem isGaloisGroup_ratFunc_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    letI := baseAlgebra hf hrange
    haveI := isGaloisGroup_coverRing hf hrange htrans hsep
    haveI := isTorsionFree_coverRing hf hrange
    letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
      (Localization.Away (punctPoly S)) ↥(coverRing hf S)
    letI := coverRatFuncAlgebra hf hrange
    IsGaloisGroup H (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) := by
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hsep
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  haveI := isGaloisGroup_fractionRing_coverRing hf hrange htrans hsep
  exact isGaloisGroup_of_ringEquiv (B := FractionRing ↥(coverRing hf S)) H
    (fractionRingAwayAlgEquivRatFunc S).symm.toRingEquiv

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The function field of a connected covering is a Galois extension of the rational functions of
the base coordinate**, provided every nontrivial deck transformation moves some function of
moderate growth. -/
theorem isGalois_ratFunc_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    letI := coverRatFuncAlgebra hf hrange
    IsGalois (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) := by
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hsep
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  letI := coverRatFuncAlgebra hf hrange
  haveI := isGaloisGroup_ratFunc_coverRing hf hrange htrans hsep
  exact IsGaloisGroup.isGalois H _ _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The deck group is the Galois group of the function field of the covering over the rational
functions of the base coordinate.** -/
def mulEquivAlgEquiv_ratFunc_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    letI := coverRatFuncAlgebra hf hrange
    H ≃* (FractionRing ↥(coverRing hf S) ≃ₐ[RatFunc ℂ] FractionRing ↥(coverRing hf S)) := by
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hsep
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  letI := coverRatFuncAlgebra hf hrange
  haveI := isGaloisGroup_ratFunc_coverRing hf hrange htrans hsep
  exact IsGaloisGroup.mulEquivAlgEquiv H _ _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The degree of the function field of a connected covering over the rational functions of the
base coordinate is the order of the deck group.** -/
theorem finrank_ratFunc_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    letI := coverRatFuncAlgebra hf hrange
    Module.finrank (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) = Nat.card H := by
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hsep
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  letI := coverRatFuncAlgebra hf hrange
  haveI := isGaloisGroup_ratFunc_coverRing hf hrange htrans hsep
  exact (IsGaloisGroup.card_eq_finrank H _ _).symm

end RatFunc

end Rigidity.RET

end
