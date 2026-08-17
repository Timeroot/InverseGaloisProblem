/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.BaseField
import InverseGalois.Rigidity.RET.Analytic.Wall

/-!
# The extension a covering always defines

The Galois statements of `RET/Analytic/BaseField.lean` all carry the same hypothesis: every
nontrivial deck transformation moves some function of moderate growth.  That hypothesis is only
used to make the action of the deck group on the functions faithful, and a group action can always
be made faithful by dividing out the elements that move nothing.  So the whole chain runs
unconditionally for the quotient of the deck group by that subgroup.

The result is that the function field of a covering of a punctured plane is *always* a Galois
extension of the rational functions of the base coordinate, with Galois group the quotient of the
deck group by the deck transformations no function sees, and of degree the order of that quotient.
The requirement of `RET/Analytic/Wall.lean` is precisely the statement that the quotient is the
whole deck group.

## Main definitions

* `Rigidity.RET.actionKernel` — the elements of a group acting on a ring that move nothing.
* `Rigidity.RET.quotientAction` — the induced faithful action of the quotient by that subgroup.
* `Rigidity.RET.deckKernel` — the deck transformations no function of moderate growth sees.

## Main results

* `Rigidity.RET.isGalois_ratFunc_quotient_coverRing` — the function field of a covering is a Galois
  extension of the rational functions of the base coordinate.
* `Rigidity.RET.finrank_ratFunc_quotient_coverRing` — its degree is the order of the quotient of
  the deck group by the deck transformations no function sees.
* `Rigidity.RET.finrank_ratFunc_coverRing_eq_card_iff` — the degree is the order of the whole deck
  group exactly when every nontrivial deck transformation moves a function.
* `Rigidity.RET.forall_ne_iff_forall_prime_ne` — and it is enough to test the deck transformations
  of prime order.
* `Rigidity.RET.hasEnoughFunctions_iff_forall_finrank_eq_card` — the requirement of
  `RET/Analytic/Wall.lean` is that the function field of every covering has the degree of its deck
  group.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### The kernel of an action on a ring -/

section Kernel

variable (B : Type*) [Semiring B] (G : Type*) [Group G] [MulSemiringAction G B]

/-- **The elements of a group acting on a ring which move nothing.** -/
def actionKernel : Subgroup G := (MulSemiringAction.toRingAut G B).ker

instance actionKernel_normal : (actionKernel B G).Normal :=
  MonoidHom.normal_ker _

variable {B G}

theorem mem_actionKernel_iff {a : G} : a ∈ actionKernel B G ↔ ∀ b : B, a • b = b := by
  rw [actionKernel, MonoidHom.mem_ker]
  exact ⟨fun h b => congrArg (fun e : RingAut B => e b) h, fun h => RingEquiv.ext h⟩

variable (B G)

/-- **The quotient of a group by the elements moving nothing acts on the ring.** -/
def quotientAction : MulSemiringAction (G ⧸ actionKernel B G) B :=
  MulSemiringAction.compHom B (QuotientGroup.kerLift (MulSemiringAction.toRingAut G B))

variable {B G}

theorem quotientAction_smul_mk (a : G) (b : B) :
    letI := quotientAction B G
    (QuotientGroup.mk a : G ⧸ actionKernel B G) • b = a • b :=
  rfl

variable (B G)

/-- **The quotient by the elements moving nothing acts faithfully.** -/
theorem faithfulSMul_quotient :
    letI := quotientAction B G
    FaithfulSMul (G ⧸ actionKernel B G) B := by
  letI := quotientAction B G
  exact ⟨fun {_ _} h =>
    QuotientGroup.kerLift_injective (MulSemiringAction.toRingAut G B) (RingEquiv.ext h)⟩

variable {B G}

/-- **The quotient by the elements moving nothing has the same invariants.** -/
theorem forall_quotient_smul_eq_iff {b : B} :
    letI := quotientAction B G
    (∀ x : G ⧸ actionKernel B G, x • b = b) ↔ ∀ a : G, a • b = b := by
  letI := quotientAction B G
  refine ⟨fun h a => h (QuotientGroup.mk a), fun h x => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  exact h a

end Kernel

/-! ### The deck transformations no function sees -/

section Deck

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ}
variable {H : Type*} [Group H] [MulAction H Y] [ContinuousConstSMul H Y]

variable (H) in
/-- **The deck transformations which no function of moderate growth sees.** -/
abbrev deckKernel (hf : IsLocalHomeomorph f) (S : Finset ℂ) [IsOverBase H f] : Subgroup H :=
  actionKernel ↥(coverRing hf S) H

theorem mem_deckKernel_iff {hf : IsLocalHomeomorph f} {S : Finset ℂ} [IsOverBase H f] {a : H} :
    a ∈ deckKernel H hf S ↔ ∀ F ∈ coverRing hf S, ∀ y : Y, F (a • y) = F y := by
  rw [deckKernel, mem_actionKernel_iff]
  constructor
  · intro h F hF y
    have hval := congrFun (congrArg Subtype.val (h ⟨F, hF⟩)) (a • y)
    rw [coverRing_smul_coe, inv_smul_smul] at hval
    exact hval.symm
  · intro h F
    refine Subtype.ext (funext fun y => ?_)
    rw [coverRing_smul_coe]
    have hval := h (F : Y → ℂ) F.2 (a⁻¹ • y)
    rw [smul_inv_smul] at hval
    exact hval.symm

/-- **No function of moderate growth sees any nontrivial deck transformation exactly when the
subgroup of unseen ones is trivial.** -/
theorem deckKernel_eq_bot_iff {hf : IsLocalHomeomorph f} {S : Finset ℂ} [IsOverBase H f] :
    deckKernel H hf S = ⊥ ↔
      ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y := by
  rw [Subgroup.eq_bot_iff_forall]
  constructor
  · intro h a ha
    by_contra hcon
    push_neg at hcon
    exact ha (h a (mem_deckKernel_iff.2 fun F hF y => hcon F hF y))
  · intro h a ha
    by_contra ha1
    obtain ⟨F, hF, y, hy⟩ := h a ha1
    exact hy (mem_deckKernel_iff.1 ha F hF y)

/-- **It is enough to test the deck transformations of prime order**: the ones no function of
moderate growth sees form a subgroup, and a nontrivial finite subgroup contains an element of
prime order. -/
theorem forall_ne_iff_forall_prime_ne [Finite H] {hf : IsLocalHomeomorph f} {S : Finset ℂ}
    [IsOverBase H f] :
    (∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) ↔
      ∀ (p : ℕ), p.Prime → ∀ a : H, orderOf a = p → ∃ F ∈ coverRing hf S, ∃ y : Y,
        F (a • y) ≠ F y := by
  constructor
  · intro h p hp a hpa
    refine h a fun ha => ?_
    rw [ha, orderOf_one] at hpa
    exact hp.ne_one hpa.symm
  intro h
  rw [← deckKernel_eq_bot_iff]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (fun h1 => hne (Subgroup.card_eq_one.1 h1) : Nat.card ↥(deckKernel H hf S) ≠ 1)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(deckKernel H hf S)) p hpd
  obtain ⟨F, hF, y, hy⟩ := h p hp (a : H) (by rwa [Subgroup.orderOf_coe])
  exact hy (mem_deckKernel_iff.1 a.2 F hF y)

end Deck

/-! ### The Galois extension a covering always defines -/

section Quotient

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {S : Finset ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]

attribute [local instance] FractionRing.liftAlgebra ratFuncAlgebra

omit [Nonempty Y] [PreconnectedSpace Y] [Finite H] in
/-- **The quotient of the deck group fixes the regular functions on the punctured plane.** -/
theorem quotient_smul_baseAwayHom (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (a : H ⧸ deckKernel H hf S) (x : Localization.Away (punctPoly S)) :
    letI := quotientAction ↥(coverRing hf S) H
    a • baseAwayHom hf hrange x = baseAwayHom hf hrange x := by
  letI := quotientAction ↥(coverRing hf S) H
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  rw [quotientAction_smul_mk]
  exact smul_baseAwayHom hf hrange a x

omit [Nonempty Y] [PreconnectedSpace Y] [Finite H] in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The quotient of the deck group by the deck transformations no function sees is a Galois group
for the ring of functions of the covering over the regular functions on the punctured plane.** -/
theorem isGaloisGroup_quotient_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) :
    letI := baseAlgebra hf hrange
    letI := quotientAction ↥(coverRing hf S) H
    IsGaloisGroup (H ⧸ deckKernel H hf S) (Localization.Away (punctPoly S))
      ↥(coverRing hf S) := by
  letI := baseAlgebra hf hrange
  letI := quotientAction ↥(coverRing hf S) H
  refine ⟨faithfulSMul_quotient _ _, ⟨fun a x F => ?_⟩, ⟨fun F hF => ?_⟩⟩
  · show a • (x • F) = x • (a • F)
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    exact quotient_smul_baseAwayHom hf hrange a x
  · exact (isInvariant_coverRing hf hrange htrans).isInvariant F
      (forall_quotient_smul_eq_iff.1 hF)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The quotient of the deck group is a Galois group for the function field of the covering over
the rational functions of the base coordinate.** -/
theorem isGaloisGroup_ratFunc_quotient_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) :
    letI := baseAlgebra hf hrange
    letI := quotientAction ↥(coverRing hf S) H
    haveI := isGaloisGroup_quotient_coverRing hf hrange htrans
    haveI := isTorsionFree_coverRing hf hrange
    letI := FractionRing.mulSemiringAction_of_isGaloisGroup (H ⧸ deckKernel H hf S)
      (Localization.Away (punctPoly S)) ↥(coverRing hf S)
    letI := coverRatFuncAlgebra hf hrange
    IsGaloisGroup (H ⧸ deckKernel H hf S) (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) := by
  letI := baseAlgebra hf hrange
  letI := quotientAction ↥(coverRing hf S) H
  haveI := isGaloisGroup_quotient_coverRing hf hrange htrans
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup (H ⧸ deckKernel H hf S)
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  haveI := IsGaloisGroup.toFractionRing (H ⧸ deckKernel H hf S)
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  exact isGaloisGroup_of_ringEquiv (B := FractionRing ↥(coverRing hf S)) (H ⧸ deckKernel H hf S)
    (fractionRingAwayAlgEquivRatFunc S).symm.toRingEquiv

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The function field of a connected covering of a punctured plane is a Galois extension of the
rational functions of the base coordinate.** -/
theorem isGalois_ratFunc_quotient_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) :
    letI := coverRatFuncAlgebra hf hrange
    IsGalois (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) := by
  letI := baseAlgebra hf hrange
  letI := quotientAction ↥(coverRing hf S) H
  haveI := isGaloisGroup_quotient_coverRing hf hrange htrans
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup (H ⧸ deckKernel H hf S)
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  letI := coverRatFuncAlgebra hf hrange
  haveI := isGaloisGroup_ratFunc_quotient_coverRing hf hrange htrans
  exact IsGaloisGroup.isGalois (H ⧸ deckKernel H hf S) _ _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The quotient of the deck group by the deck transformations no function sees is the Galois
group of the function field of the covering over the rational functions of the base
coordinate.** -/
def mulEquivAlgEquiv_ratFunc_quotient_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) :
    letI := coverRatFuncAlgebra hf hrange
    (H ⧸ deckKernel H hf S) ≃*
      (FractionRing ↥(coverRing hf S) ≃ₐ[RatFunc ℂ] FractionRing ↥(coverRing hf S)) := by
  letI := baseAlgebra hf hrange
  letI := quotientAction ↥(coverRing hf S) H
  haveI := isGaloisGroup_quotient_coverRing hf hrange htrans
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup (H ⧸ deckKernel H hf S)
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  letI := coverRatFuncAlgebra hf hrange
  haveI := isGaloisGroup_ratFunc_quotient_coverRing hf hrange htrans
  exact IsGaloisGroup.mulEquivAlgEquiv (H ⧸ deckKernel H hf S) _ _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The degree of the function field of a connected covering over the rational functions of the
base coordinate is the order of the quotient of the deck group by the deck transformations no
function of moderate growth sees.** -/
theorem finrank_ratFunc_quotient_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) :
    letI := coverRatFuncAlgebra hf hrange
    Module.finrank (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) =
      Nat.card (H ⧸ deckKernel H hf S) := by
  letI := baseAlgebra hf hrange
  letI := quotientAction ↥(coverRing hf S) H
  haveI := isGaloisGroup_quotient_coverRing hf hrange htrans
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup (H ⧸ deckKernel H hf S)
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  letI := coverRatFuncAlgebra hf hrange
  haveI := isGaloisGroup_ratFunc_quotient_coverRing hf hrange htrans
  exact (IsGaloisGroup.card_eq_finrank (H ⧸ deckKernel H hf S) _ _).symm

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The function field of a covering has the degree of the whole deck group exactly when every
nontrivial deck transformation moves a function of moderate growth.** -/
theorem finrank_ratFunc_coverRing_eq_card_iff (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) :
    letI := coverRatFuncAlgebra hf hrange
    Module.finrank (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) = Nat.card H ↔
      ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y := by
  letI := coverRatFuncAlgebra hf hrange
  refine ⟨fun hrank => ?_, fun hsep => finrank_ratFunc_coverRing hf hrange htrans hsep⟩
  rw [← deckKernel_eq_bot_iff, ← Subgroup.card_eq_one]
  have hcard : Nat.card (H ⧸ deckKernel H hf S) = Nat.card H :=
    (finrank_ratFunc_quotient_coverRing hf hrange htrans).symm.trans hrank
  have hmul := Subgroup.card_mul_index (deckKernel H hf S)
  rw [Subgroup.index_eq_card, hcard] at hmul
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hmul.trans (one_mul _).symm)

end Quotient

/-! ### The requirement, restated as a degree -/

attribute [local instance] FractionRing.liftAlgebra ratFuncAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The requirement of `RET/Analytic/Wall.lean` is that the function field of every covering of a
punctured plane has the degree of its deck group.**

Whatever the covering, its function field is a Galois extension of the rational functions of the
base coordinate, of degree the order of the quotient of the deck group by the deck transformations
no function of moderate growth sees.  The requirement is that the quotient is always the whole deck
group. -/
theorem hasEnoughFunctions_iff_forall_finrank_eq_card :
    HasEnoughFunctions ↔
      ∀ (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
        (q : Y → ↥((S : Set ℂ)ᶜ)), IsCoveringMap q →
        ∀ (hf : IsLocalHomeomorph fun y => ((q y : ℂ)))
          (hrange : Set.range (fun y => ((q y : ℂ))) = (↑S : Set ℂ)ᶜ)
          (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]
          [FaithfulSMul H Y] [IsOverBase H fun y => ((q y : ℂ))],
          (∀ y y' : Y, (q y : ℂ) = (q y' : ℂ) → ∃ b : H, y' = b • y) →
          letI := coverRatFuncAlgebra hf hrange
          Module.finrank (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) = Nat.card H := by
  constructor
  · intro hwall S Y _ _ _ q hq hf hrange H _ _ _ _ _ _ htrans
    exact (finrank_ratFunc_coverRing_eq_card_iff hf hrange htrans).2
      (hwall S Y q hq hf hrange H htrans)
  · intro h S Y _ _ _ q hq hf hrange H _ _ _ _ _ _ htrans
    exact (finrank_ratFunc_coverRing_eq_card_iff hf hrange htrans).1
      (h S Y q hq hf hrange H htrans)

end Rigidity.RET

end
