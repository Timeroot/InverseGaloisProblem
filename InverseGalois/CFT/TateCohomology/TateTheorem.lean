/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.CocycleExtension

/-!
# Tate's theorem on the complete cohomology of a finite group

Let a one cocycle of a representation be given.  It twists the action of the group on the sum of
the representation and the integers into an extension of the integers by the representation, and
the connecting map of that extension carries the class of one in degree zero to the class of the
cocycle in degree one.  Reading the extension on a subgroup gives the extension attached to the
restricted cocycle, so the same description of the connecting map holds there.

Suppose that on every subgroup the complete cohomology of the representation vanishes in degree
zero, while in degree one it consists exactly of the multiples of the class of the restricted
cocycle and only the multiples of the order of the subgroup annihilate that class.  Then the
connecting map of the restricted extension is bijective in degree zero, because in degree zero over
the integers the classes are the multiples of the class of one and exactly the multiples of the
order of the subgroup vanish.  The long exact sequence then makes the middle term of the restricted
extension vanish in degrees zero and one.

Two consecutive vanishing degrees on a Sylow subgroup for each prime force the middle term to have
no complete cohomology whatsoever, so the connecting map of the extension itself is bijective in
every degree: the complete cohomology of the integers in a degree is the complete cohomology of the
representation in the following degree.

## Main definitions

* `InverseGalois.CFT.Tate.resCocycles₁`: a one cocycle read on a subgroup.
* `InverseGalois.CFT.Tate.IsTateClass`: the hypotheses of Tate's theorem on a subgroup.

## Main results

* `InverseGalois.CFT.Tate.isZero_tateModule_cocycleObj`: **the extension attached to the cocycle
  has no complete cohomology at all.**
* `InverseGalois.CFT.Tate.tateTheoremEquiv`: **the complete cohomology of the integers in a degree
  is the complete cohomology of the representation in the following degree.**

## Tags

Tate cohomology, Tate's theorem, cohomologically trivial, Sylow subgroup
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### Vanishing of the middle term of an extension -/

section Acyclic

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

/-- **The middle term has nothing in degree zero** when the sub has nothing there and the
connecting map out of degree zero is injective. -/
theorem isZero_tateModule_X₂_zero (h1 : Limits.IsZero (tateModule X.X₁ 0))
    (hδ : Function.Injective (tateδ hX 0)) : Limits.IsZero (tateModule X.X₂ 0) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  have h : tateMap X.g 0 x = 0 := by
    refine hδ ?_
    rw [map_zero]
    exact (tateExact_map_δ hX 0).apply_apply_eq_zero x
  obtain ⟨y, rfl⟩ := (tateExact_map_map hX 0 x).1 h
  rw [eq_zero_of_isZero h1 y, map_zero]

/-- **The middle term has nothing in degree one** when the quotient has nothing there and the
connecting map out of degree zero is surjective. -/
theorem isZero_tateModule_X₂_one (h3 : Limits.IsZero (tateModule X.X₃ 1))
    (hδ : Function.Surjective (tateδ hX 0)) : Limits.IsZero (tateModule X.X₂ 1) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨y, rfl⟩ := (tateExact_map_map hX 1 x).1 (eq_zero_of_isZero h3 _)
  obtain ⟨w, rfl⟩ := hδ y
  exact (tateExact_δ_map hX 0).apply_apply_eq_zero w

end Acyclic

/-! ### A cocycle read on a subgroup -/

section Restrict

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **A one cocycle read on a subgroup.** -/
def resCocycles₁ (H : Subgroup G) (A : Rep k G) (b : groupCohomology.cocycles₁ A) :
    groupCohomology.cocycles₁ (resObj H A) :=
  ⟨fun h => b (h : G), (groupCohomology.mem_cocycles₁_iff _).2 fun g h =>
    (groupCohomology.mem_cocycles₁_iff (b : G → ↥A.V)).1 b.2 (g : G) (h : G)⟩

omit [Finite G] in
/-- **The extension attached to a cocycle, read on a subgroup, is the extension attached to the
restricted cocycle.** -/
theorem resSeq_cocycleSeq (H : Subgroup G) (A : Rep k G) (b : groupCohomology.cocycles₁ A) :
    resSeq H (cocycleSeq A b) = cocycleSeq (resObj H A) (resCocycles₁ H A b) := rfl

omit [Finite G] in
/-- **The twisted representation, read on a subgroup, is the representation twisted by the
restricted cocycle.** -/
theorem resObj_cocycleObj (H : Subgroup G) (A : Rep k G) (b : groupCohomology.cocycles₁ A) :
    resObj H (cocycleObj A b) = cocycleObj (resObj H A) (resCocycles₁ H A b) := rfl

end Restrict

/-! ### The hypotheses of Tate's theorem -/

section Hypotheses

variable {G : Type} [Group G] [Finite G]

/-- **The hypotheses of Tate's theorem on a subgroup**: the complete cohomology of the
representation vanishes in degree zero, in degree one it consists of the multiples of the class of
the restricted cocycle, and only the multiples of the order of the subgroup annihilate that
class. -/
structure IsTateClass (H : Subgroup G) (A : Rep ℤ G) (b : groupCohomology.cocycles₁ A) :
    Prop where
  /-- The complete cohomology of the representation vanishes in degree zero. -/
  isZero_zero : Limits.IsZero (tateModule (resObj H A) 0)
  /-- Every class in degree one is a multiple of the class of the restricted cocycle. -/
  exists_zsmul : ∀ y : groupCohomology (resObj H A) 1,
    ∃ m : ℤ, y = m • groupCohomology.H1π (resObj H A) (resCocycles₁ H A b)
  /-- Only the multiples of the order of the subgroup annihilate the class of the restricted
  cocycle. -/
  dvd_of_zsmul_eq_zero : ∀ m : ℤ,
    m • groupCohomology.H1π (resObj H A) (resCocycles₁ H A b) = 0 → (Nat.card ↥H : ℤ) ∣ m

variable {H : Subgroup G} {A : Rep ℤ G} {b : groupCohomology.cocycles₁ A}

/-- **The connecting map of the restricted extension carries the class of one to the class of the
restricted cocycle.** -/
theorem tateδ_cocycleSeq_tateIntGen :
    tateδ (cocycleSeq_shortExact (resObj H A) (resCocycles₁ H A b)) 0 (tateIntGen ↥H)
      = groupCohomology.H1π (resObj H A) (resCocycles₁ H A b) :=
  H0toH1_cocycleSeq (resObj H A) (resCocycles₁ H A b)

/-- **The connecting map of the restricted extension is surjective in degree zero.** -/
theorem surjective_tateδ_cocycleSeq (h : IsTateClass H A b) :
    Function.Surjective
      (tateδ (cocycleSeq_shortExact (resObj H A) (resCocycles₁ H A b)) 0) := by
  intro y
  obtain ⟨m, rfl⟩ := h.exists_zsmul y
  exact ⟨m • tateIntGen ↥H, by rw [map_zsmul, tateδ_cocycleSeq_tateIntGen]⟩

/-- **The connecting map of the restricted extension is injective in degree zero.** -/
theorem injective_tateδ_cocycleSeq (h : IsTateClass H A b) :
    Function.Injective
      (tateδ (cocycleSeq_shortExact (resObj H A) (resCocycles₁ H A b)) 0) := by
  intro u v huv
  refine sub_eq_zero.1 ?_
  obtain ⟨m, hm⟩ := exists_zsmul_tateIntGen ↥H (u - v)
  rw [hm, zsmul_tateIntGen_eq_zero_iff]
  refine h.dvd_of_zsmul_eq_zero m ?_
  have hz : tateδ (cocycleSeq_shortExact (resObj H A) (resCocycles₁ H A b)) 0 (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  rwa [hm, map_zsmul, tateδ_cocycleSeq_tateIntGen] at hz

/-- **The extension attached to the restricted cocycle has nothing in degree zero.** -/
theorem isZero_tateModule_cocycleObj_res_zero (h : IsTateClass H A b) :
    Limits.IsZero (tateModule (cocycleObj (resObj H A) (resCocycles₁ H A b)) 0) :=
  isZero_tateModule_X₂_zero (X := cocycleSeq (resObj H A) (resCocycles₁ H A b))
    (cocycleSeq_shortExact _ _) h.isZero_zero (injective_tateδ_cocycleSeq h)

/-- **The extension attached to the restricted cocycle has nothing in degree one.** -/
theorem isZero_tateModule_cocycleObj_res_one (h : IsTateClass H A b) :
    Limits.IsZero (tateModule (cocycleObj (resObj H A) (resCocycles₁ H A b)) 1) :=
  isZero_tateModule_X₂_one (X := cocycleSeq (resObj H A) (resCocycles₁ H A b))
    (cocycleSeq_shortExact _ _) (isZero_tateModule_trivialInt_one ↥H)
    (surjective_tateδ_cocycleSeq h)

end Hypotheses

/-! ### Tate's theorem -/

section Theorem

variable {G : Type} [Group G] [Finite G] {A : Rep ℤ G} {b : groupCohomology.cocycles₁ A}

/-- **The extension attached to the cocycle has no complete cohomology at all** as soon as the
hypotheses of Tate's theorem hold on a Sylow subgroup for every prime. -/
theorem isZero_tateModule_cocycleObj
    (h : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsTateClass (P : Subgroup G) A b) (n : ℤ) :
    Limits.IsZero (tateModule (cocycleObj A b) n) := by
  refine isZero_tateModule_of_sylow (cocycleObj A b) (fun p hp P => ⟨0, ?_, ?_⟩) n
  · rw [resObj_cocycleObj]
    exact isZero_tateModule_cocycleObj_res_zero (h p hp P)
  · rw [resObj_cocycleObj]
    exact isZero_tateModule_cocycleObj_res_one (h p hp P)

/-- **Tate's theorem**: the complete cohomology of the integers in a degree is the complete
cohomology of the representation in the following degree. -/
def tateTheoremEquiv
    (h : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsTateClass (P : Subgroup G) A b) (n : ℤ) :
    tateModule (Rep.trivial ℤ G ℤ) n ≃ₗ[ℤ] tateModule A (n + 1) :=
  LinearEquiv.ofBijective (tateδ (cocycleSeq_shortExact A b) n).hom
    (bijective_tateδ (cocycleSeq_shortExact A b) n (isZero_tateModule_cocycleObj h n)
      (isZero_tateModule_cocycleObj h (n + 1)))

end Theorem

end

end InverseGalois.CFT.Tate
