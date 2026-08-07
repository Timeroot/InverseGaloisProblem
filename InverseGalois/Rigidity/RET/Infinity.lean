/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Twist

/-!
# Subcovers of a twisted cover, and unramifiedness at infinity

Twisting a cover by a coordinate change `φ` of the base leaves the field, and hence the lattice of
intermediate fields, untouched: an intermediate field of `M / ℚ̄(T)` is the same subset as an
intermediate field of the twist, because `φ` is a bijection of the base with itself
(`Twist.subFieldOrderIso`).  Consequently the subcovers of a twisted cover are the twists of the
subcovers, and the compositum lemma for unramifiedness (`RET/Unramified.lean`) applies verbatim at
the point at infinity.

## Main definitions

* `Rigidity.RET.Twist.subField` — an intermediate field of the twist, from one of the field.

## Main results

* `Rigidity.RET.Twist.subFieldOrderIso` — the two lattices of intermediate fields agree.
* `Rigidity.RET.LineCover.IsUnramifiedAtInfinity.of_iSup` — the compositum lemma at infinity.
* `Rigidity.RET.LineCover.IsUnramifiedAtInfinity.transport` — unramifiedness at infinity only
  depends on the isomorphism class of the cover.
-/

open Polynomial

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace Rigidity.RET

open GeomAKLB

namespace Twist

variable {φ : RatFunc k ≃+* RatFunc k} {M : Type} [Field M] [Algebra (RatFunc k) M]

/-- An intermediate field of the twist, from an intermediate field of `M`: the same subset.  It is
closed under the twisted scalars because `φ` maps the base onto itself. -/
def subField (E : IntermediateField (RatFunc k) M) : IntermediateField (RatFunc k) (Twist φ M) where
  carrier := (E : Set M)
  mul_mem' := E.mul_mem
  one_mem' := E.one_mem
  add_mem' := E.add_mem
  zero_mem' := E.zero_mem
  algebraMap_mem' f := E.algebraMap_mem (φ f)
  inv_mem' _ hx := E.inv_mem hx

/-- An intermediate field of `M`, from an intermediate field of the twist: the same subset. -/
def unSubField (E : IntermediateField (RatFunc k) (Twist φ M)) : IntermediateField (RatFunc k) M
    where
  carrier := (E : Set (Twist φ M))
  mul_mem' := E.mul_mem
  one_mem' := E.one_mem
  add_mem' := E.add_mem
  zero_mem' := E.zero_mem
  algebraMap_mem' f := by
    have := E.algebraMap_mem (φ.symm f)
    rwa [algebraMap_symm] at this
  inv_mem' _ hx := E.inv_mem hx

/-- **The intermediate fields of a twist are the intermediate fields.** -/
def subFieldOrderIso :
    IntermediateField (RatFunc k) M ≃o IntermediateField (RatFunc k) (Twist φ M) where
  toFun := subField
  invFun := unSubField
  left_inv _ := SetLike.ext' rfl
  right_inv _ := SetLike.ext' rfl
  map_rel_iff' := Iff.rfl

@[simp] theorem subFieldOrderIso_apply (E : IntermediateField (RatFunc k) M) :
    (subFieldOrderIso (φ := φ)) E = subField E := rfl

/-- A family generating `M` generates the twist. -/
theorem subField_iSup_eq_top {ι : Sort*} (E : ι → IntermediateField (RatFunc k) M)
    (hsup : ⨆ i, E i = ⊤) : ⨆ i, subField (φ := φ) (E i) = ⊤ := by
  have h1 := congrArg (subFieldOrderIso (φ := φ) (M := M)) hsup
  rw [OrderIso.map_iSup, OrderIso.map_top] at h1
  simpa using h1

/-- The twist of an intermediate field is the corresponding intermediate field of the twist. -/
def subFieldEquiv (E : IntermediateField (RatFunc k) M) :
    Twist φ (E : Type _) ≃ₐ[RatFunc k] (subField (φ := φ) E : Type _) :=
  { (RingEquiv.refl (Twist φ (E : Type _)) :
      Twist φ (E : Type _) ≃+* (subField (φ := φ) E : Type _)) with
    commutes' := fun _ => rfl }

end Twist

namespace LineCover

/-- Unramifiedness at infinity is unramifiedness of the inversion twist at every point but `0`
being unconstrained — that is, unramifiedness of the twist "outside the complement of `0`". -/
theorem isUnramifiedAtInfinity_iff (L : LineCover) :
    L.IsUnramifiedAtInfinity ↔ (L.twist invSubst.toRingEquiv).IsUnramifiedOutside {(0 : k)}ᶜ := by
  constructor
  · intro h t ht σ hσ
    have h0 : t = 0 := by simpa using ht
    exact h σ (h0 ▸ hσ)
  · intro h σ hσ
    exact h 0 (by simp) σ hσ

/-- Unramifiedness at infinity only depends on the isomorphism class of the cover. -/
theorem IsUnramifiedAtInfinity.transport {L L' : LineCover} (e : L.M ≃ₐ[RatFunc k] L'.M)
    (h : L.IsUnramifiedAtInfinity) : L'.IsUnramifiedAtInfinity := by
  rw [isUnramifiedAtInfinity_iff] at h ⊢
  exact IsUnramifiedOutside.transport
    (L := L.twist invSubst.toRingEquiv) (L' := L'.twist invSubst.toRingEquiv)
    (Twist.congr (φ := invSubst.toRingEquiv) (M₁ := L.M) (M₂ := L'.M) e) h

/-- **The compositum lemma at infinity.**  If a cover is generated, as a field, by normal subcovers
each unramified at infinity, then the cover itself is unramified at infinity.

The subcovers of the inversion twist are the twists of the subcovers, and their supremum is again
everything, so this is the compositum lemma of `RET/Unramified.lean` applied to the twist. -/
theorem IsUnramifiedAtInfinity.of_iSup {L : LineCover} {ι : Sort*}
    (E : ι → IntermediateField (RatFunc k) L.M) [hnorm : ∀ i, Normal (RatFunc k) (E i)]
    (hsup : ⨆ i, E i = ⊤)
    (hE : ∀ i, (L.sub (E i)).IsUnramifiedAtInfinity) : L.IsUnramifiedAtInfinity := by
  haveI hgal : ∀ i, IsGalois (RatFunc k) (E i) := fun i => sub_isGalois L (E i)
  haveI hnorm' : ∀ i,
      Normal (RatFunc k) (Twist.subField (φ := invSubst.toRingEquiv) (E i)) := fun i =>
    Normal.of_algEquiv (F := RatFunc k) (E := Twist invSubst.toRingEquiv ((E i : Type _)))
      (Twist.subFieldEquiv (E i))
  rw [isUnramifiedAtInfinity_iff]
  refine @IsUnramifiedOutside.of_iSup (L.twist invSubst.toRingEquiv) ({(0 : k)}ᶜ) ι
    (fun i => Twist.subField (φ := invSubst.toRingEquiv) (M := L.M) (E i)) hnorm'
    (Twist.subField_iSup_eq_top (φ := invSubst.toRingEquiv) E hsup) ?_
  · intro i
    refine IsUnramifiedOutside.transport
      (L := (L.sub (E i)).twist invSubst.toRingEquiv)
      (L' := @LineCover.sub (L.twist invSubst.toRingEquiv)
        (Twist.subField (φ := invSubst.toRingEquiv) (M := L.M) (E i)) (hnorm' i))
      (Twist.subFieldEquiv (φ := invSubst.toRingEquiv) (M := L.M) (E i)) ?_
    exact (isUnramifiedAtInfinity_iff (L.sub (E i))).mp (hE i)

end LineCover

end Rigidity.RET
