/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteFamily
import InverseGalois.CFT.Tate.InfinitePlaces
import InverseGalois.CFT.Units.InfiniteGalois

/-!
# The archimedean part of the ideles fixed by the Galois group

A family of local units of the base field, one at each infinite place, determines a family of local
units of the extension: at a place of the extension take the image of the unit at the place below.
This file shows that the families so obtained are exactly the families fixed by the Galois group.

One inclusion is the compatibility of the Galois transports between completions with the inclusion
of the completion of the base, which is checked on the dense image of the base field.  For the
other, a fixed family has its value at a place fixed by the decomposition group there, hence coming
from the completion of the base; and the values at the other places above the same place of the
base are the transports of that one, so they are the images of the same element.

This is the archimedean half of the description of the ideles fixed by the Galois group; the finite
half is the same argument at the primes.

## Main definitions

* `InverseGalois.CFT.infiniteUnitsComapSections`: **a family of local units of the base field at the
  infinite places, viewed as a family of local units of the extension.**

## Main results

* `InverseGalois.CFT.infiniteCompletionGalEquiv_infiniteCompletionComap`: the Galois transports
  commute with the inclusion of the completion of the base.
* `InverseGalois.CFT.familyAut_infiniteUnitsComapSections`: the families coming from the base are
  fixed.
* `InverseGalois.CFT.infiniteUnitsComapSections_injective`: distinct families of the base give
  distinct families of the extension.
* `InverseGalois.CFT.mem_range_infiniteUnitsComapSections_iff`: **the families of local units at the
  infinite places fixed by the Galois group are exactly those coming from the base field.**

## Tags

number field, idele, infinite place, completion, Galois action, decomposition group
-/

namespace InverseGalois.CFT

open MulAction NumberField NumberField.InfinitePlace

section InfiniteFixed

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-! ### The transports commute with the inclusion of the base -/

omit [NumberField k] [NumberField K] in
/-- **The Galois transport between completions at the infinite places commutes with the inclusion of
the completion of the base field**, the two sides agreeing on the dense image of the base field. -/
theorem infiniteCompletionGalEquiv_infiniteCompletionComap (w : InfinitePlace K) (σ : Gal(K/k))
    (c : (w.comap (algebraMap k K)).Completion) :
    infiniteCompletionGalEquiv w σ (infiniteCompletionComap k w c)
      = infiniteCompletionComap k (σ • w)
          (ringCast (fun u : InfinitePlace k => u.Completion)
            (comap_smul_infinitePlace σ w).symm c) := by
  refine UniformSpace.Completion.induction_on c ?_ ?_
  · exact isClosed_eq
      ((continuous_infiniteCompletionGalEquiv w σ).comp (continuous_infiniteCompletionComap k w))
      ((continuous_infiniteCompletionComap k (σ • w)).comp (continuous_ringCast _ _))
  · intro x
    set y : k := WithAbs.equiv (w.comap (algebraMap k K)).1 x with hy
    have h1 : infiniteCompletionComap k w (infiniteCoe y (w.comap (algebraMap k K)))
        = infiniteCoe (algebraMap k K y) w := infiniteCompletionComap_coe k w _
    have h2 : infiniteCompletionComap k (σ • w) (infiniteCoe y ((σ • w).comap (algebraMap k K)))
        = infiniteCoe (algebraMap k K y) (σ • w) := infiniteCompletionComap_coe k (σ • w) _
    show infiniteCompletionGalEquiv w σ
        (infiniteCompletionComap k w (infiniteCoe y (w.comap (algebraMap k K))))
      = infiniteCompletionComap k (σ • w)
        (ringCast _ (comap_smul_infinitePlace σ w).symm
          (infiniteCoe y (w.comap (algebraMap k K))))
    rw [ringCast_infiniteCoe, h1, h2, infiniteCompletionGalEquiv_infiniteCoe, AlgEquiv.commutes]

/-! ### The families of local units coming from the base -/

variable (k) in
/-- **A family of local units of the base field at the infinite places, viewed as a family of local
units of the extension**: at a place of the extension, the image of the unit at the place below. -/
noncomputable def infiniteUnitsComapSections :
    (∀ v : InfinitePlace k, Additive v.Completionˣ) →+
      ∀ w : InfinitePlace K, Additive w.Completionˣ where
  toFun y w := infiniteUnitsComap k w (y (w.comap (algebraMap k K)))
  map_zero' := funext fun w => map_zero (infiniteUnitsComap k w)
  map_add' _ _ := funext fun w => map_add (infiniteUnitsComap k w) _ _

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
@[simp]
theorem infiniteUnitsComapSections_apply (y : ∀ v : InfinitePlace k, Additive v.Completionˣ)
    (w : InfinitePlace K) :
    infiniteUnitsComapSections k (K := K) y w
      = infiniteUnitsComap k w (y (w.comap (algebraMap k K))) := rfl

variable (k) in
omit [NumberField k] [NumberField K] in
/-- **The transport of a local unit of the base field is the local unit of the base field at the
image place.** -/
theorem unitsFamily_map_infiniteUnitsComap (w : InfinitePlace K) (σ : Gal(K/k))
    (c : Additive ((w.comap (algebraMap k K)).Completion)ˣ) :
    (infiniteRingFamily (k := k) (K := K)).unitsFamily.map σ w (infiniteUnitsComap k w c)
      = infiniteUnitsComap k (σ • w)
          (famCast (fun u : InfinitePlace k => Additive (u.Completion)ˣ)
            (comap_smul_infinitePlace σ w).symm c) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [famCast_units, coe_infiniteUnitsComap]
  show infiniteCompletionGalEquiv w σ
      ((Additive.toMul (infiniteUnitsComap k w c) : (w.Completion)ˣ) : w.Completion)
    = algebraMap (((σ • w).comap (algebraMap k K)).Completion) ((σ • w).Completion)
        (ringCast (fun u : InfinitePlace k => u.Completion)
          (comap_smul_infinitePlace σ w).symm
          ((Additive.toMul c : ((w.comap (algebraMap k K)).Completion)ˣ) :
            (w.comap (algebraMap k K)).Completion))
  rw [coe_infiniteUnitsComap, algebraMap_infiniteCompletion k w,
    algebraMap_infiniteCompletion k (σ • w)]
  exact infiniteCompletionGalEquiv_infiniteCompletionComap w σ _

variable (k) in
omit [NumberField k] [NumberField K] in
/-- **A family of local units at the infinite places coming from the base field is fixed by the
Galois group.** -/
theorem familyAut_infiniteUnitsComapSections (σ : Gal(K/k))
    (y : ∀ v : InfinitePlace k, Additive v.Completionˣ) :
    (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ
        (infiniteUnitsComapSections k y)
      = infiniteUnitsComapSections k y := by
  refine FamilyAction.familyAut_eq_of_map _ σ _ _ fun w => ?_
  rw [infiniteUnitsComapSections_apply, unitsFamily_map_infiniteUnitsComap,
    infiniteUnitsComapSections_apply]
  exact congrArg (infiniteUnitsComap k (σ • w)) (famCast_apply_section _ _ y)

variable (k) in
/-- **Distinct families of local units of the base field give distinct families of local units of
the extension.** -/
theorem infiniteUnitsComapSections_injective :
    Function.Injective (infiniteUnitsComapSections k (K := K)) := by
  intro y y' h
  funext v
  obtain ⟨w, rfl⟩ : ∃ w : InfinitePlace K, w.comap (algebraMap k K) = v :=
    InfinitePlace.comap_surjective v
  exact infiniteUnitsComap_injective k w (congrFun h w)

/-! ### The fixed families -/

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **The value of a fixed family at an infinite place is fixed by the decomposition group
there.** -/
theorem smulUnitsAut_apply_of_familyAut_eq_infinite
    {x : ∀ w : InfinitePlace K, Additive w.Completionˣ}
    (hx : ∀ σ : Gal(K/k), (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ x = x)
    (w : InfinitePlace K) (σ : ↥(stabilizer Gal(K/k) w)) :
    smulUnitsAut σ (x w) = x w := by
  have hσ : (σ : Gal(K/k)) • w = w := mem_stabilizer_iff.mp σ.2
  have hmap : (infiniteRingFamily (k := k) (K := K)).unitsFamily.map (σ : Gal(K/k)) w (x w)
      = x ((σ : Gal(K/k)) • w) := by
    rw [← FamilyAction.familyAut_apply_smul, hx]
  have h := transport_infiniteUnitsFamily w (σ : Gal(K/k)) hσ (x w)
  rw [FamilyAction.transport_apply, hmap, famCast_apply_section] at h
  exact h.symm

variable (k) in
omit [NumberField k] [NumberField K] in
/-- **A fixed family is determined at every infinite place by its value at any one place above the
same place of the base.** -/
theorem infiniteUnitsComap_famCast_eq_of_familyAut_eq
    {x : ∀ w : InfinitePlace K, Additive w.Completionˣ}
    (hx : ∀ σ : Gal(K/k), (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ x = x)
    (W w : InfinitePlace K)
    (h : W.comap (algebraMap k K) = w.comap (algebraMap k K))
    (c : Additive ((W.comap (algebraMap k K)).Completion)ˣ)
    (hc : infiniteUnitsComap k W c = x W) :
    infiniteUnitsComap k w
        (famCast (fun u : InfinitePlace k => Additive (u.Completion)ˣ) h c) = x w := by
  obtain ⟨σ, rfl⟩ := InfinitePlace.exists_smul_eq_of_comap_eq h
  have hmap : (infiniteRingFamily (k := k) (K := K)).unitsFamily.map σ W (x W) = x (σ • W) := by
    rw [← FamilyAction.familyAut_apply_smul, hx]
  rw [← hmap, ← hc, unitsFamily_map_infiniteUnitsComap]

variable (k) in
/-- **The families of local units at the infinite places fixed by the Galois group are exactly those
coming from the base field.** -/
theorem mem_range_infiniteUnitsComapSections_iff
    (x : ∀ w : InfinitePlace K, Additive w.Completionˣ) :
    x ∈ (infiniteUnitsComapSections k (K := K)).range ↔
      ∀ σ : Gal(K/k), (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ x = x := by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ σ
    exact familyAut_infiniteUnitsComapSections k σ y
  · have hc : ∀ v : InfinitePlace k,
        ∃ c : Additive (((placeAbove k K v).comap (algebraMap k K)).Completion)ˣ,
          infiniteUnitsComap k (placeAbove k K v) c = x (placeAbove k K v) := fun v =>
      (mem_range_infiniteUnitsComap_iff k (placeAbove k K v) (x (placeAbove k K v))).mpr
        (smulUnitsAut_apply_of_familyAut_eq_infinite k hx (placeAbove k K v))
    choose c hcx using hc
    refine ⟨fun v => famCast (fun u : InfinitePlace k => Additive (u.Completion)ˣ)
      (comap_placeAbove k K v) (c v), funext fun w => ?_⟩
    exact infiniteUnitsComap_famCast_eq_of_familyAut_eq k hx
      (placeAbove k K (w.comap (algebraMap k K))) w
      (comap_placeAbove k K (w.comap (algebraMap k K))) _ (hcx _)

end InfiniteFixed

end InverseGalois.CFT
