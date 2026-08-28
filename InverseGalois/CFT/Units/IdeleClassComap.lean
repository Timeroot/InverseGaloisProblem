/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleClassFixed
import InverseGalois.CFT.Units.IdeleClassIndex
import InverseGalois.CFT.Units.IdeleRestrict

/-!
# The idele class group of a subfield

The ideles of a subfield sit inside the ideles of the extension, and a principal idele of the
subfield becomes a principal idele of the extension, so the construction descends to a map of idele
class groups.

That map is injective for a Galois extension.  An idele of the subfield whose class dies upstairs
differs from a principal idele of the extension, and that principal idele is then fixed by the whole
Galois group; a fixed unit is a unit of the subfield, so the idele was already principal downstairs.

Its image is exactly the part fixed by the Galois group of the extension over the subfield: a class
fixed by every automorphism is the class of a fixed idele, and a fixed idele is an idele of the
subfield.  Finally, if the subfield is normal over a smaller field, the inclusion intertwines the
action of an automorphism of the extension with the action of its restriction to the subfield.

## Main definitions

* `InverseGalois.CFT.ideleClassComap`: **the idele classes of the subfield, viewed among the idele
  classes of the extension.**

## Main results

* `InverseGalois.CFT.ideleClassComap_injective`: **the idele class group of a subfield injects into
  the idele class group of a Galois extension.**
* `InverseGalois.CFT.ideleClassAut_ideleClassComap`: the inclusion intertwines the action of an
  automorphism with the action of its restriction.
* `InverseGalois.CFT.mem_range_ideleClassComap_iff`: **the idele classes fixed by the automorphisms
  over the subfield are exactly the idele classes of the subfield.**

## Tags

number field, idele class group, Galois action, fixed points, tower
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section IdeleClassComap

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [IsGalois F K]

variable (F K) in
/-- **The idele classes of the subfield, viewed among the idele classes of the extension.** -/
noncomputable def ideleClassComap :
    (↥(idele F) ⧸ (ideleDiag F).range) →+ ↥(idele K) ⧸ (ideleDiag K).range :=
  QuotientAddGroup.map _ _ (ideleComap F K) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨globalUnitsComap F K u, (ideleComap_ideleDiag F K u).symm⟩)

variable (F K) in
@[simp]
theorem ideleClassComap_mk (a : ↥(idele F)) :
    ideleClassComap F K (QuotientAddGroup.mk a)
      = QuotientAddGroup.mk (ideleComap F K a) := rfl

variable (F K) in
/-- **The idele class group of a subfield injects into the idele class group of a Galois
extension**: an idele of the subfield that becomes principal upstairs does so through a unit fixed
by the Galois group, which is a unit of the subfield. -/
theorem ideleClassComap_injective :
    Function.Injective (ideleClassComap F K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [ideleClassComap_mk, QuotientAddGroup.eq_zero_iff] at hx
  obtain ⟨u, hu⟩ := hx
  have hfix : ∀ σ : Gal(K/F), globalUnitsAut (k := F) σ u = u := by
    intro σ
    refine ideleDiag_injective K ?_
    rw [← ideleAut_ideleDiag, hu, ideleAut_ideleComap]
  obtain ⟨v, rfl⟩ := (mem_range_globalUnitsComap_iff u).mpr hfix
  rw [QuotientAddGroup.eq_zero_iff]
  refine ⟨v, ideleComap_injective F K ?_⟩
  rw [ideleComap_ideleDiag, hu]

variable {k : Type*} [Field k] [NumberField k] [Algebra k F] [Algebra k K]
  [IsScalarTower k F K] [IsGalois k F]

variable (F) in
omit [NumberField k] in
/-- The inclusion of the idele classes of the middle field intertwines the action of an automorphism
of the top field with the action of its restriction to the middle field. -/
theorem ideleClassAut_ideleClassComap (σ : Gal(K/k))
    (x : ↥(idele F) ⧸ (ideleDiag F).range) :
    ideleClassAut (k := k) σ (ideleClassComap F K x)
      = ideleClassComap F K
          (ideleClassAut (k := k) (AlgEquiv.restrictNormalHom F σ) x) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [ideleClassComap_mk, ideleClassAut_mk, ideleClassAut_mk, ideleClassComap_mk,
    ideleAut_ideleComap_restrict]

variable (F K) in
/-- **The idele classes of the extension fixed by the automorphisms over the subfield are exactly
the idele classes of the subfield.** -/
theorem mem_range_ideleClassComap_iff (x : ↥(idele K) ⧸ (ideleDiag K).range) :
    x ∈ (ideleClassComap F K).range ↔ ∀ σ : Gal(K/F), ideleClassAut (k := F) σ x = x := by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ σ
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [ideleClassComap_mk, ideleClassAut_mk, ideleAut_ideleComap]
  · obtain ⟨a, ha, rfl⟩ := exists_fixed_ideleClass_of_forall (k := F) hx
    obtain ⟨b, rfl⟩ := (mem_range_ideleComap_iff F K a).mpr ha
    exact ⟨QuotientAddGroup.mk b, ideleClassComap_mk F K b⟩

end IdeleClassComap

end InverseGalois.CFT
