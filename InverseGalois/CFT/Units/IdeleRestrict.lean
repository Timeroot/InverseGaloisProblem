/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleTower
import InverseGalois.CFT.Units.PlaceRestrict

/-!
# The Galois action on the ideles of a tower

An automorphism of the top field of a tower whose middle field is normal over the bottom acts on the
ideles of the top field, and restricts to an automorphism of the middle field, which acts on the
ideles of the middle field.  The inclusion of the ideles of the middle field into the ideles of the
top field intertwines the two actions: moving an idele of the middle field and then including it is
including it and then moving it by the restricted automorphism.

This is what lets the norm from the top field to the bottom be computed in two steps.  Place by
place it is the compatibility of the isomorphisms of completions with restriction, and the
bookkeeping here is only the assembly of those compatibilities over all places.

## Main results

* `InverseGalois.CFT.familyAut_adicUnitsComapSections_restrict`,
  `InverseGalois.CFT.familyAut_infiniteUnitsComapSections_restrict`: the actions on the families of
  local units are intertwined by the inclusion.
* `InverseGalois.CFT.fullIdeleAut_fullIdeleComap_restrict`: the same for the local unit groups of
  the ideles.
* `InverseGalois.CFT.ideleAut_ideleComap_restrict`: **the inclusion of the ideles of the middle
  field intertwines the action of an automorphism with the action of its restriction.**

## Tags

number field, idele, tower, Galois action, restriction
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField NumberField.InfinitePlace

section IdeleRestrict

variable {k F K : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F] [IsGalois F K]

variable (F) in
omit [NumberField k] [IsGalois F K] in
/-- **The action on the families of local units at the finite places is intertwined by the inclusion
of the families of the middle field.** -/
theorem familyAut_adicUnitsComapSections_restrict (σ : Gal(K/k))
    (z : ∀ p : HeightOneSpectrum (𝓞 F), Additive (p.adicCompletion F)ˣ) :
    (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ (adicUnitsComapSections F z)
      = adicUnitsComapSections F ((adicRingFamily (k := k) (K := F)).unitsFamily.familyAut
          (AlgEquiv.restrictNormalHom F σ) z) := by
  refine FamilyAction.familyAut_eq_of_map _ σ _ _ fun w => ?_
  rw [adicUnitsComapSections_apply, unitsFamily_map_adicUnitsComap_restrict F,
    adicUnitsComapSections_apply]
  refine congrArg (adicUnitsComap F (σ • w)) ?_
  rw [← FamilyAction.familyAut_apply_smul]
  exact famCast_apply_section _ _ _

variable (F) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois F K] in
/-- **The action on the families of local units at the infinite places is intertwined by the
inclusion of the families of the middle field.** -/
theorem familyAut_infiniteUnitsComapSections_restrict (σ : Gal(K/k))
    (z : ∀ u : InfinitePlace F, Additive u.Completionˣ) :
    (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ (infiniteUnitsComapSections F z)
      = infiniteUnitsComapSections F ((infiniteRingFamily (k := k) (K := F)).unitsFamily.familyAut
          (AlgEquiv.restrictNormalHom F σ) z) := by
  refine FamilyAction.familyAut_eq_of_map _ σ _ _ fun w => ?_
  rw [infiniteUnitsComapSections_apply, unitsFamily_map_infiniteUnitsComap_restrict F,
    infiniteUnitsComapSections_apply]
  refine congrArg (infiniteUnitsComap F (σ • w)) ?_
  rw [← FamilyAction.familyAut_apply_smul]
  exact famCast_apply_section _ _ _

variable (F) in
omit [NumberField k] [IsGalois F K] in
/-- **The inclusion of the local unit groups of the middle field intertwines the action of an
automorphism with the action of its restriction.** -/
theorem fullIdeleAut_fullIdeleComap_restrict (σ : Gal(K/k)) (x : FullIdele F) :
    fullIdeleAut (k := k) σ (fullIdeleComap F K x)
      = fullIdeleComap F K (fullIdeleAut (k := k) (K := F) (AlgEquiv.restrictNormalHom F σ) x) := by
  rw [fullIdeleComap_apply, fullIdeleAut, prodAut_apply,
    familyAut_infiniteUnitsComapSections_restrict F, familyAut_adicUnitsComapSections_restrict F,
    fullIdeleAut, prodAut_apply, fullIdeleComap_apply]

variable (F) in
omit [NumberField k] in
/-- **The inclusion of the ideles of the middle field intertwines the action of an automorphism of
the top field with the action of its restriction to the middle field.** -/
theorem ideleAut_ideleComap_restrict (σ : Gal(K/k)) (z : ↥(idele F)) :
    ideleAut (k := k) (K := K) σ (ideleComap F K z)
      = ideleComap F K (ideleAut (k := k) (K := F) (AlgEquiv.restrictNormalHom F σ) z) :=
  Subtype.ext (fullIdeleAut_fullIdeleComap_restrict F σ (z : FullIdele F))

end IdeleRestrict

end InverseGalois.CFT
