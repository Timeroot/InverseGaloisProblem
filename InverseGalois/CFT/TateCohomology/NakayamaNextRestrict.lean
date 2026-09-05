/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.NakayamaRestrict

/-!
# The map leaving the comparison of Tate and Nakayama against a subgroup

The comparison of Tate and Nakayama sits in a four term exact sequence whose next map is induced by
the inclusion of the tensor product into the extension attached to the cocycle, read through the two
identifications of degree.  That next map measures how far the comparison is from being onto: a
class of the tensor product is a value of the comparison exactly when the next map kills it.

Both identifications of degree commute with restriction to a subgroup and with corestriction from
it, and they are invertible, so the composite of their inverses does too; the induced map commutes
with both by naturality.  Hence **the map leaving the comparison commutes with restriction to a
subgroup and with corestriction from it**, the map on the subgroup being the one built from the
shift read on the subgroup and the restricted cocycle.

Corestriction therefore carries what the map leaving the comparison reaches on a subgroup onto what
it reaches on the whole group, as soon as corestriction of the tensor product is onto.  This is the
form in which the map is used: it turns a statement about the whole group into the sum over a family
of subgroups of statements about those subgroups.

## Main definitions

* `InverseGalois.CFT.Tate.resNakayamaIso`: the two identifications of degree that follow the
  connecting map, read on a subgroup.
* `InverseGalois.CFT.Tate.resTateNakayamaNextMap`: the map leaving the comparison of Tate and
  Nakayama on a subgroup.
* `InverseGalois.CFT.Tate.resTateNakayamaTwoNextMap`: the same for the cocycle attached to a
  prescribed class in degree two.

## Main results

* `InverseGalois.CFT.Tate.tateRes_tateNakayamaNextMap` and
  `InverseGalois.CFT.Tate.tateCor_tateNakayamaNextMap`: **the map leaving the comparison of Tate and
  Nakayama commutes with restriction to a subgroup and with corestriction from it**, in every
  integer degree.
* `InverseGalois.CFT.Tate.map_range_resTateNakayamaNextMap`: **what the map leaving the comparison
  reaches is the corestriction of what it reaches on a subgroup**, as soon as corestriction of the
  tensor product from that subgroup is onto.
* `InverseGalois.CFT.Tate.tateRes_tateNakayamaTwoNextMap`,
  `InverseGalois.CFT.Tate.tateCor_tateNakayamaTwoNextMap` and
  `InverseGalois.CFT.Tate.map_range_resTateNakayamaTwoNextMap`: the same three statements for the
  cocycle attached to a prescribed class in degree two.

## Tags

Tate cohomology, Tate-Nakayama, restriction, corestriction, connecting homomorphism
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (H : Subgroup G)

/-! ### The two identifications of degree, read on a subgroup -/

section Identifications

variable (A M : Rep k G)

/-- **The two identifications that follow the connecting map, read on a subgroup**: the shift of a
tensor product is the tensor product of the shift, and the complete cohomology of a shift on the
subgroup in a degree is that of the representation on the subgroup one degree higher. -/
def resNakayamaIso (n : ℤ) :
    tateModule (resObj H (tensorObj (shiftObj A) M)) (n + 1) ≃ₗ[k]
      tateModule (resObj H (tensorObj A M)) (n + 1 + 1) :=
  (tateMapIso ((Action.res _ H.subtype).mapIso (shiftTensorIso A M)) (n + 1)).toLinearEquiv.trans
    (resShiftEquiv H (tensorObj A M) (n + 1))

theorem resNakayamaIso_apply (n : ℤ)
    (z : ↥(tateModule (resObj H (tensorObj (shiftObj A) M)) (n + 1))) :
    resNakayamaIso H A M n z
      = resShiftEquiv H (tensorObj A M) (n + 1)
        (tateMap (resHom H (shiftTensorIso A M).hom) (n + 1) z) := rfl

/-- **The two identifications of degree commute with restriction to a subgroup.** -/
theorem tateRes_tateNakayamaIso (n : ℤ) (z : ↥(tateModule (tensorObj (shiftObj A) M) (n + 1))) :
    tateRes H (tensorObj A M) (n + 1 + 1) (tateNakayamaIso A M n z)
      = resNakayamaIso H A M n (tateRes H (tensorObj (shiftObj A) M) (n + 1) z) := by
  show tateRes H (tensorObj A M) (n + 1 + 1)
      (tateShiftEquiv (tensorObj A M) (n + 1)
        (tateMap (shiftTensorIso A M).hom (n + 1) z)) = _
  rw [tateRes_tateShiftEquiv_int, tateRes_naturality, resNakayamaIso_apply]

/-- **The two identifications of degree commute with corestriction from a subgroup.** -/
theorem tateCor_resNakayamaIso (n : ℤ)
    (z : ↥(tateModule (resObj H (tensorObj (shiftObj A) M)) (n + 1))) :
    tateCor H (tensorObj A M) (n + 1 + 1) (resNakayamaIso H A M n z)
      = tateNakayamaIso A M n (tateCor H (tensorObj (shiftObj A) M) (n + 1) z) := by
  rw [resNakayamaIso_apply, tateCor_tateShiftEquiv_int, tateCor_naturality]
  rfl

/-- **The inverses of the two identifications of degree commute with restriction to a subgroup.** -/
theorem tateRes_tateNakayamaIso_symm (n : ℤ) (x : ↥(tateModule (tensorObj A M) (n + 1 + 1))) :
    tateRes H (tensorObj (shiftObj A) M) (n + 1) ((tateNakayamaIso A M n).symm x)
      = (resNakayamaIso H A M n).symm (tateRes H (tensorObj A M) (n + 1 + 1) x) := by
  apply (resNakayamaIso H A M n).injective
  rw [LinearEquiv.apply_symm_apply, ← tateRes_tateNakayamaIso, LinearEquiv.apply_symm_apply]

/-- **The inverses of the two identifications of degree commute with corestriction from a
subgroup.** -/
theorem tateCor_resNakayamaIso_symm (n : ℤ)
    (y : ↥(tateModule (resObj H (tensorObj A M)) (n + 1 + 1))) :
    tateCor H (tensorObj (shiftObj A) M) (n + 1) ((resNakayamaIso H A M n).symm y)
      = (tateNakayamaIso A M n).symm (tateCor H (tensorObj A M) (n + 1 + 1) y) := by
  apply (tateNakayamaIso A M n).injective
  rw [LinearEquiv.apply_symm_apply, ← tateCor_resNakayamaIso, LinearEquiv.apply_symm_apply]

end Identifications

/-! ### The map leaving the comparison -/

section Nakayama

variable (A : Rep k G) (b : groupCohomology.cocycles₁ (shiftObj A)) (M : Rep k G)

/-- **The map leaving the comparison of Tate and Nakayama on a subgroup**: the map induced by the
inclusion of the tensor product into the extension attached to the restricted cocycle, read through
the two identifications of degree on the subgroup. -/
def resTateNakayamaNextMap (n : ℤ) :
    ↥(tateModule (resObj H (tensorObj A M)) (n + 1 + 1)) →ₗ[k]
      ↥(tateModule (resObj H (cocycleTensorObj (shiftObj A) b M)) (n + 1)) :=
  (tateMap (resHom H (cocycleTensorSeq (shiftObj A) b M).f) (n + 1)).hom ∘ₗ
    (resNakayamaIso H A M n).symm.toLinearMap

theorem resTateNakayamaNextMap_apply (n : ℤ)
    (y : ↥(tateModule (resObj H (tensorObj A M)) (n + 1 + 1))) :
    resTateNakayamaNextMap H A b M n y
      = tateMap (resHom H (cocycleTensorSeq (shiftObj A) b M).f) (n + 1)
        ((resNakayamaIso H A M n).symm y) := rfl

/-- **The map leaving the comparison of Tate and Nakayama commutes with restriction to a
subgroup**, in every integer degree. -/
theorem tateRes_tateNakayamaNextMap (n : ℤ) (x : ↥(tateModule (tensorObj A M) (n + 1 + 1))) :
    tateRes H (cocycleTensorObj (shiftObj A) b M) (n + 1) (tateNakayamaNextMap A b M n x)
      = resTateNakayamaNextMap H A b M n (tateRes H (tensorObj A M) (n + 1 + 1) x) := by
  have h := tateRes_naturality (A := tensorObj (shiftObj A) M)
    (B := cocycleTensorObj (shiftObj A) b M) H (cocycleTensorSeq (shiftObj A) b M).f (n + 1)
    ((tateNakayamaIso A M n).symm x)
  rw [tateRes_tateNakayamaIso_symm] at h
  exact h

/-- **The map leaving the comparison of Tate and Nakayama commutes with corestriction from a
subgroup**, in every integer degree. -/
theorem tateCor_tateNakayamaNextMap (n : ℤ)
    (y : ↥(tateModule (resObj H (tensorObj A M)) (n + 1 + 1))) :
    tateCor H (cocycleTensorObj (shiftObj A) b M) (n + 1) (resTateNakayamaNextMap H A b M n y)
      = tateNakayamaNextMap A b M n (tateCor H (tensorObj A M) (n + 1 + 1) y) := by
  have h := tateCor_naturality (A := tensorObj (shiftObj A) M)
    (B := cocycleTensorObj (shiftObj A) b M) H (cocycleTensorSeq (shiftObj A) b M).f (n + 1)
    ((resNakayamaIso H A M n).symm y)
  rw [tateCor_resNakayamaIso_symm] at h
  exact h

/-- **What the map leaving the comparison of Tate and Nakayama reaches is the corestriction of what
it reaches on a subgroup**, as soon as corestriction of the tensor product from that subgroup is
onto. -/
theorem map_range_resTateNakayamaNextMap (n : ℤ)
    (hcor : Function.Surjective (tateCor H (tensorObj A M) (n + 1 + 1))) :
    Submodule.map (tateCor H (cocycleTensorObj (shiftObj A) b M) (n + 1))
        (LinearMap.range (resTateNakayamaNextMap H A b M n))
      = LinearMap.range (tateNakayamaNextMap A b M n) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨tateCor H (tensorObj A M) (n + 1 + 1) y,
      (tateCor_tateNakayamaNextMap H A b M n y).symm⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hcor x
    exact ⟨resTateNakayamaNextMap H A b M n y, LinearMap.mem_range_self _ _,
      tateCor_tateNakayamaNextMap H A b M n y⟩

end Nakayama

/-! ### A class in degree two -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G] (H : Subgroup G) (A : Rep ℤ G) (α : tateModule A 2)
  (M : Rep ℤ G)

/-- **The map leaving the comparison of Tate and Nakayama on a subgroup, for the cocycle attached to
a prescribed class in degree two.** -/
def resTateNakayamaTwoNextMap (n : ℤ) :
    ↥(tateModule (resObj H (tensorObj A M)) (n + 1 + 1)) →ₗ[ℤ]
      ↥(tateModule (resObj H (cocycleTensorObj (shiftObj A) (tateTwoCocycle A α) M)) (n + 1)) :=
  resTateNakayamaNextMap H A (tateTwoCocycle A α) M n

/-- **The map leaving the comparison for a class in degree two commutes with restriction to a
subgroup**, in every integer degree. -/
theorem tateRes_tateNakayamaTwoNextMap (n : ℤ)
    (x : ↥(tateModule (tensorObj A M) (n + 1 + 1))) :
    tateRes H (cocycleTensorObj (shiftObj A) (tateTwoCocycle A α) M) (n + 1)
        (tateNakayamaTwoNextMap A α M n x)
      = resTateNakayamaTwoNextMap H A α M n (tateRes H (tensorObj A M) (n + 1 + 1) x) :=
  tateRes_tateNakayamaNextMap H A (tateTwoCocycle A α) M n x

/-- **The map leaving the comparison for a class in degree two commutes with corestriction from a
subgroup**, in every integer degree. -/
theorem tateCor_tateNakayamaTwoNextMap (n : ℤ)
    (y : ↥(tateModule (resObj H (tensorObj A M)) (n + 1 + 1))) :
    tateCor H (cocycleTensorObj (shiftObj A) (tateTwoCocycle A α) M) (n + 1)
        (resTateNakayamaTwoNextMap H A α M n y)
      = tateNakayamaTwoNextMap A α M n (tateCor H (tensorObj A M) (n + 1 + 1) y) :=
  tateCor_tateNakayamaNextMap H A (tateTwoCocycle A α) M n y

/-- **What the map leaving the comparison for a class in degree two reaches is the corestriction of
what it reaches on a subgroup**, as soon as corestriction of the tensor product from that subgroup
is onto. -/
theorem map_range_resTateNakayamaTwoNextMap (n : ℤ)
    (hcor : Function.Surjective (tateCor H (tensorObj A M) (n + 1 + 1))) :
    Submodule.map (tateCor H (cocycleTensorObj (shiftObj A) (tateTwoCocycle A α) M) (n + 1))
        (LinearMap.range (resTateNakayamaTwoNextMap H A α M n))
      = LinearMap.range (tateNakayamaTwoNextMap A α M n) :=
  map_range_resTateNakayamaNextMap H A (tateTwoCocycle A α) M n hcor

end DegreeTwo

end

end InverseGalois.CFT.Tate
