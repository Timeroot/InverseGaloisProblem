/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.RestrictSplit
import InverseGalois.CFT.TateCohomology.TateNakayamaError
import InverseGalois.CFT.TateCohomology.TateTheorem
import InverseGalois.CFT.TateCohomology.TensorTrivial

/-!
# The comparison of Tate and Nakayama against restriction to a subgroup

The extension of a representation by a tensor product attached to a one cocycle is a sum as a
sequence of modules, the inclusion of the tensor product and the projection onto the representation
being the two coordinates of a product; and read on a subgroup it is the extension attached to the
restricted cocycle.  So the connecting map of that extension commutes with restriction and with
corestriction in every integer degree.

The comparison of Tate and Nakayama is that connecting map followed by two identifications: the
shift of a tensor product is the tensor product of the shift, and the complete cohomology of a shift
in a degree is that of the representation one degree higher.  Both commute with restriction and with
corestriction, the first because restriction commutes with an induced map and the second in every
degree.  So **the comparison of Tate and Nakayama commutes with restriction to a subgroup and with
corestriction from it**, the map on the subgroup being the one built from the shift read on the
subgroup and the restricted cocycle.

## Main definitions

* `InverseGalois.CFT.Tate.resTateNakayamaMap`: the comparison of Tate and Nakayama on a subgroup.

## Main results

* `InverseGalois.CFT.Tate.tateRes_tateδ_cocycleTensorSeq` and
  `InverseGalois.CFT.Tate.tateCor_tateδ_cocycleTensorSeq`: **the connecting map of the tensored
  extension of a cocycle commutes with restriction and with corestriction**, in every integer
  degree.
* `InverseGalois.CFT.Tate.tateRes_tateNakayamaMap` and
  `InverseGalois.CFT.Tate.tateCor_tateNakayamaMap`: **the comparison of Tate and Nakayama commutes
  with restriction to a subgroup and with corestriction from it**, in every integer degree.
* `InverseGalois.CFT.Tate.tateRes_tateNakayamaTwoMap` and
  `InverseGalois.CFT.Tate.tateCor_tateNakayamaTwoMap`: the same for the comparison attached to a
  prescribed class in degree two.
* `InverseGalois.CFT.Tate.surjective_tateNakayamaMap_of_cor`: **the comparison of Tate and Nakayama
  is onto as soon as it is onto on a subgroup from which corestriction is onto.**
* `InverseGalois.CFT.Tate.injective_tateNakayamaMap_of_res`: **the comparison of Tate and Nakayama
  is injective as soon as it is injective on a subgroup to which restriction of the coefficients is
  injective.**

## Tags

Tate cohomology, Tate-Nakayama, restriction, corestriction, connecting homomorphism
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (H : Subgroup G)

/-! ### The tensored extension of a cocycle, read on a subgroup -/

section Cocycle

variable (S : Rep k G) (b : groupCohomology.cocycles₁ S) (M : Rep k G)

omit [Finite G] in
/-- **The tensored extension of a cocycle, read on a subgroup, is the tensored extension of the
restricted cocycle.** -/
theorem resSeq_cocycleTensorSeq :
    resSeq H (cocycleTensorSeq S b M)
      = cocycleTensorSeq (resObj H S) (resCocycles₁ H S b) (resObj H M) := rfl

omit [Finite G] in
/-- **The tensored extension of a cocycle is split as a sequence of modules**: the tensor product is
the first coordinate of a product. -/
theorem cocycleTensorFst_inl (t : ↥(tensorObj S M).V) :
    LinearMap.fst k (↥S.V ⊗[k] ↥M.V) ↥M.V ((cocycleTensorSeq S b M).f.hom.hom t) = t := rfl

/-- **Restriction to a subgroup commutes with the connecting map of the tensored extension of a
cocycle**, in every integer degree. -/
theorem tateRes_tateδ_cocycleTensorSeq (n : ℤ) (x : ↥(tateModule M n)) :
    tateRes H (tensorObj S M) (n + 1) (tateδ (cocycleTensorSeq_shortExact S b M) n x)
      = tateδ (cocycleTensorSeq_shortExact (resObj H S) (resCocycles₁ H S b) (resObj H M)) n
        (tateRes H M n x) :=
  tateRes_tateδ (cocycleTensorSeq_shortExact S b M)
    (LinearMap.fst k (↥S.V ⊗[k] ↥M.V) ↥M.V) (cocycleTensorFst_inl S b M)
    (cocycleTensorInr S b M) (cocycleTensorSnd_inr S b M) H n x

/-- **Corestriction from a subgroup commutes with the connecting map of the tensored extension of a
cocycle**, in every integer degree. -/
theorem tateCor_tateδ_cocycleTensorSeq (n : ℤ) (z : ↥(tateModule (resObj H M) n)) :
    tateCor H (tensorObj S M) (n + 1)
        (tateδ (cocycleTensorSeq_shortExact (resObj H S) (resCocycles₁ H S b) (resObj H M)) n z)
      = tateδ (cocycleTensorSeq_shortExact S b M) n (tateCor H M n z) :=
  tateCor_tateδ (cocycleTensorSeq_shortExact S b M)
    (LinearMap.fst k (↥S.V ⊗[k] ↥M.V) ↥M.V) (cocycleTensorFst_inl S b M)
    (cocycleTensorInr S b M) (cocycleTensorSnd_inr S b M) H n z

end Cocycle

/-! ### The comparison of Tate and Nakayama -/

section Nakayama

variable (A : Rep k G) (b : groupCohomology.cocycles₁ (shiftObj A)) (M : Rep k G)

/-- **The comparison of Tate and Nakayama on a subgroup**: the connecting map of the tensored
extension of the restricted cocycle, followed by the two identifications of degree read on the
subgroup. -/
def resTateNakayamaMap (n : ℤ) :
    ↥(tateModule (resObj H M) n) →ₗ[k] ↥(tateModule (resObj H (tensorObj A M)) (n + 1 + 1)) :=
  (resShiftEquiv H (tensorObj A M) (n + 1)).toLinearMap ∘ₗ
    (tateMap (resHom H (shiftTensorIso A M).hom) (n + 1)).hom ∘ₗ
      (tateδ (cocycleTensorSeq_shortExact (resObj H (shiftObj A))
        (resCocycles₁ H (shiftObj A) b) (resObj H M)) n).hom

theorem resTateNakayamaMap_apply (n : ℤ) (z : ↥(tateModule (resObj H M) n)) :
    resTateNakayamaMap H A b M n z
      = resShiftEquiv H (tensorObj A M) (n + 1)
        (tateMap (resHom H (shiftTensorIso A M).hom) (n + 1)
          (tateδ (cocycleTensorSeq_shortExact (resObj H (shiftObj A))
            (resCocycles₁ H (shiftObj A) b) (resObj H M)) n z)) := rfl

/-- **The comparison of Tate and Nakayama commutes with restriction to a subgroup**, in every
integer degree. -/
theorem tateRes_tateNakayamaMap (n : ℤ) (x : ↥(tateModule M n)) :
    tateRes H (tensorObj A M) (n + 1 + 1) (tateNakayamaMap A b M n x)
      = resTateNakayamaMap H A b M n (tateRes H M n x) := by
  show tateRes H (tensorObj A M) (n + 1 + 1)
      (tateShiftEquiv (tensorObj A M) (n + 1)
        (tateMap (shiftTensorIso A M).hom (n + 1)
          (tateδ (cocycleTensorSeq_shortExact (shiftObj A) b M) n x))) = _
  rw [tateRes_tateShiftEquiv_int, tateRes_naturality, tateRes_tateδ_cocycleTensorSeq,
    resTateNakayamaMap_apply]

/-- **The comparison of Tate and Nakayama commutes with corestriction from a subgroup**, in every
integer degree. -/
theorem tateCor_tateNakayamaMap (n : ℤ) (z : ↥(tateModule (resObj H M) n)) :
    tateCor H (tensorObj A M) (n + 1 + 1) (resTateNakayamaMap H A b M n z)
      = tateNakayamaMap A b M n (tateCor H M n z) := by
  rw [resTateNakayamaMap_apply, tateCor_tateShiftEquiv_int, tateCor_naturality,
    tateCor_tateδ_cocycleTensorSeq]
  rfl

/-- **The comparison of Tate and Nakayama is onto as soon as it is onto on a subgroup from which
corestriction is onto.** -/
theorem surjective_tateNakayamaMap_of_cor (n : ℤ)
    (hres : Function.Surjective (resTateNakayamaMap H A b M n))
    (hcor : Function.Surjective (tateCor H (tensorObj A M) (n + 1 + 1))) :
    Function.Surjective (tateNakayamaMap A b M n) := by
  intro y
  obtain ⟨w, rfl⟩ := hcor y
  obtain ⟨z, rfl⟩ := hres w
  exact ⟨tateCor H M n z, (tateCor_tateNakayamaMap H A b M n z).symm⟩

/-- **The comparison of Tate and Nakayama is injective as soon as it is injective on a subgroup to
which restriction of the coefficients is injective.** -/
theorem injective_tateNakayamaMap_of_res (n : ℤ)
    (hres : Function.Injective (resTateNakayamaMap H A b M n))
    (hM : Function.Injective (tateRes H M n)) :
    Function.Injective (tateNakayamaMap A b M n) := by
  refine fun x x' hx => hM (hres ?_)
  rw [← tateRes_tateNakayamaMap, ← tateRes_tateNakayamaMap, hx]

end Nakayama

/-! ### A class in degree two -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G] (H : Subgroup G) (A : Rep ℤ G) (α : tateModule A 2)
  (M : Rep ℤ G)

/-- **The comparison of Tate and Nakayama on a subgroup, for the cocycle attached to a prescribed
class in degree two.** -/
def resTateNakayamaTwoMap (n : ℤ) :
    ↥(tateModule (resObj H M) n) →ₗ[ℤ] ↥(tateModule (resObj H (tensorObj A M)) (n + 1 + 1)) :=
  resTateNakayamaMap H A (tateTwoCocycle A α) M n

/-- **The comparison of Tate and Nakayama for a class in degree two commutes with restriction to a
subgroup**, in every integer degree. -/
theorem tateRes_tateNakayamaTwoMap (n : ℤ) (x : ↥(tateModule M n)) :
    tateRes H (tensorObj A M) (n + 1 + 1) (tateNakayamaTwoMap A α M n x)
      = resTateNakayamaTwoMap H A α M n (tateRes H M n x) :=
  tateRes_tateNakayamaMap H A (tateTwoCocycle A α) M n x

/-- **The comparison of Tate and Nakayama for a class in degree two commutes with corestriction from
a subgroup**, in every integer degree. -/
theorem tateCor_tateNakayamaTwoMap (n : ℤ) (z : ↥(tateModule (resObj H M) n)) :
    tateCor H (tensorObj A M) (n + 1 + 1) (resTateNakayamaTwoMap H A α M n z)
      = tateNakayamaTwoMap A α M n (tateCor H M n z) :=
  tateCor_tateNakayamaMap H A (tateTwoCocycle A α) M n z

/-- **The comparison of Tate and Nakayama for a class in degree two is onto as soon as it is onto on
a subgroup from which corestriction is onto.** -/
theorem surjective_tateNakayamaTwoMap_of_cor (n : ℤ)
    (hres : Function.Surjective (resTateNakayamaTwoMap H A α M n))
    (hcor : Function.Surjective (tateCor H (tensorObj A M) (n + 1 + 1))) :
    Function.Surjective (tateNakayamaTwoMap A α M n) :=
  surjective_tateNakayamaMap_of_cor H A (tateTwoCocycle A α) M n hres hcor

/-- **The comparison of Tate and Nakayama for a class in degree two is injective as soon as it is
injective on a subgroup to which restriction of the coefficients is injective.** -/
theorem injective_tateNakayamaTwoMap_of_res (n : ℤ)
    (hres : Function.Injective (resTateNakayamaTwoMap H A α M n))
    (hM : Function.Injective (tateRes H M n)) :
    Function.Injective (tateNakayamaTwoMap A α M n) :=
  injective_tateNakayamaMap_of_res H A (tateTwoCocycle A α) M n hres hM

end DegreeTwo

end

end InverseGalois.CFT.Tate
