/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorExtension
import InverseGalois.CFT.TateCohomology.TateDegreeTwo

/-!
# Raising the degree by two with coefficients in a tensor product

A class in degree two of a representation is the class of a one cocycle of its shift, and that
cocycle twists the sum of the shift and the base ring into an extension of the base ring by the
shift.  The extension splits as a module, so it may be tensored with an arbitrary representation
and stays an extension: of that representation by the shift tensored with it.

The shift tensored with a representation is the shift of the tensor product, so the connecting map
of the tensored extension reads as a map from the complete cohomology of the representation in a
degree to the complete cohomology of the tensor product two degrees higher.  It is bijective
exactly when the tensored extension has no complete cohomology; that is the one thing the splitting
of the extension does not supply on its own, and it is carried here as a hypothesis.

Over the integers the cocycle may be taken to be the one attached to a prescribed class in degree
two, and the conclusion is then the classical statement: the complete cohomology of a
representation in a degree is the complete cohomology of its tensor product with the coefficients
two degrees higher.

## Main definitions

* `InverseGalois.CFT.Tate.tateNakayamaShiftEquiv`: the connecting map of the tensored extension.

## Main results

* `InverseGalois.CFT.Tate.isZero_tateModule_cocycleTensorObj`: **the tensored extension has no
  complete cohomology as soon as the extension itself keeps none after tensoring.**
* `InverseGalois.CFT.Tate.tateNakayamaEquiv`: **the complete cohomology of a representation in a
  degree is the complete cohomology of its tensor product with the coefficients two degrees
  higher.**
* `InverseGalois.CFT.Tate.tateNakayamaTwoEquiv`: the same, for the cocycle attached to a prescribed
  class in degree two.

## Tags

Tate cohomology, Tate–Nakayama, tensor product, fundamental class, dimension shifting
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### The tensored extension -/

section Nakayama

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  (A : Rep k G) (b : groupCohomology.cocycles₁ (shiftObj A)) (M : Rep k G)

/-- **The tensored extension has no complete cohomology** as soon as the extension itself keeps
none after tensoring. -/
theorem isZero_tateModule_cocycleTensorObj
    (h : ∀ m : ℤ, Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) m))
    (n : ℤ) : Limits.IsZero (tateModule (cocycleTensorObj (shiftObj A) b M) n) :=
  isZero_tateModule_of_iso (cocycleTensorIso (shiftObj A) M b).symm n (h n)

/-- **The connecting map of the tensored extension**: the complete cohomology of a representation
in a degree is the complete cohomology of the shift tensored with it in the following degree. -/
def tateNakayamaShiftEquiv
    (h : ∀ m : ℤ, Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) m))
    (n : ℤ) : tateModule M n ≃ₗ[k] tateModule (tensorObj (shiftObj A) M) (n + 1) :=
  LinearEquiv.ofBijective (tateδ (cocycleTensorSeq_shortExact (shiftObj A) b M) n).hom
    (bijective_tateδ (cocycleTensorSeq_shortExact (shiftObj A) b M) n
      (isZero_tateModule_cocycleTensorObj A b M h n)
      (isZero_tateModule_cocycleTensorObj A b M h (n + 1)))

/-- **The complete cohomology of a representation in a degree is the complete cohomology of its
tensor product with the coefficients two degrees higher.** -/
def tateNakayamaEquiv
    (h : ∀ m : ℤ, Limits.IsZero (tateModule (tensorObj (cocycleObj (shiftObj A) b) M) m))
    (n : ℤ) : tateModule M n ≃ₗ[k] tateModule (tensorObj A M) (n + 1 + 1) :=
  ((tateNakayamaShiftEquiv A b M h n).trans
      (tateMapIso (shiftTensorIso A M) (n + 1)).toLinearEquiv).trans
    (tateShiftEquiv (tensorObj A M) (n + 1))

end Nakayama

/-! ### A class in degree two -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G]

/-- **The complete cohomology of a representation in a degree is the complete cohomology of its
tensor product with the coefficients two degrees higher**, for the cocycle attached to a prescribed
class in degree two. -/
def tateNakayamaTwoEquiv (A : Rep ℤ G) (α : tateModule A 2) (M : Rep ℤ G)
    (h : ∀ m : ℤ, Limits.IsZero
      (tateModule (tensorObj (cocycleObj (shiftObj A) (tateTwoCocycle A α)) M) m))
    (n : ℤ) : tateModule M n ≃ₗ[ℤ] tateModule (tensorObj A M) (n + 1 + 1) :=
  tateNakayamaEquiv A (tateTwoCocycle A α) M h n

end DegreeTwo

end

end InverseGalois.CFT.Tate
