/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DeltaRetract
import InverseGalois.CFT.TateCohomology.Restrict
import InverseGalois.CFT.TateCohomology.RestrictNatural
import InverseGalois.CFT.TateCohomology.ShiftSplit
import InverseGalois.CFT.TateCohomology.TensorFunctor
import InverseGalois.CFT.TateCohomology.TensorShift

/-!
# The shift of a representation read on a subgroup

The shift of a representation is the quotient of the functions on the group by the record of all
the translates of a vector.  Read on a subgroup it is still the functions on the whole group, while
the shift of the representation read on the subgroup is the functions on the subgroup only: the two
are different modules, and the second is not the first read on the subgroup.

They are nevertheless compared, and canonically so.  A short exact sequence which is split as a
sequence of modules is compared with the sequence defining the shift of its sub by the retraction of
the injection and a section of the surjection; the sequence defining the shift, read on a subgroup,
is split by the value at the unit of the group and by subtracting the record of the translates of
that value, and both splittings are already the ones used for the whole group.  The comparison they
produce is the map which restricts a function of the group to the subgroup and subtracts the
translates of its value at the unit.

That map is exactly the difference between the two identifications raising the degree by one — the
one built on the subgroup for the restricted representation and the one obtained by restricting the
map built on the whole group.  It is also compatible with the passage of the shift through a tensor
product, on the nose: both ways round send a class of a function tensored with a vector to the class
of the function of the subgroup whose value is the corrected value tensored with the translate of
the vector.

## Main definitions

* `InverseGalois.CFT.Tate.resShiftHom`: **the comparison of the shift of a representation read on a
  subgroup with the shift of the representation read on the subgroup.**

## Main results

* `InverseGalois.CFT.Tate.resShiftEquiv_eq_tateShiftEquiv`: **the identification raising the degree
  on a subgroup is the identification of the restricted representation, composed with the
  comparison.**
* `InverseGalois.CFT.Tate.resShiftHom_mk`: the comparison restricts a function of the group to the
  subgroup and subtracts the translates of its value at the unit.
* `InverseGalois.CFT.Tate.resShiftHom_shiftTensorIso`: **the comparison commutes with the passage of
  the shift through a tensor product.**

## Tags

Tate cohomology, dimension shifting, restriction, subgroup, tensor product
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **The comparison of the shift of a representation read on a subgroup with the shift of the
representation read on the subgroup.**  It is the comparison of a split sequence with the sequence
defining the shift, for the splitting given by the value at the unit of the group and by subtracting
the record of the translates of that value. -/
def resShiftHom (H : Subgroup G) (A : Rep k G) :
    resObj H (shiftObj A) ⟶ shiftObj (resObj H A) :=
  retractQuotHom (resSeq_shortExact (shiftSeq_shortExact A) H)
    (coindRetract k G (V := ↥A.V)) (coindRetract_shiftSeq_f A)
    (shiftSection A.ρ) (shiftSeq_hom_shiftSection A)

/-- **The identification raising the degree by one on a subgroup is the identification of the
restricted representation, composed with the comparison of the two shifts.** -/
theorem resShiftEquiv_eq_tateShiftEquiv (H : Subgroup G) (A : Rep k G) (n : ℤ)
    (z : ↥(tateModule (resObj H (shiftObj A)) n)) :
    resShiftEquiv H A n z = tateShiftEquiv (resObj H A) n (tateMap (resShiftHom H A) n z) :=
  tateδ_eq_retractQuot (resSeq_shortExact (shiftSeq_shortExact A) H) _ _ _ _ n z

omit [Finite G] in
/-- **The comparison of the two shifts restricts a function of the group to the subgroup and
subtracts the translates of its value at the unit.** -/
theorem resShiftHom_mk (H : Subgroup G) (A : Rep k G) (f : G → ↥A.V) :
    (resShiftHom H A).hom.hom (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (fun h : ↥H => f (h : G) - A.ρ (h : G) (f 1)) := by
  refine congrArg (Submodule.Quotient.mk (p := LinearMap.range (coindEmb (resObj H A).ρ))) ?_
  funext h
  show coindRetract k G
      ((inducedRep k G ↥A.V (h : G)) (shiftSection A.ρ (Submodule.Quotient.mk f)))
    = f (h : G) - A.ρ (h : G) (f 1)
  rw [coindRetract_apply]
  show (shiftSection A.ρ (Submodule.Quotient.mk f)) (1 * (h : G)) = _
  rw [one_mul]
  rfl

/-- **The comparison of the two shifts commutes with the passage of the shift through a tensor
product.** -/
theorem resShiftHom_shiftTensorIso (H : Subgroup G) (A M : Rep k G) :
    resHom H (shiftTensorIso A M).hom ≫ resShiftHom H (tensorObj A M)
      = tensorHomLeft (resObj H M) (resShiftHom H A)
          ≫ (shiftTensorIso (resObj H A) (resObj H M)).hom := by
  refine tensorHomLeft_ext (A := resObj H (shiftObj A))
    (B := shiftObj (tensorObj (resObj H A) (resObj H M))) (resObj H M) fun a m => ?_
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb A.ρ)) a
  show (resShiftHom H (tensorObj A M)).hom.hom
      (shiftTensorEquiv A M (Submodule.Quotient.mk f ⊗ₜ[k] m))
    = shiftTensorEquiv (resObj H A) (resObj H M)
      ((resShiftHom H A).hom.hom (Submodule.Quotient.mk f) ⊗ₜ[k] m)
  rw [shiftTensorEquiv_mk_tmul, resShiftHom_mk, resShiftHom_mk, shiftTensorEquiv_mk_tmul]
  refine congrArg (Submodule.Quotient.mk
    (p := LinearMap.range (coindEmb (tensorObj (resObj H A) (resObj H M)).ρ))) ?_
  funext h
  rw [map_one, Module.End.one_apply, TensorProduct.sub_tmul]
  rfl

end

end InverseGalois.CFT.Tate
