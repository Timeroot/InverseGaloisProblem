/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Compositum

/-!
# Restricting an automorphism to a smaller intermediate field

Two intermediate fields `E ≤ E'` of the same extension are not related by an algebra structure that
`Mathlib` finds on its own, so the restriction of an automorphism of `E'` to `E` has to be routed
through the copy of `E` inside `E'`, which is `IntermediateField.restrict`.  This module packages
that route once and for all: the restriction homomorphism, and the fact that it does nothing but
apply the automorphism, read inside the ambient field.

## Main definitions

* `InverseGalois.CFT.galRestrictLE`: restriction of an automorphism of the larger intermediate
  field to the smaller one, which is normal over the base.

## Main results

* `InverseGalois.CFT.coe_galRestrictLE`: **the restriction acts as the original automorphism**,
  read inside the ambient field.
* `InverseGalois.CFT.galRestrictLE_galRestrictLE`: **restricting twice is restricting once.**

## Tags

intermediate field, restriction, Galois group, normal extension
-/

namespace InverseGalois.CFT

open IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {E E' : IntermediateField F L}

/-- An intermediate field that is normal over the base stays normal when viewed as an intermediate
field of a larger intermediate field. -/
instance normalRestrictLE (h : E ≤ E') [Normal F ↥E] :
    Normal F ↥(IntermediateField.restrict h) :=
  Normal.of_algEquiv (IntermediateField.restrict_algEquiv h)

/-- **Restriction of an automorphism of the larger intermediate field to the smaller one**, which
is normal over the base. -/
noncomputable def galRestrictLE (h : E ≤ E') [Normal F ↥E] : Gal(↥E'/F) →* Gal(↥E/F) :=
  (AlgEquiv.autCongr (IntermediateField.restrict_algEquiv h)).symm.toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (IntermediateField.restrict h))

/-- **The restriction acts as the original automorphism**, read inside the ambient field. -/
theorem coe_galRestrictLE (h : E ≤ E') [Normal F ↥E] (σ : Gal(↥E'/F)) (x : ↥E) :
    ((galRestrictLE h σ x : ↥E) : L) = ((σ ⟨(x : L), h x.2⟩ : ↥E') : L) :=
  coe_autCongr_symm_restrictNormalHom h σ x

/-- **Restricting twice is restricting once.** -/
theorem galRestrictLE_galRestrictLE {E'' : IntermediateField F L} (h : E ≤ E') (h' : E' ≤ E'')
    [Normal F ↥E] [Normal F ↥E'] (σ : Gal(↥E''/F)) :
    galRestrictLE h (galRestrictLE h' σ) = galRestrictLE (h.trans h') σ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [coe_galRestrictLE h, coe_galRestrictLE h', coe_galRestrictLE (h.trans h')]

/-- **Every automorphism of a normal subextension extends to the larger intermediate field**, when
that too is normal over the base. -/
theorem galRestrictLE_surjective (h : E ≤ E') [Normal F ↥E] [Normal F ↥E'] :
    Function.Surjective (galRestrictLE h) :=
  (AlgEquiv.autCongr (IntermediateField.restrict_algEquiv h)).symm.surjective.comp
    (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥(IntermediateField.restrict h))
      (E := ↥E'))

end InverseGalois.CFT
