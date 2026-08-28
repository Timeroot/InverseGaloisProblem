/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.RestrictLE

/-!
# The subfield cut out by a homomorphism of a Galois group

A surjection of the Galois group of a finite Galois extension onto a group `G` realises `G` as the
Galois group of the fixed field of its kernel.  That fixed field is an intermediate field of the
extension, and lifting it back to the ambient field turns it into a subfield of the same ambient
field, so that further fields can be composed with it.

The identification of its Galois group with `G` is a special case of a purely group-theoretic
statement: two surjections out of the same group with the same kernel identify their targets, and
the identification is compatible with the two surjections.

## Main definitions

* `InverseGalois.CFT.mulEquivOfKerEq`: the isomorphism of the targets of two surjections with the
  same kernel.
* `InverseGalois.CFT.cutField`: the subfield of the ambient field cut out by a homomorphism of the
  Galois group.
* `InverseGalois.CFT.galEquivCutField`: **the Galois group of the cut field is the target of the
  homomorphism.**

## Main results

* `InverseGalois.CFT.ker_galRestrictLE_cutField`: **restriction to the cut field has exactly the
  kernel of the homomorphism.**
* `InverseGalois.CFT.galEquivCutField_galRestrictLE`: **the identification of the Galois group of
  the cut field with the target undoes the restriction.**
* `InverseGalois.CFT.le_cutField`: a subextension on which the kernel acts trivially lies inside
  the cut field.
* `InverseGalois.CFT.cutField_le_cutField`: **a homomorphism with the smaller kernel cuts out the
  larger field.**
* `InverseGalois.CFT.cutField_eq_of_ker_eq`: **the field cut out by a homomorphism depends on its
  kernel alone.**
* `InverseGalois.CFT.cutField_eq_self_of_ker_eq_bot`: an injective homomorphism cuts out the whole
  field.
* `InverseGalois.CFT.cutField_comp_galRestrictLE`: **pulling a homomorphism back along a
  restriction does not change the field it cuts out.**

## Tags

Galois group, fixed field, intermediate field, quotient group
-/

namespace InverseGalois.CFT

open IntermediateField

/-! ### Two surjections with the same kernel -/

section Group

variable {A B C : Type*} [Group A] [Group B] [Group C]

/-- **Two surjections out of the same group with the same kernel identify their targets.**  Both
targets are the quotient by that kernel. -/
noncomputable def mulEquivOfKerEq (u : A →* B) (hu : Function.Surjective u) (v : A →* C)
    (hv : Function.Surjective v) (h : u.ker = v.ker) : B ≃* C :=
  (QuotientGroup.quotientKerEquivOfSurjective u hu).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective v hv))

/-- **The identification of the targets of two surjections with the same kernel carries one
surjection to the other.** -/
@[simp]
theorem mulEquivOfKerEq_apply (u : A →* B) (hu : Function.Surjective u) (v : A →* C)
    (hv : Function.Surjective v) (h : u.ker = v.ker) (a : A) :
    mulEquivOfKerEq u hu v hv h (u a) = v a := by
  have h1 : QuotientGroup.quotientKerEquivOfSurjective u hu (QuotientGroup.mk a) = u a := rfl
  rw [mulEquivOfKerEq, MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
  rfl

end Group

/-! ### The cut field -/

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {E : IntermediateField F L}
variable [FiniteDimensional F ↥E] [IsGalois F ↥E] {G : Type*} [Group G] (ψ : Gal(↥E/F) →* G)

/-- **The subfield of the ambient field cut out by a homomorphism of the Galois group**: the fixed
field of its kernel, read inside the ambient field. -/
def cutField : IntermediateField F L :=
  IntermediateField.lift (IntermediateField.fixedField ψ.ker)

omit [FiniteDimensional F ↥E] [IsGalois F ↥E] in
/-- The cut field sits inside the field the homomorphism is defined on. -/
theorem cutField_le : cutField ψ ≤ E :=
  IntermediateField.lift_le _

/-- The cut field is isomorphic to the fixed field of the kernel it was lifted from. -/
noncomputable def cutFieldAlgEquiv : ↥(IntermediateField.fixedField ψ.ker) ≃ₐ[F] ↥(cutField ψ) :=
  IntermediateField.liftAlgEquiv (IntermediateField.fixedField ψ.ker)

/-- The cut field is normal over the base, the kernel being a normal subgroup. -/
instance normal_cutField : Normal F ↥(cutField ψ) :=
  Normal.of_algEquiv (cutFieldAlgEquiv ψ)

instance isGalois_cutField : IsGalois F ↥(cutField ψ) :=
  IsGalois.of_algEquiv (cutFieldAlgEquiv ψ)

instance finiteDimensional_cutField : FiniteDimensional F ↥(cutField ψ) :=
  (cutFieldAlgEquiv ψ).toLinearEquiv.finiteDimensional

omit [FiniteDimensional F ↥E] [IsGalois F ↥E] in
/-- Read inside the field the homomorphism is defined on, the cut field is the fixed field of the
kernel. -/
theorem restrict_cutField_le :
    IntermediateField.restrict (cutField_le ψ) = IntermediateField.fixedField ψ.ker :=
  IntermediateField.lift_injective E (by rw [IntermediateField.lift_restrict]; rfl)

/-- **Restriction to the cut field has exactly the kernel of the homomorphism.** -/
theorem ker_galRestrictLE_cutField : (galRestrictLE (cutField_le ψ)).ker = ψ.ker := by
  rw [ker_galRestrictLE, restrict_cutField_le, IntermediateField.fixingSubgroup_fixedField]

/-- **The Galois group of the cut field is the target of the homomorphism.** -/
noncomputable def galEquivCutField (hψ : Function.Surjective ψ) :
    Gal(↥(cutField ψ)/F) ≃* G :=
  mulEquivOfKerEq (galRestrictLE (cutField_le ψ)) (galRestrictLE_surjective _) ψ hψ
    (ker_galRestrictLE_cutField ψ)

/-- **The identification of the Galois group of the cut field with the target undoes the
restriction.** -/
@[simp]
theorem galEquivCutField_galRestrictLE (hψ : Function.Surjective ψ) (σ : Gal(↥E/F)) :
    galEquivCutField ψ hψ (galRestrictLE (cutField_le ψ) σ) = ψ σ :=
  mulEquivOfKerEq_apply _ _ _ _ _ σ

omit [FiniteDimensional F ↥E] [IsGalois F ↥E] in
/-- **A subextension on which the kernel acts trivially lies inside the cut field.** -/
theorem le_cutField {A : IntermediateField F L} (hAE : A ≤ E) [Normal F ↥A]
    (h : ψ.ker ≤ (galRestrictLE hAE).ker) : A ≤ cutField ψ := by
  have hle : IntermediateField.restrict hAE ≤ IntermediateField.fixedField ψ.ker :=
    (IntermediateField.le_iff_le _ _).mpr (by rwa [← ker_galRestrictLE hAE])
  intro x hx
  exact (IntermediateField.mem_lift ⟨x, hAE hx⟩).mpr
    (hle ((IntermediateField.mem_restrict hAE ⟨x, hAE hx⟩).mpr hx))

/-! ### Comparing cut fields -/

section Compare

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

/-- **A homomorphism with the smaller kernel cuts out the larger field.** -/
theorem cutField_le_cutField (ψ₁ : Gal(↥E/F) →* G₁) (ψ₂ : Gal(↥E/F) →* G₂)
    (h : ψ₁.ker ≤ ψ₂.ker) : cutField ψ₂ ≤ cutField ψ₁ :=
  le_cutField ψ₁ (cutField_le ψ₂) (by rw [ker_galRestrictLE_cutField]; exact h)

omit [FiniteDimensional F ↥E] [IsGalois F ↥E] in
/-- **The field cut out by a homomorphism depends on its kernel alone.** -/
theorem cutField_eq_of_ker_eq (ψ₁ : Gal(↥E/F) →* G₁) (ψ₂ : Gal(↥E/F) →* G₂)
    (h : ψ₁.ker = ψ₂.ker) : cutField ψ₁ = cutField ψ₂ := by
  unfold cutField
  rw [h]

omit [FiniteDimensional F ↥E] [IsGalois F ↥E] in
/-- **An injective homomorphism cuts out the whole field.** -/
theorem cutField_eq_self_of_ker_eq_bot (ψ₁ : Gal(↥E/F) →* G₁) (h : ψ₁.ker = ⊥) :
    cutField ψ₁ = E := by
  unfold cutField
  rw [h, IntermediateField.fixedField_bot, IntermediateField.lift_top]

end Compare

/-! ### Pulling a homomorphism back to a larger field -/

section Tower

variable {E' : IntermediateField F L} [FiniteDimensional F ↥E'] [IsGalois F ↥E']

omit [FiniteDimensional F ↥E] in
/-- The field cut out by the restriction to a smaller intermediate field is that field. -/
theorem cutField_galRestrictLE (h : E ≤ E') : cutField (galRestrictLE h) = E := by
  rw [cutField, fixedField_ker_galRestrictLE h, IntermediateField.lift_restrict]

/-- **Pulling a homomorphism back along a restriction does not change the field it cuts out.**
Both kernels consist of the automorphisms acting trivially on the same subfield. -/
theorem cutField_comp_galRestrictLE (h : E ≤ E') (ψ : Gal(↥E/F) →* G) :
    cutField (ψ.comp (galRestrictLE h)) = cutField ψ := by
  have hker : (galRestrictLE h).ker ≤ (ψ.comp (galRestrictLE h)).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    rw [MonoidHom.comp_apply, hσ, map_one]
  have hA : cutField (ψ.comp (galRestrictLE h)) ≤ E :=
    (cutField_le_cutField _ _ hker).trans (cutField_galRestrictLE h).le
  refine le_antisymm (le_cutField ψ hA fun τ hτ => ?_)
    (le_cutField (ψ.comp (galRestrictLE h)) ((cutField_le ψ).trans h) fun σ hσ => ?_)
  · obtain ⟨σ, rfl⟩ := galRestrictLE_surjective h τ
    have hσ : σ ∈ (galRestrictLE (cutField_le (ψ.comp (galRestrictLE h)))).ker := by
      rw [ker_galRestrictLE_cutField]
      exact hτ
    rw [MonoidHom.mem_ker, galRestrictLE_galRestrictLE hA h]
    exact hσ
  · have hσ' : galRestrictLE h σ ∈ (galRestrictLE (cutField_le ψ)).ker := by
      rw [ker_galRestrictLE_cutField]
      exact hσ
    rw [MonoidHom.mem_ker, ← galRestrictLE_galRestrictLE (cutField_le ψ) h]
    exact hσ'

end Tower

end InverseGalois.CFT
