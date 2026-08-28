/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.RestrictLE

/-!
# The subfield cut out by a quotient of the Galois group

A homomorphism from the Galois group of an intermediate field onto a group singles out a smaller
intermediate field, the fixed field of its kernel.  Read inside the ambient field rather than
inside the intermediate field it was carved from, that subfield can be compared with the other
intermediate fields at hand, and the restriction homomorphism between the two Galois groups is
exactly the given homomorphism once the target is identified with the quotient by the kernel.

This is the construction the shrinking process of the dyadic Scholz–Reichardt induction runs on: a
large field realising a free object of high rank is cut down to the fixed field of the kernel of a
collapse, and elements of the large field fixed by that kernel become elements of the small one.

## Main definitions

* `InverseGalois.CFT.kerField`: the fixed field of the kernel of a homomorphism out of the Galois
  group, read inside the ambient field.
* `InverseGalois.CFT.toKerField`: an element fixed by the kernel, read as an element of that
  subfield.

## Main results

* `InverseGalois.CFT.ker_galRestrictLE_kerField`: **restriction to the cut-out subfield has exactly
  the given kernel.**
* `InverseGalois.CFT.galEquivKerField`: **the Galois group of the cut-out subfield is the target of
  the homomorphism**, compatibly with restriction.

## Tags

intermediate field, fixed field, Galois group, quotient, restriction
-/

namespace InverseGalois.CFT

open IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-! ### Restricting a lifted subfield -/

/-- **Reading a subfield of an intermediate field inside the ambient field and then back again
returns it unchanged.** -/
theorem restrict_lift {A : IntermediateField F L} (B : IntermediateField F ↥A) :
    IntermediateField.restrict (IntermediateField.lift_le B) = B := by
  ext x
  rw [IntermediateField.mem_restrict, IntermediateField.mem_lift]

/-! ### The subfield cut out by a homomorphism -/

variable {A : IntermediateField F L} [FiniteDimensional F ↥A] [IsGalois F ↥A] {G : Type*} [Group G]

/-- **The subfield cut out by a homomorphism out of the Galois group**: the fixed field of its
kernel, read inside the ambient field. -/
noncomputable def kerField (π : Gal(↥A/F) →* G) : IntermediateField F L :=
  IntermediateField.lift (IntermediateField.fixedField π.ker)

variable (π : Gal(↥A/F) →* G)

omit [FiniteDimensional F ↥A] [IsGalois F ↥A] in
theorem kerField_le : kerField π ≤ A := IntermediateField.lift_le _

omit [FiniteDimensional F ↥A] [IsGalois F ↥A] in
theorem restrict_kerField :
    IntermediateField.restrict (kerField_le π) = IntermediateField.fixedField π.ker :=
  restrict_lift _

/-- The cut-out subfield is isomorphic to the fixed field it was lifted from. -/
noncomputable def kerFieldAlgEquiv : ↥(IntermediateField.fixedField π.ker) ≃ₐ[F] ↥(kerField π) :=
  IntermediateField.liftAlgEquiv _

instance isGalois_kerField : IsGalois F ↥(kerField π) :=
  IsGalois.of_algEquiv (kerFieldAlgEquiv π)

instance finiteDimensional_kerField : FiniteDimensional F ↥(kerField π) :=
  (kerFieldAlgEquiv π).toLinearEquiv.finiteDimensional

/-- **Restriction to the cut-out subfield has exactly the given kernel.** -/
theorem ker_galRestrictLE_kerField : (galRestrictLE (kerField_le π)).ker = π.ker := by
  rw [ker_galRestrictLE, restrict_kerField, IntermediateField.fixingSubgroup_fixedField]

/-! ### The Galois group of the cut-out subfield -/

variable (hπ : Function.Surjective π)

include hπ in
/-- **The Galois group of the cut-out subfield is the target of the homomorphism.**  Both are the
quotient of the Galois group of the ambient intermediate field by the kernel. -/
noncomputable def galEquivKerField : Gal(↥(kerField π)/F) ≃* G :=
  ((QuotientGroup.quotientKerEquivOfSurjective _
        (galRestrictLE_surjective (kerField_le π))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (ker_galRestrictLE_kerField π))).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)

/-- **The isomorphism of the Galois group of the cut-out subfield with the target is compatible
with restriction.** -/
theorem galEquivKerField_galRestrictLE (σ : Gal(↥A/F)) :
    galEquivKerField π hπ (galRestrictLE (kerField_le π) σ) = π σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (galRestrictLE (kerField_le π))
      (galRestrictLE_surjective (kerField_le π))).symm (galRestrictLE (kerField_le π) σ)
      = QuotientGroup.mk σ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (QuotientGroup.quotientKerEquivOfSurjective π hπ)
    ((QuotientGroup.quotientMulEquivOfEq (ker_galRestrictLE_kerField π))
      ((QuotientGroup.quotientKerEquivOfSurjective (galRestrictLE (kerField_le π))
        (galRestrictLE_surjective (kerField_le π))).symm
        (galRestrictLE (kerField_le π) σ))) = π σ
  rw [h]
  rfl

/-! ### Elements of the cut-out subfield -/

omit [FiniteDimensional F ↥A] [IsGalois F ↥A] in
/-- An element fixed by the kernel of the homomorphism lies in the cut-out subfield. -/
theorem coe_mem_kerField {y : ↥A} (hy : ∀ σ : Gal(↥A/F), π σ = 1 → σ y = y) :
    (y : L) ∈ kerField π :=
  (IntermediateField.mem_lift y).mpr
    ((IntermediateField.mem_fixedField_iff _ y).mpr fun σ hσ => hy σ (MonoidHom.mem_ker.mp hσ))

/-- **An element fixed by the kernel of the homomorphism, read as an element of the cut-out
subfield.** -/
noncomputable def toKerField {y : ↥A} (hy : ∀ σ : Gal(↥A/F), π σ = 1 → σ y = y) :
    ↥(kerField π) :=
  ⟨(y : L), coe_mem_kerField π hy⟩

omit [FiniteDimensional F ↥A] [IsGalois F ↥A] in
@[simp]
theorem coe_toKerField {y : ↥A} (hy : ∀ σ : Gal(↥A/F), π σ = 1 → σ y = y) :
    ((toKerField π hy : ↥(kerField π)) : L) = (y : L) := rfl

omit [FiniteDimensional F ↥A] [IsGalois F ↥A] in
/-- **The image of a fixed element in the ambient intermediate field is the element itself.** -/
theorem inclusion_toKerField {y : ↥A} (hy : ∀ σ : Gal(↥A/F), π σ = 1 → σ y = y) :
    IntermediateField.inclusion (kerField_le π) (toKerField π hy) = y := rfl

/-! ### Comparing the subfields cut out at two levels -/

/-- **The subfield cut out by a homomorphism is contained in the one cut out by a homomorphism
above it**, whenever the two are compatible with restriction.  An automorphism killed by the
homomorphism above restricts to one killed by the homomorphism below, so it fixes everything the
lower kernel does. -/
theorem kerField_le_kerField {A B : IntermediateField F L} (hAB : A ≤ B) [FiniteDimensional F ↥A]
    [IsGalois F ↥A] [FiniteDimensional F ↥B] [IsGalois F ↥B] {G G' : Type*} [Group G] [Group G']
    (πA : Gal(↥A/F) →* G) (πB : Gal(↥B/F) →* G') (g : G' →* G)
    (hg : ∀ τ, πA (galRestrictLE hAB τ) = g (πB τ)) : kerField πA ≤ kerField πB := by
  intro x hx
  have hxA : x ∈ A := kerField_le πA hx
  have hfix : ∀ σ : Gal(↥A/F), πA σ = 1 → σ ⟨x, hxA⟩ = ⟨x, hxA⟩ := fun σ hσ =>
    (IntermediateField.mem_fixedField_iff _ _).mp
      ((IntermediateField.mem_lift (⟨x, hxA⟩ : ↥A)).mp hx) σ (MonoidHom.mem_ker.mpr hσ)
  refine coe_mem_kerField πB (y := ⟨x, hAB hxA⟩) fun τ hτ => Subtype.ext ?_
  have h1 : πA (galRestrictLE hAB τ) = 1 := by rw [hg, hτ, map_one]
  have hcoe : ((galRestrictLE hAB τ ⟨x, hxA⟩ : ↥A) : L) = ((⟨x, hxA⟩ : ↥A) : L) := by
    rw [hfix _ h1]
  rw [coe_galRestrictLE hAB τ ⟨x, hxA⟩] at hcoe
  exact hcoe

end InverseGalois.CFT
