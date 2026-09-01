/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.DivisionResidue

/-!
# The residue field of the base field inside the residue ring

The absolute value of a division algebra over a nonarchimedean local field restricts on the scalars
to the absolute value of the base field, so the integers of the base field land in the integers of
the algebra and two scalars which are congruent stay congruent.  The residue field of the base field
therefore maps to the residue ring of the algebra, and the map is injective because the source is a
field.

This is what makes the residue ring an algebra over the residue field of the base field, which is
the setting in which the residue degree of an extension is read off.

## Main definitions

* `InverseGalois.CFT.divisionResidueBase`: the residue field of the base field inside the residue
  ring of the algebra.

## Main results

* `InverseGalois.CFT.divisionResidueBase_injective`: **the map on residues is injective.**

## Tags

local field, division algebra, residue field, residue degree
-/

universe u

namespace InverseGalois.CFT

variable {K D : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

omit [IsUltrametricDist K] [ProperSpace K] in
/-- On the base field the absolute value of the algebra is the absolute value of the field. -/
theorem divisionNorm_base (k : K) : divisionNorm K K k = ‖k‖ := by
  simpa using divisionNorm_algebraMap (K := K) (D := K) k

variable (D) in
/-- The integers of the base field inside the integers of the algebra. -/
noncomputable def divisionIntegersBase : divisionIntegers K K →+* divisionIntegers K D :=
  RingHom.codRestrict ((algebraMap K D).comp (divisionIntegers K K).subtype)
    (divisionIntegers K D) fun x => by
      have hx : ((algebraMap K D).comp (divisionIntegers K K).subtype) x
          = algebraMap K D (x : K) := rfl
      have hx2 : divisionNorm K K (x : K) ≤ 1 := mem_divisionIntegers.1 x.2
      rw [hx, mem_divisionIntegers, divisionNorm_algebraMap]
      rwa [divisionNorm_base] at hx2

@[simp]
theorem coe_divisionIntegersBase (x : divisionIntegers K K) :
    ((divisionIntegersBase D x : divisionIntegers K D) : D) = algebraMap K D (x : K) := rfl

variable (D) in
/-- **The residue field of the base field inside the residue ring of the algebra.** -/
noncomputable def divisionResidueBase : DivisionResidue K K →+* DivisionResidue K D :=
  (divisionResidueCon K K).lift
    (((divisionResidueCon K D).mk').comp (divisionIntegersBase D))
    (by
      intro x y h
      have h' : divisionNorm K K ((x : K) - (y : K)) < 1 := h
      rw [RingCon.ker_apply]
      simp only [RingHom.comp_apply, RingCon.coe_mk']
      refine divisionResidue_eq_iff.2 ?_
      rw [coe_divisionIntegersBase, coe_divisionIntegersBase, ← map_sub, divisionNorm_algebraMap]
      rwa [divisionNorm_base] at h')

@[simp]
theorem divisionResidueBase_coe (x : divisionIntegers K K) :
    divisionResidueBase D ((x : divisionIntegers K K) : DivisionResidue K K)
      = ((divisionIntegersBase D x : divisionIntegers K D) : DivisionResidue K D) := rfl

/-- **The map on residues is injective**, because the residue ring of the base field is a finite
domain and therefore a field. -/
theorem divisionResidueBase_injective :
    Function.Injective (divisionResidueBase (K := K) D) := by
  haveI : IsField (DivisionResidue K K) := Finite.isField_of_domain _
  letI := this.toField
  exact (divisionResidueBase (K := K) D).injective

end InverseGalois.CFT
