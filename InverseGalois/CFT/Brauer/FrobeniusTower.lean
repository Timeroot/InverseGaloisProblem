/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.Frobenius

/-!
# The Frobenius automorphism along a tower of local fields

The absolute value of a finite extension of a nonarchimedean local field is the spectral norm, and
the spectral norm of an element depends only on its minimal polynomial over the base field.  In a
tower the minimal polynomial does not change, so the absolute value of an intermediate field is the
restriction of the absolute value of the top field.

Consequently the integers and the residues of an intermediate field sit inside those of the top
field, an intermediate field of an unramified extension is itself unramified, and **the Frobenius
automorphism of the top field restricts to the Frobenius automorphism of the intermediate field**.
This is the compatibility that makes the normalised invariant of a cyclic algebra independent of the
level of the unramified tower at which it is computed.

## Main definitions

* `InverseGalois.CFT.divisionResidueTower`: the residue field of an intermediate field inside the
  residue field of the top field.

## Main results

* `InverseGalois.CFT.divisionNorm_algebraMap_tower`: **the absolute value of an intermediate field
  is the restriction of the absolute value of the top field.**
* `InverseGalois.CFT.restrictNormal_divisionFrobenius`: **the Frobenius automorphism restricts to
  the Frobenius automorphism.**

## Tags

local field, unramified extension, Frobenius, tower
-/

set_option synthInstance.maxHeartbeats 800000

universe u

namespace InverseGalois.CFT

open Module

variable {K L L' : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Field L'] [Algebra K L'] [FiniteDimensional K L']
variable [Algebra L L'] [IsScalarTower K L L']

/-! ### The absolute value along a tower -/

/-- **The absolute value of an intermediate field of a tower of local fields is the restriction of
the absolute value of the top field**, because both are the spectral norm and the minimal polynomial
over the base field does not change. -/
theorem divisionNorm_algebraMap_tower (y : L) :
    divisionNorm K L' (algebraMap L L' y) = divisionNorm K L y := by
  rw [divisionNorm_eq_spectralNorm, divisionNorm_eq_spectralNorm]
  exact (spectralNorm.eq_of_tower (K := K) (L := L') y).symm

/-- **An intermediate field of an unramified extension of a local field is unramified.** -/
theorem unramified_of_unramified_tower
    (hur : ∀ z : L', z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L' z = ‖c‖) :
    ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖ := by
  intro z hz
  obtain ⟨c, hc, hcz⟩ :=
    hur (algebraMap L L' z) ((map_ne_zero_iff _ (algebraMap L L').injective).2 hz)
  exact ⟨c, hc, by rw [← divisionNorm_algebraMap_tower (L' := L'), hcz]⟩

/-! ### The integers and the residues along a tower -/

variable (L') in
/-- The integers of an intermediate field inside the integers of the top field. -/
noncomputable def divisionIntegersTower : divisionIntegers K L →+* divisionIntegers K L' :=
  RingHom.codRestrict ((algebraMap L L').comp (divisionIntegers K L).subtype)
    (divisionIntegers K L') fun x => by
      have hx : ((algebraMap L L').comp (divisionIntegers K L).subtype) x
          = algebraMap L L' (x : L) := rfl
      rw [hx, mem_divisionIntegers, divisionNorm_algebraMap_tower]
      exact mem_divisionIntegers.1 x.2

@[simp]
theorem coe_divisionIntegersTower (x : divisionIntegers K L) :
    ((divisionIntegersTower L' x : divisionIntegers K L') : L') = algebraMap L L' (x : L) := rfl

variable (L') in
/-- **The residue field of an intermediate field inside the residue field of the top field.** -/
noncomputable def divisionResidueTower : DivisionResidue K L →+* DivisionResidue K L' :=
  (divisionResidueCon K L).lift
    (((divisionResidueCon K L').mk').comp (divisionIntegersTower L'))
    (by
      intro x y h
      have h' : divisionNorm K L ((x : L) - (y : L)) < 1 := h
      rw [RingCon.ker_apply]
      simp only [RingHom.comp_apply, RingCon.coe_mk']
      refine divisionResidue_eq_iff.2 ?_
      rw [coe_divisionIntegersTower, coe_divisionIntegersTower, ← map_sub,
        divisionNorm_algebraMap_tower]
      exact h')

@[simp]
theorem divisionResidueTower_coe (x : divisionIntegers K L) :
    divisionResidueTower L' ((x : divisionIntegers K L) : DivisionResidue K L)
      = ((divisionIntegersTower L' x : divisionIntegers K L') : DivisionResidue K L') := rfl

/-- **The map on residues along a tower is injective**, because the residue ring of an intermediate
field is a finite domain and therefore a field. -/
theorem divisionResidueTower_injective :
    Function.Injective (divisionResidueTower (K := K) (L := L) L') := by
  haveI : IsField (DivisionResidue K L) := Finite.isField_of_domain _
  letI := this.toField
  exact (divisionResidueTower (K := K) (L := L) L').injective

/-! ### The Frobenius automorphism along a tower -/

/-- The restriction of an automorphism of the top field to an intermediate field is compatible with
the inclusion of the integers. -/
theorem divisionIntegersTower_divisionIntegersAlgEquiv [Normal K L] (σ : L' ≃ₐ[K] L')
    (x : divisionIntegers K L) :
    divisionIntegersTower L' (divisionIntegersAlgEquiv (σ.restrictNormal L) x)
      = divisionIntegersAlgEquiv σ (divisionIntegersTower L' x) := by
  refine Subtype.ext ?_
  rw [coe_divisionIntegersTower, coe_divisionIntegersAlgEquiv, coe_divisionIntegersAlgEquiv,
    coe_divisionIntegersTower]
  exact σ.restrictNormal_commutes L (x : L)

/-- **The restriction of a Frobenius automorphism to an intermediate field is a Frobenius
automorphism.** -/
theorem isDivisionFrobenius_restrictNormal [Normal K L] {σ : L' ≃ₐ[K] L'}
    (hσ : IsDivisionFrobenius σ) : IsDivisionFrobenius (σ.restrictNormal L) := by
  intro x
  refine divisionResidueTower_injective (L' := L') ?_
  rw [divisionResidueTower_coe, map_pow, divisionResidueTower_coe,
    divisionIntegersTower_divisionIntegersAlgEquiv]
  exact hσ (divisionIntegersTower L' x)

/-- **The Frobenius automorphism of an unramified extension of a local field restricts to the
Frobenius automorphism of an intermediate field.** -/
theorem restrictNormal_divisionFrobenius [Normal K L]
    (hur : ∀ z : L', z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L' z = ‖c‖) :
    (divisionFrobenius K L' hur).restrictNormal L
      = divisionFrobenius K L (unramified_of_unramified_tower hur) :=
  eq_divisionFrobenius K L _
    (isDivisionFrobenius_restrictNormal (isDivisionFrobenius_divisionFrobenius K L' hur))

end InverseGalois.CFT
