/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.DivisionResidueBase

/-!
# The residue degree of an extension of a local field

Integers of an extension of a nonarchimedean local field whose residues are independent over the
residue field of the base field are themselves independent over the base field: a relation among
them can be rescaled so that its coefficients are integers and at least one of them is a unit, and
reducing the rescaled relation contradicts the independence of the residues.

Consequently the residue field of an extension is no larger than the degree of the extension allows.

## Main results

* `InverseGalois.CFT.card_divisionResidue_le_pow_finrank`: **the residue field of an extension of a
  local field has at most as many elements as the degree of the extension allows.**

## Tags

local field, residue field, residue degree
-/

set_option synthInstance.maxHeartbeats 800000

universe u

namespace InverseGalois.CFT

open Module

variable {K L : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

/-! ### The residue field of the base field -/

/-- The residue ring of a nonarchimedean local field is a field. -/
noncomputable local instance residueBaseField : Field (DivisionResidue K K) :=
  (Finite.isField_of_domain (DivisionResidue K K)).toField

/-- The residue ring of an extension is an algebra over the residue field of the base field. -/
noncomputable local instance residueBaseAlgebra :
    Algebra (DivisionResidue K K) (DivisionResidue K L) :=
  (divisionResidueBase L).toAlgebra

theorem residueBaseAlgebra_smul_def (c : DivisionResidue K K) (z : DivisionResidue K L) :
    c • z = divisionResidueBase L c * z := rfl

/-! ### Lifting a relation -/

/-- An element of the base field of absolute value at most one is an integer. -/
theorem mem_divisionIntegers_base {c : K} (hc : ‖c‖ ≤ 1) : c ∈ divisionIntegers K K :=
  mem_divisionIntegers.2 (by rwa [divisionNorm_base])

/-- **Integers whose residues are independent over the residue field of the base field are
independent over the base field.** -/
theorem linearIndependent_of_linearIndependent_divisionResidue {m : ℕ}
    (y : Fin m → divisionIntegers K L)
    (hy : LinearIndependent (DivisionResidue K K)
      fun i => ((y i : divisionIntegers K L) : DivisionResidue K L)) :
    LinearIndependent K fun i => ((y i : divisionIntegers K L) : L) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin m)) (fun i => ‖c i‖) ⟨i₀, Finset.mem_univ _⟩
  have hcj : c j ≠ 0 := by
    intro h
    exact hi₀ (norm_eq_zero.1 (le_antisymm (by simpa [h] using hj i₀ (Finset.mem_univ _))
      (norm_nonneg _)))
  -- rescale the relation so that the coefficients are integers and the `j`-th one is a unit
  have hdle : ∀ i, ‖c i / c j‖ ≤ 1 := by
    intro i
    rw [norm_div, div_le_one (by positivity)]
    exact hj i (Finset.mem_univ _)
  set D : Fin m → divisionIntegers K K :=
    fun i => ⟨c i / c j, mem_divisionIntegers_base (hdle i)⟩ with hD
  have hDcoe : ∀ i, ((D i : divisionIntegers K K) : K) = c i / c j := fun _ => rfl
  -- the rescaled relation still holds
  have hsum : ∑ i, divisionIntegersBase L (D i) * y i = 0 := by
    have hcoe : ((∑ i, divisionIntegersBase L (D i) * y i : divisionIntegers K L) : L)
        = (c j)⁻¹ • ∑ i, c i • ((y i : divisionIntegers K L) : L) := by
      push_cast
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coe_divisionIntegersBase, hDcoe, smul_smul, Algebra.smul_def, div_eq_inv_mul]
    have hz : ((∑ i, divisionIntegersBase L (D i) * y i : divisionIntegers K L) : L) = 0 := by
      rw [hcoe, hc, smul_zero]
    exact Subtype.ext hz
  -- reduce it
  have hres0 := congrArg (divisionResidueCon K L).mk' hsum
  rw [map_sum, map_zero] at hres0
  simp only [map_mul, RingCon.coe_mk'] at hres0
  have hres : ∑ i, ((D i : divisionIntegers K K) : DivisionResidue K K) •
      ((y i : divisionIntegers K L) : DivisionResidue K L) = 0 := by
    rw [← hres0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [residueBaseAlgebra_smul_def, divisionResidueBase_coe]
  have hzero := Fintype.linearIndependent_iff.1 hy _ hres
  have hone : ((D j : divisionIntegers K K) : DivisionResidue K K) = 1 := by
    have hj1 : D j = 1 := Subtype.ext (by rw [hDcoe]; exact div_self hcj)
    rw [hj1]
    rfl
  exact one_ne_zero (hone ▸ hzero j)

/-! ### The bound on the residue field -/

variable (K L) in
/-- **The residue field of an extension of a local field has at most as many elements as the degree
of the extension allows.** -/
theorem card_divisionResidue_le_pow_finrank :
    Nat.card (DivisionResidue K L) ≤ Nat.card (DivisionResidue K K) ^ finrank K L := by
  classical
  have hle : finrank (DivisionResidue K K) (DivisionResidue K L) ≤ finrank K L := by
    set b := Module.finBasis (DivisionResidue K K) (DivisionResidue K L) with hb
    choose y hy using fun i => (divisionResidueCon K L).mk'_surjective (b i)
    have hind : LinearIndependent K fun i => ((y i : divisionIntegers K L) : L) := by
      refine linearIndependent_of_linearIndependent_divisionResidue y ?_
      have hEq : (fun i => ((y i : divisionIntegers K L) : DivisionResidue K L)) = b := by
        funext i
        exact hy i
      rw [hEq]
      exact b.linearIndependent
    simpa using hind.fintype_card_le_finrank
  calc Nat.card (DivisionResidue K L)
      = Nat.card (DivisionResidue K K) ^ finrank (DivisionResidue K K) (DivisionResidue K L) :=
        Module.natCard_eq_pow_finrank
    _ ≤ Nat.card (DivisionResidue K K) ^ finrank K L :=
        Nat.pow_le_pow_right Nat.card_pos hle

end InverseGalois.CFT
