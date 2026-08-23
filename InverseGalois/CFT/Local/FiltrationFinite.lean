/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitFiltration

/-!
# Finiteness of the steps of the unit filtration

A valued field whose graded pieces are all finite has finite quotients between any two steps of
the additive filtration: the relative index is multiplicative in towers, and each single step
contributes exactly one graded piece.  The same argument applies to the unit filtration, because
subtracting one carries a step of the unit filtration onto the corresponding graded piece of the
additive filtration with the next step as its kernel.

## Main results

* `InverseGalois.CFT.finite_quotient_valAddSubgroup`: **any two steps of the additive filtration
  have a finite quotient.**
* `InverseGalois.CFT.finite_quotient_valAddSubgroup_zero`: the elements of nonnegative valuation
  have a finite quotient by any later step of the additive filtration.
* `InverseGalois.CFT.finite_quotient_unitFiltrationAdd`: **any two steps of the unit filtration
  have a finite quotient.**

## Tags

valued field, unit filtration, graded piece, finite index, finite residue field
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-! ### Relative indices and finite quotients -/

/-- The quotient of a subgroup by a nested one is finite exactly when the relative index of the
two subgroups is nonzero. -/
theorem finite_quotient_iff_relIndex_ne_zero {G : Type*} [AddGroup G] (H K : AddSubgroup G) :
    Finite (↥K ⧸ H.addSubgroupOf K) ↔ H.relIndex K ≠ 0 :=
  AddSubgroup.index_ne_zero_iff_finite.symm

/-! ### The additive filtration -/

/-- Consecutive steps of the additive filtration have nonzero relative index, since the quotient
between them is a graded piece. -/
theorem relIndex_valAddSubgroup_succ [∀ k : ℤ, Finite (gradedAdd A k)] (j : ℤ) :
    (valAddSubgroup A (j + 1)).relIndex (valAddSubgroup A j) ≠ 0 :=
  (finite_quotient_iff_relIndex_ne_zero _ _).mp inferInstance

/-- A step of the additive filtration a fixed number of places further down has nonzero relative
index. -/
theorem relIndex_valAddSubgroup_add_natCast [∀ k : ℤ, Finite (gradedAdd A k)] (i : ℤ) (n : ℕ) :
    (valAddSubgroup A (i + n)).relIndex (valAddSubgroup A i) ≠ 0 := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, add_zero, AddSubgroup.relIndex_self]
    exact one_ne_zero
  | succ n ih =>
    have hcast : (i : ℤ) + ((n + 1 : ℕ) : ℤ) = i + n + 1 := by push_cast; ring
    rw [hcast]
    exact AddSubgroup.relIndex_ne_zero_trans (relIndex_valAddSubgroup_succ (i + n)) ih

/-- **Any two steps of the additive filtration have a finite quotient**, when every graded piece
of the filtration is finite. -/
theorem finite_quotient_valAddSubgroup [∀ k : ℤ, Finite (gradedAdd A k)] {i j : ℤ} (hij : i ≤ j) :
    Finite (↥(valAddSubgroup A i) ⧸ (valAddSubgroup A j).addSubgroupOf (valAddSubgroup A i)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = i + n := ⟨(j - i).toNat, by omega⟩
  exact (finite_quotient_iff_relIndex_ne_zero _ _).mpr (relIndex_valAddSubgroup_add_natCast i n)

/-- The elements of nonnegative valuation have a finite quotient by any later step of the additive
filtration. -/
theorem finite_quotient_valAddSubgroup_zero [∀ k : ℤ, Finite (gradedAdd A k)] {j : ℤ}
    (hj : 0 ≤ j) :
    Finite (↥(valAddSubgroup A 0) ⧸ (valAddSubgroup A j).addSubgroupOf (valAddSubgroup A 0)) :=
  finite_quotient_valAddSubgroup hj

/-! ### The unit filtration -/

/-- The kernel of subtracting one on a step of the unit filtration is the next step of the unit
filtration, viewed inside that step. -/
theorem ker_gradedUnitHom (i : ℕ) :
    (gradedUnitHom A i).ker
      = (unitFiltrationAdd A (i + 1)).addSubgroupOf (unitFiltrationAdd A i) := by
  ext u
  rw [AddMonoidHom.mem_ker, gradedUnitHom_eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

/-- **The quotient of a step of the unit filtration by the next one is finite**, being isomorphic
to a graded piece of the additive filtration. -/
theorem finite_quotient_unitFiltrationAdd_succ [∀ k : ℤ, Finite (gradedAdd A k)] (i : ℕ) :
    Finite (↥(unitFiltrationAdd A i)
      ⧸ (unitFiltrationAdd A (i + 1)).addSubgroupOf (unitFiltrationAdd A i)) := by
  rw [← ker_gradedUnitHom i]
  exact Finite.of_equiv _
    (QuotientAddGroup.quotientKerEquivOfSurjective (gradedUnitHom A i)
      (gradedUnitHom_surjective i)).symm.toEquiv

/-- Consecutive steps of the unit filtration have nonzero relative index. -/
theorem relIndex_unitFiltrationAdd_succ [∀ k : ℤ, Finite (gradedAdd A k)] (i : ℕ) :
    (unitFiltrationAdd A (i + 1)).relIndex (unitFiltrationAdd A i) ≠ 0 :=
  (finite_quotient_iff_relIndex_ne_zero _ _).mp (finite_quotient_unitFiltrationAdd_succ i)

/-- A step of the unit filtration a fixed number of places further down has nonzero relative
index. -/
theorem relIndex_unitFiltrationAdd_add [∀ k : ℤ, Finite (gradedAdd A k)] (i n : ℕ) :
    (unitFiltrationAdd A (i + n)).relIndex (unitFiltrationAdd A i) ≠ 0 := by
  induction n with
  | zero =>
    rw [Nat.add_zero, AddSubgroup.relIndex_self]
    exact one_ne_zero
  | succ n ih =>
    rw [← Nat.add_assoc]
    exact AddSubgroup.relIndex_ne_zero_trans (relIndex_unitFiltrationAdd_succ (i + n)) ih

/-- **Any two steps of the unit filtration have a finite quotient**, when every graded piece of
the additive filtration is finite. -/
theorem finite_quotient_unitFiltrationAdd [∀ k : ℤ, Finite (gradedAdd A k)] {i j : ℕ}
    (hij : i ≤ j) :
    Finite (↥(unitFiltrationAdd A i)
      ⧸ (unitFiltrationAdd A j).addSubgroupOf (unitFiltrationAdd A i)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = i + n := ⟨j - i, by omega⟩
  exact (finite_quotient_iff_relIndex_ne_zero _ _).mpr (relIndex_unitFiltrationAdd_add i n)

end InverseGalois.CFT
