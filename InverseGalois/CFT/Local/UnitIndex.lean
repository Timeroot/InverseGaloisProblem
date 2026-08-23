/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.FiltrationFinite
import InverseGalois.CFT.Local.UnitFiltration
import InverseGalois.CFT.Local.UnitValuation

/-!
# The unit filtration has finite index in the units of the valuation ring

A unit congruent to one has valuation one, so every step of the unit filtration sits inside the
group of units of the valuation ring, the kernel of the valuation of a unit.  The first step is
already of finite index there as soon as the zeroth graded piece of the additive filtration is
finite: sending a unit of valuation one to its class in that graded piece is not a homomorphism,
but two such units have the same class exactly when their quotient is congruent to one, because
multiplying by a unit of valuation one leaves valuations unchanged.  Injectivity of the induced
map on cosets therefore bounds the number of cosets by the size of the graded piece.  Since the
relative index is multiplicative in towers, every later step of the unit filtration is of finite
index too whenever all the graded pieces of the additive filtration are finite.

## Main results

* `InverseGalois.CFT.unitFiltrationAdd_le_ker_unitVal`: a step of the unit filtration lies inside
  the units of the valuation ring.
* `InverseGalois.CFT.finite_quotient_ker_unitVal_unitFiltrationAdd`: **the first step of the unit
  filtration has finite index in the units of the valuation ring**, when the zeroth graded piece
  of the additive filtration is finite.
* `InverseGalois.CFT.finite_quotient_ker_unitVal`: **every step of the unit filtration has finite
  index in the units of the valuation ring**, when all the graded pieces of the additive
  filtration are finite.

## Tags

valued field, unit filtration, principal units, finite index, residue field
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-! ### The unit filtration inside the units of the valuation ring -/

/-- **A step of the unit filtration lies inside the units of the valuation ring**, since a unit
congruent to one has valuation one. -/
theorem unitFiltrationAdd_le_ker_unitVal (i : ℕ) :
    unitFiltrationAdd A i ≤ (unitVal (A := A)).ker := by
  intro x hx
  rw [mem_ker_unitVal]
  exact valued_eq_one_of_sub_one_lt_one
    (lt_one_of_le_exp_neg (by omega) (mem_unitFiltrationAdd.mp hx))

/-! ### Comparing two units of valuation one -/

/-- Two elements of a step of the additive filtration have the same class in the graded piece
exactly when the valuation of their difference is small enough. -/
theorem gradedAdd_mk_eq_iff {j : ℤ} {x y : ↥(valAddSubgroup A j)} :
    (QuotientAddGroup.mk x : gradedAdd A j) = QuotientAddGroup.mk y ↔
      Valued.v ((x : A) - (y : A)) ≤ WithZero.exp (-(j + 1)) := by
  refine ⟨fun h => ?_, gradedAdd_mk_eq⟩
  have h' := QuotientAddGroup.eq.mp h
  rw [AddSubgroup.mem_addSubgroupOf] at h'
  have hcoe : ((-x + y : ↥(valAddSubgroup A j)) : A) = -((x : A) - (y : A)) := by
    push_cast; ring
  rw [hcoe] at h'
  have hmem := mem_valAddSubgroup.mp ((valAddSubgroup A (j + 1)).neg_mem h')
  rwa [neg_neg] at hmem

/-- The quotient of a unit of valuation one by another unit is congruent to one modulo the first
step of the additive filtration exactly when the difference of the two units has valuation at
most that of a uniformizer. -/
theorem inv_mul_mem_unitFiltration_zero_iff {u w : Aˣ} (hu : Valued.v (u : A) = 1) :
    u⁻¹ * w ∈ unitFiltration A 0 ↔ Valued.v ((u : A) - (w : A)) ≤ WithZero.exp (-1) := by
  have hcoe : ((u⁻¹ * w : Aˣ) : A) - 1 = -(((u : A))⁻¹ * ((u : A) - (w : A))) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ u.ne_zero]
    ring
  rw [mem_unitFiltration, hcoe, Valuation.map_neg, map_mul, map_inv₀, hu, inv_one, one_mul]
  norm_num

/-! ### The class of a unit of the valuation ring in the zeroth graded piece -/

/-- A unit of the valuation ring, viewed among the elements of nonnegative valuation. -/
def kerUnitValToVal (x : ↥(unitVal (A := A)).ker) : ↥(valAddSubgroup A 0) :=
  ⟨((Additive.toMul (x : Additive Aˣ) : Aˣ) : A), by
    refine mem_valAddSubgroup.mpr (le_of_eq ?_)
    rw [mem_ker_unitVal.mp x.2, neg_zero, WithZero.exp_zero]⟩

@[simp]
theorem coe_kerUnitValToVal (x : ↥(unitVal (A := A)).ker) :
    (kerUnitValToVal x : A) = ((Additive.toMul (x : Additive Aˣ) : Aˣ) : A) := rfl

/-- The class of a unit of the valuation ring in the zeroth graded piece of the additive
filtration. -/
def kerUnitValGradedFun (x : ↥(unitVal (A := A)).ker) : gradedAdd A 0 :=
  QuotientAddGroup.mk (kerUnitValToVal x)

/-- Two units of the valuation ring have the same class in the zeroth graded piece of the additive
filtration exactly when they lie in the same coset of the first step of the unit filtration. -/
theorem kerUnitValGradedFun_eq_iff (x y : ↥(unitVal (A := A)).ker) :
    kerUnitValGradedFun x = kerUnitValGradedFun y ↔
      -x + y ∈ (unitFiltrationAdd A 0).addSubgroupOf (unitVal (A := A)).ker := by
  have hstep : (((-x + y : ↥(unitVal (A := A)).ker) : Additive Aˣ) ∈ unitFiltrationAdd A 0)
      ↔ (Additive.toMul (x : Additive Aˣ))⁻¹ * Additive.toMul (y : Additive Aˣ)
          ∈ unitFiltration A 0 := Iff.rfl
  rw [kerUnitValGradedFun, kerUnitValGradedFun, gradedAdd_mk_eq_iff,
    AddSubgroup.mem_addSubgroupOf, hstep,
    inv_mul_mem_unitFiltration_zero_iff (mem_ker_unitVal.mp x.2), coe_kerUnitValToVal,
    coe_kerUnitValToVal]
  norm_num

/-- The class in the zeroth graded piece of the additive filtration, as a map on the cosets of the
first step of the unit filtration inside the units of the valuation ring. -/
def kerUnitValGraded :
    ↥(unitVal (A := A)).ker ⧸ (unitFiltrationAdd A 0).addSubgroupOf (unitVal (A := A)).ker →
      gradedAdd A 0 := fun q =>
  Quotient.liftOn' q kerUnitValGradedFun fun _ _ h =>
    (kerUnitValGradedFun_eq_iff _ _).mpr (QuotientAddGroup.leftRel_apply.mp h)

/-- Distinct cosets of the first step of the unit filtration have distinct classes in the zeroth
graded piece of the additive filtration. -/
theorem kerUnitValGraded_injective : Function.Injective (kerUnitValGraded (A := A)) := by
  refine fun q₁ q₂ => ?_
  induction q₁ using QuotientAddGroup.induction_on with
  | H x =>
    induction q₂ using QuotientAddGroup.induction_on with
    | H y =>
      intro h
      exact QuotientAddGroup.eq.mpr ((kerUnitValGradedFun_eq_iff x y).mp h)

/-! ### Finiteness of the index -/

/-- **The first step of the unit filtration has finite index in the units of the valuation ring**,
when the zeroth graded piece of the additive filtration is finite. -/
theorem finite_quotient_ker_unitVal_unitFiltrationAdd [Finite (gradedAdd A 0)] :
    Finite (↥(unitVal (A := A)).ker
      ⧸ (unitFiltrationAdd A 0).addSubgroupOf (unitVal (A := A)).ker) :=
  Finite.of_injective _ kerUnitValGraded_injective

/-- The first step of the unit filtration has nonzero relative index in the units of the valuation
ring. -/
theorem relIndex_unitFiltrationAdd_ker_unitVal [Finite (gradedAdd A 0)] :
    (unitFiltrationAdd A 0).relIndex (unitVal (A := A)).ker ≠ 0 :=
  (finite_quotient_iff_relIndex_ne_zero _ _).mp finite_quotient_ker_unitVal_unitFiltrationAdd

/-- **Every step of the unit filtration has finite index in the units of the valuation ring**, when
all the graded pieces of the additive filtration are finite. -/
theorem finite_quotient_ker_unitVal [∀ k : ℤ, Finite (gradedAdd A k)] (i : ℕ) :
    Finite (↥(unitVal (A := A)).ker
      ⧸ (unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker) := by
  refine (finite_quotient_iff_relIndex_ne_zero _ _).mpr ?_
  refine AddSubgroup.relIndex_ne_zero_trans ?_ relIndex_unitFiltrationAdd_ker_unitVal
  have h := relIndex_unitFiltrationAdd_add (A := A) 0 i
  rwa [Nat.zero_add] at h

end InverseGalois.CFT
