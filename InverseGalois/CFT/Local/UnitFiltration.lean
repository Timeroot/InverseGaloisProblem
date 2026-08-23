/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitValuation

/-!
# The unit filtration of a valued field

The elements of valuation at most a given power of the value of a uniformizer form an additive
subgroup, and the units that are congruent to one modulo such a subgroup form a subgroup of the
unit group.  The product of two elements of the filtration lies two steps further down, so
subtracting one is a homomorphism from a step of the unit filtration to the corresponding graded
piece of the additive filtration; it is surjective, and its kernel is the next step of the unit
filtration.

## Main definitions

* `InverseGalois.CFT.valAddSubgroup`: the elements of valuation at most a given power.
* `InverseGalois.CFT.unitFiltration`: the units congruent to one modulo a step of the filtration.
* `InverseGalois.CFT.unitFiltrationAdd`: the same, inside the additive form of the unit group.
* `InverseGalois.CFT.gradedAdd`: a graded piece of the additive filtration.
* `InverseGalois.CFT.gradedUnitHom`: subtracting one, from a step of the unit filtration to the
  corresponding graded piece.

## Main results

* `InverseGalois.CFT.valued_eq_one_of_mem_unitFiltration`: a unit congruent to one has valuation
  one.
* `InverseGalois.CFT.gradedUnitHom_eq_zero_iff`: the kernel of subtracting one is the next step of
  the unit filtration.
* `InverseGalois.CFT.gradedUnitHom_surjective`: **subtracting one carries a step of the unit
  filtration onto the corresponding graded piece of the additive filtration.**

## Tags

valued field, unit filtration, principal units, graded piece
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-! ### The additive filtration -/

variable (A) in
/-- **The elements of valuation at most a given power.** -/
def valAddSubgroup (j : ℤ) : AddSubgroup A where
  carrier := {x | Valued.v x ≤ WithZero.exp (-j)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact le_trans (Valuation.map_add Valued.v _ _) (max_le ha hb)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Valuation.map_neg] at ha ⊢
    exact ha

@[simp]
theorem mem_valAddSubgroup {j : ℤ} {x : A} :
    x ∈ valAddSubgroup A j ↔ Valued.v x ≤ WithZero.exp (-j) := by rfl

theorem valAddSubgroup_le_valAddSubgroup {i j : ℤ} (h : i ≤ j) :
    valAddSubgroup A j ≤ valAddSubgroup A i := by
  intro x hx
  rw [mem_valAddSubgroup] at hx ⊢
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

theorem mul_mem_valAddSubgroup {i j : ℤ} {x y : A} (hx : x ∈ valAddSubgroup A i)
    (hy : y ∈ valAddSubgroup A j) : x * y ∈ valAddSubgroup A (i + j) := by
  rw [mem_valAddSubgroup] at hx hy ⊢
  calc Valued.v (x * y) = Valued.v x * Valued.v y := map_mul _ _ _
    _ ≤ WithZero.exp (-i) * WithZero.exp (-j) := mul_le_mul' hx hy
    _ = WithZero.exp (-(i + j)) := by rw [← WithZero.exp_add]; ring_nf

/-! ### Units congruent to one -/

/-- A valuation bounded by a strictly negative power is smaller than one. -/
theorem lt_one_of_le_exp_neg {j : ℤ} (hj : 0 < j) {x : A}
    (hx : Valued.v x ≤ WithZero.exp (-j)) : Valued.v x < 1 :=
  lt_of_le_of_lt hx (by simpa using WithZero.exp_lt_exp.mpr (by omega : -j < 0))

/-- An element congruent to one modulo a valuation strictly smaller than one has valuation one. -/
theorem valued_eq_one_of_sub_one_lt_one {x : A} (hx : Valued.v (x - 1) < 1) :
    Valued.v x = 1 := by
  have h := Valuation.map_add_eq_of_lt_right (v := (Valued.v : Valuation A ℤᵐ⁰))
    (x := x - 1) (y := 1) (by simpa using hx)
  rwa [sub_add_cancel, map_one] at h

variable (A) in
/-- **The units congruent to one modulo the `(i + 1)`-st step of the additive filtration.** -/
def unitFiltration (i : ℕ) : Subgroup Aˣ where
  carrier := {u | Valued.v ((u : A) - 1) ≤ WithZero.exp (-((i : ℤ) + 1))}
  one_mem' := by simp
  mul_mem' := by
    intro u w hu hw
    simp only [Set.mem_setOf_eq] at hu hw ⊢
    have hw1 : Valued.v (w : A) ≤ 1 :=
      le_of_eq (valued_eq_one_of_sub_one_lt_one (lt_one_of_le_exp_neg (by omega) hw))
    have hkey : ((u * w : Aˣ) : A) - 1 = ((u : A) - 1) * (w : A) + ((w : A) - 1) := by
      push_cast; ring
    rw [hkey]
    refine (Valuation.map_add Valued.v _ _).trans (max_le ?_ hw)
    calc Valued.v (((u : A) - 1) * (w : A)) = Valued.v ((u : A) - 1) * Valued.v (w : A) :=
          map_mul _ _ _
      _ ≤ WithZero.exp (-((i : ℤ) + 1)) * 1 := mul_le_mul' hu hw1
      _ = WithZero.exp (-((i : ℤ) + 1)) := mul_one _
  inv_mem' := by
    intro u hu
    simp only [Set.mem_setOf_eq] at hu ⊢
    have hu1 : Valued.v (u : A) = 1 :=
      valued_eq_one_of_sub_one_lt_one (lt_one_of_le_exp_neg (by omega) hu)
    have hune : (u : A) ≠ 0 := u.ne_zero
    have hkey : ((u⁻¹ : Aˣ) : A) - 1 = -(((u : A) - 1) * ((u : A))⁻¹) := by
      rw [Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [hkey, Valuation.map_neg, map_mul, map_inv₀, hu1, inv_one, mul_one]
    exact hu

@[simp]
theorem mem_unitFiltration {i : ℕ} {u : Aˣ} :
    u ∈ unitFiltration A i ↔ Valued.v ((u : A) - 1) ≤ WithZero.exp (-((i : ℤ) + 1)) := by rfl

theorem unitFiltration_le_unitFiltration {i j : ℕ} (h : i ≤ j) :
    unitFiltration A j ≤ unitFiltration A i := by
  intro u hu
  rw [mem_unitFiltration] at hu ⊢
  exact hu.trans (WithZero.exp_le_exp.mpr (by omega))

theorem unitFiltration_succ_le (i : ℕ) : unitFiltration A (i + 1) ≤ unitFiltration A i :=
  unitFiltration_le_unitFiltration (Nat.le_succ i)

/-- **A unit congruent to one has valuation one.** -/
theorem valued_eq_one_of_mem_unitFiltration {i : ℕ} {u : Aˣ} (hu : u ∈ unitFiltration A i) :
    Valued.v (u : A) = 1 :=
  valued_eq_one_of_sub_one_lt_one
    (lt_one_of_le_exp_neg (j := (i : ℤ) + 1) (by omega) (mem_unitFiltration.mp hu))

/-- Subtracting one carries a step of the unit filtration into the corresponding step of the
additive filtration. -/
theorem sub_one_mem_valAddSubgroup {i : ℕ} {u : Aˣ} (hu : u ∈ unitFiltration A i) :
    (u : A) - 1 ∈ valAddSubgroup A ((i : ℤ) + 1) :=
  mem_valAddSubgroup.mpr (mem_unitFiltration.mp hu)

/-- Adding one to an element of a step of the additive filtration gives a unit. -/
theorem exists_val_eq_one_add {j : ℤ} (hj : 0 < j) {x : A} (hx : x ∈ valAddSubgroup A j) :
    ∃ u : Aˣ, (u : A) = 1 + x := by
  have hlt : Valued.v x < 1 := lt_one_of_le_exp_neg hj (mem_valAddSubgroup.mp hx)
  have hne : (1 : A) + x ≠ 0 := by
    intro h
    have hx1 : x = -1 := by linear_combination h
    rw [hx1, Valuation.map_neg, map_one] at hlt
    exact absurd hlt (lt_irrefl 1)
  exact ⟨Units.mk0 (1 + x) hne, rfl⟩

/-! ### The additive form of the unit filtration -/

variable (A) in
/-- **The unit filtration, as a subgroup of the additive form of the unit group.** -/
def unitFiltrationAdd (i : ℕ) : AddSubgroup (Additive Aˣ) :=
  Subgroup.toAddSubgroup (unitFiltration A i)

@[simp]
theorem mem_unitFiltrationAdd {i : ℕ} {x : Additive Aˣ} :
    x ∈ unitFiltrationAdd A i ↔
      Valued.v (((Additive.toMul x : Aˣ) : A) - 1) ≤ WithZero.exp (-((i : ℤ) + 1)) :=
  mem_unitFiltration

theorem unitFiltrationAdd_le_unitFiltrationAdd {i j : ℕ} (h : i ≤ j) :
    unitFiltrationAdd A j ≤ unitFiltrationAdd A i := fun _ hx =>
  unitFiltration_le_unitFiltration h hx

theorem unitFiltrationAdd_succ_le (i : ℕ) : unitFiltrationAdd A (i + 1) ≤ unitFiltrationAdd A i :=
  unitFiltrationAdd_le_unitFiltrationAdd (Nat.le_succ i)

/-! ### The graded pieces -/

variable (A) in
/-- **A graded piece of the additive filtration.** -/
abbrev gradedAdd (j : ℤ) : Type _ :=
  ↥(valAddSubgroup A j) ⧸ (valAddSubgroup A (j + 1)).addSubgroupOf (valAddSubgroup A j)

/-- Two elements of a step of the additive filtration agree in the graded piece as soon as the
valuation of their difference is small enough. -/
theorem gradedAdd_mk_eq {j : ℤ} {x y : ↥(valAddSubgroup A j)}
    (h : Valued.v ((x : A) - (y : A)) ≤ WithZero.exp (-(j + 1))) :
    (QuotientAddGroup.mk x : gradedAdd A j) = QuotientAddGroup.mk y := by
  refine QuotientAddGroup.eq.mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  have hcoe : ((-x + y : ↥(valAddSubgroup A j)) : A) = -((x : A) - (y : A)) := by
    push_cast; ring
  rw [hcoe]
  exact (valAddSubgroup A (j + 1)).neg_mem (mem_valAddSubgroup.mpr h)

variable (A) in
/-- Subtracting one, as a map from a step of the unit filtration to the corresponding step of the
additive filtration. -/
def subOneFun (i : ℕ) (u : ↥(unitFiltrationAdd A i)) : ↥(valAddSubgroup A ((i : ℤ) + 1)) :=
  ⟨((Additive.toMul (u : Additive Aˣ) : Aˣ) : A) - 1,
    sub_one_mem_valAddSubgroup (mem_unitFiltrationAdd.mp u.2)⟩

@[simp]
theorem coe_subOneFun (i : ℕ) (u : ↥(unitFiltrationAdd A i)) :
    (subOneFun A i u : A) = ((Additive.toMul (u : Additive Aˣ) : Aˣ) : A) - 1 := rfl

variable (A) in
/-- **Subtracting one, from a step of the unit filtration to the corresponding graded piece.** -/
def gradedUnitHom (i : ℕ) : ↥(unitFiltrationAdd A i) →+ gradedAdd A ((i : ℤ) + 1) where
  toFun u := QuotientAddGroup.mk (subOneFun A i u)
  map_zero' := by
    refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf, coe_subOneFun]
    have hone : (Additive.toMul ((0 : ↥(unitFiltrationAdd A i)) : Additive Aˣ) : Aˣ) = 1 := rfl
    rw [hone, Units.val_one, sub_self]
    exact zero_mem _
  map_add' u w := by
    rw [← QuotientAddGroup.mk_add]
    refine gradedAdd_mk_eq ?_
    have ha : ((Additive.toMul (u : Additive Aˣ) : Aˣ) : A) - 1 ∈
        valAddSubgroup A ((i : ℤ) + 1) := sub_one_mem_valAddSubgroup (mem_unitFiltrationAdd.mp u.2)
    have hb : ((Additive.toMul (w : Additive Aˣ) : Aˣ) : A) - 1 ∈
        valAddSubgroup A ((i : ℤ) + 1) := sub_one_mem_valAddSubgroup (mem_unitFiltrationAdd.mp w.2)
    have hmul : (Additive.toMul (((u + w : ↥(unitFiltrationAdd A i)) : Additive Aˣ)) : Aˣ)
        = (Additive.toMul (u : Additive Aˣ) : Aˣ) * (Additive.toMul (w : Additive Aˣ) : Aˣ) := rfl
    have hcoe : (subOneFun A i (u + w) : A)
        - ((subOneFun A i u + subOneFun A i w : ↥(valAddSubgroup A ((i : ℤ) + 1))) : A)
        = (((Additive.toMul (u : Additive Aˣ) : Aˣ) : A) - 1)
          * (((Additive.toMul (w : Additive Aˣ) : Aˣ) : A) - 1) := by
      rw [AddSubgroup.coe_add, coe_subOneFun, coe_subOneFun, coe_subOneFun, hmul, Units.val_mul]
      ring
    rw [hcoe]
    exact mem_valAddSubgroup.mp
      (valAddSubgroup_le_valAddSubgroup (by omega) (mul_mem_valAddSubgroup ha hb))

@[simp]
theorem gradedUnitHom_apply (i : ℕ) (u : ↥(unitFiltrationAdd A i)) :
    gradedUnitHom A i u = QuotientAddGroup.mk (subOneFun A i u) := rfl

/-- **The kernel of subtracting one is the next step of the unit filtration.** -/
theorem gradedUnitHom_eq_zero_iff (i : ℕ) (u : ↥(unitFiltrationAdd A i)) :
    gradedUnitHom A i u = 0 ↔ (u : Additive Aˣ) ∈ unitFiltrationAdd A (i + 1) := by
  rw [gradedUnitHom_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    coe_subOneFun, mem_unitFiltrationAdd, mem_valAddSubgroup]
  norm_num

/-- **Subtracting one carries a step of the unit filtration onto the corresponding graded piece of
the additive filtration.** -/
theorem gradedUnitHom_surjective (i : ℕ) : Function.Surjective (gradedUnitHom A i) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨u, hu⟩ := exists_val_eq_one_add (j := (i : ℤ) + 1) (by omega) x.2
    have humem : Additive.ofMul u ∈ unitFiltrationAdd A i := by
      rw [mem_unitFiltrationAdd]
      have hx : Valued.v (x : A) ≤ WithZero.exp (-((i : ℤ) + 1)) := mem_valAddSubgroup.mp x.2
      show Valued.v ((u : A) - 1) ≤ _
      rw [hu]
      simpa using hx
    refine ⟨⟨Additive.ofMul u, humem⟩, ?_⟩
    rw [gradedUnitHom_apply]
    refine gradedAdd_mk_eq ?_
    rw [coe_subOneFun]
    have hz : (Additive.toMul ((⟨Additive.ofMul u, humem⟩ :
        ↥(unitFiltrationAdd A i)) : Additive Aˣ) : Aˣ) = u := rfl
    rw [hz, hu]
    have hzero : (1 + (x : A)) - 1 - (x : A) = 0 := by ring
    rw [hzero, map_zero]
    exact zero_le'

end InverseGalois.CFT
