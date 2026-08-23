/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitFiltration

/-!
# The graded pieces of a valued field are all of the same size

Multiplying by a fixed nonzero element of a valued field shifts the additive filtration by the
value of that element: an element of valuation at most a given power is carried to an element of
valuation at most the product of the two powers, and multiplying by the inverse undoes the
operation.  Consequently multiplication is an isomorphism between two steps of the filtration, and
since it matches the next steps as well it descends to an isomorphism between the corresponding
graded pieces.

When the field carries a uniformizer, that is an element whose value generates the value group,
its integral powers realise every value, so any two graded pieces of the additive filtration are
isomorphic.  In particular all of them are finite as soon as a single one is, which is the shape
in which the hypothesis of a finite residue field is usually available.

## Main definitions

* `InverseGalois.CFT.mulValAddSubgroupEquiv`: multiplication by a fixed element, as an isomorphism
  between two steps of the additive filtration.
* `InverseGalois.CFT.gradedAddEquivOfMul`: the induced isomorphism between two graded pieces.

## Main results

* `InverseGalois.CFT.exists_valued_eq_exp`: a uniformizer has powers of every value.
* `InverseGalois.CFT.finite_gradedAdd`: **every graded piece of the additive filtration is finite
  as soon as one of them is**, provided a uniformizer exists.
* `InverseGalois.CFT.finite_gradedAdd_forall`: the same statement in the form of a universally
  quantified hypothesis.

## Tags

valued field, uniformizer, additive filtration, graded piece, finite residue field
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-! ### Multiplication by an element of prescribed value -/

/-- An element whose value is a power of the value group is nonzero. -/
theorem ne_zero_of_valued_eq_exp {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m)) : c ≠ 0 := by
  intro h
  rw [h, map_zero] at hc
  exact WithZero.exp_pos.ne hc

/-- The inverse of an element whose value is a power of the value group has the opposite power as
its value. -/
theorem valued_inv_eq_exp {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m)) :
    Valued.v c⁻¹ = WithZero.exp (-(-m)) := by
  rw [map_inv₀, hc, ← WithZero.exp_neg]

/-- Multiplying by an element of a given value moves a step of the additive filtration that many
places further down. -/
theorem mul_mem_valAddSubgroup_of_val_eq {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m))
    {j : ℤ} {x : A} (hx : x ∈ valAddSubgroup A j) : c * x ∈ valAddSubgroup A (j + m) := by
  rw [mem_valAddSubgroup] at hx ⊢
  calc Valued.v (c * x) = Valued.v c * Valued.v x := map_mul _ _ _
    _ ≤ WithZero.exp (-m) * WithZero.exp (-j) := mul_le_mul' (le_of_eq hc) hx
    _ = WithZero.exp (-(j + m)) := by rw [← WithZero.exp_add]; ring_nf

/-- Multiplying by the inverse of an element of a given value moves a step of the additive
filtration that many places back up. -/
theorem inv_mul_mem_valAddSubgroup {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m)) {j : ℤ}
    {y : A} (hy : y ∈ valAddSubgroup A (j + m)) : c⁻¹ * y ∈ valAddSubgroup A j := by
  have h := mul_mem_valAddSubgroup_of_val_eq (valued_inv_eq_exp hc) hy
  rwa [show j + m + -m = j from by ring] at h

/-- Multiplying by an element of a given value characterises membership in the shifted step of the
additive filtration. -/
theorem mul_mem_valAddSubgroup_iff {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m)) {j : ℤ}
    {x : A} : c * x ∈ valAddSubgroup A (j + m) ↔ x ∈ valAddSubgroup A j := by
  refine ⟨fun h => ?_, fun h => mul_mem_valAddSubgroup_of_val_eq hc h⟩
  have h2 := inv_mul_mem_valAddSubgroup hc h
  rwa [← mul_assoc, inv_mul_cancel₀ (ne_zero_of_valued_eq_exp hc), one_mul] at h2

/-- **Multiplication by an element of a given value, as an isomorphism between two steps of the
additive filtration.** -/
def mulValAddSubgroupEquiv {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m)) (j : ℤ) :
    ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A (j + m)) where
  toFun x := ⟨c * (x : A), mul_mem_valAddSubgroup_of_val_eq hc x.2⟩
  invFun y := ⟨c⁻¹ * (y : A), inv_mul_mem_valAddSubgroup hc y.2⟩
  left_inv x := by
    refine Subtype.ext ?_
    show c⁻¹ * (c * (x : A)) = (x : A)
    rw [← mul_assoc, inv_mul_cancel₀ (ne_zero_of_valued_eq_exp hc), one_mul]
  right_inv y := by
    refine Subtype.ext ?_
    show c * (c⁻¹ * (y : A)) = (y : A)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_zero_of_valued_eq_exp hc), one_mul]
  map_add' x y := by
    refine Subtype.ext ?_
    push_cast
    ring

@[simp]
theorem coe_mulValAddSubgroupEquiv {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m)) (j : ℤ)
    (x : ↥(valAddSubgroup A j)) : (mulValAddSubgroupEquiv hc j x : A) = c * (x : A) := rfl

@[simp]
theorem coe_mulValAddSubgroupEquiv_symm {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m))
    (j : ℤ) (y : ↥(valAddSubgroup A (j + m))) :
    ((mulValAddSubgroupEquiv hc j).symm y : A) = c⁻¹ * (y : A) := rfl

/-! ### The induced isomorphism of graded pieces -/

/-- Multiplication by an element of a given value carries the next step of the additive filtration
onto the next step of the shifted filtration. -/
theorem map_addSubgroupOf_mulValAddSubgroupEquiv {c : A} {m : ℤ}
    (hc : Valued.v c = WithZero.exp (-m)) (j : ℤ) :
    ((valAddSubgroup A (j + 1)).addSubgroupOf (valAddSubgroup A j)).map
        (mulValAddSubgroupEquiv hc j).toAddMonoidHom
      = (valAddSubgroup A (j + m + 1)).addSubgroupOf (valAddSubgroup A (j + m)) := by
  ext y
  rw [AddSubgroup.mem_map_equiv, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf,
    coe_mulValAddSubgroupEquiv_symm]
  have key := mul_mem_valAddSubgroup_iff (c := c) hc (j := j + 1) (x := c⁻¹ * (y : A))
  rw [← mul_assoc, mul_inv_cancel₀ (ne_zero_of_valued_eq_exp hc), one_mul,
    show j + 1 + m = j + m + 1 from by ring] at key
  exact key.symm

/-- **Multiplication by an element of a given value, as an isomorphism between two graded pieces of
the additive filtration.** -/
def gradedAddEquivOfMul {c : A} {m : ℤ} (hc : Valued.v c = WithZero.exp (-m)) (j : ℤ) :
    gradedAdd A j ≃+ gradedAdd A (j + m) :=
  QuotientAddGroup.congr _ _ (mulValAddSubgroupEquiv hc j)
    (map_addSubgroupOf_mulValAddSubgroupEquiv hc j)

/-! ### Finiteness of every graded piece -/

/-- **A uniformizer has powers of every value**: if some element has the value that generates the
value group, then every power of the value group is attained. -/
theorem exists_valued_eq_exp (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    ∃ c : A, Valued.v c = WithZero.exp (-k) := by
  obtain ⟨π, hval⟩ := hπ
  refine ⟨π ^ k, ?_⟩
  rw [map_zpow₀, hval, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]

/-- **Every graded piece of the additive filtration is finite as soon as one of them is**, provided
the field carries a uniformizer. -/
theorem finite_gradedAdd (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    [Finite (gradedAdd A 0)] (k : ℤ) : Finite (gradedAdd A k) := by
  obtain ⟨c, hc⟩ := exists_valued_eq_exp hπ k
  have hfin := Finite.of_equiv _ (gradedAddEquivOfMul hc 0).toEquiv
  rwa [zero_add] at hfin

/-- All the graded pieces of the additive filtration of a valued field with a uniformizer are
finite as soon as one of them is. -/
theorem finite_gradedAdd_forall (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    [Finite (gradedAdd A 0)] : ∀ k : ℤ, Finite (gradedAdd A k) :=
  finite_gradedAdd hπ

end InverseGalois.CFT
