/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.ExpSurjective

/-!
# The exponential identifies the additive and the multiplicative filtration

On a step of the additive filtration deep enough for the exponential series to converge, the
exponential turns addition into multiplication, preserves valuations exactly, and hits every unit
congruent to one to the same accuracy.  It is therefore an isomorphism from that step of the
additive filtration onto the corresponding step of the unit filtration, written additively.

## Main definitions

* `InverseGalois.CFT.padicExpHom`: the exponential as a homomorphism from a step of the additive
  filtration to a step of the unit filtration.
* `InverseGalois.CFT.padicExpEquiv`: **the exponential as an isomorphism between them.**

## Main results

* `InverseGalois.CFT.coe_padicExpHom`: the underlying field element of a value of the
  homomorphism.

## Tags

valued field, exponential, unit filtration, additive filtration
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {p e : ℕ}

/-- The exponential of an element of a step of the additive filtration is a nonzero, since its
valuation is one. -/
theorem padicExp_ne_zero (h : HasResidueChar A p e) {j : ℤ} (hj : (e : ℤ) < j * ((p : ℤ) - 1))
    {x : A} (hx : x ∈ valAddSubgroup A j) : padicExp x ≠ 0 := by
  intro hz
  have := valued_padicExp h (mem_valAddSubgroup.mp hx) hj
  rw [hz, map_zero] at this
  exact zero_ne_one this

/-- **The exponential as a homomorphism from a step of the additive filtration to the
corresponding step of the unit filtration.** -/
noncomputable def padicExpHom (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) :
    ↥(valAddSubgroup A ((i : ℤ) + 1)) →+ ↥(unitFiltrationAdd A i) where
  toFun x :=
    ⟨Additive.ofMul (Units.mk0 (padicExp (x : A)) (padicExp_ne_zero h hi x.2)),
      mem_unitFiltrationAdd.mpr
        (valued_padicExp_sub_one_le h (mem_valAddSubgroup.mp x.2) hi)⟩
  map_zero' := by
    refine Subtype.ext (Additive.toMul.injective (Units.ext ?_))
    show padicExp ((0 : ↥(valAddSubgroup A ((i : ℤ) + 1))) : A) = (1 : A)
    rw [ZeroMemClass.coe_zero, padicExp_zero]
  map_add' x y := by
    refine Subtype.ext (Additive.toMul.injective (Units.ext ?_))
    show padicExp ((x : A) + (y : A)) = padicExp (x : A) * padicExp (y : A)
    exact padicExp_add h (mem_valAddSubgroup.mp x.2) (mem_valAddSubgroup.mp y.2) hi

@[simp]
theorem coe_padicExpHom (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) (x : ↥(valAddSubgroup A ((i : ℤ) + 1))) :
    ((Additive.toMul (padicExpHom h hi x : Additive Aˣ) : Aˣ) : A) = padicExp (x : A) :=
  rfl

theorem padicExpHom_injective (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) :
    Function.Injective (padicExpHom h hi) := by
  intro x y hxy
  refine Subtype.ext (padicExp_injOn h hi (mem_valAddSubgroup.mp x.2) (mem_valAddSubgroup.mp y.2)
    ?_)
  exact congrArg (fun u : ↥(unitFiltrationAdd A i) => ((Additive.toMul (u : Additive Aˣ) : Aˣ) : A))
    hxy

theorem padicExpHom_surjective (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) :
    Function.Surjective (padicExpHom h hi) := by
  intro u
  obtain ⟨x, hx, hux⟩ := exists_padicExp_eq h hi (mem_unitFiltrationAdd.mp u.2)
  refine ⟨⟨x, mem_valAddSubgroup.mpr hx⟩, ?_⟩
  refine Subtype.ext (Additive.toMul.injective (Units.ext ?_))
  exact hux

/-- **The exponential is an isomorphism from a step of the additive filtration onto the
corresponding step of the unit filtration.** -/
noncomputable def padicExpEquiv (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) :
    ↥(valAddSubgroup A ((i : ℤ) + 1)) ≃+ ↥(unitFiltrationAdd A i) :=
  AddEquiv.ofBijective (padicExpHom h hi) ⟨padicExpHom_injective h hi, padicExpHom_surjective h hi⟩

@[simp]
theorem coe_padicExpEquiv (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) (x : ↥(valAddSubgroup A ((i : ℤ) + 1))) :
    ((Additive.toMul (padicExpEquiv h hi x : Additive Aˣ) : Aˣ) : A) = padicExp (x : A) :=
  rfl

end InverseGalois.CFT
