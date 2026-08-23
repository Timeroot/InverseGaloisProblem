/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Herbrand
import InverseGalois.CFT.Tate.Hexagon
import InverseGalois.CFT.Tate.Restrict
import InverseGalois.CFT.Tate.Trivial

/-!
# The valuation of a unit of a discretely valued field

The valuation of a nonzero element of a discretely valued field is an integer, and the map sending
a unit to that integer is a surjective homomorphism onto the integers whose kernel is the group of
units of the valuation ring.  A group of automorphisms preserving the valuation acts trivially on
the integers, so the sequence is a short exact sequence of modules over the group: the Herbrand
quotient of the units of the field is that of the units of the valuation ring, multiplied by the
order of the group.

## Main definitions

* `InverseGalois.CFT.smulUnitsAut`: the action of a group of ring automorphisms on the units,
  written
  additively.
* `InverseGalois.CFT.unitVal`: **the valuation of a unit, as an integer.**
* `InverseGalois.CFT.localUnitsTateSES`: the short exact sequence of the unit group.

## Main results

* `InverseGalois.CFT.unitVal_surjective`: the valuation of a unit is a surjection onto the
  integers.
* `InverseGalois.CFT.mem_ker_unitVal`: the kernel of the valuation is the group of units of the
  valuation ring.
* `InverseGalois.CFT.herbrand_smulUnitsAut_mul`: **the Herbrand quotient of the units of the field
  is
  that of the units of the valuation ring, multiplied by the order of the group.**

## Tags

valued field, discrete valuation, unit group, Herbrand quotient, local field
-/

namespace InverseGalois.CFT

open MulAction

open scoped WithZero

/-! ### The action on the units -/

section UnitsAut

variable {G R : Type*} [Group G] [Ring R] [MulSemiringAction G R]

/-- **The action of a group of ring automorphisms on the units, written additively.** -/
def smulUnitsAut : G →* (Additive Rˣ ≃+ Additive Rˣ) where
  toFun σ := MulEquiv.toAdditive (Units.mapEquiv (MulSemiringAction.toRingEquiv G R σ).toMulEquiv)
  map_one' := by
    refine AddEquiv.ext fun u => Units.ext ?_
    exact one_smul G _
  map_mul' σ τ := by
    refine AddEquiv.ext fun u => Units.ext ?_
    exact mul_smul σ τ _

@[simp]
theorem coe_smulUnitsAut_apply (σ : G) (u : Additive Rˣ) :
    ((Additive.toMul (smulUnitsAut σ u) : Rˣ) : R) = σ • ((Additive.toMul u : Rˣ) : R) := rfl

/-- **The additive action inherits the order of the automorphism.** -/
theorem smulUnitsAut_pow_eq_one {σ : G} {n : ℕ} (hσ : σ ^ n = 1) :
    (smulUnitsAut (R := R) σ) ^ n = 1 := by
  rw [← map_pow, hσ, map_one]

theorem smulUnitsAut_inv (σ : G) : smulUnitsAut (R := R) σ⁻¹ = (smulUnitsAut (R := R) σ).symm := by
  rw [map_inv]
  rfl

end UnitsAut

/-! ### The valuation of a unit -/

section ValuedField

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

theorem valued_unit_ne_zero (x : Aˣ) : Valued.v (x : A) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr x.ne_zero

/-- **The valuation of a unit, as an integer.** -/
def unitVal : Additive Aˣ →+ ℤ where
  toFun x := WithZero.log (Valued.v ((Additive.toMul x : Aˣ) : A))
  map_zero' := by
    show WithZero.log (Valued.v ((1 : Aˣ) : A)) = 0
    rw [Units.val_one, map_one, WithZero.log_one]
  map_add' x y := by
    show WithZero.log (Valued.v ((Additive.toMul x * Additive.toMul y : Aˣ) : A))
      = WithZero.log (Valued.v ((Additive.toMul x : Aˣ) : A))
        + WithZero.log (Valued.v ((Additive.toMul y : Aˣ) : A))
    rw [Units.val_mul, map_mul,
      WithZero.log_mul (valued_unit_ne_zero _) (valued_unit_ne_zero _)]

theorem unitVal_apply (x : Aˣ) :
    unitVal (Additive.ofMul x) = WithZero.log (Valued.v (x : A)) := rfl

theorem valued_eq_exp_unitVal (x : Aˣ) :
    Valued.v (x : A) = WithZero.exp (unitVal (Additive.ofMul x)) :=
  (WithZero.exp_log (valued_unit_ne_zero x)).symm

/-- **The valuation of a unit is a surjection onto the integers** when the valuation of the field
is surjective. -/
theorem unitVal_surjective (h : Function.Surjective (Valued.v : A → ℤᵐ⁰)) :
    Function.Surjective (unitVal : Additive Aˣ →+ ℤ) := by
  intro n
  obtain ⟨a, ha⟩ := h (WithZero.exp n)
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  show WithZero.log (Valued.v a) = n
  rw [ha, WithZero.log_exp]

/-- **The kernel of the valuation is the group of units of the valuation ring.** -/
theorem mem_ker_unitVal {x : Additive Aˣ} :
    x ∈ (unitVal (A := A)).ker ↔ Valued.v ((Additive.toMul x : Aˣ) : A) = 1 := by
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h
    have hx : Valued.v ((Additive.toMul x : Aˣ) : A) = WithZero.exp (unitVal x) :=
      valued_eq_exp_unitVal (Additive.toMul x)
    rw [h, WithZero.exp_zero] at hx
    exact hx
  · intro h
    show WithZero.log (Valued.v ((Additive.toMul x : Aˣ) : A)) = 0
    rw [h, WithZero.log_one]

theorem mem_ker_unitVal_iff_mem_unitGroup {x : Additive Aˣ} :
    x ∈ (unitVal (A := A)).ker ↔
      (Additive.toMul x : Aˣ) ∈ ValuationSubring.unitGroup
        (Valuation.valuationSubring (Valued.v : Valuation A ℤᵐ⁰)) := by
  rw [mem_ker_unitVal, ValuationSubring.mem_unitGroup_iff]
  have h := Valuation.isEquiv_valuation_valuationSubring (Valued.v : Valuation A ℤᵐ⁰)
  constructor
  · intro hx
    refine le_antisymm ?_ ?_
    · have := (h ((Additive.toMul x : Aˣ) : A) 1).mp (by rw [hx, map_one])
      rwa [map_one] at this
    · have := (h 1 ((Additive.toMul x : Aˣ) : A)).mp (by rw [hx, map_one])
      rwa [map_one] at this
  · intro hx
    refine le_antisymm ?_ ?_
    · have := (h ((Additive.toMul x : Aˣ) : A) 1).mpr (by rw [hx, map_one])
      rwa [map_one] at this
    · have := (h 1 ((Additive.toMul x : Aˣ) : A)).mpr (by rw [hx, map_one])
      rwa [map_one] at this

end ValuedField

/-! ### The short exact sequence of the unit group -/

section Equivariant

variable {G A : Type*} [Group G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

theorem unitVal_smulUnitsAut (σ : G) (x : Additive Aˣ) :
    unitVal (smulUnitsAut σ x) = unitVal x := by
  show WithZero.log (Valued.v ((Additive.toMul (smulUnitsAut σ x) : Aˣ) : A)) = _
  rw [coe_smulUnitsAut_apply, hv]
  rfl

theorem smulUnitsAut_mem_ker_unitVal (σ : G) {x : Additive Aˣ} (hx : x ∈ (unitVal (A := A)).ker) :
    smulUnitsAut σ x ∈ (unitVal (A := A)).ker := by
  rw [AddMonoidHom.mem_ker, unitVal_smulUnitsAut hv]
  exact hx

theorem smulUnitsAut_symm_mem_ker_unitVal (σ : G) {x : Additive Aˣ}
    (hx : x ∈ (unitVal (A := A)).ker) : (smulUnitsAut σ).symm x ∈ (unitVal (A := A)).ker := by
  have h := smulUnitsAut_mem_ker_unitVal hv σ⁻¹ hx
  rwa [smulUnitsAut_inv] at h

/-- The automorphism of the units of the valuation ring induced by an automorphism preserving the
valuation. -/
def kerUnitValAut (σ : G) : ↥(unitVal (A := A)).ker ≃+ ↥(unitVal (A := A)).ker :=
  subgroupAut (V := Additive Aˣ) (smulUnitsAut σ) (unitVal (A := A)).ker
    (fun _ hx => smulUnitsAut_mem_ker_unitVal hv σ hx)
    (fun _ hx => smulUnitsAut_symm_mem_ker_unitVal hv σ hx)

theorem kerUnitValAut_pow_eq_one {σ : G} {n : ℕ} (hσ : σ ^ n = 1) :
    (kerUnitValAut hv σ) ^ n = 1 :=
  subgroupAut_pow_eq_one _ _ (smulUnitsAut_pow_eq_one hσ)

variable (hsurj : Function.Surjective (Valued.v : A → ℤᵐ⁰))

include hsurj

/-- **The short exact sequence relating the units of the valuation ring, the units of the field and
the integers.** -/
def localUnitsTateSES (σ : G) {n : ℕ} (hσ : σ ^ n = 1) :
    TateSES n ↥(unitVal (A := A)).ker (Additive Aˣ) ℤ where
  σA := kerUnitValAut hv σ
  σB := smulUnitsAut σ
  σC := 1
  hσA := kerUnitValAut_pow_eq_one hv hσ
  hσB := smulUnitsAut_pow_eq_one hσ
  hσC := one_pow n
  f := (unitVal (A := A)).ker.subtype
  g := unitVal
  hf _ := rfl
  hg b := unitVal_smulUnitsAut hv σ b
  finj := AddSubgroup.subtype_injective _
  gsurj := unitVal_surjective hsurj
  range_eq_ker := AddSubgroup.range_subtype _

/-- **The Herbrand quotient of the units of the field is that of the units of the valuation ring,
multiplied by the order of the group.** -/
theorem herbrand_smulUnitsAut_mul (σ : G) {n : ℕ} (hn : n ≠ 0) (hσ : σ ^ n = 1)
    [hA0 : Finite (tateH0 (kerUnitValAut hv σ) n)]
    [hB0 : Finite (tateH0 (smulUnitsAut (R := A) σ) n)]
    [hAm : Finite (tateHm1 (kerUnitValAut hv σ) n)]
    [hBm : Finite (tateHm1 (smulUnitsAut (R := A) σ) n)] :
    herbrand (kerUnitValAut hv σ) n * n = herbrand (smulUnitsAut (R := A) σ) n := by
  haveI hC0 : Finite (tateH0 (1 : ℤ ≃+ ℤ) n) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateH0_int]
    exact hn
  haveI hCm : Finite (tateHm1 (1 : ℤ ≃+ ℤ) n) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateHm1_int n hn]
    exact one_ne_zero
  haveI : Finite (tateH0 (localUnitsTateSES hv hsurj σ hσ).σA n) := hA0
  haveI : Finite (tateH0 (localUnitsTateSES hv hsurj σ hσ).σB n) := hB0
  haveI : Finite (tateH0 (localUnitsTateSES hv hsurj σ hσ).σC n) := hC0
  haveI : Finite (tateHm1 (localUnitsTateSES hv hsurj σ hσ).σA n) := hAm
  haveI : Finite (tateHm1 (localUnitsTateSES hv hsurj σ hσ).σB n) := hBm
  haveI : Finite (tateHm1 (localUnitsTateSES hv hsurj σ hσ).σC n) := hCm
  have h := (localUnitsTateSES hv hsurj σ hσ).herbrand_mul
  rw [show (localUnitsTateSES hv hsurj σ hσ).σA = kerUnitValAut hv σ from rfl,
    show (localUnitsTateSES hv hsurj σ hσ).σB = smulUnitsAut σ from rfl,
    show (localUnitsTateSES hv hsurj σ hσ).σC = 1 from rfl, herbrand_int n hn] at h
  exact h

end Equivariant

end InverseGalois.CFT
