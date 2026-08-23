/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitFiltration

/-!
# The action of an isometric group of automorphisms on the unit filtration

A group acting on a valued field by isometries preserves every step of the additive filtration by
valuation, and every step of the multiplicative filtration by congruence to one.  Subtracting one
carries a step of the unit filtration onto the corresponding graded piece of the additive
filtration, equivariantly and without choosing a uniformizer, so the two filtrations are linked by
a short exact sequence of modules over the group.

## Main definitions

* `InverseGalois.CFT.smulAddAut`: the action on the field, written additively.
* `InverseGalois.CFT.valAddSubgroupAut`: the action on a step of the additive filtration.
* `InverseGalois.CFT.unitFiltrationAut`: the action on a step of the unit filtration.
* `InverseGalois.CFT.gradedAddAut`: the action on a graded piece of the additive filtration.
* `InverseGalois.CFT.unitFiltrationTateSES`: the short exact sequence comparing consecutive steps
  of the unit filtration with a graded piece of the additive filtration.

## Main results

* `InverseGalois.CFT.smul_mem_valAddSubgroup`: an isometry preserves the additive filtration.
* `InverseGalois.CFT.smulUnitsAut_mem_unitFiltrationAdd`: an isometry preserves the unit
  filtration.

## Tags

valued field, unit filtration, graded piece, isometry, Tate cohomology
-/

namespace InverseGalois.CFT

open scoped WithZero

section Ring

variable {G A : Type*} [Group G] [Ring A] [MulSemiringAction G A]

/-! ### The action on the field, additively -/

/-- **A group of ring automorphisms acting on the additive group of the field.** -/
def smulAddAut : G →* (A ≃+ A) where
  toFun σ := (MulSemiringAction.toRingEquiv G A σ).toAddEquiv
  map_one' := AddEquiv.ext fun x => one_smul G x
  map_mul' σ τ := AddEquiv.ext fun x => mul_smul σ τ x

@[simp]
theorem smulAddAut_apply (σ : G) (x : A) : smulAddAut σ x = σ • x := rfl

theorem smulAddAut_pow_eq_one {σ : G} {n : ℕ} (hσ : σ ^ n = 1) :
    (smulAddAut (A := A) σ) ^ n = 1 := by
  rw [← map_pow, hσ, map_one]

theorem smulAddAut_inv (σ : G) : smulAddAut (A := A) σ⁻¹ = (smulAddAut (A := A) σ).symm := by
  rw [map_inv]
  rfl

@[simp]
theorem smulAddAut_symm_apply (σ : G) (x : A) :
    (smulAddAut (A := A) σ).symm x = σ⁻¹ • x := by
  rw [← smulAddAut_inv]
  rfl

end Ring

variable {G A : Type*} [Group G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-! ### The action on the additive filtration -/

/-- **An isometry preserves the additive filtration.** -/
theorem smul_mem_valAddSubgroup (σ : G) {j : ℤ} {x : A} (hx : x ∈ valAddSubgroup A j) :
    σ • x ∈ valAddSubgroup A j := by
  rw [mem_valAddSubgroup, hv]
  exact mem_valAddSubgroup.mp hx

/-- **The action on a step of the additive filtration.** -/
def valAddSubgroupAut (σ : G) (j : ℤ) : ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A j) :=
  subgroupAut (V := A) (smulAddAut σ) (valAddSubgroup A j)
    (fun _ hx => smul_mem_valAddSubgroup hv σ hx)
    (fun _ hx => by
      rw [smulAddAut_symm_apply]
      exact smul_mem_valAddSubgroup hv σ⁻¹ hx)

@[simp]
theorem coe_valAddSubgroupAut (σ : G) (j : ℤ) (x : ↥(valAddSubgroup A j)) :
    ((valAddSubgroupAut hv σ j x : ↥(valAddSubgroup A j)) : A) = σ • (x : A) := rfl

@[simp]
theorem coe_valAddSubgroupAut_symm (σ : G) (j : ℤ) (x : ↥(valAddSubgroup A j)) :
    (((valAddSubgroupAut hv σ j).symm x : ↥(valAddSubgroup A j)) : A) = σ⁻¹ • (x : A) := rfl

theorem valAddSubgroupAut_pow_eq_one {σ : G} {n : ℕ} (hσ : σ ^ n = 1) (j : ℤ) :
    (valAddSubgroupAut hv σ j) ^ n = 1 :=
  subgroupAut_pow_eq_one _ _ (smulAddAut_pow_eq_one hσ)

/-! ### The action on the unit filtration -/

/-- **An isometry preserves the unit filtration.** -/
theorem smulUnitsAut_mem_unitFiltrationAdd (σ : G) {i : ℕ} {x : Additive Aˣ}
    (hx : x ∈ unitFiltrationAdd A i) : smulUnitsAut σ x ∈ unitFiltrationAdd A i := by
  rw [mem_unitFiltrationAdd] at hx ⊢
  rw [coe_smulUnitsAut_apply,
    show σ • ((Additive.toMul x : Aˣ) : A) - 1 = σ • (((Additive.toMul x : Aˣ) : A) - 1) by
      rw [smul_sub, smul_one], hv]
  exact hx

/-- **The action on a step of the unit filtration.** -/
def unitFiltrationAut (σ : G) (i : ℕ) :
    ↥(unitFiltrationAdd A i) ≃+ ↥(unitFiltrationAdd A i) :=
  subgroupAut (V := Additive Aˣ) (smulUnitsAut σ) (unitFiltrationAdd A i)
    (fun _ hx => smulUnitsAut_mem_unitFiltrationAdd hv σ hx)
    (fun _ hx => by
      rw [← smulUnitsAut_inv]
      exact smulUnitsAut_mem_unitFiltrationAdd hv σ⁻¹ hx)

@[simp]
theorem coe_unitFiltrationAut (σ : G) (i : ℕ) (u : ↥(unitFiltrationAdd A i)) :
    ((unitFiltrationAut hv σ i u : ↥(unitFiltrationAdd A i)) : Additive Aˣ)
      = smulUnitsAut σ (u : Additive Aˣ) := rfl

theorem unitFiltrationAut_pow_eq_one {σ : G} {n : ℕ} (hσ : σ ^ n = 1) (i : ℕ) :
    (unitFiltrationAut hv σ i) ^ n = 1 :=
  subgroupAut_pow_eq_one _ _ (smulUnitsAut_pow_eq_one hσ)

/-! ### The action on a graded piece -/

theorem map_valAddSubgroupAut (σ : G) (j : ℤ) :
    ((valAddSubgroup A (j + 1)).addSubgroupOf (valAddSubgroup A j)).map
        (valAddSubgroupAut hv σ j) =
      (valAddSubgroup A (j + 1)).addSubgroupOf (valAddSubgroup A j) := by
  ext x
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact smul_mem_valAddSubgroup hv σ hy
  · intro hx
    exact ⟨(valAddSubgroupAut hv σ j).symm x, smul_mem_valAddSubgroup hv σ⁻¹ hx, by simp⟩

/-- **The action on a graded piece of the additive filtration.** -/
def gradedAddAut (σ : G) (j : ℤ) : gradedAdd A j ≃+ gradedAdd A j :=
  QuotientAddGroup.congr _ _ (valAddSubgroupAut hv σ j) (map_valAddSubgroupAut hv σ j)

@[simp]
theorem gradedAddAut_mk (σ : G) (j : ℤ) (x : ↥(valAddSubgroup A j)) :
    gradedAddAut hv σ j (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk (valAddSubgroupAut hv σ j x) := rfl

theorem gradedAddAut_pow_mk (σ : G) (j : ℤ) (k : ℕ) (x : ↥(valAddSubgroup A j)) :
    ((gradedAddAut hv σ j) ^ k) (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk (((valAddSubgroupAut hv σ j) ^ k) x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, ih, gradedAddAut_mk, ← pow_succ_apply]

theorem gradedAddAut_pow_eq_one {σ : G} {n : ℕ} (hσ : σ ^ n = 1) (j : ℤ) :
    (gradedAddAut hv σ j) ^ n = 1 :=
  AddEquiv.ext fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H y => rw [gradedAddAut_pow_mk, valAddSubgroupAut_pow_eq_one hv hσ]; rfl

/-! ### The short exact sequence -/

/-- **Consecutive steps of the unit filtration differ by a graded piece of the additive
filtration.** -/
def unitFiltrationTateSES (σ : G) {n : ℕ} (hσ : σ ^ n = 1) (i : ℕ) :
    TateSES n ↥(unitFiltrationAdd A (i + 1)) ↥(unitFiltrationAdd A i)
      (gradedAdd A ((i : ℤ) + 1)) where
  σA := unitFiltrationAut hv σ (i + 1)
  σB := unitFiltrationAut hv σ i
  σC := gradedAddAut hv σ ((i : ℤ) + 1)
  hσA := unitFiltrationAut_pow_eq_one hv hσ _
  hσB := unitFiltrationAut_pow_eq_one hv hσ _
  hσC := gradedAddAut_pow_eq_one hv hσ _
  f := AddSubgroup.inclusion (unitFiltrationAdd_succ_le i)
  g := gradedUnitHom A i
  hf _ := rfl
  hg b := by
    refine congrArg QuotientAddGroup.mk (Subtype.ext ?_)
    show ((Additive.toMul (smulUnitsAut σ (b : Additive Aˣ)) : Aˣ) : A) - 1
        = σ • (((Additive.toMul (b : Additive Aˣ) : Aˣ) : A) - 1)
    rw [coe_smulUnitsAut_apply, smul_sub, smul_one]
  finj := AddSubgroup.inclusion_injective _
  gsurj := gradedUnitHom_surjective i
  range_eq_ker := by
    ext x
    rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, gradedUnitHom_eq_zero_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨(x : Additive Aˣ), hx⟩, rfl⟩

end InverseGalois.CFT
