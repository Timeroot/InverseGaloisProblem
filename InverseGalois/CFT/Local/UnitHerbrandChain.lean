/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.ExpAction
import InverseGalois.CFT.Local.FiltrationHerbrand
import InverseGalois.CFT.Local.NormalLattice
import InverseGalois.CFT.Local.UnitIndex

/-!
# The Herbrand quotient of the units of a complete discretely valued field

A cyclic group acting faithfully by isometries on a complete discretely valued field with finite
graded pieces gives every step of the additive filtration Herbrand quotient one, because each step
contains a normal lattice of finite index.  The exponential carries a deep enough step of the
additive filtration isomorphically and equivariantly onto a step of the unit filtration, so that
step of the unit filtration also has Herbrand quotient one; and it is of finite index in the units
of the valuation ring, so those have Herbrand quotient one as well.  Comparing with the valuation
gives the Herbrand quotient of the units of the field: it is the order of the group.

## Main definitions

* `InverseGalois.CFT.kerUnitFiltrationAut`: the action on a step of the unit filtration, viewed
  inside the units of the valuation ring.

## Main results

* `InverseGalois.CFT.herbrand_unitFiltrationAut_eq_one`: **a deep enough step of the unit
  filtration has Herbrand quotient one.**
* `InverseGalois.CFT.herbrand_kerUnitValAut_eq_one`: **the units of the valuation ring have
  Herbrand quotient one.**
* `InverseGalois.CFT.herbrand_smulUnitsAut_eq_card`: **the units of the field have Herbrand
  quotient the order of the group.**

## Tags

valued field, unit group, Herbrand quotient, normal basis, local field
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {G A : Type*} [Group G] [Fintype G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  [FaithfulSMul G A] {p e : ℕ}
  (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-! ### The additive filtration -/

/-- Both Tate groups of every step of the additive filtration are finite under a cyclic group. -/
theorem finite_tate_valAddSubgroupAut_all [∀ k : ℤ, Finite (gradedAdd A k)] {σ : G}
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) (k : ℤ) :
    Finite (tateH0 (valAddSubgroupAut hv σ k) d)
      ∧ Finite (tateHm1 (valAddSubgroupAut hv σ k) d) := by
  obtain ⟨j, hj⟩ := exists_mem_valAddSubgroup_normalElt (G := G) (A := A)
  obtain ⟨h0, h1⟩ := finite_tate_valAddSubgroupAut_normal hv hgen hσ hcard j hj
  haveI := h0
  haveI := h1
  exact finite_tate_valAddSubgroupAut hv hσ j k

/-! ### The unit filtration -/

variable [CompleteSpace A]

/-- Both Tate groups of a deep enough step of the unit filtration are finite under a cyclic
group. -/
theorem finite_tate_unitFiltrationAut [∀ k : ℤ, Finite (gradedAdd A k)] (h : HasResidueChar A p e)
    {i : ℕ} (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) {σ : G}
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) :
    Finite (tateH0 (unitFiltrationAut hv σ i) d)
      ∧ Finite (tateHm1 (unitFiltrationAut hv σ i) d) := by
  obtain ⟨h0, h1⟩ := finite_tate_valAddSubgroupAut_all hv hgen hσ hcard ((i : ℤ) + 1)
  haveI := h0
  haveI := h1
  exact ⟨Finite.of_equiv _
      (tateH0Congr (padicExpEquiv h hi) (padicExpEquiv_equivariant hv h hi σ) d).toEquiv,
    Finite.of_equiv _
      (tateHm1Congr (padicExpEquiv h hi) (padicExpEquiv_equivariant hv h hi σ) d).toEquiv⟩

/-- **A deep enough step of the unit filtration has Herbrand quotient one.** -/
theorem herbrand_unitFiltrationAut_eq_one [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) {i : ℕ} (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) {σ : G}
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) : herbrand (unitFiltrationAut hv σ i) d = 1 := by
  rw [← herbrand_unitFiltrationAut hv h hi σ d]
  exact herbrand_valAddSubgroupAut_eq_one hv hgen hσ hcard _

/-! ### The units of the valuation ring -/

omit [Fintype G] [FaithfulSMul G A] [CompleteSpace A] in
/-- A step of the unit filtration is preserved by the action on the units of the valuation ring. -/
theorem kerUnitValAut_mem_addSubgroupOf (σ : G) (i : ℕ) (x : ↥(unitVal (A := A)).ker)
    (hx : x ∈ (unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker) :
    kerUnitValAut hv σ x ∈ (unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker :=
  smulUnitsAut_mem_unitFiltrationAdd hv σ hx

omit [Fintype G] [FaithfulSMul G A] [CompleteSpace A] in
/-- A step of the unit filtration is preserved by the inverse of the action on the units of the
valuation ring. -/
theorem kerUnitValAut_symm_mem_addSubgroupOf (σ : G) (i : ℕ) (x : ↥(unitVal (A := A)).ker)
    (hx : x ∈ (unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker) :
    (kerUnitValAut hv σ).symm x ∈ (unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker := by
  have hmem : (smulUnitsAut σ⁻¹ (x : Additive Aˣ)) ∈ unitFiltrationAdd A i :=
    smulUnitsAut_mem_unitFiltrationAdd hv σ⁻¹ hx
  rw [smulUnitsAut_inv] at hmem
  exact hmem

omit [Fintype G] [FaithfulSMul G A] [CompleteSpace A] in
/-- **The action on a step of the unit filtration, viewed inside the units of the valuation
ring.** -/
def kerUnitFiltrationAut (σ : G) (i : ℕ) :
    ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)
      ≃+ ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker) :=
  subgroupAut (kerUnitValAut hv σ) _ (kerUnitValAut_mem_addSubgroupOf hv σ i)
    (kerUnitValAut_symm_mem_addSubgroupOf hv σ i)

omit [Fintype G] [FaithfulSMul G A] [CompleteSpace A] in
theorem kerUnitFiltrationAut_pow_eq_one {σ : G} {n : ℕ} (hσ : σ ^ n = 1) (i : ℕ) :
    (kerUnitFiltrationAut hv σ i) ^ n = 1 :=
  subgroupAut_pow_eq_one _ _ (kerUnitValAut_pow_eq_one hv hσ)

omit [Fintype G] [FaithfulSMul G A] [CompleteSpace A] in
/-- Forgetting that a step of the unit filtration lies inside the units of the valuation ring is
equivariant. -/
theorem addSubgroupOfEquivOfLe_equivariant (σ : G) (i : ℕ)
    (x : ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)) :
    AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal i)
        (kerUnitFiltrationAut hv σ i x)
      = unitFiltrationAut hv σ i
        (AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal i) x) := rfl

/-- Both Tate groups of a step of the unit filtration, viewed inside the units of the valuation
ring, are finite under a cyclic group. -/
theorem finite_tate_kerUnitFiltrationAut [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) {i : ℕ} (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) {σ : G}
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) :
    Finite (tateH0 (kerUnitFiltrationAut hv σ i) d)
      ∧ Finite (tateHm1 (kerUnitFiltrationAut hv σ i) d) := by
  obtain ⟨h0, h1⟩ := finite_tate_unitFiltrationAut hv h hi hgen hσ hcard
  haveI := h0
  haveI := h1
  exact ⟨Finite.of_equiv _ (tateH0Congr
      (AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal i))
      (addSubgroupOfEquivOfLe_equivariant hv σ i) d).symm.toEquiv,
    Finite.of_equiv _ (tateHm1Congr
      (AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal i))
      (addSubgroupOfEquivOfLe_equivariant hv σ i) d).symm.toEquiv⟩

omit [Fintype G] [FaithfulSMul G A] hv [CompleteSpace A] in
/-- The prime itself gives a step of the unit filtration deep enough for the exponential. -/
theorem lt_mul_sub_one (h : HasResidueChar A p e) :
    (e : ℤ) < ((e : ℤ) + 1) * ((p : ℤ) - 1) := by
  have hp : 1 < (p : ℤ) := h.one_lt_p
  nlinarith [Int.natCast_nonneg e]

/-- **The units of the valuation ring have Herbrand quotient one.** -/
theorem herbrand_kerUnitValAut_eq_one [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d]
    (hσ : σ ^ d = 1) (hcard : Nat.card G = d) : herbrand (kerUnitValAut hv σ) d = 1 := by
  obtain ⟨h0, h1⟩ := finite_tate_kerUnitFiltrationAut hv h (lt_mul_sub_one h) hgen hσ hcard
  haveI := h0
  haveI := h1
  haveI := finite_quotient_ker_unitVal (A := A) e
  rw [← herbrand_eq_of_finite_index_of_finite_source (kerUnitValAut_pow_eq_one hv hσ) _
    (kerUnitFiltrationAut hv σ e) (fun _ => rfl) (kerUnitFiltrationAut_pow_eq_one hv hσ e)]
  rw [herbrand_congr (AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal e))
    (addSubgroupOfEquivOfLe_equivariant hv σ e) d]
  exact herbrand_unitFiltrationAut_eq_one hv h (lt_mul_sub_one h) hgen hσ hcard

/-- Both Tate groups of the units of the valuation ring are finite under a cyclic group. -/
theorem finite_tate_kerUnitValAut [∀ k : ℤ, Finite (gradedAdd A k)] (h : HasResidueChar A p e)
    {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) :
    Finite (tateH0 (kerUnitValAut hv σ) d) ∧ Finite (tateHm1 (kerUnitValAut hv σ) d) := by
  obtain ⟨h0, h1⟩ := finite_tate_kerUnitFiltrationAut hv h (lt_mul_sub_one h) hgen hσ hcard
  haveI := h0
  haveI := h1
  haveI := finite_quotient_ker_unitVal (A := A) e
  haveI : Finite (↥(unitVal (A := A)).ker ⧸
      ((unitFiltrationAdd A e).addSubgroupOf (unitVal (A := A)).ker).subtype.range) := by
    rw [range_subtype_eq]
    infer_instance
  exact ⟨finite_tateH0_of_injective (kerUnitFiltrationAut_pow_eq_one hv hσ e)
      (kerUnitValAut_pow_eq_one hv hσ) _ (fun _ => rfl)
      (AddSubgroup.subtype_injective _),
    finite_tateHm1_of_injective (kerUnitFiltrationAut_pow_eq_one hv hσ e)
      (kerUnitValAut_pow_eq_one hv hσ) _ (fun _ => rfl)
      (AddSubgroup.subtype_injective _)⟩

/-! ### The units of the field -/

variable {m : ℤ} (hm : IsUnitValGen A m)

include hm

/-- Both Tate groups of the units of the field are finite under a cyclic group. -/
theorem finite_tate_smulUnitsAut [∀ k : ℤ, Finite (gradedAdd A k)] (h : HasResidueChar A p e)
    {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) :
    Finite (tateH0 (smulUnitsAut (R := A) σ) d)
      ∧ Finite (tateHm1 (smulUnitsAut (R := A) σ) d) := by
  obtain ⟨h0, h1⟩ := finite_tate_kerUnitValAut hv h hgen hσ hcard
  have hd : d ≠ 0 := NeZero.ne d
  haveI hC0 : Finite (tateH0 (1 : ℤ ≃+ ℤ) d) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateH0_int]
    exact hd
  haveI hCm : Finite (tateHm1 (1 : ℤ ≃+ ℤ) d) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateHm1_int d hd]
    exact one_ne_zero
  haveI : Finite (tateH0 (localUnitsTateSES hv hm σ hσ).σA d) := h0
  haveI : Finite (tateHm1 (localUnitsTateSES hv hm σ hσ).σA d) := h1
  haveI : Finite (tateH0 (localUnitsTateSES hv hm σ hσ).σC d) := hC0
  haveI : Finite (tateHm1 (localUnitsTateSES hv hm σ hσ).σC d) := hCm
  exact ⟨(localUnitsTateSES hv hm σ hσ).finite_tateH0_mid',
    (localUnitsTateSES hv hm σ hσ).finite_tateHm1_mid'⟩

/-- **The units of the field have Herbrand quotient the order of the group.** -/
theorem herbrand_smulUnitsAut_eq_card [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d]
    (hσ : σ ^ d = 1) (hcard : Nat.card G = d) :
    herbrand (smulUnitsAut (R := A) σ) d = d := by
  obtain ⟨hA0, hAm⟩ := finite_tate_kerUnitValAut hv h hgen hσ hcard
  obtain ⟨hB0, hBm⟩ := finite_tate_smulUnitsAut hv hm h hgen hσ hcard
  haveI := hA0
  haveI := hAm
  haveI := hB0
  haveI := hBm
  rw [← herbrand_smulUnitsAut_mul hv hm σ (NeZero.ne d) hσ,
    herbrand_kerUnitValAut_eq_one hv h hgen hσ hcard, one_mul]

end InverseGalois.CFT
