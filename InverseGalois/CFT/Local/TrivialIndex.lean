/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.GradedFinite
import InverseGalois.CFT.Local.UnitHerbrandChain
import InverseGalois.CFT.Tate.TrivialLattice

/-!
# The index of the `n`-th powers in the units of a complete discretely valued field

Forgetting any action, the Herbrand machinery still computes.  Multiplication by `n` carries a step
of the additive filtration isomorphically onto the step that is the valuation of `n` places further
down, so the upper Tate group of a step with trivial action is the quotient of the two steps while
the lower one vanishes: the Herbrand quotient of a step is the order of a graded piece raised to
the valuation of `n`.  The exponential carries a deep enough step of the additive filtration onto a
step of the unit filtration, that step has finite index in the units of the valuation ring, and the
valuation presents the units of the field as an extension of the integers by the units of the
valuation ring.  Multiplying the three contributions, the units of the field have Herbrand quotient
`n` times the order of a graded piece raised to the valuation of `n`.

Read through the definition of the quotient, this is the classical local index formula: the index
of the `n`-th powers in the units of the field is `n`, times the order of the residue field raised
to the valuation of `n`, times the number of `n`-th roots of unity in the field.

## Main definitions

* `InverseGalois.CFT.localUnitsTrivialTateSES`: the valuation sequence of the units, with trivial
  actions.

## Main results

* `InverseGalois.CFT.relIndex_valAddSubgroup_add_eq`: the relative index of two steps of the
  additive filtration is the order of a graded piece raised to the number of steps between them.
* `InverseGalois.CFT.herbrand_one_valAddSubgroup`: **a step of the additive filtration has Herbrand
  quotient the order of a graded piece raised to the valuation of `n`.**
* `InverseGalois.CFT.herbrand_one_kerUnitVal`: the units of the valuation ring have the same
  Herbrand quotient.
* `InverseGalois.CFT.herbrand_one_localUnits`: **the units of the field have Herbrand quotient `n`
  times that.**
* `InverseGalois.CFT.index_range_powMonoidHom_units`: **the index of the `n`-th powers in the units
  of the field**, in terms of the number of `n`-th roots of unity.
* `InverseGalois.CFT.index_range_powMonoidHom_units_padicValNat`: the same, with the valuation of
  `n` expressed through the residue characteristic.

## Tags

local field, unit group, index, Herbrand quotient, roots of unity, exponential
-/

namespace InverseGalois.CFT

open scoped WithZero

/-! ### The relative index of two steps of the additive filtration -/

section Filtration

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-- A surjective valuation has a uniformizer. -/
theorem exists_valued_eq_exp_neg_one (hsurj : Function.Surjective (Valued.v : A → ℤᵐ⁰)) :
    ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ) := hsurj _

/-- All the graded pieces of the additive filtration of a field with a uniformizer have the same
order. -/
theorem card_gradedAdd_eq (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ)) (j : ℤ) :
    Nat.card (gradedAdd A j) = Nat.card (gradedAdd A 0) := by
  obtain ⟨c, hc⟩ := exists_valued_eq_exp hπ j
  have h := Nat.card_congr (gradedAddEquivOfMul hc 0).toEquiv
  rw [zero_add] at h
  exact h.symm

/-- The relative index of consecutive steps of the additive filtration is the order of the graded
piece between them. -/
theorem relIndex_valAddSubgroup_succ_eq (j : ℤ) :
    (valAddSubgroup A (j + 1)).relIndex (valAddSubgroup A j) = Nat.card (gradedAdd A j) := rfl

/-- **The relative index of two steps of the additive filtration** is the order of a graded piece
raised to the number of steps between them. -/
theorem relIndex_valAddSubgroup_add_eq (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ)) (j : ℤ)
    (m : ℕ) :
    (valAddSubgroup A (j + m)).relIndex (valAddSubgroup A j) = Nat.card (gradedAdd A 0) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hstep := AddSubgroup.relIndex_mul_relIndex (valAddSubgroup A (j + (k : ℤ) + 1))
      (valAddSubgroup A (j + (k : ℤ))) (valAddSubgroup A j)
      (valAddSubgroup_le_valAddSubgroup (by omega)) (valAddSubgroup_le_valAddSubgroup (by omega))
    rw [relIndex_valAddSubgroup_succ_eq, card_gradedAdd_eq hπ, ih] at hstep
    have hj : j + ((k + 1 : ℕ) : ℤ) = j + (k : ℤ) + 1 := by push_cast; ring
    rw [hj, ← hstep, pow_succ, mul_comm]

end Filtration

/-! ### A step of the additive filtration with trivial action -/

section Additive

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {n m : ℕ}

/-- **The norms of a trivial action on a step of the additive filtration are the step that is the
valuation of `n` places further down.** -/
theorem range_normHom_one_valAddSubgroup (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ)))
    (j : ℤ) :
    (normHom (1 : ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A j)) n).range
      = (valAddSubgroup A (j + m)).addSubgroupOf (valAddSubgroup A j) := by
  ext y
  rw [AddMonoidHom.mem_range, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨x, rfl⟩
    have hcoe : ((normHom (1 : ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A j)) n x :
        ↥(valAddSubgroup A j)) : A) = ((n : ℕ) : A) * (x : A) := by
      rw [normHom_one_apply]
      push_cast
      ring
    rw [hcoe]
    exact mul_mem_valAddSubgroup_of_val_eq hn x.2
  · intro hy
    refine ⟨⟨((n : ℕ) : A)⁻¹ * (y : A), inv_mul_mem_valAddSubgroup hn hy⟩, Subtype.ext ?_⟩
    rw [normHom_one_apply]
    show (n : ℕ) • (((n : ℕ) : A)⁻¹ * (y : A)) = (y : A)
    rw [nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_zero_of_valued_eq_exp hn), one_mul]

/-- A step of the additive filtration has no `n`-torsion, so its lower Tate group for a trivial
action vanishes. -/
theorem card_tateHm1_one_valAddSubgroup (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ)))
    (j : ℤ) :
    Nat.card (tateHm1 (1 : ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A j)) n) = 1 := by
  refine card_tateHm1_trivial n fun x hx => ?_
  have hc : ((n : ℕ) : A) * (x : A) = 0 := by
    have h := congrArg (fun y : ↥(valAddSubgroup A j) => (y : A)) hx
    simpa [nsmul_eq_mul] using h
  exact Subtype.ext ((mul_eq_zero.mp hc).resolve_left (ne_zero_of_valued_eq_exp hn))

/-- **The upper Tate group of a step of the additive filtration with trivial action** is the
quotient by the step that is the valuation of `n` places further down. -/
theorem card_tateH0_one_valAddSubgroup (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) (j : ℤ) :
    Nat.card (tateH0 (1 : ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A j)) n)
      = Nat.card (gradedAdd A 0) ^ m := by
  have hrel : ((valAddSubgroup A (j + m)).addSubgroupOf (valAddSubgroup A j)).index
      = (valAddSubgroup A (j + m)).relIndex (valAddSubgroup A j) := rfl
  rw [card_tateH0_trivial, range_normHom_one_valAddSubgroup hn, hrel,
    relIndex_valAddSubgroup_add_eq hπ]

/-- **A step of the additive filtration has Herbrand quotient the order of a graded piece raised to
the valuation of `n`.** -/
theorem herbrand_one_valAddSubgroup (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) (j : ℤ) :
    herbrand (1 : ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A j)) n
      = (Nat.card (gradedAdd A 0) : ℚ) ^ m := by
  rw [herbrand, card_tateH0_one_valAddSubgroup hπ hn, card_tateHm1_one_valAddSubgroup hn,
    Nat.cast_one, div_one, Nat.cast_pow]

/-- Both Tate groups of a step of the additive filtration with trivial action are finite. -/
theorem finite_tate_one_valAddSubgroup [Finite (gradedAdd A 0)]
    (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) (j : ℤ) :
    Finite (tateH0 (1 : ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A j)) n)
      ∧ Finite (tateHm1 (1 : ↥(valAddSubgroup A j) ≃+ ↥(valAddSubgroup A j)) n) := by
  constructor
  · refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateH0_one_valAddSubgroup hπ hn]
    exact pow_ne_zero _ (Nat.card_pos (α := gradedAdd A 0)).ne'
  · refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateHm1_one_valAddSubgroup hn]
    exact one_ne_zero

end Additive

/-! ### The unit filtration and the units of the valuation ring -/

section Unit

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {p e n m : ℕ}

/-- **A deep enough step of the unit filtration has Herbrand quotient the order of a graded piece
raised to the valuation of `n`**, the exponential carrying a step of the additive filtration onto
it. -/
theorem herbrand_one_unitFiltrationAdd (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1))
    (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    herbrand (1 : ↥(unitFiltrationAdd A i) ≃+ ↥(unitFiltrationAdd A i)) n
      = (Nat.card (gradedAdd A 0) : ℚ) ^ m := by
  rw [← herbrand_congr (σA := (1 : ↥(valAddSubgroup A ((i : ℤ) + 1))
    ≃+ ↥(valAddSubgroup A ((i : ℤ) + 1)))) (σB := 1) (padicExpEquiv h hi) (fun _ => rfl) n]
  exact herbrand_one_valAddSubgroup hπ hn _

/-- Both Tate groups of a deep enough step of the unit filtration with trivial action are
finite. -/
theorem finite_tate_one_unitFiltrationAdd [Finite (gradedAdd A 0)] (h : HasResidueChar A p e)
    {i : ℕ} (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1))
    (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    Finite (tateH0 (1 : ↥(unitFiltrationAdd A i) ≃+ ↥(unitFiltrationAdd A i)) n)
      ∧ Finite (tateHm1 (1 : ↥(unitFiltrationAdd A i) ≃+ ↥(unitFiltrationAdd A i)) n) := by
  obtain ⟨h0, h1⟩ := finite_tate_one_valAddSubgroup (n := n) (m := m) hπ hn ((i : ℤ) + 1)
  haveI := h0
  haveI := h1
  exact ⟨Finite.of_equiv _ (tateH0Congr (σA := 1) (σB := 1) (padicExpEquiv h hi)
      (fun _ => rfl) n).toEquiv,
    Finite.of_equiv _ (tateHm1Congr (σA := 1) (σB := 1) (padicExpEquiv h hi)
      (fun _ => rfl) n).toEquiv⟩

omit [CompleteSpace A] in
/-- Forgetting that a step of the unit filtration lies inside the units of the valuation ring
commutes with the trivial actions. -/
theorem addSubgroupOfEquivOfLe_one_equivariant (i : ℕ)
    (x : ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)) :
    AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal i)
        ((1 : ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)
          ≃+ ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)) x)
      = (1 : ↥(unitFiltrationAdd A i) ≃+ ↥(unitFiltrationAdd A i))
        (AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal i) x) := rfl

/-- Both Tate groups of a step of the unit filtration, viewed inside the units of the valuation
ring, are finite for the trivial action. -/
theorem finite_tate_one_kerUnitFiltration [Finite (gradedAdd A 0)] (h : HasResidueChar A p e)
    {i : ℕ} (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1))
    (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    Finite (tateH0 (1 : ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)
        ≃+ ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)) n)
      ∧ Finite (tateHm1 (1 : ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)
        ≃+ ↥((unitFiltrationAdd A i).addSubgroupOf (unitVal (A := A)).ker)) n) := by
  obtain ⟨h0, h1⟩ := finite_tate_one_unitFiltrationAdd (n := n) (m := m) h hi hπ hn
  haveI := h0
  haveI := h1
  exact ⟨Finite.of_equiv _ (tateH0Congr (σA := 1) (σB := 1)
      (AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal i))
      (addSubgroupOfEquivOfLe_one_equivariant i) n).symm.toEquiv,
    Finite.of_equiv _ (tateHm1Congr (σA := 1) (σB := 1)
      (AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal i))
      (addSubgroupOfEquivOfLe_one_equivariant i) n).symm.toEquiv⟩

/-- **The units of the valuation ring have Herbrand quotient the order of a graded piece raised to
the valuation of `n`**, a deep step of the unit filtration having finite index in them. -/
theorem herbrand_one_kerUnitVal [∀ k : ℤ, Finite (gradedAdd A k)] (h : HasResidueChar A p e)
    (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    herbrand (1 : ↥(unitVal (A := A)).ker ≃+ ↥(unitVal (A := A)).ker) n
      = (Nat.card (gradedAdd A 0) : ℚ) ^ m := by
  obtain ⟨h0, h1⟩ := finite_tate_one_kerUnitFiltration (n := n) (m := m) h (lt_mul_sub_one h) hπ hn
  haveI := h0
  haveI := h1
  haveI := finite_quotient_ker_unitVal (A := A) e
  rw [← herbrand_eq_of_finite_index_of_finite_source
    (σB := (1 : ↥(unitVal (A := A)).ker ≃+ ↥(unitVal (A := A)).ker)) (one_pow n)
    ((unitFiltrationAdd A e).addSubgroupOf (unitVal (A := A)).ker)
    (1 : ↥((unitFiltrationAdd A e).addSubgroupOf (unitVal (A := A)).ker)
      ≃+ ↥((unitFiltrationAdd A e).addSubgroupOf (unitVal (A := A)).ker))
    (fun _ => rfl) (one_pow n)]
  rw [herbrand_congr (σA := 1) (σB := 1)
    (AddSubgroup.addSubgroupOfEquivOfLe (unitFiltrationAdd_le_ker_unitVal e))
    (addSubgroupOfEquivOfLe_one_equivariant e) n]
  exact herbrand_one_unitFiltrationAdd h (lt_mul_sub_one h) hπ hn

/-- Both Tate groups of the units of the valuation ring with trivial action are finite. -/
theorem finite_tate_one_kerUnitVal [∀ k : ℤ, Finite (gradedAdd A k)] (h : HasResidueChar A p e)
    (hπ : ∃ π : A, Valued.v π = WithZero.exp (-1 : ℤ))
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    Finite (tateH0 (1 : ↥(unitVal (A := A)).ker ≃+ ↥(unitVal (A := A)).ker) n)
      ∧ Finite (tateHm1 (1 : ↥(unitVal (A := A)).ker ≃+ ↥(unitVal (A := A)).ker) n) := by
  obtain ⟨h0, h1⟩ := finite_tate_one_kerUnitFiltration (n := n) (m := m) h (lt_mul_sub_one h) hπ hn
  haveI := h0
  haveI := h1
  haveI := finite_quotient_ker_unitVal (A := A) e
  haveI : Finite (↥(unitVal (A := A)).ker ⧸
      ((unitFiltrationAdd A e).addSubgroupOf (unitVal (A := A)).ker).subtype.range) := by
    rw [range_subtype_eq]
    infer_instance
  exact ⟨finite_tateH0_of_injective (σA := 1) (σB := 1) (one_pow n) (one_pow n)
      ((unitFiltrationAdd A e).addSubgroupOf (unitVal (A := A)).ker).subtype (fun _ => rfl)
      (AddSubgroup.subtype_injective _),
    finite_tateHm1_of_injective (σA := 1) (σB := 1) (one_pow n) (one_pow n)
      ((unitFiltrationAdd A e).addSubgroupOf (unitVal (A := A)).ker).subtype (fun _ => rfl)
      (AddSubgroup.subtype_injective _)⟩

end Unit

/-! ### The units of the field -/

section Units

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {p e n m : ℕ}
  (hsurj : Function.Surjective (Valued.v : A → ℤᵐ⁰))

include hsurj

/-- **The valuation sequence of the units of the field, with trivial actions**: the units of the
valuation ring, the units of the field, and the integers. -/
def localUnitsTrivialTateSES (n : ℕ) :
    TateSES n ↥(unitVal (A := A)).ker (Additive Aˣ) ℤ where
  σA := 1
  σB := 1
  σC := 1
  hσA := one_pow n
  hσB := one_pow n
  hσC := one_pow n
  f := (unitVal (A := A)).ker.subtype
  g := unitVal
  hf _ := rfl
  hg _ := rfl
  finj := AddSubgroup.subtype_injective _
  gsurj := unitVal_surjective hsurj
  range_eq_ker := AddSubgroup.range_subtype _

/-- Both Tate groups of the units of the field with trivial action are finite. -/
theorem finite_tate_one_units [∀ k : ℤ, Finite (gradedAdd A k)] (h : HasResidueChar A p e)
    (hnz : n ≠ 0) (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    Finite (tateH0 (1 : Additive Aˣ ≃+ Additive Aˣ) n)
      ∧ Finite (tateHm1 (1 : Additive Aˣ ≃+ Additive Aˣ) n) := by
  obtain ⟨h0, h1⟩ :=
    finite_tate_one_kerUnitVal (n := n) (m := m) h (exists_valued_eq_exp_neg_one hsurj) hn
  haveI hC0 : Finite (tateH0 (1 : ℤ ≃+ ℤ) n) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateH0_int]
    exact hnz
  haveI hCm : Finite (tateHm1 (1 : ℤ ≃+ ℤ) n) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateHm1_int n hnz]
    exact one_ne_zero
  haveI : Finite (tateH0 (localUnitsTrivialTateSES hsurj n).σA n) := h0
  haveI : Finite (tateHm1 (localUnitsTrivialTateSES hsurj n).σA n) := h1
  haveI : Finite (tateH0 (localUnitsTrivialTateSES hsurj n).σC n) := hC0
  haveI : Finite (tateHm1 (localUnitsTrivialTateSES hsurj n).σC n) := hCm
  exact ⟨(localUnitsTrivialTateSES hsurj n).finite_tateH0_mid',
    (localUnitsTrivialTateSES hsurj n).finite_tateHm1_mid'⟩

/-- **The units of the field have Herbrand quotient `n` times the order of a graded piece raised to
the valuation of `n`.** -/
theorem herbrand_one_localUnits [∀ k : ℤ, Finite (gradedAdd A k)] (h : HasResidueChar A p e)
    (hnz : n ≠ 0) (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    herbrand (1 : Additive Aˣ ≃+ Additive Aˣ) n
      = (n : ℚ) * (Nat.card (gradedAdd A 0) : ℚ) ^ m := by
  obtain ⟨hA0, hAm⟩ :=
    finite_tate_one_kerUnitVal (n := n) (m := m) h (exists_valued_eq_exp_neg_one hsurj) hn
  obtain ⟨hB0, hBm⟩ := finite_tate_one_units (m := m) hsurj h hnz hn
  haveI hC0 : Finite (tateH0 (1 : ℤ ≃+ ℤ) n) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateH0_int]
    exact hnz
  haveI hCm : Finite (tateHm1 (1 : ℤ ≃+ ℤ) n) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_tateHm1_int n hnz]
    exact one_ne_zero
  haveI : Finite (tateH0 (localUnitsTrivialTateSES hsurj n).σA n) := hA0
  haveI : Finite (tateHm1 (localUnitsTrivialTateSES hsurj n).σA n) := hAm
  haveI : Finite (tateH0 (localUnitsTrivialTateSES hsurj n).σB n) := hB0
  haveI : Finite (tateHm1 (localUnitsTrivialTateSES hsurj n).σB n) := hBm
  haveI : Finite (tateH0 (localUnitsTrivialTateSES hsurj n).σC n) := hC0
  haveI : Finite (tateHm1 (localUnitsTrivialTateSES hsurj n).σC n) := hCm
  have hmul := (localUnitsTrivialTateSES (A := A) hsurj n).herbrand_mul
  rw [show (localUnitsTrivialTateSES (A := A) hsurj n).σA = 1 from rfl,
    show (localUnitsTrivialTateSES (A := A) hsurj n).σB = 1 from rfl,
    show (localUnitsTrivialTateSES (A := A) hsurj n).σC = 1 from rfl,
    herbrand_one_kerUnitVal h (exists_valued_eq_exp_neg_one hsurj) hn,
    herbrand_int n hnz] at hmul
  rw [← hmul, mul_comm]

omit [Valued A ℤᵐ⁰] [CompleteSpace A] hsurj in
/-- The `n`-th roots of unity are the kernel of raising to the `n`-th power. -/
theorem ker_powMonoidHom_units :
    (powMonoidHom n : Aˣ →* Aˣ).ker = rootsOfUnity n A := by
  ext u
  rw [MonoidHom.mem_ker, powMonoidHom_apply, mem_rootsOfUnity]

/-- **The index of the `n`-th powers in the units of a complete discretely valued field**: it is
`n`, times the order of a graded piece raised to the valuation of `n`, times the number of `n`-th
roots of unity. -/
theorem index_range_powMonoidHom_units [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) (hnz : n ≠ 0)
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    (powMonoidHom n : Aˣ →* Aˣ).range.index
      = n * Nat.card (gradedAdd A 0) ^ m * Nat.card ↥(rootsOfUnity n A) := by
  obtain ⟨hB0, hBm⟩ := finite_tate_one_units (m := m) hsurj h hnz hn
  haveI := hB0
  haveI := hBm
  have hq := herbrand_one_localUnits (m := m) hsurj h hnz hn
  rw [herbrand] at hq
  have hcard : (Nat.card (tateHm1 (1 : Additive Aˣ ≃+ Additive Aˣ) n) : ℚ)
      = (Nat.card ↥(rootsOfUnity n A) : ℚ) := by
    rw [card_tateHm1_one_additive, ker_powMonoidHom_units]
  have hpos : (Nat.card (tateHm1 (1 : Additive Aˣ ≃+ Additive Aˣ) n) : ℚ) ≠ 0 :=
    (cast_card_tateHm1_pos (1 : Additive Aˣ ≃+ Additive Aˣ) n).ne'
  rw [div_eq_iff hpos, hcard] at hq
  refine Nat.cast_injective (R := ℚ) ?_
  rw [← card_tateH0_one_additive, hq]
  push_cast
  ring

/-- **The index of the `n`-th powers in the units of a complete discretely valued field**, with the
valuation of `n` read off from the residue characteristic. -/
theorem index_range_powMonoidHom_units_padicValNat [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) (hnz : n ≠ 0) :
    (powMonoidHom n : Aˣ →* Aˣ).range.index
      = n * Nat.card (gradedAdd A 0) ^ (e * padicValNat p n) * Nat.card ↥(rootsOfUnity n A) := by
  refine index_range_powMonoidHom_units (m := e * padicValNat p n) hsurj h hnz ?_
  rw [h.valued_natCast hnz]
  push_cast
  ring_nf

end Units

end InverseGalois.CFT
