/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.TrivialIndex

/-!
# The index of the `n`-th powers in the units of the valuation ring

The units of the valuation ring of a complete discretely valued field have Herbrand quotient the
order of the residue field raised to the valuation of `n`, the exponential carrying a step of the
additive filtration onto a step of the unit filtration.  Reading the quotient through its
definition turns that into an index computation: the `n`-th powers of units of the valuation ring
have index the order of the residue field raised to the valuation of `n`, times the number of
`n`-th roots of unity of the field.

Every root of unity is a unit of the valuation ring, since the value group is torsion free, so the
torsion contribution is the same as for the units of the whole field.  Comparing with the index
formula for the units of the field, the two answers differ exactly by the factor `n` coming from
the valuation.

When `n` is a unit at the place, the order of the residue field contributes nothing and the index
is simply the number of `n`-th roots of unity.

## Main definitions

* `InverseGalois.CFT.localUnitGroup`: **the units of the valuation ring**, as a subgroup of the
  units of the field.

## Main results

* `InverseGalois.CFT.valued_eq_one_of_pow_eq_one`: a root of unity is a unit of the valuation ring.
* `InverseGalois.CFT.map_ker_powMonoidHom_localUnitGroup`: the `n`-th roots of unity among the units
  of the valuation ring are all of them.
* `InverseGalois.CFT.index_range_powMonoidHom_localUnitGroup`: **the index of the `n`-th powers in
  the units of the valuation ring.**
* `InverseGalois.CFT.index_range_powMonoidHom_localUnitGroup_of_valued_eq_one`: the same when `n` is
  a unit at the place, where the answer is the number of `n`-th roots of unity.

## Tags

local field, valuation ring, unit group, index, Herbrand quotient, roots of unity
-/

namespace InverseGalois.CFT

open scoped WithZero

/-! ### The units of the valuation ring -/

section UnitGroup

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-- **The units of the valuation ring**, as a subgroup of the units of the field. -/
def localUnitGroup (A : Type*) [Field A] [Valued A ℤᵐ⁰] : Subgroup Aˣ :=
  ValuationSubring.unitGroup (Valuation.valuationSubring (Valued.v : Valuation A ℤᵐ⁰))

theorem mem_localUnitGroup {u : Aˣ} : u ∈ localUnitGroup A ↔ Valued.v (u : A) = 1 :=
  (mem_ker_unitVal_iff_mem_unitGroup (x := Additive.ofMul u)).symm.trans mem_ker_unitVal

/-- **The units of the valuation ring are the kernel of the valuation**, written additively. -/
def kerUnitValAddEquiv : ↥(unitVal (A := A)).ker ≃+ Additive ↥(localUnitGroup A) where
  toFun x := Additive.ofMul (⟨Additive.toMul (x : Additive Aˣ),
    mem_localUnitGroup.mpr (mem_ker_unitVal.mp x.2)⟩ : ↥(localUnitGroup A))
  invFun y := ⟨Additive.ofMul (((Additive.toMul y : ↥(localUnitGroup A)) : Aˣ)),
    mem_ker_unitVal.mpr (mem_localUnitGroup.mp (Additive.toMul y).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **A root of unity is a unit of the valuation ring**, the value group being torsion free. -/
theorem valued_eq_one_of_pow_eq_one {n : ℕ} (hnz : n ≠ 0) {u : Aˣ} (hu : u ^ n = 1) :
    Valued.v (u : A) = 1 := by
  have hzero : unitVal (n • Additive.ofMul u) = 0 := by
    rw [show (n • Additive.ofMul u : Additive Aˣ) = Additive.ofMul (u ^ n) from rfl, hu]
    exact map_zero _
  rw [map_nsmul, nsmul_eq_mul] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) hnz
  · exact mem_ker_unitVal.mp (AddMonoidHom.mem_ker.mpr h)

/-- **The `n`-th roots of unity among the units of the valuation ring are all of them.** -/
theorem map_ker_powMonoidHom_localUnitGroup {n : ℕ} (hnz : n ≠ 0) :
    Subgroup.map (localUnitGroup A).subtype
        (powMonoidHom n : ↥(localUnitGroup A) →* ↥(localUnitGroup A)).ker
      = rootsOfUnity n A := by
  ext u
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.coe_subtype,
    mem_rootsOfUnity]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using congrArg (fun z : ↥(localUnitGroup A) => (z : Aˣ)) hx
  · intro hu
    exact ⟨⟨u, mem_localUnitGroup.mpr (valued_eq_one_of_pow_eq_one hnz hu)⟩,
      Subtype.ext (by simpa using hu), rfl⟩

/-- The number of `n`-th roots of unity among the units of the valuation ring. -/
theorem card_ker_powMonoidHom_localUnitGroup {n : ℕ} (hnz : n ≠ 0) :
    Nat.card ↥(powMonoidHom n : ↥(localUnitGroup A) →* ↥(localUnitGroup A)).ker
      = Nat.card ↥(rootsOfUnity n A) := by
  rw [← map_ker_powMonoidHom_localUnitGroup (A := A) hnz]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (Subgroup.subtype_injective _)).toEquiv

end UnitGroup

/-! ### The index of the `n`-th powers -/

section Index

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {p e n m : ℕ}
  (hsurj : Function.Surjective (Valued.v : A → ℤᵐ⁰))

include hsurj

/-- **The index of the `n`-th powers in the units of the valuation ring**: it is the order of the
residue field raised to the valuation of `n`, times the number of `n`-th roots of unity of the
field. -/
theorem index_range_powMonoidHom_localUnitGroup [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) (hnz : n ≠ 0)
    (hn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    (powMonoidHom n : ↥(localUnitGroup A) →* ↥(localUnitGroup A)).range.index
      = Nat.card (gradedAdd A 0) ^ m * Nat.card ↥(rootsOfUnity n A) := by
  obtain ⟨h0, h1⟩ :=
    finite_tate_one_kerUnitVal (n := n) (m := m) h (exists_valued_eq_exp_neg_one hsurj) hn
  haveI := h0
  haveI := h1
  haveI : Finite (tateH0 (1 : Additive ↥(localUnitGroup A) ≃+ Additive ↥(localUnitGroup A)) n) :=
    Finite.of_equiv _ (tateH0Congr (σA := 1) (σB := 1) (kerUnitValAddEquiv (A := A))
      (fun _ => rfl) n).toEquiv
  haveI : Finite (tateHm1 (1 : Additive ↥(localUnitGroup A) ≃+ Additive ↥(localUnitGroup A)) n) :=
    Finite.of_equiv _ (tateHm1Congr (σA := 1) (σB := 1) (kerUnitValAddEquiv (A := A))
      (fun _ => rfl) n).toEquiv
  have hq : herbrand (1 : Additive ↥(localUnitGroup A) ≃+ Additive ↥(localUnitGroup A)) n
      = (Nat.card (gradedAdd A 0) : ℚ) ^ m := by
    rw [← herbrand_congr (σA := 1) (σB := 1) (kerUnitValAddEquiv (A := A)) (fun _ => rfl) n]
    exact herbrand_one_kerUnitVal h (exists_valued_eq_exp_neg_one hsurj) hn
  rw [herbrand] at hq
  have hcard : (Nat.card (tateHm1
        (1 : Additive ↥(localUnitGroup A) ≃+ Additive ↥(localUnitGroup A)) n) : ℚ)
      = (Nat.card ↥(rootsOfUnity n A) : ℚ) := by
    rw [card_tateHm1_one_additive, card_ker_powMonoidHom_localUnitGroup hnz]
  have hpos : (Nat.card (tateHm1
      (1 : Additive ↥(localUnitGroup A) ≃+ Additive ↥(localUnitGroup A)) n) : ℚ) ≠ 0 :=
    (cast_card_tateHm1_pos _ n).ne'
  rw [div_eq_iff hpos, hcard] at hq
  refine Nat.cast_injective (R := ℚ) ?_
  rw [← card_tateH0_one_additive, hq]
  push_cast
  ring

/-- **The index of the `n`-th powers in the units of the valuation ring when `n` is a unit at the
place**: it is the number of `n`-th roots of unity of the field. -/
theorem index_range_powMonoidHom_localUnitGroup_of_valued_eq_one [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) (hnz : n ≠ 0) (hn : Valued.v ((n : ℕ) : A) = 1) :
    (powMonoidHom n : ↥(localUnitGroup A) →* ↥(localUnitGroup A)).range.index
      = Nat.card ↥(rootsOfUnity n A) := by
  rw [index_range_powMonoidHom_localUnitGroup (m := 0) hsurj h hnz (by
      rw [hn, Nat.cast_zero, neg_zero, WithZero.exp_zero]), pow_zero, one_mul]

end Index

end InverseGalois.CFT
