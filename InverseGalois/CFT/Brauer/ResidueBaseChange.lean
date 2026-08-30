/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.FrobeniusBaseChange

/-!
# The residues of an extension seen over a compatibly normed intermediate field

Let `K ⊆ M ⊆ L` be a tower of nonarchimedean local fields in which the absolute value of `M`
extends the absolute value of `K`.  The absolute value of `L` is then the same whether it is
computed over `K` or over `M`, so the integers of `L` are the same subring in both cases and the
congruence cutting out the residues is the same congruence.  **The residue ring of `L` therefore
does not depend on which of the two base fields it is computed over.**

This is the counting statement that turns "the intermediate field is totally ramified" into a
statement one can compare with the degree of an unramified extension of it.

## Main definitions

* `InverseGalois.CFT.divisionResidueBaseChange`: the residue ring over the intermediate field
  inside the residue ring over the base field.

## Main results

* `InverseGalois.CFT.divisionResidueBaseChange_bijective`,
  `InverseGalois.CFT.natCard_divisionResidue_base`: **the residues of an extension do not depend on
  which of two compatibly normed base fields they are computed over.**

## Tags

local field, residue field, base change, ramification
-/

set_option synthInstance.maxHeartbeats 800000

universe u

namespace InverseGalois.CFT

open Module

variable {K M L : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [NontriviallyNormedField M] [IsUltrametricDist M] [ProperSpace M]
variable [Algebra K M] [FiniteDimensional K M]
variable [Field L] [Algebra M L] [FiniteDimensional M L] [Algebra K L] [IsScalarTower K M L]
variable [FiniteDimensional K L]

/-! ### The integers -/

/-- The integers of an extension over an intermediate field are its integers over the base
field. -/
noncomputable def divisionIntegersBaseChange (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖) :
    divisionIntegers M L →+* divisionIntegers K L :=
  RingHom.codRestrict (divisionIntegers M L).subtype (divisionIntegers K L) fun x => by
    rw [mem_divisionIntegers, ← divisionNorm_eq_of_base hnorm]
    exact mem_divisionIntegers.1 x.2

@[simp]
theorem coe_divisionIntegersBaseChange (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (x : divisionIntegers M L) :
    ((divisionIntegersBaseChange (L := L) hnorm x : divisionIntegers K L) : L) = (x : L) := rfl

/-! ### The residues -/

/-- **The residue ring of an extension over an intermediate field inside its residue ring over the
base field.** -/
noncomputable def divisionResidueBaseChange (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖) :
    DivisionResidue M L →+* DivisionResidue K L :=
  (divisionResidueCon M L).lift
    (((divisionResidueCon K L).mk').comp (divisionIntegersBaseChange hnorm))
    (by
      intro x y h
      have h' : divisionNorm M L ((x : L) - (y : L)) < 1 := h
      rw [RingCon.ker_apply]
      simp only [RingHom.comp_apply, RingCon.coe_mk']
      refine divisionResidue_eq_iff.2 ?_
      rw [coe_divisionIntegersBaseChange, coe_divisionIntegersBaseChange,
        ← divisionNorm_eq_of_base hnorm]
      exact h')

@[simp]
theorem divisionResidueBaseChange_coe (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (x : divisionIntegers M L) :
    divisionResidueBaseChange hnorm ((x : divisionIntegers M L) : DivisionResidue M L)
      = ((divisionIntegersBaseChange hnorm x : divisionIntegers K L) : DivisionResidue K L) := rfl

/-- **The two residue rings of an extension agree**, because the two absolute values agree and so
the integers and the congruence on them agree. -/
theorem divisionResidueBaseChange_bijective (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖) :
    Function.Bijective (divisionResidueBaseChange (L := L) hnorm) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := (divisionResidueCon M L).mk'_surjective a
    obtain ⟨y, rfl⟩ := (divisionResidueCon M L).mk'_surjective b
    simp only [RingCon.coe_mk', divisionResidueBaseChange_coe, divisionResidue_eq_iff,
      coe_divisionIntegersBaseChange] at hab ⊢
    rwa [divisionNorm_eq_of_base hnorm]
  · intro r
    obtain ⟨x, rfl⟩ := (divisionResidueCon K L).mk'_surjective r
    have hx : (x : L) ∈ divisionIntegers M L := by
      rw [mem_divisionIntegers, divisionNorm_eq_of_base hnorm]
      exact mem_divisionIntegers.1 x.2
    refine ⟨((⟨(x : L), hx⟩ : divisionIntegers M L) : DivisionResidue M L), ?_⟩
    rw [divisionResidueBaseChange_coe, RingCon.coe_mk']
    exact congrArg _ (Subtype.ext rfl)

/-- **An extension has as many residues over an intermediate field as over the base field.** -/
theorem natCard_divisionResidue_base (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖) :
    Nat.card (DivisionResidue M L) = Nat.card (DivisionResidue K L) :=
  Nat.card_eq_of_bijective _ (divisionResidueBaseChange_bijective hnorm)

end InverseGalois.CFT
