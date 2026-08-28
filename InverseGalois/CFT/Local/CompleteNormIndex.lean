/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitHerbrandChain
import InverseGalois.CFT.Tate.CyclicHilbert90
import InverseGalois.CFT.Tate.GaloisH0

/-!
# The norm index of a cyclic extension with complete discretely valued top field

The Herbrand quotient of the group of units of a complete discretely valued field, under a finite
cyclic group of automorphisms preserving the valuation, is the order of the group.  Hilbert's
theorem 90 makes the denominator of that quotient one, so the numerator — the units of the base
field modulo the norms — has order the degree.  This is the first inequality of local class field
theory, in the form in which the dévissage of a solvable extension consumes it.

Nothing is assumed of the base field beyond the extension being Galois: all the hypotheses are on
the larger field, which is what makes the statement survive the dévissage.

## Main results

* `InverseGalois.CFT.index_normSubgroup_eq_finrank_of_complete`: **the index of the norm subgroup of
  a cyclic extension whose larger field is complete and discretely valued is the degree.**

## Tags

local field, norm index, Hilbert theorem 90, Herbrand quotient, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped WithZero

variable {K A : Type} [Field K] [Field A] [Algebra K A] [FiniteDimensional K A] [IsGalois K A]

omit [FiniteDimensional K A] [IsGalois K A] in
/-- The action of the Galois group on the units is the transport of the action on the field. -/
theorem smulUnitsAut_eq_addAut_unitsAut (σ : A ≃ₐ[K] A) :
    smulUnitsAut (G := A ≃ₐ[K] A) (R := A) σ = addAut (unitsAut σ) := rfl

variable [Valued A ℤᵐ⁰] [CompleteSpace A]

/-- **The index of the norm subgroup of a cyclic extension whose larger field is complete and
discretely valued is the degree.**  The Herbrand quotient of the unit group is the order of the
Galois group, and its denominator is one by Hilbert's theorem 90, so its numerator — the units of
the base field modulo the norms — has order the degree. -/
theorem index_normSubgroup_eq_finrank_of_complete {p e : ℕ}
    (hv : ∀ (σ : A ≃ₐ[K] A) (x : A), Valued.v (σ x) = Valued.v x)
    (hres : HasResidueChar A p e) (hgr : ∀ k : ℤ, Finite (gradedAdd A k))
    (hnt : ∃ x : Aˣ, Valued.v (x : A) ≠ 1) (hcyc : IsCyclic (A ≃ₐ[K] A)) :
    (normSubgroup K A).index = finrank K A := by
  haveI := hcyc
  haveI : ∀ k : ℤ, Finite (gradedAdd A k) := hgr
  haveI : Fintype (A ≃ₐ[K] A) := Fintype.ofFinite _
  obtain ⟨m, hm⟩ := exists_isUnitValGen hnt
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := A ≃ₐ[K] A)
  have hcard : Nat.card (A ≃ₐ[K] A) = finrank K A := IsGalois.card_aut_eq_finrank K A
  haveI : NeZero (finrank K A) := ⟨by rw [← hcard]; exact Nat.card_pos.ne'⟩
  have hσ : σ ^ finrank K A = 1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  have hvsmul : ∀ (τ : A ≃ₐ[K] A) (x : A), Valued.v (τ • x) = Valued.v x := hv
  have hloc := herbrand_smulUnitsAut_eq_card hvsmul hm hres hgen hσ hcard
  have hglob := herbrand_units σ hgen
  rw [smulUnitsAut_eq_addAut_unitsAut] at hloc
  rw [hcard, hloc] at hglob
  exact_mod_cast hglob.symm

end InverseGalois.CFT
