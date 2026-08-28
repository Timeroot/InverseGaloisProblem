/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SolvableNormBound
import InverseGalois.CFT.Local.CompleteNormIndex
import InverseGalois.CFT.Local.FixedFieldValued

/-!
# The relative Brauer group of a solvable extension of local fields

An extension is *local* here when the larger field carries a complete valuation with a residue
characteristic and finite graded pieces, whose value group is nontrivial and which every
automorphism over the smaller field preserves.  For a cyclic such extension the index of the norm
subgroup is the degree, and the class of local extensions is closed under both halves of the tower
cut out by a group of automorphisms: the fixed subfield carries the restricted valuation, is closed
and hence complete, keeps the residue characteristic and the finiteness of the graded pieces, and
still has a nontrivial value group because the norm of an element of nontrivial value is fixed.

The dévissage of a solvable extension therefore applies, and bounds the relative Brauer group of
every solvable extension of local fields by its degree.  This is the counting half of the first
inequality of local class field theory.

## Main definitions

* `InverseGalois.CFT.IsLocalExtension`: the larger field carries a complete discrete valuation
  preserved by the automorphisms over the smaller one.

## Main results

* `InverseGalois.CFT.isDevissageClosed_isLocalExtension`: **the class of local extensions is closed
  under the dévissage.**
* `InverseGalois.CFT.hasCyclicNormIndexBound_isLocalExtension`: the norm index of a cyclic local
  extension is at most the degree.
* `InverseGalois.CFT.card_relative_le_finrank_of_isLocalExtension`: **the relative Brauer group of
  a solvable extension of local fields has order at most the degree.**

## Tags

local field, Brauer group, relative Brauer group, norm index, solvable, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped WithZero

/-- **A local extension**: the larger field carries a complete valuation with a residue
characteristic, finite graded pieces and a nontrivial value group, and every automorphism over the
smaller field preserves it. -/
def IsLocalExtension (K A : Type) [Field K] [Field A] [Algebra K A] : Prop :=
  ∃ (val : Valued A ℤᵐ⁰) (p e : ℕ),
    letI : Valued A ℤᵐ⁰ := val
    CompleteSpace A ∧ HasResidueChar A p e ∧ (∀ k : ℤ, Finite (gradedAdd A k)) ∧
      (∃ x : Aˣ, Valued.v (x : A) ≠ 1) ∧
      ∀ (σ : A ≃ₐ[K] A) (x : A), Valued.v (σ x) = Valued.v x

/-- **The class of local extensions is closed under the dévissage.**  The larger field keeps its
valuation, and an automorphism of it over the fixed subfield is in particular one over the base;
the fixed subfield carries the restricted valuation, which is complete because the subfield is
closed, has the same residue characteristic and finite graded pieces, and has a nontrivial value
group because the norm of an element of nontrivial value is fixed. -/
theorem isDevissageClosed_isLocalExtension :
    BrauerGroup.IsDevissageClosed IsLocalExtension := by
  intro F E _ _ _ _ _ hFE C
  obtain ⟨val, p, e, hcomp, hres, hgr, hnt, hv⟩ := hFE
  letI := val
  haveI := hcomp
  haveI : ∀ k : ℤ, Finite (gradedAdd E k) := hgr
  refine ⟨⟨val, p, e, hcomp, hres, hgr, hnt, fun τ x => valued_algEquiv_restrictScalars hv τ x⟩, ?_⟩
  letI valM : Valued ↥(IntermediateField.fixedField C) ℤᵐ⁰ :=
    subValued ↥(IntermediateField.fixedField C) E
  have hext : IsValuedExtension ↥(IntermediateField.fixedField C) E :=
    isValuedExtension_subValued _ _
  exact ⟨valM, p, e,
    completeSpace_of_range_eq_fixedField hv hext C (range_algebraMap_intermediateField _),
    hext.hasResidueChar hres, fun k => hext.finite_gradedAdd k,
    exists_units_val_ne_one_of_range_eq_fixedField hv hext C
      (range_algebraMap_intermediateField _) hnt,
    fun τ y => valued_algEquiv_of_isValuedExtension hv hext τ y⟩

/-- The norm subgroup of a cyclic local extension has index the degree, in particular finite index
at most the degree. -/
theorem hasCyclicNormIndexBound_isLocalExtension :
    HasCyclicNormIndexBound IsLocalExtension := by
  intro F E _ _ _ _ _ hFE hcyc
  obtain ⟨val, p, e, hcomp, hres, hgr, hnt, hv⟩ := hFE
  letI := val
  haveI := hcomp
  have hpos : 0 < finrank F E := by
    rw [← IsGalois.card_aut_eq_finrank F E]
    exact Nat.card_pos
  have h : (normSubgroup F E).index = finrank F E :=
    index_normSubgroup_eq_finrank_of_complete hv hres hgr hnt hcyc
  exact ⟨by rw [h]; omega, by rw [h]⟩

/-- **The relative Brauer group of a solvable extension of local fields has order at most the
degree.**  This is the counting half of the first inequality of local class field theory. -/
theorem card_relative_le_finrank_of_isLocalExtension (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hL : IsLocalExtension K L)
    (hsolv : IsSolvable (L ≃ₐ[K] L)) :
    Finite ↥(BrauerGroup.relative K L) ∧
      Nat.card ↥(BrauerGroup.relative K L) ≤ finrank K L :=
  card_relative_le_finrank_of_isSolvable_of_normIndex isDevissageClosed_isLocalExtension
    hasCyclicNormIndexBound_isLocalExtension K L hL hsolv

end InverseGalois.CFT
