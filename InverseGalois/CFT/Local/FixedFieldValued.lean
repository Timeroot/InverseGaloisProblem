/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.ExpAction
import InverseGalois.CFT.Local.SubfieldValued

/-!
# The subfield fixed by a group of isometries

A group of automorphisms of a valued field preserving the valuation fixes a subfield, and that
subfield inherits every hypothesis of the local computation of the norm index: it is closed, hence
complete; the restricted valuation has the same residue characteristic and finite graded pieces;
and its value group is still nontrivial, because the norm of an element of nontrivial value is
fixed and its value is a power of the original one.

The last ingredient is what lets the dévissage of a solvable extension descend: an automorphism of
the fixed subfield over the base extends to the larger field, so it is an isometry too, and an
automorphism of the larger field over the fixed subfield is in particular one over the base.

The statements are phrased for an abstract field mapping to the larger one, with the hypothesis
that its range is the fixed subfield, rather than for the subtype itself: the subtype carries a
uniformity of its own, which is not the one the restricted valuation defines.

## Main results

* `InverseGalois.CFT.isClosed_fixedField`: **the subfield fixed by a group of isometries is
  closed.**
* `InverseGalois.CFT.completeSpace_of_range_eq_fixedField`: **the subfield fixed by a group of
  isometries of a complete valued field is complete.**
* `InverseGalois.CFT.exists_mem_fixedField_val_ne_one`: **the subfield fixed by a finite group of
  isometries contains an element of nontrivial value.**
* `InverseGalois.CFT.valued_algEquiv_of_isValuedExtension`: **an automorphism of an intermediate
  field of a normal extension is an isometry.**
* `InverseGalois.CFT.valued_algEquiv_restrictScalars`: **an automorphism over an intermediate field
  is an isometry.**

## Tags

valued field, fixed field, isometry, complete field, norm
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Valued L ℤᵐ⁰]

/-! ### The range of an intermediate field -/

omit [Valued L ℤᵐ⁰] in
/-- The range of the structure map of an intermediate field is the field itself. -/
theorem range_algebraMap_intermediateField (M : IntermediateField K L) :
    Set.range (algebraMap ↥M L) = (M : Set L) := by
  ext x
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

variable (hv : ∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x)

include hv

/-! ### Closedness and completeness -/

/-- **The subfield fixed by a group of isometries is closed.**  It is the intersection, over the
group, of the sets on which an automorphism agrees with the identity, and an isometry is
continuous. -/
theorem isClosed_fixedField (C : Subgroup (L ≃ₐ[K] L)) :
    IsClosed ((IntermediateField.fixedField C : IntermediateField K L) : Set L) := by
  haveI : T2Space L := inferInstance
  have hset : ((IntermediateField.fixedField C : IntermediateField K L) : Set L)
      = ⋂ σ : ↥C, {x : L | (σ : L ≃ₐ[K] L) x = x} := by
    ext x
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff, Set.mem_iInter]
    exact ⟨fun h σ => h σ σ.2, fun h σ hσ => h ⟨σ, hσ⟩⟩
  rw [hset]
  exact isClosed_iInter fun σ =>
    isClosed_eq (continuous_smul_of_valued hv (σ : L ≃ₐ[K] L)) continuous_id

/-- **The subfield fixed by a group of isometries of a complete valued field is complete**, being
a closed subfield. -/
theorem completeSpace_of_range_eq_fixedField {S : Type*} [Field S] [Valued S ℤᵐ⁰] [Algebra S L]
    [CompleteSpace L] (hext : IsValuedExtension S L) (C : Subgroup (L ≃ₐ[K] L))
    (hrange : Set.range (algebraMap S L) = (IntermediateField.fixedField C : Set L)) :
    CompleteSpace S :=
  hext.completeSpace (hrange ▸ isClosed_fixedField hv C)

/-! ### Nontriviality of the value group -/

/-- **The subfield fixed by a finite group of isometries contains an element of nontrivial
value.**  The norm of an element of nontrivial value is fixed, and its value is the original one
raised to the order of the group. -/
theorem exists_mem_fixedField_val_ne_one (C : Subgroup (L ≃ₐ[K] L)) [Finite ↥C]
    (hnt : ∃ x : Lˣ, Valued.v (x : L) ≠ 1) :
    ∃ y : L, y ∈ IntermediateField.fixedField C ∧ y ≠ 0 ∧ Valued.v y ≠ 1 := by
  classical
  haveI : Fintype ↥C := Fintype.ofFinite _
  haveI : Nonempty ↥C := ⟨1⟩
  obtain ⟨x, hx⟩ := hnt
  refine ⟨∏ σ : ↥C, (σ : L ≃ₐ[K] L) (x : L), ?_, ?_, ?_⟩
  · rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : ↥C)) _ _ fun _ => rfl
  · exact Finset.prod_ne_zero_iff.mpr fun σ _ => (map_ne_zero _).mpr x.ne_zero
  · have hval : Valued.v (∏ σ : ↥C, (σ : L ≃ₐ[K] L) (x : L))
        = Valued.v (x : L) ^ Fintype.card ↥C := by
      rw [map_prod]
      simp only [hv, Finset.prod_const, Finset.card_univ]
    have hx0 : Valued.v (x : L) ≠ 0 := (map_ne_zero _).mpr x.ne_zero
    have hlog : WithZero.log (Valued.v (x : L)) ≠ 0 := fun h =>
      hx (by rw [← WithZero.exp_log hx0, h, WithZero.exp_zero])
    rw [hval]
    intro hone
    have hpow := WithZero.log_pow (Valued.v (x : L)) (Fintype.card ↥C)
    rw [hone, WithZero.log_one] at hpow
    rcases smul_eq_zero.mp hpow.symm with h | h
    · exact Fintype.card_ne_zero h
    · exact hlog h

omit hv in
/-- A valued field whose valuation is restricted from a larger one has a nontrivial value group as
soon as it contains an element whose value in the larger field is nontrivial. -/
theorem exists_units_val_ne_one_of_mem {S : Type*} [Field S] [Valued S ℤᵐ⁰] [Algebra S L]
    (hext : IsValuedExtension S L) (y : S) (hy0 : y ≠ 0)
    (hy : Valued.v (algebraMap S L y) ≠ 1) : ∃ u : Sˣ, Valued.v (u : S) ≠ 1 :=
  ⟨Units.mk0 y hy0, by rwa [Units.val_mk0, ← hext.val_algebraMap]⟩

/-- **The value group of the subfield fixed by a finite group of isometries is nontrivial.** -/
theorem exists_units_val_ne_one_of_range_eq_fixedField {S : Type*} [Field S] [Valued S ℤᵐ⁰]
    [Algebra S L] (hext : IsValuedExtension S L) (C : Subgroup (L ≃ₐ[K] L)) [Finite ↥C]
    (hrange : Set.range (algebraMap S L) = (IntermediateField.fixedField C : Set L))
    (hnt : ∃ x : Lˣ, Valued.v (x : L) ≠ 1) : ∃ u : Sˣ, Valued.v (u : S) ≠ 1 := by
  obtain ⟨y, hmem, hy0, hy⟩ := exists_mem_fixedField_val_ne_one hv C hnt
  obtain ⟨z, hz⟩ : y ∈ Set.range (algebraMap S L) := by rw [hrange]; exact hmem
  refine exists_units_val_ne_one_of_mem hext z (fun h => hy0 ?_) ?_
  · rw [← hz, h, map_zero]
  · rw [hz]
    exact hy

/-! ### Transporting the isometry hypothesis -/

/-- **An automorphism of an intermediate field of a normal extension is an isometry** for the
restricted valuation: it lifts to an automorphism of the larger field, which is one by
hypothesis. -/
theorem valued_algEquiv_of_isValuedExtension {S : Type*} [Field S] [Valued S ℤᵐ⁰] [Algebra K S]
    [Algebra S L] [IsScalarTower K S L] [Normal K L] (hext : IsValuedExtension S L)
    (τ : S ≃ₐ[K] S) (y : S) : Valued.v (τ y) = Valued.v y := by
  rw [← hext.val_algebraMap, ← hext.val_algebraMap y, ← AlgEquiv.liftNormal_commutes τ L y]
  exact hv _ _

/-- **An automorphism over an intermediate field is an isometry**, being in particular an
automorphism over the base field. -/
theorem valued_algEquiv_restrictScalars {S : Type*} [Field S] [Algebra K S] [Algebra S L]
    [IsScalarTower K S L] (τ : L ≃ₐ[S] L) (x : L) : Valued.v (τ x) = Valued.v x :=
  hv (τ.restrictScalars K) x

end InverseGalois.CFT
