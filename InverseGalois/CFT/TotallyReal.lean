/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Totally real number fields, and what they buy at the archimedean places

An archimedean place ramifies in an extension exactly when a complex place lies over a real one, so
an extension whose top field is totally real is unramified at every archimedean place.  Over the
rationals the converse holds as well, the only place of `ℚ` being real, and the two conditions are
the same.  This is the hypothesis that replaces oddness in the local–global step at the prime two:
the decomposition group of an unramified archimedean place is trivial, so the archimedean places
impose nothing whatever the order of the kernel.

The condition is free in odd degree, an odd-degree Galois extension of the rationals having no
element of order two to act as complex conjugation, and it is stable under compositum, which is
what lets an induction carry it.

## Main results

* `InverseGalois.CFT.IsUnramifiedAtInfinitePlaces.of_isTotallyReal`: an extension whose top field
  is totally real is unramified at the archimedean places.
* `InverseGalois.CFT.isTotallyReal_of_isUnramifiedAtInfinitePlaces`: over the rationals the
  converse, so that the two conditions agree.
* `InverseGalois.CFT.isTotallyReal_of_odd_finrank`: **a Galois extension of the rationals of odd
  degree is totally real.**
* `InverseGalois.CFT.isTotallyReal_sup`: **a compositum of totally real intermediate fields is
  totally real**, together with the version for an arbitrary supremum.

## Tags

number field, totally real, infinite place, ramification, archimedean place
-/

open NumberField

namespace InverseGalois.CFT

/-! ### Total reality and unramifiedness at the archimedean places -/

section Unramified

variable (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]

/-- **An extension whose top field is totally real is unramified at the archimedean places**, a
ramified archimedean place being a complex place lying over a real one. -/
theorem IsUnramifiedAtInfinitePlaces.of_isTotallyReal [IsTotallyReal K] :
    IsUnramifiedAtInfinitePlaces k K where
  isUnramified w := (IsTotallyReal.isReal w).isUnramified (k := k)

/-- **Over the rationals, unramifiedness at the archimedean places is total reality.**  The only
place of `ℚ` is real, so an unramified place above it cannot be complex. -/
theorem isTotallyReal_of_isUnramifiedAtInfinitePlaces (K : Type*) [Field K] [NumberField K]
    [IsUnramifiedAtInfinitePlaces ℚ K] : IsTotallyReal K where
  isReal w := by
    refine (InfinitePlace.isUnramified_iff.mp (w.isUnramified ℚ)).resolve_right ?_
    exact InfinitePlace.not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal _)

/-- **Over the rationals the two conditions agree.** -/
theorem isTotallyReal_iff_isUnramifiedAtInfinitePlaces (K : Type*) [Field K] [NumberField K] :
    IsTotallyReal K ↔ IsUnramifiedAtInfinitePlaces ℚ K :=
  ⟨fun _ => IsUnramifiedAtInfinitePlaces.of_isTotallyReal ℚ K,
    fun _ => isTotallyReal_of_isUnramifiedAtInfinitePlaces K⟩

/-- **A Galois extension of the rationals of odd degree is totally real**, there being no element
of order two in its Galois group to act as complex conjugation. -/
theorem isTotallyReal_of_odd_finrank (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (h : Odd (Module.finrank ℚ K)) : IsTotallyReal K :=
  haveI := IsUnramifiedAtInfinitePlaces_of_odd_finrank (k := ℚ) (K := K) h
  isTotallyReal_of_isUnramifiedAtInfinitePlaces K

end Unramified

/-! ### Stability under compositum -/

section Compositum

variable {L : Type*} [Field L]

/-- An intermediate field and the subfield underlying it are the same field. -/
def toSubfieldRingEquiv {F : Type*} [Field F] [Algebra F L] (E : IntermediateField F L) :
    ↥E ≃+* ↥E.toSubfield where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable [CharZero L] [Algebra.IsAlgebraic ℚ L]

/-- **A compositum of two totally real intermediate fields is totally real.**  An embedding of the
compositum into the complex numbers is fixed by conjugation on each of the two fields, hence on a
set of generators. -/
theorem isTotallyReal_sup {E F : IntermediateField ℚ L} [IsTotallyReal ↥E] [IsTotallyReal ↥F] :
    IsTotallyReal ↥(E ⊔ F) := by
  haveI : IsTotallyReal ↥E.toSubfield := IsTotallyReal.ofRingEquiv (toSubfieldRingEquiv E)
  haveI : IsTotallyReal ↥F.toSubfield := IsTotallyReal.ofRingEquiv (toSubfieldRingEquiv F)
  have h : IsTotallyReal ↥(E.toSubfield ⊔ F.toSubfield) := NumberField.isTotallyReal_sup
  rw [← IntermediateField.sup_toSubfield] at h
  exact IsTotallyReal.ofRingEquiv (toSubfieldRingEquiv (E ⊔ F)).symm

/-- **A supremum of totally real intermediate fields is totally real.** -/
theorem isTotallyReal_iSup {ι : Type*} [Nonempty ι] {E : ι → IntermediateField ℚ L}
    [∀ i, IsTotallyReal ↥(E i)] : IsTotallyReal ↥(⨆ i, E i) := by
  haveI : ∀ i, IsTotallyReal ↥(E i).toSubfield := fun i =>
    IsTotallyReal.ofRingEquiv (toSubfieldRingEquiv (E i))
  have h : IsTotallyReal ↥(⨆ i, (E i).toSubfield) := NumberField.isTotallyReal_iSup
  rw [← IntermediateField.iSup_toSubfield] at h
  exact IsTotallyReal.ofRingEquiv (toSubfieldRingEquiv (⨆ i, E i)).symm

end Compositum

end InverseGalois.CFT
