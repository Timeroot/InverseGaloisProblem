/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceInvariant
import InverseGalois.CFT.Brauer.RealBrauer

/-!
# The invariant of a Brauer class at an infinite place

The completion of a number field at an infinite place is the reals or the complex numbers.  At a
complex place the completion is algebraically closed, so it splits every Brauer class of the base
and the invariant there is trivial.  At a real place the completion is isomorphic to the reals over
the base, so the relative Brauer group of the completion is the relative Brauer group of the reals
along the associated real embedding, and the invariant is the one already attached to that
embedding.

This makes the archimedean member of the family of local invariants available for every infinite
place, with no case distinction left to the caller: the invariant vanishes exactly when the
completion at that place splits the class, which is the form in which the
Albert-Brauer-Hasse-Noether theorem consumes it.

## Main definitions

* `InverseGalois.CFT.infinitePlaceInvariant`: **the invariant of a Brauer class of a number field
  at an infinite place.**

## Main results

* `InverseGalois.CFT.relative_completion_eq_top_of_isComplex`: the completion at a complex place
  splits every Brauer class.
* `InverseGalois.CFT.relative_completion_eq_relative_real`: at a real place the completion splits
  the same classes as the reals along the associated embedding.
* `InverseGalois.CFT.infinitePlaceInvariant_eq_one_iff`: **a Brauer class of a number field has
  trivial invariant at an infinite place exactly when the completion at that place splits it.**

## Tags

Brauer group, number field, infinite place, archimedean, local invariant, class field theory
-/

namespace InverseGalois.CFT

open NumberField

section InfiniteInvariant

variable (k : Type) [Field k] [NumberField k]

/-! ### The completion at a complex place -/

omit [NumberField k] in
/-- **The completion at a complex place splits every Brauer class of the base.**  It is isomorphic
over the base to the complex numbers, which are algebraically closed. -/
theorem relative_completion_eq_top_of_isComplex {u : InfinitePlace k} (hu : u.IsComplex) :
    BrauerGroup.relative k u.Completion = ⊤ := by
  letI : Algebra k ℂ := u.embedding.toAlgebra
  have hmap : ∀ r : k,
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu
          (algebraMap k u.Completion r) = algebraMap k ℂ r := fun r =>
    NumberField.InfinitePlace.Completion.extensionEmbedding_coe u r
  let e : u.Completion ≃ₐ[k] ℂ := AlgEquiv.ofRingEquiv hmap
  have htop : BrauerGroup.relative k ℂ = ⊤ := BrauerGroup.relative_eq_top_of_isAlgClosed ℂ
  exact eq_top_iff.mpr (htop ▸ relative_le_relative_of_algHom e.symm.toAlgHom)

/-! ### The completion at a real place -/

omit [NumberField k] in
/-- **At a real place the completion splits the same Brauer classes as the reals** along the
associated real embedding, because it is isomorphic to the reals over the base. -/
theorem relative_completion_eq_relative_real {u : InfinitePlace k} (hu : u.IsReal) [Algebra k ℝ]
    (halg : (algebraMap k ℝ) = (InfinitePlace.embedding_of_isReal hu : k →+* ℝ)) :
    BrauerGroup.relative k u.Completion = BrauerGroup.relative k ℝ := by
  have hmap : ∀ r : k,
      NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hu
          (algebraMap k u.Completion r) = algebraMap k ℝ r := by
    intro r
    rw [halg]
    exact NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hu r
  let e : u.Completion ≃ₐ[k] ℝ := AlgEquiv.ofRingEquiv hmap
  exact le_antisymm (relative_le_relative_of_algHom e.toAlgHom)
    (relative_le_relative_of_algHom e.symm.toAlgHom)

/-! ### The invariant at an infinite place -/

open Classical in
/-- **The invariant of a Brauer class of a number field at an infinite place.**  At a real place it
is the invariant at the associated real embedding, and at a complex place it is trivial. -/
noncomputable def infinitePlaceInvariant (u : InfinitePlace k) :
    BrauerGroup.{0, 0} k →* Multiplicative QModZ :=
  if hu : u.IsReal then realPlaceInvariant k hu else 1

omit [NumberField k] in
/-- At a real place the invariant is the invariant at the associated real embedding. -/
theorem infinitePlaceInvariant_of_isReal {u : InfinitePlace k} (hu : u.IsReal) :
    infinitePlaceInvariant k u = realPlaceInvariant k hu := by
  simp only [infinitePlaceInvariant, dif_pos hu]

omit [NumberField k] in
/-- At a complex place the invariant is trivial. -/
theorem infinitePlaceInvariant_of_isComplex {u : InfinitePlace k} (hu : u.IsComplex) :
    infinitePlaceInvariant k u = 1 := by
  simp only [infinitePlaceInvariant,
    dif_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hu)]

omit [NumberField k] in
/-- **A Brauer class of a number field has trivial invariant at an infinite place exactly when the
completion at that place splits it.** -/
theorem infinitePlaceInvariant_eq_one_iff (u : InfinitePlace k) (x : BrauerGroup.{0, 0} k) :
    infinitePlaceInvariant k u x = 1 ↔ x ∈ BrauerGroup.relative k u.Completion := by
  rcases u.isReal_or_isComplex with hu | hu
  · rw [infinitePlaceInvariant_of_isReal k hu]
    letI : Algebra k ℝ := (InfinitePlace.embedding_of_isReal hu).toAlgebra
    have hstep : realPlaceInvariant k hu x = realEmbeddingInvariant k x := rfl
    rw [hstep, realEmbeddingInvariant_eq_one_iff,
      relative_completion_eq_relative_real k hu rfl]
  · rw [infinitePlaceInvariant_of_isComplex k hu, relative_completion_eq_top_of_isComplex k hu]
    exact ⟨fun _ => Subgroup.mem_top x, fun _ => rfl⟩

end InfiniteInvariant

end InverseGalois.CFT
