/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicBrauer
import InverseGalois.CFT.Brauer.TotalInvariant

/-!
# The archimedean invariants of a class split by a totally real field

Every infinite place of the rationals is real, so the completion of the rationals there is the
reals and a Brauer class of the rationals is split by that completion exactly when it is split by
the reals.  A field with a real embedding therefore splits, at every infinite place, everything it
splits globally; in particular a totally real number field does, because each of its own infinite
places supplies a real embedding.

For a cyclic algebra over the rationals whose splitting field is totally real this removes the
archimedean places from the sum of the local invariants: the total invariant is the product of the
invariants at the finite places alone.

## Main results

* `InverseGalois.CFT.relative_completion_rat_eq_relative_real`: the completion of the rationals at
  an infinite place splits the same Brauer classes as the reals.
* `InverseGalois.CFT.mem_relative_real_of_isTotallyReal`: **a Brauer class of the rationals split
  by a totally real number field is split by the reals.**
* `InverseGalois.CFT.infinitePlaceInvariant_rat_eq_one_of_isTotallyReal`: **a Brauer class of the
  rationals split by a totally real number field has trivial invariant at every infinite place.**
* `InverseGalois.CFT.totalInvariant_eq_finprod`: the total invariant is the product over the finite
  places once the archimedean invariants are known to be trivial.
* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_rat`: **the total invariant of a cyclic algebra
  over the rationals with a totally real splitting field is the product of its invariants at the
  finite places.**

## Tags

Brauer group, invariant, infinite place, totally real, cyclic algebra, reciprocity
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### The infinite places of the rationals -/

section RatInfinite

/-- **The completion of the rationals at an infinite place splits the same Brauer classes as the
reals.**  The rationals are totally real, so the place is real, and the only ring homomorphism from
the rationals to the reals is the associated real embedding. -/
theorem relative_completion_rat_eq_relative_real (u : InfinitePlace ℚ) :
    BrauerGroup.relative ℚ u.Completion = BrauerGroup.relative ℚ ℝ :=
  relative_completion_eq_relative_real ℚ (IsTotallyReal.isReal u) (Subsingleton.elim _ _)

/-- **A Brauer class of the rationals split by a field with a real embedding has trivial invariant
at every infinite place.**  A ring homomorphism into the reals is automatically a homomorphism of
algebras over the rationals, so the reals split whatever the field splits. -/
theorem infinitePlaceInvariant_rat_eq_one_of_ringHom {L : Type} [Field L] [Algebra ℚ L]
    (ψ : L →+* ℝ) (u : InfinitePlace ℚ) {x : BrauerGroup.{0, 0} ℚ}
    (hx : x ∈ BrauerGroup.relative ℚ L) : infinitePlaceInvariant ℚ u x = 1 := by
  rw [infinitePlaceInvariant_eq_one_iff, relative_completion_rat_eq_relative_real]
  exact relative_le_relative_of_algHom ψ.toRatAlgHom hx

/-- **A Brauer class of the rationals split by a totally real number field is split by the
reals.**  Any infinite place of the splitting field is real and provides an embedding of that field
into the reals. -/
theorem mem_relative_real_of_isTotallyReal {L : Type} [Field L] [NumberField L] [IsTotallyReal L]
    {x : BrauerGroup.{0, 0} ℚ} (hx : x ∈ BrauerGroup.relative ℚ L) :
    x ∈ BrauerGroup.relative ℚ ℝ := by
  obtain ⟨U⟩ : Nonempty (InfinitePlace L) := inferInstance
  exact relative_le_relative_of_algHom
    (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal U)).toRatAlgHom hx

/-- **A Brauer class of the rationals split by a totally real number field has trivial invariant at
every infinite place.**  Any infinite place of the splitting field is real and provides the real
embedding. -/
theorem infinitePlaceInvariant_rat_eq_one_of_isTotallyReal {L : Type} [Field L] [NumberField L]
    [IsTotallyReal L] (u : InfinitePlace ℚ) {x : BrauerGroup.{0, 0} ℚ}
    (hx : x ∈ BrauerGroup.relative ℚ L) : infinitePlaceInvariant ℚ u x = 1 := by
  obtain ⟨U⟩ : Nonempty (InfinitePlace L) := inferInstance
  exact infinitePlaceInvariant_rat_eq_one_of_ringHom
    (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal U)) u hx

end RatInfinite

/-! ### Removing the archimedean places from the sum of the invariants -/

section TotalInvariant

/-- **The total invariant is the product of the invariants at the finite places** once the
invariants at the infinite places are known to be trivial. -/
theorem totalInvariant_eq_finprod (k : Type) [Field k] [NumberField k] (x : BrauerGroup.{0, 0} k)
    (h : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1) :
    totalInvariant k x = ∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x := by
  rw [totalInvariant_apply, Finset.prod_congr rfl fun u _ => h u, Finset.prod_const_one, mul_one]

/-- **The total invariant of a Brauer class of the rationals split by a totally real number field
is the product of its invariants at the finite places.** -/
theorem totalInvariant_rat_eq_finprod_of_isTotallyReal {L : Type} [Field L] [NumberField L]
    [IsTotallyReal L] {x : BrauerGroup.{0, 0} ℚ} (hx : x ∈ BrauerGroup.relative ℚ L) :
    totalInvariant ℚ x = ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), placeInvariant ℚ v x :=
  totalInvariant_eq_finprod ℚ x fun u =>
    infinitePlaceInvariant_rat_eq_one_of_isTotallyReal u hx

end TotalInvariant

/-! ### Cyclic algebras with a totally real splitting field -/

section Cyclic

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] [IsTotallyReal L] {σ₀ : Gal(L/ℚ)}
  (hσ₀ : ∀ x : Gal(L/ℚ), x ∈ Subgroup.zpowers σ₀)

/-- **A cyclic algebra over the rationals with a totally real splitting field has trivial invariant
at every infinite place.** -/
theorem infinitePlaceInvariant_cyclicBrauerHom_rat (a : ℚˣ) (u : InfinitePlace ℚ) :
    infinitePlaceInvariant ℚ u (cyclicBrauerHom hσ₀ a) = 1 :=
  infinitePlaceInvariant_rat_eq_one_of_isTotallyReal u (cyclicBrauerHom_mem_relative hσ₀ a)

/-- **The total invariant of a cyclic algebra over the rationals with a totally real splitting field
is the product of its invariants at the finite places.**  This is the archimedean half of the
reciprocity computation for such an algebra. -/
theorem totalInvariant_cyclicBrauerHom_rat (a : ℚˣ) :
    totalInvariant ℚ (cyclicBrauerHom hσ₀ a)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), placeInvariant ℚ v (cyclicBrauerHom hσ₀ a) :=
  totalInvariant_eq_finprod ℚ _ (infinitePlaceInvariant_cyclicBrauerHom_rat hσ₀ a)

end Cyclic

end InverseGalois.CFT
