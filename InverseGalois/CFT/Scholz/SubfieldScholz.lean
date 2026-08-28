/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.CompositumTransport
import InverseGalois.CFT.UnramifiedCompositum

/-!
# Serre's condition on a subfield

Both halves of Serre's condition only constrain the primes that ramify, so both are inherited by a
subfield.  What is more, the residue-degree half says something at the primes a subfield does *not*
ramify at: the residue degree in the subfield divides the residue degree above, so a prime ramified
in the larger field has residue degree one in the subfield as well, and if it is unramified there
then it splits completely.

That is the observation the shrinking process of the dyadic Scholz–Reichardt induction runs on.  A
prime ramified in the large realization but not in the piece cut out of it splits completely in that
piece, and the residue correction absorbs fresh ramification of exactly that kind.

## Main results

* `InverseGalois.CFT.inertiaDeg_eq_one_of_isSplitInertia_of_tower`: **a prime ramified in a field
  with split inertia has residue degree one in every subfield.**
* `InverseGalois.CFT.splitsCompletely_of_isSplitInertia_of_tower`: **a prime ramified in a field
  with split inertia splits completely in every subfield it does not ramify in.**
* `InverseGalois.CFT.ramifiedSet_sup_intermediateField`: **the ramified primes of a compositum of
  two number fields inside a common extension of the rationals are the ramified primes of the two
  factors together.**
* `InverseGalois.CFT.ramifiedSet_of_le`: ramification propagates upward along an inclusion of
  intermediate fields.
* `InverseGalois.CFT.IsScholz.of_le`: Serre's condition is inherited by a smaller intermediate
  field.

## Tags

Scholz–Reichardt, residue degree, split inertia, subfield, splitting completely
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Residue degree one below a prime ramified above -/

/-- **A prime ramified in a field with split inertia has residue degree one in every subfield.**
The residue degree above it factors through the intermediate field, and the factor at the top is
one. -/
theorem inertiaDeg_eq_one_of_isSplitInertia_of_tower {E M : Type*} [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra E M] (h : IsSplitInertia M) {p : ℕ}
    (hp : p ∈ ramifiedSet M) (P : Ideal (𝓞 E)) (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(p : ℤ)})) :
    (Ideal.span {(p : ℤ)}).inertiaDeg P = 1 := by
  haveI := hPprime
  haveI := hPover
  have hprime : p.Prime := hp.1
  haveI := isMaximal_span_prime hprime
  have hspan : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hprime.ne_zero
  have hP0 : P ≠ ⊥ := by
    intro hb
    refine hspan ?_
    rw [hPover.over, hb, Ideal.under,
      Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hPprime
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) P
  haveI := hQmax
  haveI := hQover
  haveI : Q.IsPrime := hQmax.isPrime
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (Ideal.span {(p : ℤ)})
  have hone := h p hp Q inferInstance inferInstance
  rw [Ideal.inertiaDeg_algebra_tower (R := ℤ) (S := 𝓞 E) (T := 𝓞 M)
    (Ideal.span {(p : ℤ)}) P Q] at hone
  exact Nat.eq_one_of_mul_eq_one_right hone

/-- **A prime ramified in a field with split inertia splits completely in every subfield it does not
ramify in.**  Its residue degree in the subfield is one because the residue degree above is, and its
ramification index there is one because the prime is unramified in the subfield. -/
theorem splitsCompletely_of_isSplitInertia_of_tower {E M : Type*} [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra E M] (h : IsSplitInertia M) {p : ℕ}
    (hp : p ∈ ramifiedSet M) (hE : p ∉ ramifiedSet E) : SplitsCompletely E p := by
  refine fun P hP => ⟨?_, inertiaDeg_eq_one_of_isSplitInertia_of_tower h hp P hP.1 hP.2⟩
  by_contra he
  exact hE ⟨hp.1, P, hP, he⟩

/-! ### The ramified primes of a compositum of subfields -/

/-- **The ramified primes of a compositum of two number fields inside a common extension of the
rationals are the ramified primes of the two factors together.** -/
theorem ramifiedSet_sup_intermediateField {L : Type*} [Field L] [CharZero L]
    (A B : IntermediateField ℚ L) [NumberField ↥A] [NumberField ↥B] :
    ramifiedSet ↥(A ⊔ B) = ramifiedSet ↥A ∪ ramifiedSet ↥B := by
  haveI : NumberField ↥(A ⊔ B) := ⟨⟩
  have htop : IntermediateField.restrict (le_sup_left : A ≤ A ⊔ B) ⊔
      IntermediateField.restrict (le_sup_right : B ≤ A ⊔ B) =
      (⊤ : IntermediateField ℚ ↥(A ⊔ B)) := restrict_sup_restrict A B
  have h1 : ramifiedSet ↥(⊤ : IntermediateField ℚ ↥(A ⊔ B)) =
      ramifiedSet ↥A ∪ ramifiedSet ↥B := by
    rw [← htop, ramifiedSet_sup, ramifiedSet_restrict, ramifiedSet_restrict]
  rw [← h1]
  exact (ramifiedSet_eq_of_ringEquiv
    (IntermediateField.topEquiv (F := ℚ) (E := ↥(A ⊔ B))).toRingEquiv).symm

/-! ### Along an inclusion of intermediate fields -/

variable {L : Type*} [Field L] [CharZero L] {A B : IntermediateField ℚ L} (h : A ≤ B)
  [NumberField ↥A] [NumberField ↥B]

include h in
/-- **Ramification propagates upward along an inclusion of intermediate fields.** -/
theorem ramifiedSet_of_le : ramifiedSet ↥A ⊆ ramifiedSet ↥B := by
  rw [← ramifiedSet_restrict h]
  exact ramifiedSet_subset ↥(IntermediateField.restrict h) ↥B

include h in
/-- **Serre's condition is inherited by a smaller intermediate field.** -/
theorem IsScholz.of_le {ℓ N : ℕ} (hB : IsScholz ℓ N ↥B) : IsScholz ℓ N ↥A :=
  IsScholz.of_ringEquiv (IntermediateField.restrict_algEquiv h).symm.toRingEquiv
    (IsScholz.of_tower (E := ↥(IntermediateField.restrict h)) hB)

include h in
/-- **A prime ramified in an intermediate field with split inertia splits completely in every
smaller intermediate field it does not ramify in.** -/
theorem splitsCompletely_of_notMem_ramifiedSet_of_le (hB : IsSplitInertia ↥B) {p : ℕ}
    (hp : p ∈ ramifiedSet ↥B) (hA : p ∉ ramifiedSet ↥A) : SplitsCompletely ↥A p := by
  refine splitsCompletely_of_ringEquiv (IntermediateField.restrict_algEquiv h).toRingEquiv hp.1
    (splitsCompletely_of_isSplitInertia_of_tower hB hp ?_)
  rwa [ramifiedSet_restrict h]

end InverseGalois.CFT
