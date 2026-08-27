/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.NilpotentRadical
import InverseGalois.CFT.Scholz.RadicalSplitting
import InverseGalois.CFT.SplitSup

/-!
# Auxiliary primes with a prescribed non-residue

A rational number which is not an `ℓ`-th power stays a non-power in a Galois extension of the
rationals with nilpotent Galois group containing the `ℓ`-th roots of unity, so adjoining one of its
`ℓ`-th roots to such an extension strictly enlarges it.  The only consequence of Chebotarev's
theorem the Scholz–Reichardt construction uses then produces infinitely many rational primes which
split completely in the nilpotent extension but not in the enlargement, and a prime splitting
completely in each of two fields splits completely in their compositum, so those primes fail to
split completely in the radical field alone.

Reading that failure through the power residue criterion for a radical field turns it into an
arithmetic statement: the radicand is not an `ℓ`-th power residue modulo such a prime.  This is
exactly the input the correction of the residue degrees needs, the radicand being a product of
powers of the primes ramified in the field being corrected.

The step through nilpotency is only available for an odd exponent, and the underlying Chebotarev
argument needs nothing beyond the absence of an `ℓ`-th root in the extension itself, so both
statements come in a version taking that absence as the hypothesis.

## Main results

* `InverseGalois.CFT.exists_prime_splitsCompletely_not_radicalField_of_forall_pow_ne`:
  **an element of the rationals having no `ℓ`-th root in a Galois extension admits infinitely many
  primes splitting completely in that extension but not in the radical field of the element.**
* `InverseGalois.CFT.exists_prime_splitsCompletely_not_splitsCompletely_radicalField`: **a rational
  number which is not an `ℓ`-th power admits infinitely many primes splitting completely in a
  nilpotent extension containing the `ℓ`-th roots of unity but not in the radical field of that
  number.**
* `InverseGalois.CFT.exists_prime_splitsCompletely_pow_ne_one_of_forall_pow_ne` and
  `InverseGalois.CFT.exists_prime_splitsCompletely_pow_ne_one`: the same conclusions read as power
  residue statements modulo the prime.

## Tags

Chebotarev density, radical extension, nilpotent group, power residue, Scholz–Reichardt
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {ℓ : ℕ}

/-- **An element of the rationals having no `ℓ`-th root in a Galois extension admits infinitely
many primes splitting completely in that extension but not in the radical field of the element.**
The compositum of the extension with the radical field is strictly larger; infinitely many primes
split completely in the smaller field and not in the larger, and such a prime cannot split
completely in the radical field, for otherwise it would split completely in the compositum. -/
theorem exists_prime_splitsCompletely_not_radicalField_of_forall_pow_ne
    [Fact ℓ.Prime] {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A] [IsGalois ℚ ↥A]
    {m : ℚ} (hm : ∀ u ∈ A, u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) m) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ SplitsCompletely ↥A q ∧
      ¬ SplitsCompletely ↥(radicalField ℓ ({m} : Finset ℚ)) q := by
  have hℓ : ℓ.Prime := Fact.out
  set R : IntermediateField ℚ (AlgebraicClosure ℚ) := radicalField ℓ ({m} : Finset ℚ) with hRdef
  -- the compositum of the two fields is strictly larger than the given extension
  have hlt : finrank ℚ ↥A < finrank ℚ ↥(A ⊔ R) := by
    rcases lt_or_ge (finrank ℚ ↥A) (finrank ℚ ↥(A ⊔ R)) with h | h
    · exact h
    have heq : A = A ⊔ R := IntermediateField.eq_of_le_of_finrank_le le_sup_left h
    obtain ⟨α, hα⟩ := exists_pow_eq_radicalField (S := ({m} : Finset ℚ)) hℓ.ne_zero
      (Finset.mem_singleton_self m)
    have hmemR : (algebraMap ↥R (AlgebraicClosure ℚ) α) ∈ A := by
      rw [heq]
      exact (le_sup_right : R ≤ A ⊔ R) α.2
    refine absurd ?_ (hm _ hmemR)
    rw [← map_pow, hα]
    exact (IsScalarTower.algebraMap_apply ℚ ↥R (AlgebraicClosure ℚ) m).symm
  -- Chebotarev supplies the primes
  have hinf := infinite_setOf_splitsCompletely_not_splitsCompletely ↥A ↥(A ⊔ R) hlt
  obtain ⟨q, ⟨⟨hqp, hqA, hqB⟩, hqT⟩⟩ := (hinf.diff T.finite_toSet).nonempty
  refine ⟨q, hqp, fun h => hqT (Finset.mem_coe.mpr h), hqA, fun h => hqB ?_⟩
  exact splitsCompletely_sup A R hqp hqA h

/-- **A rational number which is not an `ℓ`-th power admits infinitely many primes splitting
completely in a nilpotent extension containing the `ℓ`-th roots of unity but not in the radical
field of that number.**  For an odd prime no `ℓ`-th root of the number lies in the nilpotent
extension. -/
theorem exists_prime_splitsCompletely_not_splitsCompletely_radicalField [Fact ℓ.Prime]
    (hodd : Odd ℓ) {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A]
    [IsGalois ℚ ↥A] (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hζA : ζ ∈ A) {m : ℚ} (hm : ∀ y : ℚ, y ^ ℓ ≠ m) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ SplitsCompletely ↥A q ∧
      ¬ SplitsCompletely ↥(radicalField ℓ ({m} : Finset ℚ)) q :=
  exists_prime_splitsCompletely_not_radicalField_of_forall_pow_ne
    (fun _ hu => pow_ne_of_isNilpotent hodd hnil hζ hζA hm hu) T

/-- **The power residue form of the choice of auxiliary prime.**  A prime splitting completely in
the given extension but not in the radical field of an integer fails the power residue criterion
for that integer, since a prime congruent to one modulo `ℓ` modulo which the integer is an `ℓ`-th
power splits completely there. -/
theorem exists_prime_splitsCompletely_pow_ne_one_of_forall_pow_ne [Fact ℓ.Prime]
    {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A] [IsGalois ℚ ↥A]
    {v : ℤ} (hv : ∀ u ∈ A, u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) (v : ℚ)) (T : Finset ℕ)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ q ≠ ℓ ∧ SplitsCompletely ↥A q ∧
      (v : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 := by
  have hℓ : ℓ.Prime := Fact.out
  classical
  obtain ⟨q, hqp, hqT, hqA, hqR⟩ :=
    exists_prime_splitsCompletely_not_radicalField_of_forall_pow_ne hv
      (insert ℓ (T ∪ v.natAbs.primeFactors))
  have hqne : q ≠ ℓ := by
    rintro rfl
    exact hqT (Finset.mem_insert_self _ _)
  have hqv : ¬ (q : ℤ) ∣ v := by
    intro h
    refine hqT (Finset.mem_insert_of_mem (Finset.mem_union_right T ?_))
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv 0 (zero_mem A) (by simp [zero_pow hℓ.ne_zero])
    exact Nat.mem_primeFactors.mpr ⟨hqp, by simpa using Int.natAbs_dvd_natAbs.mpr h,
      Int.natAbs_ne_zero.mpr hv0⟩
  refine ⟨q, hqp, fun h => hqT (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)), hqne, hqA,
    fun h => hqR ?_⟩
  exact splitsCompletely_radicalField hℓ hqp (hdvd q hqp hqne hqA) hqv h

/-- **The power residue form of the choice of auxiliary prime for an odd prime exponent.**  An
integer which is not an `ℓ`-th power in the rationals is not one in a nilpotent extension
containing the `ℓ`-th roots of unity. -/
theorem exists_prime_splitsCompletely_pow_ne_one [Fact ℓ.Prime] (hodd : Odd ℓ)
    {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A] [IsGalois ℚ ↥A]
    (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ ℓ)
    (hζA : ζ ∈ A) {v : ℤ} (hv : ∀ y : ℚ, y ^ ℓ ≠ (v : ℚ)) (T : Finset ℕ)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ q ≠ ℓ ∧ SplitsCompletely ↥A q ∧
      (v : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 :=
  exists_prime_splitsCompletely_pow_ne_one_of_forall_pow_ne
    (fun _ hu => pow_ne_of_isNilpotent hodd hnil hζ hζA hv hu) T hdvd

end InverseGalois.CFT
