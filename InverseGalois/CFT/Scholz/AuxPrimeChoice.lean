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

## Main results

* `InverseGalois.CFT.exists_prime_splitsCompletely_not_splitsCompletely_radicalField`: **a rational
  number which is not an `ℓ`-th power admits infinitely many primes splitting completely in a
  nilpotent extension containing the `ℓ`-th roots of unity but not in the radical field of that
  number.**
* `InverseGalois.CFT.exists_prime_splitsCompletely_pow_ne_one`: the same conclusion read as a power
  residue statement modulo the prime.

## Tags

Chebotarev density, radical extension, nilpotent group, power residue, Scholz–Reichardt
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {ℓ : ℕ}

/-- **A rational number which is not an `ℓ`-th power admits infinitely many primes splitting
completely in a nilpotent extension containing the `ℓ`-th roots of unity but not in the radical
field of that number.**  No `ℓ`-th root of the number lies in the nilpotent extension, so the
compositum of that extension with the radical field is strictly larger; infinitely many primes
split completely in the smaller field and not in the larger, and such a prime cannot split
completely in the radical field, for otherwise it would split completely in the compositum. -/
theorem exists_prime_splitsCompletely_not_splitsCompletely_radicalField [Fact ℓ.Prime]
    (hodd : Odd ℓ) {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A]
    [IsGalois ℚ ↥A] (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hζA : ζ ∈ A) {m : ℚ} (hm : ∀ y : ℚ, y ^ ℓ ≠ m) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ SplitsCompletely ↥A q ∧
      ¬ SplitsCompletely ↥(radicalField ℓ ({m} : Finset ℚ)) q := by
  have hℓ : ℓ.Prime := Fact.out
  set R : IntermediateField ℚ (AlgebraicClosure ℚ) := radicalField ℓ ({m} : Finset ℚ) with hRdef
  -- the compositum of the two fields is strictly larger than the nilpotent extension
  have hlt : finrank ℚ ↥A < finrank ℚ ↥(A ⊔ R) := by
    rcases lt_or_ge (finrank ℚ ↥A) (finrank ℚ ↥(A ⊔ R)) with h | h
    · exact h
    have heq : A = A ⊔ R := IntermediateField.eq_of_le_of_finrank_le le_sup_left h
    obtain ⟨α, hα⟩ := exists_pow_eq_radicalField (S := ({m} : Finset ℚ)) hℓ.ne_zero
      (Finset.mem_singleton_self m)
    have hmemR : (algebraMap ↥R (AlgebraicClosure ℚ) α) ∈ A := by
      rw [heq]
      exact (le_sup_right : R ≤ A ⊔ R) α.2
    refine absurd ?_ (pow_ne_of_isNilpotent hodd hnil hζ hζA hm hmemR)
    rw [← map_pow, hα]
    exact (IsScalarTower.algebraMap_apply ℚ ↥R (AlgebraicClosure ℚ) m).symm
  -- Chebotarev supplies the primes
  have hinf := infinite_setOf_splitsCompletely_not_splitsCompletely ↥A ↥(A ⊔ R) hlt
  obtain ⟨q, ⟨⟨hqp, hqA, hqB⟩, hqT⟩⟩ := (hinf.diff T.finite_toSet).nonempty
  refine ⟨q, hqp, fun h => hqT (Finset.mem_coe.mpr h), hqA, fun h => hqB ?_⟩
  exact splitsCompletely_sup A R hqp hqA h

/-- **The power residue form of the choice of auxiliary prime.**  A prime splitting completely in
the nilpotent extension but not in the radical field of an integer fails the power residue
criterion for that integer, since a prime congruent to one modulo `ℓ` modulo which the integer is
an `ℓ`-th power splits completely there. -/
theorem exists_prime_splitsCompletely_pow_ne_one [Fact ℓ.Prime] (hodd : Odd ℓ)
    {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A] [IsGalois ℚ ↥A]
    (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ ℓ)
    (hζA : ζ ∈ A) {v : ℤ} (hv : ∀ y : ℚ, y ^ ℓ ≠ (v : ℚ)) (T : Finset ℕ)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ q ≠ ℓ ∧ SplitsCompletely ↥A q ∧
      (v : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 := by
  have hℓ : ℓ.Prime := Fact.out
  classical
  obtain ⟨q, hqp, hqT, hqA, hqR⟩ :=
    exists_prime_splitsCompletely_not_splitsCompletely_radicalField hodd hnil hζ hζA hv
      (insert ℓ (T ∪ v.natAbs.primeFactors))
  have hqne : q ≠ ℓ := by
    rintro rfl
    exact hqT (Finset.mem_insert_self _ _)
  have hqv : ¬ (q : ℤ) ∣ v := by
    intro h
    refine hqT (Finset.mem_insert_of_mem (Finset.mem_union_right T ?_))
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv 0 (by simp [zero_pow hℓ.ne_zero])
    exact Nat.mem_primeFactors.mpr ⟨hqp, by simpa using Int.natAbs_dvd_natAbs.mpr h,
      Int.natAbs_ne_zero.mpr hv0⟩
  refine ⟨q, hqp, fun h => hqT (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)), hqne, hqA,
    fun h => hqR ?_⟩
  exact splitsCompletely_radicalField hℓ hqp (hdvd q hqp hqne hqA) hqv h

end InverseGalois.CFT
