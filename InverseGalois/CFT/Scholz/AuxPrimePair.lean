/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.AuxPrimeChoice
import InverseGalois.CFT.Scholz.RadicalDegree
import InverseGalois.NumberTheory.SplitDensityPair

/-!
# Auxiliary primes with two prescribed non-residues

Two rational numbers with no `ℓ`-th root in a Galois extension of the rationals containing the
`ℓ`-th roots of unity give two enlargements of that extension, each of degree exactly `ℓ` over it.
For `ℓ` at least three the two reciprocal degrees do not add up to the reciprocal degree of the
extension itself, so the density bound leaves infinitely many primes splitting completely in the
extension and in neither enlargement.  Such a prime splits completely in neither radical field.

Read through the power residue criterion this produces a prime modulo which two prescribed integers
are both non-residues.  A single non-residue corrects one place at a time, which never reduces
their number; two at once is what makes the count drop.

## Main results

* `InverseGalois.CFT.exists_prime_splitsCompletely_not_radicalField₂_of_forall_pow_ne`: **two
  elements of the rationals having no `ℓ`-th root in a Galois extension admit infinitely many
  primes splitting completely in that extension but in neither of their radical fields**, for `ℓ`
  an odd prime.
* `InverseGalois.CFT.exists_prime_splitsCompletely_pow_ne_one₂_of_forall_pow_ne` and
  `InverseGalois.CFT.exists_prime_splitsCompletely_pow_ne_one₂`: the same conclusion read as a pair
  of power residue statements modulo the prime.

## Tags

Chebotarev density, radical extension, power residue, auxiliary prime, Kummer theory
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {ℓ : ℕ}

/-! ### Two radical fields avoided at once -/

section TwoRadicals

variable [Fact ℓ.Prime] {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A]
  [IsGalois ℚ ↥A] {ζ : AlgebraicClosure ℚ}

/-- **Two elements of the rationals having no `ℓ`-th root in a Galois extension admit infinitely
many primes splitting completely in that extension but in neither of their radical fields**, for
`ℓ` an odd prime.  Each compositum of the extension with one of the radical fields has degree
exactly `ℓ` times that of the extension, and two such reciprocal degrees fall short of the
reciprocal degree of the extension; a prime splitting completely in the extension and in a radical
field would split completely in the corresponding compositum. -/
theorem exists_prime_splitsCompletely_not_radicalField₂_of_forall_pow_ne (hℓ3 : 2 < ℓ)
    (hζ : IsPrimitiveRoot ζ ℓ) (hζA : ζ ∈ A) {m₁ m₂ : ℚ}
    (hm₁ : ∀ u ∈ A, u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) m₁)
    (hm₂ : ∀ u ∈ A, u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) m₂) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ SplitsCompletely ↥A q ∧
      ¬ SplitsCompletely ↥(radicalField ℓ ({m₁} : Finset ℚ)) q ∧
      ¬ SplitsCompletely ↥(radicalField ℓ ({m₂} : Finset ℚ)) q := by
  have hℓ : ℓ.Prime := Fact.out
  set R₁ : IntermediateField ℚ (AlgebraicClosure ℚ) := radicalField ℓ ({m₁} : Finset ℚ) with hR₁
  set R₂ : IntermediateField ℚ (AlgebraicClosure ℚ) := radicalField ℓ ({m₂} : Finset ℚ) with hR₂
  have hdeg₁ : finrank ℚ ↥(A ⊔ R₁) = ℓ * finrank ℚ ↥A :=
    finrank_sup_radicalField_singleton hℓ hζ hζA hm₁
  have hdeg₂ : finrank ℚ ↥(A ⊔ R₂) = ℓ * finrank ℚ ↥A :=
    finrank_sup_radicalField_singleton hℓ hζ hζA hm₂
  have hApos : (0 : ℝ) < (finrank ℚ ↥A : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := ↥A)
    positivity
  have hℓR : (2 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ3
  have hlt : 1 / (finrank ℚ ↥(A ⊔ R₁) : ℝ) + 1 / (finrank ℚ ↥(A ⊔ R₂) : ℝ)
      < 1 / (finrank ℚ ↥A : ℝ) := by
    have hcast₁ : (finrank ℚ ↥(A ⊔ R₁) : ℝ) = (ℓ : ℝ) * (finrank ℚ ↥A : ℝ) := by
      rw [hdeg₁]; push_cast; ring
    have hcast₂ : (finrank ℚ ↥(A ⊔ R₂) : ℝ) = (ℓ : ℝ) * (finrank ℚ ↥A : ℝ) := by
      rw [hdeg₂]; push_cast; ring
    rw [hcast₁, hcast₂, ← add_div, div_lt_div_iff₀ (by positivity) hApos]
    nlinarith
  have hinf := infinite_setOf_splitsCompletely_not_splitsCompletely₂ ↥A ↥(A ⊔ R₁) ↥(A ⊔ R₂) hlt
  obtain ⟨q, ⟨⟨hqp, hqA, hq₁, hq₂⟩, hqT⟩⟩ := (hinf.diff T.finite_toSet).nonempty
  exact ⟨q, hqp, fun h => hqT (Finset.mem_coe.mpr h), hqA,
    fun h => hq₁ (splitsCompletely_sup A R₁ hqp hqA h),
    fun h => hq₂ (splitsCompletely_sup A R₂ hqp hqA h)⟩

/-- **The power residue form of the choice of an auxiliary prime with two non-residues.**  A prime
splitting completely in the given extension but in neither radical field fails the power residue
criterion for both integers, since a prime congruent to one modulo `ℓ` modulo which an integer is
an `ℓ`-th power splits completely in its radical field. -/
theorem exists_prime_splitsCompletely_pow_ne_one₂_of_forall_pow_ne (hℓ3 : 2 < ℓ)
    (hζ : IsPrimitiveRoot ζ ℓ) (hζA : ζ ∈ A) {v₁ v₂ : ℤ}
    (hv₁ : ∀ u ∈ A, u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) (v₁ : ℚ))
    (hv₂ : ∀ u ∈ A, u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) (v₂ : ℚ)) (T : Finset ℕ)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ q ≠ ℓ ∧ SplitsCompletely ↥A q ∧
      (v₁ : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 ∧ (v₂ : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 := by
  have hℓ : ℓ.Prime := Fact.out
  classical
  obtain ⟨q, hqp, hqT, hqA, hqR₁, hqR₂⟩ :=
    exists_prime_splitsCompletely_not_radicalField₂_of_forall_pow_ne hℓ3 hζ hζA hv₁ hv₂
      (insert ℓ (T ∪ (v₁.natAbs.primeFactors ∪ v₂.natAbs.primeFactors)))
  have hqne : q ≠ ℓ := by
    rintro rfl
    exact hqT (Finset.mem_insert_self _ _)
  have hqv₁ : ¬ (q : ℤ) ∣ v₁ := by
    intro h
    have hv0 : v₁ ≠ 0 := by
      rintro rfl
      exact hv₁ 0 (zero_mem A) (by simp [zero_pow hℓ.ne_zero])
    refine hqT (Finset.mem_insert_of_mem (Finset.mem_union_right T (Finset.mem_union_left _ ?_)))
    exact Nat.mem_primeFactors.mpr ⟨hqp, by simpa using Int.natAbs_dvd_natAbs.mpr h,
      Int.natAbs_ne_zero.mpr hv0⟩
  have hqv₂ : ¬ (q : ℤ) ∣ v₂ := by
    intro h
    have hv0 : v₂ ≠ 0 := by
      rintro rfl
      exact hv₂ 0 (zero_mem A) (by simp [zero_pow hℓ.ne_zero])
    refine hqT (Finset.mem_insert_of_mem (Finset.mem_union_right T (Finset.mem_union_right _ ?_)))
    exact Nat.mem_primeFactors.mpr ⟨hqp, by simpa using Int.natAbs_dvd_natAbs.mpr h,
      Int.natAbs_ne_zero.mpr hv0⟩
  refine ⟨q, hqp, fun h => hqT (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)), hqne, hqA,
    fun h => hqR₁ ?_, fun h => hqR₂ ?_⟩
  · exact splitsCompletely_radicalField hℓ hqp (hdvd q hqp hqne hqA) hqv₁ h
  · exact splitsCompletely_radicalField hℓ hqp (hdvd q hqp hqne hqA) hqv₂ h

/-- **The power residue form of the choice of an auxiliary prime with two non-residues, for a
nilpotent extension.**  Two integers which are not `ℓ`-th powers in the rationals are not `ℓ`-th
powers in a nilpotent extension of the rationals containing the `ℓ`-th roots of unity, for `ℓ` an
odd prime. -/
theorem exists_prime_splitsCompletely_pow_ne_one₂ (hℓ3 : 2 < ℓ)
    (hnil : Group.IsNilpotent Gal(↥A/ℚ)) (hζ : IsPrimitiveRoot ζ ℓ) (hζA : ζ ∈ A) {v₁ v₂ : ℤ}
    (hv₁ : ∀ y : ℚ, y ^ ℓ ≠ (v₁ : ℚ)) (hv₂ : ∀ y : ℚ, y ^ ℓ ≠ (v₂ : ℚ)) (T : Finset ℕ)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ q ≠ ℓ ∧ SplitsCompletely ↥A q ∧
      (v₁ : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 ∧ (v₂ : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 := by
  have hodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)
  exact exists_prime_splitsCompletely_pow_ne_one₂_of_forall_pow_ne hℓ3 hζ hζA
    (fun _ hu => pow_ne_of_isNilpotent hodd hnil hζ hζA hv₁ hu)
    (fun _ hu => pow_ne_of_isNilpotent hodd hnil hζ hζA hv₂ hu) T hdvd

end TwoRadicals

end InverseGalois.CFT
