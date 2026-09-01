/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.Cyclotomic.FrobeniusSplitting
import InverseGalois.CFT.Units.DecompositionGalois
import InverseGalois.CFT.Units.FrobeniusPlace

/-!
# Splitting completely and the local degree

The order of the decomposition group at a prime of a Galois number field is the ramification index
times the residue degree, and it is also the degree of the completion over the completion of the
rational prime below.  A rational prime therefore splits completely exactly when that local degree
is one.

For a Galois extension of the rationals of prime degree the local degree divides the degree, so it
is either one or the whole degree.  At a rational prime that does not split completely the local
degree is thus the whole degree, which is the input needed to check that a Brauer class is split by
such a field: the local condition of the Hasse principle asks the local invariant to be killed by
the local degree.

## Main results

* `InverseGalois.CFT.splitsCompletely_iff_card_stabilizer_eq_one`: **a rational prime splits
  completely exactly when its decomposition group is trivial.**
* `InverseGalois.CFT.card_stabilizer_asIdeal_eq_finrank_adicCompletion`: the order of the
  decomposition group at a finite place is the local degree over the rationals.
* `InverseGalois.CFT.prime_dvd_finrank_adicCompletion_of_not_splitsCompletely`: **in a Galois
  extension of the rationals of prime degree, the degree divides the local degree at a rational
  prime that does not split completely.**

## Tags

number field, decomposition group, local degree, splitting completely, completion
-/

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField InverseGalois.NumberTheory

open scoped Pointwise

/-! ### Splitting completely is triviality of the decomposition group -/

section Stabilizer

/-- **A rational prime splits completely in a Galois number field exactly when its decomposition
group is trivial.**  The order of that group is the ramification index times the residue degree,
and splitting completely says exactly that both are one. -/
theorem splitsCompletely_iff_card_stabilizer_eq_one (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    SplitsCompletely K p ↔ Nat.card ↥(stabilizer Gal(K/ℚ) P) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [splitsCompletely_iff_of_liesOver p P, card_stabilizer_eq_mul K hp P]
  refine ⟨fun h => by rw [h.1, h.2], fun h =>
    ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩⟩

end Stabilizer

/-! ### The decomposition group and the local degree -/

section LocalDegree

variable (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]

/-- **The order of the decomposition group at a finite place is the local degree over the
rationals.** -/
theorem card_stabilizer_asIdeal_eq_finrank_adicCompletion (w : HeightOneSpectrum (𝓞 K)) :
    Nat.card ↥(stabilizer Gal(K/ℚ) w.asIdeal)
      = finrank ((primeUnder (𝓞 ℚ) w).adicCompletion ℚ) (w.adicCompletion K) := by
  rw [← stabilizer_eq_stabilizer_asIdeal (k := ℚ) w, card_stabilizer_eq_finrank_adicCompletion ℚ w]

/-- **In a Galois extension of the rationals of prime degree, the degree divides the local degree
at a rational prime that does not split completely.**  The decomposition group is a subgroup, so
its order divides the degree; the degree being prime, that order is one or the degree, and one is
excluded because it would mean the prime splits completely. -/
theorem prime_dvd_finrank_adicCompletion_of_not_splitsCompletely {N : ℕ} (hN : N.Prime)
    (hcard : Nat.card Gal(K/ℚ) = N) {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] (h : ¬ SplitsCompletely K p) :
    N ∣ finrank ((primeUnder (𝓞 ℚ) w).adicCompletion ℚ) (w.adicCompletion K) := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  rw [← card_stabilizer_asIdeal_eq_finrank_adicCompletion K w]
  have hdvd : Nat.card ↥(stabilizer Gal(K/ℚ) w.asIdeal) ∣ N := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card ↥(stabilizer Gal(K/ℚ) w.asIdeal) ≠ 1 := fun hc =>
    h ((splitsCompletely_iff_card_stabilizer_eq_one K hp w.asIdeal).mpr hc)
  rcases hN.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact absurd h1 hne
  · rw [h1]

end LocalDegree

end InverseGalois.CFT
