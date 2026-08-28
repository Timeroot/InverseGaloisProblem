/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The primes above a natural number

Whether a prime of the ring of integers lies above a natural number can be read off in three
equivalent ways: from membership of the number in the prime, from the adic valuation of the number,
and from the normalised absolute value at the associated finite place.  This file records the
translations, so that a hypothesis naming the primes above a number may be stated once and used
wherever any of the three shapes is expected.

## Main results

* `InverseGalois.CFT.valuation_eq_one_iff_notMem`: an element of a Dedekind domain has adic
  valuation one at a prime exactly when it lies outside that prime.
* `InverseGalois.CFT.valuation_natCast_eq_one_iff`: **a natural number has adic valuation one at a
  prime exactly when the prime does not lie above it.**
* `InverseGalois.CFT.valued_natCast_eq_one_iff`: the same, read in the completion.
* `InverseGalois.CFT.finitePlace_natCast_eq_one_iff`: the same, read at the finite place.

## Tags

Dedekind domain, number field, prime, adic valuation, finite place
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- An element of a Dedekind domain has adic valuation one at a prime exactly when it lies outside
that prime. -/
theorem valuation_eq_one_iff_notMem (r : R) :
    v.valuation K (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]

/-- **A natural number has adic valuation one at a prime exactly when the prime does not lie above
it.** -/
theorem valuation_natCast_eq_one_iff (n : ℕ) :
    v.valuation K ((n : ℕ) : K) = 1 ↔ (n : R) ∉ v.asIdeal := by
  rw [← map_natCast (algebraMap R K) n, valuation_eq_one_iff_notMem]

/-- A natural number is a unit in the completion at a prime exactly when the prime does not lie
above it. -/
theorem valued_natCast_eq_one_iff (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion K) = 1 ↔ (n : R) ∉ v.asIdeal := by
  have hcast : ((n : ℕ) : v.adicCompletion K) = (((n : ℕ) : K) : v.adicCompletion K) :=
    (map_natCast (UniformSpace.Completion.coeRingHom :
      WithVal (v.valuation K) →+* v.adicCompletion K) n).symm
  rw [hcast, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', valuation_natCast_eq_one_iff]

end Dedekind

section NumberFieldPlace

variable {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- **A natural number has normalised absolute value one at a finite place exactly when the
underlying prime does not lie above it.** -/
theorem finitePlace_natCast_eq_one_iff (n : ℕ) :
    FinitePlace.mk v ((n : ℕ) : K) = 1 ↔ (n : 𝓞 K) ∉ v.asIdeal := by
  rw [FinitePlace.mk_apply,
    show ((n : ℕ) : K) = algebraMap (𝓞 K) K (n : 𝓞 K) by rw [map_natCast]]
  exact FinitePlace.norm_eq_one_iff_notMem v (n : 𝓞 K)

end NumberFieldPlace

end InverseGalois.CFT
