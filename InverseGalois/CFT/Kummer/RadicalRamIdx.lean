/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.UnramifiedOrd
import InverseGalois.CFT.Units.OrbitPlaces
import InverseGalois.CFT.Units.PlaceComap
import InverseGalois.CFT.Units.PrimeAbove

/-!
# A prime of a radical extension with ramification index one

An extension unramified at a prime has ramification index one there, and a radical extension is
unramified at a prime away from the exponent at which the order of each radicand is a multiple of
the exponent.  Combining the two with the existence of a prime above a given prime of the base
produces, over any prime of the base away from the exponent at which the radicands have order a
multiple of the exponent, a prime of the radical extension with ramification index one.

That a natural number has normalised absolute value one at a prime is the same as the prime not
lying above it, and a prime of the extension lies above the natural number exactly when the prime
below it does, so the hypothesis is read off from the absolute value of the exponent at the prime
of the base.

## Main results

* `InverseGalois.CFT.ramIdx_eq_one_of_isUnramifiedAt`: a place of an extension of number fields at
  which the extension is unramified has ramification index one.
* `InverseGalois.CFT.exists_primeUnder_ramIdx_eq_one_of_radicals`: **a radical extension of number
  fields has, above a prime away from the exponent at which the order of each radicand is a
  multiple of the exponent, a prime with ramification index one.**

## Tags

number field, Kummer theory, radical, ramification index, unramified
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### An unramified place -/

section Unramified

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/-- **A place of an extension of number fields at which the extension is unramified has
ramification index one.** -/
theorem ramIdx_eq_one_of_isUnramifiedAt (w : HeightOneSpectrum (𝓞 M))
    [Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal] : ramIdx (𝓞 K) w = 1 := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt w.ne_bot

end Unramified

/-! ### A prime of a radical extension -/

section Radical

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] {p : ℕ}

/-- **A radical extension of number fields has, above a prime of the base away from the exponent at
which the order of each radicand is a multiple of the exponent, a prime with ramification index
one.**  Some prime of the extension lies above the given one, it too lies away from the exponent,
and there the extension is unramified. -/
theorem exists_primeUnder_ramIdx_eq_one_of_radicals (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {ι : Type*} {α : ι → M} {a : ι → Kˣ}
    (hpow : ∀ i, α i ^ p = algebraMap K M ((a i : K)))
    (hgen : IntermediateField.adjoin K (Set.range α) = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hv : FinitePlace.mk v ((p : ℕ) : K) = 1)
    (hav : ∀ i, (p : ℤ) ∣ ord K v ((a i : K))) :
    ∃ w : HeightOneSpectrum (𝓞 M), primeUnder (𝓞 K) w = v ∧ ramIdx (𝓞 K) w = 1 := by
  obtain ⟨w, hw⟩ := exists_primeUnder_eq (𝓞 K) (𝓞 M) v
  refine ⟨w, hw, ?_⟩
  have hpv : ((p : ℕ) : 𝓞 K) ∉ v.asIdeal := (finitePlace_natCast_eq_one_iff v p).1 hv
  have hpw : ((p : ℕ) : 𝓞 M) ∉ w.asIdeal := by
    intro hmem
    refine hpv ?_
    rw [← hw, primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  haveI := isUnramifiedAt_of_radicals_of_dvd_ord hp hζ hpow hgen hpw
    fun i => by rw [hw]; exact hav i
  exact ramIdx_eq_one_of_isUnramifiedAt w

end Radical

end InverseGalois.CFT
