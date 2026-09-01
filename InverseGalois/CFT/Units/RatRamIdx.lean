/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.Ramified
import InverseGalois.CFT.Units.PlaceComap
import InverseGalois.CFT.Units.PrimeAbove

/-!
# The ramification index of a place of a number field over the rationals

The ramification index attached to a place of a number field is defined relative to the ring of
integers of the base field, while the commutative-algebra notion of unramifiedness and the
cyclotomic computations of Mathlib are both stated relative to the rational integers.  Over the
rationals the two agree, because the ring of integers of the rationals is the rational integers: the
structure map is surjective, so the ideal below a place is the extension of the ideal below it in
the rational integers, and the ramification index only sees the extended ideal.

## Main results

* `InverseGalois.CFT.ramIdx_rat_eq_ramificationIdx_int`: **the ramification index of a place over
  the rationals is its ramification index over the rational integers.**
* `InverseGalois.CFT.ramIdx_rat_eq_one_of_isUnramifiedAt`: **an unramified place of a number field
  has ramification index one over the rationals.**
* `InverseGalois.CFT.ramIdx_rat_eq_one_of_not_dvd`: **a place of a subfield of a cyclotomic field
  lying over a rational prime that does not divide the conductor has ramification index one.**
* `InverseGalois.CFT.valuation_natCast_eq_one_of_not_dvd`: a natural number prime to the rational
  prime below a place is a unit there.

## Tags

number field, ring of integers, ramification index, unramified, cyclotomic field
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### The ramification index only sees the extended ideal -/

section Congr

/-- **The ramification index depends on the base only through the extended ideal.** -/
theorem ramificationIdx_congr {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S]
    (f : R →+* S) (g : R' →+* S) {p : Ideal R} {p' : Ideal R'} (P : Ideal S)
    (h : Ideal.map f p = Ideal.map g p') :
    Ideal.ramificationIdx f p P = Ideal.ramificationIdx g p' P := by
  unfold Ideal.ramificationIdx
  rw [h]

end Congr

/-! ### The rational integers are the ring of integers of the rationals -/

section Rat

/-- **The structure map of the ring of integers of the rationals is surjective**, because the ring
of integers of the rationals is the rational integers. -/
theorem surjective_algebraMap_int_ringOfIntegers_rat :
    Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
  have h : (algebraMap ℤ (𝓞 ℚ)) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    RingHom.ext_int _ _
  rw [h]
  exact Rat.ringOfIntegersEquiv.symm.surjective

variable {K : Type*} [Field K] [NumberField K]

/-- The ideal below a prime in the rational integers extends to the ideal below it in the ring of
integers of the rationals. -/
theorem map_under_int_eq_under_rat (P : Ideal (𝓞 K)) :
    Ideal.map (algebraMap ℤ (𝓞 ℚ)) (Ideal.under ℤ P) = Ideal.under (𝓞 ℚ) P := by
  have hcomap : Ideal.under ℤ P
      = Ideal.comap (algebraMap ℤ (𝓞 ℚ)) (Ideal.under (𝓞 ℚ) P) := by
    rw [Ideal.under_def, Ideal.under_def, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq ℤ (𝓞 ℚ) (𝓞 K)]
  rw [hcomap]
  exact Ideal.map_comap_of_surjective _ surjective_algebraMap_int_ringOfIntegers_rat _

/-- The ideal below a prime extends to the same ideal whether it is taken in the rational integers
or in the ring of integers of the rationals. -/
theorem map_under_rat_eq_map_under_int (P : Ideal (𝓞 K)) :
    Ideal.map (algebraMap (𝓞 ℚ) (𝓞 K)) (Ideal.under (𝓞 ℚ) P)
      = Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.under ℤ P) := by
  rw [← map_under_int_eq_under_rat P, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq ℤ (𝓞 ℚ) (𝓞 K)]

/-- **The ramification index of a place over the rationals is its ramification index over the
rational integers.** -/
theorem ramIdx_rat_eq_ramificationIdx_int (w : HeightOneSpectrum (𝓞 K)) :
    ramIdx (𝓞 ℚ) w
      = Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.under ℤ w.asIdeal) w.asIdeal :=
  ramificationIdx_congr _ _ _ (map_under_rat_eq_map_under_int w.asIdeal)

/-- **An unramified place of a number field has ramification index one over the rationals.** -/
theorem ramIdx_rat_eq_one_of_isUnramifiedAt (w : HeightOneSpectrum (𝓞 K))
    [Algebra.IsUnramifiedAt ℤ w.asIdeal] : ramIdx (𝓞 ℚ) w = 1 := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  rw [ramIdx_rat_eq_ramificationIdx_int]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt w.ne_bot

end Rat

/-! ### Places away from the conductor of a cyclotomic field -/

section Cyclotomic

/-- **A place of a subfield of a cyclotomic field away from the conductor is unramified.**  A place
of a number field embedded in the cyclotomic field of conductor `n` lying over a rational prime that
does not divide `n` has ramification index one over the rationals. -/
theorem ramIdx_rat_eq_one_of_not_dvd (n : ℕ) [NeZero n] (E : Type*) [Field E] [NumberField E]
    [IsCyclotomicExtension {n} ℚ E] {F : Type*} [Field F] [NumberField F] [Algebra F E] (p : ℕ)
    [Fact (Nat.Prime p)] (w : HeightOneSpectrum (𝓞 F))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] (hn : ¬ p ∣ n) : ramIdx (𝓞 ℚ) w = 1 := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI := isUnramifiedAt_of_not_dvd_of_algebra n E p w.asIdeal hn
  exact ramIdx_rat_eq_one_of_isUnramifiedAt w

/-- **A place of a subfield of a cyclotomic field containing no rational prime dividing the
conductor is unramified.**  This is the form that does not name the rational prime below the
place. -/
theorem ramIdx_rat_eq_one_of_forall_prime_not_dvd (n : ℕ) [NeZero n] (E : Type*) [Field E]
    [NumberField E] [IsCyclotomicExtension {n} ℚ E] {F : Type*} [Field F] [NumberField F]
    [Algebra F E] (w : HeightOneSpectrum (𝓞 F))
    (h : ∀ q : ℕ, q.Prime → (q : 𝓞 F) ∈ w.asIdeal → ¬ q ∣ n) : ramIdx (𝓞 ℚ) w = 1 := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI := isUnramifiedAt_of_forall_prime_not_dvd_of_algebra n E w.asIdeal w.ne_bot h
  exact ramIdx_rat_eq_one_of_isUnramifiedAt w

end Cyclotomic

/-! ### Numbers prime to the residue characteristic -/

section Unit

/-- **A natural number prime to the rational prime below a place is a unit there.**  If it were not,
it would lie in the prime of the place, hence in the prime below it, which is the ideal generated by
the rational prime. -/
theorem valuation_natCast_eq_one_of_not_dvd {K : Type*} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {p : ℕ} [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] {m : ℕ}
    (hpm : ¬ p ∣ m) : w.valuation K ((m : ℕ) : K) = 1 := by
  rw [valuation_natCast_eq_one_iff]
  intro hmem
  have hunder : (m : ℤ) ∈ Ideal.under ℤ w.asIdeal := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using hmem
  rw [← Ideal.LiesOver.over (p := Ideal.span {(p : ℤ)}) (P := w.asIdeal),
    Ideal.mem_span_singleton] at hunder
  exact hpm (Int.ofNat_dvd.mp hunder)

end Unit

end InverseGalois.CFT
