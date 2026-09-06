/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NormPlaceValue

/-!
# Units at a place and the norm

The value of a unit of a number field at a finite place vanishes exactly when its image in the
completion has valuation one, since the value is the logarithm of that valuation.

The value of a norm at a place of the rationals is the sum, over the places above it, of the
residue degree times the value there, so a unit that is invertible at every place above a rational
prime has a norm invertible at that prime.  This is what lets the local computation at the
conductor of a cyclic algebra be carried out simultaneously over a number field and over the
rationals.

## Main results

* `InverseGalois.CFT.valued_eq_one_of_placeValue_eq_zero`: a unit of value zero at a place has
  valuation one in the completion there.
* `InverseGalois.CFT.placeValue_eq_zero_iff_valued_eq_one`: the two conditions agree.
* `InverseGalois.CFT.placeValue_normUnit_eq_zero`: **the norm of a unit invertible at every place
  above a rational prime is invertible at that prime.**

## Tags

number field, finite place, valuation, unit, norm, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section UnitValue

variable {k : Type} [Field k] [NumberField k]

/-- A unit of value zero at a place has valuation one in the completion there. -/
theorem valued_eq_one_of_placeValue_eq_zero (v : HeightOneSpectrum (𝓞 k)) {a : kˣ}
    (ha : placeValue v a = 0) :
    Valued.v (algebraMap k (v.adicCompletion k) (a : k)) = 1 := by
  have hne : v.valuation k (a : k) ≠ 0 := valuation_ne_zero v (Units.ne_zero a)
  have hlog : WithZero.log (v.valuation k (a : k)) = 0 := by
    rw [← placeOrd_apply, ← placeValue_eq_placeOrd]
    exact ha
  rw [valued_algebraMap_eq_valuation, ← WithZero.exp_log hne, hlog, WithZero.exp_zero]

/-- **The value of a unit at a place vanishes exactly when its image in the completion has
valuation one.** -/
theorem placeValue_eq_zero_iff_valued_eq_one (v : HeightOneSpectrum (𝓞 k)) (a : kˣ) :
    placeValue v a = 0 ↔ Valued.v (algebraMap k (v.adicCompletion k) (a : k)) = 1 :=
  ⟨valued_eq_one_of_placeValue_eq_zero v, placeValue_eq_zero v⟩

end UnitValue

/-! ### The norm of a unit invertible above a rational prime -/

section NormUnit

variable {k : Type} [Field k] [NumberField k]

/-- **The norm of a unit invertible at every place above a rational prime is invertible at that
prime.**  The value of the norm is the sum over the places above the prime of the residue degree
there times the value there, and every term vanishes. -/
theorem placeValue_normUnit_eq_zero (P : HeightOneSpectrum (𝓞 ℚ)) (a : kˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P → placeValue v a = 0) :
    placeValue P (Units.map (Algebra.norm ℚ : k →* ℚ) a) = 0 := by
  rw [placeValue_normUnit P a]
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  by_cases hW : Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 k)) W.asIdeal = P.asIdeal
  · have hWP : primeUnder (𝓞 ℚ) W = P := by
      refine HeightOneSpectrum.ext ?_
      rw [primeUnder_asIdeal, Ideal.under_def]
      exact hW
    rw [h W hWP, mul_zero]
  · rw [inertiaDeg_eq_zero_of_comap_ne hW, Nat.cast_zero, zero_mul]

end NormUnit

end InverseGalois.CFT
