/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NormPrimesOver
import InverseGalois.CFT.Units.RatRamIdx

/-!
# The rationals as a base field

The ring of integers of the rationals is the ring of rational integers, and the two consequences of
that identification which the comparison of local invariants needs are recorded here.

The first is that the extension of the rational integers to the integers of the rationals carries a
prime to the prime below it, so a place of the rationals is unramified over the rational integers.
This is what lets the computation of the invariant at the place of a conductor, which is stated for
an arbitrary base unramified over the rational prime below, be applied over the rationals
themselves.

The second is that the norm of an algebraic integer taken relative to the integers of the rationals
is the norm of its image taken relative to the rationals.  Both are restrictions of the same norm
of the fraction fields, since the integers of a number field are free of finite rank over the
integers of the rationals.

## Main results

* `InverseGalois.CFT.ramIdx_int_rat_eq_one`: **a place of the rationals is unramified over the
  rational integers.**
* `InverseGalois.CFT.algebraMap_norm_ringOfIntegers_rat`: **the norm of an algebraic integer
  relative to the integers of the rationals is the norm of its image relative to the rationals.**

## Tags

number field, ring of integers, rational integers, ramification index, norm, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### A place of the rationals is unramified over the rational integers -/

section RamIdx

/-- **A place of the rationals is unramified over the rational integers.**  The structure map of
the integers of the rationals is surjective, so the prime below a place extends to the place
itself, and a prime is not contained in its own square. -/
theorem ramIdx_int_rat_eq_one (P : HeightOneSpectrum (𝓞 ℚ)) : ramIdx ℤ P = 1 := by
  haveI : P.asIdeal.IsPrime := P.isPrime
  have hmap : Ideal.map (algebraMap ℤ (𝓞 ℚ)) (primeUnder ℤ P).asIdeal = P.asIdeal := by
    rw [primeUnder_asIdeal, map_under_int_eq_under_rat P.asIdeal, Ideal.under_def,
      Algebra.algebraMap_self, Ideal.comap_id]
  show Ideal.ramificationIdx (algebraMap ℤ (𝓞 ℚ)) (primeUnder ℤ P).asIdeal P.asIdeal = 1
  refine Ideal.ramificationIdx_spec ?_ ?_
  · rw [hmap, pow_one]
  · rw [hmap]
    intro h
    exact (Ideal.pow_succ_lt_pow P.ne_bot 1).not_ge (by rwa [pow_one])

end RamIdx

/-! ### The norm relative to the integers of the rationals -/

section Norm

variable {k : Type} [Field k] [NumberField k]

/-- **The norm of an algebraic integer relative to the integers of the rationals is the norm of its
image relative to the rationals.**  The integers of a number field are free of finite rank over the
integers of the rationals, which are a principal ideal ring, so the norm over the integers is the
restriction of the norm over the fraction fields. -/
theorem algebraMap_norm_ringOfIntegers_rat (b : 𝓞 k) :
    algebraMap (𝓞 ℚ) ℚ (Algebra.norm (𝓞 ℚ) b) = Algebra.norm ℚ (algebraMap (𝓞 k) k b) := by
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm
      Rat.ringOfIntegersEquiv.symm.surjective
  haveI : Module.Free (𝓞 ℚ) (𝓞 k) :=
    Module.free_of_finite_type_torsion_free' (R := 𝓞 ℚ) (M := 𝓞 k)
  rw [← Algebra.intNorm_eq_norm (A := 𝓞 ℚ) (B := 𝓞 k)]
  exact Algebra.algebraMap_intNorm (A := 𝓞 ℚ) (K := ℚ) (B := 𝓞 k) (L := k) b

end Norm

end InverseGalois.CFT
