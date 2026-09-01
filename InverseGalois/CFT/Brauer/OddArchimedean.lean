/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealBrauer
import InverseGalois.CFT.Brauer.TotallyRealInvariant

/-!
# A Brauer class of odd order is split at every archimedean place

The Brauer group of the reals has two elements, so every real class is killed by squaring.  A class
of the rationals whose order is odd therefore base changes to the trivial class over the reals: its
image is killed both by two and by the odd exponent, hence by their greatest common divisor.

The completion of the rationals at an infinite place is the reals, and the completion of a number
field at a real place receives the reals, so the same class is split by every archimedean
completion of every number field.  For a class of odd order the archimedean conditions in the Hasse
principle are therefore automatic, and the total invariant is the product over the finite places.

## Main results

* `InverseGalois.CFT.mem_relative_real_of_odd_pow_eq_one`: **a Brauer class of the rationals killed
  by an odd exponent is split by the reals.**
* `InverseGalois.CFT.mem_relative_completion_of_odd_pow_eq_one`: **such a class is split by the
  completion of any number field at a real place.**
* `InverseGalois.CFT.totalInvariant_eq_finprod_of_odd_pow_eq_one`: **the total invariant of such a
  class is the product of its invariants at the finite places.**

## Tags

Brauer group, real place, infinite place, odd order, invariant, Hasse principle
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Odd order kills the real base change -/

section OddReal

variable {N : ℕ} (hN : Odd N) {x : BrauerGroup.{0, 0} ℚ} (hx : x ^ N = 1)

include hN hx

/-- **A Brauer class of the rationals killed by an odd exponent is split by the reals.**  Its base
change to the reals is killed by two, because the Brauer group of the reals has two elements, and
by the odd exponent; those two are coprime. -/
theorem mem_relative_real_of_odd_pow_eq_one : x ∈ BrauerGroup.relative ℚ ℝ := by
  rw [BrauerGroup.relative, MonoidHom.mem_ker]
  have h2 : orderOf (BrauerGroup.baseChangeHom ℝ x) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (sq_eq_one_brauerGroup_real _)
  have hNe : orderOf (BrauerGroup.baseChangeHom ℝ x) ∣ N :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have hgcd := Nat.dvd_gcd h2 hNe
  rw [Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr hN)] at hgcd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)

/-- **A Brauer class of the rationals killed by an odd exponent is split by the completion of any
number field at a real place.**  Such a completion receives the reals, and the reals already split
the class. -/
theorem mem_relative_completion_of_odd_pow_eq_one {L : Type} [Field L] [NumberField L]
    {U : InfinitePlace L} (hU : U.IsReal) : x ∈ BrauerGroup.relative ℚ U.Completion :=
  relative_le_relative_of_algHom
    ((InfinitePlace.Completion.ringEquivRealOfIsReal hU).symm.toRingHom.toRatAlgHom)
    (mem_relative_real_of_odd_pow_eq_one hN hx)

/-- **A Brauer class of the rationals killed by an odd exponent has trivial invariant at every
infinite place.**  The completion of the rationals at an infinite place splits the same classes as
the reals. -/
theorem infinitePlaceInvariant_rat_eq_one_of_odd_pow_eq_one (u : InfinitePlace ℚ) :
    infinitePlaceInvariant ℚ u x = 1 := by
  rw [infinitePlaceInvariant_eq_one_iff, relative_completion_rat_eq_relative_real]
  exact mem_relative_real_of_odd_pow_eq_one hN hx

/-- **The total invariant of a Brauer class of the rationals killed by an odd exponent is the
product of its invariants at the finite places.** -/
theorem totalInvariant_eq_finprod_of_odd_pow_eq_one :
    totalInvariant ℚ x = ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), placeInvariant ℚ v x :=
  totalInvariant_eq_finprod ℚ x (infinitePlaceInvariant_rat_eq_one_of_odd_pow_eq_one hN hx)

end OddReal

end InverseGalois.CFT
