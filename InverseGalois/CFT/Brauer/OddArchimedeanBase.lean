/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealBrauer
import InverseGalois.CFT.Brauer.TotallyRealInvariant

/-!
# A Brauer class of odd order over a number field is split at every archimedean place

The completion of a number field at a real place is isomorphic to the reals over the field, and the
Brauer group of the reals has two elements.  A class killed by an odd exponent therefore has trivial
image in the Brauer group of every real completion, its image being killed both by two and by the
odd exponent, and those two exponents are coprime.  At a complex place every class is split because
the completion is algebraically closed.  So the archimedean invariants of a class of odd order all
vanish and its total invariant is the product of its invariants at the finite places alone.

Over the rationals this is the content of the corresponding statements for the reals themselves; the
argument needs no property of the base beyond having a completion isomorphic to the reals at a real
place, so it runs verbatim over an arbitrary number field.

## Main results

* `InverseGalois.CFT.infinitePlaceInvariant_eq_one_of_odd_pow_eq_one`: **a Brauer class of a number
  field killed by an odd exponent has trivial invariant at every infinite place.**
* `InverseGalois.CFT.totalInvariant_eq_finprod_of_odd_pow_eq_one_base`: **the total invariant of
  such a class is the product of its invariants at the finite places.**

## Tags

Brauer group, number field, infinite place, archimedean, odd order, local invariant
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section OddBase

variable {k : Type} [Field k] [NumberField k] {N : ℕ} (hN : Odd N)
  {x : BrauerGroup.{0, 0} k} (hx : x ^ N = 1)

include hN hx

omit [NumberField k] in
/-- **A Brauer class of a number field killed by an odd exponent has trivial invariant at every
infinite place.**  At a complex place every class is split, and at a real place the completion is
the reals, whose Brauer group is killed by two. -/
theorem infinitePlaceInvariant_eq_one_of_odd_pow_eq_one (u : InfinitePlace k) :
    infinitePlaceInvariant k u x = 1 := by
  rcases u.isReal_or_isComplex with hu | hu
  · letI : Algebra k ℝ := (InfinitePlace.embedding_of_isReal hu).toAlgebra
    rw [infinitePlaceInvariant_eq_one_iff, relative_completion_eq_relative_real k hu rfl,
      BrauerGroup.relative, MonoidHom.mem_ker]
    have h2 : orderOf (BrauerGroup.baseChangeHom ℝ x) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (sq_eq_one_brauerGroup_real _)
    have hNe : orderOf (BrauerGroup.baseChangeHom ℝ x) ∣ N :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
    have hgcd := Nat.dvd_gcd h2 hNe
    rw [Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr hN)] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  · rw [infinitePlaceInvariant_of_isComplex k hu, MonoidHom.one_apply]

/-- **The total invariant of a Brauer class of a number field killed by an odd exponent is the
product of its invariants at the finite places.** -/
theorem totalInvariant_eq_finprod_of_odd_pow_eq_one_base :
    totalInvariant k x = ∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x :=
  totalInvariant_eq_finprod k x (infinitePlaceInvariant_eq_one_of_odd_pow_eq_one hN hx)

end OddBase

end InverseGalois.CFT
