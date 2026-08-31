/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InfiniteInvariant
import InverseGalois.CFT.Brauer.PlaceInvariantFinite

/-!
# The family of local invariants of a Brauer class over a number field

Every place of a number field, finite or infinite, carries an invariant of the Brauer group with
values in the rationals modulo the integers, and a class is split by the completion at a place
exactly when its invariant there vanishes.  Only finitely many of these invariants are nonzero, and
by the Albert-Brauer-Hasse-Noether theorem a class with all invariants zero is trivial: a Brauer
class over a number field is determined by its family of local invariants.

Because almost all the invariants vanish, their sum over all places is a well defined element of the
rationals modulo the integers.  That sum is written multiplicatively here, as a product over the
finite places of a family with finite support times a product over the finitely many infinite
places.

## Main definitions

* `InverseGalois.CFT.localInvariants`: **the family of local invariants of a Brauer class of a
  number field**, one for each finite place and one for each infinite place.
* `InverseGalois.CFT.totalInvariant`: **the sum of the local invariants over all places.**

## Main results

* `InverseGalois.CFT.eq_one_of_forall_invariant_eq_one`: **a Brauer class over a number field all of
  whose local invariants vanish is trivial.**
* `InverseGalois.CFT.localInvariants_injective`: **a Brauer class over a number field is determined
  by its family of local invariants.**

## Tags

Brauer group, number field, local invariant, Albert-Brauer-Hasse-Noether, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section TotalInvariant

variable (k : Type) [Field k] [NumberField k]

/-! ### The family of local invariants -/

/-- **The family of local invariants of a Brauer class of a number field**: the invariant at each
finite place together with the invariant at each infinite place. -/
noncomputable def localInvariants :
    BrauerGroup.{0, 0} k →*
      ((HeightOneSpectrum (𝓞 k) → Multiplicative QModZ) ×
        (InfinitePlace k → Multiplicative QModZ)) :=
  (Pi.monoidHom fun v : HeightOneSpectrum (𝓞 k) => placeInvariant k v).prod
    (Pi.monoidHom fun u : InfinitePlace k => infinitePlaceInvariant k u)

@[simp]
theorem localInvariants_apply (x : BrauerGroup.{0, 0} k) :
    localInvariants k x
      = (fun v : HeightOneSpectrum (𝓞 k) => placeInvariant k v x,
          fun u : InfinitePlace k => infinitePlaceInvariant k u x) := rfl

/-- **A Brauer class over a number field all of whose local invariants vanish is trivial.**  This is
the Albert-Brauer-Hasse-Noether theorem, with the archimedean places phrased through their
invariants as well. -/
theorem eq_one_of_forall_invariant_eq_one (x : BrauerGroup.{0, 0} k)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x = 1)
    (hinf : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1) :
    x = 1 :=
  eq_one_of_forall_placeInvariant_eq_one x hfin fun u =>
    (infinitePlaceInvariant_eq_one_iff k u x).mp (hinf u)

/-- **A Brauer class over a number field is determined by its family of local invariants.** -/
theorem localInvariants_injective : Function.Injective (localInvariants k) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
  refine eq_one_of_forall_invariant_eq_one k x (fun v => ?_) fun u => ?_
  · simpa using congrFun (congrArg Prod.fst hx) v
  · simpa using congrFun (congrArg Prod.snd hx) u

/-! ### The sum of the local invariants -/

/-- **The sum of the local invariants of a Brauer class of a number field over all places.**  The
invariants at the finite places vanish outside a finite set, so the product over the finite places
is a finite product, and there are only finitely many infinite places. -/
noncomputable def totalInvariant : BrauerGroup.{0, 0} k →* Multiplicative QModZ where
  toFun x := (∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x) *
    ∏ u : InfinitePlace k, infinitePlaceInvariant k u x
  map_one' := by
    simp only [map_one, finprod_one, Finset.prod_const_one, mul_one]
  map_mul' x y := by
    have hx : (Function.mulSupport
        fun v : HeightOneSpectrum (𝓞 k) => placeInvariant k v x).Finite :=
      finite_setOf_placeInvariant_ne_one x
    have hy : (Function.mulSupport
        fun v : HeightOneSpectrum (𝓞 k) => placeInvariant k v y).Finite :=
      finite_setOf_placeInvariant_ne_one y
    simp only [map_mul]
    rw [finprod_mul_distrib hx hy, Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

theorem totalInvariant_apply (x : BrauerGroup.{0, 0} k) :
    totalInvariant k x = (∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x) *
      ∏ u : InfinitePlace k, infinitePlaceInvariant k u x := rfl

end TotalInvariant

end InverseGalois.CFT
