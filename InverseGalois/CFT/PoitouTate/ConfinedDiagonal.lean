/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharPlace
import InverseGalois.CFT.PoitouTate.ConfinedSurjective
import InverseGalois.CFT.PoitouTate.SUnitReduce

/-!
# A diagonal of confined units, described by local conditions alone

For a prime exponent the orders of the confined units at a finite set of places are onto as soon as
there is a diagonal: one confined unit for each of the places, whose order there is prime to the
exponent and whose order at the other places of the set is divisible by it.  That criterion is
stated in terms of orders, but the units which the arithmetic actually produces are described by
local conditions — they are asked to be local powers at prescribed places — and it is convenient to
be able to hand those conditions over directly.

The translation is a single step.  A unit which is a local power at a place is in particular
unramified there, so its order at that place is divisible by the exponent; the value of a unit at a
finite place is minus its order, so the divisibility transfers between the two readings without
changing anything.  A local power is therefore more than the off-diagonal demand of the criterion
asks for, and only the divisibility it implies has to be carried over.

So the diagonal is produced by a family of units subject to two local demands — local powers at the
places where the radicand must stay inert and orders divisible by the exponent outside the places
where ramification is allowed — together with the two demands at the named places themselves, that
the order be divisible by the exponent at the other named places and prime to it at the place the
unit belongs to.

Neither of the two readings notices an automorphism of the field applied to the unit and to the
place at once: the order is unchanged, and the classes at the two places are identified by the
automorphism, so a local power stays one.  A diagonal at one place of an orbit is therefore a
diagonal at every place of that orbit, and only one place in each orbit has to be dealt with.

## Main results

* `InverseGalois.CFT.dvd_ord_of_localClassHom_eq_one`: a unit whose local class at a place is
  trivial has order there divisible by the exponent.
* `InverseGalois.CFT.surjective_confinedOrd_of_exists_units`: **the local conditions alone produce
  the diagonal**, so the orders of the confined units at the named places are onto.
* `InverseGalois.CFT.ord_galUnits`, `InverseGalois.CFT.localClassHom_galUnits_eq_one_iff`: moving a
  unit and the place it is read at together changes neither its order nor its being a local power,
  so a diagonal at one place of an orbit is a diagonal at all of them.

## Tags

number field, confined unit, local class, order, diagonal, surjective
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### The order of a local power -/

section Order

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]

/-- **A unit whose local class at a place is trivial has order there divisible by the exponent.**
The trivial class is unramified, which is the same divisibility read on the value of the unit, and
the value at a finite place is minus the order. -/
theorem dvd_ord_of_localClassHom_eq_one {v : HeightOneSpectrum (𝓞 K)} {a : Kˣ}
    (h : localClassHom v n a = 1) : (n : ℤ) ∣ ord K v ((a : Kˣ) : K) := by
  have hv := dvd_placeValue_of_localClassHom_eq_one h
  rwa [placeValue_eq_neg_ord, dvd_neg] at hv

end Order

/-! ### Moving a unit and the place it is read at -/

section Move

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]

/-- **The order of a unit at a place is the order of its image at the image of the place.** -/
theorem ord_galUnits (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ord K (σ • v) ((galUnits σ a : Kˣ) : K) = ord K v ((a : Kˣ) : K) := by
  rw [coe_galUnits_apply]
  exact ord_galSmul σ v ((a : Kˣ) : K)

/-- **A unit is a local power at a place exactly when its image is one at the image of the
place**, the classes at the two places being identified by the automorphism. -/
theorem localClassHom_galUnits_eq_one_iff (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a : Kˣ) : localClassHom (σ • v) n (galUnits σ a) = 1 ↔ localClassHom v n a = 1 := by
  rw [← localClassesGalEquiv_localClassHom, (localClassesGalEquiv σ v n).map_eq_one_iff]

end Move

/-! ### The diagonal from the local conditions -/

section Diagonal

variable {K : Type} [Field K] [NumberField K] (n : ℕ)
variable (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs]

/-- **The local conditions alone produce the diagonal.**  Suppose that for each named place there is
a unit which is a local power at every place of the inert set, whose order is divisible by the
exponent outside the allowed set and at every other named place, and whose order at the place itself
is prime to the exponent.  Then every system of orders at the named places is the system of orders
of a confined unit.

The first two conditions say that the unit is confined; the third is the off-diagonal divisibility,
which a local power at the place would in particular give; the fourth is the invertibility of the
diagonal entry. -/
theorem surjective_confinedOrd_of_exists_units (hn : Nat.Prime n)
    (hu : ∀ y : ↥Xs, ∃ u : Kˣ, (∀ v ∈ Tz, localClassHom v n u = 1) ∧
      (∀ v ∉ Y, (n : ℤ) ∣ ord K v ((u : Kˣ) : K)) ∧
      (∀ z : ↥Xs, z ≠ y → (n : ℤ) ∣ ord K (z : HeightOneSpectrum (𝓞 K)) ((u : Kˣ) : K)) ∧
      ¬ (n : ℤ) ∣ ord K (y : HeightOneSpectrum (𝓞 K)) ((u : Kˣ) : K)) :
    Function.Surjective (confinedOrd n Tz Y Xs) := by
  classical
  haveI : NeZero n := ⟨hn.ne_zero⟩
  choose u hTz hY hoff hon using hu
  refine surjective_confinedOrd_of_forall_place n Tz Y Xs hn
    (fun y => ⟨u y, hTz y, hY y⟩) (fun y z hyz => ?_) (fun y => ?_)
  · rw [confinedOrd_apply]
    exact hoff y z (Ne.symm hyz)
  · rw [confinedOrd_apply]
    exact hon y

end Diagonal

end InverseGalois.CFT
