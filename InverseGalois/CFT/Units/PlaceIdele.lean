/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Idele

/-!
# The idele supported at a single finite place

A unit of the completion at one finite place of a number field, extended by the trivial unit at
every other place, is an idele: its local component is a unit of the valuation ring outside a
single prime.  This file records that embedding and the computation of its components.

Subtracting the value at one place turns an arbitrary idele into one whose component there is
trivial, which is how a distinguished prime is separated off from the rest of the places.

## Main definitions

* `InverseGalois.CFT.fullPlaceIdele`: a local unit at one finite place, extended trivially, as an
  element of the product of all the local unit groups.
* `InverseGalois.CFT.adicPlaceIdele`: **the idele supported at a single finite place.**

## Main results

* `InverseGalois.CFT.fullPlaceIdele_snd_self`: its component at the chosen place is the given unit.
* `InverseGalois.CFT.fullPlaceIdele_snd_of_ne`: its component at any other finite place is trivial.

## Tags

number field, idele, place, completion, unit
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section PlaceIdele

variable (k : Type*) [Field k] [NumberField k]

open scoped Classical in
/-- A local unit at one finite place, extended by the trivial unit at every other place. -/
noncomputable def fullPlaceIdele (v : HeightOneSpectrum (𝓞 k)) :
    Additive (v.adicCompletion k)ˣ →+ FullIdele k where
  toFun u := (0, Pi.single (M := fun v' : HeightOneSpectrum (𝓞 k) =>
    Additive (v'.adicCompletion k)ˣ) v u)
  map_zero' := Prod.ext rfl (Pi.single_zero (M := fun v' : HeightOneSpectrum (𝓞 k) =>
    Additive (v'.adicCompletion k)ˣ) v)
  map_add' u u' := Prod.ext (add_zero 0).symm (Pi.single_add (f := fun v' :
    HeightOneSpectrum (𝓞 k) => Additive (v'.adicCompletion k)ˣ) v u u')

variable {k}

@[simp]
theorem fullPlaceIdele_fst (v : HeightOneSpectrum (𝓞 k)) (u : Additive (v.adicCompletion k)ˣ)
    (w : InfinitePlace k) : (fullPlaceIdele k v u).1 w = 0 := rfl

open scoped Classical in
@[simp]
theorem fullPlaceIdele_snd_self (v : HeightOneSpectrum (𝓞 k))
    (u : Additive (v.adicCompletion k)ˣ) : (fullPlaceIdele k v u).2 v = u :=
  Pi.single_eq_same
    (M := fun v' : HeightOneSpectrum (𝓞 k) => Additive (v'.adicCompletion k)ˣ) v u

open scoped Classical in
@[simp]
theorem fullPlaceIdele_snd_of_ne {v v' : HeightOneSpectrum (𝓞 k)} (h : v' ≠ v)
    (u : Additive (v.adicCompletion k)ˣ) : (fullPlaceIdele k v u).2 v' = 0 :=
  Pi.single_eq_of_ne
    (M := fun v'' : HeightOneSpectrum (𝓞 k) => Additive (v''.adicCompletion k)ˣ) h u

variable (k) in
/-- A local unit at one finite place, extended trivially, is an idele: away from that place its
component is the trivial unit, which is a unit of the valuation ring. -/
theorem fullPlaceIdele_mem_idele (v : HeightOneSpectrum (𝓞 k))
    (u : Additive (v.adicCompletion k)ˣ) : fullPlaceIdele k v u ∈ idele k := by
  rw [mem_idele, Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton v) fun v' hv' => ?_
  simp only [Set.mem_setOf_eq] at hv'
  rw [Set.mem_singleton_iff]
  by_contra hne
  exact hv' (by rw [fullPlaceIdele_snd_of_ne hne, map_zero])

variable (k) in
/-- **The idele supported at a single finite place.** -/
noncomputable def adicPlaceIdele (v : HeightOneSpectrum (𝓞 k)) :
    Additive (v.adicCompletion k)ˣ →+ ↥(idele k) where
  toFun u := ⟨fullPlaceIdele k v u, fullPlaceIdele_mem_idele k v u⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem coe_adicPlaceIdele (v : HeightOneSpectrum (𝓞 k)) (u : Additive (v.adicCompletion k)ˣ) :
    ((adicPlaceIdele k v u : ↥(idele k)) : FullIdele k) = fullPlaceIdele k v u := rfl

end PlaceIdele

end InverseGalois.CFT
