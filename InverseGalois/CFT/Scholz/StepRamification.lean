/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Disjoint
import InverseGalois.CFT.Level
import InverseGalois.CFT.Scholz.SplitStep

/-!
# The branching prime of a split step really branches

The compositum of `InverseGalois.CFT.Scholz.SplitStep` is ramified at the primes of the field it
extends and at the branching prime only.  Both inclusions are in fact equalities: ramification
propagates upward along the two factors, and the new factor is ramified somewhere because a number
field unramified at every rational prime is `ℚ` — Minkowski's theorem — while the only prime
available to it is the branching prime.

Knowing the ramified set exactly, rather than up to inclusion, is what lets an iterated split step
produce a prescribed number of *distinct* ramified primes: the branching prime of the next step is
unramified in the field built so far, hence different from all the primes already used.

## Main results

* `InverseGalois.CFT.ramifiedSet_stepAux_eq`: the new factor is ramified at the branching prime and
  nowhere else.
* `InverseGalois.CFT.ramifiedSet_stepField_eq`: **the compositum is ramified exactly at the primes
  of the field it extends together with the branching prime.**

## Tags

Scholz–Reichardt, ramification, Minkowski, compositum
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable (L : Type*) [Field L] [NumberField L] {ℓ : ℕ} (hℓ : ℓ.Prime) (N e : ℕ)

/-- **The new factor is ramified at the branching prime and nowhere else.**  It is ramified at no
other prime, and it is ramified somewhere because its degree exceeds one. -/
theorem ramifiedSet_stepAux_eq (he : e ≠ 0) :
    ramifiedSet ↥(stepAux L hℓ N e) = {stepPrime L hℓ N e} := by
  rcases Set.subset_singleton_iff_eq.mp (ramifiedSet_stepAux L hℓ N e) with h | h
  · exact absurd ((finrank_stepAux L hℓ N e).symm.trans
      (finrank_eq_one_of_ramifiedSet_eq_empty ↥(stepAux L hℓ N e) h))
      (Nat.one_lt_pow he hℓ.one_lt).ne'
  · exact h

/-- **The branching prime is ramified in the compositum.**  It is ramified in the new factor, and
ramification propagates upward. -/
theorem mem_ramifiedSet_stepField (he : e ≠ 0) :
    stepPrime L hℓ N e ∈ ramifiedSet ↥(stepField L hℓ N e) := by
  refine ramifiedSet_subset ↥(innerNew L hℓ N e) ↥(stepField L hℓ N e) ?_
  rw [← ramifiedSet_eq_of_ringEquiv (innerNewEquiv L hℓ N e).toRingEquiv,
    ramifiedSet_stepAux_eq L hℓ N e he]
  exact rfl

/-- **Every prime ramified in the field being extended is ramified in the compositum.** -/
theorem ramifiedSet_subset_stepField :
    ramifiedSet L ⊆ ramifiedSet ↥(stepField L hℓ N e) := by
  rw [← ramifiedSet_innerOld L hℓ N e]
  exact ramifiedSet_subset ↥(innerOld L hℓ N e) ↥(stepField L hℓ N e)

/-- **The compositum is ramified exactly at the primes of the field it extends together with the
branching prime.** -/
theorem ramifiedSet_stepField_eq (he : e ≠ 0) :
    ramifiedSet ↥(stepField L hℓ N e) = ramifiedSet L ∪ {stepPrime L hℓ N e} :=
  Set.Subset.antisymm (ramifiedSet_stepField L hℓ N e)
    (Set.union_subset (ramifiedSet_subset_stepField L hℓ N e)
      (Set.singleton_subset_iff.mpr (mem_ramifiedSet_stepField L hℓ N e he)))

end InverseGalois.CFT
