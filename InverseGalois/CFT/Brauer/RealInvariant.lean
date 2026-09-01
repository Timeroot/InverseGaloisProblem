/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicInvariant
import InverseGalois.CFT.Brauer.RealBrauer

/-!
# The invariant of the Brauer group at the real place

The Brauer group of the reals is cyclic of order two, so it has exactly one injection into the
rationals modulo the integers: the trivial class goes to zero and the class of the Hamilton
quaternions goes to one half.  This is the invariant of the Brauer group at the real place, the
archimedean member of the family of local invariants whose sum over all places of a number field
vanishes.

## Main definitions

* `InverseGalois.CFT.realBrauerInvariant`: the invariant at the real place.

## Main results

* `InverseGalois.CFT.realBrauerInvariant_injective`: **the invariant at the real place is
  injective.**
* `InverseGalois.CFT.realBrauerInvariant_of_ne_one`: the invariant of a nontrivial real class is
  one half.

## Tags

Brauer group, real place, invariant map, class field theory
-/

namespace InverseGalois.CFT

/-- **The invariant of the Brauer group at the real place.**  The Brauer group of the reals is
cyclic of order two, and its invariant is the corresponding element of the rationals modulo the
integers. -/
noncomputable def realBrauerInvariant : BrauerGroup ℝ →* Multiplicative QModZ :=
  (AddMonoidHom.toMultiplicative (zmodQModZ 2)).comp brauerRealEquiv.toMonoidHom

/-- **The invariant at the real place is injective.** -/
theorem realBrauerInvariant_injective : Function.Injective realBrauerInvariant := by
  intro x y h
  refine brauerRealEquiv.injective (zmodQModZ_injective 2 ?_)
  exact h

/-- **The invariant at the real place detects the trivial class.** -/
theorem realBrauerInvariant_eq_one_iff (x : BrauerGroup ℝ) :
    realBrauerInvariant x = 1 ↔ x = 1 :=
  ⟨fun h => realBrauerInvariant_injective (by rw [h, map_one]), fun h => by rw [h, map_one]⟩

/-- **The invariant of a nontrivial real class is one half.** -/
theorem realBrauerInvariant_of_ne_one {x : BrauerGroup ℝ} (hx : x ≠ 1) :
    realBrauerInvariant x = Multiplicative.ofAdd (QuotientAddGroup.mk (1 / 2 : ℚ)) := by
  have hne : Multiplicative.toAdd (brauerRealEquiv x) ≠ 0 := by
    intro h
    refine hx (brauerRealEquiv.injective ?_)
    rw [map_one]
    exact Multiplicative.toAdd.injective h
  have hall : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have h1 : Multiplicative.toAdd (brauerRealEquiv x) = 1 := hall _ hne
  have h3 : zmodQModZ 2 (1 : ZMod 2) = QuotientAddGroup.mk (1 / 2 : ℚ) := by
    have h2 : ((1 : ℤ) : ZMod 2) = 1 := by norm_num
    rw [← h2, zmodQModZ_intCast]
    norm_num
  show Multiplicative.ofAdd (zmodQModZ 2 (Multiplicative.toAdd (brauerRealEquiv x))) = _
  rw [h1, h3]

end InverseGalois.CFT
