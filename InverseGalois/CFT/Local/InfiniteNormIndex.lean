/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteHerbrand
import InverseGalois.CFT.Tate.CyclicHilbert90
import InverseGalois.CFT.Tate.H0Norm

/-!
# The norm index at an infinite place

The decomposition group at an infinite place of a Galois extension of number fields acts faithfully
on the completion, which is a field, so Hilbert's theorem 90 makes the lower Tate group of the
units vanish.  The Herbrand quotient of those units is the order of the decomposition group, so
dividing leaves that order as the order of the upper Tate group: the norm index at an infinite
place is the local degree, exactly as at a finite place.

## Main results

* `InverseGalois.CFT.subsingleton_tateHm1_infiniteUnits`: **Hilbert's theorem 90 at an infinite
  place**, that the lower Tate group of the units of the completion vanishes.
* `InverseGalois.CFT.card_tateHm1_infiniteUnits`: the same, read as an order.
* `InverseGalois.CFT.card_tateH0_infiniteUnits`: **the norm index at an infinite place is the local
  degree.**
* `InverseGalois.CFT.exists_normHom_infiniteUnits_eq_nsmul`: **every multiple of the local degree of
  an element of the completion fixed by the decomposition group is a local norm.**

## Tags

infinite place, norm index, Hilbert theorem 90, Tate cohomology, decomposition group
-/

namespace InverseGalois.CFT

open MulAction NumberField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K] (w : InfinitePlace K)
  [Finite ↥(stabilizer Gal(K/k) w)]
  {σ : ↥(stabilizer Gal(K/k) w)} (hgen : ∀ g : ↥(stabilizer Gal(K/k) w), g ∈ Subgroup.zpowers σ)
  {d : ℕ} (hcard : Nat.card ↥(stabilizer Gal(K/k) w) = d)

include hgen hcard

omit [IsGalois k K] in
/-- **Hilbert's theorem 90 at an infinite place.**  The decomposition group acts faithfully on the
completion, which is a field, so an element whose conjugates multiply to one is a quotient of an
element by its conjugate. -/
theorem subsingleton_tateHm1_infiniteUnits :
    Subsingleton (tateHm1 (smulUnitsAut (R := w.Completion) σ) d) :=
  ⟨fun x y => by
    rw [tateHm1_unitsSmulAut_eq_zero hgen hcard x, tateHm1_unitsSmulAut_eq_zero hgen hcard y]⟩

omit [IsGalois k K] in
/-- The lower Tate group of the units of the completion at an infinite place has order one. -/
theorem card_tateHm1_infiniteUnits :
    Nat.card (tateHm1 (smulUnitsAut (R := w.Completion) σ) d) = 1 :=
  haveI := subsingleton_tateHm1_infiniteUnits w hgen hcard
  Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- **The norm index at an infinite place is the local degree.**  The Herbrand quotient of the units
of the completion is the order of the decomposition group, and the denominator of that quotient is
one by Hilbert's theorem 90. -/
theorem card_tateH0_infiniteUnits :
    Nat.card (tateH0 (smulUnitsAut (R := w.Completion) σ) d) = d := by
  have hq := herbrand_infiniteUnits_eq_card w hgen hcard
  rw [herbrand, card_tateHm1_infiniteUnits w hgen hcard] at hq
  push_cast at hq
  rw [div_one] at hq
  exact_mod_cast hq

/-- **Every multiple of the local degree of an element of the completion fixed by the decomposition
group is a local norm.**  The norm index is the local degree, and the order of the zeroth Tate group
annihilates it. -/
theorem exists_normHom_infiniteUnits_eq_nsmul (x : Additive (w.Completion)ˣ)
    (hx : smulUnitsAut (R := w.Completion) σ x = x) {m : ℕ} (hm : d ∣ m) :
    ∃ y, normHom (smulUnitsAut (R := w.Completion) σ) d y = m • x :=
  exists_normHom_eq_nsmul x hx (by rwa [card_tateH0_infiniteUnits w hgen hcard])

end InverseGalois.CFT
