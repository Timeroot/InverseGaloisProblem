/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedWeighted
import InverseGalois.CFT.Units.SUnitGens

/-!
# Counting the coefficients of the second reading

The coefficients left by reading a confined unit twice — once at the named places, once at every
place outside a finite set — have no order at the named places and none outside the finite set.
Their order is therefore carried by the part of the finite set which is not named, and they are
units for that part alone.

That part is the **correction room**: the places at which an element realising a prescribed reading
is allowed an uncontrolled order.  It is what has to be small.  The named places are only known
once the class to be counted is, and they may be many; but the correction room may be chosen apart
from them, and the number of generators of the coefficients is bounded by the number of generators
of the units of the ring of integers plus the number of places in the correction room.  So a bound
on the size of the correction room, which belongs to the field alone, fixes the size of the spanning
family a count consumes before the count begins.

## Main results

* `InverseGalois.CFT.confinedTToSUnits`: the coefficients of the second reading are units for the
  correction room.
* `InverseGalois.CFT.exists_fin_span_confinedTUnits`: **the coefficients of the second reading are
  spanned by a number of elements bounded by the size of the correction room.**

## Tags

number field, place, confined unit, S-unit, spanning family, generators
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

section Gens

variable {K : Type} [Field K] [NumberField K]
variable (n : ℕ) (Tz Y Xs T Aux : Set (HeightOneSpectrum (𝓞 K)))

/-- **A confined unit of order zero at the named places and outside the finite set is a unit for
the part of the finite set which is not named.**  At a place outside the finite set the second
reading kills the order; at a place of the finite set which is not in the correction room the first
reading does. -/
theorem coe_mem_sUnits_of_mem_confinedTUnits (hT : T ⊆ Xs ∪ Aux)
    (x : ↥(confinedTUnits n Tz Y Xs T)) :
    ((((x : ↥(confinedSUnits n Tz Y Xs)) : ↥(confinedUnits K n Tz Y)) : Kˣ)) ∈
      sUnits K Aux := by
  intro v hv
  by_cases hvT : v ∈ T
  · have hvXs : v ∈ Xs := by
      rcases hT hvT with h | h
      · exact h
      · exact absurd h hv
    exact (x : ↥(confinedSUnits n Tz Y Xs)).2 ⟨v, hvXs⟩
  · exact x.2 ⟨v, hvT⟩

/-- **The coefficients of the second reading are units for the correction room.** -/
def confinedTToSUnits (hT : T ⊆ Xs ∪ Aux) :
    ↥(confinedTUnits n Tz Y Xs T) →* ↥(sUnits K Aux) :=
  MonoidHom.codRestrict
    (((confinedUnits K n Tz Y).subtype.comp (confinedSUnits n Tz Y Xs).subtype).comp
      (confinedTUnits n Tz Y Xs T).subtype)
    (sUnits K Aux) (coe_mem_sUnits_of_mem_confinedTUnits n Tz Y Xs T Aux hT)

/-- **A coefficient of the second reading is determined by the unit it is.** -/
theorem confinedTToSUnits_injective (hT : T ⊆ Xs ∪ Aux) :
    Function.Injective (confinedTToSUnits n Tz Y Xs T Aux hT) := by
  intro x y h
  have h1 : ((confinedTToSUnits n Tz Y Xs T Aux hT x : ↥(sUnits K Aux)) : Kˣ)
      = ((confinedTToSUnits n Tz Y Xs T Aux hT y : ↥(sUnits K Aux)) : Kˣ) := by rw [h]
  exact Subtype.ext (Subtype.ext (Subtype.ext h1))

/-- **The coefficients of the second reading are spanned by a number of elements bounded by the
size of the correction room.**  The bound is the number of generators of the units of the ring of
integers plus a bound on the number of places of the correction room, and neither of those depends
on the named places. -/
theorem exists_fin_span_confinedTUnits (hAux : Aux.Finite) (hT : T ⊆ Xs ∪ Aux)
    {d₁ c : ℕ} (a : Fin d₁ → Additive (𝓞 K)ˣ) (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (hcard : Nat.card ↥Aux ≤ c) :
    ∃ b : Fin (d₁ + c) → Additive ↥(confinedTUnits n Tz Y Xs T),
      Submodule.span ℤ (Set.range b) = ⊤ := by
  obtain ⟨p, hp⟩ := exists_fin_span_sUnits_of_card_le Aux hAux a ha hcard
  refine exists_fin_span_of_injective p hp
    (MonoidHom.toAdditive (confinedTToSUnits n Tz Y Xs T Aux hT)) fun u w h => ?_
  have h2 : confinedTToSUnits n Tz Y Xs T Aux hT u.toMul
      = confinedTToSUnits n Tz Y Xs T Aux hT w.toMul := h
  exact Additive.toMul.injective (confinedTToSUnits_injective n Tz Y Xs T Aux hT h2)

end Gens

end InverseGalois.CFT
