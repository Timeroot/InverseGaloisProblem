/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.PowIndex
import InverseGalois.CFT.PiIndex
import InverseGalois.CFT.Units.Idele

/-!
# The `n`-th powers inside the ideles of a set of places

Two subgroups of the ideles govern the counting argument behind the second inequality.  The larger
one is everything at the infinite places and at a distinguished finite set of places, and the units
of the valuation ring elsewhere.  The smaller one replaces "everything" by "the `n`-th powers" at
the infinite places and at part of that finite set, keeping "everything" at the rest of it.

The two subgroups are products of local subgroups which differ only at the places where `n`-th
powers were imposed, so their relative index is the product of the local indices of the `n`-th
powers there.  When the finite places carrying the `n`-th powers include all the places at which
`n` has absolute value different from one, and the base field contains a primitive `n`-th root of
unity, the product formula evaluates that product: it is `n` raised to twice the number of places
involved.

## Main definitions

* `InverseGalois.CFT.adicSIdele`: the local component at a finite place of the ideles of a set of
  places.
* `InverseGalois.CFT.adicPowSIdele`: the local component at a finite place of the subgroup carrying
  the `n`-th powers.
* `InverseGalois.CFT.sIdele`: **the ideles of a set of places**, as a subgroup of the product of the
  local unit groups.
* `InverseGalois.CFT.powSIdele`: **the subgroup carrying the `n`-th powers.**

## Main results

* `InverseGalois.CFT.relIndex_powSIdele`: **the relative index of the two subgroups** is the product
  of the local indices of the `n`-th powers.
* `InverseGalois.CFT.relIndex_powSIdele_of_isPrimitiveRoot`: **the same relative index when the base
  field contains a primitive `n`-th root of unity**, where it is `n` raised to twice the number of
  places involved.

## Tags

number field, idele, place, `n`-th power, relative index, product formula
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### The local components -/

section Local

variable {K : Type*} [Field K] [NumberField K]

/-- The `n`-th powers in the units of the completion at an infinite place, written additively. -/
noncomputable def infinitePow (n : ℕ) (w : InfinitePlace K) :
    AddSubgroup (Additive w.Completionˣ) :=
  Subgroup.toAddSubgroup (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range

/-- The local component at a finite place of the ideles of a set of places: everything at a place
of either set, and the units of the valuation ring elsewhere. -/
def adicSIdele (S T : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (v : HeightOneSpectrum (𝓞 K)) :
    AddSubgroup (Additive (v.adicCompletion K)ˣ) :=
  if v ∈ S then ⊤ else adicSUnits T v

/-- The local component at a finite place of the subgroup carrying the `n`-th powers: the `n`-th
powers at a place of the first set, everything at a place of the second, and the units of the
valuation ring elsewhere. -/
noncomputable def adicPowSIdele (n : ℕ) (S T : Set (HeightOneSpectrum (𝓞 K)))
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] (v : HeightOneSpectrum (𝓞 K)) :
    AddSubgroup (Additive (v.adicCompletion K)ˣ) :=
  if v ∈ S then
    Subgroup.toAddSubgroup (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
  else adicSUnits T v

variable (S T : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]

theorem adicSIdele_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : adicSIdele S T v = ⊤ :=
  if_pos hv

theorem adicSIdele_of_notMem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    adicSIdele S T v = adicSUnits T v :=
  if_neg hv

theorem adicPowSIdele_of_mem (n : ℕ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    adicPowSIdele n S T v = Subgroup.toAddSubgroup
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :=
  if_pos hv

theorem adicPowSIdele_of_notMem (n : ℕ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    adicPowSIdele n S T v = adicSUnits T v :=
  if_neg hv

end Local

/-! ### The two subgroups of the ideles -/

section Subgroups

variable {K : Type*} [Field K] [NumberField K] (S T : Set (HeightOneSpectrum (𝓞 K)))
  [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]

/-- **The ideles of a set of places**: everything at the infinite places and at the places of either
set, and the units of the valuation ring at every other finite place. -/
def sIdele : AddSubgroup (FullIdele K) :=
  (AddSubgroup.pi Set.univ fun _ : InfinitePlace K => ⊤).prod
    (AddSubgroup.pi Set.univ (adicSIdele S T))

/-- **The subgroup carrying the `n`-th powers**: the `n`-th powers at the infinite places and at the
places of the first set, everything at the places of the second, and the units of the valuation ring
at every other finite place. -/
noncomputable def powSIdele (n : ℕ) : AddSubgroup (FullIdele K) :=
  (AddSubgroup.pi Set.univ (infinitePow n)).prod
    (AddSubgroup.pi Set.univ (adicPowSIdele n S T))

end Subgroups

/-! ### The relative index -/

section RelIndex

variable {K : Type*} [Field K] [NumberField K] (S T : Set (HeightOneSpectrum (𝓞 K)))
  [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]

/-- **The relative index of the subgroup carrying the `n`-th powers** inside the ideles of the two
sets of places: the two agree away from the places where `n`-th powers were imposed, so the index is
the product of the local indices there. -/
theorem relIndex_powSIdele (n : ℕ) (F : Finset (HeightOneSpectrum (𝓞 K)))
    (hF : ∀ v, v ∈ F ↔ v ∈ S) :
    (powSIdele S T n).relIndex (sIdele S T)
      = (∏ w : InfinitePlace K,
          (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index)
        * ∏ v ∈ F, (powMonoidHom n :
          (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index := by
  rw [powSIdele, sIdele, relIndex_prod,
    relIndex_pi _ _ Finset.univ fun w hw => absurd (Finset.mem_univ w) hw,
    relIndex_pi _ _ F fun v hv => by
      rw [adicPowSIdele_of_notMem S T n fun h => hv ((hF v).mpr h),
        adicSIdele_of_notMem S T fun h => hv ((hF v).mpr h)]]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [AddSubgroup.relIndex_top_right, infinitePow, Subgroup.index_toAddSubgroup]
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [adicPowSIdele_of_mem S T n ((hF v).mp hv), adicSIdele_of_mem S T ((hF v).mp hv),
      AddSubgroup.relIndex_top_right, Subgroup.index_toAddSubgroup]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The relative index of the subgroup carrying the `n`-th powers when the base field contains a
primitive `n`-th root of unity** and the places carrying them include every place at which `n` has
absolute value different from one: it is `n` raised to twice the number of places involved. -/
theorem relIndex_powSIdele_of_isPrimitiveRoot {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (F : Finset (HeightOneSpectrum (𝓞 K)))
    (hF : ∀ v, v ∈ F ↔ v ∈ S)
    (hn : ∀ v, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ F) :
    (powSIdele S T n).relIndex (sIdele S T)
      = n ^ (2 * (Fintype.card (InfinitePlace K) + F.card)) := by
  rw [relIndex_powSIdele S T n F hF,
    prod_index_range_powMonoidHom_units_of_isPrimitiveRoot hζ F hn]

end RelIndex

end InverseGalois.CFT
