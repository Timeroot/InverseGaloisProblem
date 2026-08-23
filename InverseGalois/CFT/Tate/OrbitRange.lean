/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.OrbitIndex
import InverseGalois.CFT.Units.EquivariantLabel

/-!
# The orbits met by the range of an equivariant injection

The finite places of a number field chosen to build the `S`-units are indexed by an abstract finite
set carrying an action of the Galois group, mapped equivariantly and injectively into the places.
The Herbrand quotient of the group of `S`-units is a product over the orbits of that abstract set,
while the Herbrand quotient of the ideles that are units outside those places is a product over the
orbits of places meeting the chosen set.  This file identifies the two index sets.

An injective equivariant map induces an injection on orbits, whose image consists of exactly the
orbits whose canonical representative lies in the range.  Along that identification a point of the
source and the canonical representative of the corresponding orbit lie in the same orbit and have
the same stabiliser, so the products of the orders of the stabilisers agree.

## Main definitions

* `InverseGalois.CFT.orbitMapOfEquivariant`: the map on orbits induced by an equivariant map.
* `InverseGalois.CFT.orbitRangeEquiv`: **the orbits of the source are the orbits of the target whose
  canonical representative lies in the range.**

## Main results

* `InverseGalois.CFT.prod_card_stabilizer_orbitRange`: **the two index sets give the same product of
  the orders of the stabilisers.**

## Tags

group action, orbit, equivariant map, stabiliser, S-unit, idele
-/

namespace InverseGalois.CFT

open MulAction

section OrbitRange

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y] {ι : Y → X}
  (hι : ∀ (g : G) (y : Y), ι (g • y) = g • ι y)

include hι

/-- The range of an equivariant map is invariant. -/
theorem smul_mem_range_iff (g : G) (x : X) : g • x ∈ Set.range ι ↔ x ∈ Set.range ι := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨g⁻¹ • y, by rw [hι, hy, inv_smul_smul]⟩
  · rintro ⟨y, hy⟩
    exact ⟨g • y, by rw [hι, hy]⟩

/-- **The map on orbits induced by an equivariant map.** -/
def orbitMapOfEquivariant : orbitRel.Quotient G Y → orbitRel.Quotient G X :=
  Quotient.map' ι fun a b h => by
    rw [orbitRel_apply] at h ⊢
    obtain ⟨g, hg⟩ := h
    exact ⟨g, (hι g b).symm.trans (congrArg ι hg)⟩

@[simp]
theorem orbitMapOfEquivariant_mk (y : Y) :
    orbitMapOfEquivariant hι (Quotient.mk'' y) = Quotient.mk'' (ι y) :=
  rfl

theorem orbitMapOfEquivariant_out (o : orbitRel.Quotient G Y) :
    orbitMapOfEquivariant hι o = Quotient.mk'' (ι o.out) := by
  conv_lhs => rw [← Quotient.out_eq' o]
  rfl

/-- The canonical representative of the image orbit lies in the orbit of the image of the canonical
representative. -/
theorem exists_smul_out_orbitMapOfEquivariant (o : orbitRel.Quotient G Y) :
    ∃ g : G, g • ι o.out = (orbitMapOfEquivariant hι o).out := by
  have h : (Quotient.mk'' (orbitMapOfEquivariant hι o).out : orbitRel.Quotient G X)
      = Quotient.mk'' (ι o.out) := by
    rw [Quotient.out_eq', orbitMapOfEquivariant_out]
  have h' := Quotient.exact' h
  rw [orbitRel_apply] at h'
  exact h'

theorem out_mem_range_orbitMapOfEquivariant (o : orbitRel.Quotient G Y) :
    (orbitMapOfEquivariant hι o).out ∈ Set.range ι := by
  obtain ⟨g, hg⟩ := exists_smul_out_orbitMapOfEquivariant hι o
  exact ⟨g • o.out, (hι g o.out).trans hg⟩

theorem orbitMapOfEquivariant_injective (hinj : Function.Injective ι) :
    Function.Injective (orbitMapOfEquivariant hι) := by
  refine Quotient.ind fun a => Quotient.ind fun b => fun h => ?_
  rw [orbitMapOfEquivariant_mk, orbitMapOfEquivariant_mk] at h
  have h' := Quotient.exact' h
  rw [orbitRel_apply] at h'
  obtain ⟨g, hg⟩ := h'
  refine Quotient.sound' (orbitRel_apply.mpr ⟨g, hinj ?_⟩)
  rw [hι]
  exact hg

theorem exists_orbitMapOfEquivariant_eq {ω : orbitRel.Quotient G X} (h : ω.out ∈ Set.range ι) :
    ∃ o : orbitRel.Quotient G Y, orbitMapOfEquivariant hι o = ω := by
  obtain ⟨y, hy⟩ := h
  exact ⟨Quotient.mk'' y, by rw [orbitMapOfEquivariant_mk, hy, Quotient.out_eq']⟩

/-- **The orbits of the source are the orbits of the target whose canonical representative lies in
the range** of an injective equivariant map. -/
noncomputable def orbitRangeEquiv (hinj : Function.Injective ι) :
    orbitRel.Quotient G Y ≃ {ω : orbitRel.Quotient G X // ω.out ∈ Set.range ι} :=
  Equiv.ofBijective
    (fun o => ⟨orbitMapOfEquivariant hι o, out_mem_range_orbitMapOfEquivariant hι o⟩)
    ⟨fun _ _ h => orbitMapOfEquivariant_injective hι hinj (congrArg Subtype.val h),
      fun ω => (exists_orbitMapOfEquivariant_eq hι ω.2).imp fun _ ho => Subtype.ext ho⟩

@[simp]
theorem coe_orbitRangeEquiv (hinj : Function.Injective ι) (o : orbitRel.Quotient G Y) :
    ((orbitRangeEquiv hι hinj o : {ω : orbitRel.Quotient G X // ω.out ∈ Set.range ι})
      : orbitRel.Quotient G X) = orbitMapOfEquivariant hι o :=
  rfl

/-- **The two index sets give the same product of the orders of the stabilisers.** -/
theorem prod_card_stabilizer_orbitRange (hinj : Function.Injective ι)
    [Fintype (orbitRel.Quotient G Y)]
    [Fintype {ω : orbitRel.Quotient G X // ω.out ∈ Set.range ι}] :
    ∏ ω : {ω : orbitRel.Quotient G X // ω.out ∈ Set.range ι},
        (Nat.card ↥(stabilizer G (ω : orbitRel.Quotient G X).out) : ℚ)
      = ∏ o : orbitRel.Quotient G Y, (Nat.card ↥(stabilizer G o.out) : ℚ) := by
  refine (Fintype.prod_equiv (orbitRangeEquiv hι hinj) _ _ fun o => ?_).symm
  obtain ⟨g, hg⟩ := exists_smul_out_orbitMapOfEquivariant hι o
  rw [← stabilizer_eq_of_equivariant hι hinj]
  refine congrArg Nat.cast (Nat.card_congr ?_)
  exact (stabilizerEquivStabilizer (a := ι o.out)
    (b := (orbitMapOfEquivariant hι o).out) (g := g) hg.symm).toEquiv

end OrbitRange

end InverseGalois.CFT
