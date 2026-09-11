/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Corestriction
import InverseGalois.CFT.Profinite.Symbol

/-!
# The second cohomology of a finite group is seen on a Sylow subgroup

Corestriction after restriction raises a class of the second cohomology to the index of the
subgroup, so a class which dies on a subgroup is killed by that index.  Coefficients killed by a
number kill the cohomology by the same number.  When the index and that number are coprime the two
together leave nothing, and for a Sylow subgroup of a finite group the index is prime to the prime
by definition.  So a group whose second cohomology vanishes on one Sylow subgroup, with coefficients
killed by a power of that prime, has no second cohomology at all.

The corestriction needs a transversal and needs the cochains it produces to stay smooth, which asks
of the subgroup that every subgroup open and normal in it contain one open and normal in the whole
group.  On a discrete group that is free: the normal core of the image of such a subgroup is open
because everything is, it is normal because a normal core is, and it lies inside the subgroup one
started from.

## Main results

* `InverseGalois.CFT.hasOpenNormalCore_of_discreteTopology`: every subgroup of a discrete group has
  an open normal core.
* `InverseGalois.CFT.subsingleton_smoothH2_of_index_coprime`: **a finite discrete group whose second
  cohomology vanishes on a subgroup of index prime to a number killing the coefficients has no
  second cohomology.**
* `InverseGalois.CFT.subsingleton_smoothH2_of_sylow`: **the same for a Sylow subgroup and
  coefficients killed by a power of that prime.**

## Tags

group cohomology, corestriction, Sylow subgroup, discrete group, transfer
-/

namespace InverseGalois.CFT

section Core

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- **Every subgroup of a discrete group has an open normal core.**  Push a subgroup open and normal
in the subgroup forward into the whole group and take its normal core: it is normal because a normal
core is, open because every set of a discrete group is, and contained in the subgroup one started
from. -/
theorem hasOpenNormalCore_of_discreteTopology (H : Subgroup G) : HasOpenNormalCore H := by
  intro N' _
  have hle : (N'.map H.subtype : Subgroup G) ≤ H := by
    rintro g hg
    obtain ⟨m, _, rfl⟩ := Subgroup.mem_map.1 hg
    exact m.2
  refine ⟨(N'.map H.subtype).normalCore, ⟨Subgroup.normalCore_normal _, isOpen_discrete _⟩,
    le_trans (Subgroup.normalCore_le _) hle, fun n hn => ?_⟩
  obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.1 (Subgroup.normalCore_le _ hn)
  exact Subtype.ext hmn ▸ hm

end Core

/-! ### Vanishing seen on a subgroup of coprime index -/

section Sylow

variable {G : Type*} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- **A finite discrete group whose second cohomology vanishes on a subgroup of index prime to a
number killing the coefficients has no second cohomology.**  A class which dies on the subgroup is
raised to the index by corestriction after restriction, and it is killed by the number that kills
the coefficients; the two being coprime, its order is one. -/
theorem subsingleton_smoothH2_of_index_coprime (H : Subgroup G) {n : ℕ}
    (hM : ∀ m : M, m ^ n = 1) (hcop : Nat.Coprime H.index n)
    (h : Subsingleton (SmoothH2 ↥H M)) : Subsingleton (SmoothH2 G M) := by
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : H.index = Fintype.card (G ⧸ H) := Nat.card_eq_fintype_card
  rw [hcard] at hcop
  have hout : ∀ x : G ⧸ H, ((Quotient.out x : G) : G ⧸ H) = x := fun x => Quotient.out_eq x
  have key : ∀ c : SmoothH2 G M, c = 1 := by
    intro c
    have hind : c ^ Fintype.card (G ⧸ H) = 1 := by
      rw [← corH2_resH2 H Quotient.out hout (hasOpenNormalCore_of_discreteTopology H) c,
        h.elim (resH2 H c) 1, _root_.map_one]
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hind)
      (orderOf_dvd_of_pow_eq_one (smoothH2_pow_eq_one hM c)))
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- **A finite discrete group whose second cohomology vanishes on a Sylow subgroup has no second
cohomology**, for coefficients killed by a power of that prime.  The index of a Sylow subgroup is
prime to the prime, so it is coprime to any power of it. -/
theorem subsingleton_smoothH2_of_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G) {j : ℕ}
    (hM : ∀ m : M, m ^ p ^ j = 1)
    (h : Subsingleton (SmoothH2 ↥(P : Subgroup G) M)) : Subsingleton (SmoothH2 G M) :=
  subsingleton_smoothH2_of_index_coprime (P : Subgroup G) hM
    (((Nat.Prime.coprime_iff_not_dvd Fact.out).2 P.not_dvd_index).symm.pow_right j) h

end Sylow

end InverseGalois.CFT
