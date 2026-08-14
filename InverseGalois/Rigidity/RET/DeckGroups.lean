/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.BranchSet
import InverseGalois.Rigidity.RET.SubUnramified
import InverseGalois.Rigidity.RET.ExistenceAbelian

/-!
# The groups that occur over a given branch locus

Which finite groups are deck groups of covers of the line branched inside a prescribed set of
points is a property of the group and the set, and it is worth naming: the covers themselves are
auxiliary, and the statements about them all read as closure properties of that class of groups.

The class grows with the set of allowed branch points, is invariant under isomorphism of groups,
and — the one statement with content — is closed under passing to quotients: the fixed field of a
normal subgroup of the deck group is a Galois subcover, its deck group is the quotient, and a
subcover branches only where the cover does.  Over at most two points the class consists of the
cyclic groups, and over `r + 1` points it contains every abelian group with `r` generators.

## Main results

* `Rigidity.RET.IsDeckGroupOver` — the class of finite groups occurring over a set of points.
* `Rigidity.RET.LineCover.exists_sub_mulEquiv_quotient` — a normal subgroup of the deck group is
  cut out by a Galois subcover whose deck group is the quotient.
* `Rigidity.RET.IsDeckGroupOver.quotient` — the class is closed under quotients.
* `Rigidity.RET.isDeckGroupOver_of_commGroup` — every finite abelian group with a product-one
  generating `r`-tuple occurs over `r` prescribed points.
* `Rigidity.RET.isCyclic_of_isDeckGroupOver` — over at most two points only cyclic groups occur.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-- **A finite group occurs over `S`** when it is the deck group of a cover of the line which is
unramified outside `S` and at infinity. -/
def IsDeckGroupOver (S : Set k) (G : Type) [Group G] [Finite G] : Prop :=
  ∃ L : LineCover, Nonempty (L.deck ≃* G) ∧ L.IsUnramifiedOutside S ∧ L.IsUnramifiedAtInfinity

/-- Allowing more branch points allows more groups. -/
theorem IsDeckGroupOver.mono {S T : Set k} (hST : S ⊆ T) {G : Type} [Group G] [Finite G]
    (h : IsDeckGroupOver S G) : IsDeckGroupOver T G := by
  obtain ⟨L, e, hout, hinf⟩ := h
  exact ⟨L, e, hout.mono hST, hinf⟩

/-- Occurring over a set of points depends only on the isomorphism type of the group. -/
theorem IsDeckGroupOver.congr {S : Set k} {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (h : IsDeckGroupOver S G) (φ : G ≃* H) : IsDeckGroupOver S H := by
  obtain ⟨L, ⟨e⟩, hout, hinf⟩ := h
  exact ⟨L, ⟨e.trans φ⟩, hout, hinf⟩

/-- The trivial group occurs over every set of points, on the trivial cover. -/
theorem isDeckGroupOver_of_subsingleton {S : Set k} {G : Type} [Group G] [Finite G]
    [Subsingleton G] : IsDeckGroupOver S G := by
  exact ⟨trivialCover, ⟨mulEquivOfSubsingleton⟩, trivialCover_isUnramifiedOutside S,
    trivialCover_isUnramifiedAtInfinity⟩

/-- **A normal subgroup of the deck group is cut out by a Galois subcover**, namely the fixed field
of the subgroup, whose own deck group is the quotient. -/
theorem LineCover.exists_sub_mulEquiv_quotient (L : LineCover) (N : Subgroup L.deck) [N.Normal] :
    ∃ (E : IntermediateField (RatFunc k) L.M) (_ : Normal (RatFunc k) E),
      Nonempty ((L.sub E).deck ≃* L.deck ⧸ N) := by
  haveI : Normal (RatFunc k) (IntermediateField.fixedField N) :=
    (IsGalois.of_fixedField_normal_subgroup (K := RatFunc k) (L := L.M) N).to_normal
  exact ⟨IntermediateField.fixedField N, inferInstance,
    ⟨(IsGalois.normalAutEquivQuotient (K := RatFunc k) (L := L.M) N).symm⟩⟩

/-- **The groups occurring over a set of points are closed under quotients.**  The quotient is the
deck group of the subcover cutting out the normal subgroup, and a subcover of a cover unramified
outside a set is again unramified outside that set. -/
theorem IsDeckGroupOver.quotient {S : Set k} {G : Type} [Group G] [Finite G]
    (h : IsDeckGroupOver S G) (N : Subgroup G) [N.Normal] : IsDeckGroupOver S (G ⧸ N) := by
  obtain ⟨L, ⟨e⟩, hout, hinf⟩ := h
  obtain ⟨E, hE, ⟨eq⟩⟩ := L.exists_sub_mulEquiv_quotient (N.comap (e : L.deck →* G))
  haveI := hE
  refine ⟨L.sub E, ⟨eq.trans (QuotientGroup.congr _ N e ?_)⟩, hout.sub E, hinf.sub E⟩
  exact Subgroup.map_comap_eq_self_of_surjective e.surjective N

/-- **Every finite abelian group with a product-one generating tuple over `r` points occurs over
those points** — the multi-point Kummer construction. -/
theorem isDeckGroupOver_of_commGroup {H : Type} [CommGroup H] [Finite H] {r : ℕ} (t : Fin r → k)
    (ht : Function.Injective t) (h : Fin r → H) (hprod : (List.ofFn h).prod = 1)
    (htop : Subgroup.closure (Set.range h) = ⊤) : IsDeckGroupOver (Set.range t) H := by
  obtain ⟨L, e, hout, hinf, -⟩ := exists_cover_of_commGroup t ht h hprod htop
  exact ⟨L, ⟨e⟩, hout, hinf⟩

/-- **Over at most two points only cyclic groups occur.** -/
theorem isCyclic_of_isDeckGroupOver {S : Set k} (hS : S.Finite) (hcard : hS.toFinset.card ≤ 2)
    {G : Type} [Group G] [Finite G] (h : IsDeckGroupOver S G) : IsCyclic G := by
  obtain ⟨L, ⟨e⟩, hout, hinf⟩ := h
  obtain ⟨t, -, hsub⟩ := exists_range_superset_of_card_le hS hcard
  haveI := LineCover.isCyclic_deck_of_unramifiedOutside_range_two L t (hout.mono hsub) hinf
  exact isCyclic_of_surjective (e : L.deck →* G) e.surjective

end Rigidity.RET
