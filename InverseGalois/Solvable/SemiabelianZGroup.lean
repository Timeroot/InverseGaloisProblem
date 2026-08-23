/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Metacyclic
import InverseGalois.Solvable.SemiabelianCriterion

/-!
# Z-groups are semiabelian

A **Z-group** is a finite group all of whose Sylow subgroups are cyclic; Mathlib records this
condition as the class `IsZGroup`.  The classical theorem of Hölder, Burnside and Zassenhaus says
that such a group is metacyclic, and Mathlib proves the two halves of that statement separately:
`IsZGroup.isCyclic_commutator` gives that the derived subgroup `commutator G` is cyclic, while
`IsZGroup.isCyclic_abelianization` gives that the abelianization is cyclic.  Since the
abelianization is by definition the quotient of `G` by its derived subgroup, and the derived
subgroup is normal, the pair `(commutator G, G ⧸ commutator G)` exhibits `G` as an extension of a
cyclic group by a cyclic group.

That is exactly the input of `IsSemiabelian.of_isCyclic_of_isCyclic_quotient`, so every Z-group
lands in Dentzer's class of semiabelian groups.  Because a group of squarefree order has every
Sylow subgroup of prime order, this covers in particular all groups of squarefree order.

## Main results

* `IsZGroup.isCyclic_quotient_commutator` — the quotient of a finite Z-group by its derived
  subgroup is cyclic, the abelianization read as a quotient group.
* `IsSemiabelian.of_isZGroup` — **every finite Z-group is semiabelian**.
* `IsZGroup.exists_normal_isCyclic` — a finite Z-group is metacyclic: it has a normal cyclic
  subgroup with cyclic quotient.
* `IsSemiabelian.of_forall_sylow_isCyclic` — the same statement with the Sylow hypothesis spelled
  out rather than packaged as an instance.
* `IsSemiabelian.of_squarefree_card` — every finite group of squarefree order is semiabelian.
* `IsSemiabelian.subgroup_of_isZGroup` — every subgroup of a finite Z-group is semiabelian, the
  Sylow hypothesis being inherited by subgroups.
-/

/-- The quotient of a finite Z-group by its derived subgroup is cyclic.  This is Mathlib's
`IsZGroup.isCyclic_abelianization` transported along the definitional identification of
`Abelianization G` with the quotient group `G ⧸ commutator G`. -/
theorem IsZGroup.isCyclic_quotient_commutator (G : Type) [Group G] [Finite G] [IsZGroup G] :
    IsCyclic (G ⧸ commutator G) :=
  inferInstanceAs (IsCyclic (Abelianization G))

/-- **Every finite Z-group is semiabelian.**  The derived subgroup of a finite Z-group is cyclic
and the abelianization is cyclic, so the derived subgroup is a normal cyclic subgroup with cyclic
quotient, and a group with such a subgroup is semiabelian. -/
theorem IsSemiabelian.of_isZGroup (G : Type) [Group G] [Finite G] [IsZGroup G] :
    IsSemiabelian G :=
  haveI : IsCyclic (commutator G) := IsZGroup.isCyclic_commutator G
  haveI : IsCyclic (G ⧸ commutator G) := IsZGroup.isCyclic_quotient_commutator G
  IsSemiabelian.of_isCyclic_of_isCyclic_quotient (commutator G)

/-- **A finite Z-group is metacyclic**: the derived subgroup is a normal cyclic subgroup whose
quotient, the abelianization, is again cyclic. -/
theorem IsZGroup.exists_normal_isCyclic (G : Type) [Group G] [Finite G] [IsZGroup G] :
    ∃ N : Subgroup G, ∃ _ : N.Normal, IsCyclic ↥N ∧ IsCyclic (G ⧸ N) :=
  ⟨commutator G, inferInstance, IsZGroup.isCyclic_commutator G,
    IsZGroup.isCyclic_quotient_commutator G⟩

/-- **A finite group all of whose Sylow subgroups are cyclic is semiabelian.**  This is the
Sylow-level formulation of `IsSemiabelian.of_isZGroup`: the hypothesis is precisely the content of
the class `IsZGroup`. -/
theorem IsSemiabelian.of_forall_sylow_isCyclic (G : Type) [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic ↥P) : IsSemiabelian G :=
  haveI : IsZGroup G := ⟨h⟩
  IsSemiabelian.of_isZGroup G

/-- **Every finite group of squarefree order is semiabelian.**  A Sylow `p`-subgroup of such a
group has order dividing `p`, hence is cyclic, so the group is a Z-group. -/
theorem IsSemiabelian.of_squarefree_card (G : Type) [Group G] [Finite G]
    (h : Squarefree (Nat.card G)) : IsSemiabelian G :=
  haveI : IsZGroup G := IsZGroup.of_squarefree h
  IsSemiabelian.of_isZGroup G

/-- **Every subgroup of a finite Z-group is semiabelian.**  A Sylow subgroup of a subgroup `H`
embeds into a Sylow subgroup of the ambient group, so `H` is again a Z-group. -/
theorem IsSemiabelian.subgroup_of_isZGroup (G : Type) [Group G] [Finite G] [IsZGroup G]
    (H : Subgroup G) : IsSemiabelian ↥H :=
  IsSemiabelian.of_isZGroup ↥H
