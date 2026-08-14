/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Compositum
import InverseGalois.Rigidity.RET.SubcoverBranch

/-!
# Products of deck groups over disjoint branch loci

Two covers of the line are placed inside their compositum, where they sit as normal subcovers
generating it.  Each is branched inside its own locus, so a subcover of both is branched inside
each; the loci being disjoint, it is branched nowhere and hence trivial, which is exactly the
linear disjointness that makes the deck group of the compositum the product of the two deck groups.
The compositum itself is branched inside the union of the two loci, so the class of groups
occurring over a branch locus is closed under direct products, at the cost of joining the loci.

## Main results

* `Rigidity.RET.IsDeckGroupOver.prod` — the groups occurring over disjoint loci multiply: `G₁`
  over `S₁` and `G₂` over `S₂` give `G₁ × G₂` over `S₁ ∪ S₂`.
-/

open Polynomial IntermediateField

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

attribute [local instance] LineCover.sub_isGalois

/-- **The groups occurring over disjoint branch loci multiply.**  Two covers are placed inside
their compositum, where they generate and — the branch loci being disjoint — meet in the base
field, so the deck group of the compositum is the product of the two deck groups, and the
compositum branches inside the union of the two loci. -/
theorem IsDeckGroupOver.prod {S₁ S₂ : Set k} (hdisj : Disjoint S₁ S₂) {G₁ G₂ : Type}
    [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (h₁ : IsDeckGroupOver S₁ G₁) (h₂ : IsDeckGroupOver S₂ G₂) :
    IsDeckGroupOver (S₁ ∪ S₂) (G₁ × G₂) := by
  obtain ⟨L₁, ⟨d₁⟩, hout₁, hinf₁⟩ := h₁
  obtain ⟨L₂, ⟨d₂⟩, hout₂, hinf₂⟩ := h₂
  have hA : ((L₁.compositum L₂).sub (L₁.compositumLeft L₂)).IsUnramifiedOutside S₁ :=
    LineCover.IsUnramifiedOutside.transport (L := L₁)
      (L' := (L₁.compositum L₂).sub (L₁.compositumLeft L₂))
      (L₁.compositumLeftEquiv L₂).symm hout₁
  have hB : ((L₁.compositum L₂).sub (L₁.compositumRight L₂)).IsUnramifiedOutside S₂ :=
    LineCover.IsUnramifiedOutside.transport (L := L₂)
      (L' := (L₁.compositum L₂).sub (L₁.compositumRight L₂))
      (L₁.compositumRightEquiv L₂).symm hout₂
  have hAi : ((L₁.compositum L₂).sub (L₁.compositumLeft L₂)).IsUnramifiedAtInfinity :=
    LineCover.IsUnramifiedAtInfinity.transport (L := L₁)
      (L' := (L₁.compositum L₂).sub (L₁.compositumLeft L₂))
      (L₁.compositumLeftEquiv L₂).symm hinf₁
  have hBi : ((L₁.compositum L₂).sub (L₁.compositumRight L₂)).IsUnramifiedAtInfinity :=
    LineCover.IsUnramifiedAtInfinity.transport (L := L₂)
      (L' := (L₁.compositum L₂).sub (L₁.compositumRight L₂))
      (L₁.compositumRightEquiv L₂).symm hinf₂
  have hsup := L₁.compositumLeft_sup_compositumRight L₂
  have hbot := LineCover.inf_eq_bot_of_disjoint (L₁.compositum L₂) (L₁.compositumLeft L₂)
    (L₁.compositumRight L₂) hdisj hA hAi hB
  obtain ⟨e⟩ := LineCover.nonempty_deck_mulEquiv_prod (L₁.compositum L₂)
    (L₁.compositumLeft L₂) (L₁.compositumRight L₂) hsup hbot
  refine ⟨L₁.compositum L₂, ⟨e.trans (MulEquiv.prodCongr
    ((AlgEquiv.autCongr (L₁.compositumLeftEquiv L₂)).trans d₁)
    ((AlgEquiv.autCongr (L₁.compositumRightEquiv L₂)).trans d₂))⟩,
    LineCover.IsUnramifiedOutside.of_sup hsup hA hB,
    LineCover.IsUnramifiedAtInfinity.of_sup hsup hAi hBi⟩

end Rigidity.RET
