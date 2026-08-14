/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Product
import InverseGalois.Rigidity.RET.MoveInfinity

/-!
# Moving a branch locus out of the way

The product construction wants the two branch loci to be disjoint, and nothing is lost by asking
for that: a cover can be translated along the line, carrying its branch locus with it, and two
finite sets of points can always be separated by a translation because the constant field is
infinite.  So the groups occurring over finite loci multiply with the number of branch points
merely adding.

## Main results

* `Rigidity.RET.IsDeckGroupOver.translate` — a group occurring over a locus occurs over any
  translate of that locus.
* `Rigidity.RET.exists_translate_disjoint` — two finite sets of points are made disjoint by a
  translation.
* `Rigidity.RET.IsDeckGroupOver.exists_prod` — the product of two groups occurring over finite
  loci occurs over a locus with at most as many points as the two together.
* `Rigidity.RET.IsAffineDeckGroup.prod_of_isDeckGroupOver` — the same count read on the affine
  line.
* `Rigidity.RET.IsAffineDeckGroup.prod` — counted on the affine line alone the branch points of a
  product add exactly, with nothing to pay for the point at infinity.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-- **A group occurring over a locus occurs over every translate of that locus**: translate the
cover, which changes neither its deck group nor its behaviour at infinity. -/
theorem IsDeckGroupOver.translate {S : Set k} (a : k) {G : Type} [Group G] [Finite G]
    (h : IsDeckGroupOver S G) : IsDeckGroupOver ((· - a) ⁻¹' S) G := by
  obtain ⟨L, ⟨e⟩, hout, hinf⟩ := h
  exact ⟨L.twist (translateSubst a),
    ⟨(Twist.autEquiv (φ := translateSubst a) (M := L.M)).symm.trans e⟩,
    LineCover.IsUnramifiedOutside.twist_translate a hout,
    LineCover.IsUnramifiedAtInfinity.twist_translate a hinf⟩

/-- The constant field is infinite. -/
instance : Infinite k :=
  Infinite.of_injective (algebraMap ℚ k) (algebraMap ℚ k).injective

/-- **Two finite sets of points are made disjoint by a translation**: the translations to avoid
are the finitely many differences of a point of one from a point of the other. -/
theorem exists_translate_disjoint {S₁ S₂ : Set k} (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) :
    ∃ a : k, Disjoint S₁ ((· - a) ⁻¹' S₂) := by
  have hbad : (Set.image2 (fun s₁ s₂ : k => s₁ - s₂) S₁ S₂).Finite := hS₁.image2 _ hS₂
  obtain ⟨a, ha⟩ := hbad.infinite_compl.nonempty
  refine ⟨a, Set.disjoint_left.2 fun x hx₁ hx₂ => ha ?_⟩
  exact ⟨x, hx₁, x - a, hx₂, sub_sub_cancel x a⟩

/-- A translate of a set of points has as many points as the set. -/
theorem ncard_preimage_sub (S : Set k) (a : k) : ((· - a) ⁻¹' S).ncard = S.ncard := by
  have himg : ((· - a) ⁻¹' S : Set k) = (· + a) '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨x - a, hx, sub_add_cancel x a⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [himg, Set.ncard_image_of_injective S (add_left_injective a)]

/-- A translate of a finite set of points is finite. -/
theorem finite_preimage_sub {S : Set k} (hS : S.Finite) (a : k) : ((· - a) ⁻¹' S).Finite :=
  Set.Finite.preimage (fun _ _ _ _ h => sub_left_inj.mp h) hS

/-- **The groups occurring over finite loci multiply, and the branch points merely add.**  One of
the two loci is translated out of the way of the other, which changes neither the group it carries
nor the number of its points, and the two disjoint loci are then joined. -/
theorem IsDeckGroupOver.exists_prod {S₁ S₂ : Set k} (hS₁ : S₁.Finite) (hS₂ : S₂.Finite)
    {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (h₁ : IsDeckGroupOver S₁ G₁) (h₂ : IsDeckGroupOver S₂ G₂) :
    ∃ S : Set k, S.Finite ∧ S.ncard ≤ S₁.ncard + S₂.ncard ∧ IsDeckGroupOver S (G₁ × G₂) := by
  obtain ⟨a, ha⟩ := exists_translate_disjoint hS₁ hS₂
  refine ⟨S₁ ∪ (· - a) ⁻¹' S₂, hS₁.union (finite_preimage_sub hS₂ a), ?_,
    h₁.prod ha (h₂.translate a)⟩
  calc (S₁ ∪ (· - a) ⁻¹' S₂).ncard ≤ S₁.ncard + ((· - a) ⁻¹' S₂).ncard := Set.ncard_union_le _ _
    _ = S₁.ncard + S₂.ncard := by rw [ncard_preimage_sub]

/-- **The product count on the affine line.** -/
theorem IsAffineDeckGroup.prod_of_isDeckGroupOver {S₁ S₂ : Set k} (hS₁ : S₁.Finite)
    (hS₂ : S₂.Finite) {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (h₁ : IsDeckGroupOver S₁ G₁) (h₂ : IsDeckGroupOver S₂ G₂) :
    IsAffineDeckGroup (S₁.ncard + S₂.ncard) (G₁ × G₂) := by
  obtain ⟨S, hS, hcard, hG⟩ := IsDeckGroupOver.exists_prod hS₁ hS₂ h₁ h₂
  refine IsAffineDeckGroup.mono ?_ (hG.isAffineDeckGroup hS)
  rwa [← Set.ncard_eq_toFinset_card _ hS]

/-! ### Counting on the affine line alone -/

namespace LineCover

attribute [local instance] sub_isGalois

/-- **Two subcovers branching over disjoint sets of points meet in the line alone.**  Nothing is
asked at infinity: a subcover of both branches nowhere on the line, and a cover of the line with
no branch point is trivial. -/
theorem inf_eq_bot_of_disjoint' (L : LineCover) (A B : IntermediateField (RatFunc k) L.M)
    [Normal (RatFunc k) A] [Normal (RatFunc k) B] {S₁ S₂ : Set k} (hdisj : Disjoint S₁ S₂)
    (hA : (L.sub A).IsUnramifiedOutside S₁) (hB : (L.sub B).IsUnramifiedOutside S₂) :
    A ⊓ B = ⊥ := by
  have hD₁ : (L.sub (A ⊓ B)).IsUnramifiedOutside S₁ :=
    IsUnramifiedOutside.sub_of_le
      (inf_le_left : (A ⊓ B : IntermediateField (RatFunc k) L.M) ≤ A) hA
  have hD₂ : (L.sub (A ⊓ B)).IsUnramifiedOutside S₂ :=
    IsUnramifiedOutside.sub_of_le
      (inf_le_right : (A ⊓ B : IntermediateField (RatFunc k) L.M) ≤ B) hB
  have hout : (L.sub (A ⊓ B)).IsUnramifiedOutside (∅ : Set k) := by
    intro t _ σ hσ
    by_cases ht : t ∈ S₁
    · exact hD₂ t (fun h2 => Set.disjoint_left.mp hdisj ht h2) σ hσ
    · exact hD₁ t ht σ hσ
  haveI hsub : Subsingleton (L.sub (A ⊓ B)).deck :=
    subsingleton_deck_of_unramifiedOutside_empty (L.sub (A ⊓ B)) hout
  have hcard : Nat.card ((A ⊓ B : IntermediateField (RatFunc k) L.M) ≃ₐ[RatFunc k]
      ((A ⊓ B : IntermediateField (RatFunc k) L.M) : Type)) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
  rw [IsGalois.card_aut_eq_finrank (RatFunc k)
    ((A ⊓ B : IntermediateField (RatFunc k) L.M) : Type)] at hcard
  exact IntermediateField.finrank_eq_one_iff.mp hcard

/-- A translated cover branches at the translates of the branch points. -/
theorem branchLocus_twist_translate_subset (L : LineCover) (a : k) :
    (L.twist (translateSubst a)).branchLocus ⊆ (· - a) ⁻¹' L.branchLocus :=
  (((L.twist (translateSubst a)).isUnramifiedOutside_iff_branchLocus_subset _).mp
    (IsUnramifiedOutside.twist_translate a L.isUnramifiedOutside_branchLocus))

end LineCover

/-- **The affine branch points of a product add.**  One cover is translated clear of the other and
the two are placed in their compositum, where they generate and, branching over disjoint sets of
points, meet in the line alone; the compositum then branches only where one of the two does.
Nothing is paid for the point at infinity, and against the Kummer construction the count is sharp:
an abelian group needs exactly as many affine branch points as it needs generators. -/
theorem IsAffineDeckGroup.prod {m n : ℕ} {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂]
    [Finite G₂] (h₁ : IsAffineDeckGroup m G₁) (h₂ : IsAffineDeckGroup n G₂) :
    IsAffineDeckGroup (m + n) (G₁ × G₂) := by
  obtain ⟨L₁, ⟨e₁⟩, hc₁⟩ := h₁
  obtain ⟨L₂, ⟨e₂⟩, hc₂⟩ := h₂
  obtain ⟨a, ha⟩ := exists_translate_disjoint L₁.finite_branchLocus L₂.finite_branchLocus
  set L₂' : LineCover := L₂.twist (translateSubst a) with hL₂'
  have hout₁ : L₁.IsUnramifiedOutside L₁.branchLocus := L₁.isUnramifiedOutside_branchLocus
  have hout₂ : L₂'.IsUnramifiedOutside ((· - a) ⁻¹' L₂.branchLocus) :=
    LineCover.IsUnramifiedOutside.twist_translate a L₂.isUnramifiedOutside_branchLocus
  have hA : ((L₁.compositum L₂').sub (L₁.compositumLeft L₂')).IsUnramifiedOutside
      L₁.branchLocus :=
    LineCover.IsUnramifiedOutside.transport (L := L₁)
      (L' := (L₁.compositum L₂').sub (L₁.compositumLeft L₂'))
      (L₁.compositumLeftEquiv L₂').symm hout₁
  have hB : ((L₁.compositum L₂').sub (L₁.compositumRight L₂')).IsUnramifiedOutside
      ((· - a) ⁻¹' L₂.branchLocus) :=
    LineCover.IsUnramifiedOutside.transport (L := L₂')
      (L' := (L₁.compositum L₂').sub (L₁.compositumRight L₂'))
      (L₁.compositumRightEquiv L₂').symm hout₂
  have hsup := L₁.compositumLeft_sup_compositumRight L₂'
  have hbot := LineCover.inf_eq_bot_of_disjoint' (L₁.compositum L₂') (L₁.compositumLeft L₂')
    (L₁.compositumRight L₂') ha hA hB
  obtain ⟨e⟩ := LineCover.nonempty_deck_mulEquiv_prod (L₁.compositum L₂')
    (L₁.compositumLeft L₂') (L₁.compositumRight L₂') hsup hbot
  refine ⟨L₁.compositum L₂', ⟨e.trans (MulEquiv.prodCongr
    ((AlgEquiv.autCongr (L₁.compositumLeftEquiv L₂')).trans e₁)
    ((AlgEquiv.autCongr (L₁.compositumRightEquiv L₂')).trans
      ((Twist.autEquiv (φ := translateSubst a) (M := L₂.M)).symm.trans e₂)))⟩, ?_⟩
  have hsub : (L₁.compositum L₂').branchLocus ⊆ L₁.branchLocus ∪ (· - a) ⁻¹' L₂.branchLocus :=
    ((L₁.compositum L₂').isUnramifiedOutside_iff_branchLocus_subset _).mp
      (LineCover.IsUnramifiedOutside.of_sup hsup hA hB)
  have hfin : (L₁.branchLocus ∪ (· - a) ⁻¹' L₂.branchLocus).Finite :=
    L₁.finite_branchLocus.union (finite_preimage_sub L₂.finite_branchLocus a)
  calc (L₁.compositum L₂').branchLocus.ncard
      ≤ (L₁.branchLocus ∪ (· - a) ⁻¹' L₂.branchLocus).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ L₁.branchLocus.ncard + ((· - a) ⁻¹' L₂.branchLocus).ncard := Set.ncard_union_le _ _
    _ ≤ m + n := by
        rw [ncard_preimage_sub]
        exact Nat.add_le_add hc₁ hc₂

end Rigidity.RET
