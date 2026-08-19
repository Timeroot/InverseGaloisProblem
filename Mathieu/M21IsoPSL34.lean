import Mathieu.PSL
import Mathieu.PSL34

/-!
# `M₂₁ ≅ PSL(3, 4)` — final assembly

This file combines the embedding `PSL(3, 4) ↪ M₂₁` (`PSL34.embeds`, built in `PSL34.lean` from
the projective-plane action of `SL(3, F4)`) with the equality of orders
`|M₂₁| = |PSL(3, 4)| = 20160` (`M21_card`, `PSL34_card`, in `PSL.lean`) to conclude that the two
groups are isomorphic.

It is kept separate from `PSL.lean` so that `PSL.lean` need not import the computable-field
groundwork (`F4.lean`, `ProjF4.lean`, `PSL34.lean`); the latter introduces a global
`Fintype (GaloisField 2 2)` instance that would otherwise perturb the fragile
`native_decide`/`+decide` cardinality proofs in `PSL.lean`.
-/

namespace Mathieu

open scoped MatrixGroups

/-- **`PSL(3,4) ↪ M₂₁`.** There is an injective homomorphism `PSL(3,4) → M₂₁`, coming from the
faithful action of `PSL(3,4)` on the `21` points of the projective plane `PG(2,4)`, whose image
is `M₂₁`.  See `PSL34.embeds`. -/
theorem PSL34_embeds_M21 :
    ∃ f : PSL(3, GaloisField 2 2) →* M21, Function.Injective f :=
  PSL34.embeds

/--
**`M₂₁ ≅ PSL(3,4)` — synthesis.** Given the embedding `PSL(3,4) ↪ M₂₁` and the equality of
orders `|M₂₁| = |PSL(3,4)| = 20160`, an injective homomorphism between finite groups of equal
cardinality is an isomorphism.
-/
theorem M21_iso_PSL34_of_embeds
    (h : ∃ f : PSL(3, GaloisField 2 2) →* M21, Function.Injective f) :
    Nonempty (M21 ≃* PSL(3, GaloisField 2 2)) := by
      revert h;
      intro h
      obtain ⟨f, hf_inj⟩ := h
      have hf_surj : Function.Surjective f := by
        have h_card : Nat.card (PSL(3, GaloisField 2 2)) = Nat.card M21 := by
          convert PSL34_card.trans M21_card.symm;
        have h_card_eq : Nat.card (Set.range f) = Nat.card M21 := by
          rw [ ← h_card, Nat.card_range_of_injective hf_inj ];
        have h_card_eq : Set.range f = Set.univ := by
          apply Set.eq_of_subset_of_ncard_le;
          · exact Set.subset_univ _;
          · simp_all +decide [ Set.ncard_univ ];
          · exact Set.toFinite _;
        exact Set.range_eq_univ.mp h_card_eq;
      exact ⟨ MulEquiv.symm <| MulEquiv.ofBijective f ⟨ hf_inj, hf_surj ⟩ ⟩

/-- **`M₂₁ ≅ PSL(3,4)`.** The Mathieu group `M₂₁` (the three-point stabiliser in `M₂₄`) is
isomorphic to the projective special linear group `PSL(3, 4)` over the field with four
elements. -/
theorem M21_iso_PSL34 :
    Nonempty (M21 ≃* PSL(3, GaloisField 2 2)) :=
  M21_iso_PSL34_of_embeds PSL34_embeds_M21

end Mathieu
