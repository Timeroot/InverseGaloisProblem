/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Relative dimension of a pair of subspaces

Two subspaces of an infinite-dimensional space can be compared even when neither is
finite-dimensional, as long as one contains the other with a finite-dimensional gap between them.
The size of the gap is the *relative dimension*, and it behaves like a dimension should: it adds
along a chain, it is the difference of the dimensions when both spaces are finite-dimensional, and
it is the difference of the codimensions when both have finite codimension.

The one identity that is not formal is the diamond law: enlarging a subspace by a finite gap
enlarges its intersection with a third subspace and its join with that subspace by gaps whose sizes
add up to the original one.  It is the two isomorphism theorems, applied to the two halves of the
chain that runs from the small subspace up to the large one through their join with the third.

The diamond law is what makes the *Euler characteristic* of a pair of subspaces — their overlap
less the codimension of their join — behave: moving one of the two subspaces up by a finite gap
moves the Euler characteristic up by exactly the size of that gap, even though each of the two
terms separately may be infinite.

## Main definitions

* `Rigidity.RET.relrank` — the dimension of the gap between two subspaces.
* `Rigidity.RET.chi` — the Euler characteristic of a pair of subspaces.

## Main results

* `Rigidity.RET.relrank_trans` — the gap adds along a chain.
* `Rigidity.RET.relrank_add_finrank`, `Rigidity.RET.relrank_add_finrank_quotient` — the gap as a
  difference of dimensions, and as a difference of codimensions.
* `Rigidity.RET.relrank_inf_add_relrank_sup` — the diamond law.
* `Rigidity.RET.chi_of_le` — enlarging a subspace raises the Euler characteristic by the size of
  the enlargement.
-/

open Module Submodule

noncomputable section

namespace Rigidity.RET

variable {k : Type*} [Field k] {N : Type*} [AddCommGroup N] [Module k N]

/-- **The relative dimension of a pair of subspaces**: the dimension of the gap between `X` and
`Y`, computed as the dimension of the image of `Y` in the quotient by `X`.  For `X ≤ Y` this is the
dimension of `Y / X`. -/
def relrank (X Y : Submodule k N) : ℕ := finrank k ↥(Y.map X.mkQ)

/-! ## The gap as a quotient of the larger space -/

theorem ker_mkQ_comp_subtype (X Y : Submodule k N) :
    LinearMap.ker (X.mkQ ∘ₗ Y.subtype) = Submodule.comap Y.subtype X := by
  ext y
  simp [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero]

theorem range_mkQ_comp_subtype (X Y : Submodule k N) :
    LinearMap.range (X.mkQ ∘ₗ Y.subtype) = Y.map X.mkQ := by
  rw [LinearMap.range_comp, Submodule.range_subtype]

/-- The image of `Y` in the quotient by `X` is a quotient of `Y`. -/
def mapMkQEquiv (X Y : Submodule k N) :
    (↥Y ⧸ Submodule.comap Y.subtype X) ≃ₗ[k] ↥(Y.map X.mkQ) :=
  (Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_subtype X Y).symm).trans
    ((LinearMap.quotKerEquivRange (X.mkQ ∘ₗ Y.subtype)).trans
      (LinearEquiv.ofEq _ _ (range_mkQ_comp_subtype X Y)))

theorem relrank_eq_finrank_quotient (X Y : Submodule k N) :
    relrank X Y = finrank k (↥Y ⧸ Submodule.comap Y.subtype X) :=
  ((mapMkQEquiv X Y).finrank_eq).symm

theorem relrank_congr_left {X X' Y : Submodule k N}
    (h : Submodule.comap Y.subtype X = Submodule.comap Y.subtype X') :
    relrank X Y = relrank X' Y := by
  rw [relrank_eq_finrank_quotient, relrank_eq_finrank_quotient, h]

@[simp]
theorem relrank_self (X : Submodule k N) : relrank X X = 0 := by
  rw [relrank, Submodule.mkQ_map_self, finrank_bot]

/-! ## The gap as a difference of dimensions -/

theorem relrank_add_finrank {X Y : Submodule k N} (h : X ≤ Y) [FiniteDimensional k ↥Y] :
    relrank X Y + finrank k ↥X = finrank k ↥Y := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (X.mkQ ∘ₗ Y.subtype)
  rw [ker_mkQ_comp_subtype, range_mkQ_comp_subtype,
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq] at hrn
  exact hrn

theorem relrank_add_finrank_quotient {X Y : Submodule k N} (h : X ≤ Y)
    [FiniteDimensional k (N ⧸ X)] :
    relrank X Y + finrank k (N ⧸ Y) = finrank k (N ⧸ X) := by
  have hq := Submodule.finrank_quotient_add_finrank (Y.map X.mkQ)
  rwa [(Submodule.quotientQuotientEquivQuotient X Y h).finrank_eq, add_comm] at hq

/-! ## The gap adds along a chain -/

theorem ker_mapQ_id {X Y : Submodule k N} (hXY : X ≤ Y) :
    LinearMap.ker (Submodule.mapQ X Y LinearMap.id hXY) = Y.map X.mkQ := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    constructor
    · intro hz
      refine ⟨z, ?_, rfl⟩
      have : Submodule.Quotient.mk (p := Y) z = 0 := hz
      exact (Submodule.Quotient.mk_eq_zero Y).mp this
    · rintro ⟨w, hw, hwz⟩
      have hwz' : w - z ∈ X := by
        simpa using (Submodule.Quotient.eq X).mp (congrArg id hwz)
      have hzw : z - w ∈ X := by simpa using neg_mem hwz'
      show Submodule.Quotient.mk (p := Y) z = 0
      rw [Submodule.Quotient.mk_eq_zero]
      have hz : z = w + (z - w) := by abel
      rw [hz]
      exact Submodule.add_mem _ hw (hXY hzw)

theorem mapQ_id_comp_mkQ {X Y : Submodule k N} (hXY : X ≤ Y) :
    (Submodule.mapQ X Y LinearMap.id hXY) ∘ₗ X.mkQ = Y.mkQ := by
  ext z
  rfl

theorem map_mapQ_id {X Y : Submodule k N} (hXY : X ≤ Y) (Z : Submodule k N) :
    (Z.map X.mkQ).map (Submodule.mapQ X Y LinearMap.id hXY) = Z.map Y.mkQ := by
  rw [← Submodule.map_comp, mapQ_id_comp_mkQ hXY]

theorem relrank_trans {X Y Z : Submodule k N} (hXY : X ≤ Y) (hYZ : Y ≤ Z)
    [FiniteDimensional k ↥(Z.map X.mkQ)] :
    relrank X Z = relrank X Y + relrank Y Z := by
  set g := Submodule.mapQ X Y LinearMap.id hXY with hg
  set f : ↥(Z.map X.mkQ) →ₗ[k] N ⧸ Y := g ∘ₗ (Z.map X.mkQ).subtype with hf
  have hrange : LinearMap.range f = Z.map Y.mkQ := by
    rw [hf, LinearMap.range_comp, Submodule.range_subtype, hg, map_mapQ_id hXY]
  have hker : LinearMap.ker f = Submodule.comap (Z.map X.mkQ).subtype (Y.map X.mkQ) := by
    rw [hf, LinearMap.ker_comp, hg, ker_mapQ_id hXY]
  have hle : Y.map X.mkQ ≤ Z.map X.mkQ := Submodule.map_mono hYZ
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hrn
  rw [relrank, relrank, relrank, ← hrn, add_comm]

/-! ## The diamond law -/

theorem relrank_sup (X Y : Submodule k N) : relrank X (X ⊔ Y) = relrank (X ⊓ Y) Y := by
  have h₁ : relrank X (X ⊔ Y) = finrank k ↥(Y.map X.mkQ) := by
    rw [relrank, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  rw [h₁, ← relrank]
  exact relrank_congr_left
    (by rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq])

/-- **The diamond law**: the gap between `X` and `W` is split by a third subspace `Y` into the gap
between the two intersections and the gap between the two joins. -/
theorem relrank_inf_add_relrank_sup {X W : Submodule k N} (h : X ≤ W) (Y : Submodule k N)
    [FiniteDimensional k ↥(W.map X.mkQ)] :
    relrank X W = relrank (X ⊓ Y) (W ⊓ Y) + relrank (X ⊔ Y) (W ⊔ Y) := by
  have hmod : X ⊔ W ⊓ Y = W ⊓ (X ⊔ Y) := by
    rw [inf_comm W Y, ← sup_inf_assoc_of_le Y h, inf_comm]
  have hle₁ : X ≤ X ⊔ W ⊓ Y := le_sup_left
  have hle₂ : X ⊔ W ⊓ Y ≤ W := sup_le h inf_le_left
  rw [relrank_trans hle₁ hle₂]
  congr 1
  · rw [relrank_sup X (W ⊓ Y), ← inf_assoc, inf_eq_left.mpr h]
  · have h₂ := relrank_sup (X ⊔ Y) W
    have h₃ : (X ⊔ Y) ⊔ W = W ⊔ Y := by
      rw [sup_right_comm, sup_eq_right.mpr h]
    rw [h₃] at h₂
    rw [hmod, h₂, inf_comm]

/-! ## The Euler characteristic of a pair of subspaces -/

/-- **The Euler characteristic of a pair of subspaces**: how much they overlap, less how much of
the ambient space they fail to cover between them.  Neither term alone is stable under moving one
of the two subspaces by a finite amount, but the difference moves by exactly the amount of the
move. -/
def chi (Λ M : Submodule k N) : ℤ :=
  (finrank k ↥(Λ ⊓ M) : ℤ) - (finrank k (N ⧸ (Λ ⊔ M)) : ℤ)

theorem chi_comm (Λ M : Submodule k N) : chi Λ M = chi M Λ := by
  rw [chi, chi, inf_comm, sup_comm]

/-- **Enlarging one of the two subspaces raises the Euler characteristic by the size of the
enlargement.**  This is the additivity that makes the Euler characteristic computable: it can be
read off from any convenient pair, and transported to the pair of interest by measuring the gaps. -/
theorem chi_of_le {Λ W : Submodule k N} (h : Λ ≤ W) (M : Submodule k N)
    [FiniteDimensional k ↥(W.map Λ.mkQ)] [FiniteDimensional k ↥(W ⊓ M)]
    [FiniteDimensional k (N ⧸ (Λ ⊔ M))] :
    chi W M = chi Λ M + relrank Λ W := by
  have e₁ : relrank (Λ ⊓ M) (W ⊓ M) + finrank k ↥(Λ ⊓ M) = finrank k ↥(W ⊓ M) :=
    relrank_add_finrank (inf_le_inf_right M h)
  have e₂ : relrank (Λ ⊔ M) (W ⊔ M) + finrank k (N ⧸ (W ⊔ M)) = finrank k (N ⧸ (Λ ⊔ M)) :=
    relrank_add_finrank_quotient (sup_le_sup_right h M)
  have e₃ := relrank_inf_add_relrank_sup h M
  rw [chi, chi]
  omega

end Rigidity.RET
