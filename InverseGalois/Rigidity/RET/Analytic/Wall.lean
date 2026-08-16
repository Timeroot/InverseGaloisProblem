/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Separating
import InverseGalois.Rigidity.RET.Analytic.PunctureEquation
import InverseGalois.Rigidity.RET.Analytic.CoverAlgebraic

/-!
# One statement, and the existence direction follows

The two halves of the existence direction of the Riemann existence theorem are in place: a
generating product-one tuple in a finite group is the monodromy of a connected topological covering
of a punctured plane, and a covering carrying one holomorphic function of moderate growth which
separates the points of a fibre has a function field which is a Galois extension of `ℂ(T)` with the
deck group as Galois group.  Between them stands exactly one statement — that a covering of a
punctured plane carries such a function.

`Rigidity.RET.HasSeparatingFunctions` is that statement, named once, and
`Rigidity.RET.HasEnoughFunctions` is the weaker form of it that the passage to a Galois extension
really consumes: not one function separating a whole fibre, but one function moved by each
nontrivial deck transformation.  Granting the weaker one, every finite group is the Galois group of
an extension of `ℂ(T)` of the expected degree, branched over any prescribed points: the covering
comes from the topology and the extension from the covering.  The power covering shows the
statements are not vacuous (`RET/Analytic/Kummer.lean`).

## Main definitions

* `Rigidity.RET.HasSeparatingFunctions` — every covering of a punctured plane carries a function of
  moderate growth separating the points of a fibre.
* `Rigidity.RET.HasEnoughFunctions` — every nontrivial deck transformation of every such covering
  moves a function of moderate growth.

## Main results

* `Rigidity.RET.hasEnoughFunctions_of_hasSeparatingFunctions` — a separating function on every
  covering is more than is needed.
* `Rigidity.RET.exists_isGalois_ratFunc_of_prodOne` — granting it, a generating product-one tuple
  in a finite group is the Galois group of an extension of the rational functions of the plane.
* `Rigidity.RET.exists_prodOne_generating` — every finite group carries a generating product-one
  tuple.
* `Rigidity.RET.exists_isGalois_ratFunc` — granting it, every finite group is the Galois group of
  an extension of the rational functions of the plane, of degree its order.
-/

noncomputable section

namespace Rigidity.RET

/-- **Every covering of a punctured plane carries a separating function**: a holomorphic function
of moderate growth taking distinct values at the points of a fibre.

This is the one statement the existence direction of the Riemann existence theorem still asks of
the analysis; everything else about that direction — the covering, and the passage from the
covering to a Galois extension of the rational functions — is available without it. -/
def HasSeparatingFunctions : Prop :=
  ∀ (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (f : Y → ℂ) (hf : IsLocalHomeomorph f), Set.range f = (↑S : Set ℂ)ᶜ →
      ∀ (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]
        [IsOverBase H f], (∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) →
        HasSeparatingFunction hf S H

/-- **The functions of moderate growth on a covering of a punctured plane see its deck group**:
every nontrivial deck transformation of every such covering moves one of them.

This is what the existence direction actually consumes, and it is weaker than asking for one
function separating a whole fibre: the function is allowed to depend on the deck transformation,
and has only to be moved somewhere. -/
def HasEnoughFunctions : Prop :=
  ∀ (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (f : Y → ℂ) (hf : IsLocalHomeomorph f), Set.range f = (↑S : Set ℂ)ᶜ →
      ∀ (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]
        [IsOverBase H f], (∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) →
        ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y

/-- **A separating function on every covering is more than the existence direction needs.** -/
theorem hasEnoughFunctions_of_hasSeparatingFunctions (hwall : HasSeparatingFunctions) :
    HasEnoughFunctions := by
  intro S Y _ _ _ f hf hrange H _ _ _ _ _ htrans a ha
  exact separating_of_hasSeparatingFunction (hwall S Y f hf hrange H htrans) a ha

/-- **A generating product-one tuple in a finite group is the Galois group of an extension of the
rational functions of the plane**, granting that coverings carry separating functions.

The covering of the plane punctured at the prescribed points with the prescribed monodromy is a
theorem of covering-space theory, and the passage from a covering with a separating function to a
Galois extension of `ℂ(T)` is a theorem of the Galois correspondence for a covering; the hypothesis
is what joins them. -/
theorem exists_isGalois_ratFunc_of_prodOne (hwall : HasEnoughFunctions) (S : Finset ℂ)
    (pt : Fin S.card → ℂ) (hpt : Set.range pt = (S : Set ℂ)) {H : Type} [Group H] [Finite H]
    (h : Fin S.card → H) (hprod : (List.ofFn h).prod = 1)
    (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L),
      IsGalois (RatFunc ℂ) L ∧ Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        Module.finrank (RatFunc ℂ) L = Nat.card H := by
  classical
  obtain ⟨z₀, hz₀⟩ := Infinite.exists_notMem_finset S
  have hz₀' : z₀ ∈ ((S : Set ℂ))ᶜ := hz₀
  haveI : PathConnectedSpace ↥((S : Set ℂ))ᶜ :=
    pathConnectedSpace_punctured S.finite_toSet.countable
  obtain ⟨-, -, D, -, -, hcov, hconn, -, htrans, -, -⟩ :=
    exists_cover_of_prodOne_ordered S hz₀' pt hpt h hprod hgen
  haveI := hconn
  have hX : IsOpen ((S : Set ℂ))ᶜ := (S.finite_toSet.isClosed).isOpen_compl
  have hf : IsLocalHomeomorph D.projC := D.isLocalHomeomorph_projC hX hcov
  have hrange : Set.range D.projC = (↑S : Set ℂ)ᶜ := D.range_projC D.surjective_proj
  letI : MulAction H D.Total := MulAction.compHom D.Total D.deckHom
  haveI : ContinuousConstSMul H D.Total := ⟨fun a => D.continuous_deck a⁻¹⟩
  haveI : IsOverBase H D.projC := ⟨fun _ _ => rfl⟩
  have htrans' : ∀ y y' : D.Total, D.projC y = D.projC y' → ∃ b : H, y' = b • y := by
    intro y y' hyy
    obtain ⟨a, ha⟩ := htrans y y' (Subtype.coe_injective hyy)
    refine ⟨a⁻¹, ?_⟩
    show y' = D.deck a⁻¹⁻¹ y
    rw [inv_inv, ha]
  exact exists_isGalois_ratFunc_of_forall_ne hf hrange htrans'
    (hwall S D.Total D.projC hf hrange H htrans')

/-- **Every finite group carries a generating product-one tuple**: list the group, and append the
inverse of the product of the list. -/
theorem exists_prodOne_generating (H : Type) [Group H] [Finite H] :
    ∃ (m : ℕ) (g : Fin m → H), (List.ofFn g).prod = 1 ∧
      Subgroup.closure (Set.range g) = ⊤ := by
  classical
  set s : Fin (Nat.card H) → H := fun i => (Finite.equivFin H).symm i with hs
  refine ⟨Nat.card H + 1, Fin.snoc s ((List.ofFn s).prod)⁻¹, ?_, ?_⟩
  · rw [List.ofFn_succ', List.prod_concat]
    simp
  · refine eq_top_iff.mpr fun x _ => ?_
    exact Subgroup.subset_closure ⟨(Finite.equivFin H x).castSucc, by simp [hs]⟩

/-- **Every finite group is the Galois group of an extension of the rational functions of the
plane**, of degree its order, granting that coverings carry separating functions.

The branch points are `0, 1, …, n`, one more than the order of the group: the tuple of branch
cycles lists the group and closes up with the inverse of the product of the list. -/
theorem exists_isGalois_ratFunc (hwall : HasEnoughFunctions) (H : Type) [Group H] [Finite H] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L),
      IsGalois (RatFunc ℂ) L ∧ Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        Module.finrank (RatFunc ℂ) L = Nat.card H := by
  classical
  obtain ⟨m, g, hprod, hgen⟩ := exists_prodOne_generating H
  set S : Finset ℂ := (Finset.range m).image (fun j : ℕ => (j : ℂ)) with hS
  have hcard : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ (Nat.cast_injective (R := ℂ)), Finset.card_range]
  refine exists_isGalois_ratFunc_of_prodOne hwall S (fun i => ((i : ℕ) : ℂ)) ?_
    (fun i => g (Fin.cast hcard i)) ?_ ?_
  · ext z
    simp only [hS, Set.mem_range, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(i : ℕ), hcard ▸ i.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega⟩, rfl⟩
  · rw [← List.ofFn_congr hcard.symm g]
    exact hprod
  · refine eq_top_iff.mpr ?_
    rw [← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨Fin.cast hcard.symm i, by simp⟩

end Rigidity.RET

end
