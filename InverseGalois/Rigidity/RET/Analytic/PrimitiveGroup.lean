/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.PrimitiveElement
import InverseGalois.Rigidity.RET.Analytic.Wall

/-!
# Every finite group, granting the requirement, is presented by one equation over `ℂ(T)`

The requirement of `RET/Analytic/Wall.lean` asks of an arbitrary covering of a punctured plane only
that each nontrivial deck transformation move some function of moderate growth.  Granting it for
every covering at once, the primitive-element argument turns each covering into a monic polynomial
over the polynomials in the base coordinate, irreducible over `ℂ(T)`, of degree the order of the
deck group and with one root generating the function field.

Covering-space theory supplies the coverings: a generating product-one tuple in a finite group is
the monodromy of a covering of the plane punctured at prescribed points, and every finite group
carries such a tuple.  So every finite group is the Galois group of one explicit equation over
`ℂ(T)`.

## Main results

* `Rigidity.RET.exists_algebraic_model_primitive_of_hasEnoughFunctions` — granting the requirement,
  every covering of a punctured plane is cut out by a monic polynomial which is irreducible over
  `ℂ(T)` and generates its function field.
* `Rigidity.RET.exists_polynomial_isGalois_ratFunc_of_prodOne` — the same conclusion for the
  covering with prescribed monodromy.
* `Rigidity.RET.exists_polynomial_isGalois_ratFunc` — every finite group is the Galois group of a
  monic irreducible polynomial over `ℂ(T)` of degree its order.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open Analytic

section Main

/-- **Granting the requirement, every covering of a punctured plane is, away from finitely many
points of the base, the root variety of a monic polynomial of degree the order of its deck group,
irreducible over the rational functions of the base and generating the function field of the
covering.**

This is the requirement of `RET/Analytic/Wall.lean` read as a statement about equations: what it
asks of an arbitrary topological covering is that the covering carry a Galois extension of `ℂ(T)`
with the prescribed group, presented by a single equation. -/
theorem exists_algebraic_model_primitive_of_hasEnoughFunctions (hwall : HasEnoughFunctions)
    (S : Finset ℂ) (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (q : Y → ↥((S : Set ℂ)ᶜ)) (hq : IsCoveringMap q)
    (hf : IsLocalHomeomorph fun y => ((q y : ℂ)))
    (hrange : Set.range (fun y => ((q y : ℂ))) = (↑S : Set ℂ)ᶜ)
    (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y] [FaithfulSMul H Y]
    [IsOverBase H fun y => ((q y : ℂ))]
    (htrans : ∀ y y' : Y, (q y : ℂ) = (q y' : ℂ) → ∃ b : H, y' = b • y) :
    ∃ (P : Polynomial ℂ[X]) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧ P.natDegree = Nat.card H ∧
      (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
      (∃ Φ : ↥((fun y => ((q y : ℂ))) ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
        ∀ y, rootBase P S' (Φ y) = ((q (y : Y) : ℂ))) ∧
      Irreducible (P.map (algebraMap ℂ[X] (RatFunc ℂ))) ∧
      ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L), IsGalois (RatFunc ℂ) L ∧
        Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        ∃ α : L, aeval α (P.map (algebraMap ℂ[X] (RatFunc ℂ))) = 0 ∧
          IntermediateField.adjoin (RatFunc ℂ) {α} = ⊤ :=
  exists_algebraic_model_primitive (H := H) hf hrange htrans
    (hwall S Y q hq hf hrange H htrans)

/-- **A generating product-one tuple in a finite group is the Galois group of a monic irreducible
polynomial over the rational functions of the plane**, of degree the order of the group, granting
that coverings carry separating functions.

The covering of the plane punctured at the prescribed points with the prescribed monodromy is a
theorem of covering-space theory, and the passage from a covering with a separating function to a
polynomial presenting its function field is the primitive-element argument above; the hypothesis is
what joins them. -/
theorem exists_polynomial_isGalois_ratFunc_of_prodOne (hwall : HasEnoughFunctions) (S : Finset ℂ)
    (pt : Fin S.card → ℂ) (hpt : Set.range pt = (S : Set ℂ)) {H : Type} [Group H] [Finite H]
    (h : Fin S.card → H) (hprod : (List.ofFn h).prod = 1)
    (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ P : Polynomial ℂ[X], P.Monic ∧ P.natDegree = Nat.card H ∧
      Irreducible (P.map (algebraMap ℂ[X] (RatFunc ℂ))) ∧
      ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L), IsGalois (RatFunc ℂ) L ∧
        Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        ∃ α : L, aeval α (P.map (algebraMap ℂ[X] (RatFunc ℂ))) = 0 ∧
          IntermediateField.adjoin (RatFunc ℂ) {α} = ⊤ := by
  classical
  obtain ⟨z₀, hz₀⟩ := Infinite.exists_notMem_finset S
  have hz₀' : z₀ ∈ ((S : Set ℂ))ᶜ := hz₀
  haveI : PathConnectedSpace ↥((S : Set ℂ))ᶜ :=
    pathConnectedSpace_punctured S.finite_toSet.countable
  obtain ⟨-, -, D, -, -, hcov, hconn, hinj, htrans, -, -⟩ :=
    exists_cover_of_prodOne_ordered S hz₀' pt hpt h hprod hgen
  haveI := hconn
  have hX : IsOpen ((S : Set ℂ))ᶜ := (S.finite_toSet.isClosed).isOpen_compl
  have hf : IsLocalHomeomorph fun y => ((D.proj y : ℂ)) := D.isLocalHomeomorph_projC hX hcov
  have hrange : Set.range (fun y => ((D.proj y : ℂ))) = (↑S : Set ℂ)ᶜ :=
    D.range_projC D.surjective_proj
  letI : MulAction H D.Total := MulAction.compHom D.Total D.deckHom
  haveI : ContinuousConstSMul H D.Total := ⟨fun a => D.continuous_deck a⁻¹⟩
  haveI : FaithfulSMul H D.Total := ⟨fun {a b} hab => hinj (Equiv.ext hab)⟩
  haveI : IsOverBase H fun y => ((D.proj y : ℂ)) := ⟨fun _ _ => rfl⟩
  have htrans' : ∀ y y' : D.Total, (D.proj y : ℂ) = (D.proj y' : ℂ) → ∃ b : H, y' = b • y := by
    intro y y' hyy
    obtain ⟨a, ha⟩ := htrans y y' (Subtype.coe_injective hyy)
    refine ⟨a⁻¹, ?_⟩
    show y' = D.deck a⁻¹⁻¹ y
    rw [inv_inv, ha]
  exact exists_primitive_polynomial hf hrange htrans'
    (hwall S D.Total D.proj hcov hf hrange H htrans')

/-- **Every finite group is the Galois group of a monic irreducible polynomial over the rational
functions of the plane**, of degree its order and with a root generating the extension, granting
that coverings carry separating functions.

The branch points are `0, 1, …, n`, one more than the order of the group: the tuple of branch
cycles lists the group and closes up with the inverse of the product of the list. -/
theorem exists_polynomial_isGalois_ratFunc (hwall : HasEnoughFunctions) (H : Type) [Group H]
    [Finite H] :
    ∃ P : Polynomial ℂ[X], P.Monic ∧ P.natDegree = Nat.card H ∧
      Irreducible (P.map (algebraMap ℂ[X] (RatFunc ℂ))) ∧
      ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L), IsGalois (RatFunc ℂ) L ∧
        Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        ∃ α : L, aeval α (P.map (algebraMap ℂ[X] (RatFunc ℂ))) = 0 ∧
          IntermediateField.adjoin (RatFunc ℂ) {α} = ⊤ := by
  classical
  obtain ⟨m, g, hprod, hgen⟩ := exists_prodOne_generating H
  set S : Finset ℂ := (Finset.range m).image (fun j : ℕ => (j : ℂ)) with hS
  have hcard : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ (Nat.cast_injective (R := ℂ)), Finset.card_range]
  refine exists_polynomial_isGalois_ratFunc_of_prodOne hwall S (fun i => ((i : ℕ) : ℂ)) ?_
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

end Main

end Rigidity.RET

end
