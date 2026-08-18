/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.AlgebraicModel
import InverseGalois.Rigidity.RET.Analytic.GenericSeparation
import InverseGalois.Rigidity.RET.Analytic.Wall

/-!
# What the requirement asks is that coverings are cut out by equations

The requirement of `RET/Analytic/Wall.lean` asks, of an arbitrary covering of a punctured plane
with a faithful transitive finite deck group, only that each nontrivial deck transformation move
some function of moderate growth.  That apparently modest demand already forces the covering to be
algebraic.

Three steps assemble the conclusion.  Functions moving the deck transformations one at a time
combine into a single function separating the points of one fibre
(`RET.hasSeparatingFunction_of_forall_ne`); a function separating one fibre separates every fibre
over the complement of a finite set (`RET.exists_finset_separating`); and a function separating
those fibres identifies the covering above them with the root variety of a monic equation
(`RET.exists_algebraic_model`).

In the other direction a covering cut out by an equation carries the functions the requirement asks
for, and so does any covering homeomorphic over the plane to one
(`RET.exists_ne_of_homeo_rootTotal`).  The two directions are not quite inverse: the algebraization
discards finitely many further points of the base, at which the equation found may degenerate even
though the covering does not.

## Main results

* `Rigidity.RET.exists_algebraic_model_of_forall_ne` — a connected covering whose functions of
  moderate growth see its deck group is the root variety of a monic equation away from finitely
  many points of the base.
* `Rigidity.RET.exists_algebraic_model_of_hasEnoughFunctions` — the same for every covering at
  once, granting the requirement.
-/

open Polynomial Topology

noncomputable section

namespace Rigidity.RET

open Analytic

section Algebraize

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
  {S : Finset ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]
  [IsOverBase H f]

/-- **A connected covering of a punctured plane whose functions of moderate growth see its deck
group is cut out by a monic equation, away from finitely many points of the base.**

The functions that move the deck transformations one at a time combine into a single function
separating the points of one fibre; the product of the differences of its values along a fibre is
an invariant function of moderate growth, hence a rational function of the base coordinate, so it
vanishes over only finitely many points and the function separates every other fibre; and a
separating function of moderate growth, multiplied by the leading coefficient of the equation it
satisfies, gives the covering as the root variety of a monic equation. -/
theorem exists_algebraic_model_of_forall_ne (hf : IsLocalHomeomorph f)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ c : H, y' = c • y)
    (hrange : Set.range f = ((S : Set ℂ))ᶜ)
    (hne : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    ∃ (P : Polynomial (Polynomial ℂ)) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧
      P.natDegree = Nat.card H ∧ (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
      ∃ Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
        ∀ y, rootBase P S' (Φ y) = f (y : Y) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨F, hF, y₀, hinj⟩ := hasSeparatingFunction_of_forall_ne (H := H) hf hne
  have hne' : ∀ c : H, c ≠ 1 → ∃ y : Y, F (c • y) ≠ F y := fun c hc =>
    ⟨y₀, fun h => hc (hinj c 1 (by simpa using h))⟩
  obtain ⟨S₁, hS₁, hsep⟩ := exists_finset_separating (H := H) hf htrans hrange hF hne'
  obtain ⟨P, hP, hdeg, hsepz, Φ, hcomm⟩ :=
    exists_algebraic_model (H := H) hf htrans hrange hS₁ hF hsep
  exact ⟨P, S₁, hS₁, hP, by rw [hdeg, Nat.card_eq_fintype_card], hsepz, Φ, hcomm⟩

end Algebraize

/-- **Granting the requirement, every covering of a punctured plane is cut out by a monic equation
away from finitely many points of the base.**

This is the converse of the transport of functions of moderate growth along a homeomorphism over
the plane: what the requirement asks of an arbitrary topological covering is that the covering be
algebraic. -/
theorem exists_algebraic_model_of_hasEnoughFunctions (hwall : HasEnoughFunctions) (S : Finset ℂ)
    (Y : Type) [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y]
    (q : Y → ↥((S : Set ℂ)ᶜ)) (hq : IsCoveringMap q)
    (hf : IsLocalHomeomorph fun y => ((q y : ℂ)))
    (hrange : Set.range (fun y => ((q y : ℂ))) = (↑S : Set ℂ)ᶜ)
    (H : Type) [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y] [FaithfulSMul H Y]
    [IsOverBase H fun y => ((q y : ℂ))]
    (htrans : ∀ y y' : Y, (q y : ℂ) = (q y' : ℂ) → ∃ b : H, y' = b • y) :
    ∃ (P : Polynomial (Polynomial ℂ)) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧
      P.natDegree = Nat.card H ∧ (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
      ∃ Φ : ↥((fun y => ((q y : ℂ))) ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
        ∀ y, rootBase P S' (Φ y) = ((q (y : Y) : ℂ)) :=
  exists_algebraic_model_of_forall_ne (H := H) hf htrans hrange
    (hwall S Y q hq hf hrange H htrans)

end Rigidity.RET

end
