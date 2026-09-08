/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerFrattini
import InverseGalois.Solvable.Shafarevich.LevelObstruction

/-!
# One level of the ladder, up to the conditions along the family

A solution at one level of the descending `ℓ`-central series, chosen with enough letters that the
class of the next layer dies on every member of the family, lifts to the next level as soon as no
class of that layer is everywhere locally trivial.  Three of the four clauses asked of a solution
come for free: the lift is again smooth, it again projects to the base realization, and past the
first layer it is again onto, the layer being non-generating.

The fourth clause, that the lift be trivial along the family wherever the base realization is, is
not free, but what stands in its way is small and named here: the lift is at worst off by an
element of the layer, so the whole of the remaining question lives in the layer.

## Main results

* `InverseGalois.Shafarevich.exists_lift_surjective_of_levelSolution` — **a solution at one level
  lifts to a smooth surjection at the next level over the base realization**, off by an element of
  the layer along each member of the family.

## Tags

Shafarevich's theorem, embedding problem, p-central series, Frattini subgroup, Shafarevich group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

attribute [local instance] genericQuotAction

/-- **A solution at one level lifts to a smooth surjection at the next level over the base
realization.**  Enough letters make the class of the layer die on every member of the family, so
the obstruction to lifting is everywhere locally trivial and by hypothesis therefore trivial; the
lift which results is smooth and projects to the base realization, and past the first layer it is
onto because the layer generates nothing.  Along a member of the family, wherever the base
realization is trivial the lift lands in the layer. -/
theorem exists_lift_surjective_of_levelSolution (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U]
    [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S]
    (hS : IsPGroup ℓ S) {j : ℕ} (hj : 1 ≤ j) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)]
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v) {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (σn : (layerExtension ℓ (genericAut U n S) j).Section)
    (hbot : sha2 ↥(layerSub ℓ (Generic U n S) j) (Set.range D) = ⊥)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) m j) :
    ∃ f : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1), Function.Surjective f ∧ IsSmoothHom f ∧
      (∀ x, SemidirectProduct.rightHom (f x) = φ x) ∧
        ∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 →
          f x ∈ (layerExtension ℓ (genericAut U n S) j).inl.range := by
  obtain ⟨Φ, f, hsurj, -, hright, hloc, hfsm, hf⟩ :=
    exists_lift_of_levelSolution ℓ U n S hS j φ hactφ D σn hbot h
  have hcomp : Function.Surjective ((layerExtension ℓ (genericAut U n S) j).rightHom.comp f) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, (hf x).trans hx⟩
  refine ⟨f, surjective_of_rightHom_comp_surjective ℓ (isPGroup_generic U n S hS)
    (genericAut U n S) hj f hcomp, hfsm, fun x => ?_, ?_⟩
  · have hproj : SemidirectProduct.rightHom (f x)
        = SemidirectProduct.rightHom ((layerExtension ℓ (genericAut U n S) j).rightHom (f x)) :=
      rfl
    rw [hproj, hf x, hright x]
  · rintro _ ⟨ν, rfl⟩ x hx hx1
    rw [(layerExtension ℓ (genericAut U n S) j).range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    exact (hf x).trans (hloc (D ν) ⟨ν, rfl⟩ x hx hx1)

end InverseGalois.Shafarevich
