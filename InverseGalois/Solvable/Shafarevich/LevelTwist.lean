/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.LiftTwist
import InverseGalois.Solvable.Shafarevich.LevelLift

/-!
# One whole rung of the ladder, in exchange for one prescription in degree one

A solution at one level of the descending `ℓ`-central series lifts to the next as soon as no class
of the layer is everywhere locally trivial, and the lift is already smooth, already over the base
realization and, past the first layer, already onto.  All that separates it from a solution at the
next level is the condition along the family: the lift is trivial there only up to an element of
the layer, and along each member of the family that discrepancy is a homomorphism into the layer.

Lifts of an embedding problem form a torsor under the one cocycles of the kernel, so the
discrepancies can be cancelled all at once by a single global cocycle restricting to their
inverses.  The whole of one rung of the ladder is therefore bought with one prescription of
restrictions in degree one — the local conditions of the arithmetic, met by a global class.

## Main results

* `InverseGalois.Shafarevich.levelSolution_succ_of_hasCocyclePrescription` — **a solution at one
  level, past the first, gives a solution at the next**, granted that the restrictions of a smooth
  one cocycle with values in the layer can be prescribed along the family.

## Tags

Shafarevich's theorem, embedding problem, p-central series, one cocycle, local conditions
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

attribute [local instance] genericQuotAction

/-- **A solution at one level of the filtration, past the first, gives a solution at the next**,
granted that the restrictions of a smooth one cocycle with values in the layer can be prescribed
along the family.

Three of the four clauses come with the lift: it is smooth, it projects to the base realization,
and past the first layer it is onto, the layer generating nothing.  The fourth is bought by the
prescription: along a member of the family, wherever the base realization is trivial, the lift is a
homomorphism into the layer, and twisting by a cocycle which restricts to the inverses of those
homomorphisms kills them all at once without disturbing the other three. -/
theorem levelSolution_succ_of_hasCocyclePrescription (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U]
    [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S]
    (hS : IsPGroup ℓ S) {j : ℕ} (hj : 1 ≤ j) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)]
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v) {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (σn : (layerExtension ℓ (genericAut U n S) j).Section)
    (hbot : sha2 ↥(layerSub ℓ (Generic U n S) j) (Set.range D) = ⊥)
    (hpres : HasCocyclePrescription ↥(layerSub ℓ (Generic U n S) j) fun ν => D ν ⊓ φ.ker)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) m j) :
    LevelSolution ℓ U S φ (Set.range D) n (j + 1) := by
  obtain ⟨Φ, f, hsurj, -, hright, hloc, hfsm, hf⟩ :=
    exists_lift_of_levelSolution ℓ U n S hS j φ hactφ D σn hbot h
  have hact : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)),
      x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom (Φ x) v := by
    intro x v
    rw [hactφ x v, ← hright x]
    exact (genericQuotAction_smul ℓ U n n S j (Φ x) v).symm.trans
      (smul_eq_conjActHom_genericLayer ℓ U n S j (Φ x) v)
  have hD : ∀ (ν : Fin t), ∀ x ∈ D ν ⊓ φ.ker, Φ x = 1 := fun ν x hx =>
    hloc (D ν) ⟨ν, rfl⟩ x (Subgroup.mem_inf.1 hx).1
      (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).2)
  obtain ⟨g, hgright, hgs, hg1⟩ :=
    exists_lift_eq_one_of_hasCocyclePrescription (layerExtension ℓ (genericAut U n S) j) hact hf
      (fun ν => D ν ⊓ φ.ker) hD hpres
      (isSmooth₁_of_isOpenNormal_ker (isOpenNormal_ker_of_isSmoothHom hfsm))
  have hcomp :
      Function.Surjective ((layerExtension ℓ (genericAut U n S) j).rightHom.comp g) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, (hgright x).trans hx⟩
  refine ⟨g, surjective_of_rightHom_comp_surjective ℓ (isPGroup_generic U n S hS)
    (genericAut U n S) hj g hcomp, isSmoothHom_of_isSmooth₁ hgs, fun x => ?_, ?_⟩
  · have hproj : SemidirectProduct.rightHom (g x)
        = SemidirectProduct.rightHom
            ((layerExtension ℓ (genericAut U n S) j).rightHom (g x)) := rfl
    rw [hproj, hgright x, hright x]
  · rintro _ ⟨ν, rfl⟩ x hx hx1
    exact hg1 ν x (Subgroup.mem_inf.2 ⟨hx, MonoidHom.mem_ker.2 hx1⟩)

end InverseGalois.Shafarevich
