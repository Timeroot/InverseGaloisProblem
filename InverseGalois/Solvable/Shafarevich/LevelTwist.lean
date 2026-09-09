/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.LiftTwist
import InverseGalois.Solvable.Shafarevich.LevelLift
import InverseGalois.Solvable.Shafarevich.LevelShrink

/-!
# One whole rung of the ladder, in exchange for one prescription in degree one

A solution at one level of the descending `ℓ`-central series lifts to the next once the everywhere
locally trivial classes of the layer are dealt with, and the lift is already smooth, already over
the base realization and, past the first layer, already onto.  All that separates it from a solution
at the next level is the condition along the family: the lift is trivial there only up to an element
of the layer, and along each member of the family that discrepancy is a homomorphism into the layer.

Lifts of an embedding problem form a torsor under the one cocycles of the kernel, so the
discrepancies can be cancelled all at once by a single global cocycle restricting to their
inverses.  The whole of one rung of the ladder is therefore bought with one prescription of
restrictions in degree one — the local conditions of the arithmetic, met by a global class.

What the lift itself is bought with is left open: either no class of the layer is everywhere locally
trivial, or every such class is inflated from the operator group and a second shrinking kills it.
Only the second is what the arithmetic supplies past the first layer.

## Main results

* `InverseGalois.Shafarevich.levelSolution_succ_of_exists_lift` — **a lift at one level, past the
  first, gives a solution at the next**, granted that the restrictions of a smooth one cocycle with
  values in the layer can be prescribed along the family and that the prescribed property can be
  restored.
* `InverseGalois.Shafarevich.levelSolution_succ_of_hasCocyclePrescription` — the same when no class
  of the layer is everywhere locally trivial.
* `InverseGalois.Shafarevich.levelSolution_succ_of_hasInflatedSha` — **the same when every
  everywhere locally trivial class of the layer is inflated from the operator group.**

## Tags

Shafarevich's theorem, embedding problem, p-central series, one cocycle, local conditions
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

attribute [local instance] genericQuotAction

/-- **A lift at one level of the filtration, past the first, gives a solution at the next**,
granted that the restrictions of a smooth one cocycle with values in the layer can be prescribed
along the family.

Three of the four clauses come with the lift: it is smooth, it projects to the base realization,
and past the first layer it is onto, the layer generating nothing.  The fourth is bought by the
prescription: along a member of the family, wherever the base realization is trivial, the lift is a
homomorphism into the layer, and twisting by a cocycle which restricts to the inverses of those
homomorphisms kills them all at once without disturbing the other three.  The prescribed property
the solution is to carry is not one of the four, and it is restored at the end. -/
theorem levelSolution_succ_of_exists_lift (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U]
    [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S]
    (hS : IsPGroup ℓ S) {j : ℕ} (hj : 1 ≤ j) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)]
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v) {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (P : LevelProperty ℓ U S k Ω)
    (hrep : HasSolutionRepair ℓ U n S j φ D P)
    (hpres : HasCocyclePrescription ↥(layerSub ℓ (Generic U n S) j) fun ν => D ν ⊓ φ.ker)
    (hlift : ∃ (Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j)
        (f : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1)),
      Function.Surjective Φ ∧ IsSmoothHom Φ ∧ (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) ∧
        (∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 → Φ x = 1) ∧ P n j Φ ∧ IsSmoothHom f ∧
          ∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom (f x) = Φ x) :
    LevelSolution ℓ U S φ (Set.range D) P n (j + 1) := by
  obtain ⟨Φ, f, hsurj, hsm, hright, hloc, hΦP, hfsm, hf⟩ := hlift
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
  exact hrep Φ g hsm hright hΦP
    (surjective_of_rightHom_comp_surjective ℓ (isPGroup_generic U n S hS) (genericAut U n S) hj g
      hcomp)
    (isSmoothHom_of_isSmooth₁ hgs) hgright fun ν x hx hx1 =>
      hg1 ν x (Subgroup.mem_inf.2 ⟨hx, MonoidHom.mem_ker.2 hx1⟩)

/-- **A solution at one level of the filtration, past the first, gives a solution at the next**,
granted that no class with coefficients in the layer is everywhere locally trivial and that the
restrictions of a smooth one cocycle with values in the layer can be prescribed along the
family. -/
theorem levelSolution_succ_of_hasCocyclePrescription (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U]
    [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S]
    (hS : IsPGroup ℓ S) {j : ℕ} (hj : 1 ≤ j) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)]
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v) {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (T : Set (Subgroup Gal(Ω/k)))
    (P : LevelProperty ℓ U S k Ω) (hstab : IsShrinkStable ℓ U S P)
    (hrep : HasSolutionRepair ℓ U n S j φ D P)
    (hvan : HasLocalLift ℓ U n S j φ D T P)
    (σn : (layerExtension ℓ (genericAut U n S) j).Section)
    (hbot : sha2 ↥(layerSub ℓ (Generic U n S) j) T = ⊥)
    (hpres : HasCocyclePrescription ↥(layerSub ℓ (Generic U n S) j) fun ν => D ν ⊓ φ.ker)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) P m j) :
    LevelSolution ℓ U S φ (Set.range D) P n (j + 1) :=
  levelSolution_succ_of_exists_lift ℓ U n S hS hj φ hactφ D P hrep hpres
    (exists_lift_of_levelSolution ℓ U n S hS j φ hactφ D T P hstab hvan σn hbot h)

/-- **A solution at one level of the filtration, past the first, gives a solution at the next**,
granted that every everywhere locally trivial class with coefficients in the layer is inflated from
the operator group and that the restrictions of a smooth one cocycle with values in the layer can be
prescribed along the family.

This is the form the arithmetic of a number field supplies past the first layer: an everywhere
locally trivial class of the second cohomology is not zero, but it is inflated from the finite
quotient the base realization cuts out, and a second shrinking kills what is inflated. -/
theorem levelSolution_succ_of_hasInflatedSha (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U]
    [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S]
    (hS : IsPGroup ℓ S) {j : ℕ} (hj : 1 ≤ j) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) (hsmφ : IsSmoothHom φ)
    [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)]
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v) {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (T : Set (Subgroup Gal(Ω/k)))
    (P : LevelProperty ℓ U S k Ω) (hstab : IsShrinkStable ℓ U S P)
    (hrep : HasSolutionRepair ℓ U n S j φ D P)
    (hvan : ∀ m : ℕ, HasLocalLift ℓ U m S j φ D T P)
    (hinfl : ∀ m : ℕ, HasInflatedSha ℓ U m S j φ T)
    (hpres : HasCocyclePrescription ↥(layerSub ℓ (Generic U n S) j) fun ν => D ν ⊓ φ.ker)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) P m j) :
    LevelSolution ℓ U S φ (Set.range D) P n (j + 1) :=
  levelSolution_succ_of_exists_lift ℓ U n S hS hj φ hactφ D P hrep hpres
    (exists_lift_of_levelSolution_of_hasInflatedSha ℓ U n S hS j φ hsmφ D T P hstab hvan hinfl h)

end InverseGalois.Shafarevich
