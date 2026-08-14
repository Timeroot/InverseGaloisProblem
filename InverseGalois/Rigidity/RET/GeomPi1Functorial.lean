/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeomPi1

/-!
# Adding punctures: the projection maps between geometric fundamental groups

Enlarging the set of punctures enlarges the compositum of the covers unramified outside it, and
restriction of automorphisms from the larger compositum to the smaller one is a surjection of
fundamental groups: puncturing the line at more points can only make the fundamental group bigger,
and every cover over the smaller set is a cover over the larger one seen through that surjection.

## Main results

* `Rigidity.RET.coverField_mono` — the cover field grows with the set of punctures.
* `Rigidity.RET.geomPi1Restrict` — the induced homomorphism of fundamental groups, and
  `Rigidity.RET.geomPi1Restrict_surjective` — it is surjective.
* `Rigidity.RET.geomPi1Restrict_comp` — the projections are compatible with each other.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-! ### The cover field grows with the set of punctures -/

/-- **A cover unramified outside a smaller set of points is unramified outside a larger one**, so
the cover field is monotone in the set of punctures. -/
theorem coverField_mono {S T : Set k} (hST : S ⊆ T) : coverField S ≤ coverField T := by
  simp only [coverField]
  exact iSup_le fun E => (E.2.mono hST).le_coverField

/-- The smaller cover field, seen as an intermediate field of the larger one. -/
abbrev coverFieldRestrict {S T : Set k} (hST : S ⊆ T) :
    IntermediateField (RatFunc k) (coverField T : Type) :=
  IntermediateField.restrict (coverField_mono hST)

/-- The smaller cover field is normal inside the larger one, being normal over the line. -/
theorem normal_coverFieldRestrict {S T : Set k} (hST : S ⊆ T) :
    Normal (RatFunc k) ((coverFieldRestrict hST : IntermediateField (RatFunc k)
      (coverField T : Type)) : Type) :=
  Normal.of_algEquiv (IntermediateField.restrict_algEquiv (coverField_mono hST))

/-! ### The projection of fundamental groups -/

/-- **Restriction of automorphisms from the compositum over a larger set of punctures to the
compositum over a smaller one.** -/
def geomPi1Restrict {S T : Set k} (hST : S ⊆ T) : geomPi1 T →* geomPi1 S :=
  letI := normal_coverFieldRestrict hST
  (AlgEquiv.autCongr
      (IntermediateField.restrict_algEquiv (coverField_mono hST)).symm).toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (coverFieldRestrict hST))

/-- **The projection is restriction**: it moves an element of the smaller compositum exactly as the
automorphism of the larger one does. -/
theorem geomPi1Restrict_apply {S T : Set k} (hST : S ⊆ T) (σ : geomPi1 T)
    (x : (coverField S : Type)) :
    ((geomPi1Restrict hST σ x : (coverField S : Type)) : LineCover.closure)
      = ((σ ⟨(x : LineCover.closure), coverField_mono hST x.2⟩ :
          (coverField T : Type)) : LineCover.closure) := by
  haveI := normal_coverFieldRestrict hST
  set e := IntermediateField.restrict_algEquiv (coverField_mono hST) with he
  have hcoe : ∀ y : (coverField S : Type),
      ((e y : (coverFieldRestrict hST : IntermediateField (RatFunc k)
          (coverField T : Type))) : (coverField T : Type))
        = ⟨(y : LineCover.closure), coverField_mono hST y.2⟩ := by
    intro y
    rfl
  have hkey := AlgEquiv.restrictNormalHom_apply (F := RatFunc k)
    (coverFieldRestrict hST) σ (e x)
  have hgoal : geomPi1Restrict hST σ x
      = e.symm (AlgEquiv.restrictNormalHom (coverFieldRestrict hST) σ (e x)) := rfl
  rw [hgoal]
  have hval : ((AlgEquiv.restrictNormalHom (coverFieldRestrict hST) σ (e x) :
      (coverFieldRestrict hST : IntermediateField (RatFunc k) (coverField T : Type))) :
        (coverField T : Type))
      = σ ⟨(x : LineCover.closure), coverField_mono hST x.2⟩ := by
    rw [hkey, hcoe]
  -- transporting back along `e` does not change the underlying element of the closure
  have hsymm : ∀ z : (coverFieldRestrict hST : IntermediateField (RatFunc k)
      (coverField T : Type)), ((e.symm z : (coverField S : Type)) : LineCover.closure)
        = ((z : (coverField T : Type)) : LineCover.closure) := by
    intro z
    have := hcoe (e.symm z)
    rw [AlgEquiv.apply_symm_apply] at this
    rw [this]
  rw [hsymm, hval]

/-- **The projection is surjective**: every automorphism of the compositum over the smaller set of
punctures extends to the compositum over the larger one. -/
theorem geomPi1Restrict_surjective {S T : Set k} (hST : S ⊆ T) :
    Function.Surjective (geomPi1Restrict hST) := by
  haveI := normal_coverFieldRestrict hST
  intro τ
  set e := IntermediateField.restrict_algEquiv (coverField_mono hST) with he
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := RatFunc k)
    (K₁ := ((coverFieldRestrict hST : IntermediateField (RatFunc k) (coverField T : Type)) : Type))
    (E := (coverField T : Type)) (e.symm.trans (τ.trans e))
  refine ⟨σ, ?_⟩
  have : geomPi1Restrict hST σ
      = (AlgEquiv.autCongr e.symm) (AlgEquiv.restrictNormalHom (coverFieldRestrict hST) σ) := rfl
  rw [this, hσ]
  refine AlgEquiv.ext fun x => ?_
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.symm_symm, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]

/-- **The projections are compatible**: restricting in two steps is restricting in one. -/
theorem geomPi1Restrict_comp {S T U : Set k} (hST : S ⊆ T) (hTU : T ⊆ U) :
    (geomPi1Restrict hST).comp (geomPi1Restrict hTU)
      = geomPi1Restrict (hST.trans hTU) := by
  ext σ x
  have h₁ := geomPi1Restrict_apply hST (geomPi1Restrict hTU σ) x
  have h₂ := geomPi1Restrict_apply hTU σ ⟨(x : LineCover.closure), coverField_mono hST x.2⟩
  have h₃ := geomPi1Restrict_apply (hST.trans hTU) σ x
  rw [MonoidHom.comp_apply, h₁, h₂, h₃]

end Rigidity.RET
