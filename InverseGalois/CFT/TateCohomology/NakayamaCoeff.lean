/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.NakayamaNatural
import InverseGalois.CFT.TateCohomology.TensorRight

/-!
# The comparison of Tate and Nakayama, along a map of coefficients

The comparison of Tate and Nakayama attached to a class in degree two of a representation raises
the degree by two, at the cost of tensoring the coefficients with the representation.  The
representation and the class stay fixed here, and the coefficients move: a map of coefficients
should carry the comparison for the source to the comparison for the target.

Nothing has to be corrected this time.  The cocycle that builds the twisted extension belongs to
the representation, not to the coefficients, so a map of coefficients extends to the two tensored
extensions by acting on both coordinates, and that extension is already equivariant.  It is a map
of the two extensions, the connecting maps agree, and the two identifications that follow are
natural in the coefficients as well; so the whole comparison is.

The consequence is the one that makes a free resolution of the coefficients useful.  If the
comparison is onto for one set of coefficients — which is what the theorem of Tate and Nakayama
gives when they are free of torsion — then everything the map of coefficients produces in the
higher degree is already a value of the comparison for the target coefficients.  The failure of the
comparison to be onto for coefficients with torsion is therefore confined to the cokernel of the
map induced by a free presentation.

## Main definitions

* `InverseGalois.CFT.Tate.cocycleTensorRightMap`: a map of coefficients, acting on both coordinates
  of a tensored extension.
* `InverseGalois.CFT.Tate.cocycleTensorSeqRightHom`: the comparison of the two tensored extensions
  attached to a map of coefficients.

## Main results

* `InverseGalois.CFT.Tate.shiftTensorIso_naturality_right`: **the comparison of the shift of a
  tensor product with the tensor product of the shift is natural in the second factor.**
* `InverseGalois.CFT.Tate.tateNakayamaMap_naturality_right`: **the comparison of Tate and Nakayama
  commutes with a map of coefficients.**
* `InverseGalois.CFT.Tate.tateNakayamaTwoMap_naturality_right`: **the comparison of Tate and
  Nakayama attached to a class in degree two commutes with a map of coefficients.**
* `InverseGalois.CFT.Tate.range_tateMap_tensorHomRight_le`: **if the comparison is onto for the
  source coefficients, then the image of the induced map is contained in the image of the
  comparison for the target coefficients.**

## Tags

Tate cohomology, Tate–Nakayama, naturality, coefficients, free presentation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### The two tensored extensions attached to a map of coefficients -/

section Compare

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)
  (b : groupCohomology.cocycles₁ A) {M N : Rep k G} (ψ : M ⟶ N)

/-- **A map of coefficients, acting on both coordinates of a tensored extension.** -/
def cocycleTensorRightMap :
    ↥(cocycleTensorObj A b M).V →ₗ[k] ↥(cocycleTensorObj A b N).V :=
  LinearMap.prodMap (LinearMap.lTensor ↥A.V ψ.hom.hom) ψ.hom.hom

@[simp]
theorem cocycleTensorRightMap_apply (p : (↥A.V ⊗[k] ↥M.V) × ↥M.V) :
    cocycleTensorRightMap A b ψ p
      = (LinearMap.lTensor ↥A.V ψ.hom.hom p.1, ψ.hom.hom p.2) := rfl

theorem cocycleTensorRightMap_equivariant (τ : G) :
    cocycleTensorRightMap A b ψ ∘ₗ (cocycleTensorObj A b M).ρ τ
      = (cocycleTensorObj A b N).ρ τ ∘ₗ cocycleTensorRightMap A b ψ := by
  have hcomm : ∀ t : ↥A.V ⊗[k] ↥M.V, LinearMap.lTensor ↥A.V ψ.hom.hom (tensorRho A M τ t)
      = tensorRho A N τ (LinearMap.lTensor ↥A.V ψ.hom.hom t) := fun t =>
    LinearMap.congr_fun (hom_equivariant (tensorHomRight A ψ) τ) t
  have hψ : ∀ m : ↥M.V, ψ.hom.hom (M.ρ τ m) = N.ρ τ (ψ.hom.hom m) := fun m =>
    LinearMap.congr_fun (hom_equivariant ψ τ) m
  refine LinearMap.ext fun p => Prod.ext ?_ (hψ p.2)
  show LinearMap.lTensor ↥A.V ψ.hom.hom (tensorRho A M τ p.1 + (b τ) ⊗ₜ[k] M.ρ τ p.2)
    = tensorRho A N τ (LinearMap.lTensor ↥A.V ψ.hom.hom p.1)
      + (b τ) ⊗ₜ[k] N.ρ τ (ψ.hom.hom p.2)
  rw [map_add, hcomm, LinearMap.lTensor_tmul, hψ]

/-- **A map of coefficients, as a map of the two tensored extensions.** -/
def cocycleTensorRightHom : cocycleTensorObj A b M ⟶ cocycleTensorObj A b N :=
  mkHom (cocycleTensorRightMap A b ψ) (cocycleTensorRightMap_equivariant A b ψ)

/-- **A map of coefficients, as a map of the two extensions.** -/
def cocycleTensorSeqRightHom : cocycleTensorSeq A b M ⟶ cocycleTensorSeq A b N where
  τ₁ := tensorHomRight A ψ
  τ₂ := cocycleTensorRightHom A b ψ
  τ₃ := ψ
  comm₁₂ := by
    refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun t => Prod.ext rfl ?_))
    show (0 : ↥N.V) = ψ.hom.hom (0 : ↥M.V)
    rw [map_zero]
  comm₂₃ := rfl

end Compare

/-! ### The connecting map -/

section Connecting

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G)
  (b : groupCohomology.cocycles₁ A) {M N : Rep k G} (ψ : M ⟶ N)

/-- **The connecting map of a tensored extension commutes with a map of coefficients.** -/
theorem tateδ_cocycleTensorSeqRight_naturality (n : ℤ) (x : ↥(tateModule M n)) :
    tateMap (tensorHomRight A ψ) (n + 1) (tateδ (cocycleTensorSeq_shortExact A b M) n x)
      = tateδ (cocycleTensorSeq_shortExact A b N) n (tateMap ψ n x) :=
  tateδ_naturality_apply (cocycleTensorSeq_shortExact A b M)
    (cocycleTensorSeq_shortExact A b N) (cocycleTensorSeqRightHom A b ψ) n x

end Connecting

/-! ### The identification of the two shifts -/

section Shift

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G) {M N : Rep k G}
  (ψ : M ⟶ N)

/-- **The comparison of the shift of a tensor product with the tensor product of the shift is
natural in the second factor.** -/
theorem shiftTensorIso_naturality_right :
    tensorHomRight (shiftObj A) ψ ≫ (shiftTensorIso A N).hom
      = (shiftTensorIso A M).hom ≫ shiftHom (tensorHomRight A ψ) := by
  refine tensorHomRight_ext (shiftObj A) fun q m => ?_
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb A.ρ)) q
  have hfun : (fun x => f x ⊗ₜ[k] N.ρ x (ψ.hom.hom m))
      = fun x => f x ⊗ₜ[k] ψ.hom.hom (M.ρ x m) :=
    funext fun x => by
      rw [← LinearMap.comp_apply, ← hom_equivariant ψ x, LinearMap.comp_apply]
  show shiftTensorEquiv A N (Submodule.Quotient.mk f ⊗ₜ[k] ψ.hom.hom m)
    = shiftLinear (tensorHomRight A ψ) (shiftTensorEquiv A M (Submodule.Quotient.mk f ⊗ₜ[k] m))
  rw [shiftTensorEquiv_mk_tmul, shiftTensorEquiv_mk_tmul, hfun]
  rfl

end Shift

/-! ### The comparison of Tate and Nakayama -/

section Nakayama

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G)
  (b : groupCohomology.cocycles₁ (shiftObj A)) {M N : Rep k G} (ψ : M ⟶ N)

/-- **The comparison of Tate and Nakayama commutes with a map of coefficients.** -/
theorem tateNakayamaMap_naturality_right (n : ℤ) (x : ↥(tateModule M n)) :
    tateMap (tensorHomRight A ψ) (n + 1 + 1) (tateNakayamaMap A b M n x)
      = tateNakayamaMap A b N n (tateMap ψ n x) := by
  have hδ := tateδ_cocycleTensorSeqRight_naturality (shiftObj A) b ψ n x
  have hsq := tateShiftEquiv_naturality (tensorHomRight A ψ) (n + 1)
    (tateMap (shiftTensorIso A M).hom (n + 1) (tateδ (cocycleTensorSeq_shortExact
      (shiftObj A) b M) n x))
  show tateMap (tensorHomRight A ψ) (n + 1 + 1) (tateShiftEquiv (tensorObj A M) (n + 1)
      (tateMap (shiftTensorIso A M).hom (n + 1)
        (tateδ (cocycleTensorSeq_shortExact (shiftObj A) b M) n x)))
    = tateShiftEquiv (tensorObj A N) (n + 1) (tateMap (shiftTensorIso A N).hom (n + 1)
        (tateδ (cocycleTensorSeq_shortExact (shiftObj A) b N) n (tateMap ψ n x)))
  rw [hsq, tateMap_comp_apply, ← shiftTensorIso_naturality_right, ← tateMap_comp_apply, hδ]

end Nakayama

/-! ### A class in degree two -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G] (A : Rep ℤ G) (α : ↥(tateModule A 2))
  {M N : Rep ℤ G} (ψ : M ⟶ N)

/-- **The comparison of Tate and Nakayama attached to a class in degree two commutes with a map of
coefficients.** -/
theorem tateNakayamaTwoMap_naturality_right (n : ℤ) (x : ↥(tateModule M n)) :
    tateMap (tensorHomRight A ψ) (n + 1 + 1) (tateNakayamaTwoMap A α M n x)
      = tateNakayamaTwoMap A α N n (tateMap ψ n x) :=
  tateNakayamaMap_naturality_right A (tateTwoCocycle A α) ψ n x

/-- **A map of coefficients along which the comparison is onto produces nothing new**: everything
in the image of the map it induces two degrees higher is a value of the comparison attached to the
target coefficients. -/
theorem range_tateMap_tensorHomRight_le (n : ℤ)
    (h : Function.Surjective (tateNakayamaTwoMap A α M n)) :
    LinearMap.range (tateMap (tensorHomRight A ψ) (n + 1 + 1)).hom
      ≤ LinearMap.range (tateNakayamaTwoMap A α N n) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, rfl⟩ := h z
  exact ⟨tateMap ψ n x, (tateNakayamaTwoMap_naturality_right A α ψ n x).symm⟩

end DegreeTwo

end

end InverseGalois.CFT.Tate
