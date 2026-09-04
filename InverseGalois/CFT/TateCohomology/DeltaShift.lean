/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DeltaNatural
import InverseGalois.CFT.TateCohomology.NakayamaNatural

/-!
# The connecting map of a split extension is a map into the shift

The sequence defining the shift of a representation is the universal extension with acyclic middle
term, and its connecting map is the identification of the complete cohomology of the shift in a
degree with that of the representation in the following degree.  Every other extension of the same
subobject compares with it, and the comparison carries the connecting map of the extension to that
identification: the connecting map of an extension admitting a comparison with the shifting sequence
is the identification composed with the map induced by the comparison in the third place.

The extension attached to a one cocycle, tensored with a representation, admits such a comparison
because it is a sum as a module: reading an element in the first entry of all of its translates
gives a map into the functions on the group, and modulo the translates of the subobject the result
depends only on the second entry.  The comparison it induces sends an element of the coefficients to
the class of the function pairing the values of the cocycle with the moved element.

The consequence is that the comparison of Tate and Nakayama, which is built from the connecting map
of that tensored extension followed by two identifications, is a composite of identifications of
shifts and of maps induced by morphisms of representations, with no connecting map left in it.  Any
statement already known for induced maps and for the identification of a shift therefore reaches the
comparison, which is what the connecting map by itself does not allow.

## Main definitions

* `InverseGalois.CFT.Tate.cocycleShiftMid`: the record of all the translates of an element of the
  tensored extension, read in the first entry.
* `InverseGalois.CFT.Tate.cocycleShiftHom`: the comparison of the coefficients with the shift of
  their tensor product.

## Main results

* `InverseGalois.CFT.Tate.tateδ_eq_tateShiftEquiv`: **the connecting map of an extension comparing
  with the sequence defining the shift is the identification of the shift composed with the induced
  map.**
* `InverseGalois.CFT.Tate.tateδ_cocycleTensorSeq_eq`: **the connecting map of the tensored extension
  is the identification of the shift composed with the map induced by the comparison.**
* `InverseGalois.CFT.Tate.tateNakayamaMap_eq`: **the comparison of Tate and Nakayama is a composite
  of identifications of shifts and of induced maps.**

## Tags

Tate cohomology, connecting map, dimension shifting, Tate-Nakayama, cocycle, extension
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### Comparing with the shifting sequence -/

section General

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **The connecting map of an extension comparing with the sequence defining the shift is the
identification of the shift composed with the induced map.** -/
theorem tateδ_eq_tateShiftEquiv {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (φ : X ⟶ shiftSeq X.X₁) (hφ : φ.τ₁ = 𝟙 X.X₁) (n : ℤ) (x : ↥(tateModule X.X₃ n)) :
    tateδ hX n x = tateShiftEquiv X.X₁ n (tateMap φ.τ₃ n x) := by
  have h := tateδ_naturality_apply hX (shiftSeq_shortExact X.X₁) φ n x
  rw [hφ] at h
  exact (tateMap_id_apply X.X₁ (n + 1) (tateδ hX n x)).symm.trans h

end General

/-! ### The tensored extension -/

section Cocycle

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  (A : Rep k G) (b : groupCohomology.cocycles₁ A) (M : Rep k G)

/-- **The record of all the translates of an element of the tensored extension**, read in the first
entry. -/
def cocycleShiftMid : ↥(cocycleTensorObj A b M).V →ₗ[k] ↥(indObj (tensorObj A M)).V :=
  (LinearMap.fst k (↥A.V ⊗[k] ↥M.V) ↥M.V).compLeft G ∘ₗ coindEmb (cocycleTensorObj A b M).ρ

omit [Finite G] in
@[simp]
theorem cocycleShiftMid_apply (p : (↥A.V ⊗[k] ↥M.V) × ↥M.V) (g : G) :
    cocycleShiftMid A b M p g = tensorRho A M g p.1 + (b g) ⊗ₜ[k] M.ρ g p.2 := rfl

omit [Finite G] in
/-- **The record of all the translates is equivariant.** -/
theorem cocycleShiftMid_equivariant (h : G) :
    cocycleShiftMid A b M ∘ₗ (cocycleTensorObj A b M).ρ h
      = (indObj (tensorObj A M)).ρ h ∘ₗ cocycleShiftMid A b M := by
  refine LinearMap.ext fun p => funext fun g => ?_
  show ((cocycleTensorObj A b M).ρ g ((cocycleTensorObj A b M).ρ h p)).1
    = ((cocycleTensorObj A b M).ρ (g * h) p).1
  rw [map_mul, Module.End.mul_apply]

/-- **The comparison of the coefficients with the shift of their tensor product** attached to a one
cocycle: an element is sent to the class of the function pairing the values of the cocycle with the
moved element. -/
def cocycleShiftMap : ↥M.V →ₗ[k] ↥(shiftObj (tensorObj A M)).V :=
  (LinearMap.range (coindEmb (tensorObj A M).ρ)).mkQ ∘ₗ cocycleShiftMid A b M
    ∘ₗ LinearMap.inr k (↥A.V ⊗[k] ↥M.V) ↥M.V

omit [Finite G] in
theorem cocycleShiftMap_apply (m : ↥M.V) :
    cocycleShiftMap A b M m
      = Submodule.Quotient.mk (p := LinearMap.range (coindEmb (tensorObj A M).ρ))
        (fun g => (b g) ⊗ₜ[k] M.ρ g m) := by
  have h : (fun g : G => tensorRho A M g (0 : ↥A.V ⊗[k] ↥M.V) + (b g) ⊗ₜ[k] M.ρ g m)
      = fun g : G => (b g) ⊗ₜ[k] M.ρ g m := by
    refine funext fun g => ?_
    rw [map_zero, zero_add]
  show Submodule.Quotient.mk (p := LinearMap.range (coindEmb (tensorObj A M).ρ))
      (fun g : G => tensorRho A M g (0 : ↥A.V ⊗[k] ↥M.V) + (b g) ⊗ₜ[k] M.ρ g m) = _
  rw [h]

omit [Finite G] in
/-- **Modulo the translates of the tensor product, the record of all the translates depends only on
the second entry.** -/
theorem mkQ_cocycleShiftMid (p : (↥A.V ⊗[k] ↥M.V) × ↥M.V) :
    Submodule.Quotient.mk (p := LinearMap.range (coindEmb (tensorObj A M).ρ))
        (cocycleShiftMid A b M p)
      = cocycleShiftMap A b M p.2 := by
  rw [cocycleShiftMap_apply]
  refine (Submodule.Quotient.eq _).2 ⟨p.1, funext fun g => ?_⟩
  show (tensorObj A M).ρ g p.1
    = tensorRho A M g p.1 + (b g) ⊗ₜ[k] M.ρ g p.2 - (b g) ⊗ₜ[k] M.ρ g p.2
  rw [add_sub_cancel_right, tensorObj_ρ_apply]

omit [Finite G] in
/-- **The comparison of the coefficients with the shift of their tensor product is
equivariant.** -/
theorem cocycleShiftMap_equivariant (h : G) :
    cocycleShiftMap A b M ∘ₗ M.ρ h
      = (shiftObj (tensorObj A M)).ρ h ∘ₗ cocycleShiftMap A b M := by
  refine LinearMap.ext fun m => ?_
  have h1 : cocycleShiftMap A b M (M.ρ h m)
      = Submodule.Quotient.mk (p := LinearMap.range (coindEmb (tensorObj A M).ρ))
        (cocycleShiftMid A b M ((cocycleTensorObj A b M).ρ h (0, m))) :=
    (mkQ_cocycleShiftMid A b M ((cocycleTensorObj A b M).ρ h (0, m))).symm
  have h2 : cocycleShiftMid A b M ((cocycleTensorObj A b M).ρ h (0, m))
      = (indObj (tensorObj A M)).ρ h (cocycleShiftMid A b M (0, m)) :=
    LinearMap.congr_fun (cocycleShiftMid_equivariant A b M h) (0, m)
  have h3 : Submodule.Quotient.mk (p := LinearMap.range (coindEmb (tensorObj A M).ρ))
        ((indObj (tensorObj A M)).ρ h (cocycleShiftMid A b M (0, m)))
      = (shiftObj (tensorObj A M)).ρ h
        (Submodule.Quotient.mk (p := LinearMap.range (coindEmb (tensorObj A M).ρ))
          (cocycleShiftMid A b M (0, m))) :=
    LinearMap.congr_fun (mkQ_comp_inducedRep (tensorObj A M).ρ h) (cocycleShiftMid A b M (0, m))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, h3, mkQ_cocycleShiftMid]

/-- **The record of all the translates**, as a morphism of representations. -/
def cocycleShiftMidHom : cocycleTensorObj A b M ⟶ indObj (tensorObj A M) :=
  mkHom (cocycleShiftMid A b M) (cocycleShiftMid_equivariant A b M)

/-- **The comparison of the coefficients with the shift of their tensor product**, as a morphism of
representations. -/
def cocycleShiftHom : M ⟶ shiftObj (tensorObj A M) :=
  mkHom (cocycleShiftMap A b M) (cocycleShiftMap_equivariant A b M)

/-- **The comparison of the tensored extension with the sequence defining the shift.** -/
def cocycleShiftSeqHom : cocycleTensorSeq A b M ⟶ shiftSeq (tensorObj A M) where
  τ₁ := 𝟙 (tensorObj A M)
  τ₂ := cocycleShiftMidHom A b M
  τ₃ := cocycleShiftHom A b M
  comm₁₂ := by
    refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun t => funext fun g => ?_))
    show (tensorObj A M).ρ g t = tensorRho A M g t + (b g) ⊗ₜ[k] M.ρ g (0 : ↥M.V)
    rw [map_zero, TensorProduct.tmul_zero, add_zero, tensorObj_ρ_apply]
  comm₂₃ :=
    Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext (mkQ_cocycleShiftMid A b M)))

/-- **The connecting map of the tensored extension is the identification of the shift composed with
the map induced by the comparison.** -/
theorem tateδ_cocycleTensorSeq_eq (n : ℤ) (x : ↥(tateModule M n)) :
    tateδ (cocycleTensorSeq_shortExact A b M) n x
      = tateShiftEquiv (tensorObj A M) n (tateMap (cocycleShiftHom A b M) n x) :=
  tateδ_eq_tateShiftEquiv (cocycleTensorSeq_shortExact A b M) (cocycleShiftSeqHom A b M) rfl n x

end Cocycle

/-! ### The comparison of Tate and Nakayama -/

section Nakayama

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  (A : Rep k G) (b : groupCohomology.cocycles₁ (shiftObj A)) (M : Rep k G)

/-- **The connecting map of the tensored extension of a shift is the identification of the shift
composed with the map induced by the comparison.** -/
theorem tateNakayamaShiftMap_eq (n : ℤ) (x : ↥(tateModule M n)) :
    tateNakayamaShiftMap A b M n x
      = tateShiftEquiv (tensorObj (shiftObj A) M) n
        (tateMap (cocycleShiftHom (shiftObj A) b M) n x) :=
  tateδ_cocycleTensorSeq_eq (shiftObj A) b M n x

/-- **The comparison of Tate and Nakayama is a composite of identifications of shifts and of maps
induced by morphisms of representations.** -/
theorem tateNakayamaMap_eq (n : ℤ) (x : ↥(tateModule M n)) :
    tateNakayamaMap A b M n x
      = tateShiftEquiv (tensorObj A M) (n + 1)
        (tateMap (shiftTensorIso A M).hom (n + 1)
          (tateShiftEquiv (tensorObj (shiftObj A) M) n
            (tateMap (cocycleShiftHom (shiftObj A) b M) n x))) := by
  show (tateShiftEquiv (tensorObj A M) (n + 1))
      ((tateMap (shiftTensorIso A M).hom (n + 1)).hom ((tateNakayamaShiftMap A b M n).hom x)) = _
  rw [tateNakayamaShiftMap_eq A b M n x]

end Nakayama

end

end InverseGalois.CFT.Tate
