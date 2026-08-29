/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Tensor

/-!
# The tensor product commutes with the shift

The shift of a representation is the cokernel of the embedding recording all the translates of a
vector.  Tensoring a cokernel with a fixed module gives the cokernel of the tensored map, and the
tensored map is, under the comparison of the functions on the group tensored with a representation
and the functions on the group with values in the tensor product, exactly the embedding of the
tensor product: the translates of a vector tensored with a vector are the translates of the tensor
of the two vectors.

So the shift of a representation tensored with another representation is the shift of the tensor
product.  That is the step which lets a statement about the tensor product be moved by one degree.

## Main definitions

* `InverseGalois.CFT.Tate.shiftTensorEquiv`: the comparison of the shift tensored with a
  representation and the shift of the tensor product.

## Main results

* `InverseGalois.CFT.Tate.shiftTensorIso`: **the shift of a representation tensored with another
  representation is the shift of the tensor product.**

## Tags

Tate cohomology, tensor product, dimension shifting, cokernel
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

section Shift

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A M : Rep k G)

/-- **The translates of a vector tensored with a vector are the translates of the tensor of the two
vectors.** -/
theorem map_indTensorLinear_range :
    Submodule.map (indTensorLinear ↥A.V M).toLinearMap
        (LinearMap.range (TensorProduct.map
          (LinearMap.range (coindEmb A.ρ)).subtype (LinearMap.id : ↥M.V →ₗ[k] ↥M.V)))
      = LinearMap.range (coindEmb (tensorObj A M).ρ) := by
  have hmem : ∀ t : ↥A.V ⊗[k] ↥M.V, coindEmb (tensorObj A M).ρ t ∈
      Submodule.map (indTensorLinear ↥A.V M).toLinearMap
        (LinearMap.range (TensorProduct.map
          (LinearMap.range (coindEmb A.ρ)).subtype (LinearMap.id : ↥M.V →ₗ[k] ↥M.V))) := by
    intro t
    induction t with
    | zero => simp
    | tmul a m =>
        refine ⟨(coindEmb A.ρ a) ⊗ₜ[k] m,
          ⟨(⟨coindEmb A.ρ a, ⟨a, rfl⟩⟩ : ↥(LinearMap.range (coindEmb A.ρ))) ⊗ₜ[k] m, rfl⟩,
          funext fun x => ?_⟩
        rw [LinearEquiv.coe_coe, indTensorLinear_tmul, coindEmb_apply]
        rfl
    | add t s ht hs =>
        rw [map_add]
        exact Submodule.add_mem _ ht hs
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    induction u with
    | zero => simp
    | tmul s m =>
        obtain ⟨a, ha⟩ := s.2
        refine ⟨a ⊗ₜ[k] m, funext fun x => ?_⟩
        show A.ρ x a ⊗ₜ[k] M.ρ x m = indTensorLinear ↥A.V M ((s : G → ↥A.V) ⊗ₜ[k] m) x
        rw [indTensorLinear_tmul, ← ha, coindEmb_apply]
    | add u v hu hv =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hu hv
  · rintro _ ⟨t, rfl⟩
    exact hmem t

/-- **The comparison of the shift tensored with a representation and the shift of the tensor
product.** -/
def shiftTensorEquiv : (↥(shiftObj A).V ⊗[k] ↥M.V) ≃ₗ[k] ↥(shiftObj (tensorObj A M)).V :=
  (TensorProduct.quotientTensorEquiv ↥M.V (LinearMap.range (coindEmb A.ρ))).trans
    (Submodule.Quotient.equiv _ _ (indTensorLinear ↥A.V M) (map_indTensorLinear_range A M))

variable {A M}

theorem shiftTensorEquiv_mk_tmul (f : G → ↥A.V) (m : ↥M.V) :
    shiftTensorEquiv A M (Submodule.Quotient.mk f ⊗ₜ[k] m)
      = Submodule.Quotient.mk (fun x => f x ⊗ₜ[k] M.ρ x m) := by
  show Submodule.Quotient.mk (indTensorLinear ↥A.V M (f ⊗ₜ[k] m)) = _
  rw [indTensorLinear_tmul']

variable (A M)

theorem shiftTensorEquiv_equivariant (g : G) :
    (shiftTensorEquiv A M).toLinearMap ∘ₗ (tensorObj (shiftObj A) M).ρ g
      = (shiftObj (tensorObj A M)).ρ g ∘ₗ (shiftTensorEquiv A M).toLinearMap := by
  refine TensorProduct.ext' fun q m => ?_
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb A.ρ)) q
  have hfun : (fun x => (inducedRep k G ↥A.V g f) x ⊗ₜ[k] M.ρ x (M.ρ g m))
      = fun x => inducedRep k G (↥A.V ⊗[k] ↥M.V) g (fun y => f y ⊗ₜ[k] M.ρ y m) x := by
    refine funext fun x => ?_
    show f (x * g) ⊗ₜ[k] M.ρ x (M.ρ g m) = f (x * g) ⊗ₜ[k] M.ρ (x * g) m
    rw [← Module.End.mul_apply, ← map_mul]
  show shiftTensorEquiv A M (Submodule.Quotient.mk (inducedRep k G ↥A.V g f) ⊗ₜ[k] M.ρ g m)
    = Submodule.Quotient.mk
        (inducedRep k G (↥A.V ⊗[k] ↥M.V) g (fun y => f y ⊗ₜ[k] M.ρ y m))
  rw [shiftTensorEquiv_mk_tmul, hfun]

/-- **The shift of a representation tensored with another representation is the shift of the tensor
product.** -/
def shiftTensorIso : tensorObj (shiftObj A) M ≅ shiftObj (tensorObj A M) :=
  Action.mkIso (shiftTensorEquiv A M).toModuleIso fun g => by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    exact LinearMap.congr_fun (shiftTensorEquiv_equivariant A M g) t

end Shift

end

end InverseGalois.CFT.Tate
