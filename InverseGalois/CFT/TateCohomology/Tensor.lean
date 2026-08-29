/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Restrict

/-!
# The tensor product of a representation with the functions on the group

The tensor product of two representations carries the diagonal action.  When the first factor is
the functions on the group with values in a module carrying no action, the diagonal action is again
the action by translation, on the functions with values in the tensor product: a function and a
vector are sent to the record, at each element of the group, of the value of the function there
tensored with the translate of the vector by that element.  The cocycle-free verification is that
translating the function and the vector together translates the record.

Since the tensor product distributes over a finite product, that comparison is an isomorphism, and
the functions on the group have no complete cohomology whatsoever; so **the tensor product of the
functions on the group with any representation has no complete cohomology either**.

## Main definitions

* `InverseGalois.CFT.Tate.tensorObj`: the tensor product of two representations, with the diagonal
  action.
* `InverseGalois.CFT.Tate.tensorRho`: the diagonal action of an element of the group, read as an
  endomorphism of the tensor product of the two underlying modules.
* `InverseGalois.CFT.Tate.indTensorLinear`: the comparison of the tensor product of the functions
  on the group with a representation and the functions on the group with values in the tensor
  product.

## Main results

* `InverseGalois.CFT.Tate.tensorCommIso`: **the tensor product of two representations does not
  depend on the order of the factors.**
* `InverseGalois.CFT.Tate.indTensorIso`: **the tensor product of the functions on the group with a
  representation is the functions on the group with values in the tensor product.**
* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_inducedRep`: **the tensor product of the
  functions on the group with any representation has no complete cohomology.**

## Tags

Tate cohomology, tensor product, induced representation, projection formula
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### The action of a group element as an automorphism -/

section Aut

variable {k G V : Type u} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- **The action of an element of the group as an automorphism.** -/
def repAut (ρ : Representation k G V) (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

@[simp]
theorem repAut_apply (ρ : Representation k G V) (g : G) (v : V) : repAut ρ g v = ρ g v := rfl

end Aut

/-! ### The tensor product of two representations -/

section Tensor

variable {k G : Type u} [CommRing k] [Group G]

/-- **The tensor product of two representations**, with the diagonal action. -/
def tensorObj (A B : Rep k G) : Rep k G := Rep.of (A.ρ.tprod B.ρ)

@[simp]
theorem tensorObj_ρ_tmul (A B : Rep k G) (g : G) (a : ↥A.V) (b : ↥B.V) :
    (tensorObj A B).ρ g (a ⊗ₜ[k] b) = A.ρ g a ⊗ₜ[k] B.ρ g b := rfl

/-- **The diagonal action of an element of the group on a tensor product**, as an endomorphism of
the tensor product of the two underlying modules. -/
def tensorRho (A B : Rep k G) (g : G) : (↥A.V ⊗[k] ↥B.V) →ₗ[k] (↥A.V ⊗[k] ↥B.V) :=
  TensorProduct.map (A.ρ g) (B.ρ g)

@[simp]
theorem tensorRho_tmul (A B : Rep k G) (g : G) (a : ↥A.V) (b : ↥B.V) :
    tensorRho A B g (a ⊗ₜ[k] b) = A.ρ g a ⊗ₜ[k] B.ρ g b := rfl

theorem tensorObj_ρ_apply (A B : Rep k G) (g : G) (t : ↥A.V ⊗[k] ↥B.V) :
    (tensorObj A B).ρ g t = tensorRho A B g t := rfl

theorem tensorRho_one (A B : Rep k G) : tensorRho A B 1 = LinearMap.id :=
  TensorProduct.ext' fun a b => by
    show A.ρ 1 a ⊗ₜ[k] B.ρ 1 b = a ⊗ₜ[k] b
    rw [map_one, map_one]
    rfl

theorem tensorRho_one_apply (A B : Rep k G) (t : ↥A.V ⊗[k] ↥B.V) : tensorRho A B 1 t = t :=
  LinearMap.congr_fun (tensorRho_one A B) t

theorem tensorRho_mul (A B : Rep k G) (g h : G) :
    tensorRho A B (g * h) = tensorRho A B g ∘ₗ tensorRho A B h :=
  TensorProduct.ext' fun a b => by
    show A.ρ (g * h) a ⊗ₜ[k] B.ρ (g * h) b = A.ρ g (A.ρ h a) ⊗ₜ[k] B.ρ g (B.ρ h b)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]

theorem tensorRho_mul_apply (A B : Rep k G) (g h : G) (t : ↥A.V ⊗[k] ↥B.V) :
    tensorRho A B (g * h) t = tensorRho A B g (tensorRho A B h t) :=
  LinearMap.congr_fun (tensorRho_mul A B g h) t

theorem tensorComm_equivariant (A B : Rep k G) (g : G) :
    (TensorProduct.comm k ↥A.V ↥B.V).toLinearMap ∘ₗ (tensorObj A B).ρ g
      = (tensorObj B A).ρ g ∘ₗ (TensorProduct.comm k ↥A.V ↥B.V).toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

/-- **The tensor product of two representations does not depend on the order of the factors.** -/
def tensorCommIso (A B : Rep k G) : tensorObj A B ≅ tensorObj B A :=
  Action.mkIso (TensorProduct.comm k ↥A.V ↥B.V).toModuleIso fun g => by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    exact LinearMap.congr_fun (tensorComm_equivariant A B g) t

end Tensor

/-! ### The functions on the group tensored with a representation -/

section Projection

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  (W : Type u) [AddCommGroup W] [Module k W] (M : Rep k G)

/-- **The comparison of the tensor product of the functions on the group with a representation and
the functions on the group with values in the tensor product.** -/
def indTensorLinear : ((G → W) ⊗[k] ↥M.V) ≃ₗ[k] (G → W ⊗[k] ↥M.V) :=
  letI := Fintype.ofFinite G
  letI := Classical.decEq G
  (TensorProduct.piLeft k ↥M.V fun _ : G => W).trans
    (LinearEquiv.piCongrRight fun x =>
      TensorProduct.congr (LinearEquiv.refl k W) (repAut M.ρ x))

variable {W M}

@[simp]
theorem indTensorLinear_tmul (f : G → W) (m : ↥M.V) (x : G) :
    indTensorLinear W M (f ⊗ₜ[k] m) x = f x ⊗ₜ[k] M.ρ x m := by
  simp [indTensorLinear]

theorem indTensorLinear_tmul' (f : G → W) (m : ↥M.V) :
    indTensorLinear W M (f ⊗ₜ[k] m) = fun x => f x ⊗ₜ[k] M.ρ x m :=
  funext fun x => indTensorLinear_tmul f m x

variable (W M)

theorem indTensorLinear_equivariant (g : G) :
    (indTensorLinear W M).toLinearMap ∘ₗ (tensorObj (Rep.of (inducedRep k G W)) M).ρ g
      = inducedRep k G (W ⊗[k] ↥M.V) g ∘ₗ (indTensorLinear W M).toLinearMap := by
  refine TensorProduct.ext' fun f m => ?_
  refine funext fun x => ?_
  show indTensorLinear W M (inducedRep k G W g f ⊗ₜ[k] M.ρ g m) x
    = indTensorLinear W M (f ⊗ₜ[k] m) (x * g)
  rw [indTensorLinear_tmul, indTensorLinear_tmul, inducedRep_apply, ← Module.End.mul_apply,
    ← map_mul]

/-- **The tensor product of the functions on the group with a representation is the functions on
the group with values in the tensor product.** -/
def indTensorIso :
    tensorObj (Rep.of (inducedRep k G W)) M ≅ Rep.of (inducedRep k G (W ⊗[k] ↥M.V)) :=
  Action.mkIso (indTensorLinear W M).toModuleIso fun g => by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    exact LinearMap.congr_fun (indTensorLinear_equivariant W M g) t

/-- **The tensor product of the functions on the group with any representation has no complete
cohomology.** -/
theorem isZero_tateModule_tensorObj_inducedRep (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj (Rep.of (inducedRep k G W)) M) n) :=
  isZero_tateModule_of_iso (indTensorIso W M) n (isZero_tateModule_inducedRep n)

/-- **Any representation tensored with the functions on the group has no complete
cohomology.** -/
theorem isZero_tateModule_tensorObj_inducedRep' (n : ℤ) :
    Limits.IsZero (tateModule (tensorObj M (Rep.of (inducedRep k G W))) n) :=
  isZero_tateModule_of_iso (tensorCommIso M (Rep.of (inducedRep k G W))) n
    (isZero_tateModule_tensorObj_inducedRep W M n)

end Projection

end

end InverseGalois.CFT.Tate
