/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorShift
import InverseGalois.CFT.TateCohomology.CocycleExtension

/-!
# The extension attached to a cocycle, tensored with a representation

The extension of the base ring attached to a one cocycle is, as a module, the sum of the
representation and the base ring; tensoring it with another representation therefore gives the sum
of the tensor product and that representation, and the twisting survives: an element of the group
moves a pair by acting diagonally on the first entry and adding the value of the cocycle tensored
with the moved second entry.

That description makes the tensored extension visibly an extension of the second representation by
the tensor product, with the inclusion and the projection of a sum.  So the whole extension can be
tensored without any hypothesis at all — the price usually paid to a flatness assumption is here
paid in advance by the splitting of the extension as a module.

## Main definitions

* `InverseGalois.CFT.Tate.cocycleTensorObj`: the extension of a representation by a tensor product
  attached to a one cocycle.
* `InverseGalois.CFT.Tate.cocycleTensorSeq`: that extension as a short complex.

## Main results

* `InverseGalois.CFT.Tate.cocycleTensorSeq_shortExact`: **the tensored extension is an extension of
  the second representation by the tensor product.**
* `InverseGalois.CFT.Tate.cocycleTensorIso`: **the extension attached to a cocycle, tensored with a
  representation, is that extension.**

## Tags

Tate cohomology, tensor product, cocycle, extension
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

section Twist

variable {k G : Type u} [CommRing k] [Group G]
  (A : Rep k G) (b : groupCohomology.cocycles₁ A) (M : Rep k G)

/-- **The twisted action of an element of the group** on the sum of a tensor product and a
representation. -/
def cocycleTensorLinear (τ : G) :
    ((↥A.V ⊗[k] ↥M.V) × ↥M.V) →ₗ[k] ((↥A.V ⊗[k] ↥M.V) × ↥M.V) :=
  LinearMap.prod
    (tensorRho A M τ ∘ₗ LinearMap.fst k (↥A.V ⊗[k] ↥M.V) ↥M.V
      + (TensorProduct.mk k ↥A.V ↥M.V (b τ) ∘ₗ M.ρ τ)
        ∘ₗ LinearMap.snd k (↥A.V ⊗[k] ↥M.V) ↥M.V)
    (M.ρ τ ∘ₗ LinearMap.snd k (↥A.V ⊗[k] ↥M.V) ↥M.V)

@[simp]
theorem cocycleTensorLinear_apply (τ : G) (p : (↥A.V ⊗[k] ↥M.V) × ↥M.V) :
    cocycleTensorLinear A b M τ p
      = (tensorRho A M τ p.1 + (b τ) ⊗ₜ[k] M.ρ τ p.2, M.ρ τ p.2) := rfl

/-- **The representation on the sum of a tensor product and a representation** twisted by a one
cocycle. -/
def cocycleTensorRep : Representation k G ((↥A.V ⊗[k] ↥M.V) × ↥M.V) where
  toFun := cocycleTensorLinear A b M
  map_one' := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_
    · show tensorRho A M 1 p.1 + (b 1) ⊗ₜ[k] M.ρ 1 p.2 = p.1
      rw [groupCohomology.cocycles₁_map_one b, TensorProduct.zero_tmul, add_zero,
        tensorRho_one_apply]
    · show M.ρ 1 p.2 = p.2
      rw [map_one, Module.End.one_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_
    · have hM : M.ρ (σ * τ) p.2 = M.ρ σ (M.ρ τ p.2) := by
        rw [map_mul, Module.End.mul_apply]
      show tensorRho A M (σ * τ) p.1 + (b (σ * τ)) ⊗ₜ[k] M.ρ (σ * τ) p.2
        = tensorRho A M σ (tensorRho A M τ p.1 + (b τ) ⊗ₜ[k] M.ρ τ p.2)
          + (b σ) ⊗ₜ[k] M.ρ σ (M.ρ τ p.2)
      rw [map_add, tensorRho_tmul, tensorRho_mul_apply, hM,
        (groupCohomology.mem_cocycles₁_iff (b : G → ↥A.V)).1 b.2 σ τ, TensorProduct.add_tmul,
        add_assoc]
    · show M.ρ (σ * τ) p.2 = M.ρ σ (M.ρ τ p.2)
      rw [map_mul, Module.End.mul_apply]

/-- **The extension of a representation by a tensor product** attached to a one cocycle. -/
def cocycleTensorObj : Rep k G := Rep.of (cocycleTensorRep A b M)

@[simp]
theorem cocycleTensorObj_ρ_apply (τ : G) (p : (↥A.V ⊗[k] ↥M.V) × ↥M.V) :
    (cocycleTensorObj A b M).ρ τ p
      = (tensorRho A M τ p.1 + (b τ) ⊗ₜ[k] M.ρ τ p.2, M.ρ τ p.2) := rfl

/-- **The inclusion of the tensor product into the tensored extension.** -/
def cocycleTensorInl : ↥(tensorObj A M).V →ₗ[k] ↥(cocycleTensorObj A b M).V :=
  LinearMap.inl k (↥A.V ⊗[k] ↥M.V) ↥M.V

/-- **The projection of the tensored extension onto the representation.** -/
def cocycleTensorSnd : ↥(cocycleTensorObj A b M).V →ₗ[k] ↥M.V :=
  LinearMap.snd k (↥A.V ⊗[k] ↥M.V) ↥M.V

theorem cocycleTensorInl_equivariant (τ : G) :
    cocycleTensorInl A b M ∘ₗ (tensorObj A M).ρ τ
      = (cocycleTensorObj A b M).ρ τ ∘ₗ cocycleTensorInl A b M := by
  refine LinearMap.ext fun t => Prod.ext ?_ ?_
  · show tensorRho A M τ t = tensorRho A M τ t + (b τ) ⊗ₜ[k] M.ρ τ (0 : ↥M.V)
    rw [map_zero, TensorProduct.tmul_zero, add_zero]
  · show (0 : ↥M.V) = M.ρ τ (0 : ↥M.V)
    rw [map_zero]

theorem cocycleTensorSnd_equivariant (τ : G) :
    cocycleTensorSnd A b M ∘ₗ (cocycleTensorObj A b M).ρ τ
      = M.ρ τ ∘ₗ cocycleTensorSnd A b M :=
  LinearMap.ext fun _ => rfl

/-- **The tensored extension as a short complex.** -/
def cocycleTensorSeq : ShortComplex (Rep k G) where
  X₁ := tensorObj A M
  X₂ := cocycleTensorObj A b M
  X₃ := M
  f := mkHom (cocycleTensorInl A b M) (cocycleTensorInl_equivariant A b M)
  g := mkHom (cocycleTensorSnd A b M) (cocycleTensorSnd_equivariant A b M)
  zero := by
    ext t
    rfl

/-- **The tensored extension is an extension of the second representation by the tensor
product.** -/
theorem cocycleTensorSeq_shortExact : (cocycleTensorSeq A b M).ShortExact :=
  shortExact_of_linearMap (fun _ _ h => congrArg Prod.fst h) (fun m => ⟨(0, m), rfl⟩)
    fun p hp => ⟨p.1, Prod.ext rfl hp.symm⟩

end Twist

/-! ### The extension tensored with a representation -/

section Compare

variable {k G : Type u} [CommRing k] [Group G] (A M : Rep k G)

/-- **The comparison of the sum of a representation and the base ring tensored with a
representation and the sum of the tensor product and that representation.** -/
def cocycleTensorEquiv :
    ((↥A.V × k) ⊗[k] ↥M.V) ≃ₗ[k] ((↥A.V ⊗[k] ↥M.V) × ↥M.V) :=
  (TensorProduct.prodLeft k k ↥A.V k ↥M.V).trans
    ((LinearEquiv.refl k (↥A.V ⊗[k] ↥M.V)).prodCongr (TensorProduct.lid k ↥M.V))

variable {A M}

@[simp]
theorem cocycleTensorEquiv_tmul (a : ↥A.V) (c : k) (m : ↥M.V) :
    cocycleTensorEquiv A M ((a, c) ⊗ₜ[k] m) = (a ⊗ₜ[k] m, c • m) := rfl

variable (A M) (b : groupCohomology.cocycles₁ A)

theorem cocycleTensorEquiv_equivariant (τ : G) :
    (cocycleTensorEquiv A M).toLinearMap ∘ₗ (tensorObj (cocycleObj A b) M).ρ τ
      = (cocycleTensorObj A b M).ρ τ ∘ₗ (cocycleTensorEquiv A M).toLinearMap := by
  refine TensorProduct.ext' fun p m => ?_
  obtain ⟨a, c⟩ := p
  show cocycleTensorEquiv A M ((A.ρ τ a + c • b τ, c) ⊗ₜ[k] M.ρ τ m)
    = (tensorRho A M τ (a ⊗ₜ[k] m) + (b τ) ⊗ₜ[k] M.ρ τ (c • m), M.ρ τ (c • m))
  rw [cocycleTensorEquiv_tmul, tensorRho_tmul, map_smul, TensorProduct.add_tmul,
    TensorProduct.smul_tmul]

/-- **The extension attached to a cocycle, tensored with a representation, is the tensored
extension.** -/
def cocycleTensorIso : tensorObj (cocycleObj A b) M ≅ cocycleTensorObj A b M :=
  Action.mkIso (cocycleTensorEquiv A M).toModuleIso fun τ => by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    exact LinearMap.congr_fun (cocycleTensorEquiv_equivariant A M b τ) t

end Compare

end

end InverseGalois.CFT.Tate
