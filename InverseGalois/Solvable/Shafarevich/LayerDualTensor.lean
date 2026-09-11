/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.GenericHomology

/-!
# A linear map out of a dual space, read inside a tensor product

The counting argument annihilates elements of a tensor product of the zeroth layer with a layer,
and what the arithmetic hands it is not an element of that product but a linear map from the dual
of the zeroth layer to the layer.  Over a field of finite dimension the two are the same thing: a
basis being named, the map is the sum of the basis vectors against its values on the dual basis,
and contracting that sum against a functional of the target of a comparison map returns the value
of the map at the functional pulled back.

That contraction is all the dictionary the assembly needs.  An element of the product being killed
by a comparison map, its contraction against every functional vanishes, so the value of the linear
map at every pulled back functional is killed by the comparison map on the layer — which is the
statement the reciprocity residue is asked to satisfy.

## Main definitions

* `InverseGalois.Shafarevich.contractDual` — the contraction of a tensor product against a
  functional on the first factor.
* `InverseGalois.Shafarevich.dualTensorElt` — **the element of the tensor product naming a linear
  map out of the dual space.**

## Main results

* `InverseGalois.Shafarevich.contractDual_map_dualTensorElt` — **contracting the comparison of the
  naming element against a functional returns the value of the map at the pulled back
  functional.**
* `InverseGalois.Shafarevich.eq_zero_of_map_dualTensorElt_eq_zero` — **a naming element killed by a
  comparison map has all its pulled back values killed.**
* `InverseGalois.Shafarevich.exists_operatorHom_tensor_eq_zero` — **finitely many elements of the
  tensor product of the zeroth layer with a layer and a module of coefficients are annihilated at
  once by a surjective equivariant homomorphism onto the intended rank.**

## Tags

tensor product, dual space, basis, Shafarevich's theorem, embedding problem
-/

open scoped TensorProduct

namespace InverseGalois.Shafarevich

/-! ### Contracting against a functional -/

section Contract

variable {𝕜 : Type*} [Field 𝕜] {V M : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup M]
  [Module 𝕜 M]

/-- The contraction of a tensor product against a functional on the first factor, the last factor
being the field itself. -/
noncomputable def contractDual (η : Module.Dual 𝕜 V) : V ⊗[𝕜] (M ⊗[𝕜] 𝕜) →ₗ[𝕜] M :=
  (TensorProduct.rid 𝕜 M).toLinearMap ∘ₗ (TensorProduct.lid 𝕜 (M ⊗[𝕜] 𝕜)).toLinearMap ∘ₗ
    TensorProduct.map η LinearMap.id

/-- The contraction of a pure tensor is the product of the value of the functional with the last
factor, acting on the middle one. -/
theorem contractDual_tmul (η : Module.Dual 𝕜 V) (x : V) (m : M) (s : 𝕜) :
    contractDual η (x ⊗ₜ[𝕜] (m ⊗ₜ[𝕜] s)) = (η x * s) • m := by
  show (TensorProduct.rid 𝕜 M) ((TensorProduct.lid 𝕜 (M ⊗[𝕜] 𝕜))
    (TensorProduct.map η LinearMap.id (x ⊗ₜ[𝕜] (m ⊗ₜ[𝕜] s)))) = _
  rw [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, TensorProduct.lid_tmul,
    TensorProduct.smul_tmul', TensorProduct.rid_tmul, smul_smul, mul_comm s (η x)]

end Contract

/-! ### The naming element -/

section Naming

variable {𝕜 : Type*} [Field 𝕜] {V M V' M' : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup M]
  [Module 𝕜 M] [AddCommGroup V'] [Module 𝕜 V'] [AddCommGroup M'] [Module 𝕜 M'] {ι : Type*}
  [Fintype ι]

/-- **The element of the tensor product naming a linear map out of the dual space**: the sum of the
basis vectors against the values of the map on the dual basis. -/
noncomputable def dualTensorElt (b : Module.Basis ι 𝕜 V) (W : Module.Dual 𝕜 V →ₗ[𝕜] M) :
    V ⊗[𝕜] (M ⊗[𝕜] 𝕜) :=
  ∑ i, b i ⊗ₜ[𝕜] (W (b.coord i) ⊗ₜ[𝕜] (1 : 𝕜))

/-- **Contracting the comparison of the naming element against a functional returns the value of
the map at the pulled back functional.**  The sum of the values of the pulled back functional on
the basis against the dual basis is the pulled back functional itself. -/
theorem contractDual_map_dualTensorElt (b : Module.Basis ι 𝕜 V) (W : Module.Dual 𝕜 V →ₗ[𝕜] M)
    (f : V →ₗ[𝕜] V') (g : M →ₗ[𝕜] M') (η : Module.Dual 𝕜 V') :
    contractDual η (TensorProduct.map f (TensorProduct.map g LinearMap.id)
      (dualTensorElt b W)) = g (W (η.comp f)) := by
  rw [dualTensorElt, map_sum, map_sum]
  have hstep : ∀ i : ι, contractDual η (TensorProduct.map f (TensorProduct.map g LinearMap.id)
      (b i ⊗ₜ[𝕜] (W (b.coord i) ⊗ₜ[𝕜] (1 : 𝕜)))) = (η.comp f) (b i) • g (W (b.coord i)) := by
    intro i
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
      contractDual_tmul, mul_one]
    rfl
  calc ∑ i, contractDual η (TensorProduct.map f (TensorProduct.map g LinearMap.id)
        (b i ⊗ₜ[𝕜] (W (b.coord i) ⊗ₜ[𝕜] (1 : 𝕜))))
      = g (W (∑ i, (η.comp f) (b i) • b.coord i)) := by
        rw [map_sum, map_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [hstep i, map_smul, map_smul]
    _ = g (W (η.comp f)) := by rw [b.sum_dual_apply_smul_coord]

/-- **A naming element killed by a comparison map has all its pulled back values killed.** -/
theorem eq_zero_of_map_dualTensorElt_eq_zero (b : Module.Basis ι 𝕜 V) (W : Module.Dual 𝕜 V →ₗ[𝕜] M)
    (f : V →ₗ[𝕜] V') (g : M →ₗ[𝕜] M')
    (h : TensorProduct.map f (TensorProduct.map g LinearMap.id) (dualTensorElt b W) = 0)
    (η : Module.Dual 𝕜 V') : g (W (η.comp f)) = 0 := by
  rw [← contractDual_map_dualTensorElt b W f g η, h, map_zero]

end Naming

/-! ### The counting argument in the tensor product -/

section GenericTensor

variable (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S] [Finite S]

/-- **Finitely many elements of the tensor product of the zeroth layer of a generic operator group
with a layer and a fixed module of coefficients are annihilated at once by a surjective equivariant
homomorphism onto the intended rank.** -/
theorem exists_operatorHom_tensor_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S) {j t : ℕ}
    (T : Type*) [AddCommGroup T] [Module (ZMod ℓ) T] [Module.Finite (ZMod ℓ) T] :
    ∃ q : ℕ, ∀ v : Fin t → Layer ℓ (Generic U q S) 0 ⊗[ZMod ℓ]
        (Layer ℓ (Generic U q S) j ⊗[ZMod ℓ] T),
      ∃ α : Generic U q S →* Generic U n S, IsOperatorHom α ∧ Function.Surjective α ∧
        ∀ ν, TensorProduct.map (layerLinear ℓ α 0)
          (TensorProduct.map (layerLinear ℓ α j) LinearMap.id) (v ν) = 0 := by
  set r : ℕ := (j + 2) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) 0 ⊗[ZMod ℓ]
    (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T))) + 1 with hrdef
  have hr : (j + 2) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) 0 ⊗[ZMod ℓ]
      (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T))) < r := by rw [hrdef]; exact Nat.lt_succ_self _
  refine ⟨r * n, fun v => ?_⟩
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_tensor_eq_zero U r n S hS T hr v
  exact ⟨genericShrink U r n S a, isOperatorHom_genericShrink U r n S a, hsurj, ha⟩

end GenericTensor

end InverseGalois.Shafarevich
