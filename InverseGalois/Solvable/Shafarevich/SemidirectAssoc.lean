/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Splitting a semidirect product with a product kernel

A group acting on each of two groups acts on their product, and a semidirect product by that
diagonal action can be taken apart one factor at a time:

`(A × B) ⋊ U ≅ A ⋊ (B ⋊ U)`,

where the outer factor `B ⋊ U` acts on `A` through its projection to `U`.  Applied repeatedly this
turns a semidirect product whose kernel is a direct product of finitely many groups into an iterated
semidirect product with one factor at each stage; for a finite nilpotent kernel, whose factors are
its Sylow subgroups, that is the reduction of a split extension with nilpotent kernel to a chain of
split extensions with kernels of prime power order.

## Main results

* `MonoidHom.prodAut` — the diagonal action of `U` on `A × B` induced by actions on `A` and on `B`.
* `SemidirectProduct.prodAssoc` — the isomorphism `(A × B) ⋊ U ≃* A ⋊ (B ⋊ U)`.
* `MulAut.restrictChar` — an automorphism of a group restricts to a characteristic subgroup, so a
  group acting on `H` acts on every characteristic subgroup of `H`.

Transporting a semidirect product along an isomorphism of its kernel is `SemidirectProduct.congr'`.
-/

namespace MulAut

variable {G : Type*} [Group G]

/-- **An automorphism restricts to a characteristic subgroup.** -/
def restrictChar (H : Subgroup G) [H.Characteristic] : MulAut G →* MulAut H where
  toFun e :=
    (e.subgroupMap H).trans
      (MulEquiv.subgroupCongr (Subgroup.characteristic_iff_map_eq.mp ‹_› e))
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem restrictChar_apply_coe (H : Subgroup G) [H.Characteristic] (e : MulAut G) (x : H) :
    ((restrictChar H e x : H) : G) = e x :=
  rfl

end MulAut

namespace MonoidHom

variable {A B U : Type*} [Group A] [Group B] [Group U]

/-- **A group acting on two groups acts diagonally on their product.** -/
@[simps]
def prodAut (φ : U →* MulAut A) (ψ : U →* MulAut B) : U →* MulAut (A × B) where
  toFun u := (φ u).prodCongr (ψ u)
  map_one' := by ext <;> simp [MulEquiv.prodCongr]
  map_mul' u v := by ext <;> simp [MulEquiv.prodCongr]

end MonoidHom

namespace SemidirectProduct

variable {A B U : Type*} [Group A] [Group B] [Group U]

/-- **A semidirect product whose kernel is a direct product splits into two stages.**

The kernel `A × B` can be adjoined one factor at a time: first `B`, then `A`, the latter acted on
through the projection of `B ⋊ U` onto `U`. -/
def prodAssoc (φ : U →* MulAut A) (ψ : U →* MulAut B) :
    (A × B) ⋊[φ.prodAut ψ] U ≃* A ⋊[φ.comp (rightHom : B ⋊[ψ] U →* U)] (B ⋊[ψ] U) where
  toFun x := ⟨x.left.1, ⟨x.left.2, x.right⟩⟩
  invFun y := ⟨(y.left, y.right.left), y.right.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem prodAssoc_apply (φ : U →* MulAut A) (ψ : U →* MulAut B) (x : (A × B) ⋊[φ.prodAut ψ] U) :
    prodAssoc φ ψ x = ⟨x.left.1, ⟨x.left.2, x.right⟩⟩ :=
  rfl

@[simp]
theorem prodAssoc_symm_apply (φ : U →* MulAut A) (ψ : U →* MulAut B)
    (y : A ⋊[φ.comp (rightHom : B ⋊[ψ] U →* U)] (B ⋊[ψ] U)) :
    (prodAssoc φ ψ).symm y = ⟨(y.left, y.right.left), y.right.right⟩ :=
  rfl

end SemidirectProduct
