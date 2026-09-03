/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorFunctor

/-!
# Tensoring in the second variable

Tensoring with a fixed representation on the *left* carries a map of representations to a map of
representations just as tensoring on the right does: the underlying map acts on the second factor
and leaves the first alone, and it commutes with the diagonal action because each factor is moved
separately.  Composition and identities are respected factor by factor, so an isomorphism stays an
isomorphism, and a short complex is carried to a short complex.

Tensoring is right exact on either side, so the map to the quotient stays surjective and the image
of the sub is still the whole kernel; only the injectivity of the map from the sub can fail, and
flatness of the fixed representation supplies it.  So **a short exact sequence of coefficients
tensored with a flat representation is short exact.**

The two variables are needed together: the first is where a class formation sits and the second is
where the coefficients of an embedding problem sit, and the correction term in the theorem of Tate
and Nakayama is computed by resolving the coefficients.

## Main definitions

* `InverseGalois.CFT.Tate.tensorHomRight`: a map of representations, tensored on the left with a
  representation.
* `InverseGalois.CFT.Tate.tensorIsoRight`: an isomorphism of representations, tensored on the left
  with a representation.
* `InverseGalois.CFT.Tate.tensorSeqRight`: a short complex of representations, tensored on the left
  with a representation.

## Main results

* `InverseGalois.CFT.Tate.tensorSeqRight_shortExact`: **a short exact sequence of representations
  tensored on the left with a flat representation is short exact.**
* `InverseGalois.CFT.Tate.tensorHomRight_surjective`,
  `InverseGalois.CFT.Tate.exists_tensorHomRight_eq`: right exactness of the tensor product in the
  second variable.

## Tags

Tate cohomology, tensor product, flat module, short exact sequence
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

section Functor

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-- **A map of representations, tensored on the left with a representation.** -/
def tensorHomRight {M N : Rep k G} (Φ : M ⟶ N) : tensorObj A M ⟶ tensorObj A N :=
  mkHom (LinearMap.lTensor ↥A.V Φ.hom.hom) fun g => by
    refine TensorProduct.ext' fun a m => ?_
    have h := LinearMap.congr_fun (hom_equivariant Φ g) m
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    show A.ρ g a ⊗ₜ[k] Φ.hom.hom (M.ρ g m) = A.ρ g a ⊗ₜ[k] N.ρ g (Φ.hom.hom m)
    rw [h]

@[simp]
theorem tensorHomRight_hom {M N : Rep k G} (Φ : M ⟶ N) :
    (tensorHomRight A Φ).hom.hom = LinearMap.lTensor ↥A.V Φ.hom.hom := rfl

/-- **Two maps out of a tensor product agree as soon as they agree on the pure tensors.** -/
theorem tensorHomRight_ext {M B : Rep k G} {Φ Ψ : tensorObj A M ⟶ B}
    (h : ∀ (a : ↥A.V) (m : ↥M.V), Φ.hom.hom (a ⊗ₜ[k] m) = Ψ.hom.hom (a ⊗ₜ[k] m)) : Φ = Ψ :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (TensorProduct.ext' h))

theorem tensorHomRight_comp {M N P : Rep k G} (Φ : M ⟶ N) (Ψ : N ⟶ P) :
    tensorHomRight A Φ ≫ tensorHomRight A Ψ = tensorHomRight A (Φ ≫ Ψ) :=
  tensorHomRight_ext A fun _ _ => rfl

theorem tensorHomRight_id (M : Rep k G) : tensorHomRight A (𝟙 M) = 𝟙 (tensorObj A M) :=
  tensorHomRight_ext A fun _ _ => rfl

/-- **An isomorphism of representations, tensored on the left with a representation.** -/
def tensorIsoRight {M N : Rep k G} (e : M ≅ N) : tensorObj A M ≅ tensorObj A N where
  hom := tensorHomRight A e.hom
  inv := tensorHomRight A e.inv
  hom_inv_id := by rw [tensorHomRight_comp, e.hom_inv_id, tensorHomRight_id]
  inv_hom_id := by rw [tensorHomRight_comp, e.inv_hom_id, tensorHomRight_id]

end Functor

/-! ### A short complex tensored with a representation -/

section Sequence

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (Y : ShortComplex (Rep k G))

/-- **A short complex of representations, tensored on the left with a representation.** -/
def tensorSeqRight : ShortComplex (Rep k G) where
  X₁ := tensorObj A Y.X₁
  X₂ := tensorObj A Y.X₂
  X₃ := tensorObj A Y.X₃
  f := tensorHomRight A Y.f
  g := tensorHomRight A Y.g
  zero := by
    refine tensorHomRight_ext A fun a m => ?_
    have h : Y.g.hom.hom (Y.f.hom.hom m) = 0 :=
      congrArg (fun φ : Y.X₁ ⟶ Y.X₃ => φ.hom.hom m) Y.zero
    show a ⊗ₜ[k] Y.g.hom.hom (Y.f.hom.hom m) = 0
    rw [h, TensorProduct.tmul_zero]

variable {Y}

/-- **The tensor product is right exact in the second variable**: the map on the quotient stays
surjective. -/
theorem tensorHomRight_surjective (hY : Y.ShortExact) :
    Function.Surjective (tensorHomRight A Y.g).hom.hom :=
  LinearMap.lTensor_surjective _ (shortExact_surjective hY)

/-- **The tensor product is right exact in the second variable**: everything killed by the map to
the quotient comes from the sub. -/
theorem exists_tensorHomRight_eq (hY : Y.ShortExact) (x : ↥(tensorObj A Y.X₂).V)
    (hx : (tensorHomRight A Y.g).hom.hom x = 0) :
    ∃ y : ↥(tensorObj A Y.X₁).V, (tensorHomRight A Y.f).hom.hom y = x := by
  have hex : Function.Exact Y.f.hom.hom Y.g.hom.hom :=
    LinearMap.exact_iff.2 (shortExact_range_eq_ker hY).symm
  exact (lTensor_exact ↥A.V hex (shortExact_surjective hY) x).1 hx

/-- **A short exact sequence of representations tensored on the left with a flat representation is
short exact.** -/
theorem tensorSeqRight_shortExact [Module.Flat k ↥A.V] (hY : Y.ShortExact) :
    (tensorSeqRight A Y).ShortExact :=
  shortExact_of_linearMap
    (Module.Flat.lTensor_preserves_injective_linearMap _ (shortExact_injective hY))
    (tensorHomRight_surjective A hY) (exists_tensorHomRight_eq A hY)

end Sequence

end

end InverseGalois.CFT.Tate
