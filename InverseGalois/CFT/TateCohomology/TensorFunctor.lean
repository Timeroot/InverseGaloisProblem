/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Tensor

/-!
# Tensoring a short exact sequence of representations

Tensoring with a fixed representation carries a map of representations to a map of representations:
the underlying map acts on the first factor and leaves the second alone, and it commutes with the
diagonal action because each factor is moved separately.  Composition and identities are respected
factor by factor, so an isomorphism of representations stays an isomorphism after tensoring.

A short complex is therefore carried to a short complex.  Tensoring is always right exact, so the
map to the quotient stays surjective and the image of the sub is still the whole kernel; the one
thing that can fail is the injectivity of the map from the sub, and that is exactly what flatness of
the fixed representation supplies.  So **a short exact sequence tensored with a flat representation
is short exact.**

## Main definitions

* `InverseGalois.CFT.Tate.tensorHomLeft`: a map of representations, tensored on the right with a
  representation.
* `InverseGalois.CFT.Tate.tensorIsoLeft`: an isomorphism of representations, tensored on the right
  with a representation.
* `InverseGalois.CFT.Tate.tensorSeq`: a short complex of representations, tensored on the right
  with a representation.

## Main results

* `InverseGalois.CFT.Tate.tensorSeq_shortExact`: **a short exact sequence of representations
  tensored with a flat representation is short exact.**

## Tags

Tate cohomology, tensor product, flat module, short exact sequence
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

section Functor

variable {k G : Type u} [CommRing k] [Group G] (M : Rep k G)

/-- **A map of representations, tensored on the right with a representation.** -/
def tensorHomLeft {A B : Rep k G} (Φ : A ⟶ B) : tensorObj A M ⟶ tensorObj B M :=
  mkHom (LinearMap.rTensor ↥M.V Φ.hom.hom) fun g => by
    refine TensorProduct.ext' fun a m => ?_
    have h := LinearMap.congr_fun (hom_equivariant Φ g) a
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    show Φ.hom.hom (A.ρ g a) ⊗ₜ[k] M.ρ g m = B.ρ g (Φ.hom.hom a) ⊗ₜ[k] M.ρ g m
    rw [h]

@[simp]
theorem tensorHomLeft_hom {A B : Rep k G} (Φ : A ⟶ B) :
    (tensorHomLeft M Φ).hom.hom = LinearMap.rTensor ↥M.V Φ.hom.hom := rfl

/-- **Two maps out of a tensor product agree as soon as they agree on the pure tensors.** -/
theorem tensorHomLeft_ext {A B : Rep k G} {Φ Ψ : tensorObj A M ⟶ B}
    (h : ∀ (a : ↥A.V) (m : ↥M.V), Φ.hom.hom (a ⊗ₜ[k] m) = Ψ.hom.hom (a ⊗ₜ[k] m)) : Φ = Ψ :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (TensorProduct.ext' h))

theorem tensorHomLeft_comp {A B C : Rep k G} (Φ : A ⟶ B) (Ψ : B ⟶ C) :
    tensorHomLeft M Φ ≫ tensorHomLeft M Ψ = tensorHomLeft M (Φ ≫ Ψ) :=
  tensorHomLeft_ext M fun _ _ => rfl

theorem tensorHomLeft_id (A : Rep k G) : tensorHomLeft M (𝟙 A) = 𝟙 (tensorObj A M) :=
  tensorHomLeft_ext M fun _ _ => rfl

/-- **An isomorphism of representations, tensored on the right with a representation.** -/
def tensorIsoLeft {A B : Rep k G} (e : A ≅ B) : tensorObj A M ≅ tensorObj B M where
  hom := tensorHomLeft M e.hom
  inv := tensorHomLeft M e.inv
  hom_inv_id := by rw [tensorHomLeft_comp, e.hom_inv_id, tensorHomLeft_id]
  inv_hom_id := by rw [tensorHomLeft_comp, e.inv_hom_id, tensorHomLeft_id]

end Functor

/-! ### A short complex tensored with a representation -/

section Sequence

variable {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (X : ShortComplex (Rep k G))

/-- **A short complex of representations, tensored on the right with a representation.** -/
def tensorSeq : ShortComplex (Rep k G) where
  X₁ := tensorObj X.X₁ M
  X₂ := tensorObj X.X₂ M
  X₃ := tensorObj X.X₃ M
  f := tensorHomLeft M X.f
  g := tensorHomLeft M X.g
  zero := by
    refine tensorHomLeft_ext M fun a m => ?_
    have h : X.g.hom.hom (X.f.hom.hom a) = 0 :=
      congrArg (fun φ : X.X₁ ⟶ X.X₃ => φ.hom.hom a) X.zero
    show X.g.hom.hom (X.f.hom.hom a) ⊗ₜ[k] m = 0
    rw [h, TensorProduct.zero_tmul]

variable {X}

/-- **A short exact sequence of representations tensored with a flat representation is short
exact.** -/
theorem tensorSeq_shortExact [Module.Flat k ↥M.V] (hX : X.ShortExact) :
    (tensorSeq M X).ShortExact := by
  have hex : Function.Exact X.f.hom.hom X.g.hom.hom :=
    LinearMap.exact_iff.2 (shortExact_range_eq_ker hX).symm
  refine shortExact_of_linearMap
    (Module.Flat.rTensor_preserves_injective_linearMap _ (shortExact_injective hX))
    (LinearMap.rTensor_surjective _ (shortExact_surjective hX)) fun x hx => ?_
  exact (rTensor_exact ↥M.V hex (shortExact_surjective hX) x).1 hx

end Sequence

end

end InverseGalois.CFT.Tate
