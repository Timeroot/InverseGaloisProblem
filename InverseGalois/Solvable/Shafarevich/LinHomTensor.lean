/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.IntLinHom
import InverseGalois.CFT.GroupCohomology.Duality

/-!
# The maps out of a finite dimensional representation are a tensor product with its dual

Global duality hands back a class whose coefficients are the maps of one representation into
another; the ladder that builds a solvable extension carries a layer tensored with a fixed module.
The two are the same coefficients, because a linear map out of a finite dimensional space is a sum
of a value against a linear form: the maps of one representation into another are the target
tensored with the dual of the source, and the group acts diagonally on the tensor product exactly as
it acts by conjugation on the maps.

Both descriptions are natural in the target.  Following a map of the target after a linear map is,
on the tensor product, the map applied to the left factor alone; that is precisely the shape of the
map of coefficients the ladder produces from a shrinking, so the identification carries the whole
compatibility across.

The section closes with the transport that the identification is for: two isomorphic pairs of
coefficients joined by a commuting square give the same vanishing in first homology, because an
isomorphism of coefficients induces an injection on homology.

## Main definitions

* `InverseGalois.Shafarevich.linHomTensorEquiv` — the target tensored with the dual of the source
  is the maps of the source into the target.
* `InverseGalois.Shafarevich.linHomTensorIso` — **the same, as an isomorphism of representations.**

## Main results

* `InverseGalois.Shafarevich.linHomTensorIso_naturality` — **the identification is compatible with a
  map of the target.**
* `InverseGalois.Shafarevich.map_eq_zero_of_isoSquare` — **a commuting square of isomorphisms
  carries the vanishing of a first homology class across.**

## Tags

group representation, duality, tensor product, group homology, Shafarevich's theorem
-/

namespace InverseGalois.Shafarevich

open CategoryTheory InverseGalois.CFT InverseGalois.CFT.Tate

open scoped TensorProduct

noncomputable section

/-! ### The maps out of a representation, as a tensor product -/

section LinHomTensor

variable {k G : Type} [Field k] [Group G] (M L : Rep k G) [FiniteDimensional k ↥M.V]

/-- **The target tensored with the dual of the source is the maps of the source into the
target.** -/
def linHomTensorEquiv : (↥L.V ⊗[k] Module.Dual k ↥M.V) ≃ₗ[k] (↥M.V →ₗ[k] ↥L.V) :=
  (TensorProduct.comm k ↥L.V (Module.Dual k ↥M.V)).trans (dualTensorHomEquiv k ↥M.V ↥L.V)

@[simp]
theorem linHomTensorEquiv_tmul (l : ↥L.V) (χ : Module.Dual k ↥M.V) (a : ↥M.V) :
    linHomTensorEquiv M L (l ⊗ₜ[k] χ) a = χ a • l := by
  simp [linHomTensorEquiv]

/-- The identification carries the diagonal action to the action by conjugation. -/
theorem linHomTensorEquiv_equivariant (g : G) :
    (linHomTensorEquiv M L).toLinearMap ∘ₗ
        (Rep.of (Representation.tprod L.ρ (dualRep M).ρ)).ρ g
      = (linHomObj M L).ρ g ∘ₗ (linHomTensorEquiv M L).toLinearMap := by
  refine TensorProduct.ext' fun l χ => LinearMap.ext fun a => ?_
  show linHomTensorEquiv M L (TensorProduct.map (L.ρ g) ((dualRep M).ρ g) (l ⊗ₜ[k] χ)) a
    = L.ρ g (linHomTensorEquiv M L (l ⊗ₜ[k] χ) (M.ρ g⁻¹ a))
  rw [TensorProduct.map_tmul, linHomTensorEquiv_tmul, linHomTensorEquiv_tmul,
    dualRep_ρ_apply, map_smul]

/-- **The target tensored with the dual of the source is the maps of the source into the target**,
as an isomorphism of representations. -/
def linHomTensorIso : Rep.of (Representation.tprod L.ρ (dualRep M).ρ) ≅ linHomObj M L :=
  Action.mkIso (linHomTensorEquiv M L).toModuleIso fun g =>
    ModuleCat.hom_ext (linHomTensorEquiv_equivariant M L g)

@[simp]
theorem linHomTensorIso_hom_apply (x : ↥L.V ⊗[k] Module.Dual k ↥M.V) :
    (linHomTensorIso M L).hom.hom x = linHomTensorEquiv M L x := rfl

variable {L}

/-- **The identification is compatible with a map of the target.**  Following a map of the target
after a linear map is, on the tensor product, that map applied to the left factor alone. -/
theorem linHomTensorIso_naturality {L' : Rep k G} (ψ : L ⟶ L')
    (Ψ : Rep.of (Representation.tprod L.ρ (dualRep M).ρ) ⟶
      Rep.of (Representation.tprod L'.ρ (dualRep M).ρ))
    (hΨ : ∀ x, Ψ.hom x = LinearMap.rTensor (Module.Dual k ↥M.V) ψ.hom.hom x) :
    (linHomTensorIso M L).hom ≫ linHomPostHom M ψ = Ψ ≫ (linHomTensorIso M L').hom := by
  refine Action.hom_ext _ _ (ModuleCat.hom_ext (TensorProduct.ext' fun l χ => ?_))
  refine LinearMap.ext fun a => ?_
  show ψ.hom.hom (linHomTensorEquiv M L (l ⊗ₜ[k] χ) a)
    = linHomTensorEquiv M L' (Ψ.hom (l ⊗ₜ[k] χ)) a
  rw [hΨ, LinearMap.rTensor_tmul, linHomTensorEquiv_tmul, linHomTensorEquiv_tmul, map_smul]

end LinHomTensor

/-! ### Carrying a vanishing across a square of isomorphisms -/

section Transport

variable {k G : Type} [CommRing k] [Group G] {X Y X' Y' : Rep k G}

/-- An isomorphism of the coefficients is undone in first homology by its inverse. -/
theorem map_map_iso_inv (e : X ≅ Y) (x : groupHomology.H1 X) :
    groupHomology.map (B := X) (MonoidHom.id G) e.inv 1
        (groupHomology.map (B := Y) (MonoidHom.id G) e.hom 1 x) = x := by
  rw [← ModuleCat.comp_apply, ← groupHomology.map_id_comp, e.hom_inv_id, groupHomology.map_id]
  rfl

/-- **A commuting square of isomorphisms carries the vanishing of a first homology class across.**
The class is moved back along the isomorphism on the left, and the vanishing of the image of that
preimage under the map on the left is, along the square, the vanishing of the image of the class
under the map on the right. -/
theorem map_eq_zero_of_isoSquare (e : X ≅ Y) (e' : X' ≅ Y') (u : X ⟶ X') (v : Y ⟶ Y')
    (h : e.hom ≫ v = u ≫ e'.hom) (x : groupHomology.H1 Y)
    (hu : groupHomology.map (B := X') (MonoidHom.id G) u 1
      (groupHomology.map (B := X) (MonoidHom.id G) e.inv 1 x) = 0) :
    groupHomology.map (B := Y') (MonoidHom.id G) v 1 x = 0 := by
  have hx : groupHomology.map (B := Y) (MonoidHom.id G) e.hom 1
      (groupHomology.map (B := X) (MonoidHom.id G) e.inv 1 x) = x := map_map_iso_inv e.symm x
  rw [← hx, ← ModuleCat.comp_apply, ← groupHomology.map_id_comp, h, groupHomology.map_id_comp,
    ModuleCat.comp_apply, hu, _root_.map_zero]

end Transport

end

end InverseGalois.Shafarevich
