/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerTensor
import InverseGalois.Solvable.Shafarevich.LayerHomology
import InverseGalois.Solvable.Shafarevich.HomologyOne
import InverseGalois.Solvable.Shafarevich.SemidirectHomology

/-!
# Killing first homology classes of a generic operator group

A generic operator group of rank `r * n` shrinks onto one of rank `n` in many ways, and each way is
compatible with the operators.  The shrinking homomorphisms are therefore homomorphisms of the
semidirect products with the operator group, and they act on the first homology of those semidirect
products with coefficients in a layer of the generic group tensored with a fixed representation of
the operator group.

The main result is that a prescribed finite family of first homology classes can be annihilated all
at once by one surjective equivariant homomorphism onto the intended rank, provided the rank one
starts from is large enough.  The proof is the tail of the homological Hochschild–Serre sequence of
the semidirect product: a class dies in the homology of the operator group after a first shrinking,
which is a counting statement about the layer with coefficients; it then comes from the homology of
the generic group itself, where the coefficients are trivial and the first homology is the zeroth
layer tensored with the coefficients, so a second counting statement finishes the argument.

## Main definitions

* `InverseGalois.Shafarevich.genericLayerTensor` — a layer of a generic operator group tensored
  with a fixed representation of the operator group.
* `InverseGalois.Shafarevich.genericInflate` — those coefficients, read on the semidirect product.
* `InverseGalois.Shafarevich.IsOperatorHom` — a homomorphism of generic operator groups commuting
  with the operators.
* `InverseGalois.Shafarevich.operatorSemidirect` — such a homomorphism, extended to the semidirect
  products.

## Main results

* `InverseGalois.Shafarevich.map_rightHom_naturality` — the projection to the operator group is
  natural in an equivariant homomorphism.
* `InverseGalois.Shafarevich.map_inl_naturality` — the inclusion of the generic group is natural in
  a homomorphism of generic operator groups.
* `InverseGalois.Shafarevich.exists_operatorHom_h1_eq_zero` — **finitely many first homology classes
  of a generic operator group extended by the operator group, with coefficients in a layer tensored
  with a fixed representation, are annihilated at once by one surjective equivariant homomorphism
  onto the intended rank.**

## Tags

group homology, semidirect product, generic operator group, Shafarevich's theorem
-/

namespace InverseGalois.Shafarevich

open CategoryTheory

open scoped TensorProduct

/-! ### Layers, linearly -/

/-- The linear map between layers induced by a composite. -/
theorem layerLinear_comp {P Q R : Type*} [Group P] [Group Q] [Group R] (p : ℕ) (g : Q →* R)
    (f : P →* Q) (n : ℕ) :
    layerLinear p (g.comp f) n = (layerLinear p g n).comp (layerLinear p f n) :=
  LinearMap.ext fun v => by
    simp only [layerLinear_apply, LinearMap.comp_apply, layerMap_comp, AddMonoidHom.comp_apply]

/-! ### A layer with coefficients -/

section Tensor

variable (U : Type) [Group U] (n : ℕ) (S : Type) [Group S]

/-- A layer of a generic operator group tensored with a fixed module of coefficients. -/
noncomputable abbrev genericLayerTensor (ℓ j : ℕ) (T : Rep (ZMod ℓ) U) : Rep (ZMod ℓ) U :=
  Rep.of (Representation.tprod (genericLayerRep U n S ℓ j) T.ρ)

/-- Those coefficients, read as a representation of the semidirect product. -/
noncomputable abbrev genericInflate (ℓ j : ℕ) (T : Rep (ZMod ℓ) U) :
    Rep (ZMod ℓ) (Generic U n S ⋊[genericAut U n S] U) :=
  inflate (genericAut U n S) (genericLayerTensor U n S ℓ j T)

end Tensor

/-! ### Equivariant homomorphisms -/

section Operator

variable {U : Type} [Group U] {S : Type} [Group S] {l m n : ℕ}

/-- A homomorphism of generic operator groups commuting with the operators. -/
def IsOperatorHom (α : Generic U m S →* Generic U n S) : Prop :=
  ∀ u : U, α.comp (genericAut U m S u).toMonoidHom = (genericAut U n S u).toMonoidHom.comp α

theorem IsOperatorHom.comp {β : Generic U m S →* Generic U n S}
    {α : Generic U l S →* Generic U m S} (hβ : IsOperatorHom β) (hα : IsOperatorHom α) :
    IsOperatorHom (β.comp α) := fun u => by
  rw [MonoidHom.comp_assoc, hα u, ← MonoidHom.comp_assoc, hβ u, MonoidHom.comp_assoc]

variable {α : Generic U m S →* Generic U n S} {ℓ j : ℕ} {T : Rep (ZMod ℓ) U}

/-- The map of layers induced by an equivariant homomorphism is equivariant. -/
theorem layerMap_isOperatorHom (hα : IsOperatorHom α) (u : U) (v : Layer ℓ (Generic U m S) j) :
    layerMap ℓ α j (genericLayerRep U m S ℓ j u v)
      = genericLayerRep U n S ℓ j u (layerMap ℓ α j v) :=
  layerMap_layerRep _ (hα u) v

/-- The underlying linear map of the morphism of coefficients induced by an equivariant
homomorphism is equivariant. -/
theorem rTensor_layerLinear_comm (hα : IsOperatorHom α) (u : U) :
    (LinearMap.rTensor T.V (layerLinear ℓ α j)).comp
        (TensorProduct.map (genericLayerRep U m S ℓ j u) (T.ρ u))
      = (TensorProduct.map (genericLayerRep U n S ℓ j u) (T.ρ u)).comp
        (LinearMap.rTensor T.V (layerLinear ℓ α j)) := by
  refine TensorProduct.ext' fun x y => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    layerLinear_apply]
  rw [layerMap_isOperatorHom hα]

/-- The morphism of coefficients induced by an equivariant homomorphism. -/
noncomputable def operatorTensorRep (hα : IsOperatorHom α) (ℓ j : ℕ) (T : Rep (ZMod ℓ) U) :
    genericLayerTensor U m S ℓ j T ⟶ genericLayerTensor U n S ℓ j T where
  hom := ModuleCat.ofHom (LinearMap.rTensor T.V (layerLinear ℓ α j))
  comm u := ModuleCat.hom_ext (rTensor_layerLinear_comm hα u)

@[simp]
theorem operatorTensorRep_hom (hα : IsOperatorHom α) :
    (operatorTensorRep hα ℓ j T).hom
      = ModuleCat.ofHom (LinearMap.rTensor T.V (layerLinear ℓ α j)) := rfl

/-- An equivariant homomorphism, extended to the semidirect products. -/
def operatorSemidirect (hα : IsOperatorHom α) :
    Generic U m S ⋊[genericAut U m S] U →* Generic U n S ⋊[genericAut U n S] U :=
  SemidirectProduct.map α (MonoidHom.id U) hα

/-- The morphism of inflated coefficients induced by an equivariant homomorphism. -/
noncomputable def operatorInflateRep (hα : IsOperatorHom α) (ℓ j : ℕ) (T : Rep (ZMod ℓ) U) :
    genericInflate U m S ℓ j T ⟶
      (Action.res _ (operatorSemidirect hα)).obj (genericInflate U n S ℓ j T) where
  hom := ModuleCat.ofHom (LinearMap.rTensor T.V (layerLinear ℓ α j))
  comm g := ModuleCat.hom_ext (rTensor_layerLinear_comm hα (SemidirectProduct.rightHom g))

@[simp]
theorem operatorInflateRep_hom (hα : IsOperatorHom α) :
    (operatorInflateRep hα ℓ j T).hom
      = ModuleCat.ofHom (LinearMap.rTensor T.V (layerLinear ℓ α j)) := rfl

/-- The same morphism, read into the coefficients of the operator group. -/
noncomputable def operatorRightRep (hα : IsOperatorHom α) (ℓ j : ℕ) (T : Rep (ZMod ℓ) U) :
    genericInflate U m S ℓ j T ⟶
      (Action.res _ (SemidirectProduct.rightHom (φ := genericAut U m S))).obj
        (genericLayerTensor U n S ℓ j T) where
  hom := ModuleCat.ofHom (LinearMap.rTensor T.V (layerLinear ℓ α j))
  comm g := ModuleCat.hom_ext (rTensor_layerLinear_comm hα (SemidirectProduct.rightHom g))

@[simp]
theorem operatorRightRep_hom (hα : IsOperatorHom α) :
    (operatorRightRep hα ℓ j T).hom
      = ModuleCat.ofHom (LinearMap.rTensor T.V (layerLinear ℓ α j)) := rfl

/-- The same morphism, read on the kernels of the projections.  Here no equivariance is needed:
the kernels act trivially. -/
noncomputable def operatorInlRep (α : Generic U m S →* Generic U n S) (ℓ j : ℕ)
    (T : Rep (ZMod ℓ) U) :
    (Action.res _ (SemidirectProduct.inl :
        Generic U m S →* Generic U m S ⋊[genericAut U m S] U)).obj
        (genericInflate U m S ℓ j T) ⟶
      (Action.res _ α).obj ((Action.res _ (SemidirectProduct.inl :
        Generic U n S →* Generic U n S ⋊[genericAut U n S] U)).obj
        (genericInflate U n S ℓ j T)) where
  hom := ModuleCat.ofHom (LinearMap.rTensor T.V (layerLinear ℓ α j))
  comm x := by
    show Action.ρ (genericLayerTensor U m S ℓ j T) 1 ≫ _
      = _ ≫ Action.ρ (genericLayerTensor U n S ℓ j T) 1
    simp

@[simp]
theorem operatorInlRep_hom (α : Generic U m S →* Generic U n S) :
    (operatorInlRep α ℓ j T).hom
      = ModuleCat.ofHom (LinearMap.rTensor T.V (layerLinear ℓ α j)) := rfl

theorem operatorInlRep_hom_hom (α : Generic U m S →* Generic U n S) :
    (operatorInlRep α ℓ j T).hom.hom
      = TensorProduct.map (layerLinear ℓ α j) LinearMap.id := rfl

/-! ### Naturality -/

/-- **The projection to the operator group is natural in an equivariant homomorphism.** -/
theorem map_rightHom_naturality (hα : IsOperatorHom α) (ℓ j : ℕ) (T : Rep (ZMod ℓ) U) :
    groupHomology.map (SemidirectProduct.rightHom (φ := genericAut U m S))
        (𝟙 (genericInflate U m S ℓ j T)) 1 ≫
      groupHomology.map (MonoidHom.id U) (operatorTensorRep hα ℓ j T) 1
      = groupHomology.map (operatorSemidirect hα) (operatorInflateRep hα ℓ j T) 1 ≫
        groupHomology.map (SemidirectProduct.rightHom (φ := genericAut U n S))
          (𝟙 (genericInflate U n S ℓ j T)) 1 := by
  rw [← map_comp_of_eq (h := SemidirectProduct.rightHom (φ := genericAut U m S))
        (C := genericLayerTensor U n S ℓ j T)
        (SemidirectProduct.rightHom (φ := genericAut U m S)) (MonoidHom.id U)
        (𝟙 (genericInflate U m S ℓ j T)) (operatorTensorRep hα ℓ j T) (MonoidHom.id_comp _)
        (operatorRightRep hα ℓ j T) (by simp) 1,
      ← map_comp_of_eq (h := SemidirectProduct.rightHom (φ := genericAut U m S))
        (operatorSemidirect hα) (SemidirectProduct.rightHom (φ := genericAut U n S))
        (operatorInflateRep hα ℓ j T) (𝟙 (genericInflate U n S ℓ j T)) rfl
        (operatorRightRep hα ℓ j T) (by simp) 1]

/-- **The inclusion of the kernel is natural in a homomorphism of generic operator groups.** -/
theorem map_inl_naturality (hα : IsOperatorHom α) (ℓ j : ℕ) (T : Rep (ZMod ℓ) U) :
    groupHomology.map (SemidirectProduct.inl :
        Generic U m S →* Generic U m S ⋊[genericAut U m S] U) (𝟙 _) 1 ≫
      groupHomology.map (operatorSemidirect hα) (operatorInflateRep hα ℓ j T) 1
      = groupHomology.map α (operatorInlRep α ℓ j T) 1 ≫
        groupHomology.map (SemidirectProduct.inl :
          Generic U n S →* Generic U n S ⋊[genericAut U n S] U) (𝟙 _) 1 := by
  rw [← map_comp_of_eq (h := (SemidirectProduct.inl :
          Generic U n S →* Generic U n S ⋊[genericAut U n S] U).comp α)
        (SemidirectProduct.inl :
          Generic U m S →* Generic U m S ⋊[genericAut U m S] U) (operatorSemidirect hα) (𝟙 _)
        (operatorInflateRep hα ℓ j T) (SemidirectProduct.map_comp_inl α (MonoidHom.id U) hα)
        (operatorInlRep α ℓ j T) (by simp) 1,
      ← map_comp_of_eq (h := (SemidirectProduct.inl :
          Generic U n S →* Generic U n S ⋊[genericAut U n S] U).comp α)
        α (SemidirectProduct.inl :
          Generic U n S →* Generic U n S ⋊[genericAut U n S] U) (operatorInlRep α ℓ j T) (𝟙 _)
        rfl (operatorInlRep α ℓ j T) (by simp) 1]

/-- **A composite of equivariant homomorphisms induces the composite in homology.** -/
theorem map_operatorSemidirect_comp {β : Generic U m S →* Generic U n S}
    {γ : Generic U l S →* Generic U m S} (hβ : IsOperatorHom β) (hγ : IsOperatorHom γ)
    (ℓ j : ℕ) (T : Rep (ZMod ℓ) U) :
    groupHomology.map (operatorSemidirect (hβ.comp hγ))
        (operatorInflateRep (hβ.comp hγ) ℓ j T) 1
      = groupHomology.map (operatorSemidirect hγ) (operatorInflateRep hγ ℓ j T) 1 ≫
        groupHomology.map (operatorSemidirect hβ) (operatorInflateRep hβ ℓ j T) 1 := by
  refine map_comp_of_eq (operatorSemidirect hγ) (operatorSemidirect hβ)
    (operatorInflateRep hγ ℓ j T) (operatorInflateRep hβ ℓ j T) rfl _ ?_ 1
  simp only [operatorInflateRep_hom, ← ModuleCat.ofHom_comp, ← LinearMap.rTensor_comp]
  rw [layerLinear_comp]

end Operator

/-- A shrinking homomorphism commutes with the operators. -/
theorem isOperatorHom_genericShrink (U : Type) [Group U] (r n : ℕ) (S : Type) [Group S]
    (a : Fin r → ℕ) : IsOperatorHom (genericShrink U r n S a) :=
  genericShrink_comp_genericAut U r n S a

/-! ### The count with coefficients -/

section Count

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

omit [Group U] in
/-- The count in a layer with coefficients, for a family indexed by an arbitrary finite type. -/
theorem exists_genericShrink_forall_rTensor_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j : ℕ} {ι : Type*} [Finite ι] (T : Type*) [AddCommGroup T] [Module (ZMod ℓ) T]
    [Module.Finite (ZMod ℓ) T]
    (hr : (j + 1) * (Nat.card ι *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r)
    (v : ι → Layer ℓ (Generic U (r * n) S) j ⊗[ZMod ℓ] T) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, LinearMap.rTensor T (layerLinear ℓ (genericShrink U r n S a) j) (v ν) = 0 := by
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_rTensor_eq_zero U r n S hS T hr
    (v ∘ (Finite.equivFin ι).symm)
  exact ⟨a, hsurj, fun ν => by simpa using ha (Finite.equivFin ι ν)⟩

/-- **Finitely many homology classes with coefficients in a layer tensored with a fixed module are
annihilated at once by a surjective shrinking homomorphism.** -/
theorem exists_genericShrink_homology_tensor_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t c : ℕ} (T : Rep (ZMod ℓ) U) [Module.Finite (ZMod ℓ) T]
    (hr : (j + 1) * (t * Nat.card U ^ c *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r)
    (x : Fin t → groupHomology (genericLayerTensor U (r * n) S ℓ j T) c) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, groupHomology.map (B := genericLayerTensor U n S ℓ j T) (MonoidHom.id U)
        (operatorTensorRep (isOperatorHom_genericShrink U r n S a) ℓ j T) c (x ν) = 0 := by
  choose z hz using fun ν =>
    (ModuleCat.epi_iff_surjective (groupHomology.π (genericLayerTensor U (r * n) S ℓ j T) c)).1
      inferInstance (x ν)
  have hcard : Nat.card (Fin t × (Fin c → U)) = t * Nat.card U ^ c := by
    simp [Nat.card_prod, Nat.card_fun]
  have hr' : (j + 1) * (Nat.card (Fin t × (Fin c → U)) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r := by rwa [hcard]
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_rTensor_eq_zero U r n S hS T hr'
    fun q : Fin t × (Fin c → U) => cycleFun (z q.1) q.2
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [← hz ν]
  exact homology_map_π_eq_zero _ _ fun g => ha (ν, g)

/-- **Finitely many first homology classes of a generic operator group with coefficients in a layer
tensored with a fixed module are annihilated at once by a surjective shrinking homomorphism.** -/
theorem exists_genericShrink_h1_inl_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S) {j t : ℕ}
    (T : Rep (ZMod ℓ) U) [Module.Finite (ZMod ℓ) T]
    (hr : (j + 2) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) 0 ⊗[ZMod ℓ]
      (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T))) < r)
    (x : Fin t → groupHomology.H1
        ((Action.res _ (SemidirectProduct.inl :
            Generic U (r * n) S →* Generic U (r * n) S ⋊[genericAut U (r * n) S] U)).obj
          (genericInflate U (r * n) S ℓ j T))) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, groupHomology.map (genericShrink U r n S a)
        (operatorInlRep (genericShrink U r n S a) ℓ j T) 1 (x ν) = 0 := by
  choose z hz using fun ν => h1Mk_surjective (x ν)
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_tensor_eq_zero U r n S hS T hr z
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [← hz ν, map_h1Mk, operatorInlRep_hom_hom]
  exact (congrArg (⇑h1Mk) (ha ν)).trans (map_zero _)

end Count

/-! ### Killing first homology classes -/

section Prop7

variable (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S] [Finite S]

/-- **Finitely many first homology classes of a generic operator group with coefficients in a layer
tensored with a fixed module are annihilated at once by a surjective equivariant homomorphism.**
This is the half of the argument that does not see the operator group. -/
theorem exists_operatorHom_h1_inl_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S) {j t : ℕ}
    (T : Rep (ZMod ℓ) U) [Module.Finite (ZMod ℓ) T] :
    ∃ q : ℕ, ∀ x : Fin t → groupHomology.H1
        ((Action.res _ (SemidirectProduct.inl :
            Generic U q S →* Generic U q S ⋊[genericAut U q S] U)).obj
          (genericInflate U q S ℓ j T)),
      ∃ α : Generic U q S →* Generic U n S, IsOperatorHom α ∧ Function.Surjective α ∧
        ∀ ν, groupHomology.map α (operatorInlRep α ℓ j T) 1 (x ν) = 0 := by
  set r : ℕ := (j + 2) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) 0 ⊗[ZMod ℓ]
    (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T))) + 1 with hrdef
  have hr : (j + 2) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) 0 ⊗[ZMod ℓ]
      (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T))) < r := by rw [hrdef]; exact Nat.lt_succ_self _
  refine ⟨r * n, fun x => ?_⟩
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_h1_inl_eq_zero U r n S hS T hr x
  exact ⟨genericShrink U r n S a, isOperatorHom_genericShrink U r n S a, hsurj, ha⟩

/-- **Proposition 7.**  Finitely many first homology classes of a generic split embedding problem
with coefficients in a layer tensored with a fixed module are annihilated at once by a surjective
equivariant homomorphism onto the intended rank. -/
theorem exists_operatorHom_h1_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S) {j t : ℕ}
    (T : Rep (ZMod ℓ) U) [Module.Finite (ZMod ℓ) T] :
    ∃ m : ℕ, ∀ x : Fin t → groupHomology.H1 (genericInflate U m S ℓ j T),
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ ν, groupHomology.map (operatorSemidirect hα) (operatorInflateRep hα ℓ j T) 1
          (x ν) = 0 := by
  obtain ⟨q, hq⟩ := exists_operatorHom_h1_inl_eq_zero U n S hS (j := j) (t := t) T
  set R : ℕ := (j + 1) * (t * Nat.card U ^ 1 *
    Module.finrank (ZMod ℓ) (Layer ℓ (Generic U q S) j ⊗[ZMod ℓ] T)) + 1 with hR
  have hlt : (j + 1) * (t * Nat.card U ^ 1 *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U q S) j ⊗[ZMod ℓ] T)) < R := by
    rw [hR]; exact Nat.lt_succ_self _
  refine ⟨R * q, fun x => ?_⟩
  obtain ⟨a, hsurj₁, ha⟩ := exists_genericShrink_homology_tensor_eq_zero U R q S hS (c := 1) T hlt
    fun ν => groupHomology.map (SemidirectProduct.rightHom (φ := genericAut U (R * q) S))
      (𝟙 (genericInflate U (R * q) S ℓ j T)) 1 (x ν)
  set hα₁ := isOperatorHom_genericShrink U R q S a with hα₁def
  have hstep : ∀ ν, groupHomology.map (SemidirectProduct.rightHom (φ := genericAut U q S))
      (𝟙 (genericInflate U q S ℓ j T)) 1
      (groupHomology.map (operatorSemidirect hα₁) (operatorInflateRep hα₁ ℓ j T) 1 (x ν)) = 0 := by
    intro ν
    have h := ConcreteCategory.congr_hom (map_rightHom_naturality hα₁ ℓ j T) (x ν)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
    rw [← h]
    exact ha ν
  choose y hy using fun ν => exists_map_inl_eq_of_map_rightHom_eq_zero
    (groupHomology.map (operatorSemidirect hα₁) (operatorInflateRep hα₁ ℓ j T) 1 (x ν)) (hstep ν)
  obtain ⟨α₂, hα₂, hsurj₂, h₂⟩ := hq y
  refine ⟨α₂.comp (genericShrink U R q S a), hα₂.comp hα₁, hsurj₂.comp hsurj₁, fun ν => ?_⟩
  rw [map_operatorSemidirect_comp hα₂ hα₁ ℓ j T, ModuleCat.comp_apply, ← hy ν]
  have h := ConcreteCategory.congr_hom (map_inl_naturality hα₂ ℓ j T) (y ν)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
  rw [h, h₂ ν, map_zero]

end Prop7

