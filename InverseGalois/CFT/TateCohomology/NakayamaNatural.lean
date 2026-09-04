/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.ShiftNatural
import InverseGalois.CFT.TateCohomology.TateNakayamaError
import InverseGalois.CFT.TateCohomology.TensorFunctor

/-!
# The comparison of Tate and Nakayama, along a map of representations

The comparison of Tate and Nakayama attached to a class in degree two of a representation is built
from a one cocycle of the shift: the cocycle twists the sum of the shift and the base ring into an
extension, tensoring that extension with the coefficients gives an extension of the coefficients by
the tensor product, and the connecting map of the latter, followed by two identifications, raises
the degree by two.

A map of representations carries a class in degree two to a class in degree two, but it carries the
chosen cocycle of the first only to a cocycle *cohomologous* to the chosen cocycle of the second.
The difference is a coboundary, and a coboundary is exactly the correction that turns the obvious
map of the two tensored extensions into an equivariant one: the vector whose failure to be
invariant is the difference is added to the tensor coordinate.  With that correction the two
extensions are compared, the connecting maps agree, and the whole comparison of Tate and Nakayama
becomes natural.

The consequence used in class field theory is that the image of the comparison attached to a class
is contained in the image of the map induced by any morphism the class comes from: if the
fundamental class of the ideles maps to the fundamental class of the idele classes, then every
value of the comparison of Tate and Nakayama for the idele classes already comes from the ideles.

## Main definitions

* `InverseGalois.CFT.Tate.homCocycles₁`: a one cocycle pushed forward along a map of
  representations.
* `InverseGalois.CFT.Tate.cocycleTensorSeqHom`: the comparison of two tensored extensions attached
  to cohomologous cocycles.

## Main results

* `InverseGalois.CFT.Tate.tateMap_one_H1π`: **the map induced in degree one carries the class of a
  cocycle to the class of the pushed forward cocycle.**
* `InverseGalois.CFT.Tate.shiftTensorIso_naturality`: **the comparison of the shift of a tensor
  product with the tensor product of the shift is natural.**
* `InverseGalois.CFT.Tate.tateNakayamaMap_naturality`: **the comparison of Tate and Nakayama
  commutes with a map of representations carrying one cocycle to a cohomologous one.**
* `InverseGalois.CFT.Tate.tateNakayamaTwoMap_naturality`: **the comparison of Tate and Nakayama
  attached to a class in degree two commutes with a map of representations**, the class on the
  target being the image of the class on the source.
* `InverseGalois.CFT.Tate.range_tateNakayamaTwoMap_le`: **the image of the comparison attached to
  an image class is contained in the image of the induced map.**

## Tags

Tate cohomology, Tate–Nakayama, naturality, fundamental class, cocycle
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### Functoriality, on elements -/

section Functorial

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

theorem tateMap_comp_apply {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℤ)
    (x : ↥(tateModule A n)) : tateMap ψ n (tateMap φ n x) = tateMap (φ ≫ ψ) n x := by
  rw [tateMap_comp]
  rfl

theorem tateMap_id_apply (A : Rep k G) (n : ℤ) (x : ↥(tateModule A n)) :
    tateMap (𝟙 A) n x = x := by
  rw [tateMap_id]
  rfl

end Functorial

/-! ### A cocycle pushed forward -/

section Push

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G}

/-- **A one cocycle pushed forward along a map of representations.** -/
def homCocycles₁ (φ : A ⟶ B) (b : groupCohomology.cocycles₁ A) :
    groupCohomology.cocycles₁ B :=
  ⟨fun τ => φ.hom.hom (b τ), (groupCohomology.mem_cocycles₁_iff _).2 fun σ τ => by
    show φ.hom.hom (b (σ * τ)) = B.ρ σ (φ.hom.hom (b τ)) + φ.hom.hom (b σ)
    rw [(groupCohomology.mem_cocycles₁_iff (b : G → ↥A.V)).1 b.2 σ τ, map_add,
      ← LinearMap.comp_apply, hom_equivariant φ σ, LinearMap.comp_apply]⟩

@[simp]
theorem homCocycles₁_apply (φ : A ⟶ B) (b : groupCohomology.cocycles₁ A) (τ : G) :
    homCocycles₁ φ b τ = φ.hom.hom (b τ) := rfl

end Push

/-! ### The class of a pushed forward cocycle -/

section DegreeOne

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B : Rep k G}

/-- **The map induced in degree one carries the class of a cocycle to the class of the pushed
forward cocycle.** -/
theorem tateMap_one_H1π (φ : A ⟶ B) (b : groupCohomology.cocycles₁ A) :
    tateMap φ 1 (groupCohomology.H1π A b) = groupCohomology.H1π B (homCocycles₁ φ b) := by
  show groupCohomology.map (MonoidHom.id G) φ 1 (groupCohomology.H1π A b) = _
  rw [groupCohomology.H1π_comp_map_apply (MonoidHom.id G) φ b]
  rfl

end DegreeOne

/-! ### The comparison of two tensored extensions -/

section Compare

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} (φ : A ⟶ B)
  (b : groupCohomology.cocycles₁ A) (c : groupCohomology.cocycles₁ B) (y : ↥B.V) (M : Rep k G)

/-- The map underlying the comparison of two tensored extensions: a map of representations on the
tensor coordinate, corrected by the vector whose failure to be invariant is the difference of the
two cocycles. -/
def cocycleTensorMap : ↥(cocycleTensorObj A b M).V →ₗ[k] ↥(cocycleTensorObj B c M).V :=
  LinearMap.prod
    (LinearMap.rTensor ↥M.V φ.hom.hom ∘ₗ LinearMap.fst k (↥A.V ⊗[k] ↥M.V) ↥M.V
      + TensorProduct.mk k ↥B.V ↥M.V y ∘ₗ LinearMap.snd k (↥A.V ⊗[k] ↥M.V) ↥M.V)
    (LinearMap.snd k (↥A.V ⊗[k] ↥M.V) ↥M.V)

@[simp]
theorem cocycleTensorMap_apply (p : (↥A.V ⊗[k] ↥M.V) × ↥M.V) :
    cocycleTensorMap φ b c y M p
      = (LinearMap.rTensor ↥M.V φ.hom.hom p.1 + y ⊗ₜ[k] p.2, p.2) := rfl

variable (hy : ∀ τ : G, φ.hom.hom (b τ) = c τ + (B.ρ τ y - y))

include hy in
theorem cocycleTensorMap_equivariant (τ : G) :
    cocycleTensorMap φ b c y M ∘ₗ (cocycleTensorObj A b M).ρ τ
      = (cocycleTensorObj B c M).ρ τ ∘ₗ cocycleTensorMap φ b c y M := by
  have hcomm : ∀ t : ↥A.V ⊗[k] ↥M.V, LinearMap.rTensor ↥M.V φ.hom.hom (tensorRho A M τ t)
      = tensorRho B M τ (LinearMap.rTensor ↥M.V φ.hom.hom t) := fun t =>
    LinearMap.congr_fun (hom_equivariant (tensorHomLeft M φ) τ) t
  refine LinearMap.ext fun p => Prod.ext ?_ rfl
  show LinearMap.rTensor ↥M.V φ.hom.hom (tensorRho A M τ p.1 + (b τ) ⊗ₜ[k] M.ρ τ p.2)
      + y ⊗ₜ[k] M.ρ τ p.2
    = tensorRho B M τ (LinearMap.rTensor ↥M.V φ.hom.hom p.1 + y ⊗ₜ[k] p.2)
      + (c τ) ⊗ₜ[k] M.ρ τ p.2
  rw [map_add, hcomm, LinearMap.rTensor_tmul, map_add, tensorRho_tmul, hy τ,
    TensorProduct.add_tmul, TensorProduct.sub_tmul]
  abel

include hy in
/-- **The comparison of two tensored extensions attached to cohomologous cocycles.** -/
def cocycleTensorHom : cocycleTensorObj A b M ⟶ cocycleTensorObj B c M :=
  mkHom (cocycleTensorMap φ b c y M) (cocycleTensorMap_equivariant φ b c y M hy)

include hy in
/-- **The comparison of two tensored extensions as a map of short complexes**: it is the map of
representations tensored with the coefficients on the sub, and the identity on the quotient. -/
def cocycleTensorSeqHom : cocycleTensorSeq A b M ⟶ cocycleTensorSeq B c M where
  τ₁ := tensorHomLeft M φ
  τ₂ := cocycleTensorHom φ b c y M hy
  τ₃ := 𝟙 M
  comm₁₂ := by
    refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun t => Prod.ext ?_ rfl))
    show LinearMap.rTensor ↥M.V φ.hom.hom t
      = LinearMap.rTensor ↥M.V φ.hom.hom t + y ⊗ₜ[k] (0 : ↥M.V)
    rw [TensorProduct.tmul_zero, add_zero]
  comm₂₃ := rfl

end Compare

/-! ### The connecting map of the tensored extension -/

section Connecting

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B : Rep k G} (φ : A ⟶ B)
  (b : groupCohomology.cocycles₁ A) (c : groupCohomology.cocycles₁ B) (y : ↥B.V) (M : Rep k G)
  (hy : ∀ τ : G, φ.hom.hom (b τ) = c τ + (B.ρ τ y - y))

include hy in
/-- **The connecting map of the tensored extension commutes with a map of representations carrying
one cocycle to a cohomologous one.** -/
theorem tateδ_cocycleTensorSeq_naturality (n : ℤ) (x : ↥(tateModule M n)) :
    tateMap (tensorHomLeft M φ) (n + 1) (tateδ (cocycleTensorSeq_shortExact A b M) n x)
      = tateδ (cocycleTensorSeq_shortExact B c M) n x := by
  refine (tateδ_naturality_apply (cocycleTensorSeq_shortExact A b M)
    (cocycleTensorSeq_shortExact B c M) (cocycleTensorSeqHom φ b c y M hy) n x).trans ?_
  exact congrArg (fun z => tateδ (cocycleTensorSeq_shortExact B c M) n z)
    (tateMap_id_apply M n x)

end Connecting

/-! ### The shift of a tensor product -/

section Shift

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B : Rep k G} (φ : A ⟶ B)
  (M : Rep k G)

/-- **The comparison of the shift of a representation tensored with another representation and the
shift of their tensor product is natural in the first representation.** -/
theorem shiftTensorIso_naturality :
    tensorHomLeft M (shiftHom φ) ≫ (shiftTensorIso B M).hom
      = (shiftTensorIso A M).hom ≫ shiftHom (tensorHomLeft M φ) := by
  refine tensorHomLeft_ext M fun q m => ?_
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (coindEmb A.ρ)) q
  show shiftTensorEquiv B M
      (Submodule.Quotient.mk (LinearMap.compLeft φ.hom.hom G f) ⊗ₜ[k] m)
    = shiftLinear (tensorHomLeft M φ)
        (shiftTensorEquiv A M (Submodule.Quotient.mk f ⊗ₜ[k] m))
  rw [shiftTensorEquiv_mk_tmul, shiftTensorEquiv_mk_tmul]
  rfl

end Shift

/-! ### The comparison of Tate and Nakayama -/

section Nakayama

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B : Rep k G} (φ : A ⟶ B)
  (b : groupCohomology.cocycles₁ (shiftObj A)) (c : groupCohomology.cocycles₁ (shiftObj B))
  (y : ↥(shiftObj B).V) (M : Rep k G)
  (hy : ∀ τ : G, (shiftHom φ).hom.hom (b τ) = c τ + ((shiftObj B).ρ τ y - y))

include hy in
/-- **The comparison of Tate and Nakayama commutes with a map of representations carrying one
cocycle of the shift to a cohomologous one.** -/
theorem tateNakayamaMap_naturality (n : ℤ) (x : ↥(tateModule M n)) :
    tateMap (tensorHomLeft M φ) (n + 1 + 1) (tateNakayamaMap A b M n x)
      = tateNakayamaMap B c M n x := by
  have hδ := tateδ_cocycleTensorSeq_naturality (shiftHom φ) b c y M hy n x
  have hsq := tateShiftEquiv_naturality (tensorHomLeft M φ) (n + 1)
    (tateMap (shiftTensorIso A M).hom (n + 1) (tateδ (cocycleTensorSeq_shortExact
      (shiftObj A) b M) n x))
  show tateMap (tensorHomLeft M φ) (n + 1 + 1) (tateShiftEquiv (tensorObj A M) (n + 1)
      (tateMap (shiftTensorIso A M).hom (n + 1)
        (tateδ (cocycleTensorSeq_shortExact (shiftObj A) b M) n x)))
    = tateShiftEquiv (tensorObj B M) (n + 1) (tateMap (shiftTensorIso B M).hom (n + 1)
        (tateδ (cocycleTensorSeq_shortExact (shiftObj B) c M) n x))
  rw [hsq, tateMap_comp_apply, ← shiftTensorIso_naturality, ← tateMap_comp_apply, hδ]

end Nakayama

/-! ### The comparison attached to a class in degree two -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G] {A B : Rep ℤ G} (φ : A ⟶ B) (α : tateModule A 2)
  (M : Rep ℤ G)

/-- The chosen cocycle of the shift of the target, compared with the chosen cocycle of the shift of
the source pushed forward: the two are cohomologous. -/
theorem exists_shiftHom_tateTwoCocycle : ∃ y : ↥(shiftObj B).V, ∀ τ : G,
    (shiftHom φ).hom.hom (tateTwoCocycle A α τ)
      = tateTwoCocycle B (tateMap φ 2 α) τ + ((shiftObj B).ρ τ y - y) := by
  have hcl : groupCohomology.H1π (shiftObj B) (homCocycles₁ (shiftHom φ) (tateTwoCocycle A α))
      = groupCohomology.H1π (shiftObj B) (tateTwoCocycle B (tateMap φ 2 α)) := by
    refine (tateShiftEquiv B 1).injective ?_
    rw [tateTwoCocycle_spec, ← tateMap_one_H1π, ← tateShiftEquiv_naturality,
      tateTwoCocycle_spec]
    rfl
  obtain ⟨y, hy⟩ := (groupCohomology.H1π_eq_iff _ _).1 hcl
  refine ⟨y, fun τ => ?_⟩
  have h := congrFun hy τ
  simp only [groupCohomology.d₀₁_hom_apply, Pi.sub_apply] at h
  rw [h, homCocycles₁_apply]
  abel

include φ in
/-- **The comparison of Tate and Nakayama attached to a class in degree two commutes with a map of
representations**, the class on the target being the image of the class on the source. -/
theorem tateNakayamaTwoMap_naturality (n : ℤ) (x : ↥(tateModule M n)) :
    tateMap (tensorHomLeft M φ) (n + 1 + 1) (tateNakayamaTwoMap A α M n x)
      = tateNakayamaTwoMap B (tateMap φ 2 α) M n x := by
  obtain ⟨y, hy⟩ := exists_shiftHom_tateTwoCocycle φ α
  exact tateNakayamaMap_naturality φ (tateTwoCocycle A α)
    (tateTwoCocycle B (tateMap φ 2 α)) y M hy n x

include φ in
/-- **The image of the comparison of Tate and Nakayama attached to an image class is contained in
the image of the induced map**: whatever the comparison produces for a class that comes from
another representation already comes from that representation. -/
theorem range_tateNakayamaTwoMap_le (n : ℤ) :
    LinearMap.range (tateNakayamaTwoMap B (tateMap φ 2 α) M n)
      ≤ LinearMap.range (tateMap (tensorHomLeft M φ) (n + 1 + 1)).hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨tateNakayamaTwoMap A α M n x, tateNakayamaTwoMap_naturality φ α M n x⟩

end DegreeTwo

end

end InverseGalois.CFT.Tate
