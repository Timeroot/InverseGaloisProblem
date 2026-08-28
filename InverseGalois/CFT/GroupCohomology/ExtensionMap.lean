/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.ToCocycle

/-!
# A morphism of extensions compares their factor sets

A morphism of group extensions with abelian kernels is a triple of homomorphisms, one on the
kernels, one on the middle terms and one on the quotients, making the two squares commute.  Such a
triple carries the action of the first quotient on the first kernel to the action of the second
quotient on the second kernel, and it identifies the two cohomology classes: the class of the first
extension, pushed forward along the map of kernels, is the class of the second extension pulled
back along the map of quotients.

The comparison is read off from the sections.  A section of the first extension and a section of
the second differ, after transport, by a function on the first quotient with values in the second
kernel, because the two have the same image in the second quotient.  Writing the multiplicativity
defect of the transported section in two ways exhibits that function as the cochain trivialising
the ratio of the two factor sets.

## Main definitions

* `GroupExtension.sectionCompare`: the element of the second kernel comparing the image of a
  section of the first extension with a section of the second.

## Main results

* `GroupExtension.map_conjActHom`: a morphism of extensions is equivariant for the induced
  actions.
* `GroupExtension.map_factorSet_eq`: **the factor set of the first extension, pushed forward along
  the map of kernels, is the factor set of the second extension pulled back along the map of
  quotients, up to the differential of the comparison of the sections.**
* `GroupExtension.exists_map_factorSet_eq`: the same, with the comparison existentially quantified.
* `GroupExtension.isMulCoboundary₂_map_factorSet_div`: over a fixed quotient, the ratio of the
  pushed forward factor set and the factor set below is a multiplicative two-coboundary, so the two
  extensions have the same class in `H²`.

## Tags

group extension, factor set, two-cocycle, morphism of extensions, embedding problem
-/

open groupCohomology

namespace GroupExtension

section Morphism

variable {M₁ M₂ E₁ E₂ G₁ G₂ : Type*} [CommGroup M₁] [CommGroup M₂] [Group E₁] [Group E₂]
  [Group G₁] [Group G₂] {S₁ : GroupExtension M₁ E₁ G₁} {S₂ : GroupExtension M₂ E₂ G₂}
  {α : M₁ →* M₂} {ψ : E₁ →* E₂} {φ : G₁ →* G₂}

/-! ### The action induced on the kernels -/

/-- **A morphism of extensions is equivariant for the actions induced on the kernels.** -/
theorem map_conjActHom (hinl : ∀ m : M₁, ψ (S₁.inl m) = S₂.inl (α m))
    (hright : ∀ e : E₁, S₂.rightHom (ψ e) = φ (S₁.rightHom e)) (g : G₁) (m : M₁) :
    α (S₁.conjActHom g m) = S₂.conjActHom (φ g) (α m) := by
  obtain ⟨e, rfl⟩ := S₁.rightHom_surjective g
  apply S₂.inl_injective
  rw [← hinl, S₁.inl_conjActHom, ← hright, map_mul, map_mul, map_inv, hinl, S₂.inl_conjActHom]

/-! ### Comparing a transported section with a section below -/

/-- The image under a morphism of extensions of a section of the first extension differs from a
section of the second by an element of the second kernel. -/
theorem mul_inv_mem_range_inl (hright : ∀ e : E₁, S₂.rightHom (ψ e) = φ (S₁.rightHom e))
    (σ₁ : S₁.Section) (σ₂ : S₂.Section) (g : G₁) :
    ψ (σ₁ g) * (σ₂ (φ g))⁻¹ ∈ S₂.inl.range := by
  rw [S₂.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, hright,
    Section.rightHom_section σ₁ g, Section.rightHom_section σ₂ (φ g), mul_inv_cancel]

variable (ψ φ)

/-- The element of the second kernel comparing the image of a section of the first extension with
a section of the second. -/
noncomputable def sectionCompare (σ₁ : S₁.Section) (σ₂ : S₂.Section) (g : G₁) : M₂ :=
  Function.invFun S₂.inl (ψ (σ₁ g) * (σ₂ (φ g))⁻¹)

variable {ψ φ}

@[simp]
theorem inl_sectionCompare (hright : ∀ e : E₁, S₂.rightHom (ψ e) = φ (S₁.rightHom e))
    (σ₁ : S₁.Section) (σ₂ : S₂.Section) (g : G₁) :
    S₂.inl (sectionCompare ψ φ σ₁ σ₂ g) = ψ (σ₁ g) * (σ₂ (φ g))⁻¹ :=
  Function.invFun_eq (MonoidHom.mem_range.mp (mul_inv_mem_range_inl hright σ₁ σ₂ g))

/-- The image of a section of the first extension, written in terms of the section below. -/
theorem map_section_eq (hright : ∀ e : E₁, S₂.rightHom (ψ e) = φ (S₁.rightHom e))
    (σ₁ : S₁.Section) (σ₂ : S₂.Section) (g : G₁) :
    ψ (σ₁ g) = S₂.inl (sectionCompare ψ φ σ₁ σ₂ g) * σ₂ (φ g) := by
  rw [inl_sectionCompare hright, inv_mul_cancel_right]

/-! ### The comparison of the factor sets -/

/-- **The factor set of the first extension, pushed forward along the map of kernels, is the factor
set of the second extension pulled back along the map of quotients, corrected by the differential
of the comparison of the sections.** -/
theorem map_factorSet_eq (hinl : ∀ m : M₁, ψ (S₁.inl m) = S₂.inl (α m))
    (hright : ∀ e : E₁, S₂.rightHom (ψ e) = φ (S₁.rightHom e))
    (σ₁ : S₁.Section) (σ₂ : S₂.Section) (g h : G₁) :
    α (S₁.factorSet σ₁ (g, h))
      = sectionCompare ψ φ σ₁ σ₂ g * S₂.conjActHom (φ g) (sectionCompare ψ φ σ₁ σ₂ h)
        * S₂.factorSet σ₂ (φ g, φ h) * (sectionCompare ψ φ σ₁ σ₂ (g * h))⁻¹ := by
  apply S₂.inl_injective
  have hfs : S₂.inl (α (S₁.factorSet σ₁ (g, h)))
      = ψ (σ₁ g) * ψ (σ₁ h) * (ψ (σ₁ (g * h)))⁻¹ := by
    rw [← hinl, S₁.inl_factorSet, map_mul, map_mul, map_inv]
  rw [hfs, map_section_eq hright σ₁ σ₂ g, map_section_eq hright σ₁ σ₂ h,
    map_section_eq hright σ₁ σ₂ (g * h)]
  simp only [map_mul, map_inv, inl_sectionCompare hright, S₂.inl_conjActHom_section σ₂,
    S₂.inl_factorSet, map_mul φ]
  group

/-- **A morphism of extensions exhibits the pushed forward factor set as the pulled back factor
set up to a coboundary.** -/
theorem exists_map_factorSet_eq (hinl : ∀ m : M₁, ψ (S₁.inl m) = S₂.inl (α m))
    (hright : ∀ e : E₁, S₂.rightHom (ψ e) = φ (S₁.rightHom e))
    (σ₁ : S₁.Section) (σ₂ : S₂.Section) :
    ∃ c : G₁ → M₂, ∀ g h : G₁,
      α (S₁.factorSet σ₁ (g, h))
        = S₂.conjActHom (φ g) (c h) / c (g * h) * c g * S₂.factorSet σ₂ (φ g, φ h) := by
  refine ⟨sectionCompare ψ φ σ₁ σ₂, fun g h ↦ ?_⟩
  rw [map_factorSet_eq hinl hright σ₁ σ₂ g h]
  rw [div_eq_mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Morphism

/-! ### Two extensions of the same group -/

section SameQuotient

variable {M₁ M₂ E₁ E₂ G : Type*} [CommGroup M₁] [CommGroup M₂] [Group E₁] [Group E₂] [Group G]
  {S₁ : GroupExtension M₁ E₁ G} {S₂ : GroupExtension M₂ E₂ G} {α : M₁ →* M₂} {ψ : E₁ →* E₂}

/-- **Over a fixed quotient, a morphism of extensions makes the ratio of the pushed forward factor
set and the factor set below a multiplicative two-coboundary**, so the two extensions have the same
class in `H²` once the kernels are identified. -/
theorem isMulCoboundary₂_map_factorSet_div (hinl : ∀ m : M₁, ψ (S₁.inl m) = S₂.inl (α m))
    (hright : ∀ e : E₁, S₂.rightHom (ψ e) = S₁.rightHom e)
    (σ₁ : S₁.Section) (σ₂ : S₂.Section) :
    letI := S₂.mulDistribMulAction
    IsMulCoboundary₂ ((fun p : G × G ↦ α (S₁.factorSet σ₁ p)) / S₂.factorSet σ₂) := by
  letI := S₂.mulDistribMulAction
  show IsMulCoboundary₂ ((fun p : G × G ↦ α (S₁.factorSet σ₁ p)) / S₂.factorSet σ₂)
  obtain ⟨c, hc⟩ := exists_map_factorSet_eq (φ := MonoidHom.id G) hinl hright σ₁ σ₂
  refine ⟨c, fun g h ↦ ?_⟩
  show S₂.conjActHom g (c h) / c (g * h) * c g = α (S₁.factorSet σ₁ (g, h)) / S₂.factorSet σ₂ (g, h)
  rw [hc g h]
  simp

end SameQuotient

end GroupExtension
