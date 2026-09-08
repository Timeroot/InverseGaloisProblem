/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.ExtensionMap
import InverseGalois.CFT.Profinite.EmbeddingClass
import InverseGalois.CFT.Profinite.PiTwo

/-!
# A morphism of extensions over a fixed quotient, read in cohomology

Two extensions of one discrete group by commutative kernels, together with a homomorphism of the
middle terms carrying the first kernel into the second and inducing the identity on the quotient,
have comparable classes.  The homomorphism of the kernels is equivariant, both actions being
conjugation inside the respective extension, so it induces a map of the second cohomology; and the
class of the first extension goes to the class of the second, the two factor sets differing by the
coboundary of the function comparing a transported section with a section below.

This is what a family of extensions indexed by a shrinking construction needs.  The classes to be
killed are the restrictions of the class of the extension upstairs to a family of subgroups; a
homomorphism of the kernels killing those restrictions makes the extension downstairs split over
every member of the family, because restriction commutes with a map of the coefficients and the
class downstairs is the image of the class upstairs.

## Main results

* `InverseGalois.CFT.map_smul_of_extensionHom`: a homomorphism of the middle terms of two
  extensions of the same group is equivariant on the kernels.
* `InverseGalois.CFT.coeffH2_extensionClass`: **the class of an extension, read through a
  homomorphism of the kernels coming from a homomorphism of the middle terms, is the class of the
  extension below.**
* `InverseGalois.CFT.coeffH2_resH2_extensionClass`: the same after restriction to a subgroup.
* `InverseGalois.CFT.exists_section_of_coeffH2_resH2_extensionClass`: **an extension splits over a
  subgroup as soon as the restriction to that subgroup of the class of an extension above it is
  killed by the map of the kernels.**

## Tags

group extension, factor set, second cohomology, embedding problem, morphism of extensions
-/

namespace InverseGalois.CFT

open GroupExtension

/-! ### A homomorphism of extensions over a fixed quotient -/

section ExtensionCoeff

variable {N₁ N₂ E₁ E₂ G : Type*} [CommGroup N₁] [CommGroup N₂] [Group E₁] [Group E₂] [Group G]
  [TopologicalSpace G] [DiscreteTopology G]
variable {S₁ : GroupExtension N₁ E₁ G} {S₂ : GroupExtension N₂ E₂ G}
  [MulDistribMulAction G N₁] [MulDistribMulAction G N₂] {α : N₁ →* N₂} {ψ : E₁ →* E₂}
variable (hact₁ : ∀ (g : G) (n : N₁), g • n = S₁.conjActHom g n)
  (hact₂ : ∀ (g : G) (n : N₂), g • n = S₂.conjActHom g n)
  (hinl : ∀ n : N₁, ψ (S₁.inl n) = S₂.inl (α n))
  (hright : ∀ e : E₁, S₂.rightHom (ψ e) = S₁.rightHom e)

omit [TopologicalSpace G] [DiscreteTopology G] in
include hact₁ hact₂ hinl hright in
/-- **A homomorphism of the middle terms of two extensions of one group is equivariant on the
kernels**, both actions being conjugation inside the extension. -/
theorem map_smul_of_extensionHom (g : G) (n : N₁) : α (g • n) = g • α n := by
  rw [hact₁, hact₂]
  exact GroupExtension.map_conjActHom (φ := MonoidHom.id G) hinl hright g n

/-- **The class of an extension, read through the induced map of the kernels, is the class of the
extension below.**  A section of the extension above, transported and compared with a section
below, is the cochain whose coboundary is the ratio of the two factor sets, and on a discrete group
that cochain is smooth for nothing. -/
theorem coeffH2_extensionClass (σ₁ : S₁.Section) (σ₂ : S₂.Section) :
    coeffH2 α (map_smul_of_extensionHom hact₁ hact₂ hinl hright) (extensionClass S₁ hact₁ σ₁)
      = extensionClass S₂ hact₂ σ₂ := by
  obtain ⟨c, hc⟩ := GroupExtension.exists_map_factorSet_eq (φ := MonoidHom.id G) hinl hright σ₁ σ₂
  simp only [MonoidHom.id_apply] at hc
  simp only [extensionClass, liftObstructionClass, coeffH2_smoothH2Mk]
  refine (smoothH2Mk_eq_iff _ _ _ _).2 ⟨c, isSmooth₁_of_discreteTopology c, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  show g • c h / c (g * h) * c g = α (S₁.factorSet σ₁ (g, h)) / S₂.factorSet σ₂ (g, h)
  rw [hact₂ g (c h), hc g h, mul_div_cancel_right]

/-- The comparison of the two classes, restricted to a subgroup. -/
theorem coeffH2_resH2_extensionClass (σ₁ : S₁.Section) (σ₂ : S₂.Section) (H : Subgroup G) :
    coeffH2 α (fun (x : ↥H) (n : N₁) =>
        map_smul_of_extensionHom hact₁ hact₂ hinl hright (x : G) n)
        (resH2 H (extensionClass S₁ hact₁ σ₁))
      = resH2 H (extensionClass S₂ hact₂ σ₂) := by
  rw [← resH2_coeffH2 α (map_smul_of_extensionHom hact₁ hact₂ hinl hright) H
    (extensionClass S₁ hact₁ σ₁), coeffH2_extensionClass hact₁ hact₂ hinl hright σ₁ σ₂]

include hact₁ hact₂ hinl hright in
/-- **An extension splits over a subgroup as soon as the map of the kernels kills the restriction
to that subgroup of the class of an extension above it.** -/
theorem exists_section_of_coeffH2_resH2_extensionClass (σ₁ : S₁.Section) (σ₂ : S₂.Section)
    (H : Subgroup G)
    (h : coeffH2 α (fun (x : ↥H) (n : N₁) =>
        map_smul_of_extensionHom hact₁ hact₂ hinl hright (x : G) n)
        (resH2 H (extensionClass S₁ hact₁ σ₁)) = 1) :
    ∃ f : ↥H →* E₂, ∀ x : ↥H, S₂.rightHom (f x) = (x : G) :=
  (resH2_extensionClass_eq_one_iff S₂ hact₂ σ₂ H).1 <| by
    rw [← coeffH2_resH2_extensionClass hact₁ hact₂ hinl hright σ₁ σ₂ H, h]

end ExtensionCoeff

end InverseGalois.CFT
