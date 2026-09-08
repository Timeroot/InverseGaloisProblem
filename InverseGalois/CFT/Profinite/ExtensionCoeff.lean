/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.ExtensionMap
import InverseGalois.CFT.Profinite.EmbeddingClass
import InverseGalois.CFT.Profinite.PiTwo

/-!
# A morphism of extensions, read in cohomology

A morphism of two group extensions with commutative kernels is a homomorphism of the middle terms
carrying the first kernel into the second and covering a homomorphism of the quotients.  The map of
the kernels is then equivariant, both actions being conjugation inside the respective extension, so
it induces a map of the second cohomology of the first quotient; and **the class of the extension
above goes to the class of the extension below, pulled back along the map of the quotients.**  The
two factor sets differ by the coboundary of the function comparing a transported section with a
section below, and on a discrete group that function is smooth for nothing.

Over a fixed quotient the pullback disappears and the statement is that the two classes correspond
under the map of the kernels.  This is what a family of extensions indexed by a shrinking
construction needs.  The classes to be killed are the restrictions of the class of the extension
above to a family of subgroups; a homomorphism of the kernels killing those restrictions makes the
extension below split over every member of the family, because restriction commutes with a map of
the coefficients.

## Main results

* `InverseGalois.CFT.map_smul_of_extensionMap`: a morphism of extensions is equivariant on the
  kernels, for the action of the quotient above.
* `InverseGalois.CFT.coeffH2_extensionClass_eq_comapH2`: **the class of the extension above, read
  through the map of the kernels, is the class of the extension below, pulled back along the map of
  the quotients.**
* `InverseGalois.CFT.coeffH2_extensionClass`: the same over a fixed quotient.
* `InverseGalois.CFT.coeffH2_resH2_extensionClass`: the same after restriction to a subgroup.
* `InverseGalois.CFT.exists_section_of_coeffH2_resH2_extensionClass`: **an extension splits over a
  subgroup as soon as the map of the kernels kills the restriction to that subgroup of the class of
  an extension above it.**

## Tags

group extension, factor set, second cohomology, embedding problem, morphism of extensions
-/

namespace InverseGalois.CFT

open GroupExtension

/-! ### Pulling back along the identity -/

section Id

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]

/-- Pulling a class of the second cohomology back along the identity does nothing. -/
theorem comapH2_id (hsm : IsSmoothHom (MonoidHom.id G)) (x : SmoothH2 G M) :
    comapH2 (MonoidHom.id G) (fun _ _ => rfl) hsm x = x := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective x
  rfl

end Id

/-! ### A morphism of extensions -/

section Map

variable {N₁ N₂ E₁ E₂ G₁ G₂ : Type*} [CommGroup N₁] [CommGroup N₂] [Group E₁] [Group E₂]
  [Group G₁] [Group G₂] [TopologicalSpace G₁] [DiscreteTopology G₁] [TopologicalSpace G₂]
  [DiscreteTopology G₂]
variable {S₁ : GroupExtension N₁ E₁ G₁} {S₂ : GroupExtension N₂ E₂ G₂}
  [MulDistribMulAction G₁ N₁] [MulDistribMulAction G₂ N₂] [MulDistribMulAction G₁ N₂]
  {α : N₁ →* N₂} {ψ : E₁ →* E₂} {φ : G₁ →* G₂}
variable (hact₁ : ∀ (g : G₁) (n : N₁), g • n = S₁.conjActHom g n)
  (hact₂ : ∀ (g : G₂) (n : N₂), g • n = S₂.conjActHom g n)
  (hact : ∀ (g : G₁) (n : N₂), g • n = φ g • n)
  (hinl : ∀ n : N₁, ψ (S₁.inl n) = S₂.inl (α n))
  (hright : ∀ e : E₁, S₂.rightHom (ψ e) = φ (S₁.rightHom e))

omit [TopologicalSpace G₁] [DiscreteTopology G₁] [TopologicalSpace G₂] [DiscreteTopology G₂] in
include hact₁ hact₂ hact hinl hright in
/-- **A morphism of extensions is equivariant on the kernels**, both actions being conjugation
inside the extension and the action of the quotient above on the kernel below being read through
the map of the quotients. -/
theorem map_smul_of_extensionMap (g : G₁) (n : N₁) : α (g • n) = g • α n := by
  rw [hact₁, hact, hact₂]
  exact GroupExtension.map_conjActHom hinl hright g n

/-- **The class of the extension above, read through the map of the kernels, is the class of the
extension below pulled back along the map of the quotients.**  A section above, transported and
compared with a section below, is the cochain whose coboundary is the ratio of the two factor sets,
and on a discrete group that cochain is smooth for nothing. -/
theorem coeffH2_extensionClass_eq_comapH2 (hsm : IsSmoothHom φ) (σ₁ : S₁.Section)
    (σ₂ : S₂.Section) :
    coeffH2 α (map_smul_of_extensionMap hact₁ hact₂ hact hinl hright)
        (extensionClass S₁ hact₁ σ₁)
      = comapH2 φ hact hsm (extensionClass S₂ hact₂ σ₂) := by
  obtain ⟨c, hc⟩ := GroupExtension.exists_map_factorSet_eq hinl hright σ₁ σ₂
  simp only [extensionClass, liftObstructionClass, coeffH2_smoothH2Mk, comapH2_smoothH2Mk]
  refine (smoothH2Mk_eq_iff _ _ _ _).2 ⟨c, isSmooth₁_of_discreteTopology c, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  show g • c h / c (g * h) * c g
    = α (S₁.factorSet σ₁ (g, h)) / S₂.factorSet σ₂ (φ g, φ h)
  rw [hact g (c h), hact₂ (φ g) (c h), hc g h, mul_div_cancel_right]

end Map

/-! ### A morphism of extensions over a fixed quotient -/

section Same

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
kernels.** -/
theorem map_smul_of_extensionHom (g : G) (n : N₁) : α (g • n) = g • α n :=
  map_smul_of_extensionMap (φ := MonoidHom.id G) hact₁ hact₂ (fun _ _ => rfl) hinl hright g n

/-- **Over a fixed quotient, the class of the extension above, read through the map of the kernels,
is the class of the extension below.** -/
theorem coeffH2_extensionClass (σ₁ : S₁.Section) (σ₂ : S₂.Section) :
    coeffH2 α (map_smul_of_extensionHom hact₁ hact₂ hinl hright) (extensionClass S₁ hact₁ σ₁)
      = extensionClass S₂ hact₂ σ₂ :=
  (coeffH2_extensionClass_eq_comapH2 (φ := MonoidHom.id G) hact₁ hact₂ (fun _ _ => rfl) hinl
    hright (isSmoothHom_of_continuous continuous_id) σ₁ σ₂).trans (comapH2_id _ _)

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

end Same

end InverseGalois.CFT
