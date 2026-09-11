/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Discrete
import InverseGalois.CFT.Profinite.EmbeddingObstruction

/-!
# The class of a group extension, and the obstruction it inflates to

On a discrete group the trivial subgroup is open, so the identity has open kernel and the
obstruction attached to an embedding problem may be formed for the identity of the quotient itself.
That is the class of the extension: a class of the smooth second cohomology of the quotient with
values in the kernel, which vanishes exactly when the extension splits.

The obstruction of an arbitrary embedding problem is that one class read through the homomorphism,
and the identity is definitional, both sides being the same factor set composed with the same map.
The same holds after restricting to a subgroup: if the homomorphism carries a subgroup of the
topological group into a subgroup of the quotient, the restricted obstruction is the restricted
class of the extension read through the induced map of subgroups.

The reading this is for is local solvability.  An embedding problem whose homomorphism carries a
subgroup into a subgroup over which the extension splits is solvable on that subgroup, with no
cohomological hypothesis of any kind, because the class it inflates is already trivial upstairs;
and a family of such subgroups puts the obstruction in the everywhere locally trivial classes.
Over a number field the family is the decomposition subgroups, and the subgroups of the quotient
are their images, so this is the step which turns "the extension splits over every decomposition
group" into a statement about a single global obstruction.

## Main definitions

* `InverseGalois.CFT.extensionClass`: **the class of a group extension** of a discrete group by a
  commutative group.
* `InverseGalois.CFT.subgroupRestrict`: a homomorphism read as a map of a subgroup of the source
  into a subgroup of the target containing its image.

## Main results

* `InverseGalois.CFT.extensionClass_eq_one_iff`: the class of an extension vanishes exactly when
  the extension splits.
* `InverseGalois.CFT.resH2_extensionClass_eq_one_iff`: the class of an extension dies on a subgroup
  exactly when the extension splits over that subgroup.
* `InverseGalois.CFT.comapH2_extensionClass`: **the obstruction class of an embedding problem is
  the class of the extension read through the homomorphism.**
* `InverseGalois.CFT.resH2_liftObstructionClass_eq_one_of_resH2_extensionClass_eq_one`: **an
  embedding problem is solvable on a subgroup whose image lies in a subgroup over which the
  extension splits.**
* `InverseGalois.CFT.liftObstructionClass_mem_sha2_of_extensionClass`: a family of such subgroups
  puts the obstruction in the everywhere locally trivial classes.

## Tags

profinite group, Galois cohomology, embedding problem, group extension, obstruction, discrete group
-/

namespace InverseGalois.CFT

open GroupExtension

/-! ### The class of an extension -/

section ExtensionClass

variable {N E G : Type*} [CommGroup N] [Group E] [Group G] [TopologicalSpace G]
  [DiscreteTopology G]
variable (S : GroupExtension N E G) [MulDistribMulAction G N]
variable (hactG : ∀ (g : G) (n : N), g • n = S.conjActHom g n)

omit [MulDistribMulAction G N] in
/-- The identity of a discrete group has open normal kernel. -/
theorem isOpenNormal_ker_id : IsOpenNormal (MonoidHom.id G).ker := by
  rw [MonoidHom.ker_id]
  exact isOpenNormal_bot

/-- **The class of a group extension with commutative kernel**: the obstruction to lifting the
identity of the quotient. -/
noncomputable def extensionClass (σ : S.Section) : SmoothH2 G N :=
  liftObstructionClass S (MonoidHom.id G) hactG isOpenNormal_ker_id σ

/-- The class of an extension does not depend on the section. -/
theorem extensionClass_eq (σ τ : S.Section) :
    extensionClass S hactG σ = extensionClass S hactG τ :=
  liftObstructionClass_eq S (MonoidHom.id G) hactG isOpenNormal_ker_id σ τ

/-- **The class of an extension vanishes exactly when the extension splits.**  A lift of the
identity is a splitting, and on a discrete group there is no smoothness left to ask of it. -/
theorem extensionClass_eq_one_iff (σ : S.Section) :
    extensionClass S hactG σ = 1 ↔ ∃ f : G →* E, ∀ g : G, S.rightHom (f g) = g :=
  (liftObstructionClass_eq_one_iff S (MonoidHom.id G) hactG isOpenNormal_ker_id σ).trans
    ⟨fun ⟨f, _, hf⟩ => ⟨f, hf⟩, fun ⟨f, hf⟩ => ⟨f, isSmooth₁_of_discreteTopology _, hf⟩⟩

/-- **The class of an extension dies on a subgroup exactly when the extension splits over that
subgroup.** -/
theorem resH2_extensionClass_eq_one_iff (σ : S.Section) (H : Subgroup G) :
    resH2 H (extensionClass S hactG σ) = 1 ↔
      ∃ f : ↥H →* E, ∀ h : ↥H, S.rightHom (f h) = (h : G) :=
  (resH2_liftObstructionClass_eq_one_iff S (MonoidHom.id G) hactG isOpenNormal_ker_id σ H).trans
    ⟨fun ⟨f, _, hf⟩ => ⟨f, hf⟩, fun ⟨f, hf⟩ => ⟨f, isSmooth₁_of_discreteTopology _, hf⟩⟩

end ExtensionClass

/-! ### The obstruction as an inflated class -/

section Inflate

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
variable {N E G : Type*} [CommGroup N] [Group E] [Group G] [TopologicalSpace G]
  [DiscreteTopology G]
variable (S : GroupExtension N E G) (ρ : Γ →* G) [MulDistribMulAction G N]
  [MulDistribMulAction Γ N]
variable (hactG : ∀ (g : G) (n : N), g • n = S.conjActHom g n)
variable (hact : ∀ (γ : Γ) (n : N), γ • n = S.conjActHom (ρ γ) n)

omit [TopologicalSpace Γ] [TopologicalSpace G] [DiscreteTopology G] in
include hactG hact in
/-- The action of the topological group is the action of the quotient read through the
homomorphism, both being conjugation inside the extension. -/
theorem smul_eq_smul_map (γ : Γ) (n : N) : γ • n = ρ γ • n :=
  (hact γ n).trans (hactG (ρ γ) n).symm

include hactG hact in
/-- **The obstruction class of an embedding problem is the class of the extension read through the
homomorphism.**  Both are the factor set of the same section, composed with the same map. -/
theorem comapH2_extensionClass (hker : IsOpenNormal ρ.ker) (σ : S.Section) :
    comapH2 ρ (smul_eq_smul_map S ρ hactG hact) (isSmoothHom_of_isOpenNormal_ker hker)
        (extensionClass S hactG σ)
      = liftObstructionClass S ρ hact hker σ := rfl

include hactG hact in
/-- **An embedding problem whose extension splits is solvable.** -/
theorem liftObstructionClass_eq_one_of_extensionClass_eq_one (hker : IsOpenNormal ρ.ker)
    (σ : S.Section) (h : extensionClass S hactG σ = 1) :
    liftObstructionClass S ρ hact hker σ = 1 := by
  rw [← comapH2_extensionClass S ρ hactG hact hker σ, h, _root_.map_one]

end Inflate

/-! ### Local solvability -/

section Local

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
variable {N E G : Type*} [CommGroup N] [Group E] [Group G] [TopologicalSpace G]
  [DiscreteTopology G]
variable (S : GroupExtension N E G) (ρ : Γ →* G) [MulDistribMulAction G N]
  [MulDistribMulAction Γ N]
variable (hactG : ∀ (g : G) (n : N), g • n = S.conjActHom g n)
variable (hact : ∀ (γ : Γ) (n : N), γ • n = S.conjActHom (ρ γ) n)
variable (hker : IsOpenNormal ρ.ker)

omit [TopologicalSpace Γ] [TopologicalSpace G] [DiscreteTopology G] [MulDistribMulAction G N]
  [MulDistribMulAction Γ N] in
/-- **A homomorphism read as a map of a subgroup into a subgroup containing its image.** -/
def subgroupRestrict (D : Subgroup Γ) (H : Subgroup G) (hle : ∀ d : ↥D, ρ (d : Γ) ∈ H) :
    ↥D →* ↥H :=
  (ρ.comp D.subtype).codRestrict H hle

omit [TopologicalSpace G] [DiscreteTopology G] [MulDistribMulAction G N]
  [MulDistribMulAction Γ N] in
include hker in
/-- The induced map of subgroups again has open normal kernel. -/
theorem isOpenNormal_ker_subgroupRestrict (D : Subgroup Γ) (H : Subgroup G)
    (hle : ∀ d : ↥D, ρ (d : Γ) ∈ H) : IsOpenNormal (subgroupRestrict ρ D H hle).ker := by
  rw [subgroupRestrict, MonoidHom.ker_codRestrict]
  exact isOpenNormal_ker_comp_subtype ρ hker D

include hactG hact in
/-- **The obstruction class restricted to a subgroup is the class of the extension restricted to a
subgroup containing its image, read through the induced map.** -/
theorem resH2_liftObstructionClass_eq_comapH2 (σ : S.Section) (D : Subgroup Γ) (H : Subgroup G)
    (hle : ∀ d : ↥D, ρ (d : Γ) ∈ H) :
    resH2 D (liftObstructionClass S ρ hact hker σ)
      = comapH2 (subgroupRestrict ρ D H hle)
          (fun d n => smul_eq_smul_map S ρ hactG hact (d : Γ) n)
          (isSmoothHom_of_isOpenNormal_ker (isOpenNormal_ker_subgroupRestrict ρ hker D H hle))
          (resH2 H (extensionClass S hactG σ)) := rfl

include hactG hact in
/-- **An embedding problem is solvable on a subgroup whose image lies in a subgroup over which the
extension splits.**  There is nothing cohomological left to check: the restricted obstruction is
inflated from a class which is already trivial. -/
theorem resH2_liftObstructionClass_eq_one_of_resH2_extensionClass_eq_one (σ : S.Section)
    (D : Subgroup Γ) (H : Subgroup G) (hle : ∀ d : ↥D, ρ (d : Γ) ∈ H)
    (h : resH2 H (extensionClass S hactG σ) = 1) :
    resH2 D (liftObstructionClass S ρ hact hker σ) = 1 := by
  rw [resH2_liftObstructionClass_eq_comapH2 S ρ hactG hact hker σ D H hle, h, _root_.map_one]

include hactG hact in
/-- **A family of subgroups whose images lie in subgroups over which the extension splits puts the
obstruction in the everywhere locally trivial classes.** -/
theorem liftObstructionClass_mem_sha2_of_extensionClass (σ : S.Section) {T : Set (Subgroup Γ)}
    (h : ∀ D ∈ T, ∃ H : Subgroup G, (∀ d : ↥D, ρ (d : Γ) ∈ H) ∧
      resH2 H (extensionClass S hactG σ) = 1) :
    liftObstructionClass S ρ hact hker σ ∈ sha2 N T := by
  refine mem_sha2.2 fun D hD => ?_
  obtain ⟨H, hle, hH⟩ := h D hD
  exact resH2_liftObstructionClass_eq_one_of_resH2_extensionClass_eq_one S ρ hactG hact hker σ D H
    hle hH

include hactG hact hker in
/-- **An embedding problem which splits over a subgroup containing the image of every member of a
family is solvable**, as soon as there is no everywhere locally trivial class. -/
theorem exists_smooth_lift_of_extensionClass (σ : S.Section) {T : Set (Subgroup Γ)}
    (hbot : sha2 N T = ⊥)
    (h : ∀ D ∈ T, ∃ H : Subgroup G, (∀ d : ↥D, ρ (d : Γ) ∈ H) ∧
      resH2 H (extensionClass S hactG σ) = 1) :
    ∃ f : Γ →* E, IsSmooth₁ (f : Γ → E) ∧ ∀ γ, S.rightHom (f γ) = ρ γ :=
  (liftObstructionClass_eq_one_iff S ρ hact hker σ).1 <|
    (Subgroup.eq_bot_iff_forall _).1 hbot _
      (liftObstructionClass_mem_sha2_of_extensionClass S ρ hactG hact hker σ h)

end Local

end InverseGalois.CFT
