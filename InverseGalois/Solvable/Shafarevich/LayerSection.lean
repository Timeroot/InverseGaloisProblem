/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerSplit

/-!
# The subgroups a completely decomposed place contributes

The count which makes the class of the extension of one layer die is fed sections of the projection
onto the operator group, defined over prescribed subgroups of that group.  What arithmetic actually
produces is not a section but a *subgroup*: the decomposition subgroup of a place, sitting inside
the group at the level reached.  The place being completely decomposed in that level over the field
the operator group cuts out says exactly that the projection is injective on that subgroup, and a
homomorphism injective on a subgroup is an isomorphism of it onto its image, so its inverse is the
section wanted.  The image is the decomposition subgroup downstairs, which is settled by the base
field and the place alone and so may be prescribed before the count chooses how far to shrink.

This file makes that translation once and for all, and restates the splitting theorem in the form
the arithmetic will use: subgroups on which the projection is injective, with prescribed image, in
place of sections.

## Main results

* `InverseGalois.Shafarevich.exists_section_of_injOn` — **a homomorphism injective on a subgroup has
  a section over the image of that subgroup, whose own image is the subgroup one started from.**
* `InverseGalois.Shafarevich.exists_operatorHom_forall_resH2_extensionClass_subgroup_eq_one` —
  **after one shrinking, the extension given by one layer splits over each of finitely many
  subgroups on which the projection is injective with prescribed image.**

## Tags

Shafarevich's theorem, embedding problem, decomposition group, section, p-central series
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

attribute [local instance] genericQuotAction

/-! ### A section over the image of a subgroup -/

/-- **A homomorphism injective on a subgroup has a section over the image of that subgroup.**  The
image of the section is the subgroup one started from, so nothing is lost in passing from the
subgroup to the section and back. -/
theorem exists_section_of_injOn {G U : Type*} [Group G] [Group U] (f : G →* U) {A : Subgroup G}
    {B : Subgroup U} (hinj : ∀ x ∈ A, f x = 1 → x = 1) (hB : A.map f = B) :
    ∃ s : ↥B →* G, (∀ y : ↥B, f (s y) = (y : U)) ∧ s.range = A := by
  subst hB
  have hq : Function.Injective (f.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    exact fun x hx => Subtype.ext (hinj (x : G) x.2 hx)
  have hrange : (f.comp A.subtype).range = A.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨A.subtype.comp
    ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hq).symm).toMonoidHom,
    fun y => ?_, ?_⟩
  · exact congrArg Subtype.val
      ((MonoidHom.ofInjective hq).apply_symm_apply (MulEquiv.subgroupCongr hrange.symm y))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-! ### Splitting over prescribed subgroups -/

/-- **After one shrinking, the extension given by one layer of the filtration splits over each of
finitely many subgroups on which the projection onto the operator group is injective with
prescribed image.**

The subgroups of the operator group are given in advance and the subgroups upstairs afterwards,
since the rank the count needs is fixed by the ones downstairs alone.  A place completely
decomposed at the level reached contributes such a subgroup upstairs, namely its decomposition
subgroup, whose image downstairs is the decomposition subgroup of the base field. -/
theorem exists_operatorHom_forall_resH2_extensionClass_subgroup_eq_one (ℓ : ℕ) [Fact ℓ.Prime]
    (U : Type) [Group U] [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type)
    [Group S] [Finite S] (hS : IsPGroup ℓ S) (j t : ℕ) (P : Fin t → Subgroup U)
    (σn : (layerExtension ℓ (genericAut U n S) j).Section) :
    ∃ m : ℕ, ∀ D : Fin t → Subgroup (GenericQuot ℓ U m S j),
      (∀ (ν : Fin t), ∀ x ∈ D ν, SemidirectProduct.rightHom x = (1 : U) → x = 1) →
      (∀ ν : Fin t, (D ν).map (SemidirectProduct.rightHom : GenericQuot ℓ U m S j →* U) = P ν) →
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ ν, resH2 ((D ν).map (layerSemidirectMap ℓ hα j))
          (extensionClass (layerExtension ℓ (genericAut U n S) j)
            (smul_eq_conjActHom_genericLayer ℓ U n S j) σn) = 1 := by
  obtain ⟨m, hm⟩ :=
    exists_operatorHom_forall_resH2_extensionClass_eq_one ℓ U n S hS j t P σn
  refine ⟨m, fun D hDinj hDmap => ?_⟩
  choose s hs hsrange using fun ν =>
    exists_section_of_injOn (SemidirectProduct.rightHom : GenericQuot ℓ U m S j →* U)
      (hDinj ν) (hDmap ν)
  obtain ⟨α, hα, hαsurj, hkill⟩ := hm s hs
  refine ⟨α, hα, hαsurj, fun ν => ?_⟩
  have hrange : ((layerSemidirectMap ℓ hα j).comp (s ν)).range
      = (D ν).map (layerSemidirectMap ℓ hα j) := by
    rw [MonoidHom.range_comp, hsrange ν]
  rw [← hrange]
  exact hkill ν

end InverseGalois.Shafarevich
