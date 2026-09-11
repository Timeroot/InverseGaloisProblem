/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.ComapIso
import InverseGalois.CFT.Profinite.ExtensionCoeff
import InverseGalois.Solvable.Shafarevich.LayerExtension
import InverseGalois.Solvable.Shafarevich.LayerSmooth

/-!
# Making the extension of one layer split over finitely many prescribed subgroups

A generic operator group, divided by one term of its descending `p`-central series and carrying its
operators alongside, is an extension of the same construction one term earlier by the layer between
the two.  The class of that extension is the obstruction to carrying a solution of an embedding
problem one step further up the filtration, and what has to be arranged is that it dies on the
subgroups the places of a number field contribute.

Those subgroups arrive as *sections*: at a place which is completely decomposed in the field the
level above cuts out, the decomposition subgroup of the big group maps isomorphically onto the
decomposition subgroup of the operator group below, so it is the image of a homomorphism from a
subgroup of the operator group which is a right inverse to the projection.  Transport along that
isomorphism turns the restriction of the class to the decomposition subgroup into a class of the
subgroup of the operator group, which is precisely the shape the shrinking count consumes.

Shrinking then does the rest.  The count kills one class of each of finitely many subgroups of the
operator group at once; the class of the extension at the level reached, pulled back along the
pushed down section, is what the count killed, because the class of the extension above read
through the map of the layers is the class of the extension below; and pulling back along an
isomorphism is injective, so the class itself dies on the image of the pushed down section.

## Main definitions

* `InverseGalois.Shafarevich.GenericQuot` — a generic operator group divided by one term of its
  descending `p`-central series, with the operators alongside.
* `InverseGalois.Shafarevich.genericQuotAction` — that group acts on a layer through the operators.

## Main results

* `InverseGalois.Shafarevich.smul_eq_conjActHom_genericLayer` — conjugation inside the extension one
  layer gives is the action of the operators.
* `InverseGalois.Shafarevich.exists_operatorHom_forall_resH2_extensionClass_eq_one` — **after one
  shrinking, the extension given by one layer splits over the image of each of finitely many
  prescribed sections.**

## Tags

Shafarevich's theorem, embedding problem, group extension, p-central series, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### A generic operator group at one level of the filtration -/

/-- A generic operator group divided by one term of its descending `p`-central series, with the
operators alongside. -/
abbrev GenericQuot (ℓ : ℕ) (U : Type) [Group U] (m : ℕ) (S : Type) [Group S] (j : ℕ) : Type :=
  (Generic U m S ⧸ pCentral ℓ (Generic U m S) j) ⋊[pCentralAut ℓ (genericAut U m S) j] U

instance (ℓ : ℕ) (U : Type) [Group U] (m : ℕ) (S : Type) [Group S] (j : ℕ) :
    TopologicalSpace (GenericQuot ℓ U m S j) := ⊥

instance (ℓ : ℕ) (U : Type) [Group U] (m : ℕ) (S : Type) [Group S] (j : ℕ) :
    DiscreteTopology (GenericQuot ℓ U m S j) := ⟨rfl⟩

/-- **A generic operator group at one level of the filtration acts on a layer at any level**,
through the operators it projects onto. -/
def genericQuotAction (ℓ : ℕ) (U : Type) [Group U] [Finite U] (m n : ℕ) (S : Type) [Group S]
    [Finite S] (j : ℕ) :
    MulDistribMulAction (GenericQuot ℓ U m S j) ↥(layerSub ℓ (Generic U n S) j) :=
  MulDistribMulAction.compHom _ (SemidirectProduct.rightHom : GenericQuot ℓ U m S j →* U)

attribute [local instance] genericQuotAction

/-- That action, computed on an element. -/
theorem genericQuotAction_smul (ℓ : ℕ) (U : Type) [Group U] [Finite U] (m n : ℕ) (S : Type)
    [Group S] [Finite S] (j : ℕ) (x : GenericQuot ℓ U m S j)
    (v : ↥(layerSub ℓ (Generic U n S) j)) :
    x • v = SemidirectProduct.rightHom x • v := rfl

/-- **Conjugation inside the extension one layer of the filtration gives is the action of the
operators**, the layer being central in the group above it. -/
theorem smul_eq_conjActHom_genericLayer (ℓ : ℕ) (U : Type) [Group U] [Finite U] (m : ℕ) (S : Type)
    [Group S] [Finite S] (j : ℕ) (x : GenericQuot ℓ U m S j)
    (v : ↥(layerSub ℓ (Generic U m S) j)) :
    x • v = (layerExtension ℓ (genericAut U m S) j).conjActHom x v :=
  (conjActHom_layerExtension ℓ (genericAut U m S) j (genericLayerSubAction_smul U m S ℓ j) x v).symm

/-! ### Splitting over the image of a section -/

/-- **After one shrinking, the extension given by one layer of the filtration splits over the image
of each of finitely many prescribed sections.**

The subgroups of the operator group are given in advance and the sections afterwards, since the rank
the count needs is fixed by the subgroups alone.  A section is what a place completely decomposed at
the level above provides, its image being the decomposition subgroup there. -/
theorem exists_operatorHom_forall_resH2_extensionClass_eq_one (ℓ : ℕ) [Fact ℓ.Prime] (U : Type)
    [Group U] [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S]
    [Finite S] (hS : IsPGroup ℓ S) (j t : ℕ) (P : Fin t → Subgroup U)
    (σn : (layerExtension ℓ (genericAut U n S) j).Section) :
    ∃ m : ℕ, ∀ s : ∀ ν, ↥(P ν) →* GenericQuot ℓ U m S j,
      (∀ (ν : Fin t) (y : ↥(P ν)), SemidirectProduct.rightHom (s ν y) = (y : U)) →
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ ν, resH2 ((layerSemidirectMap ℓ hα j).comp (s ν)).range
          (extensionClass (layerExtension ℓ (genericAut U n S) j)
            (smul_eq_conjActHom_genericLayer ℓ U n S j) σn) = 1 := by
  obtain ⟨m, hm⟩ := exists_operatorHom_forall_subgroupCoeffH2_eq_one (j := j) U n S hS P
  refine ⟨m, fun s hs => ?_⟩
  -- a set theoretic section of the extension at the level above
  have hsurjm := (layerExtension ℓ (genericAut U m S) j).rightHom_surjective
  let σm : (layerExtension ℓ (genericAut U m S) j).Section :=
    ⟨Function.surjInv hsurjm, Function.rightInverse_surjInv hsurjm⟩
  -- the two classes of the two extensions
  let cm := extensionClass (layerExtension ℓ (genericAut U m S) j)
    (smul_eq_conjActHom_genericLayer ℓ U m S j) σm
  let cn := extensionClass (layerExtension ℓ (genericAut U n S) j)
    (smul_eq_conjActHom_genericLayer ℓ U n S j) σn
  -- a section is compatible with the two actions
  have hacts : ∀ (ν : Fin t) (y : ↥(P ν)) (v : ↥(layerSub ℓ (Generic U m S) j)),
      y • v = s ν y • v := by
    intro ν y v
    show ((y : U)) • v = SemidirectProduct.rightHom (s ν y) • v
    rw [hs ν y]
  have hactsN : ∀ (ν : Fin t) (y : ↥(P ν)) (v : ↥(layerSub ℓ (Generic U n S) j)),
      y • v = s ν y • v := by
    intro ν y v
    show ((y : U)) • v = SemidirectProduct.rightHom (s ν y) • v
    rw [hs ν y]
  have hsms : ∀ ν, IsSmoothHom (s ν) := fun _ =>
    isSmoothHom_of_continuous continuous_of_discreteTopology
  -- the count kills the pullback of the class above along each of the sections
  obtain ⟨α, hα, hαsurj, hkill⟩ := hm fun ν => comapH2 (s ν) (hacts ν) (hsms ν) cm
  refine ⟨α, hα, hαsurj, fun ν => ?_⟩
  have hsmφ : IsSmoothHom (layerSemidirectMap ℓ hα j) :=
    isSmoothHom_of_continuous continuous_of_discreteTopology
  -- the map of the layers is equivariant for the group above
  have hequiv := map_smul_of_extensionMap
    (S₁ := layerExtension ℓ (genericAut U m S) j) (S₂ := layerExtension ℓ (genericAut U n S) j)
    (α := layerSubMap ℓ α j) (ψ := layerSemidirectMap ℓ hα (j + 1))
    (φ := layerSemidirectMap ℓ hα j) (smul_eq_conjActHom_genericLayer ℓ U m S j)
    (smul_eq_conjActHom_genericLayer ℓ U n S j) (fun _ _ => rfl) (inl_layerSemidirectMap ℓ j hα)
    (rightHom_layerSemidirectMap ℓ j hα)
  -- the class above, read through the map of the layers, is the class below
  have hcmp := coeffH2_extensionClass_eq_comapH2
    (S₁ := layerExtension ℓ (genericAut U m S) j) (S₂ := layerExtension ℓ (genericAut U n S) j)
    (α := layerSubMap ℓ α j) (ψ := layerSemidirectMap ℓ hα (j + 1))
    (φ := layerSemidirectMap ℓ hα j) (smul_eq_conjActHom_genericLayer ℓ U m S j)
    (smul_eq_conjActHom_genericLayer ℓ U n S j) (fun _ _ => rfl) (inl_layerSemidirectMap ℓ j hα)
    (rightHom_layerSemidirectMap ℓ j hα) hsmφ σm σn
  -- the pushed down section is again a section, and it is injective
  have hfright : ∀ y : ↥(P ν),
      SemidirectProduct.rightHom (((layerSemidirectMap ℓ hα j).comp (s ν)) y) = (y : U) :=
    fun y => hs ν y
  have hfinj : Function.Injective ((layerSemidirectMap ℓ hα j).comp (s ν)) := by
    intro y z hyz
    have hr := congrArg SemidirectProduct.rightHom hyz
    rw [hfright, hfright] at hr
    exact Subtype.ext hr
  have hactf : ∀ (y : ↥(P ν)) (v : ↥(layerSub ℓ (Generic U n S) j)),
      y • v = ((layerSemidirectMap ℓ hα j).comp (s ν)) y • v := by
    intro y v
    show ((y : U)) • v
      = SemidirectProduct.rightHom (((layerSemidirectMap ℓ hα j).comp (s ν)) y) • v
    rw [hfright y]
  refine resH2_range_eq_one_of_comapH2_eq_one hfinj hactf
    (isSmoothHom_comp (hsms ν) hsmφ) ?_
  -- the pullback along the pushed down section is what the count killed
  refine Eq.trans ?_ (hkill ν)
  refine Eq.trans (comapH2_comapH2 (hactsN ν) (fun _ _ => rfl) (hsms ν) hsmφ cn).symm ?_
  refine Eq.trans (congrArg (comapH2 (s ν) (hactsN ν) (hsms ν)) hcmp.symm) ?_
  exact (coeffH2_comapH2 (hacts ν) (hactsN ν) (hsms ν)
    (layerSubMap_smul_subgroup (P ν) hα) hequiv cm).symm

end InverseGalois.Shafarevich
