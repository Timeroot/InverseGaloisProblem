/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyCoboundaryOne
import InverseGalois.CFT.Tate.FamilyCoind
import InverseGalois.CFT.TateCohomology.NakayamaNatural
import InverseGalois.CFT.TateCohomology.RestrictOne
import InverseGalois.CFT.TateCohomology.TateDegreeTwo

/-!
# The first cohomology of the sections of a family is detected at the indices

The sections of a family of modules indexed by a set with a group action are a representation of
the group, and evaluation at an index is a map of representations of any subgroup fixing that
index.  A class in the first cohomology of the sections therefore has a local class at every index,
namely its restriction to the stabiliser of the index followed by evaluation there, and the
question is whether those local classes determine it.

They do, and the reason is the coboundary theorem for families in degree one: a cocycle whose
value at every index is a coboundary for the stabiliser of that index is a coboundary.  The local
class at an index vanishes exactly when the value there is such a coboundary, so **a class of the
sections all of whose local classes vanish is zero**.  This is Shapiro's lemma in the only form the
ideles need, and it is proved without ever constructing the Shapiro isomorphism: the local
hypothesis is used at the level of cochains, so no naturality statement for a comparison of
coinduced modules is required.

## Main definitions

* `InverseGalois.CFT.sectionsStabHom`: evaluation at an index, as a map of representations of a
  subgroup fixing that index.
* `InverseGalois.CFT.stabCocycles₁`: the value at an index of a one-cocycle of the sections, as a
  one-cocycle of a subgroup fixing that index.

## Main results

* `InverseGalois.CFT.H1π_eq_zero_of_forall_stab`: **the class of a one-cocycle of the sections
  vanishes as soon as its class at the stabiliser of every index vanishes.**
* `InverseGalois.CFT.eq_zero_of_forall_tateMap_tateRes_eq_zero`: the same for a class of the first
  cohomology, written with restriction to the stabiliser followed by evaluation.

## Tags

group cohomology, Shapiro's lemma, family of modules, sections, stabiliser, decomposition group,
idele
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate groupCohomology

noncomputable section

/-! ### Evaluation at an index -/

section Local

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (x₀ : X) {H : Subgroup G} (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)

/-- **Evaluation at an index, as a map of representations of a subgroup fixing that index.** -/
def sectionsStabHom : resObj H (orbitSectionsRep F) ⟶ orbitStabRep x₀ hH' F :=
  mkHom { toFun := fun u => u x₀, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    fun s => LinearMap.ext fun u => F.familyAut_apply_eq_transport (hH' s) u

/-- **The value at an index of a one-cocycle of the sections, as a one-cocycle of a subgroup fixing
that index.** -/
def stabCocycles₁ (b : cocycles₁ (orbitSectionsRep F)) : cocycles₁ (orbitStabRep x₀ hH' F) :=
  ⟨fun s => (b : G → ∀ x, M x) (s : G) x₀, (mem_cocycles₁_iff _).2 fun s t => by
    show (b : G → ∀ x, M x) ((s : G) * (t : G)) x₀
      = F.transport (hH' s) ((b : G → ∀ x, M x) (t : G) x₀) + (b : G → ∀ x, M x) (s : G) x₀
    rw [(mem_cocycles₁_iff (b : G → ↥(orbitSectionsRep F).V)).1 b.2 (s : G) (t : G)]
    show F.familyAut (s : G) ((b : G → ∀ x, M x) (t : G)) x₀ + (b : G → ∀ x, M x) (s : G) x₀ = _
    rw [F.familyAut_apply_eq_transport (hH' s)]⟩

@[simp]
theorem stabCocycles₁_apply (b : cocycles₁ (orbitSectionsRep F)) (s : ↥H) :
    stabCocycles₁ F x₀ hH' b s = (b : G → ∀ x, M x) (s : G) x₀ := rfl

/-- The value at an index of a one-cocycle is the cocycle read on the subgroup and pushed forward
along evaluation. -/
theorem stabCocycles₁_eq (b : cocycles₁ (orbitSectionsRep F)) :
    stabCocycles₁ F x₀ hH' b
      = homCocycles₁ (sectionsStabHom F x₀ hH') (resCocycles₁ H (orbitSectionsRep F) b) := rfl

end Local

/-! ### A class with vanishing local classes -/

section Global

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G)

/-- **The class of a one-cocycle of the sections of a family vanishes as soon as its class at the
stabiliser of every index vanishes.**  A local class vanishes exactly when the value of the cocycle
at the index is a coboundary for the stabiliser there, which is the hypothesis of the coboundary
theorem for families in degree one. -/
theorem H1π_eq_zero_of_forall_stab (b : cocycles₁ (orbitSectionsRep F))
    (h : ∀ x₀ : X, H1π (orbitStabRep x₀ (fun g : ↥(stabilizer G x₀) => g.2) F)
      (stabCocycles₁ F x₀ (fun g : ↥(stabilizer G x₀) => g.2) b) = 0) :
    H1π (orbitSectionsRep F) b = 0 := by
  have hcoc : F.IsCocycle₁ (fun g => (b : G → ∀ x, M x) g) := fun g g' =>
    (mem_cocycles₁_iff (b : G → ↥(orbitSectionsRep F).V)).1 b.2 g g'
  obtain ⟨u, hu⟩ := FamilyAction.exists_coboundary₁ hcoc fun x₀ => by
    obtain ⟨c, hc⟩ := (H1π_eq_zero_iff _).1 (h x₀)
    exact ⟨c, fun s hs => (congrFun hc ⟨s, hs⟩).symm⟩
  exact (H1π_eq_zero_iff b).2 ⟨u, funext fun g => hu g⟩

variable [Finite G]

/-- **A class in the first cohomology of the sections of a family vanishes as soon as its
restriction to the stabiliser of every index, evaluated there, vanishes.** -/
theorem eq_zero_of_forall_tateMap_tateRes_eq_zero (x : groupCohomology (orbitSectionsRep F) 1)
    (h : ∀ x₀ : X, tateMap (sectionsStabHom F x₀ (fun g : ↥(stabilizer G x₀) => g.2)) 1
      (tateRes (stabilizer G x₀) (orbitSectionsRep F) 1 x) = 0) :
    x = 0 := by
  obtain ⟨b, rfl⟩ := Tate.exists_H1π (orbitSectionsRep F) x
  refine H1π_eq_zero_of_forall_stab F b fun x₀ => ?_
  have hx := h x₀
  rw [tateRes_one_H1π, tateMap_one_H1π] at hx
  rw [stabCocycles₁_eq]
  exact hx

end Global

end

end InverseGalois.CFT
