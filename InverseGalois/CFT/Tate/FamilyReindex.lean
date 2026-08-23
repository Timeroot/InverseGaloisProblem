/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family
import InverseGalois.CFT.Tate.FamilySigma

/-!
# Reindexing a family of modules along an equivalence of index sets

A family of modules indexed by a set with a group action may be pulled back along an equivalence of
index sets that respects the actions, and its group of sections is then carried along.  This is the
step that turns an abstract decomposition of the index set into a decomposition of the sections:
the places of a Galois extension of number fields are the disjoint union of their orbits under the
Galois group, and the equivalence expressing that is exactly the kind of reindexing set up here.

Combining the reindexing with the splitting of the sections over a disjoint union presents the
group of sections of any family as the product over the orbits of the sections over one orbit.

## Main definitions

* `InverseGalois.CFT.FamilyAction.reindex`: the family pulled back along an equivalence of index
  sets respecting the actions.
* `InverseGalois.CFT.reindexFamilyEquiv`: **the sections of the family and of its pullback are the
  same.**

## Main results

* `InverseGalois.CFT.reindexFamilyEquiv_familyAut`: the identification of the sections is
  compatible with the actions.
* `InverseGalois.CFT.herbrand_familyAut_reindex`: reindexing does not change the Herbrand quotient
  of the sections.
* `InverseGalois.CFT.equivariant_selfEquivSigmaOrbits`: the decomposition of a set into its orbits
  respects the action.

## Tags

Tate cohomology, Herbrand quotient, family of modules, reindexing, orbit decomposition
-/

namespace InverseGalois.CFT

variable {G X X' : Type*} [Group G] [MulAction G X] [MulAction G X']
  {M : X → Type*} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)
  (e : X' ≃ X) (he : ∀ (g : G) (x' : X'), e (g • x') = g • e x')

/-! ### A transport followed by a change of the target index -/

/-- Transporting and then moving the target index by an equality is one transport. -/
theorem famCast_transport {g : G} {x y z : X} (h : g • x = y) (h' : y = z) (a : M x) :
    famCast M h' (F.transport h a) = F.transport (h.trans h') a := by
  rw [FamilyAction.transport_apply, FamilyAction.transport_apply, famCast_trans_apply]

/-! ### The pullback of a family -/

namespace FamilyAction

/-- **The family pulled back along an equivalence of index sets respecting the actions.** -/
def reindex : FamilyAction (fun x' : X' => M (e x')) G where
  map g x' := F.transport (he g x').symm
  map_one x' a := (F.transport_one _ a).trans (famCast_comp M e (one_smul G x').symm a).symm
  map_mul g h x' a := by
    rw [famCast_comp M e (mul_smul g h x').symm, famCast_transport,
      F.transport_trans (he h x').symm
        (((he g (h • x')).symm).trans (congrArg e (mul_smul g h x').symm)) (he (g * h) x').symm]

@[simp]
theorem reindex_map (g : G) (x' : X') :
    (F.reindex e he).map g x' = F.transport (he g x').symm := rfl

/-- A transport for the pullback is a transport for the family. -/
theorem reindex_transport {g : G} {x' y' : X'} (h : g • x' = y') (a : M (e x')) :
    (F.reindex e he).transport h a = F.transport ((he g x').symm.trans (congrArg e h)) a := by
  rw [FamilyAction.transport_apply (F.reindex e he) h a, FamilyAction.reindex_map,
    famCast_comp M e h, famCast_transport]

end FamilyAction

/-! ### The sections of the pullback -/

/-- **The sections of a family and of its pullback along an equivalence of index sets are the
same.** -/
def reindexFamilyEquiv : (∀ x : X, M x) ≃+ (∀ x' : X', M (e x')) where
  toFun f x' := f (e x')
  invFun f x := famCast M (e.apply_symm_apply x) (f (e.symm x))
  left_inv f := funext fun x => famCast_apply_section M (e.apply_symm_apply x) f
  right_inv f := by
    funext x'
    show famCast M (congrArg e (e.symm_apply_apply x')) (f (e.symm (e x'))) = f x'
    rw [← famCast_comp M e (e.symm_apply_apply x')]
    exact famCast_apply_section (fun w => M (e w)) (e.symm_apply_apply x') f
  map_add' _ _ := rfl

@[simp]
theorem reindexFamilyEquiv_apply (f : ∀ x : X, M x) (x' : X') :
    reindexFamilyEquiv e f x' = f (e x') := rfl

/-- **The identification of the sections is compatible with the actions.** -/
theorem reindexFamilyEquiv_familyAut (σ : G) (f : ∀ x : X, M x) :
    reindexFamilyEquiv e (F.familyAut σ f)
      = (F.reindex e he).familyAut σ (reindexFamilyEquiv (M := M) e f) := by
  funext x'
  have h : σ • e (σ⁻¹ • x') = e x' :=
    (he σ (σ⁻¹ • x')).symm.trans (congrArg e (smul_inv_smul σ x'))
  show F.familyAut σ f (e x') = (F.reindex e he).familyAut σ (fun w => f (e w)) x'
  rw [F.familyAut_apply_eq_transport h f,
    (F.reindex e he).familyAut_apply_eq_transport (smul_inv_smul σ x') (fun w => f (e w)),
    FamilyAction.reindex_transport]

/-- **Reindexing does not change the Herbrand quotient of the sections.** -/
theorem herbrand_familyAut_reindex (σ : G) (n : ℕ) :
    herbrand (F.familyAut σ) n = herbrand ((F.reindex e he).familyAut σ) n :=
  herbrand_congr (reindexFamilyEquiv (M := M) e) (reindexFamilyEquiv_familyAut F e he σ) n

/-- Reindexing does not change the vanishing of the upper Tate group of the sections. -/
theorem subsingleton_tateH0_familyAut_reindex (σ : G) (n : ℕ)
    (h : Subsingleton (tateH0 ((F.reindex e he).familyAut σ) n)) :
    Subsingleton (tateH0 (F.familyAut σ) n) :=
  ⟨fun _ _ => (tateH0Congr (reindexFamilyEquiv (M := M) e)
    (reindexFamilyEquiv_familyAut F e he σ) n).injective (Subsingleton.elim _ _)⟩

/-- Reindexing does not change the vanishing of the lower Tate group of the sections. -/
theorem subsingleton_tateHm1_familyAut_reindex (σ : G) (n : ℕ)
    (h : Subsingleton (tateHm1 ((F.reindex e he).familyAut σ) n)) :
    Subsingleton (tateHm1 (F.familyAut σ) n) :=
  ⟨fun _ _ => (tateHm1Congr (reindexFamilyEquiv (M := M) e)
    (reindexFamilyEquiv_familyAut F e he σ) n).injective (Subsingleton.elim _ _)⟩

/-! ### The decomposition into orbits -/

open MulAction

/-- The decomposition of a set into its orbits reads off the underlying point. -/
theorem selfEquivSigmaOrbits_symm_apply (s : Σ ω : orbitRel.Quotient G X, ω.orbit) :
    (selfEquivSigmaOrbits' G X).symm s = (s.2 : X) := rfl

/-- **The decomposition of a set into its orbits respects the action.** -/
theorem equivariant_selfEquivSigmaOrbits (g : G) (s : Σ ω : orbitRel.Quotient G X, ω.orbit) :
    (selfEquivSigmaOrbits' G X).symm (g • s) = g • (selfEquivSigmaOrbits' G X).symm s := rfl

end InverseGalois.CFT
