/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyH1Local
import InverseGalois.CFT.Tate.FamilyTensorFull

/-!
# The twisted first cohomology of the sections of a family is detected at the indices

Coefficients of finite rank over a prime field pass through the sections of a family of modules, so
the sections tensored with such coefficients are the sections of the tensored family.  The statement
that a class of the first cohomology of the sections all of whose local classes vanish is zero
therefore survives twisting, and this file records it in the form the ideles need: **a class of the
first cohomology of the sections of a family tensored with the coefficients is zero as soon as, for
every index, its restriction to the stabiliser of that index followed by evaluation there
vanishes.**

Two comparisons are needed to say this.  Evaluation at an index is tensored with the coefficients
read on the stabiliser, which is the map the local hypothesis is about; and at a fixed index the
tensored family is the module there tensored with the restricted coefficients, an identification
that is the identity on the underlying groups.  Both are transparent, and no isomorphism between
the sections over an orbit and a coinduced module is constructed anywhere: the local hypothesis is
consumed at the level of cochains.

## Main definitions

* `InverseGalois.CFT.stabTensorIso`: at a fixed index the tensored family gives the module there
  tensored with the coefficients restricted to a subgroup fixing the index.
* `InverseGalois.CFT.sectionsStabTensorHom`: evaluation at an index, tensored with the coefficients.

## Main results

* `InverseGalois.CFT.eq_zero_of_forall_local_tensor`: **a class of the first cohomology of the
  twisted sections of a family vanishes as soon as all of its local classes do.**

## Tags

group cohomology, Shapiro's lemma, family of modules, sections, stabiliser, decomposition group,
idele, tensor product
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate groupCohomology

noncomputable section

/-! ### The tensored family at one index -/

section Stab

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (W : Rep ℤ G) (x₀ : X) {H : Subgroup G}
  (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)

/-- **At an index fixed by a subgroup the tensored family gives the module there tensored with the
coefficients restricted to that subgroup.**  The identification is the identity on the underlying
groups: transporting a pure tensor around the tensored family transports the first factor and acts
on the second. -/
def stabTensorIso :
    orbitStabRep x₀ hH' (F.tensorRight W) ≅ tensorObj (orbitStabRep x₀ hH' F) (resObj H W) :=
  Action.mkIso (AddEquiv.refl _).toIntLinearEquiv.toModuleIso fun g => by
    ext a
    induction a using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul b w => exact tensorRight_transport_tmul F W (hH' g) b w
    | add a a' ha ha' => rw [map_add, map_add, ha, ha']

/-- **Evaluation at an index, tensored with the coefficients**, as a map of representations of a
subgroup fixing the index. -/
def sectionsStabTensorHom :
    resObj H (tensorObj (orbitSectionsRep F) W) ⟶ tensorObj (orbitStabRep x₀ hH' F) (resObj H W) :=
  tensorHomLeft (resObj H W) (sectionsStabHom F x₀ hH')

end Stab

/-! ### A twisted class with vanishing local classes -/

section Main

variable {G X : Type} [Group G] [MulAction G X] [Finite G] {M : X → Type}
  [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (W : Rep ℤ G) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p))

include e in
/-- **A class of the first cohomology of the sections of a family tensored with coefficients of
finite rank over a prime field vanishes as soon as, at every index, its restriction to the
stabiliser of the index followed by evaluation there vanishes.**  The coefficients pass through the
sections, so the class becomes one of the sections of the tensored family, where the coboundary
theorem for families applies; the local hypotheses are the same after the two transparent
comparisons of the twisted evaluation maps. -/
theorem eq_zero_of_forall_local_tensor (x : groupCohomology (tensorObj (orbitSectionsRep F) W) 1)
    (h : ∀ x₀ : X, tateMap (sectionsStabTensorHom F W x₀ (fun g : ↥(stabilizer G x₀) => g.2)) 1
      (tateRes (stabilizer G x₀) (tensorObj (orbitSectionsRep F) W) 1 x) = 0) :
    x = 0 := by
  obtain ⟨b, rfl⟩ := Tate.exists_H1π (tensorObj (orbitSectionsRep F) W) x
  refine (tateMapIso (tensorSectionsIsoOfEquivPi F W e) 1).toLinearEquiv.toAddEquiv.injective ?_
  rw [_root_.map_zero]
  show tateMap (tensorSectionsIsoOfEquivPi F W e).hom 1 _ = 0
  rw [tateMap_one_H1π]
  refine H1π_eq_zero_of_forall_stab (F.tensorRight W) _ fun x₀ => ?_
  refine (tateMapIso (stabTensorIso F W x₀ (fun g : ↥(stabilizer G x₀) => g.2))
    1).toLinearEquiv.toAddEquiv.injective ?_
  rw [_root_.map_zero]
  show tateMap (stabTensorIso F W x₀ (fun g : ↥(stabilizer G x₀) => g.2)).hom 1 _ = 0
  rw [tateMap_one_H1π]
  have hx := h x₀
  rw [tateRes_one_H1π, tateMap_one_H1π] at hx
  rw [show homCocycles₁ (stabTensorIso F W x₀ (fun g : ↥(stabilizer G x₀) => g.2)).hom
        (stabCocycles₁ (F.tensorRight W) x₀ (fun g : ↥(stabilizer G x₀) => g.2)
          (homCocycles₁ (tensorSectionsIsoOfEquivPi F W e).hom b))
      = homCocycles₁ (sectionsStabTensorHom F W x₀ (fun g : ↥(stabilizer G x₀) => g.2))
          (resCocycles₁ (stabilizer G x₀) (tensorObj (orbitSectionsRep F) W) b) from
    Subtype.ext (funext fun s => sectionsTensorMap_apply F W x₀ (b (s : G)))]
  exact hx

end Main

end

end InverseGalois.CFT
