/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Tensor
import InverseGalois.CFT.TateCohomology.TensorRight
import InverseGalois.CFT.TateCohomology.TensorTrivial

/-!
# Being the functions on the group is inherited by subgroups and survives tensoring

The functions on a finite group with values in a module have no complete cohomology at all, and
neither does their restriction to a subgroup, nor their tensor product with any representation.
Each of those three statements is already available for a representation which *is* the functions
on the group; what is wanted in practice is the same statements for a representation which is
merely *isomorphic* to them, because that is the shape in which a coefficient module arrives.

The point of collecting them is that the property composes.  A representation isomorphic to the
functions on the group restricts, on any subgroup, to a representation isomorphic to the functions
on that subgroup, with values in the functions on the cosets.  So the property can be transported
along a chain of subgroups and then spent, at the bottom of the chain, against an arbitrary tensor
factor.  That is exactly the pattern in which a vanishing criterion asks for a condition at a Sylow
subgroup, and then again at the stabiliser of a place inside it.

## Main definitions

* `InverseGalois.CFT.Tate.resInducedIso`: the functions on the group, restricted to a subgroup, are
  the functions on the subgroup with values in the functions on the cosets.
* `InverseGalois.CFT.Tate.resIsoInducedRep`: **a representation isomorphic to the functions on the
  group restricts to a representation isomorphic to the functions on a subgroup.**
* `InverseGalois.CFT.Tate.repEval`: the record of the values of a linear map out of a
  representation at all the translates of a vector.
* `InverseGalois.CFT.Tate.inducedRepIsoOfBijective`: **a representation whose reading as functions
  on the group is bijective is the functions on the group.**

## Main results

* `InverseGalois.CFT.Tate.isZero_tateModule_of_isoInducedRep`: a representation isomorphic to the
  functions on the group has no complete cohomology.
* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_right_of_isoInducedRep`,
  `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_left_of_isoInducedRep`: **any representation
  tensored with one isomorphic to the functions on the group has no complete cohomology**, on
  either side.
* `InverseGalois.CFT.Tate.isZero_tateModule_resObj_of_isoInducedRep`: the same after restriction to
  a subgroup.

## Tags

Tate cohomology, induced representation, cohomologically trivial, restriction, tensor product
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

universe u

noncomputable section

section Induced

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **The functions on the group, restricted to a subgroup, are the functions on the subgroup with
values in the functions on the cosets.** -/
def resInducedIso (H : Subgroup G) (X : Type u) [AddCommGroup X] [Module k X] :
    resObj H (Rep.of (inducedRep k G X)) ≅ Rep.of (inducedRep k ↥H ((G ⧸ H) → X)) :=
  indRestrictIso H (Rep.trivial k G X)

variable {X : Type u} [AddCommGroup X] [Module k X] {A : Rep k G}

/-- **A representation isomorphic to the functions on the group restricts, on a subgroup, to a
representation isomorphic to the functions on that subgroup**, with values in the functions on the
cosets.  So the hypothesis that a coefficient module is the functions on the group can be carried
down a chain of subgroups. -/
def resIsoInducedRep (e : A ≅ Rep.of (inducedRep k G X)) (H : Subgroup G) :
    resObj H A ≅ Rep.of (inducedRep k ↥H ((G ⧸ H) → X)) :=
  (Action.res _ H.subtype).mapIso e ≪≫ resInducedIso H X

/-- **A representation isomorphic to the functions on the group has no complete cohomology.** -/
theorem isZero_tateModule_of_isoInducedRep (e : A ≅ Rep.of (inducedRep k G X)) (n : ℤ) :
    Limits.IsZero (tateModule A n) :=
  isZero_tateModule_of_iso e n (isZero_tateModule_inducedRep n)

/-- **A representation isomorphic to the functions on the group still has no complete cohomology
after restriction to a subgroup.** -/
theorem isZero_tateModule_resObj_of_isoInducedRep (e : A ≅ Rep.of (inducedRep k G X))
    (H : Subgroup G) (n : ℤ) : Limits.IsZero (tateModule (resObj H A) n) :=
  isZero_tateModule_of_isoInducedRep (resIsoInducedRep e H) n

/-- **Any representation tensored on the left with one isomorphic to the functions on the group has
no complete cohomology.** -/
theorem isZero_tateModule_tensorObj_right_of_isoInducedRep (e : A ≅ Rep.of (inducedRep k G X))
    (M : Rep k G) (n : ℤ) : Limits.IsZero (tateModule (tensorObj M A) n) :=
  isZero_tateModule_of_iso (tensorIsoRight M e) n
    (isZero_tateModule_tensorObj_inducedRep' X M n)

/-- **Any representation tensored on the right with one isomorphic to the functions on the group
has no complete cohomology.** -/
theorem isZero_tateModule_tensorObj_left_of_isoInducedRep (e : A ≅ Rep.of (inducedRep k G X))
    (M : Rep k G) (n : ℤ) : Limits.IsZero (tateModule (tensorObj A M) n) :=
  isZero_tateModule_of_iso (tensorIsoLeft M e) n
    (isZero_tateModule_tensorObj_inducedRep X M n)

end Induced

section Bijective

variable {k G : Type u} [CommRing k] [Group G] {Y : Type u} [AddCommGroup Y] [Module k Y]
  {A : Rep k G}

/-- **The reading of a representation as functions on the group**: the record of the values of a
linear map out of it at all the translates of a vector. -/
def repEval (φ : ↥A.V →ₗ[k] Y) : ↥A.V →ₗ[k] (G → Y) where
  toFun a x := φ (A.ρ x a)
  map_add' a b := funext fun x => by rw [Pi.add_apply, _root_.map_add, _root_.map_add]
  map_smul' c a := funext fun x => by
    rw [Pi.smul_apply, RingHom.id_apply, _root_.map_smul, _root_.map_smul]

@[simp]
theorem repEval_apply (φ : ↥A.V →ₗ[k] Y) (a : ↥A.V) (x : G) : repEval φ a x = φ (A.ρ x a) := rfl

/-- **The reading of a representation as functions on the group is equivariant** for translation on
the right. -/
theorem repEval_comp_rho (φ : ↥A.V →ₗ[k] Y) (g : G) :
    repEval φ ∘ₗ (A.ρ g : ↥A.V →ₗ[k] ↥A.V) = (inducedRep k G Y g : (G → Y) →ₗ[k] (G → Y))
      ∘ₗ repEval φ :=
  LinearMap.ext fun a => funext fun x => by
    show φ (A.ρ x (A.ρ g a)) = φ (A.ρ (x * g) a)
    rw [← Module.End.mul_apply, ← _root_.map_mul]

/-- **A representation whose reading as functions on the group is bijective is the functions on the
group.**  So a single map out of the coefficients, whose translates separate and exhaust, is all
the data needed to recognise the coefficients as an induced module. -/
def inducedRepIsoOfBijective (φ : ↥A.V →ₗ[k] Y) (hbij : Function.Bijective (repEval φ)) :
    A ≅ Rep.of (inducedRep k G Y) :=
  Action.mkIso (LinearEquiv.ofBijective (repEval φ) hbij).toModuleIso fun g =>
    ModuleCat.hom_ext (repEval_comp_rho φ g)

end Bijective

end

end InverseGalois.CFT.Tate
