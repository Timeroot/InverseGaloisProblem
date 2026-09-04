/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Graded

/-!
# Transport of cohomology along an isomorphism of groups

The cohomology of a group with coefficients in a representation is computed by the complex of
inhomogeneous cochains, and a homomorphism of groups together with a compatible map of coefficients
induces a map of those complexes: a cochain is composed with the homomorphism in its arguments and
with the coefficient map in its values.  When the homomorphism is an isomorphism and the coefficient
map is bijective, both of those operations are bijections, so the induced map of complexes is an
isomorphism in every degree, hence an isomorphism of complexes.

Homology carries an isomorphism of complexes to an isomorphism, so the cohomology of the two groups
agrees in every degree.  This is what lets a computation made for one presentation of a group be
read off for another — for the decomposition group of a place of a Galois extension of number
fields, say, which is at once a subgroup of the global Galois group and the Galois group of the
extension of the completions.

## Main definitions

* `InverseGalois.CFT.Tate.groupCohomologyCongr`: **the cohomology of a group transported along an
  isomorphism of groups and a bijective map of coefficients.**
* `InverseGalois.CFT.Tate.tateModuleCongrSucc`: the same statement in a positive degree of the
  complete cohomology.
* `InverseGalois.CFT.Tate.tateOneCongr`, `InverseGalois.CFT.Tate.tateTwoCongr`: the same statement
  in degrees one and two.

## Main results

* `InverseGalois.CFT.Tate.bijective_cochainsMap_f`: every component of the induced map of complexes
  of inhomogeneous cochains is bijective.
* `InverseGalois.CFT.Tate.isIso_cochainsMap_of_bijective`: hence that map is an isomorphism of
  complexes.

## Tags

group cohomology, isomorphism of groups, inhomogeneous cochains, Tate cohomology
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

universe u

noncomputable section

variable {k G G' : Type u} [CommRing k] [Group G] [Group G'] {A : Rep k G'} {B : Rep k G}
  (e : G ≃* G') (φ : (Action.res _ (e : G →* G')).obj A ⟶ B)

/-! ### The map of complexes of inhomogeneous cochains -/

/-- **Every component of the map of complexes of inhomogeneous cochains attached to an isomorphism
of groups and a bijective map of coefficients is bijective**: composing the arguments of a cochain
with a bijection is a bijection, and so is applying a bijection to its values. -/
theorem bijective_cochainsMap_f (hφ : Function.Bijective ⇑φ.hom.hom) (i : ℕ) :
    Function.Bijective ⇑((groupCohomology.cochainsMap (e : G →* G') φ).f i) := by
  haveI : Mono φ := (Rep.mono_iff_injective φ).2 hφ.1
  haveI : Epi φ := (Rep.epi_iff_surjective φ).2 hφ.2
  haveI := groupCohomology.cochainsMap_f_map_mono (e : G →* G') φ e.surjective i
  haveI := groupCohomology.cochainsMap_f_map_epi (e : G →* G') φ e.injective i
  exact ⟨(ModuleCat.mono_iff_injective _).1 inferInstance,
    (ModuleCat.epi_iff_surjective _).1 inferInstance⟩

/-- **The map of complexes of inhomogeneous cochains attached to an isomorphism of groups and a
bijective map of coefficients is an isomorphism of complexes**, being an isomorphism in every
degree. -/
theorem isIso_cochainsMap_of_bijective (hφ : Function.Bijective ⇑φ.hom.hom) :
    IsIso (groupCohomology.cochainsMap (e : G →* G') φ) := by
  haveI : ∀ i : ℕ, IsIso ((groupCohomology.cochainsMap (e : G →* G') φ).f i) := fun i =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_cochainsMap_f e φ hφ i)
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ### The transported cohomology -/

/-- **The cohomology of a group with coefficients in a representation depends on the pair only up
to isomorphism**: an isomorphism of groups and a bijective map of coefficients compatible with it
induce an isomorphism of the cohomology in every degree. -/
def groupCohomologyCongr (hφ : Function.Bijective ⇑φ.hom.hom) (n : ℕ) :
    groupCohomology A n ≅ groupCohomology B n :=
  letI := isIso_cochainsMap_of_bijective e φ hφ
  HomologicalComplex.homologyMapIso (asIso (groupCohomology.cochainsMap (e : G →* G') φ)) n

/-- The transported cohomology is the functorial map of the underlying homomorphism of groups. -/
theorem groupCohomologyCongr_hom (hφ : Function.Bijective ⇑φ.hom.hom) (n : ℕ) :
    (groupCohomologyCongr e φ hφ n).hom = groupCohomology.map (e : G →* G') φ n :=
  rfl

variable (A) in
/-- **The cohomology of a group is the cohomology of any group isomorphic to it**, with
coefficients restricted along the isomorphism. -/
def groupCohomologyResCongr (n : ℕ) :
    groupCohomology A n ≅ groupCohomology ((Action.res _ (e : G →* G')).obj A) n :=
  groupCohomologyCongr e (𝟙 _) Function.bijective_id n

/-! ### The complete cohomology -/

section Tate

variable [Finite G] [Finite G']

/-- **A positive degree of the complete cohomology of a group depends on the pair of the group and
its coefficients only up to isomorphism.** -/
def tateModuleCongrSucc (hφ : Function.Bijective ⇑φ.hom.hom) (m : ℕ) :
    tateModule A ((m : ℤ) + 1) ≅ tateModule B ((m : ℤ) + 1) :=
  eqToIso (tateModule_natCast_succ A m) ≪≫ groupCohomologyCongr e φ hφ (m + 1) ≪≫
    eqToIso (tateModule_natCast_succ B m).symm

/-- **Degree one of the complete cohomology of a group depends on the pair of the group and its
coefficients only up to isomorphism**, which is the degree whose vanishing enters Tate's theorem. -/
def tateOneCongr (hφ : Function.Bijective ⇑φ.hom.hom) : tateModule A 1 ≅ tateModule B 1 :=
  eqToIso (congrArg (tateModule A) (by norm_num)) ≪≫ tateModuleCongrSucc e φ hφ 0 ≪≫
    eqToIso (congrArg (tateModule B) (by norm_num))

/-- **Degree two of the complete cohomology of a group depends on the pair of the group and its
coefficients only up to isomorphism**, which is the degree carrying the local invariants. -/
def tateTwoCongr (hφ : Function.Bijective ⇑φ.hom.hom) : tateModule A 2 ≅ tateModule B 2 :=
  eqToIso (congrArg (tateModule A) (by norm_num)) ≪≫ tateModuleCongrSucc e φ hφ 1 ≪≫
    eqToIso (congrArg (tateModule B) (by norm_num))

end Tate

end

end InverseGalois.CFT.Tate
