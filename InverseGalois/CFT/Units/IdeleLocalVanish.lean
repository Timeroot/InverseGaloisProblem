/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTensorLocal
import InverseGalois.CFT.Tate.ProdH1
import InverseGalois.CFT.TateCohomology.RestrictNatural
import InverseGalois.CFT.Units.IdeleFullCompare

/-!
# A twisted class of the ideles that is trivial at every place is trivial

The ideles of a number field carry the Galois action of an extension, and every place of the top
field has a decomposition subgroup, its stabiliser, together with the local unit group there.  A
class of the first cohomology of the twisted ideles therefore has a local class at every place,
obtained by restricting to the decomposition subgroup and then evaluating at the place, and the
question the Shafarevich tower asks of it is whether those local classes see everything.

They do.  Three steps assemble the statement.  The ideles sit inside the product of all the local
unit groups with a quotient whose invariants all lift, so the first cohomology of the twisted ideles
injects into that of the twisted product.  The product is a product of two halves, the infinite
places and the finite ones, and a class of the first cohomology of a product vanishes as soon as
both of its projections do, the tensored form of the splitting being available because a tensor
product commutes with a product of two modules.  Each half is the sections of a family indexed by
the places of that kind, where a twisted class is detected at the indices.  Chaining the three
gives **a class of the first cohomology of the twisted ideles that is trivial in every
decomposition subgroup is trivial.**

## Main definitions

* `InverseGalois.CFT.ideleInfiniteHom`, `InverseGalois.CFT.ideleAdicHom`: the ideles, read at the
  infinite places and at the finite ones.
* `InverseGalois.CFT.ideleInfiniteLocalHom`, `InverseGalois.CFT.ideleAdicLocalHom`: the twisted
  ideles read in the decomposition subgroup of a place and evaluated there.

## Main results

* `InverseGalois.CFT.eq_zero_of_forall_local_idele`: **a class of the first cohomology of the
  twisted ideles all of whose local classes vanish is zero.**

## Tags

number field, idele, decomposition group, Tate cohomology, local-global, Shafarevich
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

open scoped TensorProduct

noncomputable section

/-! ### Two maps of representations, tensored and composed -/

section TensorAux

variable {G : Type} [Group G] [Finite G] (W : Rep ℤ G)

/-- **A composite of two maps of representations, tensored with coefficients, induces the composite
of the two induced maps** on complete cohomology. -/
theorem tateMap_tensorHomLeft_comp_apply {A B C : Rep ℤ G} (Φ : A ⟶ B) (Ψ : B ⟶ C) (n : ℤ)
    (x : ↥(tateModule (tensorObj A W) n)) :
    tateMap (tensorHomLeft W Ψ) n (tateMap (tensorHomLeft W Φ) n x)
      = tateMap (tensorHomLeft W (Φ ≫ Ψ)) n x := by
  rw [tateMap_comp_apply, tensorHomLeft_comp]

end TensorAux

/-! ### The ideles at the places of one kind -/

section Hom

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **The ideles, read at the infinite places.** -/
def ideleInfiniteHom :
    ideleRep k K ⟶ orbitSectionsRep (infiniteRingFamily (k := k) (K := K)).unitsFamily :=
  ideleToFullIdele k K ≫
    prodFstHom (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut
      (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut

/-- **The ideles, read at the finite places.** -/
def ideleAdicHom :
    ideleRep k K ⟶ orbitSectionsRep (adicRingFamily (k := k) (K := K)).unitsFamily :=
  ideleToFullIdele k K ≫
    prodSndHom (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut
      (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut

variable (W : Rep ℤ Gal(K/k))

/-- **The twisted ideles read in the decomposition subgroup of an infinite place and evaluated
there.** -/
def ideleInfiniteLocalHom (w : InfinitePlace K) :
    resObj (stabilizer Gal(K/k) w) (tensorObj (ideleRep k K) W) ⟶
      tensorObj (orbitStabRep w (fun g : ↥(stabilizer Gal(K/k) w) => g.2)
        (infiniteRingFamily (k := k) (K := K)).unitsFamily)
        (resObj (stabilizer Gal(K/k) w) W) :=
  resHom _ (tensorHomLeft W (ideleInfiniteHom k K)) ≫
    sectionsStabTensorHom (infiniteRingFamily (k := k) (K := K)).unitsFamily W w
      (fun g : ↥(stabilizer Gal(K/k) w) => g.2)

/-- **The twisted ideles read in the decomposition subgroup of a finite place and evaluated
there.** -/
def ideleAdicLocalHom (v : HeightOneSpectrum (𝓞 K)) :
    resObj (stabilizer Gal(K/k) v) (tensorObj (ideleRep k K) W) ⟶
      tensorObj (orbitStabRep v (fun g : ↥(stabilizer Gal(K/k) v) => g.2)
        (adicRingFamily (k := k) (K := K)).unitsFamily)
        (resObj (stabilizer Gal(K/k) v) W) :=
  resHom _ (tensorHomLeft W (ideleAdicHom k K)) ≫
    sectionsStabTensorHom (adicRingFamily (k := k) (K := K)).unitsFamily W v
      (fun g : ↥(stabilizer Gal(K/k) v) => g.2)

end Hom

/-! ### A class trivial at every place -/

section Main

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))

include e in
/-- **A class of the first cohomology of the twisted ideles whose local classes at the infinite
places all vanish dies at the infinite places.**  Restriction to a decomposition subgroup commutes
with reading the ideles at the infinite places, so the hypothesis is the local hypothesis of the
detection theorem for the sections of a family. -/
theorem tateMap_ideleInfiniteHom_eq_zero (y : groupCohomology (tensorObj (ideleRep k K) W) 1)
    (h : ∀ w : InfinitePlace K, tateMap (ideleInfiniteLocalHom k K W w) 1
      (tateRes (stabilizer Gal(K/k) w) (tensorObj (ideleRep k K) W) 1 y) = 0) :
    tateMap (tensorHomLeft W (ideleInfiniteHom k K)) 1 y = 0 := by
  refine eq_zero_of_forall_local_tensor (infiniteRingFamily (k := k) (K := K)).unitsFamily W e _
    fun w => ?_
  rw [tateRes_naturality, tateMap_comp_apply]
  exact h w

include e in
/-- **A class of the first cohomology of the twisted ideles whose local classes at the finite places
all vanish dies at the finite places.** -/
theorem tateMap_ideleAdicHom_eq_zero (y : groupCohomology (tensorObj (ideleRep k K) W) 1)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), tateMap (ideleAdicLocalHom k K W v) 1
      (tateRes (stabilizer Gal(K/k) v) (tensorObj (ideleRep k K) W) 1 y) = 0) :
    tateMap (tensorHomLeft W (ideleAdicHom k K)) 1 y = 0 := by
  refine eq_zero_of_forall_local_tensor (adicRingFamily (k := k) (K := K)).unitsFamily W e _
    fun v => ?_
  rw [tateRes_naturality, tateMap_comp_apply]
  exact h v

include e in
/-- **A class of the first cohomology of the twisted ideles all of whose local classes vanish is
zero.**  The class injects into the twisted product of all the local unit groups, which is a
product of the infinite half and the finite one; both projections of the image vanish because each
half is the sections of a family whose twisted classes are detected at the indices. -/
theorem eq_zero_of_forall_local_idele (y : groupCohomology (tensorObj (ideleRep k K) W) 1)
    (h₁ : ∀ w : InfinitePlace K, tateMap (ideleInfiniteLocalHom k K W w) 1
      (tateRes (stabilizer Gal(K/k) w) (tensorObj (ideleRep k K) W) 1 y) = 0)
    (h₂ : ∀ v : HeightOneSpectrum (𝓞 K), tateMap (ideleAdicLocalHom k K W v) 1
      (tateRes (stabilizer Gal(K/k) v) (tensorObj (ideleRep k K) W) 1 y) = 0) :
    y = 0 := by
  refine injective_tateMap_one_tensor_ideleToFullIdele W e ?_
  rw [_root_.map_zero]
  refine eq_zero_of_tateMap_pairProj
    (tensorHomLeft W (prodFstHom (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut
      (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut))
    (tensorHomLeft W (prodSndHom (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut
      (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut))
    (bijective_pairProj_tensor_prod _ _ W) _ ?_ ?_
  · exact (tateMap_tensorHomLeft_comp_apply W (ideleToFullIdele k K)
      (prodFstHom (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut
        (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut) 1 y).trans
      (tateMap_ideleInfiniteHom_eq_zero W e y h₁)
  · exact (tateMap_tensorHomLeft_comp_apply W (ideleToFullIdele k K)
      (prodSndHom (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut
        (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut) 1 y).trans
      (tateMap_ideleAdicHom_eq_zero W e y h₂)

end Main

end

end InverseGalois.CFT
