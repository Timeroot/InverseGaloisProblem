/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.TorsionRep
import InverseGalois.CFT.TateCohomology.NakayamaNatural
import InverseGalois.CFT.TateCohomology.TateDegreeTwo
import InverseGalois.CFT.TateCohomology.TensorFunctor

/-!
# A representation cut into two pieces sees its first cohomology piecewise

A pair of maps out of a representation whose combined effect is a bijection presents that
representation as a product of the two targets, and cohomology of a product is the product of the
cohomologies.  In degree one this can be seen directly on cocycles: a cocycle whose two images are
coboundaries is a coboundary, because the two coboundary witnesses assemble to a single element
under the bijection.  **So a class of the first cohomology vanishes as soon as both of its images
do.**

The pair of maps this is wanted for is the two projections of a product of two modules with
componentwise actions, and the twisted form of it, where both projections are tensored on the right
with coefficients.  The twisted form is not a formal consequence of the untwisted one, because a
tensor product need not commute with an arbitrary product; but it does commute with a product of
*two* modules, with no hypothesis on either of them, and that is what is recorded here.

The group of ideles of a number field is a product of two such halves, the infinite places and the
finite ones, and the coefficients that Kummer theory attaches to a solvable embedding problem are
not killed by any single integer on the local unit groups.  So the twisted product statement below
is the only form of the splitting that applies to it.

## Main definitions

* `InverseGalois.CFT.Tate.pairProj`: a pair of maps out of a representation, read as a single map
  to the product of the two targets.
* `InverseGalois.CFT.Tate.prodFstHom`, `InverseGalois.CFT.Tate.prodSndHom`: the two projections of
  a product of two modules with componentwise actions.

## Main results

* `InverseGalois.CFT.Tate.H1π_eq_zero_of_pairProj`: **the class of a one cocycle vanishes as soon
  as the classes of both of its images do**, for a pair of maps whose combined effect is a
  bijection.
* `InverseGalois.CFT.Tate.eq_zero_of_tateMap_pairProj`: the same for a class of the first
  cohomology.
* `InverseGalois.CFT.Tate.bijective_pairProj_prod`,
  `InverseGalois.CFT.Tate.bijective_pairProj_tensor_prod`: the two projections of a product of two
  modules, and the same two projections tensored with coefficients, are such a pair.

## Tags

group cohomology, Tate cohomology, product, projection, tensor product, idele
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation groupCohomology

open scoped TensorProduct

universe u

noncomputable section

/-! ### A pair of maps out of a representation -/

section Pair

variable {k G : Type u} [CommRing k] [Group G] {P A₁ A₂ : Rep k G} (π₁ : P ⟶ A₁) (π₂ : P ⟶ A₂)

/-- **A pair of maps out of a representation, read as a single map to the product of the two
targets.** -/
def pairProj (x : ↥P.V) : ↥A₁.V × ↥A₂.V := (π₁.hom.hom x, π₂.hom.hom x)

/-- **The class of a one cocycle vanishes as soon as the classes of both of its images vanish**,
for a pair of maps whose combined effect is a bijection.  The two coboundary witnesses form a pair,
which comes from a single element of the source, and that element is a coboundary witness for the
cocycle itself because the pair of maps is injective. -/
theorem H1π_eq_zero_of_pairProj (hbij : Function.Bijective (pairProj π₁ π₂))
    (b : cocycles₁ P) (h₁ : H1π A₁ (homCocycles₁ π₁ b) = 0)
    (h₂ : H1π A₂ (homCocycles₁ π₂ b) = 0) :
    H1π P b = 0 := by
  obtain ⟨c₁, hc₁⟩ := (H1π_eq_zero_iff _).1 h₁
  obtain ⟨c₂, hc₂⟩ := (H1π_eq_zero_iff _).1 h₂
  obtain ⟨c, hc⟩ := hbij.surjective (c₁, c₂)
  refine (H1π_eq_zero_iff b).2 ⟨c, funext fun g => hbij.injective (Prod.ext ?_ ?_)⟩
  · show π₁.hom.hom (P.ρ g c - c) = π₁.hom.hom ((b : G → ↥P.V) g)
    rw [_root_.map_sub, ← LinearMap.comp_apply, hom_equivariant π₁ g, LinearMap.comp_apply,
      show π₁.hom.hom c = c₁ from congrArg Prod.fst hc]
    exact congrFun hc₁ g
  · show π₂.hom.hom (P.ρ g c - c) = π₂.hom.hom ((b : G → ↥P.V) g)
    rw [_root_.map_sub, ← LinearMap.comp_apply, hom_equivariant π₂ g, LinearMap.comp_apply,
      show π₂.hom.hom c = c₂ from congrArg Prod.snd hc]
    exact congrFun hc₂ g

variable [Finite G]

/-- **A class of the first cohomology vanishes as soon as both of its images vanish**, for a pair
of maps whose combined effect is a bijection. -/
theorem eq_zero_of_tateMap_pairProj (hbij : Function.Bijective (pairProj π₁ π₂))
    (x : groupCohomology P 1) (h₁ : tateMap π₁ 1 x = 0) (h₂ : tateMap π₂ 1 x = 0) :
    x = 0 := by
  obtain ⟨b, rfl⟩ := Tate.exists_H1π P x
  rw [tateMap_one_H1π] at h₁ h₂
  exact H1π_eq_zero_of_pairProj π₁ π₂ hbij b h₁ h₂

end Pair

/-! ### The two projections of a product of two modules -/

section Prod

variable {G A B : Type} [Group G] [AddCommGroup A] [AddCommGroup B]
  (φ : G →* AddAut A) (ψ : G →* AddAut B)

/-- **The first projection of a product of two modules with componentwise actions.** -/
def prodFstHom : repOfAddAut (prodAutHom φ ψ) ⟶ repOfAddAut φ :=
  mkHom (LinearMap.fst ℤ A B) fun _ => rfl

/-- **The second projection of a product of two modules with componentwise actions.** -/
def prodSndHom : repOfAddAut (prodAutHom φ ψ) ⟶ repOfAddAut ψ :=
  mkHom (LinearMap.snd ℤ A B) fun _ => rfl

/-- **The two projections of a product of two modules combine to a bijection**, which is the
identity. -/
theorem bijective_pairProj_prod :
    Function.Bijective (pairProj (prodFstHom φ ψ) (prodSndHom φ ψ)) :=
  ⟨fun _ _ h => Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h), fun z => ⟨z, rfl⟩⟩

variable (W : Rep ℤ G)

/-- **The two projections of a product of two modules, tensored with coefficients, combine to a
bijection.**  A tensor product commutes with a product of two modules with no hypothesis on either
of them, and the combined map is exactly that comparison. -/
theorem bijective_pairProj_tensor_prod :
    Function.Bijective (pairProj (tensorHomLeft W (prodFstHom φ ψ))
      (tensorHomLeft W (prodSndHom φ ψ))) := by
  have hlin : LinearMap.prod (tensorHomLeft W (prodFstHom φ ψ)).hom.hom
      (tensorHomLeft W (prodSndHom φ ψ)).hom.hom
      = (TensorProduct.prodLeft ℤ ℤ A B ↥W.V).toLinearMap :=
    TensorProduct.ext' fun _ _ => rfl
  have hfun : pairProj (tensorHomLeft W (prodFstHom φ ψ)) (tensorHomLeft W (prodSndHom φ ψ))
      = ⇑(TensorProduct.prodLeft ℤ ℤ A B ↥W.V) :=
    funext fun x => LinearMap.congr_fun hlin x
  rw [hfun]
  exact (TensorProduct.prodLeft ℤ ℤ A B ↥W.V).bijective

end Prod

end

end InverseGalois.CFT.Tate
