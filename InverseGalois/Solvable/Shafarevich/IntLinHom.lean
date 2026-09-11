/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.HomologyIntegral
import InverseGalois.CFT.TateCohomology.CyclicDualNatural

/-!
# The maps between two representations of prime characteristic, read over the integers

Between two modules over the integers modulo a number, an additive map is automatically linear:
the scalars are themselves classes of integers, and multiplication by an integer is repeated
addition.  So the maps of one representation of prime characteristic into another are the same
whether they are counted over the small ring or over the integers, and reading a representation
over the integers commutes with forming the representation of maps.

That identification is what lets a class of complete cohomology produced by global duality, whose
coefficients are the maps of one abelian group into another, be recognised as a class with the
coefficients the ladder uses.  It is compatible with a map of the target, which is what carries the
recognition along a shrinking.

## Main definitions

* `InverseGalois.Shafarevich.intRepIso` — an isomorphism of representations of prime
  characteristic, read over the integers.
* `InverseGalois.Shafarevich.intLinHomIso` — **the maps between two representations of prime
  characteristic, over the integers, are the maps over the small ring.**

## Main results

* `InverseGalois.Shafarevich.intLinHomIso_naturality` — **that identification is compatible with a
  map of the target representation.**

## Tags

group representation, change of rings, duality, Shafarevich's theorem
-/

namespace InverseGalois.Shafarevich

open CategoryTheory InverseGalois.CFT InverseGalois.CFT.Tate

/-! ### Reading a map of representations over the integers is functorial -/

section Functorial

variable {ℓ : ℕ} {G : Type} [Group G]

@[simp]
theorem intRepMap_id (A : Rep (ZMod ℓ) G) : intRepMap (𝟙 A) = 𝟙 (intRep A) :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

@[simp]
theorem intRepMap_comp {A B C : Rep (ZMod ℓ) G} (ψ : A ⟶ B) (χ : B ⟶ C) :
    intRepMap (ψ ≫ χ) = intRepMap ψ ≫ intRepMap χ :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- **An isomorphism of representations of prime characteristic, read over the integers.** -/
noncomputable def intRepIso {A B : Rep (ZMod ℓ) G} (e : A ≅ B) : intRep A ≅ intRep B where
  hom := intRepMap e.hom
  inv := intRepMap e.inv
  hom_inv_id := by rw [← intRepMap_comp, e.hom_inv_id, intRepMap_id]
  inv_hom_id := by rw [← intRepMap_comp, e.inv_hom_id, intRepMap_id]

@[simp]
theorem intRepIso_hom {A B : Rep (ZMod ℓ) G} (e : A ≅ B) :
    (intRepIso e).hom = intRepMap e.hom := rfl

end Functorial

/-! ### The maps between two representations do not depend on the ring -/

noncomputable section LinHom

variable {ℓ : ℕ} {G : Type} [Group G] (M L : Rep (ZMod ℓ) G)

/-- **An additive map between modules over the integers modulo a number is linear**, so the maps
between two representations of prime characteristic are the same over the integers as over the
small ring. -/
def intLinHomEquiv : (↥M.V →ₗ[ℤ] ↥L.V) ≃ₗ[ℤ] (↥M.V →ₗ[ZMod ℓ] ↥L.V) where
  toFun y := y.toAddMonoidHom.toZModLinearMap ℓ
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  invFun x := x.toAddMonoidHom.toIntLinearMap
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

theorem intLinHomEquiv_equivariant (g : G) :
    (intLinHomEquiv M L).toLinearMap ∘ₗ (linHomObj (intRep M) (intRep L)).ρ g
      = (intRep (linHomObj M L)).ρ g ∘ₗ (intLinHomEquiv M L).toLinearMap :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

theorem intLinHomEquiv_symm_equivariant (g : G) :
    (intLinHomEquiv M L).symm.toLinearMap ∘ₗ (intRep (linHomObj M L)).ρ g
      = (linHomObj (intRep M) (intRep L)).ρ g ∘ₗ (intLinHomEquiv M L).symm.toLinearMap :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- **The maps between two representations of prime characteristic, over the integers, are the maps
over the small ring.** -/
def intLinHomIso : linHomObj (intRep M) (intRep L) ≅ intRep (linHomObj M L) where
  hom := mkHom (intLinHomEquiv M L).toLinearMap (intLinHomEquiv_equivariant M L)
  inv := mkHom (intLinHomEquiv M L).symm.toLinearMap (intLinHomEquiv_symm_equivariant M L)
  hom_inv_id :=
    Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))
  inv_hom_id :=
    Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

@[simp]
theorem intLinHomEquiv_apply (y : ↥M.V →ₗ[ℤ] ↥L.V) (a : ↥M.V) : intLinHomEquiv M L y a = y a := rfl

@[simp]
theorem intLinHomIso_hom_apply (y : ↥M.V →ₗ[ℤ] ↥L.V) :
    (intLinHomIso M L).hom.hom y = intLinHomEquiv M L y := rfl

variable {L}

/-- **Reading the maps into a representation over the integers is compatible with a map of that
representation.** -/
theorem intLinHomIso_naturality {L' : Rep (ZMod ℓ) G} (ψ : L ⟶ L') :
    linHomPostHom (intRep M) (intRepMap ψ) ≫ (intLinHomIso M L').hom
      = (intLinHomIso M L).hom ≫ intRepMap (linHomPostHom M ψ) :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

end LinHom

end InverseGalois.Shafarevich
