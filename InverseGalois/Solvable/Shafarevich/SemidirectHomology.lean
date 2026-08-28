/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The first homology of a semidirect product

A representation of the second factor of a semidirect product is a representation of the whole
product, on which the first factor acts trivially.  For such coefficients the corestriction and
coinflation maps of the first homology fit into an exact sequence, and the quotient by the kernel of
the projection is the second factor itself, so the sequence reads

`H₁(N, A) ⟶ H₁(N ⋊ U, A) ⟶ H₁(U, A)`.

The content is Mathlib's exactness of the degree one corestriction-coinflation sequence; what is
added here is the identification of the two ends, which requires moving a homology map along an
equality of homomorphisms of groups.  That move is packaged separately: two morphisms of
coefficients with the same underlying linear map induce the same map in homology even when the
homomorphisms of groups they lie over are merely equal, and a composite of homology maps may
therefore be recognised whenever the underlying linear maps compose.

## Main definitions

* `InverseGalois.Shafarevich.inflate` — a representation of the second factor, read as a
  representation of the semidirect product.
* `InverseGalois.Shafarevich.kerLeft` — the first factor, as the kernel of the projection.

## Main results

* `InverseGalois.Shafarevich.map_comp_of_eq` — a map in homology splits as a composite as soon as
  the homomorphisms of groups and the underlying linear maps do.
* `InverseGalois.Shafarevich.exists_map_inl_eq_of_map_rightHom_eq_zero` — **a first homology class
  of a semidirect product with coefficients inflated from the second factor comes from the first
  factor as soon as it dies in the homology of the second factor.**

## Tags

group homology, semidirect product, Hochschild–Serre, Shafarevich's theorem
-/

namespace InverseGalois.Shafarevich

open CategoryTheory

/-! ### Moving a homology map along an equality of homomorphisms -/

section Transport

variable {k : Type} [CommRing k] {G H K : Type} [Group G] [Group H] [Group K]

/-- **Two morphisms of coefficients with the same underlying map induce the same map in homology**,
even when the homomorphisms of groups they lie over are only equal. -/
theorem map_eq_map_of_hom_eq {A : Rep k G} {B : Rep k H} {f₁ f₂ : G →* H} (hf : f₁ = f₂)
    (φ₁ : A ⟶ (Action.res _ f₁).obj B) (φ₂ : A ⟶ (Action.res _ f₂).obj B)
    (hφ : φ₁.hom = φ₂.hom) (n : ℕ) :
    groupHomology.map f₁ φ₁ n = groupHomology.map f₂ φ₂ n := by
  subst hf
  exact congrArg (fun ψ => groupHomology.map f₁ ψ n) (Action.Hom.ext hφ)

/-- **A map in homology splits as a composite** as soon as the homomorphisms of groups compose and
the underlying linear maps do. -/
theorem map_comp_of_eq {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (α : A ⟶ (Action.res _ f).obj B) (β : B ⟶ (Action.res _ g).obj C) {h : G →* K}
    (hh : g.comp f = h) (χ : A ⟶ (Action.res _ h).obj C) (hχ : χ.hom = α.hom ≫ β.hom) (n : ℕ) :
    groupHomology.map h χ n = groupHomology.map f α n ≫ groupHomology.map g β n := by
  rw [← groupHomology.map_comp f g α β n]
  exact map_eq_map_of_hom_eq hh.symm χ _ hχ n

end Transport

/-! ### Coefficients inflated from the second factor -/

section Semidirect

variable {k : Type} [CommRing k] {N U : Type} [Group N] [Group U] (φ : U →* MulAut N)
  (B : Rep k U)

/-- A representation of the second factor of a semidirect product, read as a representation of the
whole product. -/
abbrev inflate : Rep k (N ⋊[φ] U) := (Action.res _ (SemidirectProduct.rightHom (φ := φ))).obj B

instance :
    Rep.IsTrivial ((Action.res _ (SemidirectProduct.inl : N →* N ⋊[φ] U)).obj (inflate φ B)) :=
  ⟨fun _ => by simp [Module.End.one_eq_id]⟩

instance : Representation.IsTrivial
    ((inflate φ B).ρ.comp (SemidirectProduct.rightHom (φ := φ)).ker.subtype) :=
  ⟨fun g => by
    have hg : (g : N ⋊[φ] U).right = 1 := g.2
    simp [hg, Module.End.one_eq_id]⟩

/-- The first factor of a semidirect product, read off from the kernel of the projection. -/
def kerLeft : (SemidirectProduct.rightHom (φ := φ)).ker →* N where
  toFun s := (s : N ⋊[φ] U).left
  map_one' := rfl
  map_mul' s t := by
    have hs : (s : N ⋊[φ] U).right = 1 := s.2
    show (s : N ⋊[φ] U).left * φ (s : N ⋊[φ] U).right (t : N ⋊[φ] U).left = _
    rw [hs, map_one]
    rfl

/-- The kernel of the projection is the image of the first factor. -/
theorem inl_comp_kerLeft :
    (SemidirectProduct.inl : N →* N ⋊[φ] U).comp (kerLeft φ)
      = (SemidirectProduct.rightHom (φ := φ)).ker.subtype := by
  refine MonoidHom.ext fun s => ?_
  have hs : (s : N ⋊[φ] U).right = 1 := s.2
  exact SemidirectProduct.ext rfl hs.symm

/-- The second factor is a section of the quotient by the kernel of the projection. -/
theorem mk'_comp_inr_comp_rightHom :
    ((QuotientGroup.mk' (SemidirectProduct.rightHom (φ := φ)).ker).comp
        (SemidirectProduct.inr : U →* N ⋊[φ] U)).comp
      (SemidirectProduct.rightHom (φ := φ))
      = QuotientGroup.mk' (SemidirectProduct.rightHom (φ := φ)).ker := by
  refine MonoidHom.ext fun g => ?_
  refine QuotientGroup.eq.2 ?_
  simp [MonoidHom.mem_ker]

/-- The identity, as a morphism of coefficients from the kernel of the projection to the first
factor. -/
def kerHom :
    (Action.res _ (SemidirectProduct.rightHom (φ := φ)).ker.subtype).obj (inflate φ B) ⟶
      (Action.res _ (kerLeft φ)).obj
        ((Action.res _ (SemidirectProduct.inl : N →* N ⋊[φ] U)).obj (inflate φ B)) where
  hom := 𝟙 _
  comm s := by
    have hs : (s : N ⋊[φ] U).right = 1 := s.2
    simp [hs]

@[simp]
theorem kerHom_hom : (kerHom φ B).hom = 𝟙 _ := rfl

/-- The identity, as a morphism of coefficients from the second factor to the quotient by the
kernel of the projection. -/
def quotHom :
    B ⟶ (Action.res _ ((QuotientGroup.mk' (SemidirectProduct.rightHom (φ := φ)).ker).comp
      (SemidirectProduct.inr : U →* N ⋊[φ] U))).obj
        ((inflate φ B).ofQuotient (SemidirectProduct.rightHom (φ := φ)).ker) :=
  𝟙 B

@[simp]
theorem quotHom_hom : (quotHom φ B).hom = 𝟙 _ := rfl

variable {φ B}

/-- **A first homology class of a semidirect product with coefficients inflated from the second
factor comes from the first factor as soon as its image in the homology of the second factor
vanishes.**  This is the tail of the homological Hochschild–Serre sequence, with the quotient by
the kernel of the projection identified with the second factor. -/
theorem exists_map_inl_eq_of_map_rightHom_eq_zero (x : groupHomology.H1 (inflate φ B))
    (hx : groupHomology.map (SemidirectProduct.rightHom (φ := φ)) (𝟙 (inflate φ B)) 1 x = 0) :
    ∃ y : groupHomology.H1
        ((Action.res _ (SemidirectProduct.inl : N →* N ⋊[φ] U)).obj (inflate φ B)),
      groupHomology.map (SemidirectProduct.inl : N →* N ⋊[φ] U) (𝟙 _) 1 y = x := by
  have hg : (groupHomology.H1CoresCoinfOfTrivial (inflate φ B)
      (SemidirectProduct.rightHom (φ := φ)).ker).g x = 0 := by
    rw [groupHomology.H1CoresCoinfOfTrivial_g,
      map_comp_of_eq (SemidirectProduct.rightHom (φ := φ))
        ((QuotientGroup.mk' (SemidirectProduct.rightHom (φ := φ)).ker).comp
          (SemidirectProduct.inr : U →* N ⋊[φ] U))
        (𝟙 (inflate φ B)) (quotHom φ B) (mk'_comp_inr_comp_rightHom φ)
        (Rep.resOfQuotientIso (inflate φ B) _).inv (by simp) 1,
      ModuleCat.comp_apply]
    show (ConcreteCategory.hom (groupHomology.map
        ((QuotientGroup.mk' (SemidirectProduct.rightHom (φ := φ)).ker).comp
          (SemidirectProduct.inr : U →* N ⋊[φ] U)) (quotHom φ B) 1))
      (ConcreteCategory.hom
        (groupHomology.map (SemidirectProduct.rightHom (φ := φ)) (𝟙 (inflate φ B)) 1) x) = 0
    rw [hx, map_zero]
  obtain ⟨y₀, hy₀⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (groupHomology.H1CoresCoinfOfTrivial_exact (inflate φ B) _) x hg
  rw [groupHomology.H1CoresCoinfOfTrivial_f] at hy₀
  refine ⟨groupHomology.map (kerLeft φ) (kerHom φ B) 1 y₀, ?_⟩
  rw [← ModuleCat.comp_apply, ← map_comp_of_eq (kerLeft φ)
    (SemidirectProduct.inl : N →* N ⋊[φ] U) (kerHom φ B) (𝟙 _) (inl_comp_kerLeft φ) (𝟙 _)
    (by simp) 1]
  exact hy₀

end Semidirect

end InverseGalois.Shafarevich
