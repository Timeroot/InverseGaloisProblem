/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Transport of the second cohomology along an isomorphism

An isomorphism of the acting groups together with a linear isomorphism of the modules
intertwining the two actions carries two-cocycles to two-cocycles and two-coboundaries to
two-coboundaries, in both directions, so the two second cohomology groups are in bijection.

The comparison map is the functorial one attached to the inverse isomorphism of groups, and both
its injectivity and its surjectivity are read off from the description of the second cohomology as
the two-cocycles modulo the two-coboundaries: a cocycle of the target is the image of the cocycle
obtained by transporting it back, and a cocycle whose image is a coboundary is a coboundary,
because the function exhibiting the image as a coboundary can be transported back as well.

## Main definitions

* `InverseGalois.CFT.transportRepHom`: a linear isomorphism intertwining the actions, read as a
  morphism of representations out of the restriction along the inverse isomorphism of groups.
* `InverseGalois.CFT.h2TransportMap`: the induced map on second cohomology.
* `InverseGalois.CFT.h2EquivOfMulEquiv`: the resulting bijection of second cohomology groups.

## Main results

* `InverseGalois.CFT.h2TransportMap_bijective`: **the comparison map on second cohomology attached
  to an isomorphism of groups compatible with a linear isomorphism of the modules is bijective.**
* `InverseGalois.CFT.card_H2_eq_of_mulEquiv`: **the second cohomology groups of two
  representations related by such an isomorphism have the same number of elements.**
* `InverseGalois.CFT.finite_H2_of_mulEquiv`: finiteness of the second cohomology is transported
  along such an isomorphism.
* `InverseGalois.CFT.exists_zsmul_eq_zero_imp_dvd_H2_of_addEquiv`: **a class annihilated only by
  the multiples of a number is transported along such an isomorphism.**

## Tags

group cohomology, second cohomology, transport, isomorphism
-/

universe u

open CategoryTheory groupCohomology

namespace InverseGalois.CFT

noncomputable section

variable {k : Type u} [CommRing k] {G G' : Type u} [Group G] [Group G']
  {A : Rep k G} {B : Rep k G'}

section Transport

variable (e : G ≃* G') (φ : A ≃ₗ[k] B)
  (hφ : ∀ (g : G) (a : A), φ (A.ρ g a) = B.ρ (e g) (φ a))

include hφ

/-- The inverse of an intertwining linear isomorphism intertwines the actions as well. -/
theorem symm_apply_rho (g : G) (b : B) : φ.symm (B.ρ (e g) b) = A.ρ g (φ.symm b) := by
  refine φ.injective ?_
  rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]

/-- A linear isomorphism intertwining the actions of two isomorphic groups, read as a morphism of
representations out of the restriction along the inverse isomorphism. -/
def transportRepHom : (Action.res _ (e.symm : G' →* G)).obj A ⟶ B where
  hom := ModuleCat.ofHom (φ : A →ₗ[k] B)
  comm q := by
    ext a
    show φ (A.ρ (e.symm q) a) = B.ρ q (φ a)
    rw [hφ, MulEquiv.apply_symm_apply]

/-- The map on second cohomology attached to an isomorphism of groups compatible with a linear
isomorphism of the modules. -/
def h2TransportMap : ↥(H2 A) →ₗ[k] ↥(H2 B) :=
  (groupCohomology.map (e.symm : G' →* G) (transportRepHom e φ hφ) 2).hom

theorem h2TransportMap_H2π (x : cocycles₂ A) :
    h2TransportMap e φ hφ (H2π A x)
      = H2π B (mapCocycles₂ (e.symm : G' →* G) (transportRepHom e φ hφ) x) :=
  H2π_comp_map_apply (e.symm : G' →* G) (transportRepHom e φ hφ) x

theorem coe_mapCocycles₂_transport (x : cocycles₂ A) (q : G' × G') :
    (⇑(mapCocycles₂ (e.symm : G' →* G) (transportRepHom e φ hφ) x) : G' × G' → B) q
      = φ ((x : G × G → A) (e.symm q.1, e.symm q.2)) := rfl

/-- Transporting a two-cocycle back along the isomorphism gives a two-cocycle. -/
theorem mem_cocycles₂_transport {z : G' × G' → B} (hz : z ∈ cocycles₂ B) :
    (fun p : G × G => φ.symm (z (e p.1, e p.2))) ∈ cocycles₂ A := by
  rw [mem_cocycles₂_iff]
  intro g h j
  have hb := (mem_cocycles₂_iff z).1 hz (e g) (e h) (e j)
  show φ.symm (z (e (g * h), e j)) + φ.symm (z (e g, e h))
    = A.ρ g (φ.symm (z (e h, e j))) + φ.symm (z (e g, e (h * j)))
  rw [map_mul, map_mul, ← symm_apply_rho e φ hφ, ← map_add, ← map_add, hb]

theorem h2TransportMap_bijective : Function.Bijective (h2TransportMap e φ hφ) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y
    induction y using H2_induction_on with
    | @h x =>
    intro hy
    rw [h2TransportMap_H2π, H2π_eq_zero_iff] at hy
    obtain ⟨v, hv⟩ := hy
    refine (H2π_eq_zero_iff x).2 ⟨fun g => φ.symm (v (e g)), funext fun p => ?_⟩
    have hvp := congrFun hv (e p.1, e p.2)
    rw [coe_mapCocycles₂_transport] at hvp
    simp only [MulEquiv.symm_apply_apply] at hvp
    rw [d₁₂_hom_apply] at hvp ⊢
    refine φ.injective ?_
    rw [← hvp, map_add, map_sub, hφ, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_mul]
  · intro y
    induction y using H2_induction_on with
    | @h z =>
    refine ⟨H2π A ⟨_, mem_cocycles₂_transport e φ hφ z.2⟩, ?_⟩
    rw [h2TransportMap_H2π]
    congr 1
    refine cocycles₂_ext fun q r => ?_
    rw [coe_mapCocycles₂_transport]
    show φ (φ.symm (z (e (e.symm q), e (e.symm r)))) = z (q, r)
    rw [LinearEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- **The second cohomology is transported along an isomorphism of groups compatible with a linear
isomorphism of the modules.** -/
def h2EquivOfMulEquiv : ↥(H2 A) ≃ ↥(H2 B) :=
  Equiv.ofBijective _ (h2TransportMap_bijective e φ hφ)

/-- **The second cohomology groups of two representations related by an isomorphism of the acting
groups and a compatible linear isomorphism of the modules have the same number of elements.** -/
theorem card_H2_eq_of_mulEquiv : Nat.card ↥(H2 A) = Nat.card ↥(H2 B) :=
  Nat.card_eq_of_bijective _ (h2TransportMap_bijective e φ hφ)

/-- Finiteness of the second cohomology is transported along an isomorphism of groups compatible
with a linear isomorphism of the modules. -/
theorem finite_H2_of_mulEquiv [Finite ↥(H2 B)] : Finite ↥(H2 A) :=
  Finite.of_injective _ (h2TransportMap_bijective e φ hφ).1

end Transport

section IntTransport

variable {H H' : Type} [Group H] [Group H'] {C : Rep ℤ H} {D : Rep ℤ H'}
  (e : H ≃* H') (φ : C ≃+ D)
  (hφ : ∀ (g : H) (c : C), φ (C.ρ g c) = D.ρ (e g) (φ c))

include hφ

/-- **The second cohomology groups of two representations over the integers related by an
isomorphism of the acting groups and a compatible additive isomorphism of the modules have the same
number of elements.** -/
theorem card_H2_eq_of_addEquiv : Nat.card ↥(H2 C) = Nat.card ↥(H2 D) :=
  card_H2_eq_of_mulEquiv e φ.toIntLinearEquiv hφ

/-- Finiteness of the second cohomology is transported along an isomorphism of groups compatible
with an additive isomorphism of the modules. -/
theorem finite_H2_of_addEquiv [Finite ↥(H2 D)] : Finite ↥(H2 C) :=
  finite_H2_of_mulEquiv e φ.toIntLinearEquiv hφ

/-- **A class annihilated only by the multiples of a number is transported along an isomorphism of
groups compatible with an additive isomorphism of the modules.**  The transport is additive and
injective, so it neither creates nor destroys an annihilating multiple. -/
theorem exists_zsmul_eq_zero_imp_dvd_H2_of_addEquiv {n : ℕ}
    (h : ∃ γ : ↥(H2 C), ∀ m : ℤ, m • γ = 0 → (n : ℤ) ∣ m) :
    ∃ γ : ↥(H2 D), ∀ m : ℤ, m • γ = 0 → (n : ℤ) ∣ m := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨h2TransportMap e φ.toIntLinearEquiv hφ γ, fun m hm => ?_⟩
  refine hγ m ((h2TransportMap_bijective e φ.toIntLinearEquiv hφ).1 ?_)
  rw [map_zsmul, hm, map_zero]

end IntTransport

end

end InverseGalois.CFT
