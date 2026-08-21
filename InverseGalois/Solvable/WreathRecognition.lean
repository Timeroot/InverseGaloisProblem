/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Solvable.Wreath

/-!
# Recognizing a regular wreath product from coordinates

A group `G` equipped with a homomorphism `π : G → H` and a family of "coordinates"
`a h : G → A`, one for each `h : H`, is a wreath product as soon as the coordinates satisfy the
cocycle identity

`a h (σ τ) = a (π τ * h) σ * a h τ`

that governs how `σ` permutes the coordinates.  This is the identity that arises when `A` acts on
`|H|` conjugate layers of a field extension and `σ` moves the layer `h` to the layer `π σ * h`: the
coordinate of a product is the coordinate of `τ` at `h` corrected by the coordinate of `σ` at the
layer that `τ` has already moved `h` to.

Matching it to the multiplication of `RegularWreathProduct`, which is
`(w * v).left x = w.left x * v.left (w.right⁻¹ * x)`, requires the coordinates to be read off in
the shifted order `x ↦ a ((π σ)⁻¹ * x) σ`; that shift is built into `coordHom`.  Two further
ingredients turn the resulting homomorphism into an isomorphism: a criterion for injectivity,
which in the intended application says that an automorphism fixing the base and every layer is
trivial, and a count, which says that `G` has as many elements as `A ≀ᵣ H`.

Nothing here mentions fields; this is the purely group-theoretic half of the recognition step.

## Main results

* `RegularWreathProduct.coordHom` — the homomorphism `G →* A ≀ᵣ H` built from a cocycle of
  coordinates.
* `RegularWreathProduct.coordHom_injective` — it is injective as soon as the only element of `G`
  with trivial image and trivial coordinates is the identity.
* `RegularWreathProduct.mulEquiv_of_injective_of_card` — an injective homomorphism to `A ≀ᵣ H` out
  of a group of the right order is an isomorphism.
-/

namespace RegularWreathProduct

variable {G A H : Type*} [Group G] [CommGroup A] [Group H]

/-- **Coordinates satisfying the wreath cocycle identity assemble into a homomorphism.**  The
coordinate at `x` of the image of `σ` is the coordinate of `σ` at the layer that `σ` moves to `x`,
which is the shift the multiplication of `RegularWreathProduct` expects. -/
def coordHom (π : G →* H) (a : H → G → A)
    (hcocycle : ∀ (h : H) (σ τ : G), a h (σ * τ) = a (π τ * h) σ * a h τ)
    (hone : ∀ h, a h 1 = 1) : G →* A ≀ᵣ H where
  toFun σ := ⟨fun x ↦ a ((π σ)⁻¹ * x) σ, π σ⟩
  map_one' := by
    refine RegularWreathProduct.ext (funext fun x ↦ ?_) (map_one π)
    show a ((π 1)⁻¹ * x) 1 = 1
    rw [hone]
  map_mul' σ τ := by
    refine RegularWreathProduct.ext (funext fun x ↦ ?_) (map_mul π σ τ)
    show a ((π (σ * τ))⁻¹ * x) (σ * τ) = a ((π σ)⁻¹ * x) σ * a ((π τ)⁻¹ * ((π σ)⁻¹ * x)) τ
    rw [hcocycle]
    congr 2
    · rw [map_mul, mul_inv_rev]
      group
    · rw [map_mul, mul_inv_rev]
      group

@[simp]
theorem coordHom_left (π : G →* H) (a : H → G → A) (hcocycle) (hone) (σ : G) :
    (coordHom π a hcocycle hone σ).left = fun x ↦ a ((π σ)⁻¹ * x) σ := rfl

@[simp]
theorem coordHom_right (π : G →* H) (a : H → G → A) (hcocycle) (hone) (σ : G) :
    (coordHom π a hcocycle hone σ).right = π σ := rfl

/-- **The coordinate homomorphism is injective** as soon as an element that is trivial on the base
and has all its coordinates trivial is itself trivial. -/
theorem coordHom_injective (π : G →* H) (a : H → G → A)
    (hcocycle : ∀ (h : H) (σ τ : G), a h (σ * τ) = a (π τ * h) σ * a h τ)
    (hone : ∀ h, a h 1 = 1)
    (hker : ∀ σ : G, π σ = 1 → (∀ h, a h σ = 1) → σ = 1) :
    Function.Injective (coordHom π a hcocycle hone) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hright : π σ = 1 := congrArg RegularWreathProduct.right hσ
  refine hker σ hright fun h ↦ ?_
  have hleft := congrFun (congrArg RegularWreathProduct.left hσ) h
  rw [coordHom_left, hright] at hleft
  simpa using hleft

/-- **An injective homomorphism into a wreath product out of a group of the right order is an
isomorphism.**  The order of `A ≀ᵣ H` is `|A| ^ |H| * |H|`. -/
theorem mulEquiv_of_injective_of_card [Finite G] [Finite A] [Finite H] (Ψ : G →* A ≀ᵣ H)
    (hinj : Function.Injective Ψ)
    (hcard : Nat.card G = Nat.card A ^ Nat.card H * Nat.card H) :
    Nonempty (G ≃* A ≀ᵣ H) := by
  have hc : Nat.card G = Nat.card (A ≀ᵣ H) := by rw [hcard, RegularWreathProduct.card]
  have hbij : Function.Bijective Ψ := (Nat.bijective_iff_injective_and_card Ψ).2 ⟨hinj, hc⟩
  exact ⟨MulEquiv.ofBijective Ψ hbij⟩

end RegularWreathProduct
