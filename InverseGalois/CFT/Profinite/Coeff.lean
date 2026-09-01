/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Cochain

/-!
# Functoriality of the cohomology of a topological group in the coefficients

A homomorphism of the coefficients commuting with the two actions carries a cochain to a cochain
by composition.  It preserves the cocycle conditions, because those are equations built from the
group law and the action, and it preserves smoothness, because a cochain constant on the cosets of
an open normal subgroup stays constant there.  A coboundary goes to the coboundary of the image of
its primitive, so the construction descends to cohomology in degrees one and two.

## Main definitions

* `InverseGalois.CFT.coeffMap₁`, `InverseGalois.CFT.coeffMap₂`: composing a cochain with a
  homomorphism of the coefficients.
* `InverseGalois.CFT.coeffH1`, `InverseGalois.CFT.coeffH2`: **the induced maps in cohomology.**

## Main results

* `InverseGalois.CFT.isMulCocycle₁_coeffMap₁`, `InverseGalois.CFT.isMulCocycle₂_coeffMap₂`: an
  equivariant homomorphism of the coefficients carries cocycles to cocycles.
* `InverseGalois.CFT.coboundary₂_coeffMap₁`: it commutes with the coboundary.
* `InverseGalois.CFT.coeffH1_smoothH1Mk`, `InverseGalois.CFT.coeffH2_smoothH2Mk`: the maps in
  cohomology are computed on cocycles.

## Tags

profinite group, Galois cohomology, smooth cochain, cocycle, coboundary, functoriality
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### Composing a cochain with a homomorphism of the coefficients -/

section Defs

variable {G M N : Type*} [Group G] [CommGroup M] [CommGroup N]

/-- Composing a one cochain with a homomorphism of the coefficients. -/
def coeffMap₁ (φ : M →* N) (u : G → M) : G → N := fun g => φ (u g)

/-- Composing a two cochain with a homomorphism of the coefficients. -/
def coeffMap₂ (φ : M →* N) (a : G × G → M) : G × G → N := fun p => φ (a p)

omit [Group G] in
@[simp]
theorem coeffMap₁_apply (φ : M →* N) (u : G → M) (g : G) : coeffMap₁ φ u g = φ (u g) := rfl

omit [Group G] in
@[simp]
theorem coeffMap₂_apply (φ : M →* N) (a : G × G → M) (p : G × G) :
    coeffMap₂ φ a p = φ (a p) := rfl

end Defs

/-! ### Smoothness -/

section Smooth

variable {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N] (φ : M →* N)

/-- The image of a smooth one cochain is smooth. -/
theorem IsSmooth₁.coeffMap₁ {u : G → M} (hu : IsSmooth₁ u) : IsSmooth₁ (coeffMap₁ φ u) := by
  obtain ⟨N', hN', h⟩ := hu
  exact ⟨N', hN', fun x n hn => congrArg φ (h x n hn)⟩

/-- The image of a smooth two cochain is smooth. -/
theorem IsSmooth₂.coeffMap₂ {a : G × G → M} (ha : IsSmooth₂ a) : IsSmooth₂ (coeffMap₂ φ a) := by
  obtain ⟨N', hN', h⟩ := ha
  exact ⟨N', hN', fun x y n hn m hm => congrArg φ (h x y n hn m hm)⟩

end Smooth

/-! ### Cocycles and coboundaries -/

section Cocycle

variable {G M N : Type*} [Group G] [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N] (φ : M →* N) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)

include hφ

/-- An equivariant homomorphism of the coefficients carries a one cocycle to a one cocycle. -/
theorem isMulCocycle₁_coeffMap₁ {u : G → M} (hu : IsMulCocycle₁ u) :
    IsMulCocycle₁ (coeffMap₁ φ u) := by
  intro g h
  simp only [coeffMap₁_apply, hu g h, map_mul, hφ]

/-- An equivariant homomorphism of the coefficients carries a two cocycle to a two cocycle. -/
theorem isMulCocycle₂_coeffMap₂ {a : G × G → M} (ha : IsMulCocycle₂ a) :
    IsMulCocycle₂ (coeffMap₂ φ a) := by
  intro g h j
  show φ (a (g * h, j)) * φ (a (g, h)) = g • φ (a (h, j)) * φ (a (g, h * j))
  rw [← map_mul, ha g h j, map_mul, hφ]

/-- An equivariant homomorphism of the coefficients commutes with the coboundary. -/
theorem coboundary₂_coeffMap₁ (u : G → M) :
    coboundary₂ (coeffMap₁ φ u) = coeffMap₂ φ (coboundary₂ u) := by
  ext p
  simp only [coboundary₂, coeffMap₁_apply, coeffMap₂_apply, map_mul, map_div, hφ]

/-- An equivariant homomorphism of the coefficients carries the coboundary of an element to the
coboundary of its image. -/
theorem coeffMap₁_smul_div (t : M) :
    coeffMap₁ (G := G) φ (fun g : G => g • t / t) = fun g : G => g • φ t / φ t := by
  ext g
  simp only [coeffMap₁_apply, map_div, hφ]

end Cocycle

/-! ### The maps in cohomology -/

section Cohomology

variable {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N] (φ : M →* N)
  (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)

include hφ

/-- An equivariant homomorphism of the coefficients, on one cocycles. -/
def coeffCocycle₁ : smoothCocycle₁ G M →* smoothCocycle₁ G N where
  toFun u := ⟨coeffMap₁ φ u.1, isMulCocycle₁_coeffMap₁ φ hφ u.2.1, u.2.2.coeffMap₁ φ⟩
  map_one' := Subtype.ext (funext fun _ => map_one φ)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul φ _ _)

/-- An equivariant homomorphism of the coefficients, on two cocycles. -/
def coeffCocycle₂ : smoothCocycle₂ G M →* smoothCocycle₂ G N where
  toFun a := ⟨coeffMap₂ φ a.1, isMulCocycle₂_coeffMap₂ φ hφ a.2.1, a.2.2.coeffMap₂ φ⟩
  map_one' := Subtype.ext (funext fun _ => map_one φ)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul φ _ _)

/-- **The map in the first cohomology induced by an equivariant homomorphism of the
coefficients.** -/
def coeffH1 : SmoothH1 G M →* SmoothH1 G N :=
  QuotientGroup.map _ _ (coeffCocycle₁ φ hφ) <| by
    rintro ⟨u, hu, hus⟩ ⟨t, rfl⟩
    exact Subgroup.mem_comap.2 ⟨φ t, (coeffMap₁_smul_div φ hφ t).symm⟩

/-- **The map in the second cohomology induced by an equivariant homomorphism of the
coefficients.** -/
def coeffH2 : SmoothH2 G M →* SmoothH2 G N :=
  QuotientGroup.map _ _ (coeffCocycle₂ φ hφ) <| by
    rintro ⟨a, ha, has⟩ ⟨u, hu, rfl⟩
    exact Subgroup.mem_comap.2
      ⟨coeffMap₁ φ u, hu.coeffMap₁ φ, coboundary₂_coeffMap₁ φ hφ u⟩

/-- **The map in cohomology is computed on cocycles.** -/
theorem coeffH1_smoothH1Mk {u : G → M} (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u) :
    coeffH1 φ hφ (smoothH1Mk u hu hs)
      = smoothH1Mk (coeffMap₁ φ u) (isMulCocycle₁_coeffMap₁ φ hφ hu) (hs.coeffMap₁ φ) := rfl

/-- **The map in cohomology is computed on cocycles.** -/
theorem coeffH2_smoothH2Mk {a : G × G → M} (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a) :
    coeffH2 φ hφ (smoothH2Mk a ha hs)
      = smoothH2Mk (coeffMap₂ φ a) (isMulCocycle₂_coeffMap₂ φ hφ ha) (hs.coeffMap₂ φ) := rfl

end Cohomology

end InverseGalois.CFT
