/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicBrauer
import InverseGalois.CFT.Brauer.CrossedProductRestrict
import InverseGalois.CFT.GroupCohomology.CyclicRestrict

/-!
# Base change of a cyclic algebra to an intermediate field

Let `L / K` be a finite cyclic Galois extension with generator `σ₀`, and let `M` be an intermediate
field such that `L / M` is again cyclic with generator `σ₁`.  Then `σ₁` induces the power `σ₀ ^ d`
on `L / K`, where `d` is the degree of `M / K`, and this is exactly the situation in which the
explicit cyclic two-cocycle pulls back to the explicit cyclic two-cocycle.

Since the restriction map on Brauer groups sends the class of a crossed product to the class of the
crossed product of the restricted cocycle, **base change carries the cyclic algebra `(L / K, σ₀, a)`
to the cyclic algebra `(L / M, σ₁, a)`**, with the *same* coefficient `a`, now read in `M`.  The
degree `d` has disappeared into the choice of generator, which is what makes the invariant of a
cyclic algebra multiply by `d` under restriction.

## Main definitions

* `InverseGalois.CFT.restrictScalarsHom`: restriction of scalars, as a homomorphism of Galois
  groups.

## Main results

* `InverseGalois.CFT.restrictCocycle_cyclicUnitCocycle`: the cyclic unit cocycle of `L / K`
  restricts to the cyclic unit cocycle of `L / M`.
* `InverseGalois.CFT.baseChangeHom_cyclicBrauerHom`: **base change sends a cyclic algebra to a
  cyclic algebra with the same coefficient.**

## Tags

Brauer group, cyclic algebra, base change, crossed product, class field theory
-/

universe u

open Module

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : Type u) [Field M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]

/-! ### Restriction of scalars as a homomorphism of Galois groups -/

variable (K) in
/-- Restriction of scalars from an intermediate field to the base field, as a homomorphism of
Galois groups. -/
def restrictScalarsHom : Gal(L/M) →* Gal(L/K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
variable (K) in
/-- Restriction of scalars, as a homomorphism, is restriction of scalars. -/
@[simp] theorem restrictScalarsHom_apply (σ : Gal(L/M)) :
    restrictScalarsHom K M σ = σ.restrictScalars K := rfl

/-! ### The restriction of the cyclic unit cocycle -/

variable [FiniteDimensional M L]

omit [IsGalois K L] in
/-- **The cyclic unit cocycle of `L / K` restricts to the cyclic unit cocycle of `L / M`.**  The
generator of `Gal(L/M)` induces the `d`-th power of the generator of `Gal(L/K)`, where `d` is the
ratio of the two orders, so the discrete logarithms scale by `d` and the comparison defining the
value of the cocycle is unchanged. -/
theorem restrictCocycle_cyclicUnitCocycle {σ₀ : Gal(L/K)} {σ₁ : Gal(L/M)}
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)
    (hσ₁ : ∀ x : Gal(L/M), x ∈ Subgroup.zpowers σ₁) {d : ℕ}
    (hpow : σ₁.restrictScalars K = σ₀ ^ d)
    (hcard : Nat.card Gal(L/K) = d * Nat.card Gal(L/M)) (a : Kˣ) :
    CrossedProduct.restrictCocycle M (cyclicUnitCocycle σ₀ a)
      = cyclicUnitCocycle σ₁ (Units.map (algebraMap K M).toMonoidHom a) := by
  funext p
  obtain ⟨σ, τ⟩ := p
  have hmap : Units.map (algebraMap M L).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom a)
      = Units.map (algebraMap K L).toMonoidHom a := by
    ext
    exact (IsScalarTower.algebraMap_apply K M L (a : K)).symm
  rw [CrossedProduct.restrictCocycle_apply, cyclicUnitCocycle, cyclicUnitCocycle, hmap]
  exact cyclicCocycle_map (restrictScalarsHom K M) hσ₀ hσ₁ hpow hcard _ σ τ

/-! ### Base change of a cyclic algebra -/

variable [IsGalois M L]

/-- **Base change sends a cyclic algebra to a cyclic algebra with the same coefficient.**  The
restriction map on Brauer groups is computed by restricting the defining cocycle, and the cyclic
cocycle of `L / K` restricts to the cyclic cocycle of `L / M`. -/
theorem baseChangeHom_cyclicBrauerHom {σ₀ : Gal(L/K)} {σ₁ : Gal(L/M)}
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)
    (hσ₁ : ∀ x : Gal(L/M), x ∈ Subgroup.zpowers σ₁) {d : ℕ}
    (hpow : σ₁.restrictScalars K = σ₀ ^ d)
    (hcard : Nat.card Gal(L/K) = d * Nat.card Gal(L/M)) (a : Kˣ) :
    BrauerGroup.baseChangeHom M (cyclicBrauerHom hσ₀ a)
      = cyclicBrauerHom hσ₁ (Units.map (algebraMap K M).toMonoidHom a) := by
  have hf' : IsMulCocycle₂ (CrossedProduct.restrictCocycle M (cyclicUnitCocycle σ₀ a)) :=
    CrossedProduct.isMulCocycle₂_restrictCocycle M (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)
  rw [cyclicBrauerHom_apply, CrossedProduct.baseChangeHom_mk_csa M
    (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) hf', cyclicBrauerHom_apply]
  exact CrossedProduct.mk_csa_congr _ _
    (restrictCocycle_cyclicUnitCocycle M hσ₀ hσ₁ hpow hcard a)

end InverseGalois.CFT
