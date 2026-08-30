/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicBrauer
import InverseGalois.CFT.Brauer.CrossedProductCompositum
import InverseGalois.CFT.GroupCohomology.CyclicRestrict

/-!
# Base change of a cyclic algebra along a field that is not intermediate

Let `E / K` be a finite cyclic Galois extension with generator `σ₀`, let `M / K` be another
extension, and let `N` be a field containing both `E` and `M`, Galois over `M`, whose Galois group
is carried onto `Gal(E/K)` by a multiplicative bijection compatible with the embedding of `E`.
When the generator `σ₁` of `Gal(N/M)` is carried to `σ₀`, the two Galois groups have the same order
and the bijection preserves discrete logarithms, so the explicit cyclic two-cocycle of `E / K`
transports to the explicit cyclic two-cocycle of `N / M` with the same coefficient.

Consequently **base change carries the cyclic algebra `(E / K, σ₀, a)` to the cyclic algebra
`(N / M, σ₁, a)`**, with the same coefficient `a`, now read in `M`.  Unlike the case of an
intermediate field, no power of the generator appears: the whole of the change of invariant is
carried by the change of valuation from `K` to `M`.

## Main results

* `InverseGalois.CFT.compositumCocycle_cyclicUnitCocycle`: the cyclic unit cocycle of `E / K`
  transports to the cyclic unit cocycle of `N / M`.
* `InverseGalois.CFT.baseChangeHom_cyclicBrauerHom_compositum`: **base change along a field that is
  not intermediate sends a cyclic algebra to a cyclic algebra with the same coefficient.**

## Tags

Brauer group, cyclic algebra, base change, compositum, crossed product, class field theory
-/

universe u

open Module

namespace InverseGalois.CFT

open groupCohomology

variable {K E M N : Type u} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
variable [Field M] [Field N] [Algebra M N] [Algebra E N] [FiniteDimensional M N] [IsGalois M N]
variable [Algebra K M] [Algebra K N] [IsScalarTower K M N] [IsScalarTower K E N]
variable {e : Gal(N/M) ≃* Gal(E/K)}

/-! ### The transport of the cyclic unit cocycle -/

omit [IsGalois K E] [IsGalois M N] in
/-- **The cyclic unit cocycle of `E / K` transports to the cyclic unit cocycle of `N / M`.**  The
bijection of Galois groups carries the generator to the generator, so it preserves discrete
logarithms, and the two orders agree, so the comparison defining the value of the cocycle is
unchanged. -/
theorem compositumCocycle_cyclicUnitCocycle {σ₀ : Gal(E/K)} {σ₁ : Gal(N/M)}
    (hσ₀ : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers σ₀)
    (hσ₁ : ∀ x : Gal(N/M), x ∈ Subgroup.zpowers σ₁) (hgen : e σ₁ = σ₀) (a : Kˣ) :
    CrossedProduct.compositumCocycle e (cyclicUnitCocycle σ₀ a)
      = cyclicUnitCocycle σ₁ (Units.map (algebraMap K M).toMonoidHom a) := by
  have hcard : Nat.card Gal(E/K) = 1 * Nat.card Gal(N/M) := by
    rw [one_mul]
    exact (Nat.card_congr e.toEquiv).symm
  have hpow : e.toMonoidHom σ₁ = σ₀ ^ 1 := by
    rw [pow_one]
    exact hgen
  have hmap : Units.map (algebraMap E N).toMonoidHom (Units.map (algebraMap K E).toMonoidHom a)
      = Units.map (algebraMap M N).toMonoidHom (Units.map (algebraMap K M).toMonoidHom a) := by
    ext
    show algebraMap E N (algebraMap K E (a : K)) = algebraMap M N (algebraMap K M (a : K))
    rw [← IsScalarTower.algebraMap_apply K E N, ← IsScalarTower.algebraMap_apply K M N]
  funext p
  obtain ⟨σ, τ⟩ := p
  have hkey : cyclicCocycle σ₀ (Units.map (algebraMap K E).toMonoidHom a) (e σ, e τ)
      = cyclicCocycle σ₁ (Units.map (algebraMap K E).toMonoidHom a) (σ, τ) :=
    cyclicCocycle_map e.toMonoidHom hσ₀ hσ₁ hpow hcard _ σ τ
  rw [CrossedProduct.compositumCocycle_apply, cyclicUnitCocycle, cyclicUnitCocycle, hkey, ← hmap]
  simp only [cyclicCocycle]
  split
  · exact map_one _
  · rfl

/-! ### Base change of a cyclic algebra -/

/-- **Base change along a field that is not intermediate sends a cyclic algebra to a cyclic algebra
with the same coefficient.**  Extending scalars sends the class of a cocycle to the class of its
transport, and the cyclic cocycle of `E / K` transports to the cyclic cocycle of `N / M`. -/
theorem baseChangeHom_cyclicBrauerHom_compositum {σ₀ : Gal(E/K)} {σ₁ : Gal(N/M)}
    (hσ₀ : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers σ₀)
    (hσ₁ : ∀ x : Gal(N/M), x ∈ Subgroup.zpowers σ₁) (hgen : e σ₁ = σ₀)
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x)) (a : Kˣ) :
    BrauerGroup.baseChangeHom M (cyclicBrauerHom hσ₀ a)
      = cyclicBrauerHom hσ₁ (Units.map (algebraMap K M).toMonoidHom a) := by
  have hf' : IsMulCocycle₂ (CrossedProduct.compositumCocycle e (cyclicUnitCocycle σ₀ a)) :=
    CrossedProduct.isMulCocycle₂_compositumCocycle he (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)
  rw [cyclicBrauerHom_apply, CrossedProduct.baseChangeHom_mk_csa_compositum
    (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) hf' he, cyclicBrauerHom_apply]
  exact CrossedProduct.mk_csa_congr _ _
    (compositumCocycle_cyclicUnitCocycle hσ₀ hσ₁ hgen a)

end InverseGalois.CFT
