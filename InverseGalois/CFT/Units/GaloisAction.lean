/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Surjection

/-!
# The Galois action on the units of a number field

An automorphism of a number field carries algebraic integers to algebraic integers and units to
units, and the group of units of the ring of integers is therefore a module over the Galois group.
The roots of unity form an invariant subgroup, recognised by the infinite places: a unit is a root
of unity exactly when it has absolute value one at every infinite place, and the Galois group
permutes the infinite places.

## Main definitions

* `InverseGalois.CFT.unitsMulEquiv`: the action of a field automorphism on the units of the ring of
  integers.
* `InverseGalois.CFT.unitsAutHom`: the same action, written additively.

## Main results

* `InverseGalois.CFT.unitsAutHom_pow_eq_one`: the additive action inherits the order of the
  automorphism.
* `InverseGalois.CFT.mem_torsion_unitsMulEquiv`: **the roots of unity are an invariant subgroup.**

## Tags

number field, unit group, torsion, Galois action, Herbrand quotient
-/

namespace InverseGalois.CFT

open NumberField NumberField.Units NumberField.InfinitePlace

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### The action on the units -/

/-- **The action of a field automorphism on the units of the ring of integers.** -/
noncomputable def unitsMulEquiv (σ : Gal(K/k)) : (𝓞 K)ˣ ≃* (𝓞 K)ˣ :=
  Units.mapEquiv (MulSemiringAction.toRingEquiv Gal(K/k) (𝓞 K) σ).toMulEquiv

@[simp]
theorem coe_unitsMulEquiv_apply (σ : Gal(K/k)) (u : (𝓞 K)ˣ) :
    ((unitsMulEquiv σ u : (𝓞 K)ˣ) : K) = σ (u : K) := rfl

/-- **The action of the Galois group on the units, written additively.** -/
noncomputable def unitsAutHom : Gal(K/k) →* (Additive (𝓞 K)ˣ ≃+ Additive (𝓞 K)ˣ) where
  toFun σ := MulEquiv.toAdditive (unitsMulEquiv σ)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem toMul_unitsAutHom_apply (σ : Gal(K/k)) (u : Additive (𝓞 K)ˣ) :
    (unitsAutHom σ u).toMul = unitsMulEquiv σ u.toMul := rfl

/-- **The additive action inherits the order of the automorphism.** -/
theorem unitsAutHom_pow_eq_one {σ : Gal(K/k)} {n : ℕ} (hσ : σ ^ n = 1) :
    (unitsAutHom σ) ^ n = 1 := by rw [← map_pow, hσ, map_one]

/-! ### The roots of unity -/

variable [NumberField K]

/-- **The roots of unity are an invariant subgroup of the units.** -/
theorem mem_torsion_unitsMulEquiv {σ : Gal(K/k)} {u : (𝓞 K)ˣ} :
    unitsMulEquiv σ u ∈ torsion K ↔ u ∈ torsion K := by
  simp only [NumberField.Units.mem_torsion]
  refine ⟨fun h w => ?_, fun h w => ?_⟩
  · simpa using h (σ • w)
  · simpa using h (σ⁻¹ • w)

end InverseGalois.CFT
