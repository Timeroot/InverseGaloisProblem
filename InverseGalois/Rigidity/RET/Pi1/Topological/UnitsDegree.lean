/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleGroup
import InverseGalois.Rigidity.RET.Pi1.Topological.GroupLoop

/-!
# The degree of the power map of the punctured plane

The fundamental group of `ℂˣ` is infinite cyclic (`Complex.fundamentalGroupUnits`), and the
multiplication of `ℂˣ` is continuous, so the general computation of `GroupLoop.lean` applies: the
`n`-th power map of `ℂˣ` raises a loop to its `n`-th power, hence multiplies the winding number by
`n`.  This is the local degree computation underlying every comparison between a cover and its
pullback along a Kummer coordinate `w ↦ wⁿ`: a loop winding once around the puncture of the source
winds `n` times around the puncture of the target.

## Main results

* `Complex.expUnit_eq_one` — the basepoint of the computation of `π₁(ℂˣ)` is the unit.
* `Complex.fundamentalGroupUnitsOne` — `π₁(ℂˣ, 1) ≅ ℤ`.
* `Complex.windingNumber_npowMap` — the `n`-th power map multiplies the winding number by `n`.
-/

open Rigidity.RET

noncomputable section

namespace Complex

/-- The homeomorphism between the units and the nonzero elements is the coercion. -/
theorem coe_unitsHomeomorphNeZero (u : ℂˣ) :
    ((unitsHomeomorphNeZero u : {g : ℂ // g ≠ 0}) : ℂ) = (u : ℂ) := rfl

/-- The inverse of the homeomorphism between the units and the nonzero elements is the coercion. -/
theorem coe_unitsHomeomorphNeZero_symm (y : {g : ℂ // g ≠ 0}) :
    ((unitsHomeomorphNeZero.symm y : ℂˣ) : ℂ) = (y : ℂ) := by
  conv_rhs => rw [← Homeomorph.apply_symm_apply unitsHomeomorphNeZero y]
  exact (coe_unitsHomeomorphNeZero _).symm

/-- The basepoint at which `π₁(ℂˣ)` was computed is the unit of `ℂˣ`. -/
theorem expUnit_eq_one : expUnit = (1 : ℂˣ) :=
  Units.ext (by rw [expUnit, coe_unitsHomeomorphNeZero_symm]; simp)

/-- **The fundamental group of `ℂˣ` at the unit is `ℤ`.** -/
def fundamentalGroupUnitsOne : FundamentalGroup ℂˣ (1 : ℂˣ) ≃* Multiplicative ℤ :=
  expUnit_eq_one ▸ fundamentalGroupUnits

/-- **The `n`-th power map of `ℂˣ` raises a loop at the unit to its `n`-th power.** -/
theorem mapOfEq_npowMap_units (n : ℕ) (γ : FundamentalGroup ℂˣ (1 : ℂˣ)) :
    FundamentalGroup.mapOfEq (npowMap ℂˣ n) (one_pow n) γ = γ ^ n :=
  mapOfEq_npowMap n γ

/-- **The `n`-th power map of the punctured plane multiplies the winding number by `n`.** -/
theorem windingNumber_npowMap (n : ℕ) (γ : FundamentalGroup ℂˣ (1 : ℂˣ)) :
    Multiplicative.toAdd (fundamentalGroupUnitsOne
        (FundamentalGroup.mapOfEq (npowMap ℂˣ n) (one_pow n) γ))
      = n * Multiplicative.toAdd (fundamentalGroupUnitsOne γ) := by
  rw [mapOfEq_npowMap_units, map_pow]
  simp

end Complex

end
