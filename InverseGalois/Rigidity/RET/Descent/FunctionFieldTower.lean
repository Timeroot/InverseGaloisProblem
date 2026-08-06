/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Function-field tower `ℚ(T) → ℚ̄(T)` for the descent

Establishes `RatFunc (AlgebraicClosure ℚ)` as a `RatFunc ℚ`-algebra, a scalar tower over ℚ, and
algebraic (indeed integral) over `RatFunc ℚ`.  Analogue of the `FractionRing`-model tower in
`RET.GeometricIrreducibility`, but for the `RatFunc` model used by `IsGeometricGaloisCover`.
-/

open Polynomial

open scoped nonZeroDivisors

namespace Rigidity.RET.Descent

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

attribute [local instance] Polynomial.algebra

/-- The coefficient-extension ring hom `ℚ[X] → ℚ̄[X]` sends nonzerodivisors to nonzerodivisors:
this is the side condition needed to lift it to rational functions with `RatFunc.mapRingHom`.
It holds because `Polynomial.map` of the injective `ℚ → ℚ̄` is injective between domains. -/
theorem hφmono :
    (ℚ[X])⁰ ≤ (AlgebraicClosure ℚ)[X]⁰.comap
      (Polynomial.mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective ℚ (AlgebraicClosure ℚ)))

/-- The base-change ring hom `ℚ(T) → ℚ̄(T)`: extend the coefficients of numerator and denominator
along `ℚ → ℚ̄`. -/
noncomputable def toClosureRatFunc : RatFunc ℚ →+* RatFunc (AlgebraicClosure ℚ) :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))) hφmono

/-- `ℚ̄(T)` is a `ℚ(T)`-algebra, via `toClosureRatFunc`. -/
noncomputable instance instAlgRatFuncClosure :
    Algebra (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
  toClosureRatFunc.toAlgebra

/-- The structure map `ℚ(T) → ℚ̄(T)` restricted to `ℚ[T]` extends coefficients along `ℚ → ℚ̄`. -/
theorem algebraMap_ratFunc_closure_comp (p : ℚ[X]) :
    algebraMap (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) (algebraMap ℚ[X] (RatFunc ℚ) p)
      = algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ))
          (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)) p) := by
  rw [RingHom.algebraMap_toAlgebra]
  show toClosureRatFunc (algebraMap ℚ[X] (RatFunc ℚ) p) = _
  rw [toClosureRatFunc]
  rw [show algebraMap ℚ[X] (RatFunc ℚ) p
        = algebraMap ℚ[X] (RatFunc ℚ) p / algebraMap ℚ[X] (RatFunc ℚ) 1 by
    rw [map_one, div_one]]
  rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
  simp [Polynomial.coe_mapRingHom]

/-- `ℚ[T] → ℚ(T) → ℚ̄(T)` is a scalar tower. -/
instance instTowerRatFuncClosure :
    IsScalarTower ℚ[X] (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [algebraMap_ratFunc_closure_comp,
    IsScalarTower.algebraMap_apply ℚ[X] (AlgebraicClosure ℚ)[X]
      (RatFunc (AlgebraicClosure ℚ))]
  rfl

/-- `ℚ → ℚ(T) → ℚ̄(T)` is a scalar tower.

The `letI`s pin `Algebra ℚ (RatFunc _)` to the `RatFunc`-model instance
(`RatFunc.instAlgebraOfPolynomial`), whose scalar action is the one appearing in the goal.
Without this, `Algebra ℚ (RatFunc ℚ)` synthesizes to the generic `DivisionRing.toRatAlgebra`,
whose `SMul` is not defeq to the `RatFunc` one (the standard ℚ-algebra diamond), and
`IsScalarTower.of_algebraMap_eq` fails to unify. -/
instance instTowerℚRatFuncClosure :
    IsScalarTower ℚ (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) := by
  letI aQ : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial (K := ℚ) (R := ℚ)
  letI aQbar : Algebra ℚ (RatFunc (AlgebraicClosure ℚ)) :=
    RatFunc.instAlgebraOfPolynomial (K := AlgebraicClosure ℚ) (R := ℚ)
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ),
    algebraMap_ratFunc_closure_comp,
    IsScalarTower.algebraMap_apply ℚ (AlgebraicClosure ℚ)[X]
      (RatFunc (AlgebraicClosure ℚ))]
  congr 1
  simp [Polynomial.algebraMap_eq, IsScalarTower.algebraMap_apply ℚ (AlgebraicClosure ℚ)
    (AlgebraicClosure ℚ)[X]]

/-- `ℚ̄(T)` is algebraic over `ℚ(T)`: it is the fraction field of `ℚ̄[T]`, which is integral over
`ℚ[T]` (coefficients algebraic over `ℚ`). -/
theorem isAlgebraic_ratFunc_closure :
    Algebra.IsAlgebraic (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) := by
  letI := Polynomial.algebra (R := ℚ) (A := AlgebraicClosure ℚ)
  exact isAlgebraic_of_isFractionRing (R := ℚ[X]) (S := (AlgebraicClosure ℚ)[X])
    (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ))

end Rigidity.RET.Descent
