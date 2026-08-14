/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.EtaleDerivation

/-!
# Differentiating the functions of a cover of the line

The coordinate of the line differentiates the functions of the line, and that differentiation
carries over to any cover of the line in exactly one way, because a cover of the line in
characteristic zero is separable, hence unramified as an extension of fields.  What results is a
derivation of the function field of the cover, over the constants, sending the coordinate to one.

Everything downstream uses only that one property.  A derivation sending the coordinate to one
preserves the polynomials in the coordinate, hence — once the cover is unbranched — also the
functions integral over them; and the derivation attached to the coordinate at the other end of
the line is obtained from it by multiplying by the square of the coordinate, so the same statement
holds at that end too.

## Main definitions

* `Rigidity.RET.ratFuncDeriv` — differentiation of rational functions in one variable.
* `Rigidity.RET.coord` — the coordinate of the line, read in the cover.
* `Rigidity.RET.lineDeriv` — differentiation along the coordinate, on the cover.

## Main results

* `Rigidity.RET.lineDeriv_coord` — the derivation sends the coordinate to one.
* `Rigidity.RET.transcendental_coord` — the coordinate is transcendental over the constants.
* `Rigidity.RET.deriv_mem_adjoin` — a derivation preserves the polynomials in an element it sends
  into those polynomials.
-/

noncomputable section

namespace Rigidity.RET

/-! ## Differentiating rational functions -/

section RatFuncDeriv

variable (k : Type*) [Field k]

local instance formallyEtale_polynomial_ratFunc :
    Algebra.FormallyEtale (Polynomial k) (RatFunc k) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Polynomial k))

/-- **Differentiation of rational functions**, obtained from differentiation of polynomials by
the fact that a field of fractions is unramified over the ring it is built from. -/
def ratFuncDeriv : Derivation k (RatFunc k) (RatFunc k) :=
  etaleLift k (Polynomial k) (RatFunc k) Polynomial.derivative'

@[simp]
theorem ratFuncDeriv_algebraMap (p : Polynomial k) :
    ratFuncDeriv k (algebraMap (Polynomial k) (RatFunc k) p)
      = algebraMap (Polynomial k) (RatFunc k) (Polynomial.derivative p) :=
  etaleLift_algebraMap _ p

@[simp]
theorem ratFuncDeriv_X : ratFuncDeriv k (RatFunc.X : RatFunc k) = 1 := by
  rw [← RatFunc.algebraMap_X, ratFuncDeriv_algebraMap]
  simp

end RatFuncDeriv

/-! ## Differentiating along the coordinate of the line -/

section LineDeriv

variable (k F : Type*) [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [Algebra.IsAlgebraic (RatFunc k) F]

attribute [local instance] Algebra.FormallyEtale.of_isSeparable

/-- **The coordinate of the line, read in the cover.** -/
def coord : F := algebraMap (RatFunc k) F RatFunc.X

/-- **Differentiation along the coordinate of the line**, on the functions of a cover. -/
def lineDeriv : Derivation k F F := etaleLift k (RatFunc k) F (ratFuncDeriv k)

@[simp]
theorem lineDeriv_algebraMap (f : RatFunc k) :
    lineDeriv k F (algebraMap (RatFunc k) F f) = algebraMap (RatFunc k) F (ratFuncDeriv k f) :=
  etaleLift_algebraMap _ f

/-- **Differentiation sends the coordinate to one.** -/
@[simp]
theorem lineDeriv_coord : lineDeriv k F (coord k F) = 1 := by
  rw [coord, lineDeriv_algebraMap, ratFuncDeriv_X, map_one]

omit [CharZero k] [Algebra.IsAlgebraic (RatFunc k) F] in
/-- **The coordinate is transcendental over the constants.** -/
theorem transcendental_coord : Transcendental k (coord k F) := by
  have hinj : Function.Injective (algebraMap (RatFunc k) F) :=
    (algebraMap (RatFunc k) F).injective
  exact (transcendental_algebraMap_iff (R := k) hinj).mpr RatFunc.transcendental_X

omit [CharZero k] [Algebra.IsAlgebraic (RatFunc k) F] in
/-- **The coordinate does not vanish.** -/
theorem coord_ne_zero : coord k F ≠ 0 := fun h => transcendental_coord k F (h ▸ isAlgebraic_zero)

end LineDeriv

/-! ## A derivation preserves the polynomials in an element it does not leave -/

section Adjoin

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **A derivation preserves the polynomials in an element, provided it sends that element to a
polynomial in it.** -/
theorem deriv_mem_adjoin {D : Derivation k F F} {t : F} (ht : D t ∈ Algebra.adjoin k {t})
    {y : F} (hy : y ∈ Algebra.adjoin k {t}) : D y ∈ Algebra.adjoin k {t} := by
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff] at hz
    exact hz ▸ ht
  | algebraMap c => simp [D.map_algebraMap c]
  | add z w _ _ hz hw => simpa using add_mem hz hw
  | mul z w hz' hw' hz hw =>
    rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hz' hw) (mul_mem hw' hz)

end Adjoin

end Rigidity.RET
