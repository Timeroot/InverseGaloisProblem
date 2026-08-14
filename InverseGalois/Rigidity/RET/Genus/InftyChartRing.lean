/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.ChartIntegral

/-!
# The far chart of the line is a polynomial ring

The functions regular at the far end of the line are the polynomials in the inverse coordinate, and
the inverse coordinate is transcendental over the constants, so that chart is again a polynomial
ring: it is a principal ideal domain, hence a Dedekind domain, and its fraction field is the whole
field of rational functions.  The last point is the only one with content, and it is the statement
that the two charts cover the line: a rational function is a ratio of two polynomials, and dividing
both by a large enough power of the coordinate turns them into functions regular at the far end
without changing their ratio.

## Main results

* `Rigidity.RET.inftyChartEquiv` — the far chart is a polynomial ring in the inverse coordinate.
* `Rigidity.RET.instIsPrincipalIdealRingInftyChart` — the far chart is a principal ideal domain.
* `Rigidity.RET.instIsFractionRingInftyChart` — its fraction field is the rational functions.
-/

open Polynomial nonZeroDivisors

noncomputable section


namespace Rigidity.RET

section InftyChart

variable (k : Type*) [Field k]

/-- **The inverse coordinate is transcendental over the constants.** -/
theorem transcendental_inv_coord : Transcendental k (RatFunc.X : RatFunc k)⁻¹ := fun h =>
  RatFunc.transcendental_X (K := k) (IsAlgebraic.inv_iff.mp h)

/-- **The far chart is a polynomial ring in the inverse coordinate**, that element being
transcendental over the constants. -/
def inftyChartEquiv : k[X] ≃ₐ[k] ↥(inftyChart k) :=
  (AlgEquiv.ofInjective (Polynomial.aeval ((RatFunc.X : RatFunc k)⁻¹) : k[X] →ₐ[k] RatFunc k)
      (transcendental_iff_injective.1 (transcendental_inv_coord k))).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k _).symm)

/-- The far chart is a principal ideal domain, being a polynomial ring. -/
instance instIsPrincipalIdealRingInftyChart : IsPrincipalIdealRing ↥(inftyChart k) :=
  IsPrincipalIdealRing.of_surjective (inftyChartEquiv k).toRingEquiv
    (inftyChartEquiv k).surjective

/-- **The rational functions are the fraction field of the far chart.**  A rational function is a
ratio of two polynomials, and dividing numerator and denominator by a power of the coordinate
exceeding both their degrees makes both regular at the far end. -/
instance instIsFractionRingInftyChart : IsFractionRing ↥(inftyChart k) (RatFunc k) := by
  refine ⟨⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩⟩
  · refine isUnit_iff_ne_zero.2 fun h => ?_
    exact (mem_nonZeroDivisors_iff_ne_zero.1 y.2) (Subtype.ext h)
  · have hd0 : algebraMap k[X] (RatFunc k) z.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).2 (RatFunc.denom_ne_zero z)
    have hzd : algebraMap k[X] (RatFunc k) z.num = z * algebraMap k[X] (RatFunc k) z.denom :=
      (div_eq_iff hd0).1 (RatFunc.num_div_denom z)
    set N := max z.num.natDegree z.denom.natDegree with hN
    have hmemn : (RatFunc.X : RatFunc k)⁻¹ ^ N * algebraMap k[X] (RatFunc k) z.num ∈ inftyChart k :=
      inv_pow_mul_algebraMap_mem_inftyChart k (le_max_left _ _)
    have hmemd :
        (RatFunc.X : RatFunc k)⁻¹ ^ N * algebraMap k[X] (RatFunc k) z.denom ∈ inftyChart k :=
      inv_pow_mul_algebraMap_mem_inftyChart k (le_max_right _ _)
    have hX0 : ((RatFunc.X : RatFunc k)⁻¹) ^ N ≠ 0 :=
      pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero)
    have hne : (RatFunc.X : RatFunc k)⁻¹ ^ N * algebraMap k[X] (RatFunc k) z.denom ≠ 0 :=
      mul_ne_zero hX0 hd0
    refine ⟨(⟨_, hmemn⟩, ⟨⟨_, hmemd⟩, mem_nonZeroDivisors_of_ne_zero (Subtype.coe_ne_coe.1 hne)⟩),
      ?_⟩
    show z * ((RatFunc.X : RatFunc k)⁻¹ ^ N * algebraMap k[X] (RatFunc k) z.denom)
      = (RatFunc.X : RatFunc k)⁻¹ ^ N * algebraMap k[X] (RatFunc k) z.num
    rw [hzd, ← mul_assoc, mul_comm z, mul_assoc]
  · exact congrArg (fun w => (1 : ↥(inftyChart k)) * w) (Subtype.ext hxy)

end InftyChart

end Rigidity.RET
