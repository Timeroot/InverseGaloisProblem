/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.ChartIntegral
import InverseGalois.Rigidity.RET.Genus.LineDerivation

/-!
# Bounding the pole of an integral function at the far end of the line

A function on a cover of the line that is regular over the first chart has poles only above the
far end of the line, and those poles have bounded order: the function satisfies a monic equation
whose coefficients are polynomials in the coordinate, and dividing by a power of the coordinate
exceeding all their degrees turns that equation into a monic equation with coefficients regular at
the far end.  Dividing the roots of an equation is exactly what scaling its roots does, so the new
equation is the old one with its roots scaled, and the function divided by that power of the
coordinate is regular at the far end.

## Main results

* `Rigidity.RET.exists_isIntegral_inftyChart_inv_pow_mul` — dividing a function integral over the
  first chart by a large enough power of the coordinate makes it integral over the second.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET

section PoleBound

variable {k F : Type*} [Field k] [Field F] [Algebra k[X] F] [Algebra (RatFunc k) F]
  [IsScalarTower k[X] (RatFunc k) F]

/-- **Dividing a function integral over the first chart by a large enough power of the coordinate
makes it integral over the second.**  The coefficients of its minimal equation over the line are
polynomials in the coordinate, and scaling the roots of that equation by the chosen power of the
inverse coordinate moves every coefficient to the second chart. -/
theorem exists_isIntegral_inftyChart_inv_pow_mul {y : F} (hy : IsIntegral k[X] y) :
    ∃ N : ℕ, IsIntegral ↥(inftyChart k) ((coord k F)⁻¹ ^ N * y) := by
  classical
  have hyL : IsIntegral (RatFunc k) y := hy.tower_top
  set P := minpoly (RatFunc k) y with hP
  have hPm : P.Monic := minpoly.monic hyL
  have hPa : Polynomial.aeval y P = 0 := minpoly.aeval _ y
  set n := P.natDegree with hn
  choose p hp using fun i =>
    exists_polynomial_of_isIntegral k (isIntegral_coeff_minpoly (A := k[X]) hy i)
  set N := (Finset.range (n + 1)).sup fun i => (p i).natDegree with hN
  refine ⟨N, ?_⟩
  -- scaling the roots of the minimal equation
  have hzero : Polynomial.aeval (algebraMap (RatFunc k) F ((RatFunc.X : RatFunc k)⁻¹ ^ N) * y)
      (P.scaleRoots ((RatFunc.X : RatFunc k)⁻¹ ^ N)) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero hPa
  have hmapu : algebraMap (RatFunc k) F ((RatFunc.X : RatFunc k)⁻¹ ^ N) = (coord k F)⁻¹ ^ N := by
    rw [map_pow, map_inv₀, coord]
  rw [hmapu] at hzero
  refine isIntegral_of_monic_of_coeff_mem ((Polynomial.monic_scaleRoots_iff _).2 hPm) ?_ hzero
  -- and checking that every coefficient became regular at the far end
  intro i
  rw [Polynomial.coeff_scaleRoots, ← hn]
  rcases lt_trichotomy i n with hi | hi | hi
  · have h1 : (p i).natDegree ≤ N :=
      Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_range.2 (by omega))
    have h2 : N ≤ N * (n - i) := Nat.le_mul_of_pos_right N (by omega)
    have hmem := inv_pow_mul_algebraMap_mem_inftyChart k (p := p i) (N := N * (n - i))
      (h1.trans h2)
    rw [hp i] at hmem
    rw [← pow_mul, mul_comm]
    exact hmem
  · rw [hi, hn, hPm.coeff_natDegree, Nat.sub_self, pow_zero, mul_one]
    exact one_mem _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
    exact zero_mem _

end PoleBound

end Rigidity.RET
