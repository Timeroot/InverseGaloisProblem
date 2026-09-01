/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Two norms from a subfield of a cyclotomic field of prime conductor

An odd prime is the norm of one less than a primitive root of unity of that conductor, so it is
already a norm from every intermediate field: taking the norm in two steps factors the norm of the
whole cyclotomic field through the intermediate one.  And `-1` is the norm of `-1` from any
extension of odd degree, since the norm of a scalar is its power by the degree.

These are the two coefficients that a reciprocity computation cannot reach by a local calculation.
A cyclic algebra whose coefficient is a norm from its splitting field is trivial, so both of them
give the trivial class, and the remaining coefficients are the primes away from the conductor.

## Main results

* `InverseGalois.CFT.exists_units_norm_eq_conductor`: **an odd prime conductor is a norm from any
  intermediate field of its cyclotomic field.**
* `InverseGalois.CFT.exists_units_norm_eq_neg_one`: `-1` is a norm from an extension of the
  rationals of odd degree.

## Tags

cyclotomic field, norm, subfield, primitive root of unity, degree
-/

namespace InverseGalois.CFT

open NumberField

/-! ### The conductor is a norm -/

section Conductor

/-- **An odd prime conductor is a norm from any intermediate field of its cyclotomic field.**  It
is the norm of one less than a primitive root of unity, and the norm of the cyclotomic field is the
norm of the intermediate field composed with the norm to it. -/
theorem exists_units_norm_eq_conductor (q : ℕ) [NeZero q] [Fact q.Prime] (L F : Type) [Field L]
    [NumberField L] [IsCyclotomicExtension {q} ℚ L] [Field F] [NumberField F] [Algebra F L]
    [IsScalarTower ℚ F L] (hq2 : q ≠ 2) :
    ∃ b : Fˣ, Algebra.norm ℚ (b : F) = (q : ℚ) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({q} : Set ℕ)) ℚ L
    (Set.mem_singleton q) (NeZero.ne q)
  have hirr : Irreducible (Polynomial.cyclotomic q ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne q))
  have hnorm : Algebra.norm ℚ (ζ - 1) = (q : ℚ) := hζ.norm_sub_one_of_prime_ne_two' hirr hq2
  have htrans : Algebra.norm ℚ (Algebra.norm F (ζ - 1)) = (q : ℚ) := by
    rw [Algebra.norm_norm]
    exact hnorm
  have hq0 : ((q : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have hzero : Algebra.norm ℚ (0 : F) = 0 := Algebra.norm_eq_zero_iff.mpr rfl
  have hne : Algebra.norm F (ζ - 1) ≠ 0 := by
    intro h
    rw [h, hzero] at htrans
    exact hq0 htrans.symm
  exact ⟨Units.mk0 _ hne, by rw [Units.val_mk0]; exact htrans⟩

end Conductor

/-! ### Minus one is a norm from an odd degree extension -/

section NegOne

variable (F : Type*) [Field F] [Algebra ℚ F]

/-- **`-1` is a norm from an extension of the rationals of odd degree**, being the norm of `-1`:
the norm of a scalar is its power by the degree. -/
theorem exists_units_norm_eq_neg_one (hodd : Odd (Module.finrank ℚ F)) :
    ∃ b : Fˣ, Algebra.norm ℚ (b : F) = -1 := by
  refine ⟨-1, ?_⟩
  have hval : ((-1 : Fˣ) : F) = algebraMap ℚ F (-1) := by
    rw [map_neg, map_one, Units.val_neg, Units.val_one]
  rw [hval, Algebra.norm_algebraMap, hodd.neg_one_pow]

end NegOne

end InverseGalois.CFT
