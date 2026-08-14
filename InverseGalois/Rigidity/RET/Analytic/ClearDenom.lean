/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Clearing denominators

A polynomial with coefficients in a field of fractions becomes a polynomial over the base ring
after multiplication by a single nonzero element of the base ring, and a finite family of them
can be cleared by one common element.  Consequently an identity

`A · f + B · g = 1`

between polynomials over the field of fractions, with `f` and `g` defined over the base ring,
can be rewritten as an identity `A' · f + B' · g = C c` with `A'`, `B'` over the base ring and
`c` a nonzero element of it.  The point of the rewriting is that the new identity may be
evaluated: at every place where `c` does not vanish, `f` and `g` remain coprime.

## Main results

* `Rigidity.RET.exists_clear_denom` — one polynomial.
* `Rigidity.RET.exists_common_denom` — a finite family, cleared by one element.
* `Rigidity.RET.exists_bezout_clear` — a Bézout identity, cleared.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **One polynomial over the field of fractions becomes integral after one multiplication.** -/
theorem exists_clear_denom (f : Polynomial K) :
    ∃ (d : R) (N : Polynomial R), d ≠ 0 ∧
      N.map (algebraMap R K) = C (algebraMap R K d) * f := by
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors R) f
  refine ⟨(b : R), IsLocalization.integerNormalization (nonZeroDivisors R) f,
    nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [hb, ← algebraMap_smul (A := K) (b : R) f, smul_eq_C_mul]

/-- **A finite family is cleared by a single element of the base ring.** -/
theorem exists_common_denom {ι : Type*} [Finite ι] (f : ι → Polynomial K) :
    ∃ (d : R) (N : ι → Polynomial R), d ≠ 0 ∧
      ∀ i, (N i).map (algebraMap R K) = C (algebraMap R K d) * f i := by
  classical
  letI := Fintype.ofFinite ι
  choose d N hd hN using fun i => exists_clear_denom (R := R) (f i)
  refine ⟨∏ i, d i, fun i => C (∏ j ∈ Finset.univ.erase i, d j) * N i,
    Finset.prod_ne_zero_iff.mpr fun i _ => hd i, fun i => ?_⟩
  rw [Polynomial.map_mul, map_C, hN i, ← mul_assoc, ← C_mul, ← map_mul,
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

/-- **A Bézout identity over the field of fractions, cleared of denominators.**  The right-hand
side is a nonzero constant of the base ring, so the identity survives every evaluation at which
that constant does not vanish. -/
theorem exists_bezout_clear {f₁ f₂ : Polynomial R} {d : R} (hd : d ≠ 0) (A₀ B₀ : Polynomial K)
    (h : A₀ * f₁.map (algebraMap R K) + B₀ * f₂.map (algebraMap R K)
      = C (algebraMap R K d)) :
    ∃ (A B : Polynomial R) (c : R), c ≠ 0 ∧ A * f₁ + B * f₂ = C c := by
  obtain ⟨e₁, A₁, he₁, hA₁⟩ := exists_clear_denom (R := R) A₀
  obtain ⟨e₂, B₁, he₂, hB₁⟩ := exists_clear_denom (R := R) B₀
  refine ⟨C e₂ * A₁, C e₁ * B₁, e₁ * e₂ * d,
    mul_ne_zero (mul_ne_zero he₁ he₂) hd, ?_⟩
  refine Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K) ?_
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, map_C, map_C, map_C, hA₁, hB₁, map_mul, map_mul]
  have hrw : C (algebraMap R K e₂) * (C (algebraMap R K e₁) * A₀) * f₁.map (algebraMap R K)
      + C (algebraMap R K e₁) * (C (algebraMap R K e₂) * B₀) * f₂.map (algebraMap R K)
      = C (algebraMap R K e₁) * C (algebraMap R K e₂)
        * (A₀ * f₁.map (algebraMap R K) + B₀ * f₂.map (algebraMap R K)) := by ring
  rw [hrw, h, map_mul, ← C_mul]

end Rigidity.RET

end
