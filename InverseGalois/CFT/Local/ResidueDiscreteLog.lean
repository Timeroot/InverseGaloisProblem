/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.ResiduePrimitiveRoot

/-!
# The power residue exponent of a number congruent to a power of a primitive root

A root of unity of a complete valued field whose residue is a power of a primitive root modulo the
residue characteristic detects the discrete logarithm of a number to the base that primitive root:
raising the root of unity to the discrete logarithm produces something congruent to the same power
of the number.

This is the congruence the power residue symbol at a ramified place reads.  The root of unity of
order the exponent has residue the complementary power of the primitive root, so its power by the
discrete logarithm has residue the complementary power of the number; and the complementary power
of the number is exactly the power residue symbol of that number.

## Main results

* `InverseGalois.CFT.valued_intCast_lt_one_of_dvd`: a multiple of the residue characteristic has
  valuation less than one.
* `InverseGalois.CFT.valued_pow_sub_natCast_pow_lt_one_of_dvd`: **the power by the discrete
  logarithm of a root of unity congruent to a power of a primitive root is congruent to the same
  power of the number.**

## Tags

valued field, residue field, primitive root, discrete logarithm, power residue symbol, root of
unity
-/

namespace InverseGalois.CFT

open scoped WithZero

section Congruence

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {q e : ℕ}

/-- **A multiple of the residue characteristic has valuation less than one**, the valuation being
that of the residue characteristic times that of the cofactor. -/
theorem valued_intCast_lt_one_of_dvd (h : HasResidueChar A q e) {m : ℤ} (hm : (q : ℤ) ∣ m) :
    Valued.v ((m : ℤ) : A) < 1 := by
  obtain ⟨c, rfl⟩ := hm
  rw [Int.cast_mul, Int.cast_natCast, Valuation.map_mul]
  calc Valued.v ((q : ℕ) : A) * Valued.v ((c : ℤ) : A)
      ≤ Valued.v ((q : ℕ) : A) * 1 := mul_le_mul' le_rfl (valued_intCast_le_one c)
    _ = Valued.v ((q : ℕ) : A) := mul_one _
    _ < 1 := valued_residueChar_lt_one h

/-- **The power by the discrete logarithm of a root of unity congruent to a power of a primitive
root is congruent to the same power of the number.**  The two congruences multiply out: the root of
unity is congruent to the complementary power of the primitive root, so its power by the discrete
logarithm is congruent to the complementary power of the power of the primitive root, which is the
complementary power of the number. -/
theorem valued_pow_sub_natCast_pow_lt_one_of_dvd (h : HasResidueChar A q e) {ζ : A} {b M c p : ℕ}
    (hζ : Valued.v (ζ - ((b ^ M : ℕ) : A)) < 1)
    (hdvd : (q : ℤ) ∣ ((p : ℕ) : ℤ) - ((b ^ c : ℕ) : ℤ)) :
    Valued.v (ζ ^ c - ((p : ℕ) : A) ^ M) < 1 := by
  have hζle : Valued.v ζ ≤ 1 := by
    have hadd := Valuation.map_add Valued.v (ζ - ((b ^ M : ℕ) : A)) (((b ^ M : ℕ) : A))
    rw [sub_add_cancel] at hadd
    exact hadd.trans (max_le hζ.le (valued_natCast_le_one _))
  have h1 : Valued.v (ζ ^ c - ((b ^ M : ℕ) : A) ^ c) < 1 :=
    valued_sub_pow_lt_one hζle (valued_natCast_le_one _) hζ c
  have h2 : Valued.v (((p : ℕ) : A) - ((b ^ c : ℕ) : A)) < 1 := by
    have hv := valued_intCast_lt_one_of_dvd h hdvd
    push_cast at hv
    push_cast
    exact hv
  have h3 : Valued.v (((p : ℕ) : A) ^ M - ((b ^ c : ℕ) : A) ^ M) < 1 :=
    valued_sub_pow_lt_one (valued_natCast_le_one _) (valued_natCast_le_one _) h2 M
  have hsplit : ζ ^ c - ((p : ℕ) : A) ^ M
      = (ζ ^ c - ((b ^ M : ℕ) : A) ^ c) - (((p : ℕ) : A) ^ M - ((b ^ c : ℕ) : A) ^ M) := by
    push_cast
    ring
  rw [hsplit]
  exact lt_of_le_of_lt (Valuation.map_sub Valued.v _ _) (max_lt h1 h3)

end Congruence

end InverseGalois.CFT
