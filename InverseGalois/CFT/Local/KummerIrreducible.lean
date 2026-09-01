/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Irreducibility of a radical polynomial of even degree

The difference of a power of the variable and a constant is irreducible exactly when the constant
is not a power of any prime order dividing the exponent — provided the exponent is odd.  For an
even exponent the criterion needs a correction, and the classical one is that a fourth power of the
exponent forces the constant away from minus four times the fourth powers.  Over a field carrying a
square root of minus one that extra condition is free, because minus four is then the fourth power
of one plus that square root, so the fourth powers and their opposites are the same set.

The proof is the same induction on the prime factorisation as for an odd exponent.  Splitting off a
prime factor, the norm of a root of the radical of the complementary exponent is a power of the
constant up to the sign coming from the parity of the factor; for an odd factor that sign is
harmless, and for the factor two it is absorbed either by an odd exponent on the other side or by
the square root of minus one.

## Main results

* `InverseGalois.CFT.pow_ne_neg_of_pow_ne`: a value whose opposite is not a power of a prime order
  is not one either, over a field with a square root of minus one when that order is two.
* `InverseGalois.CFT.X_pow_sub_C_irreducible_of_ne_zero`: **the difference of a power of the
  variable and a constant is irreducible as soon as the constant is not a power of any prime order
  dividing the exponent**, provided a fourth power of the exponent comes with a square root of
  minus one.
* `InverseGalois.CFT.X_pow_sub_C_irreducible_iff_of_ne_zero`: the same as a criterion.

## Tags

Kummer extension, radical extension, irreducible polynomial, norm, root of unity
-/

universe u

namespace InverseGalois.CFT

open Polynomial IntermediateField

/-! ### Changing the sign of a constant term -/

section Sign

/-- **A value whose opposite is not a power of a prime order is not one either**, over a field
carrying a square root of minus one when that order is two: for an odd order the opposite of the
value is the power of the opposite of the root, and for the order two it is the power of the
product of the root with the square root of minus one. -/
theorem pow_ne_neg_of_pow_ne {K : Type*} [Field K] {q : ℕ} (hq : q.Prime)
    (hi : q = 2 → ∃ i : K, i ^ 2 = -1) {a : K} (ha : ∀ b : K, b ^ q ≠ a) (c : K) :
    c ^ q ≠ -a := by
  intro hc
  rcases hq.eq_two_or_odd' with rfl | hodd
  · obtain ⟨i, hi2⟩ := hi rfl
    refine ha (i * c) ?_
    rw [mul_pow, hi2, hc, neg_mul, one_mul, neg_neg]
  · refine ha (-c) ?_
    rw [hodd.neg_pow, hc, neg_neg]

end Sign

/-! ### The criterion for an arbitrary exponent -/

section Irreducible

variable {K : Type u} [Field K]

/-- **The difference of a power of the variable and a constant is irreducible as soon as the
constant is not a power of any prime order dividing the exponent**, provided a fourth power of the
exponent comes with a square root of minus one in the field.  Splitting off a prime factor of the
exponent, the norm of a root of the radical of the complementary exponent is, up to the sign of the
parity of the factor, a power of the constant. -/
theorem X_pow_sub_C_irreducible_of_ne_zero {n : ℕ} (hn : n ≠ 0)
    (hi : 4 ∣ n → ∃ i : K, i ^ 2 = -1) {a : K}
    (ha : ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ n - C a) := by
  induction n using induction_on_primes generalizing K a with
  | zero => exact absurd rfl hn
  | one => simpa using irreducible_X_sub_C a
  | prime_mul p m hp IH =>
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hn (Nat.mul_zero p)
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mul_right _ _)))
    intro E _ _ x hx
    have hint : IsIntegral K x := not_not.mp fun h => by
      simpa only [degree_zero, degree_X_pow_sub_C hp.pos, WithBot.natCast_ne_bot] using
        congr_arg degree (hx.symm.trans (dif_neg h))
    have hi' : 4 ∣ m → ∃ i : ↥K⟮x⟯, i ^ 2 = -1 := fun h4 => by
      obtain ⟨i, hi2⟩ := hi (h4.mul_left p)
      exact ⟨algebraMap K ↥K⟮x⟯ i, by rw [← map_pow, hi2, map_neg, map_one]⟩
    refine IH hm0 hi' fun q hq hqm b hb => ?_
    rcases hp.eq_two_or_odd' with rfl | hpodd
    · have hnorm : (Algebra.norm K b) ^ q = -a := by
        rw [← map_pow, hb, ← adjoin.powerBasis_gen hint,
          Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
        simp [minpoly_gen, hx]
      refine pow_ne_neg_of_pow_ne hq (fun hq2 => hi ?_)
        (ha q hq (dvd_mul_of_dvd_right hqm 2)) (Algebra.norm K b) hnorm
      exact (by norm_num : (4 : ℕ) = 2 * 2) ▸ mul_dvd_mul_left 2 (hq2 ▸ hqm)
    · refine ha q hq (dvd_mul_of_dvd_right hqm p) (Algebra.norm K b) ?_
      rw [← map_pow, hb, ← adjoin.powerBasis_gen hint,
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
      simp [minpoly_gen, hx, hp.ne_zero.symm, hpodd.neg_pow]

/-- **The difference of a power of the variable and a constant is irreducible exactly when the
constant is not a power of any prime order dividing the exponent**, provided a fourth power of the
exponent comes with a square root of minus one in the field. -/
theorem X_pow_sub_C_irreducible_iff_of_ne_zero {n : ℕ} (hn : n ≠ 0)
    (hi : 4 ∣ n → ∃ i : K, i ^ 2 = -1) {a : K} :
    Irreducible (X ^ n - C a) ↔ ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a :=
  ⟨fun e _ hp hpn => pow_ne_of_irreducible_X_pow_sub_C e hpn hp.ne_one,
    X_pow_sub_C_irreducible_of_ne_zero hn hi⟩

end Irreducible

end InverseGalois.CFT
