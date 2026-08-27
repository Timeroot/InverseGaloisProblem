/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A product of two squarefree products of primes is a square only when they agree

A product over a finite set of distinct primes is squarefree, so the exponent of a prime in the
product of two such is the number of the two sets containing it.  That number is even exactly when
the prime lies in both or in neither, so a square forces the two sets to coincide.

A rational number whose square is a natural number is itself a natural number, because the
denominator of a square is the square of the denominator.  Together these say that two finite sets
of primes with a rational square root of the product of their products are equal, which is how a
radicand recovers the set of primes dividing it.

## Main results

* `InverseGalois.CFT.exists_sq_eq_of_rat_sq_eq_natCast`: a rational number whose square is a natural
  number is a natural number.
* `InverseGalois.CFT.eq_of_prod_mul_prod_eq_sq`: **two finite sets of primes whose products have a
  square product are equal.**
* `InverseGalois.CFT.eq_of_rat_sq_eq_prod_mul_prod`: the same with a rational square root.

## Tags

prime, squarefree, factorization, square
-/

namespace InverseGalois.CFT

/-! ### Rational square roots of natural numbers -/

/-- A rational number whose square is a natural number is a natural number. -/
theorem exists_sq_eq_of_rat_sq_eq_natCast {c : ℚ} {n : ℕ} (h : c ^ 2 = (n : ℚ)) :
    ∃ k : ℕ, k ^ 2 = n := by
  have hden : c.den = 1 := by
    have h1 : c.den ^ 2 = 1 := by rw [← Rat.den_pow, h, Rat.den_natCast]
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 (by norm_num)
  have hc : ((c.num : ℚ)) = c := (Rat.den_eq_one_iff c).mp hden
  refine ⟨c.num.natAbs, ?_⟩
  have hq : ((c.num ^ 2 : ℤ) : ℚ) = ((n : ℤ) : ℚ) := by push_cast [hc]; exact_mod_cast h
  have hz : c.num ^ 2 = (n : ℤ) := Int.cast_injective hq
  have hn : ((c.num.natAbs ^ 2 : ℕ) : ℤ) = (n : ℤ) := by
    push_cast
    rw [sq_abs]
    exact hz
  exact_mod_cast hn

/-! ### The factorization of a product of distinct primes -/

/-- The exponent of a prime in a product over a finite set of distinct primes is one when the prime
lies in the set and zero otherwise. -/
theorem factorization_prod_prime {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (p : ℕ) :
    (∏ q ∈ T, q).factorization p = if p ∈ T then 1 else 0 := by
  classical
  have hterm : ∀ q ∈ T, (Nat.factorization q) p = if q = p then 1 else 0 := by
    intro q hq
    rw [(hT q hq).factorization, Finsupp.single_apply]
  rw [Nat.factorization_prod fun x hx => (hT x hx).ne_zero, Finset.sum_apply',
    Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T p fun _ => 1]

/-- A product over a finite set of primes is nonzero. -/
theorem prod_prime_ne_zero {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : (∏ q ∈ T, q) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun q hq => (hT q hq).ne_zero

/-- **Two finite sets of primes whose products have a square product are equal.**  A prime occurs in
the product with exponent the number of the two sets containing it, and that number is even only
when it is zero or two. -/
theorem eq_of_prod_mul_prod_eq_sq {T₁ T₂ : Finset ℕ} (h₁ : ∀ p ∈ T₁, p.Prime)
    (h₂ : ∀ p ∈ T₂, p.Prime) {k : ℕ} (h : (∏ p ∈ T₁, p) * (∏ p ∈ T₂, p) = k ^ 2) :
    T₁ = T₂ := by
  classical
  have key : ∀ p : ℕ,
      ((if p ∈ T₁ then 1 else 0) + (if p ∈ T₂ then 1 else 0) : ℕ) = 2 * k.factorization p := by
    intro p
    have hfac : ((∏ p ∈ T₁, p) * (∏ p ∈ T₂, p)).factorization p = (k ^ 2).factorization p := by
      rw [h]
    rw [Nat.factorization_mul (prod_prime_ne_zero h₁) (prod_prime_ne_zero h₂), Finsupp.add_apply,
      factorization_prod_prime h₁, factorization_prod_prime h₂, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul] at hfac
    exact hfac
  refine Finset.ext fun p => ?_
  have hk := key p
  by_cases hp1 : p ∈ T₁ <;> by_cases hp2 : p ∈ T₂ <;> simp only [hp1, hp2, if_true, if_false] at hk
  · simp [hp1, hp2]
  · omega
  · omega
  · simp [hp1, hp2]

/-- **Two finite sets of primes whose products have a product with a rational square root are
equal.** -/
theorem eq_of_rat_sq_eq_prod_mul_prod {T₁ T₂ : Finset ℕ} (h₁ : ∀ p ∈ T₁, p.Prime)
    (h₂ : ∀ p ∈ T₂, p.Prime) {c : ℚ}
    (h : c ^ 2 = ((((∏ p ∈ T₁, p) * (∏ p ∈ T₂, p) : ℕ)) : ℚ)) : T₁ = T₂ := by
  obtain ⟨k, hk⟩ := exists_sq_eq_of_rat_sq_eq_natCast h
  exact eq_of_prod_mul_prod_eq_sq h₁ h₂ hk.symm

end InverseGalois.CFT
