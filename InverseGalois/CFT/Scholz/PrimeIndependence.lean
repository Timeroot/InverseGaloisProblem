/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Distinct primes are independent modulo `ℓ`-th powers

A product of powers of distinct primes is an `ℓ`-th power of a rational number only when every
exponent is divisible by `ℓ`.  The reason is the `p`-adic valuation: it reads off the exponent of
`p` in the product, and it is divisible by `ℓ` on every `ℓ`-th power.

This is the source of the auxiliary primes of the Scholz–Reichardt construction.  The correction of
the residue degrees is governed by an `𝔽_ℓ`-linear map whose source is spanned by the power residue
vectors of the auxiliary primes; a vector annihilating the span produces a product of powers of the
ramified primes which is an `ℓ`-th power residue modulo every admissible auxiliary prime, and the
statement below is what makes such a product a genuinely new radical.

## Main results

* `InverseGalois.CFT.pow_ne_prod_pow`: **a product of powers of distinct primes with one exponent
  not divisible by `ℓ` is not an `ℓ`-th power in the rationals.**

## Tags

prime factorisation, `p`-adic valuation, radical, `ℓ`-th power
-/

namespace InverseGalois.CFT

open Finset

variable {ℓ : ℕ} {S : Finset ℕ} {a : ℕ → ℕ} {p₀ : ℕ}

/-- The `p`-adic valuation of a product of prime powers is the exponent of `p`. -/
theorem padicValNat_prod_pow (hS : ∀ p ∈ S, p.Prime) (hp₀ : p₀ ∈ S) :
    padicValNat p₀ (∏ p ∈ S, p ^ a p) = a p₀ := by
  haveI : Fact p₀.Prime := ⟨hS p₀ hp₀⟩
  have hne : ∀ p ∈ S, p ^ a p ≠ 0 := fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  have hfac := Nat.factorization_prod (S := S) (g := fun p => p ^ a p) hne
  have hval : (∏ p ∈ S, p ^ a p).factorization p₀ = a p₀ := by
    rw [hfac]
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single p₀]
    · rw [Nat.Prime.factorization_pow (hS p₀ hp₀)]
      simp
    · intro p hp hpne
      rw [Nat.Prime.factorization_pow (hS p hp)]
      simp [Ne.symm hpne]
    · intro h
      exact absurd hp₀ h
  rw [← hval, Nat.factorization_def _ (hS p₀ hp₀)]

/-- **A product of powers of distinct primes with one exponent not divisible by `ℓ` is not an
`ℓ`-th power in the rationals.**  The valuation at the prime with the offending exponent is that
exponent, while the valuation of an `ℓ`-th power is divisible by `ℓ`. -/
theorem pow_ne_prod_pow (hS : ∀ p ∈ S, p.Prime) (hp₀ : p₀ ∈ S) (hdvd : ¬ ℓ ∣ a p₀) (y : ℚ) :
    y ^ ℓ ≠ ((∏ p ∈ S, p ^ a p : ℕ) : ℚ) := by
  haveI : Fact p₀.Prime := ⟨hS p₀ hp₀⟩
  intro hy
  have hprod : (∏ p ∈ S, p ^ a p : ℕ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · rw [pow_zero] at hy
    have hone : (∏ p ∈ S, p ^ a p : ℕ) = 1 := by exact_mod_cast hy.symm
    rw [← padicValNat_prod_pow (a := a) hS hp₀, hone] at hdvd
    simp at hdvd
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_pow hpos.ne'] at hy
    exact hprod (by exact_mod_cast hy.symm)
  have hval : padicValRat p₀ (y ^ ℓ) = (ℓ : ℤ) * padicValRat p₀ y := padicValRat.pow hy0
  rw [hy, padicValRat.of_nat, padicValNat_prod_pow hS hp₀] at hval
  exact hdvd (Int.ofNat_dvd.mp ⟨padicValRat p₀ y, hval⟩)

end InverseGalois.CFT
