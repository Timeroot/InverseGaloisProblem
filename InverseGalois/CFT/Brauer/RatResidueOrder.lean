/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.ResidueCard
import InverseGalois.CFT.Brauer.ResidueCardDegree

/-!
# Residues of the rationals at a prime, and the order of a power of a primitive root

The residue ring of the integers of the rationals at a place containing a prime has that prime as
its characteristic and as its number of elements, so two natural numbers have the same residue
there exactly when they are congruent modulo the prime.

Naming a residue by a primitive root modulo the prime therefore transports faithfully: a power of
a primitive root whose exponent is complementary to a divisor of one less than the prime has
exactly that divisor as its multiplicative order among the residues.  This is the input needed to
compare the exponents naming the invariants above a prime with the exponent naming the invariant
below it.

## Main results

* `InverseGalois.CFT.natCard_quotient_rat`: the residue ring of the rationals at a place containing
  a prime has that prime as its number of elements.
* `InverseGalois.CFT.charP_quotient_rat`: it has that prime as its characteristic.
* `InverseGalois.CFT.mk_natCast_eq_mk_natCast_iff_modEq`: two natural numbers have the same residue
  exactly when they are congruent modulo the prime.
* `InverseGalois.CFT.orderOf_mk_natCast_pow_rat`: **the residue of a power of a primitive root has
  as multiplicative order the complementary factor of its exponent in one less than the prime.**

## Tags

number field, rational numbers, residue field, characteristic, primitive root, multiplicative
order, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section RatResidue

variable {q : ℕ}

/-- The residue ring of the integers of the rationals at a place containing a prime has that prime
as its number of elements. -/
theorem natCard_quotient_rat (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : Nat.card (𝓞 ℚ ⧸ v.asIdeal) = q := by
  rw [← natCard_divisionResidue_adicCompletion_eq_natCard_quotient]
  exact natCard_divisionResidue_adicCompletion_rat hq v hv

/-- The residue ring of the integers of the rationals at a place containing a prime has that prime
as its characteristic. -/
theorem charP_quotient_rat (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : CharP (𝓞 ℚ ⧸ v.asIdeal) q := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI : IsDomain (𝓞 ℚ ⧸ v.asIdeal) := Ideal.Quotient.isDomain _
  refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal) q, Ideal.Quotient.eq_zero_iff_mem]
  exact hv

/-- **Two natural numbers have the same residue at a place of the rationals containing a prime
exactly when they are congruent modulo that prime.** -/
theorem mk_natCast_eq_mk_natCast_iff_modEq (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (n m : ℕ) :
    Ideal.Quotient.mk v.asIdeal ((n : ℕ) : 𝓞 ℚ)
        = Ideal.Quotient.mk v.asIdeal ((m : ℕ) : 𝓞 ℚ) ↔ Nat.ModEq q n m := by
  haveI := charP_quotient_rat hq v hv
  rw [map_natCast, map_natCast]
  exact CharP.natCast_eq_natCast _ _

end RatResidue

/-! ### The order of the residue of a power of a primitive root -/

section Order

variable {q g M N : ℕ}

/-- **The residue of a power of a primitive root modulo a prime has as multiplicative order the
complementary factor of its exponent in one less than the prime.**  Its power by that factor is the
full power given by the little theorem, and any power of it that is trivial gives a multiple of one
less than the prime, hence a multiple of the factor. -/
theorem orderOf_mk_natCast_pow_rat (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hg : ¬ q ∣ g)
    (hgord : ∀ m : ℕ, q ∣ g ^ m - 1 → (q - 1) ∣ m) (hMN : M * N = q - 1) :
    orderOf (Ideal.Quotient.mk v.asIdeal (((g ^ M : ℕ) : 𝓞 ℚ))) = N := by
  have hq1 : 1 < q := hq.one_lt
  have hMN0 : M * N ≠ 0 := by omega
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hMN0
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hMN0
  have hgc : Nat.Coprime g q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hg).symm
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · rw [Nat.coprime_zero_left] at hgc
      omega
    · exact h
  -- a trivial residue of a power of the primitive root is a multiple of the full order
  have hkey : ∀ m : ℕ,
      Ideal.Quotient.mk v.asIdeal (((g ^ m : ℕ) : 𝓞 ℚ))
          = Ideal.Quotient.mk v.asIdeal (((1 : ℕ) : 𝓞 ℚ)) → (q - 1) ∣ m := by
    intro m hm
    refine hgord m ?_
    have h := ((mk_natCast_eq_mk_natCast_iff_modEq hq v hv _ _).mp hm).symm
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hg0)).mp h
  have hpow : Ideal.Quotient.mk v.asIdeal (((g ^ M : ℕ) : 𝓞 ℚ)) ^ N = 1 := by
    have h1 : Ideal.Quotient.mk v.asIdeal (((g ^ (M * N) : ℕ) : 𝓞 ℚ))
        = Ideal.Quotient.mk v.asIdeal (((g ^ M : ℕ) : 𝓞 ℚ)) ^ N := by
      rw [pow_mul, Nat.cast_pow, map_pow]
    rw [← h1, hMN]
    have h2 : Nat.ModEq q (g ^ (q - 1)) 1 := by
      have := Nat.ModEq.pow_totient hgc
      rwa [Nat.totient_prime hq] at this
    rw [(mk_natCast_eq_mk_natCast_iff_modEq hq v hv _ _).mpr h2]
    rw [map_natCast, Nat.cast_one]
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow) ?_
  have hord : Ideal.Quotient.mk v.asIdeal (((g ^ M : ℕ) : 𝓞 ℚ))
      ^ orderOf (Ideal.Quotient.mk v.asIdeal (((g ^ M : ℕ) : 𝓞 ℚ))) = 1 := pow_orderOf_eq_one _
  have hcast : Ideal.Quotient.mk v.asIdeal
        (((g ^ (M * orderOf (Ideal.Quotient.mk v.asIdeal (((g ^ M : ℕ) : 𝓞 ℚ)))) : ℕ) : 𝓞 ℚ))
      = Ideal.Quotient.mk v.asIdeal (((g ^ M : ℕ) : 𝓞 ℚ))
        ^ orderOf (Ideal.Quotient.mk v.asIdeal (((g ^ M : ℕ) : 𝓞 ℚ))) := by
    rw [pow_mul, Nat.cast_pow, map_pow]
  rw [← hcast] at hord
  have hone : Ideal.Quotient.mk v.asIdeal (((1 : ℕ) : 𝓞 ℚ)) = 1 := by
    rw [map_natCast, Nat.cast_one]
  rw [← hone] at hord
  have hdvd := hkey _ hord
  rw [← hMN] at hdvd
  exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hM0)).mp hdvd

end Order

end InverseGalois.CFT
