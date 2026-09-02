/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.BaseSubcyclotomicSplit
import InverseGalois.CFT.Brauer.OddArchimedeanBase
import InverseGalois.CFT.Scholz.AuxPrimeFamily

/-!
# Global reciprocity over a number field for a class of odd order

The invariants of a Brauer class of odd order over an arbitrary number field add up to zero.  Over
the rationals the same statement is reached by a reduction consuming one auxiliary prime per pair of
bad primes; over a general base no such reduction is available, because the correcting cyclic
algebras that move an invariant from one place to another are not free to be built at a prescribed
place.  What replaces the reduction is a single auxiliary prime doing all the work at once.

That is possible because the criterion the auxiliary prime has to satisfy is a power residue
condition at an exponent the argument is free to raise: a class of order dividing a power of `ℓ` is
split by the subfield of degree a high power of `ℓ` of the cyclotomic field of the auxiliary prime
as soon as every rational prime below a place carrying a nontrivial invariant is a non-residue at an
exponent bounded in terms of the excess of the degree over the order, and that excess is
unconstrained.  Raising the exponent past the number of bad primes makes the union bound behind the
density argument succeed for all of them simultaneously.

For an odd exponent the archimedean invariants are automatically trivial, since the Brauer group of
the reals is killed by two.  A class of arbitrary odd order splits as a product of classes of
prime-power order, one for each prime factor of the order, so the prime-power case carries the
general one.

## Main results

* `InverseGalois.CFT.totalInvariant_eq_one_of_pow_eq_one_primePow_base`: **the invariants of a
  Brauer class of a number field of odd prime-power order add up to zero.**
* `InverseGalois.CFT.totalInvariant_eq_one_of_pow_eq_one_odd_base`: **the invariants of a Brauer
  class of a number field of odd order add up to zero.**

## Tags

Brauer group, local invariant, global reciprocity, number field, auxiliary prime, power residue,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField InverseGalois.NumberTheory

/-! ### Reciprocity for a class of odd prime-power order -/

section PrimePower

/-- **The invariants of a Brauer class of a number field of odd prime-power order add up to zero.**
Its invariants are nontrivial at only finitely many places, so only finitely many rational primes
lie below a place carrying one; a single auxiliary prime modulo which all of them are non-residues
at an exponent exceeding their number splits the class over a cyclic subfield of the cyclotomic
field of that auxiliary prime, and the archimedean invariants of a class of odd order are
trivial. -/
theorem totalInvariant_eq_one_of_pow_eq_one_primePow_base {k : Type} [Field k] [NumberField k]
    {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) {x : BrauerGroup.{0, 0} k} (hx : x ^ ℓ ^ e = 1) :
    totalInvariant k x = 1 := by
  classical
  rcases eq_or_ne e 0 with rfl | he
  · rw [pow_zero, pow_one] at hx
    rw [hx, map_one]
  have hfin := finite_setOf_placeInvariant_ne_one (k := k) x
  obtain ⟨P, hPp, hbadP⟩ : ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧
      ∀ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x ≠ 1 →
        ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 k) ∈ v.asIdeal → p ∈ P := by
    refine ⟨hfin.toFinset.image fun v => Rat.HeightOneSpectrum.natGenerator (primeUnder (𝓞 ℚ) v),
      ?_, ?_⟩
    · intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
      exact Rat.HeightOneSpectrum.prime_natGenerator _
    · intro v hinv p hp hpv
      refine Finset.mem_image.mpr ⟨v, hfin.mem_toFinset.mpr hinv, ?_⟩
      refine natGenerator_eq_of_natCast_mem hp ?_
      rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hpv
  have hcard : P.card < ℓ ^ (P.card + 1) :=
    lt_of_lt_of_le (Nat.lt_pow_self hℓ.one_lt) (Nat.pow_le_pow_right hℓ.pos (by omega))
  obtain ⟨q, hqp, hqT, hqdvd, hqres⟩ :=
    exists_prime_two_mul_dvd_sub_one_forall_pow_ne_one
      (d := e + Nat.log ℓ (finrank ℚ k) + P.card) (M := P.card + 1) hℓ hℓodd (by omega)
      (by omega) hPp hcard (finite_ramifiedSet k).toFinset
  refine totalInvariant_eq_one_of_forall_pow_ne_one_primePow_base k hℓ he (by omega)
    (infinitePlaceInvariant_eq_one_of_odd_pow_eq_one hℓodd.pow hx) hx hqp
    (fun hc => hqT ((Set.Finite.mem_toFinset _).mpr hc)) hqdvd ?_
  intro v hinv p hp hpv
  rw [show e + Nat.log ℓ (finrank ℚ k) + P.card - e - Nat.log ℓ (finrank ℚ k) + 1 = P.card + 1 by
    omega]
  exact hqres p (hbadP v hinv p hp hpv)

end PrimePower

/-! ### Reciprocity for a class of odd order -/

section Odd

/-- **The invariants of a Brauer class of a number field of odd order add up to zero.**  Splitting
the order at its least prime factor into a prime power and a coprime cofactor, a Bézout relation
writes the class as a product of a class killed by the prime power and a class killed by the
strictly smaller cofactor; the first is covered by the prime-power case and the second by
induction. -/
theorem totalInvariant_eq_one_of_pow_eq_one_odd_base (k : Type) [Field k] [NumberField k] :
    ∀ n : ℕ, Odd n → ∀ x : BrauerGroup.{0, 0} k, x ^ n = 1 → totalInvariant k x = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd x hx
    have hn : n ≠ 0 := by
      rintro rfl
      rw [Nat.odd_iff] at hodd
      omega
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with h1 | h1
    · rw [← h1, pow_one] at hx
      rw [hx, map_one]
    set p := n.minFac with hp
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have hpodd : Odd p := hodd.of_dvd_nat (Nat.minFac_dvd n)
    set c := n.factorization p with hc
    set r := p ^ c with hr
    set m := n / r with hm
    have hrm : r * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hcop : Nat.Coprime r m := Nat.Coprime.pow_left c (Nat.coprime_ordCompl hpp hn)
    have hm0 : m ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hrm
      exact hn hrm.symm
    have hc1 : 1 ≤ c := hpp.factorization_pos_of_dvd hn (Nat.minFac_dvd n)
    have hr2 : 2 ≤ r := le_trans hpp.two_le (le_trans (le_of_eq (pow_one p).symm)
      (Nat.pow_le_pow_right hpp.pos hc1))
    have hmn : m < n := by
      rw [← hrm]
      nlinarith [Nat.pos_of_ne_zero hm0]
    have hmdvd : m ∣ n := ⟨r, by rw [← hrm]; exact mul_comm r m⟩
    have hA : totalInvariant k (x ^ m) = 1 := by
      refine totalInvariant_eq_one_of_pow_eq_one_primePow_base (e := c) hpp hpodd ?_
      rw [← pow_mul, mul_comm m r, hrm, hx]
    have hB : totalInvariant k (x ^ r) = 1 := by
      refine ih m hmn (hodd.of_dvd_nat hmdvd) (x ^ r) ?_
      rw [← pow_mul, hrm, hx]
    have hbez : (1 : ℤ) = (r : ℤ) * Nat.gcdA r m + (m : ℤ) * Nat.gcdB r m := by
      have hg := Nat.gcd_eq_gcd_ab r m
      rwa [hcop, Nat.cast_one] at hg
    have hsplit : x = (x ^ r) ^ (Nat.gcdA r m) * (x ^ m) ^ (Nat.gcdB r m) := by
      rw [← zpow_natCast x r, ← zpow_natCast x m, ← zpow_mul, ← zpow_mul, ← zpow_add,
        ← hbez, zpow_one]
    rw [hsplit, map_mul, map_zpow, map_zpow, hA, hB, one_zpow, one_zpow, one_mul]

end Odd

end InverseGalois.CFT
