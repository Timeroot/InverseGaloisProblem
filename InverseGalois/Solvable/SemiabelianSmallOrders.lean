/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianP2Q
import InverseGalois.Solvable.SemiabelianP4
import InverseGalois.Solvable.SemiabelianSmall

/-!
# Every finite group of order less than `24` is semiabelian

The criteria collected in `InverseGalois.Solvable.SemiabelianSmall`,
`InverseGalois.Solvable.SemiabelianP2Q` and `InverseGalois.Solvable.SemiabelianP4` cover between
them every shape of order below `24`.  Writing out the factorizations:

* `1` is the trivial group;
* `2, 3, 5, 7, 11, 13, 17, 19, 23` are prime;
* `4, 6, 9, 10, 14, 15, 21, 22` are products of two primes;
* `8` is a cube of a prime;
* `12, 18, 20` are of the shape `p ^ 2 * q` for distinct primes;
* `16` is a fourth power of a prime.

Every one of those shapes carries a normal abelian subgroup with a semiabelian supplement, so the
covering criterion of `InverseGalois.Solvable.SemiabelianCriterion` applies throughout.  The order
`24` is the first one this list leaves out, and the first at which the shapes above are exhausted:
it is `p ^ 3 * q`, a shape none of the criteria reach.

## Main results

* `IsSemiabelian.of_card_eq_prime_pow_four_two`, `IsSemiabelian.of_card_eq_sixteen`: every group of
  order `16` is semiabelian.
* `IsSemiabelian.of_card_lt_twentyfour`: **every finite group of order less than `24` is
  semiabelian.**
-/

namespace IsSemiabelian

/-- **Every group of order `16` is semiabelian**, being a group of order `p ^ 4` for the prime
`p = 2`. -/
theorem of_card_eq_prime_pow_four_two {G : Type} [Group G] [Finite G] (h : Nat.card G = 2 ^ 4) :
    IsSemiabelian G :=
  of_card_eq_prime_pow_four Nat.prime_two h

/-- **Every group of order `16` is semiabelian.** -/
theorem of_card_eq_sixteen {G : Type} [Group G] [Finite G] (h : Nat.card G = 16) :
    IsSemiabelian G :=
  of_card_eq_prime_pow_four_two (h.trans (by norm_num))

/-- **Every finite group of order less than `24` is semiabelian.**  Each order below `24` is a
prime, a product of two primes, a prime cube, a prime fourth power, or of the shape `p ^ 2 * q`
for distinct primes `p` and `q`, and every one of those shapes is covered by a criterion of its
own. -/
theorem of_card_lt_twentyfour {G : Type} [Group G] [Finite G] (h : Nat.card G < 24) :
    IsSemiabelian G := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card G = n := ⟨_, rfl⟩
  have hpos : 0 < n := hn ▸ Nat.card_pos
  rw [hn] at h
  interval_cases n
  · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hn).1
    exact of_subsingleton G
  · exact of_card_eq_prime Nat.prime_two hn
  · exact of_card_eq_prime Nat.prime_three hn
  · exact of_card_eq_prime_mul_prime Nat.prime_two Nat.prime_two (hn.trans (by norm_num))
  · exact of_card_eq_prime (by norm_num) hn
  · exact of_card_eq_prime_mul_prime Nat.prime_two Nat.prime_three (hn.trans (by norm_num))
  · exact of_card_eq_prime (by norm_num) hn
  · exact of_card_eq_prime_cube Nat.prime_two (hn.trans (by norm_num))
  · exact of_card_eq_prime_mul_prime Nat.prime_three Nat.prime_three (hn.trans (by norm_num))
  · exact of_card_eq_prime_mul_prime Nat.prime_two (q := 5) (by norm_num) (hn.trans (by norm_num))
  · exact of_card_eq_prime (by norm_num) hn
  · exact of_card_eq_sq_mul_prime Nat.prime_two Nat.prime_three (by norm_num)
      (hn.trans (by norm_num))
  · exact of_card_eq_prime (by norm_num) hn
  · exact of_card_eq_prime_mul_prime Nat.prime_two (q := 7) (by norm_num) (hn.trans (by norm_num))
  · exact of_card_eq_prime_mul_prime Nat.prime_three (q := 5) (by norm_num)
      (hn.trans (by norm_num))
  · exact of_card_eq_sixteen hn
  · exact of_card_eq_prime (by norm_num) hn
  · exact of_card_eq_sq_mul_prime Nat.prime_three Nat.prime_two (by norm_num)
      (hn.trans (by norm_num))
  · exact of_card_eq_prime (by norm_num) hn
  · exact of_card_eq_sq_mul_prime Nat.prime_two (q := 5) (by norm_num) (by norm_num)
      (hn.trans (by norm_num))
  · exact of_card_eq_prime_mul_prime Nat.prime_three (q := 7) (by norm_num)
      (hn.trans (by norm_num))
  · exact of_card_eq_prime_mul_prime Nat.prime_two (q := 11) (by norm_num)
      (hn.trans (by norm_num))
  · exact of_card_eq_prime (by norm_num) hn

end IsSemiabelian
