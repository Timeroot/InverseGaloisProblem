/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianP2Q
import InverseGalois.Solvable.SemiabelianP4
import InverseGalois.Solvable.SemiabelianSmall
import InverseGalois.Solvable.SemiabelianZGroup

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

Past `24` the shapes resume: `25 = 5 ^ 2`, `26 = 2 * 13`, `27 = 3 ^ 3`, `28 = 2 ^ 2 * 7`, the
primes `29` and `31`, and the squarefree order `30`.  So the single order `24` is all that has to
be set aside to reach `32`.

## Main results

* `IsSemiabelian.of_card_eq_prime_pow_four_two`, `IsSemiabelian.of_card_eq_sixteen`: every group of
  order `16` is semiabelian.
* `IsSemiabelian.of_card_lt_twentyfour`: **every finite group of order less than `24` is
  semiabelian.**
* `IsSemiabelian.of_card_lt_thirtytwo`: **every finite group of order less than `32` other than
  `24` is semiabelian.**
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

/-- **Every finite group of order less than `32` other than `24` is semiabelian.**  The orders
between `24` and `32` are a prime square, a product of two primes, a prime cube, a shape
`p ^ 2 * q`, two primes and a squarefree order, so each of them is covered by a criterion of its
own; the order `24` is the one that has to be left out. -/
theorem of_card_lt_thirtytwo {G : Type} [Group G] [Finite G] (h : Nat.card G < 32)
    (h24 : Nat.card G ≠ 24) : IsSemiabelian G := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card G = n := ⟨_, rfl⟩
  rw [hn] at h h24
  rcases lt_or_ge n 24 with hlt | hge
  · exact of_card_lt_twentyfour (hn ▸ hlt)
  · interval_cases n
    · exact absurd rfl h24
    · exact of_card_eq_prime_sq (p := 5) (by norm_num) (hn.trans (by norm_num))
    · exact of_card_eq_prime_mul_prime Nat.prime_two (q := 13) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_prime_cube Nat.prime_three (hn.trans (by norm_num))
    · exact of_card_eq_sq_mul_prime Nat.prime_two (q := 7) (by norm_num) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_prime (by norm_num) hn
    · exact of_squarefree_card G (by rw [hn]; decide +kernel)
    · exact of_card_eq_prime (by norm_num) hn

end IsSemiabelian
