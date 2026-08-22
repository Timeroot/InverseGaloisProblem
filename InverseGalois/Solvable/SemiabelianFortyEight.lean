/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianSmallOrders
import InverseGalois.Solvable.SemiabelianSylowCount
import InverseGalois.Solvable.SemiabelianP2Q2

/-!
# The orders below `48`

The enumeration of `InverseGalois.Solvable.SemiabelianSmallOrders` stops at `32`, the first order
whose shape `2 ^ 5` no criterion of that file reaches.  Every order from `33` to `47` is again of a
shape that is covered, either by a factorization into at most two prime powers or by the Sylow
count that makes a Sylow subgroup unique:

* `33 = 3 * 11`, `34 = 2 * 17`, `35 = 5 * 7`, `38 = 2 * 19`, `39 = 3 * 13`, `46 = 2 * 23` are
  products of two primes;
* `37`, `41`, `43`, `47` are prime;
* `36 = 2 ^ 2 * 3 ^ 2` and `44 = 2 ^ 2 * 11` are of the shapes `p ^ 2 * q ^ 2` and `p ^ 2 * q`;
* `42 = 2 * 3 * 7` is squarefree;
* `40 = 2 ^ 3 * 5` and `45 = 3 ^ 2 * 5` have a unique Sylow subgroup at their largest prime,
  because no divisor of the complementary factor other than `1` is congruent to `1` modulo it.

So `24` and `32` are the only two orders below `48` left out, and `48` is where the enumeration
genuinely halts: the group `C2 . S4` of order `48` is not semiabelian.

## Main results

* `IsSemiabelian.of_card_lt_fortyeight`: **every finite group of order less than `48` other than
  `24` and `32` is semiabelian.**
* `IsSemiabelian.of_card_eq_mul_prime_of_divisors_lt_fortyeight`,
  `IsSemiabelian.of_card_eq_mul_prime_sq_of_divisors_lt_fortyeight`: the unbounded families
  `m * q` and `m * q ^ 2` with `m` below `48`, which the wider enumeration now reaches.
-/

namespace IsSemiabelian

/-- **Every finite group of order less than `48` other than `24` and `32` is semiabelian.**  The
orders from `33` to `47` are products of two primes, primes, the shapes `p ^ 2 * q` and
`p ^ 2 * q ^ 2`, a squarefree order, and two orders whose largest Sylow subgroup is unique by a
divisor count. -/
theorem of_card_lt_fortyeight {G : Type} [Group G] [Finite G] (h : Nat.card G < 48)
    (h24 : Nat.card G ≠ 24) (h32 : Nat.card G ≠ 32) : IsSemiabelian G := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card G = n := ⟨_, rfl⟩
  rw [hn] at h h24 h32
  rcases lt_or_ge n 32 with hlt | hge
  · exact of_card_lt_thirtytwo (hn ▸ hlt) (hn ▸ h24)
  · interval_cases n
    · exact absurd rfl h32
    · exact of_card_eq_prime_mul_prime Nat.prime_three (q := 11) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_prime_mul_prime Nat.prime_two (q := 17) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_prime_mul_prime (p := 5) (q := 7) (by norm_num) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_thirtysix hn
    · exact of_card_eq_prime (by norm_num) hn
    · exact of_card_eq_prime_mul_prime Nat.prime_two (q := 19) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_prime_mul_prime Nat.prime_three (q := 13) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_forty hn
    · exact of_card_eq_prime (by norm_num) hn
    · exact of_squarefree_card G (by rw [hn]; decide +kernel)
    · exact of_card_eq_prime (by norm_num) hn
    · exact of_card_eq_sq_mul_prime Nat.prime_two (q := 11) (by norm_num) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_fortyfive hn
    · exact of_card_eq_prime_mul_prime Nat.prime_two (q := 23) (by norm_num)
        (hn.trans (by norm_num))
    · exact of_card_eq_prime (by norm_num) hn

/-- **A group of order `m * q` with `m < 48` other than `24` and `32`, in which `1` is the only
divisor of `m` congruent to `1` modulo the prime `q`, is semiabelian.**  The count makes the Sylow
`q`-subgroup unique, hence normal, and the quotient of order `m` is semiabelian. -/
theorem of_card_eq_mul_prime_of_divisors_lt_fortyeight {G : Type} [Group G] [Finite G] {m q : ℕ}
    (hq : q.Prime) (hm : ¬ q ∣ m) (hmlt : m < 48) (hm24 : m ≠ 24) (hm32 : m ≠ 32)
    (h : Nat.card G = m * q) (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) : IsSemiabelian G :=
  of_card_eq_mul_prime_of_forall_mem_divisors hq hm h hdiv
    fun _ _ _ hH => of_card_lt_fortyeight (hH ▸ hmlt) (hH ▸ hm24) (hH ▸ hm32)

/-- **A group of order `m * q ^ 2` with `m < 48` other than `24` and `32`, in which `1` is the only
divisor of `m` congruent to `1` modulo the prime `q`, is semiabelian.** -/
theorem of_card_eq_mul_prime_sq_of_divisors_lt_fortyeight {G : Type} [Group G] [Finite G] {m q : ℕ}
    (hq : q.Prime) (hm : ¬ q ∣ m) (hmlt : m < 48) (hm24 : m ≠ 24) (hm32 : m ≠ 32)
    (h : Nat.card G = m * q ^ 2) (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) : IsSemiabelian G :=
  of_card_eq_mul_prime_sq_of_forall_mem_divisors hq hm h hdiv
    fun _ _ _ hH => of_card_lt_fortyeight (hH ▸ hmlt) (hH ▸ hm24) (hH ▸ hm32)

end IsSemiabelian
