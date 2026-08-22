/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.Main
import InverseGalois.Solvable.SemiabelianHall
import InverseGalois.Solvable.SemiabelianSmall
import InverseGalois.Solvable.SemiabelianZGroup
import InverseGalois.Solvable.SemiabelianSmallOrders
import InverseGalois.Solvable.SemiabelianLargePrime
import InverseGalois.Solvable.SemiabelianClassTwo
import InverseGalois.Solvable.SemiabelianP2Q2
import InverseGalois.Solvable.SemiabelianSylowCount
import InverseGalois.Solvable.SemiabelianAGroup
import InverseGalois.Solvable.SemiabelianWreath
import InverseGalois.Solvable.SemiabelianFortyEight

/-!
# Z-groups and groups of small order, regularly over `ℚ(T)`

The Dentzer–Stoll construction realizes every finite semiabelian group regularly over `ℚ(T)`, so
each group-theoretic criterion for semiabelianness immediately becomes an entry of the catalogue of
regular Galois groups.  This file records the entries supplied by the splitting criteria and by the
classification of the small orders.

The widest of them is the theorem of Hölder, Burnside and Zassenhaus: a finite group all of whose
Sylow subgroups are cyclic is metacyclic, hence semiabelian.  Since a group of squarefree order has
all its Sylow subgroups of prime order, every such group is covered; so are the groups of order
`p`, `p ^ 2`, `p ^ 3` and `p * q`, whose semiabelianness comes from an abelian subgroup of index
the smallest prime factor of the order.

## Main results

* `InverseGalois.isRegularInverseGalois_of_isZGroup`: **a finite group all of whose Sylow subgroups
  are cyclic is a regular Galois group over `ℚ(T)`.**
* `InverseGalois.isRegularInverseGalois_of_squarefree_card`: **every finite group of squarefree
  order is a regular Galois group over `ℚ(T)`.**
* `InverseGalois.isRegularInverseGalois_of_abelian_of_index_eq_minFac`: the same for a group with an
  abelian subgroup whose index is the smallest prime factor of the order.
* `InverseGalois.isRegularInverseGalois_of_card_eq_prime`,
  `InverseGalois.isRegularInverseGalois_of_card_eq_prime_sq`,
  `InverseGalois.isRegularInverseGalois_of_card_eq_prime_cube`,
  `InverseGalois.isRegularInverseGalois_of_card_eq_prime_mul_prime`,
  `InverseGalois.isRegularInverseGalois_of_card_eq_sq_mul_prime`,
  `InverseGalois.isRegularInverseGalois_of_card_eq_prime_pow_four`: the groups of order `p`,
  `p ^ 2`, `p ^ 3`, `p * q`, `p ^ 2 * q` and `p ^ 4`.
* `InverseGalois.isRegularInverseGalois_of_card_lt_twentyfour`: **every finite group of order less
  than `24` is a regular Galois group over `ℚ(T)`.**
* `InverseGalois.isRegularInverseGalois_of_card_lt_thirtytwo`: **every finite group of order less
  than `32` other than `24` is a regular Galois group over `ℚ(T)`.**
* `InverseGalois.isRegularInverseGalois_of_card_lt_fortyeight`: **every finite group of order less
  than `48` other than `24` and `32` is a regular Galois group over `ℚ(T)`.**
* `InverseGalois.isRegularInverseGalois_of_card_eq_mul_prime_of_divisors_lt_fortyeight`,
  `InverseGalois.isRegularInverseGalois_of_card_eq_mul_prime_sq_of_divisors_lt_fortyeight`: the
  unbounded families `m * q` and `m * q ^ 2` with `m` below `48`.
* `InverseGalois.isRegularInverseGalois_of_forall_sylow_comm`: **every finite solvable group all of
  whose Sylow subgroups are abelian is a regular Galois group over `ℚ(T)`.**
* `InverseGalois.isRegularInverseGalois_of_isSolvable_of_cubefree`: **every finite solvable group of
  cubefree order is a regular Galois group over `ℚ(T)`.**
* `InverseGalois.isRegularInverseGalois_regularWreathProduct`,
  `InverseGalois.isRegularInverseGalois_iteratedWreathProduct`,
  `InverseGalois.isRegularInverseGalois_sylow_perm`: the regular wreath product of two semiabelian
  groups, its iterates, and **a Sylow `p`-subgroup of a symmetric group on `p ^ n` letters.**
* `InverseGalois.isRegularInverseGalois_of_card_eq_mul_prime_of_lt_twentyfour`,
  `InverseGalois.isRegularInverseGalois_of_card_eq_mul_prime_sq_of_lt_twentyfour`: the same for a
  group whose order is a prime, or the square of a prime, times a cofactor smaller than both that
  prime and `24`.
* `InverseGalois.isRegularInverseGalois_of_commutator_le_center`,
  `InverseGalois.isRegularInverseGalois_of_nilpotencyClass_le_two`: **every finite group of
  nilpotency class at most `2` is a regular Galois group over `ℚ(T)`.**
* `InverseGalois.isRegularInverseGalois_of_card_eq_sq_mul_sq`: the groups of order `p ^ 2 * q ^ 2`.
* `InverseGalois.isRegularInverseGalois_of_card_eq_mul_prime_of_divisors`,
  `InverseGalois.isRegularInverseGalois_of_card_eq_mul_prime_sq_of_divisors`: the size comparison
  replaced by the divisor count that makes the Sylow subgroup unique.
* `InverseGalois.isRegularInverseGalois_of_normal_abelian_of_coprime_index`,
  `InverseGalois.isRegularInverseGalois_of_normal_abelian_sylow`,
  `InverseGalois.isRegularInverseGalois_of_normal_abelian_of_section`: the Schur–Zassenhaus and
  split-extension criteria.
-/

namespace InverseGalois

/-! ### Z-groups -/

/-- **A finite group all of whose Sylow subgroups are cyclic is a regular Galois group over
`ℚ(T)`.**  Such a group is metacyclic, hence semiabelian. -/
theorem isRegularInverseGalois_of_isZGroup (G : Type) [Group G] [Finite G] [IsZGroup G] :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_isZGroup G)

/-- **A finite group all of whose Sylow subgroups are cyclic is a regular Galois group over
`ℚ(T)`**, with the hypothesis spelled out over the primes rather than packaged as an instance. -/
theorem isRegularInverseGalois_of_forall_sylow_isCyclic (G : Type) [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic ↥P) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_forall_sylow_isCyclic G h)

/-- **Every finite group of squarefree order is a regular Galois group over `ℚ(T)`.**  Each Sylow
subgroup of such a group has prime order, so the group is a Z-group. -/
theorem isRegularInverseGalois_of_squarefree_card (G : Type) [Group G] [Finite G]
    (h : Squarefree (Nat.card G)) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_squarefree_card G h)

/-! ### Groups of small order -/

/-- **A finite group with an abelian subgroup whose index is the smallest prime factor of its order
is a regular Galois group over `ℚ(T)`.**  Such a subgroup is automatically normal, and the quotient
is cyclic of prime order. -/
theorem isRegularInverseGalois_of_abelian_of_index_eq_minFac {G : Type} [Group G] [Finite G]
    (N : Subgroup G) (hcomm : ∀ x y : ↥N, x * y = y * x) (hN : N.index = (Nat.card G).minFac) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_abelian_of_index_eq_minFac N hcomm hN)

/-- **Every group of prime order is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_prime {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : Nat.card G = p) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_eq_prime hp h)

/-- **Every group of order `p ^ 2` is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_prime_sq {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : Nat.card G = p ^ 2) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_eq_prime_sq hp h)

/-- **Every group of order `p ^ 3` is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_prime_cube {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : Nat.card G = p ^ 3) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_eq_prime_cube hp h)

/-- **Every group whose order is a product of two primes is a regular Galois group over
`ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_prime_mul_prime {G : Type} [Group G] [Finite G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : Nat.card G = p * q) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_eq_prime_mul_prime hp hq h)

/-- **Every group whose order is `p ^ 2 * q` for distinct primes `p` and `q` is a regular Galois
group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_sq_mul_prime {G : Type} [Group G] [Finite G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_eq_sq_mul_prime hp hq hpq h)

/-- **Every group of order `p ^ 4` is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_prime_pow_four {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : Nat.card G = p ^ 4) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_eq_prime_pow_four hp h)

/-- **Every finite group of order less than `24` is a regular Galois group over `ℚ(T)`.**  Every
order below `24` is a prime, a product of two primes, a prime cube, a prime fourth power, or of the
shape `p ^ 2 * q` for distinct primes, and each of those shapes is semiabelian. -/
theorem isRegularInverseGalois_of_card_lt_twentyfour {G : Type} [Group G] [Finite G]
    (h : Nat.card G < 24) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_lt_twentyfour h)

/-- **Every finite group of order less than `32` other than `24` is a regular Galois group over
`ℚ(T)`.**  The orders between `24` and `32` are again of the shapes the semiabelian criteria
cover, the single order `24` excepted. -/
theorem isRegularInverseGalois_of_card_lt_thirtytwo {G : Type} [Group G] [Finite G]
    (h : Nat.card G < 32) (h24 : Nat.card G ≠ 24) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_lt_thirtytwo h h24)

/-- **Every finite group of order less than `48` other than `24` and `32` is a regular Galois group
over `ℚ(T)`.**  The orders from `33` to `47` are again of shapes the semiabelian criteria cover. -/
theorem isRegularInverseGalois_of_card_lt_fortyeight {G : Type} [Group G] [Finite G]
    (h : Nat.card G < 48) (h24 : Nat.card G ≠ 24) (h32 : Nat.card G ≠ 32) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_lt_fortyeight h h24 h32)

/-- **A group of order `m * q` with `m < 48` other than `24` and `32`, in which `1` is the only
divisor of `m` congruent to `1` modulo the prime `q`, is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_mul_prime_of_divisors_lt_fortyeight {G : Type} [Group G]
    [Finite G] {m q : ℕ} (hq : q.Prime) (hm : ¬ q ∣ m) (hmlt : m < 48) (hm24 : m ≠ 24)
    (hm32 : m ≠ 32) (h : Nat.card G = m * q) (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian
    (IsSemiabelian.of_card_eq_mul_prime_of_divisors_lt_fortyeight hq hm hmlt hm24 hm32 h hdiv)

/-- **A group of order `m * q ^ 2` with `m < 48` other than `24` and `32`, in which `1` is the only
divisor of `m` congruent to `1` modulo the prime `q`, is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_mul_prime_sq_of_divisors_lt_fortyeight {G : Type}
    [Group G] [Finite G] {m q : ℕ} (hq : q.Prime) (hm : ¬ q ∣ m) (hmlt : m < 48) (hm24 : m ≠ 24)
    (hm32 : m ≠ 32) (h : Nat.card G = m * q ^ 2) (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian
    (IsSemiabelian.of_card_eq_mul_prime_sq_of_divisors_lt_fortyeight hq hm hmlt hm24 hm32 h hdiv)

/-- **Every finite solvable group all of whose Sylow subgroups are abelian is a regular Galois
group over `ℚ(T)`.**  Such a group is semiabelian by Thompson's criterion. -/
theorem isRegularInverseGalois_of_forall_sylow_comm {G : Type} [Group G] [Finite G] [IsSolvable G]
    (h : ∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (x y : ↥(P : Subgroup G)), x * y = y * x) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_forall_sylow_comm h)

/-- **Every finite solvable group of cubefree order is a regular Galois group over `ℚ(T)`.**  A
Sylow subgroup of such a group has order `1`, `p` or `p ^ 2`, hence is abelian. -/
theorem isRegularInverseGalois_of_isSolvable_of_cubefree {G : Type} [Group G] [Finite G]
    [IsSolvable G] (h : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ Nat.card G) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_isSolvable_of_cubefree h)

/-! ### Wreath products -/

/-- **The regular wreath product of two finite semiabelian groups is a regular Galois group over
`ℚ(T)`.** -/
theorem isRegularInverseGalois_regularWreathProduct {D Q : Type} [Group D] [Finite D] [Group Q]
    [Finite Q] (hD : IsSemiabelian D) (hQ : IsSemiabelian Q) :
    IsRegularInverseGalois (D ≀ᵣ Q) :=
  isRegularInverseGalois_of_isSemiabelian (hD.regularWreathProduct hQ)

/-- **Every iterated regular wreath product of a finite semiabelian group with itself is a regular
Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_iteratedWreathProduct {G : Type} [Group G] [Finite G]
    (hG : IsSemiabelian G) (n : ℕ) : IsRegularInverseGalois (IteratedWreathProduct G n) :=
  isRegularInverseGalois_of_isSemiabelian (hG.iteratedWreathProduct n)

/-- **A Sylow `p`-subgroup of the symmetric group on `p ^ n` letters is a regular Galois group over
`ℚ(T)`.**  Such a subgroup is an `n`-fold iterated wreath product of cyclic groups of order `p`. -/
theorem isRegularInverseGalois_sylow_perm {p n : ℕ} [Fact p.Prime] {α : Type} [Finite α]
    (hα : Nat.card α = p ^ n) (P : Sylow p (Equiv.Perm α)) :
    IsRegularInverseGalois ↥(P : Subgroup (Equiv.Perm α)) :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.sylow_perm hα P)

/-- **A finite group whose order is a prime `q` times a cofactor smaller than both `q` and `24` is
a regular Galois group over `ℚ(T)`.**  The Sylow `q`-subgroup is unique, hence normal and abelian,
and the quotient by it is semiabelian. -/
theorem isRegularInverseGalois_of_card_eq_mul_prime_of_lt_twentyfour {G : Type} [Group G]
    [Finite G] {m q : ℕ} (hq : q.Prime) (hm : m < 24) (hlt : m < q) (h : Nat.card G = m * q) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian
    (IsSemiabelian.of_card_eq_mul_prime_of_lt_twentyfour hq hm hlt h)

/-- **A finite group whose order is the square of a prime `q` times a cofactor smaller than both
`q` and `24` is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_mul_prime_sq_of_lt_twentyfour {G : Type} [Group G]
    [Finite G] {m q : ℕ} (hq : q.Prime) (hm : m < 24) (hlt : m < q)
    (h : Nat.card G = m * q ^ 2) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian
    (IsSemiabelian.of_card_eq_mul_prime_sq_of_lt_twentyfour hq hm hlt h)

/-- **A finite group whose commutator subgroup is central is a regular Galois group over `ℚ(T)`.**
Adjoining to the centre a generator outside the Frattini subgroup produces an abelian normal
subgroup with a proper supplement, and the induction on the order makes the group semiabelian. -/
theorem isRegularInverseGalois_of_commutator_le_center {G : Type} [Group G] [Finite G]
    (h : commutator G ≤ Subgroup.center G) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_commutator_le_center h)

/-- **A finite group of nilpotency class at most `2` is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_nilpotencyClass_le_two {G : Type} [Group G] [Finite G]
    [Group.IsNilpotent G] (h : Group.nilpotencyClass G ≤ 2) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_nilpotencyClass_le_two h)

/-- **Every group whose order is `p ^ 2 * q ^ 2` for distinct primes `p` and `q` is a regular
Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_sq_mul_sq {G : Type} [Group G] [Finite G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q ^ 2) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_card_eq_sq_mul_sq hp hq hpq h)

/-- **A finite group whose order is a prime `q` times a cofactor `m < 24` no divisor of which,
other than `1`, is congruent to `1` modulo `q` is a regular Galois group over `ℚ(T)`.**  The
divisor condition makes the Sylow `q`-subgroup unique, hence normal and of prime order. -/
theorem isRegularInverseGalois_of_card_eq_mul_prime_of_divisors {G : Type} [Group G] [Finite G]
    {m q : ℕ} (hq : q.Prime) (hm : ¬ q ∣ m) (hmlt : m < 24) (h : Nat.card G = m * q)
    (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian
    (IsSemiabelian.of_card_eq_mul_prime_of_divisors_lt_twentyfour hq hm hmlt h hdiv)

/-- **A finite group whose order is the square of a prime `q` times a cofactor `m < 24` no divisor
of which, other than `1`, is congruent to `1` modulo `q` is a regular Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_card_eq_mul_prime_sq_of_divisors {G : Type} [Group G] [Finite G]
    {m q : ℕ} (hq : q.Prime) (hm : ¬ q ∣ m) (hmlt : m < 24) (h : Nat.card G = m * q ^ 2)
    (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian
    (IsSemiabelian.of_card_eq_mul_prime_sq_of_divisors_lt_twentyfour hq hm hmlt h hdiv)

/-! ### Splitting criteria -/

/-- **The Schur–Zassenhaus criterion for regular realizability.**  A finite group with a normal
abelian subgroup whose order is coprime to its index is a regular Galois group over `ℚ(T)` as soon
as the quotient is. -/
theorem isRegularInverseGalois_of_normal_abelian_of_coprime_index {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hcomm : ∀ x y : ↥N, x * y = y * x)
    (hcop : Nat.Coprime (Nat.card ↥N) N.index) (hQ : IsSemiabelian (G ⧸ N)) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian
    (IsSemiabelian.of_normal_abelian_of_coprime_index N hcomm hcop hQ)

/-- **A finite group with a normal abelian Sylow subgroup of semiabelian quotient is a regular
Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_normal_abelian_sylow {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) [(P : Subgroup G).Normal]
    (hcomm : ∀ x y : ↥(P : Subgroup G), x * y = y * x)
    (hQ : IsSemiabelian (G ⧸ (P : Subgroup G))) : IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian (IsSemiabelian.of_normal_abelian_sylow P hcomm hQ)

/-- **A split extension of a semiabelian group by a finite abelian normal subgroup is a regular
Galois group over `ℚ(T)`.** -/
theorem isRegularInverseGalois_of_normal_abelian_of_section {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hcomm : ∀ x y : ↥N, x * y = y * x) (s : G ⧸ N →* G)
    (hs : ∀ x : G ⧸ N, (QuotientGroup.mk (s x) : G ⧸ N) = x) (hQ : IsSemiabelian (G ⧸ N)) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isSemiabelian
    (IsSemiabelian.of_normal_abelian_of_section N hcomm s hs hQ)

end InverseGalois
