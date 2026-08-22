/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.Main
import InverseGalois.Solvable.SemiabelianHall
import InverseGalois.Solvable.SemiabelianSmall
import InverseGalois.Solvable.SemiabelianZGroup

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
  `InverseGalois.isRegularInverseGalois_of_card_eq_prime_mul_prime`: the groups of order `p`,
  `p ^ 2`, `p ^ 3` and `p * q`.
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
