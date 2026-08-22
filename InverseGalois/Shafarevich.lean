/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.NilpotentSylowTwo
import InverseGalois.Rigidity.RET.Specialization
import InverseGalois.Rigidity.RET.Wreath.SmallGroups

/-!
# The nilpotent case of Shafarevich's theorem

Shafarevich's theorem is approached here along two independent routes that meet on the nilpotent
groups.  The arithmetic route is the Scholz–Reichardt induction of `InverseGalois/CFT/Scholz/`,
which realises every finite `ℓ`-group for odd `ℓ` once its central embedding step is granted, and
hence every finite nilpotent group of odd order.  The geometric route is the Dentzer–Stoll wreath
product construction of `InverseGalois/Rigidity/RET/Wreath/`, which realises every finite
semiabelian group regularly over `ℚ(T)`, with no arithmetic input at all and no restriction on the
primes involved.

A finite nilpotent group is the direct product of its Sylow subgroups, and realizability over `ℚ`
is closed under products of groups of coprime order, so the two routes may be applied prime by
prime.  The arithmetic route covers every odd prime; the prime `2`, which the Scholz–Reichardt
argument excludes, is left to the geometric route.  The result is that a finite nilpotent group is
a Galois group over `ℚ` — granted the odd central step — as soon as its Sylow `2`-subgroup is
semiabelian.  That is a mild condition on a `2`-group: it holds for the abelian ones, for the
cyclic ones, for the metacyclic ones, and for all of them of order at most `8`.

## Main results

* `InverseGalois.isInverseGalois_of_isNilpotent_of_semiabelian_sylow_two`: **granted the central
  step for the odd primes, a finite nilpotent group whose Sylow `2`-subgroups are semiabelian is a
  Galois group over `ℚ`.**
* `InverseGalois.isInverseGalois_of_isNilpotent_of_abelian_sylow_two`,
  `InverseGalois.isInverseGalois_of_isNilpotent_of_cyclic_sylow_two`: the abelian and cyclic cases
  of the hypothesis on the prime `2`.
* `InverseGalois.isInverseGalois_of_isNilpotent_of_not_dvd_sixteen`: **granted the central step for
  the odd primes, every finite nilpotent group of order not divisible by `16` is a Galois group
  over `ℚ`.**
-/

namespace InverseGalois

open CFT

/-- **Granted the central step for the odd primes, a finite nilpotent group whose Sylow
`2`-subgroups are semiabelian is a Galois group over `ℚ`.**  The Sylow subgroups at the odd primes
are realised by the Scholz–Reichardt induction and the one at the prime `2` by the Dentzer–Stoll
construction, which realises a semiabelian group regularly over `ℚ(T)` and hence, by
specialization, over `ℚ`. -/
theorem isInverseGalois_of_isNilpotent_of_semiabelian_sylow_two
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] (h2 : ∀ P : Sylow 2 G, IsSemiabelian ↥(P : Subgroup G)) :
    IsInverseGalois G :=
  isInverseGalois_of_isNilpotent_of_sylow_two hstep G fun P =>
    _root_.IsRegularInverseGalois.isInverseGalois
      (isRegularInverseGalois_of_isSemiabelian (h2 P))

/-- **Granted the central step for the odd primes, a finite nilpotent group whose Sylow
`2`-subgroups are abelian is a Galois group over `ℚ`.** -/
theorem isInverseGalois_of_isNilpotent_of_abelian_sylow_two
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    [Group.IsNilpotent G]
    (h2 : ∀ (P : Sylow 2 G) (x y : ↥(P : Subgroup G)), x * y = y * x) :
    IsInverseGalois G :=
  isInverseGalois_of_isNilpotent_of_semiabelian_sylow_two hstep G fun P =>
    IsSemiabelian.of_mul_comm (h2 P)

/-- **Granted the central step for the odd primes, a finite nilpotent group whose Sylow
`2`-subgroups are cyclic is a Galois group over `ℚ`.**  A cyclic group is abelian. -/
theorem isInverseGalois_of_isNilpotent_of_cyclic_sylow_two
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] (h2 : ∀ P : Sylow 2 G, IsCyclic ↥(P : Subgroup G)) :
    IsInverseGalois G := by
  refine isInverseGalois_of_isNilpotent_of_abelian_sylow_two hstep G fun P x y => ?_
  haveI := h2 P
  exact (IsCyclic.commutative (α := ↥(P : Subgroup G))).comm x y

/-- **Granted the central step for the odd primes, every finite nilpotent group of order not
divisible by `16` is a Galois group over `ℚ`.**  The order of a Sylow `2`-subgroup is a power of
`2` dividing the order of the group, so it is at most `8`, and a group of order `1`, `2`, `4` or
`8` is semiabelian. -/
theorem isInverseGalois_of_isNilpotent_of_not_dvd_sixteen
    (hstep : ∀ q : ℕ, q.Prime → Odd q → IsCentralStepSolvable q) (G : Type) [Group G] [Finite G]
    [Group.IsNilpotent G] (h16 : ¬ (16 ∣ Nat.card G)) : IsInverseGalois G := by
  refine isInverseGalois_of_isNilpotent_of_semiabelian_sylow_two hstep G fun P => ?_
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdvd : (2 : ℕ) ^ n ∣ Nat.card G := by
    rw [← hn]
    exact Subgroup.card_subgroup_dvd_card _
  have hle : n ≤ 3 := by
    by_contra hc
    push_neg at hc
    exact h16 (dvd_trans (by rw [show (16 : ℕ) = 2 ^ 4 by norm_num]; exact pow_dvd_pow 2 hc) hdvd)
  interval_cases n
  · haveI : Subsingleton ↥(P : Subgroup G) :=
      (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
    exact .of_subsingleton _
  · exact IsSemiabelian.of_card_eq_prime Nat.prime_two (by simpa using hn)
  · exact IsSemiabelian.of_card_eq_prime_sq Nat.prime_two hn
  · exact IsSemiabelian.of_card_eq_prime_cube Nat.prime_two hn

end InverseGalois
