/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianP2Q
import InverseGalois.Solvable.SemiabelianSmallOrders

/-!
# A normal Sylow subgroup from a divisor count

Write the order of a finite group as `m * q ^ b` with `q` a prime not dividing `m`.  The number of
Sylow `q`-subgroups divides the index `m` and is congruent to `1` modulo `q`, so it is `1` as soon
as the only divisor of `m` congruent to `1` modulo `q` is `1` itself.  The Sylow subgroup is then
normal, and if moreover `b ≤ 2` it is abelian, so the group is semiabelian as soon as the quotient
of order `m` is.

The divisor condition is a statement about the finite set `m.divisors` and is therefore decidable,
which makes the criterion usable at a concrete order by evaluation: the orders `40`, `45`, `75` and
`99` are recorded as examples.

## Main results

* `Semiabelian.card_index_sylow_pow`: the order and index of a Sylow `q`-subgroup of a group of
  order `m * q ^ b` with `q` not dividing `m`.
* `Semiabelian.card_sylow_eq_one_of_forall_mem_divisors`: **the Sylow `q`-subgroup is unique when no
  divisor of `m` other than `1` is congruent to `1` modulo `q`.**
* `IsSemiabelian.of_card_eq_mul_prime_of_forall_mem_divisors`,
  `IsSemiabelian.of_card_eq_mul_prime_sq_of_forall_mem_divisors`: **a group of order `m * q` or
  `m * q ^ 2` satisfying the divisor condition is semiabelian as soon as the groups of order `m`
  are.**
* `IsSemiabelian.of_card_eq_forty`, `IsSemiabelian.of_card_eq_fortyfive`,
  `IsSemiabelian.of_card_eq_seventyfive`, `IsSemiabelian.of_card_eq_ninetynine`: the criterion at
  four concrete orders.
-/

namespace Semiabelian

/-- **The Sylow `q`-subgroups of a group of order `m * q ^ b` with `q` not dividing `m` have order
`q ^ b` and index `m`.**  The exponent of `q` in `m * q ^ b` is `b`, since `q` does not divide `m`,
and the order of a Sylow subgroup is that full prime power; the index is then the complementary
factor. -/
theorem card_index_sylow_pow {G : Type} [Group G] [Finite G] {m q b : ℕ} (hq : q.Prime)
    (hm : ¬ q ∣ m) (h : Nat.card G = m * q ^ b) (Q : Sylow q G) :
    Nat.card ↥(Q : Subgroup G) = q ^ b ∧ (Q : Subgroup G).index = m := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  have hfac : (Nat.card G).factorization q = b := by
    rw [h, Nat.factorization_mul hm0 (pow_ne_zero b hq.pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm, hq.factorization_pow]
    simp
  have hcard : Nat.card ↥(Q : Subgroup G) = q ^ b := by rw [Q.card_eq_multiplicity, hfac]
  refine ⟨hcard, ?_⟩
  have hmul := (Q : Subgroup G).card_mul_index
  rw [hcard, h] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos b) (by rw [hmul]; ring)

/-- **A group of order `m * q ^ b` has a single Sylow `q`-subgroup whenever `1` is the only divisor
of `m` congruent to `1` modulo `q`.**  The number of Sylow `q`-subgroups divides the index `m` and
is congruent to `1` modulo `q`, so the hypothesis pins it down. -/
theorem card_sylow_eq_one_of_forall_mem_divisors {G : Type} [Group G] [Finite G] {m q b : ℕ}
    (hq : q.Prime) (hm : ¬ q ∣ m) (h : Nat.card G = m * q ^ b)
    (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) : Nat.card (Sylow q G) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨-, hindex⟩ := card_index_sylow_pow hq hm h Q
  have hdvd : Nat.card (Sylow q G) ∣ m := hindex ▸ Sylow.card_dvd_index Q
  have hmod : Nat.card (Sylow q G) % q = 1 := by
    have hcong := card_sylow_modEq_one q G
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hq.one_lt] at hcong
  exact hdiv _ (Nat.mem_divisors.mpr ⟨hdvd, hm0⟩) hmod

end Semiabelian

namespace IsSemiabelian

/-- **A group of order `m * q` in which `1` is the only divisor of `m` congruent to `1` modulo the
prime `q` is semiabelian as soon as the groups of order `m` are.**  The count makes the Sylow
`q`-subgroup unique, hence normal, and it is cyclic of prime order, so the covering criterion
applies with the quotient of order `m`. -/
theorem of_card_eq_mul_prime_of_forall_mem_divisors {G : Type} [Group G] [Finite G] {m q : ℕ}
    (hq : q.Prime) (hm : ¬ q ∣ m) (h : Nat.card G = m * q)
    (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1)
    (hquot : ∀ (H : Type) [Group H] [Finite H], Nat.card H = m → IsSemiabelian H) :
    IsSemiabelian G := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h' : Nat.card G = m * q ^ 1 := by rwa [pow_one]
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨hcard, hindex⟩ := Semiabelian.card_index_sylow_pow hq hm h' Q
  haveI : (Q : Subgroup G).Normal :=
    Semiabelian.normal_of_card_sylow_eq_one
      (Semiabelian.card_sylow_eq_one_of_forall_mem_divisors hq hm h' hdiv) Q
  rw [pow_one] at hcard
  haveI : IsCyclic ↥(Q : Subgroup G) := isCyclic_of_prime_card hcard
  refine of_normal_abelian_sylow Q (fun x y => ?_) ?_
  · exact (IsCyclic.commutative (α := ↥(Q : Subgroup G))).comm x y
  · exact hquot (G ⧸ (Q : Subgroup G)) (by rw [← Subgroup.index_eq_card]; exact hindex)

/-- **A group of order `m * q ^ 2` in which `1` is the only divisor of `m` congruent to `1` modulo
the prime `q` is semiabelian as soon as the groups of order `m` are.**  The count makes the Sylow
`q`-subgroup unique, hence normal, and a group of order the square of a prime is abelian. -/
theorem of_card_eq_mul_prime_sq_of_forall_mem_divisors {G : Type} [Group G] [Finite G] {m q : ℕ}
    (hq : q.Prime) (hm : ¬ q ∣ m) (h : Nat.card G = m * q ^ 2)
    (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1)
    (hquot : ∀ (H : Type) [Group H] [Finite H], Nat.card H = m → IsSemiabelian H) :
    IsSemiabelian G := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨hcard, hindex⟩ := Semiabelian.card_index_sylow_pow hq hm h Q
  haveI : (Q : Subgroup G).Normal :=
    Semiabelian.normal_of_card_sylow_eq_one
      (Semiabelian.card_sylow_eq_one_of_forall_mem_divisors hq hm h hdiv) Q
  refine of_normal_abelian_sylow Q (IsPGroup.commutative_of_card_eq_prime_sq hcard) ?_
  exact hquot (G ⧸ (Q : Subgroup G)) (by rw [← Subgroup.index_eq_card]; exact hindex)

/-- **A group of order `m * q` with `m < 24` in which `1` is the only divisor of `m` congruent to
`1` modulo the prime `q` is semiabelian.**  Every group of order less than `24` is semiabelian, so
the quotient hypothesis is automatic. -/
theorem of_card_eq_mul_prime_of_divisors_lt_twentyfour {G : Type} [Group G] [Finite G] {m q : ℕ}
    (hq : q.Prime) (hm : ¬ q ∣ m) (hmlt : m < 24) (h : Nat.card G = m * q)
    (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) : IsSemiabelian G :=
  of_card_eq_mul_prime_of_forall_mem_divisors hq hm h hdiv
    fun _ _ _ hH => of_card_lt_twentyfour (hH ▸ hmlt)

/-- **A group of order `m * q ^ 2` with `m < 24` in which `1` is the only divisor of `m` congruent
to `1` modulo the prime `q` is semiabelian.** -/
theorem of_card_eq_mul_prime_sq_of_divisors_lt_twentyfour {G : Type} [Group G] [Finite G] {m q : ℕ}
    (hq : q.Prime) (hm : ¬ q ∣ m) (hmlt : m < 24) (h : Nat.card G = m * q ^ 2)
    (hdiv : ∀ d ∈ m.divisors, d % q = 1 → d = 1) : IsSemiabelian G :=
  of_card_eq_mul_prime_sq_of_forall_mem_divisors hq hm h hdiv
    fun _ _ _ hH => of_card_lt_twentyfour (hH ▸ hmlt)

/-- **Every group of order `40` is semiabelian.**  No divisor of `8` other than `1` is congruent to
`1` modulo `5`, so the Sylow `5`-subgroup is normal, and the quotient has order `8`. -/
theorem of_card_eq_forty {G : Type} [Group G] [Finite G] (h : Nat.card G = 40) :
    IsSemiabelian G :=
  of_card_eq_mul_prime_of_divisors_lt_twentyfour (m := 8) (q := 5) (by norm_num) (by norm_num)
    (by norm_num) (h.trans (by norm_num)) (by decide)

/-- **Every group of order `45` is semiabelian.**  No divisor of `9` other than `1` is congruent to
`1` modulo `5`, so the Sylow `5`-subgroup is normal, and the quotient has order `9`. -/
theorem of_card_eq_fortyfive {G : Type} [Group G] [Finite G] (h : Nat.card G = 45) :
    IsSemiabelian G :=
  of_card_eq_mul_prime_of_divisors_lt_twentyfour (m := 9) (q := 5) (by norm_num) (by norm_num)
    (by norm_num) (h.trans (by norm_num)) (by decide)

/-- **Every group of order `75` is semiabelian.**  No divisor of `3` other than `1` is congruent to
`1` modulo `5`, so the Sylow `5`-subgroup is normal; it has order `25` and is therefore abelian,
and the quotient has order `3`. -/
theorem of_card_eq_seventyfive {G : Type} [Group G] [Finite G] (h : Nat.card G = 75) :
    IsSemiabelian G :=
  of_card_eq_mul_prime_sq_of_divisors_lt_twentyfour (m := 3) (q := 5) (by norm_num) (by norm_num)
    (by norm_num) (h.trans (by norm_num)) (by decide)

/-- **Every group of order `99` is semiabelian.**  No divisor of `9` other than `1` is congruent to
`1` modulo `11`, so the Sylow `11`-subgroup is normal, and the quotient has order `9`. -/
theorem of_card_eq_ninetynine {G : Type} [Group G] [Finite G] (h : Nat.card G = 99) :
    IsSemiabelian G :=
  of_card_eq_mul_prime_of_divisors_lt_twentyfour (m := 9) (q := 11) (by norm_num) (by norm_num)
    (by norm_num) (h.trans (by norm_num)) (by decide)

end IsSemiabelian
