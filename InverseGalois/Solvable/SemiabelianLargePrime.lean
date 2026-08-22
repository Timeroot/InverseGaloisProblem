/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianHall
import InverseGalois.Solvable.SemiabelianP2Q
import InverseGalois.Solvable.SemiabelianSmallOrders

/-!
# A prime larger than the rest of the order

If the order of a finite group `G` factors as `m * q` with `q` a prime exceeding `m`, then the
Sylow `q`-subgroups of `G` are forced to be unique.  Indeed their number divides the index `m` of
one of them and is congruent to `1` modulo `q`; being at most `m`, it is smaller than `q`, and the
only such number congruent to `1` modulo `q` is `1` itself.

The unique Sylow `q`-subgroup is therefore normal, and it is cyclic of prime order, hence abelian.
Schur–Zassenhaus splits it off, so `G` is semiabelian as soon as the quotient of order `m` is.
Combined with the classification of the orders below `24`, this covers every order of the shape
`m * q` with `m < 24 < q`.  The same counting works when the prime occurs to a higher power, and
for the square of a prime the Sylow subgroup is again abelian, so the orders `m * q ^ 2` with
`m < 24 < q` are covered as well.

## Main results

* `Semiabelian.card_sylow_eq_one_of_lt`: **a prime larger than the cofactor of the order has a
  unique Sylow subgroup.**
* `IsSemiabelian.of_card_eq_mul_prime_of_lt`: **a finite group of order `m * q` with `q` a prime
  larger than `m` is semiabelian as soon as the groups of order `m` are.**
* `IsSemiabelian.of_card_eq_mul_prime_of_lt_twentyfour`: **a finite group of order `m * q` with
  `q` a prime and `m < 24`, `m < q`, is semiabelian.**
* `IsSemiabelian.of_card_eq_mul_prime_sq_of_lt`,
  `IsSemiabelian.of_card_eq_mul_prime_sq_of_lt_twentyfour`: the same with the prime appearing
  squared, the Sylow subgroup then having order `q ^ 2` and being abelian for that reason.
-/

namespace Semiabelian

/-- **The order and index of a Sylow subgroup for a prime larger than the cofactor.**  The prime
`q` cannot divide the cofactor `m`, being larger than it, so the full power of `q` in `m * q` is
`q` itself. -/
theorem card_index_sylow_of_lt {G : Type} [Group G] [Finite G] {m q : ℕ} (hq : q.Prime)
    (hlt : m < q) (h : Nat.card G = m * q) (Q : Sylow q G) :
    Nat.card ↥(Q : Subgroup G) = q ∧ (Q : Subgroup G).index = m := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  have hqm : ¬ q ∣ m := fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd)
    (not_le.mpr hlt)
  have hfac : (Nat.card G).factorization q = 1 := by
    rw [h, Nat.factorization_mul hm0 hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqm, hq.factorization, Finsupp.single_eq_same,
      zero_add]
  have hcard : Nat.card ↥(Q : Subgroup G) = q := by
    rw [Q.card_eq_multiplicity, hfac, pow_one]
  refine ⟨hcard, ?_⟩
  have hmul : q * (Q : Subgroup G).index = q * m := by
    have hci := (Q : Subgroup G).card_mul_index
    rw [hcard, h] at hci
    calc q * (Q : Subgroup G).index = m * q := hci
      _ = q * m := Nat.mul_comm m q
  exact Nat.eq_of_mul_eq_mul_left hq.pos hmul

/-- **A prime larger than the cofactor of the order has a unique Sylow subgroup.**  The number of
Sylow `q`-subgroups divides the index `m`, hence is smaller than `q`, and it is congruent to `1`
modulo `q`. -/
theorem card_sylow_eq_one_of_lt {G : Type} [Group G] [Finite G] {m q : ℕ} (hq : q.Prime)
    (hlt : m < q) (h : Nat.card G = m * q) : Nat.card (Sylow q G) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨-, hindex⟩ := card_index_sylow_of_lt hq hlt h Q
  have hdvd : Nat.card (Sylow q G) ∣ m := hindex ▸ Q.card_dvd_index
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  have hle : Nat.card (Sylow q G) ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  have hmod : Nat.card (Sylow q G) % q = 1 % q := card_sylow_modEq_one q G
  rwa [Nat.mod_eq_of_lt (lt_of_le_of_lt hle hlt), Nat.mod_eq_of_lt hq.one_lt] at hmod

/-- **The order and index of a Sylow subgroup for a prime power whose prime exceeds the cofactor.**
The prime `q` cannot divide the cofactor `m`, being larger than it, so the full power of `q` in
`m * q ^ k` is `q ^ k`. -/
theorem card_index_sylow_pow_of_lt {G : Type} [Group G] [Finite G] {m q k : ℕ} (hq : q.Prime)
    (hlt : m < q) (h : Nat.card G = m * q ^ k) (Q : Sylow q G) :
    Nat.card ↥(Q : Subgroup G) = q ^ k ∧ (Q : Subgroup G).index = m := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  have hqm : ¬ q ∣ m := fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd)
    (not_le.mpr hlt)
  have hfac : (Nat.card G).factorization q = k := by
    rw [h, Nat.factorization_mul hm0 (pow_ne_zero k hq.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqm, Nat.factorization_pow_self hq, zero_add]
  have hcard : Nat.card ↥(Q : Subgroup G) = q ^ k := by
    rw [Q.card_eq_multiplicity, hfac]
  refine ⟨hcard, ?_⟩
  have hmul : q ^ k * (Q : Subgroup G).index = q ^ k * m := by
    have hci := (Q : Subgroup G).card_mul_index
    rw [hcard, h] at hci
    calc q ^ k * (Q : Subgroup G).index = m * q ^ k := hci
      _ = q ^ k * m := Nat.mul_comm m (q ^ k)
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hq.pos) hmul

/-- **A prime power whose prime exceeds the cofactor of the order has a unique Sylow subgroup.** -/
theorem card_sylow_eq_one_of_lt_pow {G : Type} [Group G] [Finite G] {m q k : ℕ} (hq : q.Prime)
    (hlt : m < q) (h : Nat.card G = m * q ^ k) : Nat.card (Sylow q G) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨-, hindex⟩ := card_index_sylow_pow_of_lt hq hlt h Q
  have hdvd : Nat.card (Sylow q G) ∣ m := hindex ▸ Q.card_dvd_index
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  have hle : Nat.card (Sylow q G) ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  have hmod : Nat.card (Sylow q G) % q = 1 % q := card_sylow_modEq_one q G
  rwa [Nat.mod_eq_of_lt (lt_of_le_of_lt hle hlt), Nat.mod_eq_of_lt hq.one_lt] at hmod

end Semiabelian

namespace IsSemiabelian

/-- **A finite group of order `m * q` with `q` a prime larger than `m` is semiabelian as soon as
the groups of order `m` are.**  The Sylow `q`-subgroup is unique, hence normal, and it is cyclic of
prime order; the quotient by it has order `m`. -/
theorem of_card_eq_mul_prime_of_lt {G : Type} [Group G] [Finite G] {m q : ℕ} (hq : q.Prime)
    (hlt : m < q) (h : Nat.card G = m * q)
    (hquot : ∀ (H : Type) [Group H] [Finite H], Nat.card H = m → IsSemiabelian H) :
    IsSemiabelian G := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨hcard, hindex⟩ := Semiabelian.card_index_sylow_of_lt hq hlt h Q
  haveI : (Q : Subgroup G).Normal :=
    Semiabelian.normal_of_card_sylow_eq_one (Semiabelian.card_sylow_eq_one_of_lt hq hlt h) Q
  haveI : IsCyclic ↥(Q : Subgroup G) := isCyclic_of_prime_card hcard
  refine of_normal_abelian_sylow Q (fun x y => ?_) ?_
  · exact (IsCyclic.commutative (α := ↥(Q : Subgroup G))).comm x y
  · exact hquot (G ⧸ (Q : Subgroup G)) (by rw [← Subgroup.index_eq_card]; exact hindex)

/-- **A finite group whose order is a prime `q` times a cofactor smaller than both `q` and `24` is
semiabelian.**  The cofactor is the order of the quotient by the normal Sylow `q`-subgroup, and
every group of order less than `24` is semiabelian. -/
theorem of_card_eq_mul_prime_of_lt_twentyfour {G : Type} [Group G] [Finite G] {m q : ℕ}
    (hq : q.Prime) (hm : m < 24) (hlt : m < q) (h : Nat.card G = m * q) : IsSemiabelian G :=
  of_card_eq_mul_prime_of_lt hq hlt h fun _ _ _ hH => of_card_lt_twentyfour (hH ▸ hm)

/-- **A finite group of order `m * q ^ 2` with `q` a prime larger than `m` is semiabelian as soon
as the groups of order `m` are.**  The Sylow `q`-subgroup is unique, hence normal, and a group of
order the square of a prime is abelian. -/
theorem of_card_eq_mul_prime_sq_of_lt {G : Type} [Group G] [Finite G] {m q : ℕ} (hq : q.Prime)
    (hlt : m < q) (h : Nat.card G = m * q ^ 2)
    (hquot : ∀ (H : Type) [Group H] [Finite H], Nat.card H = m → IsSemiabelian H) :
    IsSemiabelian G := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨hcard, hindex⟩ := Semiabelian.card_index_sylow_pow_of_lt hq hlt h Q
  haveI : (Q : Subgroup G).Normal :=
    Semiabelian.normal_of_card_sylow_eq_one (Semiabelian.card_sylow_eq_one_of_lt_pow hq hlt h) Q
  refine of_normal_abelian_sylow Q (IsPGroup.commutative_of_card_eq_prime_sq hcard) ?_
  exact hquot (G ⧸ (Q : Subgroup G)) (by rw [← Subgroup.index_eq_card]; exact hindex)

/-- **A finite group whose order is the square of a prime `q` times a cofactor smaller than both
`q` and `24` is semiabelian.** -/
theorem of_card_eq_mul_prime_sq_of_lt_twentyfour {G : Type} [Group G] [Finite G] {m q : ℕ}
    (hq : q.Prime) (hm : m < 24) (hlt : m < q) (h : Nat.card G = m * q ^ 2) : IsSemiabelian G :=
  of_card_eq_mul_prime_sq_of_lt hq hlt h fun _ _ _ hH => of_card_lt_twentyfour (hH ▸ hm)

end IsSemiabelian
