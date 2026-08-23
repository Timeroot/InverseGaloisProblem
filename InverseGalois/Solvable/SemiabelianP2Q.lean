/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianHall
import InverseGalois.Solvable.SemiabelianSmall

/-!
# Groups of order `p ^ 2 * q` are semiabelian

A finite group whose order is `p ^ 2 * q` for two distinct primes `p` and `q` always has a normal
Sylow subgroup, and this is exactly the input that the splitting criteria of
`InverseGalois.Solvable.SemiabelianHall` need: a normal Sylow subgroup is abelian here, being of
order `p ^ 2`, `p` or `q`, and the quotient by it has order `q` or `p ^ 2`, hence is semiabelian by
`InverseGalois.Solvable.SemiabelianSmall`.  Since a Sylow subgroup is a Hall subgroup, the
Schur–Zassenhaus splitting applies and the extension is semiabelian.

The group-theoretic heart of the file is Sylow's counting theorem.  Write `n_p` and `n_q` for the
numbers of Sylow `p`- and Sylow `q`-subgroups; each is congruent to `1` modulo its own prime and
divides the index of the corresponding Sylow subgroup, which here is `q` respectively `p ^ 2`.

If `q < p`, then `n_p` divides the prime `q`, so it is `1` or `q`; the value `q` is excluded because
`q` lies strictly between `1` and `p`, so it cannot be congruent to `1` modulo `p`.  Hence the Sylow
`p`-subgroup is normal.

If `p < q`, then `n_q` is a power `p ^ k` with `k ≤ 2`.  The value `p` is excluded exactly as
before.  The value `p ^ 2` forces `q ∣ p ^ 2 - 1 = (p - 1) * (p + 1)`; the prime `q` cannot divide
`p - 1`, which is positive and smaller than `q`, so it divides `p + 1`, and `p < q ≤ p + 1` pins
`q = p + 1`.  Consecutive primes of this shape are only `2` and `3`, so the sole survivor is a group
of order `12` with four Sylow `3`-subgroups.

That last configuration is settled by counting elements.  Every nonidentity element of a Sylow
`3`-subgroup generates it, since the subgroup has prime order `3`; consequently two distinct Sylow
`3`-subgroups meet only in the identity, and the four of them account for exactly `4 * 2 = 8`
elements.  A Sylow `2`-subgroup has `4` elements, none of them among those `8` because the order of
an element lying in both a Sylow `2`- and a Sylow `3`-subgroup divides both `4` and `3`.  The four
remaining elements of the group therefore constitute every Sylow `2`-subgroup at once, so there is
only one and it is normal.

## Main results

* `Semiabelian.exists_normal_sylow_of_card_eq_sq_mul_prime` — **a finite group of order `p ^ 2 * q`
  for distinct primes `p` and `q` has a normal Sylow `p`-subgroup or a normal Sylow `q`-subgroup.**
* `Semiabelian.subsingleton_sylow_two_of_card_eq_twelve` — a group of order `12` with four Sylow
  `3`-subgroups has a unique Sylow `2`-subgroup.
* `IsSemiabelian.of_card_eq_sq_mul_prime` — **every finite group of order `p ^ 2 * q`, for distinct
  primes `p` and `q`, is semiabelian.**
* `IsSemiabelian.of_card_eq_twelve` — every group of order `12` is semiabelian.
-/

namespace Semiabelian

/-- **The Sylow `p`-subgroups of a group of order `p ^ 2 * q` have order `p ^ 2` and index `q`.**
The order of a Sylow subgroup is the full power of `p` dividing the group order, and the exponent of
`p` in `p ^ 2 * q` is `2` because the prime `q` is different from `p`; the index is then read off
from the product of order and index. -/
theorem card_index_sylow_prime_sq {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q) (P : Sylow p G) :
    Nat.card ↥(P : Subgroup G) = p ^ 2 ∧ (P : Subgroup G).index = q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfac : (Nat.card G).factorization p = 2 := by
    rw [h, Nat.factorization_mul (pow_ne_zero 2 hp.pos.ne') hq.pos.ne', Finsupp.add_apply,
      hp.factorization_pow, hq.factorization]
    simp [hpq]
  have hcard : Nat.card ↥(P : Subgroup G) = p ^ 2 := by rw [P.card_eq_multiplicity, hfac]
  refine ⟨hcard, ?_⟩
  have hmul := (P : Subgroup G).card_mul_index
  rw [hcard, h] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hmul

/-- **The Sylow `q`-subgroups of a group of order `p ^ 2 * q` have order `q` and index `p ^ 2`.**
The exponent of `q` in `p ^ 2 * q` is `1`, since `p` differs from `q`, so a Sylow `q`-subgroup has
prime order `q`, and its index is the complementary factor `p ^ 2`. -/
theorem card_index_sylow_prime {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q) (Q : Sylow q G) :
    Nat.card ↥(Q : Subgroup G) = q ∧ (Q : Subgroup G).index = p ^ 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hfac : (Nat.card G).factorization q = 1 := by
    rw [h, Nat.factorization_mul (pow_ne_zero 2 hp.pos.ne') hq.pos.ne', Finsupp.add_apply,
      hp.factorization_pow, hq.factorization]
    simp [hpq]
  have hcard : Nat.card ↥(Q : Subgroup G) = q := by
    rw [Q.card_eq_multiplicity, hfac, pow_one]
  refine ⟨hcard, ?_⟩
  have hmul := (Q : Subgroup G).card_mul_index
  rw [hcard, h] at hmul
  exact Nat.eq_of_mul_eq_mul_left hq.pos (by rw [hmul]; ring)

/-- **A prime for which there is a single Sylow subgroup has a normal Sylow subgroup.**  All Sylow
`p`-subgroups are conjugate, so when there is only one of them it is fixed by conjugation, that is,
it is normal — indeed characteristic. -/
theorem normal_of_card_sylow_eq_one {G : Type} [Group G] [Finite G] {p : ℕ}
    (hn : Nat.card (Sylow p G) = 1) (P : Sylow p G) : (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hn).1
  exact Sylow.normal_of_subsingleton P

/-- **Two primes `p < q` with `q` dividing `p ^ 2 - 1` are `2` and `3`.**  Writing
`p ^ 2 - 1 = (p - 1) * (p + 1)`, the prime `q` divides one of the two factors; it cannot divide the
positive number `p - 1`, which is smaller than `q`, so it divides `p + 1` and therefore equals
`p + 1`.  Two consecutive integers cannot both be odd, so the smaller of the two consecutive primes
is even, hence `p = 2` and `q = 3`. -/
theorem eq_two_and_three_of_dvd_sq_sub_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q)
    (hdvd : q ∣ p ^ 2 - 1) : p = 2 ∧ q = 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hfac : (m + 2) ^ 2 - 1 = (m + 1) * (m + 3) := by
    have hsq : (m + 2) ^ 2 = (m + 1) * (m + 3) + 1 := by ring
    omega
  rw [hfac] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with hd | hd
  · have := Nat.le_of_dvd (by omega) hd
    omega
  · have hle := Nat.le_of_dvd (by omega) hd
    have hq3 : q = m + 3 := by omega
    rcases hp.eq_two_or_odd' with h2 | ⟨a, ha⟩
    · omega
    · rcases hq.eq_two_or_odd' with h2' | ⟨b, hb⟩
      · omega
      · omega

/-- **A group of order `12` with four Sylow `3`-subgroups has a unique Sylow `2`-subgroup.**  Each
Sylow `3`-subgroup has prime order `3`, so it is generated by any of its two nonidentity elements;
two distinct ones therefore intersect trivially and the four subgroups contribute `4 * 2 = 8`
distinct elements.  A Sylow `2`-subgroup has order `4` and avoids all of them, since an element
common to a Sylow `2`- and a Sylow `3`-subgroup has order dividing both `4` and `3`.  Only four
elements of the group are left, so every Sylow `2`-subgroup consists precisely of those. -/
theorem subsingleton_sylow_two_of_card_eq_twelve {G : Type} [Group G] [Finite G]
    (h : Nat.card G = 12) (h3 : Nat.card (Sylow 3 G) = 4) : Subsingleton (Sylow 2 G) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hG12 : Nat.card G = 2 ^ 2 * 3 := by rw [h]; norm_num
  have hc3 : ∀ P : Sylow 3 G, Nat.card ↥(P : Subgroup G) = 3 := fun P =>
    (card_index_sylow_prime Nat.prime_two Nat.prime_three (by norm_num) hG12 P).1
  have hc2 : ∀ S : Sylow 2 G, Nat.card ↥(S : Subgroup G) = 4 := fun S =>
    ((card_index_sylow_prime_sq Nat.prime_two Nat.prime_three (by norm_num) hG12 S).1).trans
      (by norm_num)
  have hgen : ∀ (P : Sylow 3 G) (g : G), g ∈ (P : Subgroup G) → g ≠ 1 →
      Subgroup.zpowers g = (P : Subgroup G) := by
    intro P g hg hg1
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_
    have hdvd : Nat.card ↥(Subgroup.zpowers g) ∣ Nat.card ↥(P : Subgroup G) :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hg)
    rw [hc3 P, Nat.card_zpowers] at hdvd ⊢
    have h1 : orderOf g ≠ 1 := by simpa [orderOf_eq_one_iff] using hg1
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h' | h'
    · exact absurd h' h1
    · omega
  set t : Sylow 3 G → Finset G := fun P => ((P : Subgroup G) : Set G).toFinset.erase 1 with ht
  have htcard : ∀ P : Sylow 3 G, (t P).card = 2 := by
    intro P
    have hmem : (1 : G) ∈ ((P : Subgroup G) : Set G).toFinset := by simp
    rw [ht]
    simp only
    rw [Finset.card_erase_of_mem hmem, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    simp only [SetLike.coe_sort_coe]
    rw [hc3 P]
  have hdisj : (↑(Finset.univ : Finset (Sylow 3 G)) : Set (Sylow 3 G)).PairwiseDisjoint t := by
    intro P _ P' _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro g hg hg'
    rw [ht] at hg hg'
    simp only [Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hg hg'
    exact hne (Sylow.ext ((hgen P g hg.2 hg.1).symm.trans (hgen P' g hg'.2 hg'.1)))
  have hUcard : (Finset.univ.biUnion t).card = 8 := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl fun P _ => htcard P]
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, h3]
  have hS : ∀ S : Sylow 2 G, ((S : Subgroup G) : Set G).toFinset = (Finset.univ.biUnion t)ᶜ := by
    intro S
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro g hg
      simp only [Set.mem_toFinset, SetLike.mem_coe] at hg
      simp only [Finset.mem_compl, Finset.mem_biUnion]
      rintro ⟨P, -, hgP⟩
      rw [ht] at hgP
      simp only [Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hgP
      have hd3 : Nat.card ↥(Subgroup.zpowers g) ∣ 3 := by
        rw [← hc3 P]; exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hgP.2)
      have hd4 : Nat.card ↥(Subgroup.zpowers g) ∣ 4 := by
        rw [← hc2 S]; exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hg)
      have h1 : Nat.card ↥(Subgroup.zpowers g) = 1 := by simpa using Nat.dvd_gcd hd3 hd4
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
      exact hgP.1 h1
    · rw [Finset.card_compl, hUcard, Set.toFinset_card, ← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card]
      simp only [SetLike.coe_sort_coe]
      rw [hc2 S, h]
  refine ⟨fun S₁ S₂ => Sylow.ext (SetLike.coe_injective ?_)⟩
  rw [← Set.toFinset_inj, hS S₁, hS S₂]

/-- **A finite group of order `p ^ 2 * q`, for distinct primes `p` and `q`, has a normal Sylow
subgroup.**  When `q < p` the number of Sylow `p`-subgroups divides the index `q` and is congruent
to `1` modulo `p`, and `q` itself is too small to be congruent to `1`, so that number is `1`.  When
`p < q` the number of Sylow `q`-subgroups is a power `p ^ k` with `k ≤ 2` congruent to `1` modulo
`q`; the exponent `k = 1` is excluded by size and `k = 2` forces `q` to divide `p ^ 2 - 1`, hence
`p = 2` and `q = 3`, a group of order `12` whose four Sylow `3`-subgroups leave room for a single
Sylow `2`-subgroup. -/
theorem exists_normal_sylow_of_card_eq_sq_mul_prime {G : Type} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q) :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ∨ (∃ Q : Sylow q G, (Q : Subgroup G).Normal) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q G))
    have hdvd : Nat.card (Sylow q G) ∣ p ^ 2 := by
      have hind := Q.card_dvd_index
      rwa [(card_index_sylow_prime hp hq hpq h Q).2] at hind
    have hmod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
    obtain ⟨k, hk2, hkk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases k
    · exact Or.inr ⟨Q, normal_of_card_sylow_eq_one (by simpa using hkk) Q⟩
    · exfalso
      rw [hkk, pow_one, Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hq.one_lt] at hmod
      exact hp.one_lt.ne' hmod
    · have hone : (1 : ℕ) ≡ p ^ 2 [MOD q] := by rw [← hkk]; exact hmod.symm
      have hqd : q ∣ p ^ 2 - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp hone
      obtain ⟨hp2, hq3⟩ := eq_two_and_three_of_dvd_sq_sub_one hp hq hlt hqd
      subst hp2
      subst hq3
      haveI := subsingleton_sylow_two_of_card_eq_twelve (by rw [h]; norm_num)
        (by rw [hkk]; norm_num)
      obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
      exact Or.inl ⟨S, Sylow.normal_of_subsingleton S⟩
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
    refine Or.inl ⟨P, normal_of_card_sylow_eq_one ?_ P⟩
    have hdvd : Nat.card (Sylow p G) ∣ q := by
      have hind := P.card_dvd_index
      rwa [(card_index_sylow_prime_sq hp hq hpq h P).2] at hind
    have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact h1
    · exfalso
      rw [h1, Nat.ModEq, Nat.mod_eq_of_lt hgt, Nat.mod_eq_of_lt hp.one_lt] at hmod
      exact hq.one_lt.ne' hmod

end Semiabelian

namespace IsSemiabelian

/-- **Every finite group of order `p ^ 2 * q`, for distinct primes `p` and `q`, is semiabelian.**
Such a group has a normal Sylow subgroup, necessarily abelian: a Sylow `p`-subgroup has order
`p ^ 2` and a group of order the square of a prime is commutative, while a Sylow `q`-subgroup has
prime order `q` and is cyclic.  A Sylow subgroup is a Hall subgroup, so Schur–Zassenhaus splits the
extension, and the quotient has order `q` respectively `p ^ 2`, hence is semiabelian. -/
theorem of_card_eq_sq_mul_prime {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q) : IsSemiabelian G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  rcases Semiabelian.exists_normal_sylow_of_card_eq_sq_mul_prime hp hq hpq h with
    ⟨P, hP⟩ | ⟨Q, hQ⟩
  · haveI := hP
    obtain ⟨hcard, hindex⟩ := Semiabelian.card_index_sylow_prime_sq hp hq hpq h P
    refine of_normal_abelian_sylow P (IsPGroup.commutative_of_card_eq_prime_sq hcard) ?_
    exact of_card_eq_prime hq (by rw [← Subgroup.index_eq_card]; exact hindex)
  · haveI := hQ
    obtain ⟨hcard, hindex⟩ := Semiabelian.card_index_sylow_prime hp hq hpq h Q
    refine of_normal_abelian_sylow Q (Semiabelian.mul_comm_of_card_eq_prime hq hcard) ?_
    exact of_card_eq_prime_sq hp (by rw [← Subgroup.index_eq_card]; exact hindex)

/-- **Every group of order `12` is semiabelian**, the case `p = 2` and `q = 3` of a group of order
`p ^ 2 * q`. -/
theorem of_card_eq_twelve {G : Type} [Group G] [Finite G] (h : Nat.card G = 12) :
    IsSemiabelian G :=
  of_card_eq_sq_mul_prime Nat.prime_two Nat.prime_three (by norm_num) (by rw [h]; norm_num)

end IsSemiabelian
