/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianHall
import InverseGalois.Solvable.SemiabelianSmall
import InverseGalois.Solvable.SemiabelianP2Q

/-!
# Groups of order `p ^ 2 * q ^ 2` are semiabelian

A finite group whose order is `p ^ 2 * q ^ 2` for two distinct primes `p` and `q` always has a
normal Sylow subgroup, and that is precisely the input the splitting criteria of
`InverseGalois.Solvable.SemiabelianHall` ask for: a normal Sylow subgroup here has order the
square of a prime, hence is commutative, and the quotient by it has order the square of the other
prime, hence is semiabelian by `InverseGalois.Solvable.SemiabelianSmall`.  A Sylow subgroup is a
Hall subgroup, so Schur–Zassenhaus splits the extension and the whole group is semiabelian.

The group-theoretic content is Sylow's counting theorem together with a single exceptional
configuration.  Writing `n_q` for the number of Sylow `q`-subgroups and assuming `p < q`, the
number `n_q` divides the index `p ^ 2` and is congruent to `1` modulo `q`; it is therefore `1`,
`p` or `p ^ 2`.  The value `p` is impossible, since `p` lies strictly between `1` and `q`.  The
value `p ^ 2` forces `q ∣ p ^ 2 - 1 = (p - 1) * (p + 1)`, and `q` is too large to divide `p - 1`,
so `q = p + 1`; consecutive primes of that shape are only `2` and `3`.  The sole survivor is a
group of order `36` with four Sylow `3`-subgroups, and it is settled by hand.

In that exceptional case, conjugation on the four Sylow `3`-subgroups is a homomorphism to a
permutation group of `4` letters.  A Sylow `3`-subgroup is its own normalizer, because the
normalizer has index `4`, so the kernel `K` of the action is contained in every Sylow
`3`-subgroup; its order divides `9`, is not `9` (else all four subgroups would coincide with `K`)
and is not `1` (else the group of order `36` would embed in a group of order `24`), so it is `3`.
Every Sylow `3`-subgroup, being of order the square of a prime, is commutative and contains `K`,
so the centralizer of `K` contains all of them; that centralizer has order `9`, `18` or `36`, and
the first two are impossible — order `9` would identify two distinct Sylow `3`-subgroups, and
order `18` would make a Sylow `3`-subgroup normal inside it, so that the centralizer would sit
inside the normalizer of a Sylow `3`-subgroup, which has order `9`.  Hence `K` is central.

The quotient by `K` has order `12`, so it has a normal Sylow subgroup.  A normal Sylow
`3`-subgroup upstairs would pull back to a normal subgroup of order `9`, that is, to a normal
Sylow `3`-subgroup of the whole group, contradicting the count of four.  So the quotient has a
normal Sylow `2`-subgroup, whose preimage `H` is a normal subgroup of order `12` containing a
Sylow `2`-subgroup `S` of the ambient group as well as `K`; since `K` is central, `H` is the
product of `S` and `K`, and an element `s * k` of `H` has fourth power `k`.  Every conjugate of an
element of `S` lies in `H` and has trivial fourth power, hence lies in `S`, so `S` is normal.

## Main results

* `Semiabelian.exists_normal_sylow_two_thirtysix` — a group of order `36` with four Sylow
  `3`-subgroups has a normal Sylow `2`-subgroup.
* `Semiabelian.exists_normal_sylow_of_card_eq_sq_mul_sq` — **a finite group of order
  `p ^ 2 * q ^ 2`, for distinct primes `p` and `q`, has a normal Sylow `p`-subgroup or a normal
  Sylow `q`-subgroup.**
* `IsSemiabelian.of_card_eq_sq_mul_sq` — **every finite group of order `p ^ 2 * q ^ 2`, for
  distinct primes `p` and `q`, is semiabelian.**
* `IsSemiabelian.of_card_eq_thirtysix` — every group of order `36` is semiabelian.
* `IsSemiabelian.of_card_eq_hundred` — every group of order `100` is semiabelian.
-/

namespace Semiabelian

/-- **The Sylow `p`-subgroups of a group of order `p ^ 2 * q ^ 2` have order `p ^ 2` and index
`q ^ 2`.**  The order of a Sylow subgroup is the full power of `p` dividing the group order, and
the exponent of `p` in `p ^ 2 * q ^ 2` is `2` because the prime `q` differs from `p`; the index is
then read off from the product of order and index. -/
theorem card_index_sylow_sq_mul_sq {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q ^ 2) (P : Sylow p G) :
    Nat.card ↥(P : Subgroup G) = p ^ 2 ∧ (P : Subgroup G).index = q ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfac : (Nat.card G).factorization p = 2 := by
    rw [h, Nat.factorization_mul (pow_ne_zero 2 hp.pos.ne') (pow_ne_zero 2 hq.pos.ne'),
      Finsupp.add_apply, hp.factorization_pow, hq.factorization_pow]
    simp [hpq]
  have hcard : Nat.card ↥(P : Subgroup G) = p ^ 2 := by rw [P.card_eq_multiplicity, hfac]
  refine ⟨hcard, ?_⟩
  have hmul := (P : Subgroup G).card_mul_index
  rw [hcard, h] at hmul
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hmul

/-- **A Sylow `3`-subgroup of a group of order `36` has order `9` and index `4`**, the case
`p = 3` and `q = 2` of the order and index of a Sylow subgroup in a group of order
`p ^ 2 * q ^ 2`. -/
theorem card_index_sylow_three_thirtysix {G : Type} [Group G] [Finite G] (h : Nat.card G = 36)
    (P : Sylow 3 G) : Nat.card ↥(P : Subgroup G) = 9 ∧ (P : Subgroup G).index = 4 := by
  have h' : Nat.card G = 3 ^ 2 * 2 ^ 2 := by rw [h]; norm_num
  obtain ⟨h1, h2⟩ := card_index_sylow_sq_mul_sq Nat.prime_three Nat.prime_two (by norm_num) h' P
  exact ⟨h1.trans (by norm_num), h2.trans (by norm_num)⟩

/-- **A Sylow `2`-subgroup of a group of order `36` has order `4` and index `9`**, the case
`p = 2` and `q = 3` of the order and index of a Sylow subgroup in a group of order
`p ^ 2 * q ^ 2`. -/
theorem card_index_sylow_two_thirtysix {G : Type} [Group G] [Finite G] (h : Nat.card G = 36)
    (S : Sylow 2 G) : Nat.card ↥(S : Subgroup G) = 4 ∧ (S : Subgroup G).index = 9 := by
  have h' : Nat.card G = 2 ^ 2 * 3 ^ 2 := by rw [h]; norm_num
  obtain ⟨h1, h2⟩ := card_index_sylow_sq_mul_sq Nat.prime_two Nat.prime_three (by norm_num) h' S
  exact ⟨h1.trans (by norm_num), h2.trans (by norm_num)⟩

/-- **In a group of order `36` with four Sylow `3`-subgroups, each of them is its own
normalizer.**  The number of Sylow `3`-subgroups is the index of the normalizer of any one of
them, so that normalizer has order `9`; a Sylow `3`-subgroup has the same order and is contained
in its normalizer, so the two coincide. -/
theorem normalizer_eq_sylow_three_thirtysix {G : Type} [Group G] [Finite G] (h : Nat.card G = 36)
    (h3 : Nat.card (Sylow 3 G) = 4) (P : Sylow 3 G) :
    (P : Subgroup G).normalizer = (P : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := (card_index_sylow_three_thirtysix h P).1
  have hidx : (P : Subgroup G).normalizer.index = 4 := by
    rw [← P.card_eq_index_normalizer]; exact h3
  have hmul := (P : Subgroup G).normalizer.card_mul_index
  rw [hidx, h] at hmul
  exact (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by omega)).symm

/-- **A group of order `36` with four Sylow `3`-subgroups has a normal subgroup of order `3`
contained in every Sylow `3`-subgroup.**  Conjugation on the four Sylow `3`-subgroups is a
homomorphism into a permutation group of four letters; its kernel is normal and is contained in
the normalizer of each Sylow `3`-subgroup, that is, in each Sylow `3`-subgroup itself, so its
order divides `9`.  The order `1` is excluded because a group of order `36` does not embed into a
group of order `24`, and the order `9` is excluded because the kernel would then equal every
Sylow `3`-subgroup, of which there are four. -/
theorem exists_normal_card_three_thirtysix {G : Type} [Group G] [Finite G] (h : Nat.card G = 36)
    (h3 : Nat.card (Sylow 3 G) = 4) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.card ↥K = 3 ∧ ∀ P : Sylow 3 G, K ≤ (P : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₁, P₂, hP12⟩ : ∃ P₁ P₂ : Sylow 3 G, P₁ ≠ P₂ := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton (Sylow 3 G) := ⟨hcon⟩
    rw [Nat.card_unique] at h3
    omega
  have hKle : ∀ P : Sylow 3 G, (MulAction.toPermHom G (Sylow 3 G)).ker ≤ (P : Subgroup G) := by
    intro P g hg
    have hg' : (MulAction.toPermHom G (Sylow 3 G)) g = 1 := MonoidHom.mem_ker.mp hg
    have h2 : g • P = P := by
      rw [show g • P = (MulAction.toPermHom G (Sylow 3 G)) g P from rfl, hg']; rfl
    have h1 : g ∈ (P : Subgroup G).normalizer := Sylow.smul_eq_iff_mem_normalizer.mp h2
    rwa [normalizer_eq_sylow_three_thirtysix h h3 P] at h1
  refine ⟨_, inferInstance, ?_, hKle⟩
  have hc1 := (card_index_sylow_three_thirtysix h P₁).1
  have hc2 := (card_index_sylow_three_thirtysix h P₂).1
  have hc9 : Nat.card ↥(MulAction.toPermHom G (Sylow 3 G)).ker ∣ 9 := by
    have := Subgroup.card_dvd_of_le (hKle P₁)
    rwa [hc1] at this
  have hperm : Nat.card (Equiv.Perm (Sylow 3 G)) = 24 := by rw [Nat.card_perm, h3]; rfl
  have hidx : (MulAction.toPermHom G (Sylow 3 G)).ker.index ∣ 24 := by
    rw [Subgroup.index_ker]
    have h1 := Subgroup.card_subgroup_dvd_card (MulAction.toPermHom G (Sylow 3 G)).range
    rwa [hperm] at h1
  have hmulK := (MulAction.toPermHom G (Sylow 3 G)).ker.card_mul_index
  rw [h] at hmulK
  rw [show (9 : ℕ) = 3 ^ 2 from by norm_num] at hc9
  obtain ⟨k, hk2, hkk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hc9
  interval_cases k
  · exfalso
    rw [pow_zero] at hkk
    rw [hkk, one_mul] at hmulK
    rw [hmulK] at hidx
    exact absurd hidx (by decide)
  · rw [hkk]; norm_num
  · exfalso
    rw [pow_two] at hkk
    have e1 : (MulAction.toPermHom G (Sylow 3 G)).ker = (P₁ : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge (hKle P₁) (by omega)
    have e2 : (MulAction.toPermHom G (Sylow 3 G)).ker = (P₂ : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge (hKle P₂) (by omega)
    exact hP12 (Sylow.ext (e1.symm.trans e2))

/-- **In a group of order `36` with four Sylow `3`-subgroups, a subgroup contained in every Sylow
`3`-subgroup is central.**  A Sylow `3`-subgroup has order the square of a prime, hence is
commutative, so it centralizes any subgroup it contains; the centralizer therefore contains all
four Sylow `3`-subgroups and its order is a multiple of `9` dividing `36`.  Order `9` would force
two distinct Sylow `3`-subgroups to coincide with the centralizer, and order `18` would give a
Sylow `3`-subgroup index `2` inside the centralizer, hence normality there, putting the
centralizer inside the normalizer of a Sylow `3`-subgroup, which has order `9`.  So the
centralizer is everything. -/
theorem le_center_of_le_sylow_three_thirtysix {G : Type} [Group G] [Finite G] (h : Nat.card G = 36)
    (h3 : Nat.card (Sylow 3 G) = 4) (K : Subgroup G)
    (hKle : ∀ P : Sylow 3 G, K ≤ (P : Subgroup G)) : K ≤ Subgroup.center G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₁, P₂, hP12⟩ : ∃ P₁ P₂ : Sylow 3 G, P₁ ≠ P₂ := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton (Sylow 3 G) := ⟨hcon⟩
    rw [Nat.card_unique] at h3
    omega
  have hc1 := (card_index_sylow_three_thirtysix h P₁).1
  have hc2 := (card_index_sylow_three_thirtysix h P₂).1
  have hPc : ∀ P : Sylow 3 G, (P : Subgroup G) ≤ Subgroup.centralizer (K : Set G) := by
    intro P x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkP : k ∈ (P : Subgroup G) := hKle P hk
    have hcard2 : Nat.card ↥(P : Subgroup G) = 3 ^ 2 :=
      (card_index_sylow_three_thirtysix h P).1.trans (by norm_num)
    have hcomm := IsPGroup.commutative_of_card_eq_prime_sq hcard2 ⟨k, hkP⟩ ⟨x, hx⟩
    simpa using congrArg Subtype.val hcomm
  have hCtop : Subgroup.centralizer (K : Set G) = ⊤ := by
    have h9 : (9 : ℕ) ∣ Nat.card ↥(Subgroup.centralizer (K : Set G)) := by
      have := Subgroup.card_dvd_of_le (hPc P₁)
      rwa [hc1] at this
    have h36 : Nat.card ↥(Subgroup.centralizer (K : Set G)) ∣ 36 := by
      have := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (K : Set G))
      rwa [h] at this
    obtain ⟨m, hm⟩ := h9
    have h94 : 9 * m ∣ 9 * 4 := by rw [← hm]; exact h36
    have hm4 : m ∣ 4 := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 9)).mp h94
    have hmle : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm4
    interval_cases m
    · exfalso
      have := Nat.card_pos (α := ↥(Subgroup.centralizer (K : Set G)))
      omega
    · exfalso
      have e1 : (P₁ : Subgroup G) = Subgroup.centralizer (K : Set G) :=
        Subgroup.eq_of_le_of_card_ge (hPc P₁) (by omega)
      have e2 : (P₂ : Subgroup G) = Subgroup.centralizer (K : Set G) :=
        Subgroup.eq_of_le_of_card_ge (hPc P₂) (by omega)
      exact hP12 (Sylow.ext (e1.trans e2.symm))
    · exfalso
      have hidx1 := (card_index_sylow_three_thirtysix h P₁).2
      have hCidx : (Subgroup.centralizer (K : Set G)).index = 2 := by
        have hmul := (Subgroup.centralizer (K : Set G)).card_mul_index
        rw [h, hm] at hmul
        omega
      have hrel : (P₁ : Subgroup G).relIndex (Subgroup.centralizer (K : Set G)) = 2 := by
        have hmul := Subgroup.relIndex_mul_index (hPc P₁)
        rw [hCidx, hidx1] at hmul
        omega
      haveI : ((P₁ : Subgroup G).subgroupOf (Subgroup.centralizer (K : Set G))).Normal :=
        Subgroup.normal_of_index_eq_two hrel
      have hle := Subgroup.le_normalizer_of_normal_subgroupOf (hPc P₁)
      rw [normalizer_eq_sylow_three_thirtysix h h3 P₁] at hle
      have hdd := Subgroup.card_dvd_of_le hle
      have := Nat.le_of_dvd (by omega) hdd
      omega
    · exact absurd hm4 (by decide)
    · exact Subgroup.eq_top_of_card_eq _ (by rw [h]; omega)
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (K : Set G) := by rw [hCtop]; trivial
  exact (Subgroup.mem_centralizer_iff.mp hg k hk).symm

/-- **A group of order `36` with four Sylow `3`-subgroups has a normal Sylow `2`-subgroup.**  The
kernel `K` of the conjugation action on the Sylow `3`-subgroups is a central subgroup of order
`3`, and the quotient by it has order `12`, so that quotient has a normal Sylow subgroup.  A
normal Sylow `3`-subgroup of the quotient would pull back to a normal subgroup of order `9`,
which is a normal Sylow `3`-subgroup of the whole group and contradicts the count of four.  So
the quotient has a normal Sylow `2`-subgroup, and its preimage `H` is normal of order `12`.  A
Sylow `2`-subgroup `S` maps into that Sylow `2`-subgroup of the quotient, so `S` and `K` both lie
in `H` and generate it.  Every element of `H` is thus a product `s * k` with `k` central, whose
fourth power is `k`; a conjugate of an element of `S` lies in `H` and has trivial fourth power,
hence lies in `S`. -/
theorem exists_normal_sylow_two_thirtysix {G : Type} [Group G] [Finite G] (h : Nat.card G = 36)
    (h3 : Nat.card (Sylow 3 G) = 4) : ∃ S : Sylow 2 G, (S : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKnormal, hKcard, hKsyl⟩ := exists_normal_card_three_thirtysix h h3
  haveI := hKnormal
  have hKcenter := le_center_of_le_sylow_three_thirtysix h h3 K hKsyl
  have hKidx : K.index = 12 := by
    have hmul := K.card_mul_index
    rw [h, hKcard] at hmul
    omega
  have hQcard : Nat.card (G ⧸ K) = 2 ^ 2 * 3 := by
    have h12 : Nat.card (G ⧸ K) = 12 := by rw [← Subgroup.index_eq_card, hKidx]
    omega
  have hφsurj : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  rcases exists_normal_sylow_of_card_eq_sq_mul_prime Nat.prime_two Nat.prime_three
    (by norm_num) hQcard with ⟨T, hT⟩ | ⟨T, hT⟩
  · obtain ⟨-, hTidx⟩ := card_index_sylow_prime_sq Nat.prime_two Nat.prime_three
      (by norm_num) hQcard T
    haveI hHnormal : ((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)).Normal :=
      hT.comap (QuotientGroup.mk' K)
    have hHidx : ((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)).index = 3 := by
      rw [Subgroup.index_comap_of_surjective _ hφsurj]; exact hTidx
    have hHcard : Nat.card ↥((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)) = 12 := by
      have hmul := ((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)).card_mul_index
      rw [h, hHidx] at hmul
      omega
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
    have hScard := (card_index_sylow_two_thirtysix h S).1
    have hmapT : (S : Subgroup G).map (QuotientGroup.mk' K) ≤ (T : Subgroup (G ⧸ K)) := by
      obtain ⟨T', hT'⟩ := (S.isPGroup'.map (QuotientGroup.mk' K)).exists_le_sylow
      haveI := Sylow.unique_of_normal T hT
      rwa [Subsingleton.elim T' T] at hT'
    have hSH : (S : Subgroup G) ≤ (T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K) :=
      Subgroup.map_le_iff_le_comap.mp hmapT
    have hKH : K ≤ (T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K) := by
      intro k hk
      rw [Subgroup.mem_comap]
      have hk1 : (QuotientGroup.mk' K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
      rw [hk1]
      exact one_mem _
    have hsup : (S : Subgroup G) ⊔ K = (T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K) := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hSH hKH) ?_
      have h4 : (4 : ℕ) ∣ Nat.card ↥((S : Subgroup G) ⊔ K) := by
        have hd := Subgroup.card_dvd_of_le
          (le_sup_left : (S : Subgroup G) ≤ (S : Subgroup G) ⊔ K)
        rwa [hScard] at hd
      have h3' : (3 : ℕ) ∣ Nat.card ↥((S : Subgroup G) ⊔ K) := by
        have hd := Subgroup.card_dvd_of_le (le_sup_right : K ≤ (S : Subgroup G) ⊔ K)
        rwa [hKcard] at hd
      have h12 : (12 : ℕ) ∣ Nat.card ↥((S : Subgroup G) ⊔ K) :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3'
      have hge := Nat.le_of_dvd Nat.card_pos h12
      omega
    have hn4 : ∀ s ∈ (S : Subgroup G), s ^ 4 = 1 := by
      intro s hs
      have hd := Subgroup.orderOf_dvd_natCard (S : Subgroup G) hs
      rw [hScard] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have hk3 : ∀ k ∈ K, k ^ 3 = 1 := by
      intro k hk
      have hd := Subgroup.orderOf_dvd_natCard K hk
      rw [hKcard] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    refine ⟨S, ⟨fun n hn g => ?_⟩⟩
    have hxH : g * n * g⁻¹ ∈ (T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K) :=
      hHnormal.conj_mem n (hSH hn) g
    have hx4 : (g * n * g⁻¹) ^ 4 = 1 := by
      rw [conj_pow, hn4 n hn, mul_one, mul_inv_cancel]
    rw [← hsup, ← SetLike.mem_coe, Subgroup.mul_normal] at hxH
    obtain ⟨s, hs, k, hk, hsk⟩ := hxH
    replace hsk : s * k = g * n * g⁻¹ := hsk
    have hkcomm : ∀ y : G, y * k = k * y := Subgroup.mem_center_iff.mp (hKcenter hk)
    have hcomm : Commute s k := hkcomm s
    have hk4 : k ^ 4 = k := by
      calc k ^ 4 = k ^ 3 * k := pow_succ k 3
        _ = k := by rw [hk3 k hk, one_mul]
    have hpow : (s * k) ^ 4 = k := by
      have hmp : (s * k) ^ 4 = s ^ 4 * k ^ 4 := hcomm.mul_pow 4
      rw [hmp, hn4 s hs, one_mul, hk4]
    rw [hsk, hx4] at hpow
    rw [← hpow, mul_one] at hsk
    rw [← hsk]
    exact hs
  · exfalso
    obtain ⟨-, hTidx⟩ := card_index_sylow_prime Nat.prime_two Nat.prime_three
      (by norm_num) hQcard T
    haveI hNnormal : ((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)).Normal :=
      hT.comap (QuotientGroup.mk' K)
    have hNidx : ((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)).index = 4 := by
      rw [Subgroup.index_comap_of_surjective _ hφsurj, hTidx]; norm_num
    have hNcard : Nat.card ↥((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)) = 9 := by
      have hmul := ((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)).card_mul_index
      rw [h, hNidx] at hmul
      omega
    have hNp : IsPGroup 3 ↥((T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)) :=
      IsPGroup.of_card (n := 2) (by simpa using hNcard)
    obtain ⟨Q, hQ⟩ := hNp.exists_le_sylow
    have hQcard9 := (card_index_sylow_three_thirtysix h Q).1
    have hNQ : (T : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K) = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hQ (by omega)
    haveI hQnormal : (Q : Subgroup G).Normal := by rw [← hNQ]; infer_instance
    haveI := Sylow.unique_of_normal Q hQnormal
    rw [Nat.card_unique] at h3
    omega

/-- **A finite group of order `p ^ 2 * q ^ 2` with `p < q` has a normal Sylow subgroup.**  The
number of Sylow `q`-subgroups divides the index `p ^ 2` and is congruent to `1` modulo `q`, so it
is `1`, `p` or `p ^ 2`.  The value `p` is too small to be congruent to `1` modulo the larger prime
`q`.  The value `p ^ 2` forces `q` to divide `p ^ 2 - 1`, hence `p = 2` and `q = 3`: a group of
order `36` with four Sylow `3`-subgroups, which has a normal Sylow `2`-subgroup. -/
theorem exists_normal_sylow_of_card_eq_sq_mul_sq_of_lt {G : Type} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hlt : p < q) (h : Nat.card G = p ^ 2 * q ^ 2) :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ∨ (∃ Q : Sylow q G, (Q : Subgroup G).Normal) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hpq : p ≠ q := hlt.ne
  have hsymm : Nat.card G = q ^ 2 * p ^ 2 := by rw [h]; ring
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q G))
  have hdvd : Nat.card (Sylow q G) ∣ p ^ 2 := by
    have hind := Q.card_dvd_index
    rwa [(card_index_sylow_sq_mul_sq hq hp hpq.symm hsymm Q).2] at hind
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
    exact Or.inl (exists_normal_sylow_two_thirtysix (by rw [h]; norm_num)
      (by rw [hkk]; norm_num))

/-- **A finite group of order `p ^ 2 * q ^ 2`, for distinct primes `p` and `q`, has a normal Sylow
`p`-subgroup or a normal Sylow `q`-subgroup.**  The hypothesis is symmetric in the two primes, so
the case of the smaller prime first covers both. -/
theorem exists_normal_sylow_of_card_eq_sq_mul_sq {G : Type} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q ^ 2) :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ∨ (∃ Q : Sylow q G, (Q : Subgroup G).Normal) := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact exists_normal_sylow_of_card_eq_sq_mul_sq_of_lt hp hq hlt h
  · exact (exists_normal_sylow_of_card_eq_sq_mul_sq_of_lt hq hp hgt (by rw [h]; ring)).symm

end Semiabelian

namespace IsSemiabelian

/-- **Every finite group of order `p ^ 2 * q ^ 2`, for distinct primes `p` and `q`, is
semiabelian.**  Such a group has a normal Sylow subgroup, necessarily commutative because a group
of order the square of a prime is; a Sylow subgroup is a Hall subgroup, so Schur–Zassenhaus splits
the extension, and the quotient has order the square of the other prime, hence is semiabelian. -/
theorem of_card_eq_sq_mul_sq {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ 2 * q ^ 2) : IsSemiabelian G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  rcases Semiabelian.exists_normal_sylow_of_card_eq_sq_mul_sq hp hq hpq h with ⟨P, hP⟩ | ⟨Q, hQ⟩
  · haveI := hP
    obtain ⟨hcard, hindex⟩ := Semiabelian.card_index_sylow_sq_mul_sq hp hq hpq h P
    refine of_normal_abelian_sylow P (IsPGroup.commutative_of_card_eq_prime_sq hcard) ?_
    exact of_card_eq_prime_sq hq (by rw [← Subgroup.index_eq_card]; exact hindex)
  · haveI := hQ
    obtain ⟨hcard, hindex⟩ := Semiabelian.card_index_sylow_sq_mul_sq hq hp hpq.symm
      (by rw [h]; ring) Q
    refine of_normal_abelian_sylow Q (IsPGroup.commutative_of_card_eq_prime_sq hcard) ?_
    exact of_card_eq_prime_sq hp (by rw [← Subgroup.index_eq_card]; exact hindex)

/-- **Every group of order `36` is semiabelian**, the case `p = 2` and `q = 3` of a group of order
`p ^ 2 * q ^ 2`. -/
theorem of_card_eq_thirtysix {G : Type} [Group G] [Finite G] (h : Nat.card G = 36) :
    IsSemiabelian G :=
  of_card_eq_sq_mul_sq Nat.prime_two Nat.prime_three (by norm_num) (by rw [h]; norm_num)

/-- **Every group of order `100` is semiabelian**, the case `p = 2` and `q = 5` of a group of
order `p ^ 2 * q ^ 2`. -/
theorem of_card_eq_hundred {G : Type} [Group G] [Finite G] (h : Nat.card G = 100) :
    IsSemiabelian G :=
  of_card_eq_sq_mul_sq (q := 5) Nat.prime_two (by norm_num) (by norm_num) (by rw [h]; norm_num)

end IsSemiabelian
