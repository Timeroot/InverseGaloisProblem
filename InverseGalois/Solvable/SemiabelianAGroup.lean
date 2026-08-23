/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.SemiabelianFrattini
import InverseGalois.Solvable.ChiefSeries

/-!
# Solvable groups with abelian Sylow subgroups are semiabelian

A finite group all of whose Sylow subgroups are abelian is called an *A-group*.  Thompson's
criterion says that a solvable A-group is semiabelian, and since the class of A-groups is closed
under passing to subgroups — a Sylow subgroup of a subgroup is a `p`-group of the ambient group,
hence sits inside one of its Sylow subgroups — the statement is amenable to induction on the order
through the supplementation criterion of `InverseGalois.Solvable.SemiabelianFrattini`.

The inductive step must produce an abelian normal subgroup of a nontrivial `G` escaping the
Frattini subgroup `Φ`.  Since `Φ` is proper, the quotient `G ⧸ Φ` is a nontrivial finite solvable
group, so it owns a nontrivial elementary abelian normal `p`-subgroup `K`; let `N` be the preimage
of `K` in `G`, a normal subgroup of `G` strictly larger than `Φ` with `Φ` of `p`-power index in it.
A Sylow `p`-subgroup `P` of `N` therefore supplements `Φ` inside `N`: the index of `P ⊔ Φ` in `N`
divides both a power of `p` and the index of `P`, which is prime to `p`, so `P ⊔ Φ = N`.  Frattini's
argument gives `N_G(P) ⊔ N = ⊤`, whence `N_G(P) ⊔ Φ = ⊤`, and the non-generating property of the
Frattini subgroup forces `N_G(P) = ⊤`: the subgroup `P` is normal in `G`.  It is a `p`-group, hence
abelian by hypothesis, and it is not contained in `Φ`, since otherwise `N = P ⊔ Φ = Φ`.

The cubefree case is a corollary: a Sylow subgroup then has order `1`, `p` or `p ^ 2`, and every
group of such an order is commutative.

## Main results

* `IsSemiabelian.of_forall_sylow_comm`: **a finite solvable group all of whose Sylow subgroups are
  abelian is semiabelian.**
* `IsSemiabelian.of_isSolvable_of_cubefree`: **every finite solvable group of cubefree order is
  semiabelian.**
* `Semiabelian.exists_normal_abelian_not_le_frattini`: the inductive step — such a group, when
  nontrivial, has an abelian normal subgroup that is not contained in its Frattini subgroup.
* `Semiabelian.forall_sylow_comm_subgroup`: having abelian Sylow subgroups passes to subgroups.
-/

open Subgroup

namespace Semiabelian

/-- In a finite group whose Sylow subgroups are abelian, every `p`-subgroup is commutative: it is
contained in a Sylow `p`-subgroup, where its elements commute. -/
theorem mul_comm_of_isPGroup {G : Type} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (x y : ↥(P : Subgroup G)), x * y = y * x)
    {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hH : IsPGroup p ↥H) (x y : ↥H) : x * y = y * x := by
  obtain ⟨S, hle⟩ := hH.exists_le_sylow
  have hxy := h p hp S ⟨(x : G), hle x.2⟩ ⟨(y : G), hle y.2⟩
  exact Subtype.ext (by simpa using congrArg Subtype.val hxy)

/-- Having abelian Sylow subgroups is inherited by subgroups: a Sylow `p`-subgroup of a subgroup
`U` maps to a `p`-subgroup of the ambient group, and `p`-subgroups of the ambient group are
commutative. -/
theorem forall_sylow_comm_subgroup {G : Type} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (x y : ↥(P : Subgroup G)), x * y = y * x)
    (U : Subgroup G) (p : ℕ) (hp : p.Prime) (P : Sylow p ↥U) (x y : ↥(P : Subgroup ↥U)) :
    x * y = y * x := by
  have hpg : IsPGroup p ↥((P : Subgroup ↥U).map U.subtype) := P.2.map U.subtype
  have key := mul_comm_of_isPGroup h hp hpg
    ⟨((x : ↥U) : G), Subgroup.mem_map_of_mem U.subtype x.2⟩
    ⟨((y : ↥U) : G), Subgroup.mem_map_of_mem U.subtype y.2⟩
  exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val key))

/-- **A nontrivial finite solvable group whose Sylow subgroups are abelian has an abelian normal
subgroup outside its Frattini subgroup.**  Pulling back an elementary abelian minimal normal
subgroup of the Frattini quotient produces a normal subgroup `N` in which the Frattini subgroup has
`p`-power index, so a Sylow `p`-subgroup of `N` supplements it there; Frattini's argument together
with the non-generating property of the Frattini subgroup then makes that Sylow subgroup normal in
the whole group, and it is abelian by hypothesis. -/
theorem exists_normal_abelian_not_le_frattini {G : Type} [Group G] [Finite G] [IsSolvable G]
    [Nontrivial G]
    (h : ∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (x y : ↥(P : Subgroup G)), x * y = y * x) :
    ∃ (A : Subgroup G) (_ : A.Normal), (∀ x y : ↥A, x * y = y * x) ∧ ¬ A ≤ frattini G := by
  have hfrne : frattini G ≠ ⊤ := by
    intro htop
    exact bot_ne_top (frattini_nongenerating (K := (⊥ : Subgroup G)) (by rw [htop, bot_sup_eq]))
  have hidx : (frattini G).index ≠ 1 := fun hh => hfrne (Subgroup.index_eq_one.mp hh)
  have hidx0 : (frattini G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  haveI : Nontrivial (G ⧸ frattini G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have hc : (frattini G).index = Nat.card (G ⧸ frattini G) :=
      Subgroup.index_eq_card (frattini G)
    omega
  obtain ⟨K, hKnorm, hKbot, p, hp, hppow, hKcomm⟩ :=
    exists_normal_elementaryAbelian (G := G ⧸ frattini G) inferInstance
  haveI := hKnorm
  haveI : Fact p.Prime := ⟨hp⟩
  have hKp : IsPGroup p ↥K := fun g => ⟨1, by rw [pow_one]; exact hppow g⟩
  obtain ⟨n, hKcard⟩ := hKp.exists_card_eq
  have hmapN : (K.comap (QuotientGroup.mk' (frattini G))).map (QuotientGroup.mk' (frattini G))
      = K := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K
  set N : Subgroup G := K.comap (QuotientGroup.mk' (frattini G)) with hNdef
  haveI : N.Normal := Subgroup.normal_comap _
  have hQN : frattini G ≤ N := by
    have hker := Subgroup.ker_le_comap (QuotientGroup.mk' (frattini G)) K
    rwa [QuotientGroup.ker_mk'] at hker
  have hNQ : N ≠ frattini G := by
    intro hEq
    refine hKbot ?_
    rw [← hmapN, hEq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  obtain ⟨P⟩ : Nonempty (Sylow p ↥N) := inferInstance
  have hrel : (frattini G).relIndex N = Nat.card ↥K := by
    have h1 := Subgroup.relIndex_ker (K := N) (QuotientGroup.mk' (frattini G))
    rw [QuotientGroup.ker_mk'] at h1
    rw [h1, hmapN]
  have hSylowIdx : ¬ p ∣ (P : Subgroup ↥N).index := P.not_dvd_index
  have h1 : ((P : Subgroup ↥N) ⊔ (frattini G).subgroupOf N).index ∣ (P : Subgroup ↥N).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have h2 : ((P : Subgroup ↥N) ⊔ (frattini G).subgroupOf N).index
      ∣ ((frattini G).subgroupOf N).index := Subgroup.index_dvd_of_le le_sup_right
  have h3 : ((frattini G).subgroupOf N).index = p ^ n := by
    rw [← hKcard, ← hrel]
    rfl
  rw [h3] at h2
  have hStop : (P : Subgroup ↥N) ⊔ (frattini G).subgroupOf N = ⊤ := by
    refine Subgroup.index_eq_one.mp ?_
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp h2
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simpa using hi
    · exact absurd ((by rw [hi]; exact dvd_pow_self p hipos.ne' : p ∣ _).trans h1) hSylowIdx
  have hsup : ((P : Subgroup ↥N).map N.subtype) ⊔ frattini G = N := by
    have hmap := congrArg (Subgroup.map N.subtype) hStop
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQN,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  have hfrat : ((P : Subgroup ↥N).map N.subtype).normalizer ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top P
  have hle : N ≤ ((P : Subgroup ↥N).map N.subtype).normalizer ⊔ frattini G :=
    hsup.ge.trans (sup_le_sup_right Subgroup.le_normalizer _)
  have htop : ((P : Subgroup ↥N).map N.subtype).normalizer ⊔ frattini G = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hfrat]
    exact sup_le le_sup_left hle
  haveI : ((P : Subgroup ↥N).map N.subtype).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (frattini_nongenerating htop)
  refine ⟨(P : Subgroup ↥N).map N.subtype, inferInstance,
    mul_comm_of_isPGroup h hp (P.2.map N.subtype), fun hcon => hNQ ?_⟩
  exact hsup.symm.trans (sup_eq_right.mpr hcon)

end Semiabelian

/-- The induction on the order behind `IsSemiabelian.of_forall_sylow_comm`, carried out over all
groups of order at most a given bound at once. -/
private theorem isSemiabelian_of_forall_sylow_comm_aux :
    ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ n → IsSolvable G →
      (∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (x y : ↥(P : Subgroup G)), x * y = y * x) →
      IsSemiabelian G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hcard _ _
    exact absurd hcard (by simpa using Nat.card_pos.ne')
  | succ n ih =>
    intro G _ _ hcard hsolv h
    haveI := hsolv
    rcases subsingleton_or_nontrivial G with hs | hnt
    · exact .of_subsingleton G
    · obtain ⟨A, hAnorm, hAcomm, hAfr⟩ := Semiabelian.exists_normal_abelian_not_le_frattini h
      haveI := hAnorm
      refine IsSemiabelian.of_normal_abelian_not_le_frattini A hAcomm hAfr fun U hU => ?_
      have hlt : Nat.card ↥U < Nat.card G := Subgroup.card_lt_card_of_ne_top hU
      exact ih ↥U (by omega) inferInstance (Semiabelian.forall_sylow_comm_subgroup h U)

/-- **A finite solvable group all of whose Sylow subgroups are abelian is semiabelian.**  A
nontrivial such group has an abelian normal subgroup escaping the Frattini subgroup, obtained as a
Sylow subgroup of the preimage of a minimal normal subgroup of the Frattini quotient, and the
hypothesis passes to subgroups, so the supplementation criterion applies by induction on the
order. -/
theorem IsSemiabelian.of_forall_sylow_comm {G : Type} [Group G] [Finite G] [IsSolvable G]
    (h : ∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (x y : ↥(P : Subgroup G)), x * y = y * x) :
    IsSemiabelian G :=
  isSemiabelian_of_forall_sylow_comm_aux (Nat.card G) G le_rfl ‹IsSolvable G› h

/-- **Every finite solvable group of cubefree order is semiabelian.**  A Sylow `p`-subgroup of such
a group has order `1`, `p` or `p ^ 2`, and a group of any of those orders is commutative, so all
Sylow subgroups are abelian. -/
theorem IsSemiabelian.of_isSolvable_of_cubefree {G : Type} [Group G] [Finite G] [IsSolvable G]
    (h : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ Nat.card G) : IsSemiabelian G := by
  refine IsSemiabelian.of_forall_sylow_comm fun p hp P x y => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := P.2.exists_card_eq
  have hdvd : p ^ m ∣ Nat.card G := hm ▸ (P : Subgroup G).card_subgroup_dvd_card
  have hm2 : m ≤ 2 := by
    by_contra hlt
    exact h p hp ((pow_dvd_pow p (by omega)).trans hdvd)
  interval_cases m
  · haveI : Subsingleton ↥(P : Subgroup G) :=
      (Nat.card_eq_one_iff_unique.mp (by simpa using hm)).1
    exact Subsingleton.elim _ _
  · haveI : IsCyclic ↥(P : Subgroup G) := isCyclic_of_prime_card (by simpa using hm)
    exact IsCyclic.commutative.comm x y
  · exact IsPGroup.commutative_of_card_eq_prime_sq hm x y
