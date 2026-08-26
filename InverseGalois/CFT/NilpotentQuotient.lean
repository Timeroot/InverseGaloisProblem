/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.Frattini

/-!
# Quotients of prime order of a nilpotent group

A finite group whose order is divisible by a prime `ℓ` need not have a quotient of order `ℓ`: a
nonabelian simple group has no proper nontrivial quotient at all.  For nilpotent groups the
situation is as good as possible: every prime dividing the order of the group is the order of some
quotient.

The mechanism is the Frattini subgroup.  A Sylow `ℓ`-subgroup of a nilpotent group is normal, so
Schur–Zassenhaus provides a complement for it; were the Sylow subgroup contained in the Frattini
subgroup, that complement together with the non-generating Frattini subgroup would generate the
whole group, forcing the complement to be everything and the Sylow subgroup to be trivial.  So the
Sylow subgroup escapes some maximal subgroup `M`, which is normal because the group is nilpotent,
and `G / M` is then a nontrivial quotient of an `ℓ`-group.  A nontrivial finite `ℓ`-group has a
subgroup of index `ℓ`, normal because its index is the smallest prime factor of the order, and
pulling it back finishes the argument.

## Main results

* `InverseGalois.CFT.exists_normal_quotient_card_eq_of_isPGroup`: a nontrivial finite `ℓ`-group has
  a normal subgroup with quotient of order `ℓ`.
* `InverseGalois.CFT.exists_normal_quotient_card_eq_of_isNilpotent`: **a finite nilpotent group
  whose order is divisible by a prime `ℓ` has a normal subgroup with quotient of order `ℓ`.**

## Tags

nilpotent group, Frattini subgroup, Sylow subgroup, quotient of prime order
-/

namespace InverseGalois.CFT

open Subgroup

variable {G : Type*} [Group G] [Finite G] {ℓ : ℕ}

/-- **A nontrivial finite `ℓ`-group has a normal subgroup with quotient of order `ℓ`.**  Sylow's
first theorem produces a subgroup of index `ℓ`, and a subgroup whose index is the smallest prime
factor of the order of the group is normal. -/
theorem exists_normal_quotient_card_eq_of_isPGroup [Nontrivial G] (hℓ : ℓ.Prime)
    (hG : IsPGroup ℓ G) : ∃ N : Subgroup G, ∃ _ : N.Normal, Nat.card (G ⧸ N) = ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have hcard1 : Nat.card G ≠ 1 := Finite.one_lt_card.ne'
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hcard1 (by simpa using hn)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) ℓ (n := n - 1)
    (hn ▸ pow_dvd_pow ℓ (Nat.sub_le n 1))
  have hidx : K.index = ℓ := by
    have h : ℓ ^ (n - 1) * K.index = ℓ ^ (n - 1) * ℓ :=
      calc ℓ ^ (n - 1) * K.index = Nat.card G := by rw [← hK, K.card_mul_index]
        _ = ℓ ^ n := hn
        _ = ℓ ^ (n - 1) * ℓ := by rw [← pow_succ]; congr 1; omega
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hℓ.pos _) h
  have hminFac : (Nat.card G).minFac = ℓ := by
    have hp := Nat.minFac_prime hcard1
    have hdvd : (Nat.card G).minFac ∣ ℓ ^ n := by rw [← hn]; exact Nat.minFac_dvd _
    exact (Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hdvd)
  haveI : K.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hminFac])
  exact ⟨K, inferInstance, by rw [← Subgroup.index_eq_card, hidx]⟩

/-- A Sylow subgroup of a finite nilpotent group whose prime divides the order of the group is not
contained in the Frattini subgroup: a complement of the Sylow subgroup, which exists by
Schur–Zassenhaus, would otherwise generate the group together with the non-generating Frattini
subgroup, making the Sylow subgroup trivial. -/
theorem not_sylow_le_frattini [Group.IsNilpotent G] [hℓ : Fact ℓ.Prime] (P : Sylow ℓ G)
    (hdvd : ℓ ∣ Nat.card G) : ¬ (P : Subgroup G) ≤ frattini G := by
  intro hle
  have hsylow : ∀ (p : ℕ) (_hp : Fact p.Prime) (Q : Sylow p G), (Q : Subgroup G).Normal :=
    ((isNilpotent_of_finite_tfae (G := G)).out 0 3).mp (inferInstance : Group.IsNilpotent G)
  haveI : (P : Subgroup G).Normal := hsylow ℓ inferInstance P
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  have htop : K = ⊤ := by
    refine frattini_nongenerating (top_le_iff.mp ?_)
    rw [← hK.sup_eq_top]
    exact sup_le (hle.trans le_sup_right) le_sup_left
  have hcard : Nat.card ((P : Subgroup G)) * Nat.card G = 1 * Nat.card G := by
    rw [one_mul]
    conv_rhs => rw [← hK.card_mul, htop, Nat.card_congr Subgroup.topEquiv.toEquiv]
  have hP1 : Nat.card ((P : Subgroup G)) = 1 := Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard
  exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp (hP1 ▸ P.dvd_card_of_dvd_card hdvd))

/-- **A finite nilpotent group whose order is divisible by a prime `ℓ` has a normal subgroup with
quotient of order `ℓ`.**  A Sylow `ℓ`-subgroup escapes some maximal subgroup, which is normal
because the group is nilpotent, so the corresponding quotient is a nontrivial `ℓ`-group; a quotient
of order `ℓ` of that group pulls back to one of the whole group. -/
theorem exists_normal_quotient_card_eq_of_isNilpotent [Group.IsNilpotent G] (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card G) : ∃ N : Subgroup G, ∃ _ : N.Normal, Nat.card (G ⧸ N) = ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P⟩ : Nonempty (Sylow ℓ G) := inferInstance
  obtain ⟨U, hUne, hUsup⟩ :=
    Shafarevich.exists_proper_supplement_of_not_le_frattini (not_sylow_le_frattini P hdvd)
  obtain ⟨M, hM, hUM⟩ := (eq_top_or_exists_le_coatom U).resolve_left hUne
  have hcoatom : ∀ H : Subgroup G, IsCoatom H → H.Normal :=
    ((isNilpotent_of_finite_tfae (G := G)).out 0 2).mp (inferInstance : Group.IsNilpotent G)
  haveI : M.Normal := hcoatom M hM
  have hMtop : (P : Subgroup G) ⊔ M = ⊤ := top_le_iff.mp (hUsup ▸ sup_le_sup_left hUM _)
  have hφsurj : Function.Surjective ((QuotientGroup.mk' M).comp (P : Subgroup G).subtype) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M x
    have hg : g ∈ (P : Subgroup G) ⊔ M := hMtop ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    refine ⟨⟨a, ha⟩, ?_⟩
    show (QuotientGroup.mk' M) a = (QuotientGroup.mk' M) (a * b)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq.mpr (by simpa using hb)
  haveI : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM.1
  obtain ⟨N, hN, hNcard⟩ :=
    exists_normal_quotient_card_eq_of_isPGroup hℓ (P.isPGroup'.of_surjective _ hφsurj)
  haveI := hN
  have hψsurj : Function.Surjective ((QuotientGroup.mk' N).comp (QuotientGroup.mk' M)) :=
    (QuotientGroup.mk'_surjective N).comp (QuotientGroup.mk'_surjective M)
  refine ⟨((QuotientGroup.mk' N).comp (QuotientGroup.mk' M)).ker, inferInstance, ?_⟩
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hψsurj).toEquiv, hNcard]

end InverseGalois.CFT
