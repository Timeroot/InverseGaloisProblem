/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Corestriction
import InverseGalois.CFT.Profinite.ShaComap

/-!
# Locally trivial classes restricted to a subgroup of finite index

A family of subgroups of a group cuts out the classes of cohomology dying on every member of the
family.  Intersecting the family with a subgroup gives a family of subgroups of that subgroup, and
restriction carries the classes dying on the first family to the classes dying on the second: every
member of the intersected family is carried by the inclusion into the member it was cut from.

Restriction loses nothing when the index of the subgroup is prime to the order of the class.
Corestriction after restriction is raising to the index, so a class dying on the subgroup is killed
by the index; if it is also killed by a number prime to the index, it is trivial.  Putting the two
together, a locally trivial class whose order is prime to the index is trivial as soon as every
locally trivial class of that order over the subgroup is, which is how a question about locally
trivial classes of `p`-power order is moved to a Sylow `p`-subgroup.

## Main definitions

* `InverseGalois.CFT.restrictFamily`: the family of subgroups of a subgroup cut out by a family of
  subgroups of the whole group.

## Main results

* `InverseGalois.CFT.resH1_mem_sha1`, `InverseGalois.CFT.resH2_mem_sha2`: **restriction to a
  subgroup carries a locally trivial class to a locally trivial class**, for the family cut out on
  the subgroup.
* `InverseGalois.CFT.pow_index_eq_one_of_resH1_eq_one`,
  `InverseGalois.CFT.pow_index_eq_one_of_resH2_eq_one`: a class dying on a subgroup of finite index
  is killed by the index.
* `InverseGalois.CFT.eq_one_of_mem_sha1_of_coprime`,
  `InverseGalois.CFT.eq_one_of_mem_sha2_of_coprime`: **a locally trivial class whose order is prime
  to the index of a subgroup is trivial as soon as every locally trivial class of that order over
  the subgroup is**, and
  `InverseGalois.CFT.eq_one_of_mem_sha1_of_coprime_of_isOpen`,
  `InverseGalois.CFT.eq_one_of_mem_sha2_of_coprime_of_isOpen` for an open subgroup of a compact
  group, where the finiteness of the index and the open normal core come for free.

## Tags

profinite group, Galois cohomology, restriction, corestriction, local-global principle, Sylow
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The family of subgroups cut out on a subgroup -/

section Family

variable {G : Type*} [Group G] (H : Subgroup G)

/-- The family of subgroups of a subgroup obtained by intersecting a family of subgroups of the
whole group with it. -/
def restrictFamily (S : Set (Subgroup G)) : Set (Subgroup ↥H) :=
  (fun D : Subgroup G => D.comap H.subtype) '' S

theorem mem_restrictFamily {S : Set (Subgroup G)} {D' : Subgroup ↥H} :
    D' ∈ restrictFamily H S ↔ ∃ D ∈ S, D.comap H.subtype = D' := Iff.rfl

/-- Every subgroup of the restricted family is carried by the inclusion into the subgroup it was
cut from. -/
theorem restrictFamily_le (S : Set (Subgroup G)) :
    ∀ D' ∈ restrictFamily H S, ∃ D ∈ S, ∀ x ∈ D', H.subtype x ∈ D := by
  rintro D' ⟨D, hD, rfl⟩
  exact ⟨D, hD, fun _ hx => hx⟩

/-- The projection onto the cosets of a subgroup has a section. -/
theorem exists_quotientSection : ∃ σ : G ⧸ H → G, ∀ x : G ⧸ H, (σ x : G ⧸ H) = x :=
  ⟨Quotient.out, fun x => x.out_eq'⟩

end Family

/-! ### Restriction preserves local triviality -/

section Restrict

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) {M : Type*} [CommGroup M]
  [MulDistribMulAction G M]

/-- **Restriction to a subgroup carries a locally trivial class of the first cohomology to a
locally trivial class**, for the family of subgroups cut out on the subgroup. -/
theorem resH1_mem_sha1 {S : Set (Subgroup G)} {z : SmoothH1 G M} (hz : z ∈ sha1 M S) :
    resH1 H z ∈ sha1 M (restrictFamily H S) :=
  comapH1_mem_sha1 (fun _ _ => rfl) (isSmoothHom_subtype H) (continuous_subtype H)
    (restrictFamily_le H S) hz

/-- **Restriction to a subgroup carries a locally trivial class of the second cohomology to a
locally trivial class**, for the family of subgroups cut out on the subgroup. -/
theorem resH2_mem_sha2 {S : Set (Subgroup G)} {z : SmoothH2 G M} (hz : z ∈ sha2 M S) :
    resH2 H z ∈ sha2 M (restrictFamily H S) :=
  comapH2_mem_sha2 (fun _ _ => rfl) (isSmoothHom_subtype H) (continuous_subtype H)
    (restrictFamily_le H S) hz

end Restrict

/-! ### What restriction to a subgroup of finite index can lose -/

section Index

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) {M : Type*} [CommGroup M]
  [MulDistribMulAction G M] [Fintype (G ⧸ H)]

/-- **A class of the first cohomology dying on a subgroup of finite index is killed by the
index**, corestriction after restriction being raising to the index. -/
theorem pow_index_eq_one_of_resH1_eq_one (hcore : HasOpenNormalCore H) {z : SmoothH1 G M}
    (hz : resH1 H z = 1) : z ^ H.index = 1 := by
  obtain ⟨σ, hσ⟩ := exists_quotientSection H
  have h := corH1_resH1 H σ hσ hcore z
  rw [hz, map_one] at h
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  exact h.symm

/-- **A class of the second cohomology dying on a subgroup of finite index is killed by the
index**, corestriction after restriction being raising to the index. -/
theorem pow_index_eq_one_of_resH2_eq_one (hcore : HasOpenNormalCore H) {z : SmoothH2 G M}
    (hz : resH2 H z = 1) : z ^ H.index = 1 := by
  obtain ⟨σ, hσ⟩ := exists_quotientSection H
  have h := corH2_resH2 H σ hσ hcore z
  rw [hz, map_one] at h
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  exact h.symm

/-- **A class of the first cohomology killed by a number prime to the index of a subgroup and dying
on that subgroup is trivial**, its order dividing both the number and the index. -/
theorem eq_one_of_resH1_eq_one_of_coprime (hcore : HasOpenNormalCore H) {n : ℕ}
    (hcop : Nat.Coprime n H.index) {z : SmoothH1 G M} (hzn : z ^ n = 1) (hz : resH1 H z = 1) :
    z = 1 := by
  have hdvd : orderOf z ∣ Nat.gcd n H.index :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzn)
      (orderOf_dvd_of_pow_eq_one (pow_index_eq_one_of_resH1_eq_one H hcore hz))
  rw [hcop.gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)

/-- **A class of the second cohomology killed by a number prime to the index of a subgroup and
dying on that subgroup is trivial**, its order dividing both the number and the index. -/
theorem eq_one_of_resH2_eq_one_of_coprime (hcore : HasOpenNormalCore H) {n : ℕ}
    (hcop : Nat.Coprime n H.index) {z : SmoothH2 G M} (hzn : z ^ n = 1) (hz : resH2 H z = 1) :
    z = 1 := by
  have hdvd : orderOf z ∣ Nat.gcd n H.index :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzn)
      (orderOf_dvd_of_pow_eq_one (pow_index_eq_one_of_resH2_eq_one H hcore hz))
  rw [hcop.gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)

/-- **A locally trivial class of the first cohomology whose order is prime to the index of a
subgroup is trivial as soon as every locally trivial class of that order over the subgroup is.**
This is what moves a question about locally trivial classes of `p`-power order to a Sylow
`p`-subgroup. -/
theorem eq_one_of_mem_sha1_of_coprime (hcore : HasOpenNormalCore H) {S : Set (Subgroup G)} {n : ℕ}
    (hcop : Nat.Coprime n H.index)
    (hsub : ∀ y ∈ sha1 M (restrictFamily H S), y ^ n = 1 → y = 1)
    {z : SmoothH1 G M} (hz : z ∈ sha1 M S) (hzn : z ^ n = 1) : z = 1 :=
  eq_one_of_resH1_eq_one_of_coprime H hcore hcop hzn
    (hsub _ (resH1_mem_sha1 H hz) (by rw [← _root_.map_pow, hzn, _root_.map_one]))

/-- **A locally trivial class of the second cohomology whose order is prime to the index of a
subgroup is trivial as soon as every locally trivial class of that order over the subgroup is.**
This is what moves a question about locally trivial classes of `p`-power order to a Sylow
`p`-subgroup. -/
theorem eq_one_of_mem_sha2_of_coprime (hcore : HasOpenNormalCore H) {S : Set (Subgroup G)} {n : ℕ}
    (hcop : Nat.Coprime n H.index)
    (hsub : ∀ y ∈ sha2 M (restrictFamily H S), y ^ n = 1 → y = 1)
    {z : SmoothH2 G M} (hz : z ∈ sha2 M S) (hzn : z ^ n = 1) : z = 1 :=
  eq_one_of_resH2_eq_one_of_coprime H hcore hcop hzn
    (hsub _ (resH2_mem_sha2 H hz) (by rw [← _root_.map_pow, hzn, _root_.map_one]))

end Index

/-! ### Open subgroups of a compact group -/

section Compact

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (H : Subgroup G) {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- **An everywhere locally trivial class of the first cohomology whose order is prime to the index
of an open subgroup is trivial as soon as every locally trivial class of that order over the
subgroup is.**  An open subgroup of a compact group has finite index and an open normal core, which
is all the reduction to it asks for. -/
theorem eq_one_of_mem_sha1_of_coprime_of_isOpen (hH : IsOpen (H : Set G)) {S : Set (Subgroup G)}
    {n : ℕ} (hcop : Nat.Coprime n H.index)
    (hsub : ∀ y ∈ sha1 M (restrictFamily H S), y ^ n = 1 → y = 1)
    {z : SmoothH1 G M} (hz : z ∈ sha1 M S) (hzn : z ^ n = 1) : z = 1 := by
  haveI : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen _ hH
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  exact eq_one_of_mem_sha1_of_coprime H (hasOpenNormalCore_of_isOpen H hH) hcop hsub hz hzn

/-- **An everywhere locally trivial class of the second cohomology whose order is prime to the index
of an open subgroup is trivial as soon as every locally trivial class of that order over the
subgroup is.**  An open subgroup of a compact group has finite index and an open normal core, which
is all the reduction to it asks for. -/
theorem eq_one_of_mem_sha2_of_coprime_of_isOpen (hH : IsOpen (H : Set G)) {S : Set (Subgroup G)}
    {n : ℕ} (hcop : Nat.Coprime n H.index)
    (hsub : ∀ y ∈ sha2 M (restrictFamily H S), y ^ n = 1 → y = 1)
    {z : SmoothH2 G M} (hz : z ∈ sha2 M S) (hzn : z ^ n = 1) : z = 1 := by
  haveI : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen _ hH
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  exact eq_one_of_mem_sha2_of_coprime H (hasOpenNormalCore_of_isOpen H hH) hcop hsub hz hzn

end Compact

end InverseGalois.CFT
