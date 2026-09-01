/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.H2Sylow
import InverseGalois.CFT.GroupCohomology.H2Transport
import InverseGalois.CFT.Units.IdeleClassH1Full
import InverseGalois.CFT.Units.IdeleClassH2
import InverseGalois.CFT.Units.IdeleClassH2Tower

/-!
# The second cohomology of the idele class group of an arbitrary Galois extension

For a cyclic extension the second cohomology of the idele class group has exactly as many elements
as the Galois group.  Two dévissages turn that into the inequality for every Galois extension of
number fields.

The first is the tower: a group of prime-power order has a normal subgroup of index the prime, so
the extension breaks into a cyclic extension of prime degree at the bottom and an extension of
smaller prime-power degree on top, and the two counts multiply, exactly matching the degree.
Induction on the exponent therefore settles every extension of prime-power degree.

The second is Sylow's theorem: a class restricting to zero on every Sylow subgroup is zero, so the
second cohomology embeds into the product over the primes of the second cohomology of the Sylow
subgroups; restriction to a subgroup is the cohomology of the same idele class group for the
extension over its fixed field, whose degree is the order of the subgroup, which is a prime power.

## Main definitions

* `InverseGalois.CFT.ideleClassRepRes`: the idele class group, as a representation of a subgroup of
  the Galois group.

## Main results

* `InverseGalois.CFT.card_H2_res_subgroup`: the second cohomology of the restriction of the
  representation to a subgroup is the second cohomology over the fixed field of that subgroup.
* `InverseGalois.CFT.finite_and_card_H2_ideleClassRep_of_card_eq_pow`: the second cohomology of the
  idele class group of an extension of prime-power degree is finite, with at most as many elements
  as the degree.
* `InverseGalois.CFT.finite_and_card_H2_ideleClassRep_general`: **the second cohomology of the idele
  class group of an arbitrary Galois extension of number fields is finite and has at most as many
  elements as the Galois group.**
* `InverseGalois.CFT.finite_and_card_H2_res_subgroup`: the same statement for the restriction of the
  representation to a subgroup of the Galois group.

## Tags

number field, idele class group, group cohomology, Sylow subgroup, dévissage
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open groupCohomology

namespace InverseGalois.CFT

section Full

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

variable (k K) in
omit [IsGalois k K] in
/-- The idele class group of the top field, as a representation of a subgroup of the Galois
group. -/
noncomputable abbrev ideleClassRepRes (S : Subgroup Gal(K/k)) : Rep ℤ ↥S :=
  (Action.res _ S.subtype).obj (ideleClassRep k K)

variable (k K) in
omit [IsGalois k K] in
/-- An element of a subgroup of the Galois group acts on the idele class group as the corresponding
automorphism over the fixed field of that subgroup. -/
theorem ideleClassRepRes_rho (S : Subgroup Gal(K/k)) (g : ↥S) (a : IdeleClass K) :
    (ideleClassRepRes k K S).ρ g a
      = (ideleClassRep ↥(IntermediateField.fixedField S) K).ρ
          (IntermediateField.subgroupEquivAlgEquiv S g) a := by
  have hrs : (IntermediateField.subgroupEquivAlgEquiv S g).restrictScalars k = (g : Gal(K/k)) :=
    AlgEquiv.ext fun _ => rfl
  show ideleClassAutHom k K (g : Gal(K/k)) a
    = ideleClassAutHom ↥(IntermediateField.fixedField S) K
        (IntermediateField.subgroupEquivAlgEquiv S g) a
  rw [← ideleClassAutHom_restrictScalars k (IntermediateField.subgroupEquivAlgEquiv S g), hrs]

omit [IsGalois k K] in
/-- The restriction of the representation on the idele class group to a subgroup of the Galois
group is the representation attached to the extension over the fixed field of that subgroup, so the
two second cohomology groups have the same number of elements. -/
theorem card_H2_res_subgroup (S : Subgroup Gal(K/k)) :
    Nat.card ↥(H2 (ideleClassRepRes k K S))
      = Nat.card ↥(H2 (ideleClassRep ↥(IntermediateField.fixedField S) K)) :=
  card_H2_eq_of_addEquiv (C := ideleClassRepRes k K S)
    (D := ideleClassRep ↥(IntermediateField.fixedField S) K)
    (IntermediateField.subgroupEquivAlgEquiv S) (AddEquiv.refl (IdeleClass K))
    (fun g a => ideleClassRepRes_rho k K S g a)

omit [IsGalois k K] in
/-- The second cohomology of the restriction of the representation to a subgroup of the Galois
group is finite as soon as the second cohomology over the fixed field of that subgroup is. -/
theorem finite_H2_res_subgroup (S : Subgroup Gal(K/k))
    [Finite ↥(H2 (ideleClassRep ↥(IntermediateField.fixedField S) K))] :
    Finite ↥(H2 (ideleClassRepRes k K S)) :=
  finite_H2_of_addEquiv (C := ideleClassRepRes k K S)
    (D := ideleClassRep ↥(IntermediateField.fixedField S) K)
    (IntermediateField.subgroupEquivAlgEquiv S) (AddEquiv.refl (IdeleClass K))
    (fun g a => ideleClassRepRes_rho k K S g a)

/-- **The second cohomology of the idele class group of an extension of prime-power degree is
finite, with at most as many elements as the degree.**  A group of order `p ^ (n + 1)` has a
subgroup of order `p ^ n`, whose index is the smallest prime factor of the order and which is
therefore normal; the extension splits into a cyclic extension of degree `p` at the bottom and an
extension of degree `p ^ n` on top. -/
theorem finite_and_card_H2_ideleClassRep_of_card_eq_pow (p : ℕ) (hp : p.Prime) :
    ∀ (n : ℕ) (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
      [Algebra k K] [IsGalois k K], Nat.card Gal(K/k) = p ^ n →
      Finite ↥(H2 (ideleClassRep k K)) ∧ Nat.card ↥(H2 (ideleClassRep k K)) ≤ p ^ n := by
  haveI := Fact.mk hp
  intro n
  induction n with
  | zero =>
    intro k K _ _ _ _ _ _ hcard
    rw [pow_zero] at hcard
    haveI : Subsingleton Gal(K/k) := (Nat.card_eq_one_iff_unique.mp hcard).1
    refine ⟨finite_H2_ideleClassRep_cyclic, ?_⟩
    rw [card_H2_ideleClassRep_cyclic, hcard]
    exact (pow_zero p).ge
  | succ n ih =>
    intro k K _ _ _ _ _ _ hcard
    obtain ⟨N, hN⟩ := Sylow.exists_subgroup_card_pow_prime (G := Gal(K/k)) p (n := n)
      (by rw [hcard]; exact pow_dvd_pow p (Nat.le_succ n))
    have hidx : N.index = p := by
      have hmul := N.card_mul_index
      rw [hN, hcard, pow_succ] at hmul
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos n) hmul
    haveI : N.Normal := by
      refine Subgroup.normal_of_index_eq_minFac_card ?_
      rw [hidx, hcard, Nat.pow_minFac (Nat.succ_ne_zero n), hp.minFac_eq]
    have hcardF : Nat.card Gal(↥(IntermediateField.fixedField N)/k) = p := by
      rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv]
      exact hidx
    haveI : IsCyclic Gal(↥(IntermediateField.fixedField N)/k) := isCyclic_of_prime_card hcardF
    have hcardK : Nat.card Gal(K/↥(IntermediateField.fixedField N)) = p ^ n := by
      rw [← Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv N).toEquiv]
      exact hN
    obtain ⟨hfinK, hleK⟩ := ih ↥(IntermediateField.fixedField N) K hcardK
    haveI := hfinK
    haveI : Finite ↥(H2 (ideleClassRep k ↥(IntermediateField.fixedField N))) :=
      finite_H2_ideleClassRep_cyclic
    obtain ⟨hfin, hle⟩ := finite_and_card_H2_ideleClassRep_of_tower
      (k := k) (F := ↥(IntermediateField.fixedField N)) (K := K)
      (fun y => eq_zero_H1_ideleClassRep_general
        (k := ↥(IntermediateField.fixedField N)) (K := K) y)
    refine ⟨hfin, hle.trans ?_⟩
    rw [card_H2_ideleClassRep_cyclic (k := k) (K := ↥(IntermediateField.fixedField N)), hcardF]
    calc p * Nat.card ↥(H2 (ideleClassRep ↥(IntermediateField.fixedField N) K))
        ≤ p * p ^ n := Nat.mul_le_mul le_rfl hleK
      _ = p ^ (n + 1) := by ring

/-- **The second cohomology of the idele class group of an arbitrary Galois extension of number
fields is finite and has at most as many elements as the Galois group.**  Restriction to the Sylow
subgroups is injective, and each Sylow subgroup fixes a field over which the extension has
prime-power degree. -/
theorem finite_and_card_H2_ideleClassRep_general :
    Finite ↥(H2 (ideleClassRep k K)) ∧
      Nat.card ↥(H2 (ideleClassRep k K)) ≤ Nat.card Gal(K/k) := by
  refine finite_and_card_H2_le_of_sylow (ideleClassRep k K) fun p hp P => ?_
  haveI := Fact.mk hp
  obtain ⟨m, hm⟩ := P.2.exists_card_eq
  have hcardP :
      Nat.card Gal(K/↥(IntermediateField.fixedField (P : Subgroup Gal(K/k)))) = p ^ m := by
    rw [← Nat.card_congr
      (IntermediateField.subgroupEquivAlgEquiv (P : Subgroup Gal(K/k))).toEquiv]
    exact hm
  obtain ⟨hfinF, hleF⟩ := finite_and_card_H2_ideleClassRep_of_card_eq_pow p hp m
    ↥(IntermediateField.fixedField (P : Subgroup Gal(K/k))) K hcardP
  haveI := hfinF
  exact ⟨finite_H2_res_subgroup (P : Subgroup Gal(K/k)),
    (le_of_eq (card_H2_res_subgroup (P : Subgroup Gal(K/k)))).trans
      (hleF.trans (le_of_eq hm.symm))⟩

/-- **The second cohomology of the restriction of the idele class group to a subgroup of the Galois
group is finite and has at most as many elements as the subgroup.** -/
theorem finite_and_card_H2_res_subgroup (S : Subgroup Gal(K/k)) :
    Finite ↥(H2 (ideleClassRepRes k K S)) ∧
      Nat.card ↥(H2 (ideleClassRepRes k K S)) ≤ Nat.card ↥S := by
  obtain ⟨hfin, hle⟩ := finite_and_card_H2_ideleClassRep_general
    (k := ↥(IntermediateField.fixedField S)) (K := K)
  haveI := hfin
  refine ⟨finite_H2_res_subgroup S, ?_⟩
  rw [card_H2_res_subgroup]
  exact hle.trans
    (le_of_eq (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv S).toEquiv).symm)

end Full

end InverseGalois.CFT
