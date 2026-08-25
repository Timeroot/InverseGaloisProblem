/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.H1Transport
import InverseGalois.CFT.GroupCohomology.SylowRes
import InverseGalois.CFT.Units.IdeleClassH1
import InverseGalois.CFT.Units.IdeleClassTower

/-!
# The first cohomology of the idele class group of an arbitrary Galois extension

The first cohomology of the idele class group vanishes for a cyclic extension.  Two dévissages
extend that to every Galois extension of number fields.

The first is the tower: a group of prime-power order has a normal subgroup of index the prime, so
the extension breaks into a cyclic extension of prime degree at the bottom and an extension of
smaller prime-power degree on top, and the vanishing propagates along the tower.  Induction on the
exponent therefore settles every extension of prime-power degree.

The second is Sylow's theorem: restriction to a subgroup followed by corestriction is multiplication
by the index, so a class restricting to zero on a Sylow subgroup is annihilated by an index prime to
that prime.  Doing this for every prime dividing the degree kills the class.  Restriction to a
subgroup is the cohomology of the same idele class group for the extension over the fixed field of
that subgroup, whose degree is the order of the subgroup, which is a prime power.

## Main results

* `InverseGalois.CFT.eq_zero_H1_res_subgroup`: the first cohomology of the restriction of the
  representation to a subgroup is the first cohomology over the fixed field of that subgroup.
* `InverseGalois.CFT.eq_zero_H1_ideleClassRep_of_card_eq_pow`: the first cohomology of the idele
  class group of an extension of prime-power degree vanishes.
* `InverseGalois.CFT.eq_zero_H1_ideleClassRep_general`: **the first cohomology of the idele class
  group of an arbitrary Galois extension of number fields vanishes.**
* `InverseGalois.CFT.subsingleton_H1_ideleClassRep_general`: the same statement, as a
  `Subsingleton` instance.

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

omit [IsGalois k K] in
/-- The restriction of the representation on the idele class group to a subgroup of the Galois
group is the representation attached to the extension over the fixed field of that subgroup, so its
first cohomology vanishes as soon as the first cohomology over the fixed field does. -/
theorem eq_zero_H1_res_subgroup (S : Subgroup Gal(K/k))
    (hS : ∀ y : groupCohomology (ideleClassRep ↥(IntermediateField.fixedField S) K) 1, y = 0)
    (y : groupCohomology ((Action.res _ S.subtype).obj (ideleClassRep k K)) 1) : y = 0 := by
  refine eq_zero_H1_of_mulEquiv (IntermediateField.subgroupEquivAlgEquiv S)
    (LinearEquiv.refl ℤ (IdeleClass K)) ?_ hS y
  intro g a
  have hrs : (IntermediateField.subgroupEquivAlgEquiv S g).restrictScalars k = (g : Gal(K/k)) :=
    AlgEquiv.ext fun _ => rfl
  have h2 : ideleClassAutHom k K (g : Gal(K/k))
      = ideleClassAutHom (↥(IntermediateField.fixedField S)) K
          (IntermediateField.subgroupEquivAlgEquiv S g) := by
    rw [← ideleClassAutHom_restrictScalars k (IntermediateField.subgroupEquivAlgEquiv S g), hrs]
  exact DFunLike.congr_fun h2 a

/-- **The first cohomology of the idele class group of an extension of prime-power degree
vanishes.**  A group of order `p ^ (n + 1)` has a subgroup of order `p ^ n`, whose index is the
smallest prime factor of the order and which is therefore normal; the extension splits into a cyclic
extension of degree `p` at the bottom and an extension of degree `p ^ n` on top. -/
theorem eq_zero_H1_ideleClassRep_of_card_eq_pow (p : ℕ) (hp : p.Prime) :
    ∀ (n : ℕ) (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
      [Algebra k K] [IsGalois k K], Nat.card Gal(K/k) = p ^ n →
      ∀ z : groupCohomology (ideleClassRep k K) 1, z = 0 := by
  haveI := Fact.mk hp
  intro n
  induction n with
  | zero =>
    intro k K _ _ _ _ _ _ hcard z
    rw [pow_zero] at hcard
    haveI : Subsingleton Gal(K/k) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact eq_zero_H1_ideleClassRep z
  | succ n ih =>
    intro k K _ _ _ _ _ _ hcard z
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
    exact eq_zero_H1_ideleClassRep_of_tower (F := ↥(IntermediateField.fixedField N))
      (fun y => eq_zero_H1_ideleClassRep y)
      (ih ↥(IntermediateField.fixedField N) K hcardK) z

/-- **The first cohomology of the idele class group of an arbitrary Galois extension of number
fields vanishes.**  For each prime dividing the degree, a Sylow subgroup has index prime to it and
its fixed field carries an extension of prime-power degree, over which the cohomology already
vanishes. -/
theorem eq_zero_H1_ideleClassRep_general (z : groupCohomology (ideleClassRep k K) 1) : z = 0 := by
  refine eq_zero_of_forall_prime_res _ z (fun p hp _ => ?_)
  haveI := Fact.mk hp
  obtain ⟨P⟩ : Nonempty (Sylow p Gal(K/k)) := inferInstance
  refine ⟨P.1, P.not_dvd_index, ?_⟩
  obtain ⟨m, hm⟩ := P.2.exists_card_eq
  refine eq_zero_H1_res_subgroup P.1 (fun y => ?_) _
  refine eq_zero_H1_ideleClassRep_of_card_eq_pow p hp m
    ↥(IntermediateField.fixedField P.1) K ?_ y
  rw [← Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv P.1).toEquiv]
  exact hm

/-- The first cohomology of the idele class group of a Galois extension of number fields has at
most one element. -/
instance subsingleton_H1_ideleClassRep_general :
    Subsingleton (groupCohomology (ideleClassRep k K) 1) :=
  ⟨fun x y => by rw [eq_zero_H1_ideleClassRep_general x, eq_zero_H1_ideleClassRep_general y]⟩

end Full

end InverseGalois.CFT
