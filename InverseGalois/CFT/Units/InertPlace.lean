/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.RelativeFrobenius
import InverseGalois.CFT.Units.DecompositionOutside
import InverseGalois.CFT.Units.FrobeniusPlace

/-!
# A place of a cyclic extension of prime power degree that stays prime

The decomposition groups at the finite places of a solvable Galois extension of number fields
generate the Galois group, and they still do after discarding the places lying over a prescribed
finite set of places of the base.  So no proper subgroup contains all of them: for every proper
subgroup there is a place, away from the prescribed set, whose decomposition group escapes it.

For a cyclic extension the elements killed by a fixed exponent form a subgroup, so an exponent that
does not kill a generator does not kill some element of some decomposition group away from the
prescribed set.  When the degree is a power of a prime the orders of the elements are powers of that
prime and hence totally ordered by divisibility, so an element escaping the largest proper exponent
has the same order as a generator and therefore generates: the decomposition group at that place is
the whole Galois group.  Discarding the finitely many ramified places as well makes the arithmetic
Frobenius there a generator, which is the density statement that a cyclic extension of prime power
degree needs, with no analysis at all.

## Main results

* `InverseGalois.CFT.exists_stabilizer_not_le`: **no proper subgroup of a solvable Galois group
  contains every decomposition group away from a finite set of places of the base.**
* `InverseGalois.CFT.exists_mem_stabilizer_pow_ne_one`: for a cyclic extension, an exponent which
  does not kill a generator of the Galois group does not kill some element of the decomposition
  group at some place away from a finite set of places of the base.
* `InverseGalois.CFT.exists_card_stabilizer_not_dvd`: **the orders of the decomposition groups of a
  cyclic extension have the degree as their least common multiple**, even after discarding finitely
  many places of the base.
* `InverseGalois.CFT.exists_stabilizer_eq_top_of_isPGroup`: **a cyclic extension of prime power
  degree has a finite place, away from a prescribed finite set of places of the base, whose
  decomposition group is the whole Galois group.**
* `InverseGalois.CFT.exists_arithFrobAt_zpowers_eq_top`: **a cyclic extension of prime power degree
  has an unramified finite place, away from a prescribed finite set of places of the base, whose
  arithmetic Frobenius generates the Galois group.**

## Tags

number field, decomposition group, cyclic extension, Frobenius, inert prime, class field theory
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain MulAction InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

section InertPlace

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {S : Set (HeightOneSpectrum (𝓞 k))} {σ₀ : Gal(K/k)}

/-- **No proper subgroup of a solvable Galois group contains every decomposition group away from a
finite set of places of the base.**  Those decomposition groups generate the whole Galois group. -/
theorem exists_stabilizer_not_le [IsSolvable Gal(K/k)] (hS : S.Finite) {H : Subgroup Gal(K/k)}
    (hH : H ≠ ⊤) :
    ∃ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S ∧ ¬ stabilizer Gal(K/k) v ≤ H := by
  by_contra hc
  push_neg at hc
  refine hH (eq_top_iff.mpr ?_)
  rw [← decompositionSubgroupOutside_eq_top k K hS]
  show Subgroup.closure (decompositionSetOutside k K S) ≤ H
  refine (Subgroup.closure_le H).mpr ?_
  rintro σ ⟨v, hvS, hv⟩
  exact hc v hvS (mem_stabilizer_iff.mpr hv)

/-- **An exponent which does not kill a generator of the Galois group of a cyclic extension does not
kill the decomposition group at some place away from a finite set of places of the base.**  The
elements killed by a fixed exponent are closed under multiplication, the group being commutative, so
were they to contain every such decomposition group they would contain the generator. -/
theorem exists_mem_stabilizer_pow_ne_one (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀)
    (hS : S.Finite) {m : ℕ} (hm : σ₀ ^ m ≠ 1) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (τ : Gal(K/k)), primeUnder (𝓞 k) v ∉ S ∧
      τ ∈ stabilizer Gal(K/k) v ∧ τ ^ m ≠ 1 := by
  have hcomm : ∀ a b : Gal(K/k), a * b = b * a := by
    intro a b
    obtain ⟨i, hi⟩ := hσ₀ a
    obtain ⟨j, hj⟩ := hσ₀ b
    subst hi
    subst hj
    exact ((Commute.refl σ₀).zpow_zpow i j).eq
  haveI : IsSolvable Gal(K/k) := isSolvable_of_comm hcomm
  by_contra hc
  push_neg at hc
  refine hm ?_
  have hall : ∀ x ∈ decompositionSubgroupOutside k K S, x ^ m = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hvS, hv⟩ := hy
      exact hc v y hvS (mem_stabilizer_iff.mpr hv)
    | one => exact one_pow m
    | mul a b _ _ ha hb =>
      have hab : Commute a b := hcomm a b
      rw [hab.mul_pow, ha, hb, one_mul]
    | inv a _ ha => rw [inv_pow, ha, inv_one]
  refine hall σ₀ ?_
  rw [decompositionSubgroupOutside_eq_top k K hS]
  exact Subgroup.mem_top σ₀

/-- **The order of the decomposition group at some place away from a finite set of places of the
base fails to divide any exponent which does not kill a generator.**  So the orders of the
decomposition groups of a cyclic extension have the degree as their least common multiple, even
after discarding finitely many places of the base. -/
theorem exists_card_stabilizer_not_dvd (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀)
    (hS : S.Finite) {m : ℕ} (hm : σ₀ ^ m ≠ 1) :
    ∃ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S ∧
      ¬ Nat.card ↥(stabilizer Gal(K/k) v) ∣ m := by
  obtain ⟨v, τ, hvS, hτ, hτm⟩ := exists_mem_stabilizer_pow_ne_one hσ₀ hS hm
  refine ⟨v, hvS, fun hdvd => hτm (orderOf_dvd_iff_pow_eq_one.mp (dvd_trans ?_ hdvd))⟩
  rw [← Subgroup.orderOf_mk _ hτ]
  exact orderOf_dvd_natCard _

/-- **A cyclic extension of prime power degree has a finite place, away from a prescribed finite set
of places of the base, whose decomposition group is the whole Galois group.**  The orders of the
elements are powers of the prime, so an element which escapes the largest proper exponent has the
order of a generator, and a group generated by one element is exhausted by the powers of any element
of the same order. -/
theorem exists_stabilizer_eq_top_of_isPGroup {p : ℕ} (hp : p.Prime)
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (hne : σ₀ ≠ 1)
    (hpG : IsPGroup p Gal(K/k)) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ∉ S ∧ stabilizer Gal(K/k) v = ⊤ := by
  haveI := Fact.mk hp
  have htop : Subgroup.zpowers σ₀ = ⊤ := (Subgroup.eq_top_iff' _).mpr hσ₀
  obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hpG σ₀
  have hane : a ≠ 0 := by
    intro h
    rw [h, pow_zero] at ha
    exact hne (orderOf_eq_one_iff.mp ha)
  -- the largest exponent that a proper subgroup can carry does not kill the generator
  have hm : σ₀ ^ (p ^ (a - 1)) ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [ha] at hdvd
    have hle := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
    omega
  obtain ⟨v, τ, hvS, hτ, hτm⟩ := exists_mem_stabilizer_pow_ne_one hσ₀ hS hm
  refine ⟨v, hvS, ?_⟩
  obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.mp hpG τ
  -- the escaping element has the order of the generator
  have hle : b ≤ a := by
    have hdvd : orderOf τ ∣ orderOf σ₀ := by
      obtain ⟨i, hi⟩ := hσ₀ τ
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, one_zpow]
    rw [ha, hb] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hge : a ≤ b := by
    by_contra hlt
    push_neg at hlt
    refine hτm (orderOf_dvd_iff_pow_eq_one.mp ?_)
    rw [hb]
    exact pow_dvd_pow p (by omega)
  have hba : b = a := le_antisymm hle hge
  -- so its powers exhaust the Galois group
  have hcard : Nat.card ↥(Subgroup.zpowers τ) = Nat.card Gal(K/k) := by
    rw [Nat.card_zpowers, hb, hba, ← ha, ← Nat.card_zpowers, htop, Subgroup.card_top]
  have hzt : Subgroup.zpowers τ = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top (le_of_eq (by rw [Subgroup.card_top, hcard]))
  refine eq_top_iff.mpr ?_
  rw [← hzt]
  exact Subgroup.zpowers_le.mpr hτ

/-- **A cyclic extension of prime power degree has an unramified finite place, away from a
prescribed finite set of places of the base, whose arithmetic Frobenius generates the Galois
group.**  Discarding the finitely many ramified places along with the prescribed ones leaves a place
whose decomposition group is everything, and at an unramified place the decomposition group is
generated by the arithmetic Frobenius. -/
theorem exists_arithFrobAt_zpowers_eq_top {p : ℕ} (hp : p.Prime)
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (hne : σ₀ ≠ 1)
    (hpG : IsPGroup p Gal(K/k)) {T : Set (HeightOneSpectrum (𝓞 k))} (hT : T.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 k), v ∉ T ∧ v ∉ relRamifiedSet k K ∧
      ∃ (P : Ideal (𝓞 K)) (_ : P.IsPrime) (_ : P.LiesOver v.asIdeal) (_ : Finite (𝓞 K ⧸ P)),
        stabilizer Gal(K/k) P = ⊤ ∧
          Subgroup.zpowers (arithFrobAt (𝓞 k) Gal(K/k) P) = ⊤ := by
  obtain ⟨w, hwS, hstab⟩ := exists_stabilizer_eq_top_of_isPGroup hp hσ₀ hne hpG
    (hT.union (finite_relRamifiedSet (k := k) (L := K)))
  rw [Set.mem_union, not_or] at hwS
  obtain ⟨hwT, hwram⟩ := hwS
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : w.asIdeal.LiesOver (primeUnder (𝓞 k) w).asIdeal := ⟨rfl⟩
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := inferInstance
  have hunr : Algebra.IsUnramifiedAt (𝓞 k) w.asIdeal := by
    refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 k) w.ne_bot).mpr ?_
    by_contra hc
    exact hwram ⟨w.asIdeal, ⟨w.isPrime, ⟨rfl⟩⟩, hc⟩
  have hstab' : stabilizer Gal(K/k) w.asIdeal = ⊤ := by
    rw [← stabilizer_eq_stabilizer_asIdeal w]
    exact hstab
  refine ⟨primeUnder (𝓞 k) w, hwT, hwram, w.asIdeal, inferInstance, inferInstance, inferInstance,
    hstab', ?_⟩
  rw [← relStabilizer_eq_zpowers_arithFrobAt (k := k) w.asIdeal w.ne_bot hunr]
  exact hstab'

end InertPlace

end InverseGalois.CFT
