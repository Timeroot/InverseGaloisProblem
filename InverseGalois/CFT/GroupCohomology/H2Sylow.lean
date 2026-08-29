/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.SylowRes

/-!
# Counting the second cohomology of a finite group from its Sylow subgroups

A positive-degree cohomology class of a finite group that restricts to zero on every Sylow
subgroup is zero, so the second cohomology embeds into the product, over the primes dividing the
order of the group, of the second cohomology of a Sylow subgroup at that prime.

Consequently, if each Sylow subgroup has at most as many second cohomology classes as it has
elements, the same holds for the whole group: the product of the orders of the Sylow subgroups is
the order of the group.

## Main results

* `InverseGalois.CFT.finite_and_card_H2_le_of_sylow`: **the second cohomology of a finite group is
  finite and has at most as many elements as the group, as soon as this holds for each of its Sylow
  subgroups.**

## Tags

group cohomology, second cohomology, Sylow subgroup, counting
-/

universe u

open CategoryTheory groupCohomology

namespace InverseGalois.CFT

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G)

/-- **The second cohomology of a finite group is finite and has at most as many elements as the
group, as soon as this holds for each of its Sylow subgroups.**  Restriction to the Sylow subgroups
is injective on the second cohomology, and the orders of the Sylow subgroups multiply to the order
of the group. -/
theorem finite_and_card_H2_le_of_sylow
    (hSyl : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G,
      Finite ↥(H2 ((Action.res _ (P : Subgroup G).subtype).obj A)) ∧
        Nat.card ↥(H2 ((Action.res _ (P : Subgroup G).subtype).obj A)) ≤ Nat.card ↥P) :
    Finite ↥(H2 A) ∧ Nat.card ↥(H2 A) ≤ Nat.card G := by
  classical
  let P : ∀ p : ↥(Nat.card G).primeFactors, Sylow (p : ℕ) G := default
  haveI hfinp : ∀ p : ↥(Nat.card G).primeFactors,
      Finite ↥(H2 ((Action.res _ (P p : Subgroup G).subtype).obj A)) :=
    fun p => (hSyl p (Nat.prime_of_mem_primeFactors p.2) (P p)).1
  haveI : Finite (∀ p : ↥(Nat.card G).primeFactors,
      ↥(H2 ((Action.res _ (P p : Subgroup G).subtype).obj A))) := Pi.finite
  have hinj : Function.Injective (fun x : ↥(H2 A) =>
      fun p : ↥(Nat.card G).primeFactors => (res (P p : Subgroup G) A 2).hom x) := by
    intro x y hxy
    refine sub_eq_zero.mp (eq_zero_of_forall_prime_res A (n := 1) (x - y) fun q hq hqdvd => ?_)
    haveI := Fact.mk hq
    have hqmem : q ∈ (Nat.card G).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
    have hcomp : (res (P ⟨q, hqmem⟩ : Subgroup G) A 2).hom x
        = (res (P ⟨q, hqmem⟩ : Subgroup G) A 2).hom y := congrFun hxy ⟨q, hqmem⟩
    refine ⟨(P ⟨q, hqmem⟩ : Subgroup G), (P ⟨q, hqmem⟩).not_dvd_index, ?_⟩
    show (res (P ⟨q, hqmem⟩ : Subgroup G) A 2).hom (x - y) = 0
    rw [map_sub, hcomp, sub_self]
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_pi] at hcard
  refine ⟨Finite.of_injective _ hinj, hcard.trans ?_⟩
  calc ∏ p : ↥(Nat.card G).primeFactors,
        Nat.card ↥(H2 ((Action.res _ (P p : Subgroup G).subtype).obj A))
      ≤ ∏ p : ↥(Nat.card G).primeFactors, Nat.card ↥(P p) :=
        Finset.prod_le_prod' fun p _ => (hSyl p (Nat.prime_of_mem_primeFactors p.2) (P p)).2
    _ = ∏ p : ↥(Nat.card G).primeFactors, (p : ℕ) ^ (Nat.card G).factorization (p : ℕ) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        haveI := Fact.mk (Nat.prime_of_mem_primeFactors p.2)
        exact (P p).card_eq_multiplicity
    _ = ∏ p ∈ (Nat.card G).primeFactors, p ^ (Nat.card G).factorization p :=
        Finset.prod_finset_coe (fun p => p ^ (Nat.card G).factorization p) _
    _ = (Nat.card G).factorization.prod (· ^ ·) := rfl
    _ = Nat.card G := Nat.factorization_prod_pow_eq_self Nat.card_pos.ne'

end

end InverseGalois.CFT
