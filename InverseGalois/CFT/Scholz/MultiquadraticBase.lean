/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.DyadicSocle
import InverseGalois.CFT.Scholz.Realization
import InverseGalois.CFT.Scholz.StepRamification
import InverseGalois.Solvable.ElementaryAbelian

/-!
# The multiquadratic base of the dyadic Scholz–Reichardt induction

Iterating the split step of `InverseGalois.CFT.Scholz.SplitStep` at the prime two, starting from
`ℚ` and adjoining one quadratic layer at a time, produces a field of degree `2 ^ d` over `ℚ`
satisfying Serre's condition and ramified at exactly `d` primes, one contributed by each layer.
The branching prime of a layer is unramified in the field built so far, and every prime already
used is genuinely ramified there, so the `d` primes are distinct.

The Galois group is abelian of exponent two and order `2 ^ d`, hence the free object of rank `d`
and `2`-class one; and because every ramified prime is one of the `d` and each is a block on its
own, the family of singletons accounts for every square root of a product of primes lying in the
field.  That is the base of the induction on the `2`-class.

## Main results

* `InverseGalois.CFT.exists_scholz_ramifiedSet_eq_range`: a field satisfying Serre's condition
  whose ramified primes are exactly a prescribed number of distinct primes, with Galois group
  abelian of exponent two.
* `InverseGalois.CFT.exists_scholz_freePClass_one`: **the same field, with its Galois group
  identified with the free object of rank `d` and `2`-class one and its ramified primes organised
  into singleton blocks accounting for its square roots.**

## Tags

Scholz–Reichardt, multiquadratic field, elementary abelian, block
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

set_option maxHeartbeats 1000000 in
/-- **A Scholz field ramified at exactly `d` distinct primes and with elementary abelian Galois
group of order `2 ^ d`.**  Each quadratic layer of the tower contributes one ramified prime, which
is unramified below it and stays ramified above it. -/
theorem exists_scholz_ramifiedSet_eq_range (N : ℕ) : ∀ d : ℕ,
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥K) (_ : IsGalois ℚ ↥K)
      (q : Fin d → ℕ), Function.Injective q ∧ (∀ i, (q i).Prime) ∧ IsScholz 2 N ↥K ∧
        ramifiedSet ↥K = Set.range q ∧ Nat.card Gal(↥K/ℚ) = 2 ^ d ∧
        ∀ σ : Gal(↥K/ℚ), σ ^ 2 = 1 := by
  intro d
  induction d with
  | zero =>
    set E : IntermediateField ℚ (AlgebraicClosure ℚ) := ⊥ with hE
    haveI : FiniteDimensional ℚ ↥E :=
      FiniteDimensional.of_finrank_eq_succ (n := 0) IntermediateField.finrank_bot
    haveI : NumberField ↥E := ⟨⟩
    haveI : IsGalois ℚ ↥E :=
      IsGalois.of_algEquiv (IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ)).symm
    have hrank : finrank ℚ ↥E = 1 := IntermediateField.finrank_bot
    have hcard : Nat.card Gal(↥E/ℚ) = 2 ^ 0 := by
      rw [IsGalois.card_aut_eq_finrank ℚ ↥E, hrank, pow_zero]
    haveI : Subsingleton Gal(↥E/ℚ) := (Nat.card_eq_one_iff_unique.mp (by rw [hcard, pow_zero])).1
    have hram : ramifiedSet ↥E = Set.range (Fin.elim0 : Fin 0 → ℕ) :=
      (ramifiedSet_eq_empty_of_finrank_eq_one ↥E hrank).trans (Set.range_eq_empty _).symm
    exact ⟨E, inferInstance, inferInstance, Fin.elim0, fun a _ _ => Subsingleton.elim a _,
      fun i => i.elim0, isScholz_of_finrank_eq_one ↥E hrank 2 N, hram, hcard,
      fun σ => by rw [Subsingleton.elim σ 1, one_pow]⟩
  | succ d ih =>
    obtain ⟨K, hNF, hGal, q, hqinj, hqp, hsch, hram, hcard, hexp⟩ := ih
    haveI := hNF
    haveI := hGal
    have hqnp : (stepPrime ↥K Nat.prime_two N 1).Prime := prime_stepPrime ↥K Nat.prime_two N 1
    have hqnnot : stepPrime ↥K Nat.prime_two N 1 ∉ Set.range q := by
      rw [← hram]
      exact stepPrime_notMem_ramifiedSet ↥K Nat.prime_two N 1
    refine ⟨stepField ↥K Nat.prime_two N 1, inferInstance, inferInstance,
      Fin.cons (stepPrime ↥K Nat.prime_two N 1) q, Fin.cons_injective_iff.mpr ⟨hqnnot, hqinj⟩,
      ?_, isScholz_stepField ↥K Nat.prime_two N 1 hsch, ?_, ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · rw [Fin.cons_zero]
        exact hqnp
      · intro j
        rw [Fin.cons_succ]
        exact hqp j
    · rw [ramifiedSet_stepField_eq ↥K Nat.prime_two N 1 one_ne_zero, hram, Fin.range_cons,
        Set.union_singleton]
    · rw [Nat.card_congr (galEquivStepField ↥K Nat.prime_two N 1).toEquiv, Nat.card_prod, hcard,
        card_gal_stepAux ↥K Nat.prime_two N 1, pow_one, pow_succ]
    · intro σ
      have hsnd := pow_card_eq_one' (G := Gal(↥(stepAux ↥K Nat.prime_two N 1)/ℚ))
        (x := (galEquivStepField ↥K Nat.prime_two N 1 σ).2)
      rw [card_gal_stepAux ↥K Nat.prime_two N 1, pow_one] at hsnd
      refine (galEquivStepField ↥K Nat.prime_two N 1).injective ?_
      rw [map_pow, map_one]
      refine Prod.ext ?_ ?_
      · show (galEquivStepField ↥K Nat.prime_two N 1 σ).1 ^ 2 = 1
        exact hexp _
      · show (galEquivStepField ↥K Nat.prime_two N 1 σ).2 ^ 2 = 1
        exact hsnd

/-- **The base of the dyadic Scholz–Reichardt induction.**  A field satisfying Serre's condition,
with Galois group the free object of rank `d` and `2`-class one, ramified at exactly `d` distinct
primes, and whose square roots of products of primes are accounted for by the singletons of those
`d` primes. -/
theorem exists_scholz_freePClass_one (N d : ℕ) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥K) (_ : IsGalois ℚ ↥K)
      (q : Fin d → ℕ), Function.Injective q ∧ (∀ i, (q i).Prime) ∧ IsScholz 2 N ↥K ∧
        ramifiedSet ↥K = Set.range q ∧ IsBlockSpanned K (fun i => ({q i} : Finset ℕ)) ∧
        Nonempty (Gal(↥K/ℚ) ≃* FreePClass 2 d 1) := by
  obtain ⟨K, hNF, hGal, q, hqinj, hqp, hsch, hram, hcard, hexp⟩ :=
    exists_scholz_ramifiedSet_eq_range N d
  haveI := hNF
  haveI := hGal
  refine ⟨K, hNF, hGal, q, hqinj, hqp, hsch, hram, ?_, ?_⟩
  · refine isBlockSpanned_of_singleton_mem_of_mem_ramifiedSet K fun p hp => ?_
    rw [hram] at hp
    obtain ⟨i, rfl⟩ := hp
    exact ⟨i, rfl⟩
  · exact exists_mulEquiv_freePClass_one
      (fun a b => (Commute.of_orderOf_dvd_two
        (fun g => orderOf_dvd_of_pow_eq_one (hexp g)) a b).eq) hexp hcard

end InverseGalois.CFT
