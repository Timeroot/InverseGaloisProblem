/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.BaseOddReciprocity
import InverseGalois.CFT.Brauer.BaseSignCorrector
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.Scholz.DyadicAuxPrimeFamily
import InverseGalois.NumberTheory.SignApproximation

/-!
# Global reciprocity over a number field

The invariants of a Brauer class of a number field add up to zero.  The odd part of the order is
already covered by the auxiliary prime construction, whose only archimedean input is that a class
of odd order is split by the reals.  What is left is the two-part, where the archimedean invariants
are genuinely present and have to be removed before the auxiliary prime can be used.

Removing them is a matter of finding a class with prescribed invariants at the real places, and the
sign correctors provide exactly that: attached to an auxiliary prime congruent to three modulo four
is a homomorphism from the units of the base to its Brauer group whose invariant at a real place is
the sign of the corresponding real embedding of the unit, and whose invariants add up to zero.  The
real places of a number field are independent as far as signs are concerned, so a unit realizing
any prescribed pattern of signs exists, and multiplying by the corrector at such a unit produces a
class of two-power order with no archimedean invariants left and with the same total invariant.

An auxiliary prime congruent to three modulo four is available because such primes are exactly the
ones that fail to split completely in the field of fourth roots of unity, and a Galois field of
degree larger than one fails to be split by infinitely many primes.

Splitting an arbitrary finite order into its two-part and its odd part, a Bézout relation writes
any class as a product of a class of two-power order and a class of odd order, and every Brauer
class of a number field has finite order.

## Main results

* `InverseGalois.CFT.exists_prime_three_mod_four_notMem`: there are arbitrarily large primes
  congruent to three modulo four.
* `InverseGalois.CFT.totalInvariant_eq_one_of_pow_eq_one_two_pow_base`: **the invariants of a
  Brauer class of a number field of two-power order add up to zero.**
* `InverseGalois.CFT.totalInvariant_eq_one_base`: **global reciprocity over a number field: the
  invariants of a Brauer class add up to zero.**

## Tags

Brauer group, local invariant, global reciprocity, number field, real place, sign, auxiliary prime,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField InverseGalois.NumberTheory

/-! ### An auxiliary prime congruent to three modulo four -/

section ThreeModFour

/-- **There are arbitrarily large primes congruent to three modulo four.**  A prime not dividing
four splits completely in the field of fourth roots of unity exactly when it is one modulo four,
and that field, being of degree two, fails to be split by infinitely many primes. -/
theorem exists_prime_three_mod_four_notMem (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ 2 < q ∧ Odd ((q - 1) / 2) := by
  classical
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : IsGalois ℚ (CyclotomicField 4 ℚ) := IsCyclotomicExtension.isGalois {4} ℚ _
  have hrank : finrank ℚ (CyclotomicField 4 ℚ) = 2 := by
    rw [IsCyclotomicExtension.finrank (CyclotomicField 4 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
    decide
  have hlt : finrank ℚ ℚ < finrank ℚ (CyclotomicField 4 ℚ) := by
    rw [hrank, Module.finrank_self]
    norm_num
  obtain ⟨q, ⟨hqp, -, hnsplit⟩, hqT⟩ :=
    (infinite_setOf_splitsCompletely_not_splitsCompletely ℚ (CyclotomicField 4 ℚ)
      hlt).exists_notMem_finset (insert 2 T)
  have hq2 : q ≠ 2 := fun h => hqT (h ▸ Finset.mem_insert_self _ _)
  haveI : Fact q.Prime := ⟨hqp⟩
  have hqodd : Odd q := hqp.odd_of_ne_two hq2
  have hnd : ¬ q ∣ 4 := by
    intro h
    have h4 : q ∣ 2 ^ 2 := by simpa using h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow h4))
  have hne : ¬ (q ≡ 1 [MOD 4]) := fun h =>
    hnsplit (splitsCompletely_of_modEq 4 (CyclotomicField 4 ℚ) q hnd h)
  have h1 : q % 2 = 1 := Nat.odd_iff.mp hqodd
  have h2 : q % 4 ≠ 1 := fun hc => hne (show q % 4 = 1 % 4 by omega)
  have hq3 : 2 < q := Nat.lt_of_le_of_ne hqp.two_le (Ne.symm hq2)
  refine ⟨q, hqp, fun hc => hqT (Finset.mem_insert_of_mem hc), hq3, ?_⟩
  rw [Nat.odd_iff]
  omega

end ThreeModFour

/-! ### Matching invariants at a real place -/

section RealMatch

/-- **Two Brauer classes with the same behaviour at a real place have trivial product there.**  The
Brauer group of the reals has order two, so the base changes of the two classes are equal as soon
as they are both nontrivial, and a class of order two squares to one. -/
theorem infinitePlaceInvariant_mul_eq_one_of_isReal {k : Type} [Field k] [NumberField k]
    {u : InfinitePlace k} (hu : u.IsReal) {x y : BrauerGroup.{0, 0} k}
    (h : infinitePlaceInvariant k u x = 1 ↔ infinitePlaceInvariant k u y = 1) :
    infinitePlaceInvariant k u (x * y) = 1 := by
  letI : Algebra k ℝ := (InfinitePlace.embedding_of_isReal hu).toAlgebra
  have hstep : ∀ z : BrauerGroup.{0, 0} k,
      infinitePlaceInvariant k u z = realEmbeddingInvariant k z := by
    intro z
    rw [infinitePlaceInvariant_of_isReal k hu]
    rfl
  simp only [hstep, realEmbeddingInvariant_apply, realBrauerInvariant_eq_one_iff] at h
  rw [hstep, realEmbeddingInvariant_apply, realBrauerInvariant_eq_one_iff, map_mul]
  by_cases hx : BrauerGroup.baseChangeHom ℝ x = 1
  · rw [hx, one_mul, h.mp hx]
  · have hy : BrauerGroup.baseChangeHom ℝ y ≠ 1 := fun hc => hx (h.mpr hc)
    rw [eq_of_ne_one_brauerGroup_real hx hy, ← sq]
    exact sq_eq_one_brauerGroup_real _

end RealMatch

/-! ### Reciprocity for a class of two-power order -/

section TwoPower

/-- **The invariants of a Brauer class of a number field of two-power order and trivial archimedean
invariants add up to zero.**  Only finitely many rational primes lie below a place carrying a
nontrivial invariant, and a single auxiliary prime modulo which all of them are power non-residues
at a two-power exponent exceeding their number splits the class over a subfield of the cyclotomic
field of that auxiliary prime. -/
theorem totalInvariant_eq_one_of_arch_of_pow_eq_one_two_pow {k : Type} [Field k] [NumberField k]
    {e : ℕ} (he : e ≠ 0) {x : BrauerGroup.{0, 0} k}
    (harch : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1) (hx : x ^ 2 ^ e = 1) :
    totalInvariant k x = 1 := by
  classical
  have hfin := finite_setOf_placeInvariant_ne_one (k := k) x
  obtain ⟨P, hPp, hbadP⟩ : ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧
      ∀ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x ≠ 1 →
        ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 k) ∈ v.asIdeal → p ∈ P := by
    refine ⟨hfin.toFinset.image fun v => Rat.HeightOneSpectrum.natGenerator (primeUnder (𝓞 ℚ) v),
      ?_, ?_⟩
    · intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
      exact Rat.HeightOneSpectrum.prime_natGenerator _
    · intro v hinv p hp hpv
      refine Finset.mem_image.mpr ⟨v, hfin.mem_toFinset.mpr hinv, ?_⟩
      refine natGenerator_eq_of_natCast_mem hp ?_
      rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hpv
  have hcard : P.card < 2 ^ (P.card + 3 - 1) :=
    lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨q, hqp, hqT, hqdvd, hqres⟩ :=
    exists_prime_two_pow_dvd_sub_one_forall_pow_ne_one
      (d := e + Nat.log 2 (finrank ℚ k) + P.card + 3) (M := P.card + 3) (by omega) (by omega)
      hPp hcard (finite_ramifiedSet k).toFinset
  refine totalInvariant_eq_one_of_forall_pow_ne_one_primePow_base k (ℓ := 2)
    (d := e + Nat.log 2 (finrank ℚ k) + P.card + 2) Nat.prime_two he (by omega) harch hx hqp
    (fun hc => hqT ((Set.Finite.mem_toFinset _).mpr hc)) ?_ ?_
  · have hpow : 2 * 2 ^ (e + Nat.log 2 (finrank ℚ k) + P.card + 2)
        = 2 ^ (e + Nat.log 2 (finrank ℚ k) + P.card + 3) := by ring
    rw [hpow]
    exact hqdvd
  · intro v hinv p hp hpv
    rw [show e + Nat.log 2 (finrank ℚ k) + P.card + 2 - e - Nat.log 2 (finrank ℚ k) + 1
      = P.card + 3 by omega]
    exact hqres p (hbadP v hinv p hp hpv)

/-- **The invariants of a Brauer class of a number field of two-power order add up to zero.**  A
unit whose real embeddings are negative exactly at the real places carrying a nontrivial invariant
turns a sign corrector into a class with the same archimedean behaviour as the given one, and the
product of the two has no archimedean invariant left while its total invariant is unchanged. -/
theorem totalInvariant_eq_one_of_pow_eq_one_two_pow_base {k : Type} [Field k] [NumberField k]
    {e : ℕ} {x : BrauerGroup.{0, 0} k} (hx : x ^ 2 ^ e = 1) : totalInvariant k x = 1 := by
  classical
  obtain ⟨q, hqp, hqT, hq2, hqodd⟩ :=
    exists_prime_three_mod_four_notMem (finite_ramifiedSet k).toFinset
  have hqk : q ∉ ramifiedSet k := fun hc => hqT ((Set.Finite.mem_toFinset _).mpr hc)
  obtain ⟨Y, hY2, hYtot, hYarch⟩ := exists_signCorrector_base k hqp hq2 hqk hqodd
  obtain ⟨a, ha⟩ := exists_units_pos_iff_notMem_set k
    {u : InfinitePlace k | infinitePlaceInvariant k u x ≠ 1}
  have harch : ∀ u : InfinitePlace k, infinitePlaceInvariant k u (x * Y a) = 1 := by
    intro u
    rcases u.isReal_or_isComplex with hu | hu
    · refine infinitePlaceInvariant_mul_eq_one_of_isReal hu ?_
      rw [hYarch a u hu, realCyclicInvariant_eq_one_iff]
      have hsign := ha u hu
      simp only [Set.mem_setOf_eq, not_not] at hsign
      simpa using hsign.symm
    · rw [infinitePlaceInvariant_of_isComplex k hu, MonoidHom.one_apply]
  have hpow : (x * Y a) ^ 2 ^ (e + 1) = 1 := by
    have h1 : x ^ 2 ^ (e + 1) = 1 := by rw [pow_succ, pow_mul, hx, one_pow]
    have h2 : (Y a) ^ 2 ^ (e + 1) = 1 := by rw [pow_succ, pow_mul', hY2 a, one_pow]
    rw [mul_pow, h1, h2, one_mul]
  have hsum := totalInvariant_eq_one_of_arch_of_pow_eq_one_two_pow (by omega) harch hpow
  rwa [map_mul, hYtot a, mul_one] at hsum

end TwoPower

/-! ### Global reciprocity -/

section General

/-- **The invariants of a Brauer class of a number field of finite order add up to zero.**
Splitting the order into its two-part and its odd part, a Bézout relation writes the class as a
product of a class of two-power order and a class of odd order. -/
theorem totalInvariant_eq_one_of_pow_eq_one_nat_base {k : Type} [Field k] [NumberField k] {n : ℕ}
    (hn : n ≠ 0) {x : BrauerGroup.{0, 0} k} (hx : x ^ n = 1) : totalInvariant k x = 1 := by
  set c := n.factorization 2 with hc
  set r := 2 ^ c with hr
  set m := n / r with hm
  have hrm : r * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime r m := Nat.Coprime.pow_left c (Nat.coprime_ordCompl Nat.prime_two hn)
  have hmodd : Odd m :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))
  have hA : totalInvariant k (x ^ m) = 1 :=
    totalInvariant_eq_one_of_pow_eq_one_two_pow_base (e := c)
      (by rw [← pow_mul, mul_comm m r, hrm, hx])
  have hB : totalInvariant k (x ^ r) = 1 :=
    totalInvariant_eq_one_of_pow_eq_one_odd_base k m hmodd (x ^ r) (by rw [← pow_mul, hrm, hx])
  have hbez : (1 : ℤ) = (r : ℤ) * Nat.gcdA r m + (m : ℤ) * Nat.gcdB r m := by
    have hg := Nat.gcd_eq_gcd_ab r m
    rwa [hcop, Nat.cast_one] at hg
  have hsplit : x = (x ^ r) ^ (Nat.gcdA r m) * (x ^ m) ^ (Nat.gcdB r m) := by
    rw [← zpow_natCast x r, ← zpow_natCast x m, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
      zpow_one]
  rw [hsplit, map_mul, map_zpow, map_zpow, hA, hB, one_zpow, one_zpow, one_mul]

/-- **Global reciprocity over a number field: the invariants of a Brauer class add up to zero.**
Every Brauer class of a perfect field is of finite order, being split by a finite Galois
extension. -/
theorem totalInvariant_eq_one_base (k : Type) [Field k] [NumberField k]
    (x : BrauerGroup.{0, 0} k) : totalInvariant k x = 1 := by
  obtain ⟨n, hn, hxn⟩ := exists_pow_eq_one x
  exact totalInvariant_eq_one_of_pow_eq_one_nat_base hn hxn

end General

end InverseGalois.CFT
